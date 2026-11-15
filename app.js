const ANGLE_DEG = 40;
const PITCH_UP_RATIO = 0.42;
const PITCH_DOWN_RATIO = 0.58;
const FACE_TOO_FAR = 0.14;
const FACE_TOO_CLOSE = 0.88;
const DISTANCE_HOLD_FRAMES = 18;
const MISSING_HOLD_FRAMES = 45;
const MATCH_FRAMES = 10;
const POSE_COOLDOWN_MS = 700;
const NEUTRAL_FRAMES = 6;
const BASELINE_HOLD_MS = 180;
const START_FALLBACK_MS = 900;
const YAW_NEUTRAL = 16;
const TILT_NEUTRAL = 0.04;
const NOSE_NEUTRAL_MIN = 0.44;
const NOSE_NEUTRAL_MAX = 0.56;
const START_YAW = 36;
const START_TILT = 0.16;
const START_NOSE_MIN = 0.32;
const START_NOSE_MAX = 0.7;
const FRONT_NOSE = 0.5;
const YAW_DELTA = 42;
const YAW_TURN_DELTA = 20;
const YAW_MATCH_FRAMES = 6;
const RECOGNIZE_MS = 3000;
const TILT_RATIO = 0.16;
const ROLL_RIGHT_RATIO = 0.09;
const PITCH_DOWN_DELTA = 0.06;
const PITCH_UP_DELTA = -0.1;
const PITCH_DOWN_DEG = 11;
const PITCH_UP_DEG = -14;

const POSES = [
  {
    id: "yaw-right",
    line1: "고개를 오른쪽으로",
    line2: "90º 돌려주세요",
    src: "오른쪽으로 돌리기.svg",
  },
  {
    id: "yaw-left",
    line1: "고개를 왼쪽으로",
    line2: "90º 돌려주세요",
    src: "왼쪽으로 돌리기.svg",
  },
  {
    id: "pitch-up",
    line1: "고개를 들어",
    line2: "천장을 바라보세요",
    src: "위.svg",
  },
  {
    id: "pitch-down",
    line1: "고개를 숙여",
    line2: "바닥을 바라보세요",
    src: "아래.svg",
  },
  {
    id: "roll-left",
    line1: "고개를 왼쪽으로",
    line2: "90º 기울이세요",
    src: "왼쪽으로 기울이기.svg",
  },
  {
    id: "roll-right",
    line1: "고개를 오른쪽으로",
    line2: "90º 기울이세요",
    src: "오른쪽으로 기울이기.svg",
  },
];

let faceLandmarker;
let cameraStarted = false;
let detectRunning = false;
let lastTimestamp = 0;
let poseQueue = [];
let poseIndex = 0;
let filledCount = 0;
let canDetect = false;
let cooldownTimer = 0;
let matchStreak = 0;
let awaitingNeutral = true;
let baseline = null;
let lastPoseId = null;
let neutralStreak = 0;
let neutralMisses = 0;
let neutralSince = 0;
let poseConsumed = true;
let settled = false;
let baselineReadyAt = 0;
let poseToken = 0;
let recognizeUntil = 0;
let readyBaseline = null;
let missingFrames = 0;
let farFrames = 0;
let closeFrames = 0;
let shownStatus = "";
let stretchCount = Number(localStorage.getItem("stretchCount") || 0);
let attemptTimer = 0;
const ATTEMPT_LIMIT_MS = 60000;
let completeTimer = 0;
let completeCopyTimer = 0;
let completeTitleTimer = 0;
let lockLeaveTimer = 0;

const video = document.getElementById("webcam");
const faceMotionEl = document.getElementById("face-motion");
const faceMotionCanvas = document.getElementById("face-motion-canvas");
const faceMotionCtx = faceMotionCanvas
  ? faceMotionCanvas.getContext("2d", { willReadFrequently: true })
  : null;
let faceMotionDraw = 0;
const pinDots = document.querySelectorAll("#pin-dots span");
const titleEl = document.getElementById("test-title");
const poseGraphicEl = document.getElementById("pose-graphic");
const statusEl = document.getElementById("track-status");
const completeCopyEl = document.getElementById("complete-copy");
const completeTitleEl = document.getElementById("complete-title-text");
const completeProgressEl = document.getElementById("complete-progress");
const lockIconEl = document.getElementById("lock-icon");
const unlockSoundEl = document.getElementById("unlock-sound");
const nodSoundEl = document.getElementById("nod-sound");
const deleteSoundEl = document.getElementById("delete-sound");
const lockedSoundEl = document.getElementById("locked-sound");
const statusSoundEl = document.getElementById("status-sound");
const DISTANCE_STATUS = new Set(["화면 앞으로 더 가까이 오세요", "뒤로 더 물러나세요"]);

function setStatus(text) {
  if (!statusEl || text === shownStatus) return;
  shownStatus = text;
  statusEl.classList.remove("is-enter");
  void statusEl.offsetWidth;
  statusEl.textContent = text;
  statusEl.classList.add("is-enter");
  if (DISTANCE_STATUS.has(text)) {
    playNamed("status");
  }
}

function shuffle(list) {
  const items = [...list];
  for (let i = items.length - 1; i > 0; i -= 1) {
    const j = Math.floor(Math.random() * (i + 1));
    [items[i], items[j]] = [items[j], items[i]];
  }
  return items;
}

function currentPose() {
  return poseQueue[poseIndex];
}

const poseSvgCache = new Map();
const SVG_NS = "http://www.w3.org/2000/svg";

function pathFlowsLeftToRight(path) {
  try {
    const length = path.getTotalLength();
    if (!length) return true;
    const start = path.getPointAtLength(0);
    const ahead = path.getPointAtLength(Math.min(length, length * 0.12));
    return ahead.x >= start.x;
  } catch {
    return true;
  }
}

function makeFlowStroke(path, dash, extraClass, shift) {
  const clone = path.cloneNode(false);
  clone.removeAttribute("class");
  clone.removeAttribute("style");
  clone.setAttribute("fill", "none");
  clone.setAttribute("pathLength", "1");
  clone.setAttribute("stroke-dasharray", dash);
  clone.setAttribute("stroke-dashoffset", String(shift));
  clone.setAttribute("class", extraClass);
  const rtl = !pathFlowsLeftToRight(path);
  const animate = document.createElementNS(SVG_NS, "animate");
  animate.setAttribute("attributeName", "stroke-dashoffset");
  animate.setAttribute("dur", "8.53s");
  animate.setAttribute("repeatCount", "indefinite");
  animate.setAttribute("from", String(shift));
  animate.setAttribute("to", String(rtl ? shift + 1 : shift - 1));
  clone.appendChild(animate);
  return clone;
}

function isEarPath(path, svg) {
  const group = path.closest("g");
  if (group && (group.classList.contains("cls-2") || group.getAttribute("opacity") === "0.5")) {
    return true;
  }
  let box;
  try {
    box = path.getBBox();
  } catch {
    return false;
  }
  const view = svg.viewBox.baseVal;
  const midX = view.x + view.width / 2;
  const cx = box.x + box.width / 2;
  const cy = box.y + box.height / 2;
  const compact = box.width < 100 && box.height < 150 && box.width * box.height < 11000;
  const earBand = cy > 370 && cy < 590;
  const onSide = Math.abs(cx - midX) > 68;
  return compact && earBand && onSide;
}

function addPoseFlowLight(svg) {
  svg.setAttribute("preserveAspectRatio", "xMidYMid meet");
  let defs = svg.querySelector("defs");
  if (!defs) {
    defs = document.createElementNS(SVG_NS, "defs");
    svg.prepend(defs);
  }
  if (!defs.querySelector("#pose-flow-glow")) {
    const filter = document.createElementNS(SVG_NS, "filter");
    filter.setAttribute("id", "pose-flow-glow");
    filter.setAttribute("x", "-80%");
    filter.setAttribute("y", "-80%");
    filter.setAttribute("width", "260%");
    filter.setAttribute("height", "260%");
    filter.innerHTML =
      '<feGaussianBlur in="SourceGraphic" stdDeviation="3.2" result="blur"></feGaussianBlur>' +
      '<feMerge><feMergeNode in="blur"></feMergeNode><feMergeNode in="SourceGraphic"></feMergeNode></feMerge>';
    defs.appendChild(filter);
  }
  const measured = [...svg.querySelectorAll("path")].map((path) => {
    let length = 0;
    try {
      length = path.getTotalLength();
    } catch {
      length = 0;
    }
    return { path, length };
  });
  const longest = Math.max(0, ...measured.map((item) => item.length));
  const glow = document.createElementNS(SVG_NS, "g");
  glow.setAttribute("class", "pose-flow");
  glow.setAttribute("filter", "url(#pose-flow-glow)");
  measured.forEach(({ path, length }) => {
    if (length < 80 || length < longest * 0.4) return;
    if (isEarPath(path, svg)) return;
    glow.appendChild(makeFlowStroke(path, "0.16 0.84", "pose-flow-halo", 0));
    glow.appendChild(makeFlowStroke(path, "0.1 0.9", "pose-flow-mid", -0.03));
    glow.appendChild(makeFlowStroke(path, "0.055 0.945", "pose-flow-soft", -0.0525));
    glow.appendChild(makeFlowStroke(path, "0.022 0.978", "pose-flow-core", -0.069));
  });
  svg.appendChild(glow);
}

async function loadPoseSvg(src) {
  if (poseSvgCache.has(src)) return poseSvgCache.get(src).cloneNode(true);
  const response = await fetch(encodeURI(src));
  const markup = await response.text();
  const parsed = new DOMParser().parseFromString(markup, "image/svg+xml");
  const svg = parsed.documentElement;
  if (!svg || svg.nodeName.toLowerCase() !== "svg") return null;
  poseSvgCache.set(src, svg);
  return svg.cloneNode(true);
}

async function renderCurrentPose() {
  const pose = currentPose();
  if (!pose || !poseGraphicEl) return;
  const line2 = pose.line2.replace(/º/g, '<span class="degree">º</span>');
  titleEl.innerHTML = `${pose.line1}<br />${line2}`;
  const svg = await loadPoseSvg(pose.src);
  if (!svg || currentPose() !== pose) return;
  poseGraphicEl.replaceChildren(svg);
  addPoseFlowLight(svg);
}

function pauseMatching() {
  awaitingNeutral = true;
  baseline = null;
  baselineReadyAt = 0;
  neutralStreak = 0;
  neutralMisses = 0;
  neutralSince = 0;
  matchStreak = 0;
  poseConsumed = true;
  settled = false;
  canDetect = false;
}

function noteTrackingGap() {
  matchStreak = 0;
  if (settled) return;
  neutralStreak = 0;
  neutralMisses = 0;
  baseline = null;
  baselineReadyAt = 0;
}

function resetUnlockSequence() {
  poseToken += 1;
  recognizeUntil = 0;
  readyBaseline = null;
  const token = poseToken;
  poseQueue = shuffle(POSES);
  poseIndex = 0;
  filledCount = 0;
  lastPoseId = null;
  window.clearTimeout(cooldownTimer);
  pinDots.forEach((dot) => dot.classList.remove("is-filled"));
  renderCurrentPose();
  pauseMatching();
  cooldownTimer = window.setTimeout(() => {
    if (token !== poseToken) return;
    canDetect = true;
  }, 400);
}

function playSound(audioEl) {
  if (!audioEl) return;
  try {
    audioEl.pause();
    audioEl.currentTime = 0;
  } catch {
    /* ignore */
  }
  const play = audioEl.play();
  if (play && typeof play.catch === "function") {
    play.catch(() => {});
  }
}

const SOUND_ELEMENTS = {
  unlock: unlockSoundEl,
  nod: nodSoundEl,
  delete: deleteSoundEl,
  locked: lockedSoundEl,
  status: statusSoundEl,
};
const DELETE_START = 0.006;
let audioCtx = null;
const soundBuffers = {};
let soundsLoading = false;

function audioSource(audioEl) {
  if (!audioEl) return "";
  const source = audioEl.querySelector("source");
  return audioEl.currentSrc || audioEl.getAttribute("src") || source?.getAttribute("src") || "";
}

function primeAudio(audioEl) {
  if (!audioEl || audioEl.dataset.primed === "1") return;
  audioEl.dataset.primed = "1";
  audioEl.muted = true;
  const play = audioEl.play();
  const finish = () => {
    audioEl.pause();
    try {
      audioEl.currentTime = 0;
    } catch {
      /* ignore */
    }
    audioEl.muted = false;
  };
  if (play && typeof play.then === "function") {
    play.then(finish).catch(() => {
      audioEl.muted = false;
    });
  } else {
    finish();
  }
}

function unlockAudio(exceptEl) {
  const Ctx = window.AudioContext || window.webkitAudioContext;
  if (Ctx && !audioCtx) audioCtx = new Ctx();
  if (audioCtx && audioCtx.state === "suspended") {
    audioCtx.resume().catch(() => {});
  }
  if (audioCtx) {
    try {
      const silent = audioCtx.createBuffer(1, 1, audioCtx.sampleRate);
      const blip = audioCtx.createBufferSource();
      blip.buffer = silent;
      blip.connect(audioCtx.destination);
      blip.start(0);
    } catch {
      /* ignore */
    }
  }
  Object.values(SOUND_ELEMENTS).forEach((audioEl) => {
    if (audioEl && audioEl !== exceptEl) primeAudio(audioEl);
  });
  if (!soundsLoading && audioCtx) {
    soundsLoading = true;
    Object.entries(SOUND_ELEMENTS).forEach(([id, audioEl]) => {
      const src = audioSource(audioEl);
      if (!src) return;
      fetch(src)
        .then((res) => res.arrayBuffer())
        .then((data) => audioCtx.decodeAudioData(data))
        .then((buffer) => {
          soundBuffers[id] = buffer;
        })
        .catch(() => {});
    });
  }
}

function playNamed(id, offset = 0) {
  const audioEl = SOUND_ELEMENTS[id];
  const buffer = soundBuffers[id];
  if (!audioCtx || !buffer) {
    playSound(audioEl);
    return;
  }
  const start = () => {
    const source = audioCtx.createBufferSource();
    source.buffer = buffer;
    source.connect(audioCtx.destination);
    const at = Math.min(offset, Math.max(0, buffer.duration - 0.02));
    source.start(0, at);
  };
  if (audioCtx.state === "suspended") {
    audioCtx.resume().then(start).catch(() => playSound(audioEl));
    return;
  }
  start();
}

function playDeleteSound() {
  playNamed("delete", DELETE_START);
}

function playLockedSound() {
  playNamed("locked");
}

function advancePose() {
  if (poseConsumed || !settled || filledCount >= pinDots.length) return;
  const token = poseToken;
  const finishedPose = currentPose();
  pauseMatching();
  pinDots[filledCount].classList.add("is-filled");
  filledCount += 1;
  lastPoseId = finishedPose?.id ?? null;

  if (filledCount >= pinDots.length) {
    if (statusEl) {
      shownStatus = "";
      statusEl.textContent = "";
      statusEl.classList.remove("is-enter");
    }
    window.clearTimeout(cooldownTimer);
    cooldownTimer = window.setTimeout(() => {
      if (token !== poseToken) return;
      startCompleteScreen();
    }, 500);
    playNodSound();
    return;
  }

  window.clearTimeout(cooldownTimer);
  cooldownTimer = window.setTimeout(() => {
    if (token !== poseToken) return;
    poseToken += 1;
    poseIndex += 1;
    renderCurrentPose();
    pauseMatching();
    canDetect = true;
  }, 500);
  playNodSound();
}

function stopFaceMotionDraw() {
  if (faceMotionDraw) {
    window.cancelAnimationFrame(faceMotionDraw);
    faceMotionDraw = 0;
  }
}

function drawFaceMotionFrame() {
  faceMotionDraw = 0;
  if (!faceMotionEl || !faceMotionCanvas || !faceMotionCtx) return;
  if (faceMotionEl.paused || faceMotionEl.ended) return;
  const width = faceMotionEl.videoWidth;
  const height = faceMotionEl.videoHeight;
  if (width && height) {
    if (faceMotionCanvas.width !== width) faceMotionCanvas.width = width;
    if (faceMotionCanvas.height !== height) faceMotionCanvas.height = height;
    faceMotionCtx.drawImage(faceMotionEl, 0, 0, width, height);
    const frame = faceMotionCtx.getImageData(0, 0, width, height);
    const pixels = frame.data;
    for (let i = 0; i < pixels.length; i += 4) {
      if (pixels[i] < 90 && pixels[i + 1] < 90 && pixels[i + 2] < 90) {
        pixels[i] = 17;
        pixels[i + 1] = 17;
        pixels[i + 2] = 17;
      }
    }
    faceMotionCtx.putImageData(frame, 0, 0);
  }
  faceMotionDraw = window.requestAnimationFrame(drawFaceMotionFrame);
}

function syncFaceMotion(id) {
  if (!faceMotionEl) return;
  if (id === "screen-1") {
    faceMotionEl.loop = true;
    const play = faceMotionEl.play();
    if (play && typeof play.catch === "function") {
      play.catch(() => {});
    }
    stopFaceMotionDraw();
    drawFaceMotionFrame();
    return;
  }
  stopFaceMotionDraw();
  faceMotionEl.pause();
}

function resetLockIcon() {
  window.clearTimeout(lockLeaveTimer);
  lockLeaveTimer = 0;
  if (!lockIconEl) return;
  lockIconEl.classList.remove("is-visible", "is-unlocking", "is-leaving");
}

function showClosedLock() {
  window.clearTimeout(lockLeaveTimer);
  lockLeaveTimer = 0;
  if (!lockIconEl) return;
  lockIconEl.classList.remove("is-unlocking", "is-leaving");
  void lockIconEl.offsetWidth;
  lockIconEl.classList.add("is-visible");
}

function playUnlockLock() {
  if (!lockIconEl) return;
  lockIconEl.classList.remove("is-leaving");
  lockIconEl.classList.add("is-visible");
  void lockIconEl.offsetWidth;
  lockIconEl.classList.add("is-unlocking");
  window.clearTimeout(lockLeaveTimer);
  lockLeaveTimer = window.setTimeout(() => {
    lockIconEl.classList.add("is-leaving");
  }, 1000);
}

function clearAttemptTimer() {
  window.clearTimeout(attemptTimer);
  attemptTimer = 0;
}

function startAttemptTimer() {
  clearAttemptTimer();
  attemptTimer = window.setTimeout(() => {
    attemptTimer = 0;
    goToOnboarding();
  }, ATTEMPT_LIMIT_MS);
}

function showScreen(id) {
  document.querySelectorAll(".screen").forEach((screen) => {
    screen.classList.toggle("is-active", screen.id === id);
  });
  syncFaceMotion(id);
  if (id === "screen-2") {
    showClosedLock();
    resetUnlockSequence();
    startCameraAndTracking();
    startAttemptTimer();
  } else if (id !== "screen-3") {
    clearAttemptTimer();
    resetLockIcon();
  }
}

function stopCameraAndTracking() {
  detectRunning = false;
  const stream = video.srcObject;
  if (stream) {
    stream.getTracks().forEach((track) => track.stop());
    video.srcObject = null;
  }
  cameraStarted = false;
}

function playUnlockSound() {
  playNamed("unlock");
}

function playNodSound() {
  playNamed("nod");
}

function clearCompleteTimers() {
  window.clearTimeout(completeTimer);
  window.clearTimeout(completeCopyTimer);
  window.clearTimeout(completeTitleTimer);
  completeTimer = 0;
  completeCopyTimer = 0;
  completeTitleTimer = 0;
}

function goToOnboarding() {
  clearAttemptTimer();
  clearCompleteTimers();
  stopCameraAndTracking();
  resetLockIcon();
  if (completeProgressEl) {
    completeProgressEl.classList.remove("is-running");
  }
  showScreen("screen-1");
  playLockedSound();
}

function startCompleteScreen() {
  clearAttemptTimer();
  stopCameraAndTracking();
  stretchCount += 1;
  localStorage.setItem("stretchCount", String(stretchCount));
  if (completeTitleEl) {
    completeTitleEl.classList.remove("is-enter");
    completeTitleEl.textContent = "잠금해제 완료!";
  }
  if (completeCopyEl) {
    completeCopyEl.classList.remove("is-enter");
    completeCopyEl.innerHTML = `6개의 암호를 해제하며 거북목 예방을 위한<br />스트레칭을 ${stretchCount}번 실천했어요.`;
  }
  showScreen("screen-3");
  playUnlockSound();
  playUnlockLock();

  if (completeProgressEl) {
    completeProgressEl.classList.remove("is-running");
    void completeProgressEl.offsetWidth;
    completeProgressEl.classList.add("is-running");
  }

  clearCompleteTimers();
  completeTitleTimer = window.setTimeout(() => {
    if (completeTitleEl) {
      completeTitleEl.classList.remove("is-enter");
      void completeTitleEl.offsetWidth;
      completeTitleEl.textContent = "거북목 예방 실천도 완료!";
      completeTitleEl.classList.add("is-enter");
    }
    if (completeCopyEl) {
      completeCopyEl.classList.remove("is-enter");
      void completeCopyEl.offsetWidth;
      completeCopyEl.innerHTML =
        "다음 체험자를 위해<br />5초 후 자동으로 처음 화면으로 돌아갑니다.";
      completeCopyEl.classList.add("is-enter");
    }
  }, 4500);
  completeTimer = window.setTimeout(() => {
    goToOnboarding();
  }, 9500);
}

if (faceMotionEl) {
  faceMotionEl.addEventListener("playing", () => {
    if (!faceMotionDraw) drawFaceMotionFrame();
  });
}

syncFaceMotion("screen-1");

document.addEventListener(
  "touchmove",
  (event) => {
    event.preventDefault();
  },
  { passive: false }
);

function lockPageSize() {
  const device = document.querySelector(".device");
  if (window.innerWidth > 430) {
    document.documentElement.style.height = "";
    document.body.style.height = "";
    if (device) device.style.height = "";
    return;
  }
  const viewport = window.visualViewport;
  const height = Math.round(viewport ? viewport.height : window.innerHeight);
  document.documentElement.style.height = `${height}px`;
  document.body.style.height = `${height}px`;
  if (device) device.style.height = `${height}px`;
  window.scrollTo(0, 0);
}

lockPageSize();
window.addEventListener("resize", lockPageSize);
if (window.visualViewport) {
  window.visualViewport.addEventListener("resize", lockPageSize);
  window.visualViewport.addEventListener("scroll", lockPageSize);
}

function bindCtaHover(button) {
  if (!button) return;
  button.addEventListener("pointerenter", () => {
    button.classList.add("is-pressed");
  });
  button.addEventListener("pointerdown", () => {
    button.classList.add("is-pressed");
  });
  button.addEventListener("pointerleave", () => {
    button.classList.remove("is-pressed");
  });
}

const onboardingCta = document.getElementById("onboarding-cta");
bindCtaHover(onboardingCta);
let startDeletePlayed = false;
onboardingCta.addEventListener("pointerdown", () => {
  startDeletePlayed = true;
  unlockAudio(deleteSoundEl);
  playDeleteSound();
});
onboardingCta.addEventListener("click", (event) => {
  event.stopPropagation();
  if (!startDeletePlayed) playDeleteSound();
  startDeletePlayed = false;
  showScreen("screen-2");
  onboardingCta.classList.remove("is-pressed");
});

const completeHomeButton = document.getElementById("complete-home");
bindCtaHover(completeHomeButton);
completeHomeButton.addEventListener("pointerdown", () => {
  unlockAudio(deleteSoundEl);
  playDeleteSound();
});
completeHomeButton.addEventListener("click", (event) => {
  event.stopPropagation();
  completeHomeButton.classList.remove("is-pressed");
  goToOnboarding();
});

function faceSize(landmarks) {
  let minX = 1;
  let minY = 1;
  let maxX = 0;
  let maxY = 0;
  [1, 10, 33, 152, 234, 263, 454].forEach((index) => {
    const point = landmarks[index];
    if (!point) return;
    minX = Math.min(minX, point.x);
    maxX = Math.max(maxX, point.x);
    minY = Math.min(minY, point.y);
    maxY = Math.max(maxY, point.y);
  });
  return Math.max(maxX - minX, maxY - minY);
}

function averageY(landmarks, indexes) {
  const points = indexes.map((index) => landmarks[index]).filter(Boolean);
  if (!points.length) return null;
  return points.reduce((sum, point) => sum + point.y, 0) / points.length;
}

function headPoseFromLandmarks(landmarks) {
  const nose = landmarks[1];
  const leftEye = landmarks[33];
  const rightEye = landmarks[263];
  const forehead = landmarks[10];
  const chin = landmarks[152];
  if (!nose || !leftEye || !rightEye) return null;

  const eyeMidX = (leftEye.x + rightEye.x) / 2;
  const eyeMidY = (leftEye.y + rightEye.y) / 2;
  const eyeDist = Math.hypot(rightEye.x - leftEye.x, rightEye.y - leftEye.y) || 0.001;
  const faceH = Math.max((chin?.y || 0.8) - (forehead?.y || 0.2), 0.001);
  const noseRatio = (nose.y - (forehead?.y || 0)) / faceH;

  const yaw = ((nose.x - eyeMidX) / eyeDist) * 90;
  const pitch = ((nose.y - eyeMidY) / eyeDist) * 90;

  const personLeftY = averageY(landmarks, [33, 133, 61, 234]);
  const personRightY = averageY(landmarks, [263, 362, 291, 454]);
  const tilt = personLeftY != null && personRightY != null ? (personLeftY - personRightY) / faceH : 0;

  return { yaw, pitch, tilt, noseRatio };
}

function isFacingForward(pose) {
  return (
    Math.abs(pose.yaw) <= YAW_NEUTRAL &&
    Math.abs(pose.tilt) <= TILT_NEUTRAL &&
    pose.noseRatio >= NOSE_NEUTRAL_MIN &&
    pose.noseRatio <= NOSE_NEUTRAL_MAX
  );
}

function isNearFront(head) {
  return (
    Math.abs(head.yaw) <= START_YAW &&
    Math.abs(head.tilt) <= START_TILT &&
    head.noseRatio >= START_NOSE_MIN &&
    head.noseRatio <= START_NOSE_MAX
  );
}

function settleBaseline(head) {
  baseline = { ...head };
  baselineReadyAt = 0;
  settled = true;
  awaitingNeutral = false;
  poseConsumed = false;
  matchStreak = 0;
  neutralStreak = 0;
  neutralMisses = 0;
  neutralSince = 0;
  if (shownStatus.startsWith("얼굴은 인식하고 있어요") && statusEl) {
    shownStatus = "";
    statusEl.textContent = "";
    statusEl.classList.remove("is-enter");
  }
}

function poseDelta(head, origin) {
  return {
    yaw: head.yaw - origin.yaw,
    pitch: head.pitch - origin.pitch,
    tilt: head.tilt - origin.tilt,
    noseRatio: head.noseRatio - origin.noseRatio,
  };
}

function poseSucceeded(id, delta, head) {
  if (!delta || !head) return false;
  if (id === "yaw-left") return delta.yaw >= YAW_TURN_DELTA;
  if (id === "yaw-right") return delta.yaw <= -YAW_TURN_DELTA;
  if (id === "pitch-down") {
    if (!(delta.noseRatio >= PITCH_DOWN_DELTA || delta.pitch >= PITCH_DOWN_DEG)) return false;
    if (lastPoseId === "pitch-up" && head) {
      return head.noseRatio >= FRONT_NOSE + PITCH_DOWN_DELTA || head.pitch >= PITCH_DOWN_DEG;
    }
    return true;
  }
  if (id === "pitch-up") {
    if (!(delta.noseRatio <= PITCH_UP_DELTA || delta.pitch <= PITCH_UP_DEG)) return false;
    if (lastPoseId === "pitch-down" && head) {
      return head.noseRatio <= FRONT_NOSE + PITCH_UP_DELTA || head.pitch <= PITCH_UP_DEG;
    }
    return true;
  }
  if (id === "roll-left") return delta.tilt <= -TILT_RATIO;
  if (id === "roll-right") return delta.tilt >= ROLL_RIGHT_RATIO;
  return false;
}

const TASKS_VISION = "https://cdn.jsdelivr.net/npm/@mediapipe/tasks-vision@0.10.21";

async function createLandmarker() {
  const { FaceLandmarker, FilesetResolver } = await import(`${TASKS_VISION}/vision_bundle.mjs`);
  const vision = await FilesetResolver.forVisionTasks(`${TASKS_VISION}/wasm`);
  const modelAssetPath = new URL("./models/face_landmarker.task", window.location.href).href;
  return FaceLandmarker.createFromOptions(vision, {
    baseOptions: {
      modelAssetPath,
      delegate: "CPU",
    },
    runningMode: "VIDEO",
    numFaces: 1,
    minFaceDetectionConfidence: 0.3,
    minFacePresenceConfidence: 0.3,
    minTrackingConfidence: 0.3,
  });
}

async function startWebcam() {
  if (cameraStarted) return;
  const stream = await navigator.mediaDevices.getUserMedia({
    video: { facingMode: "user", width: { ideal: 1280 }, height: { ideal: 720 } },
    audio: false,
  });
  video.srcObject = stream;
  video.muted = true;
  video.setAttribute("playsinline", "true");
  video.playsInline = true;
  await new Promise((resolve) => {
    if (video.readyState >= 2) {
      resolve();
      return;
    }
    video.addEventListener("loadeddata", resolve, { once: true });
  });
  await video.play();
  cameraStarted = true;
}

async function startCameraAndTracking() {
  lastTimestamp = 0;
  setStatus("카메라를 켜는 중");
  try {
    await startWebcam();
  } catch (error) {
    setStatus("카메라 권한을 허용해 주세요");
    console.error(error);
    return;
  }

  detectRunning = true;
  requestAnimationFrame(detectLoop);

  if (!faceLandmarker) {
    setStatus("Face Landmarker 불러오는 중");
    try {
      faceLandmarker = await createLandmarker();
    } catch (error) {
      const detail = error && error.message ? error.message : "알 수 없는 오류";
      setStatus(`모델을 불러오지 못했습니다: ${detail}`);
      console.error(error);
    }
  }
}

createLandmarker()
  .then((landmarker) => {
    faceLandmarker = landmarker;
  })
  .catch((error) => {
    console.error("Face Landmarker 미리 로드 실패", error);
  });

function detectLoop() {
  if (!detectRunning) return;
  requestAnimationFrame(detectLoop);

  if (!faceLandmarker || video.readyState < 2 || video.videoWidth === 0) {
    return;
  }

  lastTimestamp = Math.max(performance.now(), lastTimestamp + 1);

  let landmarks;
  try {
    const result = faceLandmarker.detectForVideo(video, lastTimestamp);
    landmarks = result.faceLandmarks?.[0];
  } catch (error) {
    return;
  }

  const pose = currentPose();
  if (!landmarks) {
    missingFrames += 1;
    farFrames = 0;
    closeFrames = 0;
    if (missingFrames >= 12) matchStreak = 0;
    if (missingFrames >= MISSING_HOLD_FRAMES) {
      setStatus("화면 앞으로 더 가까이 오세요");
      noteTrackingGap();
    }
    return;
  }
  missingFrames = 0;

  const size = faceSize(landmarks);
  const head = headPoseFromLandmarks(landmarks);
  const turned = head && !isFacingForward(head);
  if (!turned && size < FACE_TOO_FAR) {
    farFrames += 1;
    closeFrames = 0;
    if (farFrames >= DISTANCE_HOLD_FRAMES) {
      setStatus("화면 앞으로 더 가까이 오세요");
      noteTrackingGap();
    }
    return;
  }
  if (!turned && size > FACE_TOO_CLOSE) {
    closeFrames += 1;
    farFrames = 0;
    if (closeFrames >= DISTANCE_HOLD_FRAMES) {
      setStatus("뒤로 더 물러나세요");
      noteTrackingGap();
    }
    return;
  }
  farFrames = 0;
  closeFrames = 0;

  if (!head || !pose || filledCount >= pinDots.length) {
    return;
  }

  if (!settled && filledCount === 0) {
    if (!recognizeUntil) recognizeUntil = performance.now() + RECOGNIZE_MS;
    const left = recognizeUntil - performance.now();
    const sec = Math.max(1, Math.ceil(left / 1000));
    setStatus(`얼굴은 인식하고 있어요. ${sec}초 남음`);
    if (!readyBaseline || Math.abs(head.yaw) + Math.abs(head.tilt) * 80 < Math.abs(readyBaseline.yaw) + Math.abs(readyBaseline.tilt) * 80) {
      readyBaseline = { ...head };
    }
    if (left > 0) {
      return;
    }
    settleBaseline(readyBaseline || head);
    return;
  }

  if (!canDetect) {
    return;
  }

  if (!settled) {
    if (!neutralSince) neutralSince = performance.now();
    const front = isNearFront(head);
    const waited = performance.now() - neutralSince >= START_FALLBACK_MS;
    if (!front && !waited) {
      neutralMisses += 1;
      if (neutralMisses <= 8) return;
      neutralStreak = 0;
      neutralMisses = 0;
      baseline = null;
      baselineReadyAt = 0;
      return;
    }
    if (!front && waited) {
      settleBaseline(head);
      return;
    }
    neutralMisses = 0;
    if (!baseline) {
      neutralStreak += 1;
      if (neutralStreak < NEUTRAL_FRAMES) return;
      baseline = { ...head };
      baselineReadyAt = performance.now() + BASELINE_HOLD_MS;
      matchStreak = 0;
      return;
    }
    if (performance.now() < baselineReadyAt) return;
    baseline = { ...head };
    settled = true;
    awaitingNeutral = false;
    poseConsumed = false;
    matchStreak = 0;
    return;
  }

  const delta = poseDelta(head, baseline);
  const matched = poseSucceeded(pose.id, delta, head);
  const yawPose = pose.id === "yaw-left" || pose.id === "yaw-right";
  if (matched) {
    matchStreak += 1;
    if (matchStreak >= (yawPose ? YAW_MATCH_FRAMES : MATCH_FRAMES)) {
      advancePose();
    }
  } else {
    matchStreak = 0;
  }
}
