/-
# GATE2 / EXL — the minimal real crossing of the ray lift, and the crossing-only (W)

`Work.GATE2.EXL.exitLoop_exists` consumes the **crossing-only** no-dip condition

    hno' : Im (gamma_1 (s_0 - 1 + t)) = 0  ->  x_0 - 3/2 < Re (gamma_1 (s_0 - 1 + t))

on the fundamental piece `gamma_1 '' [s_0 - 1, s_0]` of a real crossing `gamma_1 s_0 = (x_0 : C)`.
This module shows that `hno'` and the confinement `Re < C` are **free**, provided the lift has a
real crossing at all: choose `s_0` to be an integer translate of the crossing that **minimises the
`1`-periodic shape function** `h s := Re (gamma_1 s) - s`.

* `exists_minCrossing`: such an `sMin` exists (compactness on one period, then periodicity).
* `re_sub_add_int`: `h` is invariant under `s |-> s + k`, `k : Z` (so is `Im gamma_1`).
* `hno'_of_minCrossing`: for *every* integer translate `s_0 = sMin + k` one has the crossing-only
  no-dip condition.  Indeed a crossing `s ∈ [s_0 - 1, s_0]` has `h s >= h sMin = h s_0`, hence
  `Re (gamma_1 s) = h s + s >= h s_0 + s_0 - 1 = x_0 - 1 > x_0 - 3/2`.
* `re_lt_of_minCrossing`: for the same translate, `Re (gamma_1 (s_0 - 1 + t)) < C` for all
  `t ∈ [0,1]` as soon as `sMin + k + liftOsc L < C` — in particular the confinement follows by
  taking `k` very negative (then the crossing `x_0` is deep as well).

So on the ray lift the whole exit loop is unconditional once the lift meets the real axis; the
remaining case is exactly case (ii) of the design's dichotomy, where it does not.
-/
import Submission.Work.GATE2.EXL.Lift

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2.EXL

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-- **The `1`-periodic shape function is invariant under integer translations.** -/
theorem re_sub_add_int {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) (s : ℝ) (k : ℤ) :
    (L.γ₁ (s + (k : ℝ))).re - (s + (k : ℝ)) = (L.γ₁ s).re - s := by
  have h := Work.ELRig.periodicShift_translate L.γ₁ L.per₁ k s
  rw [h, Complex.add_re, Complex.intCast_re]; ring

/-- **`Im gamma_1` is invariant under integer translations.** -/
theorem im_add_int {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) (s : ℝ) (k : ℤ) :
    (L.γ₁ (s + (k : ℝ))).im = (L.γ₁ s).im := by
  have h := Work.ELRig.periodicShift_translate L.γ₁ L.per₁ k s
  rw [h, Complex.add_im, Complex.intCast_im, add_zero]

/-- The shape function is `1`-periodic: `h (fract s) = h s`. -/
theorem re_sub_fract {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) (s : ℝ) :
    (L.γ₁ (Int.fract s)).re - Int.fract s = (L.γ₁ s).re - s := by
  have h := Work.ELRig.periodicShift_translate L.γ₁ L.per₁ ⌊s⌋ (Int.fract s)
  rw [Int.fract_add_floor] at h
  have h1 : (L.γ₁ s).re = (L.γ₁ (Int.fract s)).re + (⌊s⌋ : ℝ) := by
    rw [h, Complex.add_re, Complex.intCast_re]
  have hs : s = Int.fract s + (⌊s⌋ : ℝ) := (Int.fract_add_floor s).symm
  linarith

/-- The `fract` of a real point of the lift is again a real point of the lift, in `[0,1]`. -/
theorem fract_mem_of_im_eq_zero {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) {s : ℝ} (hs : (L.γ₁ s).im = 0) :
    Int.fract s ∈ Set.Icc (0 : ℝ) 1 ∧ (L.γ₁ (Int.fract s)).im = 0 := by
  refine ⟨⟨Int.fract_nonneg s, le_of_lt (Int.fract_lt_one s)⟩, ?_⟩
  have him : (L.γ₁ s).im = (L.γ₁ (Int.fract s)).im := by
    have h := Work.ELRig.periodicShift_translate L.γ₁ L.per₁ ⌊s⌋ (Int.fract s)
    rw [Int.fract_add_floor] at h
    rw [h, Complex.add_im, Complex.intCast_im, add_zero]
  rw [← him]; exact hs

/-- **The crossing that minimises the shape function `h s = Re (gamma_1 s) - s`.**  Exists whenever
the lift has a real point: `Im gamma_1` and `h` are `1`-periodic and continuous, so `h` attains its
minimum on the nonempty compact set of crossings in one period. -/
theorem exists_minCrossing {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) (h0 : ∃ s : ℝ, (L.γ₁ s).im = 0) :
    ∃ sMin : ℝ, (L.γ₁ sMin).im = 0 ∧
      ∀ s : ℝ, (L.γ₁ s).im = 0 → (L.γ₁ sMin).re - sMin ≤ (L.γ₁ s).re - s := by
  set S : Set ℝ := {s : ℝ | s ∈ Set.Icc (0 : ℝ) 1 ∧ (L.γ₁ s).im = 0} with hS
  have hsub : S ⊆ Set.Icc (0 : ℝ) 1 := fun s hs => hs.1
  have hclosed : IsClosed S :=
    isClosed_Icc.inter (isClosed_eq (Complex.continuous_im.comp L.cont₁) continuous_const)
  have hcomp : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed hsub
  obtain ⟨s₀, hs₀⟩ := h0
  have hne : S.Nonempty := ⟨Int.fract s₀, fract_mem_of_im_eq_zero L hs₀⟩
  have hf : ContinuousOn (fun s : ℝ => (L.γ₁ s).re - s) S :=
    ((Complex.continuous_re.comp L.cont₁).sub continuous_id).continuousOn
  obtain ⟨sMin, hsMinS, hmin⟩ := hcomp.exists_isMinOn hne hf
  refine ⟨sMin, hsMinS.2, fun s hs => ?_⟩
  have hle : (L.γ₁ sMin).re - sMin ≤ (L.γ₁ (Int.fract s)).re - Int.fract s :=
    hmin (fract_mem_of_im_eq_zero L hs)
  rwa [re_sub_fract L s] at hle

/-- **The crossing-only no-dip condition at every integer translate of the minimal crossing.** -/
theorem hno'_of_minCrossing {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) {sMin : ℝ} (hsMinim : (L.γ₁ sMin).im = 0)
    (hmin : ∀ s : ℝ, (L.γ₁ s).im = 0 → (L.γ₁ sMin).re - sMin ≤ (L.γ₁ s).re - s)
    (k : ℤ) :
    (L.γ₁ (sMin + (k : ℝ))).im = 0 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, (L.γ₁ (sMin + (k : ℝ) - 1 + t)).im = 0 →
        (L.γ₁ (sMin + (k : ℝ))).re - 3 / 2 < (L.γ₁ (sMin + (k : ℝ) - 1 + t)).re := by
  refine ⟨by rw [im_add_int L sMin k, hsMinim], fun t ht htim => ?_⟩
  have h1 : (L.γ₁ (sMin + (k : ℝ))).re - (sMin + (k : ℝ)) = (L.γ₁ sMin).re - sMin :=
    re_sub_add_int L sMin k
  have h0 := hmin (sMin + (k : ℝ) - 1 + t) htim
  have ht0 : 0 ≤ t := ht.1
  linarith

/-- **The confinement at an integer translate of the minimal crossing.**  `Re (gamma_1 s) <=
liftOsc L + s`, and `s <= sMin + k` on the fundamental piece, so the piece lies below
`liftOsc L + sMin + k`; taking `k` very negative makes this `< C`, and makes the crossing
`x_0 = Re (gamma_1 (sMin + k))` deep. -/
theorem re_lt_of_minCrossing {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) {sMin : ℝ} (k : ℤ) {C : ℝ}
    (hC : sMin + (k : ℝ) + liftOsc L < C) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, (L.γ₁ (sMin + (k : ℝ) - 1 + t)).re < C := by
  intro t ht
  have h := lift_re_le L (sMin + (k : ℝ) - 1 + t)
  have ht1 : t ≤ 1 := ht.2
  linarith

/-- **Case (i) of the design's dichotomy is *closed*: a real crossing of the lift produces both exit
loops, unconditionally.**

If the lift `gamma_1` has a real point, then (with `sMin` the crossing minimising the shape
function and `k` an integer chosen so that `sMin + k` is deep) the centre
`y_0 := Re (gamma_1 (sMin + k))` is a **real leak point off `K c_0`** (it lies on the `alpha_1`-ray
by `RayCylLift.img_1`), and there are exit loops at `y_0` (angle `alpha_1`) and at `y_0 + 1/2`
(angle `alpha_2`).  No `no-dip`, no confinement and no depth hypothesis remains: the crossing is
chosen by `exists_minCrossing` and translated by `k` (`hno'_of_minCrossing`,
`re_lt_of_minCrossing`). -/
theorem exists_exitLoop_of_realCrossing {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁)
    (Lray : Work.ELRig.RayCylLift d fl)
    (h0 : ∃ s : ℝ, (Lray.γ₁ s).im = 0) :
    ∃ y₀ : ℝ, y₀ < -(3 / 2 : ℝ) ∧ fl.Ψ ((y₀ : ℝ) : ℂ) ∉ Work.EL.K c₀ ∧
      (∃ R : ℝ, 0 < R ∧ ∀ r₀ ∈ Set.Ioc (0 : ℝ) R, ∀ v : ℝ,
        Nonempty (Work.GATE2.ExitLoop c₀ fl.Ψ y₀ r₀ v Work.EL.alpha1)) ∧
      (∃ R : ℝ, 0 < R ∧ ∀ r₀ ∈ Set.Ioc (0 : ℝ) R, ∀ v : ℝ,
        Nonempty (Work.GATE2.ExitLoop c₀ fl.Ψ (y₀ + 1 / 2) r₀ v Work.EL.alpha2)) := by
  obtain ⟨sMin, hsMinim, hmin⟩ := exists_minCrossing Lray h0
  set k : ℤ := ⌊(-(3 / 2 : ℝ) - liftOsc Lray - sMin)⌋ - 1 with hkdef
  have hk : sMin + (k : ℝ) + liftOsc Lray < -(3 / 2 : ℝ) := by
    have h1 : ((⌊(-(3 / 2 : ℝ) - liftOsc Lray - sMin)⌋ : ℤ) : ℝ)
        ≤ -(3 / 2 : ℝ) - liftOsc Lray - sMin := Int.floor_le _
    have h2 : ((k : ℤ) : ℝ) = ((⌊(-(3 / 2 : ℝ) - liftOsc Lray - sMin)⌋ : ℤ) : ℝ) - 1 := by
      simp [hkdef]
    linarith
  have him : (Lray.γ₁ (sMin + (k : ℝ))).im = 0 := by
    rw [im_add_int Lray sMin k, hsMinim]
  set y₀ : ℝ := (Lray.γ₁ (sMin + (k : ℝ))).re with hy₀def
  have hγ1 : Lray.γ₁ (sMin + (k : ℝ)) = ((y₀ : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [hy₀def]
    · simpa using him
  have hK1 : fl.Ψ ((y₀ : ℝ) : ℂ) ∉ Work.EL.K c₀ := by
    rw [← hγ1]
    exact Work.EL.paramRay_subset_compl d.hN Work.EL.alpha1 (Lray.img₁ _)
  have hreC : ∀ t ∈ Set.Icc (0 : ℝ) 1, (Lray.γ₁ (sMin + (k : ℝ) - 1 + t)).re < -(3 / 2 : ℝ) :=
    re_lt_of_minCrossing Lray k hk
  have hre1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, (Lray.γ₁ (sMin + (k : ℝ) - 1 + t)).re < -1 :=
    fun t ht => by linarith [hreC t ht]
  have hno1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, (Lray.γ₁ (sMin + (k : ℝ) - 1 + t)).im = 0 →
      y₀ - 3 / 2 < (Lray.γ₁ (sMin + (k : ℝ) - 1 + t)).re := by
    have h := (hno'_of_minCrossing Lray hsMinim hmin k).2
    simpa [hy₀def] using h
  obtain ⟨R₁, hR₁, hgen₁⟩ := exitLoop_at_relaxed fl Lray hγ1 hre1 hno1
  -- the `iota` tongue
  have hγ2 : Lray.γ₂ (sMin + (k : ℝ)) = (((y₀ + 1 / 2 : ℝ)) : ℂ) := by
    rw [Lray.anti, hγ1]
    simp
  have hre2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, (Lray.γ₂ (sMin + (k : ℝ) - 1 + t)).re < -1 := by
    intro t ht
    have h := hreC t ht
    have h2 : (Lray.γ₂ (sMin + (k : ℝ) - 1 + t)).re
        = (Lray.γ₁ (sMin + (k : ℝ) - 1 + t)).re + 1 / 2 := by
      rw [Lray.anti]; simp
    linarith
  have hno2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, (Lray.γ₂ (sMin + (k : ℝ) - 1 + t)).im = 0 →
      (y₀ + 1 / 2) - 3 / 2 < (Lray.γ₂ (sMin + (k : ℝ) - 1 + t)).re := by
    intro t ht him2
    have him1 : (Lray.γ₁ (sMin + (k : ℝ) - 1 + t)).im = 0 := by
      have h2 : (Lray.γ₂ (sMin + (k : ℝ) - 1 + t)).im
          = -(Lray.γ₁ (sMin + (k : ℝ) - 1 + t)).im := by rw [Lray.anti]; simp
      rw [h2] at him2; linarith
    have h2 : (Lray.γ₂ (sMin + (k : ℝ) - 1 + t)).re
        = (Lray.γ₁ (sMin + (k : ℝ) - 1 + t)).re + 1 / 2 := by rw [Lray.anti]; simp
    have h := hno1 t ht him1
    linarith
  obtain ⟨R₂, hR₂, hgen₂⟩ := exitLoop_iota_at_relaxed fl Lray hγ2 hre2 hno2
  have hy₀deep : y₀ < -(3 / 2 : ℝ) := by
    have h := lift_re_le Lray (sMin + (k : ℝ))
    rw [hγ1] at h
    simp only [Complex.ofReal_re] at h
    linarith
  exact ⟨y₀, hy₀deep, hK1, ⟨R₁, hR₁, hgen₁⟩, ⟨R₂, hR₂, hgen₂⟩⟩

end Work.GATE2.EXL
