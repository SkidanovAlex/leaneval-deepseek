/-
# ELRig — the band bound, the tail, and the vertical-segment separation

This file contains the elementary *geometry of the lift curve* `L.γ₁` in the repelling
coordinate that R-a3 (`equatorTail_mem_near`, and its parity form
`Work.ELRig.exists_pairSideNear_of_crossingOdd`) consumes:

* **`band₁`/`band₂`** — the lift stays inside the horizontal band `|Im| ≤ R₀` of the far-left
  half plane.  If `|Im (γ₁ s)| > R₀` and `Re (γ₁ s) < -R`, then `Ψ (γ₁ s) ∈ Pa` (the flower's
  `Ψ_ends`, recorded as `hγ`), but `Ψ (γ₁ s)` lies on the external ray `R(α₁)`, which is
  disjoint from `K c ⊇ Pa`.  This is the reason why *every* crossing of a far-left vertical line
  with the lift lies in the band.
* **`re_sub_bounded`** — `s ↦ Re (γ₁ s) - s` is `1`-periodic and continuous, hence bounded:
  `Re (γ₁ s) = s + O(1)`.  Consequently all crossings of the level `Re = x₀` lie in the window
  `[-x₀ - M, -x₀ + M]`, i.e. on the *tail* of the lift when `-x₀` is large.
* **`exists_tail_one_side`** — the tail `γ₁ ((-∞, s₁])` (which lies in `Re < -R`) is connected
  and misses the real axis (under `hE : E ⊆ K`, by `RayCylLift.hreal_of`), hence lies entirely
  in one of the two open half planes; `0 < ε₁ · Im (γ₁ s)` for all `s ≤ s₁`.
* **`segment_sep`** — combining the last two: the vertical segment
  `{x₀ + i t | 0 ≤ ε₁ t ≤ R₀ + 1}` meets the two lifts *exactly* at the `γ₁`-crossings of the
  level `x₀`.  In particular the `γ₂`-crossings of that level (which sit at height `-ε₁`) are off
  the segment, and `t = 0` is off both lifts.
* **`side_constant_left`** — under `hE` the side of `Ψ` on the far-left real axis is locally
  constant, hence constant: `Ψ (x) ∈ pairSideNear P` for one `x < -R` gives it for all.
-/
import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.Inputs
import Submission.Work.ELRig.Sides
import Submission.Work.ELRig.Flower
import Submission.Work.ELRig.exists_liftCurvesV2
import Submission.Work.ELRig.odd_transversal_level

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.ELRig

open Work.EL
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c : ℂ} {d : Work.EL.RootParabolic c}
variable {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}

/-! ## The lift stays in the band `|Im| ≤ R₀` -/

/-- **The first lift stays inside the band.**  If `Re (γ₁ s) < -R` and `|Im (γ₁ s)| > R₀`, then
`Ψ (γ₁ s) ∈ Pa ⊆ K c` (the flower's `Ψ_ends`), contradicting `Ψ (γ₁ s) ∈ R(α₁) ⊆ (K c)ᶜ`. -/
theorem band₁ (L : RayCylLift d fl) {R₀ : ℝ} (hRR₀ : R₀ < L.R)
    (hγ : ∀ w : ℂ, w.re < -R₀ → R₀ < |w.im| → fl.Ψ w ∈ fl.Pa) {s : ℝ}
    (hs : (L.γ₁ s).re < -L.R) : |(L.γ₁ s).im| ≤ R₀ := by
  by_contra h
  rw [not_le] at h
  have hre : (L.γ₁ s).re < -R₀ := by linarith
  exact (Work.EL.paramRay_subset_compl d.hN Work.EL.alpha1 (L.img₁ s))
    (Work.EL.Pa_subset_K' fl (hγ _ hre h))

/-- **The second lift stays inside the band.** -/
theorem band₂ (L : RayCylLift d fl) {R₀ : ℝ} (hRR₀ : R₀ < L.R)
    (hγ : ∀ w : ℂ, w.re < -R₀ → R₀ < |w.im| → fl.Ψ w ∈ fl.Pa) {s : ℝ}
    (hs : (L.γ₂ s).re < -L.R) : |(L.γ₂ s).im| ≤ R₀ := by
  by_contra h
  rw [not_le] at h
  have hre : (L.γ₂ s).re < -R₀ := by linarith
  exact (Work.EL.paramRay_subset_compl d.hN Work.EL.alpha2 (L.img₂ s))
    (Work.EL.Pa_subset_K' fl (hγ _ hre h))

/-! ## `Re ∘ γ₁ = id + O(1)` -/

/-- **The real part of the lift grows like the parameter.**  `s ↦ Re (γ₁ s) - s` is `1`-periodic
and continuous, hence bounded. -/
theorem re_sub_bounded (L : RayCylLift d fl) :
    ∃ M : ℝ, ∀ s : ℝ, |(L.γ₁ s).re - s| ≤ M := by
  have hper : Function.Periodic (fun s : ℝ => (L.γ₁ s).re - s) 1 := by
    intro s
    show (L.γ₁ (s + 1)).re - (s + 1) = (L.γ₁ s).re - s
    rw [L.per₁ s, Complex.add_re, Complex.one_re]
    ring
  have hcont : Continuous (fun s : ℝ => (L.γ₁ s).re - s) :=
    (Complex.continuous_re.comp L.cont₁).sub continuous_id
  have hb := hper.isBounded_of_continuous (by norm_num) hcont
  obtain ⟨C, hC⟩ := Metric.isBounded_range_iff.mp hb
  refine ⟨C + |(L.γ₁ 0).re|, fun s => ?_⟩
  have h0 : dist ((L.γ₁ s).re - s) ((L.γ₁ 0).re - 0) ≤ C := hC s 0
  rw [Real.dist_eq] at h0
  calc |(L.γ₁ s).re - s|
      = |(((L.γ₁ s).re - s) - ((L.γ₁ 0).re - 0)) + ((L.γ₁ 0).re - 0)| := by ring_nf
    _ ≤ |((L.γ₁ s).re - s) - ((L.γ₁ 0).re - 0)| + |(L.γ₁ 0).re - 0| := abs_add_le _ _
    _ = |((L.γ₁ s).re - s) - ((L.γ₁ 0).re - 0)| + |(L.γ₁ 0).re| := by rw [sub_zero]
    _ ≤ C + |(L.γ₁ 0).re| := add_le_add h0 le_rfl

/-- **All crossings of a far-left level lie in the window `[x₀ - M, x₀ + M]`.** -/
theorem le_of_crossing (L : RayCylLift d fl) {M x₀ s₁ : ℝ}
    (hM : ∀ s : ℝ, |(L.γ₁ s).re - s| ≤ M) (hx : x₀ + M ≤ s₁) {s : ℝ}
    (hs : (L.γ₁ s).re = x₀) : s ≤ s₁ := by
  have h1 : s ≤ (L.γ₁ s).re + M := by
    have h2 := (abs_le.mp (hM s)).1
    linarith
  rw [hs] at h1
  linarith

/-! ## The lift is injective -/

/-- **The first lift is injective** (a ray point determines its level: `rayPt_level_inj`). -/
theorem injective₁ (L : RayCylLift d fl) : ∀ s s' : ℝ, L.γ₁ s = L.γ₁ s' → s = s' := by
  intro s s' h
  refine L.hτmono.injective (Work.ELRig.rayPt_level_inj (θ := Work.EL.alpha1) d.hN (L.hτ1 s) (L.hτ1 s') ?_)
  rw [← L.hΨ₁ s, ← L.hΨ₁ s', h]

/-! ## The tail of the lift lies in one half plane -/

/-- **The far-left tail of the lift lies in one of the open half planes.**  The tail
`γ₁ ((-∞, s₁])` lies in `{Re < -R}`, where the lift avoids the real axis
(`RayCylLift.hreal_of`); being connected, it lies on one side of it. -/
theorem exists_tail_one_side (L : RayCylLift d fl)
    (hE : ∀ x : ℝ, fl.Ψ (x : ℂ) ∈ Work.EL.K c) :
    ∃ s₁ ε₁ : ℝ, (ε₁ = 1 ∨ ε₁ = -1) ∧ ∀ s : ℝ, s ≤ s₁ → 0 < ε₁ * (L.γ₁ s).im := by
  obtain ⟨M, hM⟩ := re_sub_bounded L
  set s₁ : ℝ := -L.R - M - 1 with hs₁
  have htail : ∀ s : ℝ, s ≤ s₁ → (L.γ₁ s).re < -L.R := by
    intro s hs
    have h1 : (L.γ₁ s).re ≤ s + M := by
      have h2 := (abs_le.mp (hM s)).2
      linarith
    rw [hs₁] at hs
    linarith
  have havoid : ∀ s : ℝ, s ≤ s₁ → (L.γ₁ s).im ≠ 0 := by
    intro s hs him
    have hre := htail s hs
    have hreal : ((L.γ₁ s).re : ℂ) = L.γ₁ s := by
      apply Complex.ext <;> simp [him]
    exact L.hreal_of hE ((L.γ₁ s).re) hre (Or.inl ⟨s, hreal.symm⟩)
  have hconn : IsPreconnected (L.γ₁ '' Set.Iic s₁) :=
    (convex_Iic s₁).isPreconnected.image _ L.cont₁.continuousOn
  have hsub : L.γ₁ '' Set.Iic s₁ ⊆ {z : ℂ | 0 < z.im} ∪ {z : ℂ | z.im < 0} := by
    rintro z ⟨s, hs, rfl⟩
    rcases lt_trichotomy (L.γ₁ s).im 0 with h | h | h
    · exact Or.inr h
    · exact absurd h (havoid s hs)
    · exact Or.inl h
  have hdisj : (L.γ₁ '' Set.Iic s₁) ∩ ({z : ℂ | 0 < z.im} ∩ {z : ℂ | z.im < 0}) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨-, h1, h2⟩
    simp only [Set.mem_ofPred_eq] at h1 h2
    linarith
  have hopen₁ : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hopen₂ : IsOpen {z : ℂ | z.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  rcases isPreconnected_iff_subset_of_disjoint.mp hconn {z : ℂ | 0 < z.im} {z : ℂ | z.im < 0}
    hopen₁ hopen₂ hsub hdisj with h | h
  · exact ⟨s₁, 1, Or.inl rfl, fun s hs => by
      simpa using h ⟨s, hs, rfl⟩⟩
  · exact ⟨s₁, -1, Or.inr rfl, fun s hs => by
      have h' := h ⟨s, hs, rfl⟩
      simp only [Set.mem_ofPred_eq] at h'
      show 0 < -1 * (L.γ₁ s).im
      linarith⟩

/-! ## The real and imaginary parts of the second lift -/

/-- The real part of the second lift is the real part of the first, shifted by `1/2`. -/
theorem re_γ₂ (L : RayCylLift d fl) (s : ℝ) : (L.γ₂ s).re = (L.γ₁ s).re + 1 / 2 := by
  rw [L.anti s]
  simp

/-- The imaginary part of the second lift is the negative of that of the first. -/
theorem im_γ₂ (L : RayCylLift d fl) (s : ℝ) : (L.γ₂ s).im = -((L.γ₁ s).im) := by
  rw [L.anti s]
  simp

/-! ## The vertical segment meets the pair curve exactly at the `γ₁`-crossings -/

/-- **The separation of the vertical segment.**  Let `x₀ < -R`, let `ε₁ = ±1`, let the tail of
`γ₁` lie on the `ε₁`-side of the real axis (`htail`), and let the `γ₁`-crossings of the level
`x₀ - 1/2` also lie on the tail (`hmem₂`, from `le_of_crossing`).  Then for `t` with
`0 ≤ ε₁ t` the point `x₀ + i t` is in one of the two lifts if and only if it is one of the
`γ₁`-crossings of the level `x₀`.  In particular the `γ₂`-crossings of the level `x₀` (which sit
at height `-Im (γ₁ s)` with `s` on the tail, hence at `ε₁`-negative height) are off the segment. -/
theorem segment_sep (L : RayCylLift d fl) {x₀ ε₁ s₁ : ℝ}
    (htail : ∀ s : ℝ, s ≤ s₁ → 0 < ε₁ * (L.γ₁ s).im)
    (hmem₂ : ∀ s : ℝ, (L.γ₁ s).re = x₀ - 1 / 2 → s ≤ s₁) :
    ∀ t : ℝ, 0 ≤ ε₁ * t →
      (((x₀ : ℂ) + t * Complex.I) ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ ↔
        ∃ s : ℝ, (L.γ₁ s).re = x₀ ∧ t = (L.γ₁ s).im) := by
  intro t ht0
  constructor
  · rintro (⟨s, hs⟩ | ⟨s, hs⟩)
    · have h0 : (L.γ₁ s).re = x₀ := by
        have h := congrArg Complex.re hs
        simpa using h
      refine ⟨s, h0, ?_⟩
      have h := congrArg Complex.im hs
      simpa using h.symm
    · exfalso
      have hre : (L.γ₁ s).re = x₀ - 1 / 2 := by
        have h1 := congrArg Complex.re hs
        rw [re_γ₂] at h1
        have h2 : (L.γ₁ s).re + 1 / 2 = x₀ := by simpa using h1
        linarith
      have him := htail s (hmem₂ s hre)
      have ht : t = (L.γ₂ s).im := by
        have h := congrArg Complex.im hs
        simpa using h.symm
      rw [ht, im_γ₂, mul_neg] at ht0
      linarith
  · rintro ⟨s, hs, ht⟩
    refine Or.inl ⟨s, ?_⟩
    rw [ht]
    apply Complex.ext
    · simpa using hs
    · simp

/-! ## The side of `Ψ` on the far-left real axis is constant -/

/-- **The side of the equator on the far-left real axis is constant.**  Under `E ⊆ K` the real
points `x < -R` are off the pair curve, so the function `x ↦` side of `Ψ (x)` is locally constant
and defined on the connected set `(-∞, -R)`; hence one instance gives all of them. -/
theorem side_constant_left {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (P : Work.EL.CoPair d.hN) (hPy : P.y = d.z₁) (hside : Work.EL.PairSides d.hN P)
    (L : RayCylLift d fl) (hE : ∀ x : ℝ, fl.Ψ (x : ℂ) ∈ Work.EL.K c)
    {x x' : ℝ} (hx : x < -L.R) (hx' : x' < -L.R)
    (hxne : fl.Ψ (x : ℂ) ∈ Work.EL.pairSideNear P) :
    fl.Ψ (x' : ℂ) ∈ Work.EL.pairSideNear P := by
  have hcont : Continuous (fun y : ℝ => fl.Ψ (y : ℂ)) :=
    fl.Ψ_diff.continuous.comp Complex.continuous_ofReal
  have hnotcurve : ∀ y : ℝ, y < -L.R → fl.Ψ (y : ℂ) ∉ Work.EL.pairCurve P := by
    intro y hy hmem
    have hK : fl.Ψ (y : ℂ) ∈ Work.EL.K c := hE y
    have hmem' := Work.EL.pairCurve_inter_K_subset (hN := d.hN) (P := P) ⟨hmem, hK⟩
    have hz1 : fl.Ψ (y : ℂ) = d.z₁ := by simpa [hPy] using hmem'
    have hre : (y : ℂ).re < -L.R := by simpa using hy
    exact L.hzne (y : ℂ) hre hz1
  have hU : IsOpen {y : ℝ | fl.Ψ (y : ℂ) ∈ Work.EL.pairSide P} :=
    hside.isOpen_far.preimage hcont
  have hV : IsOpen {y : ℝ | fl.Ψ (y : ℂ) ∈ Work.EL.pairSideNear P} :=
    hside.isOpen_near.preimage hcont
  have hsub : Set.Iio (-L.R) ⊆ {y : ℝ | fl.Ψ (y : ℂ) ∈ Work.EL.pairSide P} ∪
      {y : ℝ | fl.Ψ (y : ℂ) ∈ Work.EL.pairSideNear P} := by
    intro y hy
    rcases hside.mem_or_mem (hnotcurve y hy) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hdisj : Set.Iio (-L.R) ∩
      ({y : ℝ | fl.Ψ (y : ℂ) ∈ Work.EL.pairSide P} ∩
       {y : ℝ | fl.Ψ (y : ℂ) ∈ Work.EL.pairSideNear P}) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨-, h1, h2⟩
    exact (Set.disjoint_left.mp hside.disjoint h1) h2
  have hconn : IsPreconnected (Set.Iio (-L.R)) := (convex_Iio (-L.R)).isPreconnected
  rcases isPreconnected_iff_subset_of_disjoint.mp hconn _ _ hU hV hsub hdisj with h | h
  · exact absurd (h (Set.mem_Iio.mpr hx))
      (fun hf => (Set.disjoint_left.mp hside.disjoint hf) hxne)
  · exact h (Set.mem_Iio.mpr hx')

end Work.ELRig
