/-
# GATE2 / EXL — the equator tail lies in the near side, from `Im γ₁ ≠ 0`

`Work.ELRig.htail_of_flip` (`Work.ELRig.ParityMain`) proves, from the hypothesis
`hE : ∀ x, fl.Ψ x ∈ K c` (the equator is contained in the filled Julia set), that the far-left
real tail of `Ψ` lies in the *near* side of the `α`-pair `nest.P0`.  The hypothesis `hE` enters
its proof in exactly two places:

* `exists_tail_one_side` — the far-left tail of the lift `γ₁` is connected and avoids the real
  axis, so it lies in one open half plane.  It uses `hE` only through `RayCylLift.hreal_of` to
  know that `γ₁` (and `γ₂`) miss the real axis;
* `side_constant_left` — the side of `Ψ` on the far-left real axis is locally constant, which
  needs the real points off the pair curve.  Again `hE` is used only to show that a real point of
  the pair curve would have to be `z₁` (via `pairCurve_inter_K_subset`) and `Ψ` misses `z₁` there;
  without `hE` the same conclusion follows from `TailId₁`/`TailId₂` (`Ψ`-preimages of the two root
  rays are the lifts) as soon as the lifts miss the real axis.

This file proves the corresponding statements from the strictly weaker hypothesis

    `hmiss : ∀ s, (L.γ₁ s).im ≠ 0`   (the lift misses the real axis; `γ₂` misses it too, since
    `γ₂ s = star (γ₁ s) + 1/2`),

and then repeats the crossing-parity argument of `htail_of_flip` verbatim with these two
replacements — no `hE`, no `K c`, no Jordan form.
-/
import Mathlib
import Submission.Work.ELRig.ParityMain
import Submission.Work.ELRig.TailBand
import Submission.Work.ELRig.CylLift

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

namespace Work.GATE2.EXL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c : ℂ} {d : Work.EL.RootParabolic c}
variable {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}

/-! ## The far-left tail of the lift lies in one open half plane -/

/-- **The tail of the first lift lies in one of the open half planes.**  The tail
`γ₁ ((-∞, s₁])` is connected and, by the hypothesis that the lift misses the real axis, contained
in `{0 < Im} ∪ {Im < 0}`; the two are open and disjoint, so the tail lies in one of them.  This is
`Work.ELRig.exists_tail_one_side` with the hypothesis `Im (γ₁ s) ≠ 0` (instead of
`E ⊆ K c`). -/
theorem exists_tail_one_side_ne (L : Work.ELRig.RayCylLift d fl)
    (hmiss : ∀ s : ℝ, (L.γ₁ s).im ≠ 0) :
    ∃ s₁ ε₁ : ℝ, (ε₁ = 1 ∨ ε₁ = -1) ∧ ∀ s : ℝ, s ≤ s₁ → 0 < ε₁ * (L.γ₁ s).im := by
  refine ⟨0, ?_⟩
  have hconn : IsPreconnected (L.γ₁ '' Set.Iic (0 : ℝ)) :=
    (convex_Iic (0 : ℝ)).isPreconnected.image _ L.cont₁.continuousOn
  have hsub : L.γ₁ '' Set.Iic (0 : ℝ) ⊆ {z : ℂ | 0 < z.im} ∪ {z : ℂ | z.im < 0} := by
    rintro z ⟨s, -, rfl⟩
    rcases lt_trichotomy (L.γ₁ s).im 0 with h | h | h
    · exact Or.inr h
    · exact absurd h (hmiss s)
    · exact Or.inl h
  have hdisj : (L.γ₁ '' Set.Iic (0 : ℝ)) ∩ ({z : ℂ | 0 < z.im} ∩ {z : ℂ | z.im < 0}) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨-, h1, h2⟩
    simp only [Set.mem_ofPred_eq] at h1 h2
    linarith
  have hopen₁ : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hopen₂ : IsOpen {z : ℂ | z.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  rcases isPreconnected_iff_subset_of_disjoint.mp hconn {z : ℂ | 0 < z.im} {z : ℂ | z.im < 0}
    hopen₁ hopen₂ hsub hdisj with h | h
  · exact ⟨1, Or.inl rfl, fun s hs => by simpa using h ⟨s, hs, rfl⟩⟩
  · exact ⟨-1, Or.inr rfl, fun s hs => by
      have h' := h ⟨s, hs, rfl⟩
      simp only [Set.mem_ofPred_eq] at h'
      show 0 < -1 * (L.γ₁ s).im
      linarith⟩

/-! ## The real points off the pair curve -/

/-- **The far-left real points lie off the pair curve.**  A `Ψ`-preimage of the pair curve in the
far-left half plane is on the pair curve, i.e. (`mem_pairCurve_iff`) on one of the two root rays or
equal to the landing point `z₁`; the two rays have their `Ψ`-preimages on the lifts (`TailId₁`,
`TailId₂`), which miss the real axis (`hmiss`, and `Im γ₂ = -Im γ₁`), and `z₁` is never hit
(`hzne`). -/
theorem notMem_pairCurve_of_real (L : Work.ELRig.RayCylLift d fl)
    (P : Work.EL.CoPair d.hN) (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2)
    (hPy : P.y = d.z₁)
    (hmiss : ∀ s : ℝ, (L.γ₁ s).im ≠ 0) {y : ℝ} (hy : y < -L.R) :
    fl.Ψ (y : ℂ) ∉ Work.EL.pairCurve P := by
  have hre : ((y : ℂ)).re < -L.R := by simpa using hy
  intro hmem
  rw [Work.EL.mem_pairCurve_iff] at hmem
  rcases hmem with h | hy' | h
  · rw [hPa] at h
    obtain ⟨s, hs⟩ := L.tailId₁ (y : ℂ) hre h
    have him : (L.γ₁ s).im = 0 := by rw [hs]; simp
    exact hmiss s him
  · rw [hPy] at hy'
    exact L.hzne (y : ℂ) hre hy'
  · rw [hPb] at h
    obtain ⟨s, hs⟩ := L.tailId₂ (y : ℂ) hre h
    have him : (L.γ₁ s).im = 0 := by
      have h1 := congrArg Complex.im hs
      rw [Work.ELRig.im_γ₂] at h1
      simpa using h1
    exact hmiss s him

/-- **The side of `Ψ` on the far-left real axis is constant** — from the lift missing the real
axis.  The real points `y < -R` are off the pair curve (`notMem_pairCurve_of_real`), so the
function `y ↦` side of `Ψ y` is locally constant on the connected set `(-∞, -R)`; one instance
gives all of them.  This is `Work.ELRig.side_constant_left` without the hypothesis `E ⊆ K c`. -/
theorem side_constant_left_ne (L : Work.ELRig.RayCylLift d fl)
    (P : Work.EL.CoPair d.hN) (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2)
    (hPy : P.y = d.z₁) (hside : Work.EL.PairSides d.hN P)
    (hmiss : ∀ s : ℝ, (L.γ₁ s).im ≠ 0) {x x' : ℝ} (hx : x < -L.R) (hx' : x' < -L.R)
    (hxne : fl.Ψ (x : ℂ) ∈ Work.EL.pairSideNear P) :
    fl.Ψ (x' : ℂ) ∈ Work.EL.pairSideNear P := by
  have hcont : Continuous (fun y : ℝ => fl.Ψ (y : ℂ)) :=
    fl.Ψ_diff.continuous.comp Complex.continuous_ofReal
  have hnotcurve : ∀ y : ℝ, y < -L.R → fl.Ψ (y : ℂ) ∉ Work.EL.pairCurve P :=
    fun y hy => notMem_pairCurve_of_real L P hPa hPb hPy hmiss hy
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

/-! ## The equator tail lies in the near side -/

/-- **The equator tail lies in the near side of the `α`-pair, from the lift missing the real
axis.**  This is `Work.ELRig.htail_of_flip` with the hypothesis `E ⊆ K c` replaced by the weaker
`∀ s, Im (γ₁ s) ≠ 0`: the crossing-parity argument produces `Ψ x₀ ∈ pairSideNear P` for a far-left
level `x₀`, and `side_constant_left_ne` propagates it to the whole far-left real tail. -/
theorem htail_of_ne {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (nest : Work.EL.Z1Nest d.hN d.z₁ fl.Pa)
    (L : Work.ELRig.RayCylLift d fl)
    (han : ∀ n : ℤ, AnalyticOn ℝ (fun s : ℝ => L.γ₁ s) (Set.Ioo (n : ℝ) ((n : ℝ) + 1)))
    (hflip : Work.ELRig.FlipHyp fl nest.P0 L)
    (hmiss : ∀ s : ℝ, (L.γ₁ s).im ≠ 0) :
    ∃ R' : ℝ, ∀ x : ℝ, x < -R' → fl.Ψ ((x : ℂ)) ∈ Work.EL.pairSideNear nest.P0 := by
  obtain ⟨R₀, hR₀R, hγ⟩ := L.hγtail
  obtain ⟨M, hM⟩ := Work.ELRig.re_sub_bounded L
  obtain ⟨s₁, ε₁, hε₁, hsign⟩ := exists_tail_one_side_ne L hmiss
  obtain ⟨x₀, hx₀lt, hodd, htrans⟩ :=
    Work.ELRig.odd_transversal_level L.cont₁ L.per₁ han (R := max L.R (M - s₁) + 1)
  have hx₀LR : x₀ < -L.R := by
    have h1 : L.R ≤ max L.R (M - s₁) := le_max_left _ _
    linarith
  have hxM : x₀ + M ≤ s₁ := by
    have h1 : M - s₁ ≤ max L.R (M - s₁) := le_max_right _ _
    linarith
  have hxM₂ : x₀ - 1 / 2 + M ≤ s₁ := by linarith
  have hmem₁ : ∀ s : ℝ, (L.γ₁ s).re = x₀ → s ≤ s₁ :=
    fun s hs => Work.ELRig.le_of_crossing L hM hxM hs
  have hmem₂ : ∀ s : ℝ, (L.γ₁ s).re = x₀ - 1 / 2 → s ≤ s₁ :=
    fun s hs => Work.ELRig.le_of_crossing L hM hxM₂ hs
  have hband1 : ∀ s : ℝ, (L.γ₁ s).re = x₀ → |(L.γ₁ s).im| ≤ R₀ :=
    fun s hs => Work.ELRig.band₁ L hR₀R hγ (by rw [hs]; exact hx₀LR)
  have hpos : ∀ s : ℝ, (L.γ₁ s).re = x₀ → 0 < ε₁ * (L.γ₁ s).im :=
    fun s hs => hsign s (hmem₁ s hs)
  have hsep : ∀ t : ℝ, 0 ≤ ε₁ * t → ε₁ * t ≤ R₀ + 1 →
      (((x₀ : ℂ) + t * Complex.I) ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ ↔
        ∃ s : ℝ, (L.γ₁ s).re = x₀ ∧ t = (L.γ₁ s).im) :=
    fun t h1 _ => Work.ELRig.segment_sep L hsign hmem₂ t h1
  have hflip₀ : ∀ s : ℝ, (L.γ₁ s).re = x₀ → ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε →
      ((x₀ : ℂ) + ((L.γ₁ s).im + δ) * Complex.I) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ →
      ((x₀ : ℂ) + ((L.γ₁ s).im - δ) * Complex.I) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ →
      ((fl.Ψ ((x₀ : ℂ) + ((L.γ₁ s).im + δ) * Complex.I) ∈ Work.EL.pairSide nest.P0 ∧
        fl.Ψ ((x₀ : ℂ) + ((L.γ₁ s).im - δ) * Complex.I) ∈ Work.EL.pairSideNear nest.P0) ∨
       (fl.Ψ ((x₀ : ℂ) + ((L.γ₁ s).im + δ) * Complex.I) ∈ Work.EL.pairSideNear nest.P0 ∧
        fl.Ψ ((x₀ : ℂ) + ((L.γ₁ s).im - δ) * Complex.I) ∈ Work.EL.pairSide nest.P0)) :=
    fun s hs => hflip x₀ hx₀LR s hs (htrans s hs)
  have hfin : ({s : ℝ | (L.γ₁ s).re = x₀}).Finite := by
    by_contra hf
    rw [Set.not_finite] at hf
    rw [hf.ncard] at hodd
    exact absurd hodd (by rintro ⟨k, hk⟩; omega)
  have hnear : fl.Ψ (x₀ : ℂ) ∈ Work.EL.pairSideNear nest.P0 :=
    Work.ELRig.exists_pairSideNear_of_crossingOdd d fl nest.P0 nest.P0_spec.1 nest.P0_spec.2.1
      nest.P0_spec.2.2 nest.sides_P0 L nest.Pa_far hx₀LR hR₀R hγ (Work.ELRig.injective₁ L) hfin hodd
      hε₁ hpos hband1 hsep hflip₀
  exact ⟨L.R, fun x hx => side_constant_left_ne L nest.P0 nest.P0_spec.1 nest.P0_spec.2.1
    nest.P0_spec.2.2 nest.sides_P0 hmiss hx₀LR hx hnear⟩

end Work.GATE2.EXL
