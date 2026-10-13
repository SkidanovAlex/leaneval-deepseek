/-
# `Work.FTS.StrongGlobal.Step` — one step of the continuation of S5

This module contains the *step* of the continuation sequence of `Work.FTS.StrongGlobal.Seq`: from
an accumulated piece `g` solving the dynamic modulated problem on `[0, stepEnd δ n]` (with the
a-priori `ℋ⁴`-bound `C₀α²` and the `ℋ⁶`-bound `Kα²`), and a strong solution `Q` on
`[stepEnd δ n, stepEnd δ n + δ]` with `Q(·,·,stepEnd δ n) = slice g (stepEnd δ n)` (produced by the
local existence S1), the concatenation `concat g Q (stepEnd δ n)` is again an accumulated piece —
now on `[0, stepEnd δ (n+1)]`.

The three ingredients are

* the junction glue for the equation `Work.FTS.StrongGlobal.isDynGSolOnIcc_concat` (and its
  pointwise companions for the regularity class, `dynLin_congr`, `dynRHS_congr`);
* the junction glue for the joint `C¹`-regularity `contDiffOn_concat_union` below, whose two
  hypotheses are `Q(·,·,τ₀) = slice g τ₀` and the equality of the fake-time derivatives at the
  junction (`junction_deriv_eq`: both derivatives are the equation evaluated on the common slice at
  `τ₀`, and both exist two-sidedly because the pieces' `StrongSolOn.c1`-slabs have one unit of slack
  so that `τ₀` is interior to both);
* the a-priori bound **S4** (`apriori_strong`) and the persistence **S2** (`PersistStrong`), which
  give the two numerical bounds on `[0, stepEnd δ (n+1)]`.

The version of the `C¹`-glue used here holds on the *union* of the two slabs: the accumulated
piece's `C¹`-slab is anchored at `-1` (since its fake-time interval starts at `0`), while the new
piece's is anchored at `τ₀ - 1`, so neither slab contains the other and only the union covers the
accumulated one.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongGlobal.Seq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.StrongGlobal

open Work.FTS.Nonlin
open Work.FTS.Apriori
open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS)

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {α : ℝ} {Φs : Fn} {EllSol : Fn → Fn}

/-! ## The fake-time slice of a jointly `C¹` family -/

/-- If a family is jointly `C¹` at `(z,θ,τ)`, then its fake-time slice `τ' ↦ F z θ τ'` is
differentiable at `τ`. -/
theorem differentiableAt_slice_of_contDiffAt {F : Fam} {z θ τ : ℝ}
    (h : ContDiffAt ℝ 1 (uncurry3 F) (z, θ, τ)) : DifferentiableAt ℝ (fun s => F z θ s) τ := by
  have hc : HasDerivAt (fun s : ℝ => (z, θ, s)) ((0 : ℝ), (0 : ℝ), (1 : ℝ)) τ :=
    (hasDerivAt_const (c := z) (x := τ)).prodMk
      ((hasDerivAt_const (c := θ) (x := τ)).prodMk (hasDerivAt_id τ))
  have h1 := (h.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt τ hc
  have h2 : DifferentiableAt ℝ (uncurry3 F ∘ fun s : ℝ => (z, θ, s)) τ := h1.differentiableAt
  convert h2 using 1
  ext s
  rfl

/-! ## The junction equality of the fake-time derivatives -/

/-- **The fake-time derivatives of the two pieces agree at the junction.**  Both are the two-sided
derivative of the fake-time slice, and both are given by the equation evaluated on the common slice
`slice g τ₀ = slice Q τ₀` (the equation gives the *within*-`[0,τ₀]` (resp. `[τ₀,τ₀+δ]`) derivative,
and `deriv_eq_of_hasDerivWithinAt_Icc` identifies it with the two-sided one, which exists by the
`C¹`-field of the pieces). -/
theorem junction_deriv_eq {n : ℕ} {δ C₀ K : ℝ} {g₀ : Fn} {g Q : Fam} (hδ : 0 < δ)
    (hg : PieceData α Φs EllSol g₀ δ C₀ K n g)
    (hQdata : ∀ z θ, Q z θ (stepEnd δ n) = slice g (stepEnd δ n) z θ)
    (hQsol : StrongSolOn α Φs EllSol (stepEnd δ n) (stepEnd δ n + δ) Q) :
    ∀ z' θ', 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      deriv (fun s => g z' θ' s) (stepEnd δ n)
        = deriv (fun s => Q z' θ' s) (stepEnd δ n) := by
  have hτ₀nn : 0 ≤ stepEnd δ n := stepEnd_nonneg hδ n
  have hτ₀pos : 0 < stepEnd δ n := stepEnd_pos hδ n
  have hslice : slice g (stepEnd δ n) = slice Q (stepEnd δ n) := by
    funext z θ
    exact (hQdata z θ).symm
  intro z' θ' hz hθ hθ'
  set V : ℝ := dynLin α g (stepEnd δ n) z' θ'
    + dynRHS α (PsiCan Φs EllSol g) g (stepEnd δ n) z' θ' with hVdef
  have hVQ : V = dynLin α Q (stepEnd δ n) z' θ'
      + dynRHS α (PsiCan Φs EllSol Q) Q (stepEnd δ n) z' θ' := by
    rw [hVdef, dynLin_congr hslice, dynRHS_congr hslice]
  have hleft : deriv (fun s => g z' θ' s) (stepEnd δ n) = V := by
    have hVw : HasDerivWithinAt (fun s => g z' θ' s) V (Set.Icc 0 (stepEnd δ n))
        (stepEnd δ n) := by
      have h := hg.sol.eq z' θ' (stepEnd δ n) ⟨hτ₀nn, le_rfl⟩ ⟨hz, hθ, hθ'⟩
      rw [hVdef]
      exact h
    have hmem : (z', θ', stepEnd δ n) ∈ slab (0 - 1) (stepEnd δ n + 1) :=
      mem_slab.mpr ⟨hz, hθ, hθ', by linarith, by linarith⟩
    have hcat : ContDiffAt ℝ 1 (uncurry3 g) (z', θ', stepEnd δ n) :=
      (hg.sol.c1.contDiffWithinAt hmem).contDiffAt
        ((isOpen_slab _ _).mem_nhds hmem)
    exact deriv_eq_of_hasDerivWithinAt_Icc hτ₀pos ⟨hτ₀nn, le_rfl⟩ hVw
      (differentiableAt_slice_of_contDiffAt hcat)
  have hright : deriv (fun s => Q z' θ' s) (stepEnd δ n) = V := by
    have hVw : HasDerivWithinAt (fun s => Q z' θ' s) V (Set.Icc (stepEnd δ n) (stepEnd δ n + δ))
        (stepEnd δ n) := by
      have h := hQsol.eq z' θ' (stepEnd δ n) ⟨le_rfl, by linarith [hδ]⟩ ⟨hz, hθ, hθ'⟩
      rw [hVQ]
      exact h
    have hmem : (z', θ', stepEnd δ n) ∈ slab (stepEnd δ n - 1) ((stepEnd δ n + δ) + 1) :=
      mem_slab.mpr ⟨hz, hθ, hθ', by linarith, by linarith⟩
    have hcat : ContDiffAt ℝ 1 (uncurry3 Q) (z', θ', stepEnd δ n) :=
      (hQsol.c1.contDiffWithinAt hmem).contDiffAt ((isOpen_slab _ _).mem_nhds hmem)
    exact deriv_eq_of_hasDerivWithinAt_Icc (by linarith [hδ]) ⟨le_rfl, by linarith [hδ]⟩ hVw
      (differentiableAt_slice_of_contDiffAt hcat)
  rw [hleft, hright]

/-! ## The junction glue for `C¹` on the union of the two slabs -/

/-- The union of two slabs whose fake-time intervals overlap (`a' < b`, `a ≤ a'`, `b ≤ b'`) is a
single slab. -/
theorem slab_union_eq {a b a' b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') (hab : a' < b) :
    slab a b ∪ slab a' b' = slab a b' := by
  ext p
  constructor
  · rintro (hp | hp)
    · obtain ⟨h1, h2, h3, h4, h5⟩ := mem_slab.mp hp
      exact mem_slab.mpr ⟨h1, h2, h3, h4, lt_of_lt_of_le h5 hb⟩
    · obtain ⟨h1, h2, h3, h4, h5⟩ := mem_slab.mp hp
      exact mem_slab.mpr ⟨h1, h2, h3, lt_of_le_of_lt ha h4, h5⟩
  · intro hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := mem_slab.mp hp
    by_cases hxb : p.2.2 < b
    · exact Or.inl (mem_slab.mpr ⟨h1, h2, h3, h4, hxb⟩)
    · exact Or.inr (mem_slab.mpr ⟨h1, h2, h3, lt_of_lt_of_le hab (not_lt.mp hxb), h5⟩)

/-- Localisation of `ContDiffAt` to the concatenation, below the junction: the concatenation
agrees with `G` near `p`. -/
theorem contDiffWithinAt_concat_of_lt {G H : Fam} {τ₀ : ℝ} {s : Set P3} {p : P3}
    (hp : p.2.2 < τ₀) (hG : ContDiffAt ℝ 1 (uncurry3 G) p) :
    ContDiffWithinAt ℝ 1 (uncurry3 (concat G H τ₀)) s p := by
  have hmain : ContDiffWithinAt ℝ 1 (uncurry3 G) s p :=
    (contDiffWithinAt_univ.mpr hG).mono (Set.subset_univ _)
  refine hmain.congr_of_eventuallyEq ?_ ?_
  · show {y : P3 | uncurry3 (concat G H τ₀) y = uncurry3 G y} ∈ 𝓝[s] p
    rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [(isOpen_lt (continuous_snd.comp continuous_snd) continuous_const).mem_nhds hp] with q hq _
    change concat G H τ₀ q.1 q.2.1 q.2.2 = G q.1 q.2.1 q.2.2
    exact concat_apply_of_le (G := G) (H := H) (τ₀ := τ₀) (τ := q.2.2) (z := q.1)
      (θ := q.2.1) (le_of_lt hq)
  · change concat G H τ₀ p.1 p.2.1 p.2.2 = G p.1 p.2.1 p.2.2
    exact concat_apply_of_le (G := G) (H := H) (τ₀ := τ₀) (τ := p.2.2) (z := p.1)
      (θ := p.2.1) (le_of_lt hp)

/-- Localisation of `ContDiffAt` to the concatenation, above the junction: the concatenation
agrees with `H` near `p`. -/
theorem contDiffWithinAt_concat_of_gt {G H : Fam} {τ₀ : ℝ} {s : Set P3} {p : P3}
    (hp : τ₀ < p.2.2) (hH : ContDiffAt ℝ 1 (uncurry3 H) p) :
    ContDiffWithinAt ℝ 1 (uncurry3 (concat G H τ₀)) s p := by
  have hmain : ContDiffWithinAt ℝ 1 (uncurry3 H) s p :=
    (contDiffWithinAt_univ.mpr hH).mono (Set.subset_univ _)
  refine hmain.congr_of_eventuallyEq ?_ ?_
  · show {y : P3 | uncurry3 (concat G H τ₀) y = uncurry3 H y} ∈ 𝓝[s] p
    rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [(isOpen_lt continuous_const (continuous_snd.comp continuous_snd)).mem_nhds hp] with q hq _
    change concat G H τ₀ q.1 q.2.1 q.2.2 = H q.1 q.2.1 q.2.2
    exact concat_apply_of_gt (G := G) (H := H) (τ₀ := τ₀) (τ := q.2.2) (z := q.1)
      (θ := q.2.1) hq
  · change concat G H τ₀ p.1 p.2.1 p.2.2 = H p.1 p.2.1 p.2.2
    exact concat_apply_of_gt (G := G) (H := H) (τ₀ := τ₀) (τ := p.2.2) (z := p.1)
      (θ := p.2.1) hp

/-- **The junction glue for the joint `C¹`-regularity, on the *union* of the two slabs.**  Same
hypotheses as `Work.FTS.StrongGlobal.contDiffOn_concat_1`, but the conclusion holds on
`slab a b ∪ slab a' b'` — which is what the continuation needs, since the accumulated piece's
`C¹`-slab is anchored at `-1` while the new piece's is anchored at `τ₀ - 1`. -/
theorem contDiffOn_concat_union {G H : Fam} {τ₀ a b a' b' : ℝ}
    (hG : ContDiffOn ℝ 1 (uncurry3 G) (slab a b))
    (hH : ContDiffOn ℝ 1 (uncurry3 H) (slab a' b'))
    (ha : a ≤ a') (hb : b ≤ b') (hGa : a < τ₀) (hGb : τ₀ < b)
    (hHa : a' < τ₀) (hHb : τ₀ < b')
    (hval : ∀ z' θ', 0 < z' → 0 < θ' → θ' < Real.pi / 2 → G z' θ' τ₀ = H z' θ' τ₀)
    (hder : ∀ z' θ', 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      deriv (fun s => G z' θ' s) τ₀ = deriv (fun s => H z' θ' s) τ₀) :
    ContDiffOn ℝ 1 (uncurry3 (concat G H τ₀)) (slab a b ∪ slab a' b') := by
  intro p hp
  rcases hp with hp | hp
  · by_cases hlt : p.2.2 < τ₀
    · exact contDiffWithinAt_concat_of_lt hlt (hG.contDiffAt ((isOpen_slab a b).mem_nhds hp))
    · rcases lt_or_eq_of_le (le_of_not_gt hlt) with hgt | heq
      · obtain ⟨h1, h2, h3, _, h5⟩ := mem_slab.mp hp
        have hp' : p ∈ slab a' b' :=
          mem_slab.mpr ⟨h1, h2, h3, lt_trans hHa hgt, lt_of_lt_of_le h5 hb⟩
        exact contDiffWithinAt_concat_of_gt hgt
          (hH.contDiffAt ((isOpen_slab a' b').mem_nhds hp'))
      · obtain ⟨h1, h2, h3, _, _⟩ := mem_slab.mp hp
        have hpt : (p.1, p.2.1, τ₀) = p := Prod.ext rfl (Prod.ext rfl heq)
        refine (contDiffWithinAt_univ.mpr ?_).mono (Set.subset_univ _)
        rw [← hpt]
        exact contDiffAt_concat_junction hG hH hGa hGb hHa hHb hval hder h1 h2 h3
  · by_cases hlt : p.2.2 < τ₀
    · obtain ⟨h1, h2, h3, h4, _⟩ := mem_slab.mp hp
      have hp' : p ∈ slab a b :=
        mem_slab.mpr ⟨h1, h2, h3, lt_of_le_of_lt ha h4, lt_trans hlt hGb⟩
      exact contDiffWithinAt_concat_of_lt hlt (hG.contDiffAt ((isOpen_slab a b).mem_nhds hp'))
    · rcases lt_or_eq_of_le (le_of_not_gt hlt) with hgt | heq
      · exact contDiffWithinAt_concat_of_gt hgt
          (hH.contDiffAt ((isOpen_slab a' b').mem_nhds hp))
      · obtain ⟨h1, h2, h3, _, _⟩ := mem_slab.mp hp
        have hpt : (p.1, p.2.1, τ₀) = p := Prod.ext rfl (Prod.ext rfl heq)
        refine (contDiffWithinAt_univ.mpr ?_).mono (Set.subset_univ _)
        rw [← hpt]
        exact contDiffAt_concat_junction hG hH hGa hGb hHa hHb hval hder h1 h2 h3

/-! ## One step of the continuation -/

/-- **One step of the continuation**: if `g` is an accumulated piece on `[0, stepEnd δ n]` and `Q`
a strong solution on `[stepEnd δ n, stepEnd δ n + δ]` starting from `slice g (stepEnd δ n)`, then
the concatenation is an accumulated piece on `[0, stepEnd δ (n+1)]`. -/
theorem concat_piece_spec {IP : ℝ → Fn → Fn → ℝ} {α₂ cc clo Cup Ccs CcN α₄ K δ C₀ : ℝ}
    {g₀ : Fn} (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hCcN : 0 < CcN) (hα₄ : 0 < α₄)
    (hα : 0 < α) (hα5 : α ≤ alpha5 CcN cc clo Cup Ccs α₂ α₄) (hδ : 0 < δ)
    (hPersist : PersistStrong α Φs EllSol (C0 CcN cc clo Cup Ccs) K)
    (hEnergy : EnergyId IP α Φs EllSol) (hPair : PairBndStrong IP α CcN Φs EllSol)
    (hXn4₀ : Xn α g₀ ≤ α ^ 2) (hXn6₀ : Xn6 α g₀ ≤ K * α ^ 2)
    (n : ℕ) (g Q : Fam) (hg : PieceData α Φs EllSol g₀ δ (C0 CcN cc clo Cup Ccs) K n g)
    (hQdata : ∀ z θ, Q z θ (stepEnd δ n) = slice g (stepEnd δ n) z θ)
    (hQsol : StrongSolOn α Φs EllSol (stepEnd δ n) (stepEnd δ n + δ) Q) :
    PieceData α Φs EllSol g₀ δ (C0 CcN cc clo Cup Ccs) K (n + 1)
      (concat g Q (stepEnd δ n)) := by
  have hτ₀nn : 0 ≤ stepEnd δ n := stepEnd_nonneg hδ n
  have hle : 0 ≤ stepEnd δ n + δ := by linarith [hτ₀nn, hδ]
  have hag : ∀ z θ, g z θ (stepEnd δ n) = Q z θ (stepEnd δ n) := fun z θ => (hQdata z θ).symm
  have hsol : StrongSolOn α Φs EllSol 0 (stepEnd δ n + δ) (concat g Q (stepEnd δ n)) := by
    have hglue := isDynGSolOnIcc_concat (α := α) (a := 0) (τ₀ := stepEnd δ n)
      (b := stepEnd δ n + δ) (Φs := Φs) (EllSol := EllSol) (G := g) (H := Q)
      hτ₀nn (by linarith [hτ₀nn, hδ]) hg.sol.toSol hQsol.toSol hag
    have hder : ∀ z' θ', 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
        deriv (fun s => g z' θ' s) (stepEnd δ n)
          = deriv (fun s => Q z' θ' s) (stepEnd δ n) :=
      junction_deriv_eq hδ hg hQdata hQsol
    have hc1 := contDiffOn_concat_union (G := g) (H := Q) (τ₀ := stepEnd δ n) (a := 0 - 1)
      (b := stepEnd δ n + 1) (a' := stepEnd δ n - 1) (b' := stepEnd δ n + δ + 1)
      hg.sol.c1 hQsol.c1 (by linarith) (by linarith [hδ]) (by linarith) (by linarith)
      (by linarith) (by linarith [hδ])
      (fun z' θ' _ _ _ => (hQdata z' θ').symm) hder
    rw [slab_union_eq (a := 0 - 1) (b := stepEnd δ n + 1) (a' := stepEnd δ n - 1)
      (b' := stepEnd δ n + δ + 1) (by linarith) (by linarith [hδ]) (by linarith [hδ])] at hc1
    refine ⟨hle, hglue.2, hglue.1, ?_, hc1, ?_, ?_⟩
    · intro τ hτ
      by_cases h : τ ≤ stepEnd δ n
      · rw [slice_concat_of_le h]
        exact hg.sol.gal τ ⟨hτ.1, h⟩
      · rw [slice_concat_of_gt (not_le.mp h)]
        exact hQsol.gal τ ⟨(not_le.mp h).le, hτ.2⟩
    · intro τ hτ
      by_cases h : τ ≤ stepEnd δ n
      · rw [dynLin_congr (slice_concat_of_le h)]
        exact hg.sol.regLin τ ⟨hτ.1, h⟩
      · rw [dynLin_congr (slice_concat_of_gt (not_le.mp h))]
        exact hQsol.regLin τ ⟨(not_le.mp h).le, hτ.2⟩
    · intro τ hτ
      by_cases h : τ ≤ stepEnd δ n
      · rw [dynRHS_congr (slice_concat_of_le h)]
        exact hg.sol.regRHS τ ⟨hτ.1, h⟩
      · rw [dynRHS_congr (slice_concat_of_gt (not_le.mp h))]
        exact hQsol.regRHS τ ⟨(not_le.mp h).le, hτ.2⟩
  have hdata : ∀ z θ, concat g Q (stepEnd δ n) z θ 0 = g₀ z θ := by
    intro z θ
    rw [concat_apply_of_le hτ₀nn]
    exact hg.data z θ
  have hsl0 : slice (concat g Q (stepEnd δ n)) 0 = g₀ := by
    funext z θ
    exact hdata z θ
  have hbnd4 : ∀ τ ∈ Set.Icc 0 (stepEnd δ n + δ),
      Xn α (slice (concat g Q (stepEnd δ n)) τ) ≤ C0 CcN cc clo Cup Ccs * α ^ 2 := by
    refine apriori_strong IP hIP hCcN hα₄ hα hα5 hle hsol ?_ ?_ ?_
    · exact hEnergy (concat g Q (stepEnd δ n)) (stepEnd δ n + δ) hle hsol
    · exact hPair (concat g Q (stepEnd δ n)) (stepEnd δ n + δ) hle hsol
    · rw [hsl0]; exact hXn4₀
  have hbnd6 : ∀ τ ∈ Set.Icc 0 (stepEnd δ n + δ),
      Xn6 α (slice (concat g Q (stepEnd δ n)) τ) ≤ K * α ^ 2 := by
    refine hPersist.2 (concat g Q (stepEnd δ n)) (stepEnd δ n + δ) hle hsol hbnd4 ?_
    rw [hsl0]; exact hXn6₀
  have hsol' : StrongSolOn α Φs EllSol 0 (stepEnd δ (n + 1)) (concat g Q (stepEnd δ n)) := by
    rw [stepEnd_succ]; exact hsol
  have hbnd4' : ∀ τ ∈ Set.Icc 0 (stepEnd δ (n + 1)),
      Xn α (slice (concat g Q (stepEnd δ n)) τ) ≤ C0 CcN cc clo Cup Ccs * α ^ 2 := by
    rw [stepEnd_succ]; exact hbnd4
  have hbnd6' : ∀ τ ∈ Set.Icc 0 (stepEnd δ (n + 1)),
      Xn6 α (slice (concat g Q (stepEnd δ n)) τ) ≤ K * α ^ 2 := by
    rw [stepEnd_succ]; exact hbnd6
  exact ⟨hdata, hsol', hbnd4', hbnd6'⟩

/-! ## The step function -/

/-- The family obtained at the `(n+1)`-st step from the accumulated piece `g`. -/
noncomputable def stepFam {α₀ K δ C₀ : ℝ} {g₀ : Fn}
    (hLWP : LWPStrong α Φs EllSol α₀ K δ) (hα : 0 < α) (hαα₀ : α ≤ α₀)
    (n : ℕ) (g : Fam) (hg : PieceData α Φs EllSol g₀ δ C₀ K n g) : Fam :=
  concat g (lwpPiece hLWP hα hαα₀ g n
    (hg.sol.reg6 (stepEnd δ n) ⟨stepEnd_nonneg hLWP.1 n, le_rfl⟩)
    (hg.bnd6 (stepEnd δ n) ⟨stepEnd_nonneg hLWP.1 n, le_rfl⟩)) (stepEnd δ n)

/-- The specification of `stepFam`: it produces the next accumulated piece. -/
theorem stepFam_spec {IP : ℝ → Fn → Fn → ℝ} {α₂ cc clo Cup Ccs CcN α₄ α₀ K δ C₀ : ℝ}
    {g₀ : Fn} (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hCcN : 0 < CcN) (hα₄ : 0 < α₄)
    (hα : 0 < α) (hα5 : α ≤ alpha5 CcN cc clo Cup Ccs α₂ α₄) (hαα₀ : α ≤ α₀)
    (hLWP : LWPStrong α Φs EllSol α₀ K δ)
    (hPersist : PersistStrong α Φs EllSol (C0 CcN cc clo Cup Ccs) K)
    (hEnergy : EnergyId IP α Φs EllSol) (hPair : PairBndStrong IP α CcN Φs EllSol)
    (hXn4₀ : Xn α g₀ ≤ α ^ 2) (hXn6₀ : Xn6 α g₀ ≤ K * α ^ 2)
    (n : ℕ) (g : Fam) (hg : PieceData α Φs EllSol g₀ δ (C0 CcN cc clo Cup Ccs) K n g) :
    PieceData α Φs EllSol g₀ δ (C0 CcN cc clo Cup Ccs) K (n + 1)
      (stepFam (Φs := Φs) (EllSol := EllSol) hLWP hα hαα₀ n g hg) := by
  have hδ : 0 < δ := hLWP.1
  have hspec := lwpPiece_spec (Φs := Φs) (EllSol := EllSol) hLWP hα hαα₀ g n
    (hg.sol.reg6 (stepEnd δ n) ⟨stepEnd_nonneg hδ n, le_rfl⟩)
    (hg.bnd6 (stepEnd δ n) ⟨stepEnd_nonneg hδ n, le_rfl⟩)
  have hfun : stepFam (Φs := Φs) (EllSol := EllSol) (C₀ := C0 CcN cc clo Cup Ccs)
      hLWP hα hαα₀ n g hg
      = concat g (lwpPiece hLWP hα hαα₀ g n
          (hg.sol.reg6 (stepEnd δ n) ⟨stepEnd_nonneg hδ n, le_rfl⟩)
          (hg.bnd6 (stepEnd δ n) ⟨stepEnd_nonneg hδ n, le_rfl⟩)) (stepEnd δ n) := rfl
  rw [hfun]
  exact concat_piece_spec (C₀ := C0 CcN cc clo Cup Ccs) hIP hCcN hα₄ hα hα5 hδ hPersist
    hEnergy hPair hXn4₀ hXn6₀ n g _ hg hspec.1 hspec.2

end Work.FTS.StrongGlobal
