import Mathlib
import Submission.Work.WilC4aP.SqDefs
import Submission.Work.WilC4aP.exists_local_factorization
import Submission.Work.WilC4aP.exists_ball_injective
import Submission.Work.WilC4aP.eval_prod_X_sub_C_eq_zero_iff
import Submission.Work.WilC4aP.eq_of_root_and_closest
import Submission.Work.WilC4aP.injective_of_prod_X_sub_C
import Submission.Work.WilC4aP.isOpen_sheet

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators

namespace Work.WilC4aP

open Polynomial

/-- The projection of the root space onto the punctured disk is a local homeomorphism: near a
point `(z₀, α)` the root space is the graph of the local branch `η k` of
`Work.WilC4aP.exists_local_factorization`.

PROOF HINT: given `e` with base `z₀ ∈ puncDisk r`, let `α = e.1.2`; it is a simple root of
`Pz P z₀`, so `exists_local_factorization` gives `ρ` and holomorphic `η : Fin m → ℂ → ℂ` with
`Pz P z = ∏ j, (X - C (η j z))` on `ball z₀ ρ`. Pick `k` with `η k z₀ = α`. Let `ρ'` be a
positive radius at which the `η j` are still pointwise injective (`exists_ball_injective`),
smaller than `ρ` and smaller than `r - ‖z₀‖` (possible since `z₀ ∈ puncDisk r`). Take
`φ := OpenPartialHomeomorph` with `toFun = rootProj P r R`,
`source = {e' | ‖e'.1.1 - z₀‖ < ρ' ∧ ∀ i ≠ k, ‖e'.1.2 - η i e'.1.1‖ > ‖e'.1.2 - η k e'.1.1‖}`,
`target = Metric.ball z₀ ρ'`, and `invFun z = (z, η k z)` (junk outside `target`). Then
`Set.EqOn (rootProj P r R) φ φ.source` holds and `IsLocalHomeomorphOn.mk` applies. The condition
"`Y` is strictly closer to `η k z` than to any other `η i z`" picks out exactly the sheet
`{Y = η k z}` because on the ball every root equals some `η i z` (by the factorization) and the
`η i z` are injective in `i`. `‖η k z‖ ≤ R` on the ball follows from `hRroot`. -/
theorem isLocalHomeomorphOn_rootProj {m : ℕ} (P : Polynomial (ℂ → ℂ)) (hmon : P.Monic)
    (hdeg : P.natDegree = m) {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hRroot : ∀ z : ℂ, ‖z‖ ≤ r → ∀ α : ℂ, (Work.WilC4aP.Pz P z).eval α = 0 → ‖α‖ ≤ R)
    (hcont : ∀ z : ℂ, z ∈ Metric.closedBall (0 : ℂ) r → Work.WilC4aP.HolCoeffs P z)
    (hsep : Work.WilC4aP.SimpleRootsOn P (Work.WilC4aP.puncDisk r)) :
    IsLocalHomeomorphOn (Work.WilC4aP.rootProj P r R)
      (Work.WilC4aP.rootProj P r R ⁻¹' Work.WilC4aP.puncDisk r) := by
  classical
  refine IsLocalHomeomorphOn.mk _ _ fun x hx => ?_
  -- `x : ↥(RootSpace P r R)` and `hx : rootProj P r R x ∈ puncDisk r`
  have hz0 : x.1.1 ∈ puncDisk r := by simpa [rootProj_apply] using hx
  have hz2 : ‖x.1.1‖ < r := hz0.2
  have hclosed : x.1.1 ∈ Metric.closedBall (0 : ℂ) r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using le_of_lt hz2
  have han : HolCoeffs P x.1.1 := hcont _ hclosed
  have hsimple : ∀ w : ℂ, (Pz P x.1.1).eval w = 0 → (Pz P x.1.1).derivative.eval w ≠ 0 :=
    hsep _ hz0
  obtain ⟨ρ, η, hρ, hηan, hfac⟩ :=
    exists_local_factorization P hmon hdeg x.1.1 han hsimple
  have hfac0 : Pz P x.1.1 = ∏ j : Fin m, (Polynomial.X - Polynomial.C (η j x.1.1)) :=
    hfac _ (Metric.mem_ball_self hρ)
  have hroot0 : (Pz P x.1.1).eval x.1.2 = 0 := rootEval_zero P x
  -- the branch passing through the point
  obtain ⟨k, hk⟩ : ∃ k : Fin m, x.1.2 = η k x.1.1 := by
    have h : (∏ j : Fin m, (Polynomial.X - Polynomial.C (η j x.1.1))).eval x.1.2 = 0 := by
      rw [← hfac0]; exact hroot0
    exact (eval_prod_X_sub_C_eq_zero_iff _ _).mp h
  have hinj0 : Function.Injective (fun j : Fin m => η j x.1.1) :=
    injective_of_prod_X_sub_C (monic_Pz hmon x.1.1) hfac0 hsimple
  have hηcont : ∀ j : Fin m, ContinuousAt (η j) x.1.1 :=
    fun j => (hηan j x.1.1 (Metric.mem_ball_self hρ)).continuousAt
  obtain ⟨ρI, hρI, hinjI⟩ := exists_ball_injective hηcont hinj0
  have hrpos : 0 < r - ‖x.1.1‖ := sub_pos.mpr hz2
  set ρ' : ℝ := min ρ (min ρI (r - ‖x.1.1‖)) with hρ'def
  have hρ'pos : 0 < ρ' := lt_min hρ (lt_min hρI hrpos)
  have hρ'ρ : ρ' ≤ ρ := min_le_left _ _
  have hρ'ρI : ρ' ≤ ρI := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ'r : ρ' ≤ r - ‖x.1.1‖ := le_trans (min_le_right _ _) (min_le_right _ _)
  -- the local model
  set tgt : Set ℂ := Metric.ball x.1.1 ρ' with htgtdef
  set S : Set (ℂ × ℂ) := {q : ℂ × ℂ | ‖q.1 - x.1.1‖ < ρ' ∧
      ∀ i, i ≠ k → ‖q.2 - η i q.1‖ > ‖q.2 - η k q.1‖} with hSdef
  set src : Set ↥(RootSpace P r R) := Subtype.val ⁻¹' S with hsrcdef
  have hS_open : IsOpen S := by
    rw [hSdef]
    exact isOpen_sheet (fun j => (hηan j).continuousOn) hρ'ρ
  have hsrc_open : IsOpen src := by
    rw [hsrcdef]; exact hS_open.preimage continuous_subtype_val
  have htgt_open : IsOpen tgt := by rw [htgtdef]; exact Metric.isOpen_ball
  -- the (partial) inverse: `z ↦ (z, η k z)`, junk outside `tgt`
  have hwf : ∀ z : ℂ, z ∈ tgt → (z, η k z) ∈ RootSpace P r R := by
    intro z hz
    have hzt : ‖z - x.1.1‖ < ρ' := by
      have := hz; rw [htgtdef, Metric.mem_ball, dist_eq_norm] at this; exact this
    have hzρ : z ∈ Metric.ball x.1.1 ρ := by
      rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hzt hρ'ρ
    have hzr : ‖z‖ ≤ r := by
      have h1 : ‖z‖ ≤ ‖x.1.1‖ + ‖z - x.1.1‖ := by
        have hz' : z = x.1.1 + (z - x.1.1) := by ring
        calc ‖z‖ = ‖x.1.1 + (z - x.1.1)‖ := congrArg (fun w : ℂ => ‖w‖) hz'
          _ ≤ ‖x.1.1‖ + ‖z - x.1.1‖ := norm_add_le _ _
      have h2 : ‖x.1.1‖ + ρ' ≤ r := by linarith [hρ'r]
      linarith
    have hroot : (Pz P z).eval (η k z) = 0 := by
      rw [hfac z hzρ, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
    refine ⟨⟨?_, ?_⟩, hroot⟩
    · simpa [Metric.mem_closedBall, dist_eq_norm] using hzr
    · simpa [Metric.mem_closedBall, dist_eq_norm] using hRroot z hzr (η k z) hroot
  let invF : ℂ → ↥(RootSpace P r R) :=
    fun z => if hz : z ∈ tgt then ⟨(z, η k z), hwf z hz⟩ else x
  have hmem_src_iff : ∀ y : ↥(RootSpace P r R), y ∈ src ↔
      (‖y.1.1 - x.1.1‖ < ρ' ∧
        ∀ i, i ≠ k → ‖y.1.2 - η i y.1.1‖ > ‖y.1.2 - η k y.1.1‖) := by
    intro y; rw [hsrcdef]; rfl
  have hmap_source : ∀ y : ↥(RootSpace P r R), y ∈ src → rootProj P r R y ∈ tgt := by
    intro y hy
    have hy1 : ‖y.1.1 - x.1.1‖ < ρ' := ((hmem_src_iff y).mp hy).1
    rw [htgtdef, Metric.mem_ball, dist_eq_norm]
    simpa [rootProj_apply] using hy1
  have hmap_target : ∀ z : ℂ, z ∈ tgt → invF z ∈ src := by
    intro z hz
    have hzt : ‖z - x.1.1‖ < ρ' := by
      have := hz; rw [htgtdef, Metric.mem_ball, dist_eq_norm] at this; exact this
    have hinjz : Function.Injective (fun j : Fin m => η j z) := by
      apply hinjI z
      rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hzt hρ'ρI
    have hinv : invF z = ⟨(z, η k z), hwf z hz⟩ := dif_pos hz
    rw [hmem_src_iff, hinv]
    refine ⟨hzt, ?_⟩
    intro i hi
    have hne : η k z ≠ η i z := fun h => hi (hinjz h.symm)
    simp only [Subtype.coe_mk]
    rw [sub_self, norm_zero]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hleft_inv : ∀ y : ↥(RootSpace P r R), y ∈ src → invF (rootProj P r R y) = y := by
    intro y hy
    have hy1 : ‖y.1.1 - x.1.1‖ < ρ' := ((hmem_src_iff y).mp hy).1
    have hy2 : ∀ i, i ≠ k → ‖y.1.2 - η i y.1.1‖ > ‖y.1.2 - η k y.1.1‖ :=
      ((hmem_src_iff y).mp hy).2
    have hyt : rootProj P r R y ∈ tgt := hmap_source y hy
    have hzρ : y.1.1 ∈ Metric.ball x.1.1 ρ := by
      rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hy1 hρ'ρ
    have hyk : y.1.2 = η k y.1.1 :=
      eq_of_root_and_closest (hfac y.1.1 hzρ) (rootEval_zero P y) hy2
    have h2 : (⟨(rootProj P r R y, η k (rootProj P r R y)), hwf _ hyt⟩ :
        ↥(RootSpace P r R)) = y := by
      apply Subtype.ext
      show (rootProj P r R y, η k (rootProj P r R y)) = y.1
      rw [rootProj_apply]
      exact Prod.ext rfl hyk.symm
    calc invF (rootProj P r R y)
        = ⟨(rootProj P r R y, η k (rootProj P r R y)), hwf _ hyt⟩ := dif_pos hyt
      _ = y := h2
  have hright_inv : ∀ z : ℂ, z ∈ tgt → rootProj P r R (invF z) = z := by
    intro z hz
    have hinv : invF z = ⟨(z, η k z), hwf z hz⟩ := dif_pos hz
    rw [hinv, rootProj_apply]
  have hcont_inv : ContinuousOn invF tgt := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : tgt.domRestrict invF =
        (fun z : tgt => (⟨(z.1, η k z.1), hwf z.1 z.2⟩ : ↥(RootSpace P r R))) := by
      funext z
      rw [Set.domRestrict_apply]
      exact dif_pos z.2
    rw [heq]
    refine Continuous.subtype_mk (f := fun z : tgt => ((z.1, η k z.1) : ℂ × ℂ)) ?_ ?_
    · refine Continuous.prodMk continuous_subtype_val ?_
      have hηc : ContinuousOn (η k) (Metric.ball x.1.1 ρ) := (hηan k).continuousOn
      have hsub : tgt ⊆ Metric.ball x.1.1 ρ := by
        rw [htgtdef]; exact Metric.ball_subset_ball hρ'ρ
      exact continuousOn_iff_continuous_domRestrict.mp (hηc.mono hsub)
  let e : OpenPartialHomeomorph ↥(RootSpace P r R) ℂ :=
    { toFun := rootProj P r R
      invFun := invF
      source := src
      target := tgt
      map_source' := hmap_source
      map_target' := hmap_target
      left_inv' := hleft_inv
      right_inv' := hright_inv
      continuousOn_toFun := (continuous_rootProj P r R).continuousOn
      continuousOn_invFun := hcont_inv
      open_source := hsrc_open
      open_target := htgt_open }
  refine ⟨e, ?_, ?_⟩
  · show x ∈ src
    rw [hmem_src_iff]
    refine ⟨?_, ?_⟩
    · rw [sub_self, norm_zero]; exact hρ'pos
    · intro i hi
      have hne : η k x.1.1 ≠ η i x.1.1 := fun h => hi (hinj0 h.symm)
      rw [hk, sub_self, norm_zero]
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  · intro y _
    rfl

end Work.WilC4aP
