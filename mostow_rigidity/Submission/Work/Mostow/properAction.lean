import Mathlib
import Submission.Work.Mostow.nearStabDefs
import Submission.Work.Mostow.abs_mat_le_tpart_actO
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.HaarBase

/-!
# Properness of the action of a discrete subgroup of `PO n 1`

`Work.Mostow.properAction`: for a discrete subgroup `Γ ≤ PO n 1`, a point `u₀` and a compact
subset `K` of the chart space `E n`, only finitely many `γ ∈ Γ` have `γ • u₀ ∈ K`.

The argument is the standard properness of the orbit map `g ↦ g • u₀`, made explicit:

* the set of `g : PO n 1` with `hdist 0 (g • 0) ≤ R` is contained in the compact set
  `matBallToPO n (cosh (max R 0))` (because a representing matrix of such a `g` has all its
  entries bounded by `tpart (g • 0) ≤ cosh R`, `abs_mat_le_tpart_actO`), and
* a discrete subgroup of a Hausdorff topological group meets every compact set finitely
  (`Subgroup.tendsto_coe_cofinite_of_isDiscrete`).

To reduce an arbitrary `u₀` and compact `K` to the near-stabiliser of the origin, translate by
`γ`: if `γ • u₀ ∈ K` for `γ ∈ Γ` then `hdist 0 (γ • 0)` is bounded by the diameter of `K` plus
`hdist 0 u₀`, using that `γ` acts by isometries.
-/

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow MeasureTheory
open scoped Topology
open Matrix

/-- A compact subset of the chart space is contained in a norm ball. -/
lemma exists_norm_le_of_isCompact {n : ℕ} {K : Set (E n)} (hK : IsCompact K) :
    ∃ M : ℝ, ∀ x ∈ K, ‖x‖ ≤ M := by
  obtain ⟨r, hr⟩ := Metric.isBounded_iff_subset_closedBall (0 : E n) |>.1 hK.isBounded
  exact ⟨r, fun x hx => by
    have h := hr hx
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h⟩

/-- The set `matBall n C` of matrices with entries bounded by `C` and satisfying the two
`O(n,1)`-relations is compact. -/
theorem matBall_compact (n : ℕ) (C : ℝ) : IsCompact (matBall n C) := by
  have h1 : IsClosed {A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ | ∀ i j, |A i j| ≤ C} := by
    rw [show {A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ | ∀ i j, |A i j| ≤ C}
        = ⋂ i, ⋂ j, {A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ | |A i j| ≤ C}
        from by ext A; simp]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_Iic.preimage (continuous_abs.comp (continuous_apply_apply i j))
  have h2 : IsClosed {A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ | Aᵀ * pmOneMat * A = pmOneMat} :=
    isClosed_singleton.preimage (by fun_prop)
  have h3 : IsClosed {A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ | A * pmOneMat * Aᵀ = pmOneMat} :=
    isClosed_singleton.preimage (by fun_prop)
  have hclosed : IsClosed (matBall n C) := by
    have heq : matBall n C =
        ({A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ | ∀ i j, |A i j| ≤ C} ∩
          {A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ | Aᵀ * pmOneMat * A = pmOneMat}) ∩
          {A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ | A * pmOneMat * Aᵀ = pmOneMat} := by
      ext A; simp [matBall, and_assoc]
    rw [heq]; exact (h1.inter h2).inter h3
  have hbox : IsCompact (Set.pi Set.univ fun _ : Fin n ⊕ Fin 1 =>
      Set.pi Set.univ fun _ : Fin n ⊕ Fin 1 => Set.Icc (-C) C) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  refine hbox.of_isClosed_subset hclosed ?_
  rintro A ⟨hA, -⟩ i - j -
  exact ⟨neg_le_of_abs_le (hA i j), le_of_abs_le (hA i j)⟩

/-- The image `matBallToPO n C` of `matBall n C` in `PO n 1` is compact. -/
theorem matBallToPO_compact (n : ℕ) (C : ℝ) : IsCompact (matBallToPO n C) := by
  rw [matBallToPO]
  have hc : CompactSpace ↥(matBall n C) := isCompact_iff_compactSpace.mp (matBall_compact n C)
  have hof : Continuous (fun A : ↥(matBall n C) =>
      (O1.ofMatrix A.1 ⟨A.2.2.1, A.2.2.2⟩ : O1 n)) := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have hq : Continuous (fun A : O1 n => (A : PO n 1)) := QuotientGroup.continuous_mk
  exact isCompact_univ.image (hq.comp hof)

/-- The set of elements displacing the origin by at most `R` is contained in the compact set
`matBallToPO n (cosh (max R 0))`. -/
theorem orbitBall_subset (n : ℕ) (R : ℝ) :
    {g : PO n 1 | hdist (0 : E n) (g • (0 : E n)) ≤ R} ⊆
      matBallToPO n (Real.cosh (max R 0)) := by
  intro g hg
  have hmat : mat (rep g) ∈ matBall n (Real.cosh (max R 0)) := by
    refine ⟨?_, O1_form_col (rep g), O1_form_row (rep g)⟩
    intro i j
    have h1 := abs_mat_le_tpart_actO (rep g) i j
    rw [show actO (rep g) (0 : E n) = g • (0 : E n) from rfl] at h1
    rw [← cosh_hdist_zero (g • (0 : E n))] at h1
    refine le_trans h1 (Real.cosh_le_cosh.mpr ?_)
    rw [abs_of_nonneg (hdist_nonneg 0 (g • (0 : E n))), abs_of_nonneg (le_max_right R 0)]
    exact le_trans hg (le_max_left R 0)
  rw [matBallToPO, Set.mem_image]
  refine ⟨⟨mat (rep g), hmat⟩, Set.mem_univ _, ?_⟩
  have hEq : O1.ofMatrix (mat (rep g)) ⟨hmat.2.1, hmat.2.2⟩ = rep g := by
    apply Subtype.ext
    exact mat_O1_ofMatrix (mat (rep g)) ⟨hmat.2.1, hmat.2.2⟩
  show ((O1.ofMatrix (mat (rep g)) ⟨hmat.2.1, hmat.2.2⟩ : O1 n) : PO n 1) = g
  rw [hEq]
  exact Quotient.out_eq g

/-- The near-stabiliser of the origin in a discrete subgroup `Γ ≤ PO n 1` is finite. -/
theorem nearStab_finite (n : ℕ) (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ))
    (R : ℝ) :
    {γ : Γ | hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤ R}.Finite := by
  have hK : IsCompact (matBallToPO n (Real.cosh (max R 0))) := matBallToPO_compact n _
  have htend : Filter.Tendsto ((↑) : Γ → PO n 1) Filter.cofinite (Filter.cocompact (PO n 1)) :=
    Subgroup.tendsto_coe_cofinite_of_isDiscrete Γ hdisc
  have hfin : {γ : Γ | (γ : PO n 1) ∈ matBallToPO n (Real.cosh (max R 0))}.Finite :=
    (tendsto_cofinite_cocompact_iff.mp htend) _ hK
  exact hfin.subset (fun γ hγ => orbitBall_subset n R hγ)

set_option linter.unusedVariables false in
/-- The action of a discrete subgroup of `PO n 1` on `ℍⁿ` is proper: for a compact `K` and a
point `u₀`, the set of `γ ∈ Γ` with `γ • u₀ ∈ K` is finite. -/
theorem properAction (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ)) (u₀ : E n) (K : Set (E n))
    (hK : IsCompact K) : {γ : Γ | (γ : PO n 1) • u₀ ∈ K}.Finite := by
  let hId := HypIsoData.ofProp hI
  have hdl : ∀ (x : E n) (M : ℝ), ‖x‖ ≤ M →
      hdist (0 : E n) x ≤ Real.arcosh (Real.sqrt (1 + M ^ 2)) := by
    intro x M hx
    have h0 : hdist (0 : E n) x = Real.arcosh (tpart x) := by rw [hdist]; simp [tpart]
    rw [h0]
    rw [Real.arcosh_le_arcosh (tpart_pos x) (Real.sqrt_pos.2 (by nlinarith [sq_nonneg M]))]
    rw [tpart]
    apply Real.sqrt_le_sqrt
    nlinarith [hx, norm_nonneg x, sq_nonneg (M - ‖x‖)]
  by_cases hne : K.Nonempty
  · obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ K, ‖x‖ ≤ M := exists_norm_le_of_isCompact hK
    set R : ℝ := Real.arcosh (Real.sqrt (1 + M ^ 2)) + hdist (0 : E n) u₀ with hRdef
    refine (nearStab_finite n Γ hdisc R).subset ?_
    intro γ hγ
    have hx : ‖(γ : PO n 1) • u₀‖ ≤ M := hM _ hγ
    have hstep1 : hdist (0 : E n) ((γ : PO n 1) • u₀) ≤ Real.arcosh (Real.sqrt (1 + M ^ 2)) :=
      hdl _ M hx
    have hstep2 : hdist ((γ : PO n 1) • u₀) ((γ : PO n 1) • (0 : E n)) = hdist u₀ (0 : E n) :=
      hId.isom_smul _ _ _
    have htri := hId.triangle (0 : E n) ((γ : PO n 1) • u₀) ((γ : PO n 1) • (0 : E n))
    show hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤ R
    calc hdist (0 : E n) ((γ : PO n 1) • (0 : E n))
        ≤ hdist (0 : E n) ((γ : PO n 1) • u₀) +
            hdist ((γ : PO n 1) • u₀) ((γ : PO n 1) • (0 : E n)) := htri
      _ = hdist (0 : E n) ((γ : PO n 1) • u₀) + hdist u₀ (0 : E n) := by rw [hstep2]
      _ ≤ Real.arcosh (Real.sqrt (1 + M ^ 2)) + hdist (0 : E n) u₀ := by
            rw [hId.symm u₀ (0 : E n)]; linarith [hstep1]
      _ = R := by rw [hRdef]
  · have hKe : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hKe]
    exact Set.finite_empty

end Work.Mostow
