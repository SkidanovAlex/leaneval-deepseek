import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.NormalForm
import Submission.Work.SG.transLattice_zlattice

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

set_option linter.style.haveILetI false

noncomputable section

/-- The linear equivalence "negate every coordinate" of `Fin 3 → ℝ` has determinant `-1`. -/
lemma det_neg_coord :
    LinearMap.det ((LinearEquiv.neg ℝ : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) :
      (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) = -1 := by
  have h1 : ((LinearEquiv.neg ℝ : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
      = (-1 : ℝ) • (1 : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) := by
    ext x; simp
  rw [h1, LinearMap.det_smul]
  simp [Module.finrank_fintype_fun_eq_card]
  norm_num

/-- Composing a coordinate endomorphism with the negation of all coordinates flips the sign of
the determinant (in dimension `3`). -/
lemma det_flip (M : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) :
    (((LinearEquiv.det ((LinearEquiv.neg ℝ).trans M) : ℝˣ)) : ℝ)
      = - (((LinearEquiv.det M : ℝˣ)) : ℝ) := by
  rw [LinearEquiv.det_trans, Units.val_mul]
  have h : (((LinearEquiv.det (LinearEquiv.neg ℝ : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) : ℝˣ)) : ℝ)
      = -1 := by
    rw [LinearEquiv.coe_det, det_neg_coord]
  rw [h]
  ring

/-- **A `ℤ`-basis of a `ℤ`-lattice, in positive orientation.**  For a discrete full `ℤ`-lattice
`L ⊆ E 3` there is a linear equivalence `T : (Fin 3 → ℝ) ≃ₗ[ℝ] E 3` which carries `ℤ³`
bijectively onto `L` (so `T` is a lattice basis) and whose coordinate matrix
`T.trans coordLin` has positive determinant.  The basis is any `ℤ`-basis `b` of `L`; its
realification `B = b.ofZLatticeBasis ℝ` has `span ℤ (range B) = L`, giving both directions of the
bijection, and if the orientation is negative one composes with the negation of all coordinates,
which preserves `ℤ³` and flips the sign of the determinant. -/
theorem exists_basis_lattice_equiv (L : Submodule ℤ (E 3)) (hD : DiscreteTopology L)
    (hZL : @IsZLattice ℝ _ _ _ _ L hD) :
    ∃ T : (Fin 3 → ℝ) ≃ₗ[ℝ] E 3,
      (∀ n : Fin 3 → ℤ, T (intVec n) ∈ L) ∧
      (∀ v ∈ L, ∃ n : Fin 3 → ℤ, T.symm v = intVec n) ∧
      0 < (((LinearEquiv.det (T.trans coordLin)) : ℝˣ) : ℝ) := by
  letI : DiscreteTopology L := hD
  letI : IsZLattice ℝ L := hZL
  -- a `ℤ`-basis of `L` indexed by `Fin 3` (the `ℤ`-rank of `L` is `finrank ℝ (E 3) = 3`)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = Fintype.card (Fin 3) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex ℤ L, ZLattice.rank ℝ L,
      finrank_euclideanSpace_fin, Fintype.card_fin]
  let b : Module.Basis (Fin 3) ℤ L :=
    (Module.Free.chooseBasis ℤ (↥L)).reindex (Fintype.equivOfCardEq hcard)
  let B : Module.Basis (Fin 3) ℝ (E 3) := Module.Basis.ofZLatticeBasis ℝ L b
  have hBspan : Submodule.span ℤ (Set.range B) = L := Module.Basis.ofZLatticeBasis_span ℝ L b
  -- `B.equivFun.symm` is the linear map `x ↦ ∑ xᵢ • Bᵢ`
  have h1 : ∀ n : Fin 3 → ℤ, B.equivFun.symm (intVec n) ∈ L := by
    intro n
    rw [← hBspan, Module.Basis.equivFun_symm_apply, Submodule.mem_span_range_iff_exists_fun]
    refine ⟨n, ?_⟩
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [intVec]
    rw [Int.cast_smul_eq_zsmul]
  -- conversely every element of `L` has integral coordinates on `B`
  have h2 : ∀ v ∈ L, ∃ n : Fin 3 → ℤ, (B.equivFun.symm).symm v = intVec n := by
    intro v hv
    refine ⟨b.repr ⟨v, hv⟩, ?_⟩
    ext i
    rw [LinearEquiv.symm_symm, Module.Basis.equivFun_apply]
    exact Module.Basis.ofZLatticeBasis_repr_apply ℝ L b ⟨v, hv⟩ i
  rcases lt_or_gt_of_ne (Units.ne_zero (LinearEquiv.det (B.equivFun.symm.trans coordLin)) :
      (((LinearEquiv.det (B.equivFun.symm.trans coordLin) : ℝˣ) : ℝ) ≠ 0)) with hneg | hpos
  · -- negative orientation: compose with the negation of all coordinates
    refine ⟨(LinearEquiv.neg ℝ).trans B.equivFun.symm, ?_, ?_, ?_⟩
    · intro n
      rw [LinearEquiv.trans_apply]
      have hσ : (LinearEquiv.neg ℝ) (intVec n) = intVec (fun i => - n i) := by
        ext i; simp [LinearEquiv.neg_apply, intVec]
      rw [hσ]; exact h1 _
    · intro v hv
      obtain ⟨c, hc⟩ := h2 v hv
      refine ⟨fun i => - c i, ?_⟩
      rw [LinearEquiv.symm_apply_eq, LinearEquiv.trans_apply]
      have hσ : (LinearEquiv.neg ℝ) (intVec (fun i => - c i)) = intVec c := by
        ext i; simp [LinearEquiv.neg_apply, intVec]
      rw [hσ, ← hc, LinearEquiv.apply_symm_apply]
    · rw [LinearEquiv.trans_assoc, det_flip]
      linarith
  · exact ⟨B.equivFun.symm, h1, h2, hpos⟩

theorem exists_lattice_equiv (G : LeanEval.Geometry.SpaceGroupsProblem.CrystallographicGroup 3) :
    ∃ hD : DiscreteTopology (Work.SG.transLattice G.1),
      @IsZLattice ℝ _ _ _ _ (Work.SG.transLattice G.1) hD ∧
      ∃ T : (Fin 3 → ℝ) ≃ₗ[ℝ] LeanEval.Geometry.SpaceGroupsProblem.E 3,
        (∀ n : Fin 3 → ℤ, T (Work.SG.intVec n) ∈ Work.SG.transLattice G.1) ∧
        (∀ v ∈ Work.SG.transLattice G.1, ∃ n : Fin 3 → ℤ, T.symm v = Work.SG.intVec n) ∧
        0 < (((LinearEquiv.det (T.trans Work.SG.coordLin)) : ℝˣ) : ℝ) := by
  obtain ⟨hD, hZL⟩ := transLattice_zlattice G
  exact ⟨hD, hZL, exists_basis_lattice_equiv (transLattice G.1) hD hZL⟩

end

end Work.SG
