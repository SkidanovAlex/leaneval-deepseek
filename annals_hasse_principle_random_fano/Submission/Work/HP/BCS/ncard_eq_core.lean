import Mathlib
import Submission.Work.HP.BCS.Transport

set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open MeasureTheory Finset
open scoped Pointwise

namespace Work.HP.BCS

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-! ## Auxiliary transport lemmas -/

/-- The coefficient map of a `ℤ`-basis of `L`, evaluated at the real coordinates of `t`, is `toEr`
of the lattice vector with coordinates `t`. -/
lemma coeffMap_equivFun_symm (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (t : Fin k → ℤ) :
    coeffMap (fun i => (b i : ι → ℤ)) (fun i => (t i : ℝ))
      = toEr ((b.equivFun.symm t : L) : ι → ℤ) := by
  rw [coeffMap_eq_sum]
  have h2 : (toErLin.comp (Submodule.subtype L)) (b.equivFun.symm t)
      = ∑ i, (t i : ℝ) • toEr ((b i : L) : ι → ℤ) := by
    rw [Module.Basis.equivFun_symm_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    rw [show (toErLin.comp (Submodule.subtype L)) (b i) = toEr ((b i : L) : ι → ℤ) by
      simp only [LinearMap.comp_apply, Submodule.coe_subtype, toErLin_apply]]
    exact (Int.cast_smul_eq_zsmul ℝ (t i) (toEr ((b i : L) : ι → ℤ))).symm
  rw [← h2]
  simp only [LinearMap.comp_apply, Submodule.coe_subtype, toErLin_apply]

/-- Unfolding `PsiOf` through the isometry `isomSpan`. -/
lemma isomSpan_symm_PsiOf (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (x : EuclideanSpace ℝ (Fin k)) :
    (isomSpan L b).symm (PsiOf L b x) = coeffEquiv L b ((toEkEquiv k).symm x) := by
  simp only [PsiOf, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.symm_apply_apply]

/-- The isometry `isomSpan L b` sends `PsiOf L b (toEk t)` to the lattice vector with coordinates
`t`. -/
lemma PsiOf_toEk_coord (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) (t : Fin k → ℤ) :
    ((isomSpan L b).symm (PsiOf L b (toEk t)) : EuclideanSpace ℝ ι)
      = toEr ((b.equivFun.symm t : L) : ι → ℤ) := by
  rw [isomSpan_symm_PsiOf, toEk_eq, LinearEquiv.symm_apply_apply, coeffEquiv_coe]
  exact coeffMap_equivFun_symm L b t

/-- The norm of `PsiOf L b (toEk t)` is the Euclidean norm of the corresponding lattice vector. -/
lemma norm_PsiOf_toEk (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) (t : Fin k → ℤ) :
    ‖PsiOf L b (toEk t)‖ = eNorm ((b.equivFun.symm t : L) : ι → ℤ) := by
  have h := PsiOf_toEk_coord L b t
  calc ‖PsiOf L b (toEk t)‖ = ‖(isomSpan L b).symm (PsiOf L b (toEk t))‖ :=
        (LinearIsometryEquiv.norm_map (isomSpan L b).symm (PsiOf L b (toEk t))).symm
    _ = ‖((isomSpan L b).symm (PsiOf L b (toEk t)) : EuclideanSpace ℝ ι)‖ := rfl
    _ = ‖toEr ((b.equivFun.symm t : L) : ι → ℤ)‖ := by rw [h]
    _ = eNorm ((b.equivFun.symm t : L) : ι → ℤ) := norm_toEr _

/-- The pairing with `coneVec L b v`, transported to the corresponding lattice vector. -/
lemma inner_coneVec_PsiOf (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (v : ι → ℝ) (t : Fin k → ℤ) :
    inner ℝ (coneVec L b v) (PsiOf L b (toEk t))
      = inner ℝ (toE v) (toEr ((b.equivFun.symm t : L) : ι → ℤ)) := by
  rw [inner_coneVec L b v (PsiOf L b (toEk t)), PsiOf_toEk_coord L b t]

/-- The cone condition `toR a ∈ Cgam v γ` for the lattice vector `a` with coordinates `t` is
equivalent to the cone condition `PsiOf L b (toEk t) ∈ coneSet (coneVec L b v) (‖toE v‖/(2γ))`. -/
lemma Cgam_iff_coneSet (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (v : ι → ℝ) (γ : ℝ) (t : Fin k → ℤ) :
    toR ((b.equivFun.symm t : L) : ι → ℤ) ∈ Cgam v γ ↔
      PsiOf L b (toEk t) ∈ coneSet (coneVec L b v) (‖toE v‖ / (2 * γ)) := by
  rw [mem_Cgam_iff, coneSet, Set.mem_ofPred_eq, inner_coneVec_PsiOf L b v t, norm_PsiOf_toEk L b t,
    norm_toEr]
  have harith : ‖toE v‖ / (2 * γ) * eNorm ((b.equivFun.symm t : L) : ι → ℤ)
      = ‖toE v‖ * eNorm ((b.equivFun.symm t : L) : ι → ℤ) / (2 * γ) := by ring
  exact iff_of_eq (congrArg
    (fun r => |inner ℝ (toE v) (toEr ((b.equivFun.symm t : L) : ι → ℤ))| ≤ r) harith.symm)

/-- Simultaneous transport of the norm bound and the cone condition from the lattice `L` to the
coordinates `ℤ^k`. -/
lemma transfer_iff (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (v : ι → ℝ) (γ T : ℝ) (t : Fin k → ℤ) :
    (eNorm ((b.equivFun.symm t : L) : ι → ℤ) ≤ T ∧
        toR ((b.equivFun.symm t : L) : ι → ℤ) ∈ Cgam v γ)
      ↔ (‖PsiOf L b (toEk t)‖ ≤ T ∧
          PsiOf L b (toEk t) ∈ coneSet (coneVec L b v) (‖toE v‖ / (2 * γ))) := by
  rw [norm_PsiOf_toEk L b t]
  exact and_congr Iff.rfl (Cgam_iff_coneSet L b v γ t)

/-! ## The count identification -/

-- The count of lattice points in the two-cone slice, transported to coordinates: the number of
-- `a ∈ L ⊆ ℤ^ι` with `eNorm a ≤ T` inside the two cones `Cgam v γ`, `Cgam w γ` equals the number of
-- coordinate vectors `t : Fin k → ℤ` whose image `Ψ (toEk t)` lies in the corresponding cone slices
-- of `ℝ^k`, where `Ψ = PsiOf L b` and `coneVec L b v` is the Riesz vector of `y ↦ ⟪toE v, e.symm y⟫`.
--
-- ROUTE.  `Basis.equivFun : L ≃ₗ[ℤ] (Fin k → ℤ)` and
-- `Basis.equivFun_symm_apply : b.equivFun.symm t = ∑ i, t i • b i` give the bijection between
-- `{a : ι → ℤ | a ∈ L}` and `Fin k → ℤ`.  Under it:
-- * `eNorm a = ‖PsiOf L b (toEk t)‖` (`Work.HP.BCS.norm_PsiOf_single`, `Work.HP.BCS.coeffMap_eq_sum`,
--   `Work.HP.norm_toEr`);
-- * `toR a ∈ Cgam v γ ↔ PsiOf L b (toEk t) ∈ coneSet (coneVec L b v) (‖toE v‖ / (2 * γ))` by
--   `Work.HP.BCS.mem_Cgam_iff` (`Submission.Work.HP.BCS.Setup`) together with
--   `Work.HP.BCS.inner_coneVec` and the isometry property of `isomSpan`;
-- * `latImage Ψ = Ψ '' Set.range toEk` contains `Ψ (toEk t)` by definition.
-- Conclude with `Set.ncard_congr` (or `Set.ncard_image_of_injective`).
theorem ncard_eq_core {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) (v w : ι → ℝ) (γ T : ℝ) :
    ({a : ι → ℤ | a ∈ L ∧ Work.HP.eNorm a ≤ T ∧ Work.HP.toR a ∈ Work.HP.Cgam v γ ∧
        Work.HP.toR a ∈ Work.HP.Cgam w γ}.ncard : ℝ)
      = ({t : Fin k → ℤ | Work.HP.BCS.PsiOf L b (Work.HP.BCS.toEk t) ∈
              Work.HP.BCS.latImage (Work.HP.BCS.PsiOf L b) ∧
            Work.HP.BCS.PsiOf L b (Work.HP.BCS.toEk t) ∈
              Work.HP.BCS.coneSet (Work.HP.BCS.coneVec L b v) (‖Work.HP.toE v‖ / (2 * γ)) ∧
            Work.HP.BCS.PsiOf L b (Work.HP.BCS.toEk t) ∈
              Work.HP.BCS.coneSet (Work.HP.BCS.coneVec L b w) (‖Work.HP.toE w‖ / (2 * γ)) ∧
            ‖Work.HP.BCS.PsiOf L b (Work.HP.BCS.toEk t)‖ ≤ T}.ncard : ℝ) := by
  classical
  have hmain : ({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ T ∧ toR a ∈ Cgam v γ ∧
        toR a ∈ Cgam w γ}.ncard)
      = ({t : Fin k → ℤ | PsiOf L b (toEk t) ∈ latImage (PsiOf L b) ∧
            PsiOf L b (toEk t) ∈ coneSet (coneVec L b v) (‖toE v‖ / (2 * γ)) ∧
            PsiOf L b (toEk t) ∈ coneSet (coneVec L b w) (‖toE w‖ / (2 * γ)) ∧
            ‖PsiOf L b (toEk t)‖ ≤ T}.ncard) := by
    refine Set.ncard_congr (fun a ha => b.equivFun ⟨a, ha.1⟩) ?_ ?_ ?_
    · intro a ha
      have hG : ((b.equivFun.symm (b.equivFun ⟨a, ha.1⟩) : L) : ι → ℤ) = a :=
        congrArg (fun x : L => (x : ι → ℤ))
          (LinearEquiv.symm_apply_apply b.equivFun ⟨a, ha.1⟩)
      have hmem : eNorm ((b.equivFun.symm (b.equivFun ⟨a, ha.1⟩) : L) : ι → ℤ) ≤ T := by
        rw [hG]; exact ha.2.1
      have hcvG : toR ((b.equivFun.symm (b.equivFun ⟨a, ha.1⟩) : L) : ι → ℤ) ∈ Cgam v γ := by
        rw [hG]; exact ha.2.2.1
      have hcwG : toR ((b.equivFun.symm (b.equivFun ⟨a, ha.1⟩) : L) : ι → ℤ) ∈ Cgam w γ := by
        rw [hG]; exact ha.2.2.2
      obtain ⟨hn, hcv⟩ := (transfer_iff L b v γ T (b.equivFun ⟨a, ha.1⟩)).mp ⟨hmem, hcvG⟩
      obtain ⟨-, hcw⟩ := (transfer_iff L b w γ T (b.equivFun ⟨a, ha.1⟩)).mp ⟨hmem, hcwG⟩
      exact ⟨⟨toEk (b.equivFun ⟨a, ha.1⟩), ⟨b.equivFun ⟨a, ha.1⟩, rfl⟩, rfl⟩, hcv, hcw, hn⟩
    · intro a a' ha ha' h
      have h' : (⟨a, ha.1⟩ : L) = ⟨a', ha'.1⟩ := b.equivFun.injective h
      exact congrArg (fun x : L => (x : ι → ℤ)) h'
    · intro t ht
      have hmem : ((b.equivFun.symm t : L) : ι → ℤ) ∈ L := (b.equivFun.symm t).2
      obtain ⟨hn, hcv⟩ := (transfer_iff L b v γ T t).mpr ⟨ht.2.2.2, ht.2.1⟩
      obtain ⟨-, hcw⟩ := (transfer_iff L b w γ T t).mpr ⟨ht.2.2.2, ht.2.2.1⟩
      refine ⟨((b.equivFun.symm t : L) : ι → ℤ), ⟨hmem, hn, hcv, hcw⟩, ?_⟩
      exact (congrArg (fun x : L => b.equivFun x) (Subtype.ext rfl)).trans
        (LinearEquiv.apply_symm_apply b.equivFun t)
  exact congrArg (fun n : ℕ => (n : ℝ)) hmain

end Work.HP.BCS
