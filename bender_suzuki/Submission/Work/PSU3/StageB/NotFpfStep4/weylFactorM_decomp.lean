import Mathlib
import Submission.Work.PSU3.Model.psu3_datum
import Submission.Work.Models.Port.PSU3.Bruhat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.NotFpfStep4

open Matrix LeanEval.GroupTheory.Defs

/-- Conjugating a unipotent element by the inverse of a torus element keeps it in `U`. -/
lemma suTg_inv_conj_mem_suU (n : ℕ) (a : (Submission.PSU3.F n)ˣ)
    {u : GL (Fin 3) (Submission.PSU3.F n)} (hu : u ∈ Submission.PSU3.suU n) :
    (Submission.PSU3.suTg n a)⁻¹ * u * Submission.PSU3.suTg n a ∈ Submission.PSU3.suU n := by
  have hmem : (Submission.PSU3.suTg n a)⁻¹ ∈ Submission.PSU3.suT n :=
    (Submission.PSU3.suT n).inv_mem ⟨a, rfl⟩
  have h := (Subgroup.le_normalizer_iff.mp (Submission.PSU3.suT_le_normalizer_suU n))
    (Submission.PSU3.suTg n a)⁻¹ hmem u hu
  simpa [inv_inv] using h

theorem weylFactorM_decomp {n : ℕ} (ζ : (Work.PSU3.E n)ˣ) (p : Work.PSU3.SZ (Work.PSU3.E n))
    (hp : p ≠ 1) (hσy : Work.PSU3.σE p.y = (ζ : Work.PSU3.E n)) :
    ∃ g : ↥(Submission.PSU3.psu3U n),
      ∃ hh : ↥(Submission.Blueprint.twoPoint (Submission.PSU3.psu3B n)
          (Submission.PSU3.psu3Weyl n)),
        (hh : LeanEval.GroupTheory.Defs.PSU3Model n) =
            Submission.PSU3.psu3Hom n ⟨Submission.PSU3.suTg n ζ⁻¹,
              Submission.PSU3.suTg_isSU3 n ζ⁻¹⟩ ∧
          Work.PSU3.Model.weylFactorM n p.x p.y
              (Work.PSU3.SZ.y_ne_zero_of_ne_one hp) p.herm =
            (g : LeanEval.GroupTheory.Defs.PSU3Model n) *
              (hh : LeanEval.GroupTheory.Defs.PSU3Model n) := by
  have hy : p.y ≠ 0 := Work.PSU3.SZ.y_ne_zero_of_ne_one hp
  -- the unit `a = σ(p.y)`, which coincides with `ζ`
  let a : (Submission.PSU3.F n)ˣ :=
    Units.mk0 (Work.PSU3.σE p.y) (Work.PSU3.Model.sigma_ne_zero hy)
  have hζa : ζ = a := Units.ext (by
    change (ζ : Work.PSU3.E n) = Work.PSU3.σE p.y
    exact hσy.symm)
  -- the `D`-component of the decomposition
  set hh0 : LeanEval.GroupTheory.Defs.PSU3Model n :=
    Submission.PSU3.psu3Hom n (Submission.PSU3.suTgSU n ζ⁻¹) with hh0def
  have hmem : hh0 ∈ Submission.Blueprint.twoPoint (Submission.PSU3.psu3B n)
      (Submission.PSU3.psu3Weyl n) := by
    rw [Work.PSU3.Model.twoPoint_psu3B_psu3Weyl n]
    exact Subgroup.mem_map.mpr ⟨Submission.PSU3.suTgSU n ζ⁻¹,
      Submission.PSU3.suTgSU_mem_suTS n ζ⁻¹, rfl⟩
  -- the Borel factor `Wf = weylFactorGL`
  let Wf : ↥(Submission.PSU3.SU3 n) :=
    ⟨Work.PSU3.Model.weylFactorGL n p.x p.y hy p.herm,
      Work.PSU3.Model.weylFactorGL_mem_SU3 n p.x p.y hy p.herm⟩
  have hWf : Submission.PSU3.psu3Hom n Wf =
      Work.PSU3.Model.weylFactorM n p.x p.y hy p.herm := Subtype.ext rfl
  -- `Wf · (suTgSU ζ⁻¹)⁻¹` lies in `U`
  have hsub : (Wf * (Submission.PSU3.suTgSU n ζ⁻¹)⁻¹ : ↥(Submission.PSU3.SU3 n)) ∈
      (Submission.PSU3.suU n).subgroupOf (Submission.PSU3.SU3 n) := by
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
      Submission.PSU3.suTgSU_val]
    show Work.PSU3.Model.weylFactorGL n p.x p.y hy p.herm *
        (Submission.PSU3.suTg n ζ⁻¹)⁻¹ ∈ Submission.PSU3.suU n
    have hconj : (Submission.PSU3.suTg n a)⁻¹ *
        Submission.PSU3.suUg n (Work.PSU3.σE p.y * p.x / p.y) (Work.PSU3.σE p.y) *
        Submission.PSU3.suTg n a ∈ Submission.PSU3.suU n :=
      suTg_inv_conj_mem_suU n a (Work.PSU3.Model.suUg_weyl_mem_suU n p.x p.y hy p.herm)
    convert hconj using 1
    rw [Work.PSU3.Model.weylFactorGL, hζa, Submission.PSU3.suTg_inv, inv_inv]
  -- the unipotent part
  have hg : Work.PSU3.Model.weylFactorM n p.x p.y hy p.herm * hh0⁻¹ ∈
      Submission.PSU3.psu3U n := by
    have hval : Work.PSU3.Model.weylFactorM n p.x p.y hy p.herm * hh0⁻¹ =
        Submission.PSU3.psu3Hom n (Wf * (Submission.PSU3.suTgSU n ζ⁻¹)⁻¹) := by
      rw [← hWf, hh0def, ← map_inv, ← map_mul]
    rw [hval]
    exact Subgroup.mem_map.mpr ⟨_, hsub, rfl⟩
  refine ⟨⟨Work.PSU3.Model.weylFactorM n p.x p.y hy p.herm * hh0⁻¹, hg⟩,
    ⟨hh0, hmem⟩, ?_, ?_⟩
  · show hh0 = Submission.PSU3.psu3Hom n ⟨Submission.PSU3.suTg n ζ⁻¹,
        Submission.PSU3.suTg_isSU3 n ζ⁻¹⟩
    rw [hh0def]
    rfl
  · change Work.PSU3.Model.weylFactorM n p.x p.y hy p.herm =
        (Work.PSU3.Model.weylFactorM n p.x p.y hy p.herm * hh0⁻¹) * hh0
    rw [mul_assoc, inv_mul_cancel, mul_one]

end Work.PSU3.StageB.NotFpfStep4
