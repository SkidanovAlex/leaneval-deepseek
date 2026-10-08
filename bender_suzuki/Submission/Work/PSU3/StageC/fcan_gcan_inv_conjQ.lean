import Mathlib
import Submission.Work.PSU3.StageC.ConjQ

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageC

theorem fcan_gcan_inv_conjQ {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ρ : Q} (hρ : (ρ : G) ≠ 1) (ζ' : fr.KW)
    (hζ'W : (ζ' : G) ∈ Work.ThmF.W H t)
    (hfρ : Work.PSU3.StageB.fcan hS.split ρ = conjQ hS fr ζ' ρ⁻¹) :
    Work.PSU3.StageB.fcan hS.split ρ⁻¹ = conjQ hS fr ζ'⁻¹ ρ ∧
      Work.PSU3.StageB.gcan hS.split ρ⁻¹ = conjQ hS fr ζ' ρ := by
  -- `ζ' ∈ W ≤ C_D(t)`, so `t ζ' t = ζ'`: H3 applies with `d = d' = ζ'`.
  have hρinv : ((ρ⁻¹ : Q) : G) ≠ 1 := Work.PSU3.StageB.inv_ne_one hρ
  have hζ't : (ζ' : G) = t * (ζ' : G) * t :=
    (t_conj_of_mem_W hS fr hζ'W).symm
  -- H3 for the pair `(ζ', ζ')`.
  have hH3 : Work.PSU3.StageB.fcan hS.split (conjQ hS fr ζ' ρ⁻¹) =
      conjQ hS fr ζ' (Work.PSU3.StageB.fcan hS.split ρ⁻¹) :=
    fcan_conjQ_eq hS fr (d := ζ') (d' := ζ') hζ't hρinv
  constructor
  · -- `f(ρ⁻¹) = (ζ') ρ (ζ')⁻¹`: apply `f` to `f(ρ) = (ζ')⁻¹ ρ⁻¹ ζ'` and use `f² = id`, H3.
    apply Subtype.ext
    have hv : (Work.PSU3.StageB.fcan hS.split ρ⁻¹ : G) = (ζ' : G) * (ρ : G) * (ζ' : G)⁻¹ := by
      have h1 : (Work.PSU3.StageB.fcan hS.split (conjQ hS fr ζ' ρ⁻¹) : G) =
          (conjQ hS fr ζ' (Work.PSU3.StageB.fcan hS.split ρ⁻¹) : G) :=
        congrArg Subtype.val hH3
      rw [← hfρ, conjQ_coe] at h1
      have h2 : (Work.PSU3.StageB.fcan hS.split (Work.PSU3.StageB.fcan hS.split ρ) : G) =
          (ρ : G) :=
        (Work.PSU3.StageB.fcan_fcan hS.split hρ).1
      rw [h2] at h1
      rw [h1]; group
    rw [hv, conjQ_coe]
    simp only [Subgroup.coe_inv]
    group
  · -- `g(ρ⁻¹) = f(ρ)⁻¹ = ((ζ')⁻¹ ρ⁻¹ ζ')⁻¹ = (ζ')⁻¹ ρ ζ'`: H1.
    apply Subtype.ext
    rw [Work.PSU3.StageB.gcan_inv hS.split hρ]
    rw [hfρ, conjQ_coe, conjQ_coe]
    simp only [Subgroup.coe_inv]
    group

end Work.PSU3.StageC
