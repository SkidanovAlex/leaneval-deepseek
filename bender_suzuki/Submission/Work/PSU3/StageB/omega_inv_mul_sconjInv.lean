import Mathlib
import Submission.Work.PSU3.StageB.Theta

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB

open Work.ThmF
open Work.PSU3

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- `s^{a⁻¹} = a s a⁻¹ = zc ((nm (κ a))⁻¹)` for `a ∈ KW` with `a ∈ Ksub H t`. -/
lemma conj_sInv_eq_zc (fr : CoarseFrame H Q t n) (a : fr.KW) (ha : (a : G) ∈ Ksub H t) :
    (a : G) * frameS fr * (a : G)⁻¹ =
      fr.zc (((fr.nm (fr.κ a) : (E n)ˣ) : E n)⁻¹) := by
  have hai : ((a⁻¹ : fr.KW) : G) ∈ Ksub H t := by
    simpa using (Ksub H t).inv_mem ha
  have h := conj_s_eq_zc fr (a := a⁻¹) hai
  rw [map_inv fr.κ a, map_inv fr.nm (fr.κ a), Units.val_inv_eq_inv_val] at h
  have hcoe : ((a⁻¹ : fr.KW) : G) = (a : G)⁻¹ := rfl
  rw [hcoe] at h
  simpa using h

theorem omega_inv_mul_sconjInv {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (fr : Work.PSU3.CoarseFrame H Q t n) {ω : G} (hω : Work.PSU3.OmegaHyp fr ω)
    (a : fr.KW) (ha : (a : G) ∈ Work.ThmF.Ksub H t) :
    (((Work.PSU3.StageB.omQ fr hω)⁻¹ * Work.PSU3.StageB.sconjInv fr a ha : ↥Q) : G)
      = ω * fr.zc (Work.PSU3.StageB.alpha fr hω +
          ((fr.nm (fr.κ a) : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)⁻¹) := by
  have hsi : (sconjInv fr a ha : G) =
      fr.zc (((fr.nm (fr.κ a) : (E n)ˣ) : E n)⁻¹) := by
    rw [sconjInv_coe]
    exact conj_sInv_eq_zc fr a ha
  have hfixN : σE (((fr.nm (fr.κ a) : (E n)ˣ) : E n)⁻¹)
      = (((fr.nm (fr.κ a) : (E n)ˣ) : E n)⁻¹) := by
    rw [map_inv₀, fr.nm_F (fr.κ a) ((fr.mem_K_iff a).mp ha)]
  calc (((omQ fr hω)⁻¹ * sconjInv fr a ha : ↥Q) : G)
      = ω⁻¹ * (sconjInv fr a ha : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, omQ_coe]
    _ = ω⁻¹ * fr.zc (((fr.nm (fr.κ a) : (E n)ˣ) : E n)⁻¹) := by rw [hsi]
    _ = (ω * (ω * ω)) * fr.zc (((fr.nm (fr.κ a) : (E n)ˣ) : E n)⁻¹) := by
        rw [omega_inv_eq fr hω]
    _ = (ω * fr.zc (alpha fr hω)) *
          fr.zc (((fr.nm (fr.κ a) : (E n)ˣ) : E n)⁻¹) := by
        rw [← alpha_spec fr hω]
    _ = ω * fr.zc (alpha fr hω +
          ((fr.nm (fr.κ a) : (E n)ˣ) : E n)⁻¹) := by
        rw [mul_assoc, ← fr.zc_add (alpha fr hω) _ (alpha_fixed fr hω) hfixN]

end Work.PSU3.StageB
