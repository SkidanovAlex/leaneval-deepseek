import Mathlib
import Submission.Work.Tame.indFun_Lgrp_apply_of_mem_Lhat
import Submission.Work.Tame.tau_at_AL_v3

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

/-- Feit–Thompson Lemma 9.1 (value part), the case `i = 0` (p. 805): if `L ∈ 𝔏₀`, i.e.
`L ∈ L̂`, `L ≠ 1` and `C(L) ⊆ 𝔏 = N(L̂)` (`L ∈ L0set Lhat`, Definition 9.1), and `α ∈ 𝓒₀(L̂)`,
then the induced function `α^* = Ind_𝔏^X α` of (9.4) satisfies `α^*(L) = α(L)`.  Indeed
`α^*(L) = |C(L)|·|C(L) ⊓ 𝔏|⁻¹·α(L)` by `indFun_Lgrp_apply_of_mem_Lhat`, and `C(L) ⊓ 𝔏 = C(L)`
because `C(L) ⊆ 𝔏`. -/
theorem indFun_Lgrp_apply_of_mem_L0set {X : Type*} [Group X] [Fintype X] {Lhat : Set X}
    {n : ℕ} {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs)
    {α : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ C0 Lhat) {L : ↥(Lgrp Lhat)}
    (hL : (L : X) ∈ L0set Lhat) :
    Induction.indFun (Lgrp Lhat) α (L : X) = α L := by
  obtain ⟨hLmem, hLne, hLcent⟩ := mem_L0set.mp hL
  have hkey := indFun_Lgrp_apply_of_mem_Lhat h hα hLmem hLne
  -- `C(L) ⊆ 𝔏`, so `C(L) ⊓ 𝔏 = C(L)`.
  have hinf : Subgroup.centralizer ({(L : X)} : Set X) ⊓ Lgrp Lhat =
      Subgroup.centralizer ({(L : X)} : Set X) := inf_eq_left.mpr hLcent
  have hne : (Nat.card ↥(Subgroup.centralizer ({(L : X)} : Set X)) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr
      ⟨⟨1, (Subgroup.centralizer ({(L : X)} : Set X)).one_mem⟩, inferInstance⟩
  rw [hkey, hinf, mul_inv_cancel₀ hne, one_mul]

end Work.Tame
