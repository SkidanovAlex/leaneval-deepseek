import Mathlib
import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

open Submission.Blueprint

/-- If the two-point stabiliser `D = twoPoint H t` is contained in `Ksub H t = ⟨J(D,t)⟩` and
`J(D,t)` is already a subgroup (closed), then the centraliser `V = C_D(t)` is trivial.

Indeed `D` has odd order (strongly embedded `H`, `t ∉ H`), and every `x ∈ D` is inverted by
`t` (from `D ≤ Ksub` and `Ksub = Kset`).  An `x ∈ C_D(t)` is then both fixed and inverted by
`t`, so `x = x⁻¹`, i.e. `x² = 1`; in a group of odd order the only such element is `1`. -/
theorem centD_eq_bot_of_le_Ksub {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hKsetEq : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t)
    (hDleK : Submission.Blueprint.twoPoint H t ≤ Work.ThmF.Ksub H t) :
    Submission.Blueprint.centD H t = ⊥ := by
  classical
  rw [← le_bot_iff]
  intro x hx
  have hxD : x ∈ Submission.Blueprint.twoPoint H t := (Subgroup.mem_inf.mp hx).1
  have hxcent : x ∈ Subgroup.centralizer ({t} : Set G) := (Subgroup.mem_inf.mp hx).2
  have hxt : t * x = x * t :=
    Subgroup.mem_centralizer_iff.mp hxcent t (Set.mem_singleton t)
  -- `x ∈ D ≤ Ksub = Kset`, so `t` inverts `x`.
  have hxK : x ∈ Work.ThmF.Kset H t := by
    rw [← hKsetEq]
    exact hDleK hxD
  have hinv : t * x * t⁻¹ = x⁻¹ := hxK.2
  -- Being both fixed and inverted by `t`, `x` equals its own inverse.
  have hxinv : x = x⁻¹ := by
    rw [← hinv, hxt]
    group
  have hx2 : x * x = 1 := mul_eq_one_iff_eq_inv.mpr hxinv
  have hpow : x ^ 2 = 1 := by rw [pow_two]; exact hx2
  have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hpow
  -- `D` has odd order, and `orderOf x ∣ Nat.card D`.
  have hoddD : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) :=
    Work.Models.IsStronglyEmbedded.odd_twoPoint h.stronglyEmbedded h.not_mem
  have hdvdD : orderOf x ∣ Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
    rw [← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxD)
  have hoddord : Odd (orderOf x) := Odd.of_dvd_nat hoddD hdvdD
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h1
  · exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)
  · exfalso
    rw [h1] at hoddord
    obtain ⟨k, hk⟩ := hoddord
    omega

end Work.PSU3.StageA
