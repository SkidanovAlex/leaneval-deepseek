import Mathlib
import Submission.Work.HallHigman.GLCore.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman.GLCore

/-- **L1 of the GL-core design** (Step 3 of the proof of Hall--Higman B, see
`NOTES_LEAD_ft_hallhigman.md` §2.2): if `c = X a X⁻¹ a⁻¹` lies in a finite `p'`-subgroup `Q`,
`X ^ p = 1`, and `c` commutes with `X`, then `c = 1`.  (Indeed `X a X⁻¹ = c a` and `Commute c X`
give `Xᵏ a X⁻ᵏ = cᵏ a`, hence `a = X ^ p a X ^ (-p) = c ^ p a` and `c ^ p = 1`, while
`orderOf c` divides `|Q|`, which is prime to `p`.) -/
lemma commutator_eq_one_of_commute {H : Type*} [Group H] {p : ℕ} [Fact p.Prime]
    {Q : Subgroup H} [Finite Q] (hQp : ¬ p ∣ Nat.card Q) {X a : H} (hXp : X ^ p = 1)
    (hc : X * a * X⁻¹ * a⁻¹ ∈ Q) (hcomm : Commute (X * a * X⁻¹ * a⁻¹) X) :
    X * a * X⁻¹ * a⁻¹ = 1 := by
  set c := X * a * X⁻¹ * a⁻¹ with hcdef
  -- Conjugating `a` by `X ^ k` multiplies the defect by `c ^ k`; in particular
  -- `X ^ k * a * (X ^ k)⁻¹ = c ^ k * a`.
  have key : ∀ k : ℕ, X ^ k * a * (X ^ k)⁻¹ = c ^ k * a := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hxk : Commute X (c ^ k) := (hcomm.symm).pow_right k
      calc X ^ (k+1) * a * (X ^ (k+1))⁻¹
          = X * (X ^ k * a * (X ^ k)⁻¹) * X⁻¹ := by group
        _ = X * (c ^ k * a) * X⁻¹ := by rw [ih]
        _ = c ^ k * (X * a * X⁻¹) := by
              rw [← mul_assoc X (c ^ k) a, hxk.eq]; group
        _ = c ^ k * (c * a) := by
              have : X * a * X⁻¹ = c * a := by rw [hcdef]; group
              rw [this]
        _ = c ^ (k+1) * a := by group
  -- At `k = p` and `X ^ p = 1` this yields `c ^ p = 1`.
  have hp : X ^ p * a * (X ^ p)⁻¹ = c ^ p * a := key p
  rw [hXp, one_mul, inv_one] at hp
  have ha : a = c ^ p * a := by simpa using hp
  have hcp : c ^ p = 1 := by
    have h1 : (1:H) * a = c ^ p * a := by rw [one_mul]; exact ha
    exact (mul_right_cancel h1).symm
  -- So `orderOf c` divides both `p` and `|Q|`, hence equals `1`.
  have hdivp : orderOf c ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hcp
  have hdivQ : orderOf c ∣ Nat.card Q := Subgroup.orderOf_dvd_natCard Q hc
  rw [Nat.dvd_prime (Fact.out : Nat.Prime p)] at hdivp
  rcases hdivp with h1 | hp'
  · exact orderOf_eq_one_iff.mp h1
  · exact absurd (hp' ▸ hdivQ) hQp

end Work.HallHigman.GLCore
