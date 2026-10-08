import Mathlib
import Submission.Work.BrauerSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Q8

/-- If a subgroup of a finite group has a unique involution, then so does every subgroup of it of
even order: any involution of a subgroup is an involution of the bigger subgroup, hence equal to
its unique one, and Cauchy's theorem produces an involution. -/
theorem hasUniqueInvolution_of_le_of_two_dvd_card {G : Type*} [Group G] [Finite G]
    {S Q : Subgroup G} (hS : Work.BrauerSuzuki.HasUniqueInvolution ↥S) (hQle : Q ≤ S)
    (hdiv : 2 ∣ Nat.card ↥Q) : Work.BrauerSuzuki.HasUniqueInvolution ↥Q := by
  obtain ⟨zS, _hzS2, hzSuniq⟩ := hS
  have h2prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) 2 hdiv
  have key : ∀ x : ↥Q, orderOf (⟨(x : G), hQle x.2⟩ : ↥S) = orderOf x := fun x =>
    (Subgroup.orderOf_coe (⟨(x : G), hQle x.2⟩ : ↥S)).symm.trans (Subgroup.orderOf_coe x)
  refine ⟨w, hw, fun u hu => ?_⟩
  apply Subtype.ext
  have hwS : (⟨(w : G), hQle w.2⟩ : ↥S) = zS := hzSuniq _ (by rw [key w, hw])
  have huS : (⟨(u : G), hQle u.2⟩ : ↥S) = zS := hzSuniq _ (by rw [key u, hu])
  have hcoe : ((⟨(w : G), hQle w.2⟩ : ↥S) : G) = ((⟨(u : G), hQle u.2⟩ : ↥S) : G) := by
    rw [hwS, huS]
  simpa using hcoe.symm

end Work.BrauerSuzuki.Q8
