import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Q8

theorem step9_sum_sq_sub_sq {ι : Type*} [Fintype ι] (f : ι → ℤ) {e m : ℤ} (he : e * e = 1)
    (hf : ∑ i, f i = (Fintype.card ι) * e) (hg : ∑ i, (f i) ^ 2 = (Fintype.card ι) * m) :
    ∑ i, (f i - e) ^ 2 = (Fintype.card ι) * (m - 1) := by
  have h1 : ∑ i, (f i - e) ^ 2 = ∑ i, ((f i) ^ 2 - (2 * e) * (f i) + (e * e)) :=
    Finset.sum_congr rfl (fun i _ => by ring)
  have h2 : ∑ i, ((f i) ^ 2 - (2 * e) * (f i) + (e * e))
      = (∑ i, (f i) ^ 2) - (2 * e) * (∑ i, f i) + (Fintype.card ι : ℤ) * (e * e) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [h1, h2, hf, hg]
  nlinarith [he]

end Work.BrauerSuzuki.Q8
