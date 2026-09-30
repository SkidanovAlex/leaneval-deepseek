import Mathlib
import Submission.Work.Pi6.EMODD.fibreOfMpathQ
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.EMODD

/-- `(ofAdd 1)^k = ofAdd k` in `Multiplicative ℤ`. -/
lemma ofAdd_one_zpow_int (k : ℤ) :
    ((Multiplicative.ofAdd (1 : ℤ)) ^ k : Multiplicative ℤ) = Multiplicative.ofAdd k := by
  rw [← ofAdd_zsmul]
  simp

/-- `(ofAdd k)^m = ofAdd (m * k)` in `Multiplicative ℤ`. -/
lemma ofAdd_zpow_int (k m : ℤ) :
    ((Multiplicative.ofAdd k) ^ m : Multiplicative ℤ) = Multiplicative.ofAdd (m * k) := by
  rw [← ofAdd_zsmul]
  simp

/-- The element `ofAdd 1 ^ k` of `Multiplicative ℤ` (for `k : ℤ`) raised to the power `m`
is `ofAdd (m * k)`. -/
lemma ofAdd_one_zpow_zpow (k m : ℤ) :
    ((Multiplicative.ofAdd (1 : ℤ)) ^ k) ^ m = Multiplicative.ofAdd (m * k) := by
  rw [ofAdd_one_zpow_int k, ofAdd_zpow_int k m]

/-- For `e : G ≃* Multiplicative ℤ` and `k = ±1`, the element `(e.symm (Multiplicative.ofAdd 1))^k` freely generates `G`, i.e. `∀ a : G, ∃! m : ℤ, a = ((e.symm (Multiplicative.ofAdd 1)) ^ k) ^ m`. Route: `e ((e.symm (ofAdd 1))^k) = (ofAdd 1)^k = ofAdd k`, every element of `Multiplicative ℤ` is `ofAdd m = (ofAdd 1)^m` uniquely, and `e` is injective; the case `k = -1` follows from `k = 1` and `inv_zpow`. Namespace `Work.Pi6.EMODD`, module `Submission.Work.Pi6.EMODD.generatorZpow`; helper declarations above the statement are welcome. -/
theorem generatorZpow {G : Type*} [Group G] (e : G ≃* Multiplicative ℤ) (k : ℤ)
    (hk : k = 1 ∨ k = -1) :
    ∀ a : G, ∃! m : ℤ, a = ((e.symm (Multiplicative.ofAdd 1)) ^ k) ^ m := by
  have hk_sq : k * k = 1 := by rcases hk with h | h <;> simp [h]
  intro a
  set g : G := e.symm (Multiplicative.ofAdd 1) with hg
  have heg : e g = Multiplicative.ofAdd (1 : ℤ) := by
    rw [hg]
    simp
  have hkey : ∀ m : ℤ, e ((g ^ k) ^ m) = Multiplicative.ofAdd (m * k) := by
    intro m
    rw [map_zpow e (g ^ k) m, map_zpow e g k, heg]
    exact ofAdd_one_zpow_zpow k m
  have htoAdd : Multiplicative.ofAdd (e a).toAdd = e a := ofAdd_toAdd (e a)
  refine ⟨(e a).toAdd * k, ?_, ?_⟩
  · apply e.injective
    rw [hkey]
    have hmul : ((e a).toAdd * k) * k = (e a).toAdd := by
      rw [mul_assoc, hk_sq, mul_one]
    rw [hmul]
    exact htoAdd.symm
  · intro m hm
    have hm' : e a = Multiplicative.ofAdd (m * k) := by
      rw [hm, hkey m]
    have h2 : m * k = (e a).toAdd := by
      apply Multiplicative.ofAdd.injective
      rw [htoAdd]
      exact hm'.symm
    calc m = m * (k * k) := by rw [hk_sq, mul_one]
      _ = (m * k) * k := by rw [← mul_assoc]
      _ = (e a).toAdd * k := by rw [h2]

end Work.Pi6.EMODD
