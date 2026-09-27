import Mathlib
import Submission.Work.Mostow.cuspDefs
import Submission.Work.Mostow.Hyper

set_option linter.style.haveILetI false

namespace Work.Mostow

/-- Auxiliary group-theoretic identity: a power of a product of two commuting elements. -/
lemma commute_zpow_mul_zpow_pow {G : Type*} [Group G] {a b : G} (hab : Commute a b)
    (m n k : ℤ) : (a ^ m * b ^ n) ^ k = a ^ (m * k) * b ^ (n * k) := by
  rw [(hab.zpow_left m).zpow_right n |>.mul_zpow]
  congr 1 <;> rw [zpow_mul]

/-- If `β : S →* Multiplicative ℝ` has image contained in a cyclic subgroup of `ℝ` and finite
kernel, then any two commuting elements `a b` of `G` with `a ^ 2, b ^ 2 ∈ S` are dependent:
some non-trivial relation `a ^ i * b ^ j = 1` holds.

Proof: if `a` (or `b`) has finite order we are done.  Otherwise `a ^ 2, b ^ 2 ∉ ker β`
(else `a` would have finite order), so writing `β a ^ 2 = p c`, `β b ^ 2 = q c` we get
`p, q ≠ 0`, and the element `z = (a ^ 2) ^ q * (b ^ 2) ^ (-p) ∈ S` satisfies `β z = 1`.
Since `ker β` is finite, `z` has finite order `k > 0`, and `z ^ k = 1` expands to
`a ^ (2 q k) * b ^ (-(2 p k)) = 1` with `2 q k ≠ 0`. -/
theorem commutingPairDependent {G : Type*} [Group G] (S : Subgroup G) (β : S →* Multiplicative ℝ)
    (c : ℝ) (hc : ∀ s : S, ∃ m : ℤ, Multiplicative.toAdd (β s) = m * c)
    (hker : {s : S | β s = 1}.Finite) (a b : G) (hab : Commute a b) (ha : a ^ 2 ∈ S)
    (hb : b ^ 2 ∈ S) : ∃ i j : ℤ, (i ≠ 0 ∨ j ≠ 0) ∧ a ^ i * b ^ j = 1 := by
  classical
  have hfin : (β.ker : Set S).Finite := hker
  haveI : Finite β.ker := hfin.to_subtype
  -- Elements of the (finite) kernel have finite order.
  have hfinord : ∀ z : S, β z = 1 → IsOfFinOrder z := by
    intro z hz
    have h2 : IsOfFinOrder (⟨z, MonoidHom.mem_ker.mpr hz⟩ : β.ker) := isOfFinOrder_of_finite _
    rw [isOfFinOrder_iff_pow_eq_one] at h2 ⊢
    obtain ⟨n, hn, hpow⟩ := h2
    exact ⟨n, hn, by simpa using congrArg Subtype.val hpow⟩
  by_cases hA : IsOfFinOrder a
  · obtain ⟨n, hn, ha1⟩ := isOfFinOrder_iff_pow_eq_one.mp hA
    exact ⟨(n : ℤ), 0, Or.inl (by exact_mod_cast hn.ne'), by simp [zpow_natCast, ha1]⟩
  by_cases hB : IsOfFinOrder b
  · obtain ⟨n, hn, hb1⟩ := isOfFinOrder_iff_pow_eq_one.mp hB
    exact ⟨0, (n : ℤ), Or.inr (by exact_mod_cast hn.ne'), by simp [zpow_natCast, hb1]⟩
  -- Both `a` and `b` have infinite order; in particular `a ^ 2`, `b ^ 2 ∉ ker β`.
  have hneA : β ⟨a ^ 2, ha⟩ ≠ 1 := by
    intro h
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp (hfinord ⟨a^2, ha⟩ h)
    apply hA
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨2 * n, by positivity, ?_⟩
    have h1 : ((⟨a^2, ha⟩ : S) : G) ^ n = 1 := by simpa using congrArg Subtype.val hpow
    calc a ^ (2 * n) = (a ^ 2) ^ n := by rw [pow_mul]
      _ = ((⟨a^2, ha⟩ : S) : G) ^ n := rfl
      _ = 1 := h1
  have hneB : β ⟨b ^ 2, hb⟩ ≠ 1 := by
    intro h
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp (hfinord ⟨b^2, hb⟩ h)
    apply hB
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨2 * n, by positivity, ?_⟩
    have h1 : ((⟨b^2, hb⟩ : S) : G) ^ n = 1 := by simpa using congrArg Subtype.val hpow
    calc b ^ (2 * n) = (b ^ 2) ^ n := by rw [pow_mul]
      _ = ((⟨b^2, hb⟩ : S) : G) ^ n := rfl
      _ = 1 := h1
  obtain ⟨p, hp⟩ := hc ⟨a^2, ha⟩
  obtain ⟨q, hq⟩ := hc ⟨b^2, hb⟩
  have hqne : q ≠ 0 := by
    intro h
    apply hneB
    apply toAdd_eq_zero.mp
    rw [hq, h]; ring
  -- The kernel element `z = (a ^ 2) ^ q * (b ^ 2) ^ (-p) ∈ S`.
  let zS : S := ⟨a ^ 2, ha⟩ ^ q * ⟨b ^ 2, hb⟩ ^ (-p)
  have hβz : β zS = 1 := by
    apply toAdd_eq_zero.mp
    have key : (β zS).toAdd = q • (p * c) + (-p) • (q * c) := by
      simp only [zS, map_mul, map_zpow, toAdd_mul, toAdd_zpow, hp, hq]
    rw [key]
    simp only [zsmul_eq_mul, Int.cast_neg]
    ring
  obtain ⟨k, hk, hkpow⟩ := isOfFinOrder_iff_pow_eq_one.mp (hfinord zS hβz)
  have hzkG : (zS : G) ^ k = 1 := by simpa using congrArg Subtype.val hkpow
  have hcomm : Commute (a^2 : G) (b^2 : G) := hab.pow_pow 2 2
  have h1 : ((a^2)^q * (b^2)^(-p)) ^ k
      = a ^ (2 * (q * (k:ℤ))) * b ^ (2 * ((-p) * (k:ℤ))) := by
    rw [← zpow_natCast, commute_zpow_mul_zpow_pow hcomm]
    congr 1 <;> group
  refine ⟨2 * q * (k : ℤ), -(2 * p * (k : ℤ)), Or.inl ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero (by norm_num) hqne) (by exact_mod_cast hk.ne')
  · calc a ^ (2 * q * (k:ℤ)) * b ^ (-(2 * p * (k:ℤ)))
        = a ^ (2 * (q * (k:ℤ))) * b ^ (2 * ((-p) * (k:ℤ))) := by congr 1 <;> group
      _ = ((a^2)^q * (b^2)^(-p)) ^ k := h1.symm
      _ = 1 := hzkG

end Work.Mostow
