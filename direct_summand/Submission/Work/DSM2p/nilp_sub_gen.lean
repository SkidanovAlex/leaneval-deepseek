import Mathlib
import Submission.Work.DSM2p.nilp_sub_defs

/-!
# `Work.DSM2p.nilp_sub_gen`

With `A ⊆ B` a subring, `ϖ ∈ A`, `a ∈ B` and `hgen : ∀ z, ∃ n c ∈ A, z * ϖ ^ n = c`
(so that `B = A[1/ϖ]`), every element `y` of `B[a⁻¹]` becomes an element of the subring
`A[a⁻¹] ⊆ B[a⁻¹]` after multiplication by a suitable power of `ϖ`:

  `y * ϖ ^ n ∈ A[a⁻¹]`.

The proof is the elementary one.  Write `y = z / a ^ k` with `z ∈ B` (`IsLocalization.Away.surj`),
and then use `hgen` on `z`: `z * ϖ ^ m = c ∈ A`.  Since `a` is invertible in `B[a⁻¹]`, this gives

  `y * ϖ ^ m = (z / a ^ k) * ϖ ^ m = c / a ^ k ∈ A[a⁻¹]`.
-/

namespace Work.DSM2p

/-- Every element of `B[a⁻¹]` lies in `A[a⁻¹]` after multiplication by a power of `ϖ`, when
`B = A[1/ϖ]`. -/
theorem nilp_sub_gen {B : Type*} [CommRing B] (A : Subring B) {ϖ : B} (hϖA : ϖ ∈ A)
    (a : B) (hgen : ∀ z : B, ∃ n : ℕ, ∃ c : A, z * ϖ ^ n = (c : B)) :
    ∀ y : Localization.Away a, ∃ n : ℕ, ∃ s : awaySubring A a,
      y * (⟨algebraMap B (Localization.Away a) ϖ, varpi_mem_awaySubring A a hϖA⟩ :
          awaySubring A a) ^ n = (s : Localization.Away a) := by
  intro y
  -- write `y = z * (a ^ k)⁻¹`
  obtain ⟨k, z, hy⟩ := IsLocalization.Away.surj (S := Localization.Away a) a y
  -- and clear the `ϖ`-power in `z` using `hgen`
  obtain ⟨m, c, hc⟩ := hgen z
  refine ⟨m, ⟨algebraMap B (Localization.Away a) (c : B) * IsLocalization.Away.invSelf a ^ k,
    Subring.mul_mem _ (algebraMap_mem_awaySubring A a c)
      (Subring.pow_mem _ (invSelf_mem_awaySubring A a) k)⟩, ?_⟩
  -- `(a ^ k) * (a ^ k)⁻¹ = 1`
  have h1 : algebraMap B (Localization.Away a) a ^ k * IsLocalization.Away.invSelf a ^ k = 1 := by
    rw [← mul_pow, IsLocalization.Away.mul_invSelf, one_pow]
  have hy' : y = algebraMap B (Localization.Away a) z * IsLocalization.Away.invSelf a ^ k := by
    calc y = y * 1 := by rw [mul_one]
      _ = y * (algebraMap B (Localization.Away a) a ^ k * IsLocalization.Away.invSelf a ^ k) := by
            rw [h1]
      _ = (y * algebraMap B (Localization.Away a) a ^ k) * IsLocalization.Away.invSelf a ^ k := by
            rw [mul_assoc]
      _ = algebraMap B (Localization.Away a) z * IsLocalization.Away.invSelf a ^ k := by rw [hy]
  have hw : ((⟨algebraMap B (Localization.Away a) ϖ, varpi_mem_awaySubring A a hϖA⟩ :
      awaySubring A a) ^ m : Localization.Away a) = algebraMap B (Localization.Away a) ϖ ^ m :=
    rfl
  rw [hy', hw]
  calc algebraMap B (Localization.Away a) z * IsLocalization.Away.invSelf a ^ k
        * algebraMap B (Localization.Away a) ϖ ^ m
      = (algebraMap B (Localization.Away a) z * algebraMap B (Localization.Away a) ϖ ^ m)
          * IsLocalization.Away.invSelf a ^ k := by ring
    _ = algebraMap B (Localization.Away a) (z * ϖ ^ m) * IsLocalization.Away.invSelf a ^ k := by
          rw [map_mul, map_pow]
    _ = algebraMap B (Localization.Away a) (c : B) * IsLocalization.Away.invSelf a ^ k := by rw [hc]

end Work.DSM2p
