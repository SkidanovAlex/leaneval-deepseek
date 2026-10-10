import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC.gal_sub_eq_of_smul`

A small pure group-theory lemma used in the twisted-function-field chapter `MotC`.

Setting: `G` is an additive commutative group, `σ : G →+ G` an additive endomorphism,
`P ∈ G` a point killed by `5` (`5 • P = 0`), and `R ∈ G` satisfies
`R - P = σ R + k • P` for `k = 2` or `k = 3`.

The claim is that then `P` lies in the image of `σ - id` restricted to the
`⟨R, P⟩`-subgroup: explicitly one takes `R' = 3 • R` when `k = 2` and `R' = R`
when `k = 3`.  Indeed `σ R = R - (k+1) • P`, so

`σ (m • R) - m • R = m • (σ R - R) = -(m (k+1)) • P`,

and for the choices above `m (k+1)` is `9` resp. `4`, and `-(9 • P) = P`,
`-(4 • P) = P` hold because `P` has order dividing `5`.
-/

namespace Work.MotC

/-- If `P` is killed by `5`, then it is killed by every multiple of `5`. -/
lemma nsmul_eq_zero_of_five_dvd {G : Type*} [AddCommGroup G] {P : G}
    (h5 : (5 : ℕ) • P = 0) {n : ℕ} (hn : 5 ∣ n) : n • P = 0 := by
  obtain ⟨t, ht⟩ := hn
  rw [ht, mul_nsmul P 5 t, h5, nsmul_zero]

/-- If `P` is killed by `5` and `5 ∣ n + 1`, then `-(n • P) = P`. -/
lemma neg_nsmul_eq_of_five_dvd_succ {G : Type*} [AddCommGroup G] {P : G}
    (h5 : (5 : ℕ) • P = 0) {n : ℕ} (hn : 5 ∣ n + 1) : -(n • P) = P := by
  have h0 : (n + 1) • P = 0 := nsmul_eq_zero_of_five_dvd h5 hn
  rw [add_nsmul, one_nsmul] at h0
  exact neg_eq_of_add_eq_zero_right h0

theorem gal_sub_eq_of_smul {G : Type*} [AddCommGroup G] (σ : G →+ G) (P R : G)
    (h5 : (5 : ℕ) • P = 0) (k : ℕ) (hk : k = 2 ∨ k = 3)
    (hR : R - P = σ R + k • P) : ∃ R' : G, σ R' - R' = P := by
  -- From `R - P = σ R + k • P` we get `σ R = R - (k+1) • P`.
  have hσR : σ R = R - (k + 1) • P := by
    have hσR0 : σ R = R - P - k • P := by rw [hR]; abel
    rw [hσR0, add_nsmul, one_nsmul]; abel
  have hsub : σ R - R = -((k + 1) • P) := by rw [hσR]; abel
  rcases hk with hk | hk
  · -- `k = 2`: take `R' = 3 • R`.
    subst hk
    refine ⟨3 • R, ?_⟩
    rw [map_nsmul, ← nsmul_sub]
    have hk3 : σ R - R = -((3 : ℕ) • P) := by rw [hsub]
    rw [hk3, neg_nsmul]
    have h9 : (3 : ℕ) • (3 • P) = (9 : ℕ) • P := by rw [← mul_nsmul P 3 3]
    rw [h9]
    exact neg_nsmul_eq_of_five_dvd_succ h5 (by norm_num)
  · -- `k = 3`: take `R' = R`.
    subst hk
    refine ⟨R, ?_⟩
    rw [hsub]
    exact neg_nsmul_eq_of_five_dvd_succ h5 (by norm_num)

end Work.MotC
