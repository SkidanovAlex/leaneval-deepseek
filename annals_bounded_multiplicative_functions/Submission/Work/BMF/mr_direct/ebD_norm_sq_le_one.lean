import Mathlib
import Submission.Work.BMF.mr_direct.buchstab_aux
import Submission.Work.BMF.mr_direct.ebound_defs
import Submission.Work.BMF.mr_direct.omegaCount_mul_prime
import Submission.Work.BMF.mr_direct.card_primeSet_filter_dvd
import Submission.Work.BMF.mr_direct.card_ebFiber_le_omegaCount
import Submission.Work.BMF.mr_direct.omegaCount_le_of_mem_ebFiber
import Submission.Work.BMF.mr_direct.norm_ebgamma_le_inv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The merged coefficient `ebD` of the range-extension error is bounded by `1`

`ebD b c K P Q X n` is the merged coefficient of the range-extension error `ebound`, obtained
by collecting all pairs `i = (p, m) ∈ pSetB K P Q X` with equal product `ebnn i = p * m = n`.
The purpose of this file is the pointwise bound

  `‖ebD b c K P Q X n‖ ^ 2 ≤ 1`

for bounded coefficients `‖b m‖ ≤ 1`, `‖c p‖ ≤ 1`.

The mathematics is a two-sided count on the fibre `ebFiber K P Q X n = {i ∈ pSetB | p * m = n}`:

* each pair `i = (p, m)` in the fibre has `p` prime, `p ∈ [P,Q]`, `p * m = n`, whence
  `p` is one of the (at most) `ω(n;P,Q) = #omegaCount P Q n` primes in `[P,Q]` dividing `n`,
  and `p ≠ p'` for distinct fibre elements, so `#fibre ≤ ω(n;P,Q)`;
* for every `i = (p,m)` in the fibre, `ω(n;P,Q) ≤ ω(m;P,Q) + 1` (the primes in `[P,Q]`
  dividing `n = p·m` are those dividing `m`, plus possibly `p`), so the coefficient
  `ebγ i = c p · b m · (ω(m;P,Q)+1)^{-1}` has norm at most `(ω(n;P,Q))^{-1}`.

Hence `‖ebD n‖ ≤ #fibre / ω(n;P,Q) ≤ 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.BMF.mr_direct

open scoped BigOperators

noncomputable section

/-- Membership in a fibre: the first coordinate is a prime of `[P,Q]`. -/
lemma mem_primeSet_of_mem_ebFiber {K P Q X : ℝ} {n : ℕ} {i : Σ _ : ℕ, ℕ}
    (hi : i ∈ ebFiber K P Q X n) : i.1 ∈ Work.BMF.mrDirect.primeSet P Q := by
  have h1 : i ∈ Work.BMF.mrDirect.pSetB K P Q X := (Finset.mem_filter.mp hi).1
  exact (Finset.mem_sigma.mp h1).1

/-- Membership in a fibre: the product of the two coordinates is `n`. -/
lemma mul_eq_of_mem_ebFiber {K P Q X : ℝ} {n : ℕ} {i : Σ _ : ℕ, ℕ}
    (hi : i ∈ ebFiber K P Q X n) : i.1 * i.2 = n := by
  have h2 := (Finset.mem_filter.mp hi).2
  simpa [ebnn] using h2

/-- Membership in a fibre: the second coordinate is positive (the lower end of the window
`winIdx K X j` is `X · e^{-(j+1)/K} > 0` by `1 ≤ X`). -/
lemma one_le_snd_of_mem_ebFiber {K P Q X : ℝ} (hX : 1 ≤ X) {n : ℕ} {i : Σ _ : ℕ, ℕ}
    (hi : i ∈ ebFiber K P Q X n) : 1 ≤ i.2 := by
  have h1 : i ∈ Work.BMF.mrDirect.pSetB K P Q X := (Finset.mem_filter.mp hi).1
  have h2 : i.2 ∈ (Work.BMF.mrDirect.winIdx K X (Work.BMF.mrDirect.jdex K i.1)).filter
      (fun m => m ∉ Work.BMF.natIcc (X / i.1) (2 * X / i.1)) := (Finset.mem_sigma.mp h1).2
  have h3 : i.2 ∈ Work.BMF.mrDirect.winIdx K X (Work.BMF.mrDirect.jdex K i.1) :=
    (Finset.mem_filter.mp h2).1
  rw [Work.BMF.mrDirect.winIdx, Work.BMF.natIcc, Finset.mem_Icc] at h3
  have hpos : (0:ℝ) < X * Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℝ)) + 1) / K) := by
    have hX0 : (0:ℝ) < X := lt_of_lt_of_le zero_lt_one hX
    positivity
  have hceil : 1 ≤ ⌈X * Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℝ)) + 1) / K)⌉₊ :=
    Nat.one_le_iff_ne_zero.mpr (ne_of_gt (Nat.ceil_pos.mpr hpos))
  omega

theorem ebD_norm_sq_le_one (b c : ℕ → ℂ) (K P Q X : ℝ) (hX : 1 ≤ X) (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1) (n : ℕ) :
    ‖Work.BMF.mr_direct.ebD b c K P Q X n‖ ^ 2 ≤ 1 := by
  set F := ebFiber K P Q X n with hF
  have hD : ebD b c K P Q X n = ∑ i ∈ F, ebγ b c P Q i := rfl
  rw [hD]
  have key : ‖∑ i ∈ F, ebγ b c P Q i‖ ≤ 1 := by
    rcases Finset.eq_empty_or_nonempty F with hEmpty | ⟨i₀, hi₀⟩
    · simp [hEmpty]
    · -- the fibre is nonempty, so `ω(n;P,Q) ≥ 1`
      set R : ℕ := Work.BMF.mrDirect.omegaCount P Q n with hR
      have hp₀mem : i₀.1 ∈ Work.BMF.mrDirect.primeSet P Q := mem_primeSet_of_mem_ebFiber hi₀
      have hmul₀ : i₀.1 * i₀.2 = n := mul_eq_of_mem_ebFiber hi₀
      have h1m₀ : 1 ≤ i₀.2 := one_le_snd_of_mem_ebFiber hX hi₀
      have hpp : i₀.1.Prime := (Finset.mem_filter.mp hp₀mem).2
      have hn1 : 1 ≤ n := by
        rw [← hmul₀]
        exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hpp.ne_zero (by omega))
      have hR1 : 1 ≤ R := by
        rw [hR, ← card_primeSet_filter_dvd (P := P) (Q := Q) hn1]
        exact Finset.card_pos.mpr ⟨i₀.1, Finset.mem_filter.mpr ⟨hp₀mem, ⟨i₀.2, hmul₀.symm⟩⟩⟩
      have hRpos : (0:ℝ) < (R:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR1)
      have hcard : (F.card : ℝ) ≤ (R:ℝ) := by
        have : F.card ≤ R := by
          rw [hF, hR]
          exact card_ebFiber_le_omegaCount K P Q X hX n
        exact_mod_cast this
      calc ‖∑ i ∈ F, ebγ b c P Q i‖
          ≤ ∑ i ∈ F, ‖ebγ b c P Q i‖ := norm_sum_le F _
        _ ≤ ∑ _i ∈ F, ((R:ℝ))⁻¹ := by
            apply Finset.sum_le_sum
            intro i hi
            have h1 := norm_ebgamma_le_inv b c P Q hb hc i
            have h2 : R ≤ Work.BMF.mrDirect.omegaCount P Q i.2 + 1 :=
              omegaCount_le_of_mem_ebFiber K P Q X hP hPQ n i hi
            have h3 : (R:ℝ) ≤ (((Work.BMF.mrDirect.omegaCount P Q i.2 : ℕ) + 1 : ℕ) : ℝ) := by
              exact_mod_cast h2
            have h4 : (((Work.BMF.mrDirect.omegaCount P Q i.2 : ℕ) + 1 : ℕ) : ℝ)⁻¹ ≤ (R:ℝ)⁻¹ := by
              simpa [one_div] using one_div_le_one_div_of_le hRpos h3
            exact le_trans h1 h4
        _ = (F.card : ℝ) * ((R:ℝ))⁻¹ := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (R:ℝ) * ((R:ℝ))⁻¹ :=
            mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr hRpos.le)
        _ = 1 := mul_inv_cancel₀ (ne_of_gt hRpos)
  exact pow_le_one₀ (norm_nonneg _) key

end

end Work.BMF.mr_direct
