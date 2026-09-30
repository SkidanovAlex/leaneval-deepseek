import Mathlib
import Submission.Work.BMF.mr_direct.eboundR_defs
import Submission.Work.BMF.mr_direct.range_defs
import Submission.Work.BMF.mr_direct.omegaCount_mul_prime
import Submission.Work.BMF.mr_direct.card_primeSet_filter_dvd
import Submission.Work.BMF.mr_direct.norm_ebgamma_le_inv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The merged coefficient `ebDR` of the range-extension error is bounded by `1`

`ebDR b c K P Q A B n` is the merged coefficient of the range-extension error `eboundR`,
obtained by collecting all pairs `i = (p, m) ∈ pSetBR K P Q A B` with equal product
`ebnn i = p * m = n`.  This is the range analogue of
`Work.BMF.mr_direct.ebD_norm_sq_le_one` (which treats `winIdx`/`natIcc (X/p) (2X/p)`).

The mathematics is the same two-sided count on the fibre
`ebFiberR K P Q A B n = {i ∈ pSetBR | p * m = n}`:

* each pair `i = (p, m)` in the fibre has `p` prime, `p ∈ [P,Q]`, and `p * m = n`, whence `p`
  is one of the (at most) `ω(n;P,Q) = #omegaCount P Q n` primes in `[P,Q]` dividing `n`; the
  map `i ↦ p` is injective on the fibre, so `#fibre ≤ ω(n;P,Q)`;
* for every `i = (p,m)` in the fibre, `ω(n;P,Q) ≤ ω(m;P,Q) + 1`, so the coefficient
  `ebγ i = c p · b m · (ω(m;P,Q)+1)^{-1}` has norm at most `(ω(n;P,Q))^{-1}`.

Hence `‖ebDR n‖ ≤ #fibre / ω(n;P,Q) ≤ 1`.

The only place the range (as opposed to the dyadic) window enters is the positivity of the
lower endpoint `A · e^{-(j+1)/K} > 0`, which uses the hypothesis `1 ≤ A`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.BMF.mr_direct

open scoped BigOperators

noncomputable section

/-- Membership in a fibre: the first coordinate is a prime of `[P,Q]`. -/
lemma mem_primeSet_of_mem_ebFiberR {K P Q A B : ℝ} {n : ℕ} {i : Σ _ : ℕ, ℕ}
    (hi : i ∈ ebFiberR K P Q A B n) : i.1 ∈ Work.BMF.mrDirect.primeSet P Q := by
  have h1 : i ∈ pSetBR K P Q A B := (Finset.mem_filter.mp hi).1
  exact (Finset.mem_sigma.mp h1).1

/-- Membership in a fibre: the product of the two coordinates is `n`. -/
lemma mul_eq_of_mem_ebFiberR {K P Q A B : ℝ} {n : ℕ} {i : Σ _ : ℕ, ℕ}
    (hi : i ∈ ebFiberR K P Q A B n) : i.1 * i.2 = n := by
  have h2 := (Finset.mem_filter.mp hi).2
  simpa [ebnn] using h2

/-- Membership in a fibre: the second coordinate is positive (the lower end of the window
`Work.BMF.mrDirect.winIdxR K A B j` is `A · e^{-(j+1)/K} > 0` by `1 ≤ A`). -/
lemma one_le_snd_of_mem_ebFiberR {K P Q A B : ℝ} (hA : 1 ≤ A) {n : ℕ} {i : Σ _ : ℕ, ℕ}
    (hi : i ∈ ebFiberR K P Q A B n) : 1 ≤ i.2 := by
  have h1 : i ∈ pSetBR K P Q A B := (Finset.mem_filter.mp hi).1
  have h2 : i.2 ∈ (Work.BMF.mrDirect.winIdxR K A B (Work.BMF.mrDirect.jdex K i.1)).filter
      (fun m => m ∉ Work.BMF.natIcc (A / i.1) (B / i.1)) := (Finset.mem_sigma.mp h1).2
  have h3 : i.2 ∈ Work.BMF.mrDirect.winIdxR K A B (Work.BMF.mrDirect.jdex K i.1) := (Finset.mem_filter.mp h2).1
  rw [Work.BMF.mrDirect.winIdxR, Work.BMF.natIcc, Finset.mem_Icc] at h3
  have hA0 : (0:ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  have hpos : (0:ℝ) < A * Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K) :=
    mul_pos hA0 (Real.exp_pos _)
  have hceil : 1 ≤ ⌈A * Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K)⌉₊ :=
    Nat.one_le_iff_ne_zero.mpr (ne_of_gt (Nat.ceil_pos.mpr hpos))
  omega

/-- For a pair `i = (p,m)` of the fibre over `n`, the primes of `[P,Q]` dividing `n = p·m`
are those dividing `m`, plus possibly `p`: hence `ω(n;P,Q) ≤ ω(m;P,Q) + 1`. -/
theorem omegaCount_le_of_mem_ebFiberR (K P Q A B : ℝ) (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (n : ℕ) (i : Σ _ : ℕ, ℕ) (hi : i ∈ ebFiberR K P Q A B n) :
    Work.BMF.mrDirect.omegaCount P Q n ≤ Work.BMF.mrDirect.omegaCount P Q i.2 + 1 := by
  rw [ebFiberR, Finset.mem_filter] at hi
  obtain ⟨hiB, hieq⟩ := hi
  rw [pSetBR, Finset.mem_sigma] at hiB
  obtain ⟨hpp_mem, -⟩ := hiB
  have hQ0 : 0 ≤ Q := by linarith
  obtain ⟨hpp, hPp, hpQ⟩ := (Work.BMF.mrDirect.mem_primeSet hQ0).mp hpp_mem
  rw [← hieq, ebnn]
  have h := omegaCount_mul_prime (P := P) (Q := Q) (p := i.1) (m := i.2) hpp hPp hpQ
  rw [mul_comm, h]
  have hif : (if i.1 ∣ i.2 then (0 : ℕ) else 1) ≤ 1 := by split <;> omega
  omega

/-- The fibre of `ebnn` over `n` injects into the primes of `primeSet P Q` dividing `n`
(by sending `(p, m)` to `p`), hence has cardinality at most `ω(n;P,Q)`. -/
theorem card_ebFiberR_le_omegaCount (K P Q A B : ℝ) (hA : 1 ≤ A) (n : ℕ) :
    (ebFiberR K P Q A B n).card ≤ Work.BMF.mrDirect.omegaCount P Q n := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    have hempty : ebFiberR K P Q A B 0 = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro i hi
      rw [ebFiberR, Finset.mem_filter] at hi
      obtain ⟨hiB, hie⟩ := hi
      rw [pSetBR, Finset.mem_sigma] at hiB
      obtain ⟨hprimemem, hi2⟩ := hiB
      rw [Work.BMF.mrDirect.primeSet, Finset.mem_filter] at hprimemem
      have hprime : i.1.Prime := hprimemem.2
      have hi2win : i.2 ∈ Work.BMF.mrDirect.winIdxR K A B (Work.BMF.mrDirect.jdex K i.1) := (Finset.mem_filter.mp hi2).1
      rw [ebnn] at hie
      have hm0 : i.2 = 0 := by
        rcases Nat.mul_eq_zero.mp hie with h | h
        · exact absurd h hprime.ne_zero
        · exact h
      rw [Work.BMF.mrDirect.winIdxR, Work.BMF.natIcc, Finset.mem_Icc] at hi2win
      have hA0 : (0:ℝ) < A := lt_of_lt_of_le zero_lt_one hA
      have ha_pos : 0 < A * Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K) :=
        mul_pos hA0 (Real.exp_pos _)
      have hceil : 1 ≤ ⌈A * Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K)⌉₊ :=
        Nat.one_le_ceil_iff.mpr ha_pos
      omega
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    rw [← card_primeSet_filter_dvd (P := P) (Q := Q) hn1]
    have hinj : Set.InjOn (fun i : Sigma (fun _ : ℕ => ℕ) => i.1)
        ↑(ebFiberR K P Q A B n) := by
      intro i hi j hj hij
      simp only [Finset.mem_coe, ebFiberR, Finset.mem_filter] at hi hj
      obtain ⟨hiB, hie⟩ := hi
      obtain ⟨hjB, hje⟩ := hj
      have hp : i.1 ∈ Work.BMF.mrDirect.primeSet P Q := (Finset.mem_sigma.mp hiB).1
      have hpprime : i.1.Prime := by
        rw [Work.BMF.mrDirect.primeSet, Finset.mem_filter] at hp
        exact hp.2
      have hp0 : 0 < i.1 := hpprime.pos
      rw [ebnn] at hie hje
      rcases i with ⟨p, m⟩
      rcases j with ⟨p', m'⟩
      simp only at hij hie hje hpprime hp0
      subst hij
      have hmm : m = m' := Nat.mul_left_cancel hp0 (by rw [hie, hje])
      subst hmm
      rfl
    have hsub : (ebFiberR K P Q A B n).image (fun i : Sigma (fun _ : ℕ => ℕ) => i.1)
        ⊆ (Work.BMF.mrDirect.primeSet P Q).filter (fun p => p ∣ n) := by
      intro p hp
      rw [Finset.mem_image] at hp
      obtain ⟨i, hi, rfl⟩ := hp
      rw [ebFiberR, Finset.mem_filter] at hi
      obtain ⟨hiB, hie⟩ := hi
      rw [Finset.mem_filter]
      refine ⟨(Finset.mem_sigma.mp hiB).1, ?_⟩
      rw [ebnn] at hie
      rw [← hie]
      exact dvd_mul_right i.1 i.2
    calc (ebFiberR K P Q A B n).card
        = ((ebFiberR K P Q A B n).image (fun i : Sigma (fun _ : ℕ => ℕ) => i.1)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ ((Work.BMF.mrDirect.primeSet P Q).filter (fun p => p ∣ n)).card :=
          Finset.card_le_card hsub

theorem ebDR_norm_sq_le_one (b c : ℕ → ℂ) (K P Q A B : ℝ) (hA : 1 ≤ A) (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1) (n : ℕ) :
    ‖Work.BMF.mr_direct.ebDR b c K P Q A B n‖ ^ 2 ≤ 1 := by
  set F := ebFiberR K P Q A B n with hF
  have hD : ebDR b c K P Q A B n = ∑ i ∈ F, ebγ b c P Q i := rfl
  rw [hD]
  have key : ‖∑ i ∈ F, ebγ b c P Q i‖ ≤ 1 := by
    rcases Finset.eq_empty_or_nonempty F with hEmpty | ⟨i₀, hi₀⟩
    · simp [hEmpty]
    · -- the fibre is nonempty, so `ω(n;P,Q) ≥ 1`
      set R : ℕ := Work.BMF.mrDirect.omegaCount P Q n with hR
      have hp₀mem : i₀.1 ∈ Work.BMF.mrDirect.primeSet P Q := mem_primeSet_of_mem_ebFiberR hi₀
      have hmul₀ : i₀.1 * i₀.2 = n := mul_eq_of_mem_ebFiberR hi₀
      have h1m₀ : 1 ≤ i₀.2 := one_le_snd_of_mem_ebFiberR hA hi₀
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
          exact card_ebFiberR_le_omegaCount K P Q A B hA n
        exact_mod_cast this
      calc ‖∑ i ∈ F, ebγ b c P Q i‖
          ≤ ∑ i ∈ F, ‖ebγ b c P Q i‖ := norm_sum_le F _
        _ ≤ ∑ _i ∈ F, ((R:ℝ))⁻¹ := by
            apply Finset.sum_le_sum
            intro i hi
            have h1 := norm_ebgamma_le_inv b c P Q hb hc i
            have h2 : R ≤ Work.BMF.mrDirect.omegaCount P Q i.2 + 1 :=
              omegaCount_le_of_mem_ebFiberR K P Q A B hP hPQ n i hi
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
