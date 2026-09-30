import Mathlib
import Submission.Work.BMF.mr_direct_range_defs
import Submission.Work.BMF.mr_direct.range_defs
import Submission.Work.BMF.mr_direct.dirPolyM_eq_mainA_add_ep2
import Submission.Work.BMF.mr_direct.card_primeSet_filter_dvd
import Submission.Work.BMF.mr_direct.mainAR_eq_mainBR_sub_eboundR
import Submission.Work.BMF.mr_direct.mainTermR_eq_mainBR_add_dupExtraR
import Submission.Work.BMF.mr_direct.card_has_prime_factorR_le
import Submission.Work.BMF.mr_direct.eboundR_integral_le
import Submission.Work.BMF.mr_direct.dupExtraR_integral_le
import Submission.Work.BMF.mr_direct.integral_norm_sum_le
import Submission.Work.BMF.mr_direct.goodSet_bound_range_defs
import Submission.Work.BMF.mr_direct.mainTermR_set_integral_le
import Submission.Work.BMF.mr_direct.ep2R_subset_integral_le
import Submission.Work.BMF.mr_direct.buchstab_smallK_set
import Submission.Work.BMF.mr_direct.rough_set_integral_le
import Submission.Work.BMF.mr_direct.coprime_primesIn_iff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Buchstab/Ramaré mean-square bound over a subset of `[-S,S]`

This file proves `Work.BMF.mr_direct.buchstab_set`, the set-integral (and support-free) form of
the Buchstab/Ramaré decomposition inequality of Matomäki–Radziwiłł (*Multiplicative functions in
short intervals*, Annals 2016, Lemma `lem:decomp`) for a general range `[X₁,X₂]` of bounded ratio
`X₂ ≤ 4 X₁`.

The proof follows the paper's proof of `lem:decomp`: write `a = a_sup + a_cop`, where `a_sup`
vanishes on the integers having no prime factor in `[P,Q]` (handled by the Buchstab/Ramaré
identity, the mean-square bounds for the three error terms, and the Cauchy–Schwarz step over the
logarithmic windows) and `a_cop` vanishes on the integers *having* a prime factor in `[P,Q]`
(handled by the crude mean-value bound for the remaining integers, which is exactly the
`Σ_{(n,∏p) = 1} |a_n|²/n` term of the statement).

The file first re-proves the range Buchstab/Ramaré identity under renamed declarations (the
original name `phi_memR` clashes with `Submission.Work.BMF.mr_direct.ep2R_defs`), then proves the
supported case, and finally assembles the two parts.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000


/-!
# The range Buchstab/Ramaré identity `dirPolyR = mainAR + ep2R`

This file proves `Work.BMF.mr_direct.dirPolyR_eq_mainAR_add_ep2R_bs`, the general-range version of
`Work.BMF.mr_direct.dirPolyM_eq_mainA_add_ep2` (the first, exact, pointwise step of the
Buchstab/Ramaré decomposition).

Writing `z = -(1+it)` and `φ(⟨p,m⟩) = m·p`, both sides are reorganised as sums of
`(coefficient) · n^z` over `n ∈ [A, B]`:

* the left-hand side is `Σ_{A ≤ n ≤ B} a n · n^z` by definition;
* the right-hand side is, after `Finset.sum_sigma` and `Finset.sum_fiberwise_of_maps_to`,
  `Σ_{A ≤ n ≤ B} (Σ_{φ x = n} buchF x) · n^z`.

The fibre `{x : φ x = n}` of the sigma-index set
`buchSigmaR_bs P Q A B = ⨿_{p ∈ primeSet P Q} [A/p, B/p]`
is in bijection with the primes `p ∈ [P,Q]` dividing `n`, and for each such `p` the coefficient
`buchF ⟨p, n/p⟩` equals `a n / ω(n;P,Q)` — either because `p ∣ n/p` (so the `if`-branch
contributes and `ω(m·p) = ω(m)`) or because `a(m·p) = b m c p` and `ω(m·p) = ω(m)+1`.
Summing over the `ω(n;P,Q)` primes gives `a n`.

Only the "shape" of the range enters: `A > 0` and `A ≤ B`.  The reindexing lemmas
`buchSigmaR_bs`, `phi_memR_bs`, `image_fiberR_bs` are the range analogues of `buchSigma`, `phi_mem`,
`image_fiber` in `Submission/Work/BMF/mr_direct/dirPolyM_eq_mainA_add_ep2.lean`, while `buchF`,
`buchE`, `buchF_eval`, `a_eq_zero_of_omegaCount_zero` are range-independent and are reused
verbatim from there.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace Work.BMF.mr_direct

open Finset
open scoped BigOperators
open Work.BMF (natIcc)
open Work.BMF.mrDirect (primeSet omegaCount mem_natIcc mem_primeSet mem_primeSet' mainAR ep2R
  dirPolyR)

noncomputable section

/-- The sigma-index set of the *range* Buchstab decomposition: pairs `(p, m)` with `p` a prime
in `[P, Q]` and `m ∈ [A/p, B/p]`. -/
def buchSigmaR_bs (P Q A B : ℝ) : Finset (Σ _ : ℕ, ℕ) :=
  (primeSet P Q).sigma (fun p => natIcc (A / p) (B / p))

/-- `mainAR` as a sum over the sigma-type of pairs `(p, m)`. -/
lemma mainAR_sigma_bs (b c : ℕ → ℂ) (P Q A B t : ℝ) :
    mainAR b c P Q A B t =
      ∑ x ∈ buchSigmaR_bs P Q A B,
        (c x.1 * b x.2 * (((omegaCount P Q x.2 : ℕ) + 1 : ℕ) : ℂ)⁻¹) * buchE t x := by
  rw [mainAR, buchSigmaR_bs, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [buchE, Nat.cast_mul, Complex.natCast_mul_natCast_cpow m p]
  ring

/-- `ep2R` as a sum over the sigma-type of pairs `(p, m)` with `p ∣ m`. -/
lemma ep2R_sigma_bs (a b c : ℕ → ℂ) (P Q A B t : ℝ) :
    ep2R a b c P Q A B t =
      ∑ x ∈ (buchSigmaR_bs P Q A B).filter (fun x => x.1 ∣ x.2),
        (a (x.2 * x.1) * (((omegaCount P Q x.2 : ℕ) : ℕ) : ℂ)⁻¹ -
          b x.2 * c x.1 * (((omegaCount P Q x.2 : ℕ) + 1 : ℕ) : ℂ)⁻¹) * buchE t x := by
  rw [ep2R, buchSigmaR_bs, Finset.filter_sigma, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun p hp => ?_
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [buchE, Nat.cast_mul, Complex.natCast_mul_natCast_cpow m p]

/-- The map `(p,m) ↦ m·p` sends the sigma-type into `[A, B]`. -/
lemma phi_memR_bs {P Q A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) {x : Σ _ : ℕ, ℕ}
    (hx : x ∈ buchSigmaR_bs P Q A B) :
    (x.2 * x.1 : ℕ) ∈ Work.BMF.natIcc A B := by
  have hB0 : (0 : ℝ) ≤ B := le_trans hA.le hAB
  rw [buchSigmaR_bs, Finset.mem_sigma] at hx
  obtain ⟨h1, h2⟩ := hx
  have hp : Nat.Prime x.1 := (Finset.mem_filter.mp h1).2
  have hp0 : (0:ℝ) < (x.1:ℝ) := by exact_mod_cast hp.pos
  rw [mem_natIcc hB0]
  obtain ⟨hm1, hm2⟩ := (mem_natIcc (show (0:ℝ) ≤ B / x.1 by positivity)).mp h2
  constructor
  · have h : (x.1:ℝ) * (A / x.1) ≤ (x.1:ℝ) * (x.2:ℝ) :=
      mul_le_mul_of_nonneg_left hm1 hp0.le
    rw [show (x.1:ℝ) * (A / x.1) = A by field_simp] at h
    calc A ≤ (x.1:ℝ) * (x.2:ℝ) := h
      _ = ((x.2 * x.1 : ℕ):ℝ) := by push_cast; ring
  · have h : (x.2:ℝ) * (x.1:ℝ) ≤ (B / x.1) * (x.1:ℝ) :=
      mul_le_mul_of_nonneg_right hm2 hp0.le
    rw [show (B / x.1) * (x.1:ℝ) = B by field_simp] at h
    calc ((x.2 * x.1 : ℕ):ℝ) = (x.2:ℝ) * (x.1:ℝ) := by push_cast; ring
      _ ≤ B := h

/-- The fibre `{x : x.2·x.1 = n}` of `buchSigmaR_bs` over `n ∈ [A,B]` is the image of the primes
`p ∈ [P,Q]` dividing `n` under `p ↦ ⟨p, n/p⟩`. -/
lemma image_fiberR_bs {P Q A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) {n : ℕ}
    (hn : n ∈ Work.BMF.natIcc A B) :
    (buchSigmaR_bs P Q A B).filter (fun x => x.2 * x.1 = n) =
      ((primeSet P Q).filter (fun p => p ∣ n)).image
        (fun p => (⟨p, n / p⟩ : Σ _ : ℕ, ℕ)) := by
  have hB0 : (0 : ℝ) ≤ B := le_trans hA.le hAB
  ext x
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hx, hxphi⟩
    rw [buchSigmaR_bs] at hx
    obtain ⟨h1, h2⟩ := Finset.mem_sigma.mp hx
    have hp : Nat.Prime x.1 := (Finset.mem_filter.mp h1).2
    have hp0 : 0 < x.1 := hp.pos
    refine ⟨x.1, Finset.mem_filter.mpr ⟨h1, ?_⟩, ?_⟩
    · exact ⟨x.2, by rw [← hxphi]; ring⟩
    · have hdiv : n / x.1 = x.2 := by
        rw [← hxphi]
        exact Nat.mul_div_cancel x.2 hp0
      rw [hdiv]
  · rintro ⟨p, hp, hpx⟩
    rw [Finset.mem_filter] at hp
    subst hpx
    have hpn : p ∣ n := hp.2
    have hpp : Nat.Prime p := (Finset.mem_filter.mp hp.1).2
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
    obtain ⟨hnlo, hnhi⟩ := (mem_natIcc hB0).mp hn
    refine ⟨?_, ?_⟩
    · show ⟨p, n / p⟩ ∈ buchSigmaR_bs P Q A B
      rw [buchSigmaR_bs, Finset.mem_sigma]
      refine ⟨hp.1, ?_⟩
      rw [mem_natIcc (show (0:ℝ) ≤ B / p by positivity), Nat.cast_div hpn hp0.ne']
      exact ⟨div_le_div_of_nonneg_right hnlo hp0.le, div_le_div_of_nonneg_right hnhi hp0.le⟩
    · rw [Nat.div_mul_cancel hpn]

/-- The total coefficient of `n^z` in the right-hand side is `a n`. -/
lemma fiber_sumR_eq_bs (a b c : ℕ → ℂ) (P Q A B : ℝ) (hA : 0 < A) (hAB : A ≤ B) (hP : 2 ≤ P)
    (hPQ : P ≤ Q)
    (hzero : ∀ n : ℕ, (∀ p : ℕ, Nat.Prime p → P ≤ (p : ℝ) → (p : ℝ) ≤ Q → ¬ p ∣ n) →
      a n = 0)
    (hmul : ∀ m p : ℕ, Nat.Prime p → P ≤ (p : ℝ) → (p : ℝ) ≤ Q → ¬ p ∣ m →
      a (m * p) = b m * c p)
    {n : ℕ} (hn : n ∈ Work.BMF.natIcc A B) :
    ∑ x ∈ (buchSigmaR_bs P Q A B).filter (fun x => x.2 * x.1 = n), buchF a b c P Q x = a n := by
  have hinj : Set.InjOn (fun p => (⟨p, n / p⟩ : Σ _ : ℕ, ℕ))
      ↑((primeSet P Q).filter (fun p => p ∣ n)) :=
    fun a1 _ a2 _ h => by simpa using congrArg Sigma.fst h
  rw [image_fiberR_bs hA hAB hn, Finset.sum_image hinj]
  have hn1 : 1 ≤ n := by
    have hn' := (mem_natIcc (le_trans hA.le hAB)).mp hn
    have : (0:ℝ) < (n:ℝ) := lt_of_lt_of_le hA hn'.1
    exact_mod_cast this
  have hcard : ((primeSet P Q).filter (fun p => p ∣ n)).card = omegaCount P Q n :=
    card_primeSet_filter_dvd hn1
  have hcongr : ∑ p ∈ (primeSet P Q).filter (fun p => p ∣ n),
        buchF a b c P Q (⟨p, n / p⟩ : Σ _ : ℕ, ℕ)
      = ∑ p ∈ (primeSet P Q).filter (fun p => p ∣ n),
        a n * (((omegaCount P Q n : ℕ) : ℕ) : ℂ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mem_filter] at hp
    exact buchF_eval a b c hP hPQ hmul hp.1 hp.2
  rw [hcongr, Finset.sum_const, hcard, nsmul_eq_mul]
  by_cases h0 : omegaCount P Q n = 0
  · rw [h0]
    have haz : a n = 0 := a_eq_zero_of_omegaCount_zero a hn1 hzero h0
    simp [haz]
  · have hcc : (((omegaCount P Q n : ℕ) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast h0
    calc (((omegaCount P Q n : ℕ) : ℕ) : ℂ) *
            (a n * (((omegaCount P Q n : ℕ) : ℕ) : ℂ)⁻¹)
          = a n * ((((omegaCount P Q n : ℕ) : ℕ) : ℂ) *
              (((omegaCount P Q n : ℕ) : ℕ) : ℂ)⁻¹) := by ring
        _ = a n := by rw [mul_inv_cancel₀ hcc, mul_one]

/-- **Range Buchstab/Ramaré identity**: `Σ_{A ≤ n ≤ B} a n n^{-(1+it)}` equals the main term
plus the `p²`-correction. -/
theorem dirPolyR_eq_mainAR_add_ep2R_bs (a b c : ℕ → ℂ) (P Q A B : ℝ) (hA : 0 < A) (hAB : A ≤ B)
    (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (hzero : ∀ n : ℕ, (∀ p : ℕ, Nat.Prime p → P ≤ (p : ℝ) → (p : ℝ) ≤ Q → ¬ p ∣ n) → a n = 0)
    (hmul : ∀ m p : ℕ, Nat.Prime p → P ≤ (p : ℝ) → (p : ℝ) ≤ Q → ¬ p ∣ m →
      a (m * p) = b m * c p) :
    ∀ t : ℝ, Work.BMF.mrDirect.dirPolyR a A B t
      = Work.BMF.mrDirect.mainAR b c P Q A B t + Work.BMF.mrDirect.ep2R a b c P Q A B t := by
  intro t
  have hcomb : mainAR b c P Q A B t + ep2R a b c P Q A B t =
      ∑ x ∈ buchSigmaR_bs P Q A B, buchF a b c P Q x * buchE t x := by
    rw [mainAR_sigma_bs b c P Q A B t, ep2R_sigma_bs a b c P Q A B t, Finset.sum_filter,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    unfold buchF
    by_cases h : x.1 ∣ x.2
    · rw [ite_eq_left h, ite_eq_left h]; ring
    · rw [ite_eq_right h, ite_eq_right h]; ring
  have hstep : ∑ x ∈ buchSigmaR_bs P Q A B, buchF a b c P Q x * buchE t x =
      ∑ n ∈ Work.BMF.natIcc A B, a n * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := buchSigmaR_bs P Q A B) (t := Work.BMF.natIcc A B)
      (g := fun x : Σ _ : ℕ, ℕ => x.2 * x.1)
      (fun x hx => phi_memR_bs hA hAB hx) (fun x : Σ _ : ℕ, ℕ => buchF a b c P Q x * buchE t x)]
    apply Finset.sum_congr rfl
    intro n hn
    have hcong : ∑ x ∈ (buchSigmaR_bs P Q A B).filter (fun x => x.2 * x.1 = n),
          buchF a b c P Q x * buchE t x
        = ∑ x ∈ (buchSigmaR_bs P Q A B).filter (fun x => x.2 * x.1 = n),
          buchF a b c P Q x * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [buchE, hx.2]
    rw [hcong, ← Finset.sum_mul, fiber_sumR_eq_bs a b c P Q A B hA hAB hP hPQ hzero hmul hn]
  rw [hcomb, hstep]
  rfl

end

end Work.BMF.mr_direct

namespace Work.BMF.mr_direct

open MeasureTheory intervalIntegral
open scoped BigOperators
open Work.BMF.mrDirect

noncomputable section

/-- The number of window indices is at most `K log (Q/P) + 2`. -/
lemma indexSet_card_le' (K P Q : ℝ) (hK : 0 < K) (hP : 1 < P) (hPQ : P ≤ Q) :
    ((indexSet K P Q).card : ℝ) ≤ K * Real.log (Q / P) + 2 := by
  have hQ1 : 1 ≤ Q := le_trans hP.le hPQ
  have hPpos : 0 < P := lt_trans zero_lt_one hP
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ1
  rcases le_or_gt ⌊K * Real.log P⌋₊ ⌊K * Real.log Q⌋₊ with h | h
  · have hcast : (((⌊K * Real.log Q⌋₊ + 1 - ⌊K * Real.log P⌋₊ : ℕ)) : ℝ)
        = ((⌊K * Real.log Q⌋₊ : ℕ) : ℝ) + 1 - ((⌊K * Real.log P⌋₊ : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : ⌊K * Real.log P⌋₊ ≤ ⌊K * Real.log Q⌋₊ + 1)]
      push_cast
      ring
    rw [indexSet, Nat.card_Icc, hcast]
    have h1 : ((⌊K * Real.log Q⌋₊ : ℕ) : ℝ) ≤ K * Real.log Q :=
      Nat.floor_le (mul_nonneg hK.le (Real.log_nonneg hQ1))
    have h2 : K * Real.log P < ((⌊K * Real.log P⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : Real.log Q - Real.log P = Real.log (Q / P) :=
      (Real.log_div (ne_of_gt hQpos) (ne_of_gt hPpos)).symm
    nlinarith [h1, h2, h3, hK]
  · rw [indexSet, Nat.card_Icc]
    have hzero : ⌊K * Real.log Q⌋₊ + 1 - ⌊K * Real.log P⌋₊ = 0 :=
      Nat.sub_eq_zero_of_le (by omega)
    rw [hzero, Nat.cast_zero]
    have hlog : 0 ≤ Real.log (Q / P) := Real.log_nonneg (by rw [le_div_iff₀ hPpos]; linarith)
    nlinarith [hlog, hK]

/-- The integral over a set of a sum of four integrable functions. -/
lemma setIntegral_four (f g h k : ℝ → ℝ) (u : Set ℝ)
    (hf : IntegrableOn f u) (hg : IntegrableOn g u) (hh : IntegrableOn h u)
    (hk : IntegrableOn k u) :
    (∫ x in u, (f x + g x + h x + k x))
      = (∫ x in u, f x) + (∫ x in u, g x) + (∫ x in u, h x) + (∫ x in u, k x) := by
  have h1 : IntegrableOn (fun x => f x + g x) u := hf.add hg
  have h2 : IntegrableOn (fun x => (f x + g x) + h x) u := h1.add hh
  rw [MeasureTheory.integral_add h2 hk, MeasureTheory.integral_add h1 hh,
    MeasureTheory.integral_add hf hg]

/-- **The supported case** of the range Buchstab/Ramaré bound over a subset of `[-S,S]`:
for `a` vanishing on the integers having no prime factor in `[P,Q]`. -/
theorem buchstab_set_supported (C₀ : ℝ) (hC₀ : Work.BMF.mrDirect.MVConst C₀)
    (a b c : ℕ → ℂ) (X₁ X₂ K P Q S : ℝ) (u : Set ℝ)
    (hX1 : 1 ≤ X₁) (hX12 : X₁ ≤ X₂) (hX24 : X₂ ≤ 4 * X₁)
    (hK : 1 ≤ K) (hP : 2 ≤ P) (hPQ : P ≤ Q) (hS : 0 ≤ S)
    (hu : MeasurableSet u) (husub : u ⊆ Set.Icc (-S) S)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, (∀ p : ℕ, Nat.Prime p → P ≤ (p : ℝ) → (p : ℝ) ≤ Q → ¬ p ∣ n) →
      a n = 0)
    (hmul : ∀ m p : ℕ, Nat.Prime p → P ≤ (p : ℝ) → (p : ℝ) ≤ Q → ¬ p ∣ m →
      a (m * p) = b m * c p) :
    (∫ t in u, ‖Work.BMF.mrDirect.dirPolyR a X₁ X₂ t‖ ^ 2) ≤
      max 4 (1000000000 * (C₀ + 1)) *
        (K * Real.log (Q / P) *
            (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
              ∫ t in u, ‖Work.BMF.mrDirect.primePoly c K j t *
                Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
          + (S + X₂) / X₁ * (1 / K + 1 / P)) := by
  have hApos : 0 < X₁ := lt_of_lt_of_le zero_lt_one hX1
  have hBpos : (0 : ℝ) ≤ X₂ := le_trans hApos.le hX12
  have hB1 : 1 ≤ X₂ := le_trans hX1 hX12
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hPpos : 0 < P := by linarith
  have hCnn : 0 ≤ C₀ := MVConst.nonneg hC₀
  set T1 : ℝ := K * Real.log (Q / P) *
      (∑ j ∈ indexSet K P Q,
        ∫ t in u, ‖primePoly c K j t * remPolyR b P Q K X₁ X₂ j t‖ ^ 2) with hT1
  set T2 : ℝ := (S + X₂) / X₁ * (1 / K + 1 / P) with hT2
  have hT1nn : 0 ≤ T1 := by
    rw [hT1]
    refine mul_nonneg (mul_nonneg (by linarith) ?_) ?_
    · apply Real.log_nonneg
      rw [le_div_iff₀ hPpos]
      linarith
    · exact Finset.sum_nonneg fun j _ => integral_nonneg (fun t => by positivity)
  have hT2nn : 0 ≤ T2 := by rw [hT2]; positivity
  have hMnn : (0 : ℝ) ≤ max 4 (1000000000 * (C₀ + 1)) :=
    le_trans (by norm_num) (le_max_left _ _)
  have hgoal : (∫ t in u, ‖dirPolyR a X₁ X₂ t‖ ^ 2)
      ≤ max 4 (1000000000 * (C₀ + 1)) * (T1 + T2) := by
    by_cases hPB : P ≤ X₂
    · by_cases hbig : 1 ≤ K * Real.log (Q / P)
      · -- ### Case A: the Buchstab decomposition
        have hId1 : ∀ t : ℝ,
            dirPolyR a X₁ X₂ t = mainAR b c P Q X₁ X₂ t + ep2R a b c P Q X₁ X₂ t :=
          fun t => dirPolyR_eq_mainAR_add_ep2R_bs a b c P Q X₁ X₂ hApos hX12 hP hPQ hasupp hmul t
        have hId2 : ∀ t : ℝ, mainAR b c P Q X₁ X₂ t
            = mainBR b c K P Q X₁ X₂ t - eboundR b c K P Q X₁ X₂ t :=
          fun t => mainAR_eq_mainBR_sub_eboundR b c K P Q X₁ X₂ hKpos hP hPQ hApos hBpos t
        have hId3 : ∀ t : ℝ,
            (∑ j ∈ indexSet K P Q, primePoly c K j t * remPolyR b P Q K X₁ X₂ j t)
              = mainBR b c K P Q X₁ X₂ t + dupExtraR b c K P Q X₁ X₂ t :=
          fun t => mainTermR_eq_mainBR_add_dupExtraR b c K P Q X₁ X₂ hKpos hP hPQ t
        have hDecomp : ∀ t : ℝ, dirPolyR a X₁ X₂ t =
            (∑ j ∈ indexSet K P Q, primePoly c K j t * remPolyR b P Q K X₁ X₂ j t)
              - (dupExtraR b c K P Q X₁ X₂ t + eboundR b c K P Q X₁ X₂ t
                  - ep2R a b c P Q X₁ X₂ t) := by
          intro t
          rw [hId3 t, hId1 t, hId2 t]
          ring
        have hpt : ∀ t : ℝ, ‖dirPolyR a X₁ X₂ t‖ ^ 2
            ≤ 4 * ‖∑ j ∈ indexSet K P Q,
                  primePoly c K j t * remPolyR b P Q K X₁ X₂ j t‖ ^ 2
              + 4 * ‖dupExtraR b c K P Q X₁ X₂ t‖ ^ 2
              + 4 * ‖eboundR b c K P Q X₁ X₂ t‖ ^ 2
              + 4 * ‖ep2R a b c P Q X₁ X₂ t‖ ^ 2 := by
          intro t
          rw [hDecomp t]
          set w₁ := (∑ j ∈ indexSet K P Q,
            primePoly c K j t * remPolyR b P Q K X₁ X₂ j t) with hw1
          set w₂ := (dupExtraR b c K P Q X₁ X₂ t + eboundR b c K P Q X₁ X₂ t
            - ep2R a b c P Q X₁ X₂ t) with hw2
          have h1 : ‖w₁ - w₂‖ ≤ ‖w₁‖ + ‖w₂‖ := norm_sub_le w₁ w₂
          have h2 : ‖w₂‖ ≤ ‖dupExtraR b c K P Q X₁ X₂ t‖ + ‖eboundR b c K P Q X₁ X₂ t‖
              + ‖ep2R a b c P Q X₁ X₂ t‖ := by
            rw [hw2]
            have h2a := norm_sub_le (dupExtraR b c K P Q X₁ X₂ t + eboundR b c K P Q X₁ X₂ t)
              (ep2R a b c P Q X₁ X₂ t)
            have h2b := norm_add_le (dupExtraR b c K P Q X₁ X₂ t) (eboundR b c K P Q X₁ X₂ t)
            linarith
          have h3 : ‖w₁ - w₂‖ ≤ ‖w₁‖ + ‖dupExtraR b c K P Q X₁ X₂ t‖
              + ‖eboundR b c K P Q X₁ X₂ t‖ + ‖ep2R a b c P Q X₁ X₂ t‖ := by linarith
          have h5 : ‖w₁ - w₂‖ ^ 2 ≤ (‖w₁‖ + ‖dupExtraR b c K P Q X₁ X₂ t‖
              + ‖eboundR b c K P Q X₁ X₂ t‖ + ‖ep2R a b c P Q X₁ X₂ t‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h3 2
          exact le_trans h5 (by
            nlinarith [sq_nonneg (‖w₁‖ - ‖dupExtraR b c K P Q X₁ X₂ t‖),
              sq_nonneg (‖w₁‖ - ‖eboundR b c K P Q X₁ X₂ t‖),
              sq_nonneg (‖w₁‖ - ‖ep2R a b c P Q X₁ X₂ t‖),
              sq_nonneg (‖dupExtraR b c K P Q X₁ X₂ t‖ - ‖eboundR b c K P Q X₁ X₂ t‖),
              sq_nonneg (‖dupExtraR b c K P Q X₁ X₂ t‖ - ‖ep2R a b c P Q X₁ X₂ t‖),
              sq_nonneg (‖eboundR b c K P Q X₁ X₂ t‖ - ‖ep2R a b c P Q X₁ X₂ t‖)])
        have hcontG : Continuous fun t => 4 * ‖∑ j ∈ indexSet K P Q,
              primePoly c K j t * remPolyR b P Q K X₁ X₂ j t‖ ^ 2
            + 4 * ‖dupExtraR b c K P Q X₁ X₂ t‖ ^ 2
            + 4 * ‖eboundR b c K P Q X₁ X₂ t‖ ^ 2
            + 4 * ‖ep2R a b c P Q X₁ X₂ t‖ ^ 2 :=
          (((Continuous.const_mul
              ((continuous_MT_R b c K P Q X₁ X₂ hApos).norm.pow 2) 4).add
            (Continuous.const_mul
              ((continuous_dupExtraR b c K P Q X₁ X₂ hApos).norm.pow 2) 4)).add
            (Continuous.const_mul
              ((continuous_eboundR b c K P Q X₁ X₂ hApos hP hPQ).norm.pow 2) 4)).add
            (Continuous.const_mul
              ((continuous_ep2R a b c P Q X₁ X₂ hApos).norm.pow 2) 4)
        have hsplit : (∫ t in u, ‖dirPolyR a X₁ X₂ t‖ ^ 2)
            ≤ 4 * (∫ t in u, ‖∑ j ∈ indexSet K P Q,
                    primePoly c K j t * remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
              + 4 * (∫ t in u, ‖dupExtraR b c K P Q X₁ X₂ t‖ ^ 2)
              + 4 * (∫ t in u, ‖eboundR b c K P Q X₁ X₂ t‖ ^ 2)
              + 4 * (∫ t in u, ‖ep2R a b c P Q X₁ X₂ t‖ ^ 2) := by
          have h1 : (∫ t in u, ‖dirPolyR a X₁ X₂ t‖ ^ 2)
              ≤ ∫ t in u, (4 * ‖∑ j ∈ indexSet K P Q,
                    primePoly c K j t * remPolyR b P Q K X₁ X₂ j t‖ ^ 2
                  + 4 * ‖dupExtraR b c K P Q X₁ X₂ t‖ ^ 2
                  + 4 * ‖eboundR b c K P Q X₁ X₂ t‖ ^ 2
                  + 4 * ‖ep2R a b c P Q X₁ X₂ t‖ ^ 2) :=
            setIntegral_mono_of_le_on ((continuous_dirPolyR a X₁ X₂ hApos).norm.pow 2).measurable
              hcontG.measurable (hcontG.continuousOn.integrableOn_Icc.mono_set husub)
              (fun x => sq_nonneg _) (fun x _ => hpt x)
          have hInt1 : IntegrableOn (fun t => 4 * ‖∑ j ∈ indexSet K P Q,
                primePoly c K j t * remPolyR b P Q K X₁ X₂ j t‖ ^ 2) u :=
            (((Continuous.const_mul
                ((continuous_MT_R b c K P Q X₁ X₂ hApos).norm.pow 2) 4)).continuousOn.integrableOn_Icc).mono_set husub
          have hInt2 : IntegrableOn (fun t => 4 * ‖dupExtraR b c K P Q X₁ X₂ t‖ ^ 2) u :=
            (((Continuous.const_mul
                ((continuous_dupExtraR b c K P Q X₁ X₂ hApos).norm.pow 2) 4)).continuousOn.integrableOn_Icc).mono_set husub
          have hInt3 : IntegrableOn (fun t => 4 * ‖eboundR b c K P Q X₁ X₂ t‖ ^ 2) u :=
            (((Continuous.const_mul
                ((continuous_eboundR b c K P Q X₁ X₂ hApos hP hPQ).norm.pow 2) 4)).continuousOn.integrableOn_Icc).mono_set husub
          have hInt4 : IntegrableOn (fun t => 4 * ‖ep2R a b c P Q X₁ X₂ t‖ ^ 2) u :=
            (((Continuous.const_mul
                ((continuous_ep2R a b c P Q X₁ X₂ hApos).norm.pow 2) 4)).continuousOn.integrableOn_Icc).mono_set husub
          have h2 := setIntegral_four
            (fun t => 4 * ‖∑ j ∈ indexSet K P Q,
                  primePoly c K j t * remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
            (fun t => 4 * ‖dupExtraR b c K P Q X₁ X₂ t‖ ^ 2)
            (fun t => 4 * ‖eboundR b c K P Q X₁ X₂ t‖ ^ 2)
            (fun t => 4 * ‖ep2R a b c P Q X₁ X₂ t‖ ^ 2) u hInt1 hInt2 hInt3 hInt4
          rw [h2] at h1
          simpa only [MeasureTheory.integral_const_mul] using h1
        have hIu_le : (∫ t in u, ‖∑ j ∈ indexSet K P Q,
              primePoly c K j t * remPolyR b P Q K X₁ X₂ j t‖ ^ 2) ≤ 3 * T1 := by
          have hcard := indexSet_card_le' K P Q hKpos (by linarith) hPQ
          have hcard3 : ((indexSet K P Q).card : ℝ) ≤ 3 * (K * Real.log (Q / P)) := by
            nlinarith [hcard, hbig]
          have hsum := mainTermR_set_integral_le c b K P Q X₁ X₂ S hApos hS u hu husub
          have hsum_nn : (0 : ℝ) ≤ ∑ j ∈ indexSet K P Q,
              ∫ t in u, ‖primePoly c K j t * remPolyR b P Q K X₁ X₂ j t‖ ^ 2 :=
            Finset.sum_nonneg fun j _ => integral_nonneg (fun t => by positivity)
          calc (∫ t in u, ‖∑ j ∈ indexSet K P Q,
                primePoly c K j t * remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
              ≤ ((indexSet K P Q).card : ℝ) *
                  (∑ j ∈ indexSet K P Q,
                    ∫ t in u, ‖primePoly c K j t * remPolyR b P Q K X₁ X₂ j t‖ ^ 2) := hsum
            _ ≤ (3 * (K * Real.log (Q / P))) *
                  (∑ j ∈ indexSet K P Q,
                    ∫ t in u, ‖primePoly c K j t * remPolyR b P Q K X₁ X₂ j t‖ ^ 2) :=
                mul_le_mul_of_nonneg_right hcard3 hsum_nn
            _ = 3 * T1 := by rw [hT1]; ring
        have hIdup : (∫ t in u, ‖dupExtraR b c K P Q X₁ X₂ t‖ ^ 2)
            ≤ (2 * S + 3 * C₀ * (X₂ * Real.exp (1 / K))) *
                (200000 / X₁ * (1 / K + 1 / P) + 100 / (P * X₁)) :=
          le_trans (setIntegral_le_intervalIntegral hS husub
            ((continuous_dupExtraR b c K P Q X₁ X₂ hApos).norm.pow 2)
            (fun x _ => sq_nonneg _))
            (dupExtraR_integral_le C₀ hC₀ b c K P Q X₁ X₂ S hX1 hX12 hX24 hK hP hPQ hb hc hS)
        have hIeb : (∫ t in u, ‖eboundR b c K P Q X₁ X₂ t‖ ^ 2)
            ≤ (2 * S + 3 * C₀ * (X₂ * Real.exp (1 / K))) *
                ((8 * X₂ / K + 8) * Real.exp 2 / X₁ ^ 2) :=
          le_trans (setIntegral_le_intervalIntegral hS husub
            ((continuous_eboundR b c K P Q X₁ X₂ hApos hP hPQ).norm.pow 2)
            (fun x _ => sq_nonneg _))
            (eboundR_integral_le C₀ hC₀ b c K P Q X₁ X₂ S hX1 hX12 hX24 hK hP hPQ hb hc hS)
        have hIep : (∫ t in u, ‖ep2R a b c P Q X₁ X₂ t‖ ^ 2)
            ≤ (2 * S + 3 * C₀ * X₂) * (100 / (P * X₁)) :=
          ep2R_subset_integral_le C₀ hC₀ a b c P Q X₁ X₂ S ha hb hc hX1 hX12 hX24 hP hPQ hS
            u hu husub
        have he_e : Real.exp (1 / K) ≤ 3 := by
          have h1 : (1 : ℝ) / K ≤ 1 := by rw [div_le_one hKpos]; linarith
          calc Real.exp (1 / K) ≤ Real.exp 1 := Real.exp_le_exp.mpr h1
            _ ≤ 3 := le_of_lt Real.exp_one_lt_three
        have he2 : Real.exp 2 ≤ 9 := by
          have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          rw [h2]
          nlinarith [Real.exp_pos 1, le_of_lt Real.exp_one_lt_three]
        have hP4 : P ≤ 4 * X₁ := le_trans hPB hX24
        have hcoef9 : 2 * S + 3 * C₀ * (X₂ * Real.exp (1 / K))
            ≤ 9 * (C₀ + 1) * (S + X₂) := by
          have h1 : 3 * C₀ * (X₂ * Real.exp (1 / K)) ≤ 3 * C₀ * (X₂ * 3) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left he_e hBpos
          nlinarith [hCnn, hS, hBpos, h1]
        have hcoef3 : 2 * S + 3 * C₀ * X₂ ≤ 3 * (C₀ + 1) * (S + X₂) := by
          nlinarith [hCnn, hS, hBpos]
        have hId_le : (∫ t in u, ‖dupExtraR b c K P Q X₁ X₂ t‖ ^ 2)
            ≤ 10000000 * (C₀ + 1) * T2 := by
          have hbr : 200000 / X₁ * (1 / K + 1 / P) + 100 / (P * X₁)
              ≤ 200100 / X₁ * (1 / K + 1 / P) := by
            have hle : (1 : ℝ) / P ≤ 1 / K + 1 / P := by
              have : (0 : ℝ) ≤ 1 / K := by positivity
              linarith
            have h1 : 100 / (P * X₁) ≤ 100 / X₁ * (1 / K + 1 / P) := by
              calc 100 / (P * X₁) = 100 / X₁ * (1 / P) := by ring
                _ ≤ 100 / X₁ * (1 / K + 1 / P) :=
                    mul_le_mul_of_nonneg_left hle (by positivity)
            have h2 : 200000 / X₁ * (1 / K + 1 / P) + 100 / X₁ * (1 / K + 1 / P)
                = 200100 / X₁ * (1 / K + 1 / P) := by ring
            linarith
          calc (∫ t in u, ‖dupExtraR b c K P Q X₁ X₂ t‖ ^ 2)
              ≤ (2 * S + 3 * C₀ * (X₂ * Real.exp (1 / K))) *
                  (200000 / X₁ * (1 / K + 1 / P) + 100 / (P * X₁)) := hIdup
            _ ≤ (9 * (C₀ + 1) * (S + X₂)) * (200100 / X₁ * (1 / K + 1 / P)) :=
                mul_le_mul hcoef9 hbr (by positivity) (by positivity)
            _ = 200100 * 9 * (C₀ + 1) * T2 := by rw [hT2]; ring
            _ ≤ 10000000 * (C₀ + 1) * T2 := by
              have hle : (200100 : ℝ) * 9 ≤ 10000000 := by norm_num
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hle (by linarith : (0 : ℝ) ≤ C₀ + 1)) hT2nn
        have hIe_le : (∫ t in u, ‖eboundR b c K P Q X₁ X₂ t‖ ^ 2)
            ≤ 10000000 * (C₀ + 1) * T2 := by
          have hbr : (8 * X₂ / K + 8) * Real.exp 2 / X₁ ^ 2
              ≤ 32 * 9 * (1 / X₁ * (1 / K + 1 / P)) := by
            have h1 : (8 * X₂ / K + 8) / X₁ ≤ 32 * (1 / K + 1 / P) := by
              have ha' : 8 * X₂ / K / X₁ ≤ 32 / K := by
                rw [div_div, div_le_iff₀ (by positivity : (0 : ℝ) < K * X₁)]
                have h2 : (32 / K) * (K * X₁) = 32 * X₁ := by field_simp
                rw [h2]
                linarith
              have hb' : 8 / X₁ ≤ 32 / P := by
                rw [div_le_div_iff₀ hApos hPpos]
                linarith
              have hsum := add_le_add ha' hb'
              have hsplit : (8 * X₂ / K + 8) / X₁ = 8 * X₂ / K / X₁ + 8 / X₁ := by ring
              rw [hsplit, show (32 : ℝ) * (1 / K + 1 / P) = 32 / K + 32 / P by ring]
              exact hsum
            calc (8 * X₂ / K + 8) * Real.exp 2 / X₁ ^ 2
                = ((8 * X₂ / K + 8) / X₁) * (Real.exp 2 / X₁) := by ring
              _ ≤ (32 * (1 / K + 1 / P)) * (9 / X₁) := by
                  apply mul_le_mul h1 _ (by positivity) (by positivity)
                  exact div_le_div_of_nonneg_right he2 hApos.le
              _ = 32 * 9 * (1 / X₁ * (1 / K + 1 / P)) := by ring
          calc (∫ t in u, ‖eboundR b c K P Q X₁ X₂ t‖ ^ 2)
              ≤ (2 * S + 3 * C₀ * (X₂ * Real.exp (1 / K))) *
                  ((8 * X₂ / K + 8) * Real.exp 2 / X₁ ^ 2) := hIeb
            _ ≤ (9 * (C₀ + 1) * (S + X₂)) * (32 * 9 * (1 / X₁ * (1 / K + 1 / P))) :=
                mul_le_mul hcoef9 hbr (by positivity) (by positivity)
            _ = 32 * 9 * 9 * (C₀ + 1) * T2 := by rw [hT2]; ring
            _ ≤ 10000000 * (C₀ + 1) * T2 := by
              have hle : (32 : ℝ) * 9 * 9 ≤ 10000000 := by norm_num
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hle (by linarith : (0 : ℝ) ≤ C₀ + 1)) hT2nn
        have hIp_le : (∫ t in u, ‖ep2R a b c P Q X₁ X₂ t‖ ^ 2)
            ≤ 10000000 * (C₀ + 1) * T2 := by
          have hbr : 100 / (P * X₁) ≤ 100 * (1 / X₁ * (1 / K + 1 / P)) := by
            have hle : (1 : ℝ) / P ≤ 1 / K + 1 / P := by
              have : (0 : ℝ) ≤ 1 / K := by positivity
              linarith
            calc 100 / (P * X₁) = 100 * (1 / X₁ * (1 / P)) := by ring
              _ ≤ 100 * (1 / X₁ * (1 / K + 1 / P)) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle (by positivity))
                    (by norm_num)
          calc (∫ t in u, ‖ep2R a b c P Q X₁ X₂ t‖ ^ 2)
              ≤ (2 * S + 3 * C₀ * X₂) * (100 / (P * X₁)) := hIep
            _ ≤ (3 * (C₀ + 1) * (S + X₂)) * (100 * (1 / X₁ * (1 / K + 1 / P))) :=
                mul_le_mul hcoef3 hbr (by positivity) (by positivity)
            _ = 300 * (C₀ + 1) * T2 := by rw [hT2]; ring
            _ ≤ 10000000 * (C₀ + 1) * T2 := by
              have hle : (300 : ℝ) ≤ 10000000 := by norm_num
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hle (by linarith : (0 : ℝ) ≤ C₀ + 1)) hT2nn
        have hMge : (1000000000 : ℝ) * (C₀ + 1)
            ≤ max 4 (1000000000 * (C₀ + 1)) := le_max_right _ _
        calc (∫ t in u, ‖dirPolyR a X₁ X₂ t‖ ^ 2)
            ≤ 4 * (∫ t in u, ‖∑ j ∈ indexSet K P Q,
                  primePoly c K j t * remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
              + 4 * (∫ t in u, ‖dupExtraR b c K P Q X₁ X₂ t‖ ^ 2)
              + 4 * (∫ t in u, ‖eboundR b c K P Q X₁ X₂ t‖ ^ 2)
              + 4 * (∫ t in u, ‖ep2R a b c P Q X₁ X₂ t‖ ^ 2) := hsplit
          _ ≤ 4 * (3 * T1) + 4 * (10000000 * (C₀ + 1) * T2)
              + 4 * (10000000 * (C₀ + 1) * T2) + 4 * (10000000 * (C₀ + 1) * T2) := by
              linarith [hIu_le, hId_le, hIe_le, hIp_le]
          _ = 12 * T1 + 120000000 * (C₀ + 1) * T2 := by ring
          _ ≤ max 4 (1000000000 * (C₀ + 1)) * T1
              + max 4 (1000000000 * (C₀ + 1)) * T2 := by
              apply add_le_add
              · apply mul_le_mul_of_nonneg_right _ hT1nn
                nlinarith [hMge, hCnn]
              · have h1 : (120000000 : ℝ) * (C₀ + 1) ≤ 1000000000 * (C₀ + 1) :=
                  mul_le_mul_of_nonneg_right (by norm_num) (by linarith : (0 : ℝ) ≤ C₀ + 1)
                exact mul_le_mul_of_nonneg_right (le_trans h1 hMge) hT2nn
          _ = max 4 (1000000000 * (C₀ + 1)) * (T1 + T2) := by ring
      · -- ### Case B: `K log (Q/P) < 1`, counting only
        have hsmall : K * Real.log (Q / P) < 1 := not_le.mp hbig
        have hb2 : (∫ t in u, ‖dirPolyR a X₁ X₂ t‖ ^ 2) ≤ 10000000 * (C₀ + 1) * T2 := by
          rw [hT2]
          exact buchstab_smallK_set C₀ hC₀ a b c X₁ X₂ K P Q S u hX1 hX12 hX24 hK hP hPQ hS
            hasupp hmul ha hu husub hsmall
        calc (∫ t in u, ‖dirPolyR a X₁ X₂ t‖ ^ 2) ≤ 10000000 * (C₀ + 1) * T2 := hb2
          _ ≤ max 4 (1000000000 * (C₀ + 1)) * (T1 + T2) := by
              have h1 : (10000000 : ℝ) * (C₀ + 1) ≤ 1000000000 * (C₀ + 1) :=
                mul_le_mul_of_nonneg_right (by norm_num) (by linarith : (0 : ℝ) ≤ C₀ + 1)
              have h2 : (10000000 : ℝ) * (C₀ + 1) * T2 ≤ (1000000000 * (C₀ + 1)) * T2 :=
                mul_le_mul_of_nonneg_right h1 hT2nn
              have h3 : (1000000000 * (C₀ + 1)) * T2
                  ≤ max 4 (1000000000 * (C₀ + 1)) * T2 :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) hT2nn
              have h4 : max 4 (1000000000 * (C₀ + 1)) * T2
                  ≤ max 4 (1000000000 * (C₀ + 1)) * (T1 + T2) :=
                mul_le_mul_of_nonneg_left (by linarith [hT1nn]) hMnn
              linarith
    · -- ### The degenerate case `X₂ < P`: `a` vanishes on the range
      have hvanish : ∀ n ∈ Work.BMF.natIcc X₁ X₂, a n = 0 := by
        intro n hn
        rw [Work.BMF.natIcc, Finset.mem_Icc] at hn
        have hn1 : 1 ≤ n := by
          have h1 : (1 : ℝ) ≤ (⌈X₁⌉₊ : ℝ) := le_trans hX1 (Nat.le_ceil X₁)
          have h2 : 1 ≤ ⌈X₁⌉₊ := by exact_mod_cast h1
          exact le_trans h2 hn.1
        have hnB : (n : ℝ) ≤ X₂ := le_trans (by exact_mod_cast hn.2) (Nat.floor_le hBpos)
        exact hasupp n (fun p hpp hPp hpQ hpd => by
          have hpn : p ≤ n := Nat.le_of_dvd (by omega) hpd
          have hcast : (p : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpn
          linarith [hcast, hnB, hPp, not_le.mp hPB])
      have hzero_poly : ∀ t : ℝ, dirPolyR a X₁ X₂ t = 0 := by
        intro t
        unfold dirPolyR
        exact Finset.sum_eq_zero fun n hn => by rw [hvanish n hn, zero_mul]
      have hLHS0 : (∫ t in u, ‖dirPolyR a X₁ X₂ t‖ ^ 2) = 0 := by simp [hzero_poly]
      rw [hLHS0]
      exact mul_nonneg hMnn (add_nonneg hT1nn hT2nn)
  exact hgoal

end

end Work.BMF.mr_direct

namespace Work.BMF.mr_direct

open MeasureTheory intervalIntegral
open scoped BigOperators
open Work.BMF.mrDirect

noncomputable section

theorem buchstab_set :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X₁ X₂ K P Q S : ℝ) (a b c : ℕ → ℂ) (u : Set ℝ),
      1 ≤ X₁ → X₁ ≤ X₂ → X₂ ≤ 4 * X₁ → 1 ≤ K → 2 ≤ P → P ≤ Q → 0 ≤ S →
      MeasurableSet u → u ⊆ Set.Icc (-S) S →
      (∀ n, ‖a n‖ ≤ 1) → (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ m p : ℕ, Nat.Prime p → P ≤ (p : ℝ) → (p : ℝ) ≤ Q → ¬ p ∣ m →
        a (m * p) = b m * c p) →
      (∫ t in u, ‖Work.BMF.mrDirect.dirPolyR a X₁ X₂ t‖ ^ 2) ≤
        C * (K * Real.log (Q / P) *
              (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
                ∫ t in u,
                  ‖Work.BMF.mrDirect.primePoly c K j t *
                    Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
          + (S + X₂) / X₁ * (1 / K + 1 / P +
              ∑ n ∈ (Work.BMF.natIcc X₁ X₂).filter
                (fun n => n.Coprime (∏ p ∈ Work.BMF.primesIn P Q, p)),
                ‖a n‖ ^ 2 / (n : ℝ))) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies
  have hCnn : 0 ≤ C₀ := MVConst.nonneg hC₀
  have hMpos : 0 < max 4 (1000000000 * (C₀ + 1)) :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨2 * max 4 (1000000000 * (C₀ + 1)) + 6 * (C₀ + 1) + 1,
    by linarith [hMpos, hCnn], ?_⟩
  intro X₁ X₂ K P Q S a b c u hX1 hX12 hX24 hK hP hPQ hS hu husub ha hb hc hmul
  classical
  have hApos : 0 < X₁ := lt_of_lt_of_le zero_lt_one hX1
  set Scop : ℝ := ∑ n ∈ (Work.BMF.natIcc X₁ X₂).filter
      (fun n => n.Coprime (∏ p ∈ Work.BMF.primesIn P Q, p)), ‖a n‖ ^ 2 / (n : ℝ) with hScop
  set T1 : ℝ := K * Real.log (Q / P) *
      (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
        ∫ t in u, ‖Work.BMF.mrDirect.primePoly c K j t *
          Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2) with hT1
  set Tbig : ℝ := (S + X₂) / X₁ * (1 / K + 1 / P + Scop) with hTbig
  set T2 : ℝ := (S + X₂) / X₁ * (1 / K + 1 / P) with hT2
  set T3 : ℝ := (S + X₂) / X₁ * Scop with hT3
  have hbig_eq : Tbig = T2 + T3 := by rw [hTbig, hT2, hT3]; ring
  -- the two parts of `a`
  set asup : ℕ → ℂ := fun n =>
    if ∃ p : ℕ, Nat.Prime p ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ p ∣ n then a n else 0 with hasupdef
  set acop : ℕ → ℂ := fun n =>
    if ∃ p : ℕ, Nat.Prime p ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ p ∣ n then 0 else a n with hacopdef
  have hasup_val : ∀ n, asup n = (if ∃ p : ℕ, Nat.Prime p ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ p ∣ n
      then a n else 0) := fun n => by rw [hasupdef]
  have hacop_val : ∀ n, acop n = (if ∃ p : ℕ, Nat.Prime p ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ p ∣ n
      then 0 else a n) := fun n => by rw [hacopdef]
  have hasup_add : ∀ n, asup n + acop n = a n := by
    intro n
    rw [hasup_val n, hacop_val n]
    by_cases h : ∃ p : ℕ, Nat.Prime p ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ p ∣ n <;> simp [h]
  have hasup_le : ∀ n, ‖asup n‖ ≤ 1 := by
    intro n
    rw [hasup_val n]
    by_cases h : ∃ p : ℕ, Nat.Prime p ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ p ∣ n
    · rw [if_pos h]; exact ha n
    · rw [if_neg h, norm_zero]; norm_num
  have hacop_le : ∀ n, ‖acop n‖ ≤ 1 := by
    intro n
    rw [hacop_val n]
    by_cases h : ∃ p : ℕ, Nat.Prime p ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ p ∣ n
    · rw [if_pos h, norm_zero]; norm_num
    · rw [if_neg h]; exact ha n
  have hasup_zero : ∀ n, (∀ p : ℕ, Nat.Prime p → P ≤ (p : ℝ) → (p : ℝ) ≤ Q → ¬ p ∣ n) →
      asup n = 0 := by
    intro n h
    rw [hasup_val n]
    rw [if_neg]
    rintro ⟨p, hpp, hPp, hpQ, hpd⟩
    exact h p hpp hPp hpQ hpd
  have hacop_zero : ∀ n, (∃ p : ℕ, Nat.Prime p ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ p ∣ n) →
      acop n = 0 := by
    intro n h
    rw [hacop_val n, if_pos h]
  have hasup_mul : ∀ m p : ℕ, Nat.Prime p → P ≤ (p : ℝ) → (p : ℝ) ≤ Q → ¬ p ∣ m →
      asup (m * p) = b m * c p := by
    intro m p hpp hPp hpQ hpd
    rw [hasup_val (m * p), if_pos ⟨p, hpp, hPp, hpQ, dvd_mul_left p m⟩]
    exact hmul m p hpp hPp hpQ hpd
  -- Step 1: split `a`
  have hsplit1 : (∫ t in u, ‖dirPolyR a X₁ X₂ t‖ ^ 2)
      ≤ 2 * (∫ t in u, ‖dirPolyR asup X₁ X₂ t‖ ^ 2)
        + 2 * (∫ t in u, ‖dirPolyR acop X₁ X₂ t‖ ^ 2) := by
    have hpt : ∀ t : ℝ, ‖dirPolyR a X₁ X₂ t‖ ^ 2
        ≤ 2 * ‖dirPolyR asup X₁ X₂ t‖ ^ 2 + 2 * ‖dirPolyR acop X₁ X₂ t‖ ^ 2 := by
      intro t
      have heq : dirPolyR a X₁ X₂ t = dirPolyR asup X₁ X₂ t + dirPolyR acop X₁ X₂ t := by
        unfold dirPolyR
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro n _
        rw [← hasup_add n]
        ring
      rw [heq]
      have h2 : ‖dirPolyR asup X₁ X₂ t + dirPolyR acop X₁ X₂ t‖
          ≤ ‖dirPolyR asup X₁ X₂ t‖ + ‖dirPolyR acop X₁ X₂ t‖ := norm_add_le _ _
      calc ‖dirPolyR asup X₁ X₂ t + dirPolyR acop X₁ X₂ t‖ ^ 2
          ≤ (‖dirPolyR asup X₁ X₂ t‖ + ‖dirPolyR acop X₁ X₂ t‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h2 2
        _ ≤ 2 * ‖dirPolyR asup X₁ X₂ t‖ ^ 2 + 2 * ‖dirPolyR acop X₁ X₂ t‖ ^ 2 := by
            nlinarith [sq_nonneg (‖dirPolyR asup X₁ X₂ t‖ - ‖dirPolyR acop X₁ X₂ t‖)]
    have hcontH : Continuous fun t => 2 * ‖dirPolyR asup X₁ X₂ t‖ ^ 2
        + 2 * ‖dirPolyR acop X₁ X₂ t‖ ^ 2 :=
      (Continuous.const_mul ((continuous_dirPolyR asup X₁ X₂ hApos).norm.pow 2) 2).add
        (Continuous.const_mul ((continuous_dirPolyR acop X₁ X₂ hApos).norm.pow 2) 2)
    have h1 : (∫ t in u, ‖dirPolyR a X₁ X₂ t‖ ^ 2)
        ≤ ∫ t in u, (2 * ‖dirPolyR asup X₁ X₂ t‖ ^ 2
            + 2 * ‖dirPolyR acop X₁ X₂ t‖ ^ 2) :=
      setIntegral_mono_of_le_on ((continuous_dirPolyR a X₁ X₂ hApos).norm.pow 2).measurable
        hcontH.measurable (hcontH.continuousOn.integrableOn_Icc.mono_set husub)
        (fun x => sq_nonneg _) (fun x _ => hpt x)
    have hIntA : IntegrableOn (fun t => 2 * ‖dirPolyR asup X₁ X₂ t‖ ^ 2) u :=
      (((Continuous.const_mul ((continuous_dirPolyR asup X₁ X₂ hApos).norm.pow 2) 2)).continuousOn.integrableOn_Icc).mono_set husub
    have hIntB : IntegrableOn (fun t => 2 * ‖dirPolyR acop X₁ X₂ t‖ ^ 2) u :=
      (((Continuous.const_mul ((continuous_dirPolyR acop X₁ X₂ hApos).norm.pow 2) 2)).continuousOn.integrableOn_Icc).mono_set husub
    rw [MeasureTheory.integral_add hIntA hIntB] at h1
    simpa only [MeasureTheory.integral_const_mul] using h1
  have hT1nn : 0 ≤ T1 := by
    rw [hT1]
    refine mul_nonneg (mul_nonneg (by linarith) ?_) ?_
    · apply Real.log_nonneg
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < P)]
      linarith
    · exact Finset.sum_nonneg fun j _ => integral_nonneg (fun t => by positivity)
  have hT2nn : 0 ≤ T2 := by
    rw [hT2]
    exact mul_nonneg (div_nonneg (by linarith [hS, hApos.le, hX12]) hApos.le) (by positivity)
  have hScopnn : 0 ≤ Scop := by
    rw [hScop]
    exact Finset.sum_nonneg fun n _ => by positivity
  have hT3nn : 0 ≤ T3 := by
    rw [hT3]
    exact mul_nonneg (div_nonneg (by linarith [hS, hApos.le, hX12]) hApos.le) hScopnn
  -- Step 2: the supported part
  have hsup_bd : (∫ t in u, ‖dirPolyR asup X₁ X₂ t‖ ^ 2)
      ≤ max 4 (1000000000 * (C₀ + 1)) * (T1 + T2) := by
    have h := buchstab_set_supported C₀ hC₀ asup b c X₁ X₂ K P Q S u
      hX1 hX12 hX24 hK hP hPQ hS hu husub hasup_le hb hc hasup_zero hasup_mul
    rw [← hT1, ← hT2] at h
    exact h
  -- Step 3: the rough part
  have hcop_bd : (∫ t in u, ‖dirPolyR acop X₁ X₂ t‖ ^ 2) ≤ 3 * (C₀ + 1) * T3 := by
    have h := rough_set_integral_le C₀ hC₀ acop X₁ X₂ P Q S u hX1 hX12 hS hu husub
      hacop_le hacop_zero
    have hsum_eq : (∑ n ∈ (Work.BMF.natIcc X₁ X₂).filter
          (fun n => n.Coprime (∏ p ∈ Work.BMF.primesIn P Q, p)),
          ‖acop n‖ ^ 2 / (n : ℝ)) = Scop := by
      rw [hScop]
      apply Finset.sum_congr rfl
      intro n hn
      have hcop := (Finset.mem_filter.mp hn).2
      have hane : acop n = a n := by
        rw [hacop_val n, if_neg]
        rintro ⟨p, hpp, hPp, hpQ, hpd⟩
        exact (coprime_primesIn_iff n P Q).mp hcop p hpp hPp hpQ hpd
      rw [hane]
    rw [hsum_eq, ← hT3] at h
    exact h
  -- Step 4: assemble
  have hMnn : (0 : ℝ) ≤ max 4 (1000000000 * (C₀ + 1)) := le_of_lt hMpos
  calc (∫ t in u, ‖dirPolyR a X₁ X₂ t‖ ^ 2)
      ≤ 2 * (∫ t in u, ‖dirPolyR asup X₁ X₂ t‖ ^ 2)
        + 2 * (∫ t in u, ‖dirPolyR acop X₁ X₂ t‖ ^ 2) := hsplit1
    _ ≤ 2 * (max 4 (1000000000 * (C₀ + 1)) * (T1 + T2)) + 2 * (3 * (C₀ + 1) * T3) := by
        linarith [hsup_bd, hcop_bd]
    _ = 2 * max 4 (1000000000 * (C₀ + 1)) * (T1 + T2) + 6 * (C₀ + 1) * T3 := by ring
    _ ≤ (2 * max 4 (1000000000 * (C₀ + 1)) + 6 * (C₀ + 1) + 1) * (T1 + T2 + T3) := by
        have h1 : 2 * max 4 (1000000000 * (C₀ + 1)) * (T1 + T2)
            ≤ (2 * max 4 (1000000000 * (C₀ + 1)) + 6 * (C₀ + 1) + 1) * (T1 + T2) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith [hT1nn, hT2nn])
          linarith
        have h2 : 6 * (C₀ + 1) * T3
            ≤ (2 * max 4 (1000000000 * (C₀ + 1)) + 6 * (C₀ + 1) + 1) * T3 := by
          apply mul_le_mul_of_nonneg_right _ hT3nn
          linarith
        linarith [h1, h2]
    _ = (2 * max 4 (1000000000 * (C₀ + 1)) + 6 * (C₀ + 1) + 1) * (T1 + Tbig) := by
        rw [hbig_eq]; ring

end

end Work.BMF.mr_direct
