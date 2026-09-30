import Mathlib
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_direct.buchstab_aux
import Submission.Work.BMF.mr_direct.omegaCount_mul_prime
import Submission.Work.BMF.mr_direct.card_primeSet_filter_dvd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Buchstab/Ramaré identity `dirPolyM = mainA + ep2`

This file proves `Work.BMF.mr_direct.dirPolyM_eq_mainA_add_ep2`, the first (exact, pointwise)
step of the Buchstab/Ramaré decomposition of Matomäki–Radziwiłł (Lemma `lem:decomp`).

Writing `z = -(1+it)` and `φ(⟨p,m⟩) = m·p`, both sides are reorganised as sums of
`(coefficient) · n^z` over `n ∈ [X, 2X]`:

* the left-hand side is `Σ_{X ≤ n ≤ 2X} a n · n^z` by definition;
* the right-hand side is, after `Finset.sum_sigma` and `Finset.sum_fiberwise_of_maps_to`,
  `Σ_{X ≤ n ≤ 2X} (Σ_{φ x = n} buchF x) · n^z`.

The fibre `{x : φ x = n}` is in bijection with the primes `p ∈ [P,Q]` dividing `n`, and for each
such `p` the coefficient `buchF ⟨p, n/p⟩` equals `a n / ω(n;P,Q)` — either because `p ∣ n/p`
(so the `if`-branch contributes and `ω(m·p) = ω(m)`) or because `a(m·p) = b m c p` and
`ω(m·p) = ω(m)+1`.  Summing over the `ω(n;P,Q)` primes gives `a n`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.BMF.mr_direct

open Finset
open scoped BigOperators
open Work.BMF.mrDirect (primeSet omegaCount mem_natIcc mem_primeSet mem_primeSet' mainA ep2 dirPolyM)

noncomputable section

/-- The sigma-index set of the Buchstab decomposition: pairs `(p, m)` with `p` a prime in
`[P, Q]` and `m ∈ [X/p, 2X/p]`. -/
def buchSigma (P Q X : ℝ) : Finset (Σ _ : ℕ, ℕ) :=
  (primeSet P Q).sigma (fun p => Work.BMF.natIcc (X / p) (2 * X / p))

/-- The value `(m·p)^{-(1+it)}` attached to the pair `(p, m)`. -/
def buchE (t : ℝ) (x : Σ _ : ℕ, ℕ) : ℂ :=
  (((x.2 * x.1 : ℕ)) : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))

/-- The coefficient of the pair `(p, m)` in the Buchstab decomposition. -/
def buchF (a b c : ℕ → ℂ) (P Q : ℝ) (x : Σ _ : ℕ, ℕ) : ℂ :=
  c x.1 * b x.2 * (((omegaCount P Q x.2 : ℕ) + 1 : ℕ) : ℂ)⁻¹ +
    (if x.1 ∣ x.2 then
      a (x.2 * x.1) * (((omegaCount P Q x.2 : ℕ) : ℕ) : ℂ)⁻¹ -
        b x.2 * c x.1 * (((omegaCount P Q x.2 : ℕ) + 1 : ℕ) : ℂ)⁻¹
    else 0)

/-- `mainA` as a sum over the sigma-type of pairs `(p, m)`. -/
lemma mainA_sigma (b c : ℕ → ℂ) (P Q X t : ℝ) :
    mainA b c P Q X t =
      ∑ x ∈ buchSigma P Q X,
        (c x.1 * b x.2 * (((omegaCount P Q x.2 : ℕ) + 1 : ℕ) : ℂ)⁻¹) * buchE t x := by
  rw [mainA, buchSigma, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [buchE, Nat.cast_mul, Complex.natCast_mul_natCast_cpow m p]
  ring

/-- `ep2` as a sum over the sigma-type of pairs `(p, m)` with `p ∣ m`. -/
lemma ep2_sigma (a b c : ℕ → ℂ) (P Q X t : ℝ) :
    ep2 a b c P Q X t =
      ∑ x ∈ (buchSigma P Q X).filter (fun x => x.1 ∣ x.2),
        (a (x.2 * x.1) * (((omegaCount P Q x.2 : ℕ) : ℕ) : ℂ)⁻¹ -
          b x.2 * c x.1 * (((omegaCount P Q x.2 : ℕ) + 1 : ℕ) : ℂ)⁻¹) * buchE t x := by
  rw [ep2, buchSigma, Finset.filter_sigma, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun p hp => ?_
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [buchE, Nat.cast_mul, Complex.natCast_mul_natCast_cpow m p]

/-- The map `(p,m) ↦ m·p` sends the sigma-type into `[X, 2X]`. -/
lemma phi_mem {P Q X : ℝ} (hX : 0 < X) {x : Σ _ : ℕ, ℕ} (hx : x ∈ buchSigma P Q X) :
    (x.2 * x.1 : ℕ) ∈ Work.BMF.natIcc X (2 * X) := by
  rw [buchSigma, Finset.mem_sigma] at hx
  obtain ⟨h1, h2⟩ := hx
  have hp : Nat.Prime x.1 := (Finset.mem_filter.mp h1).2
  have hp2 : (2:ℝ) ≤ (x.1:ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0:ℝ) < (x.1:ℝ) := by linarith
  rw [mem_natIcc (by linarith : (0:ℝ) ≤ 2 * X)]
  obtain ⟨hm1, hm2⟩ := (mem_natIcc (show (0:ℝ) ≤ 2 * X / x.1 by positivity)).mp h2
  constructor
  · have h : (x.1:ℝ) * (X / x.1) ≤ (x.1:ℝ) * (x.2:ℝ) :=
      mul_le_mul_of_nonneg_left hm1 hp0.le
    rw [show (x.1:ℝ) * (X / x.1) = X by field_simp] at h
    calc X ≤ (x.1:ℝ) * (x.2:ℝ) := h
      _ = ((x.2 * x.1 : ℕ):ℝ) := by push_cast; ring
  · have h : (x.2:ℝ) * (x.1:ℝ) ≤ (2 * X / x.1) * (x.1:ℝ) :=
      mul_le_mul_of_nonneg_right hm2 hp0.le
    rw [show (2 * X / x.1) * (x.1:ℝ) = 2 * X by field_simp] at h
    calc ((x.2 * x.1 : ℕ):ℝ) = (x.2:ℝ) * (x.1:ℝ) := by push_cast; ring
      _ ≤ 2 * X := h

/-- The fibre `{x : x.2·x.1 = n}` of `buchSigma` over `n ∈ [X,2X]` is the image of the primes
`p ∈ [P,Q]` dividing `n` under `p ↦ ⟨p, n/p⟩`. -/
lemma image_fiber {P Q X : ℝ} (hX : 0 < X) {n : ℕ} (hn : n ∈ Work.BMF.natIcc X (2 * X)) :
    (buchSigma P Q X).filter (fun x => x.2 * x.1 = n) =
      ((primeSet P Q).filter (fun p => p ∣ n)).image
        (fun p => (⟨p, n / p⟩ : Σ _ : ℕ, ℕ)) := by
  ext x
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hx, hxphi⟩
    rw [buchSigma] at hx
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
    obtain ⟨hnlo, hnhi⟩ := (mem_natIcc (by linarith : (0:ℝ) ≤ 2*X)).mp hn
    refine ⟨?_, ?_⟩
    · show ⟨p, n / p⟩ ∈ buchSigma P Q X
      rw [buchSigma, Finset.mem_sigma]
      refine ⟨hp.1, ?_⟩
      rw [mem_natIcc (show (0:ℝ) ≤ 2 * X / p by positivity), Nat.cast_div hpn hp0.ne']
      exact ⟨div_le_div_of_nonneg_right hnlo hp0.le, div_le_div_of_nonneg_right hnhi hp0.le⟩
    · rw [Nat.div_mul_cancel hpn]

/-- If `ω(n;P,Q) = 0` then no prime of `[P,Q]` divides `n`, hence `a n = 0`. -/
lemma a_eq_zero_of_omegaCount_zero (a : ℕ → ℂ) {P Q : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hzero : ∀ n : ℕ, (∀ p : ℕ, Nat.Prime p → P ≤ (p : ℝ) → (p : ℝ) ≤ Q → ¬ p ∣ n) → a n = 0)
    (h : omegaCount P Q n = 0) : a n = 0 := by
  apply hzero
  intro p hpp hPp hpQ hpd
  have hcard : ((primeSet P Q).filter (fun p => p ∣ n)).card = 0 := by
    rw [card_primeSet_filter_dvd hn]; exact h
  have hempty : (primeSet P Q).filter (fun p => p ∣ n) = ∅ := Finset.card_eq_zero.mp hcard
  have : p ∉ (primeSet P Q).filter (fun p => p ∣ n) := by rw [hempty]; simp
  exact this (Finset.mem_filter.mpr ⟨mem_primeSet' hpp hPp hpQ, hpd⟩)

/-- For a prime `p ∈ [P,Q]` dividing `n`, the coefficient of the pair `(p, n/p)` is
`a n / ω(n;P,Q)`. -/
lemma buchF_eval (a b c : ℕ → ℂ) {P Q : ℝ} (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (hmul : ∀ m p : ℕ, Nat.Prime p → P ≤ (p : ℝ) → (p : ℝ) ≤ Q → ¬ p ∣ m →
      a (m * p) = b m * c p)
    {n p : ℕ} (hp : p ∈ primeSet P Q) (hpn : p ∣ n) :
    buchF a b c P Q (⟨p, n / p⟩ : Σ _ : ℕ, ℕ) =
      a n * (((omegaCount P Q n : ℕ) : ℕ) : ℂ)⁻¹ := by
  obtain ⟨hpp, hPp, hpQ⟩ := (mem_primeSet (by linarith : (0:ℝ) ≤ Q)).mp hp
  have hmp : n / p * p = n := Nat.div_mul_cancel hpn
  rw [buchF]
  by_cases hpdm : p ∣ n / p
  · rw [ite_eq_left hpdm]
    have homega : omegaCount P Q n = omegaCount P Q (n / p) := by
      have h := omegaCount_mul_prime (P := P) (Q := Q) (m := n / p) (p := p) hpp hPp hpQ
      rw [ite_eq_left hpdm, hmp] at h
      simpa using h
    rw [homega, hmp]
    ring
  · rw [ite_eq_right hpdm]
    have homega : omegaCount P Q n = omegaCount P Q (n / p) + 1 := by
      have h := omegaCount_mul_prime (P := P) (Q := Q) (m := n / p) (p := p) hpp hPp hpQ
      rw [ite_eq_right hpdm, hmp] at h
      simpa using h
    have haeq : a n = b (n / p) * c p := by
      have h := hmul (n / p) p hpp hPp hpQ hpdm
      rwa [hmp] at h
    rw [homega, haeq]
    ring

/-- The total coefficient of `n^z` in the right-hand side is `a n`. -/
lemma fiber_sum_eq (a b c : ℕ → ℂ) (P Q X : ℝ) (hX : 0 < X) (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (hzero : ∀ n : ℕ, (∀ p : ℕ, Nat.Prime p → P ≤ (p : ℝ) → (p : ℝ) ≤ Q → ¬ p ∣ n) →
      a n = 0)
    (hmul : ∀ m p : ℕ, Nat.Prime p → P ≤ (p : ℝ) → (p : ℝ) ≤ Q → ¬ p ∣ m →
      a (m * p) = b m * c p)
    {n : ℕ} (hn : n ∈ Work.BMF.natIcc X (2 * X)) :
    ∑ x ∈ (buchSigma P Q X).filter (fun x => x.2 * x.1 = n), buchF a b c P Q x = a n := by
  have hinj : Set.InjOn (fun p => (⟨p, n / p⟩ : Σ _ : ℕ, ℕ))
      ↑((primeSet P Q).filter (fun p => p ∣ n)) :=
    fun a1 _ a2 _ h => by simpa using congrArg Sigma.fst h
  rw [image_fiber (P := P) (Q := Q) hX hn, Finset.sum_image hinj]
  have hn1 : 1 ≤ n := by
    have hn' := (mem_natIcc (by linarith : (0:ℝ) ≤ 2*X)).mp hn
    have : (0:ℝ) < (n:ℝ) := lt_of_lt_of_le hX hn'.1
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

/-- **Buchstab/Ramaré identity** (Matomäki–Radziwiłł, Lemma `lem:decomp`, first step):
`Σ_{X ≤ n ≤ 2X} a n n^{-(1+it)}` equals the main term plus the `p²`-correction. -/
theorem dirPolyM_eq_mainA_add_ep2 (a b c : ℕ → ℂ) (P Q X : ℝ) (hX : 0 < X) (hP : 2 ≤ P)
    (hPQ : P ≤ Q)
    (hzero : ∀ n : ℕ, (∀ p : ℕ, Nat.Prime p → P ≤ (p : ℝ) → (p : ℝ) ≤ Q → ¬ p ∣ n) →
      a n = 0)
    (hmul : ∀ m p : ℕ, Nat.Prime p → P ≤ (p : ℝ) → (p : ℝ) ≤ Q → ¬ p ∣ m →
      a (m * p) = b m * c p) :
    ∀ t : ℝ,
      Work.BMF.mrDirect.dirPolyM a X t =
        Work.BMF.mrDirect.mainA b c P Q X t + Work.BMF.mrDirect.ep2 a b c P Q X t := by
  intro t
  have hcomb : mainA b c P Q X t + ep2 a b c P Q X t =
      ∑ x ∈ buchSigma P Q X, buchF a b c P Q x * buchE t x := by
    rw [mainA_sigma b c P Q X t, ep2_sigma a b c P Q X t, Finset.sum_filter,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    unfold buchF
    by_cases h : x.1 ∣ x.2
    · rw [ite_eq_left h, ite_eq_left h]; ring
    · rw [ite_eq_right h, ite_eq_right h]; ring
  have hstep : ∑ x ∈ buchSigma P Q X, buchF a b c P Q x * buchE t x =
      ∑ n ∈ Work.BMF.natIcc X (2 * X), a n * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := buchSigma P Q X) (t := Work.BMF.natIcc X (2 * X))
      (g := fun x : Σ _ : ℕ, ℕ => x.2 * x.1)
      (fun x hx => phi_mem hX hx) (fun x : Σ _ : ℕ, ℕ => buchF a b c P Q x * buchE t x)]
    apply Finset.sum_congr rfl
    intro n hn
    have hcong : ∑ x ∈ (buchSigma P Q X).filter (fun x => x.2 * x.1 = n),
          buchF a b c P Q x * buchE t x
        = ∑ x ∈ (buchSigma P Q X).filter (fun x => x.2 * x.1 = n),
          buchF a b c P Q x * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [buchE, hx.2]
    rw [hcong, ← Finset.sum_mul, fiber_sum_eq a b c P Q X hX hP hPQ hzero hmul hn]
  rw [hcomb, hstep]
  rfl

end

end Work.BMF.mr_direct
