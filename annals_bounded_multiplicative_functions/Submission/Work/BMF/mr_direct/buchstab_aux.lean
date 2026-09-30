import Mathlib
import Submission.Work.BMF.mr_direct_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary vocabulary for `Work.BMF.mr_direct.buchstab_identity`

Sets of primes / integers used by the Buchstab (Ramaré) decomposition:
`primeSet P Q` are the primes in `[P,Q]`, `winPrimes K j` are the primes in the `j`-th
logarithmic window `[e^{j/K}, e^{(j+1)/K}]` (the index set of `primePoly`), and `winIdx K X j`
is the integer window of `remPoly`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.BMF

open MeasureTheory intervalIntegral
open scoped BigOperators

namespace mrDirect

noncomputable section

/-- The primes in the real interval `[P, Q]`. -/
def primeSet (P Q : ℝ) : Finset ℕ := (Finset.Icc ⌈P⌉₊ ⌊Q⌋₊).filter Nat.Prime

/-- The primes in the `j`-th logarithmic window `[e^{j/K}, e^{(j+1)/K}]` that lie in `[P,Q]`. -/
def primesJ (K P Q : ℝ) (j : ℕ) : Finset ℕ :=
  ((Finset.Icc ⌈Real.exp ((j : ℝ) / K)⌉₊ ⌊Real.exp (((j : ℝ) + 1) / K)⌋₊).filter
    Nat.Prime).filter (fun p => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q)

/-- The primes in the `j`-th logarithmic window (the index set of `primePoly`). -/
def winPrimes (K : ℝ) (j : ℕ) : Finset ℕ :=
  (Finset.Icc ⌈Real.exp ((j : ℝ) / K)⌉₊ ⌊Real.exp (((j : ℝ) + 1) / K)⌋₊).filter Nat.Prime

/-- The integer window of `remPoly`: `ℕ ∩ [X e^{-(j+1)/K}, 2X e^{-j/K}]`. -/
def winIdx (K X : ℝ) (j : ℕ) : Finset ℕ :=
  Work.BMF.natIcc (X * Real.exp (-((j : ℝ) + 1) / K)) (2 * X * Real.exp (-(j : ℝ) / K))

/-- The logarithmic window containing a prime `p`: `j = ⌊K log p⌋`. -/
def jdex (K : ℝ) (p : ℕ) : ℕ := ⌊K * Real.log (p : ℝ)⌋₊

/-- Membership in `natIcc`, as real inequalities. -/
lemma mem_natIcc {a b : ℝ} {n : ℕ} (hb : 0 ≤ b) :
    n ∈ Work.BMF.natIcc a b ↔ a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b := by
  rw [Work.BMF.natIcc, Finset.mem_Icc]
  constructor
  · intro h
    exact ⟨le_trans (Nat.le_ceil a) (by exact_mod_cast h.1),
      le_trans (by exact_mod_cast h.2) (Nat.floor_le hb)⟩
  · intro h
    exact ⟨Nat.ceil_le.mpr h.1, Nat.le_floor h.2⟩

lemma mem_primeSet {P Q : ℝ} {p : ℕ} (hQ0 : 0 ≤ Q) :
    p ∈ primeSet P Q ↔ p.Prime ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q := by
  rw [primeSet, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨hp, le_trans (Nat.le_ceil P) (by exact_mod_cast h1),
      le_trans (by exact_mod_cast h2) (Nat.floor_le hQ0)⟩
  · rintro ⟨hp, h1, h2⟩
    exact ⟨⟨Nat.ceil_le.mpr h1, Nat.le_floor h2⟩, hp⟩

lemma mem_primeSet' {P Q : ℝ} {p : ℕ} (hp : p.Prime) (hP : P ≤ (p : ℝ)) (hQ : (p : ℝ) ≤ Q) :
    p ∈ primeSet P Q :=
  (mem_primeSet (le_trans (by positivity : (0 : ℝ) ≤ (p : ℝ)) hQ)).mpr ⟨hp, hP, hQ⟩

lemma mem_winPrimes {K : ℝ} {j p : ℕ} :
    p ∈ winPrimes K j ↔
      p.Prime ∧ Real.exp ((j : ℝ) / K) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (((j : ℝ) + 1) / K) := by
  rw [winPrimes, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨hp, le_trans (Nat.le_ceil _) (by exact_mod_cast h1),
      le_trans (by exact_mod_cast h2) (Nat.floor_le (Real.exp_pos _).le)⟩
  · rintro ⟨hp, h1, h2⟩
    exact ⟨⟨Nat.ceil_le.mpr h1, Nat.le_floor h2⟩, hp⟩

lemma mem_winIdx {K X : ℝ} {j m : ℕ} (h : 0 ≤ 2 * X * Real.exp (-(j : ℝ) / K)) :
    m ∈ winIdx K X j ↔
      X * Real.exp (-((j : ℝ) + 1) / K) ≤ (m : ℝ) ∧
        (m : ℝ) ≤ 2 * X * Real.exp (-(j : ℝ) / K) :=
  mem_natIcc h

lemma natIcc_mono {a a' b b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') :
    Work.BMF.natIcc a b ⊆ Work.BMF.natIcc a' b' := by
  intro n hn
  rw [Work.BMF.natIcc, Finset.mem_Icc] at hn ⊢
  exact ⟨le_trans (Nat.ceil_mono ha) hn.1, le_trans hn.2 (Nat.floor_mono hb)⟩

lemma primePoly_eq (c : ℕ → ℂ) (K : ℝ) (j : ℕ) (t : ℝ) :
    primePoly c K j t = ∑ p ∈ winPrimes K j, c p * (p : ℂ) ^ (-(1 + Complex.I * t)) := rfl

lemma remPoly_eq (b : ℕ → ℂ) (P Q K X : ℝ) (j : ℕ) (t : ℝ) :
    remPoly b P Q K X j t =
      ∑ m ∈ winIdx K X j, b m * (((omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ *
        (m : ℂ) ^ (-(1 + Complex.I * t)) := rfl


/-! ### The terms of the Buchstab decomposition -/

/-- `Σ_p c p · p^{-s} · Σ_{X/p ≤ m ≤ 2X/p} b m (ω(m;P,Q)+1)^{-1} m^{-s}`. -/
noncomputable def mainA (b c : ℕ → ℂ) (P Q X : ℝ) (t : ℝ) : ℂ :=
  ∑ p ∈ primeSet P Q, c p * (p : ℂ) ^ (-(1 + Complex.I * t)) *
    ∑ m ∈ Work.BMF.natIcc (X / p) (2 * X / p),
      b m * (((omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ * (m : ℂ) ^ (-(1 + Complex.I * t))

/-- The `p²`-correction term of the Buchstab decomposition. -/
noncomputable def ep2 (a b c : ℕ → ℂ) (P Q X : ℝ) (t : ℝ) : ℂ :=
  ∑ p ∈ primeSet P Q,
    ∑ m ∈ (Work.BMF.natIcc (X / p) (2 * X / p)).filter (fun m => p ∣ m),
      (a (m * p) * (((omegaCount P Q m : ℕ) : ℕ) : ℂ)⁻¹ -
        b m * c p * (((omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹) *
        ((m * p : ℕ) : ℂ) ^ (-(1 + Complex.I * t))

/-- The main term grouped by the canonical window of each prime. -/
noncomputable def mainB (b c : ℕ → ℂ) (K P Q X : ℝ) (t : ℝ) : ℂ :=
  ∑ p ∈ primeSet P Q, c p * (p : ℂ) ^ (-(1 + Complex.I * t)) *
    ∑ m ∈ winIdx K X (jdex K p),
      b m * (((omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ * (m : ℂ) ^ (-(1 + Complex.I * t))

/-- The range-extension error: `mainB - mainA` (a signed sum over the extra range). -/
noncomputable def ebound (b c : ℕ → ℂ) (K P Q X : ℝ) (t : ℝ) : ℂ :=
  ∑ p ∈ primeSet P Q, c p * (p : ℂ) ^ (-(1 + Complex.I * t)) *
    ∑ m ∈ (winIdx K X (jdex K p)).filter
        (fun m => m ∉ Work.BMF.natIcc (X / p) (2 * X / p)),
      b m * (((omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ * (m : ℂ) ^ (-(1 + Complex.I * t))

/-- The error from primes lying in a window but outside `[P,Q]`, or in two windows:
`Σ_j (Σ_{p ∈ winPrimes j, non-canonical} c p p^{-s}) remPoly_j - (main term)`. -/
noncomputable def dupExtra (b c : ℕ → ℂ) (K P Q X : ℝ) (t : ℝ) : ℂ :=
  ∑ j ∈ indexSet K P Q,
    (∑ p ∈ (winPrimes K j).filter
        (fun (p : ℕ) => ¬(P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j = jdex K p)),
      c p * (p : ℂ) ^ (-(1 + Complex.I * t))) * remPoly b P Q K X j t

/-- Index set of `ebound`, as a `sigma`-type. -/
def pSetB (K P Q X : ℝ) : Finset (Σ _ : ℕ, ℕ) :=
  (primeSet P Q).sigma (fun (p : ℕ) => (winIdx K X (jdex K p)).filter
    (fun (m : ℕ) => m ∉ Work.BMF.natIcc (X / p) (2 * X / p)))

/-- Index set of `ep2`, as a `sigma`-type. -/
def pSetE (P Q X : ℝ) : Finset (Σ _ : ℕ, ℕ) :=
  (primeSet P Q).sigma (fun (p : ℕ) =>
    (Work.BMF.natIcc (X / p) (2 * X / p)).filter (fun (m : ℕ) => p ∣ m))

/-- Index set of `dupExtra`, as a `sigma`-type. -/
def pSetD (K P Q X : ℝ) : Finset (Σ _ : Σ _ : ℕ, ℕ, ℕ) :=
  ((indexSet K P Q).sigma (fun (j : ℕ) => (winPrimes K j).filter
      (fun (p : ℕ) => ¬(P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j = jdex K p)))).sigma
    (fun (x : Σ _ : ℕ, ℕ) => winIdx K X x.1)


/-! ### Range lemmas for the canonical window of a prime -/

/-- The canonical window of a prime `p ∈ [P,Q]` lies in `indexSet K P Q`. -/
lemma jdex_mem_indexSet {K P Q : ℝ} {p : ℕ} (hK : 0 < K) (hp : 1 ≤ p) (hP : 0 < P)
    (hPp : P ≤ (p : ℝ)) (hpQ : (p : ℝ) ≤ Q) : jdex K p ∈ indexSet K P Q := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have h1 : Real.log P ≤ Real.log (p : ℝ) := Real.log_le_log hP hPp
  have h2 : Real.log (p : ℝ) ≤ Real.log Q := Real.log_le_log hp0 hpQ
  simp only [indexSet, jdex, Finset.mem_Icc]
  exact ⟨Nat.floor_mono (mul_le_mul_of_nonneg_left h1 hK.le),
    Nat.floor_mono (mul_le_mul_of_nonneg_left h2 hK.le)⟩

/-- A prime lies in its own canonical window. -/
lemma mem_winPrimes_jdex {K : ℝ} {p : ℕ} (hK : 0 < K) (hp : p.Prime) :
    p ∈ winPrimes K (jdex K p) := by
  rw [mem_winPrimes]
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
  refine ⟨hp, ?_, ?_⟩
  · rw [← Real.exp_log hp0]
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ hK, jdex]
    have h := Nat.floor_le (le_of_lt (mul_pos hK hlog))
    linarith
  · rw [← Real.log_le_iff_le_exp hp0, le_div_iff₀ hK, jdex]
    have h := Nat.lt_floor_add_one (K * Real.log (p : ℝ))
    linarith

/-- In a prime window `winPrimes K j`, the index `j` is within `1` of `K log p`. -/
lemma win_idx_bounds {K : ℝ} {j p : ℕ} (hK : 0 < K) (hp : p ∈ winPrimes K j) :
    K * Real.log (p : ℝ) - 1 ≤ (j : ℝ) ∧ (j : ℝ) ≤ K * Real.log (p : ℝ) := by
  obtain ⟨-, h1, h2⟩ := mem_winPrimes.mp hp
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le (Real.exp_pos _) h1
  constructor
  · have h := Real.log_le_log hp0 h2
    rw [Real.log_exp, le_div_iff₀ hK] at h
    linarith
  · have h := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp, div_le_iff₀ hK] at h
    linarith

/-- At most one prime `p` can satisfy `K log p ∈ ℕ`. -/
lemma eq_of_mul_log_eq {K : ℝ} (hK : 0 < K) {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime)
    {m m' : ℕ} (hm : K * Real.log (p : ℝ) = m) (hm' : K * Real.log (p' : ℝ) = m') :
    p = p' := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp2' : (2 : ℝ) ≤ (p' : ℝ) := by exact_mod_cast hp'.two_le
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
  have hlogp' : 0 < Real.log (p' : ℝ) := Real.log_pos (by linarith)
  have key : (m : ℝ) * Real.log (p' : ℝ) = (m' : ℝ) * Real.log (p : ℝ) := by
    rw [← hm, ← hm']; ring
  have h1' : (p' : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log (p' : ℝ)) := by
    conv_lhs => rw [← Real.exp_log (show (0 : ℝ) < (p' : ℝ) by linarith), ← Real.exp_nat_mul]
  have h2' : Real.exp ((m' : ℝ) * Real.log (p : ℝ)) = (p : ℝ) ^ m' := by
    rw [Real.exp_nat_mul, Real.exp_log (show (0 : ℝ) < (p : ℝ) by linarith)]
  have hpow : (p' : ℝ) ^ m = (p : ℝ) ^ m' := by rw [h1', ← h2', key]
  have hnat : p' ^ m = p ^ m' := by exact_mod_cast hpow
  have hm1 : 1 ≤ m := by
    have : (0 : ℝ) < (m : ℝ) := by rw [← hm]; exact mul_pos hK hlogp
    exact_mod_cast this
  have hm'1 : 1 ≤ m' := by
    have : (0 : ℝ) < (m' : ℝ) := by rw [← hm']; exact mul_pos hK hlogp'
    exact_mod_cast this
  have hdvd : p ∣ p' ^ m := by
    rw [hnat]
    exact dvd_pow_self p (by omega)
  have h2 := hp.dvd_of_dvd_pow hdvd
  exact (Nat.prime_dvd_prime_iff_eq hp hp').mp h2

/-- A prime lies in at most two windows. -/
lemma card_winPrimes_le_two {K : ℝ} {p : ℕ} (hK : 0 < K) (hp : p.Prime) :
    ((Finset.range (jdex K p + 1)).filter (fun j => p ∈ winPrimes K j)).card ≤ 2 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
  have hfl : (jdex K p : ℝ) ≤ K * Real.log (p : ℝ) := by
    simp only [jdex]
    exact Nat.floor_le (le_of_lt (mul_pos hK hlog))
  have hfl2 : K * Real.log (p : ℝ) - 1 < (jdex K p : ℝ) := by
    have := Nat.lt_floor_add_one (K * Real.log (p : ℝ))
    simp only [jdex]
    linarith
  have hsub : (Finset.range (jdex K p + 1)).filter (fun j => p ∈ winPrimes K j) ⊆
      Finset.Icc (jdex K p - 1) (jdex K p) := by
    intro j hj
    obtain ⟨h1, h2⟩ := win_idx_bounds hK (Finset.mem_filter.mp hj).2
    rw [Finset.mem_Icc]
    constructor
    · have hle : jdex K p ≤ j + 1 := by
        exact_mod_cast (show (jdex K p : ℝ) ≤ (j : ℝ) + 1 from by linarith)
      omega
    · exact Nat.lt_succ_iff.mp (by
        exact_mod_cast (show (j : ℝ) < (jdex K p : ℝ) + 1 from by linarith))
  refine le_trans (Finset.card_le_card hsub) ?_
  have hpair : Finset.Icc (jdex K p - 1) (jdex K p) ⊆
      ({(jdex K p - 1), (jdex K p)} : Finset ℕ) := by
    intro x hx
    simp only [Finset.mem_Icc] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  refine le_trans (Finset.card_le_card hpair) ?_
  calc (({(jdex K p - 1), (jdex K p)} : Finset ℕ)).card
      = (insert (jdex K p - 1) {jdex K p} : Finset ℕ).card := rfl
    _ ≤ ({jdex K p} : Finset ℕ).card + 1 := Finset.card_insert_le _ _
    _ = 2 := by simp

/-- `[X/p, 2X/p]` is contained in the canonical window of `p`. -/
lemma natIcc_div_subset_winIdx {K X : ℝ} {j : ℕ} {p : ℕ} (hX : 0 < X)
    (hp : p ∈ winPrimes K j) : Work.BMF.natIcc (X / p) (2 * X / p) ⊆ winIdx K X j := by
  obtain ⟨-, h1, h2⟩ := mem_winPrimes.mp hp
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le (Real.exp_pos _) h1
  refine natIcc_mono ?_ ?_
  · have h3 : Real.exp (-((j : ℝ) + 1) / K) ≤ 1 / (p : ℝ) := by
      rw [show -((j : ℝ) + 1) / K = -(((j : ℝ) + 1) / K) by ring, Real.exp_neg, one_div]
      simpa only [one_div] using one_div_le_one_div_of_le (show (0:ℝ) < (p:ℝ) by positivity) h2
    calc X * Real.exp (-((j : ℝ) + 1) / K) ≤ X * (1 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left h3 hX.le
      _ = X / (p : ℝ) := by ring
  · have h4 : 1 / (p : ℝ) ≤ Real.exp (-(j : ℝ) / K) := by
      rw [show -(j : ℝ) / K = -((j : ℝ) / K) by ring, Real.exp_neg, one_div]
      simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos ((j : ℝ) / K)) h1
    calc 2 * X / (p : ℝ) = (2 * X) * (1 / (p : ℝ)) := by ring
      _ ≤ (2 * X) * Real.exp (-(j : ℝ) / K) := mul_le_mul_of_nonneg_left h4 (by positivity)

/-- A prime of a window which is not in `[P,Q]` lies in the "extra range" of `P` or of `Q`. -/
lemma extra_prime_mem {K P Q : ℝ} {j p : ℕ} (hK : 0 < K) (hP : 0 < P) (hQ : 0 < Q)
    (hP1 : 1 ≤ P) (hQ1 : 1 ≤ Q)
    (hj : j ∈ indexSet K P Q) (hp : p ∈ winPrimes K j)
    (hextra : (p : ℝ) < P ∨ Q < (p : ℝ)) :
    p ∈ Work.BMF.primesIn (P * Real.exp (-(1 / K))) P ∪
        Work.BMF.primesIn Q (Q * Real.exp (1 / K)) := by
  obtain ⟨hpp, h1, h2⟩ := mem_winPrimes.mp hp
  rw [indexSet, Finset.mem_Icc] at hj
  have hjlo : (⌊K * Real.log P⌋₊ : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
  have hjhi : (j : ℝ) ≤ (⌊K * Real.log Q⌋₊ : ℝ) := by exact_mod_cast hj.2
  have hfP : K * Real.log P - 1 < (⌊K * Real.log P⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (K * Real.log P); linarith
  have hfQ : (⌊K * Real.log Q⌋₊ : ℝ) ≤ K * Real.log Q :=
    Nat.floor_le (mul_nonneg hK.le (Real.log_nonneg hQ1))
  rcases hextra with hpP | hQp
  · have hlow : P * Real.exp (-(1 / K)) ≤ (p : ℝ) := by
      have hstep : Real.exp ((K * Real.log P - 1) / K) ≤ Real.exp ((j : ℝ) / K) := by
        apply Real.exp_le_exp.mpr
        rw [div_le_div_iff_of_pos_right hK]
        linarith
      refine le_trans ?_ (le_trans hstep h1)
      rw [show (K * Real.log P - 1) / K = -(1 / K) + Real.log P by field_simp; ring]
      rw [Real.exp_add, Real.exp_log hP, mul_comm]
    rw [Finset.mem_union]
    left
    rw [Work.BMF.primesIn, Finset.mem_filter, Work.BMF.natIcc, Finset.mem_Icc]
    exact ⟨⟨Nat.ceil_le.mpr hlow, Nat.le_floor (le_of_lt hpP)⟩, hpp⟩
  · have hhigh : (p : ℝ) ≤ Q * Real.exp (1 / K) := by
      have hstep : Real.exp (((j : ℝ) + 1) / K) ≤ Real.exp ((K * Real.log Q + 1) / K) := by
        apply Real.exp_le_exp.mpr
        rw [div_le_div_iff_of_pos_right hK]
        linarith
      refine le_trans h2 (le_trans hstep ?_)
      rw [show (K * Real.log Q + 1) / K = 1 / K + Real.log Q by field_simp; ring,
        Real.exp_add, Real.exp_log hQ, mul_comm]
    rw [Finset.mem_union]
    right
    rw [Work.BMF.primesIn, Finset.mem_filter, Work.BMF.natIcc, Finset.mem_Icc]
    exact ⟨⟨Nat.ceil_le.mpr (le_of_lt hQp), Nat.le_floor hhigh⟩, hpp⟩

end

end mrDirect

end Work.BMF
