/-
  Companion paper (§5): the estimate `T(x;y,z) ≪ A(x)(log x)^{-2}`.

  `T(x;y,z) = ∑_{b ≤ y} μ(b) ∑_{c ≤ z} Λ(c) V_{bc}(x)` (the object `Tsum2` of `Defs.lean`).
  Following §5 we insert (1.7) into `V_{bc}`; the main terms become
  `∑_ν λ_ν g(ν) (∑_b μ(b)g(b/(ν,b)))(∑_c Λ(c)g(c/(ν,c)))` (with the coupling `c ∤ b`),
  which is bounded by (2.4) and (1.8), and the remainder terms are handled by the `Λ`-fibre
  exchange `∑_{bc} Λ(c)X(bc) ≤ ∑_d (log d)X(d)` and (R′).
-/
import Mathlib
import Submission.ASP.Defs
import Submission.Work.FIChain.LocalS4
import Submission.Work.FIChain.LocalS5
import Submission.Commons.NumberTheory.Sieve.moebius_density_sum_le
import Submission.Commons.NumberTheory.Sieve.sum_mu_g_div_gcd_le
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Commons.NumberTheory.Nat.sum_log_primeFactors_le_log
import Submission.Commons.NumberTheory.Sieve.sum_primes_log_mul_g_div_gcd_le

namespace Submission.ASP

open Finset

noncomputable section

/-! ### Elementary squarefree bookkeeping -/

/-- For `b, c ≥ 1`, `Squarefree (b*c)` means `b`, `c` squarefree and coprime. -/
lemma squarefree_mul_facts {b c : ℕ} (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h : Squarefree (b * c)) : Squarefree b ∧ Squarefree c ∧ Nat.Coprime b c := by
  have hb0 : b ≠ 0 := by omega
  have hc0 : c ≠ 0 := by omega
  refine ⟨Squarefree.of_mul_left h, Squarefree.of_mul_right h, ?_⟩
  rw [Nat.coprime_iff_isRelPrime]
  exact (squarefree_mul_iff.mp h).1

/-- For a prime `p` and squarefree `b`, `b*p` is squarefree iff `p ∤ b`. -/
lemma squarefree_mul_prime_iff {b p : ℕ} (hb : Squarefree b) (hp : p.Prime) :
    Squarefree (b * p) ↔ ¬ p ∣ b := by
  rw [squarefree_mul_iff]
  constructor
  · rintro ⟨hrel, _, _⟩ hdvd
    exact (hp.coprime_iff_not_dvd.mp (Nat.coprime_iff_isRelPrime.mpr hrel).symm) hdvd
  · intro hnd
    refine ⟨?_, hb, hp.squarefree⟩
    rw [← Nat.coprime_iff_isRelPrime]
    exact (hp.coprime_iff_not_dvd.mpr hnd).symm

/-- For coprime `b, c`, the quotients `b/(ν,b)` and `c/(ν,c)` are coprime. -/
lemma coprime_div_gcd_div_gcd {ν b c : ℕ} (h : Nat.Coprime b c) :
    Nat.Coprime (b / Nat.gcd ν b) (c / Nat.gcd ν c) :=
  (Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right ν b)) h).coprime_dvd_right
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right ν c))

/-- `gcd ν (b*c) = gcd ν b * gcd ν c` for coprime `b, c`. -/
lemma gcd_mul_of_coprime {ν b c : ℕ} (h : Nat.Coprime b c) :
    Nat.gcd ν (b * c) = Nat.gcd ν b * Nat.gcd ν c := by
  have hdvd : Nat.gcd ν (b * c) ∣ b * c := Nat.gcd_dvd_right ν (b * c)
  have h1 := (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime (x := Nat.gcd ν (b * c)) h).mpr hdvd
  have h2 : Nat.gcd (Nat.gcd ν (b * c)) b = Nat.gcd ν b := by
    rw [Nat.gcd_assoc, Nat.gcd_eq_right (dvd_mul_right b c)]
  have h3 : Nat.gcd (Nat.gcd ν (b * c)) c = Nat.gcd ν c := by
    rw [Nat.gcd_assoc, Nat.gcd_eq_right (dvd_mul_left c b)]
  rw [← h1, h2, h3]

/-- `(b*c)/(ν,b*c) = (b/(ν,b))*(c/(ν,c))` for coprime `b, c`. -/
lemma div_gcd_mul_div_gcd {ν b c : ℕ} (h : Nat.Coprime b c) (hb : 0 < b) (hc : 0 < c) :
    b * c / Nat.gcd ν (b * c) = b / Nat.gcd ν b * (c / Nat.gcd ν c) := by
  have hg : Nat.gcd ν (b * c) = Nat.gcd ν b * Nat.gcd ν c := gcd_mul_of_coprime h
  have hb' : Nat.gcd ν b * (b / Nat.gcd ν b) = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right ν b)
  have hc' : Nat.gcd ν c * (c / Nat.gcd ν c) = c := Nat.mul_div_cancel' (Nat.gcd_dvd_right ν c)
  have hpos : 0 < Nat.gcd ν b * Nat.gcd ν c :=
    Nat.mul_pos (Nat.gcd_pos_of_pos_right ν hb) (Nat.gcd_pos_of_pos_right ν hc)
  have hnum : b * c = (Nat.gcd ν b * Nat.gcd ν c) * (b / Nat.gcd ν b * (c / Nat.gcd ν c)) := by
    calc b * c = (Nat.gcd ν b * (b / Nat.gcd ν b)) * (Nat.gcd ν c * (c / Nat.gcd ν c)) := by
          rw [hb', hc']
      _ = _ := by ring
  rw [hg, hnum, Nat.mul_div_right _ hpos]

/-- The counting function of the reindexed Möbius sum. -/
def Smu (g : ℕ → ℝ) (ν u : ℕ) : ℝ :=
  ∑ b ∈ Finset.Icc 1 u, (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b)

/-- The Möbius sum restricted to `b` coprime to `p` (the scale `⌊M/p⌋` of §5). -/
def Smup (g : ℕ → ℝ) (ν p u : ℕ) : ℝ :=
  ∑ b ∈ (Finset.Icc 1 u).filter (fun b => ¬ p ∣ b),
    (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b)

/-- The coprime Möbius sum of (2.4). -/
def Gmu (g : ℕ → ℝ) (ν u : ℕ) : ℝ :=
  ∑ b ∈ (Finset.Icc 1 u).filter (fun b => Nat.Coprime b ν),
    (ArithmeticFunction.moebius b : ℝ) * g b

/-! ### The reindexing of the Möbius sum along `b ↦ ((ν,b), b/(ν,b))` -/

/-- For squarefree `b`, `gcd (gcd a b) (b / gcd a b) = 1`. -/
private lemma gcd_gcd_div_gcd_eq_one (a b : ℕ) (hb : Squarefree b) :
    Nat.gcd (Nat.gcd a b) (b / Nat.gcd a b) = 1 := by
  set g := Nat.gcd a b with hg
  have hgdvd : g ∣ b := Nat.gcd_dvd_right a b
  have hgdiv : Nat.gcd g (b / g) ∣ g := Nat.gcd_dvd_left g (b / g)
  have hdiv : Nat.gcd g (b / g) ∣ b / g := Nat.gcd_dvd_right g (b / g)
  have hdvd : Nat.gcd g (b / g) * Nat.gcd g (b / g) ∣ b := by
    have h1 : Nat.gcd g (b / g) * Nat.gcd g (b / g) ∣ g * (b / g) :=
      mul_dvd_mul hgdiv hdiv
    rwa [Nat.mul_div_cancel' hgdvd] at h1
  have := hb _ hdvd
  rwa [Nat.isUnit_iff] at this

/-- For squarefree `b`, `b / gcd a b` is coprime to `a`. -/
private lemma coprime_div_gcd_of_squarefree {a b : ℕ} (hb : Squarefree b) :
    Nat.Coprime (b / Nat.gcd a b) a := by
  rw [Nat.coprime_iff_gcd_eq_one]
  set g := Nat.gcd a b with hg
  set d := Nat.gcd (b / g) a with hd
  have hgb : g * (b / g) = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have h1 : d ∣ a := Nat.gcd_dvd_right (b / g) a
  have h2 : d ∣ b / g := Nat.gcd_dvd_left (b / g) a
  have h3 : d ∣ b := by rw [← hgb]; exact dvd_mul_of_dvd_right h2 g
  have h4 : d ∣ g := by rw [hg]; exact Nat.dvd_gcd h1 h3
  have h5 : d * d ∣ b := by rw [← hgb]; exact mul_dvd_mul h4 h2
  have hunit : IsUnit d := hb d h5
  rw [Nat.isUnit_iff] at hunit
  rw [hd] at hunit
  exact hunit

/-- `gcd ν (b₁*b₀) = b₁` when `b₁ ∣ ν` and `b₀` is coprime to `ν`. -/
private lemma gcd_mul_of_dvd_coprime {ν b₁ b₀ : ℕ} (hb₁ : b₁ ∣ ν) (hcop : Nat.Coprime b₀ ν) :
    Nat.gcd ν (b₁ * b₀) = b₁ := by
  obtain ⟨ν', rfl⟩ := hb₁
  rw [Nat.gcd_mul_left, (hcop.coprime_mul_left_right.symm).gcd_eq_one, mul_one]

/-- `μ(b₁*b₀) = μ(b₁)*μ(b₀)` for coprime arguments, as reals. -/
private lemma moebius_mul_coprime_real {m n : ℕ} (h : Nat.Coprime m n) :
    ((ArithmeticFunction.moebius (m * n) : ℤ) : ℝ)
      = ((ArithmeticFunction.moebius m : ℤ) : ℝ) * ((ArithmeticFunction.moebius n : ℤ) : ℝ) := by
  have hz : ArithmeticFunction.moebius (m * n)
      = ArithmeticFunction.moebius m * ArithmeticFunction.moebius n :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (Nat.coprime_iff_gcd_eq_one.mp h)
  have := congrArg (fun z : ℤ => (z : ℝ)) hz
  simpa using this

/-- The Möbius sum reindexed: `∑_{b ≤ y} μ b g(b/(ν,b)) = ∑_{b₁ ∣ ν} μ b₁ G_ν(⌊y/b₁⌋)`. -/
lemma Smu_eq_reindex {g : ℕ → ℝ} {ν y : ℕ} (hν : Squarefree ν) :
    Smu g ν y
      = ∑ b₁ ∈ ν.divisors, (ArithmeticFunction.moebius b₁ : ℝ) * Gmu g ν (y / b₁) := by
  classical
  have hsq_eq : Smu g ν y
      = ∑ b ∈ (Finset.Icc 1 y).filter (fun b => Squarefree b),
          (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) := by
    rw [Smu, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : Squarefree b
    · rw [if_pos hb]
    · rw [if_neg hb, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hb]; ring
  set Cset : Finset (Sigma (fun _ : ℕ => ℕ)) :=
    ν.divisors.sigma (fun b₁ =>
      (((Finset.Icc 1 (y / b₁)).filter (fun d => Nat.Coprime d ν)).filter
        (fun d => Squarefree d))) with hC
  have hbij : (∑ b ∈ (Finset.Icc 1 y).filter (fun b => Squarefree b),
        (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b))
      = ∑ c ∈ Cset, (ArithmeticFunction.moebius c.1 : ℝ) * (ArithmeticFunction.moebius c.2 : ℝ)
          * g c.2 := by
    refine Finset.sum_bij'
      (fun b _ => (⟨Nat.gcd ν b, b / Nat.gcd ν b⟩ : Sigma (fun _ : ℕ => ℕ)))
      (fun c _ => c.1 * c.2) ?_ ?_ ?_ ?_ ?_
    · intro b hb
      rw [hC, Finset.mem_sigma]
      obtain ⟨hbIcc, hbsq⟩ := Finset.mem_filter.mp hb
      rw [Finset.mem_Icc] at hbIcc
      obtain ⟨hb1, hby⟩ := hbIcc
      have hbpos : 0 < b := by omega
      have hgb : Nat.gcd ν b ∣ b := Nat.gcd_dvd_right ν b
      have hgpos : 0 < Nat.gcd ν b := Nat.pos_of_dvd_of_pos hgb hbpos
      refine ⟨?_, ?_⟩
      · rw [Nat.mem_divisors]; exact ⟨Nat.gcd_dvd_left ν b, hν.ne_zero⟩
      · rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨⟨(Nat.one_le_div_iff hgpos).mpr (Nat.gcd_le_right ν hbpos),
                 Nat.div_le_div_right hby⟩,
                 coprime_div_gcd_of_squarefree hbsq⟩,
                 Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hgb) hbsq⟩
    · intro c hc
      rw [hC, Finset.mem_sigma] at hc
      obtain ⟨hc1mem, hc2mem⟩ := hc
      rw [Finset.mem_filter, Finset.mem_filter] at hc2mem
      obtain ⟨⟨hc2Icc, hc2cop⟩, hc2sq⟩ := hc2mem
      rw [Finset.mem_Icc] at hc2Icc
      obtain ⟨hc21, hc2y⟩ := hc2Icc
      have hc1dvd : c.1 ∣ ν := (Nat.mem_divisors.mp hc1mem).1
      have hc1pos : 0 < c.1 := Nat.pos_of_mem_divisors hc1mem
      have hc1sq : Squarefree c.1 := Squarefree.squarefree_of_dvd hc1dvd hν
      have hcop : Nat.Coprime c.1 c.2 := Nat.Coprime.coprime_dvd_left hc1dvd hc2cop.symm
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have : 0 < c.1 * c.2 := Nat.mul_pos hc1pos (by omega)
        omega
      · have := (Nat.le_div_iff_mul_le hc1pos).mp hc2y
        calc c.1 * c.2 ≤ c.2 * c.1 := by rw [mul_comm]
          _ ≤ y := this
      · exact (Nat.squarefree_mul hcop).mpr ⟨hc1sq, hc2sq⟩
    · intro b hb
      exact Nat.mul_div_cancel' (Nat.gcd_dvd_right ν b)
    · intro c hc
      rw [hC, Finset.mem_sigma] at hc
      obtain ⟨hc1mem, hc2mem⟩ := hc
      rw [Finset.mem_filter, Finset.mem_filter] at hc2mem
      obtain ⟨⟨hc2Icc, hc2cop⟩, _⟩ := hc2mem
      obtain ⟨b₁, b₀⟩ := c
      have hc1dvd : b₁ ∣ ν := (Nat.mem_divisors.mp hc1mem).1
      have hc1pos : 0 < b₁ := Nat.pos_of_mem_divisors hc1mem
      rw [gcd_mul_of_dvd_coprime hc1dvd hc2cop, Nat.mul_div_right b₀ hc1pos]
    · intro b hb
      obtain ⟨_, hbsq⟩ := Finset.mem_filter.mp hb
      have hcop : Nat.Coprime (Nat.gcd ν b) (b / Nat.gcd ν b) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        exact gcd_gcd_div_gcd_eq_one ν b hbsq
      have hnat : Nat.gcd ν b * (b / Nat.gcd ν b) = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right ν b)
      nth_rewrite 1 [← hnat]
      rw [moebius_mul_coprime_real hcop]
  rw [hsq_eq, hbij, hC]
  rw [← Finset.sum_sigma' (ν.divisors)
        (fun b₁ => ((Finset.Icc 1 (y / b₁)).filter (fun d => Nat.Coprime d ν)).filter
          (fun d => Squarefree d))
        (fun a b => (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) * g b)]
  apply Finset.sum_congr rfl
  intro b₁ hb₁
  trans ∑ b₀ ∈ (Finset.Icc 1 (y / b₁)).filter (fun d => Nat.Coprime d ν),
      (ArithmeticFunction.moebius b₁ : ℝ) * (ArithmeticFunction.moebius b₀ : ℝ) * g b₀
  · exact Finset.sum_subset (Finset.filter_subset _ _) (fun b₀ hb₀ hb₀not => by
      rw [Finset.mem_filter] at hb₀not
      push Not at hb₀not
      have hs : ¬ Squarefree b₀ := hb₀not hb₀
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
      ring)
  · rw [Gmu, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b₀ _
    ring

/-- `|μ n| ≤ 1` as a real number. -/
private lemma abs_moebius_cast_le_one (n : ℕ) :
    |(((ArithmeticFunction.moebius n : ℤ)) : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs, ArithmeticFunction.abs_moebius]
  split <;> norm_num

/-- `|G_ν(y)| ≤ 1` for `y ≤ 1`. -/
private lemma Gmu_le_one {g : ℕ → ℝ} (hg1 : g 1 = 1) (ν : ℕ) {y : ℕ} (hy : y ≤ 1) :
    |Gmu g ν y| ≤ 1 := by
  interval_cases y
  · simp [Gmu]
  · rw [Gmu]
    have : (Finset.Icc 1 1).filter (fun b => Nat.Coprime b ν) = {1} := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h1, h2⟩, _⟩; omega
      · rintro rfl; exact ⟨⟨le_rfl, le_rfl⟩, Nat.coprime_one_left ν⟩
    rw [this, Finset.sum_singleton, ArithmeticFunction.moebius_apply_one, hg1]
    norm_num

/-- `(u:ℝ)/(2ν) ≤ max 2 ⌊u/b⌋` for `0 < b ≤ ν`. -/
private lemma div_two_nu_le_max_div {u b ν : ℕ} (hb : 0 < b) (hbν : b ≤ ν) :
    (u : ℝ) / (2 * (ν : ℝ)) ≤ max 2 ((u / b : ℕ) : ℝ) := by
  rcases lt_or_ge (2 : ℝ) ((u : ℝ) / (2 * (ν : ℝ))) with h | h
  · have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
    have hνR : (0 : ℝ) < (ν : ℝ) := by exact_mod_cast (lt_of_lt_of_le hb hbν)
    have hbνR : (b : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hbν
    -- `u > 4ν` hence `4 ≤ u / b`
    have hu4ν : 4 * (ν : ℝ) < (u : ℝ) := by
      rw [lt_div_iff₀ (by positivity)] at h
      linarith
    have h4le : 4 * b ≤ u := by
      have hb4 : (4 * b : ℕ) ≤ 4 * ν := Nat.mul_le_mul_left 4 hbν
      have : (4 * ν : ℕ) < u := by
        have h4νR : (4 : ℝ) * (ν : ℝ) < (u : ℝ) := hu4ν
        exact_mod_cast (show 4 * ν < u by exact_mod_cast h4νR)
      omega
    have hquot : 4 ≤ u / b := (Nat.le_div_iff_mul_le hb).mpr (by linarith [h4le])
    have hhalf : (u : ℝ) / (2 * (b : ℝ)) ≤ ((u / b : ℕ) : ℝ) := by
      have hlt : (u : ℝ) / b < ((u / b : ℕ) : ℝ) + 1 := by
        have hmm := Nat.lt_mul_div_succ u hb
        have hcast : ((b * (u / b + 1) : ℕ) : ℝ) = (b : ℝ) * (((u / b : ℕ) : ℝ) + 1) := by
          push_cast; ring
        calc (u : ℝ) / b < ((b * (u / b + 1) : ℕ) : ℝ) / b := by
              rw [div_lt_div_iff_of_pos_right hbR]
              exact_mod_cast hmm
          _ = ((u / b : ℕ) : ℝ) + 1 := by rw [hcast]; field_simp
      have hkey : (u : ℝ) / (2 * (b : ℝ)) = ((u : ℝ) / b) / 2 := by ring
      rw [hkey]
      have h2R : (2 : ℝ) ≤ (u / b : ℕ) := by
        exact_mod_cast (le_trans (by norm_num : 2 ≤ 4) hquot)
      linarith
    refine le_trans ?_ (le_max_right _ _)
    calc (u : ℝ) / (2 * (ν : ℝ)) ≤ (u : ℝ) / (2 * (b : ℝ)) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          linarith
      _ ≤ ((u / b : ℕ) : ℝ) := hhalf
  · exact le_trans h (le_max_left _ _)

/-- **Companion (2.4) at an arbitrary scale**, with the `ν`-twist: for every `u`,
`|∑_{b ≤ u} μ b g(b/(ν,b))| ≤ C σ_ν τ(ν) (log max(2, u/(2ν)))^{-6}`. -/
lemma abs_Smu_le {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hg1 : g 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p ∧ g p < 1)
    (hbound : ∃ C : ℝ, ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    (h9 : ∃ c C : ℝ, ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, g p) - Real.log (Real.log y) - c|
        ≤ C * (Real.log y) ^ (-(10 : ℤ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν u : ℕ, Squarefree ν → 1 ≤ ν →
      |Smu g ν u| ≤ C * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
          * (ν.divisors.card : ℝ)
          * (Real.log (max 2 (((u : ℝ)) / (2 * (ν : ℝ))))) ^ (-(6 : ℤ)) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.NumberTheory.Sieve.moebius_density_sum_le hmul hg1 hp hbound h9
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hinv6 : (1 : ℝ) ≤ (Real.log 2) ^ (-(6 : ℤ)) := by
    have hp6 : (Real.log 2) ^ (6 : ℕ) ≤ 1 := by
      calc (Real.log 2) ^ 6 ≤ 1 ^ 6 := pow_le_pow_left₀ hlog2pos.le hlog2le 6
        _ = 1 := one_pow 6
    rw [zpow_neg]
    exact (one_le_inv₀ (by positivity : (0:ℝ) < (Real.log 2) ^ (6:ℤ))).mpr (by
      simpa using hp6)
  refine ⟨max C₀ 1 * (Real.log 2) ^ (-(6 : ℤ)), by positivity, ?_⟩
  intro ν u hν hν1
  set γ : ℝ := ∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) with hγ
  have hνpos : 0 < ν := by omega
  have hγ1 : 1 ≤ γ := by
    rw [hγ]
    refine Finset.one_le_prod₀ (fun p _ => ?_)
    have : (0 : ℝ) ≤ 1 / Real.sqrt (p : ℝ) := by positivity
    linarith
  have hγ0 : 0 ≤ γ := le_trans (by norm_num) hγ1
  have hC₀le : C₀ ≤ max C₀ 1 * (Real.log 2) ^ (-(6 : ℤ)) := by
    have h1 : C₀ ≤ max C₀ 1 := le_max_left _ _
    have h2 : (1 : ℝ) ≤ (Real.log 2) ^ (-(6 : ℤ)) := hinv6
    have h3 : (0 : ℝ) < max C₀ 1 := lt_of_lt_of_le hC₀pos h1
    nlinarith [h1, h2, h3, hC₀pos]
  set ξ : ℝ := Real.log (max 2 (((u : ℝ)) / (2 * (ν : ℝ)))) with hξ
  have hξpos : 0 < ξ := Real.log_pos (lt_of_lt_of_le (by norm_num : (1:ℝ) < 2)
    (le_max_left (2:ℝ) (((u : ℝ)) / (2 * (ν : ℝ)))))
  have _hξ1 : (1:ℝ) < max 2 (((u : ℝ)) / (2 * (ν : ℝ))) :=
    lt_of_lt_of_le (by norm_num : (1:ℝ) < 2) (le_max_left (2:ℝ) (((u : ℝ)) / (2 * (ν : ℝ))))
  -- uniform bound for `|G_ν(y)|`
  have hG : ∀ y : ℕ, |Gmu g ν y| ≤ max C₀ 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ
      * (Real.log (max 2 ((y : ℝ)))) ^ (-(6 : ℤ)) := by
    intro y
    rcases lt_or_ge y 2 with hy | hy
    · have hy1 : y ≤ 1 := by omega
      have hmaxeq : max 2 ((y : ℝ)) = 2 := max_eq_left (by exact_mod_cast (show y ≤ 2 by omega))
      have hbig : (1 : ℝ) ≤ max C₀ 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ
          * (Real.log 2) ^ (-(6 : ℤ)) := by
        have h1 : (1 : ℝ) ≤ max C₀ 1 := le_max_right _ _
        have h2 : (1 : ℝ) ≤ (Real.log 2) ^ (-(6 : ℤ)) := hinv6
        have h3 : (1 : ℝ) ≤ γ := hγ1
        have hmm : (1 : ℝ) ≤ max C₀ 1 * (Real.log 2) ^ (-(6 : ℤ)) := by
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ max C₀ 1 * (Real.log 2) ^ (-(6 : ℤ)) :=
                mul_le_mul h1 h2 (by norm_num) (by positivity)
        have hmm2 : (1 : ℝ) ≤ max C₀ 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ := by
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ max C₀ 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ :=
                mul_le_mul hmm h3 (by norm_num) (by positivity)
        calc (1 : ℝ) = 1 * 1 := by ring
          _ ≤ max C₀ 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ * (Real.log 2) ^ (-(6 : ℤ)) :=
              mul_le_mul hmm2 h2 (by norm_num) (by positivity)
      rw [hmaxeq]
      exact le_trans (Gmu_le_one hg1 ν hy1) hbig
    · have hmaxeq : max 2 ((y : ℝ)) = (y : ℝ) := max_eq_right (by exact_mod_cast hy)
      rw [hmaxeq]
      refine le_trans (hC₀ ν y hν1 hy) ?_
      have hY0 : 0 ≤ (Real.log (y : ℝ)) ^ (-(6 : ℤ)) :=
        le_of_lt (zpow_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < y))) _)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₀le hγ0) hY0
  rw [Smu_eq_reindex hν]
  have hterm : ∀ b₁ ∈ ν.divisors,
      |((ArithmeticFunction.moebius b₁ : ℤ) : ℝ) * Gmu g ν (u / b₁)|
        ≤ max C₀ 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ * ξ ^ (-(6 : ℤ)) := by
    intro b₁ hb₁
    have hb₁dvd : b₁ ∣ ν := (Nat.mem_divisors.mp hb₁).1
    have hb₁pos : 0 < b₁ := Nat.pos_of_mem_divisors hb₁
    have hb₁le : b₁ ≤ ν := Nat.le_of_dvd hνpos hb₁dvd
    rw [abs_mul]
    refine le_trans (mul_le_of_le_one_left (abs_nonneg _) (abs_moebius_cast_le_one b₁)) ?_
    refine le_trans (hG (u / b₁)) ?_
    have h1 : (u : ℝ) / (2 * (ν : ℝ)) ≤ max 2 (((u / b₁ : ℕ)) : ℝ) :=
      div_two_nu_le_max_div hb₁pos hb₁le
    have h2 : max 2 (((u : ℝ) / (2 * (ν : ℝ)))) ≤ max 2 (((u / b₁ : ℕ)) : ℝ) :=
      max_le (le_max_left _ _) h1
    have hlog : ξ ≤ Real.log (max 2 (((u / b₁ : ℕ)) : ℝ)) := by
      rw [hξ]
      exact Real.log_le_log (lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) (le_max_left _ _)) h2
    have hlogmaxpos : 0 < Real.log (max 2 (((u / b₁ : ℕ)) : ℝ)) :=
      Real.log_pos (lt_of_lt_of_le (by norm_num : (1:ℝ) < 2)
        (le_max_left (2:ℝ) (((u / b₁ : ℕ)) : ℝ)))
    have _hlogmax1 : (1:ℝ) < max 2 (((u / b₁ : ℕ)) : ℝ) :=
      lt_of_lt_of_le (by norm_num : (1:ℝ) < 2) (le_max_left (2:ℝ) (((u / b₁ : ℕ)) : ℝ))
    have hpow : (Real.log (max 2 (((u / b₁ : ℕ)) : ℝ))) ^ (-(6 : ℤ)) ≤ ξ ^ (-(6 : ℤ)) := by
      rw [zpow_neg, zpow_neg]
      refine (inv_le_inv₀ (zpow_pos hlogmaxpos 6) (zpow_pos hξpos 6)).mpr ?_
      exact pow_le_pow_left₀ hξpos.le hlog 6
    have hcoef : 0 ≤ max C₀ 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ := by
      have h1 : (0:ℝ) ≤ (Real.log 2) ^ (-(6 : ℤ)) := le_of_lt (zpow_pos hlog2pos _)
      have h2 : (0:ℝ) ≤ max C₀ 1 := le_trans hC₀pos.le (le_max_left _ _)
      exact mul_nonneg (mul_nonneg h2 h1) hγ0
    exact mul_le_mul_of_nonneg_left hpow hcoef
  calc |∑ b₁ ∈ ν.divisors, ((ArithmeticFunction.moebius b₁ : ℤ) : ℝ) * Gmu g ν (u / b₁)|
      ≤ ∑ b₁ ∈ ν.divisors,
        |((ArithmeticFunction.moebius b₁ : ℤ) : ℝ) * Gmu g ν (u / b₁)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b₁ ∈ ν.divisors,
          max C₀ 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ * ξ ^ (-(6 : ℤ)) :=
        Finset.sum_le_sum hterm
    _ = max C₀ 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ * (ν.divisors.card : ℝ)
          * ξ ^ (-(6 : ℤ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ = max C₀ 1 * (Real.log 2) ^ (-(6 : ℤ))
          * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) * (ν.divisors.card : ℝ)
          * (Real.log (max 2 (((u : ℝ)) / (2 * (ν : ℝ))))) ^ (-(6 : ℤ)) := by
        rw [hγ, hξ]

/-! ### The `p`-coprime variant (needed for the coupling `c ∤ b` of §5) -/

/-- The coprime sum with modulus `ν*p` written as a `p`-coprime constrained sum. -/
lemma Gmu_mul_prime_eq {g : ℕ → ℝ} {ν p y : ℕ} (hp : p.Prime) :
    Gmu g (ν * p) y
      = ∑ b ∈ ((Finset.Icc 1 y).filter (fun b => Nat.Coprime b ν)).filter
          (fun b => ¬ p ∣ b), (ArithmeticFunction.moebius b : ℝ) * g b := by
  rw [Gmu]
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hb, hcop⟩
    exact ⟨⟨hb, hcop.coprime_mul_right_right⟩,
      hp.coprime_iff_not_dvd.mp hcop.coprime_mul_left_right.symm⟩
  · rintro ⟨⟨hb, hcop⟩, hnd⟩
    exact ⟨hb, (Nat.coprime_mul_iff_right).mpr
      ⟨hcop, (hp.coprime_iff_not_dvd.mpr hnd).symm⟩⟩
/-- The `p`-coprime Möbius sum reindexed. -/
lemma Smup_eq_reindex {g : ℕ → ℝ} {ν p u : ℕ} (hp : p.Prime) (hν : Squarefree ν) :
    Smup g ν p u
      = ∑ b₁ ∈ ν.divisors.filter (fun b₁ => ¬ p ∣ b₁),
          (ArithmeticFunction.moebius b₁ : ℝ) * Gmu g (ν * p) (u / b₁) := by
  classical
  have hsq_eq : Smup g ν p u
      = ∑ b ∈ ((Finset.Icc 1 u).filter (fun b => ¬ p ∣ b)).filter (fun b => Squarefree b),
          (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) := by
    rw [Smup]
    exact (Finset.sum_subset (Finset.filter_subset _ _) (fun b hb hbn => by
      rw [Finset.mem_filter] at hbn
      push Not at hbn
      have hs : ¬ Squarefree b := hbn hb
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]; ring)).symm
  set Cset : Finset (Sigma (fun _ : ℕ => ℕ)) :=
    (ν.divisors.filter (fun b₁ => ¬ p ∣ b₁)).sigma (fun b₁ =>
      ((((Finset.Icc 1 (u / b₁)).filter (fun d => Nat.Coprime d ν)).filter
        (fun d => ¬ p ∣ d)).filter (fun d => Squarefree d))) with hC
  have hbij : (∑ b ∈ ((Finset.Icc 1 u).filter (fun b => ¬ p ∣ b)).filter (fun b => Squarefree b),
        (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b))
      = ∑ c ∈ Cset, (ArithmeticFunction.moebius c.1 : ℝ) * (ArithmeticFunction.moebius c.2 : ℝ)
          * g c.2 := by
    refine Finset.sum_bij'
      (fun b _ => (⟨Nat.gcd ν b, b / Nat.gcd ν b⟩ : Sigma (fun _ : ℕ => ℕ)))
      (fun c _ => c.1 * c.2) ?_ ?_ ?_ ?_ ?_
    · intro b hb
      rw [hC, Finset.mem_sigma]
      have hbfil : b ∈ (Finset.Icc 1 u).filter (fun b => ¬ p ∣ b) := (Finset.mem_filter.mp hb).1
      have hbsq : Squarefree b := (Finset.mem_filter.mp hb).2
      have hbIcc : b ∈ Finset.Icc 1 u := (Finset.mem_filter.mp hbfil).1
      have hbnd : ¬ p ∣ b := (Finset.mem_filter.mp hbfil).2
      rw [Finset.mem_Icc] at hbIcc
      obtain ⟨hb1, hby⟩ := hbIcc
      have hbpos : 0 < b := by omega
      have hgb : Nat.gcd ν b ∣ b := Nat.gcd_dvd_right ν b
      have hgpos : 0 < Nat.gcd ν b := Nat.pos_of_dvd_of_pos hgb hbpos
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_filter, Nat.mem_divisors]
        exact ⟨⟨Nat.gcd_dvd_left ν b, hν.ne_zero⟩,
          fun hdvd => hbnd (dvd_trans hdvd hgb)⟩
      · rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨⟨⟨(Nat.one_le_div_iff hgpos).mpr (Nat.gcd_le_right ν hbpos),
              Nat.div_le_div_right hby⟩, coprime_div_gcd_of_squarefree hbsq⟩,
              fun hdvd => hbnd (dvd_trans hdvd (Nat.div_dvd_of_dvd hgb))⟩,
              Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hgb) hbsq⟩
    · intro c hc
      rw [hC, Finset.mem_sigma] at hc
      have hc1fil : c.1 ∈ ν.divisors.filter (fun b₁ => ¬ p ∣ b₁) := hc.1
      have hc1mem : c.1 ∈ ν.divisors := (Finset.mem_filter.mp hc1fil).1
      have hc1nd : ¬ p ∣ c.1 := (Finset.mem_filter.mp hc1fil).2
      have hc2sq : Squarefree c.2 := (Finset.mem_filter.mp hc.2).2
      have hc2fil : c.2 ∈ ((Finset.Icc 1 (u / c.1)).filter (fun d => Nat.Coprime d ν)).filter
          (fun d => ¬ p ∣ d) := (Finset.mem_filter.mp hc.2).1
      have hc2nd : ¬ p ∣ c.2 := (Finset.mem_filter.mp hc2fil).2
      have hc2cop : Nat.Coprime c.2 ν :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hc2fil).1).2
      have hc2Icc : c.2 ∈ Finset.Icc 1 (u / c.1) :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hc2fil).1).1
      rw [Finset.mem_Icc] at hc2Icc
      obtain ⟨hc21, hc2y⟩ := hc2Icc
      have hc1dvd : c.1 ∣ ν := (Nat.mem_divisors.mp hc1mem).1
      have hc1pos : 0 < c.1 := Nat.pos_of_mem_divisors hc1mem
      have hc1sq : Squarefree c.1 := Squarefree.squarefree_of_dvd hc1dvd hν
      have hcop : Nat.Coprime c.1 c.2 := Nat.Coprime.coprime_dvd_left hc1dvd hc2cop.symm
      have hprod : c.1 * c.2 ≤ u := by
        have := (Nat.le_div_iff_mul_le hc1pos).mp hc2y
        calc c.1 * c.2 ≤ c.2 * c.1 := by rw [mul_comm]
          _ ≤ u := this
      have hpos0 : 0 < c.1 * c.2 := Nat.mul_pos hc1pos (by omega)
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨⟨Nat.one_le_iff_ne_zero.mpr hpos0.ne', hprod⟩,
        fun hd => (hp.dvd_mul.mp hd).elim hc1nd hc2nd⟩,
        (Nat.squarefree_mul hcop).mpr ⟨hc1sq, hc2sq⟩⟩
    · intro b hb
      exact Nat.mul_div_cancel' (Nat.gcd_dvd_right ν b)
    · intro c hc
      rw [hC, Finset.mem_sigma] at hc
      have hc1fil : c.1 ∈ ν.divisors.filter (fun b₁ => ¬ p ∣ b₁) := hc.1
      have hc1mem : c.1 ∈ ν.divisors := (Finset.mem_filter.mp hc1fil).1
      have hc2fil : c.2 ∈ ((Finset.Icc 1 (u / c.1)).filter (fun d => Nat.Coprime d ν)).filter
          (fun d => ¬ p ∣ d) := (Finset.mem_filter.mp hc.2).1
      have hc2cop : Nat.Coprime c.2 ν :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hc2fil).1).2
      obtain ⟨b₁, b₀⟩ := c
      have hc1dvd : b₁ ∣ ν := (Nat.mem_divisors.mp hc1mem).1
      have hc1pos : 0 < b₁ := Nat.pos_of_mem_divisors hc1mem
      rw [gcd_mul_of_dvd_coprime hc1dvd hc2cop, Nat.mul_div_right b₀ hc1pos]
    · intro b hb
      have hbsq : Squarefree b := (Finset.mem_filter.mp hb).2
      have hcop : Nat.Coprime (Nat.gcd ν b) (b / Nat.gcd ν b) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        exact gcd_gcd_div_gcd_eq_one ν b hbsq
      have hnat : Nat.gcd ν b * (b / Nat.gcd ν b) = b :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right ν b)
      nth_rewrite 1 [← hnat]
      rw [moebius_mul_coprime_real hcop]
  rw [hsq_eq, hbij, hC]
  rw [← Finset.sum_sigma' (ν.divisors.filter (fun b₁ => ¬ p ∣ b₁))
        (fun b₁ => ((((Finset.Icc 1 (u / b₁)).filter (fun d => Nat.Coprime d ν)).filter
          (fun d => ¬ p ∣ d)).filter (fun d => Squarefree d)))
        (fun a b => (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) * g b)]
  apply Finset.sum_congr rfl
  intro b₁ hb₁
  trans ∑ b₀ ∈ ((Finset.Icc 1 (u / b₁)).filter (fun d => Nat.Coprime d ν)).filter
      (fun d => ¬ p ∣ d),
      (ArithmeticFunction.moebius b₁ : ℝ) * (ArithmeticFunction.moebius b₀ : ℝ) * g b₀
  · exact Finset.sum_subset (Finset.filter_subset _ _) (fun b₀ hb₀ hb₀not => by
      rw [Finset.mem_filter] at hb₀not
      push Not at hb₀not
      have hs : ¬ Squarefree b₀ := hb₀not hb₀
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
      ring)
  · rw [Gmu_mul_prime_eq hp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b₀ _
    ring

/-- `σ_{νp} ≤ 2 σ_ν` for a prime `p`. -/
private lemma prod_primeFactors_mul_prime_le {ν p : ℕ} (hp : p.Prime) (hν0 : ν ≠ 0) :
    (∏ q ∈ (ν * p).primeFactors, (1 + 1 / Real.sqrt (q : ℝ)))
      ≤ 2 * ∏ q ∈ ν.primeFactors, (1 + 1 / Real.sqrt (q : ℝ)) := by
  have hνp0 : ν * p ≠ 0 := Nat.mul_ne_zero hν0 hp.ne_zero
  have hsub : (ν * p).primeFactors ⊆ ν.primeFactors ∪ {p} := by
    intro q hq
    obtain ⟨hqprime, hqdvd, _⟩ := Nat.mem_primeFactors.mp hq
    rw [Finset.mem_union, Finset.mem_singleton]
    rcases hqprime.dvd_mul.mp hqdvd with h | h
    · exact Or.inl (Nat.mem_primeFactors.mpr ⟨hqprime, h, hν0⟩)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hqprime hp).mp h)
  have hstep : ∏ q ∈ (ν * p).primeFactors, (1 + 1 / Real.sqrt (q : ℝ))
      ≤ ∏ q ∈ ν.primeFactors ∪ {p}, (1 + 1 / Real.sqrt (q : ℝ)) :=
    Finset.prod_le_prod_of_subset_of_one_le₀ hsub (fun q _ => by
      have : (0 : ℝ) ≤ 1 / Real.sqrt (q : ℝ) := by positivity
      linarith) (fun q _ _ => by
      have : (0 : ℝ) ≤ 1 / Real.sqrt (q : ℝ) := by positivity
      linarith)
  have hγ0 : (0 : ℝ) ≤ ∏ q ∈ ν.primeFactors, (1 + 1 / Real.sqrt (q : ℝ)) :=
    Finset.prod_nonneg (fun q _ => by
      have : (0 : ℝ) ≤ 1 / Real.sqrt (q : ℝ) := by positivity
      linarith)
  have hfp : (1 + 1 / Real.sqrt (p : ℝ)) ≤ 2 := by
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
    have hspos : 1 ≤ Real.sqrt (p : ℝ) := Real.one_le_sqrt.mpr hp1
    have : 1 / Real.sqrt (p : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]; exact hspos
    linarith
  by_cases hmem : p ∈ ν.primeFactors
  · have hunion : ν.primeFactors ∪ {p} = ν.primeFactors := by
      ext q
      rw [Finset.mem_union, Finset.mem_singleton]
      exact ⟨fun h => h.elim id (fun hq => hq ▸ hmem), Or.inl⟩
    rw [hunion] at hstep
    linarith
  · have hinsert : ν.primeFactors ∪ {p} = insert p ν.primeFactors := by
      ext q
      rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
      tauto
    rw [hinsert, Finset.prod_insert hmem] at hstep
    linarith [mul_le_mul_of_nonneg_right hfp hγ0]

/-- **The `p`-coprime version of (2.4)**: for a prime `p` and squarefree `ν`,
`|∑_{b ≤ u, p∤b} μ b g(b/(ν,b))| ≤ C σ_ν τ(ν) (log max(2, u/(2ν)))^{-6}`. -/
lemma abs_Smup_le {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hg1 : g 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p ∧ g p < 1)
    (hbound : ∃ C : ℝ, ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    (h9 : ∃ c C : ℝ, ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, g p) - Real.log (Real.log y) - c|
        ≤ C * (Real.log y) ^ (-(10 : ℤ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν p u : ℕ, p.Prime → Squarefree ν → 1 ≤ ν →
      |Smup g ν p u| ≤ C * (∏ q ∈ ν.primeFactors, (1 + 1 / Real.sqrt (q : ℝ)))
          * (ν.divisors.card : ℝ)
          * (Real.log (max 2 (((u : ℝ)) / (2 * (ν : ℝ))))) ^ (-(6 : ℤ)) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.NumberTheory.Sieve.moebius_density_sum_le hmul hg1 hp hbound h9
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hinv6 : (1 : ℝ) ≤ (Real.log 2) ^ (-(6 : ℤ)) := by
    have hp6 : (Real.log 2) ^ (6 : ℕ) ≤ 1 := by
      calc (Real.log 2) ^ 6 ≤ 1 ^ 6 := pow_le_pow_left₀ hlog2pos.le hlog2le 6
        _ = 1 := one_pow 6
    rw [zpow_neg]
    exact (one_le_inv₀ (by positivity : (0:ℝ) < (Real.log 2) ^ (6:ℤ))).mpr (by
      simpa using hp6)
  refine ⟨max (2 * C₀) 1 * (Real.log 2) ^ (-(6 : ℤ)), by positivity, ?_⟩
  intro ν p u hpp hν hν1
  set γ : ℝ := ∏ q ∈ ν.primeFactors, (1 + 1 / Real.sqrt (q : ℝ)) with hγ
  have hνpos : 0 < ν := by omega
  have hγ1 : 1 ≤ γ := by
    rw [hγ]
    refine Finset.one_le_prod₀ (fun q _ => ?_)
    have : (0 : ℝ) ≤ 1 / Real.sqrt (q : ℝ) := by positivity
    linarith
  have hγ0 : 0 ≤ γ := le_trans (by norm_num) hγ1
  have hσ : (∏ q ∈ (ν * p).primeFactors, (1 + 1 / Real.sqrt (q : ℝ))) ≤ 2 * γ := by
    rw [hγ]; exact prod_primeFactors_mul_prime_le hpp hν.ne_zero
  have hD : 2 * C₀ ≤ max (2 * C₀) 1 * (Real.log 2) ^ (-(6 : ℤ)) := by
    have h1 : 2 * C₀ ≤ max (2 * C₀) 1 := le_max_left _ _
    have h2 : (1 : ℝ) ≤ (Real.log 2) ^ (-(6 : ℤ)) := hinv6
    have h3 : (0 : ℝ) < max (2 * C₀) 1 := lt_of_lt_of_le (by positivity) h1
    nlinarith [h1, h2, h3]
  set ξ : ℝ := Real.log (max 2 (((u : ℝ)) / (2 * (ν : ℝ)))) with hξ
  have hξpos : 0 < ξ := Real.log_pos (lt_of_lt_of_le (by norm_num : (1:ℝ) < 2)
    (le_max_left (2:ℝ) (((u : ℝ)) / (2 * (ν : ℝ)))))
  have hG : ∀ y : ℕ, |Gmu g (ν * p) y| ≤ max (2 * C₀) 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ
      * (Real.log (max 2 ((y : ℝ)))) ^ (-(6 : ℤ)) := by
    intro y
    have hνp1 : 1 ≤ ν * p := by
      have h1 := hpp.one_le
      have h2 : 1 ≤ ν := hν1
      nlinarith
    rcases lt_or_ge y 2 with hy | hy
    · have hy1 : y ≤ 1 := by omega
      have hmaxeq : max 2 ((y : ℝ)) = 2 := max_eq_left (by exact_mod_cast (show y ≤ 2 by omega))
      have hbig : (1 : ℝ) ≤ max (2 * C₀) 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ
          * (Real.log 2) ^ (-(6 : ℤ)) := by
        have h1 : (1 : ℝ) ≤ max (2 * C₀) 1 := le_max_right _ _
        have h2 : (1 : ℝ) ≤ (Real.log 2) ^ (-(6 : ℤ)) := hinv6
        have h3 : (1 : ℝ) ≤ γ := hγ1
        have hmm : (1 : ℝ) ≤ max (2 * C₀) 1 * (Real.log 2) ^ (-(6 : ℤ)) := by
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ max (2 * C₀) 1 * (Real.log 2) ^ (-(6 : ℤ)) :=
                mul_le_mul h1 h2 (by norm_num) (by positivity)
        have hmm2 : (1 : ℝ) ≤ max (2 * C₀) 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ := by
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ max (2 * C₀) 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ :=
                mul_le_mul hmm h3 (by norm_num) (by positivity)
        calc (1 : ℝ) = 1 * 1 := by ring
          _ ≤ max (2 * C₀) 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ * (Real.log 2) ^ (-(6 : ℤ)) :=
              mul_le_mul hmm2 h2 (by norm_num) (by positivity)
      rw [hmaxeq]
      refine le_trans (Gmu_le_one hg1 (ν * p) hy1) hbig
    · have hmaxeq : max 2 ((y : ℝ)) = (y : ℝ) := max_eq_right (by exact_mod_cast hy)
      rw [hmaxeq]
      have hY0 : 0 ≤ (Real.log (y : ℝ)) ^ (-(6 : ℤ)) :=
        le_of_lt (zpow_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < y))) _)
      refine le_trans (hC₀ (ν * p) y hνp1 hy) ?_
      have hCσ : C₀ * (∏ q ∈ (ν * p).primeFactors, (1 + 1 / Real.sqrt (q : ℝ)))
          ≤ max (2 * C₀) 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ := by
        calc C₀ * (∏ q ∈ (ν * p).primeFactors, (1 + 1 / Real.sqrt (q : ℝ)))
            ≤ C₀ * (2 * γ) := mul_le_mul_of_nonneg_left hσ hC₀pos.le
          _ = 2 * C₀ * γ := by ring
          _ ≤ max (2 * C₀) 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ :=
              mul_le_mul_of_nonneg_right hD hγ0
      exact mul_le_mul_of_nonneg_right hCσ hY0
  rw [Smup_eq_reindex hpp hν]
  calc |∑ b₁ ∈ ν.divisors.filter (fun b₁ => ¬ p ∣ b₁),
        ((ArithmeticFunction.moebius b₁ : ℤ) : ℝ) * Gmu g (ν * p) (u / b₁)|
      ≤ ∑ b₁ ∈ ν.divisors.filter (fun b₁ => ¬ p ∣ b₁),
        |((ArithmeticFunction.moebius b₁ : ℤ) : ℝ) * Gmu g (ν * p) (u / b₁)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b₁ ∈ ν.divisors.filter (fun b₁ => ¬ p ∣ b₁),
          max (2 * C₀) 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ * ξ ^ (-(6 : ℤ)) := by
        apply Finset.sum_le_sum
        intro b₁ hb₁
        have hb₁mem : b₁ ∈ ν.divisors := (Finset.mem_filter.mp hb₁).1
        have hb₁dvd : b₁ ∣ ν := (Nat.mem_divisors.mp hb₁mem).1
        have hb₁pos : 0 < b₁ := Nat.pos_of_mem_divisors hb₁mem
        have hb₁le : b₁ ≤ ν := Nat.le_of_dvd hνpos hb₁dvd
        rw [abs_mul]
        refine le_trans (mul_le_of_le_one_left (abs_nonneg _) (abs_moebius_cast_le_one b₁)) ?_
        refine le_trans (hG (u / b₁)) ?_
        have h1 : (u : ℝ) / (2 * (ν : ℝ)) ≤ max 2 (((u / b₁ : ℕ)) : ℝ) :=
          div_two_nu_le_max_div hb₁pos hb₁le
        have h2 : max 2 (((u : ℝ) / (2 * (ν : ℝ)))) ≤ max 2 (((u / b₁ : ℕ)) : ℝ) :=
          max_le (le_max_left _ _) h1
        have hlog : ξ ≤ Real.log (max 2 (((u / b₁ : ℕ)) : ℝ)) := by
          rw [hξ]
          exact Real.log_le_log (lt_of_lt_of_le (by norm_num : (0:ℝ) < 2)
            (le_max_left _ _)) h2
        have hlogmaxpos : 0 < Real.log (max 2 (((u / b₁ : ℕ)) : ℝ)) :=
          Real.log_pos (lt_of_lt_of_le (by norm_num : (1:ℝ) < 2)
            (le_max_left (2:ℝ) (((u / b₁ : ℕ)) : ℝ)))
        have hpow : (Real.log (max 2 (((u / b₁ : ℕ)) : ℝ))) ^ (-(6 : ℤ)) ≤ ξ ^ (-(6 : ℤ)) := by
          rw [zpow_neg, zpow_neg]
          refine (inv_le_inv₀ (zpow_pos hlogmaxpos 6) (zpow_pos hξpos 6)).mpr ?_
          exact pow_le_pow_left₀ hξpos.le hlog 6
        have hcoef : 0 ≤ max (2 * C₀) 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ := by
          have h1 : (0:ℝ) ≤ (Real.log 2) ^ (-(6 : ℤ)) := le_of_lt (zpow_pos hlog2pos _)
          have h2 : (0:ℝ) ≤ max (2 * C₀) 1 := le_trans (by positivity) (le_max_left _ _)
          exact mul_nonneg (mul_nonneg h2 h1) hγ0
        exact mul_le_mul_of_nonneg_left hpow hcoef
    _ = max (2 * C₀) 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ
          * ((ν.divisors.filter (fun b₁ => ¬ p ∣ b₁)).card : ℝ) * ξ ^ (-(6 : ℤ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ max (2 * C₀) 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ
          * (ν.divisors.card : ℝ) * ξ ^ (-(6 : ℤ)) := by
        have hcard : ((ν.divisors.filter (fun b₁ => ¬ p ∣ b₁)).card : ℝ) ≤ (ν.divisors.card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
        have hcoef : 0 ≤ max (2 * C₀) 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ * ξ ^ (-(6 : ℤ)) := by
          have h1 : (0:ℝ) ≤ (Real.log 2) ^ (-(6 : ℤ)) := le_of_lt (zpow_pos hlog2pos _)
          have h2 : (0:ℝ) ≤ max (2 * C₀) 1 := le_trans (by positivity) (le_max_left _ _)
          exact mul_nonneg (mul_nonneg (mul_nonneg h2 h1) hγ0) (le_of_lt (zpow_pos hξpos _))
        calc max (2 * C₀) 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ
              * ((ν.divisors.filter (fun b₁ => ¬ p ∣ b₁)).card : ℝ) * ξ ^ (-(6 : ℤ))
            = max (2 * C₀) 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ * ξ ^ (-(6 : ℤ))
              * ((ν.divisors.filter (fun b₁ => ¬ p ∣ b₁)).card : ℝ) := by ring
          _ ≤ max (2 * C₀) 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ * ξ ^ (-(6 : ℤ))
              * (ν.divisors.card : ℝ) := mul_le_mul_of_nonneg_left hcard hcoef
          _ = max (2 * C₀) 1 * (Real.log 2) ^ (-(6 : ℤ)) * γ
              * (ν.divisors.card : ℝ) * ξ ^ (-(6 : ℤ)) := by ring
    _ = max (2 * C₀) 1 * (Real.log 2) ^ (-(6 : ℤ))
          * (∏ q ∈ ν.primeFactors, (1 + 1 / Real.sqrt (q : ℝ))) * (ν.divisors.card : ℝ)
          * (Real.log (max 2 (((u : ℝ)) / (2 * (ν : ℝ))))) ^ (-(6 : ℤ)) := by
        rw [hγ, hξ]


/-! ### The `Λ`-sum restricted to primes -/

/-- If `f` vanishes away from squarefree numbers, the `Λ`-sum of `f` localises on primes. -/
lemma sum_vonMangoldt_mul_eq_primes {N : ℕ} {f : ℕ → ℝ}
    (hf : ∀ n : ℕ, ¬ Squarefree n → f n = 0) :
    (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * f n)
      = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) * f p := by
  classical
  have hΛ0 : ∀ n : ℕ, ¬ IsPrimePow n → ArithmeticFunction.vonMangoldt n = 0 :=
    fun n hn => ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn
  have hstep1 : (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * f n)
      = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ Squarefree n),
          ArithmeticFunction.vonMangoldt n * f n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : IsPrimePow n ∧ Squarefree n
    · rw [if_pos h]
    · rw [if_neg h]
      by_cases hnp : IsPrimePow n
      · have hns : ¬ Squarefree n := fun hs => h ⟨hnp, hs⟩
        rw [hf n hns]; ring
      · rw [hΛ0 n hnp]; ring
  have hstep2 : (∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ Squarefree n),
        ArithmeticFunction.vonMangoldt n * f n)
      = ∑ n ∈ (Finset.Icc 1 N).filter Nat.Prime, ArithmeticFunction.vonMangoldt n * f n := by
    congr 1
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hmem, hpp, hsq⟩
      obtain ⟨p, k, hprime, hk0, rfl⟩ := hpp
      have hk1 : k = 1 := by
        rcases lt_or_eq_of_le (Nat.one_le_iff_ne_zero.mpr hk0.ne') with h | h
        · exfalso
          have hdvd : p * p ∣ p ^ k := by
            obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
            rw [pow_add, pow_two]
            exact dvd_mul_left (p * p) (p ^ j)
          have hunit : IsUnit p := hsq p hdvd
          rw [Nat.isUnit_iff] at hunit
          exact hprime.ne_one hunit
        · exact h.symm
      subst hk1
      simp only [pow_one] at hmem ⊢
      exact ⟨hmem, hprime.nat_prime⟩
    · rintro ⟨hmem, hprime⟩
      exact ⟨hmem, hprime.isPrimePow, hprime.squarefree⟩
  rw [hstep1, hstep2]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp.2]


/-! ### The main-term sum of §5 and its `ν`-decomposition -/

/-- The main-term sum of §5: `∑_{b ≤ M}∑_{c ≤ P} μ b Λ c [b c squarefree] lamCoeff(bc)`. -/
def MainS (g lam : ℕ → ℝ) (Δ M P : ℕ) : ℝ :=
  ∑ b ∈ Finset.Icc 1 M, ∑ c ∈ Finset.Icc 1 P,
    (ArithmeticFunction.moebius b : ℝ) * ArithmeticFunction.vonMangoldt c *
      (if Squarefree (b * c) then lamCoeff g lam Δ (b * c) else 0)

/-- The inner `ν`-sum of §5 after the sieve decomposition. -/
def Tnu (g : ℕ → ℝ) (M P ν : ℕ) : ℝ :=
  ∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) *
    ∑ p ∈ (Finset.Icc 1 P).filter Nat.Prime,
      Real.log (p : ℝ) * g (p / Nat.gcd ν p) * (if p ∣ b then 0 else 1)

/-- The `c`-sum over primes: for squarefree `b`, the `Λ`-sum localises on the primes
`p ≤ P` with `p ∤ b`. -/
private lemma Tnu_inner_eq {g : ℕ → ℝ} {b ν : ℕ} (hb : Squarefree b) (P : ℕ) :
    (∑ c ∈ Finset.Icc 1 P, ArithmeticFunction.vonMangoldt c *
        (if Squarefree (b * c) then g (c / Nat.gcd ν c) else 0))
      = ∑ p ∈ (Finset.Icc 1 P).filter Nat.Prime,
          Real.log (p : ℝ) * g (p / Nat.gcd ν p) * (if p ∣ b then 0 else 1) := by
  rw [sum_vonMangoldt_mul_eq_primes (f := fun c =>
    (if Squarefree (b * c) then g (c / Nat.gcd ν c) else 0)) (fun n hn => by
      have hns : ¬ Squarefree (b * n) := fun h => hn (h.squarefree_of_dvd (dvd_mul_left n b))
      rw [if_neg hns])]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  by_cases hpb : p ∣ b
  · rw [if_pos hpb, if_neg (fun h => ((squarefree_mul_prime_iff hb hp.2).mp h) hpb)]
    ring
  · rw [if_neg hpb, if_pos ((squarefree_mul_prime_iff hb hp.2).mpr hpb)]
    ring

/-- **§5, main terms**: `MainS = ∑_ν λ_ν g(ν) T_ν`. -/
lemma mainS_eq {g lam : ℕ → ℝ} {Δ M P : ℕ}
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hlam_sq : ∀ ν : ℕ, ¬ Squarefree ν → lam ν = 0) :
    MainS g lam Δ M P
      = ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree, lam ν * g ν * Tnu g M P ν := by
  classical
  set F : ℕ → ℕ → ℕ → ℝ := fun b c ν =>
    (ArithmeticFunction.moebius b : ℝ) * ArithmeticFunction.vonMangoldt c *
      (if Squarefree (b * c) then lam ν * g ν *
        (g (b / Nat.gcd ν b) * g (c / Nat.gcd ν c)) else 0) with hF
  -- Step 1: factorise `lamCoeff` and push the `ν`-sum inside
  have h1 : MainS g lam Δ M P
      = ∑ b ∈ Finset.Icc 1 M, ∑ c ∈ Finset.Icc 1 P, ∑ ν ∈ Finset.Icc 1 Δ, F b c ν := by
    rw [MainS]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    by_cases h : Squarefree (b * c)
    · rw [if_pos h, lamCoeff, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ν _
      have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
      have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hc).1
      obtain ⟨hbsq, hcsq, hbc⟩ := squarefree_mul_facts hb1 hc1 h
      rw [hF]
      simp only
      rw [if_pos h, div_gcd_mul_div_gcd hbc (by omega) (by omega),
        hgmul _ _ (coprime_div_gcd_div_gcd hbc)]
    · have hzero : ∀ ν ∈ Finset.Icc 1 Δ, F b c ν = 0 := by
        intro ν _
        change (ArithmeticFunction.moebius b : ℝ) * ArithmeticFunction.vonMangoldt c *
          (if Squarefree (b * c) then lam ν * g ν *
            (g (b / Nat.gcd ν b) * g (c / Nat.gcd ν c)) else 0) = 0
        rw [if_neg h]
        ring
      rw [Finset.sum_eq_zero hzero, if_neg h, mul_zero]
  -- Step 2: bring the `ν`-sum to the outside
  have h2 : (∑ b ∈ Finset.Icc 1 M, ∑ c ∈ Finset.Icc 1 P, ∑ ν ∈ Finset.Icc 1 Δ, F b c ν)
      = ∑ ν ∈ Finset.Icc 1 Δ, ∑ b ∈ Finset.Icc 1 M, ∑ c ∈ Finset.Icc 1 P, F b c ν := by
    rw [show (∑ b ∈ Finset.Icc 1 M, ∑ c ∈ Finset.Icc 1 P, ∑ ν ∈ Finset.Icc 1 Δ, F b c ν)
        = ∑ b ∈ Finset.Icc 1 M, ∑ ν ∈ Finset.Icc 1 Δ, ∑ c ∈ Finset.Icc 1 P, F b c ν from
      Finset.sum_congr rfl (fun b _ => Finset.sum_comm)]
    exact Finset.sum_comm
  -- Step 3: factor the `c`-sum and localise it on primes
  have h3 : (∑ ν ∈ Finset.Icc 1 Δ, ∑ b ∈ Finset.Icc 1 M, ∑ c ∈ Finset.Icc 1 P, F b c ν)
      = ∑ ν ∈ Finset.Icc 1 Δ, lam ν * g ν * Tnu g M P ν := by
    apply Finset.sum_congr rfl
    intro ν _
    rw [Tnu, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hbsq : Squarefree b
    · have hinner : (∑ c ∈ Finset.Icc 1 P, F b c ν)
          = (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) * (lam ν * g ν) *
              ∑ c ∈ Finset.Icc 1 P, ArithmeticFunction.vonMangoldt c *
                (if Squarefree (b * c) then g (c / Nat.gcd ν c) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        rw [hF]
        by_cases h : Squarefree (b * c) <;> simp only [h, if_true, if_false] <;> ring
      rw [hinner, Tnu_inner_eq hbsq P]
      ring
    · have hmu : (ArithmeticFunction.moebius b : ℝ) = 0 := by
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hbsq]; norm_num
      rw [Finset.sum_eq_zero (fun c _ => by rw [hF]; simp only; rw [hmu]; ring), hmu]
      ring
  -- Step 4: restrict to squarefree `ν`
  have h4 : (∑ ν ∈ Finset.Icc 1 Δ, lam ν * g ν * Tnu g M P ν)
      = ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree, lam ν * g ν * Tnu g M P ν :=
    (Finset.sum_subset (Finset.filter_subset _ _) (fun ν hνmem hνnot => by
      rw [Finset.mem_filter] at hνnot
      push Not at hνnot
      rw [hlam_sq ν (hνnot hνmem)]; ring)).symm
  rw [h1, h2, h3, h4]

/-! ### Reindexing the divisors of a prime and the Möbius factor -/

/-- `∑_{b ≤ M, p ∣ b} f b = ∑_{b' ≤ ⌊M/p⌋} f (p b')`. -/
private lemma sum_filter_dvd_eq {p M : ℕ} (hp : 0 < p) (f : ℕ → ℝ) :
    (∑ b ∈ (Finset.Icc 1 M).filter (fun b => p ∣ b), f b)
      = ∑ b' ∈ Finset.Icc 1 (M / p), f (p * b') := by
  refine Finset.sum_bij' (fun b _ => b / p) (fun b' _ => p * b') ?_ ?_ ?_ ?_ ?_
  · intro b hb
    obtain ⟨hbIcc, hpb⟩ := Finset.mem_filter.mp hb
    obtain ⟨hb1, hbM⟩ := Finset.mem_Icc.mp hbIcc
    have hple : p ≤ b := Nat.le_of_dvd (by omega) hpb
    rw [Finset.mem_Icc]
    exact ⟨(Nat.one_le_div_iff hp).mpr hple, Nat.div_le_div_right hbM⟩
  · intro b' hb'
    obtain ⟨hb'1, hb'M⟩ := Finset.mem_Icc.mp hb'
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (by positivity), by
      calc p * b' ≤ p * (M / p) := Nat.mul_le_mul_left p hb'M
        _ ≤ M := Nat.mul_div_le M p⟩, dvd_mul_right p b'⟩
  · intro b hb
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp hb).2
  · intro b' _
    exact Nat.mul_div_right b' hp
  · intro b hb
    rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hb).2]

/-- `μ(p b) = -μ(b)` for a prime `p ∤ b`, and `= 0` otherwise. -/
private lemma moebius_prime_mul {p b : ℕ} (hp : p.Prime) :
    ((ArithmeticFunction.moebius (p * b) : ℤ) : ℝ)
      = if p ∣ b then 0 else -((ArithmeticFunction.moebius b : ℤ) : ℝ) := by
  by_cases hpb : p ∣ b
  · rw [if_pos hpb]
    have hns : ¬ Squarefree (p * b) := by
      intro h
      obtain ⟨c, rfl⟩ := hpb
      have hdvd : p * p ∣ p * (p * c) := ⟨c, by ring⟩
      exact hp.ne_one (Nat.isUnit_iff.mp (h p hdvd))
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns]
    norm_num
  · rw [if_neg hpb]
    have hcop : Nat.Coprime p b := hp.coprime_iff_not_dvd.mpr hpb
    have hz : ArithmeticFunction.moebius (p * b)
        = ArithmeticFunction.moebius p * ArithmeticFunction.moebius b :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        (Nat.coprime_iff_gcd_eq_one.mp hcop)
    rw [hz, ArithmeticFunction.moebius_apply_prime hp]
    push_cast
    ring

/-- The substitution `b ↦ p b'` in the Möbius summand. -/
private lemma mu_g_div_gcd_mul_prime {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    {ν p b : ℕ} (hp : p.Prime) (hb : 0 < b) :
    ((ArithmeticFunction.moebius (p * b) : ℤ) : ℝ) * g (p * b / Nat.gcd ν (p * b))
      = if p ∣ b then 0
        else -((ArithmeticFunction.moebius b : ℤ) : ℝ)
          * (g (p / Nat.gcd ν p) * g (b / Nat.gcd ν b)) := by
  rw [moebius_prime_mul hp]
  by_cases hpb : p ∣ b
  · rw [if_pos hpb, if_pos hpb]
    ring
  · rw [if_neg hpb, if_neg hpb]
    have hcop : Nat.Coprime p b := hp.coprime_iff_not_dvd.mpr hpb
    rw [div_gcd_mul_div_gcd hcop hp.pos hb, hmul _ _ (coprime_div_gcd_div_gcd hcop)]


/-! ### The decomposition of `T_ν` -/

/-- **§5**: `T_ν = X_ν·S_ν(M) + ∑_p (log p) g(p/(ν,p))² S^{(p)}_ν(⌊M/p⌋)`. -/
lemma Tnu_eq {g : ℕ → ℝ} {ν M P : ℕ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) :
    Tnu g M P ν
      = (∑ p ∈ (Finset.Icc 1 P).filter Nat.Prime, Real.log (p : ℝ) * g (p / Nat.gcd ν p))
          * Smu g ν M
        + ∑ p ∈ (Finset.Icc 1 P).filter Nat.Prime,
            Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2 * Smup g ν p (M / p) := by
  classical
  set Ps := (Finset.Icc 1 P).filter Nat.Prime with hPs
  set F : ℕ → ℝ := fun p => Real.log (p : ℝ) * g (p / Nat.gcd ν p) with hF
  -- (a) split the inner prime sum
  have hinner : ∀ b ∈ Finset.Icc 1 M,
      (∑ p ∈ Ps, F p * (if p ∣ b then 0 else 1))
        = (∑ p ∈ Ps, F p) - ∑ p ∈ Ps.filter (fun p => p ∣ b), F p := by
    intro b _
    have h1 : (∑ p ∈ Ps, F p * (if p ∣ b then 0 else 1))
        = ∑ p ∈ Ps.filter (fun p => ¬ p ∣ b), F p := by
      conv_rhs => rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases h : p ∣ b <;> simp [h]
    have h2 : (∑ p ∈ Ps.filter (fun p => p ∣ b), F p)
        + ∑ p ∈ Ps.filter (fun p => ¬ p ∣ b), F p = ∑ p ∈ Ps, F p :=
      Finset.sum_filter_add_sum_filter_not Ps (fun p => p ∣ b) F
    linarith
  -- (b) `Tnu` as a difference of two sums
  have hstep : Tnu g M P ν
      = (∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b))
          * (∑ p ∈ Ps, F p)
        - ∑ b ∈ Finset.Icc 1 M, ∑ p ∈ Ps.filter (fun p => p ∣ b),
            (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) * F p := by
    have hpt : ∀ b ∈ Finset.Icc 1 M,
        (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) *
            (∑ p ∈ (Finset.Icc 1 P).filter Nat.Prime,
              Real.log (p : ℝ) * g (p / Nat.gcd ν p) * (if p ∣ b then 0 else 1))
          = (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b)
              * ((∑ p ∈ Ps, F p) - ∑ p ∈ Ps.filter (fun p => p ∣ b), F p) := by
      intro b hb
      rw [hinner b hb]
    have heq : (∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ)
          * g (b / Nat.gcd ν b) *
            (∑ p ∈ (Finset.Icc 1 P).filter Nat.Prime,
              Real.log (p : ℝ) * g (p / Nat.gcd ν p) * (if p ∣ b then 0 else 1)))
        = ∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) *
            ((∑ p ∈ Ps, F p) - ∑ p ∈ Ps.filter (fun p => p ∣ b), F p) :=
      Finset.sum_congr rfl hpt
    have heq2 : (∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) *
            ((∑ p ∈ Ps, F p) - ∑ p ∈ Ps.filter (fun p => p ∣ b), F p))
        = ∑ b ∈ Finset.Icc 1 M,
            ((ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) * (∑ p ∈ Ps, F p)
              - (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b)
                * ∑ p ∈ Ps.filter (fun p => p ∣ b), F p) :=
      Finset.sum_congr rfl (fun b _ => by rw [mul_sub])
    rw [Tnu, heq, heq2, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_mul]
    · exact Finset.sum_congr rfl (fun b _ => by rw [Finset.mul_sum])
  -- (c) swap the double sum and evaluate the fibre
  have hswap : (∑ b ∈ Finset.Icc 1 M, ∑ p ∈ Ps.filter (fun p => p ∣ b),
        (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) * F p)
      = ∑ p ∈ Ps, F p * ∑ b ∈ (Finset.Icc 1 M).filter (fun b => p ∣ b),
          (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) := by
    have h1 : (∑ b ∈ Finset.Icc 1 M, ∑ p ∈ Ps.filter (fun p => p ∣ b),
          (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) * F p)
        = ∑ b ∈ Finset.Icc 1 M, ∑ p ∈ Ps,
            (if p ∣ b then (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) * F p
              else 0) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_filter]
    have h2 : (∑ p ∈ Ps, ∑ b ∈ Finset.Icc 1 M,
          (if p ∣ b then (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) * F p
            else 0))
        = ∑ p ∈ Ps, F p * ∑ b ∈ (Finset.Icc 1 M).filter (fun b => p ∣ b),
            (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
      conv_rhs => rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : p ∣ b <;> simp [h] <;> ring
    rw [h1, Finset.sum_comm, h2]
  -- (d) the `b`-fibre
  have hfibre : ∀ p ∈ Ps,
      ((∑ b ∈ (Finset.Icc 1 M).filter (fun b => p ∣ b),
          (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b)))
        = -g (p / Nat.gcd ν p) * Smup g ν p (M / p) := by
    intro p hp
    rw [hPs] at hp
    rw [Finset.mem_filter] at hp
    have hpp : p.Prime := hp.2
    rw [sum_filter_dvd_eq hpp.pos]
    have hpt : ∀ b' ∈ Finset.Icc 1 (M / p),
        (ArithmeticFunction.moebius (p * b') : ℝ) * g (p * b' / Nat.gcd ν (p * b'))
          = (if p ∣ b' then 0 else
              -((ArithmeticFunction.moebius b' : ℤ) : ℝ)
                * (g (p / Nat.gcd ν p) * g (b' / Nat.gcd ν b'))) := by
      intro b' hb'
      exact mu_g_div_gcd_mul_prime hmul hpp (by
        have := (Finset.mem_Icc.mp hb').1
        omega)
    rw [Finset.sum_congr rfl hpt, Smup, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b' _
    by_cases h : p ∣ b' <;> simp [h] <;> ring
  rw [hstep, hswap]
  have hlast : ∀ p ∈ Ps, F p * (∑ b ∈ (Finset.Icc 1 M).filter (fun b => p ∣ b),
        (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b))
      = F p * (-g (p / Nat.gcd ν p) * Smup g ν p (M / p)) := by
    intro p hp
    rw [hfibre p hp]
  rw [Finset.sum_congr rfl hlast, hPs, hF]
  have key1 : (∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b))
      = Smu g ν M := rfl
  have key2 : (∑ p ∈ (Finset.Icc 1 P).filter Nat.Prime,
        Real.log (p : ℝ) * g (p / Nat.gcd ν p))
      = ∑ p ∈ (Finset.Icc 1 P).filter Nat.Prime, Real.log (p : ℝ) * g (p / Nat.gcd ν p) := rfl
  have key3 : (∑ p ∈ (Finset.Icc 1 P).filter Nat.Prime,
        Real.log (p : ℝ) * g (p / Nat.gcd ν p) * (-g (p / Nat.gcd ν p) * Smup g ν p (M / p)))
      = -∑ p ∈ (Finset.Icc 1 P).filter Nat.Prime,
          Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2 * Smup g ν p (M / p) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [key1, key3, sub_neg_eq_add]
  ring



/-! ### The weighted prime sum of §5 -/

/-- Auxiliary: `(log 2)^{-6} ≤ 10`. -/
private lemma log_two_zpow_le : (Real.log 2) ^ (-(6 : ℤ)) ≤ 10 := by
  have h1 : (0.69 : ℝ) ≤ Real.log 2 := le_of_lt (by linarith [Real.log_two_gt_d9])
  have h3 : (0.1 : ℝ) ≤ (0.69 : ℝ) ^ (6 : ℕ) := by norm_num
  have h4 : (0.69 : ℝ) ^ (6 : ℕ) ≤ (Real.log 2) ^ (6 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) h1 6
  have h5 : (1 : ℝ) ≤ 10 * (Real.log 2) ^ (6 : ℕ) := by nlinarith
  rw [zpow_neg]
  exact (inv_le_iff_one_le_mul₀ (by positivity : (0:ℝ) < (Real.log 2) ^ (6:ℤ))).mpr
    (by simpa using h5)

/-- Auxiliary: `8 log 2 ≤ log M` for `M ≥ 256`. -/
private lemma eight_log_two_le {M : ℕ} (hM : 256 ≤ M) :
    8 * Real.log 2 ≤ Real.log (M : ℝ) := by
  have h1 : (256 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have h2 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 from by norm_num, Real.log_pow]
    norm_num
  have h3 := Real.log_le_log (by norm_num : (0:ℝ) < 256) h1
  rw [h2] at h3
  exact h3


end

end Submission.ASP
