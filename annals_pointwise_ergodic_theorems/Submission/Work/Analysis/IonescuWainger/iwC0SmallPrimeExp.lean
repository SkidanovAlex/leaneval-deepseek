import Mathlib
import Submission.Work.Analysis.IonescuWainger.Basic
import Submission.Work.Analysis.IonescuWainger.prime_rpow_le

/-!
# Small primes in the Ionescu–Wainger congruence argument

Appendix A of Krause–Mirek–Tao, *Pointwise ergodic theorems for non-conventional bilinear
polynomial averages*, Annals of Math. 195 (2022), needs the following arithmetic fact: in the
regime `l ≥ C⁰_ρ`, a prime power `p ^ j` with `p ≤ N_0^{(l)}` whose size is at most `2 ^ l`
(the largest admissible denominator) cannot have an exponent `j` exceeding what the factorial
`N_0^{(l)}!` can absorb.

The mechanism is the identity `(2/ρ)(1 + ε_ρ) = D_ρ` with `ε_ρ = ρ D_ρ/2 - 1`:
from `prime_rpow_le` one has `N_0^{(l)} ≤ p^{(1+ε_ρ) ⌊N_0^{(l)}/p⌋}`, while `p^j ≤ 2^l` and
`2^{ρl/2} < N_0^{(l)}` give
`j log p ≤ l log 2 < (2/ρ) log N_0^{(l)} ≤ D_ρ ⌊N_0^{(l)}/p⌋ log p`,
i.e. `j ≤ D_ρ ⌊N_0^{(l)}/p⌋`.  Legendre's formula (`Nat.factorization_factorial`) supplies
`⌊N_0^{(l)}/p⌋ ≤ v_p(N_0^{(l)}!)`.

## Main result

* `Work.Analysis.IonescuWainger.iwC0SmallPrimeExp`
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Analysis.IonescuWainger

/-- `2/ρ < D_ρ`, the lower bound coming from the floor in the definition of `D_ρ`. -/
private theorem iwD_gt (ρ : ℝ) : 2 / ρ < (iwD ρ : ℝ) := by
  rw [iwD, Nat.cast_add, Nat.cast_one]
  exact Nat.lt_floor_add_one _

/-- `D_ρ ≤ 2/ρ + 1`, the matching upper bound. -/
private theorem iwD_le {ρ : ℝ} (hρ : 0 < ρ) : (iwD ρ : ℝ) ≤ 2 / ρ + 1 := by
  rw [iwD, Nat.cast_add, Nat.cast_one]
  have := Nat.floor_le (show (0 : ℝ) ≤ 2 / ρ by positivity)
  linarith

/-- `ε_ρ = ρ D_ρ / 2 - 1` is positive: it is `ρD_ρ/2 - 1 > 0` since `D_ρ > 2/ρ`. -/
private theorem iwEps_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < iwEps ρ := by
  rw [iwEps]
  have h2 := mul_lt_mul_of_pos_left (iwD_gt ρ) hρ
  rw [mul_comm ρ (2 / ρ), div_mul_cancel₀ 2 (ne_of_gt hρ)] at h2
  linarith

/-- `ε_ρ ≤ 1/2` when `ρ ≤ 1`. -/
private theorem iwEps_le_half {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) : iwEps ρ ≤ 1 / 2 := by
  rw [iwEps]
  have hmul := mul_le_mul_of_nonneg_left (iwD_le hρ) hρ.le
  have heq : ρ * (2 / ρ + 1) = 2 + ρ := by field_simp
  rw [heq] at hmul
  linarith

/-- The identity `(2/ρ)(1 + ε_ρ) = D_ρ` relating the Ionescu–Wainger parameters. -/
private theorem iwD_eq_ratio {ρ : ℝ} (hρ : 0 < ρ) : (2 / ρ) * (1 + iwEps ρ) = (iwD ρ : ℝ) := by
  rw [iwEps]; field_simp; ring

/-- The lower bound on the threshold `C⁰_ρ` that drives the estimate:
`(2/ρ)(1 + ε_ρ)/ε_ρ ≤ C⁰_ρ`. -/
private theorem iwC0_lower (ρ : ℝ) : (2 / ρ) * ((1 + iwEps ρ) / iwEps ρ) ≤ (iwC0 ρ : ℝ) := by
  rw [iwC0]
  have h := Nat.le_ceil ((2 / ρ) * ((1 + iwEps ρ) / iwEps ρ))
  push_cast
  linarith

/-- `2^{ρl/2} < N_0^{(l)}`, since `N_0^{(l)} = ⌊2^{ρl/2}⌋ + 1`. -/
private theorem iwN0_gt (ρ : ℝ) (l : ℕ) : (2 : ℝ) ^ (ρ * (l : ℝ) / 2) < (iwN0 ρ l : ℝ) := by
  rw [iwN0, Nat.cast_add, Nat.cast_one]
  have := Nat.lt_floor_add_one ((2 : ℝ) ^ (ρ * (l : ℝ) / 2))
  linarith

/-- **Small primes have bounded exponent.**  For `ρ ∈ (0,1]`, in the regime `l ≥ C⁰_ρ`, any prime
power `p ^ j` with `j ≥ 1`, `p ≤ N_0^{(l)}` prime and `p ^ j ≤ 2 ^ l` satisfies
`j ≤ D_ρ · v_p(N_0^{(l)}!)`. -/
theorem iwC0SmallPrimeExp {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l q p j : ℕ}
    (hl : iwC0 ρ ≤ l) (hq : q ≤ 2 ^ l) (hp : p.Prime) (hpN : p ≤ iwN0 ρ l)
    (hpj : p ^ j ≤ q) : j ≤ iwD ρ * (iwN0 ρ l).factorial.factorization p := by
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hεpos : 0 < iwEps ρ := iwEps_pos hρ
  have hεhalf : iwEps ρ ≤ 1 / 2 := iwEps_le_half hρ hρ1
  have hNgt : (2 : ℝ) ^ (ρ * (l : ℝ) / 2) < (iwN0 ρ l : ℝ) := iwN0_gt ρ l
  -- `l ≥ C⁰_ρ` gives `(2/ρ)(1+ε_ρ)/ε_ρ ≤ l`, hence `(1+ε_ρ)/ε_ρ ≤ ρl/2`
  have hl' : (2 / ρ) * ((1 + iwEps ρ) / iwEps ρ) ≤ (l : ℝ) := by
    have h1 : (2 / ρ) * ((1 + iwEps ρ) / iwEps ρ) ≤ (iwC0 ρ : ℝ) := iwC0_lower ρ
    have h2 : ((iwC0 ρ : ℕ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    linarith
  have hratio : (1 + iwEps ρ) / iwEps ρ ≤ ρ * (l : ℝ) / 2 := by
    have h2 : (0 : ℝ) < ρ / 2 := by linarith
    have h3 := mul_le_mul_of_nonneg_left hl' h2.le
    have heq : (ρ / 2) * ((2 / ρ) * ((1 + iwEps ρ) / iwEps ρ)) = (1 + iwEps ρ) / iwEps ρ := by
      field_simp
    calc (1 + iwEps ρ) / iwEps ρ = (ρ / 2) * ((2 / ρ) * ((1 + iwEps ρ) / iwEps ρ)) := heq.symm
      _ ≤ (ρ / 2) * (l : ℝ) := h3
      _ = ρ * (l : ℝ) / 2 := by ring
  -- consequently `ρl/2 ≥ 3` and `N_0^{(l)} ≥ 8`
  have h3le : (3 : ℝ) ≤ ρ * (l : ℝ) / 2 := by
    have h1 : (3 : ℝ) ≤ (1 + iwEps ρ) / iwEps ρ := by
      rw [le_div_iff₀ hεpos]; nlinarith [hεhalf]
    linarith
  have hN8 : 8 ≤ iwN0 ρ l := by
    have h8 : (8 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ) / 2) := by
      have h23 : (2 : ℝ) ^ (3 : ℝ) = 8 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
      calc (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := h23.symm
        _ ≤ (2 : ℝ) ^ (ρ * (l : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3le
    have : (8 : ℝ) < (iwN0 ρ l : ℝ) := lt_of_le_of_lt h8 hNgt
    exact le_of_lt (Nat.cast_lt.mp this)
  -- the hypothesis `2^{(1+ε)/ε} ≤ N_0^{(l)}` of `prime_rpow_le`
  have hN' : (2 : ℝ) ^ ((1 + iwEps ρ) / iwEps ρ) ≤ (iwN0 ρ l : ℝ) :=
    le_of_lt (lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le (by norm_num) hratio) hNgt)
  have hNp : (iwN0 ρ l : ℝ) ≤ (p : ℝ) ^ ((1 + iwEps ρ) * ((iwN0 ρ l / p : ℕ) : ℝ)) :=
    prime_rpow_le hεpos hεhalf hN8 hN' hp hpN
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hNpos : (0 : ℝ) < (iwN0 ρ l : ℝ) := by
    exact_mod_cast (show 0 < iwN0 ρ l by rw [iwN0]; exact Nat.succ_pos _)
  -- logarithmic form of `p ^ j ≤ q ≤ 2 ^ l`
  have hstep1 : (j : ℝ) * Real.log (p : ℝ) ≤ (l : ℝ) * Real.log 2 := by
    have h1 : ((p ^ j : ℕ) : ℝ) ≤ ((2 ^ l : ℕ) : ℝ) := by exact_mod_cast le_trans hpj hq
    rw [Nat.cast_pow, Nat.cast_pow] at h1
    have h2 := Real.log_le_log (by positivity) h1
    rwa [Real.log_pow, Real.log_pow] at h2
  have hstep2 : ρ * (l : ℝ) / 2 * Real.log 2 < Real.log (iwN0 ρ l : ℝ) := by
    have h2 := Real.log_lt_log (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) hNgt
    rwa [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at h2
  have hstep3 : Real.log (iwN0 ρ l : ℝ) ≤
      (1 + iwEps ρ) * ((iwN0 ρ l / p : ℕ) : ℝ) * Real.log (p : ℝ) := by
    have h3 := Real.log_le_log hNpos hNp
    rwa [Real.log_rpow hppos] at h3
  -- the chain `j log p < D_ρ ⌊N_0/p⌋ log p`
  have hchain : (j : ℝ) * Real.log (p : ℝ) <
      ((iwD ρ : ℝ) * ((iwN0 ρ l / p : ℕ) : ℝ)) * Real.log (p : ℝ) := by
    have hρ2 : 0 < 2 / ρ := by positivity
    have heqD : (2 / ρ) * (1 + iwEps ρ) = (iwD ρ : ℝ) := iwD_eq_ratio hρ
    have heq2 : (l : ℝ) * Real.log 2 = (2 / ρ) * (ρ * (l : ℝ) / 2 * Real.log 2) := by
      field_simp
    calc (j : ℝ) * Real.log (p : ℝ) ≤ (l : ℝ) * Real.log 2 := hstep1
      _ = (2 / ρ) * (ρ * (l : ℝ) / 2 * Real.log 2) := heq2
      _ < (2 / ρ) * Real.log (iwN0 ρ l : ℝ) := mul_lt_mul_of_pos_left hstep2 hρ2
      _ ≤ (2 / ρ) * ((1 + iwEps ρ) * ((iwN0 ρ l / p : ℕ) : ℝ) * Real.log (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hstep3 hρ2.le
      _ = ((iwD ρ : ℝ) * ((iwN0 ρ l / p : ℕ) : ℝ)) * Real.log (p : ℝ) := by
          rw [show (2 / ρ) * ((1 + iwEps ρ) * ((iwN0 ρ l / p : ℕ) : ℝ) * Real.log (p : ℝ))
              = ((2 / ρ) * (1 + iwEps ρ)) * (((iwN0 ρ l / p : ℕ) : ℝ) * Real.log (p : ℝ))
              by ring,
            heqD]
          ring
  have hlt : (j : ℝ) < (iwD ρ : ℝ) * ((iwN0 ρ l / p : ℕ) : ℝ) :=
    lt_of_mul_lt_mul_right hchain hlogp.le
  have hjlt : j < iwD ρ * (iwN0 ρ l / p) := by
    rw [← Nat.cast_mul] at hlt
    exact_mod_cast hlt
  -- Legendre: `⌊N_0/p⌋ ≤ v_p(N_0!)`
  have hwv : iwN0 ρ l / p ≤ (iwN0 ρ l).factorial.factorization p := by
    have hlogN : Nat.log p (iwN0 ρ l) < iwN0 ρ l + 1 := Nat.lt_succ_of_le (Nat.log_le_self _ _)
    rw [Nat.factorization_factorial (b := iwN0 ρ l + 1) hp hlogN]
    have hmem : 1 ∈ Finset.Ico 1 (iwN0 ρ l + 1) :=
      Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
    have hle := Finset.single_le_sum (f := fun i => iwN0 ρ l / p ^ i) (fun i _ => Nat.zero_le _)
      hmem
    simpa using hle
  exact le_trans hjlt.le (Nat.mul_le_mul_left _ hwv)

end Work.Analysis.IonescuWainger
