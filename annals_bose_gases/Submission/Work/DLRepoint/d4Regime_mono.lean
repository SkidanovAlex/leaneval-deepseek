import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.DLRepoint.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.DLRepoint

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# `Work.DLRepoint.d4Regime_mono` — the regime transport in the particle count

The count-dependent fields of `Work.DLRepoint.D4Regime` are all of the shape
*nonneg coefficient times a nondecreasing function of the count*.  This file
proves the four monotonicity facts (one per count-dependent field) and
assembles them into `d4Regime_mono`.
-/

/-- **D1's `n₊`-coefficient is monotone in the count** (`d1C·(a v)·(N̂+1)/s³`). -/
lemma kinPBogErr_mono {Ct s : ℝ} {v : ℝ³ → ℝ} {n n' : ℕ}
    (ha : 0 ≤ a v) (hs : 0 < s) (hn : n ≤ n') :
    Work.SmallBoxA0.kinPBogErr Ct n s v ≤ Work.SmallBoxA0.kinPBogErr Ct n' s v := by
  unfold Work.SmallBoxA0.kinPBogErr
  have hC : 0 ≤ Work.SmallBoxA0.d1C Ct := Work.BlockBound4.d4C_nonneg Ct
  have hnn : ((n : ℝ) + 1) ≤ ((n' : ℝ) + 1) := by exact_mod_cast Nat.succ_le_succ hn
  have hs3 : (0 : ℝ) < s ^ 3 := by positivity
  have hle : ((n : ℝ) + 1) / s ^ 3 ≤ ((n' : ℝ) + 1) / s ^ 3 :=
    div_le_div_of_nonneg_right hnn (le_of_lt hs3)
  exact mul_le_mul_of_nonneg_left hle (mul_nonneg hC ha)

/-- **D1's loss-factor term is monotone in the count**: the coefficient
`½|η|·8π(a v)·s⁻³` is nonnegative and the count-factor `(N̂+2)²` is
nondecreasing. -/
lemma eta_term_mono {Ct R0 s c₀ : ℝ} {v : ℝ³ → ℝ} {n n' : ℕ}
    (ha : 0 ≤ a v) (hs : 0 < s) (hn : n ≤ n') :
    (1 / 2) * |Work.SmallBoxA0.kinPeta Ct R0 s c₀ v| * (8 * Real.pi * (a v))
        * (((((n + 1 : ℕ) : ℝ)) + 1) ^ 2) * (s ^ 3)⁻¹
      ≤ (1 / 2) * |Work.SmallBoxA0.kinPeta Ct R0 s c₀ v| * (8 * Real.pi * (a v))
        * (((((n' + 1 : ℕ) : ℝ)) + 1) ^ 2) * (s ^ 3)⁻¹ := by
  have hs3 : (0 : ℝ) < s ^ 3 := by positivity
  have hF : 0 ≤ (1 / 2) * |Work.SmallBoxA0.kinPeta Ct R0 s c₀ v| * (8 * Real.pi * (a v))
      * (s ^ 3)⁻¹ :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _))
        (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt Real.pi_pos)) ha))
      (le_of_lt (inv_pos.mpr hs3))
  have hA : (((((n + 1 : ℕ) : ℝ)) + 1) ^ 2) ≤ (((((n' + 1 : ℕ) : ℝ)) + 1) ^ 2) := by
    have h1 : ((((n + 1 : ℕ) : ℝ)) + 1) ≤ ((((n' + 1 : ℕ) : ℝ)) + 1) := by
      have : n + 1 + 1 ≤ n' + 1 + 1 := by omega
      push_cast
      exact_mod_cast this
    have h0 : (0 : ℝ) ≤ ((((n + 1 : ℕ) : ℝ)) + 1) := by positivity
    nlinarith [h1, h0]
  have key : (1 / 2) * |Work.SmallBoxA0.kinPeta Ct R0 s c₀ v| * (8 * Real.pi * (a v))
        * (s ^ 3)⁻¹ * (((((n + 1 : ℕ) : ℝ)) + 1) ^ 2)
      ≤ (1 / 2) * |Work.SmallBoxA0.kinPeta Ct R0 s c₀ v| * (8 * Real.pi * (a v))
        * (s ^ 3)⁻¹ * (((((n' + 1 : ℕ) : ℝ)) + 1) ^ 2) :=
    mul_le_mul_of_nonneg_left hA hF
  calc (1 / 2) * |Work.SmallBoxA0.kinPeta Ct R0 s c₀ v| * (8 * Real.pi * (a v))
          * (((((n + 1 : ℕ) : ℝ)) + 1) ^ 2) * (s ^ 3)⁻¹
      = (1 / 2) * |Work.SmallBoxA0.kinPeta Ct R0 s c₀ v| * (8 * Real.pi * (a v))
          * (s ^ 3)⁻¹ * (((((n + 1 : ℕ) : ℝ)) + 1) ^ 2) := by ring
    _ ≤ (1 / 2) * |Work.SmallBoxA0.kinPeta Ct R0 s c₀ v| * (8 * Real.pi * (a v))
          * (s ^ 3)⁻¹ * (((((n' + 1 : ℕ) : ℝ)) + 1) ^ 2) := key
    _ = (1 / 2) * |Work.SmallBoxA0.kinPeta Ct R0 s c₀ v| * (8 * Real.pi * (a v))
          * (((((n' + 1 : ℕ) : ℝ)) + 1) ^ 2) * (s ^ 3)⁻¹ := by ring

/-- **The core of D1's error bracket is monotone**, term by term: with every
coefficient nonnegative the three summands are `coeff·(k²/s³)`,
`coeff·(k/s³)⁴·s³` and `coeff·(k/s³)·s³`, each nondecreasing in `k ≥ 0`. -/
lemma bracket_core {a c₀ L s : ℝ} (ha : 0 ≤ a) (hc0 : 0 < c₀) (hL : 0 ≤ L) (hs : 0 < s)
    {k k' : ℝ} (hk0 : 0 ≤ k) (hk : k ≤ k') :
    a ^ 2 * c₀ * L * ((k * k) / s ^ 3) + a ^ 4 * (c₀ ^ 3)⁻¹ * ((k / s ^ 3) ^ 3) * (k / s ^ 3) * s ^ 3
      + a * c₀ ^ 3 * (k / s ^ 3) * s ^ 3
    ≤ a ^ 2 * c₀ * L * ((k' * k') / s ^ 3) + a ^ 4 * (c₀ ^ 3)⁻¹ * ((k' / s ^ 3) ^ 3) * (k' / s ^ 3) * s ^ 3
      + a * c₀ ^ 3 * (k' / s ^ 3) * s ^ 3 := by
  have hs3 : 0 < s ^ 3 := by positivity
  have hs3i : 0 ≤ (s ^ 3)⁻¹ := le_of_lt (inv_pos.mpr hs3)
  have hk0' : 0 ≤ k' := le_trans hk0 hk
  have hkk : k * k ≤ k' * k' := mul_self_le_mul_self hk0 hk
  have hu : k / s ^ 3 ≤ k' / s ^ 3 := div_le_div_of_nonneg_right hk (le_of_lt hs3)
  have hu0 : 0 ≤ k / s ^ 3 := div_nonneg hk0 (le_of_lt hs3)
  have hu0' : 0 ≤ k' / s ^ 3 := div_nonneg hk0' (le_of_lt hs3)
  have hT1 : a ^ 2 * c₀ * L * ((k * k) / s ^ 3) ≤ a ^ 2 * c₀ * L * ((k' * k') / s ^ 3) := by
    have hcoef : 0 ≤ a ^ 2 * c₀ * L * (s ^ 3)⁻¹ :=
      mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ha 2) (le_of_lt hc0)) hL) hs3i
    have h1 : a ^ 2 * c₀ * L * (s ^ 3)⁻¹ * (k * k) ≤ a ^ 2 * c₀ * L * (s ^ 3)⁻¹ * (k' * k') :=
      mul_le_mul_of_nonneg_left hkk hcoef
    calc a ^ 2 * c₀ * L * ((k * k) / s ^ 3)
        = a ^ 2 * c₀ * L * (s ^ 3)⁻¹ * (k * k) := by ring
      _ ≤ a ^ 2 * c₀ * L * (s ^ 3)⁻¹ * (k' * k') := h1
      _ = a ^ 2 * c₀ * L * ((k' * k') / s ^ 3) := by ring
  have hT2 : a ^ 4 * (c₀ ^ 3)⁻¹ * ((k / s ^ 3) ^ 3) * (k / s ^ 3) * s ^ 3
      ≤ a ^ 4 * (c₀ ^ 3)⁻¹ * ((k' / s ^ 3) ^ 3) * (k' / s ^ 3) * s ^ 3 := by
    have hpow : (k / s ^ 3) ^ 3 ≤ (k' / s ^ 3) ^ 3 := pow_le_pow_left₀ hu0 hu 3
    have hcoef : 0 ≤ a ^ 4 * (c₀ ^ 3)⁻¹ * s ^ 3 :=
      mul_nonneg (mul_nonneg (pow_nonneg ha 4)
        (inv_nonneg.mpr (pow_nonneg (le_of_lt hc0) 3))) (le_of_lt hs3)
    have h1 : a ^ 4 * (c₀ ^ 3)⁻¹ * s ^ 3 * ((k / s ^ 3) ^ 3) * (k / s ^ 3)
        ≤ a ^ 4 * (c₀ ^ 3)⁻¹ * s ^ 3 * ((k' / s ^ 3) ^ 3) * (k' / s ^ 3) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hpow hcoef
      · exact hu
      · exact hu0
      · positivity
    nlinarith [h1]
  have hT3 : a * c₀ ^ 3 * (k / s ^ 3) * s ^ 3 ≤ a * c₀ ^ 3 * (k' / s ^ 3) * s ^ 3 := by
    have hcoef : 0 ≤ a * c₀ ^ 3 * s ^ 3 :=
      mul_nonneg (mul_nonneg ha (pow_nonneg (le_of_lt hc0) 3)) (le_of_lt hs3)
    have h1 : a * c₀ ^ 3 * s ^ 3 * (k / s ^ 3) ≤ a * c₀ ^ 3 * s ^ 3 * (k' / s ^ 3) :=
      mul_le_mul_of_nonneg_left hu hcoef
    nlinarith [h1]
  exact add_le_add (add_le_add hT1 hT2) hT3

/-- **D1's error bracket is monotone in the count.**  The log coefficient is
nonnegative under D1's dilute regime (`c₀·(a v) ≤ 1`, so `(c₀·(a v))⁻¹ ≥ 1`),
which is what `bracket_core` needs. -/
lemma kinPBracket_mono {Ct s c₀ : ℝ} {v : ℝ³ → ℝ} {n n' : ℕ}
    (ha : 0 ≤ a v) (hc0 : 0 < c₀) (hs : 0 < s) (hdil : 2 * c₀ * (a v) ≤ 1) (hn : n ≤ n') :
    Work.SmallBoxA0.kinPBracket Ct n s c₀ v ≤ Work.SmallBoxA0.kinPBracket Ct n' s c₀ v := by
  have hc0a : 0 ≤ c₀ * (a v) := mul_nonneg (le_of_lt hc0) ha
  have hcle1 : c₀ * (a v) ≤ 1 := by linarith
  have hlog : 0 ≤ Real.log ((c₀ * (a v))⁻¹) := by
    rcases eq_or_lt_of_le hc0a with h0 | hpos
    · rw [← h0]; simp
    · exact Real.log_nonneg ((one_le_inv₀ hpos).mpr hcle1)
  have hC : 0 ≤ Work.SmallBoxA0.d1C Ct := Work.BlockBound4.d4C_nonneg Ct
  have hk : ((n : ℝ) + 1) ≤ ((n' : ℝ) + 1) := by
    have : n + 1 ≤ n' + 1 := Nat.succ_le_succ hn
    exact_mod_cast this
  have hk0 : 0 ≤ ((n : ℝ) + 1) := by positivity
  unfold Work.SmallBoxA0.kinPBracket
  apply mul_le_mul_of_nonneg_left _ hC
  exact bracket_core ha hc0 hlog hs hk0 hk

/-- **The AM–GM `Corr` budget's count factor is monotone**: the coefficient
`4·(32π·χ²·a v)²` is nonnegative and the count factor `(N̂+1)²·(N̂+1)` is
nondecreasing. -/
lemma corr_term_mono {v : ℝ³ → ℝ} {n n' : ℕ}
    (ha : 0 ≤ a v) (hn : n ≤ n') :
    4 * ((32 * Real.pi * chiSup ^ 2 * ((((n + 1 : ℕ) : ℝ)) + 1)) * (a v)) ^ 2
        * (((n + 1 : ℕ) : ℝ))
      ≤ 4 * ((32 * Real.pi * chiSup ^ 2 * ((((n' + 1 : ℕ) : ℝ)) + 1)) * (a v)) ^ 2
        * (((n' + 1 : ℕ) : ℝ)) := by
  have hchi : (0 : ℝ) ≤ chiSup := le_of_lt chiSup_pos
  have hpi : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
  have hk : ((n : ℝ) + 1) ≤ ((n' : ℝ) + 1) := by
    have : n + 1 ≤ n' + 1 := Nat.succ_le_succ hn
    exact_mod_cast this
  have hK : ((n : ℝ) + 1) + 1 ≤ ((n' : ℝ) + 1) + 1 := by linarith
  have hk0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hc0 : (0 : ℝ) ≤ 32 * Real.pi * chiSup ^ 2 * (a v) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hpi) (pow_nonneg hchi 2)) ha
  have hcK : 32 * Real.pi * chiSup ^ 2 * (((n : ℝ) + 1) + 1) * (a v)
      ≤ 32 * Real.pi * chiSup ^ 2 * (((n' : ℝ) + 1) + 1) * (a v) := by
    have := mul_le_mul_of_nonneg_right hK hc0
    nlinarith [this]
  have hsq : (32 * Real.pi * chiSup ^ 2 * (((n : ℝ) + 1) + 1) * (a v)) ^ 2
      ≤ (32 * Real.pi * chiSup ^ 2 * (((n' : ℝ) + 1) + 1) * (a v)) ^ 2 := by
    apply sq_le_sq'
    · nlinarith [hc0, hK, hk0]
    · exact hcK
  have h1 : 4 * (32 * Real.pi * chiSup ^ 2 * (((n : ℝ) + 1) + 1) * (a v)) ^ 2 * ((n : ℝ) + 1)
      ≤ 4 * (32 * Real.pi * chiSup ^ 2 * (((n' : ℝ) + 1) + 1) * (a v)) ^ 2 * ((n' : ℝ) + 1) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hsq (by norm_num)
    · exact hk
    · exact hk0
    · positivity
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] using h1

/-- **The regime transport in the particle count**: the count-dependent regime
fields of the faithful block bundle (`Work.DLRepoint.D4Regime`: the `n₊`-coefficient
cap, D1's loss-factor domination, D1's bracket budget, the AM–GM `Corr` budget, and
the `ε_T`-gap domination) are MONOTONE in the count `n`: the fields at a larger
count imply them at a smaller one.  This is what makes FS `eq:appdellsassumption`
readable as a single parameter regime (carry it at one maximal window count, get it
at every window count below). -/
theorem d4Regime_mono {s μ R0 K_B Ct c₀ cgap : ℝ}
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} {n n' : ℕ}
    (hs : 0 < s) (hav : 0 ≤ BoseGases.a v) (hc0 : 0 < c₀)
    (hdil : 2 * c₀ * BoseGases.a v ≤ 1)
    (hn : n ≤ n') (h : Work.DLRepoint.D4Regime s μ R0 K_B Ct c₀ cgap v n') :
    Work.DLRepoint.D4Regime s μ R0 K_B Ct c₀ cgap v n := by
  refine ⟨?_, ?_, ?_, ?_, h.hcgap, h.hchi⟩
  · have hb := kinPBogErr_mono (Ct := Ct) (s := s) (v := v) hav hs hn
    linarith [h.hbox, hb]
  · have he := eta_term_mono (Ct := Ct) (R0 := R0) (s := s) (c₀ := c₀) (v := v) hav hs hn
    linarith [h.hη, he]
  · have hbr := kinPBracket_mono (Ct := Ct) (s := s) (c₀ := c₀) (v := v) hav hc0 hs hdil hn
    linarith [h.hbracket, hbr]
  · have hcr := corr_term_mono (v := v) hav hn
    linarith [h.hcorrreg, hcr]

end Work.DLRepoint
