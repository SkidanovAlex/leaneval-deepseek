/-
# A uniform-in-`t` bound for the twisted bilinear multiplier `BtwistSet`

This module proves `Work.KMTAreas.A7.exists_bound_BtwistSet_uniform`, the version of
`Work.KMTAreas.A7.exists_bound_Btwist_uniform` for an **arbitrary pair of finite frequency sets**
`A₁`, `A₂` (rather than the Ionescu--Wainger sets `iwArithFreqs ρ l₁`, `iwArithFreqs ρ l₂`).

The arithmetic kernel of `BtwistSet` is the double sum

  `arithKernelSet P q A₁ A₂ j₁ j₂ = ∑_{α₁∈A₁}∑_{α₂∈A₂} m_Ẑ(α₁,α₂) e(-j₁α₁) e(-j₂α₂)`,

a finite sum of terms of modulus at most one.  The hypothesis `hK` of the statement provides a
uniform bound `K` on `‖arithKernelSet P q A₁ A₂ j₁ j₂‖` (in the applications this is either the
cardinality bound `#A₁ · #A₂` of `norm_arithKernelSet_le`, or a sharper arithmetic input), and the
rest of the argument is the elementary double-series estimate of `exists_bound_Btwist_uniform`:
the two Fourier-coefficient families `cw m₁`, `cw m₂` decay quadratically, the two `t`-dependent
inputs `h t`, `k t` are uniformly bounded on `t ∈ [1/2,1]`, so

  `‖BtwistSet ρ P l₁ l₂ A₁ A₂ m₁ m₂ (h t) (k t) x‖
      ≤ K · Ch · Ck · Cd₁ · Cd₂ · (∑_j 1/(1+j²))²`

for every `t ∈ [1/2,1]`, by absolute convergence of the iterated series
(`Work.KMTAreas.tsum_inv_sq_shift_le` gives the summability and the uniform bound of the weights).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.FiberGeneral
import Submission.Work.KMTAreas.tsum_inv_sq_shift_le

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-! ## The kernel of `BtwistSet` -/

/-- The kernel of the twisted bilinear multiplier at an arbitrary pair of frequency sets, as a
function of the two summation variables:
`arithKernelSet P q A₁ A₂ j₁ j₂ · cw m₁ j₁ · cw m₂ j₂`. -/
private def btwSetK (P : ℤ[X]) (q : ℕ) (A₁ A₂ : Finset Work.Analysis.IonescuWainger.Circle)
    (m₁ m₂ : ℝ → ℂ) (j₁ j₂ : ℤ) : ℂ :=
  arithKernelSet P q A₁ A₂ j₁ j₂ * cw m₁ j₁ * cw m₂ j₂

/-- `BtwistSet` is the iterated series of the kernel `btwSetK` against the two inputs. -/
private theorem btwSet_eq (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ)
    (A₁ A₂ : Finset Work.Analysis.IonescuWainger.Circle) (m₁ m₂ : ℝ → ℂ) (a b : ℤ → ℂ)
    (x : ℤ) :
    BtwistSet ρ P l₁ l₂ A₁ A₂ m₁ m₂ a b x
      = ∑' j₁ : ℤ, ∑' j₂ : ℤ,
          btwSetK P (arithQ ρ (max l₁ l₂)) A₁ A₂ m₁ m₂ j₁ j₂ * a (x - j₁) * b (x - j₂) := rfl

/-- The kernel is dominated by the a priori bound `K` on the arithmetic kernel. -/
private lemma btwSetK_norm_le {P : ℤ[X]} {q : ℕ} {A₁ A₂ : Finset Work.Analysis.IonescuWainger.Circle} {m₁ m₂ : ℝ → ℂ}
    {K : ℝ} (hK : ∀ j₁ j₂ : ℤ, ‖arithKernelSet P q A₁ A₂ j₁ j₂‖ ≤ K) (j₁ j₂ : ℤ) :
    ‖btwSetK P q A₁ A₂ m₁ m₂ j₁ j₂‖ ≤ K * ‖cw m₁ j₁‖ * ‖cw m₂ j₂‖ := by
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0 0)
  unfold btwSetK
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul (hK j₁ j₂) le_rfl (norm_nonneg _) hK0) le_rfl (norm_nonneg _)
    (mul_nonneg hK0 (norm_nonneg _))

/-! ## Elementary summation tools -/

/-- `‖z₁ z₂ z₃‖ ≤ Z₁ Z₂ Z₃` for `‖zᵢ‖ ≤ Zᵢ`. -/
private lemma norm_mul_mul_le_ {z₁ z₂ z₃ : ℂ} {Z₁ Z₂ Z₃ : ℝ} (h₁ : ‖z₁‖ ≤ Z₁)
    (h₂ : ‖z₂‖ ≤ Z₂) (h₃ : ‖z₃‖ ≤ Z₃) : ‖z₁ * z₂ * z₃‖ ≤ Z₁ * Z₂ * Z₃ := by
  have h₁' : 0 ≤ Z₁ := le_trans (norm_nonneg z₁) h₁
  have h₂' : 0 ≤ Z₂ := le_trans (norm_nonneg z₂) h₂
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _) h₁') h₃ (norm_nonneg _)
    (mul_nonneg h₁' h₂')

/-- **Absolute summability of an iterated series.**  If `‖F j₁ j₂‖ ≤ G j₁ · H j₂` with `G`, `H`
summable, then `j₁ ↦ ∑' j₂, F j₁ j₂` is summable. -/
private lemma summable_tsum_of_bound {F : ℤ → ℤ → ℂ} {G H : ℤ → ℝ}
    (hG : Summable G) (hH : Summable H) (hF : ∀ j₁ j₂, ‖F j₁ j₂‖ ≤ G j₁ * H j₂) :
    Summable (fun j₁ : ℤ => ∑' j₂ : ℤ, F j₁ j₂) := by
  have hnorm : ∀ j₁ : ℤ, Summable (fun j₂ : ℤ => ‖F j₁ j₂‖) := fun j₁ =>
    Summable.of_nonneg_of_le (fun j₂ => norm_nonneg _) (fun j₂ => hF j₁ j₂)
      (hH.mul_left (G j₁))
  refine Summable.of_norm_bounded (g := fun j₁ : ℤ => G j₁ * (∑' j₂ : ℤ, H j₂))
    (hG.mul_right _) (fun j₁ => ?_)
  calc ‖∑' j₂ : ℤ, F j₁ j₂‖ ≤ ∑' j₂ : ℤ, ‖F j₁ j₂‖ := norm_tsum_le_tsum_norm (hnorm j₁)
    _ ≤ ∑' j₂ : ℤ, G j₁ * H j₂ :=
        Summable.tsum_le_tsum (fun j₂ => hF j₁ j₂) (hnorm j₁) (hH.mul_left (G j₁))
    _ = G j₁ * ∑' j₂ : ℤ, H j₂ := tsum_mul_left

/-! ## Summability of the series defining `BtwistSet` -/

/-- Summability of the inner series of `BtwistSet` in the second summation variable. -/
private lemma btwSet_inner_summable {P : ℤ[X]} {q : ℕ} {A₁ A₂ : Finset Work.Analysis.IonescuWainger.Circle} {m₁ m₂ : ℝ → ℂ}
    {K : ℝ} (hK : ∀ j₁ j₂ : ℤ, ‖arithKernelSet P q A₁ A₂ j₁ j₂‖ ≤ K)
    (hm₂ : Summable (fun j : ℤ => ‖cw m₂ j‖))
    (a b : ℤ → ℂ) {Ca Cb : ℝ} (ha : ∀ y : ℤ, ‖a y‖ ≤ Ca) (hb : ∀ y : ℤ, ‖b y‖ ≤ Cb)
    (x j₁ : ℤ) :
    Summable (fun j₂ : ℤ => btwSetK P q A₁ A₂ m₁ m₂ j₁ j₂ * a (x - j₁) * b (x - j₂)) := by
  refine Summable.of_norm_bounded
    (g := fun j₂ : ℤ => (K * ‖cw m₁ j₁‖ * Ca * Cb) * ‖cw m₂ j₂‖)
    (hm₂.mul_left _) (fun j₂ => ?_)
  calc ‖btwSetK P q A₁ A₂ m₁ m₂ j₁ j₂ * a (x - j₁) * b (x - j₂)‖
      ≤ (K * ‖cw m₁ j₁‖ * ‖cw m₂ j₂‖) * Ca * Cb :=
        norm_mul_mul_le_ (btwSetK_norm_le hK j₁ j₂) (ha _) (hb _)
    _ = (K * ‖cw m₁ j₁‖ * Ca * Cb) * ‖cw m₂ j₂‖ := by ring

/-- **Absolute summability of the iterated series defining `BtwistSet`.** -/
private lemma btwSet_summable_of_bounded {P : ℤ[X]} {q : ℕ} {A₁ A₂ : Finset Work.Analysis.IonescuWainger.Circle}
    {m₁ m₂ : ℝ → ℂ} {K : ℝ}
    (hK : ∀ j₁ j₂ : ℤ, ‖arithKernelSet P q A₁ A₂ j₁ j₂‖ ≤ K)
    (hm₁ : Summable (fun j : ℤ => ‖cw m₁ j‖)) (hm₂ : Summable (fun j : ℤ => ‖cw m₂ j‖))
    (a b : ℤ → ℂ) {Ca Cb : ℝ} (ha : ∀ y : ℤ, ‖a y‖ ≤ Ca) (hb : ∀ y : ℤ, ‖b y‖ ≤ Cb)
    (x : ℤ) :
    Summable (fun j₁ : ℤ => ∑' j₂ : ℤ,
      btwSetK P q A₁ A₂ m₁ m₂ j₁ j₂ * a (x - j₁) * b (x - j₂)) := by
  refine summable_tsum_of_bound
    (G := fun j₁ : ℤ => K * ‖cw m₁ j₁‖ * Ca * Cb) (H := fun j₂ : ℤ => ‖cw m₂ j₂‖) ?_ hm₂ ?_
  · exact ((hm₁.mul_left K).mul_right Ca).mul_right Cb
  · intro j₁ j₂
    calc ‖btwSetK P q A₁ A₂ m₁ m₂ j₁ j₂ * a (x - j₁) * b (x - j₂)‖
        ≤ (K * ‖cw m₁ j₁‖ * ‖cw m₂ j₂‖) * Ca * Cb :=
          norm_mul_mul_le_ (btwSetK_norm_le hK j₁ j₂) (ha _) (hb _)
      _ = (K * ‖cw m₁ j₁‖ * Ca * Cb) * ‖cw m₂ j₂‖ := by ring

/-! ## The uniform bound -/

/-- **Uniform-in-`t` bound for the twisted bilinear multiplier at arbitrary frequency sets.**  The
double series is dominated by `K · Ch · Ck · Cd₁ · Cd₂ · (∑_j 1/(1+j²))²`, a constant independent
of `t ∈ [1/2,1]`. -/
theorem exists_bound_BtwistSet_uniform (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ)
    (A₁ A₂ : Finset Work.Analysis.IonescuWainger.Circle) (m₁ m₂ : ℝ → ℂ)
    (h k : ℝ → ℤ → ℂ) (x : ℤ)
    (hK : ∃ K : ℝ, ∀ j₁ j₂ : ℤ, ‖Work.KMTAreas.A7.arithKernelSet P
      (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) A₁ A₂ j₁ j₂‖ ≤ K)
    (hdec₁ : ∃ Cd : ℝ, ∀ j : ℤ, ‖Work.KMTAreas.A7.cw m₁ j‖ ≤ Cd / (1 + |(j : ℝ)|)^2)
    (hdec₂ : ∃ Cd : ℝ, ∀ j : ℤ, ‖Work.KMTAreas.A7.cw m₂ j‖ ≤ Cd / (1 + |(j : ℝ)|)^2)
    (hb₁ : ∃ Ch : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ y : ℤ, ‖h t y‖ ≤ Ch)
    (hb₂ : ∃ Ck : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ y : ℤ, ‖k t y‖ ≤ Ck) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      ‖Work.KMTAreas.A7.BtwistSet ρ P l₁ l₂ A₁ A₂ m₁ m₂ (h t) (k t) x‖ ≤ C := by
  classical
  obtain ⟨K, hK⟩ := hK
  obtain ⟨Cd₁, hd₁⟩ := hdec₁
  obtain ⟨Cd₂, hd₂⟩ := hdec₂
  obtain ⟨Ch, hh⟩ := hb₁
  obtain ⟨Ck, hk⟩ := hb₂
  -- the constants are non-negative (evaluate the bounds at `j = 0`, resp. `t = 1/2`, `y = 0`)
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0 0)
  have hCd₁ : 0 ≤ Cd₁ := by
    have h0 : ‖cw m₁ 0‖ ≤ Cd₁ := by simpa using hd₁ 0
    exact le_trans (norm_nonneg _) h0
  have hCd₂ : 0 ≤ Cd₂ := by
    have h0 : ‖cw m₂ 0‖ ≤ Cd₂ := by simpa using hd₂ 0
    exact le_trans (norm_nonneg _) h0
  have hCh : 0 ≤ Ch :=
    le_trans (norm_nonneg _) (hh (1/2) (by constructor <;> norm_num) 0)
  have hCk : 0 ≤ Ck :=
    le_trans (norm_nonneg _) (hk (1/2) (by constructor <;> norm_num) 0)
  -- the summability weight `g j = 1/(1+j²)` and its total mass `SG`
  set g : ℤ → ℝ := fun j => 1 / (1 + (j : ℝ) ^ 2) with hg
  obtain ⟨B, hB0, hBfun⟩ := Work.KMTAreas.tsum_inv_sq_shift_le
  have hg_sum : Summable g := by
    rw [hg]; simpa using (hBfun 0).1
  set SG : ℝ := ∑' j : ℤ, g j with hSG
  have hSG_nonneg : 0 ≤ SG := by
    rw [hSG]
    refine tsum_nonneg (fun j => ?_)
    rw [hg]
    positivity
  -- the comparison `1/(1+|j|)² ≤ g j` and the resulting quadratic-decay bounds
  have hstep : ∀ j : ℤ, (1 : ℝ) / (1 + |(j : ℝ)|) ^ 2 ≤ g j := by
    intro j
    rw [hg]
    apply one_div_le_one_div_of_le (a := 1 + (j : ℝ) ^ 2) (b := (1 + |(j : ℝ)|) ^ 2)
    · nlinarith [sq_nonneg (j : ℝ)]
    · nlinarith [sq_abs (j : ℝ), abs_nonneg (j : ℝ)]
  have hle₁ : ∀ j : ℤ, ‖cw m₁ j‖ ≤ Cd₁ * g j := by
    intro j
    calc ‖cw m₁ j‖ ≤ Cd₁ / (1 + |(j : ℝ)|) ^ 2 := hd₁ j
      _ = Cd₁ * ((1 : ℝ) / (1 + |(j : ℝ)|) ^ 2) := by ring
      _ ≤ Cd₁ * g j := mul_le_mul_of_nonneg_left (hstep j) hCd₁
  have hle₂ : ∀ j : ℤ, ‖cw m₂ j‖ ≤ Cd₂ * g j := by
    intro j
    calc ‖cw m₂ j‖ ≤ Cd₂ / (1 + |(j : ℝ)|) ^ 2 := hd₂ j
      _ = Cd₂ * ((1 : ℝ) / (1 + |(j : ℝ)|) ^ 2) := by ring
      _ ≤ Cd₂ * g j := mul_le_mul_of_nonneg_left (hstep j) hCd₂
  have hm₁ : Summable (fun j : ℤ => ‖cw m₁ j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hle₁ (hg_sum.mul_left Cd₁)
  have hm₂ : Summable (fun j : ℤ => ‖cw m₂ j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hle₂ (hg_sum.mul_left Cd₂)
  set SM₂ : ℝ := ∑' j : ℤ, ‖cw m₂ j‖ with hSM₂
  have hSM₂_nonneg : 0 ≤ SM₂ := by
    rw [hSM₂]; exact tsum_nonneg (fun j => norm_nonneg _)
  have hSM₂_le : SM₂ ≤ Cd₂ * SG := by
    rw [hSM₂, hSG]
    calc ∑' j : ℤ, ‖cw m₂ j‖ ≤ ∑' j : ℤ, Cd₂ * g j :=
          Summable.tsum_le_tsum hle₂ hm₂ (hg_sum.mul_left Cd₂)
      _ = Cd₂ * ∑' j : ℤ, g j := tsum_mul_left
  have hSM₁_le : (∑' j : ℤ, ‖cw m₁ j‖) ≤ Cd₁ * SG := by
    rw [hSG]
    calc ∑' j : ℤ, ‖cw m₁ j‖ ≤ ∑' j : ℤ, Cd₁ * g j :=
          Summable.tsum_le_tsum hle₁ hm₁ (hg_sum.mul_left Cd₁)
      _ = Cd₁ * ∑' j : ℤ, g j := tsum_mul_left
  set Pc : ℝ := K * Ch * Ck * SM₂ with hPc
  have hPc_nonneg : 0 ≤ Pc := by
    rw [hPc]
    exact mul_nonneg (mul_nonneg (mul_nonneg hK0 hCh) hCk) hSM₂_nonneg
  refine ⟨K * Ch * Ck * Cd₂ * Cd₁ * SG * SG, fun t ht => ?_⟩
  have ha : ∀ y : ℤ, ‖h t y‖ ≤ Ch := fun y => hh t ht y
  have hb : ∀ y : ℤ, ‖k t y‖ ≤ Ck := fun y => hk t ht y
  have hsumOuter : Summable (fun j₁ : ℤ => ∑' j₂ : ℤ,
      btwSetK P (arithQ ρ (max l₁ l₂)) A₁ A₂ m₁ m₂ j₁ j₂ * h t (x - j₁) * k t (x - j₂)) :=
    btwSet_summable_of_bounded hK hm₁ hm₂ (h t) (k t) ha hb x
  have hinner : ∀ j₁ : ℤ,
      ‖∑' j₂ : ℤ, btwSetK P (arithQ ρ (max l₁ l₂)) A₁ A₂ m₁ m₂ j₁ j₂ * h t (x - j₁)
        * k t (x - j₂)‖ ≤ Pc * ‖cw m₁ j₁‖ := by
    intro j₁
    have hinnerSum : Summable (fun j₂ : ℤ =>
        btwSetK P (arithQ ρ (max l₁ l₂)) A₁ A₂ m₁ m₂ j₁ j₂ * h t (x - j₁) * k t (x - j₂)) :=
      btwSet_inner_summable hK hm₂ (h t) (k t) ha hb x j₁
    have hinnerNorm : Summable (fun j₂ : ℤ =>
        ‖btwSetK P (arithQ ρ (max l₁ l₂)) A₁ A₂ m₁ m₂ j₁ j₂ * h t (x - j₁)
          * k t (x - j₂)‖) := hinnerSum.norm
    have hpt : ∀ j₂ : ℤ,
        ‖btwSetK P (arithQ ρ (max l₁ l₂)) A₁ A₂ m₁ m₂ j₁ j₂ * h t (x - j₁) * k t (x - j₂)‖
          ≤ (K * ‖cw m₁ j₁‖ * Ch * Ck) * ‖cw m₂ j₂‖ := by
      intro j₂
      calc ‖btwSetK P (arithQ ρ (max l₁ l₂)) A₁ A₂ m₁ m₂ j₁ j₂ * h t (x - j₁)
            * k t (x - j₂)‖
          ≤ (K * ‖cw m₁ j₁‖ * ‖cw m₂ j₂‖) * Ch * Ck :=
            norm_mul_mul_le_ (btwSetK_norm_le hK j₁ j₂) (ha _) (hb _)
        _ = (K * ‖cw m₁ j₁‖ * Ch * Ck) * ‖cw m₂ j₂‖ := by ring
    calc ‖∑' j₂ : ℤ, btwSetK P (arithQ ρ (max l₁ l₂)) A₁ A₂ m₁ m₂ j₁ j₂ * h t (x - j₁)
          * k t (x - j₂)‖
        ≤ ∑' j₂ : ℤ, ‖btwSetK P (arithQ ρ (max l₁ l₂)) A₁ A₂ m₁ m₂ j₁ j₂ * h t (x - j₁)
            * k t (x - j₂)‖ := norm_tsum_le_tsum_norm hinnerNorm
      _ ≤ ∑' j₂ : ℤ, (K * ‖cw m₁ j₁‖ * Ch * Ck) * ‖cw m₂ j₂‖ :=
          Summable.tsum_le_tsum hpt hinnerNorm (hm₂.mul_left _)
      _ = (K * ‖cw m₁ j₁‖ * Ch * Ck) * SM₂ := by
          rw [hSM₂]; exact tsum_mul_left
      _ = Pc * ‖cw m₁ j₁‖ := by rw [hPc]; ring
  calc ‖BtwistSet ρ P l₁ l₂ A₁ A₂ m₁ m₂ (h t) (k t) x‖
      = ‖∑' j₁ : ℤ, ∑' j₂ : ℤ,
          btwSetK P (arithQ ρ (max l₁ l₂)) A₁ A₂ m₁ m₂ j₁ j₂ * h t (x - j₁)
            * k t (x - j₂)‖ := by rw [btwSet_eq]
    _ ≤ ∑' j₁ : ℤ,
          ‖∑' j₂ : ℤ, btwSetK P (arithQ ρ (max l₁ l₂)) A₁ A₂ m₁ m₂ j₁ j₂ * h t (x - j₁)
            * k t (x - j₂)‖ := norm_tsum_le_tsum_norm hsumOuter.norm
    _ ≤ ∑' j₁ : ℤ, Pc * ‖cw m₁ j₁‖ :=
        Summable.tsum_le_tsum hinner hsumOuter.norm (hm₁.mul_left Pc)
    _ = Pc * (∑' j₁ : ℤ, ‖cw m₁ j₁‖) := tsum_mul_left
    _ ≤ Pc * (Cd₁ * SG) := mul_le_mul_of_nonneg_left hSM₁_le hPc_nonneg
    _ ≤ K * Ch * Ck * Cd₂ * Cd₁ * SG * SG := by
        rw [hPc]
        have h1 : K * Ch * Ck * SM₂ ≤ K * Ch * Ck * (Cd₂ * SG) :=
          mul_le_mul_of_nonneg_left hSM₂_le (mul_nonneg (mul_nonneg hK0 hCh) hCk)
        have h2 : (K * Ch * Ck * SM₂) * (Cd₁ * SG)
            ≤ (K * Ch * Ck * (Cd₂ * SG)) * (Cd₁ * SG) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg hCd₁ hSG_nonneg)
        calc (K * Ch * Ck * SM₂) * (Cd₁ * SG)
            ≤ (K * Ch * Ck * (Cd₂ * SG)) * (Cd₁ * SG) := h2
          _ = K * Ch * Ck * Cd₂ * Cd₁ * SG * SG := by ring

end

end Work.KMTAreas.A7
