/-
# The summation of the single-scale model approximation over the lacunary small scales

This module proves `Work.KMTAreas.A7.SmallModApprox_of_single`: the *single-scale* model
approximation of §6 — in the sharp form given by the paper's Proposition `mod-approx` composed
with the functional calculus `bn-ident`, i.e.

  `‖ smallMainPart n − smallModelTuple n ‖_{ℓ^p}
      ≤ K(Λ)·modelWeight A ρ l₁ l₂ k₁ k₂·⌊a n⌋⁻¹·‖f‖_{ℓ^{p₁}}‖g‖_{ℓ^{p₂}}`

with `modelWeight A ρ L = ⟨L⟩^A·2^{A·2^{ρL}}` and `A` independent of `ρ` — summed over the
lacunary scales of the index set, gives the *variational* estimate `Work.KMTAreas.A7.SmallModApprox`
(hypothesis `h1` of `Work.KMTAreas.A7.SmallLossOfBounds`), with the exponent `A + 1` in the
weight `lossWeight (A+1) ρ L = ⟨L⟩^{A+1}·2^{(A+1)ρL}`.

The summation is the paper's (`nmax`) + (`varsum`):

* `V^r(u) ≤ ∑_n 4‖u n‖_{ℓ^p}` (`Work.KMTAreas.A7.VarNormTsumLp`);
* the scale condition `smallCond` implies `L ≤ heightScale C₀ ⌊a n⌋ = C₀ log₂(log₂⌊a n⌋ + 2)`, so
  `∑_{n ∈ smallCond} ⌊a n⌋⁻¹ ≲ 2^{-2^{L/C₀} + 2}`
  (`Work.KMTAreas.A7.invFloorSum_le` together with `tsum_ite_floor_le_indexSet` of
  `A7/ModelApproxHelpers.lean`);
* **this is where the `2^{A·2^{ρL}}` factor of the single scale is killed** — it is the reason why
  the statement must be the *summed* one: for `ρ ≤ 1/(4C₀)` the exponential gain
  `2^{-2^{L/C₀}}` dominates `2^{A2^{ρL}}` uniformly in `L`
  (`Work.KMTAreas.A7.SmallWeightArith`), and the residual constant is absorbed by passing from
  `modelWeight A ρ L` to `lossWeight (A+1) ρ L = ⟨L⟩^{A+1}2^{(A+1)ρL}`
  (`⟨L⟩^A ≤ ⟨L⟩^{A+1}` and `2^{(A+1)ρL} ≥ 1`).

Both tuples carry the *same* guard `smallCond` (`A7/SmallDefs.lean`), so the difference vanishes
off it and the trivial cases are immediate.  The model operator `smallModelOp` is the one of
`A7/SmallDefs.lean`, built from the *exact-height* IW multipliers `Tm ρ l` and the exact-height
arithmetic kernel `smallArithKernel` (`diffFreqs`), which is the convention of the paper's §5–§6
and of the contract's pieces `Fpiece`, `Gpiece`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.SmallDefs
import Submission.Work.KMTAreas.A7.VarNormTsumLp
import Submission.Work.KMTAreas.A7.invFloorSum_le
import Submission.Work.KMTAreas.A7.ModelApproxHelpers
import Submission.Work.KMTAreas.A7.SmallWeightArith

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract Work.Analysis.EndVar

/-- The difference of the two small-scale tuples is supported on the (common) guard `smallCond`. -/
theorem smallDiff_eq_zero_of_not_cond (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ n : ℕ) (h : ¬ smallCond ρ C₀ a l₁ l₂ k₁ k₂ n) :
    (fun x : ℤ => smallMainPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      - smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) = 0 := by
  funext x
  have h1 : smallMainPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
    simp only [smallMainPart]; exact if_neg h
  have h2 : smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
    simp only [smallModelTuple]; exact if_neg h
  simp only [Pi.sub_apply, h1, h2, sub_zero, Pi.zero_apply]

/-- The single-scale form of the model approximation, in the sharp weight
`modelWeight A ρ l₁ l₂ k₁ k₂ · ⌊a n⌋⁻¹` produced by the §6 analysis (Proposition `mod-approx`
composed with `bn-ident`), with `A` independent of `ρ`. -/
def SmallSingleScale (P : ℤ[X]) (p₁ p₂ : ENNReal) : Prop :=
  ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
        ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
          ∀ n : ℕ,
          MeasureTheory.eLpNorm (fun x : ℤ =>
              smallMainPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                - smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) *
              ENNReal.ofReal (modelWeight A ρ l₁ l₂ k₁ k₂) *
              ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) *
              MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
              MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count

/-- **The summation step.**  The single-scale model approximation (in the sharp weight
`modelWeight A ρ l₁ l₂ k₁ k₂·⌊a n⌋⁻¹`) implies the variational small-scale model approximation
(hypothesis `h1` of `SmallLossOfBounds`), with the loss exponent `A + 1`. -/
theorem SmallModApprox_of_single (P : ℤ[X]) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1)
    (hsingle : SmallSingleScale P p₁ p₂) :
    ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
      ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
          ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  smallMainPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                    - smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) *
                ENNReal.ofReal (lossWeight c ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
  classical
  intro C₀ r hC₀ hr
  obtain ⟨A, hA, ρc, hρc, hS⟩ := hsingle C₀ r hC₀ hr
  have hD := invFloorSum_le C₀ hC₀
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  have hq : (1 : ENNReal) ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
  -- the `Λ`-dependent summation constants
  set Dfun : ℝ≥0 → ℝ := fun Λ =>
    if h : 1 < Λ then Classical.choose (hD Λ h) else 0 with hDfun
  have hDfun0 : ∀ Λ : ℝ≥0, 0 ≤ Dfun Λ := by
    intro Λ
    by_cases h : 1 < Λ
    · rw [hDfun]; simp only [dif_pos h]
      exact (Classical.choose_spec (hD Λ h)).1
    · rw [hDfun]; simp [h]
  have hDfunb : ∀ Λ : ℝ≥0, 1 < Λ → ∀ (L : ℕ), 1 ≤ L → ∀ (a : ℕ → ℝ≥0),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      (∑' n : ℕ, (if L ≤ heightScale C₀ (Nat.floor (a n))
        then (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ else 0))
        ≤ Dfun Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2) := by
    intro Λ hΛ L hL a ha ha1
    rw [hDfun]; simp only [dif_pos hΛ]
    exact (Classical.choose_spec (hD Λ hΛ)).2 L hL a ha ha1
  set Efun : ℝ≥0 → ℝ := fun Λ => max (2 * (Λ : ℝ) / ((Λ : ℝ) - 1)) (Dfun Λ) with hEfun
  have hEfun0 : ∀ Λ : ℝ≥0, 0 ≤ Efun Λ := by
    intro Λ
    rw [hEfun]
    exact le_trans (hDfun0 Λ) (le_max_right _ _)
  -- the conclusion
  refine ⟨A + 1, by linarith, min ρc (1 / (4 * (C₀ : ℝ))), lt_min hρc (by positivity), ?_⟩
  intro ρ hρ hρle
  have hρc' : ρ ≤ ρc := le_trans hρle (min_le_left _ _)
  have hρ4 : ρ ≤ 1 / (4 * (C₀ : ℝ)) := le_trans hρle (min_le_right _ _)
  obtain ⟨K, hK⟩ := hS ρ hρ hρc'
  -- the `L`-uniform weight arithmetic
  obtain ⟨Kabs, hKabs1, hKabs⟩ := SmallWeightArith A hA C₀ hC₀ ρ hρ.le hρ4
  have hKconst : ∀ Λ : ℝ≥0, 0 ≤ 4 * (K Λ : ℝ) * Efun Λ * Kabs + 16 := by
    intro Λ
    have h1 : (0 : ℝ) ≤ (K Λ : ℝ) := by positivity
    have h2 := hEfun0 Λ
    have h3 : (0 : ℝ) ≤ Kabs := by linarith
    have h4 : (0 : ℝ) ≤ (K Λ : ℝ) * Efun Λ := mul_nonneg h1 h2
    have h5 : (0 : ℝ) ≤ (K Λ : ℝ) * Efun Λ * Kabs := mul_nonneg h4 h3
    nlinarith [h5]
  refine ⟨fun Λ => ⟨4 * (K Λ : ℝ) * Efun Λ * Kabs + 16, hKconst Λ⟩, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1
  set Kvv : NNReal := ⟨4 * (K Λ : ℝ) * Efun Λ * Kabs + 16, hKconst Λ⟩ with hKvv
  set W : ℝ := modelWeight A ρ l₁ l₂ k₁ k₂ with hW
  set Lr : ℝ := lmaxR l₁ l₂ k₁ k₂ with hLr
  set sig : ℝ := (2 : ℝ) ^ (-((2 : ℝ) ^ (Lr / (C₀ : ℝ))) + 2) with hsig
  set u : ℕ → ℤ → ℂ := fun n x =>
    smallMainPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      - smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x with hu
  set Gc : ℕ → Prop := fun n => smallCond ρ C₀ a l₁ l₂ k₁ k₂ n with hGc
  have hzero : ∀ n : ℕ, ¬ Gc n → u n = 0 := by
    intro n hn
    rw [hu]; exact smallDiff_eq_zero_of_not_cond ρ P C₀ a f g l₁ l₂ k₁ k₂ n hn
  have hLrcast : ((smallL l₁ l₂ k₁ k₂ : ℕ) : ℝ) = Lr := by
    rw [hLr, lmaxR, Work.Analysis.EndVar.lmax, smallL]
    push_cast
    rfl
  -- the per-scale bound, guarded
  have hper : ∀ n : ℕ, MeasureTheory.eLpNorm (fun x : ℤ => u n x)
      ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
      ≤ if Gc n then (K Λ : ENNReal) * ENNReal.ofReal W *
          ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count else 0 := by
    intro n
    by_cases hg : Gc n
    · rw [if_pos hg, hu]
      have h := hK a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 n
      rw [hW]
      exact h
    · rw [if_neg hg, hzero n hg]
      simp
  -- the scale condition implies the height condition
  have hcond : ∀ n : ℕ, Gc n → smallL l₁ l₂ k₁ k₂ ≤ heightScale C₀ (Nat.floor (a n)) := by
    intro n hg
    have h1 : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) := hg.1
    rw [inIndexSet] at h1
    have h2 : max (l₁ : ℤ) (l₂ : ℤ) ≤ ((heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) := h1.1
    have h3 : (k₁ : ℤ) ≤ ((heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) := h1.2.1
    have h4 : (k₂ : ℤ) ≤ ((heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) := h1.2.2
    rw [smallL]
    omega
  have hsum2 : (∑' n : ℕ, (if Gc n then
        ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0))
      ≤ ENNReal.ofReal (Efun Λ * sig) := by
    have hthis := tsum_ite_floor_le_indexSet C₀ hC₀ Λ hΛ (Dfun Λ) (hDfun0 Λ)
      (fun L hL a ha ha1 => hDfunb Λ hΛ L hL a ha ha1) (smallL l₁ l₂ k₁ k₂) (Efun Λ)
      (le_of_eq rfl) a ha ha1 Gc hcond
    rw [hLrcast] at hthis
    exact hthis
  -- the weight comparison
  have hW0 : 0 ≤ W := by rw [hW]; exact modelWeight_nonneg A ρ hA l₁ l₂ k₁ k₂
  have hK0 : (0 : ℝ) ≤ (K Λ : ℝ) := by positivity
  have hE0 : 0 ≤ Efun Λ := hEfun0 Λ
  have hKabs0 : 0 ≤ Kabs := by linarith
  have hLr0 : (0 : ℝ) ≤ Lr := by rw [hLr]; exact lmaxR_nonneg l₁ l₂ k₁ k₂
  have hKE : (0 : ℝ) ≤ 4 * (K Λ : ℝ) * Efun Λ :=
    mul_nonneg (mul_nonneg (by norm_num) hK0) hE0
  have hKEK : (0 : ℝ) ≤ 4 * (K Λ : ℝ) * Efun Λ * Kabs := mul_nonneg hKE hKabs0
  -- `modelWeight A ρ L · sig ≤ ⟨L⟩^A · Kabs`
  have hWsig : W * sig ≤ (1 + Lr) ^ A * Kabs := by
    rw [hW, modelWeight, hsig, hLr]
    have hmono : A * (2 : ℝ) ^ (ρ * Lr) ≤ A * max ((2 : ℝ) ^ (ρ * Lr)) Lr :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hA
    have h2 : (2 : ℝ) ^ (A * (2 : ℝ) ^ (ρ * Lr))
        ≤ (2 : ℝ) ^ (A * max ((2 : ℝ) ^ (ρ * Lr)) Lr) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hmono
    have h3 := hKabs (smallL l₁ l₂ k₁ k₂)
    rw [hLrcast] at h3
    have h4 : (0 : ℝ) ≤ (1 + Lr) ^ A := Real.rpow_nonneg (by linarith) A
    have h5 : (0 : ℝ) ≤ (2 : ℝ) ^ (-((2 : ℝ) ^ (Lr / (C₀ : ℝ))) + 2) :=
      le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
    calc (1 + Lr) ^ A * (2 : ℝ) ^ (A * (2 : ℝ) ^ (ρ * Lr)) *
          (2 : ℝ) ^ (-((2 : ℝ) ^ (Lr / (C₀ : ℝ))) + 2)
        = (1 + Lr) ^ A * ((2 : ℝ) ^ (A * (2 : ℝ) ^ (ρ * Lr)) *
            (2 : ℝ) ^ (-((2 : ℝ) ^ (Lr / (C₀ : ℝ))) + 2)) := by ring
      _ ≤ (1 + Lr) ^ A * ((2 : ℝ) ^ (A * max ((2 : ℝ) ^ (ρ * Lr)) Lr) *
            (2 : ℝ) ^ (-((2 : ℝ) ^ (Lr / (C₀ : ℝ))) + 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 h5) h4
      _ ≤ (1 + Lr) ^ A * Kabs := mul_le_mul_of_nonneg_left h3 h4
  -- the real weight comparison
  have hreal : 4 * (K Λ : ℝ) * W * (Efun Λ * sig)
      ≤ (4 * (K Λ : ℝ) * Efun Λ * Kabs + 16) * lossWeight (A + 1) ρ l₁ l₂ k₁ k₂ := by
    have hpow : (1 + Lr) ^ A ≤ (1 + Lr) ^ (A + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ ((A + 1) * ρ * Lr) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg (mul_nonneg (by linarith) hρ.le) hLr0)
    have hLw : lossWeight (A + 1) ρ l₁ l₂ k₁ k₂
        = (1 + Lr) ^ (A + 1) * (2 : ℝ) ^ ((A + 1) * ρ * Lr) := by
      rw [lossWeight, hLr]
    have hLw0 : 0 ≤ lossWeight (A + 1) ρ l₁ l₂ k₁ k₂ :=
      lossWeight_nonneg (A + 1) ρ l₁ l₂ k₁ k₂
    calc 4 * (K Λ : ℝ) * W * (Efun Λ * sig)
        = 4 * (K Λ : ℝ) * Efun Λ * (W * sig) := by ring
      _ ≤ 4 * (K Λ : ℝ) * Efun Λ * ((1 + Lr) ^ A * Kabs) :=
          mul_le_mul_of_nonneg_left hWsig hKE
      _ = (4 * (K Λ : ℝ) * Efun Λ * Kabs) * (1 + Lr) ^ A := by ring
      _ ≤ (4 * (K Λ : ℝ) * Efun Λ * Kabs) *
            ((1 + Lr) ^ (A + 1) * (2 : ℝ) ^ ((A + 1) * ρ * Lr)) := by
          refine mul_le_mul_of_nonneg_left ?_ hKEK
          calc (1 + Lr) ^ A ≤ (1 + Lr) ^ (A + 1) := hpow
            _ = (1 + Lr) ^ (A + 1) * 1 := (mul_one _).symm
            _ ≤ (1 + Lr) ^ (A + 1) * (2 : ℝ) ^ ((A + 1) * ρ * Lr) :=
                mul_le_mul_of_nonneg_left hone (Real.rpow_nonneg (by linarith) _)
      _ = (4 * (K Λ : ℝ) * Efun Λ * Kabs + 16) * lossWeight (A + 1) ρ l₁ l₂ k₁ k₂
            - 16 * lossWeight (A + 1) ρ l₁ l₂ k₁ k₂ := by rw [hLw]; ring
      _ ≤ (4 * (K Λ : ℝ) * Efun Λ * Kabs + 16) * lossWeight (A + 1) ρ l₁ l₂ k₁ k₂ := by
          linarith
  -- the `ENNReal` version of the weight comparison
  have hmul : 4 * (K Λ : ENNReal) * ENNReal.ofReal W * ENNReal.ofReal (Efun Λ * sig)
      ≤ (Kvv : ENNReal) * ENNReal.ofReal (lossWeight (A + 1) ρ l₁ l₂ k₁ k₂) := by
    have hKcoe : (4 : ENNReal) * (K Λ : ENNReal) = ENNReal.ofReal (4 * (K Λ : ℝ)) := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    have hmerge : ENNReal.ofReal (4 * (K Λ : ℝ)) * ENNReal.ofReal W *
          ENNReal.ofReal (Efun Λ * sig)
        = ENNReal.ofReal (4 * (K Λ : ℝ) * W * (Efun Λ * sig)) := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * (K Λ : ℝ)),
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * (K Λ : ℝ) * W)]
    have hKfuncoe : ((Kvv : NNReal) : ENNReal)
        = ENNReal.ofReal (4 * (K Λ : ℝ) * Efun Λ * Kabs + 16) :=
      ENNReal.ofReal_coe_nnreal.symm
    calc 4 * (K Λ : ENNReal) * ENNReal.ofReal W * ENNReal.ofReal (Efun Λ * sig)
        = ENNReal.ofReal (4 * (K Λ : ℝ) * W * (Efun Λ * sig)) := by rw [hKcoe, hmerge]
      _ ≤ ENNReal.ofReal ((4 * (K Λ : ℝ) * Efun Λ * Kabs + 16) *
            lossWeight (A + 1) ρ l₁ l₂ k₁ k₂) := ENNReal.ofReal_le_ofReal hreal
      _ = (Kvv : ENNReal) * ENNReal.ofReal (lossWeight (A + 1) ρ l₁ l₂ k₁ k₂) := by
          rw [hKfuncoe,
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * (K Λ : ℝ) * Efun Λ * Kabs + 16)]
  -- the chain
  have hVar := VarNormTsumLp (r := r) hr1 (p := (p₁⁻¹ + p₂⁻¹)⁻¹) hq u
  refine hVar.trans ?_
  have hstep1 : (∑' n : ℕ, 4 * MeasureTheory.eLpNorm (fun x : ℤ => u n x)
        ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count)
      ≤ ∑' n : ℕ, 4 * (if Gc n then (K Λ : ENNReal) * ENNReal.ofReal W *
          ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count else 0) :=
    ENNReal.tsum_le_tsum (fun n => mul_le_mul' le_rfl (hper n))
  refine hstep1.trans ?_
  have hstep2 : (∑' n : ℕ, 4 * (if Gc n then (K Λ : ENNReal) * ENNReal.ofReal W *
        ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) *
        MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
        MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count else 0))
      = (4 * (K Λ : ENNReal) * ENNReal.ofReal W *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) *
        (∑' n : ℕ, (if Gc n then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0)) := by
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    by_cases hg : Gc n
    · rw [if_pos hg, if_pos hg]; ring
    · rw [if_neg hg, if_neg hg]; simp
  rw [hstep2]
  calc (4 * (K Λ : ENNReal) * ENNReal.ofReal W *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) *
        (∑' n : ℕ, (if Gc n then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0))
      ≤ (4 * (K Λ : ENNReal) * ENNReal.ofReal W *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) * ENNReal.ofReal (Efun Λ * sig) :=
        mul_le_mul' le_rfl hsum2
    _ = (4 * (K Λ : ENNReal) * ENNReal.ofReal W * ENNReal.ofReal (Efun Λ * sig)) *
          (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) := by ring
    _ ≤ ((Kvv : ENNReal) * ENNReal.ofReal (lossWeight (A + 1) ρ l₁ l₂ k₁ k₂)) *
          (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) :=
        mul_le_mul' hmul le_rfl
    _ = (Kvv : ENNReal) * ENNReal.ofReal (lossWeight (A + 1) ρ l₁ l₂ k₁ k₂) *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by ring

end

end Work.KMTAreas.A7
