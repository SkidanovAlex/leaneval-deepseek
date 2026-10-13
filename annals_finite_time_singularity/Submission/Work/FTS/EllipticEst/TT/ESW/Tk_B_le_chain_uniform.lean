import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.ESW.Defs
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.TT.ESW.ChainAux
import Submission.Work.FTS.EllipticEst.TT.ESW.TkChainIntegrable
import Submission.Work.FTS.EllipticEst.remov.high_chain_sum_self

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ESW.Tk_B_le_chain_uniform`: the top angular slot, with a constant uniform in `α` and `Ψ`

`Tk_B_le_chain` (in `ChainAux.lean`) proves, for *fixed* `α` and `Ψ`,

`Step.Tk α k (∂_θθΨ) ≤ C(α,Ψ) · (Σ_{1 ≤ r ≤ k-1} ∫∫ (∂_θ^r∂_θθΨ)² w² sin^{2r-γ}
   + ∫∫ (∂_θ^{k+2}Ψ)² w² sin^{2k-γ})`

with a constant `C(α,Ψ)` that is allowed to depend on the datum.  Here we remove that
dependence: the assembly `Tk_chain_of` and the pointwise chain both use a constant depending
on `k` only, so a single constant works for all `α` and all `Ψ` simultaneously.

The content is

* `TkChain_pointwise`: the pointwise forward chain
  `(D_θ^k v · W_t)² ≤ C_k · Σ_{1 ≤ r ≤ k} w² (∂_θ^r v)² sin(2θ)^{2r-γ}`,
  obtained from the *exact* expansion `D_θ^k v = Σ_{r ≤ k} a_{k,r}(θ) ∂_θ^r v` with
  `a_{k,r} = sin(2θ)^r · b_{k,r}` (`b_{k,r}` bounded, `a_{k,0} = 0`) followed by
  Cauchy–Schwarz.  The constant is `k · K²` with `K` a bound for the `b_{k,r}`, hence
  depends on `k` but neither on `α` nor on `v`;
* `Tk_B_le_chain_fixed`: the measure-theoretic assembly `Tk_chain_of` +
  `Icc 1 k = insert k (Icc 1 (k-1))` + `∂_θ^k∂_θ²Ψ = ∂_θ^{k+2}Ψ`, with the constant kept
  explicit (`Ca` on both sides) instead of hidden behind an existential;
* the target `Tk_B_le_chain_uniform`, by pulling the existential out of `α`, `Ψ`.
-/

namespace Work.FTS.EllipticEst.TT.ESW

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Two elementary bookkeeping lemmas -/

/-- The weight split `sin(2θ)^{2r-γ} = sin(2θ)^{2r}·sin(2θ)^{-γ}` in the shape needed by the
chain: on the interval where `sin(2θ) > 0`, `Real.rpow_add` gives the additive splitting and
`Real.rpow_natCast` converts the natural power `sin(2θ)^{2r}`. -/
theorem sin_rpow_split {θ : ℝ} (hs : 0 < Real.sin (2 * θ)) (r : ℕ) (γ : ℝ) :
    Real.sin (2 * θ) ^ (2 * (r : ℝ) - γ)
      = (Real.sin (2 * θ) ^ r) ^ 2 * Real.sin (2 * θ) ^ (-γ) := by
  have h1 : (2 * (r : ℝ) - γ) = ((2 * r : ℕ) : ℝ) + (-γ) := by push_cast; ring
  rw [h1, Real.rpow_add hs, Real.rpow_natCast, ← pow_mul, Nat.mul_comm 2 r]

/-- Reindexing `Icc 1 k` against `range k`: `Σ_{1 ≤ r ≤ k} f r = Σ_{i < k} f (i+1)`. -/
theorem sumIccOne_eq (k : ℕ) (f : ℕ → ℝ) :
    ∑ r ∈ Finset.Icc 1 k, f r = ∑ i ∈ Finset.range k, f (i + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-! ## The pointwise forward chain -/

/-- **The pointwise `D_θ`-chain, with a constant depending on `k` only.**  For `k ≥ 1`, at every
point where `v` is `C^∞`, the top angular slot `(D_θ^k v · W_t)²` is dominated by the plain
angular slots `(∂_θ^r v)² sin(2θ)^{2r-γ}`, `1 ≤ r ≤ k`.

The proof uses the exact expansion `D_θ^k v = Σ_{r ≤ k} a_{k,r}(θ) ∂_θ^r v`
(`selfdth.DthIter_expansion_local`) together with the divisibility `a_{k,r} = sin(2θ)^r b_{k,r}`
with `b_{k,r}` bounded (`selfdth.dthCoef_eq_sin_pow_mul_dB`, `selfdth.dB_bounded`) and the
vanishing of the `r = 0` coefficient (`selfdth.dB_apply_zero_of_one_le`); Cauchy–Schwarz on the
resulting `k`-term sum and the weight identity `sin^{-γ}·sin^{2r} = sin^{2r-γ}` finish it. -/
theorem TkChain_pointwise (k : ℕ) (hk : 1 ≤ k) :
    ∃ Ca : ℝ, 0 < Ca ∧ ∀ (α : ℝ) (v : ℝ → ℝ → ℝ) (z θ : ℝ),
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry v) (z, θ)) →
      (Work.Spaces.DthIter k v z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Ca * ∑ r ∈ Finset.Icc 1 k, ChainG α v z θ r := by
  classical
  choose KB hKB using fun r : ℕ => Work.FTS.EllipticEst.remov.selfdth.dB_bounded k r
  set KD : ℝ := 1 + ∑ r ∈ Finset.Icc 1 k, (KB r + 1) with hKD
  have hKD1 : 1 ≤ KD := by
    rw [hKD]
    have h : 0 ≤ ∑ r ∈ Finset.Icc 1 k, (KB r + 1) :=
      Finset.sum_nonneg (fun r _ => by linarith [(hKB r).1])
    linarith
  have hKDb : ∀ (r : ℕ) (θ : ℝ), 1 ≤ r → r ≤ k →
      |Work.FTS.EllipticEst.remov.selfdth.dB k r θ| ≤ KD := by
    intro r θ hr1 hrk
    have h1 : KB r + 1 ≤ ∑ r' ∈ Finset.Icc 1 k, (KB r' + 1) :=
      Finset.single_le_sum (f := fun r' => KB r' + 1)
        (fun r' _ => by linarith [(hKB r').1]) (Finset.mem_Icc.mpr ⟨hr1, hrk⟩)
    have h2 : |Work.FTS.EllipticEst.remov.selfdth.dB k r θ| ≤ KB r := (hKB r).2 θ
    rw [hKD] at *
    linarith
  refine ⟨(k : ℝ) * KD ^ 2, by positivity, ?_⟩
  intro α v z θ hθ hf
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hdB0 : Work.FTS.EllipticEst.remov.selfdth.dB k 0 θ = 0 :=
    congrFun (Work.FTS.EllipticEst.remov.selfdth.dB_apply_zero_of_one_le k hk) θ
  have hdc0 : Work.FTS.EllipticEst.remov.selfdth.dthCoef k 0 θ = 0 := by
    rw [congrFun (Work.FTS.EllipticEst.remov.selfdth.dthCoef_eq_sin_pow_mul_dB k 0) θ,
      hdB0, mul_zero]
  -- Step 1: the triangular expansion, with the `r = 0` term dropped
  have hstep1 : |Work.Spaces.DthIter k v z θ|
      ≤ KD * ∑ r ∈ Finset.Icc 1 k,
          (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ| := by
    have hexp : Work.Spaces.DthIter k v z θ
        = ∑ r ∈ Finset.range (k + 1),
            Work.FTS.EllipticEst.remov.selfdth.dthCoef k r θ
              * Work.Spaces.pthIter r v z θ :=
      Work.FTS.EllipticEst.remov.selfdth.DthIter_expansion_local k v z θ hf
    rw [hexp, Finset.sum_range_succ']
    simp only [hdc0, zero_mul, add_zero]
    have h1 : |∑ i ∈ Finset.range k, Work.FTS.EllipticEst.remov.selfdth.dthCoef k (i + 1) θ
          * Work.Spaces.pthIter (i + 1) v z θ|
        ≤ ∑ i ∈ Finset.range k,
            (Real.sin (2 * θ)) ^ (i + 1)
              * |Work.FTS.EllipticEst.remov.selfdth.dB k (i + 1) θ|
              * |Work.Spaces.pthIter (i + 1) v z θ| := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum fun i _ => ?_
      rw [show Work.FTS.EllipticEst.remov.selfdth.dthCoef k (i + 1) θ
          = (Real.sin (2 * θ)) ^ (i + 1) * Work.FTS.EllipticEst.remov.selfdth.dB k (i + 1) θ
          from congrFun (Work.FTS.EllipticEst.remov.selfdth.dthCoef_eq_sin_pow_mul_dB k (i + 1)) θ,
        abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hs.le _)]
    have h2 : ∑ i ∈ Finset.range k,
            (Real.sin (2 * θ)) ^ (i + 1)
              * |Work.FTS.EllipticEst.remov.selfdth.dB k (i + 1) θ|
              * |Work.Spaces.pthIter (i + 1) v z θ|
        ≤ ∑ i ∈ Finset.range k,
            KD * ((Real.sin (2 * θ)) ^ (i + 1) * |Work.Spaces.pthIter (i + 1) v z θ|) := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hi1 : i + 1 ≤ k := by have := Finset.mem_range.mp hi; omega
      have hb : |Work.FTS.EllipticEst.remov.selfdth.dB k (i + 1) θ| ≤ KD :=
        hKDb (i + 1) θ (by omega) hi1
      have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (i + 1) := pow_nonneg hs.le _
      have ha : 0 ≤ |Work.Spaces.pthIter (i + 1) v z θ| := abs_nonneg _
      calc (Real.sin (2 * θ)) ^ (i + 1)
            * |Work.FTS.EllipticEst.remov.selfdth.dB k (i + 1) θ|
            * |Work.Spaces.pthIter (i + 1) v z θ|
          ≤ (Real.sin (2 * θ)) ^ (i + 1) * KD
              * |Work.Spaces.pthIter (i + 1) v z θ| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hsnn) ha
        _ = KD * ((Real.sin (2 * θ)) ^ (i + 1)
              * |Work.Spaces.pthIter (i + 1) v z θ|) := by ring
    have h3 : (∑ i ∈ Finset.range k,
            KD * ((Real.sin (2 * θ)) ^ (i + 1) * |Work.Spaces.pthIter (i + 1) v z θ|))
        = KD * ∑ r ∈ Finset.Icc 1 k,
            (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ| := by
      rw [sumIccOne_eq k (fun r => (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|),
        Finset.mul_sum]
    calc |∑ i ∈ Finset.range k, Work.FTS.EllipticEst.remov.selfdth.dthCoef k (i + 1) θ
          * Work.Spaces.pthIter (i + 1) v z θ| ≤ _ := h1
      _ ≤ _ := h2
      _ = _ := h3
  -- Step 2: Cauchy-Schwarz on the `k`-term chain
  have hcs : (Work.Spaces.DthIter k v z θ) ^ 2 ≤ KD ^ 2 *
      ((k : ℝ) * ∑ r ∈ Finset.Icc 1 k,
        ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2) := by
    have h1 : (Work.Spaces.DthIter k v z θ) ^ 2 = |Work.Spaces.DthIter k v z θ| ^ 2 :=
      (sq_abs _).symm
    rw [h1]
    have h2 : |Work.Spaces.DthIter k v z θ| ^ 2
        ≤ (KD * ∑ r ∈ Finset.Icc 1 k,
            (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hstep1 2
    have h4 : (∑ r ∈ Finset.Icc 1 k,
          (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2
        ≤ (k : ℝ) * ∑ r ∈ Finset.Icc 1 k,
            ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.Icc 1 k)
        (f := fun r => (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|)
      rw [Nat.card_Icc, show k + 1 - 1 = k from by omega] at h
      exact h
    calc |Work.Spaces.DthIter k v z θ| ^ 2
        ≤ (KD * ∑ r ∈ Finset.Icc 1 k,
            (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2 := h2
      _ = KD ^ 2 * (∑ r ∈ Finset.Icc 1 k,
            (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2 := by rw [mul_pow]
      _ ≤ KD ^ 2 * ((k : ℝ) * ∑ r ∈ Finset.Icc 1 k,
            ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2) :=
          mul_le_mul_of_nonneg_left h4 (sq_nonneg KD)
  -- Step 3: insert the weight `(W_t)² = w² sin^{-γ}` slot by slot
  have hWt : (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
    congr 1
    rw [sq, ← Real.rpow_add hs]
    congr 1
    ring
  have hXnn : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _)
  have hterm : ∀ r ∈ Finset.Icc 1 k,
      ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        = ChainG α v z θ r := by
    intro r _
    rw [ChainG]
    change ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = Work.Spaces.w z ^ 2 * (Work.Spaces.pthIter r v z θ ^ 2
          * Real.sin (2 * θ) ^ (2 * (r : ℝ) - Work.Spaces.gam α))
    rw [sin_rpow_split hs r (Work.Spaces.gam α), mul_pow, sq_abs]
    ring
  rw [mul_pow, hWt]
  calc (Work.Spaces.DthIter k v z θ) ^ 2
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ (KD ^ 2 * ((k : ℝ) * ∑ r ∈ Finset.Icc 1 k,
            ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2))
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
        mul_le_mul_of_nonneg_right hcs hXnn
    _ = KD ^ 2 * ((k * (∑ r ∈ Finset.Icc 1 k,
            ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2))
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
        ring
    _ = KD ^ 2 * (k * ∑ r ∈ Finset.Icc 1 k,
            (((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))) := by
        rw [mul_assoc, Finset.sum_mul]
    _ = KD ^ 2 * (k * ∑ r ∈ Finset.Icc 1 k, ChainG α v z θ r) := by
        rw [Finset.sum_congr rfl hterm]
    _ = (k : ℝ) * KD ^ 2 * ∑ r ∈ Finset.Icc 1 k, ChainG α v z θ r := by
        ring

/-! ## The measure-theoretic assembly, with the constant kept explicit -/

/-- **`Tk_B_le_chain_aux` with the constant explicit.**  The pointwise chain with the fixed
constant `Ca` (the content of `TkChain_pointwise`) together with the integrability of the chain
slots gives the chain bound for `Bsl Ψ = ∂_θθΨ` with that same constant. -/
theorem Tk_B_le_chain_fixed {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {Ca : ℝ} (hCa_pos : 0 < Ca)
    (hCa : ∀ (α' : ℝ) (v : ℝ → ℝ → ℝ) (z θ : ℝ), θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry v) (z, θ)) →
      (Work.Spaces.DthIter k v z θ * Work.Spaces.Wt α' z θ) ^ 2
        ≤ Ca * ∑ r ∈ Finset.Icc 1 k, ChainG α' v z θ r)
    (hintθ : ∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => ChainG α (Bsl Ψ) z θ m) Work.Spaces.Iθ)
    (hintz : ∀ m : ℕ, 1 ≤ m → m ≤ k →
      MeasureTheory.IntegrableOn (fun z => ChainH α (Bsl Ψ) z m) Work.Spaces.Iz) :
    Work.FTS.EllipticEst.remov.Step.Tk α k (Bsl Ψ) ≤ Ca *
        ((∑ r ∈ Finset.Icc 1 (k - 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter r (Bsl Ψ) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α))
          + ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen (Bsl Ψ) := SmoothOpen.pthIter hΨ 2
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Bsl Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hSO n
  have hcore := Tk_chain_of hk hCa_pos hsm (fun z θ hθ hs => hCa α (Bsl Ψ) z θ hθ hs) hintθ hintz
  have htop : (∫ z in Work.Spaces.Iz, ChainH α (Bsl Ψ) z k)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - Work.Spaces.gam α)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter k (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - Work.Spaces.gam α)) = _
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    rw [← pthIter_add k 2 Ψ]
  calc Work.FTS.EllipticEst.remov.Step.Tk α k (Bsl Ψ)
      ≤ Ca * ∑ r ∈ Finset.Icc 1 k, ∫ z in Work.Spaces.Iz, ChainH α (Bsl Ψ) z r := hcore
    _ = Ca * ((∫ z in Work.Spaces.Iz, ChainH α (Bsl Ψ) z k)
          + (∑ r ∈ Finset.Icc 1 (k - 1), ∫ z in Work.Spaces.Iz, ChainH α (Bsl Ψ) z r)) := by
        rw [Icc_one_split hk, Finset.sum_insert (not_mem_Icc_pred hk)]
    _ = Ca * ((∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - Work.Spaces.gam α))
          + (∑ r ∈ Finset.Icc 1 (k - 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter r (Bsl Ψ) z θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (r : ℝ) - Work.Spaces.gam α))) := by
        rw [htop]
    _ = Ca * ((∑ r ∈ Finset.Icc 1 (k - 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter r (Bsl Ψ) z θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (r : ℝ) - Work.Spaces.gam α))
          + ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - Work.Spaces.gam α)) := by
        ring

/-- **The target.**  The constant of the chain `Tk_B_le_chain` can be taken independent of the
datum `(α,Ψ)`: it is the constant of the pointwise chain (`TkChain_pointwise`), which depends on
`k` only, and the assembly is uniform in the datum. -/
theorem Tk_B_le_chain_uniform (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (Ψ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen Ψ →
      Work.Spaces.HkMem α k (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ) →
      Work.FTS.EllipticEst.remov.Step.Tk α k (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ) ≤ C *
        ((∑ r ∈ Finset.Icc 1 (k - 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter r (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α))
          + ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) := by
  obtain ⟨Ca, hCa_pos, hCa⟩ := TkChain_pointwise k hk
  refine ⟨Ca, hCa_pos, ?_⟩
  intro α Ψ hΨ hmem
  have hSO : Work.FTS.EllipticEst.SmoothOpen (Bsl Ψ) := SmoothOpen.pthIter hΨ 2
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Bsl Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hSO n
  have hintθ : ∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => ChainG α (Bsl Ψ) z θ m) Work.Spaces.Iθ :=
    fun m hm hmk z hz =>
      (TkChainIntegrable (α := α) (K := k) (v := Bsl Ψ) (m := m) hm hmk hsm hmem).1 z hz
  have hintz : ∀ m : ℕ, 1 ≤ m → m ≤ k →
      MeasureTheory.IntegrableOn (fun z => ChainH α (Bsl Ψ) z m) Work.Spaces.Iz :=
    fun m hm hmk =>
      (TkChainIntegrable (α := α) (K := k) (v := Bsl Ψ) (m := m) hm hmk hsm hmem).2
  exact Tk_B_le_chain_fixed hk hΨ hCa_pos
    (fun α' v z θ hθ hs => hCa α' v z θ hθ hs) hintθ hintz

end Work.FTS.EllipticEst.TT.ESW
