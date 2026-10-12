import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.LatSym.iteratedFDeriv_le_of_dIter_decay
import Submission.Work.BoseBoxFock.LatSym.quadCut_iteratedFDeriv_le
import Submission.Work.BoseBoxFock.lap3_ibp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.LatSym.integral_mul_lap3_eq_of_quad`

`lap3 = Δ³` (see `Submission/Work/BoseBoxFock/NormSymAux.lean`, where
`lap3 f = ∑_a ∑_b ∑_c dIter f (lap3List a b c)`).

Target: the `Δ³`-integration by parts for a symbol of **quadratic growth**:

  `∫ p, (σ p : ℂ) * lap3 v p = ∫ p, lap3 (fun q => (σ q : ℂ)) q * v p`

where `σ` is smooth, `|σ| ≤ A (1+‖·‖)²` and `‖iteratedFDeriv ℝ 6 σ‖` is integrable — so **all the
`L¹`-information is on `lap3 σ`** (`NormSymAux.norm_lap3_apply_le`:
`‖lap3 σ p‖ ≤ 27 ‖iteratedFDeriv ℝ 6 σ p‖`) — while `v` is smooth with all its `dIter`'s of order
`≤ 6` decaying like `(1+‖p‖)^{-7}`.  `σ` is **not** compactly supported, so the sibling
`Work.BoseBoxFock.LatSym.integral_lap3_mul_eq` (which needs the compact support on its *first*
argument) does not apply directly; the truncation goes on `v`.

## Proof

`σ` is not compactly supported, so the truncation is put on `v`: let
`χ_n := Work.BoseBoxFock.LatSym.quadCut n` be the truncating bump of
`Submission/Work/BoseBoxFock/LatSym/quadCutDefs.lean` (smooth, equal to `1` on `closedBall 0 (n+1)`,
vanishing outside `closedBall 0 (2(n+1))`, with iterated derivatives bounded uniformly in `n` and
in the point).

1. For every `n`, the unconditional compact-support integration by parts
   `Work.BoseBoxFock.lap3_ibp`, with `f := fun p => (σ p : ℂ)` and `g := fun p => v p * χ_n p`,
   gives `∫ p, (σ p : ℂ) * lap3 (v · χ_n) p = ∫ p, lap3 (fun q => (σ q : ℂ)) p * (v p * χ_n p)`.
2. The right-hand side converges to `∫ p, lap3 σ p * v p` by dominated convergence: the integrand is
   bounded by `27 · C · ‖D⁶σ‖ ∈ L¹` (using only the *order-0* decay `‖v p‖ ≤ C (1+‖p‖)^{-7}` from
   `hvdec` at `L = []`) and converges pointwise because `χ_n = 1` near `p` for `n` large.
3. The left-hand side converges to `∫ p, (σ p : ℂ) * lap3 v p`: pointwise because
   `v · χ_n =ᶠ[𝓝 p] v` for `n` large (so the sixth iterated derivatives at `p` agree, hence `lap3`
   does), and by dominated convergence with the majorant `|A| · 27 · K · (1+‖p‖)^{-5}` — the sixth
   derivative of the product is handled by `norm_iteratedFDeriv_mul_le`, whose two factors are
   controlled by the decay of `v` (`iteratedFDeriv_le_of_dIter_decay`, obtained from `hvdec` by
   expanding a multilinear map in the basis `single k 1` of `ℝ³`) and by the uniform bound on `χ_n`
   (`quadCut_iteratedFDeriv_le`).
4. `tendsto_nhds_unique` in `ℂ` finishes the proof.
-/

noncomputable section

open MeasureTheory Filter
open scoped Real BigOperators Topology

namespace Work.BoseBoxFock.LatSym

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Elementary helpers -/

/-- `lap3` of a smooth function is continuous. -/
lemma continuous_lap3 {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) : Continuous (lap3 g) := by
  change Continuous (fun p : E3 => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
    dIter g (lap3List a b c) p)
  refine continuous_finsetSum _ (fun a _ => ?_)
  refine continuous_finsetSum _ (fun b _ => ?_)
  refine continuous_finsetSum _ (fun c _ => ?_)
  exact (Work.BoseBoxFock.contDiff_dIter hg (lap3List a b c)).continuous

/-- The norm of a real number seen as a complex number. -/
lemma norm_ofReal_eq_abs (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by simp

/-- The norm of the coercion `ℝ → ℂ` as a continuous linear map. -/
lemma norm_ofRealCLM_le_one : ‖(Complex.ofRealCLM : ℝ →L[ℝ] ℂ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun z => ?_)
  rw [one_mul]
  rw [show (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) z = ((z : ℝ) : ℂ) from rfl, norm_ofReal_eq_abs,
    Real.norm_eq_abs]

/-- Complexification does not increase the iterated-derivative norms. -/
lemma norm_iteratedFDeriv_ofReal_comp_le {f : E3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k : ℕ) (p : E3) :
    ‖iteratedFDeriv ℝ k (fun q => ((f q : ℝ) : ℂ)) p‖ ≤ ‖iteratedFDeriv ℝ k f p‖ := by
  have hfun : (fun q : E3 => ((f q : ℝ) : ℂ))
      = (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) ∘ f := rfl
  have hcomp := ContinuousLinearMap.iteratedFDeriv_comp_left (𝕜 := ℝ)
    (g := (Complex.ofRealCLM : ℝ →L[ℝ] ℂ)) (f := f) (x := p) (n := (⊤ : ℕ∞))
    hf.contDiffAt (i := k) (WithTop.coe_le_coe.mpr le_top)
  rw [hfun, hcomp]
  calc ‖(Complex.ofRealCLM : ℝ →L[ℝ] ℂ).compContinuousMultilinearMap
        (iteratedFDeriv ℝ k f p)‖
      ≤ ‖(Complex.ofRealCLM : ℝ →L[ℝ] ℂ)‖ * ‖iteratedFDeriv ℝ k f p‖ :=
        ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 1 * ‖iteratedFDeriv ℝ k f p‖ :=
        mul_le_mul_of_nonneg_right norm_ofRealCLM_le_one (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ k f p‖ := one_mul _

/-- For every `p` and all sufficiently large `n`, `‖p‖ < n + 1`. -/
lemma eventually_norm_lt_succ_nat (p : E3) : ∀ᶠ n : ℕ in atTop, ‖p‖ < (n : ℝ) + 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖p‖
  refine Filter.eventually_atTop.mpr ⟨N, fun b hb => ?_⟩
  have h1 : (N : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  linarith

/-- The elementary exponent identity `x² · x^{-7} = x^{-5}` for `x > 0`. -/
lemma sq_mul_rpow_neg_seven (x : ℝ) (hx : 0 < x) :
    x ^ (2 : ℕ) * x ^ (-7 : ℝ) = x ^ (-5 : ℝ) := by
  rw [show x ^ (2 : ℕ) = x ^ ((2 : ℕ) : ℝ) from (Real.rpow_natCast x 2).symm,
    ← Real.rpow_add hx]
  norm_num

/-- The elementary bound `x^{-7} ≤ 1` for `x ≥ 1`. -/
lemma rpow_neg_seven_le_one {x : ℝ} (hx : 1 ≤ x) : x ^ (-7 : ℝ) ≤ 1 := by
  have h := Real.rpow_le_rpow_of_exponent_le (x := x) (y := (-7 : ℝ)) (z := 0) hx (by norm_num)
  rwa [Real.rpow_zero] at h

/-! ## 2. The Leibniz estimate for `lap3` of a product -/

/-- The Leibniz estimate for `lap3` of a product: if the iterated derivatives of `f` of order
`≤ 6` decay like `K (1+‖·‖)^{-7}` and those of `g` of order `≤ 6` are bounded by `B`, then
`lap3 (f · g)` is bounded by `27 (∑_i C(6,i) K B) (1+‖·‖)^{-7}`. -/
lemma norm_lap3_mul_le {f g : E3 → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hfd : ∀ i : ℕ, i ≤ 6 → ∀ p : E3,
      ‖iteratedFDeriv ℝ i f p‖ ≤ K * (1 + ‖p‖) ^ (-7 : ℝ))
    (hgd : ∀ k : ℕ, k ≤ 6 → ∀ p : E3, ‖iteratedFDeriv ℝ k g p‖ ≤ B) :
    ∀ p : E3, ‖lap3 (fun q => f q * g q) p‖
      ≤ 27 * (∑ i ∈ Finset.range 7, ((Nat.choose 6 i : ℕ) : ℝ) * K * B)
        * (1 + ‖p‖) ^ (-7 : ℝ) := by
  intro p
  have hmul : ContDiff ℝ (⊤ : ℕ∞) (fun q => f q * g q) := hf.mul hg
  have h1 : ‖iteratedFDeriv ℝ 6 (fun q => f q * g q) p‖
      ≤ (∑ i ∈ Finset.range 7, ((Nat.choose 6 i : ℕ) : ℝ) * K * B) * (1 + ‖p‖) ^ (-7 : ℝ) := by
    have hleib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := f) (g := g) hf hg p (n := 6)
      (WithTop.coe_le_coe.mpr le_top)
    refine hleib.trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi6 : i ≤ 6 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hci : (0 : ℝ) ≤ ((Nat.choose 6 i : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcp : 0 ≤ (1 + ‖p‖) ^ (-7 : ℝ) :=
      le_of_lt (Real.rpow_pos_of_pos (by positivity) _)
    have hstep := mul_le_mul (mul_le_mul_of_nonneg_left (hfd i hi6 p) hci)
      (hgd (6 - i) (Nat.sub_le 6 i) p) (norm_nonneg _) (mul_nonneg hci (mul_nonneg hK hcp))
    calc ((Nat.choose 6 i : ℕ) : ℝ) * ‖iteratedFDeriv ℝ i f p‖ * ‖iteratedFDeriv ℝ (6 - i) g p‖
        ≤ ((Nat.choose 6 i : ℕ) : ℝ) * (K * (1 + ‖p‖) ^ (-7 : ℝ)) * B := hstep
      _ = ((Nat.choose 6 i : ℕ) : ℝ) * K * B * (1 + ‖p‖) ^ (-7 : ℝ) := by ring
  calc ‖lap3 (fun q => f q * g q) p‖
      ≤ 27 * ‖iteratedFDeriv ℝ 6 (fun q => f q * g q) p‖ := norm_lap3_apply_le _ hmul p
    _ ≤ 27 * ((∑ i ∈ Finset.range 7, ((Nat.choose 6 i : ℕ) : ℝ) * K * B)
          * (1 + ‖p‖) ^ (-7 : ℝ)) := by linarith
    _ = 27 * (∑ i ∈ Finset.range 7, ((Nat.choose 6 i : ℕ) : ℝ) * K * B)
          * (1 + ‖p‖) ^ (-7 : ℝ) := by ring

/-! ## 3. Pointwise convergence of `lap3` of the truncated function -/

/-- If `χ = 1` near `p`, then `lap3 (v · χ) p = lap3 v p`. -/
lemma lap3_mul_eq_of_eventuallyEq_one {v χ : E3 → ℂ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {p : E3} (h : χ =ᶠ[𝓝 p] (fun _ => 1)) :
    lap3 (fun q => v q * χ q) p = lap3 v p := by
  have hEq : (fun q => v q * χ q) =ᶠ[𝓝 p] v := by
    filter_upwards [h] with q hq
    rw [hq, mul_one]
  have h6 := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hEq 6).eq_of_nhds
  have h6' : ∀ a b c : Fin 3,
      iteratedFDeriv ℝ (lap3List a b c).length (fun q => v q * χ q) p
        = iteratedFDeriv ℝ (lap3List a b c).length v p := by
    intro a b c
    rw [length_lap3List]
    exact h6
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun q => v q * χ q) := hv.mul hχ
  have hd : ∀ a b c : Fin 3, dIter (fun q => v q * χ q) (lap3List a b c) p
      = dIter v (lap3List a b c) p := by
    intro a b c
    rw [dIter_eq_iteratedFDeriv _ hsm (lap3List a b c) p,
      dIter_eq_iteratedFDeriv _ hv (lap3List a b c) p, h6' a b c]
  simp only [lap3, hd]

/-! ## 4. The two delegated pieces

The decay of the *full* iterated derivatives of `v` from the decay of its directional derivatives is
`Work.BoseBoxFock.LatSym.iteratedFDeriv_le_of_dIter_decay`
(`Submission/Work/BoseBoxFock/LatSym/iteratedFDeriv_le_of_dIter_decay.lean`), and the uniform bound
on the derivatives of the truncating bumps is `Work.BoseBoxFock.LatSym.quadCut_iteratedFDeriv_le`
(`Submission/Work/BoseBoxFock/LatSym/quadCut_iteratedFDeriv_le.lean`). -/

/-! ## 5. The main theorem -/

theorem integral_mul_lap3_eq_of_quad {σ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hσ : ContDiff ℝ (⊤ : ℕ∞) σ)
    (hσg : ∃ A : ℝ, ∀ p : EuclideanSpace ℝ (Fin 3), |σ p| ≤ A * (1 + ‖p‖) ^ 2)
    (hσ6 : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) => ‖iteratedFDeriv ℝ 6 σ p‖))
    {v : EuclideanSpace ℝ (Fin 3) → ℂ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvdec : ∀ L : List (EuclideanSpace ℝ (Fin 3)), L.length ≤ 6 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ p : EuclideanSpace ℝ (Fin 3),
        ‖Work.BoseBoxFock.dIter v L p‖ ≤ C * (1 + ‖p‖) ^ (-7 : ℝ)) :
    (∫ p : EuclideanSpace ℝ (Fin 3), (σ p : ℂ) * Work.BoseBoxFock.lap3 v p)
      = ∫ p : EuclideanSpace ℝ (Fin 3),
          Work.BoseBoxFock.lap3 (fun q : EuclideanSpace ℝ (Fin 3) => (σ q : ℂ)) p * v p := by
  obtain ⟨A, hA⟩ := hσg
  obtain ⟨Cv, hCv0, hCv⟩ := hvdec [] (by simp)
  obtain ⟨Kv, hKv0, hKv⟩ := iteratedFDeriv_le_of_dIter_decay hv hvdec
  obtain ⟨Mk, hMk0, hMk⟩ := quadCut_iteratedFDeriv_le
  have hσc : ContDiff ℝ (⊤ : ℕ∞) (fun p : E3 => (σ p : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hσ
  set Mb : ℝ := ∑ k ∈ Finset.range 7, Mk k with hMbdef
  have hMb0 : 0 ≤ Mb := Finset.sum_nonneg (fun k _ => hMk0 k)
  have hMble : ∀ k : ℕ, k ≤ 6 → Mk k ≤ Mb := by
    intro k hk
    rw [hMbdef]
    exact Finset.single_le_sum (fun j _ => hMk0 j)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  have hKb0 : 0 ≤ ∑ i ∈ Finset.range 7, ((Nat.choose 6 i : ℕ) : ℝ) * Kv * Mb :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hKv0) hMb0)
  -- the two dominating functions
  set bL : E3 → ℝ := fun p => |A| * 27 * (∑ i ∈ Finset.range 7, ((Nat.choose 6 i : ℕ) : ℝ) * Kv
      * Mb) * (1 + ‖p‖) ^ (-5 : ℝ) with hbLdef
  set bR : E3 → ℝ := fun p => 27 * Cv * ‖iteratedFDeriv ℝ 6 σ p‖ with hbRdef
  have hbLint : Integrable bL := by
    have h0 : Integrable (fun p : E3 => (1 + ‖p‖) ^ (-(5 : ℝ))) :=
      integrable_one_add_norm (E := E3) (μ := volume) (r := 5)
        (by rw [finrank_euclideanSpace_fin]; norm_num)
    have h1 : Integrable (fun p : E3 =>
        (|A| * 27 * (∑ i ∈ Finset.range 7, ((Nat.choose 6 i : ℕ) : ℝ) * Kv * Mb))
          * (1 + ‖p‖) ^ (-(5 : ℝ))) := h0.const_mul _
    refine h1.congr (Filter.Eventually.of_forall (fun p => ?_))
    simp only [hbLdef]
  have hbRint : Integrable bR := by
    have h1 : Integrable (fun p : E3 => (27 * Cv) * ‖iteratedFDeriv ℝ 6 σ p‖) :=
      hσ6.const_mul _
    refine h1.congr (Filter.Eventually.of_forall (fun p => ?_))
    simp only [hbRdef]
  -- the pointwise bound on the left integrand
  have hLbound : ∀ (n : ℕ) (p : E3),
      ‖(σ p : ℂ) * lap3 (fun q => v q * quadCut n q) p‖ ≤ bL p := by
    intro n p
    have hpl := norm_lap3_mul_le hv (quadCut_contDiff n) hKv0 hMb0 hKv
      (fun k hk q => (hMk k n q).trans (hMble k hk)) p
    have hsig : ‖(σ p : ℂ)‖ ≤ |A| * (1 + ‖p‖) ^ 2 := by
      rw [norm_ofReal_eq_abs]
      exact (hA p).trans (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity))
    calc ‖(σ p : ℂ) * lap3 (fun q => v q * quadCut n q) p‖
        = ‖(σ p : ℂ)‖ * ‖lap3 (fun q => v q * quadCut n q) p‖ := norm_mul _ _
      _ ≤ (|A| * (1 + ‖p‖) ^ 2) * (27 * (∑ i ∈ Finset.range 7, ((Nat.choose 6 i : ℕ) : ℝ) * Kv
            * Mb) * (1 + ‖p‖) ^ (-7 : ℝ)) :=
          mul_le_mul hsig hpl (norm_nonneg _) (by positivity)
      _ = |A| * 27 * (∑ i ∈ Finset.range 7, ((Nat.choose 6 i : ℕ) : ℝ) * Kv * Mb)
            * ((1 + ‖p‖) ^ (2 : ℕ) * (1 + ‖p‖) ^ (-7 : ℝ)) := by ring
      _ = |A| * 27 * (∑ i ∈ Finset.range 7, ((Nat.choose 6 i : ℕ) : ℝ) * Kv * Mb)
            * (1 + ‖p‖) ^ (-5 : ℝ) := by
          rw [sq_mul_rpow_neg_seven _ (by positivity)]
      _ = bL p := by rw [hbLdef]
  -- the pointwise bound on the right integrand
  have hRbound : ∀ (n : ℕ) (p : E3),
      ‖lap3 (fun q => (σ q : ℂ)) p * (v p * quadCut n p)‖ ≤ bR p := by
    intro n p
    have hpl : ‖lap3 (fun q => (σ q : ℂ)) p‖ ≤ 27 * ‖iteratedFDeriv ℝ 6 σ p‖ :=
      (norm_lap3_apply_le _ hσc p).trans
        (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_ofReal_comp_le hσ 6 p) (by norm_num))
    have hv1 : ‖v p‖ ≤ Cv := by
      refine (hCv p).trans ?_
      calc Cv * (1 + ‖p‖) ^ (-7 : ℝ) ≤ Cv * 1 :=
            mul_le_mul_of_nonneg_left
              (rpow_neg_seven_le_one (by have h := norm_nonneg p; linarith)) hCv0
        _ = Cv := mul_one Cv
    calc ‖lap3 (fun q => (σ q : ℂ)) p * (v p * quadCut n p)‖
        = ‖lap3 (fun q => (σ q : ℂ)) p‖ * ‖(v p * quadCut n p)‖ := norm_mul _ _
      _ ≤ (27 * ‖iteratedFDeriv ℝ 6 σ p‖) * (Cv * 1) := by
          refine mul_le_mul hpl ?_ (norm_nonneg _) (by positivity)
          calc ‖v p * quadCut n p‖ = ‖v p‖ * ‖quadCut n p‖ := norm_mul _ _
            _ ≤ Cv * 1 := mul_le_mul hv1 (norm_quadCut_le_one n p) (norm_nonneg _) hCv0
      _ = bR p := by rw [hbRdef]; ring
  -- the pointwise convergence of the left integrand
  have hLlim : ∀ᵐ p ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))),
      Tendsto (fun n : ℕ => (σ p : ℂ) * lap3 (fun q => v q * quadCut n q) p) atTop
        (𝓝 ((σ p : ℂ) * lap3 v p)) := by
    refine Filter.Eventually.of_forall (fun p => ?_)
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_norm_lt_succ_nat p] with n hn
    rw [lap3_mul_eq_of_eventuallyEq_one hv (quadCut_contDiff n)
      (quadCut_eventuallyEq_one n hn)]
  -- the pointwise convergence of the right integrand
  have hRlim : ∀ᵐ p ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))),
      Tendsto (fun n : ℕ => lap3 (fun q => (σ q : ℂ)) p * (v p * quadCut n p)) atTop
        (𝓝 (lap3 (fun q => (σ q : ℂ)) p * v p)) := by
    refine Filter.Eventually.of_forall (fun p => ?_)
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_norm_lt_succ_nat p] with n hn
    rw [quadCut_apply, quadCutR_eq_one_of_norm_le (le_of_lt hn), Complex.ofReal_one, mul_one]
  -- dominated convergence, left
  have hLtend : Tendsto
      (fun n : ℕ => ∫ p : E3, (σ p : ℂ) * lap3 (fun q => v q * quadCut n q) p) atTop
      (𝓝 (∫ p : E3, (σ p : ℂ) * lap3 v p)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence bL (fun n => ?_)
      hbLint (fun n => Filter.Eventually.of_forall (hLbound n)) hLlim
    exact ((Complex.continuous_ofReal.comp hσ.continuous).mul
      (continuous_lap3 (hv.mul (quadCut_contDiff n)))).aestronglyMeasurable
  -- dominated convergence, right
  have hRtend : Tendsto
      (fun n : ℕ => ∫ p : E3, lap3 (fun q => (σ q : ℂ)) p * (v p * quadCut n p)) atTop
      (𝓝 (∫ p : E3, lap3 (fun q => (σ q : ℂ)) p * v p)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence bR (fun n => ?_)
      hbRint (fun n => Filter.Eventually.of_forall (hRbound n)) hRlim
    exact ((continuous_lap3 hσc).mul (hv.continuous.mul (quadCut_contDiff n).continuous))
      |>.aestronglyMeasurable
  -- the integration by parts for each `n`
  have hkey : ∀ n : ℕ, (∫ p : E3, (σ p : ℂ) * lap3 (fun q => v q * quadCut n q) p)
      = ∫ p : E3, lap3 (fun q => (σ q : ℂ)) p * (v p * quadCut n p) := by
    intro n
    exact Work.BoseBoxFock.lap3_ibp (f := fun p : E3 => (σ p : ℂ))
      (g := fun p : E3 => v p * quadCut n p) hσc (hv.mul (quadCut_contDiff n))
      (quadCut_hasCompactSupport n).mul_left
  have hRtend' : Tendsto
      (fun n : ℕ => ∫ p : E3, (σ p : ℂ) * lap3 (fun q => v q * quadCut n q) p) atTop
      (𝓝 (∫ p : E3, lap3 (fun q => (σ q : ℂ)) p * v p)) :=
    hRtend.congr' (Filter.Eventually.of_forall (fun n => (hkey n).symm))
  exact tendsto_nhds_unique hLtend hRtend'

end Work.BoseBoxFock.LatSym
