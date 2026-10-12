import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.lap3_cutoff_eventuallyEq
import Submission.Work.BoseBoxFock.lap3_mul_le_of_cutoff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.lap3_ibp_of_decay` — integration by parts for `Δ³` against a decaying test
function

The compactly supported identity `lap3_ibp` (`∫ f · Δ³ g = ∫ (Δ³ f) · g` for `g` of class `C^∞`
with compact support) is extended here to test functions `g` that are merely *bounded* with
decaying derivatives: `f` is smooth with integrable `Δ³ f`, `g` is smooth and bounded, and
`p ↦ ‖f p‖ ‖D^k g p‖` is integrable for every `k ≤ 6`.

## Route

Choose a smooth cutoff family `θ` with `θ R = 1` on `B(0,R)`, `θ R = 0` off `B(0,2R)`, values in
`[0,1]`, and `‖D^k (θ R) x‖ ≤ C_k` uniformly in `R ≥ 1` (`cutoffHyp_exists`).  For each `R ≥ 1`,
`g_R := (θ R : ℂ) · g` is smooth with compact support, so `lap3_ibp` gives

    ∫ f · Δ³ g_R = ∫ (Δ³ f) · g_R .

Both sides converge as `R → ∞` by dominated convergence:

* the sequence `Δ³ g_R` is dominated by `27 Σ_{i≤6} binom(6,i) C_i ‖D^{6-i} g‖` (the Leibniz
  bound `lap3_mul_le_of_cutoff`), whose product with `‖f‖` is integrable by `hmom`;
* `Δ³ g_R → Δ³ g` pointwise, since `θ R ≡ 1` near any fixed point (`lap3_cutoff_eventuallyEq`);
* on the right-hand side the dominating function is `‖Δ³ f‖ · B`, integrable by `hfi` and
  boundedness of `g`, and `g_R → g` pointwise.

Equality of limits gives the claim.
-/

noncomputable section

open MeasureTheory Filter
open scoped Real BigOperators Topology

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `Δ³` of a smooth function is smooth. -/
lemma contDiff_lap3 {f : E3 → ℂ} (hf : ContDiff ℝ (⊤ : ENat) f) :
    ContDiff ℝ (⊤ : ENat) (lap3 f) := by
  rw [lap3_eq_sum]
  exact ContDiff.sum (fun t _ => contDiff_dIter hf (lap3List t.1 t.2.1 t.2.2))

/-- Composing a smooth real function with the isometric embedding `ℝ → ℂ` stays smooth. -/
lemma contDiff_ofReal_comp {θ : E3 → ℝ} (h : ContDiff ℝ (⊤ : ENat) θ) :
    ContDiff ℝ (⊤ : ENat) (fun y => ((θ y : ℝ) : ℂ)) := by
  have hcomp : (fun y : E3 => ((θ y : ℝ) : ℂ)) = ⇑Complex.ofRealCLM ∘ θ := rfl
  rw [hcomp]
  exact (Complex.ofRealCLM.contDiff (𝕜 := ℝ)).comp h

/-- Composing a compactly supported real function with the isometric embedding `ℝ → ℂ` stays
compactly supported. -/
lemma hasCompactSupport_ofReal_comp {θ : E3 → ℝ} (h : HasCompactSupport θ) :
    HasCompactSupport (fun y => ((θ y : ℝ) : ℂ)) := by
  have hcomp : (fun y : E3 => ((θ y : ℝ) : ℂ)) = ⇑Complex.ofRealCLM ∘ θ := rfl
  rw [hcomp]
  exact h.comp_left (g := ⇑Complex.ofRealCLM) (by simp)

/-- The norm of a real number embedded in `ℂ` is at most `1` when the number is in `[0,1]`. -/
lemma norm_ofReal_complex_le_one {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    ‖((r : ℝ) : ℂ)‖ ≤ 1 := by
  have hle : ‖Complex.ofRealLI r‖ ≤ 1 := by
    rw [Complex.ofRealLI.norm_map, Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  simpa using hle

theorem lap3_ibp_of_decay {f g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hf : ContDiff ℝ (⊤ : ENat) f)
    (hfi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => Work.BoseBoxFock.lap3 f p))
    (hg : ContDiff ℝ (⊤ : ENat) g)
    (hbdd : ∃ B : ℝ, 0 ≤ B ∧ ∀ p : EuclideanSpace ℝ (Fin 3), ‖g p‖ ≤ B)
    (hmom : ∀ k : ℕ, k ≤ 6 → MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        ‖f p‖ * ‖iteratedFDeriv ℝ k g p‖)) :
    ∫ p : EuclideanSpace ℝ (Fin 3), f p * Work.BoseBoxFock.lap3 g p
      = ∫ p : EuclideanSpace ℝ (Fin 3), Work.BoseBoxFock.lap3 f p * g p := by
  obtain ⟨θ, hθ⟩ := cutoffHyp_exists
  have hCexists : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ R, 1 ≤ R → ∀ x : E3,
      ‖iteratedFDeriv ℝ k (fun y => ((θ R y : ℝ) : ℂ)) x‖ ≤ C :=
    fun k => cutoff_deriv_bound_le hθ k
  choose C hC using hCexists
  obtain ⟨B, hB0, hB⟩ := hbdd
  -- the cutoff factor is smooth and compactly supported
  have hcut_contDiff : ∀ R, ContDiff ℝ (⊤ : ENat) (fun y : E3 => ((θ R y : ℝ) : ℂ)) :=
    fun R => contDiff_ofReal_comp (hθ.contDiff R)
  have hcut_cs : ∀ R, 0 < R → HasCompactSupport (fun y : E3 => ((θ R y : ℝ) : ℂ)) :=
    fun R hR => hasCompactSupport_ofReal_comp (hθ.compactSupport R hR)
  let gR : ℝ → E3 → ℂ := fun R y => ((θ R y : ℝ) : ℂ) * g y
  have hgR_eq : ∀ R, gR R = fun y : E3 => ((θ R y : ℝ) : ℂ) * g y := fun R => rfl
  have hgR_contDiff : ∀ R, ContDiff ℝ (⊤ : ENat) (gR R) := fun R => (hcut_contDiff R).mul hg
  have hgR_cs : ∀ R, 0 < R → HasCompactSupport (gR R) := fun R hR => (hcut_cs R hR).mul_right
  -- integrability of the two limiting integrands
  have hint_g : Integrable (fun p : E3 => lap3 f p * g p) := by
    refine Integrable.mono' (hfi.norm.mul_const B)
      (((contDiff_lap3 hf).continuous.mul hg.continuous).aestronglyMeasurable) ?_
    filter_upwards with p
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB p) (norm_nonneg _)
  have hint_f : Integrable (fun p : E3 => f p * lap3 g p) := by
    have hmaj6 : Integrable (fun p : E3 => 27 * (‖f p‖ * ‖iteratedFDeriv ℝ 6 g p‖)) :=
      (hmom 6 le_rfl).const_mul 27
    refine hmaj6.mono'
      ((hf.continuous.mul (contDiff_lap3 hg).continuous).aestronglyMeasurable) ?_
    filter_upwards with p
    rw [norm_mul]
    calc ‖f p‖ * ‖lap3 g p‖ ≤ ‖f p‖ * (27 * ‖iteratedFDeriv ℝ 6 g p‖) :=
          mul_le_mul_of_nonneg_left (norm_lap3_apply_le g hg p) (norm_nonneg _)
      _ = 27 * (‖f p‖ * ‖iteratedFDeriv ℝ 6 g p‖) := by ring
  -- the majorant of the left-hand sequence
  let boundL : E3 → ℝ := fun p => 27 * ∑ i ∈ Finset.range 7,
      ((6 : ℕ).choose i : ℝ) * C i * (‖f p‖ * ‖iteratedFDeriv ℝ (6 - i) g p‖)
  have hboundL_int : Integrable boundL := by
    refine (integrable_finsetSum _ (fun i hi => ?_)).const_mul 27
    have hi6 : 6 - i ≤ 6 := by
      have := Finset.mem_range.mp hi
      omega
    exact (hmom (6 - i) hi6).const_mul (((6 : ℕ).choose i : ℝ) * C i)
  have hrearr : ∀ p : E3, ‖f p‖ * (27 * ∑ i ∈ Finset.range 7,
        ((6 : ℕ).choose i : ℝ) * C i * ‖iteratedFDeriv ℝ (6 - i) g p‖) = boundL p := by
    intro p
    show ‖f p‖ * (27 * ∑ i ∈ Finset.range 7,
        ((6 : ℕ).choose i : ℝ) * C i * ‖iteratedFDeriv ℝ (6 - i) g p‖)
      = 27 * ∑ i ∈ Finset.range 7,
        ((6 : ℕ).choose i : ℝ) * C i * (‖f p‖ * ‖iteratedFDeriv ℝ (6 - i) g p‖)
    rw [← mul_assoc, mul_comm (‖f p‖) 27, mul_assoc, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)
  -- the left-hand convergence
  have hlimL : Tendsto (fun R : ℝ => ∫ p : E3, f p * lap3 (gR R) p) atTop
      (𝓝 (∫ p : E3, f p * lap3 g p)) := by
    refine tendsto_integral_filter_of_dominated_convergence boundL ?_ ?_ hboundL_int ?_
    · filter_upwards with R
      exact ((hf.continuous.mul (contDiff_lap3 (hgR_contDiff R)).continuous)).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
      filter_upwards with p
      have hb := lap3_mul_le_of_cutoff hθ hg (fun k _ R' hR' x => (hC k).2 R' hR' x) hR p
      rw [norm_mul]
      change ‖f p‖ * ‖lap3 (fun y : E3 => ((θ R y : ℝ) : ℂ) * g y) p‖ ≤ boundL p
      calc ‖f p‖ * ‖lap3 (fun y : E3 => ((θ R y : ℝ) : ℂ) * g y) p‖
          ≤ ‖f p‖ * (27 * ∑ i ∈ Finset.range 7,
              ((6 : ℕ).choose i : ℝ) * C i * ‖iteratedFDeriv ℝ (6 - i) g p‖) :=
            mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = boundL p := hrearr p
    · refine Filter.Eventually.of_forall (fun p => ?_)
      refine (tendsto_const_nhds (x := f p * lap3 g p)).congr' ?_
      filter_upwards [lap3_cutoff_eventuallyEq hθ hg p] with R hR
      have hstep : lap3 (gR R) p = lap3 g p := by
        rw [hgR_eq R]
        exact hR
      rw [hstep]
  -- the right-hand convergence
  have hlimR : Tendsto (fun R : ℝ => ∫ p : E3, lap3 f p * gR R p) atTop
      (𝓝 (∫ p : E3, lap3 f p * g p)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun p : E3 => ‖lap3 f p‖ * B)
      ?_ ?_ (hfi.norm.mul_const B) ?_
    · filter_upwards with R
      exact (((contDiff_lap3 hf).continuous).mul
        ((hcut_contDiff R).continuous.mul hg.continuous)).aestronglyMeasurable
    · filter_upwards with R
      filter_upwards with p
      have hcut1 : ‖((θ R p : ℝ) : ℂ)‖ ≤ 1 :=
        norm_ofReal_complex_le_one (hθ.nonneg R p) (hθ.le_one R p)
      change ‖lap3 f p * (((θ R p : ℝ) : ℂ) * g p)‖ ≤ ‖lap3 f p‖ * B
      rw [norm_mul, norm_mul]
      calc ‖lap3 f p‖ * (‖((θ R p : ℝ) : ℂ)‖ * ‖g p‖)
          ≤ ‖lap3 f p‖ * (1 * ‖g p‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcut1 (norm_nonneg _))
              (norm_nonneg _)
        _ ≤ ‖lap3 f p‖ * (1 * B) := mul_le_mul_of_nonneg_left
            (by simpa using hB p) (norm_nonneg _)
        _ = ‖lap3 f p‖ * B := by ring
    · refine Filter.Eventually.of_forall (fun p => ?_)
      refine (tendsto_const_nhds (x := lap3 f p * g p)).congr' ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop ‖p‖] with R hR hRp
      have h1 : ((θ R p : ℝ) : ℂ) = 1 := by
        rw [hθ.eq_one R (lt_of_lt_of_le zero_lt_one hR) p hRp, Complex.ofReal_one]
      change lap3 f p * g p = lap3 f p * (((θ R p : ℝ) : ℂ) * g p)
      rw [h1, one_mul]
  -- glue
  have hkey : ∀ R : ℝ, 1 ≤ R → (∫ p : E3, f p * lap3 (gR R) p)
      = (∫ p : E3, lap3 f p * gR R p) := fun R hR =>
    lap3_ibp hf (hgR_contDiff R) (hgR_cs R (lt_of_lt_of_le zero_lt_one hR))
  have hev : (fun R : ℝ => ∫ p : E3, f p * lap3 (gR R) p)
      =ᶠ[atTop] (fun R : ℝ => ∫ p : E3, lap3 f p * gR R p) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact hkey R hR
  exact tendsto_nhds_unique hlimL (hlimR.congr' hev.symm)

end Work.BoseBoxFock

end

