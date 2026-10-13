import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.LocUnif.D5.l1_cauchy_pz
import Submission.Work.FTS.StrongEps.LocUnif.D5.window_bound
import Submission.Work.FTS.StrongEps.LocUnif.D5.slice_pointwise_le
import Submission.Work.FTS.StrongEps.LocUnif.D5.box_integral_eq
import Submission.Work.FTS.StrongEps.LocUnif.D5.intervalIntegral_swap
import Submission.Work.FTS.StrongEps.LocUnif.D5.continuousOn_intervalIntegral_shift
import Submission.Work.FTS.StrongEps.LocUnif.D5.integrableOn_slice_integrals

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif.D5

/-
Box-local version of `Work.FTS.StrongEps.LocUnif.D5.l1_cauchy_pz`: the smoothness hypothesis
`SmoothOpen (L n)` (which forces every point of the box to lie in the open quadrant
`(0,∞) × (0,π/2)`, hence demands `d < π/2`) is replaced by exactly the facts its proof uses:
the two one-variable derivative relations on the box and the continuity of `∂_z L n` and
`∂_z² L n` on the box.  The proof is a verbatim copy of `l1_cauchy_pz`'s proof (same file
`Submission/Work/FTS/StrongEps/LocUnif/D5/l1_cauchy_pz.lean`, with the helper `l1_box_le`
reproduced or imported), with `hsm`-derived facts replaced by the new hypotheses and all
`Q0`-membership bookkeeping deleted.
-/
theorem l1_cauchy_pz_gen {a b a₀ b₀ c d M : ℝ} (ha₀ : 0 < a₀) (ha₀a : a₀ < a) (hab : a < b)
    (hbb₀ : b < b₀) (hcd : c < d) (hM : 0 ≤ M)
    {L : ℕ → ℝ → ℝ → ℝ} {Llim : ℝ → ℝ → ℝ}
    (hconv : TendstoUniformlyOn (fun n (p : ℝ × ℝ) => L n p.1 p.2) (fun p => Llim p.1 p.2)
      Filter.atTop (Set.Icc a₀ b₀ ×ˢ Set.Icc c d))
    (hder : ∀ n : ℕ, ∀ θ ∈ Set.Icc c d, ∀ z ∈ Set.Icc a₀ b₀,
      HasDerivAt (fun z' => L n z' θ) (Work.Spaces.pz (L n) z θ) z)
    (hder2 : ∀ n : ℕ, ∀ θ ∈ Set.Icc c d, ∀ z ∈ Set.Icc a₀ b₀,
      HasDerivAt (fun z' => Work.Spaces.pz (L n) z' θ)
        (Work.Spaces.pz (Work.Spaces.pz (L n)) z θ) z)
    (hcont : ∀ n : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz (L n) p.1 p.2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d))
    (hcont2 : ∀ n : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d))
    (h1 : ∀ n : ℕ, ∫⁻ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pz (L n) p.1 p.2) ^ 2) ≤ ENNReal.ofReal M)
    (h2 : ∀ n : ℕ, ∫⁻ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2)
          ≤ ENNReal.ofReal M) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal |Work.Spaces.pz (L n) p.1 p.2 - Work.Spaces.pz (L m) p.1 p.2|
          ≤ ENNReal.ofReal ε := by
  intro ε hε
  have ha_pos : 0 < a := lt_trans ha₀ ha₀a
  have hdc : 0 < d - c := by linarith
  -- constants
  set c₁ : ℝ := 2 * (b - a) * (d - c) with hc₁def
  have hc₁pos : 0 < c₁ := by rw [hc₁def]; positivity
  set M₄ : ℝ := 4 * M with hM₄def
  have hM₄nn : 0 ≤ M₄ := by rw [hM₄def]; linarith
  set K₂ : ℝ := M₄ + (b₀ - a) * (d - c) / 4 with hK₂def
  have hK₂nn : 0 ≤ K₂ := by
    rw [hK₂def]
    have h : 0 ≤ (b₀ - a) * (d - c) := by nlinarith [hM₄nn]
    linarith
  set hh : ℝ := min ((b₀ - b) / 2) (ε / (2 * (K₂ + 1))) with hhhdef
  have hhhpos : 0 < hh := by
    rw [hhhdef]
    exact lt_min (by linarith) (by positivity)
  have hhhle₁ : hh ≤ (b₀ - b) / 2 := by rw [hhhdef]; exact min_le_left _ _
  have hhhle₂ : hh ≤ ε / (2 * (K₂ + 1)) := by rw [hhhdef]; exact min_le_right _ _
  have hbhh : b + hh ≤ b₀ := by linarith
  have hK₂hh : hh * K₂ ≤ ε / 2 := by
    have h1 : K₂ ≤ K₂ + 1 := by linarith
    have h3 : hh * K₂ ≤ hh * (K₂ + 1) := mul_le_mul_of_nonneg_left h1 hhhpos.le
    have h4 : hh * (K₂ + 1) ≤ (ε / (2 * (K₂ + 1))) * (K₂ + 1) :=
      mul_le_mul_of_nonneg_right hhhle₂ (by linarith)
    have h5 : (ε / (2 * (K₂ + 1))) * (K₂ + 1) = ε / 2 := by
      field_simp
    linarith
  set δ : ℝ := ε * hh / (2 * c₁) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδeq : c₁ * δ / hh = ε / 2 := by
    have hc₁ne : c₁ ≠ 0 := ne_of_gt hc₁pos
    have hhne : hh ≠ 0 := ne_of_gt hhhpos
    rw [hδdef]
    field_simp
  -- the uniform-convergence threshold
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ p ∈ Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
      dist (Llim p.1 p.2) (L n p.1 p.2) < δ / 2 := by
    have h := (Metric.tendstoUniformlyOn_iff.mp hconv) (δ / 2) (by linarith)
    rw [Filter.eventually_atTop] at h
    obtain ⟨N, hN⟩ := h
    exact ⟨N, fun n hn => hN n hn⟩
  refine ⟨N, fun n m hn hm => ?_⟩
  -- the box inclusions
  have hsubbox : Set.Icc a (b + hh) ×ˢ Set.Icc c d ⊆ Set.Icc a₀ b₀ ×ˢ Set.Icc c d :=
    Set.prod_mono (Set.Icc_subset_Icc ha₀a.le hbhh) Subset.rfl
  -- the pointwise bound on the difference
  have hPbound : ∀ z ∈ Set.Icc a (b + hh), ∀ θ ∈ Set.Icc c d,
      |L n z θ - L m z θ| ≤ δ := by
    intro z hz θ hθ
    have hz' : (z, θ) ∈ Set.Icc a₀ b₀ ×ˢ Set.Icc c d :=
      ⟨⟨le_trans ha₀a.le hz.1, le_trans hz.2 hbhh⟩, hθ⟩
    have h1 := hN n hn (z, θ) hz'
    have h2 := hN m hm (z, θ) hz'
    have h3 : dist (L n z θ) (L m z θ) < δ := by
      calc dist (L n z θ) (L m z θ)
          ≤ dist (L n z θ) (Llim z θ) + dist (Llim z θ) (L m z θ) := dist_triangle _ _ _
        _ = dist (Llim z θ) (L n z θ) + dist (Llim z θ) (L m z θ) := by
            rw [dist_comm (L n z θ) (Llim z θ)]
        _ < δ / 2 + δ / 2 := add_lt_add h1 h2
        _ = δ := by ring
    rw [Real.dist_eq] at h3
    exact le_of_lt h3
  -- the derivative relations, from `hder` / `hder2`
  have hGderiv : ∀ θ ∈ Set.Icc c d, ∀ z ∈ Set.Icc a (b + hh),
      HasDerivAt (fun z' => L n z' θ - L m z' θ)
        (Work.Spaces.pz (L n) z θ - Work.Spaces.pz (L m) z θ) z := by
    intro θ hθ z hz
    have hz' : z ∈ Set.Icc a₀ b₀ :=
      ⟨le_trans ha₀a.le hz.1, le_trans hz.2 hbhh⟩
    exact (hder n θ hθ z hz').sub (hder m θ hθ z hz')
  have hG'deriv : ∀ θ ∈ Set.Icc c d, ∀ z ∈ Set.Icc a (b + hh),
      HasDerivAt (fun z' => Work.Spaces.pz (L n) z' θ - Work.Spaces.pz (L m) z' θ)
        (Work.Spaces.pz (Work.Spaces.pz (L n)) z θ
          - Work.Spaces.pz (Work.Spaces.pz (L m)) z θ) z := by
    intro θ hθ z hz
    have hz' : z ∈ Set.Icc a₀ b₀ :=
      ⟨le_trans ha₀a.le hz.1, le_trans hz.2 hbhh⟩
    exact (hder2 n θ hθ z hz').sub (hder2 m θ hθ z hz')
  -- joint continuity
  have hGcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pz (L n) p.1 p.2 - Work.Spaces.pz (L m) p.1 p.2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
    (hcont n).sub (hcont m)
  have hG'cont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2
        - Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
    (hcont2 n).sub (hcont2 m)
  -- the `L²` bound on the difference
  have hIntN : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) ((hcont2 n).pow 2)
  have hIntM : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) ((hcont2 m).pow 2)
  have hreN : ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2 ≤ M := by
    have h := h2 n
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntN
      (Filter.Eventually.of_forall fun p => sq_nonneg _)] at h
    exact (ENNReal.ofReal_le_ofReal_iff hM).mp h
  have hreM : ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2 ≤ M := by
    have h := h2 m
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntM
      (Filter.Eventually.of_forall fun p => sq_nonneg _)] at h
    exact (ENNReal.ofReal_le_ofReal_iff hM).mp h
  have hcomb : ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2
        - Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2 ≤ M₄ := by
    have hmaj : MeasureTheory.IntegrableOn
        (fun p : ℝ × ℝ => 2 * (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2
          + 2 * (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2)
        (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
      (hIntN.const_mul 2).add (hIntM.const_mul 2)
    have hpt : ∀ᵐ p ∂(volume.restrict (Set.Icc a₀ b₀ ×ˢ Set.Icc c d)),
        (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2
          - Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2
        ≤ 2 * (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2
          + 2 * (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2 :=
      Filter.Eventually.of_forall fun p => by nlinarith [sq_nonneg (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2 + Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2)]
    have hstep : ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
          (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2
            - Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2
        ≤ ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
          (2 * (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2
            + 2 * (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2) :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun p => sq_nonneg _) hmaj hpt
    have hsplit : ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
          (2 * (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2
            + 2 * (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2)
        = 2 * (∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
            (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2)
          + 2 * (∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
            (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2) := by
      rw [MeasureTheory.integral_add (hIntN.const_mul 2) (hIntM.const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [hsplit] at hstep
    rw [hM₄def]
    linarith
  -- the engine
  have hmain := l1_box_le ha₀a.le (le_of_lt hab) hbhh hhhpos (le_of_lt hcd)
    hPbound hGderiv hG'deriv hGcont hG'cont hcomb
  have hreal : ∫ p in Set.Icc a b ×ˢ Set.Icc c d,
      |Work.Spaces.pz (L n) p.1 p.2 - Work.Spaces.pz (L m) p.1 p.2| ≤ ε := by
    have hK₂' : M₄ + (b - a + hh) * (d - c) / 4 ≤ K₂ := by
      rw [hK₂def]
      have hle : b - a + hh ≤ b₀ - a := by linarith
      have hmul : (b - a + hh) * (d - c) ≤ (b₀ - a) * (d - c) :=
        mul_le_mul_of_nonneg_right hle hdc.le
      have hdiv : (b - a + hh) * (d - c) / 4 ≤ (b₀ - a) * (d - c) / 4 :=
        div_le_div_of_nonneg_right hmul (by norm_num)
      linarith
    have hstep : hh * (M₄ + (b - a + hh) * (d - c) / 4) ≤ hh * K₂ :=
      mul_le_mul_of_nonneg_left hK₂' hhhpos.le
    have hstep' : hh * (M₄ + (b - a + hh) * (d - c) / 4) ≤ ε / 2 := le_trans hstep hK₂hh
    have h1 : 2 * (b - a) * (d - c) * δ / hh = c₁ * δ / hh := by rw [hc₁def]
    rw [h1] at hmain
    linarith [hmain, hstep', hδeq]
  -- convert the real bound into the lower integral
  have hIntabs : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => |Work.Spaces.pz (L n) p.1 p.2 - Work.Spaces.pz (L m) p.1 p.2|)
      (Set.Icc a b ×ˢ Set.Icc c d) := by
    have hsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Set.Icc a₀ b₀ ×ˢ Set.Icc c d :=
      Set.prod_mono (Set.Icc_subset_Icc ha₀a.le (le_of_lt hbb₀)) Subset.rfl
    exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      ((hGcont.mono hsub).abs)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntabs
    (Filter.Eventually.of_forall fun p => abs_nonneg _)]
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mpr hreal

end Work.FTS.StrongEps.LocUnif.D5
