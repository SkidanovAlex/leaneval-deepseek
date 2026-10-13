import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology NNReal
open Filter Set Metric

namespace Work.FTS_EllLimOK.ProducerH.ThetaZero

/-- A function which is Lipschitz on the open interval `(a,b)` has a limit at `a` from the
right.  (This is the "cluster set at `a` is a single point" argument, phrased through Cauchy
filters and completeness of `ℝ`.) -/
private lemma exists_tendsto_nhdsGT_of_lipschitzOn {f : ℝ → ℝ} {a b : ℝ} {C : ℝ≥0}
    (hab : a < b) (hL : LipschitzOnWith C f (Ioo a b)) :
    ∃ L : ℝ, Tendsto f (𝓝[>] a) (𝓝 L) := by
  rw [← cauchy_map_iff_exists_tendsto]
  rw [Metric.cauchy_iff]
  refine ⟨inferInstance, ?_⟩
  intro ε hε
  set δ : ℝ := ε / (2 * ((C : ℝ) + 1)) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; exact div_pos hε (by positivity)
  have hCpos : (0 : ℝ) < (C : ℝ) + 1 := by positivity
  have hac : a < min b (a + δ) := lt_min hab (lt_add_of_pos_right a hδ)
  refine ⟨f '' Ioo a (min b (a + δ)), image_mem_map (Ioo_mem_nhdsGT hac), ?_⟩
  intro x hx y hy
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  have hpb : p ∈ Ioo a b := ⟨hp.1, lt_of_lt_of_le hp.2 (min_le_left _ _)⟩
  have hqb : q ∈ Ioo a b := ⟨hq.1, lt_of_lt_of_le hq.2 (min_le_left _ _)⟩
  have h1 : dist (f p) (f q) ≤ (C : ℝ) * dist p q := hL.dist_le_mul p hpb q hqb
  have h2 : dist p q ≤ δ := by
    rw [Real.dist_eq]
    have hlt : |p - q| < min b (a + δ) - a := by
      rw [abs_lt]
      constructor <;> linarith [hp.1, hp.2, hq.1, hq.2]
    have hle : min b (a + δ) - a ≤ δ := by linarith [min_le_right b (a + δ)]
    linarith
  have h3 : (C : ℝ) * dist p q ≤ (C : ℝ) * δ :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : (C : ℝ) * δ < ε := by
    have hδnn : 0 ≤ δ := le_of_lt hδ
    have h5 : (C : ℝ) * δ ≤ ((C : ℝ) + 1) * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hδnn
    have h6 : ((C : ℝ) + 1) * δ = ε / 2 := by
      rw [hδdef]; field_simp
    linarith
  linarith

/-- A function which is Lipschitz on the open interval `(a,b)` has a limit at `b` from the
left (the mirror image of the previous lemma). -/
private lemma exists_tendsto_nhdsLT_of_lipschitzOn {f : ℝ → ℝ} {a b : ℝ} {C : ℝ≥0}
    (hab : a < b) (hL : LipschitzOnWith C f (Ioo a b)) :
    ∃ R : ℝ, Tendsto f (𝓝[<] b) (𝓝 R) := by
  rw [← cauchy_map_iff_exists_tendsto]
  rw [Metric.cauchy_iff]
  refine ⟨inferInstance, ?_⟩
  intro ε hε
  set δ : ℝ := ε / (2 * ((C : ℝ) + 1)) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; exact div_pos hε (by positivity)
  have hCpos : (0 : ℝ) < (C : ℝ) + 1 := by positivity
  have hcb : max a (b - δ) < b := max_lt hab (by linarith)
  refine ⟨f '' Ioo (max a (b - δ)) b, image_mem_map (Ioo_mem_nhdsLT hcb), ?_⟩
  intro x hx y hy
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  have hpb : p ∈ Ioo a b := ⟨lt_of_le_of_lt (le_max_left _ _) hp.1, hp.2⟩
  have hqb : q ∈ Ioo a b := ⟨lt_of_le_of_lt (le_max_left _ _) hq.1, hq.2⟩
  have h1 : dist (f p) (f q) ≤ (C : ℝ) * dist p q := hL.dist_le_mul p hpb q hqb
  have h2 : dist p q ≤ δ := by
    rw [Real.dist_eq]
    have hlt : |p - q| < b - max a (b - δ) := by
      rw [abs_lt]
      constructor <;> linarith [hp.1, hp.2, hq.1, hq.2]
    have hle : b - max a (b - δ) ≤ δ := by linarith [le_max_right a (b - δ)]
    linarith
  have h3 : (C : ℝ) * dist p q ≤ (C : ℝ) * δ :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : (C : ℝ) * δ < ε := by
    have hδnn : 0 ≤ δ := le_of_lt hδ
    have h5 : (C : ℝ) * δ ≤ ((C : ℝ) + 1) * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hδnn
    have h6 : ((C : ℝ) + 1) * δ = ε / 2 := by
      rw [hδdef]; field_simp
    linarith
  linarith

theorem tendsto_of_deriv_bounded {f : ℝ → ℝ} {a b M : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 1 f (Set.Ioo a b)) (hM : ∀ x ∈ Set.Ioo a b, |deriv f x| ≤ M) :
    (∃ L : ℝ, Filter.Tendsto f (nhdsWithin a (Set.Ioi a)) (nhds L)) ∧
      (∃ R : ℝ, Filter.Tendsto f (nhdsWithin b (Set.Iio b)) (nhds R)) := by
  have hL : LipschitzOnWith (⟨max M 0, le_max_right M 0⟩ : ℝ≥0) f (Ioo a b) := by
    refine Convex.lipschitzOnWith_of_nnnorm_deriv_le (fun x hx => ?_) (fun x hx => ?_)
      (convex_Ioo a b)
    · exact (hf.differentiableOn_one x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
    · have hm : |deriv f x| ≤ max M 0 := le_trans (hM x hx) (le_max_left M 0)
      exact_mod_cast hm
  exact ⟨exists_tendsto_nhdsGT_of_lipschitzOn hab hL,
    exists_tendsto_nhdsLT_of_lipschitzOn hab hL⟩

end Work.FTS_EllLimOK.ProducerH.ThetaZero
