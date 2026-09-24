import Mathlib
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.refsum_law
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.uniform_of_exp
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.exp_integral_neg
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.moment_cSum
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.summable_cY_ae
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.cY_ae_selfsimilar
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.joint_law_head_tail
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.gamma_log_limit
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.ode_solve
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.cNu_Iic_of_selfsimilar
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.inv_eq_exp_neg_gamma

set_option linter.style.haveILetI false

/-!
# The CDF of the reference sum on the canonical space

`canonM (cSet θ) = θ · e^{-γ}` for `0 < θ ≤ 1`, together with the transfer of the law of
`Σ_{k ≥ 1} e^{-S_k}` to an arbitrary iid standard-exponential sequence.
-/

namespace Work.ChenPlan.LinearSieve.Selberg.Alt
open MeasureTheory
open scoped ENNReal

lemma measurableSet_cSet (θ : ℝ) : MeasurableSet (cSet θ) :=
  measurable_cY measurableSet_Iio

lemma measurable_pair_head_tail : Measurable (fun x : ℕ → ℝ => (x 0, cshift x)) :=
  Measurable.prodMk (by simpa using measurable_pi_apply 0) measurable_cshift

theorem cNu_selfsimilar : cNu = (cUnif.prod cNu).map (fun p : ℝ × ℝ => p.1 * (1 + p.2)) := by
  have hexp : Measurable (fun t : ℝ => Real.exp (-t)) := Real.measurable_exp.comp measurable_neg
  have hmap : Measurable (Prod.map (fun t : ℝ => Real.exp (-t)) cY) :=
    hexp.prodMap measurable_cY
  have hpair : Measurable (fun x : ℕ → ℝ => (x 0, cshift x)) := measurable_pair_head_tail
  have hcomp : Measurable ((Prod.map (fun t : ℝ => Real.exp (-t)) cY)
      ∘ (fun x : ℕ → ℝ => (x 0, cshift x))) := hmap.comp hpair
  have hstep1 : canonM.map ((Prod.map (fun t : ℝ => Real.exp (-t)) cY)
      ∘ (fun x : ℕ → ℝ => (x 0, cshift x))) = cUnif.prod cNu := by
    have hmm := Measure.map_map (μ := canonM)
      (f := fun x : ℕ → ℝ => (x 0, cshift x))
      (g := Prod.map (fun t : ℝ => Real.exp (-t)) cY) hmap hpair
    rw [← hmm, joint_law_head_tail]
    exact (Measure.map_prod_map (f := fun t : ℝ => Real.exp (-t)) (g := cY)
      expLaw canonM hexp measurable_cY).symm
  have h2 : canonM.map cY
      = canonM.map (fun x : ℕ → ℝ => Real.exp (-(x 0)) * (1 + cY (cshift x))) :=
    Measure.map_congr (cY_ae_selfsimilar summable_cY_ae)
  have h3 : canonM.map (fun x : ℕ → ℝ => Real.exp (-(x 0)) * (1 + cY (cshift x)))
      = (canonM.map ((Prod.map (fun t : ℝ => Real.exp (-t)) cY)
            ∘ (fun x : ℕ → ℝ => (x 0, cshift x)))).map
          (fun q : ℝ × ℝ => q.1 * (1 + q.2)) := by
    have hg : Measurable (fun q : ℝ × ℝ => q.1 * (1 + q.2)) := by fun_prop
    have hmm := Measure.map_map (μ := canonM)
      (f := (Prod.map (fun t : ℝ => Real.exp (-t)) cY)
        ∘ (fun x : ℕ → ℝ => (x 0, cshift x)))
      (g := fun q : ℝ × ℝ => q.1 * (1 + q.2)) hg hcomp
    exact hmm.symm
  calc cNu = canonM.map cY := rfl
    _ = canonM.map (fun x : ℕ → ℝ => Real.exp (-(x 0)) * (1 + cY (cshift x))) := h2
    _ = (canonM.map ((Prod.map (fun t : ℝ => Real.exp (-t)) cY)
            ∘ (fun x : ℕ → ℝ => (x 0, cshift x)))).map
          (fun q : ℝ × ℝ => q.1 * (1 + q.2)) := h3
    _ = (cUnif.prod cNu).map (fun q : ℝ × ℝ => q.1 * (1 + q.2)) := by rw [hstep1]

-- ============ atoms ============

lemma cUnif_singleton_eq_zero (hcUnif : cUnif = MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) 1))
    (a : ℝ) : cUnif {a} = 0 := by
  rw [hcUnif, Measure.restrict_apply (measurableSet_singleton a)]
  exact le_antisymm (by
    calc MeasureTheory.volume ({a} ∩ Set.Ioo (0:ℝ) 1)
        ≤ MeasureTheory.volume ({a} : Set ℝ) := measure_mono Set.inter_subset_left
      _ = 0 := Real.volume_singleton) bot_le
lemma cUnif_subsingleton_eq_zero (hcUnif : cUnif = MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) 1))
    {s : Set ℝ} (hs : s.Subsingleton) : cUnif s = 0 := by
  rcases hs.eq_empty_or_singleton with h | ⟨a, rfl⟩
  · rw [h]; simp
  · exact cUnif_singleton_eq_zero hcUnif a

lemma cNu_singleton_eq_zero (hself : cNu = (cUnif.prod cNu).map (fun p : ℝ × ℝ => p.1 * (1 + p.2)))
    (hcUnif : cUnif = MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) 1))
    {t : ℝ} (ht : t ≠ 0) : cNu {t} = 0 := by
  have hf : Measurable (fun p : ℝ × ℝ => p.1 * (1 + p.2)) := by fun_prop
  have hmeas : MeasurableSet ((fun p : ℝ × ℝ => p.1 * (1 + p.2)) ⁻¹' ({t} : Set ℝ)) :=
    hf (measurableSet_singleton t)
  have h1 : cNu {t} = (cUnif.prod cNu) ((fun p : ℝ × ℝ => p.1 * (1 + p.2)) ⁻¹' {t}) := by
    conv_lhs => rw [hself]
    exact Measure.map_apply hf (measurableSet_singleton t)
  haveI hcNuProb : IsProbabilityMeasure cNu :=
    (Measure.isProbabilityMeasure_map_iff (μ := canonM) (f := cY) measurable_cY.aemeasurable).mpr inferInstance
  haveI hcUnifProb : IsProbabilityMeasure cUnif :=
    (Measure.isProbabilityMeasure_map_iff (μ := expLaw) (f := fun t : ℝ => Real.exp (-t))
      (Real.measurable_exp.comp measurable_neg).aemeasurable).mpr inferInstance
  rw [h1, Measure.prod_apply_symm hmeas]
  have hzero : ∀ z : ℝ,
      cUnif ((fun x : ℝ => (x, z)) ⁻¹' ((fun p : ℝ × ℝ => p.1 * (1 + p.2)) ⁻¹' {t})) = 0 := by
    intro z
    have hset : (fun x : ℝ => (x, z)) ⁻¹' ((fun p : ℝ × ℝ => p.1 * (1 + p.2)) ⁻¹' {t})
        = {u : ℝ | u * (1+z) = t} := rfl
    rw [hset]
    apply cUnif_subsingleton_eq_zero hcUnif
    intro u hu v hv
    have hzu : (1+z) ≠ 0 := by
      intro hz
      exact ht (by rw [← hu, hz, mul_zero])
    have h2 : u * (1+z) = v * (1+z) := by rw [hu, hv]
    exact mul_right_cancel₀ hzu h2
  simp_rw [hzero]
  simp

-- ============ transfer ============

theorem isStdExp_map_eq_expLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hmeas : AEMeasurable X P) (hlaw : IsStdExp X P) :
    P.map X = expLaw := by
  refine Measure.ext_of_Iic _ _ fun a => ?_
  rw [Measure.map_apply_of_aemeasurable hmeas measurableSet_Iic]
  change P {ω | X ω ≤ a} = expLaw (Set.Iic a)
  rw [hlaw a, ← ProbabilityTheory.ofReal_cdf expLaw a]
  have hcdf : (ProbabilityTheory.cdf expLaw : ℝ → ℝ) a
      = if 0 ≤ a then 1 - Real.exp (-a) else 0 := by
    simpa [expLaw] using ProbabilityTheory.cdf_expMeasure_eq (r := 1) one_pos a
  by_cases h : 0 ≤ a
  · rw [hcdf, if_pos h]
  · have hc : (ProbabilityTheory.cdf expLaw : ℝ → ℝ) a = 0 := by rw [hcdf, if_neg h]
    have hle : 1 - Real.exp (-a) ≤ 0 := by
      have : 1 ≤ Real.exp (-a) := Real.one_le_exp (by linarith)
      linarith
    rw [hc, ENNReal.ofReal_of_nonpos hle, ENNReal.ofReal_zero]

theorem map_seq_eq_canonM {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (E : ℕ → Ω → ℝ) (hEmeas : ∀ i, AEMeasurable (E i) P)
    (hElaw : ∀ i, IsStdExp (E i) P) (hindep : ProbabilityTheory.iIndepFun E P) :
    P.map (fun ω i => E i ω) = canonM := by
  rw [ProbabilityTheory.iIndepFun.map_fun_eq_infinitePi_map₀' hEmeas hindep]
  have : (fun i => P.map (E i)) = fun _ : ℕ => expLaw :=
    funext fun i => isStdExp_map_eq_expLaw P (hEmeas i) (hElaw i)
  rw [this]
  rfl

-- ============ final assembly ============

theorem cdf_canonM (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    canonM (cSet θ) = ENNReal.ofReal (θ * Real.exp (- Real.eulerMascheroniConstant)) := by
  have hset : cSet θ = cY ⁻¹' (Set.Iio θ) := rfl
  have hmap : cNu (Set.Iio θ) = canonM (cSet θ) := by
    rw [cNu, Measure.map_apply measurable_cY measurableSet_Iio, hset]
  rw [← hmap]
  have hIic := cNu_Iic_of_selfsimilar cNu_selfsimilar uniform_of_exp θ hθ0 hθ1
  have hatom := cNu_singleton_eq_zero cNu_selfsimilar uniform_of_exp (ne_of_gt hθ0)
  have hIio : cNu (Set.Iio θ) = cNu (Set.Iic θ) := by
    have hdisj : Disjoint (Set.Iio θ) ({θ} : Set ℝ) := by
      rw [Set.disjoint_left]
      intro a ha hb
      exact absurd (hb ▸ ha) (lt_irrefl a)
    have hunion : Set.Iio θ ∪ {θ} = Set.Iic θ := by
      ext a
      simp only [Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff, Set.mem_Iic]
      exact ⟨fun h => h.elim le_of_lt le_of_eq, fun h => le_iff_lt_or_eq.mp h⟩
    rw [← hunion, measure_union hdisj (measurableSet_singleton θ), hatom, add_zero]
  rw [hIio, hIic, inv_eq_exp_neg_gamma cNu_selfsimilar uniform_of_exp]

end Work.ChenPlan.LinearSieve.Selberg.Alt
