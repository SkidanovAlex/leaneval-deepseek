import Submission.MinkBox
import Submission.MinkLower
import Submission.Contracts
import Submission.EnergyHalf
import Submission.SerreExample
import Submission.SupportConcentration
import Submission.SerreHolder
import Submission.MuAtomFree
import Submission.WeightedNorm
import Submission.WnormToolkit
import Submission.PotentialContinuity
import Submission.LogProductMeasure
import Submission.ArithmeticAssembly
import Submission.EnergyNeg
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

noncomputable section

open Polynomial
open scoped Real BigOperators Topology ENNReal
open MeasureTheory

namespace Submission.SqueezeCore

open Submission.MinkBox
open Submission.Contracts
open Submission.EnergyHalf
open Submission.WeightedNorm
open Submission.SerreExample
open Submission.Serre
open Submission.PotentialContinuity
open Submission.PotentialDefs
open Submission.WnormToolkit
open Submission.SupportConcentration

/-! ## Local instances for the Serre measure `muSerre`. -/

instance instIsProbabilityMeasure_muSerre : IsProbabilityMeasure (muSerre : Measure ℝ) := by
  unfold muSerre
  infer_instance

instance instSigmaFinite_muSerre : SigmaFinite (muSerre : Measure ℝ) := by
  unfold muSerre
  infer_instance

instance instNullSingletonClass_muSerre : NullSingletonClass (muSerre : Measure ℝ) := by
  unfold muSerre
  infer_instance

instance instIsFiniteMeasure_muSerre : IsFiniteMeasure (muSerre : Measure ℝ) := by
  unfold muSerre
  infer_instance

/-- μ gives full mass to the interval. -/
lemma muSerre_Icc : muSerre (Set.Icc aSerre bSerre) = 1 := by
  unfold muSerre
  exact muS_Icc

/-- μ gives no mass to the complement of the interval. -/
lemma muSerre_compl_Icc : muSerre ((Set.Icc aSerre bSerre)ᶜ) = 0 := by
  unfold muSerre
  exact muS_compl_Icc

/-- μ is atom-free. -/
lemma muSerre_singleton (r : ℝ) : muSerre {r} = 0 := by
  unfold muSerre
  exact Submission.MuAtomFree.serre_atom_free r

/-- points of the interval are μ-almost everywhere. -/
lemma ae_mem_Icc_muSerre : (∀ᵐ x ∂muSerre, x ∈ Set.Icc aSerre bSerre) := by
  rw [MeasureTheory.ae_iff]
  have hset : {x : ℝ | ¬x ∈ Set.Icc aSerre bSerre} = (Set.Icc aSerre bSerre)ᶜ := by
    ext x
    simp
  rw [hset]
  exact muSerre_compl_Icc

/-! ## Weight, potential, energy -/

/-- `log w(x) = U(x)` pointwise. -/
lemma log_weight_eq_potential (x : ℝ) :
    Real.log (weight muSerre x) = logPotential muSerre (x : ℂ) := by
  unfold weight
  exact Real.log_exp _

/-- The integral of the potential against μ is the energy. -/
lemma integral_potential_eq_energy :
    (∫ x : ℝ, logPotential muSerre (x : ℂ) ∂muSerre) = energy := by
  unfold energy
  simpa [muSerre]

/-- `∫ n·log w = n·energy`. -/
lemma integral_log_weight (n : ℕ) :
    (∫ x : ℝ, (n : ℝ) * Real.log (weight muSerre x) ∂muSerre) =
      (n : ℝ) * energy := by
  calc
    (∫ x : ℝ, (n : ℝ) * Real.log (weight muSerre x) ∂muSerre)
        = (∫ x : ℝ, (n : ℝ) * logPotential muSerre (x : ℂ) ∂muSerre) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          rw [log_weight_eq_potential]
    _ = (n : ℝ) * (∫ x : ℝ, logPotential muSerre (x : ℂ) ∂muSerre) := by
          rw [MeasureTheory.integral_const_mul]
    _ = (n : ℝ) * energy := by rw [integral_potential_eq_energy]

/-- the log-weight function is continuous. -/
lemma continuous_log_weight : Continuous (fun x : ℝ => Real.log (weight muSerre x)) := by
  have hEq : (fun x : ℝ => Real.log (weight muSerre x))
      = (fun x : ℝ => logPotential muSerre (x : ℂ)) := by
    funext x
    rw [log_weight_eq_potential]
  rw [hEq]
  unfold muSerre
  exact logPotential_continuous_real

/-- log-weight is integrable against μ. -/
lemma integrable_log_weight : Integrable (fun x : ℝ => Real.log (weight muSerre x)) muSerre := by
  have hg : Integrable (fun x : ℝ => logPotential muS (x : ℂ)) muS := integrable_logPotential
  have hg' : Integrable (fun x : ℝ => logPotential muSerre (x : ℂ)) muSerre := by
    simpa [muSerre] using hg
  refine hg'.congr ?_
  filter_upwards with x
  exact (log_weight_eq_potential x).symm

/-- log-weight scaled is integrable. -/
lemma integrable_const_mul_log_weight (n : ℕ) :
    Integrable (fun x : ℝ => (n : ℝ) * Real.log (weight muSerre x)) muSerre := by
  exact integrable_log_weight.const_mul (n : ℝ)

/-! ## 1D log kernel facts against μ -/

/-- `y ↦ log|x − y|` is integrable against μ for every centre x. -/
lemma integrable_log_sub (x : ℝ) : Integrable (fun y : ℝ => Real.log (|x - y|)) muSerre := by
  unfold muSerre
  exact log_integrable x

/-- `y ↦ |log|x − y||` is integrable. -/
lemma integrable_abs_log_sub (x : ℝ) : Integrable (fun y : ℝ => |Real.log (|x - y|)|) muSerre := by
  unfold muSerre
  exact logAbs_integrable x

/-- ∫_y log|x−y| dμ(y) = −U(x). -/
lemma integral_log_sub_eq_neg_potential (x : ℝ) :
    (∫ y : ℝ, Real.log (|x - y|) ∂muSerre) = -logPotential muSerre (x : ℂ) := by
  have hpot : logPotential muSerre (x : ℂ) = ∫ y : ℝ, -Real.log (|x - y|) ∂muSerre := by
    unfold logPotential
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => log_norm_sub_ofReal x y)
  have hneg : (∫ y : ℝ, -Real.log (|x - y|) ∂muSerre) =
      -(∫ y : ℝ, Real.log (|x - y|) ∂muSerre) := by
    exact MeasureTheory.integral_neg (μ := muSerre) (f := fun y : ℝ => Real.log (|x - y|))
  linarith

/-- ∫_x ∫_y log|x−y| = −energy (iterated form). -/
lemma integral_log_pair_energy :
    (∫ x : ℝ, (∫ y : ℝ, Real.log (|x - y|) ∂muSerre) ∂muSerre) = -energy := by
  calc
    (∫ x : ℝ, (∫ y : ℝ, Real.log (|x - y|) ∂muSerre) ∂muSerre)
        = (∫ x : ℝ, -logPotential muSerre (x : ℂ) ∂muSerre) := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall (fun x => integral_log_sub_eq_neg_potential x)
    _ = -energy := by
          rw [MeasureTheory.integral_neg]
          rw [integral_potential_eq_energy]

/-! ## The tuple functions -/

/-- product measure of d independent copies of μ. -/
def pserre (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ : Fin d => muSerre)

instance (d : ℕ) : IsProbabilityMeasure (pserre d) := by
  dsimp [pserre]
  infer_instance

instance (d : ℕ) : SigmaFinite (pserre d) := by
  dsimp [pserre]
  infer_instance

/-- The logarithm of the per-coordinate factor `w(x)^n · |R(x)|`. -/
def coordLog (n : ℕ) (R : Polynomial ℤ) (x : ℝ) : ℝ :=
  Real.log (|Polynomial.aeval x R|) + (n : ℝ) * Real.log (weight muSerre x)

/-- The logarithm of the Vandermonde factors `∏_{i<j}|x_i − x_j|`. -/
def pairLog (d : ℕ) (x : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, ∑ j ∈ (Finset.univ.filter (fun j : Fin d => i < j)), Real.log (|x i - x j|)

/-- The full log of the tuple product (a.e. on the good set). -/
def totalLog (d : ℕ) (n : ℕ) (R : Polynomial ℤ) (x : Fin d → ℝ) : ℝ :=
  (∑ k : Fin d, coordLog n R (x k)) + pairLog d x

/-- The actual tuple product `F(x) = (∏_k w(x_k)^n|R(x_k)|)·pairProd`. -/
def tupleF (d : ℕ) (n : ℕ) (R : Polynomial ℤ) (x : Fin d → ℝ) : ℝ :=
  (∏ k : Fin d, (weight muSerre (x k)) ^ n * (|Polynomial.aeval (x k) R|)) *
    MinkBox.pairProd d x

/-! ## The good set -/

/-- a tuple is good: inside the interval, not a root of R, pairwise distinct. -/
def GoodTuple (d : ℕ) (R : Polynomial ℤ) (x : Fin d → ℝ) : Prop :=
  (∀ k : Fin d, x k ∈ Set.Icc aSerre bSerre) ∧
  (∀ k : Fin d, Polynomial.aeval (x k) R ≠ 0) ∧
  Function.Injective x

/-! ## Integrability of the coordinate terms -/

/-- `log|aeval · R|` (real) is integrable. -/
lemma integrable_log_abs_aeval (R : Polynomial ℤ) (hR : R ≠ 0) :
    Integrable (fun x : ℝ => Real.log (|Polynomial.aeval x R|)) muSerre := by
  simpa [muSerre] using (Submission.EnergyNeg.log_aeval_integrable R hR)

/-- single-coordinate marginal integral -/
lemma integral_comp_eval_mu {d : ℕ} (k : Fin d) (f : ℝ → ℝ) (hf : Integrable f muSerre) :
    (∫ x : Fin d → ℝ, f (x k) ∂pserre d) = ∫ x : ℝ, f x ∂muSerre := by
  dsimp [pserre]
  exact MeasureTheory.integral_comp_eval (μ := fun _ : Fin d => muSerre) (i := k)
    hf.aestronglyMeasurable

lemma integrable_comp_eval_mu {d : ℕ} (k : Fin d) (f : ℝ → ℝ) (hf : Integrable f muSerre) :
    Integrable (fun x : Fin d → ℝ => f (x k)) (pserre d) := by
  dsimp [pserre]
  exact MeasureTheory.integrable_comp_eval (μ := fun _ : Fin d => muSerre) (i := k) hf

/-! ## Coordinate-union measure facts -/

lemma measure_coord_notin_Icc {d : ℕ} (k : Fin d) :
    pserre d {x : Fin d → ℝ | x k ∉ Set.Icc aSerre bSerre} = 0 := by
  have hset : {x : Fin d → ℝ | x k ∉ Set.Icc aSerre bSerre} =
      (fun x : Fin d → ℝ => x k) ⁻¹' ((Set.Icc aSerre bSerre)ᶜ) := by
    ext x
    simp
  rw [hset]
  dsimp [pserre]
  exact Measure.pi_eval_preimage_null (μ := fun _ : Fin d => muSerre) (i := k)
    muSerre_compl_Icc

/-- the set of real roots of R has μ-measure zero. -/
lemma measure_root_1d (R : Polynomial ℤ) (hR : R ≠ 0) :
    muSerre {y : ℝ | Polynomial.aeval y R = 0} = 0 := by
  have hz : {y : ℝ | (zmap R).eval y = 0} = (Submission.LogProductMeasure.realRootSet R) :=
    Submission.EnergyNeg.zeroSet_zmap_eq_realRootSet R
  have hn : muSerre (Submission.LogProductMeasure.realRootSet R) = 0 := by
    unfold muSerre
    exact Submission.EnergyNeg.realRootSet_null R hR
  have hconv : {y : ℝ | Polynomial.aeval y R = 0} = {y : ℝ | (zmap R).eval y = 0} := by
    ext y
    simp [Submission.EnergyNeg.aeval_eq_zmap_eval]
  rw [hconv, hz]
  exact hn

lemma measure_coord_root {d : ℕ} (R : Polynomial ℤ) (hR : R ≠ 0) (k : Fin d) :
    pserre d {x : Fin d → ℝ | Polynomial.aeval (x k) R = 0} = 0 := by
  have hset : {x : Fin d → ℝ | Polynomial.aeval (x k) R = 0} =
      (fun x : Fin d → ℝ => x k) ⁻¹' {y : ℝ | Polynomial.aeval y R = 0} := by
    ext x
    simp
  rw [hset]
  dsimp [pserre]
  exact Measure.pi_eval_preimage_null (μ := fun _ : Fin d => muSerre) (i := k)
    (measure_root_1d R hR)


/-! ## Pair projection machinery -/

/-- the two-coordinate cylinder has measure `μA·μB`. -/
lemma measure_pair_cyl {d : ℕ} (i j : Fin d) (hij : i ≠ j) (A B : Set ℝ) :
    pserre d {x : Fin d → ℝ | x i ∈ A ∧ x j ∈ B} = muSerre A * muSerre B := by
  classical
  have hset : {x : Fin d → ℝ | x i ∈ A ∧ x j ∈ B} =
      Set.pi Set.univ (fun k : Fin d => if k = i then A else if k = j then B else Set.univ) := by
    ext x
    constructor
    · rintro ⟨hi, hj⟩ k hk
      by_cases hki : k = i
      · simpa [hki] using hi
      · by_cases hkj : k = j
        · simpa [hkj, hij.symm] using hj
        · simp [hki, hkj]
    · intro hx
      constructor
      · have := hx i (by simp)
        simpa using this
      · have := hx j (by simp)
        simpa [hij.symm] using this
  rw [hset]
  dsimp [pserre]
  rw [Measure.pi_pi (μ := fun _ : Fin d => muSerre)]
  let f : Fin d → ℝ≥0∞ := fun k => muSerre (if k = i then A else if k = j then B else Set.univ)
  have h1 : i ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ i
  have h2 : j ∈ (Finset.univ : Finset (Fin d)) \ {i} := by simp [hij.symm]
  calc
    (∏ k : Fin d, f k) = ∏ k ∈ (Finset.univ : Finset (Fin d)), f k := rfl
    _ = f i * ∏ k ∈ (Finset.univ : Finset (Fin d)) \ {i}, f k := by
          rw [Finset.prod_eq_mul_prod_sdiff_singleton (s := (Finset.univ : Finset (Fin d))) i f
            (fun hi => False.elim (hi h1))]
    _ = f i * (f j * ∏ k ∈ ((Finset.univ : Finset (Fin d)) \ {i}) \ {j}, f k) := by
          rw [Finset.prod_eq_mul_prod_sdiff_singleton
            (s := (Finset.univ : Finset (Fin d)) \ {i}) j f (fun hj => False.elim (hj h2))]
    _ = muSerre A * muSerre B := by
          have hrest : (∏ k ∈ ((Finset.univ : Finset (Fin d)) \ {i}) \ {j}, f k) = (1 : ℝ≥0∞) := by
            refine Finset.prod_eq_one ?_
            intro k hk
            have hmem1 : k ∈ (Finset.univ : Finset (Fin d)) \ {i} := (Finset.mem_sdiff.mp hk).1
            have hki : k ≠ i := by
              intro h
              have : k ∉ ({i} : Finset (Fin d)) := (Finset.mem_sdiff.mp hmem1).2
              exact this (by simp [h])
            have hkj : k ≠ j := by
              intro h
              have : k ∉ ({j} : Finset (Fin d)) := (Finset.mem_sdiff.mp hk).2
              exact this (by simp [h])
            simp [f, hki, hkj]
          dsimp [f]
          rw [if_neg hij.symm]
          rw [hrest]
          simp

/-- mapping a d-tuple to its pair (i,j) pushes π_d forward to μ⊗μ. -/
lemma pair_map_measure {d : ℕ} (i j : Fin d) (hij : i ≠ j) :
    Measure.map (fun x : Fin d → ℝ => (x i, x j)) (pserre d) = muSerre.prod muSerre := by
  classical
  let T2 : (Fin d → ℝ) → (Fin 2 → ℝ) := fun x t => if t = 0 then x i else x j
  have hT2m : Measurable T2 := by
    dsimp [T2]
    refine measurable_pi_iff.mpr ?_
    intro t
    by_cases ht0 : t = (0 : Fin 2)
    · simpa [ht0] using (measurable_pi_apply i)
    · have ht1 : t = (1 : Fin 2) := by
        rcases t with ⟨v, hv⟩
        have hvne0 : v ≠ 0 := by
          intro h
          apply ht0
          ext
          exact h
        omega
      simpa [ht1] using (measurable_pi_apply j)
  have hmap2 : Measure.map T2 (pserre d) = pserre 2 := by
    refine ((Measure.pi_eq (ι := Fin 2) (α := fun _ : Fin 2 => ℝ)
      (μ := fun _ : Fin 2 => muSerre)) ?_).symm
    intro s hs
    rw [Measure.map_apply hT2m]
    · have hpre : T2 ⁻¹' (Set.pi Set.univ s) =
          {x : Fin d → ℝ | x i ∈ s (0 : Fin 2) ∧ x j ∈ s (1 : Fin 2)} := by
        ext x
        constructor
        · intro hx
          constructor
          · have := hx (0 : Fin 2) (by simp)
            simpa [T2] using this
          · have := hx (1 : Fin 2) (by simp)
            simpa [T2] using this
        · intro hx
          intro t ht
          by_cases ht0 : t = (0 : Fin 2)
          · simpa [T2, ht0] using hx.1
          · have ht1 : t = (1 : Fin 2) := by
              rcases t with ⟨v, hv⟩
              have hvne0 : v ≠ 0 := by
                intro h
                apply ht0
                ext
                exact h
              omega
            simpa [T2, ht1] using hx.2
      rw [hpre]
      simpa [Fin.prod_univ_two] using measure_pair_cyl i j hij (s (0 : Fin 2)) (s (1 : Fin 2))
    · exact MeasurableSet.univ_pi hs
  let e := (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))
  have heq_fun : (fun x : Fin d → ℝ => (x i, x j)) = (fun x : Fin d → ℝ => e (T2 x)) := by
    funext x
    dsimp [T2]
    rw [MeasurableEquiv.piFinTwo_apply]
    congr 1 <;> simp
  calc
    Measure.map (fun x : Fin d → ℝ => (x i, x j)) (pserre d)
        = Measure.map (fun x : Fin d → ℝ => e (T2 x)) (pserre d) := by rw [heq_fun]
    _ = Measure.map e (Measure.map T2 (pserre d)) := by
          rw [show (fun x : Fin d → ℝ => e (T2 x)) = e ∘ T2 by rfl]
          exact (Measure.map_map e.measurable hT2m).symm
    _ = Measure.map e (pserre 2) := by
          rw [hmap2]
    _ = muSerre.prod muSerre := by
          have hp := measurePreserving_piFinTwo (μ := fun _ : Fin 2 => muSerre)
          simpa [pserre, e, MeasurableEquiv.piFinTwo_apply] using hp.map_eq

/-- the diagonal `x_i = x_j` is π_d-null. -/
lemma measure_diag_pair {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    pserre d {x : Fin d → ℝ | x i = x j} = 0 := by
  let T : (Fin d → ℝ) → ℝ × ℝ := fun x => (x i, x j)
  have hTmeas : Measurable T := by fun_prop
  have hdiag0 : (muSerre.prod muSerre) {p : ℝ × ℝ | p.1 = p.2} = 0 := by
    have hs : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} := by
      exact measurableSet_eq_fun measurable_fst measurable_snd
    rw [Measure.prod_apply hs]
    have hfun : (fun x : ℝ => muSerre (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2})) =
        fun x : ℝ => (0 : ℝ≥0∞) := by
      funext x
      have hset : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = ({x} : Set ℝ) := by
        ext y
        simp
      rw [hset]
      exact muSerre_singleton x
    rw [hfun]
    simp
  calc
    pserre d {x : Fin d → ℝ | x i = x j}
        = (Measure.map T (pserre d)) {p : ℝ × ℝ | p.1 = p.2} := by
          rw [Measure.map_apply hTmeas]
          · rfl
          · exact measurableSet_eq_fun measurable_fst measurable_snd
    _ = (muSerre.prod muSerre) {p : ℝ × ℝ | p.1 = p.2} := by
          rw [pair_map_measure i j hij]
    _ = 0 := hdiag0

/-- the (ordered) diagonal-with-inequality set is π_d-null. -/
lemma measure_diag_pair' {d : ℕ} (a b : Fin d) :
    pserre d {x : Fin d → ℝ | x a = x b ∧ a ≠ b} = 0 := by
  by_cases hab : a = b
  · subst b
    simp
  · have h : {x : Fin d → ℝ | x a = x b ∧ a ≠ b} ⊆ {x : Fin d → ℝ | x a = x b} := by
      intro x hx
      exact hx.1
    exact measure_mono_null h (measure_diag_pair hab)

/-- the pair integral over π_d reduces to the two-fold integral. -/
lemma integral_pair_marginal {d : ℕ} {i j : Fin d} (hij : i ≠ j)
    {g : ℝ → ℝ → ℝ} (hg : Integrable (fun p : ℝ × ℝ => g p.1 p.2) (muSerre.prod muSerre)) :
    (∫ x : Fin d → ℝ, g (x i) (x j) ∂pserre d) =
      ∫ p : ℝ × ℝ, g p.1 p.2 ∂(muSerre.prod muSerre) := by
  let T : (Fin d → ℝ) → ℝ × ℝ := fun x => (x i, x j)
  have hTmeas : Measurable T := by fun_prop
  have hTae : AEMeasurable T (pserre d) := hTmeas.aemeasurable
  have hmap : Measure.map T (pserre d) = muSerre.prod muSerre := pair_map_measure i j hij
  have hgm : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1 p.2) (Measure.map T (pserre d)) := by
    simpa [hmap] using hg.aestronglyMeasurable
  calc
    (∫ x : Fin d → ℝ, g (x i) (x j) ∂pserre d)
        = ∫ y : ℝ × ℝ, g y.1 y.2 ∂(Measure.map T (pserre d)) := by
          rw [MeasureTheory.integral_map hTae hgm]
    _ = ∫ p : ℝ × ℝ, g p.1 p.2 ∂(muSerre.prod muSerre) := by
          rw [hmap]

/-- integrability of the pair term on π_d, from 2D integrability. -/
lemma integrable_pair_marginal {d : ℕ} {i j : Fin d} (hij : i ≠ j)
    {g : ℝ → ℝ → ℝ} (hg : Integrable (fun p : ℝ × ℝ => g p.1 p.2) (muSerre.prod muSerre)) :
    Integrable (fun x : Fin d → ℝ => g (x i) (x j)) (pserre d) := by
  let T : (Fin d → ℝ) → ℝ × ℝ := fun x => (x i, x j)
  have hTmeas : Measurable T := by fun_prop
  have hmap : Measure.map T (pserre d) = muSerre.prod muSerre := pair_map_measure i j hij
  have hgmap : Integrable (fun p : ℝ × ℝ => g p.1 p.2) (Measure.map T (pserre d)) := by
    simpa [hmap] using hg
  exact MeasureTheory.Integrable.comp_measurable hgmap hTmeas

/-- the diagonal is measurable. -/
lemma measurable_set_diag {d : ℕ} (i j : Fin d) :
    MeasurableSet {x : Fin d → ℝ | x i = x j} := by
  exact measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)

/-- polynomial evaluation is continuous. -/
lemma continuous_aeval_Int (R : Polynomial ℤ) :
    Continuous (fun y : ℝ => Polynomial.aeval y R) := by
  have h : (fun y : ℝ => Polynomial.aeval y R) = fun y : ℝ => (zmap R).eval y := by
    funext y
    exact Submission.EnergyNeg.aeval_eq_zmap_eval R y
  rw [h]
  have hc : Continuous (fun y : ℝ => aeval y (zmap R)) := Polynomial.continuous_aeval (zmap R)
  -- aeval y (zmap R) = eval y (zmap R) since coefficients are already in ℝ
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_id] using hc

/-- the good set is measurable. -/
lemma measurable_GoodTuple (d : ℕ) (R : Polynomial ℤ) :
    MeasurableSet {x : Fin d → ℝ | GoodTuple d R x} := by
  classical
  have hI : MeasurableSet {x : Fin d → ℝ | ∀ k : Fin d, x k ∈ Set.Icc aSerre bSerre} := by
    rw [show {x : Fin d → ℝ | ∀ k : Fin d, x k ∈ Set.Icc aSerre bSerre} =
        ⋂ k : Fin d, {x : Fin d → ℝ | x k ∈ Set.Icc aSerre bSerre} by
          ext x
          simp]
    exact MeasurableSet.iInter (fun k => (measurable_pi_apply k) isClosed_Icc.measurableSet)
  have hRset : MeasurableSet {x : Fin d → ℝ | ∀ k : Fin d, Polynomial.aeval (x k) R ≠ 0} := by
    rw [show {x : Fin d → ℝ | ∀ k : Fin d, Polynomial.aeval (x k) R ≠ 0} =
        ⋂ k : Fin d, {x : Fin d → ℝ | Polynomial.aeval (x k) R ≠ 0} by
          ext x
          simp]
    refine MeasurableSet.iInter ?_
    intro k
    have hsetR : {x : Fin d → ℝ | Polynomial.aeval (x k) R ≠ 0} =
        (fun x : Fin d → ℝ => x k) ⁻¹' {y : ℝ | Polynomial.aeval y R ≠ 0} := by
      ext x
      simp
    rw [hsetR]
    exact ((isOpen_compl_singleton.preimage (continuous_aeval_Int R)).measurableSet.preimage
      (measurable_pi_apply k))
  have hnotinj : {x : Fin d → ℝ | ¬ Function.Injective x} =
        ⋃ a : Fin d, ⋃ b : Fin d, {x : Fin d → ℝ | x a = x b ∧ a ≠ b} := by
      ext x
      constructor
      · intro hx
        rcases not_forall.mp hx with ⟨a, ha⟩
        rcases not_forall.mp ha with ⟨b, hb⟩
        refine Set.mem_iUnion.mpr ⟨a, ?_⟩
        refine Set.mem_iUnion.mpr ⟨b, ?_⟩
        have hEq : x a = x b := by
          by_contra hne
          exact hb (fun h => False.elim (hne h))
        have hab : a ≠ b := by
          intro hab
          exact hb (fun _ => hab)
        exact ⟨hEq, hab⟩
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨a, ha⟩
        rcases Set.mem_iUnion.mp ha with ⟨b, hb⟩
        intro hinj
        exact hb.2 (hinj hb.1)
  have hInj : MeasurableSet {x : Fin d → ℝ | Function.Injective x} := by
    rw [show {x : Fin d → ℝ | Function.Injective x} =
        (⋃ a : Fin d, ⋃ b : Fin d, {x : Fin d → ℝ | x a = x b ∧ a ≠ b})ᶜ by
          ext x
          rw [← hnotinj]
          simp]
    refine (MeasurableSet.iUnion ?_).compl
    intro a
    refine MeasurableSet.iUnion ?_
    intro b
    have hdiagset : {x : Fin d → ℝ | x a = x b ∧ a ≠ b} =
        {x : Fin d → ℝ | x a = x b} ∩ {x : Fin d → ℝ | a ≠ b} := by
      ext x
      simp
    rw [hdiagset]
    exact (measurable_set_diag a b).inter (by
      by_cases hab : a = b <;> simp [hab])
  have hset : {x : Fin d → ℝ | GoodTuple d R x} =
      {x : Fin d → ℝ | ∀ k : Fin d, x k ∈ Set.Icc aSerre bSerre} ∩
      {x : Fin d → ℝ | ∀ k : Fin d, Polynomial.aeval (x k) R ≠ 0} ∩
      {x : Fin d → ℝ | Function.Injective x} := by
    ext x
    simp [GoodTuple, and_assoc]
  rw [hset]
  exact (hI.inter hRset).inter hInj

/-- The good set has full measure. -/
lemma measure_good_compl {d : ℕ} (R : Polynomial ℤ) (hR : R ≠ 0) :
    pserre d {x : Fin d → ℝ | ¬ GoodTuple d R x} = 0 := by
  classical
  have hsub : {x : Fin d → ℝ | ¬ GoodTuple d R x} ⊆
      (⋃ i : Fin d, {x : Fin d → ℝ | x i ∉ Set.Icc aSerre bSerre}) ∪
      (⋃ i : Fin d, {x : Fin d → ℝ | Polynomial.aeval (x i) R = 0}) ∪
      (⋃ a : Fin d, ⋃ b : Fin d, {x : Fin d → ℝ | x a = x b ∧ a ≠ b}) := by
    intro x hx
    by_cases hI : ∀ k : Fin d, x k ∈ Set.Icc aSerre bSerre
    · by_cases hR0 : ∀ k : Fin d, Polynomial.aeval (x k) R ≠ 0
      · right
        have hinj : ¬ Function.Injective x := by
          intro hinj
          exact hx ⟨hI, hR0, hinj⟩
        rcases not_forall.mp hinj with ⟨a, ha⟩
        rcases not_forall.mp ha with ⟨b, hb⟩
        refine Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨b, ?_⟩⟩
        have hEq : x a = x b := by
          by_contra hne
          exact hb (fun h => False.elim (hne h))
        have hab : a ≠ b := by
          intro hab
          exact hb (fun _ => hab)
        exact ⟨hEq, hab⟩
      · left
        right
        rcases not_forall.mp hR0 with ⟨a, ha⟩
        exact Set.mem_iUnion.mpr ⟨a, by
          exact (Classical.not_not.mp ha)⟩
    · left
      left
      rcases not_forall.mp hI with ⟨a, ha⟩
      exact Set.mem_iUnion.mpr ⟨a, ha⟩
  have hnull1 : pserre d (⋃ i : Fin d, {x : Fin d → ℝ | x i ∉ Set.Icc aSerre bSerre}) = 0 := by
    apply le_antisymm
    · calc
        pserre d (⋃ i : Fin d, {x : Fin d → ℝ | x i ∉ Set.Icc aSerre bSerre})
            ≤ ∑' i : Fin d, pserre d {x : Fin d → ℝ | x i ∉ Set.Icc aSerre bSerre} :=
              measure_iUnion_le _
        _ = 0 := by
            rw [tsum_fintype]
            apply Finset.sum_eq_zero
            intro i hi
            exact measure_coord_notin_Icc i
    · exact zero_le
  have hnull2 : pserre d (⋃ i : Fin d, {x : Fin d → ℝ | Polynomial.aeval (x i) R = 0}) = 0 := by
    apply le_antisymm
    · calc
        pserre d (⋃ i : Fin d, {x : Fin d → ℝ | Polynomial.aeval (x i) R = 0})
            ≤ ∑' i : Fin d, pserre d {x : Fin d → ℝ | Polynomial.aeval (x i) R = 0} :=
              measure_iUnion_le _
        _ = 0 := by
            rw [tsum_fintype]
            simp [measure_coord_root R hR]
    · exact zero_le
  have hnull3 : pserre d (⋃ a : Fin d, ⋃ b : Fin d,
      {x : Fin d → ℝ | x a = x b ∧ a ≠ b}) = 0 := by
    apply le_antisymm
    · calc
        pserre d (⋃ a : Fin d, ⋃ b : Fin d, {x : Fin d → ℝ | x a = x b ∧ a ≠ b})
            ≤ ∑' a : Fin d, pserre d (⋃ b : Fin d, {x : Fin d → ℝ | x a = x b ∧ a ≠ b}) :=
              measure_iUnion_le _
        _ ≤ ∑' a : Fin d, ∑' b : Fin d,
              pserre d {x : Fin d → ℝ | x a = x b ∧ a ≠ b} := by
            exact ENNReal.tsum_le_tsum (fun a => measure_iUnion_le _)
        _ = 0 := by
            simp_rw [tsum_fintype]
            apply Finset.sum_eq_zero
            intro a ha
            apply Finset.sum_eq_zero
            intro b hb
            exact measure_diag_pair' a b
    · exact zero_le
  have hsub' : {x : Fin d → ℝ | ¬ GoodTuple d R x} ⊆
      (⋃ i : Fin d, {x : Fin d → ℝ | x i ∉ Set.Icc aSerre bSerre}) ∪
      ((⋃ i : Fin d, {x : Fin d → ℝ | Polynomial.aeval (x i) R = 0}) ∪
      (⋃ a : Fin d, ⋃ b : Fin d, {x : Fin d → ℝ | x a = x b ∧ a ≠ b})) := by
    simpa [Set.union_assoc] using hsub
  exact measure_mono_null hsub' (measure_union_null hnull1 (measure_union_null hnull2 hnull3))

/-- The good set has measure one. -/
lemma measure_good {d : ℕ} (R : Polynomial ℤ) (hR : R ≠ 0) :
    pserre d {x : Fin d → ℝ | GoodTuple d R x} = 1 := by
  have hmeas := measurable_GoodTuple d R
  have hcompl : pserre d ({x : Fin d → ℝ | GoodTuple d R x}ᶜ) = 0 := by
    have hset : ({x : Fin d → ℝ | GoodTuple d R x}ᶜ) = {x : Fin d → ℝ | ¬ GoodTuple d R x} := by
      ext x
      simp
    rw [hset]
    exact measure_good_compl R hR
  have hsum := MeasureTheory.measure_add_measure_compl (μ := pserre d) hmeas
  rw [hcompl, add_zero] at hsum
  have huniv : pserre d Set.univ = 1 := by
    dsimp [pserre]
    simp
  rw [huniv] at hsum
  exact hsum


end Submission.SqueezeCore
