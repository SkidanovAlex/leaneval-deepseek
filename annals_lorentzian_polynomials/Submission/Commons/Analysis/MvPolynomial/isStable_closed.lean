import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPowerSeries.Evaluation

open MvPolynomial Polynomial BigOperators
open scoped MvPowerSeries.WithPiTopology
open Topology Filter

namespace Commons.Analysis.MvPolynomial

-- Helper lemmas (copied)
lemma continuous_coeff_mvpoly (n : ℕ) (m : Fin n →₀ ℕ) :
    Continuous fun p : MvPolynomial (Fin n) ℝ => p.coeff m := by
  have h := (MvPowerSeries.WithPiTopology.continuous_coeff (σ := Fin n) (R := ℝ) m).comp
    (MvPolynomial.toMvPowerSeries_isUniformInducing.uniformContinuous.continuous :
      Continuous (toMvPowerSeries (σ := Fin n) (R := ℝ)))
  exact h.congr (fun p => MvPolynomial.coeff_coe p m)

noncomputable def slicePoly (n d : ℕ) (z v : Fin n → ℂ)
    (f : homogeneousSubmodule (Fin n) ℝ d) : Polynomial ℂ :=
  MvPolynomial.aeval (R := ℝ) (fun i => Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X) f.1

lemma mem_finsuppAntidiag_univ_iff_degree (n d : ℕ) (m : Fin n →₀ ℕ) :
    m ∈ (Finset.univ : Finset (Fin n)).finsuppAntidiag d ↔ Finsupp.degree m = d := by
  classical
  rw [Finset.mem_finsuppAntidiag]
  have hsum_univ : (Finset.univ : Finset (Fin n)).sum (fun i => m i) = ∑ i ∈ m.support, m i := by
    have h := Finset.sum_subset (s₁ := m.support) (s₂ := (Finset.univ : Finset (Fin n)))
      (by simp) (by
        intro i hi hnot
        have hi0 : m i = 0 := by
          by_contra h
          exact hnot (Finsupp.mem_support_iff.mpr h)
        exact hi0)
    rw [h]
  constructor
  · rintro ⟨hsum, hsupp⟩
    rw [Finsupp.degree_apply]
    rwa [hsum_univ] at hsum
  · intro hdeg
    constructor
    · rw [hsum_univ]
      simpa [Finsupp.degree_apply] using hdeg
    · simp

lemma slicePoly_eq_sum (n d : ℕ) (z v : Fin n → ℂ)
    (f : homogeneousSubmodule (Fin n) ℝ d) :
    slicePoly n d z v f =
      ∑ m ∈ (Finset.univ : Finset (Fin n)).finsuppAntidiag d,
        MvPolynomial.aeval (R := ℝ) (fun i => Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X)
          (MvPolynomial.monomial m (MvPolynomial.coeff (R := ℝ) m f.1)) := by
  classical
  unfold slicePoly
  conv_lhs => rw [← f.1.support_sum_monomial_coeff]
  rw [map_sum]
  apply Finset.sum_subset
  · intro m hm
    have hc : MvPolynomial.coeff (R := ℝ) m f.1 ≠ 0 := MvPolynomial.mem_support_iff.mp hm
    have hdeg : Finsupp.degree m = d := by
      rw [Finsupp.degree_eq_weight_one]
      exact f.2 hc
    exact (mem_finsuppAntidiag_univ_iff_degree n d m).mpr hdeg
  · intro m hmS hnot
    have hc : MvPolynomial.coeff (R := ℝ) m f.1 = 0 := by
      by_contra h
      exact hnot (MvPolynomial.mem_support_iff.mpr h)
    simp [hc]

lemma continuous_slicePoly_coeff (n d : ℕ) (z v : Fin n → ℂ) (i : ℕ) :
    Continuous fun f : homogeneousSubmodule (Fin n) ℝ d => (slicePoly n d z v f).coeff i := by
  classical
  let a : Fin n → Polynomial ℂ := fun j => Polynomial.C (z j) + Polynomial.C (v j) * Polynomial.X
  let S : Finset (Fin n →₀ ℕ) := (Finset.univ : Finset (Fin n)).finsuppAntidiag d
  have hfun : (fun f : homogeneousSubmodule (Fin n) ℝ d => (slicePoly n d z v f).coeff i) =
      fun f => ∑ m ∈ S, (MvPolynomial.aeval (R := ℝ) a
        (MvPolynomial.monomial m (MvPolynomial.coeff (R := ℝ) m f.1))).coeff i := by
    funext f
    rw [slicePoly_eq_sum n d z v f]
    rw [Polynomial.finsetSum_coeff]
  rw [hfun]
  refine continuous_finsetSum S ?_
  intro m hm
  have hterm : (fun f : homogeneousSubmodule (Fin n) ℝ d =>
      (MvPolynomial.aeval (R := ℝ) a
        (MvPolynomial.monomial m (MvPolynomial.coeff (R := ℝ) m f.1))).coeff i) =
      fun f => algebraMap ℝ ℂ (MvPolynomial.coeff (R := ℝ) m f.1) *
        (m.prod (fun j k => a j ^ k)).coeff i := by
    ext f
    rw [MvPolynomial.aeval_monomial]
    change (Polynomial.C (algebraMap ℝ ℂ (MvPolynomial.coeff (R := ℝ) m f.1)) *
        m.prod (fun j k => a j ^ k)).coeff i =
      algebraMap ℝ ℂ (MvPolynomial.coeff (R := ℝ) m f.1) * (m.prod (fun j k => a j ^ k)).coeff i
    rw [Polynomial.coeff_C_mul]
  rw [hterm]
  have hconst : Continuous (fun _ : homogeneousSubmodule (Fin n) ℝ d =>
      (m.prod (fun j k => a j ^ k)).coeff i) := continuous_const
  have hcoeff_cont : Continuous (fun f : homogeneousSubmodule (Fin n) ℝ d =>
      algebraMap ℝ ℂ (MvPolynomial.coeff (R := ℝ) m f.1)) :=
    (continuous_algebraMap ℝ ℂ).comp ((continuous_coeff_mvpoly n m).comp continuous_subtype_val)
  exact hcoeff_cont.mul hconst

lemma slicePoly_natDegree_le (n d : ℕ) (z v : Fin n → ℂ)
    (f : homogeneousSubmodule (Fin n) ℝ d) :
    (slicePoly n d z v f).natDegree ≤ d := by
  classical
  unfold slicePoly
  let a : Fin n → Polynomial ℂ := fun i => Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X
  have hlin : ∀ i, (a i).natDegree ≤ 1 := by
    intro i
    dsimp [a]
    rw [add_comm]
    exact Polynomial.natDegree_linear_le
  have hdeg_monomial : ∀ m : Fin n →₀ ℕ, m ∈ f.1.support →
      (MvPolynomial.aeval (R := ℝ) a (MvPolynomial.monomial m (MvPolynomial.coeff (R := ℝ) m f.1))).natDegree ≤ d := by
    intro m hm
    have hc : MvPolynomial.coeff (R := ℝ) m f.1 ≠ 0 := MvPolynomial.mem_support_iff.mp hm
    have hdeg_m : Finsupp.degree m = d := by
      rw [Finsupp.degree_eq_weight_one]
      exact f.2 hc
    rw [MvPolynomial.aeval_monomial]
    calc
      (Polynomial.C (algebraMap ℝ ℂ (MvPolynomial.coeff (R := ℝ) m f.1)) *
          (m.prod fun i k => a i ^ k)).natDegree
          ≤ (m.prod fun i k => a i ^ k).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ ≤ ∑ i ∈ m.support, ((a i) ^ (m i)).natDegree := by
          simpa [Finsupp.prod] using Polynomial.natDegree_prod_le m.support (fun i => a i ^ m i)
      _ ≤ ∑ i ∈ m.support, m i * 1 := by
          apply Finset.sum_le_sum
          intro i hi
          exact Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hlin i))
      _ = d := by
          rw [← hdeg_m, Finsupp.degree_apply]
          simp
  have hsum : (∑ m ∈ f.1.support, MvPolynomial.aeval (R := ℝ) a
      (MvPolynomial.monomial m (MvPolynomial.coeff (R := ℝ) m f.1))).natDegree ≤ d := by
    calc
      (∑ m ∈ f.1.support, MvPolynomial.aeval (R := ℝ) a
        (MvPolynomial.monomial m (MvPolynomial.coeff (R := ℝ) m f.1))).natDegree
          ≤ Finset.fold max 0 (Polynomial.natDegree ∘ fun m =>
              MvPolynomial.aeval (R := ℝ) a (MvPolynomial.monomial m (MvPolynomial.coeff (R := ℝ) m f.1))) f.1.support :=
        Polynomial.natDegree_sum_le _ _
      _ ≤ d := by
        exact Finset.sup_le (s := f.1.support)
          (f := fun m => (MvPolynomial.aeval (R := ℝ) a
            (MvPolynomial.monomial m (MvPolynomial.coeff (R := ℝ) m f.1))).natDegree) (by
            intro m hm
            exact hdeg_monomial m hm)
  have hsum_eq : MvPolynomial.aeval (R := ℝ) a f.1 =
      ∑ m ∈ f.1.support, MvPolynomial.aeval (R := ℝ) a
        (MvPolynomial.monomial m (MvPolynomial.coeff (R := ℝ) m f.1)) := by
    conv_lhs => rw [← f.1.support_sum_monomial_coeff]
    rw [map_sum]
  change (MvPolynomial.aeval (R := ℝ) a f.1).natDegree ≤ d
  rw [hsum_eq]
  exact hsum

lemma coeff_one_affine (z v : ℂ) :
    (Polynomial.C z + Polynomial.C v * Polynomial.X).coeff 1 = v := by
  rw [show Polynomial.C v * Polynomial.X = Polynomial.monomial 1 v by
    simpa using (Polynomial.C_mul_X_eq_monomial (a := v))]
  rw [add_comm, Polynomial.coeff_add, Polynomial.coeff_monomial, Polynomial.coeff_C]
  simp

lemma coeff_prod_eq_prod_coeff_of_natDegree_le {ι R : Type*} [CommSemiring R]
    (s : Finset ι) (f : ι → Polynomial R) (n : ι → ℕ)
    (h : ∀ i ∈ s, natDegree (f i) ≤ n i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, n i) = ∏ i ∈ s, (f i).coeff (n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hsum_le : natDegree (∏ i ∈ s, f i) ≤ ∑ i ∈ s, n i := by
        calc
          natDegree (∏ i ∈ s, f i) ≤ ∑ i ∈ s, natDegree (f i) := Polynomial.natDegree_prod_le _ _
          _ ≤ ∑ i ∈ s, n i := by
            apply Finset.sum_le_sum
            intro i hi
            exact h i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      rw [Polynomial.coeff_mul_add_eq_of_natDegree_le (h a (Finset.mem_insert_self a s)) hsum_le]
      rw [Finset.prod_insert ha]
      rw [ih]
      intro i hi
      exact h i (Finset.mem_insert_of_mem hi)

lemma slicePoly_coeff_d (n d : ℕ) (z v : Fin n → ℂ)
    (f : homogeneousSubmodule (Fin n) ℝ d) :
    (slicePoly n d z v f).coeff d = MvPolynomial.aeval (R := ℝ) v f.1 := by
  classical
  unfold slicePoly
  let a : Fin n → Polynomial ℂ := fun i => Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X
  have hlin : ∀ i, natDegree (a i) ≤ 1 := by
    intro i
    dsimp [a]
    rw [add_comm]
    exact Polynomial.natDegree_linear_le
  have hdeg_monomial : ∀ m : Fin n →₀ ℕ, m ∈ f.1.support →
      (MvPolynomial.aeval (R := ℝ) a (MvPolynomial.monomial m (MvPolynomial.coeff (R := ℝ) m f.1))).coeff d =
        algebraMap ℝ ℂ (MvPolynomial.coeff (R := ℝ) m f.1) * ∏ i ∈ m.support, v i ^ m i := by
    intro m hm
    have hc : MvPolynomial.coeff (R := ℝ) m f.1 ≠ 0 := MvPolynomial.mem_support_iff.mp hm
    have hdeg_m : Finsupp.degree m = d := by
      rw [Finsupp.degree_eq_weight_one]
      exact f.2 hc
    have hdeg_sum : ∑ i ∈ m.support, m i = d := by
      rw [← hdeg_m, Finsupp.degree_apply]
    rw [MvPolynomial.aeval_monomial]
    change (Polynomial.C (algebraMap ℝ ℂ (MvPolynomial.coeff (R := ℝ) m f.1)) *
        m.prod (fun i k => a i ^ k)).coeff d =
        algebraMap ℝ ℂ (MvPolynomial.coeff (R := ℝ) m f.1) * ∏ i ∈ m.support, v i ^ m i
    rw [Polynomial.coeff_C_mul]
    have hprod_coeff :
        (m.prod fun i k => a i ^ k).coeff d = ∏ i ∈ m.support, v i ^ m i := by
      rw [← hdeg_sum]
      change (∏ i ∈ m.support, a i ^ m i).coeff (∑ i ∈ m.support, m i) = ∏ i ∈ m.support, v i ^ m i
      rw [coeff_prod_eq_prod_coeff_of_natDegree_le m.support (fun i => a i ^ m i) (fun i => m i) ?_]
      · apply Finset.prod_congr rfl
        intro i hi
        have hpow : (a i ^ m i).coeff (m i) = v i ^ m i := by
          have h := Polynomial.coeff_pow_of_natDegree_le (p := a i) (m := m i) (n := 1) (hlin i)
          simpa [a, coeff_one_affine] using h
        exact hpow
      · intro i hi
        have hle := (Polynomial.natDegree_pow_le (p := a i) (n := m i)).trans
          (Nat.mul_le_mul_left (m i) (hlin i))
        simpa using hle
    rw [hprod_coeff]
  have hsum_coeff : (∑ m ∈ f.1.support, MvPolynomial.aeval (R := ℝ) a
      (MvPolynomial.monomial m (MvPolynomial.coeff (R := ℝ) m f.1))).coeff d =
        ∑ m ∈ f.1.support, algebraMap ℝ ℂ (MvPolynomial.coeff (R := ℝ) m f.1) * ∏ i ∈ m.support, v i ^ m i := by
    rw [Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro m hm
    exact hdeg_monomial m hm
  have hsum_eval : MvPolynomial.aeval (R := ℝ) a f.1 =
      ∑ m ∈ f.1.support, MvPolynomial.aeval (R := ℝ) a
        (MvPolynomial.monomial m (MvPolynomial.coeff (R := ℝ) m f.1)) := by
    conv_lhs => rw [← f.1.support_sum_monomial_coeff]
    rw [map_sum]
  have hsum_v : MvPolynomial.aeval (R := ℝ) v f.1 =
      ∑ m ∈ f.1.support, algebraMap ℝ ℂ (MvPolynomial.coeff (R := ℝ) m f.1) * ∏ i ∈ m.support, v i ^ m i := by
    conv_lhs => rw [← f.1.support_sum_monomial_coeff]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [MvPolynomial.aeval_monomial]
    change algebraMap ℝ ℂ (MvPolynomial.coeff (R := ℝ) m f.1) * (m.prod fun i k => v i ^ k) =
      algebraMap ℝ ℂ (MvPolynomial.coeff (R := ℝ) m f.1) * ∏ i ∈ m.support, v i ^ m i
    rfl
  rw [hsum_eval, hsum_coeff, hsum_v]

lemma slicePoly_natDegree_eq_of_aeval_ne_zero (n d : ℕ) (z v : Fin n → ℂ)
    (f : homogeneousSubmodule (Fin n) ℝ d)
    (hv : MvPolynomial.aeval (R := ℝ) v f.1 ≠ 0) :
    (slicePoly n d z v f).natDegree = d := by
  have hle := slicePoly_natDegree_le n d z v f
  have hcoeff := slicePoly_coeff_d n d z v f
  have hne : (slicePoly n d z v f).coeff d ≠ 0 := by
    rwa [hcoeff]
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle hne

lemma slicePoly_eval (n d : ℕ) (z v : Fin n → ℂ)
    (f : homogeneousSubmodule (Fin n) ℝ d) (b : ℂ) :
    Polynomial.eval b (slicePoly n d z v f) =
      MvPolynomial.aeval (R := ℝ) (fun i => z i + b * v i) f.1 := by
  classical
  unfold slicePoly
  let a : Fin n → Polynomial ℂ := fun i => Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X
  let φ : Polynomial ℂ →ₐ[ℝ] ℂ := (Polynomial.aeval (R := ℂ) b).restrictScalars ℝ
  have h := MvPolynomial.comp_aeval_apply (f := a) (φ := φ) (p := f.1)
  change φ (MvPolynomial.aeval (R := ℝ) a f.1) = MvPolynomial.aeval (R := ℝ) (fun i => z i + b * v i) f.1
  have hfun : (fun i => φ (a i)) = (fun i => z i + b * v i) := by
    funext i
    dsimp [φ, a]
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    simp [mul_comm]
  rw [h, hfun]

lemma exists_complex_aeval_ne_zero_of_ne_zero (n d : ℕ)
    (f : homogeneousSubmodule (Fin n) ℝ d) (hf : f.1 ≠ 0) :
    ∃ v : Fin n → ℂ, MvPolynomial.aeval (R := ℝ) v f.1 ≠ 0 := by
  classical
  have hreal : ∃ r : Fin n → ℝ, MvPolynomial.eval r f.1 ≠ 0 := by
    by_contra h
    apply hf
    have hforall : ∀ r : Fin n → ℝ, MvPolynomial.eval r f.1 = 0 := by
      simpa [not_exists, not_ne_iff] using h
    exact MvPolynomial.IsHomogeneous.eq_zero_of_forall_eval_eq_zero f.2 hforall
  rcases hreal with ⟨r, hr⟩
  refine ⟨fun i => (r i : ℂ), ?_⟩
  have hae : MvPolynomial.aeval (R := ℝ) (fun i => (r i : ℂ)) f.1 =
      algebraMap ℝ ℂ (MvPolynomial.eval r f.1) := by
    change MvPolynomial.aeval (R := ℝ) (Complex.ofReal ∘ r) f.1 = _
    simpa using MvPolynomial.aeval_algebraMap_apply (B := ℂ) (x := r) (p := f.1)
  rw [hae]
  exact Complex.ofReal_ne_zero.mpr hr

lemma exists_pos_rpow_lt (d : ℕ) (hd : 0 < d) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ (((d + 1 : ℕ) : ℝ) * ε) ^ ((d : ℝ)⁻¹) < δ := by
  let x : ℝ := δ / 2
  have hx : 0 < x := by positivity
  let ε : ℝ := x ^ d / (d + 1)
  refine ⟨ε, ?_, ?_⟩
  · dsimp [ε, x]
    positivity
  · have hden : (d + 1 : ℝ) ≠ 0 := by positivity
    have hmul : (((d + 1 : ℕ) : ℝ) * ε) = x ^ d := by
      dsimp [ε, x]
      rw [Nat.cast_add, Nat.cast_one]
      field_simp [hden]
    rw [hmul]
    have hxle : 0 ≤ x := le_of_lt hx
    have hpow : (x ^ d) ^ ((d : ℝ)⁻¹) = x := by
      have hmain := Real.rpow_mul hxle (d : ℝ) ((d : ℝ)⁻¹)
      rw [Real.rpow_natCast] at hmain
      have hdreal : (d : ℝ) * (d : ℝ)⁻¹ = 1 := by
        exact mul_inv_cancel₀ (by exact_mod_cast (ne_of_gt hd))
      rw [hdreal, Real.rpow_one] at hmain
      exact hmain.symm
    rw [hpow]
    dsimp [x]
    linarith

-- Main root-near lemma
lemma exists_slice_root_near (n d : ℕ) (z v : Fin n → ℂ)
    (f : homogeneousSubmodule (Fin n) ℝ d)
    (hv : MvPolynomial.aeval (R := ℝ) v f.1 ≠ 0)
    (hz : MvPolynomial.aeval (R := ℝ) z f.1 = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ U ∈ 𝓝 f, ∀ g ∈ U, g.1 ≠ 0 ∧ ∃ t : ℂ,
      MvPolynomial.aeval (R := ℝ) (fun i => z i + t * v i) g.1 = 0 ∧ ‖t‖ < δ := by
  classical
  let P : homogeneousSubmodule (Fin n) ℝ d → Polynomial ℂ := fun g => slicePoly n d z v g
  have hdpos : 0 < d := by
    by_contra hd
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    have hcoeff0 : (P f).coeff 0 ≠ 0 := by
      have hcd : (P f).coeff 0 = MvPolynomial.aeval (R := ℝ) v f.1 := by
        simpa [hd0] using slicePoly_coeff_d n d z v f
      rwa [hcd]
    have heval0 : Polynomial.eval 0 (P f) = 0 := by
      change Polynomial.eval 0 (slicePoly n d z v f) = 0
      rw [slicePoly_eval n d z v f 0]
      rw [show (fun i => z i + 0 * v i) = z by funext i; simp]
      exact hz
    have heval0' : (P f).coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact heval0
    exact hcoeff0 heval0'
  obtain ⟨ε, hεpos, hεroot⟩ := exists_pos_rpow_lt d hdpos δ hδ
  let Qcoeff : ℕ → homogeneousSubmodule (Fin n) ℝ d → ℂ :=
    fun i g => (P g).coeff i * ((P g).coeff d)⁻¹
  have hPcoeff_cont (i : ℕ) : Continuous (fun g : homogeneousSubmodule (Fin n) ℝ d => (P g).coeff i) := by
    change Continuous (fun g : homogeneousSubmodule (Fin n) ℝ d => (slicePoly n d z v g).coeff i)
    exact continuous_slicePoly_coeff n d z v i
  have hPcoeff_d_ne : (P f).coeff d ≠ 0 := by
    rw [slicePoly_coeff_d]
    exact hv
  have hQcoeff_cont (i : ℕ) : ContinuousAt (Qcoeff i) f := by
    dsimp [Qcoeff]
    apply ContinuousAt.mul
    · exact (hPcoeff_cont i).continuousAt
    · apply ContinuousAt.inv₀
      · exact (hPcoeff_cont d).continuousAt
      · exact hPcoeff_d_ne
  have hnon : ∀ᶠ g in 𝓝 f, (P g).coeff d ≠ 0 := by
    exact (hPcoeff_cont d).continuousAt.eventually_ne hPcoeff_d_ne
  have hclose_i (i : ℕ) (hi : i ∈ Finset.range (d + 1)) :
      ∀ᶠ g in 𝓝 f, ‖Qcoeff i g - Qcoeff i f‖ < ε := by
    have ht := (hQcoeff_cont i).tendsto
    refine (ht.eventually (Metric.ball_mem_nhds (Qcoeff i f) hεpos)).mono ?_
    intro g hg
    simpa [Metric.mem_ball, dist_eq_norm] using hg
  have hclose_all : ∀ᶠ g in 𝓝 f, ∀ i ∈ Finset.range (d + 1),
      ‖Qcoeff i g - Qcoeff i f‖ < ε := by
    rw [Filter.eventually_all_finset]
    intro i hi
    exact hclose_i i hi
  have hfinal : ∀ᶠ g in 𝓝 f,
      (P g).coeff d ≠ 0 ∧ ∀ i ∈ Finset.range (d + 1), ‖Qcoeff i g - Qcoeff i f‖ < ε :=
    hnon.and hclose_all
  rcases Filter.Eventually.exists_mem hfinal with ⟨U, hUmem, hU⟩
  refine ⟨U, hUmem, ?_⟩
  intro g hg
  have hgprop := hU g hg
  have hg0 : (P g).coeff d ≠ 0 := hgprop.1
  have hgclose := hgprop.2
  have hg_ne_zero : g.1 ≠ 0 := by
    intro hzero
    apply hg0
    dsimp [P]
    unfold slicePoly
    rw [hzero]
    simp
  let qf : Polynomial ℂ := (P f) * Polynomial.C ((P f).coeff d)⁻¹
  let qg : Polynomial ℂ := (P g) * Polynomial.C ((P g).coeff d)⁻¹
  have hnd_f : (P f).natDegree = d :=
    slicePoly_natDegree_eq_of_aeval_ne_zero n d z v f hv
  have hnd_g : (P g).natDegree = d := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · exact slicePoly_natDegree_le n d z v g
    · exact hg0
  have hleading_f : (P f).leadingCoeff = (P f).coeff d := by
    rw [Polynomial.leadingCoeff, hnd_f]
  have hleading_g : (P g).leadingCoeff = (P g).coeff d := by
    rw [Polynomial.leadingCoeff, hnd_g]
  have hqf_monic : qf.Monic := by
    dsimp [qf]
    apply Polynomial.monic_mul_C_of_leadingCoeff_mul_eq_one
    rw [hleading_f]
    exact mul_inv_cancel₀ hPcoeff_d_ne
  have hqg_monic : qg.Monic := by
    dsimp [qg]
    apply Polynomial.monic_mul_C_of_leadingCoeff_mul_eq_one
    rw [hleading_g]
    exact mul_inv_cancel₀ hg0
  have hqg_natDegree : qg.natDegree = d := by
    dsimp [qg]
    rw [Polynomial.natDegree_mul_C]
    · exact hnd_g
    · exact inv_ne_zero hg0
  have hqf_natDegree : qf.natDegree = d := by
    dsimp [qf]
    rw [Polynomial.natDegree_mul_C]
    · exact hnd_f
    · exact inv_ne_zero hPcoeff_d_ne
  have hqf_eval0 : Polynomial.eval 0 qf = 0 := by
    dsimp [qf]
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    have hP0 : Polynomial.eval 0 (P f) = 0 := by
      change Polynomial.eval 0 (slicePoly n d z v f) = 0
      rw [slicePoly_eval n d z v f 0]
      rw [show (fun i => z i + 0 * v i) = z by funext i; simp]
      exact hz
    simp [hP0]
  have hcoeff_all : ∀ i : ℕ, ‖(qg).coeff i - (qf).coeff i‖ < ε := by
    intro i
    by_cases hi : i ∈ Finset.range (d + 1)
    · have h := hgclose i hi
      dsimp [qg, qf]
      simpa [Polynomial.coeff_mul_C] using h
    · have hgt : d < i := Nat.lt_of_succ_le (by simpa [Finset.mem_range] using hi)
      have hqg0 : (qg).coeff i = 0 := by
        dsimp [qg]
        rw [Polynomial.coeff_mul_C]
        apply mul_eq_zero_of_left
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hnd_g]; exact hgt)
      have hqf0 : (qf).coeff i = 0 := by
        dsimp [qf]
        rw [Polynomial.coeff_mul_C]
        apply mul_eq_zero_of_left
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hnd_f]; exact hgt)
      simp [hqg0, hqf0, hεpos]
  have hdeg_eq : qg.natDegree = qf.natDegree := by rw [hqg_natDegree, hqf_natDegree]
  have hroots := Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt
    (hε := hεpos) (a := (0 : ℂ)) (f := qf) (g := qg)
    hqf_eval0 hqf_monic hqg_monic hdeg_eq hcoeff_all (IsAlgClosed.splits qg)
  rcases hroots with ⟨b, hb_mem, hbdist⟩
  have hb_root_qg : Polynomial.eval b qg = 0 :=
    Polynomial.isRoot_of_mem_roots hb_mem
  have hb_root_P : Polynomial.eval b (P g) = 0 := by
    have hprod : Polynomial.eval b qg = Polynomial.eval b (P g) * ((P g).coeff d)⁻¹ := by
      dsimp [qg]
      rw [Polynomial.eval_mul, Polynomial.eval_C]
    rw [hprod] at hb_root_qg
    exact (mul_eq_zero.mp hb_root_qg).resolve_right (inv_ne_zero hg0)
  refine ⟨hg_ne_zero, b, ?_, ?_⟩
  · rw [← slicePoly_eval n d z v g b]
    exact hb_root_P
  · have hb_norm_lt : ‖b‖ < δ := by
      have hmax : max ‖(0 : ℂ)‖ 1 = 1 := by simp
      have hbdist' : ‖b‖ < (((d + 1 : ℕ) : ℝ) * ε) ^ ((d : ℝ)⁻¹) := by
        simpa [hqf_natDegree, hmax, norm_sub_rev] using hbdist
      exact hbdist'.trans hεroot
    exact hb_norm_lt



theorem isStable_closed (n d : ℕ) :
  IsClosed {f : homogeneousSubmodule (Fin n) ℝ d |
    f.1 = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
      MvPolynomial.aeval ((fun h : UpperHalfPlane => (h : ℂ)) ∘ z) f.1 ≠ 0} := by
  classical
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro f hf
  rw [Set.mem_compl_iff, Set.mem_ofPred_eq] at hf
  push Not at hf
  rcases hf with ⟨hf0, z, hz⟩
  let zc : Fin n → ℂ := fun i => (z i : ℂ)
  have hzc : MvPolynomial.aeval (R := ℝ) zc f.1 = 0 := by
    dsimp [zc]
    exact hz
  obtain ⟨v, hv⟩ := exists_complex_aeval_ne_zero_of_ne_zero n d f hf0
  let ratio : Fin n → ℝ := fun i => ((z i : ℂ).im) / (‖v i‖ + 1)
  have hratio_pos : ∀ i, 0 < ratio i := by
    intro i
    dsimp [ratio]
    positivity
  by_cases hn : Nonempty (Fin n)
  · let δ : ℝ := (Finset.univ.inf' (Finset.univ_nonempty) ratio) / 2
    have hinf_pos : 0 < Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty) ratio := by
      rw [Finset.lt_inf'_iff]
      intro i hi
      exact hratio_pos i
    have hδpos : 0 < δ := by
      dsimp [δ]
      positivity
    have hδ_lt_ratio : ∀ i, δ < ratio i := by
      intro i
      have hhalf : (Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty) ratio) / 2 <
          Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty) ratio := by
        rw [div_lt_iff₀ zero_lt_two]
        linarith
      have hle := Finset.inf'_le ratio (Finset.mem_univ i)
      exact lt_of_lt_of_le hhalf hle
    have hδsmall : ∀ i, δ * ‖v i‖ < ((z i : ℂ).im) := by
      intro i
      have hden : 0 < ‖v i‖ + 1 := by positivity
      have hlt : δ * (‖v i‖ + 1) < ((z i : ℂ).im) := by
        exact (lt_div_iff₀ hden).mp (by simpa [ratio] using hδ_lt_ratio i)
      calc
        δ * ‖v i‖ ≤ δ * (‖v i‖ + 1) := by
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hδpos.le
        _ < ((z i : ℂ).im) := hlt
    obtain ⟨U0, hU0mem, hU0⟩ := exists_slice_root_near n d zc v f hv hzc hδpos
    refine mem_of_superset hU0mem ?_
    intro g hg
    rw [Set.mem_compl_iff, Set.mem_ofPred_eq]
    push Not
    rcases hU0 g hg with ⟨hg_ne_zero, t, ht_zero, ht_norm⟩
    refine ⟨hg_ne_zero, ?_⟩
    have him : ∀ i, 0 < ((zc i + t * v i).im) := by
      intro i
      have hnorm_lt : ‖t * v i‖ < ((z i : ℂ).im) := by
        by_cases hv0 : ‖v i‖ = 0
        · rw [norm_mul, hv0, mul_zero]
          exact (z i).im_pos
        · have hvpos : 0 < ‖v i‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv0)
          calc
            ‖t * v i‖ = ‖t‖ * ‖v i‖ := norm_mul _ _
            _ < δ * ‖v i‖ := mul_lt_mul_of_pos_right ht_norm hvpos
            _ < ((z i : ℂ).im) := hδsmall i
      have h_abs_im : |(t * v i).im| < ((z i : ℂ).im) :=
        (Complex.abs_im_le_norm _).trans_lt hnorm_lt
      have hlow : -((z i : ℂ).im) < (t * v i).im := (abs_lt.mp h_abs_im).1
      have him_sum : ((zc i + t * v i).im) = ((z i : ℂ).im) + (t * v i).im := by
        simp [zc, Complex.add_im]
      rw [him_sum]
      linarith
    let z' : Fin n → UpperHalfPlane := fun i => ⟨zc i + t * v i, him i⟩
    refine ⟨z', ?_⟩
    change MvPolynomial.aeval (R := ℝ) (fun i => (z' i : ℂ)) g.1 = 0
    simpa [z'] using ht_zero
  · let δ : ℝ := 1
    have hδpos : 0 < δ := by norm_num
    have hδsmall : ∀ i, δ * ‖v i‖ < ((z i : ℂ).im) := by
      intro i
      exact False.elim (hn ⟨i⟩)
    obtain ⟨U0, hU0mem, hU0⟩ := exists_slice_root_near n d zc v f hv hzc hδpos
    refine mem_of_superset hU0mem ?_
    intro g hg
    rw [Set.mem_compl_iff, Set.mem_ofPred_eq]
    push Not
    rcases hU0 g hg with ⟨hg_ne_zero, t, ht_zero, ht_norm⟩
    refine ⟨hg_ne_zero, ?_⟩
    have him : ∀ i, 0 < ((zc i + t * v i).im) := by
      intro i
      exact False.elim (hn ⟨i⟩)
    let z' : Fin n → UpperHalfPlane := fun i => ⟨zc i + t * v i, him i⟩
    refine ⟨z', ?_⟩
    change MvPolynomial.aeval (R := ℝ) (fun i => (z' i : ℂ)) g.1 = 0
    simpa [z'] using ht_zero

end Commons.Analysis.MvPolynomial