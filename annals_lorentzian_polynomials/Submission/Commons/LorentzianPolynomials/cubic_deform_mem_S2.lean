import Mathlib
import Submission.Commons.Analysis.MvPolynomial.gch_complexHurwitz
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.LorentzianPolynomials.strict_subset_L
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.LorentzianPolynomials.closure_diagonalize
import Submission.Commons.LorentzianPolynomials.closure_strict_eq_L_of_degree_le_two
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq
import Submission.Commons.LorentzianPolynomials.quad_deform_stable
import Submission.Commons.LorentzianPolynomials.deform_support_MConvex
import Submission.Commons.LorentzianPolynomials.pderiv_stable_mem_S
import Submission.Commons.LorentzianPolynomials.L_mem_nonneg
import Submission.Commons.LorentzianPolynomials.two_term_degenerate_mem_S
import Submission.Commons.Analysis.Complex.Polynomial.deriv_stable_of_stable
import Submission.Commons.Analysis.Complex.Polynomial.plus_x_mul_deriv_stable
import Submission.Commons.Analysis.MvPolynomial.isStable_of_degree_le_one

open Finsupp Matrix MvPolynomial Polynomial UpperHalfPlane Topology Set Filter
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! Private (renamed) copies of the "closure package" lemmas that live on the
`isStable_tendsto_of_degree_le` side of the commons, which cannot be imported
together with the `isStable_closed` side that defines `S`, `L`, ... -/

namespace Commons.LorentzianPolynomials

noncomputable section

/-- Stability is preserved by renaming along any map (forward direction). -/
private lemma cdm_IsStable_rename {n m : ℕ} (e : Fin n → Fin m) (p : MvPolynomial (Fin n) ℝ)
    (h : IsStable p) : IsStable (MvPolynomial.rename e p) := by
  rcases h with hz | hf
  · left
    rw [hz]
    simp
  · right
    intro z
    rw [MvPolynomial.aeval_rename]
    exact hf (fun i : Fin n => z (e i))

/-- Stability is preserved by embedding in one more variable (via `castSucc`). -/
private lemma cdm_IsStable_rename_castSucc {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (h : IsStable (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) p)) :
    IsStable p := by
  classical
  let I : UpperHalfPlane := ⟨Complex.I, by simp⟩
  rcases h with hz | hf
  · left
    exact MvPolynomial.rename_injective (Fin.castSucc : Fin n → Fin (n + 1))
      (by intro a b hab; apply Fin.ext; simpa using congrArg Fin.val hab) hz
  · right
    intro z
    let g : Fin (n + 1) → UpperHalfPlane := fun j =>
      if hj : j.1 < n then z ⟨j.1, hj⟩ else I
    have hge : ∀ i : Fin n, g (Fin.castSucc i) = z i := by
      intro i
      dsimp [g]
      simp
    have hfun : ((fun j : Fin (n + 1) => ((g j : UpperHalfPlane) : ℂ)) ∘
          (Fin.castSucc : Fin n → Fin (n + 1))) = (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) := by
      funext i
      simp [hge i]
    have heq : MvPolynomial.aeval (fun i : Fin n => (z i : ℂ)) p =
        MvPolynomial.aeval (fun j : Fin (n + 1) => ((g j : UpperHalfPlane) : ℂ))
          (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) p) := by
      rw [MvPolynomial.aeval_rename]
      rw [hfun]
    change MvPolynomial.aeval (fun i : Fin n => ((z i : ℍ) : ℂ)) p ≠ 0
    rw [heq]
    exact hf g

end
end Commons.LorentzianPolynomials

noncomputable section

open Filter Topology Polynomial
open scoped Topology BigOperators

namespace Commons.Analysis.MvPolynomial

/-! The slice of a multivariate polynomial along an affine complex line. -/

/-- The univariate polynomial `t ↦ p(z + t v)`, viewed as a complex polynomial in `t`. -/
def cdmT_slicePoly (n : ℕ) (z v : Fin n → ℂ) (p : MvPolynomial (Fin n) ℝ) : Polynomial ℂ :=
  MvPolynomial.aeval (R := ℝ)
    (fun i : Fin n => Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X) p

lemma cdmT_slicePoly_eval (n : ℕ) (z v : Fin n → ℂ) (p : MvPolynomial (Fin n) ℝ) (b : ℂ) :
    Polynomial.eval b (cdmT_slicePoly n z v p) =
      MvPolynomial.aeval (R := ℝ) (fun i : Fin n => z i + b * v i) p := by
  unfold cdmT_slicePoly
  let a : Fin n → Polynomial ℂ :=
    fun i => Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X
  let φ : Polynomial ℂ →ₐ[ℝ] ℂ := (Polynomial.aeval (R := ℂ) b).restrictScalars ℝ
  have h := MvPolynomial.comp_aeval_apply (f := a) (φ := φ) (p := p)
  change φ (MvPolynomial.aeval (R := ℝ) a p) =
    MvPolynomial.aeval (R := ℝ) (fun i => z i + b * v i) p
  have hfun : (fun i => φ (a i)) = (fun i => z i + b * v i) := by
    funext i
    dsimp [φ, a]
    change Polynomial.eval b (Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X) = z i + b * v i
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  rw [h, hfun]

/-- The slice monomial factor `∏_i (C (z i) + C (v i) X) ^ (m i)`. -/
def cdmT_sliceMon (n : ℕ) (z v : Fin n → ℂ) (m : Fin n →₀ ℕ) : Polynomial ℂ :=
  m.prod fun i k => (Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X) ^ k

lemma cdmT_sliceMon_natDegree_le {n : ℕ} (z v : Fin n → ℂ) (m : Fin n →₀ ℕ) :
    (cdmT_sliceMon n z v m).natDegree ≤ Finsupp.degree m := by
  classical
  let a : Fin n → Polynomial ℂ := fun i => Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X
  have hlin : ∀ i, (a i).natDegree ≤ 1 := by
    intro i
    dsimp [a]
    rw [add_comm]
    exact Polynomial.natDegree_linear_le
  calc
    (cdmT_sliceMon n z v m).natDegree = (m.prod fun i k => a i ^ k).natDegree := by rfl
    _ ≤ ∑ i ∈ m.support, (a i ^ m i).natDegree := by
      simpa [Finsupp.prod] using
        (Polynomial.natDegree_prod_le m.support (fun i => a i ^ m i))
    _ ≤ ∑ i ∈ m.support, m i * 1 := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Polynomial.natDegree_pow_le (p := a i) (n := m i)).trans
        (Nat.mul_le_mul_left (m i) (hlin i))
    _ = Finsupp.degree m := by
      rw [Finsupp.degree_apply]
      simp

lemma cdmT_sliceMon_coeff_eq_zero_of_weight_lt {n : ℕ} (z v : Fin n → ℂ) (m : Fin n →₀ ℕ)
    {j : ℕ} (hj : Finsupp.degree m < j) : (cdmT_sliceMon n z v m).coeff j = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (cdmT_sliceMon_natDegree_le z v m) hj)

lemma cdmT_slicePoly_coeff_eq_sum_support (n : ℕ) (z v : Fin n → ℂ) (p : MvPolynomial (Fin n) ℝ) (j : ℕ) :
    (cdmT_slicePoly n z v p).coeff j =
      ∑ m ∈ p.support, ((p.coeff m : ℝ) : ℂ) * (cdmT_sliceMon n z v m).coeff j := by
  classical
  let a : Fin n → Polynomial ℂ :=
    fun i => Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X
  have hae : MvPolynomial.aeval (R := ℝ) a p =
      ∑ m ∈ p.support, Polynomial.C ((p.coeff m : ℝ) : ℂ) * cdmT_sliceMon n z v m := by
    conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [MvPolynomial.aeval_monomial]
    rfl
  unfold cdmT_slicePoly
  rw [hae]
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Polynomial.coeff_C_mul]

lemma cdmT_slicePoly_natDegree_le (n : ℕ) (z v : Fin n → ℂ) (p : MvPolynomial (Fin n) ℝ) :
    (cdmT_slicePoly n z v p).natDegree ≤ p.totalDegree := by
  classical
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [cdmT_slicePoly_coeff_eq_sum_support]
  apply Finset.sum_eq_zero
  intro m hm
  have hdeg_le : Finsupp.degree m ≤ p.totalDegree := by
    have h := MvPolynomial.le_totalDegree (p := p) hm
    simpa [Finsupp.degree_apply, Finsupp.sum] using h
  have hlt : Finsupp.degree m < N := lt_of_le_of_lt hdeg_le hN
  rw [cdmT_sliceMon_coeff_eq_zero_of_weight_lt (m := m) (j := N) (z := z) (v := v) hlt]
  simp

lemma cdmT_slicePoly_eq_partialSum {n D : ℕ} (z v : Fin n → ℂ) (p : MvPolynomial (Fin n) ℝ)
    (hdeg : p.totalDegree ≤ D) :
    cdmT_slicePoly n z v p =
      ∑ i : Fin (D + 1), Polynomial.monomial (i : ℕ) ((cdmT_slicePoly n z v p).coeff (i : ℕ)) := by
  classical
  have hnd : (cdmT_slicePoly n z v p).natDegree ≤ D :=
    le_trans (cdmT_slicePoly_natDegree_le n z v p) hdeg
  have hndlt : (cdmT_slicePoly n z v p).natDegree < D + 1 := Nat.lt_succ_of_le hnd
  have h := Polynomial.as_sum_range' (cdmT_slicePoly n z v p) (D + 1) hndlt
  calc
    cdmT_slicePoly n z v p =
        ∑ i ∈ Finset.range (D + 1), Polynomial.monomial i ((cdmT_slicePoly n z v p).coeff i) := h
    _ = ∑ i : Fin (D + 1), Polynomial.monomial (i : ℕ) ((cdmT_slicePoly n z v p).coeff (i : ℕ)) := by
      exact (Fin.sum_univ_eq_sum_range
        (fun i : ℕ => Polynomial.monomial i ((cdmT_slicePoly n z v p).coeff i)) (D + 1)).symm

/-! The (finite) set of monomials of total degree at most `D`. -/

/-- All monomials in `n` variables of total degree at most `D`, as a finset. -/
def cdmT_monomialsLE (n D : ℕ) : Finset (Fin n →₀ ℕ) := by
  classical
  exact (Finset.range (D + 1)).biUnion
    (fun d : ℕ => (Finset.univ : Finset (Fin n)).finsuppAntidiag d)

lemma mem_cdmT_monomialsLE {n D : ℕ} (m : Fin n →₀ ℕ) :
    m ∈ cdmT_monomialsLE n D ↔ Finsupp.degree m ≤ D := by
  classical
  rw [cdmT_monomialsLE, Finset.mem_biUnion]
  constructor
  · rintro ⟨d, hd, hm⟩
    have hmem := (Finset.mem_finsuppAntidiag).mp hm
    have hd_le : d ≤ D := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
    have hdeg : Finsupp.degree m = d := by
      rw [Finsupp.degree_eq_sum]
      exact hmem.1
    exact le_trans (le_of_eq hdeg) hd_le
  · intro hdeg
    refine ⟨Finsupp.degree m, Finset.mem_range.mpr (Nat.lt_succ_of_le hdeg), ?_⟩
    rw [Finset.mem_finsuppAntidiag]
    simp [Finsupp.degree_eq_sum]

lemma support_subset_cdmT_monomialsLE {n D : ℕ} (p : MvPolynomial (Fin n) ℝ) (hdeg : p.totalDegree ≤ D) :
    p.support ⊆ cdmT_monomialsLE n D := by
  classical
  intro m hm
  rw [mem_cdmT_monomialsLE]
  have h := MvPolynomial.le_totalDegree (p := p) hm
  exact le_trans h hdeg

lemma cdmT_slicePoly_coeff_eq_sum_cdmT_monomialsLE {n D : ℕ} (z v : Fin n → ℂ) (p : MvPolynomial (Fin n) ℝ)
    (hdeg : p.totalDegree ≤ D) (j : ℕ) :
    (cdmT_slicePoly n z v p).coeff j =
      ∑ m ∈ cdmT_monomialsLE n D, ((p.coeff m : ℝ) : ℂ) * (cdmT_sliceMon n z v m).coeff j := by
  classical
  rw [cdmT_slicePoly_coeff_eq_sum_support]
  exact Finset.sum_subset (support_subset_cdmT_monomialsLE p hdeg) (by
    intro m hmS hmnot
    have hc : p.coeff m = 0 := by
      by_contra h
      exact hmnot (MvPolynomial.mem_support_iff.mpr h)
    simp [hc])

lemma cdmT_slicePoly_coeff_tendsto {n D : ℕ} (z v : Fin n → ℂ) (u : ℕ → MvPolynomial (Fin n) ℝ)
    (g : MvPolynomial (Fin n) ℝ)
    (huD : ∀ k : ℕ, (u k).totalDegree ≤ D) (hgD : g.totalDegree ≤ D)
    (hconv : ∀ m : Fin n →₀ ℕ, Tendsto (fun k : ℕ => (u k).coeff m) atTop (𝓝 (g.coeff m)))
    (j : ℕ) :
    Tendsto (fun k : ℕ => (cdmT_slicePoly n z v (u k)).coeff j) atTop
      (𝓝 ((cdmT_slicePoly n z v g).coeff j)) := by
  classical
  rw [show (fun k : ℕ => (cdmT_slicePoly n z v (u k)).coeff j) =
      fun k : ℕ => ∑ m ∈ cdmT_monomialsLE n D,
        (((u k).coeff m : ℝ) : ℂ) * (cdmT_sliceMon n z v m).coeff j by
        funext k
        exact (cdmT_slicePoly_coeff_eq_sum_cdmT_monomialsLE z v (u k) (huD k) j)]
  rw [show (𝓝 ((cdmT_slicePoly n z v g).coeff j)) =
      𝓝 (∑ m ∈ cdmT_monomialsLE n D,
        ((g.coeff m : ℝ) : ℂ) * (cdmT_sliceMon n z v m).coeff j) by
        congr 1
        exact (cdmT_slicePoly_coeff_eq_sum_cdmT_monomialsLE z v g hgD j)]
  refine tendsto_finsetSum (cdmT_monomialsLE n D) ?_
  intro m hm
  have hmc : Tendsto (fun k : ℕ => (((u k).coeff m : ℝ) : ℂ)) atTop (𝓝 (((g.coeff m : ℝ) : ℂ))) := by
    exact (continuous_algebraMap ℝ ℂ).continuousAt.tendsto.comp (hconv m)
  have hcst : Tendsto (fun k : ℕ => (cdmT_sliceMon n z v m).coeff j) atTop
      (𝓝 ((cdmT_sliceMon n z v m).coeff j)) := tendsto_const_nhds
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmc.mul hcst

/-! Convergence of coefficients, a good slice direction, root isolation. -/

lemma cdmT_exists_monomial_ne_zero_of_ne_zero {n : ℕ} (g : MvPolynomial (Fin n) ℝ) (hg : g ≠ 0) :
    ∃ m : Fin n →₀ ℕ, g.coeff m ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hg
  ext m
  exact h m

lemma cdmT_coeff_tendsto_of_deg_le {n D : ℕ} (u : ℕ → MvPolynomial (Fin n) ℝ)
    (g : MvPolynomial (Fin n) ℝ)
    (hconv : ∀ m : Fin n →₀ ℕ, Tendsto (fun k : ℕ => (u k).coeff m) atTop (𝓝 (g.coeff m)))
    (hg : g ≠ 0) :
    ∀ᶠ k in atTop, u k ≠ 0 := by
  classical
  rcases cdmT_exists_monomial_ne_zero_of_ne_zero g hg with ⟨m, hm⟩
  have ht : Tendsto (fun k : ℕ => (u k).coeff m) atTop (𝓝 (g.coeff m)) := hconv m
  have hev : ∀ᶠ k in atTop, (u k).coeff m ≠ 0 := by
    exact ht.eventually_ne hm
  filter_upwards [hev] with k hk
  intro hk0
  apply hk
  rw [hk0]
  simp

lemma exists_cdmT_slicePoly_ne_zero {n : ℕ} (z : Fin n → ℂ) (g : MvPolynomial (Fin n) ℝ)
    (hg : g ≠ 0) :
    ∃ v : Fin n → ℂ, cdmT_slicePoly n z v g ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hg
  apply MvPolynomial.funext (p := g) (q := 0)
  intro x
  have hx : MvPolynomial.aeval (R := ℝ) (fun i : Fin n => (x i : ℂ)) g = 0 := by
    have hv := h (fun i : Fin n => (x i : ℂ) - z i)
    have hslice := cdmT_slicePoly_eval n z (fun i : Fin n => (x i : ℂ) - z i) g 1
    rw [hv] at hslice
    have hfun : (fun i : Fin n => z i + 1 * ((x i : ℂ) - z i)) = fun i : Fin n => (x i : ℂ) := by
      funext i
      ring
    simpa [hfun] using hslice.symm
  have h3 := MvPolynomial.aeval_algebraMap_apply (R := ℝ) (A := ℝ) (B := ℂ) (x := x) (p := g)
  have hx0 : (algebraMap ℝ ℂ (MvPolynomial.aeval x g)) = 0 := by
    rw [← h3]
    simpa [Function.comp_def] using hx
  have hx0' : MvPolynomial.aeval x g = 0 := Complex.ofReal_eq_zero.mp hx0
  simpa using hx0'

lemma cdmT_exists_lt_norm_of_finite_nonzero {s : Finset ℂ} (hs : ∀ z ∈ s, z ≠ 0)
    (hsne : s.Nonempty) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ s, ρ < ‖z‖ := by
  classical
  let N : Finset ℝ := s.image (fun z : ℂ => ‖z‖)
  have hNne : N.Nonempty := by
    rcases hsne with ⟨z, hz⟩
    exact ⟨‖z‖, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
  let m : ℝ := N.min' hNne
  have hm_mem : m ∈ N := Finset.min'_mem N hNne
  have hm_pos : 0 < m := by
    rcases Finset.mem_image.mp hm_mem with ⟨z, hz, hzN⟩
    rw [← hzN]
    exact norm_pos_iff.mpr (hs z hz)
  refine ⟨m / 2, by positivity, ?_⟩
  intro z hz
  have hzn : ‖z‖ ∈ N := Finset.mem_image.mpr ⟨z, hz, rfl⟩
  have hmle : m ≤ ‖z‖ := Finset.min'_le N ‖z‖ hzn
  linarith

lemma cdmT_exists_root_isolated {p : Polynomial ℂ} (hp : p ≠ 0) (hp0 : p.eval 0 = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, z ∈ Metric.closedBall 0 ρ → z ≠ 0 → p.eval z ≠ 0 := by
  classical
  let S : Set ℂ := {z | z ≠ 0 ∧ p.eval z = 0}
  have hSfin : S.Finite := by
    refine (Polynomial.finite_setOfPred_isRoot hp).subset ?_
    intro z hz
    exact hz.2
  by_cases hS : S = ∅
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz hz0 hroot
    have hzS : z ∈ S := ⟨hz0, hroot⟩
    rw [hS] at hzS
    exact hzS
  · have hSne : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hS
    let T : Finset ℂ := hSfin.toFinset
    have hT : T.Nonempty := by
      rcases hSne with ⟨z, hz⟩
      exact ⟨z, (hSfin.mem_toFinset).mpr hz⟩
    have hTz : ∀ z ∈ T, z ≠ 0 := by
      intro z hz
      exact ((hSfin.mem_toFinset).mp hz).1
    rcases cdmT_exists_lt_norm_of_finite_nonzero hTz hT with ⟨ρ, hρ0, hρ⟩
    refine ⟨ρ, hρ0, ?_⟩
    intro z hz hz0 hroot
    have hzS : z ∈ S := ⟨hz0, hroot⟩
    have hzT : z ∈ T := (hSfin.mem_toFinset).mpr hzS
    have hzρ : ‖z‖ ≤ ρ := by
      have hzball := Metric.mem_closedBall.mp hz
      simpa using hzball
    have hlt := hρ z hzT  -- ρ < ‖z‖
    linarith

/-- For every `i`, `z i + t (v i)` stays in the upper half plane for `‖t‖`
sufficiently small, uniformly in `i`. -/
lemma cdmT_exists_stay_upper (n : ℕ) (z v : Fin n → ℂ)
    (hz : ∀ i : Fin n, 0 < (z i).im) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℂ, ‖t‖ < ρ → ∀ i : Fin n, 0 < (z i + t * v i).im := by
  classical
  by_cases hn : Nonempty (Fin n)
  · let ratio : Fin n → ℝ := fun i => (z i).im / (‖v i‖ + 1)
    have hratio_pos : ∀ i, 0 < ratio i := by
      intro i
      dsimp [ratio]
      exact div_pos (hz i) (by positivity)
    let ρ : ℝ := (Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty) ratio) / 2
    have hinf_pos : 0 < Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty) ratio := by
      rw [Finset.lt_inf'_iff]
      intro i hi
      exact hratio_pos i
    have hρpos : 0 < ρ := by
      dsimp [ρ]
      exact div_pos hinf_pos zero_lt_two
    have hρ_lt : ∀ i, ρ < ratio i := by
      intro i
      have hhalf : (Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty) ratio) / 2 <
          Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty) ratio := by
        rw [div_lt_iff₀ zero_lt_two]
        linarith
      have hle := Finset.inf'_le ratio (Finset.mem_univ i)
      exact lt_of_lt_of_le hhalf hle
    refine ⟨ρ, hρpos, ?_⟩
    intro t ht i
    have h_lt_ratio : ‖t‖ < ratio i := lt_trans ht (hρ_lt i)
    have hden : 0 < ‖v i‖ + 1 := by positivity
    have hmul_lt : ‖t‖ * ‖v i‖ < (z i).im := by
      have hmul : ‖t‖ * ‖v i‖ ≤ ‖t‖ * (‖v i‖ + 1) := by
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (norm_nonneg t)
      have hlt' : ‖t‖ * (‖v i‖ + 1) < (z i).im := by
        exact (lt_div_iff₀ hden).mp h_lt_ratio
      exact lt_of_le_of_lt hmul hlt'
    have him : ‖t * v i‖ < (z i).im := by
      simpa [norm_mul] using hmul_lt
    have h_abs_im : |(t * v i).im| < (z i).im :=
      (Complex.abs_im_le_norm (t * v i)).trans_lt him
    have hlow : -((z i).im) < (t * v i).im := (abs_lt.mp h_abs_im).1
    have him_sum : (z i + t * v i).im = (z i).im + (t * v i).im := by
      simp [Complex.add_im]
    rw [him_sum]
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro t ht i
    exact False.elim (hn ⟨i⟩)


theorem cdmT_isStable_tendsto_of_degree_le (n D : ℕ) (u : ℕ → MvPolynomial (Fin n) ℝ)
    (g : MvPolynomial (Fin n) ℝ)
    (huD : ∀ k : ℕ, (u k).totalDegree ≤ D) (hgD : g.totalDegree ≤ D)
    (hconv : ∀ m : Fin n →₀ ℕ, Tendsto (fun k : ℕ => (u k).coeff m) atTop (𝓝 (g.coeff m)))
    (hstab : ∀ k : ℕ, (u k) = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) (u k) ≠ 0) :
    g = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) g ≠ 0 := by
  classical
  by_cases hg : g = 0
  · exact Or.inl hg
  · right
    intro z
    by_contra hz0
    let zc : Fin n → ℂ := fun i => ((z i : UpperHalfPlane) : ℂ)
    have hz0' : MvPolynomial.aeval (R := ℝ) zc g = 0 := by
      simpa [zc] using hz0
    have hz_im : ∀ i : Fin n, 0 < (zc i).im := by
      intro i
      dsimp [zc]
      exact UpperHalfPlane.im_pos (z i)
    obtain ⟨v, hv⟩ := exists_cdmT_slicePoly_ne_zero zc g hg
    let Q : Polynomial ℂ := cdmT_slicePoly n zc v g
    have hQ0 : Q.eval 0 = 0 := by
      change Polynomial.eval 0 (cdmT_slicePoly n zc v g) = 0
      simpa [hz0'] using cdmT_slicePoly_eval n zc v g 0
    obtain ⟨ρ₁, hρ₁0, hiso⟩ := cdmT_exists_root_isolated (p := Q) hv hQ0
    obtain ⟨ρ₂, hρ₂0, hup⟩ := cdmT_exists_stay_upper n zc v hz_im
    let ρ : ℝ := min ρ₁ ρ₂
    have hρ0 : 0 < ρ := lt_min hρ₁0 hρ₂0
    have hρ_le₁ : ρ ≤ ρ₁ := min_le_left ρ₁ ρ₂
    have hρ_le₂ : ρ ≤ ρ₂ := min_le_right ρ₁ ρ₂
    have hlim : ∀ i : Fin (D + 1),
        Tendsto (fun k : ℕ => (cdmT_slicePoly n zc v (u k)).coeff (i : ℕ)) atTop
          (𝓝 ((cdmT_slicePoly n zc v g).coeff (i : ℕ))) := by
      intro i
      exact cdmT_slicePoly_coeff_tendsto zc v u g huD hgD hconv (i : ℕ)
    let c : ℕ → Fin (D + 1) → ℂ := fun k i => (cdmT_slicePoly n zc v (u k)).coeff (i : ℕ)
    let cf : Fin (D + 1) → ℂ := fun i => (cdmT_slicePoly n zc v g).coeff (i : ℕ)
    have hsum_eq_g : (∑ i : Fin (D + 1), Polynomial.monomial (i : ℕ) (cf i)) = Q := by
      dsimp [cf, Q]
      exact (cdmT_slicePoly_eq_partialSum zc v g hgD).symm
    have hroot0 : Polynomial.eval 0 (∑ i : Fin (D + 1), Polynomial.monomial (i : ℕ) (cf i)) = 0 := by
      rw [hsum_eq_g]
      exact hQ0
    have hpunct : ∀ w : ℂ, w ∈ Metric.closedBall 0 ρ → w ≠ 0 →
        Polynomial.eval w (∑ i : Fin (D + 1), Polynomial.monomial (i : ℕ) (cf i)) ≠ 0 := by
      intro w hw hw0
      rw [hsum_eq_g]
      have hw₁ : w ∈ Metric.closedBall 0 ρ₁ := by
        exact (Metric.closedBall_subset_closedBall hρ_le₁) hw
      exact hiso w hw₁ hw0
    obtain ⟨N, hN⟩ := gch_complexHurwitz D c cf hlim (0 : ℂ) (ρ := ρ) hρ0 hroot0 hpunct
    have hnev : ∀ᶠ k in atTop, u k ≠ 0 := cdmT_coeff_tendsto_of_deg_le (n := n) (D := D) u g hconv hg
    have hevge : ∀ᶠ k in atTop, N ≤ k := Filter.eventually_ge_atTop N
    have hevall : ∀ᶠ k in atTop, u k ≠ 0 ∧ N ≤ k := hnev.and hevge
    rw [Filter.eventually_atTop] at hevall
    rcases hevall with ⟨N₀, hN₀⟩
    let k : ℕ := max N₀ N
    have hkprop := hN₀ k (le_max_left N₀ N)
    have huk0 : u k ≠ 0 := hkprop.1
    have hkN : N ≤ k := le_max_right N₀ N
    rcases hN k hkN with ⟨w, hwd, hwroot⟩
    have hwρ : ‖w‖ < ρ := by
      simpa [dist_eq_norm] using hwd
    have hwρ₂ : ‖w‖ < ρ₂ := lt_of_lt_of_le hwρ hρ_le₂
    let z' : Fin n → UpperHalfPlane := fun i => ⟨zc i + w * v i, hup w hwρ₂ i⟩
    have hstabk := hstab k
    cases hstabk with
    | inl hk0 =>
        exact huk0 hk0
    | inr hstable =>
        -- hstable : ∀ z' : Fin n → UpperHalfPlane, aeval (fun i => (z' i : ℂ)) (u k) ≠ 0
        have hcontra : MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z' i : UpperHalfPlane) : ℂ)) (u k) = 0 := by
          have hz'eval : MvPolynomial.aeval (R := ℝ) (fun i : Fin n => zc i + w * v i) (u k) = 0 := by
            have heq : (cdmT_slicePoly n zc v (u k)) = ∑ j : Fin (D + 1),
                Polynomial.monomial (j : ℕ) ((cdmT_slicePoly n zc v (u k)).coeff (j : ℕ)) := by
              exact cdmT_slicePoly_eq_partialSum zc v (u k) (huD k)
            have hwroot' : Polynomial.eval w (cdmT_slicePoly n zc v (u k)) = 0 := by
              -- hwroot is about the c-sum; the c-sum equals the slice
              have hsum_eq_uk : (∑ j : Fin (D + 1), Polynomial.monomial (j : ℕ) (c k j)) =
                  cdmT_slicePoly n zc v (u k) := by
                rw [heq]
              rw [← hsum_eq_uk]
              exact hwroot
            have hslice := cdmT_slicePoly_eval n zc v (u k) w
            simpa using (hslice.symm.trans hwroot')
          simpa [z'] using hz'eval
        exact hstable z' hcontra

end Commons.Analysis.MvPolynomial

open Finsupp Matrix MvPolynomial Polynomial UpperHalfPlane Filter Topology
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Commons.LorentzianPolynomials

/-! # `cdmP_pderiv_stable_of_stable`
If `f` is stable (nonvanishing on the open upper half plane `ℍⁿ`, or zero) then the
formal partial derivative `∂ᵢf` is stable.  The proof follows Wagner (Lemma 2.4(f)):
the degree of the slice of `f` in the direction of `i` is constant over `ℍⁿ⁻¹`
(shown by a scaling limit, which is stable by Hurwitz-type closure), so each slice is
a nonconstant univariate polynomial with all roots in the closed lower half plane, and
the univariate half-plane derivative lemma applies. -/

/-- "slice" polynomial: substitute complex constants `z` in all variables but `i`,
leaving `X` (the univariate variable) in position `i`. -/
def cdmP_pss_slicePoly {n : ℕ} (i : Fin n) (z : Fin n → ℂ) (f : MvPolynomial (Fin n) ℝ) : Polynomial ℂ :=
  MvPolynomial.aeval (R := ℝ)
    (fun j : Fin n => if j = i then Polynomial.X else Polynomial.C (z j)) f

/-- evaluating the slice at `w` evaluates `f` at the point whose `i`-th coordinate is `w`. -/
lemma cdmP_pss_slicePoly_eval {n : ℕ} (i : Fin n) (z : Fin n → ℂ) (f : MvPolynomial (Fin n) ℝ) (w : ℂ) :
    (cdmP_pss_slicePoly i z f).eval w =
      MvPolynomial.aeval (R := ℝ) (fun j : Fin n => if j = i then w else z j) f := by
  classical
  unfold cdmP_pss_slicePoly
  let a : Fin n → Polynomial ℂ := fun j => if j = i then Polynomial.X else Polynomial.C (z j)
  let b : Fin n → ℂ := fun j => if j = i then w else z j
  induction f using MvPolynomial.induction_on with
  | C c => simp [a, b]
  | add p q hp hq => simp [hp, hq, b, Polynomial.eval_add]
  | mul_X p j hp =>
      have hmain : Polynomial.eval w ((MvPolynomial.aeval (R := ℝ) a) (p * MvPolynomial.X j)) =
          (MvPolynomial.aeval (R := ℝ) b) (p * MvPolynomial.X j) := by
        rw [show (MvPolynomial.aeval (R := ℝ) a) (p * MvPolynomial.X j) =
            (MvPolynomial.aeval (R := ℝ) a) p * a j by simp [a]]
        rw [show (MvPolynomial.aeval (R := ℝ) b) (p * MvPolynomial.X j) =
            (MvPolynomial.aeval (R := ℝ) b) p * b j by simp [b]]
        rw [Polynomial.eval_mul]
        rw [hp]
        congr 1
        · by_cases hj : j = i
          · subst j
            simp [a, b]
          · simp [a, b, hj]
      simpa [a, b] using hmain

/-- the derivative of the slice is the slice of the partial derivative -/
lemma cdmP_pss_slicePoly_deriv {n : ℕ} (i : Fin n) (z : Fin n → ℂ) (f : MvPolynomial (Fin n) ℝ) :
    (cdmP_pss_slicePoly i z f).derivative = cdmP_pss_slicePoly i z (MvPolynomial.pderiv i f) := by
  classical
  unfold cdmP_pss_slicePoly
  let a : Fin n → Polynomial ℂ := fun j => if j = i then Polynomial.X else Polynomial.C (z j)
  induction f using MvPolynomial.induction_on with
  | C c => simp [a]
  | add p q hp hq =>
      simp only [map_add, map_add]
      rw [hp, hq]
  | mul_X p j hp =>
      by_cases hj : j = i
      · subst j
        have hpm : (MvPolynomial.aeval (R := ℝ) a) (p * MvPolynomial.X i)
            = (MvPolynomial.aeval (R := ℝ) a) p * a i := by simp [a]
        have hdpm : ((MvPolynomial.pderiv i) (p * MvPolynomial.X i))
            = (MvPolynomial.pderiv i) p * MvPolynomial.X i + p := by
          rw [MvPolynomial.pderiv_mul]
          simp [MvPolynomial.pderiv_X]
        rw [hpm, hdpm]
        rw [Polynomial.derivative_mul]
        rw [map_add]
        simp [a, hp]
      · have hX0 : (MvPolynomial.pderiv i) (MvPolynomial.X j) = (0 : MvPolynomial (Fin n) ℝ) := by
          simp [MvPolynomial.pderiv_X, hj]
        have haC : a j = Polynomial.C (z j) := by simp [a, hj]
        have hpm : (MvPolynomial.aeval (R := ℝ) a) (p * MvPolynomial.X j)
            = (MvPolynomial.aeval (R := ℝ) a) p * a j := by simp [a]
        have hdpm : ((MvPolynomial.pderiv i) (p * MvPolynomial.X j))
            = (MvPolynomial.pderiv i) p * MvPolynomial.X j := by
          rw [MvPolynomial.pderiv_mul]
          simp [hX0]
        rw [hpm, hdpm]
        rw [Polynomial.derivative_mul]
        rw [map_mul, MvPolynomial.aeval_X]
        rw [show derivative ((MvPolynomial.aeval (R := ℝ) a) p) * a j =
            (MvPolynomial.aeval (R := ℝ) a) ((MvPolynomial.pderiv i) p) * a j by rw [hp]]
        have hda0 : (a j).derivative = 0 := by
          rw [haC]
          simp
        rw [hda0, mul_zero, add_zero]

/-- evaluation of a monomial at `z` -/
lemma cdmP_pss_aeval_monomial (n : ℕ) (z : Fin n → ℂ) (m : Fin n →₀ ℕ) (r : ℝ) :
    MvPolynomial.aeval (R := ℝ) z (MvPolynomial.monomial m r) =
      (r : ℂ) * (m.prod fun j k => z j ^ k) := by
  rw [MvPolynomial.aeval_monomial]
  rfl

/-- product over the support of `m`, split at the index `i` -/
lemma cdmP_pss_prod_split (n : ℕ) (m : Fin n →₀ ℕ) (i : Fin n) (a : Fin n → ℂ)
    (hi : i ∈ m.support) :
    (m.prod fun j k => a j ^ k) = (∏ j ∈ m.support.erase i, a j ^ m j) * (a i) ^ m i := by
  classical
  unfold Finsupp.prod
  exact (Finset.prod_erase_mul (s := m.support)
    (f := fun j : Fin n => a j ^ m j) (by simpa using hi)).symm

/-- product of `z`-monomial over all indices of `m`, expressed through coordinate `i` -/
lemma cdmP_pss_prod_eq (n : ℕ) (m : Fin n →₀ ℕ) (i : Fin n) (a : Fin n → ℂ) (e : ℕ)
    (he : m i = e) :
    (m.prod fun j k => a j ^ k) = (a i) ^ e * (∏ j ∈ (m.support.erase i), a j ^ m j) := by
  classical
  by_cases hi : i ∈ m.support
  · rw [cdmP_pss_prod_split n m i a hi, he]
    ring
  · -- i not in support: m i = 0, e = 0 (since he), product over support.erase i = support
    have hmi : m i = 0 := by
      by_contra h
      exact hi (Finsupp.mem_support_iff.mpr h)
    have he0 : e = 0 := by omega
    rw [he0]
    have herase : (m.support.erase i) = m.support := by
      apply Finset.erase_eq_self.mpr hi
    have happly : (a i) ^ 0 = (1 : ℂ) := by simp
    rw [happly, one_mul]
    rw [herase]
    unfold Finsupp.prod
    rfl

/-- evaluation of a support-sum polynomial -/
lemma cdmP_pss_aeval_sum_support (n : ℕ) (z : Fin n → ℂ) (S : Finset (Fin n →₀ ℕ))
    (c : (Fin n →₀ ℕ) → ℝ) :
    MvPolynomial.aeval (R := ℝ) z (∑ m ∈ S, MvPolynomial.monomial m (c m)) =
      ∑ m ∈ S, ((c m : ℝ) : ℂ) * (m.prod fun j k => z j ^ k) := by
  classical
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  exact cdmP_pss_aeval_monomial n z m (c m)

/-- The polynomial `f` equals the support-sum of its monomials. -/
lemma cdmP_pss_support_sum (n : ℕ) (f : MvPolynomial (Fin n) ℝ) :
    f = ∑ m ∈ f.support, MvPolynomial.monomial m (MvPolynomial.coeff m f) := by
  classical
  exact (MvPolynomial.support_sum_monomial_coeff f).symm



/-- coefficient of a sum of monomials -/
lemma cdmP_pss_coeff_sum_monomial (n : ℕ) (T : Finset (Fin n →₀ ℕ)) (c : (Fin n →₀ ℕ) → ℝ)
    (m' : Fin n →₀ ℕ) :
    MvPolynomial.coeff m' (∑ m ∈ T, MvPolynomial.monomial m (c m)) =
      if m' ∈ T then c m' else 0 := by
  classical
  rw [MvPolynomial.coeff_sum]
  by_cases h : m' ∈ T
  · rw [if_pos h]
    rw [Finset.sum_eq_single m']
    · rw [MvPolynomial.coeff_monomial]
      simp
    · intro b hb hbne
      rw [MvPolynomial.coeff_monomial, if_neg]
      exact hbne
    · intro hnot
      exact False.elim (hnot h)
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro b hb
    have hbne : b ≠ m' := by
      intro hb''
      subst b
      exact h hb
    rw [MvPolynomial.coeff_monomial, if_neg hbne]

/-- The top part of `f` in the variable `i`: the sum of the monomials whose exponent of
`X_i` equals the `i`-degree of `f`. -/
noncomputable def cdmP_pss_top (n : ℕ) (i : Fin n) (f : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ m ∈ f.support.filter (fun m => m i = f.degreeOf i), MvPolynomial.monomial m (f.coeff m)

/-- the recession sequence: `u k = (k:ℝ)^(-e) · f(X_1,.., (k:ℝ)·X_i, .., X_n)`, where
`e = degreeOf i f`.  Its coefficientwise limit is `cdmP_pss_top i f`. -/
noncomputable def cdmP_pss_recession (n : ℕ) (i : Fin n) (f : MvPolynomial (Fin n) ℝ) (k : ℕ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ m ∈ f.support,
    MvPolynomial.monomial m (f.coeff m * (((k : ℝ) ^ f.degreeOf i)⁻¹ * (k : ℝ) ^ (m i)))

lemma cdmP_pss_coeff_top (n : ℕ) (i : Fin n) (f : MvPolynomial (Fin n) ℝ) (m' : Fin n →₀ ℕ) :
    MvPolynomial.coeff m' (cdmP_pss_top n i f) =
      if m' i = f.degreeOf i then f.coeff m' else 0 := by
  classical
  unfold cdmP_pss_top
  rw [cdmP_pss_coeff_sum_monomial]
  by_cases h : m' i = f.degreeOf i
  · rw [if_pos h]
    by_cases hs : m' ∈ f.support
    · have hmem : m' ∈ f.support.filter (fun m => m i = f.degreeOf i) := by
        simpa [hs, h]
      rw [if_pos hmem]
    · have hnot : m' ∉ f.support.filter (fun m => m i = f.degreeOf i) := by
        intro hh
        exact hs (Finset.mem_filter.mp hh).1
      rw [if_neg hnot]
      have hc : f.coeff m' = 0 := by
        by_contra hc0
        exact hs (MvPolynomial.mem_support_iff.mpr hc0)
      exact hc.symm
  · rw [if_neg h]
    have hnot : m' ∉ f.support.filter (fun m => m i = f.degreeOf i) := by
      intro hh
      exact h (Finset.mem_filter.mp hh).2
    rw [if_neg hnot]

lemma cdmP_pss_coeff_recession (n : ℕ) (i : Fin n) (f : MvPolynomial (Fin n) ℝ) (k : ℕ) (m' : Fin n →₀ ℕ) :
    MvPolynomial.coeff m' (cdmP_pss_recession n i f k) =
      f.coeff m' * (((k : ℝ) ^ f.degreeOf i)⁻¹ * (k : ℝ) ^ (m' i)) := by
  classical
  unfold cdmP_pss_recession
  rw [cdmP_pss_coeff_sum_monomial]
  by_cases hs : m' ∈ f.support
  · rw [if_pos hs]
  · rw [if_neg hs]
    have hc : f.coeff m' = 0 := by
      by_contra hc0
      exact hs (MvPolynomial.mem_support_iff.mpr hc0)
    simp [hc]

/-- evaluation of `f` at `z`, expanded over the support -/
lemma cdmP_pss_eval_support (n : ℕ) (z : Fin n → ℂ) (f : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.aeval (R := ℝ) z f =
      ∑ m ∈ f.support, ((f.coeff m : ℝ) : ℂ) * (m.prod fun j k => z j ^ k) := by
  classical
  have h := cdmP_pss_aeval_sum_support n z f.support (fun m => f.coeff m)
  rw [← cdmP_pss_support_sum n f] at h
  exact h

/-- product over the support of `m`: scaling the `i`-th factor by `c` -/
lemma cdmP_pss_prod_scale (n : ℕ) (m : Fin n →₀ ℕ) (i : Fin n) (c : ℂ) (a : Fin n → ℂ) :
    (m.prod fun j k => (if j = i then c * a j else a j) ^ k) =
      c ^ (m i) * (m.prod fun j k => a j ^ k) := by
  classical
  by_cases hi : i ∈ m.support
  · have hsplit := cdmP_pss_prod_split n m i (fun j => if j = i then c * a j else a j) hi
    have hsplit' := cdmP_pss_prod_split n m i a hi
    have herase : (∏ j ∈ m.support.erase i, (if j = i then c * a j else a j) ^ m j) =
        ∏ j ∈ m.support.erase i, a j ^ m j := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := by
        intro h
        subst h
        exact (Finset.mem_erase.mp hj).1 rfl
      simp [hji]
    calc
      (m.prod fun j k => (if j = i then c * a j else a j) ^ k)
          = (∏ j ∈ m.support.erase i, (if j = i then c * a j else a j) ^ m j) *
              (if i = i then c * a i else a i) ^ m i := hsplit
      _ = (∏ j ∈ m.support.erase i, a j ^ m j) * (c * a i) ^ m i := by
            rw [herase]
            simp
      _ = (∏ j ∈ m.support.erase i, a j ^ m j) * (c ^ (m i) * (a i) ^ (m i)) := by
            rw [mul_pow]
      _ = c ^ (m i) * ((∏ j ∈ m.support.erase i, a j ^ m j) * (a i) ^ (m i)) := by ring
      _ = c ^ (m i) * (m.prod fun j k => a j ^ k) := by
            rw [hsplit']
  · have hmi : m i = 0 := by
      by_contra h
      exact hi (Finsupp.mem_support_iff.mpr h)
    have happly : (m.prod fun j k => (if j = i then c * a j else a j) ^ k) =
        m.prod fun j k => a j ^ k := by
      unfold Finsupp.prod
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := by
        intro h
        subst h
        exact hi hj
      simp [hji]
    rw [happly, hmi]
    simp

/-- evaluation of the recession sequence: scaling `X_i` by `k` in `f` -/
lemma cdmP_pss_recession_eval (n : ℕ) (i : Fin n) (f : MvPolynomial (Fin n) ℝ) (k : ℕ)
    (zc : Fin n → ℂ) :
    MvPolynomial.aeval (R := ℝ) zc (cdmP_pss_recession n i f k) =
      (((k : ℝ) : ℂ) ^ f.degreeOf i)⁻¹ *
        MvPolynomial.aeval (R := ℝ) (fun j : Fin n => if j = i then ((k : ℝ) : ℂ) * zc j else zc j) f := by
  classical
  let zs : Fin n → ℂ := fun j => if j = i then ((k : ℝ) : ℂ) * zc j else zc j
  have hL : MvPolynomial.aeval (R := ℝ) zc (cdmP_pss_recession n i f k) =
      ∑ m ∈ f.support,
        (((f.coeff m * (((k : ℝ) ^ f.degreeOf i)⁻¹ * (k : ℝ) ^ (m i))) : ℝ) : ℂ) *
          (m.prod fun j kk => zc j ^ kk) := by
    unfold cdmP_pss_recession
    rw [cdmP_pss_aeval_sum_support]
  have hR : MvPolynomial.aeval (R := ℝ) zs f =
      ∑ m ∈ f.support, ((f.coeff m : ℝ) : ℂ) *
        (((k : ℝ) : ℂ) ^ (m i) * (m.prod fun j kk => zc j ^ kk)) := by
    rw [cdmP_pss_eval_support]
    apply Finset.sum_congr rfl
    intro m hm
    congr 1
    have hp := cdmP_pss_prod_scale n m i ((k : ℝ) : ℂ) zc
    have hzs : (fun j : Fin n => (if j = i then ((k : ℝ) : ℂ) * zc j else zc j)) = zs := by
      rfl
    rw [← hzs]
    rw [hp]
  have hMain : (∑ m ∈ f.support,
        (((f.coeff m * (((k : ℝ) ^ f.degreeOf i)⁻¹ * (k : ℝ) ^ (m i))) : ℝ) : ℂ) *
          (m.prod fun j kk => zc j ^ kk))
        = (((k : ℝ) : ℂ) ^ f.degreeOf i)⁻¹ *
            (∑ m ∈ f.support, ((f.coeff m : ℝ) : ℂ) *
              (((k : ℝ) : ℂ) ^ (m i) * (m.prod fun j kk => zc j ^ kk))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    norm_num <;> ring
  calc
    MvPolynomial.aeval (R := ℝ) zc (cdmP_pss_recession n i f k)
        = ∑ m ∈ f.support,
            (((f.coeff m * (((k : ℝ) ^ f.degreeOf i)⁻¹ * (k : ℝ) ^ (m i))) : ℝ) : ℂ) *
              (m.prod fun j kk => zc j ^ kk) := hL
    _ = (((k : ℝ) : ℂ) ^ f.degreeOf i)⁻¹ *
            (∑ m ∈ f.support, ((f.coeff m : ℝ) : ℂ) *
              (((k : ℝ) : ℂ) ^ (m i) * (m.prod fun j kk => zc j ^ kk))) := hMain
    _ = (((k : ℝ) : ℂ) ^ f.degreeOf i)⁻¹ * MvPolynomial.aeval (R := ℝ) zs f := by
          rw [hR]
    _ = (((k : ℝ) : ℂ) ^ f.degreeOf i)⁻¹ *
          MvPolynomial.aeval (R := ℝ) (fun j : Fin n => if j = i then ((k : ℝ) : ℂ) * zc j else zc j) f := by
          rfl

/-- The recession sequence stays stable when `f` is stable. -/
lemma cdmP_pss_recession_stable (n : ℕ) (i : Fin n) (f : MvPolynomial (Fin n) ℝ)
    (hd : 1 ≤ f.degreeOf i) (hstab : IsStable f) (k : ℕ) :
    cdmP_pss_recession n i f k = 0 ∨
      ∀ z : Fin n → ℍ,
        MvPolynomial.aeval (R := ℝ) (fun j : Fin n => ((z j : ℍ) : ℂ)) (cdmP_pss_recession n i f k) ≠ 0 := by
  classical
  by_cases hf0 : f = 0
  · left
    ext m
    rw [cdmP_pss_coeff_recession, hf0]
    simp
  · rcases hstab with h0 | hnv
    · exact False.elim (hf0 h0)
    · by_cases hk : k = 0
      · subst k
        left
        ext m
        rw [cdmP_pss_coeff_recession]
        have hpow0 : (0 : ℝ) ^ f.degreeOf i = 0 := by
          apply zero_pow
          omega
        simp [hpow0]
      · right
        have hkpos : 0 < (k : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hk)
        intro z
        let zhat : Fin n → ℍ := fun j =>
          if h : j = i then ⟨(k : ℝ) • ((z i : ℍ) : ℂ), by
            rw [Complex.smul_im]
            exact mul_pos hkpos (UpperHalfPlane.im_pos (z i))⟩
          else z j
        have hzhatc (j : Fin n) : ((zhat j : ℍ) : ℂ) =
            if j = i then (k : ℝ) • ((z i : ℍ) : ℂ) else ((z j : ℍ) : ℂ) := by
          dsimp [zhat]
          by_cases hj : j = i
          · subst j
            simp
          · simp [hj]
        have hstable : MvPolynomial.aeval (R := ℝ) (fun j : Fin n => ((zhat j : ℍ) : ℂ)) f ≠ 0 := hnv zhat
        -- identity: aeval z (recession) = ((k:ℝ)^e : ℂ)⁻¹ * aeval zhat f
        have hev0 := cdmP_pss_recession_eval n i f k (fun j : Fin n => ((z j : ℍ) : ℂ))
        have hfun : (fun j : Fin n => if j = i then ((k : ℝ) : ℂ) * ((z j : ℍ) : ℂ) else ((z j : ℍ) : ℂ))
            = (fun j : Fin n => ((zhat j : ℍ) : ℂ)) := by
          funext j
          by_cases hj : j = i
          · subst j
            dsimp [zhat]
            simp
          · simp [hj, zhat]
        have hev : MvPolynomial.aeval (R := ℝ) (fun j : Fin n => ((z j : ℍ) : ℂ))
              (cdmP_pss_recession n i f k) =
            (((k : ℝ) : ℂ) ^ f.degreeOf i)⁻¹ * MvPolynomial.aeval (R := ℝ)
              (fun j : Fin n => ((zhat j : ℍ) : ℂ)) f := by
          rw [hev0, hfun]
        rw [hev]
        intro hz0
        have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
        have hkℂ : ((k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hkne
        have hpowℂ : (((k : ℝ) : ℂ) ^ f.degreeOf i) ≠ 0 := pow_ne_zero _ hkℂ
        have hinv : (((k : ℝ) : ℂ) ^ f.degreeOf i)⁻¹ ≠ 0 := inv_ne_zero hpowℂ
        exact hstable ((mul_eq_zero.mp hz0).resolve_left hinv)

/-- `(k:ℝ)^p⁻¹ → 0` for a positive power -/
lemma cdmP_pss_tendsto_inv_pow (p : ℕ) (hp : 0 < p) :
    Tendsto (fun k : ℕ => (((k : ℝ) ^ p)⁻¹)) atTop (𝓝 0) := by
  classical
  have hbase : Tendsto (fun k : ℕ => ((k : ℝ)⁻¹)) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (a := (0 : ℝ))
    (g := fun _ : ℕ => (0 : ℝ)) (h := fun k : ℕ => (k : ℝ)⁻¹) tendsto_const_nhds hbase ?_ ?_
  · apply Eventually.of_forall
    intro k
    exact inv_nonneg.mpr (pow_nonneg (by exact_mod_cast (Nat.zero_le k)) p)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hkp : (k : ℝ) ≤ (k : ℝ) ^ p := by
      calc (k : ℝ) = (k : ℝ) ^ 1 := by rw [pow_one]
      _ ≤ (k : ℝ) ^ p := by
            apply pow_le_pow_right₀ hk1
            omega
    have hkpos : 0 < (k : ℝ) := by nlinarith
    exact (inv_le_inv₀ (a := (k : ℝ) ^ p) (b := k) (pow_pos hkpos p) hkpos).mpr hkp

lemma cdmP_pss_support_subset_recession (n : ℕ) (i : Fin n) (f : MvPolynomial (Fin n) ℝ) (k : ℕ) :
    (cdmP_pss_recession n i f k).support ⊆ f.support := by
  classical
  intro m hm
  have hc : MvPolynomial.coeff m (cdmP_pss_recession n i f k) ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  by_contra hnot
  have hc0 : MvPolynomial.coeff m f = 0 := by
    by_contra hc0'
    exact hnot (MvPolynomial.mem_support_iff.mpr hc0')
  rw [cdmP_pss_coeff_recession, hc0] at hc
  simp at hc

lemma cdmP_pss_support_subset_top (n : ℕ) (i : Fin n) (f : MvPolynomial (Fin n) ℝ) :
    (cdmP_pss_top n i f).support ⊆ f.support := by
  classical
  intro m hm
  have hc : MvPolynomial.coeff m (cdmP_pss_top n i f) ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  by_cases hmi : m i = f.degreeOf i
  · rw [cdmP_pss_coeff_top, if_pos hmi] at hc
    exact MvPolynomial.mem_support_iff.mpr hc
  · rw [cdmP_pss_coeff_top, if_neg hmi] at hc
    simp at hc

/-- coefficientwise convergence of the recession sequence to the top part -/
lemma cdmP_pss_tendsto_coeff_top (n : ℕ) (i : Fin n) (f : MvPolynomial (Fin n) ℝ) (m' : Fin n →₀ ℕ) :
    Tendsto (fun k : ℕ => MvPolynomial.coeff m' (cdmP_pss_recession n i f k)) atTop
      (𝓝 (MvPolynomial.coeff m' (cdmP_pss_top n i f))) := by
  classical
  by_cases hmi : m' i = f.degreeOf i
  · -- ratio → 1
    have htop : MvPolynomial.coeff m' (cdmP_pss_top n i f) = f.coeff m' := by
      rw [cdmP_pss_coeff_top, if_pos hmi]
    have hconv : ∀ᶠ k in atTop,
        (fun _ : ℕ => f.coeff m') k = MvPolynomial.coeff m' (cdmP_pss_recession n i f k) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
      have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.succ_le_iff.mp hk))
      rw [cdmP_pss_coeff_recession]
      have h1 : (((k : ℝ) ^ f.degreeOf i)⁻¹ * (k : ℝ) ^ (m' i)) = 1 := by
        rw [hmi]
        exact inv_mul_cancel₀ (pow_ne_zero _ hkne)
      simp [h1]
    have ht : Tendsto (fun k : ℕ => MvPolynomial.coeff m' (cdmP_pss_recession n i f k)) atTop
        (𝓝 (f.coeff m')) :=
      (tendsto_const_nhds (x := f.coeff m')).congr' hconv
    simpa [htop] using ht
  · -- m' i ≠ degree: coefficient → 0
    have htop : MvPolynomial.coeff m' (cdmP_pss_top n i f) = 0 := by
      rw [cdmP_pss_coeff_top, if_neg hmi]
    rw [htop]
    by_cases hlt : m' i < f.degreeOf i
    · -- positive power ratio → 0
      have hp : 0 < f.degreeOf i - m' i := Nat.sub_pos_of_lt hlt
      have ht0 : Tendsto (fun k : ℕ => (((k : ℝ) ^ (f.degreeOf i - m' i))⁻¹)) atTop (𝓝 0) :=
        cdmP_pss_tendsto_inv_pow (f.degreeOf i - m' i) hp
      have ht' : Tendsto (fun k : ℕ => f.coeff m' * (((k : ℝ) ^ (f.degreeOf i - m' i))⁻¹))
          atTop (𝓝 (0 : ℝ)) := by
        simpa using (ht0.const_mul (f.coeff m'))
      have hcv : ∀ᶠ k in atTop,
          (fun kk : ℕ => f.coeff m' * (((kk : ℝ) ^ (f.degreeOf i - m' i))⁻¹)) k =
            MvPolynomial.coeff m' (cdmP_pss_recession n i f k) := by
        filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
        have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.succ_le_iff.mp hk))
        rw [cdmP_pss_coeff_recession]
        have hsplit' : (f.degreeOf i - m' i) + m' i = f.degreeOf i := by omega
        have h1 : ((k : ℝ) ^ f.degreeOf i)⁻¹ * (k : ℝ) ^ (m' i) =
            ((k : ℝ) ^ (f.degreeOf i - m' i))⁻¹ := by
          rw [← hsplit']
          rw [pow_add]
          rw [_root_.mul_inv_rev]
          field_simp [pow_ne_zero (m' i) hkne]
          rw [show (f.degreeOf i - m' i + m' i - m' i) = (f.degreeOf i - m' i) by omega]
        rw [h1]
      exact ht'.congr' hcv
    · have hgt : m' i > f.degreeOf i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hmi)
      -- coefficient of f at m' is zero
      have hc0 : f.coeff m' = 0 := by
        by_contra hc
        have hsup : m' ∈ f.support := MvPolynomial.mem_support_iff.mpr hc
        have hle : m' i ≤ f.degreeOf i := by
          exact MvPolynomial.monomial_le_degreeOf i hsup
        omega
      have hcv : ∀ k : ℕ, MvPolynomial.coeff m' (cdmP_pss_recession n i f k) = 0 := by
        intro k
        rw [cdmP_pss_coeff_recession, hc0]
        simp
      simpa using ((tendsto_const_nhds (x := (0 : ℝ))).congr'
        (Eventually.of_forall (fun k => (hcv k).symm)))


/-- The top part of a stable polynomial (in the variable `i`) is stable. -/
lemma cdmP_pss_top_stable (n : ℕ) (i : Fin n) (f : MvPolynomial (Fin n) ℝ)
    (hd : 1 ≤ f.degreeOf i) (hstab : IsStable f) :
    cdmP_pss_top n i f = 0 ∨
      ∀ z : Fin n → ℍ,
        MvPolynomial.aeval (R := ℝ) (fun j : Fin n => ((z j : ℍ) : ℂ)) (cdmP_pss_top n i f) ≠ 0 := by
  classical
  let u : ℕ → MvPolynomial (Fin n) ℝ := fun k => cdmP_pss_recession n i f k
  have huD : ∀ k : ℕ, (u k).totalDegree ≤ f.totalDegree := by
    intro k
    dsimp [u]
    apply MvPolynomial.totalDegree_le_of_support_subset
    exact cdmP_pss_support_subset_recession n i f k
  have hgD : (cdmP_pss_top n i f).totalDegree ≤ f.totalDegree := by
    apply MvPolynomial.totalDegree_le_of_support_subset
    exact cdmP_pss_support_subset_top n i f
  have hconv : ∀ m : Fin n →₀ ℕ, Tendsto (fun k : ℕ => (u k).coeff m) atTop
      (𝓝 ((cdmP_pss_top n i f).coeff m)) := by
    intro m
    dsimp [u]
    exact cdmP_pss_tendsto_coeff_top n i f m
  have hstab' : ∀ k : ℕ, (u k) = 0 ∨ ∀ z : Fin n → ℍ,
      MvPolynomial.aeval (R := ℝ) (fun j : Fin n => ((z j : ℍ) : ℂ)) (u k) ≠ 0 := by
    intro k
    dsimp [u]
    exact cdmP_pss_recession_stable n i f hd hstab k
  exact Commons.Analysis.MvPolynomial.cdmT_isStable_tendsto_of_degree_le n f.totalDegree u (cdmP_pss_top n i f)
    huD hgD hconv hstab'

/-- `∂ᵢf ≠ 0` forces positive `i`-degree -/
lemma cdmP_pss_degreeOf_of_pderiv_ne (n : ℕ) (i : Fin n) (f : MvPolynomial (Fin n) ℝ)
    (hp : MvPolynomial.pderiv i f ≠ 0) : 1 ≤ f.degreeOf i := by
  classical
  by_contra h
  have hle : f.degreeOf i ≤ 0 := by omega
  have hd0 : f.degreeOf i = 0 := le_antisymm hle (Nat.zero_le _)
  apply hp
  ext m
  by_cases hsup : m + (Finsupp.single i 1 : Fin n →₀ ℕ) ∈ f.support
  · have hmi : (m + (Finsupp.single i 1 : Fin n →₀ ℕ)) i ≤ f.degreeOf i := by
      exact MvPolynomial.monomial_le_degreeOf i hsup
    have hval : (m + (Finsupp.single i 1 : Fin n →₀ ℕ)) i = m i + 1 := by
      rw [Finsupp.add_apply, Finsupp.single_eq_same]
    rw [hd0] at hmi
    omega
  · have hc0 : f.coeff (m + (Finsupp.single i 1 : Fin n →₀ ℕ)) = 0 := by
      by_contra hc
      exact hsup (MvPolynomial.mem_support_iff.mpr hc)
    have hpd : MvPolynomial.coeff m (MvPolynomial.pderiv i f) = 0 := by
      rw [MvPolynomial.coeff_pderiv, hc0]
      simp
    simp [hpd]

lemma cdmP_pss_prod_erase_C (n : ℕ) (zc : Fin n → ℂ) (m : Fin n →₀ ℕ) (i : Fin n) :
    (∏ j ∈ (m.support.erase i), (Polynomial.C (zc j) : Polynomial ℂ) ^ m j) =
      Polynomial.C (∏ j ∈ (m.support.erase i), zc j ^ m j) := by
  classical
  calc
    (∏ j ∈ (m.support.erase i), (Polynomial.C (zc j) : Polynomial ℂ) ^ m j)
        = ∏ j ∈ (m.support.erase i), Polynomial.C (zc j ^ m j) := by
            apply Finset.prod_congr rfl
            intro j hj
            exact (map_pow (f := (Polynomial.C : ℂ →+* Polynomial ℂ)) (a := zc j) (n := m j)).symm
    _ = Polynomial.C (∏ j ∈ (m.support.erase i), zc j ^ m j) := by
            exact (map_prod (g := (Polynomial.C : ℂ →+* Polynomial ℂ))
              (f := fun j : Fin n => zc j ^ m j) (s := (m.support.erase i))).symm

/-- substitute `X_i ↦ X`, others ↦ constants: image of a monomial -/
lemma cdmP_pss_aeval_sigma_monomial (n : ℕ) (i : Fin n) (zc : Fin n → ℂ) (m : Fin n →₀ ℕ) (r : ℝ) :
    MvPolynomial.aeval (R := ℝ) (fun j : Fin n =>
        if j = i then Polynomial.X else Polynomial.C (zc j)) (MvPolynomial.monomial m r)
      = Polynomial.C (((r : ℝ) : ℂ) * ∏ j ∈ (m.support.erase i), zc j ^ m j) *
          Polynomial.X ^ (m i) := by
  classical
  rw [MvPolynomial.aeval_monomial]
  have hprod : m.prod (fun j k => (if j = i then Polynomial.X else Polynomial.C (zc j)) ^ k) =
      Polynomial.C (∏ j ∈ (m.support.erase i), zc j ^ m j) * Polynomial.X ^ (m i) := by
    by_cases hi : i ∈ m.support
    · have hsplit : (m.prod fun j k => (if j = i then Polynomial.X else Polynomial.C (zc j)) ^ k) =
          (∏ j ∈ m.support.erase i, (if j = i then Polynomial.X else Polynomial.C (zc j)) ^ m j) *
            (if i = i then Polynomial.X else Polynomial.C (zc i)) ^ m i := by
          unfold Finsupp.prod
          exact (Finset.prod_erase_mul (s := m.support)
            (f := fun j : Fin n => (if j = i then Polynomial.X else Polynomial.C (zc j)) ^ m j)
            hi).symm
      rw [hsplit]
      have herase : (∏ j ∈ m.support.erase i, (if j = i then Polynomial.X else Polynomial.C (zc j)) ^ m j) =
          ∏ j ∈ m.support.erase i, (Polynomial.C (zc j) : Polynomial ℂ) ^ m j := by
        apply Finset.prod_congr rfl
        intro j hj
        have hji : j ≠ i := by
          intro h
          subst h
          exact (Finset.mem_erase.mp hj).1 rfl
        simp [hji]
      rw [herase]
      rw [cdmP_pss_prod_erase_C n zc m i]
      simp
    · have hmi : m i = 0 := by
        by_contra h
        exact hi (Finsupp.mem_support_iff.mpr h)
      have happly : (m.prod fun j k => (if j = i then Polynomial.X else Polynomial.C (zc j)) ^ k) =
          (∏ j ∈ m.support, (Polynomial.C (zc j) : Polynomial ℂ) ^ m j) := by
        unfold Finsupp.prod
        apply Finset.prod_congr rfl
        intro j hj
        have hji : j ≠ i := by
          intro h
          subst h
          exact hi hj
        simp [hji]
      rw [happly]
      have herase : (m.support.erase i) = m.support := by
        apply Finset.erase_eq_self.mpr hi
      rw [← herase]
      rw [cdmP_pss_prod_erase_C n zc m i]
      rw [hmi]
      simp
  rw [hprod]
  rw [show (algebraMap ℝ (Polynomial ℂ) r) = Polynomial.C (((r : ℝ) : ℂ)) by simp]
  rw [← mul_assoc]
  rw [← Polynomial.C_mul]

/-- coefficient of `X^e` in the slice of a monomial -/
lemma cdmP_pss_slice_monomial_coeff (n : ℕ) (i : Fin n) (zc : Fin n → ℂ) (m : Fin n →₀ ℕ) (r : ℝ) (e : ℕ) :
    (MvPolynomial.aeval (R := ℝ) (fun j : Fin n =>
        if j = i then Polynomial.X else Polynomial.C (zc j)) (MvPolynomial.monomial m r)).coeff e =
      if m i = e then ((r : ℝ) : ℂ) * (∏ j ∈ (m.support.erase i), zc j ^ m j) else 0 := by
  classical
  rw [cdmP_pss_aeval_sigma_monomial]
  by_cases h : m i = e
  · rw [if_pos h]
    rw [← h]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp
  · rw [if_neg h]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    have h' : ¬ e = m i := by exact fun he => h he.symm
    simp [h']

/-- coefficient of `X^e` in the slice of `f` -/
lemma cdmP_pss_slice_coeff_formula (n : ℕ) (i : Fin n) (zc : Fin n → ℂ) (f : MvPolynomial (Fin n) ℝ) (e : ℕ) :
    (cdmP_pss_slicePoly i zc f).coeff e =
      ∑ m ∈ f.support.filter (fun m => m i = e),
        ((f.coeff m : ℝ) : ℂ) * (∏ j ∈ (m.support.erase i), zc j ^ m j) := by
  classical
  unfold cdmP_pss_slicePoly
  conv_lhs => rw [cdmP_pss_support_sum n f]
  rw [map_sum]
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  rw [cdmP_pss_slice_monomial_coeff]

/-- evaluation of the top part at `zc` equals `(zc i)^e` times the `e`-coefficient of the slice -/
lemma cdmP_pss_aeval_top (n : ℕ) (i : Fin n) (zc : Fin n → ℂ) (f : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.aeval (R := ℝ) zc (cdmP_pss_top n i f) =
      (zc i) ^ (f.degreeOf i) * (cdmP_pss_slicePoly i zc f).coeff (f.degreeOf i) := by
  classical
  let e : ℕ := f.degreeOf i
  have hL : MvPolynomial.aeval (R := ℝ) zc (cdmP_pss_top n i f) =
      ∑ m ∈ f.support.filter (fun m => m i = e),
        ((f.coeff m : ℝ) : ℂ) * (m.prod fun j k => zc j ^ k) := by
    -- cdmP_pss_top is the sum over the filtered support of monomials
    have hss : cdmP_pss_top n i f = ∑ m ∈ f.support.filter (fun m => m i = f.degreeOf i),
        MvPolynomial.monomial m (f.coeff m) := by
      rfl
    dsimp [e]
    rw [hss]
    exact cdmP_pss_aeval_sum_support n zc (f.support.filter (fun m => m i = f.degreeOf i))
      (fun m => f.coeff m)
  have hR : (cdmP_pss_slicePoly i zc f).coeff e =
      ∑ m ∈ f.support.filter (fun m => m i = e),
        ((f.coeff m : ℝ) : ℂ) * (∏ j ∈ (m.support.erase i), zc j ^ m j) := by
    dsimp [e]
    exact cdmP_pss_slice_coeff_formula n i zc f (f.degreeOf i)
  calc
    MvPolynomial.aeval (R := ℝ) zc (cdmP_pss_top n i f)
        = ∑ m ∈ f.support.filter (fun m => m i = e),
            ((f.coeff m : ℝ) : ℂ) * (m.prod fun j k => zc j ^ k) := hL
    _ = ∑ m ∈ f.support.filter (fun m => m i = e),
            ((f.coeff m : ℝ) : ℂ) * ((zc i) ^ e * (∏ j ∈ (m.support.erase i), zc j ^ m j)) := by
          apply Finset.sum_congr rfl
          intro m hm
          have hme : m i = e := (Finset.mem_filter.mp hm).2
          rw [cdmP_pss_prod_eq n m i zc e hme]
    _ = (zc i) ^ e * ∑ m ∈ f.support.filter (fun m => m i = e),
            ((f.coeff m : ℝ) : ℂ) * (∏ j ∈ (m.support.erase i), zc j ^ m j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          ring
    _ = (zc i) ^ e * (cdmP_pss_slicePoly i zc f).coeff e := by rw [hR]
    _ = (zc i) ^ (f.degreeOf i) * (cdmP_pss_slicePoly i zc f).coeff (f.degreeOf i) := by
          dsimp [e]


/-- a nonzero polynomial has a nonzero coefficient -/
lemma cdmP_pss_exists_coeff_ne_zero (n : ℕ) (f : MvPolynomial (Fin n) ℝ) (hf : f ≠ 0) :
    ∃ m : Fin n →₀ ℕ, f.coeff m ≠ 0 := by
  classical
  by_contra h
  apply hf
  ext m
  have h0 : f.coeff m = 0 := by
    by_contra hc
    exact h ⟨m, hc⟩
  simp [h0]

/-- the top part of a nonzero polynomial is nonzero -/
lemma cdmP_pss_top_ne_zero_of_ne_zero (n : ℕ) (i : Fin n) (f : MvPolynomial (Fin n) ℝ) (hf : f ≠ 0) :
    cdmP_pss_top n i f ≠ 0 := by
  classical
  rcases cdmP_pss_exists_coeff_ne_zero n f hf with ⟨m, hm⟩
  have hsup : m ∈ f.support := MvPolynomial.mem_support_iff.mpr hm
  have hne_supp : f.support.Nonempty := ⟨m, hsup⟩
  rcases Finset.exists_mem_eq_sup (s := f.support) hne_supp (fun m : Fin n →₀ ℕ => m i)
    with ⟨m₀, hm₀, hsupval⟩
  have hme : m₀ i = f.degreeOf i := by
    rw [MvPolynomial.degreeOf_eq_sup]
    exact hsupval.symm
  have hc : (cdmP_pss_top n i f).coeff m₀ ≠ 0 := by
    rw [cdmP_pss_coeff_top, if_pos hme]
    exact MvPolynomial.mem_support_iff.mp hm₀
  intro hL0
  rw [hL0] at hc
  simp at hc


/-- `∂ᵢf` evaluated at `z` equals the derivative of the slice of `f` at `z`, evaluated at `zᵢ` -/
lemma cdmP_pss_pderiv_eval_slice (n : ℕ) (i : Fin n) (z : Fin n → ℍ) (f : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.aeval (R := ℝ) (fun j : Fin n => ((z j : ℍ) : ℂ)) (MvPolynomial.pderiv i f) =
      (cdmP_pss_slicePoly i (fun j : Fin n => ((z j : ℍ) : ℂ)) f).derivative.eval ((z i : ℍ) : ℂ) := by
  classical
  have hder := cdmP_pss_slicePoly_deriv i (fun j : Fin n => ((z j : ℍ) : ℂ)) f
  have heval := cdmP_pss_slicePoly_eval i (fun j : Fin n => ((z j : ℍ) : ℂ)) (MvPolynomial.pderiv i f)
    ((z i : ℍ) : ℂ)
  calc
    MvPolynomial.aeval (R := ℝ) (fun j : Fin n => ((z j : ℍ) : ℂ)) (MvPolynomial.pderiv i f)
        = (cdmP_pss_slicePoly i (fun j : Fin n => ((z j : ℍ) : ℂ)) (MvPolynomial.pderiv i f)).eval
            ((z i : ℍ) : ℂ) := by
            rw [heval]
            apply congrArg (fun g : Fin n → ℂ =>
              MvPolynomial.aeval (R := ℝ) g (MvPolynomial.pderiv i f))
            funext j
            by_cases hj : j = i <;> simp [hj]
    _ = (cdmP_pss_slicePoly i (fun j : Fin n => ((z j : ℍ) : ℂ)) f).derivative.eval
            ((z i : ℍ) : ℂ) := by
            rw [hder]


theorem cdmP_pderiv_stable_of_stable {n : ℕ} (i : Fin n) (f : MvPolynomial (Fin n) ℝ)
    (hf : Commons.LorentzianPolynomials.IsStable f) :
    Commons.LorentzianPolynomials.IsStable (MvPolynomial.pderiv i f) := by
  classical
  by_cases hp0 : MvPolynomial.pderiv i f = 0
  · exact Or.inl hp0
  · right
    have hf0 : f ≠ 0 := by
      intro hfz
      apply hp0
      rw [hfz]
      simp
    have hstab : ∀ z : Fin n → ℍ,
        MvPolynomial.aeval (R := ℝ) (fun j : Fin n => ((z j : ℍ) : ℂ)) f ≠ 0 := by
      rcases hf with h0 | hnz
      · exact False.elim (hf0 h0)
      · exact hnz
    intro z
    change MvPolynomial.aeval (R := ℝ) (fun j : Fin n => ((z j : ℍ) : ℂ))
      (MvPolynomial.pderiv i f) ≠ 0
    by_contra hnz0
    let zc : Fin n → ℂ := fun j => ((z j : ℍ) : ℂ)
    have h0' : MvPolynomial.aeval (R := ℝ) (fun j : Fin n => ((z j : ℍ) : ℂ))
        (MvPolynomial.pderiv i f) = 0 := by
      simpa using hnz0
    -- slice polynomial
    let P : Polynomial ℂ := cdmP_pss_slicePoly i zc f
    have hPne : P ≠ 0 := by
      intro hP0
      have hv : P.eval (zc i) = 0 := by rw [hP0]; simp
      have hslice := cdmP_pss_slicePoly_eval i zc f (zc i)
      have hstabz := hstab z
      have hz' : MvPolynomial.aeval (R := ℝ) zc f ≠ 0 := by simpa [zc] using hstabz
      have hzeq : P.eval (zc i) = MvPolynomial.aeval (R := ℝ) zc f := by
        rw [hslice]
        apply congrArg (fun g : Fin n → ℂ => MvPolynomial.aeval (R := ℝ) g f)
        funext j
        by_cases hj : j = i <;> simp [hj]
      exact hz' (by rw [← hzeq]; exact hv)
    have hPstab : ∀ u : ℍ, P.eval (u : ℂ) ≠ 0 := by
      intro u
      let pt : Fin n → ℍ := fun j => if j = i then u else z j
      have hpt := hstab pt
      have hslice := cdmP_pss_slicePoly_eval i zc f (u : ℂ)
      have hfun : (fun j : Fin n => if j = i then (u : ℂ) else zc j) =
          (fun j : Fin n => ((pt j : ℍ) : ℂ)) := by
        funext j
        dsimp [pt, zc]
        by_cases hj : j = i
        · subst j
          simp
        · simp [hj]
      rw [hslice, hfun]
      simpa using hpt
    have hder : P.derivative.eval (zc i) = 0 := by
      have hpe := cdmP_pss_pderiv_eval_slice n i z f
      rw [← hpe]
      exact h0'
    have hU := Commons.Analysis.Complex.Polynomial.deriv_stable_of_stable P hPne hPstab
    rcases hU with hPd0 | hPdz
    · -- P is constant; the top part of f vanishes at z, contradicting its stability
      have hd1 : 1 ≤ f.degreeOf i := cdmP_pss_degreeOf_of_pderiv_ne n i f hp0
      have hLstab := cdmP_pss_top_stable n i f hd1 hf
      have hLne : cdmP_pss_top n i f ≠ 0 := cdmP_pss_top_ne_zero_of_ne_zero n i f hf0
      rcases hLstab with hL0 | hLz
      · exact False.elim (hLne hL0)
      · have hLz' : MvPolynomial.aeval (R := ℝ) zc (cdmP_pss_top n i f) ≠ 0 := by
          have := hLz z
          simpa [zc] using this
        have hPd0' : P.natDegree = 0 := (Polynomial.derivative_eq_zero (R := ℂ)).mp hPd0
        have hPcoeff : P.coeff (f.degreeOf i) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          rw [hPd0']
          exact hd1
        have hid := cdmP_pss_aeval_top n i zc f
        have hzero : MvPolynomial.aeval (R := ℝ) zc (cdmP_pss_top n i f) = 0 := by
          rw [hid]
          dsimp [P] at hPcoeff
          rw [hPcoeff]
          simp
        exact False.elim (hLz' hzero)
    · -- the derivative of the slice does not vanish on ℍ
      have hE : P.derivative.eval (zc i) ≠ 0 := by
        have := hPdz (z i)
        simpa [zc] using this
      exact False.elim (hE hder)


end Commons.LorentzianPolynomials

open Finsupp Matrix MvPolynomial Polynomial UpperHalfPlane Topology Set

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Commons.LorentzianPolynomials

noncomputable section

/-- "slice" polynomial: substitute complex constants `z` in all variables but `i` -/
def cdmD_slicePoly {n : ℕ} (i : Fin n) (z : Fin n → ℂ) (f : MvPolynomial (Fin n) ℝ) : Polynomial ℂ :=
  MvPolynomial.aeval (R := ℝ)
    (fun j : Fin n => if j = i then Polynomial.X else Polynomial.C (z j)) f

/-- evaluating the slice at `w` evaluates `f` at the point whose `i`-th coordinate is `w`. -/
lemma cdmD_slicePoly_eval {n : ℕ} (i : Fin n) (z : Fin n → ℂ) (f : MvPolynomial (Fin n) ℝ) (w : ℂ) :
    (cdmD_slicePoly i z f).eval w =
      MvPolynomial.aeval (R := ℝ) (fun j : Fin n => if j = i then w else z j) f := by
  classical
  unfold cdmD_slicePoly
  let a : Fin n → Polynomial ℂ := fun j => if j = i then Polynomial.X else Polynomial.C (z j)
  let b : Fin n → ℂ := fun j => if j = i then w else z j
  induction f using MvPolynomial.induction_on with
  | C c => simp [a, b]
  | add p q hp hq => simp [hp, hq, b, Polynomial.eval_add]
  | mul_X p j hp =>
      have hmain : Polynomial.eval w ((MvPolynomial.aeval (R := ℝ) a) (p * MvPolynomial.X j)) =
          (MvPolynomial.aeval (R := ℝ) b) (p * MvPolynomial.X j) := by
        rw [show (MvPolynomial.aeval (R := ℝ) a) (p * MvPolynomial.X j) =
            (MvPolynomial.aeval (R := ℝ) a) p * a j by simp [a]]
        rw [show (MvPolynomial.aeval (R := ℝ) b) (p * MvPolynomial.X j) =
            (MvPolynomial.aeval (R := ℝ) b) p * b j by simp [b]]
        rw [Polynomial.eval_mul]
        rw [hp]
        congr 1
        · by_cases hj : j = i
          · subst j
            simp [a, b]
          · simp [a, b, hj]
      simpa [a, b] using hmain

/-- the derivative of the slice is the slice of the partial derivative -/
lemma cdmD_slicePoly_deriv {n : ℕ} (i : Fin n) (z : Fin n → ℂ) (f : MvPolynomial (Fin n) ℝ) :
    (cdmD_slicePoly i z f).derivative = cdmD_slicePoly i z (MvPolynomial.pderiv i f) := by
  classical
  unfold cdmD_slicePoly
  let a : Fin n → Polynomial ℂ := fun j => if j = i then Polynomial.X else Polynomial.C (z j)
  induction f using MvPolynomial.induction_on with
  | C c => simp [a]
  | add p q hp hq =>
      simp only [map_add, map_add]
      rw [hp, hq]
  | mul_X p j hp =>
      by_cases hj : j = i
      · subst j
        have hpm : (MvPolynomial.aeval (R := ℝ) a) (p * MvPolynomial.X i)
            = (MvPolynomial.aeval (R := ℝ) a) p * a i := by simp [a]
        have hdpm : ((MvPolynomial.pderiv i) (p * MvPolynomial.X i))
            = (MvPolynomial.pderiv i) p * MvPolynomial.X i + p := by
          rw [MvPolynomial.pderiv_mul]
          simp [MvPolynomial.pderiv_X]
        rw [hpm, hdpm]
        rw [Polynomial.derivative_mul]
        rw [map_add]
        simp [a, hp]
      · have hX0 : (MvPolynomial.pderiv i) (MvPolynomial.X j) = (0 : MvPolynomial (Fin n) ℝ) := by
          simp [MvPolynomial.pderiv_X, hj]
        have haC : a j = Polynomial.C (z j) := by simp [a, hj]
        have hpm : (MvPolynomial.aeval (R := ℝ) a) (p * MvPolynomial.X j)
            = (MvPolynomial.aeval (R := ℝ) a) p * a j := by simp [a]
        have hdpm : ((MvPolynomial.pderiv i) (p * MvPolynomial.X j))
            = (MvPolynomial.pderiv i) p * MvPolynomial.X j := by
          rw [MvPolynomial.pderiv_mul]
          simp [hX0]
        rw [hpm, hdpm]
        rw [Polynomial.derivative_mul]
        rw [map_mul, MvPolynomial.aeval_X]
        rw [show derivative ((MvPolynomial.aeval (R := ℝ) a) p) * a j =
            (MvPolynomial.aeval (R := ℝ) a) ((MvPolynomial.pderiv i) p) * a j by rw [hp]]
        have hda0 : (a j).derivative = 0 := by
          rw [haC]
          simp
        rw [hda0, mul_zero, add_zero]

/-- the second conjunct of `cdmD_closure_derivative_precedes` (the `≺` part) -/
lemma cdmD_precedes_second_conjunct {n : ℕ} (i : Fin n) (f : MvPolynomial (Fin n) ℝ)
    (hf : Commons.LorentzianPolynomials.IsStable f) :
    Commons.LorentzianPolynomials.IsStable
        (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f +
          MvPolynomial.X (Fin.last n) *
            MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1))
              (MvPolynomial.pderiv i f)) := by
  by_cases hf0 : f = 0
  · left
    subst f
    simp
  · right
    have hstab : ∀ z : Fin n → ℍ,
        MvPolynomial.aeval (R := ℝ) (fun j : Fin n => ((z j : ℍ) : ℂ)) f ≠ 0 := by
      rcases hf with hz | hz
      · exact False.elim (hf0 hz)
      · exact hz
    intro zz
    let zc : Fin n → ℂ := fun j => ((zz (Fin.castSucc j) : ℍ) : ℂ)
    let xc : ℂ := ((zz (Fin.last n) : ℍ) : ℂ)
    let P : Polynomial ℂ := cdmD_slicePoly i zc f
    have him (j : Fin n) : 0 < (zc j).im := by
      dsimp [zc]
      simpa using (zz (Fin.castSucc j)).im_pos
    let u : ℍ := ⟨zc i, him i⟩
    let xh : ℍ := ⟨xc, by
      dsimp [xc]
      simpa using (zz (Fin.last n)).im_pos⟩
    -- slice evaluation at u equals aeval zc f
    have hslice_u : P.eval (u : ℂ) =
        MvPolynomial.aeval (R := ℝ) (fun j : Fin n => zc j) f := by
      dsimp [P, u]
      rw [cdmD_slicePoly_eval]
      apply congrArg (fun g : Fin n → ℂ => MvPolynomial.aeval (R := ℝ) g f)
      funext j
      by_cases hj : j = i
      · subst j
        simp [zc]
      · simp [hj, zc]
    -- P has no zeroes on the upper half plane
    have hPstab : ∀ u₀ : ℍ, P.eval (u₀ : ℂ) ≠ 0 := by
      intro u₀
      -- value at the H-point with coordinate i replaced by u₀
      let pt : Fin n → ℍ := fun j => if h : j = i then u₀ else ⟨zc j, him j⟩
      have hfun : (fun j : Fin n => if j = i then (u₀ : ℂ) else zc j) =
          (fun j : Fin n => ((pt j : ℍ) : ℂ)) := by
        funext j
        by_cases hj : j = i
        · subst j
          simp [pt, zc]
        · simp [hj, pt, zc]
      rw [cdmD_slicePoly_eval]
      rw [hfun]
      exact hstab pt
    -- P is not the zero polynomial
    have hP0 : P ≠ 0 := by
      intro hP0
      have hP0' : P.eval (u : ℂ) = 0 := by rw [hP0]; simp
      have h : MvPolynomial.aeval (R := ℝ) (fun j : Fin n => zc j) f = 0 := by
        rw [← hslice_u]
        exact hP0'
      have hpt : MvPolynomial.aeval (R := ℝ) (fun j : Fin n => (zc j : ℂ)) f ≠ 0 := by
        let pt : Fin n → ℍ := fun j => ⟨zc j, him j⟩
        have hh := hstab pt
        -- aeval over coercion of pt equals aeval over zc
        convert hh using 1
      exact hpt h
    have hU2 := Commons.Analysis.Complex.Polynomial.plus_x_mul_deriv_stable P hP0 hPstab u xh
    -- now relate aeval of the whole expression to the slice quantities
    have hne : P.eval (u : ℂ) + (xh : ℂ) * P.derivative.eval (u : ℂ) ≠ 0 := hU2
    dsimp [xh, u] at hne
    -- the big evaluation
    have hval :
        MvPolynomial.aeval (R := ℝ) (fun j : Fin (n + 1) => ((zz j : ℍ) : ℂ))
          (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f +
            MvPolynomial.X (Fin.last n) *
              MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1))
                (MvPolynomial.pderiv i f)) ≠ 0 := by
      -- expand via aeval lemmas
      rw [map_add, map_mul]
      rw [MvPolynomial.aeval_X]
      rw [MvPolynomial.aeval_rename, MvPolynomial.aeval_rename]
      change MvPolynomial.aeval (R := ℝ) (fun j : Fin n => zc j) f +
          xc * MvPolynomial.aeval (R := ℝ) (fun j : Fin n => zc j) (MvPolynomial.pderiv i f) ≠ 0
      rw [← hslice_u]
      -- derivative slice:
      have hder : (cdmD_slicePoly i zc (MvPolynomial.pderiv i f)).eval (zc i) =
          P.derivative.eval (u : ℂ) := by
        dsimp [P, u]
        rw [← cdmD_slicePoly_deriv]
      have hB : MvPolynomial.aeval (R := ℝ) (fun j : Fin n => zc j) (MvPolynomial.pderiv i f) =
          (cdmD_slicePoly i zc (MvPolynomial.pderiv i f)).eval (zc i) := by
        rw [cdmD_slicePoly_eval]
        apply congrArg (fun g : Fin n → ℂ => MvPolynomial.aeval (R := ℝ) g (MvPolynomial.pderiv i f))
        funext j
        by_cases hj : j = i
        · subst j; simp [zc]
        · simp [hj, zc]
      rw [hB, hder]
      -- hne with the dsimp already applied: zc i = (u : ℂ)?
      simpa [P, zc, xc] using hne
    exact hval

theorem cdmD_closure_derivative_precedes {n : ℕ} (i : Fin n) (f : MvPolynomial (Fin n) ℝ)
    (hf : Commons.LorentzianPolynomials.IsStable f) :
    Commons.LorentzianPolynomials.IsStable (MvPolynomial.pderiv i f) ∧
      Commons.LorentzianPolynomials.IsStable
        (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f +
          MvPolynomial.X (Fin.last n) *
            MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1))
              (MvPolynomial.pderiv i f)) := by
  exact ⟨cdmP_pderiv_stable_of_stable i f hf, cdmD_precedes_second_conjunct i f hf⟩

end
end Commons.LorentzianPolynomials

namespace Commons.LorentzianPolynomials

open Finsupp Matrix MvPolynomial UpperHalfPlane
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

/-! Helpers: `pderiv` of the "last" variable kills polynomials that do not involve it. -/

private lemma cdmA_pderiv_last_rename_castSucc (n : ℕ) (q : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.pderiv (Fin.last n)
      (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) q) = 0 := by
  classical
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
      have hx : MvPolynomial.pderiv (Fin.last n)
          (MvPolynomial.X (Fin.castSucc i) : MvPolynomial (Fin (n + 1)) ℝ) = 0 := by
        exact MvPolynomial.pderiv_X_of_ne (i := Fin.last n) (j := Fin.castSucc i)
          (σ := Fin (n + 1)) (R := ℝ) (Fin.castSucc_ne_last i)
      rw [map_mul, MvPolynomial.rename_X, pderiv_mul, hp, hx]
      simp

/-- `∂_last (X_last * rename f) = rename f`, when `rename f` does not involve `X_last`. -/
private lemma cdmA_pderiv_last_X_mul_rename (n : ℕ) (f : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.pderiv (Fin.last n)
      (MvPolynomial.X (Fin.last n) *
        MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f) =
      MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f := by
  classical
  rw [pderiv_mul]
  rw [MvPolynomial.pderiv_X_self]
  rw [cdmA_pderiv_last_rename_castSucc n f]
  ring

private lemma cdmA_rename_castSucc_ne_zero (n : ℕ) (f : MvPolynomial (Fin n) ℝ) (hf : f ≠ 0) :
    MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f ≠ 0 := by
  exact (MvPolynomial.rename_injective (Fin.castSucc : Fin n → Fin (n + 1))
    (Fin.castSucc_injective n)).ne hf

/-- Evaluation of a polynomial lifted by the last variable at an appended point. -/
private lemma cdmA_aeval_lastCases_rename (n : ℕ) (u : Fin n → UpperHalfPlane) (w : UpperHalfPlane)
    (q : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.aeval (R := ℝ)
        (fun i : Fin (n + 1) => ((Fin.lastCases w u i : UpperHalfPlane) : ℂ))
        (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) q) =
      MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((u i : UpperHalfPlane) : ℂ)) q := by
  have hfun : (fun i : Fin (n + 1) => ((Fin.lastCases w u i : UpperHalfPlane) : ℂ)) ∘
        (Fin.castSucc : Fin n → Fin (n + 1)) =
      fun i : Fin n => ((u i : UpperHalfPlane) : ℂ) := by
    funext i
    simp [Fin.lastCases_castSucc]
  rw [MvPolynomial.aeval_rename, hfun]

/-- Evaluation of the polynomial `rename g + X_last * rename f`. -/
private lemma cdmA_aeval_linear_last (n : ℕ) (g f : MvPolynomial (Fin n) ℝ)
    (z : Fin (n + 1) → ℂ) :
    MvPolynomial.aeval (R := ℝ) z
        (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) g +
          MvPolynomial.X (Fin.last n) *
            MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f) =
      MvPolynomial.aeval (R := ℝ) (fun i : Fin n => z (Fin.castSucc i)) g +
        z (Fin.last n) *
          MvPolynomial.aeval (R := ℝ) (fun i : Fin n => z (Fin.castSucc i)) f := by
  rw [map_add, map_mul, MvPolynomial.aeval_X]
  rw [MvPolynomial.aeval_rename, MvPolynomial.aeval_rename]
  rfl

/-- Evaluation of the target (positively combined) polynomial. -/
private lemma cdmA_aeval_target (n : ℕ) (f g₁ g₂ : MvPolynomial (Fin n) ℝ) (θ₁ θ₂ : ℝ)
    (z : Fin (n + 1) → ℂ) :
    MvPolynomial.aeval (R := ℝ) z
        (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) (θ₁ • g₁ + θ₂ • g₂) +
          MvPolynomial.X (Fin.last n) *
            MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f) =
      (θ₁ • MvPolynomial.aeval (R := ℝ) (fun i : Fin n => z (Fin.castSucc i)) g₁ +
        θ₂ • MvPolynomial.aeval (R := ℝ) (fun i : Fin n => z (Fin.castSucc i)) g₂) +
        z (Fin.last n) *
          MvPolynomial.aeval (R := ℝ) (fun i : Fin n => z (Fin.castSucc i)) f := by
  rw [map_add, map_mul, MvPolynomial.aeval_X]
  rw [MvPolynomial.aeval_rename]
  rw [map_add, map_smul, map_smul]
  rw [MvPolynomial.aeval_rename]
  abel

/-- The complex core of the argument: if `a + w·c` and `b + w·c` never vanish for
`w` in the upper half plane (with `c ≠ 0`), then the same holds for the positive
combination `(θ₁·a + θ₂·b) + w·c`.  This is the convexity of the closed half-plane
`{z : ℂ | 0 ≤ Im(z/c)}`. -/
private lemma cdmA_upper_linear_comb_ne_zero {a b c : ℂ} {θ₁ θ₂ : ℝ}
    (hθ₁ : 0 ≤ θ₁) (hθ₂ : 0 ≤ θ₂) (hc : c ≠ 0)
    (ha : ∀ w : UpperHalfPlane, a + (w : ℂ) * c ≠ 0)
    (hb : ∀ w : UpperHalfPlane, b + (w : ℂ) * c ≠ 0) :
    ∀ w₀ : UpperHalfPlane, (θ₁ • a + θ₂ • b) + (w₀ : ℂ) * c ≠ 0 := by
  intro w₀ hz
  have haim : 0 ≤ (a / c).im := by
    by_contra hnot
    have hlt : (a / c).im < 0 := lt_of_not_ge hnot
    let w : UpperHalfPlane := ⟨-(a / c), by simpa using (neg_pos.mpr hlt)⟩
    have hz1 : a + (w : ℂ) * c = 0 := by
      dsimp [w]
      field_simp [hc]
      ring
    exact ha w hz1
  have hbim : 0 ≤ (b / c).im := by
    by_contra hnot
    have hlt : (b / c).im < 0 := lt_of_not_ge hnot
    let w : UpperHalfPlane := ⟨-(b / c), by simpa using (neg_pos.mpr hlt)⟩
    have hz1 : b + (w : ℂ) * c = 0 := by
      dsimp [w]
      field_simp [hc]
      ring
    exact hb w hz1
  let u : ℂ := θ₁ • (a / c) + θ₂ • (b / c) + (w₀ : ℂ)
  have huim : 0 < u.im := by
    have hlin : u.im = θ₁ * (a / c).im + θ₂ * (b / c).im + w₀.im := by
      dsimp [u]
      simp
    rw [hlin]
    have hw : 0 < w₀.im := by simpa using w₀.2
    nlinarith
  have hu : u ≠ 0 := by
    intro hu0
    rw [hu0] at huim
    norm_num at huim
  have hfac : (θ₁ • a + θ₂ • b) + (w₀ : ℂ) * c = c * u := by
    dsimp [u]
    field_simp [hc]
  exact (mul_ne_zero hc hu) (hfac ▸ hz)

theorem cdmA_closure_sum_above {n : ℕ} (f g₁ g₂ : MvPolynomial (Fin n) ℝ) (θ₁ θ₂ : ℝ)
    (hθ₁ : 0 ≤ θ₁) (hθ₂ : 0 ≤ θ₂) (hf0 : f ≠ 0)
    (hg₁ : Commons.LorentzianPolynomials.IsStable g₁)
    (hg₂ : Commons.LorentzianPolynomials.IsStable g₂)
    (h₁ : Commons.LorentzianPolynomials.IsStable
      (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) g₁ +
        MvPolynomial.X (Fin.last n) *
          MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f))
    (h₂ : Commons.LorentzianPolynomials.IsStable
      (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) g₂ +
        MvPolynomial.X (Fin.last n) *
          MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f)) :
    Commons.LorentzianPolynomials.IsStable
      (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) (θ₁ • g₁ + θ₂ • g₂) +
        MvPolynomial.X (Fin.last n) *
          MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f) := by
  classical
  let k : Fin n → Fin (n + 1) := Fin.castSucc
  let j : Fin (n + 1) := Fin.last n
  let F : MvPolynomial (Fin (n + 1)) ℝ := MvPolynomial.rename k f
  let P₁ : MvPolynomial (Fin (n + 1)) ℝ := MvPolynomial.rename k g₁ + MvPolynomial.X j * F
  let P₂ : MvPolynomial (Fin (n + 1)) ℝ := MvPolynomial.rename k g₂ + MvPolynomial.X j * F
  have hF0 : F ≠ 0 := by
    simpa [F] using cdmA_rename_castSucc_ne_zero n f hf0
  have hp₁ : MvPolynomial.pderiv (Fin.last n) P₁ = F := by
    dsimp [P₁, F, k, j]
    rw [map_add, cdmA_pderiv_last_rename_castSucc n g₁, cdmA_pderiv_last_X_mul_rename n f]
    simp
  have hp₂ : MvPolynomial.pderiv (Fin.last n) P₂ = F := by
    dsimp [P₂, F, k, j]
    rw [map_add, cdmA_pderiv_last_rename_castSucc n g₂, cdmA_pderiv_last_X_mul_rename n f]
    simp
  have hP₁0 : P₁ ≠ 0 := by
    intro hP0
    apply hF0
    rw [← hp₁, hP0]
    simp
  have hP₂0 : P₂ ≠ 0 := by
    intro hP0
    apply hF0
    rw [← hp₂, hP0]
    simp
  -- stability of the "above" part `F = rename k f`
  have hFstab : Commons.LorentzianPolynomials.IsStable F := by
    have hsp := cdmP_pderiv_stable_of_stable (Fin.last n) P₁ h₁
    rwa [hp₁] at hsp
  have hFz : ∀ z : Fin (n + 1) → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin (n + 1) => ((z i : UpperHalfPlane) : ℂ)) F ≠ 0 := by
    rcases hFstab with h0 | hnz
    · exact False.elim (hF0 h0)
    · exact hnz
  have hfU : ∀ u : Fin n → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((u i : UpperHalfPlane) : ℂ)) f ≠ 0 := by
    intro u
    let z : Fin (n + 1) → UpperHalfPlane := fun i => Fin.lastCases UpperHalfPlane.I u i
    have hz := hFz z
    have heq : MvPolynomial.aeval (R := ℝ)
        (fun i : Fin (n + 1) => ((z i : UpperHalfPlane) : ℂ)) F =
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((u i : UpperHalfPlane) : ℂ)) f := by
      dsimp [F, z, k]
      exact cdmA_aeval_lastCases_rename n u UpperHalfPlane.I f
    rw [heq] at hz
    exact hz
  have hP₁z : ∀ z : Fin (n + 1) → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin (n + 1) => ((z i : UpperHalfPlane) : ℂ)) P₁ ≠ 0 := by
    rcases h₁ with h0 | hnz
    · exact False.elim (hP₁0 h0)
    · exact hnz
  have hP₂z : ∀ z : Fin (n + 1) → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin (n + 1) => ((z i : UpperHalfPlane) : ℂ)) P₂ ≠ 0 := by
    rcases h₂ with h0 | hnz
    · exact False.elim (hP₂0 h0)
    · exact hnz
  -- main: prove the nonvanishing disjunct of `IsStable`
  right
  intro z
  change MvPolynomial.aeval (R := ℝ)
        (fun i : Fin (n + 1) => ((z i : UpperHalfPlane) : ℂ))
        (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) (θ₁ • g₁ + θ₂ • g₂) +
          MvPolynomial.X (Fin.last n) *
            MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f) ≠ 0
  let u : Fin n → UpperHalfPlane := fun i => z (Fin.castSucc i)
  let w : UpperHalfPlane := z (Fin.last n)
  let zc : Fin n → ℂ := fun i => ((u i : UpperHalfPlane) : ℂ)
  let a : ℂ := MvPolynomial.aeval (R := ℝ) zc g₁
  let b : ℂ := MvPolynomial.aeval (R := ℝ) zc g₂
  let c : ℂ := MvPolynomial.aeval (R := ℝ) zc f
  have hc' : c ≠ 0 := by
    dsimp [c]
    simpa [zc] using hfU u
  have ha : ∀ w' : UpperHalfPlane, a + (w' : ℂ) * c ≠ 0 := by
    intro w'
    let z' : Fin (n + 1) → UpperHalfPlane := fun i => Fin.lastCases w' u i
    have hz' : MvPolynomial.aeval (R := ℝ)
        (fun i : Fin (n + 1) => ((z' i : UpperHalfPlane) : ℂ)) P₁ ≠ 0 := hP₁z z'
    have heq : MvPolynomial.aeval (R := ℝ)
        (fun i : Fin (n + 1) => ((z' i : UpperHalfPlane) : ℂ)) P₁ = a + (w' : ℂ) * c := by
      dsimp [z', P₁, F, k, j, u, zc, a, c]
      rw [cdmA_aeval_linear_last]
      simp [Fin.lastCases_castSucc, Fin.lastCases_last]
    rwa [heq] at hz'
  have hb : ∀ w' : UpperHalfPlane, b + (w' : ℂ) * c ≠ 0 := by
    intro w'
    let z' : Fin (n + 1) → UpperHalfPlane := fun i => Fin.lastCases w' u i
    have hz' : MvPolynomial.aeval (R := ℝ)
        (fun i : Fin (n + 1) => ((z' i : UpperHalfPlane) : ℂ)) P₂ ≠ 0 := hP₂z z'
    have heq : MvPolynomial.aeval (R := ℝ)
        (fun i : Fin (n + 1) => ((z' i : UpperHalfPlane) : ℂ)) P₂ = b + (w' : ℂ) * c := by
      dsimp [z', P₂, F, k, j, u, zc, b, c]
      rw [cdmA_aeval_linear_last]
      simp [Fin.lastCases_castSucc, Fin.lastCases_last]
    rwa [heq] at hz'
  -- the core convexity step
  have hcore := cdmA_upper_linear_comb_ne_zero (a := a) (b := b) (c := c) (θ₁ := θ₁) (θ₂ := θ₂)
    hθ₁ hθ₂ hc' ha hb w
  -- the value of the target polynomial at z is exactly the core expression
  have hval : MvPolynomial.aeval (R := ℝ)
        (fun i : Fin (n + 1) => ((z i : UpperHalfPlane) : ℂ))
        (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) (θ₁ • g₁ + θ₂ • g₂) +
          MvPolynomial.X (Fin.last n) *
            MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f) =
      (θ₁ • a + θ₂ • b) + (w : ℂ) * c := by
    rw [cdmA_aeval_target]
  rw [hval]
  exact hcore

end

end Commons.LorentzianPolynomials

open Finsupp Matrix MvPolynomial Polynomial UpperHalfPlane Filter Topology
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Commons.LorentzianPolynomials

noncomputable section

/-!
# Nonnegative dilations preserve stability

If `f ∈ ℝ[x₁,…,xₙ]` is stable (zero, or nonvanishing on the open upper half
plane `ℍⁿ`) then the substitution `x_j ↦ a_j x_j` with all `a_j ≥ 0` is stable
as well.

For strictly positive `a_j` this is immediate, since multiplying a point of `ℍ`
by a positive real keeps it in `ℍ`.  For `a_j = 0` we pass to the limit:
`f` dilated by `a_j + 1/(k+1)` is stable for every `k`, and as `k → ∞` these
polynomials converge coefficientwise to the dilation by `a`.  Stability is
preserved under coefficientwise limits of uniformly bounded degree
(`Commons.Analysis.MvPolynomial.cdmT_isStable_tendsto_of_degree_le`).
-/

/-- Evaluation of the dilated polynomial: substituting `z` into
`f(b₁x₁,…,bₙxₙ)` gives `f` evaluated at `(b₁z₁,…,bₙzₙ)`. -/
lemma cdmN_cdn_dil_aeval_eval (n : ℕ) (b : Fin n → ℝ) (z : Fin n → ℂ)
    (f : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.aeval (R := ℝ) z
        (MvPolynomial.aeval (R := ℝ) (fun j : Fin n => MvPolynomial.C (b j) * MvPolynomial.X j) f)
      = MvPolynomial.aeval (R := ℝ) (fun j : Fin n => (b j : ℂ) * z j) f := by
  classical
  let φ : MvPolynomial (Fin n) ℝ →ₐ[ℝ] ℂ := MvPolynomial.aeval (R := ℝ) z
  have h := MvPolynomial.comp_aeval_apply
    (f := (fun j : Fin n => MvPolynomial.C (b j) * MvPolynomial.X j)) (φ := φ) (p := f)
  have hφfun : (fun i : Fin n => φ (MvPolynomial.C (b i) * MvPolynomial.X i)) =
      (fun i : Fin n => (b i : ℂ) * z i) := by
    funext i
    dsimp [φ]
    rw [map_mul]
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    rfl
  rw [h, hφfun]

/-- `(C b * X j)^k = C(b^k) * X j ^ k`. -/
lemma cdmN_cdn_pow_C_mul_X (n : ℕ) (b : ℝ) (j : Fin n) (k : ℕ) :
    (MvPolynomial.C b * MvPolynomial.X j) ^ k =
      MvPolynomial.C (b ^ k) * MvPolynomial.X j ^ k := by
  rw [mul_pow]
  rw [← map_pow (MvPolynomial.C : ℝ →+* MvPolynomial (Fin n) ℝ) b k]

/-- Image of a monomial under the dilation `X_j ↦ b_j X_j`. -/
lemma cdmN_cdn_dil_aeval_monomial (n : ℕ) (b : Fin n → ℝ) (m : Fin n →₀ ℕ) (r : ℝ) :
    MvPolynomial.aeval (R := ℝ) (fun j : Fin n => MvPolynomial.C (b j) * MvPolynomial.X j)
        (MvPolynomial.monomial m r)
      = MvPolynomial.monomial m (r * ∏ j ∈ m.support, (b j) ^ (m j)) := by
  classical
  rw [MvPolynomial.aeval_monomial]
  rw [MvPolynomial.algebraMap_eq]
  have hfac (j : Fin n) :
      (MvPolynomial.C (b j) * MvPolynomial.X j) ^ (m j) =
        MvPolynomial.C ((b j) ^ (m j)) * MvPolynomial.X j ^ (m j) := by
    exact cdmN_cdn_pow_C_mul_X n (b j) j (m j)
  have hCprod : (∏ j ∈ m.support,
        (MvPolynomial.C ((b j) ^ (m j)) : MvPolynomial (Fin n) ℝ)) =
      (MvPolynomial.C (∏ j ∈ m.support, (b j) ^ (m j)) : MvPolynomial (Fin n) ℝ) := by
    exact (map_prod (g := (MvPolynomial.C : ℝ →+* MvPolynomial (Fin n) ℝ))
      (f := fun j : Fin n => (b j) ^ (m j)) (s := m.support)).symm
  have hXprod : (∏ j ∈ m.support, (MvPolynomial.X j : MvPolynomial (Fin n) ℝ) ^ (m j)) =
      (monomial m 1 : MvPolynomial (Fin n) ℝ) := by
    exact MvPolynomial.prod_X_pow_eq_monomial (R := ℝ) (s := m)
  calc
    MvPolynomial.C r * m.prod (fun j k => (MvPolynomial.C (b j) * MvPolynomial.X j) ^ k)
        = MvPolynomial.C r * (∏ j ∈ m.support, (MvPolynomial.C (b j) * MvPolynomial.X j) ^ (m j)) := by
            rw [Finsupp.prod]
    _ = MvPolynomial.C r * (∏ j ∈ m.support,
          (MvPolynomial.C ((b j) ^ (m j)) * MvPolynomial.X j ^ (m j))) := by
            congr 1
            apply Finset.prod_congr rfl
            intro j hj
            exact hfac j
    _ = MvPolynomial.C r * ((∏ j ∈ m.support, MvPolynomial.C ((b j) ^ (m j))) *
          (∏ j ∈ m.support, MvPolynomial.X j ^ (m j))) := by
            congr 1
            rw [Finset.prod_mul_distrib]
    _ = MvPolynomial.C r * (MvPolynomial.C (∏ j ∈ m.support, (b j) ^ (m j)) * monomial m 1) := by
            rw [hCprod, hXprod]
    _ = MvPolynomial.C (r * ∏ j ∈ m.support, (b j) ^ (m j)) * monomial m 1 := by
            rw [← mul_assoc, ← MvPolynomial.C_mul]
    _ = monomial m (r * ∏ j ∈ m.support, (b j) ^ (m j)) := by
            rw [MvPolynomial.C_mul_monomial]
            simp

/-- The dilation of `f` expressed as a sum over the support of `f`. -/
lemma cdmN_cdn_dil_aeval_sum (n : ℕ) (b : Fin n → ℝ) (f : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.aeval (R := ℝ) (fun j : Fin n => MvPolynomial.C (b j) * MvPolynomial.X j) f =
      ∑ m ∈ f.support, MvPolynomial.monomial m
        (f.coeff m * ∏ j ∈ m.support, (b j) ^ (m j)) := by
  classical
  conv_lhs =>
    rw [← MvPolynomial.support_sum_monomial_coeff f]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  exact cdmN_cdn_dil_aeval_monomial n b m (f.coeff m)

/-- Coefficients of the dilated polynomial: only the coefficient of `f` at the same
monomial matters. -/
lemma cdmN_cdn_dil_aeval_coeff (n : ℕ) (b : Fin n → ℝ) (f : MvPolynomial (Fin n) ℝ)
    (m : Fin n →₀ ℕ) :
    (MvPolynomial.aeval (R := ℝ) (fun j : Fin n => MvPolynomial.C (b j) * MvPolynomial.X j)
        f).coeff m
      = f.coeff m * ∏ j ∈ m.support, (b j) ^ (m j) := by
  classical
  rw [cdmN_cdn_dil_aeval_sum]
  rw [MvPolynomial.coeff_sum]
  by_cases hm : m ∈ f.support
  · rw [Finset.sum_eq_single m]
    · rw [MvPolynomial.coeff_monomial]
      simp
    · intro b' hb' hne
      rw [MvPolynomial.coeff_monomial]
      simp [hne]
    · intro hnot
      exact False.elim (hnot hm)
  · have hc : f.coeff m = 0 := by
      simpa [MvPolynomial.mem_support_iff] using hm
    rw [Finset.sum_eq_zero]
    · simp [hc]
    · intro x hx
      rw [MvPolynomial.coeff_monomial]
      by_cases h : x = m
      · subst x
        simp [hc]
      · simp [h]

/-- The dilation does not enlarge the support. -/
lemma cdmN_cdn_dil_aeval_support_subset (n : ℕ) (b : Fin n → ℝ) (f : MvPolynomial (Fin n) ℝ) :
    (MvPolynomial.aeval (R := ℝ) (fun j : Fin n => MvPolynomial.C (b j) * MvPolynomial.X j)
        f).support ⊆ f.support := by
  intro m hm
  by_contra hnot
  have hc : (MvPolynomial.aeval (R := ℝ)
      (fun j : Fin n => MvPolynomial.C (b j) * MvPolynomial.X j) f).coeff m ≠ 0 :=
    (MvPolynomial.mem_support_iff).mp hm
  have hf0 : f.coeff m = 0 := by
    simpa [MvPolynomial.mem_support_iff] using hnot
  rw [cdmN_cdn_dil_aeval_coeff, hf0] at hc
  simp at hc

/-- Strictly positive dilations preserve stability. -/
lemma cdmN_cdn_dil_aeval_stable_pos (n : ℕ) (b : Fin n → ℝ) (hb : ∀ j : Fin n, 0 < b j)
    (f : MvPolynomial (Fin n) ℝ) (hf : IsStable f) :
    IsStable (MvPolynomial.aeval (R := ℝ)
      (fun j : Fin n => MvPolynomial.C (b j) * MvPolynomial.X j) f) := by
  classical
  rcases hf with hf0 | hfz
  · left
    rw [hf0]
    simp
  · right
    intro z
    have him (j : Fin n) : 0 < ((b j : ℂ) * ((z j : ℍ) : ℂ)).im := by
      have h1 : ((b j : ℂ) * ((z j : ℍ) : ℂ)).im = (b j) * ((z j : ℍ) : ℂ).im := by
        rw [Complex.mul_im]
        simp
      rw [h1]
      exact mul_pos (hb j) ((z j : ℍ).im_pos)
    let w : Fin n → ℍ := fun j => ⟨(b j : ℂ) * ((z j : ℍ) : ℂ), him j⟩
    have hw : (fun j : Fin n => ((w j : ℍ) : ℂ)) =
        fun j : Fin n => (b j : ℂ) * ((z j : ℍ) : ℂ) := by
      funext j
      rfl
    have hne : MvPolynomial.aeval (R := ℝ)
        (fun j : Fin n => (b j : ℂ) * ((z j : ℍ) : ℂ)) f ≠ 0 := by
      rw [← hw]
      exact hfz w
    change MvPolynomial.aeval (R := ℝ) (fun j : Fin n => ((z j : ℍ) : ℂ))
        (MvPolynomial.aeval (R := ℝ) (fun j : Fin n => MvPolynomial.C (b j) * MvPolynomial.X j) f) ≠ 0
    rw [cdmN_cdn_dil_aeval_eval n b (fun j : Fin n => ((z j : ℍ) : ℂ)) f]
    exact hne

/-- `1/(k+1) → 0` as `k → ∞`. -/
lemma cdmN_cdn_tendsto_one_div_succ (𝕜 : Type*) [DivisionSemiring 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] :
    Tendsto (fun k : ℕ => (1 : 𝕜) / ((k : 𝕜) + 1)) atTop (𝓝 (0 : 𝕜)) :=
  tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := 𝕜)

/-- Products of finitely many convergent sequences converge to the product of the
limits. -/
lemma cdmN_cdn_prod_tendsto {ι : Type*} (s : Finset ι) (v : ℕ → ι → ℝ) (w : ι → ℝ)
    (e : ι → ℕ) (hv : ∀ i ∈ s, Tendsto (fun k : ℕ => v k i) atTop (𝓝 (w i))) :
    Tendsto (fun k : ℕ => ∏ i ∈ s, (v k i) ^ (e i)) atTop
      (𝓝 (∏ i ∈ s, (w i) ^ (e i))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hv_s : ∀ i ∈ s, Tendsto (fun k : ℕ => v k i) atTop (𝓝 (w i)) := by
        intro i hi
        exact hv i (Finset.mem_insert_of_mem hi)
      have hih := ih hv_s
      have hpow : Tendsto (fun k : ℕ => (v k a) ^ (e a)) atTop (𝓝 ((w a) ^ (e a))) :=
        (hv a (by simp)).pow (e a)
      have hmul := hpow.mul hih
      simpa [Finset.prod_insert ha] using hmul

/-- The dilation coefficients `a_j + 1/(k+1)` converge to `a_j`. -/
lemma cdmN_cdn_tendsto_dil_coeff (n : ℕ) (a : Fin n → ℝ) (f : MvPolynomial (Fin n) ℝ)
    (m : Fin n →₀ ℕ) :
    Tendsto (fun k : ℕ =>
        (MvPolynomial.aeval (R := ℝ)
          (fun j : Fin n => MvPolynomial.C (a j + (1 : ℝ) / ((k : ℝ) + 1)) *
            MvPolynomial.X j) f).coeff m) atTop
      (𝓝 ((MvPolynomial.aeval (R := ℝ)
        (fun j : Fin n => MvPolynomial.C (a j) * MvPolynomial.X j) f).coeff m)) := by
  classical
  have hb_tendsto (j : Fin n) : Tendsto (fun k : ℕ =>
      a j + (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 (a j)) := by
    have h1 : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      cdmN_cdn_tendsto_one_div_succ ℝ
    simpa using (tendsto_const_nhds (x := a j)).add h1
  have hmain : Tendsto (fun k : ℕ => f.coeff m *
        ∏ j ∈ m.support, (a j + (1 : ℝ) / ((k : ℝ) + 1)) ^ (m j)) atTop
      (𝓝 (f.coeff m * ∏ j ∈ m.support, (a j) ^ (m j))) := by
    have hprod := cdmN_cdn_prod_tendsto m.support
      (fun k : ℕ => fun j : Fin n => a j + (1 : ℝ) / ((k : ℝ) + 1)) a
      (fun j : Fin n => m j)
      (by
        intro j hj
        exact hb_tendsto j)
    simpa using hprod.const_mul (f.coeff m)
  have hconv : (fun k : ℕ =>
        (MvPolynomial.aeval (R := ℝ)
          (fun j : Fin n => MvPolynomial.C (a j + (1 : ℝ) / ((k : ℝ) + 1)) *
            MvPolynomial.X j) f).coeff m) =ᶠ[atTop]
      (fun k : ℕ => f.coeff m *
        ∏ j ∈ m.support, (a j + (1 : ℝ) / ((k : ℝ) + 1)) ^ (m j)) := by
    refine Filter.Eventually.of_forall ?_
    intro k
    exact cdmN_cdn_dil_aeval_coeff n (fun j : Fin n => a j + (1 : ℝ) / ((k : ℝ) + 1)) f m
  have hg : (𝓝 ((MvPolynomial.aeval (R := ℝ)
      (fun j : Fin n => MvPolynomial.C (a j) * MvPolynomial.X j) f).coeff m)) =
      𝓝 (f.coeff m * ∏ j ∈ m.support, (a j) ^ (m j)) := by
    congr 1
    exact cdmN_cdn_dil_aeval_coeff n a f m
  rw [hg]
  exact Filter.Tendsto.congr' hconv.symm hmain

/-- A nonnegative dilation of a stable polynomial is stable. -/
theorem cdmN_closure_dilate_nonneg {n : ℕ} (a : Fin n → ℝ) (ha : ∀ j : Fin n, 0 ≤ a j)
    (f : MvPolynomial (Fin n) ℝ) (hf : Commons.LorentzianPolynomials.IsStable f) :
    Commons.LorentzianPolynomials.IsStable
      (MvPolynomial.aeval (fun j : Fin n => MvPolynomial.C (a j) * MvPolynomial.X j) f) := by
  classical
  let u : ℕ → MvPolynomial (Fin n) ℝ := fun k =>
    MvPolynomial.aeval (R := ℝ)
      (fun j : Fin n => MvPolynomial.C (a j + (1 : ℝ) / ((k : ℝ) + 1)) * MvPolynomial.X j) f
  let g : MvPolynomial (Fin n) ℝ :=
    MvPolynomial.aeval (R := ℝ)
      (fun j : Fin n => MvPolynomial.C (a j) * MvPolynomial.X j) f
  have huD : ∀ k : ℕ, (u k).totalDegree ≤ f.totalDegree := by
    intro k
    exact MvPolynomial.totalDegree_le_of_support_subset
      (cdmN_cdn_dil_aeval_support_subset n (fun j : Fin n => a j + (1 : ℝ) / ((k : ℝ) + 1)) f)
  have hgD : g.totalDegree ≤ f.totalDegree := by
    dsimp [g]
    exact MvPolynomial.totalDegree_le_of_support_subset
      (cdmN_cdn_dil_aeval_support_subset n a f)
  have hconv : ∀ m : Fin n →₀ ℕ,
      Tendsto (fun k : ℕ => (u k).coeff m) atTop (𝓝 (g.coeff m)) := by
    intro m
    dsimp [u, g]
    exact cdmN_cdn_tendsto_dil_coeff n a f m
  have hstab : ∀ k : ℕ, (u k) = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) (u k) ≠ 0 := by
    intro k
    have hpos (j : Fin n) : 0 < (1 : ℝ) / ((k : ℝ) + 1) := by
      have hkp : 0 < (k : ℝ) + 1 := by positivity
      exact div_pos zero_lt_one hkp
    have hb : ∀ j : Fin n, 0 < a j + (1 : ℝ) / ((k : ℝ) + 1) := by
      intro j
      linarith [ha j, hpos j]
    dsimp [u]
    exact cdmN_cdn_dil_aeval_stable_pos n (fun j : Fin n => a j + (1 : ℝ) / ((k : ℝ) + 1)) hb f hf
  have hres := Commons.Analysis.MvPolynomial.cdmT_isStable_tendsto_of_degree_le n f.totalDegree u g
    huD hgD hconv hstab
  dsimp [g] at hres
  exact hres

end
end Commons.LorentzianPolynomials
open Finsupp Matrix MvPolynomial Polynomial UpperHalfPlane Topology Set Filter
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Commons.LorentzianPolynomials

noncomputable section

/-! ## Helpers for the cubic deform statement -/

/-- In degree three, partial derivatives land in `L n 2` (by the definition of `L`). -/
private lemma pderiv_mem_L_of_mem_L_three (n : ℕ) (f : H n 3) (hf : f ∈ L n 3) (k : Fin n) :
    (⟨f.1.pderiv k, f.2.pderiv⟩ : H n 2) ∈ L n 2 := by
  unfold L at hf ⊢
  simp at hf ⊢
  exact hf.2 k

/-- In degree three, partial derivatives land in `S n 2` (since `L n 2 = S n 2`). -/
private lemma pderiv_mem_S_of_mem_L_three (n : ℕ) (f : H n 3) (hf : f ∈ L n 3) (k : Fin n) :
    (⟨f.1.pderiv k, f.2.pderiv⟩ : H n 2) ∈ S n 2 := by
  simpa [L] using pderiv_mem_L_of_mem_L_three n f hf k

/-- second partial derivatives commute -/
private lemma pderiv_comm (n : ℕ) (a b : Fin n) (f : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.pderiv a (MvPolynomial.pderiv b f) =
      MvPolynomial.pderiv b (MvPolynomial.pderiv a f) := by
  classical
  by_cases hab : a = b
  · subst b
    rfl
  · apply MvPolynomial.ext
    intro m
    simp only [MvPolynomial.coeff_pderiv]
    have h1 : (m + (Finsupp.single a (1 : ℕ) : Fin n →₀ ℕ)) b = m b := by
      simp [Finsupp.add_apply, Finsupp.single_apply, hab]
    have h2 : (m + (Finsupp.single b (1 : ℕ) : Fin n →₀ ℕ)) a = m a := by
      simp [Finsupp.add_apply, Finsupp.single_apply, Ne.symm hab]
    rw [h1, h2]
    have hidx : (m + (Finsupp.single a (1 : ℕ) : Fin n →₀ ℕ)) + (Finsupp.single b (1 : ℕ) : Fin n →₀ ℕ)
        = (m + (Finsupp.single b (1 : ℕ) : Fin n →₀ ℕ)) + (Finsupp.single a (1 : ℕ) : Fin n →₀ ℕ) := by
      rw [add_assoc, add_assoc, add_comm (Finsupp.single a (1 : ℕ) : Fin n →₀ ℕ)
        (Finsupp.single b (1 : ℕ) : Fin n →₀ ℕ)]
    rw [hidx]
    ring

/-- coefficients of `X_i · (∂_j f)` are nonnegative when those of `f` are -/
private lemma coeff_X_mul_pderiv_nonneg (n : ℕ) (i j : Fin n) (f : MvPolynomial (Fin n) ℝ)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ f.coeff m) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ (MvPolynomial.X i * MvPolynomial.pderiv j f).coeff m := by
  classical
  intro m
  by_cases hmi : m i ≥ 1
  · rw [ds_coeff_X_mul_shift (p := MvPolynomial.pderiv j f) i m hmi]
    rw [MvPolynomial.coeff_pderiv]
    exact mul_nonneg (hnn ((m - Finsupp.single i 1) + Finsupp.single j 1)) (by positivity)
  · have hmi0 : m i = 0 := by omega
    rw [ds_coeff_X_mul_zero (p := MvPolynomial.pderiv j f) i m hmi0]

/-- coefficients of `X_i · ℓ` are nonnegative when those of `ℓ` are -/
private lemma coeff_X_mul_nonneg_coeff (n : ℕ) (i : Fin n) (ℓ : MvPolynomial (Fin n) ℝ)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ ℓ.coeff m) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ (MvPolynomial.X i * ℓ).coeff m := by
  classical
  intro m
  by_cases hmi : m i ≥ 1
  · rw [ds_coeff_X_mul_shift (p := ℓ) i m hmi]
    exact hnn (m - Finsupp.single i 1)
  · have hmi0 : m i = 0 := by omega
    rw [ds_coeff_X_mul_zero (p := ℓ) i m hmi0]



/-- Local abbreviation: polynomials in `Fin m` variables. -/
abbrev cdmRM (m : ℕ) := MvPolynomial (Fin m) ℝ

/-- Homogeneity of the deformed quadratic `∂ᵢh + φ∂ⱼh + ψXᵢ∂ᵢ∂ⱼh`. -/
private lemma cdm_deform_hom_two (n : ℕ) (i j : Fin n) (h : H n 3)
    (φ ψ : ℝ) :
    (MvPolynomial.pderiv i h.1 + MvPolynomial.C φ * MvPolynomial.pderiv j h.1 +
      MvPolynomial.C ψ * MvPolynomial.X i * MvPolynomial.pderiv i (MvPolynomial.pderiv j h.1)
      : MvPolynomial (Fin n) ℝ).IsHomogeneous 2 := by
  have hA : (MvPolynomial.pderiv i h.1).IsHomogeneous 2 := by
    simpa using h.2.pderiv
  have hB : (MvPolynomial.pderiv j h.1).IsHomogeneous 2 := by
    simpa using h.2.pderiv
  have hℓ : (MvPolynomial.pderiv i (MvPolynomial.pderiv j h.1)).IsHomogeneous 1 := by
    simpa using hB.pderiv
  have hCφ : (MvPolynomial.C φ : MvPolynomial (Fin n) ℝ).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_C (σ := Fin n) (R := ℝ) φ
  have hCψ : (MvPolynomial.C ψ : MvPolynomial (Fin n) ℝ).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_C (σ := Fin n) (R := ℝ) ψ
  have hX : (MvPolynomial.X i : MvPolynomial (Fin n) ℝ).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X (σ := Fin n) (R := ℝ) i
  have h1 : (MvPolynomial.C φ * MvPolynomial.pderiv j h.1).IsHomogeneous 2 := by
    simpa [show 0 + 2 = 2 by norm_num] using hCφ.mul hB
  have h2 : (MvPolynomial.C ψ * MvPolynomial.X i *
      MvPolynomial.pderiv i (MvPolynomial.pderiv j h.1)).IsHomogeneous 2 := by
    have hXℓ : (MvPolynomial.X i * MvPolynomial.pderiv i (MvPolynomial.pderiv j h.1)).IsHomogeneous 2 := by
      simpa [show 1 + 1 = 2 by norm_num] using hX.mul hℓ
    simpa [show 0 + 2 = 2 by norm_num, mul_assoc] using hCψ.mul hXℓ
  exact (hA.add h1).add h2

/-- The non-degenerate case (`∂ᵢ∂ⱼh ≠ 0`): the quadratic
`∂ᵢh + φ∂ⱼh + ψXᵢ∂ᵢ∂ⱼh` lies in `S n 2`. -/
private lemma cdm_nondeg_mem_S {n : ℕ} (i j : Fin n) (h : H n 3) (hh : h ∈ L n 3)
    (φ ψ : ℝ) (hφ : 0 ≤ φ) (hψ : 0 ≤ ψ)
    (hℓ : MvPolynomial.pderiv i (MvPolynomial.pderiv j h.1) ≠ 0) :
    ∃ u : H n 2, u ∈ S n 2 ∧ u.1 = MvPolynomial.pderiv i h.1 +
      MvPolynomial.C φ * MvPolynomial.pderiv j h.1 +
        MvPolynomial.C ψ * MvPolynomial.X i * MvPolynomial.pderiv i (MvPolynomial.pderiv j h.1) := by
  classical
  let e : Fin n → Fin (n + 1) := Fin.castSucc
  let ℓ : MvPolynomial (Fin n) ℝ := MvPolynomial.pderiv i (MvPolynomial.pderiv j h.1)
  let A : MvPolynomial (Fin n) ℝ := MvPolynomial.pderiv i h.1
  let B : MvPolynomial (Fin n) ℝ := MvPolynomial.pderiv j h.1
  let T : MvPolynomial (Fin n) ℝ :=
    A + MvPolynomial.C φ * B + MvPolynomial.C ψ * MvPolynomial.X i * ℓ
  have hSi : (⟨A, h.2.pderiv⟩ : H n 2) ∈ S n 2 := by
    dsimp [A]
    exact pderiv_mem_S_of_mem_L_three n h hh i
  have hSj : (⟨B, h.2.pderiv⟩ : H n 2) ∈ S n 2 := by
    dsimp [B]
    exact pderiv_mem_S_of_mem_L_three n h hh j
  rcases hSi with ⟨hstabA, hnnA⟩
  rcases hSj with ⟨hstabB, hnnB⟩
  have hpre_i := cdmD_closure_derivative_precedes (n := n) i B hstabB
  have h₁ : IsStable
      (MvPolynomial.rename e B + MvPolynomial.X (Fin.last n) * MvPolynomial.rename e ℓ) := by
    simpa [ℓ] using hpre_i.2
  have hpre_j := cdmD_closure_derivative_precedes (n := n) j A hstabA
  have h₂ : IsStable
      (MvPolynomial.rename e A + MvPolynomial.X (Fin.last n) * MvPolynomial.rename e ℓ) := by
    have hrewrite : MvPolynomial.rename e (MvPolynomial.pderiv j (MvPolynomial.pderiv i h.1)) =
        MvPolynomial.rename e (MvPolynomial.pderiv i (MvPolynomial.pderiv j h.1)) := by
      rw [pderiv_comm n j i h.1]
    have hh' := hpre_j.2
    rwa [hrewrite] at hh'
  have hP : IsStable
      (MvPolynomial.rename e (φ • B + (1 : ℝ) • A)
        + MvPolynomial.X (Fin.last n) * MvPolynomial.rename e ℓ) := by
    exact (cdmA_closure_sum_above (n := n) ℓ B A φ (1 : ℝ) hφ (by norm_num) hℓ
      hstabB hstabA h₁ h₂)
  let a : Fin (n + 1) → ℝ := fun j => if j = Fin.last n then ψ else 1
  have ha : ∀ j : Fin (n + 1), 0 ≤ a j := by
    intro j
    by_cases hj : j = Fin.last n
    · subst j; simp [a, hψ]
    · simp [a, hj]
  have hD : IsStable
      (MvPolynomial.aeval (fun j : Fin (n + 1) => MvPolynomial.C (a j) * MvPolynomial.X j)
        (MvPolynomial.rename e (φ • B + (1 : ℝ) • A)
          + MvPolynomial.X (Fin.last n) * MvPolynomial.rename e ℓ)) := by
    exact (cdmN_closure_dilate_nonneg (n := n + 1) a ha
      (MvPolynomial.rename e (φ • B + (1 : ℝ) • A)
        + MvPolynomial.X (Fin.last n) * MvPolynomial.rename e ℓ) hP)
  have hne : Fin.castSucc i ≠ Fin.last n := by
    intro h
    have hval : (Fin.castSucc i).val = (Fin.last n).val := congrArg Fin.val h
    have hcast : (Fin.castSucc i).val = i.val := by simp [Fin.castSucc]
    have hlast : (Fin.last n).val = n := by simp [Fin.last]
    rw [hcast, hlast] at hval
    omega
  have hDG : IsStable
      (MvPolynomial.aeval (fun k : Fin (n + 1) =>
          if k = Fin.last n then MvPolynomial.X (Fin.castSucc i) else MvPolynomial.X k)
        (MvPolynomial.aeval (fun j : Fin (n + 1) => MvPolynomial.C (a j) * MvPolynomial.X j)
          (MvPolynomial.rename e (φ • B + (1 : ℝ) • A)
            + MvPolynomial.X (Fin.last n) * MvPolynomial.rename e ℓ))) := by
    exact closure_diagonalize (n := n + 1) (i := Fin.castSucc i) (j := Fin.last n) hne
      (MvPolynomial.aeval (fun j : Fin (n + 1) => MvPolynomial.C (a j) * MvPolynomial.X j)
        (MvPolynomial.rename e (φ • B + (1 : ℝ) • A)
          + MvPolynomial.X (Fin.last n) * MvPolynomial.rename e ℓ)) hD
  have hsmulR : ∀ (c : ℝ) (r : MvPolynomial (Fin (n + 1)) ℝ),
      c • r = MvPolynomial.C c * r := by
    intro c r
    apply MvPolynomial.ext
    intro m
    rw [MvPolynomial.coeff_C_mul]
    simp
  have hfix_dil : ∀ s : MvPolynomial (Fin n) ℝ,
      MvPolynomial.aeval (fun j : Fin (n + 1) => MvPolynomial.C (a j) * MvPolynomial.X j)
        (MvPolynomial.rename e s) = MvPolynomial.rename e s := by
    intro s
    rw [MvPolynomial.aeval_rename]
    have heq : (fun j : Fin (n + 1) => MvPolynomial.C (a j) * MvPolynomial.X j) ∘ e
        = (fun i0 : Fin n => MvPolynomial.X (e i0)) := by
      funext i0
      have h : Fin.castSucc i0 ≠ Fin.last n := by
        intro hh
        have hval : (Fin.castSucc i0).val = (Fin.last n).val := congrArg Fin.val hh
        have hcast : (Fin.castSucc i0).val = i0.val := by simp [Fin.castSucc]
        have hlast : (Fin.last n).val = n := by simp [Fin.last]
        rw [hcast, hlast] at hval
        omega
      simp [e, a, h]
    rw [heq]
    have hR : MvPolynomial.aeval (fun i0 : Fin n => (MvPolynomial.X (Fin.castSucc i0) : cdmRM (n + 1))) s =
        MvPolynomial.rename e s := by
      classical
      induction s using MvPolynomial.induction_on with
      | C a => simp
      | add p q hp hq => rw [map_add, map_add, hp, hq]
      | mul_X p t hp => rw [map_mul, map_mul, hp]; simp [e]
    simpa [e] using hR
  have hfix_diag : ∀ s : MvPolynomial (Fin n) ℝ,
      MvPolynomial.aeval (fun k : Fin (n + 1) =>
          if k = Fin.last n then MvPolynomial.X (Fin.castSucc i) else MvPolynomial.X k)
        (MvPolynomial.rename e s) = MvPolynomial.rename e s := by
    intro s
    rw [MvPolynomial.aeval_rename]
    have heq : (fun k : Fin (n + 1) => (if k = Fin.last n then (MvPolynomial.X (Fin.castSucc i) : cdmRM (n + 1)) else (MvPolynomial.X k : cdmRM (n + 1)))) ∘ e
        = (fun i0 : Fin n => (MvPolynomial.X (e i0) : cdmRM (n + 1))) := by
      funext i0
      have h : Fin.castSucc i0 ≠ Fin.last n := by
        intro hh
        have hval : (Fin.castSucc i0).val = (Fin.last n).val := congrArg Fin.val hh
        have hcast : (Fin.castSucc i0).val = i0.val := by simp [Fin.castSucc]
        have hlast : (Fin.last n).val = n := by simp [Fin.last]
        rw [hcast, hlast] at hval
        omega
      simp [e, h]
    rw [heq]
    have hR : MvPolynomial.aeval (fun i0 : Fin n => (MvPolynomial.X (Fin.castSucc i0) : cdmRM (n + 1))) s =
        MvPolynomial.rename e s := by
      classical
      induction s using MvPolynomial.induction_on with
      | C a => simp
      | add p q hp hq => rw [map_add, map_add, hp, hq]
      | mul_X p t hp => rw [map_mul, map_mul, hp]; simp [e]
    simpa [e] using hR
  let q' : MvPolynomial (Fin n) ℝ := φ • B + (1 : ℝ) • A
  have hdil_last : MvPolynomial.aeval
        (fun j : Fin (n + 1) => MvPolynomial.C (a j) * MvPolynomial.X j)
        (MvPolynomial.X (Fin.last n) * MvPolynomial.rename e ℓ) =
        MvPolynomial.C ψ * MvPolynomial.X (Fin.last n) * MvPolynomial.rename e ℓ := by
      rw [map_mul]
      have hx : MvPolynomial.aeval (fun j : Fin (n + 1) => MvPolynomial.C (a j) * MvPolynomial.X j)
          (MvPolynomial.X (Fin.last n) : cdmRM (n + 1)) = MvPolynomial.C ψ * (MvPolynomial.X (Fin.last n) : cdmRM (n + 1)) := by
        simp [a]
      rw [hx]
      rw [hfix_dil ℓ]
  have hstage : MvPolynomial.aeval
        (fun j : Fin (n + 1) => MvPolynomial.C (a j) * MvPolynomial.X j)
        (MvPolynomial.rename e q' + MvPolynomial.X (Fin.last n) * MvPolynomial.rename e ℓ) =
        MvPolynomial.rename e q' + MvPolynomial.C ψ * MvPolynomial.X (Fin.last n) * MvPolynomial.rename e ℓ := by
      rw [map_add, hfix_dil q', hdil_last]
  have hcomp : MvPolynomial.aeval (fun k : Fin (n + 1) =>
          if k = Fin.last n then MvPolynomial.X (Fin.castSucc i) else MvPolynomial.X k)
        (MvPolynomial.aeval (fun j : Fin (n + 1) => MvPolynomial.C (a j) * MvPolynomial.X j)
          (MvPolynomial.rename e q' + MvPolynomial.X (Fin.last n) * MvPolynomial.rename e ℓ))
      = MvPolynomial.rename e T := by
    calc
      MvPolynomial.aeval (fun k : Fin (n + 1) =>
            if k = Fin.last n then MvPolynomial.X (Fin.castSucc i) else MvPolynomial.X k)
          (MvPolynomial.aeval (fun j : Fin (n + 1) => MvPolynomial.C (a j) * MvPolynomial.X j)
            (MvPolynomial.rename e q' + MvPolynomial.X (Fin.last n) * MvPolynomial.rename e ℓ))
          = MvPolynomial.aeval (fun k : Fin (n + 1) =>
              if k = Fin.last n then MvPolynomial.X (Fin.castSucc i) else MvPolynomial.X k)
            (MvPolynomial.rename e q' + MvPolynomial.C ψ * MvPolynomial.X (Fin.last n) * MvPolynomial.rename e ℓ) := by rw [hstage]
      _ = MvPolynomial.rename e q' + MvPolynomial.C ψ * MvPolynomial.X (Fin.castSucc i) * MvPolynomial.rename e ℓ := by
            rw [map_add, map_mul]
            rw [hfix_diag q']
            rw [hfix_diag ℓ]
            have hdiag_last : MvPolynomial.aeval (fun k : Fin (n + 1) =>
                  if k = Fin.last n then MvPolynomial.X (Fin.castSucc i) else MvPolynomial.X k)
                  (MvPolynomial.C ψ * MvPolynomial.X (Fin.last n)) =
                MvPolynomial.C ψ * MvPolynomial.X (Fin.castSucc i) := by
              rw [map_mul]
              simp
            rw [hdiag_last]
      _ = MvPolynomial.rename e T := by
            have hsmulN : ∀ (c : ℝ) (r : MvPolynomial (Fin n) ℝ), c • r = MvPolynomial.C c * r := by
              intro c r
              apply MvPolynomial.ext
              intro m
              rw [MvPolynomial.coeff_C_mul]
              simp
            have hqeq : MvPolynomial.rename e q' =
                MvPolynomial.rename e A + MvPolynomial.rename e (MvPolynomial.C φ * B) := by
              dsimp [q']
              rw [map_add]
              rw [hsmulN]
              rw [one_smul]
              ring
            rw [hqeq]
            dsimp [T]
            simp only [map_add, map_mul, MvPolynomial.rename_X, MvPolynomial.rename_C]
            simp [e]
  have hT : IsStable T := by
    have hR : IsStable (MvPolynomial.rename e T) := by
      rwa [hcomp] at hDG
    exact cdm_IsStable_rename_castSucc T hR
  -- nonnegativity of the coefficients of T
  have hSℓ : (⟨MvPolynomial.pderiv i B, (⟨B, h.2.pderiv⟩ : H n 2).2.pderiv⟩ : H n 1) ∈ S n 1 := by
    exact pderiv_stable_mem_S (n := n) (d := 2) (hd := by norm_num)
      (⟨B, h.2.pderiv⟩ : H n 2) (pderiv_mem_S_of_mem_L_three n h hh j) i
  have hnnℓ : ∀ m : Fin n →₀ ℕ, 0 ≤ ℓ.coeff m := by
    intro m
    have h := hSℓ.2 m
    dsimp [B, ℓ] at h ⊢
    exact h
  have hnnXℓ : ∀ m : Fin n →₀ ℕ, 0 ≤ (MvPolynomial.X i * ℓ).coeff m :=
    coeff_X_mul_nonneg_coeff n i ℓ hnnℓ
  have hnnT : ∀ m : Fin n →₀ ℕ, 0 ≤ T.coeff m := by
    intro m
    dsimp [T]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add, mul_assoc]
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul]
    exact add_nonneg (add_nonneg (hnnA m) (mul_nonneg hφ (hnnB m)))
      (mul_nonneg hψ (hnnXℓ m))
  have hhomT : T.IsHomogeneous 2 := by
    dsimp [T, A, B, ℓ]
    exact cdm_deform_hom_two n i j h φ ψ
  let u : H n 2 := ⟨T, by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact hhomT⟩
  have hS : u ∈ S n 2 := by
    change IsStable u.1 ∧ ∀ m : Fin n →₀ ℕ, 0 ≤ u.1.coeff m
    constructor
    · dsimp [u]
      exact hT
    · intro m
      dsimp [u]
      exact hnnT m
  refine ⟨u, hS, ?_⟩
  dsimp [u, T, A, B, ℓ]

/-! ## Main statement -/

theorem cubic_deform_mem_S2 (n : ℕ) (hn : 0 < n) (φ ψ : ℝ) (hφ : 0 ≤ φ) (hψ : 0 ≤ ψ)
    (i j : Fin n) (h : Commons.LorentzianPolynomials.H n 3)
    (hh : h ∈ Commons.LorentzianPolynomials.L n 3) :
    ∃ u : Commons.LorentzianPolynomials.H n 2,
      u ∈ Commons.LorentzianPolynomials.S n 2 ∧
        u.1 = MvPolynomial.pderiv i h.1 +
          MvPolynomial.C φ * MvPolynomial.pderiv j h.1 +
            MvPolynomial.C ψ * MvPolynomial.X i *
              MvPolynomial.pderiv i (MvPolynomial.pderiv j h.1) := by
  classical
  by_cases hℓ0 : MvPolynomial.pderiv i (MvPolynomial.pderiv j h.1) = 0
  · -- degenerate: two-term lemma; the `X_i`-term is zero
    rcases two_term_degenerate_mem_S (n := n) hn i j h hh hℓ0 φ hφ with ⟨u, hSu, hu⟩
    refine ⟨u, hSu, ?_⟩
    rw [hℓ0]
    simp
    exact hu
  · -- non-degenerate
    exact cdm_nondeg_mem_S i j h hh φ ψ hφ hψ hℓ0

end
end Commons.LorentzianPolynomials
