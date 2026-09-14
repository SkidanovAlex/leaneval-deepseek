import Mathlib
import Submission.Subspace.RothBase
import Submission.Subspace.RothSetup
import Submission.Subspace.RothSplit
import Submission.Subspace.RothIndexSplit
import Submission.Subspace.PderivDiv
import Submission.Subspace.IndexScale
import Submission.Commons.Algebra.MvPolynomial.degreeOf_det_le
import Submission.Commons.NumberTheory.Height.MvPolynomial.logHeight_gP_of_coeff_bound
import Submission.Commons.NumberTheory.Height.MvPolynomial.logHeight_gP_rename
import Submission.Commons.NumberTheory.Height.MvPolynomial.polyHeight_int_tensor_eq_fin
import Submission.Commons.Algebra.MvPolynomial.pderivIter_rename
import Submission.Commons.Algebra.MvPolynomial.uniqueAlgEquiv_pderivIter

set_option maxHeartbeats 1600000

/-!
# The multivariate Roth lemma

This file assembles the multivariate Roth lemma from the Wronskian/index machinery
(`RothSetup`, `RothWronskian`, `RothIndexSplit`, `RothBase`) and the divided-derivative height
bounds (`PderivDiv`).

The statement proved is `roth_lemma` (see `Submission/Work/RothGoal.lean` for the goal statement):
for `P ∈ ℤ[x_0,…,x_{m-1}]` with `deg_{x_i} P ≤ r_i ≥ 1`, a point `β`, and `0 < η ≤ 1/2` with
rapidly growing weights `r_i ≤ η^{2^{m-1}(j-i)} r_j` (`i ≤ j`) and

`η^{2^{m-1}} · ⨅_i (r_i · h(β_i)) ≥ h(P) + 100 m (∑_i r_i)`,

one has `Ind_{β,r}(P) ≤ 4 m η`.
-/

open scoped BigOperators Matrix

namespace Submission.Subspace

open MvPolynomial
open Commons.NumberTheory.Height.MvPolynomial (gP)

variable {σ : Type*}

/-! ### Scaling of determinants -/

/-- Determinant of a matrix obtained from `A` by scaling row `i` by `r i` and column `j` by
`c j`. -/
lemma det_scaled {K : Type*} [CommRing K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (r c : ι → K) :
    (Matrix.of fun i j => r i * A i j * c j).det = (∏ i, r i) * (∏ j, c j) * A.det := by
  have h : (Matrix.of fun i j => r i * A i j * c j)
      = Matrix.diagonal r * A * Matrix.diagonal c := by
    ext i j
    show r i * A i j * c j = (Matrix.diagonal r * A * Matrix.diagonal c) i j
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single j]
    · rw [Matrix.diagonal_mul, Matrix.diagonal_apply_eq]
    · intro b _ hb
      rw [Matrix.diagonal_mul, Matrix.diagonal_apply_ne _ hb, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
  ring

/-! ### The product of factorials -/

/-- `Fin.succ`-image multi-indices and multiples of `e_0` have disjoint support. -/
lemma disjoint_mapDomain_succ_smul_single (n j : ℕ) (m : Fin n →₀ ℕ) :
    ∀ t : Fin (n + 1), (m.mapDomain Fin.succ) t = 0 ∨
      ((j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) t = 0 := by
  intro t
  rcases Fin.eq_zero_or_eq_succ t with h | ⟨t', rfl⟩
  · subst h
    left
    exact Finsupp.mapDomain_of_notMem_range m 0 (by rintro ⟨a, ha⟩; exact Fin.succ_ne_zero a ha)
  · right
    rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne (Fin.succ_ne_zero t'), smul_zero]

/-- The product of factorials `ν! = ∏ i, (ν i)!` is multiplicative on Finsupps with pointwise
disjoint support. -/
lemma facOf_add_of_disjoint [Fintype σ] {m n : σ →₀ ℕ}
    (hpt : ∀ i : σ, m i = 0 ∨ n i = 0) : facOf (m + n) = facOf m * facOf n := by
  classical
  have hpt2 : ∀ i : σ, ((m + n) i).factorial = (m i).factorial * (n i).factorial := by
    intro i
    rw [Finsupp.add_apply]
    rcases hpt i with h0 | h0 <;> rw [h0] <;> simp
  rw [facOf, facOf, facOf, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun i _ => hpt2 i)

lemma facOf_mapDomain_succ_add_smul_single (n j : ℕ) (m : Fin n →₀ ℕ) :
    facOf (m.mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) =
      facOf (m.mapDomain Fin.succ) * j.factorial := by
  rw [facOf_add_of_disjoint (disjoint_mapDomain_succ_smul_single n j m)]
  congr 1
  rw [facOf, Finset.prod_eq_single (0 : Fin (n + 1))]
  · rw [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  · intro b _ hb
    rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne hb, smul_zero, Nat.factorial_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A partial derivative in a variable outside the range of the renaming annihilates the
renamed polynomial as a *degree*: `degreeOf i (rename f P) = 0` when `i ∉ range f`. -/
lemma degreeOf_rename_eq_zero_of_notMem_range {R : Type*} [CommSemiring R] {σ τ : Type*}
    (f : σ → τ) {i : τ} (hi : i ∉ Set.range f) (P : MvPolynomial σ R) :
    MvPolynomial.degreeOf i (MvPolynomial.rename f P) = 0 := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.rename_C, MvPolynomial.degreeOf_C]
  | add p q hp hq =>
      rw [map_add]
      have h := MvPolynomial.degreeOf_add_le i (MvPolynomial.rename f p) (MvPolynomial.rename f q)
      rw [hp, hq, max_self] at h
      exact le_antisymm h (Nat.zero_le _)
  | mul_X p k hp =>
      have hk : f k ≠ i := fun h => hi ⟨k, h⟩
      rw [map_mul, MvPolynomial.rename_X]
      have h := MvPolynomial.degreeOf_mul_le i (MvPolynomial.rename f p) (MvPolynomial.X (f k))
      rw [hp, MvPolynomial.degreeOf_X_of_ne (Ne.symm hk), add_zero] at h
      exact le_antisymm h (Nat.zero_le _)

/-- `uniqueAlgEquiv` is inverse to `aeval (X 0)` for polynomials in one variable. -/
lemma uniqueAlgEquiv_symm_eq_aeval {K : Type*} [CommSemiring K] (ψ : Polynomial K) :
    (MvPolynomial.uniqueAlgEquiv K (Fin 1)).symm ψ =
      Polynomial.aeval (A := MvPolynomial (Fin 1) K) (MvPolynomial.X 0) ψ := by
  rw [MvPolynomial.uniqueAlgEquiv_symm_apply, Polynomial.aeval_def, MvPolynomial.algebraMap_eq,
    show (default : Fin 1) = (0 : Fin 1) from Subsingleton.elim _ _]


/-! ### Height and degree bounds for the divided Wronskian -/

/-- The height of `∂^ν P / ν!` grows by at most `(∑_j r_j) log 2` when `deg_{x_j} P ≤ r_j`
(Schmidt's "ht of derivative"). -/
lemma hZ_pderivIterDiv_le [Fintype σ] [DecidableEq σ] (r : σ → ℕ) (ν : σ →₀ ℕ)
    (P : MvPolynomial σ ℤ) (h : ∀ t ∈ P.support, ∀ j, t j ≤ r j) :
    hZ (pderivIterDiv ν P) ≤ hZ P + ((∑ j : σ, r j : ℕ) : ℝ) * Real.log 2 := by
  have hQ : ∀ n : σ →₀ ℕ,
      MvPolynomial.coeff n ((pderivIterDiv ν P).map (Int.castRingHom ℚ)) =
        MvPolynomial.coeff (n + ν) (P.map (Int.castRingHom ℚ)) *
          ∏ i : σ, Nat.choose ((n + ν) i) (ν i) := by
    intro n
    rw [MvPolynomial.coeff_map, coeff_pderivIterDiv, MvPolynomial.coeff_map, map_mul]
    exact congrArg (fun x : ℚ => (Int.castRingHom ℚ) (MvPolynomial.coeff (n + ν) P) * x)
      (Int.cast_natCast _)
  have h' : ∀ t ∈ (P.map (Int.castRingHom ℚ)).support, ∀ j : σ, t j ≤ r j := by
    intro t ht j
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map] at ht
    refine h t (MvPolynomial.mem_support_iff.mpr ?_) j
    intro h0
    exact ht (by rw [h0, map_zero])
  have hkey := Commons.NumberTheory.Height.MvPolynomial.logHeight_gP_of_coeff_bound r ν
    (P.map (Int.castRingHom ℚ)) ((pderivIterDiv ν P).map (Int.castRingHom ℚ)) hQ h'
  simpa [hZ] using hkey

/-- **Height of the divided Wronskian determinant.** -/
theorem hZ_det_pderivIterDiv_le {n k : ℕ} (P : MvPolynomial (Fin (n + 1)) ℤ)
    (r : Fin (n + 1) → ℕ) (hdeg : ∀ t ∈ P.support, ∀ j, t j ≤ r j)
    (μ : Fin k → Fin n →₀ ℕ) :
    hZ (Matrix.of (fun i j : Fin k => pderivIterDiv
        ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P)).det ≤
      (k : ℝ) * hZ P +
        ((2 * k * (∑ j : Fin (n + 1), r j) + (n + 1) * k : ℕ) : ℝ) * Real.log 2 +
        Real.log (Nat.factorial k) := by
  classical
  set S : ℝ := ((∑ j : Fin (n + 1), r j : ℕ) : ℝ) with hS
  set H : ℝ := hZ P + S * Real.log 2 with hH
  have hH0 : 0 ≤ H := by
    have h1 : 0 ≤ hZ P := by rw [hZ_eq]; exact logHeight_gP_nonneg _
    rw [hH, hS]
    positivity
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  set L : ℝ := ((k * (∑ j : Fin (n + 1), r j) + (n + 1) * k : ℕ) : ℝ) * Real.log 2 with hL
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hentry : ∀ i j : Fin k, hZ (pderivIterDiv
      ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P) ≤ H := by
    intro i j
    have h1 := hZ_pderivIterDiv_le r
      ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P hdeg
    rw [hH, hS]
    exact h1
  have hprod : ∀ π : Equiv.Perm (Fin k), hZ (Finset.univ.prod fun i => pderivIterDiv
      ((μ (π i)).mapDomain Fin.succ + (i : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P) ≤
      H * k + L := by
    intro π
    have hd : ∀ i : Fin k, ∀ t ∈ (pderivIterDiv
        ((μ (π i)).mapDomain Fin.succ + (i : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P).support,
        ∀ j, t j ≤ r j := fun i => support_pderivIterDiv_degree_le _ P r hdeg
    have h1 := hZ_prod_le (σ := Fin (n + 1)) (fun i : Fin k => pderivIterDiv
        ((μ (π i)).mapDomain Fin.succ + (i : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P) r hd
    have h2 : (∑ i : Fin k, hZ (pderivIterDiv
        ((μ (π i)).mapDomain Fin.succ + (i : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P)) ≤
        (k : ℝ) * H := by
      calc (∑ i : Fin k, hZ (pderivIterDiv
            ((μ (π i)).mapDomain Fin.succ + (i : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P))
          ≤ ∑ _i : Fin k, H := Finset.sum_le_sum fun i _ => hentry (π i) i
        _ = (k : ℝ) * H := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hcard : ((k * (∑ j : Fin (n + 1), r j) + (n + 1) * (k - 1) : ℕ) : ℝ) * Real.log 2 ≤ L := by
      rw [hL]
      refine mul_le_mul_of_nonneg_right ?_ hlog2
      refine Nat.cast_le.mpr ?_
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) _
    simp only [Fintype.card_fin] at h1
    linarith [h1, h2, hcard]
  have hmain := hZ_det_le (σ := Fin (n + 1)) (A := Matrix.of (fun i j : Fin k => pderivIterDiv
      ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P)) H L hH0 hL0
    hprod
  have hHk : H * (k : ℝ) = (k : ℝ) * hZ P + (k : ℝ) * S * Real.log 2 := by rw [hH]; ring
  rw [hHk, hS, hL] at hmain
  have hgoal : (k : ℝ) * ((∑ j : Fin (n + 1), r j : ℕ) : ℝ) * Real.log 2 +
      ((k * (∑ j : Fin (n + 1), r j) + (n + 1) * k : ℕ) : ℝ) * Real.log 2 =
      ((2 * k * (∑ j : Fin (n + 1), r j) + (n + 1) * k : ℕ) : ℝ) * Real.log 2 := by
    push_cast
    ring
  linarith [hmain, hgoal]

/-- **Degree of the divided Wronskian determinant.** -/
theorem degreeOf_det_pderivIterDiv_le {n k : ℕ} (P : MvPolynomial (Fin (n + 1)) ℤ)
    (r : Fin (n + 1) → ℕ) (hdeg : ∀ t ∈ P.support, ∀ j, t j ≤ r j)
    (μ : Fin k → Fin n →₀ ℕ) (t : Fin (n + 1)) :
    MvPolynomial.degreeOf t (Matrix.of (fun i j : Fin k => pderivIterDiv
        ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P)).det ≤
      k * r t := by
  have hmain := Commons.Algebra.MvPolynomial.degreeOf_det_le t (Matrix.of (fun i j : Fin k =>
      pderivIterDiv ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P))
    (r t) (fun i j => le_trans (degreeOf_pderivIterDiv_le _ P t)
      (MvPolynomial.degreeOf_le_iff.mpr (fun m hm => hdeg m hm t)))
  simpa using hmain


/-! ### The Roth induction -/

private lemma iInf_le_fin {ι : Type*} [Fintype ι] (f : ι → ℝ) (i : ι) : (⨅ j, f j) ≤ f i :=
  ciInf_le (Set.Finite.bddBelow (Set.finite_range f)) i

private lemma logHeight₁_nonneg' {K : Type*} [Field K] [Height.AdmissibleAbsValues K] (x : K) :
    0 ≤ Height.logHeight₁ x := by
  rw [Height.logHeight₁_eq_log_mulHeight₁]
  exact Real.log_nonneg (Height.one_le_mulHeight₁ x)

private lemma facOf_pos {σ : Type*} [Fintype σ] (ν : σ →₀ ℕ) : 0 < facOf ν := by
  rw [facOf]
  exact Finset.prod_pos fun i _ => Nat.factorial_pos _

private lemma prod_C_eq_C_prod {R : Type*} [CommSemiring R] {σ ι : Type*} (s : Finset ι)
    (f : ι → R) :
    (∏ i ∈ s, (MvPolynomial.C (f i) : MvPolynomial σ R)) = MvPolynomial.C (∏ i ∈ s, f i) :=
  (map_prod (MvPolynomial.C : R →+* MvPolynomial σ R) f s).symm

/-- The multivariate Roth lemma in the "`Fin (n+1)`" formulation, proved by strong induction
on the number `n` of "extra" variables. -/
private theorem roth_lemma_aux : ∀ n : ℕ, ∀ (P : MvPolynomial (Fin (n + 1)) ℤ), P ≠ 0 →
    ∀ (r : Fin (n + 1) → ℕ), (∀ i, 1 ≤ r i) → (∀ t ∈ P.support, ∀ i, t i ≤ r i) →
    ∀ (β : Fin (n + 1) → ℚ) (η : ℝ), 0 < η → η ≤ 1 / 2 →
    (∀ i j : Fin (n + 1), i ≤ j →
      (r i : ℝ) ≤ η ^ (2 ^ n * ((j : ℕ) - (i : ℕ))) * (r j : ℝ)) →
    η ^ (2 ^ n) * (⨅ i : Fin (n + 1), (r i : ℝ) * Height.logHeight₁ (β i)) ≥
      hZ P + 100 * ((n + 1 : ℕ) : ℝ) * (∑ i : Fin (n + 1), (r i : ℝ)) →
    index β r (P.map (Int.castRingHom ℚ)) ≤ 4 * ((n + 1 : ℕ) : ℝ) * η := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P hP r hr hdeg β η hη0 hη hratio hcond
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      have hle : (⨅ i : Fin (0 + 1), (r i : ℝ) * Height.logHeight₁ (β i)) ≤
          (r 0 : ℝ) * Height.logHeight₁ (β 0) := iInf_le_fin _ 0
      have hcond' : η * ((r 0 : ℝ) * Height.logHeight₁ (β 0)) ≥ hZ P + 100 * (r 0 : ℝ) := by
        have hsum1 : (∑ i : Fin (0 + 1), (r i : ℝ)) = (r 0 : ℝ) := Fin.sum_univ_one _
        have hc : (((0 + 1 : ℕ)) : ℝ) = 1 := by norm_num
        simp only [pow_zero, pow_one, hsum1, hc, one_mul] at hcond
        have h := mul_le_mul_of_nonneg_left hle (le_of_lt hη0)
        linarith [hcond, h]
      have hbase := index_fin_one_le hP r (hr 0) β η hη0 hcond'
      simpa using hbase
    · -- induction step
      have hn1 : 1 ≤ n := hnpos
      set Pq : MvPolynomial (Fin (n + 1)) ℚ := P.map (Int.castRingHom ℚ) with hPqdef
      have hPqne : Pq ≠ 0 := by
        rw [hPqdef]
        intro h
        exact hP (MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
          (h.trans (map_zero _).symm))
      obtain ⟨k, φ, ψ₀, μ, hdec₀, hμ, hdetφ, hdetψ, hk⟩ := exists_roth_data (K := ℚ) Pq
      have hkpos : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | hpos
        · exfalso
          have hsum0 : (∑ j : Fin k, MvPolynomial.rename Fin.succ (φ j) *
              Polynomial.aeval (A := MvPolynomial (Fin (n + 1)) ℚ) (MvPolynomial.X 0)
                (ψ₀ j)) = 0 := by
            have hempty : (Finset.univ : Finset (Fin k)) = ∅ := by
              rw [h0]
              exact Finset.univ_eq_empty
            simp [hempty]
          exact hPqne (hdec₀.trans hsum0)
        · exact hpos
      have hdeg0 : MvPolynomial.degreeOf (0 : Fin (n + 1)) Pq ≤ r 0 := by
        rw [MvPolynomial.degreeOf_le_iff]
        intro m hm
        rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map] at hm
        refine hdeg m (MvPolynomial.mem_support_iff.mpr ?_) 0
        intro h0
        exact hm (by rw [h0, map_zero])
      have hk_le : k ≤ r 0 + 1 := le_trans (hk hPqne) (Nat.add_le_add_right hdeg0 1)
      have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hkpos
      set ψ : Fin k → MvPolynomial (Fin 1) ℚ :=
        fun j => (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).symm (ψ₀ j) with hψdef
      have hψeq : ∀ j, Polynomial.aeval (A := MvPolynomial (Fin 1) ℚ) (MvPolynomial.X 0) (ψ₀ j)
          = ψ j := by
        intro j
        rw [hψdef]
        exact (uniqueAlgEquiv_symm_eq_aeval (ψ₀ j)).symm
      have hdec : Pq = ∑ j, MvPolynomial.rename Fin.succ (φ j) *
          MvPolynomial.rename (fun _ : Fin 1 => (0 : Fin (n + 1))) (ψ j) := by
        rw [hdec₀]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [aeval_X_zero_eq_rename, hψeq j]
      have hdetψ' : (Matrix.of fun i j : Fin k => Commons.Algebra.MvPolynomial.pderivIter
          ((i : ℕ) • Finsupp.single (0 : Fin 1) 1) (ψ j)).det ≠ 0 := by
        intro hc
        have h1 : (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1))
            (Matrix.of fun i j : Fin k => Commons.Algebra.MvPolynomial.pderivIter
              ((i : ℕ) • Finsupp.single (0 : Fin 1) 1) (ψ j)).det = 0 := by rw [hc, map_zero]
        rw [AlgEquiv.map_det] at h1
        have h2 : (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).mapMatrix
              (Matrix.of fun i j : Fin k => Commons.Algebra.MvPolynomial.pderivIter
                ((i : ℕ) • Finsupp.single (0 : Fin 1) 1) (ψ j))
            = Matrix.of fun i j : Fin k => (Polynomial.derivative^[(i : ℕ)]) (ψ₀ j) := by
          apply Matrix.ext
          intro i j
          rw [AlgEquiv.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
          rw [show (i : ℕ) • Finsupp.single (0 : Fin 1) 1 =
              (i : ℕ) • Finsupp.single (default : Fin 1) 1 from by
            rw [show (0 : Fin 1) = default from Subsingleton.elim _ _]]
          rw [Commons.Algebra.MvPolynomial.uniqueAlgEquiv_pderivIter, AlgEquiv.apply_symm_apply]
          simp
        rw [h2] at h1
        exact hdetψ h1
      set Bm : Matrix (Fin k) (Fin k) (MvPolynomial (Fin (n + 1)) ℚ) := Matrix.of fun i j : Fin k =>
        Commons.Algebra.MvPolynomial.pderivIter
          ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) Pq
        with hBmdef
      set A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin (n + 1)) ℤ) := Matrix.of fun i j : Fin k =>
        pderivIterDiv ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P
        with hAdef
      set V : MvPolynomial (Fin (n + 1)) ℤ := A.det with hVdef
      set U₁ : MvPolynomial (Fin 1) ℚ := (Matrix.of fun i j : Fin k =>
        Commons.Algebra.MvPolynomial.pderivIter ((i : ℕ) • Finsupp.single (0 : Fin 1) 1)
          (ψ j)).det with hU₁def
      set U₂ : MvPolynomial (Fin n) ℚ := (Matrix.of fun i j : Fin k =>
        Commons.Algebra.MvPolynomial.pderivIter (μ i) (φ j)).det with hU₂def
      have hU₁ne : U₁ ≠ 0 := by rw [hU₁def]; exact hdetψ'
      have hU₂ne : U₂ ≠ 0 := by rw [hU₂def]; exact hdetφ
      have hBfac : Bm.det = MvPolynomial.rename Fin.succ U₂ *
          MvPolynomial.rename (fun _ : Fin 1 => (0 : Fin (n + 1))) U₁ := by
        rw [hBmdef, hU₂def, hU₁def]
        exact det_wronskian_factorization_rename Pq φ ψ μ hdec
      have hBdet : Bm.det ≠ 0 := by
        rw [hBmdef]
        exact det_wronskian_mv_ne_zero Pq φ ψ μ hdec hdetφ hdetψ'
      set rs : Fin k → ℚ := fun i => ((facOf ((μ i).mapDomain Fin.succ) : ℕ) : ℚ)⁻¹ with hrsdef
      set cs : Fin k → ℚ := fun j => (((j : ℕ).factorial : ℕ) : ℚ)⁻¹ with hcsdef
      set c₀ : ℚ := (∏ i, rs i) * (∏ j, cs j) with hc₀def
      have hc₀ne : c₀ ≠ 0 := by
        rw [hc₀def]
        refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
          (Finset.prod_ne_zero_iff.mpr fun j _ => ?_)
        · rw [hrsdef]
          exact inv_ne_zero (Nat.cast_ne_zero.mpr (ne_of_gt (facOf_pos _)))
        · rw [hcsdef]
          exact inv_ne_zero (Nat.cast_ne_zero.mpr (ne_of_gt (Nat.factorial_pos _)))
      have hc₀C : (∏ i, (MvPolynomial.C (rs i) : MvPolynomial (Fin (n + 1)) ℚ)) *
            (∏ j, (MvPolynomial.C (cs j) : MvPolynomial (Fin (n + 1)) ℚ)) =
          (MvPolynomial.C c₀ : MvPolynomial (Fin (n + 1)) ℚ) := by
        rw [prod_C_eq_C_prod, prod_C_eq_C_prod, ← map_mul, ← hc₀def]
      have hAmat : A.map (MvPolynomial.map (Int.castRingHom ℚ)) =
          Matrix.of fun i j : Fin k => MvPolynomial.C (rs i) * Bm i j * MvPolynomial.C (cs j) := by
        apply Matrix.ext
        intro i j
        simp only [Matrix.map_apply, Matrix.of_apply, hAdef, hBmdef, hrsdef, hcsdef]
        rw [← pderivIterDiv_map, pderivIterDiv_eq_inv_mul, facOf_mapDomain_succ_add_smul_single,
          Nat.cast_mul, mul_inv, map_mul]
        ring
      have hVmap : V.map (Int.castRingHom ℚ) =
          (MvPolynomial.C c₀ : MvPolynomial (Fin (n + 1)) ℚ) * Bm.det := by
        have h1 : V.map (Int.castRingHom ℚ) =
            (A.map (MvPolynomial.map (Int.castRingHom ℚ))).det := by
          rw [hVdef, RingHom.map_det, RingHom.mapMatrix_apply]
        rw [h1, hAmat, det_scaled, ← hc₀C]
      have hCne : (MvPolynomial.C c₀ : MvPolynomial (Fin 1) ℚ) ≠ 0 := by
        intro h
        exact hc₀ne (by simpa using congrArg (fun P => MvPolynomial.coeff 0 P) h)
      have hVfac : V.map (Int.castRingHom ℚ) =
          MvPolynomial.rename (fun _ : Fin 1 => (0 : Fin (n + 1)))
              ((MvPolynomial.C c₀ : MvPolynomial (Fin 1) ℚ) * U₁) *
            MvPolynomial.rename Fin.succ U₂ := by
        rw [hVmap, hBfac]
        simp only [map_mul, MvPolynomial.rename_C]
        ring
      obtain ⟨c, W₁, W₂, hc, hW₁, hW₂, hU₁eq, hU₂eq, hVeq, hZh⟩ :=
        exists_integral_split V ((MvPolynomial.C c₀ : MvPolynomial (Fin 1) ℚ) * U₁) U₂
          (mul_ne_zero hCne hU₁ne) hU₂ne hVfac
      have hW₁qne : W₁.map (Int.castRingHom ℚ) ≠ 0 := fun h =>
        hW₁ (MvPolynomial.map_injective _ Int.cast_injective (by rw [h, map_zero]))
      have hW₂qne : W₂.map (Int.castRingHom ℚ) ≠ 0 := fun h =>
        hW₂ (MvPolynomial.map_injective _ Int.cast_injective (by rw [h, map_zero]))
      have hZV : hZ V ≤ (k : ℝ) * hZ P +
          ((2 * k * (∑ j : Fin (n + 1), r j) + (n + 1) * k : ℕ) : ℝ) * Real.log 2 +
          Real.log (Nat.factorial k) := by
        rw [hVdef, hAdef]
        exact hZ_det_pderivIterDiv_le P r hdeg μ
      have hZW₁ : 0 ≤ hZ W₁ := by rw [hZ_eq]; exact logHeight_gP_nonneg _
      have hZW₂ : 0 ≤ hZ W₂ := by rw [hZ_eq]; exact logHeight_gP_nonneg _
      have hW₂le : hZ W₂ ≤ hZ V := by linarith [hZh, hZW₁]
      have hW₁le : hZ W₁ ≤ hZ V := by linarith [hZh, hZW₂]
      set S : ℝ := ∑ i : Fin (n + 1), (r i : ℝ) with hSdef
      have hr0S : (r 0 : ℝ) ≤ S := by
        rw [hSdef]
        exact Finset.single_le_sum (s := Finset.univ) (f := fun i : Fin (n + 1) => (r i : ℝ))
          (fun i _ => by positivity) (Finset.mem_univ (0 : Fin (n + 1)))
      have hS1 : 1 ≤ S := le_trans (by exact_mod_cast hr 0) hr0S
      have hloss : ((2 * k * (∑ j : Fin (n + 1), r j) + (n + 1) * k : ℕ) : ℝ) * Real.log 2 +
          Real.log (Nat.factorial k) ≤ 100 * (k : ℝ) * S := by
        have hkR : (0:ℝ) ≤ (k : ℝ) := by positivity
        have hfact : Real.log (Nat.factorial k) ≤ (k : ℝ) * Real.log k := by
          rw [← Real.log_pow]
          exact Real.log_le_log (by exact_mod_cast Nat.factorial_pos k)
            (by exact_mod_cast Nat.factorial_le_pow k)
        have hkS : (k : ℝ) ≤ S + 1 := by
          have h1 : (k : ℝ) ≤ (r 0 : ℝ) + 1 := by exact_mod_cast hk_le
          linarith
        have hlogk : Real.log k ≤ S := by
          have hpos : 0 < (k : ℝ) := by exact_mod_cast hkpos
          have h3 : Real.log (k : ℝ) ≤ Real.log (S + 1) := Real.log_le_log hpos (by linarith)
          have h4 : Real.log (S + 1) ≤ S := by
            have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < S + 1)
            linarith
          linarith
        have hKS : ((2 * k * (∑ j : Fin (n + 1), r j) + (n + 1) * k : ℕ) : ℝ) * Real.log 2
            ≤ 3 * (k : ℝ) * S := by
          have hlog2 : Real.log 2 ≤ 1 := by
            have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
            linarith
          have hnS : ((n : ℝ) + 1) ≤ S := by
            rw [hSdef]
            have hcast1 : ((n:ℝ) + 1) = ∑ _i : Fin (n + 1), (1:ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
              push_cast
              ring
            rw [hcast1]
            exact Finset.sum_le_sum fun i _ => by exact_mod_cast hr i
          have hcast : ((2 * k * (∑ j : Fin (n + 1), r j) + (n + 1) * k : ℕ) : ℝ)
              = 2 * (k : ℝ) * S + ((n : ℝ) + 1) * (k : ℝ) := by
            rw [hSdef]; push_cast; ring
          rw [hcast]
          have hfac0 : 0 ≤ 2 * (k:ℝ) * S + ((n:ℝ)+1) * (k:ℝ) := by positivity
          have hm := mul_le_mul_of_nonneg_left hlog2 hfac0
          nlinarith [hm, hnS, hkR]
        nlinarith [hfact, hlogk, hKS, hkR]
      have hren₁ : MvPolynomial.rename (fun _ : Fin 1 => (0 : Fin (n + 1))) W₁ ≠ 0 := fun h =>
        hW₁ (MvPolynomial.rename_injective _ (fun a b _ => Subsingleton.elim a b)
          (by rw [h, map_zero]))
      have hren₂ : MvPolynomial.rename Fin.succ W₂ ≠ 0 := fun h =>
        hW₂ (MvPolynomial.rename_injective Fin.succ (Fin.succ_injective n)
          (by rw [h, map_zero]))
      have hW₂deg : ∀ t ∈ W₂.support, ∀ i : Fin n, t i ≤ k * r (Fin.succ i) := by
        intro t ht i
        have h1 : MvPolynomial.degreeOf (Fin.succ i) V ≤ k * r (Fin.succ i) := by
          rw [hVdef, hAdef]
          exact degreeOf_det_pderivIterDiv_le P r hdeg μ (Fin.succ i)
        have h3 : MvPolynomial.degreeOf (Fin.succ i) V =
            MvPolynomial.degreeOf (Fin.succ i)
              (MvPolynomial.rename (fun _ : Fin 1 => (0 : Fin (n + 1))) W₁) +
            MvPolynomial.degreeOf (Fin.succ i) (MvPolynomial.rename Fin.succ W₂) := by
          rw [hVeq]
          exact MvPolynomial.degreeOf_mul_eq hren₁ hren₂
        have h4 : MvPolynomial.degreeOf (Fin.succ i)
            (MvPolynomial.rename (fun _ : Fin 1 => (0 : Fin (n + 1))) W₁) = 0 :=
          degreeOf_rename_eq_zero_of_notMem_range _ (by
            rintro ⟨a, ha⟩
            fin_cases a
            exact Fin.succ_ne_zero i ha.symm) W₁
        have h5 : MvPolynomial.degreeOf (Fin.succ i) (MvPolynomial.rename Fin.succ W₂) =
            MvPolynomial.degreeOf i W₂ :=
          MvPolynomial.degreeOf_rename_of_injective (Fin.succ_injective n) i
        rw [h3, h4, zero_add, h5] at h1
        exact MvPolynomial.degreeOf_le_iff.mp h1 t ht
      have hVind : index β r (Bm.det) =
          index (β ∘ Fin.succ) (r ∘ Fin.succ) (W₂.map (Int.castRingHom ℚ)) +
          index (β ∘ (fun _ : Fin 1 => (0 : Fin (n + 1))))
            (r ∘ (fun _ : Fin 1 => (0 : Fin (n + 1)))) (W₁.map (Int.castRingHom ℚ)) := by
        rw [index_wronskian_det_split β r Pq φ ψ μ hdec hdetφ hdetψ']
        congr 1
        · rw [← hU₂def, hU₂eq,
            index_C_mul (β ∘ Fin.succ) (r ∘ Fin.succ) c⁻¹ (inv_ne_zero hc)
              (W₂.map (Int.castRingHom ℚ)) hW₂qne]
        · rw [← hU₁def, ← index_C_mul (β ∘ (fun _ : Fin 1 => (0 : Fin (n + 1))))
              (r ∘ (fun _ : Fin 1 => (0 : Fin (n + 1)))) c₀ hc₀ne U₁ hU₁ne, hU₁eq,
            index_C_mul (β ∘ (fun _ : Fin 1 => (0 : Fin (n + 1))))
              (r ∘ (fun _ : Fin 1 => (0 : Fin (n + 1)))) c hc
              (W₁.map (Int.castRingHom ℚ)) hW₁qne]
      have hBwt : ∀ i : Fin k, Commons.Algebra.MvPolynomial.indexWt r ((μ i).mapDomain Fin.succ)
          ≤ η ^ (2 ^ n) := by
        intro i
        have hr1pos : (0:ℝ) < (r 1 : ℝ) := by
          have := hr 1; exact_mod_cast (show 0 < r 1 by omega)
        have hle1 : ∀ t : Fin n, (r 1 : ℝ) ≤ (r (Fin.succ t) : ℝ) := by
          intro t
          have h1le : (1 : Fin (n + 1)) ≤ Fin.succ t := by
            rw [Fin.le_iff_val_le_val]
            exact le_trans (Nat.mod_le _ _) (Nat.le_add_left 1 (t : ℕ))
          have h := hratio 1 (Fin.succ t) h1le
          have h3 : η ^ (2 ^ n * (((Fin.succ t : Fin (n + 1)) : ℕ) -
              ((1 : Fin (n + 1)) : ℕ))) ≤ 1 :=
            pow_le_one₀ (le_of_lt hη0) (le_trans hη (by norm_num))
          have h4 : (0:ℝ) < (r (Fin.succ t) : ℝ) :=
            Nat.cast_pos.mpr (by have := hr (Fin.succ t); omega)
          have h5 : η ^ (2 ^ n * (((Fin.succ t : Fin (n + 1)) : ℕ) -
              ((1 : Fin (n + 1)) : ℕ))) * (r (Fin.succ t) : ℝ) ≤ (r (Fin.succ t) : ℝ) :=
            mul_le_of_le_one_left (le_of_lt h4) h3
          linarith [h, h5]
        have hsum : Commons.Algebra.MvPolynomial.indexWt r ((μ i).mapDomain Fin.succ) =
            ∑ t : Fin n, ((μ i) t : ℝ) / (r (Fin.succ t) : ℝ) := by
          rw [Commons.Algebra.MvPolynomial.indexWt, Fin.sum_univ_succ]
          have h0 : ((μ i).mapDomain Fin.succ (0 : Fin (n + 1)) : ℝ) = 0 := by
            rw [Finsupp.mapDomain_of_notMem_range _ 0 (by
              rintro ⟨a, ha⟩; exact Fin.succ_ne_zero a ha)]
            simp
          rw [h0, zero_div, zero_add]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finsupp.mapDomain_apply (Fin.succ_injective n)]
        have hnum : (∑ t : Fin n, ((μ i) t : ℝ)) ≤ (r 0 : ℝ) := by
          have h1 : ((((μ i).sum (fun _ m => m) : ℕ)) : ℝ) ≤ (i : ℝ) := Nat.cast_le.mpr (hμ i)
          have h2 : (∑ t : Fin n, ((μ i) t : ℝ)) = ((((μ i).sum (fun _ m => m) : ℕ)) : ℝ) := by
            rw [Finsupp.sum, Nat.cast_sum]
            exact (Finset.sum_subset (Finset.subset_univ _) fun t _ ht => by
              rw [Finsupp.notMem_support_iff.mp ht, Nat.cast_zero]).symm
          have h3 : (i : ℝ) ≤ (k : ℝ) - 1 := by
            have hik : (i : ℕ) ≤ k - 1 := by omega
            rw [← Nat.cast_one, ← Nat.cast_sub hkpos]
            exact_mod_cast hik
          have h4 : (k : ℝ) - 1 ≤ (r 0 : ℝ) := by
            have hk1 : k - 1 ≤ r 0 := by omega
            rw [← Nat.cast_one, ← Nat.cast_sub hkpos]
            exact_mod_cast hk1
          rw [h2]; linarith
        rw [hsum]
        have h2 : (∑ t : Fin n, ((μ i) t : ℝ) / (r (Fin.succ t) : ℝ)) ≤
            (∑ t : Fin n, ((μ i) t : ℝ)) / (r 1 : ℝ) := by
          rw [Finset.sum_div]
          exact Finset.sum_le_sum fun t _ =>
            div_le_div_of_nonneg_left (by positivity) hr1pos (hle1 t)
        have h3 : (∑ t : Fin n, ((μ i) t : ℝ)) / (r 1 : ℝ) ≤ (r 0 : ℝ) / (r 1 : ℝ) :=
          div_le_div_of_nonneg_right hnum (le_of_lt hr1pos)
        have h4 : (r 0 : ℝ) / (r 1 : ℝ) ≤ η ^ (2 ^ n) := by
          have h := hratio 0 1 (by simp)
          have hgap : ((1 : Fin (n + 1)) : ℕ) - ((0 : Fin (n + 1)) : ℕ) = 1 := by
            have h1' : ((1 : Fin (n + 1)) : ℕ) = 1 := by
              show 1 % (n + 1) = 1
              exact Nat.mod_eq_of_lt (by omega)
            have h0' : ((0 : Fin (n + 1)) : ℕ) = 0 := rfl
            omega
          rw [hgap] at h
          rw [mul_one] at h
          rw [div_le_iff₀ (by positivity : (0:ℝ) < (r 1 : ℝ))]
          linarith [h]
        linarith [h2, h3, h4]
      have hηpow0 : 0 ≤ η ^ (2 ^ n) := pow_nonneg (le_of_lt hη0) _
      have hIm : index β r Pq ≤ ((n : ℝ) + 1) := by
        have h := index_le_sum_degree_div β r Pq
        have hdegPq : ∀ i : Fin (n + 1), MvPolynomial.degreeOf i Pq ≤ r i := by
          intro i
          rw [MvPolynomial.degreeOf_le_iff]
          intro m hm
          rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map] at hm
          exact hdeg m (MvPolynomial.mem_support_iff.mpr fun h0 => hm (by rw [h0, map_zero])) i
        refine h.trans ?_
        calc (∑ i : Fin (n + 1), (MvPolynomial.degreeOf i Pq : ℝ) / (r i : ℝ))
            ≤ ∑ _i : Fin (n + 1), (1:ℝ) := Finset.sum_le_sum fun i _ => by
              rw [div_le_one (Nat.cast_pos.mpr (by have := hr i; omega))]
              exact Nat.cast_le.mpr (hdegPq i)
          _ = ((n : ℝ) + 1) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
              push_cast; ring
      have hge := index_wronskian_det_ge β r Pq μ (η ^ (2 ^ n)) hBwt hηpow0 hBdet
        (hr 0) (by exact_mod_cast hk_le) (by omega : 2 ≤ n + 1) hIm
      have ih' : ∀ (Q : MvPolynomial (Fin n) ℤ), Q ≠ 0 →
          ∀ (r' : Fin n → ℕ), (∀ i, 1 ≤ r' i) → (∀ t ∈ Q.support, ∀ i, t i ≤ r' i) →
          ∀ (β' : Fin n → ℚ) (η' : ℝ), 0 < η' → η' ≤ 1 / 2 →
          (∀ i j : Fin n, i ≤ j →
            (r' i : ℝ) ≤ η' ^ (2 ^ (n - 1) * ((j : ℕ) - (i : ℕ))) * (r' j : ℝ)) →
          η' ^ (2 ^ (n - 1)) * (⨅ i : Fin n, (r' i : ℝ) * Height.logHeight₁ (β' i)) ≥
            hZ Q + 100 * ((n : ℕ) : ℝ) * (∑ i : Fin n, (r' i : ℝ)) →
          index β' r' (Q.map (Int.castRingHom ℚ)) ≤ 4 * ((n : ℕ) : ℝ) * η' := by
        have h := ih (n - 1) (by omega)
        rw [Nat.sub_add_cancel hn1] at h
        exact h
      have hratio2 : ∀ i j : Fin n, i ≤ j →
          (((k * r (Fin.succ i) : ℕ)) : ℝ) ≤
            (η ^ 2) ^ (2 ^ (n - 1) * ((j : ℕ) - (i : ℕ))) *
              (((k * r (Fin.succ j) : ℕ)) : ℝ) := by
        intro i j hij
        have h := hratio (Fin.succ i) (Fin.succ j) (by
          rw [Fin.le_iff_val_le_val] at hij ⊢; simp [hij])
        have h2 : ((Fin.succ j : Fin (n + 1)) : ℕ) - ((Fin.succ i : Fin (n + 1)) : ℕ) =
            (j : ℕ) - (i : ℕ) := by simp
        rw [h2] at h
        have h4 : (η ^ 2) ^ (2 ^ (n - 1) * ((j : ℕ) - (i : ℕ))) =
            η ^ (2 ^ n * ((j : ℕ) - (i : ℕ))) := by
          rw [← pow_mul]
          congr 1
          have hp : (2:ℕ) ^ n = 2 ^ (n - 1) * 2 := by
            conv_lhs => rw [← Nat.sub_add_cancel hn1]
            rw [pow_succ]
          rw [hp]; ring
        rw [h4]
        have hm := mul_le_mul_of_nonneg_right h (by positivity : (0:ℝ) ≤ (k:ℝ))
        push_cast
        linarith [hm]
      have hsum_succ : (∑ i : Fin n, (r (Fin.succ i) : ℝ)) = S - (r 0 : ℝ) := by
        rw [hSdef, Fin.sum_univ_succ]
        ring
      have hpow : (η ^ 2) ^ (2 ^ (n - 1)) = η ^ (2 ^ n) := by
        rw [← pow_mul]
        congr 1
        have hp : (2:ℕ) ^ n = 2 ^ (n - 1) * 2 := by
          conv_lhs => rw [← Nat.sub_add_cancel hn1]
          rw [pow_succ]
        rw [hp]; ring
      have hpow1 : η ^ (2 ^ n) ≤ 1 := pow_le_one₀ (le_of_lt hη0) (le_trans hη (by norm_num))
      have hcond2 : (η ^ 2) ^ (2 ^ (n - 1)) *
            (⨅ i : Fin n, (((k * r (Fin.succ i) : ℕ)) : ℝ) * Height.logHeight₁ (β (Fin.succ i))) ≥
          hZ W₂ + 100 * ((n : ℕ) : ℝ) * (∑ i : Fin n, (((k * r (Fin.succ i) : ℕ)) : ℝ)) := by
        rw [hpow]
        have hinf : η ^ (2 ^ n) * (⨅ i : Fin n,
              (((k * r (Fin.succ i) : ℕ)) : ℝ) * Height.logHeight₁ (β (Fin.succ i)))
            ≥ (k : ℝ) * (hZ P + 100 * ((n + 1 : ℕ) : ℝ) * S) := by
          have hηpos : 0 < η ^ (2 ^ n) := pow_pos hη0 _
          have hkey : ((k : ℝ) * (hZ P + 100 * ((n + 1 : ℕ) : ℝ) * S)) / η ^ (2 ^ n) ≤
              ⨅ i : Fin n, (((k * r (Fin.succ i) : ℕ)) : ℝ) * Height.logHeight₁ (β (Fin.succ i)) := by
            haveI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
            refine le_ciInf fun i => ?_
            rw [div_le_iff₀ hηpos]
            rw [hSdef] at hcond
            have hle := iInf_le_fin (fun j : Fin (n + 1) => (r j : ℝ) * Height.logHeight₁ (β j))
              (Fin.succ i)
            have h1 : η ^ (2 ^ n) * ((r (Fin.succ i) : ℝ) * Height.logHeight₁ (β (Fin.succ i))) ≥
                hZ P + 100 * ((n + 1 : ℕ) : ℝ) * S := by
              have h := mul_le_mul_of_nonneg_left hle (le_of_lt hηpos)
              linarith [hcond, h]
            have h2 : (k : ℝ) * (hZ P + 100 * ((n + 1 : ℕ) : ℝ) * S) ≤
                ((((k * r (Fin.succ i) : ℕ)) : ℝ) * Height.logHeight₁ (β (Fin.succ i))) *
                  η ^ (2 ^ n) := by
              have h2' := mul_le_mul_of_nonneg_left h1 (le_of_lt hkR)
              calc (k : ℝ) * (hZ P + 100 * ((n + 1 : ℕ) : ℝ) * S)
                  ≤ (k : ℝ) * (η ^ (2 ^ n) *
                      ((r (Fin.succ i) : ℝ) * Height.logHeight₁ (β (Fin.succ i)))) := h2'
                _ = ((((k * r (Fin.succ i) : ℕ)) : ℝ) * Height.logHeight₁ (β (Fin.succ i))) *
                      η ^ (2 ^ n) := by push_cast; ring
            exact h2
          have hfin := mul_le_mul_of_nonneg_left hkey (le_of_lt hηpos)
          have hsimp : η ^ (2 ^ n) *
              (((k : ℝ) * (hZ P + 100 * ((n + 1 : ℕ) : ℝ) * S)) / η ^ (2 ^ n)) =
              (k : ℝ) * (hZ P + 100 * ((n + 1 : ℕ) : ℝ) * S) := by
            field_simp
          rw [hsimp] at hfin
          exact hfin
        have hbound : hZ W₂ ≤ (k : ℝ) * hZ P + 100 * (k : ℝ) * S := by
          linarith [hW₂le, hZV, hloss]
        have hsumk : (∑ i : Fin n, (((k * r (Fin.succ i) : ℕ)) : ℝ)) =
            (k : ℝ) * (S - (r 0 : ℝ)) := by
          have h1 : (∑ i : Fin n, (((k * r (Fin.succ i) : ℕ)) : ℝ)) =
              (k : ℝ) * (∑ i : Fin n, (r (Fin.succ i) : ℝ)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            push_cast; ring
          rw [h1, hsum_succ]
        have hn0R : (0:ℝ) ≤ (n:ℝ) := by positivity
        have hbound2 : hZ W₂ + 100 * ((n : ℕ) : ℝ) *
            (∑ i : Fin n, (((k * r (Fin.succ i) : ℕ)) : ℝ)) ≤
            (k : ℝ) * (hZ P + 100 * ((n + 1 : ℕ) : ℝ) * S) := by
          rw [hsumk]
          have hstep : 100 * (k:ℝ) * S + 100 * (n:ℝ) * ((k:ℝ) * (S - (r 0 : ℝ))) ≤
              100 * (k:ℝ) * ((n:ℝ) + 1) * S := by
            have hkey : (S - (r 0 : ℝ)) ≤ S := by linarith [hr0S]
            have h1 : (n:ℝ) * (S - (r 0 : ℝ)) ≤ (n:ℝ) * S := mul_le_mul_of_nonneg_left hkey hn0R
            nlinarith [h1, hkR, hn0R]
          push_cast
          linarith [hbound, hstep]
        linarith [hinf, hbound2]
      have hrn : ∀ i : Fin n, 1 ≤ k * r (Fin.succ i) := by
        intro i
        exact Nat.mul_pos hkpos (by have := hr (Fin.succ i); omega)
      have hη2pos : 0 < η ^ 2 := by positivity
      have hη2half : η ^ 2 ≤ 1 / 2 := by nlinarith [hη0, hη]
      have hIH := ih' W₂ hW₂ (fun i => k * r (Fin.succ i)) hrn hW₂deg
        (fun i => β (Fin.succ i)) (η ^ 2) hη2pos hη2half hratio2 hcond2
      have hrn0 : 1 ≤ k * r 0 := Nat.mul_pos hkpos (by have := hr 0; omega)
      have hcond1 : η ^ (2 ^ n) * ((((k * r 0 : ℕ)) : ℝ) * Height.logHeight₁ (β 0)) ≥
          hZ W₁ + 100 * (((k * r 0 : ℕ)) : ℝ) := by
        rw [hSdef] at hcond
        have hle := iInf_le_fin (fun j : Fin (n + 1) => (r j : ℝ) * Height.logHeight₁ (β j)) 0
        have h1 : η ^ (2 ^ n) * ((r 0 : ℝ) * Height.logHeight₁ (β 0)) ≥
            hZ P + 100 * ((n + 1 : ℕ) : ℝ) * S := by
          have h := mul_le_mul_of_nonneg_left hle hηpow0
          linarith [hcond, h]
        have h2 : (k : ℝ) * (hZ P + 100 * ((n + 1 : ℕ) : ℝ) * S) ≤
            η ^ (2 ^ n) * ((((k * r 0 : ℕ)) : ℝ) * Height.logHeight₁ (β 0)) := by
          have h2' := mul_le_mul_of_nonneg_left h1 (le_of_lt hkR)
          have h4 : ((((k * r 0 : ℕ)) : ℝ) * Height.logHeight₁ (β 0)) =
              (k : ℝ) * ((r 0 : ℝ) * Height.logHeight₁ (β 0)) := by push_cast; ring
          rw [h4]
          calc (k : ℝ) * (hZ P + 100 * ((n + 1 : ℕ) : ℝ) * S)
              ≤ (k : ℝ) * (η ^ (2 ^ n) * ((r 0 : ℝ) * Height.logHeight₁ (β 0))) := h2'
            _ = η ^ (2 ^ n) * ((k : ℝ) * ((r 0 : ℝ) * Height.logHeight₁ (β 0))) := by ring
        have hbound : hZ W₁ ≤ (k : ℝ) * hZ P + 100 * (k : ℝ) * S := by
          linarith [hW₁le, hZV, hloss]
        have hr0nS : (r 0 : ℝ) ≤ (n : ℝ) * S := by
          have hn1R : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hnpos
          nlinarith [hr0S, hn1R, hS1]
        have hstep : 100 * (k:ℝ) * S + 100 * (k:ℝ) * (r 0 : ℝ) ≤
            100 * (k:ℝ) * ((n:ℝ) + 1) * S := by nlinarith [hr0nS, hkR, hS1]
        push_cast at h2 ⊢
        linarith [h2, hbound, hstep]
      have hbase := index_fin_one_le hW₁ (fun _ : Fin 1 => k * r 0) (by simpa using hrn0)
        (fun _ => β 0) (η ^ (2 ^ n)) (by positivity) hcond1
      have hup₂ : index (β ∘ Fin.succ) (r ∘ Fin.succ) (W₂.map (Int.castRingHom ℚ)) ≤
          (k : ℝ) * (4 * (n : ℝ) * η ^ 2) := by
        rw [index_eq_mul_index_nsmul k hkpos]
        exact mul_le_mul_of_nonneg_left hIH (by positivity)
      have hup₁ : index (β ∘ (fun _ : Fin 1 => (0 : Fin (n + 1))))
          (r ∘ (fun _ : Fin 1 => (0 : Fin (n + 1)))) (W₁.map (Int.castRingHom ℚ)) ≤
          (k : ℝ) * (4 * η ^ (2 ^ n)) := by
        rw [index_eq_mul_index_nsmul k hkpos]
        exact mul_le_mul_of_nonneg_left hbase (by positivity)
      have hηsq : η ^ (2 ^ n) ≤ η ^ 2 := by
        refine pow_le_pow_of_le_one (le_of_lt hη0) (le_trans hη (by norm_num)) ?_
        calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
      have hmain : (index β r Pq) ^ 2 / (2 * ((n : ℝ) + 1)) ≤ 4 * (n:ℝ) * η^2 + 5 * η ^ (2 ^ n) := by
        have h1 : (k:ℝ) * (index β r Pq) ^ 2 / (2 * ((n : ℝ) + 1)) - (k:ℝ) * η ^ (2 ^ n) ≤
            (k:ℝ) * (4 * (n:ℝ) * η^2) + (k:ℝ) * (4 * η ^ (2 ^ n)) := by
          calc (k:ℝ) * (index β r Pq) ^ 2 / (2 * ((n : ℝ) + 1)) - (k:ℝ) * η ^ (2 ^ n)
              ≤ index β r (Bm.det) := hge
            _ = index (β ∘ Fin.succ) (r ∘ Fin.succ) (W₂.map (Int.castRingHom ℚ)) +
                index (β ∘ (fun _ : Fin 1 => (0 : Fin (n + 1))))
                  (r ∘ (fun _ : Fin 1 => (0 : Fin (n + 1)))) (W₁.map (Int.castRingHom ℚ)) := hVind
            _ ≤ (k:ℝ) * (4 * (n:ℝ) * η^2) + (k:ℝ) * (4 * η ^ (2 ^ n)) := add_le_add hup₂ hup₁
        have h2 : (k:ℝ) * ((index β r Pq) ^ 2 / (2 * ((n : ℝ) + 1))) ≤
            (k:ℝ) * (4 * (n:ℝ) * η^2 + 5 * η ^ (2 ^ n)) := by
          have h3 : (k:ℝ) * ((index β r Pq) ^ 2 / (2 * ((n : ℝ) + 1))) =
              (k:ℝ) * (index β r Pq) ^ 2 / (2 * ((n : ℝ) + 1)) := by ring
          rw [h3]
          linarith [h1]
        exact le_of_mul_le_mul_left h2 hkR
      have hfin : (index β r Pq) ^ 2 ≤ (4 * ((n : ℝ) + 1) * η) ^ 2 := by
        have h4 := (div_le_iff₀ (by positivity : (0:ℝ) < 2 * ((n:ℝ)+1))).mp hmain
        have h5 : (index β r Pq) ^ 2 ≤ 2 * ((n:ℝ) + 1) * (4 * (n:ℝ) + 5) * η^2 := by
          nlinarith [h4, hηsq, hη0]
        have h6 : 2 * ((n:ℝ) + 1) * (4 * (n:ℝ) + 5) ≤ 16 * ((n:ℝ) + 1) ^ 2 := by
          have hn0R : (0:ℝ) ≤ (n:ℝ) := by positivity
          nlinarith
        nlinarith [h5, h6, hη0]
      have hind0 : 0 ≤ index β r Pq := index_nonneg β r Pq
      have hpos4 : (0:ℝ) ≤ 4 * ((n:ℝ) + 1) * η := by positivity
      have hfin2 : index β r Pq ≤ 4 * ((n : ℝ) + 1) * η := by
        have habs : |index β r Pq| ≤ |4 * ((n:ℝ) + 1) * η| := sq_le_sq.mp hfin
        rw [abs_of_nonneg hind0, abs_of_nonneg hpos4] at habs
        exact habs
      simpa [hPqdef] using hfin2

/-- **The multivariate Roth lemma.**  For `P ∈ ℤ[x_0,…,x_{m-1}]` with `deg_{x_i} P ≤ r_i ≥ 1`,
a point `β`, and `0 < η ≤ 1/2` with rapidly growing weights
(`r_i ≤ η^{2^{m-1}(j-i)} r_j` for `i ≤ j`) and

`η^{2^{m-1}} · ⨅_i (r_i · h(β_i)) ≥ h(P) + 100 m (∑_i r_i)`,

the index of `P` at `β` with respect to the weights `r` is at most `4 m η`. -/
theorem roth_lemma {m : ℕ} [NeZero m] (P : MvPolynomial (Fin m) ℤ) (hP : P ≠ 0)
    (r : Fin m → ℕ) (hr : ∀ i, 1 ≤ r i) (hdeg : ∀ t ∈ P.support, ∀ i, t i ≤ r i)
    (β : Fin m → ℚ) (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (hratio : ∀ i j : Fin m, i ≤ j →
      (r i : ℝ) ≤ η ^ (2 ^ (m - 1) * ((j : ℕ) - (i : ℕ))) * (r j : ℝ))
    (hcond : η ^ (2 ^ (m - 1)) * (⨅ i : Fin m, (r i : ℝ) * Height.logHeight₁ (β i)) ≥
      hZ P + 100 * (m : ℝ) * (∑ i : Fin m, (r i : ℝ))) :
    index β r (P.map (Int.castRingHom ℚ)) ≤ 4 * (m : ℝ) * η := by
  have hm : 1 ≤ m := NeZero.one_le
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  set e : Fin m ≃ Fin (m - 1 + 1) := (finCongr hm').symm with hedef
  set P' : MvPolynomial (Fin (m - 1 + 1)) ℤ := MvPolynomial.rename e P with hP'def
  set r' : Fin (m - 1 + 1) → ℕ := fun i => r (e.symm i) with hr'def
  set β' : Fin (m - 1 + 1) → ℚ := fun i => β (e.symm i) with hβ'def
  have hecoe : ∀ i : Fin (m - 1 + 1), ((e.symm i : Fin m) : ℕ) = (i : ℕ) := by
    intro i
    rw [hedef, Equiv.symm_symm]
    exact finCongr_apply_coe hm' i
  have hesum : ∀ x : Fin m, e.symm (e x) = x := fun x => Equiv.symm_apply_apply e x
  have hP' : P' ≠ 0 := by
    rw [hP'def]
    intro h
    exact hP (MvPolynomial.rename_injective e e.injective (h.trans (map_zero _).symm))
  have hr' : ∀ i, 1 ≤ r' i := fun i => hr _
  have hdeg' : ∀ t ∈ P'.support, ∀ i, t i ≤ r' i := by
    intro t ht i
    have h1 : MvPolynomial.degreeOf i P' ≤ r' i := by
      have h2 : MvPolynomial.degreeOf (e (e.symm i)) (MvPolynomial.rename e P) =
          MvPolynomial.degreeOf (e.symm i) P :=
        MvPolynomial.degreeOf_rename_of_injective (p := P) e.injective (e.symm i)
      rw [Equiv.apply_symm_apply] at h2
      rw [hP'def, hr'def, h2]
      exact MvPolynomial.degreeOf_le_iff.mpr (fun m hm => hdeg m hm (e.symm i))
    exact MvPolynomial.degreeOf_le_iff.mp h1 t ht
  have hratio' : ∀ i j : Fin (m - 1 + 1), i ≤ j →
      (r' i : ℝ) ≤ η ^ (2 ^ (m - 1) * ((j : ℕ) - (i : ℕ))) * (r' j : ℝ) := by
    intro i j hij
    have hij' : e.symm i ≤ e.symm j := by
      rw [Fin.le_iff_val_le_val, hecoe i, hecoe j]
      rwa [Fin.le_iff_val_le_val] at hij
    have h := hratio (e.symm i) (e.symm j) hij'
    rw [hecoe i, hecoe j] at h
    simpa [hr'def] using h
  have hZP' : hZ P' = hZ P := by
    rw [hZ_eq, hZ_eq, hP'def, MvPolynomial.map_rename]
    exact Commons.NumberTheory.Height.MvPolynomial.logHeight_gP_rename e
      (P.map (Int.castRingHom ℚ))
  have hcond' : η ^ (2 ^ (m - 1)) *
        (⨅ i : Fin (m - 1 + 1), (r' i : ℝ) * Height.logHeight₁ (β' i)) ≥
      hZ P' + 100 * (((m - 1 + 1 : ℕ)) : ℝ) * (∑ i : Fin (m - 1 + 1), (r' i : ℝ)) := by
    have hinf : (⨅ i : Fin (m - 1 + 1), (r' i : ℝ) * Height.logHeight₁ (β' i)) =
        (⨅ i : Fin m, (r i : ℝ) * Height.logHeight₁ (β i)) := by
      rw [← Equiv.iInf_comp (g := fun i : Fin (m - 1 + 1) =>
        (r' i : ℝ) * Height.logHeight₁ (β' i)) e]
      refine iInf_congr fun x => ?_
      simp only [hr'def, hβ'def, hesum x]
    have hsum : (∑ i : Fin (m - 1 + 1), (r' i : ℝ)) = (∑ i : Fin m, (r i : ℝ)) := by
      rw [← Equiv.sum_comp e (fun i : Fin (m - 1 + 1) => (r' i : ℝ))]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hr'def]
      exact congrArg (fun y => (r y : ℝ)) (hesum x)
    rw [hinf, hsum, hZP', hm']
    exact hcond
  have hmain := roth_lemma_aux (m - 1) P' hP' r' hr' hdeg' β' η hη0 hη hratio' hcond'
  have h1 : index β' r' (P'.map (Int.castRingHom ℚ)) = index β r (P.map (Int.castRingHom ℚ)) := by
    have hmap : P'.map (Int.castRingHom ℚ) =
        MvPolynomial.rename (e : Fin m → Fin (m - 1 + 1)) (P.map (Int.castRingHom ℚ)) := by
      rw [hP'def, MvPolynomial.map_rename]
    rw [hmap, index_rename (e : Fin m → Fin (m - 1 + 1)) e.injective β' r']
    refine congrArg₂ (fun (f : Fin m → ℚ) (g : Fin m → ℕ) =>
      index f g (P.map (Int.castRingHom ℚ))) ?_ ?_
    · ext x
      exact congrArg β (Equiv.symm_apply_apply e x)
    · ext x
      exact congrArg r (Equiv.symm_apply_apply e x)
  rw [← h1]
  have h4 : (4:ℝ) * (((m - 1 + 1 : ℕ)) : ℝ) * η = 4 * (m : ℝ) * η := by rw [hm']
  linarith [hmain, h4]

end Submission.Subspace
