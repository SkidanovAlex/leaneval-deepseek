import Mathlib
import Submission.Work.BW.ACBase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

namespace Work.BW

/-! ### Helper lemmas for the degree bounds of the §13 auxiliary polynomial `Qpoly`.

`Qpoly` is a finite sum of terms of the shape

`C c * (aeval (X₀ + C a) q) * ∏ j, X_{j+1} ^ k_j`

where `q = hasseDeriv t₀ (Δ(·;h) ^ (λ₋₁+1))`.  The two lemmas below bound the `Y₀`-degree
of `aeval (X₀ + C a) q` by `q.natDegree` (using the fact that `Y₀ + a` has degree `1` in
`Y₀`) and its degree in every `Y_{j+1}` by `0` (since `Y₀ + a` does not involve `Y_{j+1}`). -/

/-- The `i`-degree of `aeval x q` is at most `q.natDegree * (degreeOf i x)`. -/
lemma aeval_degreeOf_le {σ : Type*} [DecidableEq σ] (i : σ) (x : MvPolynomial σ ℂ)
    (q : Polynomial ℚ) :
    (Polynomial.aeval x q).degreeOf i ≤ q.natDegree * x.degreeOf i := by
  rw [Polynomial.aeval_eq_sum_range]
  refine (MvPolynomial.degreeOf_sum_le i _ _).trans ?_
  rw [Finset.sup_le_iff]
  intro n hn
  rw [Finset.mem_range] at hn
  have hnle : n ≤ q.natDegree := Nat.lt_succ_iff.mp hn
  calc (q.coeff n • x ^ n).degreeOf i
      ≤ (x ^ n).degreeOf i := by
        rw [Algebra.smul_def, MvPolynomial.algebraMap_apply]
        exact MvPolynomial.degreeOf_C_mul_le _ _ _
    _ ≤ n * x.degreeOf i := MvPolynomial.degreeOf_pow_le i x n
    _ ≤ q.natDegree * x.degreeOf i := Nat.mul_le_mul_right _ hnle

/-- A finite sum of polynomials whose `i`-degree is bounded by `d` has `i`-degree `≤ d`. -/
lemma degreeOf_finset_sum_le {σ ι : Type*} [DecidableEq σ] (i : σ) (s : Finset ι)
    (f : ι → MvPolynomial σ ℂ) (d : ℕ) (h : ∀ x ∈ s, (f x).degreeOf i ≤ d) :
    (Finset.sum s f).degreeOf i ≤ d :=
  (MvPolynomial.degreeOf_sum_le i s f).trans (Finset.sup_le h)

/-- `natDegree (Δ(·;h)) ≤ h`, since `Δ(·;h) = (h!)⁻¹ ∏_{i<h} (X + C (i+1))`. -/
lemma natDegree_deltaPoly_le (h : ℕ) : (deltaPoly h).natDegree ≤ h := by
  unfold deltaPoly
  refine (Polynomial.natDegree_smul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  have : ∀ x ∈ Finset.range h, (Polynomial.X + Polynomial.C ((x:ℚ)+1)).natDegree = 1 :=
    fun x _ => Polynomial.natDegree_X_add_C _
  rw [Finset.sum_congr rfl this]
  simp

/-- `natDegree (hasseDeriv t₀ (Δ(·;h) ^ (λ₋₁+1))) ≤ h (D₀+1)` for `λ₋₁ < D₀+1`:
the Hasse derivative does not increase the degree, `Δ ^ m` has degree `≤ m h`, and
`m = λ₋₁+1 ≤ D₀+1`. -/
lemma hasseDeriv_deltaPoly_natDegree_le (h D0 : ℕ) (lm1 : Fin (D0+1)) (t0 : ℕ) :
    (Polynomial.hasseDeriv t0 (deltaPoly h ^ ((lm1 : ℕ) + 1))).natDegree ≤ h * (D0 + 1) := by
  refine (Polynomial.natDegree_hasseDeriv_le _ _).trans ?_
  refine (Nat.sub_le _ _).trans ?_
  refine (Polynomial.natDegree_pow_le).trans ?_
  refine (Nat.mul_le_mul_left _ (natDegree_deltaPoly_le h)).trans ?_
  refine (Nat.mul_le_mul_right h (Nat.succ_le_succ (Nat.lt_succ_iff.mp lm1.isLt))).trans ?_
  exact le_of_eq (Nat.mul_comm _ _)

/-- The `Y₀`-degree of a single summand of `Qpoly` is `≤ h (D₀+1)`. -/
lemma Qpoly_summand_degreeOf_zero {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ)
    (b : Fin n → ℤ) (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n)
    (α' : Fin r → K) (h D0 : ℕ) (Dj : Fin r → ℕ) (p : AuxIdx r h D0 Dj → K)
    (t0 : ℕ) (t : Fin (r - 1) → ℕ) (lm : AuxIdx r h D0 Dj) :
    (MvPolynomial.C (φ (p lm) *
        (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)) * (ulcm h : ℂ) ^ t0)
      * Polynomial.aeval (MvPolynomial.X (0 : Fin (r+1)) + MvPolynomial.C ((lm.1 : ℕ) : ℂ))
          (Polynomial.hasseDeriv t0 (deltaPoly h ^ ((lm.2.1 : ℕ) + 1)))
      * ∏ j : Fin r, MvPolynomial.X j.succ ^ ((lm.2.2 j : ℕ))).degreeOf (0 : Fin (r+1))
      ≤ h * (D0 + 1) := by
  set c : ℂ := φ (p lm) *
    (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)) * (ulcm h : ℂ) ^ t0 with hc
  set A : MvPolynomial (Fin (r+1)) ℂ :=
    Polynomial.aeval (MvPolynomial.X (0 : Fin (r+1)) + MvPolynomial.C ((lm.1 : ℕ) : ℂ))
      (Polynomial.hasseDeriv t0 (deltaPoly h ^ ((lm.2.1 : ℕ) + 1))) with hA
  set B : MvPolynomial (Fin (r+1)) ℂ := ∏ j : Fin r, MvPolynomial.X j.succ ^ ((lm.2.2 j : ℕ))
    with hB
  have hx0 : (MvPolynomial.X (0 : Fin (r+1)) +
      MvPolynomial.C ((lm.1 : ℕ) : ℂ)).degreeOf (0:Fin (r+1)) ≤ 1 := by
    refine (MvPolynomial.degreeOf_add_le (0 : Fin (r+1)) (MvPolynomial.X (0 : Fin (r+1)))
      (MvPolynomial.C ((lm.1 : ℕ) : ℂ))).trans ?_
    rw [MvPolynomial.degreeOf_X_self, MvPolynomial.degreeOf_C]
    simp
  have hA0 : A.degreeOf 0 ≤ h * (D0 + 1) := by
    rw [hA]
    refine (aeval_degreeOf_le 0 _ _).trans ?_
    refine (Nat.mul_le_mul_left _ hx0).trans ?_
    rw [mul_one]
    exact hasseDeriv_deltaPoly_natDegree_le h D0 lm.2.1 t0
  have hB0 : B.degreeOf 0 ≤ 0 := by
    rw [hB]
    have h := MvPolynomial.degreeOf_prod_le (0 : Fin (r+1)) (Finset.univ : Finset (Fin r))
        (fun b : Fin r => (MvPolynomial.X b.succ ^ ((lm.2.2 b : ℕ)) : MvPolynomial (Fin (r+1)) ℂ))
    rw [Finset.sum_eq_zero
      (fun b _ => MvPolynomial.degreeOf_X_pow_of_ne _ (Fin.succ_ne_zero b).symm)] at h
    exact h
  calc (MvPolynomial.C c * A * B).degreeOf (0 : Fin (r+1))
      ≤ (MvPolynomial.C c * A).degreeOf (0 : Fin (r+1)) + B.degreeOf (0 : Fin (r+1)) :=
        MvPolynomial.degreeOf_mul_le (0 : Fin (r+1)) _ _
    _ ≤ A.degreeOf (0 : Fin (r+1)) + B.degreeOf (0 : Fin (r+1)) :=
        add_le_add (MvPolynomial.degreeOf_C_mul_le A (0 : Fin (r+1)) c) (le_refl _)
    _ ≤ A.degreeOf (0 : Fin (r+1)) + 0 := add_le_add (le_refl _) hB0
    _ ≤ h * (D0 + 1) := hA0

/-- The `Y_{j+1}`-degree of a single summand of `Qpoly` is `≤ D_j`. -/
lemma Qpoly_summand_degreeOf_succ {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ)
    (b : Fin n → ℤ) (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n)
    (α' : Fin r → K) (h D0 : ℕ) (Dj : Fin r → ℕ) (p : AuxIdx r h D0 Dj → K)
    (t0 : ℕ) (t : Fin (r - 1) → ℕ) (lm : AuxIdx r h D0 Dj) (j : Fin r) :
    (MvPolynomial.C (φ (p lm) *
        (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)) * (ulcm h : ℂ) ^ t0)
      * Polynomial.aeval (MvPolynomial.X (0 : Fin (r+1)) + MvPolynomial.C ((lm.1 : ℕ) : ℂ))
          (Polynomial.hasseDeriv t0 (deltaPoly h ^ ((lm.2.1 : ℕ) + 1)))
      * ∏ j : Fin r, MvPolynomial.X j.succ ^ ((lm.2.2 j : ℕ))).degreeOf j.succ ≤ Dj j := by
  set c : ℂ := φ (p lm) *
    (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)) * (ulcm h : ℂ) ^ t0 with hc
  set A : MvPolynomial (Fin (r+1)) ℂ :=
    Polynomial.aeval (MvPolynomial.X (0 : Fin (r+1)) + MvPolynomial.C ((lm.1 : ℕ) : ℂ))
      (Polynomial.hasseDeriv t0 (deltaPoly h ^ ((lm.2.1 : ℕ) + 1))) with hA
  set B : MvPolynomial (Fin (r+1)) ℂ := ∏ j : Fin r, MvPolynomial.X j.succ ^ ((lm.2.2 j : ℕ))
    with hB
  have hxj : (MvPolynomial.X (0 : Fin (r+1)) +
      MvPolynomial.C ((lm.1 : ℕ) : ℂ)).degreeOf j.succ = 0 := by
    apply le_antisymm
    · refine (MvPolynomial.degreeOf_add_le j.succ (MvPolynomial.X (0 : Fin (r+1)))
        (MvPolynomial.C ((lm.1 : ℕ) : ℂ))).trans ?_
      rw [MvPolynomial.degreeOf_X_of_ne (Fin.succ_ne_zero j), MvPolynomial.degreeOf_C]
      simp
    · exact Nat.zero_le _
  have hAj : A.degreeOf j.succ ≤ 0 := by
    rw [hA]
    refine (aeval_degreeOf_le j.succ _ _).trans ?_
    rw [hxj, Nat.mul_zero]
  have hBj : B.degreeOf j.succ ≤ Dj j := by
    rw [hB]
    have hsum : (∑ b ∈ (Finset.univ : Finset (Fin r)),
        (MvPolynomial.X b.succ ^ ((lm.2.2 b : ℕ)) : MvPolynomial (Fin (r+1)) ℂ).degreeOf
          j.succ) = (lm.2.2 j : ℕ) := by
      refine (Finset.sum_eq_single j ?_ ?_).trans ?_
      · intro b _ hb
        exact MvPolynomial.degreeOf_X_pow_of_ne _ (fun hh => hb (Fin.succ_inj.mp hh).symm)
      · intro hj; exact absurd (Finset.mem_univ j) hj
      · exact MvPolynomial.degreeOf_X_self_pow _ _
    have h := MvPolynomial.degreeOf_prod_le j.succ (Finset.univ : Finset (Fin r))
        (fun b : Fin r => (MvPolynomial.X b.succ ^ ((lm.2.2 b : ℕ)) : MvPolynomial (Fin (r+1)) ℂ))
    rw [hsum] at h
    exact h.trans (Nat.lt_succ_iff.mp (lm.2.2 j).isLt)
  calc (MvPolynomial.C c * A * B).degreeOf j.succ
      ≤ (MvPolynomial.C c * A).degreeOf j.succ + B.degreeOf j.succ :=
        MvPolynomial.degreeOf_mul_le j.succ _ _
    _ ≤ A.degreeOf j.succ + B.degreeOf j.succ :=
        add_le_add (MvPolynomial.degreeOf_C_mul_le A j.succ c) (le_refl _)
    _ ≤ 0 + Dj j := add_le_add hAj hBj
    _ ≤ Dj j := le_of_eq (zero_add _)

/-- BW §13: the auxiliary polynomial `Qpoly` (defined in `Submission.Work.BW.analytic_core`,
with `Qval = eval (ptS (lamP …) s) (Qpoly …)`) has `Y₀`-degree `≤ h(D₀+1)` and, for every
`j : Fin r`, `Y_{j+1}`-degree `≤ D_j` — the degree bounds required by BW §13. -/
theorem Qpoly_degreeOf {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (b : Fin n → ℤ)
    (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (α' : Fin r → K)
    (h D0 : ℕ) (Dj : Fin r → ℕ) (p : AuxIdx r h D0 Dj → K) (t0 : ℕ) (t : Fin (r - 1) → ℕ) :
    (Qpoly φ b k L ι α' h D0 Dj p t0 t).degreeOf 0 ≤ h * (D0 + 1) ∧
    ∀ j : Fin r, (Qpoly φ b k L ι α' h D0 Dj p t0 t).degreeOf j.succ ≤ Dj j := by
  classical
  constructor
  · rw [Qpoly]
    apply degreeOf_finset_sum_le
    intro lm _
    exact Qpoly_summand_degreeOf_zero φ b k L ι α' h D0 Dj p t0 t lm
  · intro j
    rw [Qpoly]
    apply degreeOf_finset_sum_le
    intro lm _
    exact Qpoly_summand_degreeOf_succ φ b k L ι α' h D0 Dj p t0 t lm j

end Work.BW
