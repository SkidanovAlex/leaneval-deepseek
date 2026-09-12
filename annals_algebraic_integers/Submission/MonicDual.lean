import Mathlib
/-!
# The monic complex dual condition (algebraic engine of `thm:adjust`)
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace Submission.MonicDual

/-- The monic quotient `Q_i = Q/(X − α_i)` as an explicit subproduct. -/
noncomputable def qic {n : ℕ} (α : Fin n → ℂ) (i : Fin n) : Polynomial ℂ :=
  ∏ k ∈ (Finset.univ.erase i), (Polynomial.X - Polynomial.C (α k))

/-- `Q` complexified. -/
noncomputable def Qc (Q : Polynomial ℤ) : Polynomial ℂ :=
  Q.map (algebraMap ℤ ℂ)

/-- The `j`-th synthetic-division quotient coefficient polynomial (integer
coefficients): `coeff j (Q /ₘ (X - C r)) = eval r ((rq Q j).map ℤ→ℂ)`. -/
noncomputable def rq (Q : Polynomial ℤ) (j : ℕ) : Polynomial ℤ :=
  ∑ t ∈ Finset.Icc (j + 1) Q.natDegree,
    Polynomial.C (Q.coeff t) * Polynomial.X ^ (t - (j + 1))

/-- The integer polynomial `d ↦ Σ_j d_j · r_j`. -/
noncomputable def Dpoly (Q : Polynomial ℤ) {n : ℕ} (d : Fin n → ℤ) : Polynomial ℤ :=
  ∑ j : Fin n, Polynomial.C (d j) * rq Q (j.val)

/-- The dual evaluation value `c_i = Σ_j d_j · (qic_i).coeff j`. -/
noncomputable def cval {n : ℕ} (α : Fin n → ℂ) (d : Fin n → ℤ) (i : Fin n) : ℂ :=
  ∑ j : Fin n, ((d j : ℂ) * (qic α i).coeff (j.val))

-- ------------------------------------------------ general polynomial helpers

lemma coeff_finset_sum {R : Type*} [Semiring R] {ι : Type*} (s : Finset ι)
    (f : ι → R[X]) (N : ℕ) :
    (∑ i ∈ s, f i).coeff N = ∑ i ∈ s, (f i).coeff N := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      rw [Finset.sum_insert ha]
      rw [Polynomial.coeff_add]
      rw [ih]

lemma coeff_fintype_sum {R : Type*} [Semiring R] {ι : Type*} [Fintype ι]
    (f : ι → R[X]) (N : ℕ) :
    (∑ i : ι, f i).coeff N = ∑ i : ι, (f i).coeff N := by
  classical
  simpa using (coeff_finset_sum (s := (Finset.univ : Finset ι)) (f := f) (N := N))

lemma polynomial_map_finset_sum {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S)
    {ι : Type*} (s : Finset ι) (f : ι → R[X]) :
    (∑ i ∈ s, f i).map φ = ∑ i ∈ s, (f i).map φ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      rw [Finset.sum_insert ha]
      rw [Polynomial.map_add]
      rw [ih]

-- map over products
lemma polynomial_map_finset_prod {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) {ι : Type*} (s : Finset ι) (f : ι → R[X]) :
    (∏ i ∈ s, f i).map φ = ∏ i ∈ s, (f i).map φ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      rw [Finset.prod_insert ha]
      rw [Polynomial.map_mul]
      rw [ih]

-- resultant of a product of linear factors
lemma resultant_prod_X_sub_C {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} (a : Fin n → R) (g : R[X]) :
    (∏ i : Fin n, (X - C (a i))).resultant g = ∏ i : Fin n, eval (a i) g := by
  rw [Polynomial.resultant_prod_left (s := (Finset.univ : Finset (Fin n)))
      (f := fun i : Fin n => (X - C (a i))) (g := g) (n := g.natDegree)]
  · simp [Polynomial.resultant_X_sub_C_left]
  · simp
  · rfl

-- resultant commutes with injective coefficient maps (default degree arguments)
lemma resultant_map_comm {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) (f g : R[X]) :
    (f.map φ).resultant (g.map φ) = φ (f.resultant g) := by
  have hf : (f.map φ).natDegree = f.natDegree := Polynomial.natDegree_map_eq_of_injective hφ f
  have hg : (g.map φ).natDegree = g.natDegree := Polynomial.natDegree_map_eq_of_injective hφ g
  rw [hf, hg]
  exact Polynomial.resultant_map_map (f := f) (g := g) (m := f.natDegree) (n := g.natDegree) φ

-- product over univ = factor * product over erase
lemma prod_univ_eq_mul_erase {n : ℕ} (f : Fin n → ℂ[X]) (i : Fin n) :
    (∏ k : Fin n, f k) = f i * ∏ k ∈ (Finset.univ.erase i), f k := by
  classical
  rw [← Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin n))) (a := i) f]
  simp

-- coefficients of the complexification
lemma Qc_coeff (Q : Polynomial ℤ) (t : ℕ) : (Qc Q).coeff t = (Q.coeff t : ℂ) := by
  simp [Qc]

-- ------------------------------------------------ Component A: qic coefficients

lemma qic_mul {n : ℕ} (Q : Polynomial ℤ) (α : Fin n → ℂ)
    (hfac : Qc Q = ∏ i : Fin n, (X - C (α i))) (i : Fin n) :
    Qc Q = (X - C (α i)) * qic α i := by
  rw [hfac]
  rw [prod_univ_eq_mul_erase (f := fun k : Fin n => (X - C (α k))) (i := i)]
  rfl

lemma qic_div {n : ℕ} (Q : Polynomial ℤ) (α : Fin n → ℂ)
    (hfac : Qc Q = ∏ i : Fin n, (X - C (α i))) (i : Fin n) :
    qic α i = Qc Q /ₘ (X - C (α i)) := by
  rw [qic_mul Q α hfac i]
  rw [Polynomial.mul_divByMonic_cancel_left (p := qic α i) (q := (X - C (α i)))
    (Polynomial.monic_X_sub_C (α i))]

lemma qic_coeff {n : ℕ} (Q : Polynomial ℤ) (α : Fin n → ℂ)
    (hfac : Qc Q = ∏ i : Fin n, (X - C (α i))) (i : Fin n) (j : ℕ) :
    (qic α i).coeff j =
      ∑ t ∈ Finset.Icc (j + 1) Q.natDegree, (α i) ^ (t - (j + 1)) * (Qc Q).coeff t := by
  rw [qic_div Q α hfac i]
  rw [Polynomial.coeff_divByMonic_X_sub_C (p := Qc Q) (a := α i) (n := j)]
  congr 1
  congr 1
  exact (Polynomial.natDegree_map_eq_of_injective (f := algebraMap ℤ ℂ)
    Int.cast_injective Q)

lemma rq_eval {n : ℕ} (Q : Polynomial ℤ) (α : Fin n → ℂ) (i : Fin n) (j : ℕ) :
    eval (α i) ((rq Q j).map (algebraMap ℤ ℂ)) =
      ∑ t ∈ Finset.Icc (j + 1) Q.natDegree,
        (α i) ^ (t - (j + 1)) * (Qc Q).coeff t := by
  rw [rq]
  rw [polynomial_map_finset_sum (algebraMap ℤ ℂ)]
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  rw [show ((algebraMap ℤ ℂ) (Q.coeff t) : ℂ) = (Qc Q).coeff t by
    rw [Qc]
    simp]
  ring

lemma qic_coeff_eq_rq {n : ℕ} (Q : Polynomial ℤ) (α : Fin n → ℂ)
    (hfac : Qc Q = ∏ i : Fin n, (X - C (α i))) (i : Fin n) (j : ℕ) :
    (qic α i).coeff j = eval (α i) ((rq Q j).map (algebraMap ℤ ℂ)) := by
  rw [qic_coeff Q α hfac i j, rq_eval]

-- ------------------------------------------------ Component A2: c_i = D(α_i)

lemma map_eval_C (P : Polynomial ℂ) (z : ℂ) :
    eval (Polynomial.C z) (P.map (Polynomial.C : ℂ →+* Polynomial ℂ)) =
      Polynomial.C (P.eval z) := by
  rw [Polynomial.eval_map]
  induction P using Polynomial.induction_on' with
  | add P Q ihP ihQ => simp [ihP, ihQ]
  | monomial n a =>
      rw [show Polynomial.monomial n a = Polynomial.C a * Polynomial.X ^ n by
        rw [Polynomial.C_mul_X_pow_eq_monomial]]
      simp

lemma cval_eq_eval_D {n : ℕ} (Q : Polynomial ℤ) (α : Fin n → ℂ)
    (hfac : Qc Q = ∏ i : Fin n, (X - C (α i))) (d : Fin n → ℤ) (i : Fin n) :
    cval α d i = eval (α i) ((Dpoly Q d).map (algebraMap ℤ ℂ)) := by
  rw [cval]
  trans eval (α i) (∑ j : Fin n,
      Polynomial.C ((d j : ℂ)) * (rq Q (j.val)).map (algebraMap ℤ ℂ))
  · rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [qic_coeff_eq_rq Q α hfac i (j.val)]
    rw [Polynomial.eval_mul, Polynomial.eval_C]
  · apply congrArg (eval (α i))
    rw [Dpoly]
    rw [polynomial_map_finset_sum (algebraMap ℤ ℂ)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Polynomial.map_mul, Polynomial.map_C]
    simp


-- ------------------------------------------------ Component R: resultant identities

/-- The resultant of `(∏ (X - α_i))` (the complexification of `Q`) with
`T - D(X)` factors as `∏_i (T - D(α_i))`; here `D(α_i) = cval α d i`. -/
lemma res_complex {n : ℕ} (Q : Polynomial ℤ) (α : Fin n → ℂ) (d : Fin n → ℤ)
    (hfac : Qc Q = ∏ i : Fin n, (X - C (α i))) :
    ((Qc Q).map (Polynomial.C : ℂ →+* Polynomial ℂ)).resultant
        (Polynomial.C (Polynomial.X : Polynomial ℂ) -
          ((Dpoly Q d).map (algebraMap ℤ ℂ)).map (Polynomial.C : ℂ →+* Polynomial ℂ))
      = ∏ i : Fin n, (Polynomial.X - Polynomial.C (cval α d i)) := by
  let g : Polynomial (Polynomial ℂ) :=
    Polynomial.C (Polynomial.X : Polynomial ℂ) -
      ((Dpoly Q d).map (algebraMap ℤ ℂ)).map (Polynomial.C : ℂ →+* Polynomial ℂ)
  have hfacmap : (Qc Q).map (Polynomial.C : ℂ →+* Polynomial ℂ)
      = ∏ i : Fin n, (Polynomial.X - Polynomial.C (Polynomial.C (α i))) := by
    rw [hfac]
    rw [polynomial_map_finset_prod (Polynomial.C : ℂ →+* Polynomial ℂ)]
    apply Finset.prod_congr rfl
    intro i hi
    simp [Polynomial.map_sub]
  have heval : ∀ i : Fin n,
      eval (Polynomial.C (α i)) g = Polynomial.X - Polynomial.C (cval α d i) := by
    intro i
    change eval (Polynomial.C (α i)) (Polynomial.C (Polynomial.X : Polynomial ℂ) -
          ((Dpoly Q d).map (algebraMap ℤ ℂ)).map (Polynomial.C : ℂ →+* Polynomial ℂ))
        = Polynomial.X - Polynomial.C (cval α d i)
    rw [Polynomial.eval_sub, Polynomial.eval_C]
    rw [map_eval_C ((Dpoly Q d).map (algebraMap ℤ ℂ)) (α i)]
    rw [← (cval_eq_eval_D Q α hfac d i)]
  rw [hfacmap]
  rw [resultant_prod_X_sub_C (R := Polynomial ℂ) (a := fun i : Fin n => Polynomial.C (α i)) (g := g)]
  apply Finset.prod_congr rfl
  intro i hi
  exact heval i

/-- The resultant (over ℤ[T]) maps to the product `∏_i (T - cval α d i)` in `ℂ[T]`. -/
lemma res_int {n : ℕ} (Q : Polynomial ℤ) (α : Fin n → ℂ) (d : Fin n → ℤ)
    (hfac : Qc Q = ∏ i : Fin n, (X - C (α i))) :
    ((Q.map (Polynomial.C : ℤ →+* Polynomial ℤ)).resultant
        (Polynomial.C (Polynomial.X : Polynomial ℤ) -
          (Dpoly Q d).map (Polynomial.C : ℤ →+* Polynomial ℤ))).map (algebraMap ℤ ℂ)
      = ∏ i : Fin n, (Polynomial.X - Polynomial.C (cval α d i)) := by
  let φ0 : ℤ →+* ℂ := algebraMap ℤ ℂ
  let Φ : Polynomial ℤ →+* Polynomial ℂ := Polynomial.mapRingHom φ0
  let fZ : Polynomial (Polynomial ℤ) := Q.map (Polynomial.C : ℤ →+* Polynomial ℤ)
  let gZ : Polynomial (Polynomial ℤ) :=
    Polynomial.C (Polynomial.X : Polynomial ℤ) -
      (Dpoly Q d).map (Polynomial.C : ℤ →+* Polynomial ℤ)
  have hh : (Polynomial.mapRingHom φ0).comp (Polynomial.C : ℤ →+* Polynomial ℤ)
      = (Polynomial.C : ℂ →+* Polynomial ℂ).comp φ0 := by
    ext k
    simp
  have hf : fZ.map Φ = (Qc Q).map (Polynomial.C : ℂ →+* Polynomial ℂ) := by
    unfold Qc
    change (Q.map (Polynomial.C : ℤ →+* Polynomial ℤ)).map Φ
      = (Q.map φ0).map (Polynomial.C : ℂ →+* Polynomial ℂ)
    rw [Polynomial.map_map, Polynomial.map_map]
    exact congrArg (fun h : ℤ →+* Polynomial ℂ => Q.map h) hh
  have hg : gZ.map Φ = Polynomial.C (Polynomial.X : Polynomial ℂ) -
      ((Dpoly Q d).map φ0).map (Polynomial.C : ℂ →+* Polynomial ℂ) := by
    rw [Polynomial.map_sub]
    rw [show (Polynomial.C (Polynomial.X : Polynomial ℤ)).map Φ =
        Polynomial.C (Polynomial.X : Polynomial ℂ) by
      rw [Polynomial.map_C]
      simp [Φ]]
    rw [Polynomial.map_map, Polynomial.map_map]
    apply congrArg (fun p : Polynomial (Polynomial ℂ) =>
      Polynomial.C (Polynomial.X : Polynomial ℂ) - p)
    exact congrArg (fun h : ℤ →+* Polynomial ℂ => (Dpoly Q d).map h) hh
  have hres := resultant_map_comm (φ := Φ) (f := fZ) (g := gZ) (by
    exact Polynomial.map_injective φ0 Int.cast_injective)
  change Φ ((fZ).resultant gZ) = ∏ i : Fin n, (Polynomial.X - Polynomial.C (cval α d i))
  rw [← hres]
  rw [hf, hg]
  exact res_complex Q α d hfac

-- ------------------------------------------------ Component D: d ≠ 0 → some cval ≠ 0

lemma rq_coeff_eq_zero (Q : Polynomial ℤ) {j m : ℕ} (hm : Q.natDegree - 1 - j < m) :
    (rq Q j).coeff m = 0 := by
  rw [rq]
  rw [coeff_finset_sum]
  apply Finset.sum_eq_zero
  intro t ht
  have ht2 : t ≤ Q.natDegree := (Finset.mem_Icc.mp ht).2
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  calc
    (Polynomial.C (Q.coeff t) * Polynomial.X ^ (t - (j + 1))).natDegree
        ≤ t - (j + 1) := Polynomial.natDegree_C_mul_X_pow_le _ _
    _ ≤ Q.natDegree - (j + 1) := by omega
    _ < m := by omega

lemma rq_coeff_self (Q : Polynomial ℤ) {j : ℕ} (hj : j < Q.natDegree) :
    (rq Q j).coeff (Q.natDegree - 1 - j) = Q.coeff Q.natDegree := by
  have h0 : ∀ b ∈ Finset.Icc (j + 1) Q.natDegree, b ≠ Q.natDegree →
      (Polynomial.C (Q.coeff b) * Polynomial.X ^ (b - (j + 1))).coeff (Q.natDegree - (j + 1)) = 0 := by
    intro b hb hbne
    have hb1 : j + 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have hb2 : b ≤ Q.natDegree := (Finset.mem_Icc.mp hb).2
    have hb3 : b < Q.natDegree := lt_of_le_of_ne hb2 hbne
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    calc
      (Polynomial.C (Q.coeff b) * Polynomial.X ^ (b - (j + 1))).natDegree ≤ b - (j + 1) :=
        Polynomial.natDegree_C_mul_X_pow_le _ _
      _ < Q.natDegree - (j + 1) := by omega
  have h1 : Q.natDegree ∉ Finset.Icc (j + 1) Q.natDegree →
      (Polynomial.C (Q.coeff Q.natDegree) * Polynomial.X ^ (Q.natDegree - (j + 1))).coeff
        (Q.natDegree - (j + 1)) = 0 := by
    intro hbnot
    exfalso
    exact hbnot (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have hconv : Q.natDegree - 1 - j = Q.natDegree - (j + 1) := by omega
  rw [hconv]
  calc
    (rq Q j).coeff (Q.natDegree - (j + 1))
        = ∑ t ∈ Finset.Icc (j + 1) Q.natDegree,
            (Polynomial.C (Q.coeff t) * Polynomial.X ^ (t - (j + 1))).coeff (Q.natDegree - (j + 1)) := by
            rw [rq, coeff_finset_sum]
    _ = (Polynomial.C (Q.coeff Q.natDegree) * Polynomial.X ^ (Q.natDegree - (j + 1))).coeff
          (Q.natDegree - (j + 1)) :=
          Finset.sum_eq_single (s := (Finset.Icc (j + 1) Q.natDegree))
            (f := fun t : ℕ => (Polynomial.C (Q.coeff t) * Polynomial.X ^ (t - (j + 1))).coeff
              (Q.natDegree - (j + 1)))
            (a := Q.natDegree) h0 h1
    _ = Q.coeff Q.natDegree := by
          rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
          simp

lemma coeff_Dpoly_eq_d {n : ℕ} (Q : Polynomial ℤ) (hQn : Q.natDegree = n) (hQm : Q.Monic)
    (d : Fin n → ℤ) (e : Fin n) (hind : ∀ j : Fin n, j.val < e.val → d j = 0) :
    (Dpoly Q d).coeff (n - 1 - e.val) = d e := by
  have hside : ∀ j ∈ (Finset.univ : Finset (Fin n)), j ≠ e →
      (Polynomial.C (d j) * rq Q (j.val)).coeff (n - 1 - e.val) = 0 := by
    intro j hj hje
    by_cases hlt : j.val < e.val
    · have dj : d j = 0 := hind j hlt
      rw [Polynomial.coeff_C_mul, dj]
      simp
    · have hgt : e.val < j.val := by
        have hval : j.val ≠ e.val := by
          intro hv
          exact hje (Fin.ext hv)
        omega
      rw [Polynomial.coeff_C_mul]
      rw [rq_coeff_eq_zero Q (j := j.val) (m := n - 1 - e.val) (by
        rw [hQn]
        omega)]
      simp
  have he_not : e ∉ (Finset.univ : Finset (Fin n)) →
      (Polynomial.C (d e) * rq Q (e.val)).coeff (n - 1 - e.val) = 0 := by
    intro henot
    exact (henot (Finset.mem_univ e)).elim
  calc
    (Dpoly Q d).coeff (n - 1 - e.val)
        = (Polynomial.C (d e) * rq Q (e.val)).coeff (n - 1 - e.val) := by
            rw [Dpoly, coeff_fintype_sum]
            exact Finset.sum_eq_single (s := (Finset.univ : Finset (Fin n)))
              (f := fun j : Fin n => (Polynomial.C (d j) * rq Q (j.val)).coeff (n - 1 - e.val))
              (a := e) hside he_not
    _ = d e := by
          rw [Polynomial.coeff_C_mul]
          rw [show (rq Q (e.val)).coeff (n - 1 - e.val) = Q.coeff Q.natDegree by
            simpa [hQn] using (rq_coeff_self Q (j := e.val) (by simpa [hQn] using e.isLt))]
          have hlead : Q.coeff Q.natDegree = 1 := by
            change Q.leadingCoeff = 1
            exact hQm
          rw [hlead, mul_one]

lemma d_eq_zero_of_Dpoly {n : ℕ} (Q : Polynomial ℤ) (hQn : Q.natDegree = n)
    (hQm : Q.Monic) (d : Fin n → ℤ) (hD : Dpoly Q d = 0) : d = 0 := by
  classical
  have hstep : ∀ k : ℕ, (∀ m < k, ∀ j : Fin n, j.val = m → d j = 0) →
      ∀ j : Fin n, j.val = k → d j = 0 := by
    intro k ih j hk
    have hind : ∀ a : Fin n, a.val < j.val → d a = 0 := by
      intro a ha
      exact ih a.val (by rw [← hk]; exact ha) a rfl
    have hcoef := coeff_Dpoly_eq_d Q hQn hQm d j hind
    have hfromD := congrArg (fun P : Polynomial ℤ => P.coeff (n - 1 - j.val)) hD
    rw [hcoef] at hfromD
    simpa using hfromD
  funext e
  exact (Nat.strong_induction_on e.val (p := fun k => ∀ j : Fin n, j.val = k → d j = 0) hstep) e rfl

lemma Dpoly_coeff_eq_zero_of_ge {n : ℕ} (Q : Polynomial ℤ) (hQn : Q.natDegree = n) (d : Fin n → ℤ)
    {N : ℕ} (hN : n ≤ N) :
    (Dpoly Q d).coeff N = 0 := by
  rw [Dpoly]
  rw [coeff_fintype_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Polynomial.coeff_C_mul]
  rw [rq_coeff_eq_zero Q (j := j.val) (m := N) (by
    rw [hQn]
    omega)]
  simp

lemma Dc_natDegree_lt {n : ℕ} (Q : Polynomial ℤ) (hQn : Q.natDegree = n)
    (hn : 1 ≤ n) (d : Fin n → ℤ) :
    ((Dpoly Q d).map (algebraMap ℤ ℂ)).natDegree < n := by
  have hdeg : (Dpoly Q d).natDegree ≤ n - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    exact Dpoly_coeff_eq_zero_of_ge Q hQn d (by omega)
  have hmap : ((Dpoly Q d).map (algebraMap ℤ ℂ)).natDegree ≤ n - 1 := by
    calc
      ((Dpoly Q d).map (algebraMap ℤ ℂ)).natDegree ≤ (Dpoly Q d).natDegree :=
        Polynomial.natDegree_map_le
      _ ≤ n - 1 := hdeg
  omega

/-- `d ≠ 0` implies some dual value `c_i` is nonzero. -/
lemma exists_cval_ne_zero {n : ℕ} (Q : Polynomial ℤ) (hQn : Q.natDegree = n)
    (hQm : Q.Monic) (hn : 1 ≤ n) (α : Fin n → ℂ) (hαinj : Function.Injective α)
    (hfac : Qc Q = ∏ i : Fin n, (X - C (α i)))
    (d : Fin n → ℤ) (hd : d ≠ 0) : ∃ i : Fin n, cval α d i ≠ 0 := by
  by_contra h
  push Not at h
  have heval : ∀ i : Fin n, eval (α i) ((Dpoly Q d).map (algebraMap ℤ ℂ)) = 0 := by
    intro i
    rw [← cval_eq_eval_D Q α hfac d i]
    exact h i
  have hDc0 : (Dpoly Q d).map (algebraMap ℤ ℂ) = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (p := (Dpoly Q d).map (algebraMap ℤ ℂ)) (f := α)
    · exact hαinj
    · exact heval
    · simpa using Dc_natDegree_lt Q hQn hn d
  have hD0 : Dpoly Q d = 0 := by
    exact (Polynomial.map_eq_zero_iff (f := algebraMap ℤ ℂ) (Int.cast_injective)).mp hDc0
  have hd0 : d = 0 := d_eq_zero_of_Dpoly Q hQn hQm d hD0
  exact hd hd0

-- ------------------------------------------------ Component K: Kronecker lemma

lemma coeff_zero_eq_eval_zero (P : Polynomial ℂ) : P.coeff 0 = eval 0 P := by
  rw [show eval 0 P = Polynomial.eval₂ (RingHom.id ℂ) 0 P by rfl]
  rw [Polynomial.eval₂_at_zero]
  simp

lemma prod_lt_one_of_pos_lt_one {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hs : s.Nonempty) (h0 : ∀ i ∈ s, 0 < f i) (h1 : ∀ i ∈ s, f i < 1) :
    (∏ i ∈ s, f i) < 1 := by
  classical
  rcases hs with ⟨i₀, hi₀⟩
  have hrest : (∏ i ∈ s.erase i₀, f i) ≤ 1 := by
    refine Finset.prod_le_one (R := ℝ) (s := s.erase i₀) (f := f) ?_ ?_
    · intro i hi
      exact le_of_lt (h0 i (Finset.mem_of_mem_erase hi))
    · intro i hi
      exact le_of_lt (h1 i (Finset.mem_of_mem_erase hi))
  calc
    (∏ i ∈ s, f i) = f i₀ * (∏ i ∈ s.erase i₀, f i) := by
      rw [← Finset.prod_erase_mul (s := s) (f := f) (a := i₀) hi₀]
      rw [mul_comm]
    _ ≤ f i₀ * 1 := by
      exact mul_le_mul_of_nonneg_left hrest (le_of_lt (h0 i₀ hi₀))
    _ = f i₀ := by rw [mul_one]
    _ < 1 := h1 i₀ hi₀

lemma int_cast_norm_ge_one {k : ℤ} (hk : k ≠ 0) : (1 : ℝ) ≤ ‖(k : ℂ)‖ := by
  rw [Complex.norm_intCast]
  rcases le_total (0 : ℤ) k with hnn | hneg
  · have hki : (1 : ℤ) ≤ k := by omega
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hki
    rw [abs_of_nonneg (by exact_mod_cast hnn : 0 ≤ (k : ℝ))]
    exact hk1
  · have hki : k ≤ -1 := by omega
    have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast hki
    rw [abs_of_nonpos (le_trans hk1 (by norm_num : (-1 : ℝ) ≤ 0))]
    linarith

/-- If a polynomial with integer coefficients maps to `∏ (X - c_i)` and every
`c_i` has norm `< 1`, while some `c_i` is nonzero, there is a contradiction
(a nonzero integer with norm `< 1`). -/
lemma kronecker_contra {ι : Type*} [Fintype ι] (F : Polynomial ℤ) (c : ι → ℂ)
    (hmap : F.map (algebraMap ℤ ℂ) = ∏ i : ι, (X - C (c i)))
    (hne : ∃ i, c i ≠ 0) (hsmall : ∀ i, ‖c i‖ < 1) : False := by
  classical
  let Z : Finset ι := (Finset.univ : Finset ι).filter (fun i => c i = 0)
  let NZ : Finset ι := (Finset.univ : Finset ι).filter (fun i => c i ≠ 0)
  let s : ℕ := Z.card
  let H1 : Polynomial ℂ := ∏ i ∈ NZ, (X - C (c i))
  -- ∏ over univ = ∏_Z · ∏_NZ, and ∏_Z = X^s
  have hfz : (∏ i ∈ Z, (X - C (c i))) = Polynomial.X ^ s := by
    have hcongr : (∏ i ∈ Z, (X - C (c i))) = (∏ i ∈ Z, Polynomial.X) := by
      refine Finset.prod_congr rfl ?_
      intro i hi
      have hci : c i = 0 := (Finset.mem_filter.mp hi).2
      rw [hci]
      simp
    calc
      (∏ i ∈ Z, (X - C (c i))) = (∏ i ∈ Z, Polynomial.X) := hcongr
      _ = Polynomial.X ^ Z.card := by rw [Finset.prod_const]
      _ = Polynomial.X ^ s := rfl
  have hsplit : (F.map (algebraMap ℤ ℂ)) = (Polynomial.X ^ s) * H1 := by
    rw [hmap]
    calc
      (∏ i : ι, (X - C (c i))) = (∏ i ∈ (Finset.univ : Finset ι), (X - C (c i))) := rfl
      _ = (∏ i ∈ Z, (X - C (c i))) * (∏ i ∈ NZ, (X - C (c i))) := by
        rw [← Finset.prod_filter_mul_prod_filter_not (s := (Finset.univ : Finset ι))
          (p := fun i => c i = 0) (f := fun i => (X - C (c i)))]
      _ = (Polynomial.X ^ s) * H1 := by rw [hfz]
  -- F.coeff s maps to H1.coeff 0
  have hcoeff : (algebraMap ℤ ℂ) (F.coeff s) = H1.coeff 0 := by
    calc
      (algebraMap ℤ ℂ) (F.coeff s) = (F.map (algebraMap ℤ ℂ)).coeff s := by simp
      _ = (Polynomial.X ^ s * H1).coeff s := by rw [hsplit]
      _ = H1.coeff 0 := by
        rw [mul_comm]
        simpa using (Polynomial.coeff_mul_X_pow (p := H1) (n := s) (d := 0))
  -- H1.coeff 0 ≠ 0
  have hce : H1.coeff 0 = eval 0 H1 := coeff_zero_eq_eval_zero H1
  have hH1ne0 : H1.coeff 0 ≠ 0 := by
    rw [hce, Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hci : c i ≠ 0 := (Finset.mem_filter.mp hi).2
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    simpa using (neg_ne_zero.mpr hci)
  -- F.coeff s ≠ 0
  have hFne0 : F.coeff s ≠ 0 := by
    intro hF
    apply hH1ne0
    rw [← hcoeff, hF]
    simp
  -- norm contradiction
  have hnormbig : (1 : ℝ) ≤ ‖(F.coeff s : ℂ)‖ := int_cast_norm_ge_one hFne0
  have hnormsmall : ‖H1.coeff 0‖ < 1 := by
    rw [hce, Polynomial.eval_prod, norm_prod]
    refine prod_lt_one_of_pos_lt_one NZ (fun i => ‖eval 0 (X - C (c i))‖) ?_ ?_ ?_
    · rcases hne with ⟨i, hi⟩
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    · intro i hi
      have hci : c i ≠ 0 := (Finset.mem_filter.mp hi).2
      have hneval : eval 0 (X - C (c i)) ≠ 0 := by
        rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        simpa using (neg_ne_zero.mpr hci)
      exact norm_pos_iff.mpr hneval
    · intro i hi
      have h : ‖eval 0 (X - C (c i))‖ = ‖c i‖ := by
        rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        rw [zero_sub, norm_neg]
      rw [h]
      exact hsmall i
  -- ‖φ(F.coeff s)‖ = ‖H1.coeff 0‖ ≥ 1 vs < 1
  have hle : (1 : ℝ) ≤ ‖H1.coeff 0‖ := by
    rw [← hcoeff]
    exact hnormbig
  exact (not_lt_of_ge hle) hnormsmall



/-- The monic complex dual condition: for every nonzero integer vector `d`, some
row of the coefficient matrix `(b_ij)`, `b_ij := (qic α i).coeff j`, has inner
product with `d` of absolute value at least 1. -/
theorem monic_dual {n : ℕ} (hn : 1 ≤ n) (Q : Polynomial ℤ) (hQm : Q.Monic)
    (hQn : Q.natDegree = n) (α : Fin n → ℂ) (hαinj : Function.Injective α)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i)))
    (d : Fin n → ℤ) (hd : d ≠ 0) :
    ∃ i : Fin n, (1 : ℝ) ≤ ‖∑ j : Fin n, ((d j : ℂ) * (qic α i).coeff (j.val))‖ := by
  classical
  let F : Polynomial ℤ := (Q.map (Polynomial.C : ℤ →+* Polynomial ℤ)).resultant
      (Polynomial.C (Polynomial.X : Polynomial ℤ) -
        (Dpoly Q d).map (Polynomial.C : ℤ →+* Polynomial ℤ))
  by_contra h
  have hsmall : ∀ i : Fin n, ‖cval α d i‖ < 1 := by
    intro i
    refine lt_of_not_ge ?_
    intro hle
    apply h
    refine ⟨i, ?_⟩
    simpa [cval] using hle
  have hmap : F.map (algebraMap ℤ ℂ) = ∏ i : Fin n, (X - C (cval α d i)) := by
    dsimp [F]
    exact res_int Q α d hfac
  have hne : ∃ i : Fin n, cval α d i ≠ 0 :=
    exists_cval_ne_zero Q hQn hQm hn α hαinj hfac d hd
  exact kronecker_contra F (cval α d) hmap hne hsmall

end Submission.MonicDual

