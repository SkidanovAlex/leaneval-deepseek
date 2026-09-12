import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Algebra.MvPolynomial

/-- For a polynomial in no variables, evaluation at the unique point is the algebra
isomorphism with the base ring. -/
lemma eval_eq_isEmptyAlgEquiv {F σ : Type*} [CommSemiring F] [IsEmpty σ]
    (x : σ → F) (p : MvPolynomial σ F) :
    MvPolynomial.eval x p = MvPolynomial.isEmptyAlgEquiv F σ p := by
  have h : p = MvPolynomial.C (MvPolynomial.isEmptyAlgEquiv F σ p) := by
    rw [← MvPolynomial.isEmptyAlgEquiv_symm_apply]
    exact ((MvPolynomial.isEmptyAlgEquiv F σ).symm_apply_apply p).symm
  conv_lhs => rw [h]
  exact MvPolynomial.eval_C _

/-- Main induction: a nonzero polynomial of total degree at most `T` in `N` variables does not
vanish on the whole simplex `{u : Fin N → ℕ | ∑ i, u i ≤ T}`. -/
theorem exists_eval_ne_zero_of_totalDegree_le_simplex_aux {F : Type*} [Field F] [CharZero F]
    (N : ℕ) : ∀ (T : ℕ) (p : MvPolynomial (Fin N) F), p ≠ 0 → p.totalDegree ≤ T →
      ∃ u : Fin N → ℕ, (∑ i, u i ≤ T) ∧ MvPolynomial.eval (fun i : Fin N => (u i : F)) p ≠ 0 := by
  induction N with
  | zero =>
    intro T p hp _
    refine ⟨Fin.elim0, ?_, ?_⟩
    · simp
    · rw [eval_eq_isEmptyAlgEquiv]
      intro h
      exact hp ((MvPolynomial.isEmptyAlgEquiv F (Fin 0)).injective (by simpa using h))
  | succ N IH =>
    intro T p hp hdeg
    set P : Polynomial (MvPolynomial (Fin N) F) := MvPolynomial.finSuccEquiv F N p with hP
    have hPne : P ≠ 0 := by
      rw [hP]
      intro h
      exact hp ((MvPolynomial.finSuccEquiv F N).injective (by simpa using h))
    set d : ℕ := P.natDegree with hd
    set c : MvPolynomial (Fin N) F := P.coeff d with hc
    have hcne : c ≠ 0 := by
      rw [hc, hd, Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hPne
    have hbdd : c.totalDegree + d ≤ T := by
      have h := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le p d
        (by rw [← hP, ← hc]; exact hcne)
      rw [← hP, ← hc] at h
      exact le_trans h hdeg
    have hcd : c.totalDegree ≤ T - d := by omega
    have hdT : d ≤ T := by omega
    obtain ⟨u', hu'sum, hu'ne⟩ := IH (T - d) c hcne hcd
    set x : Fin N → F := fun i => (u' i : F) with hx
    have hxne : MvPolynomial.eval x c ≠ 0 := by rw [hx]; exact hu'ne
    set q : Polynomial F := Polynomial.map (MvPolynomial.eval x) P with hq
    have hqne : q ≠ 0 := by
      intro hq0
      have h1 : q.coeff d = 0 := by rw [hq0]; simp
      rw [hq, Polynomial.coeff_map, ← hc] at h1
      exact hxne h1
    have hqdeg : q.natDegree ≤ d := by
      rw [hq, hd]
      exact Polynomial.natDegree_map_le
    obtain ⟨y, hyd, hyne⟩ : ∃ y : ℕ, y ≤ d ∧ q.eval (y : F) ≠ 0 := by
      by_contra h
      push Not at h
      exact hqne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero q
        (f := fun i : Fin (d + 1) => ((i : ℕ) : F))
        (fun i j hij => Fin.ext (Nat.cast_injective hij))
        (fun i => h (i : ℕ) (Nat.lt_succ_iff.mp i.isLt))
        (by rw [Fintype.card_fin]; exact Nat.lt_succ_of_le hqdeg))
    refine ⟨(Fin.cons y u' : Fin (N + 1) → ℕ), ?_, ?_⟩
    · rw [Fin.sum_cons]
      omega
    · have hsub : (fun i : Fin (N + 1) => (((Fin.cons y u' : Fin (N + 1) → ℕ) i : ℕ) : F))
            = (fun i => Fin.cases ((MvPolynomial.eval x) (MvPolynomial.C (y : F))) x i) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [Fin.cons_zero, Fin.cases_zero]
        · simp [Fin.cons_succ, Fin.cases_succ, hx]
      rw [hsub, ← MvPolynomial.eval_polynomial_eval_finSuccEquiv p (MvPolynomial.C (y : F))]
      rw [← Polynomial.eval_map_apply]
      simp only [MvPolynomial.eval_C]
      rw [← hP, ← hq]
      exact hyne

theorem exists_eval_ne_zero_of_totalDegree_le_simplex {F : Type*} [Field F] [CharZero F] {N T : ℕ}
    (p : MvPolynomial (Fin N) F) (hp : p ≠ 0) (hdeg : p.totalDegree ≤ T) :
    ∃ u : Fin N → ℕ, (∑ i, u i ≤ T) ∧ MvPolynomial.eval (fun i : Fin N => (u i : F)) p ≠ 0 :=
  exists_eval_ne_zero_of_totalDegree_le_simplex_aux N T p hp hdeg

end Commons.Algebra.MvPolynomial