import Mathlib
import Submission.Commons.Algebra.MvPolynomial.exists_eval_ne_zero_of_totalDegree_le_simplex
import Submission.Commons.NumberTheory.NumberField.exists_certificate_poly

namespace Commons.NumberTheory.NumberField

open MvPolynomial

/-- `house` of an integer multiple. -/
lemma house_int_smul {K : Type*} [Field K] [NumberField K] (m : ℤ) (x : K) :
    NumberField.house (m • x) ≤ |(m : ℝ)| * NumberField.house x := by
  have h : m • x = (m : K) * x := by rw [zsmul_eq_mul]
  rw [h]
  calc NumberField.house ((m : K) * x) ≤ NumberField.house ((m : K)) * NumberField.house x :=
        NumberField.house_mul_le _ _
    _ = |(m : ℝ)| * NumberField.house x := by rw [NumberField.house_intCast, Int.cast_abs]

variable {K : Type*} [Field K] [NumberField K]

/-- The integral point of `𝓞 K^r` encoded by the natural coordinates `u` in the basis `ωb`. -/
noncomputable def ptInt {n r : ℕ}
    (ωb : Module.Basis (Fin n) ℤ (NumberField.RingOfIntegers K)) (u : Fin n × Fin r → ℕ) :
    Fin r → NumberField.RingOfIntegers K :=
  fun j => ∑ i : Fin n, (u (i, j) : ℤ) • (ωb i)

/-- The natural point and the rational point agree. -/
lemma ptInt_coe {n r : ℕ}
    (ωb : Module.Basis (Fin n) ℤ (NumberField.RingOfIntegers K)) (u : Fin n × Fin r → ℕ) (j : Fin r) :
    ((ptInt ωb u j : NumberField.RingOfIntegers K) : K) = pt ωb (fun p => (u p : ℚ)) j := by
  simp only [ptInt, pt, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_zsmul, zsmul_eq_mul, Algebra.smul_def]
  push_cast
  rfl

/-- Reduction of the main goal to an explicit polynomial certificate: if `Q` is a nonzero polynomial
of total degree `≤ d * n * (r+1)` in the coordinates `u : Fin n × Fin r → ℚ` whose non-vanishing at
`u` guarantees that the point `pt ωb u` is well poised in degree `d`, then there is a well poised
point of `𝓞 K^r` with all `house`s bounded by `d * n * (r+1) * R`. -/
theorem exists_wellPoised_point_bounded_of_certificate
    (n r d : ℕ)
    (hn : Module.finrank ℚ K = n) (ωb : Module.Basis (Fin n) ℤ (NumberField.RingOfIntegers K))
    (R : ℝ) (hR : ∀ i, NumberField.house (((ωb i : NumberField.RingOfIntegers K) : K)) ≤ R)
    (hd : 0 < d)
    (Q : MvPolynomial (Fin n × Fin r) ℚ) (hQ : Q ≠ 0) (hQdeg : Q.totalDegree ≤ d * n * (r + 1))
    (hcert : ∀ u : Fin n × Fin r → ℚ, MvPolynomial.eval u Q ≠ 0 →
        ∀ g : K × (Fin r → K), ∃ f : MvPolynomial (Fin r) ℚ, f.totalDegree ≤ d ∧
          MvPolynomial.aeval (pt ωb u) f = g.1 ∧
          ∀ j : Fin r, MvPolynomial.aeval (pt ωb u) (MvPolynomial.pderiv j f) = g.2 j) :
    ∃ κ : Fin r → NumberField.RingOfIntegers K,
      (∀ j, NumberField.house (((κ j : NumberField.RingOfIntegers K) : K)) ≤ (↑d * ↑n * ↑(r + 1)) * R) ∧
      (∀ g : K × (Fin r → K), ∃ f : MvPolynomial (Fin r) ℚ, f.totalDegree ≤ d ∧
        (MvPolynomial.aeval (fun j : Fin r => (((κ j : NumberField.RingOfIntegers K) : K)))) f = g.1 ∧
        ∀ j : Fin r, (MvPolynomial.aeval (fun j : Fin r => (((κ j : NumberField.RingOfIntegers K) : K)))) (MvPolynomial.pderiv j f) = g.2 j) := by
  classical
  have hnpos : 0 < n := by rw [← hn]; exact Module.finrank_pos
  -- reindex the variables `Fin n × Fin r` as `Fin (n * r)`
  have hcard : Fintype.card (Fin n × Fin r) = n * r := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  obtain ⟨e⟩ : Nonempty (Fin n × Fin r ≃ Fin (n * r)) := ⟨Fintype.equivFinOfCardEq hcard⟩
  set Q' : MvPolynomial (Fin (n * r)) ℚ := MvPolynomial.renameEquiv ℚ e Q with hQ'def
  have hQ'ne : Q' ≠ 0 := by
    rw [hQ'def]
    intro h
    exact hQ ((MvPolynomial.renameEquiv ℚ e).injective (by rw [h]; simp))
  have hQ'deg : Q'.totalDegree ≤ d * n * (r + 1) := by
    rw [hQ'def, MvPolynomial.totalDegree_renameEquiv]; exact hQdeg
  obtain ⟨v, hvsum, hvne⟩ :=
    Commons.Algebra.MvPolynomial.exists_eval_ne_zero_of_totalDegree_le_simplex
      (F := ℚ) Q' hQ'ne hQ'deg
  let u : Fin n × Fin r → ℕ := fun p => v (e p)
  have hueval : MvPolynomial.eval (fun p => (u p : ℚ)) Q ≠ 0 := by
    have h1 : MvPolynomial.eval (fun p : Fin n × Fin r => (u p : ℚ)) Q
        = MvPolynomial.eval (fun i : Fin (n * r) => (v i : ℚ)) Q' := by
      rw [hQ'def]
      simp only [MvPolynomial.renameEquiv_apply]
      rw [MvPolynomial.eval_rename]
      rfl
    rw [h1]; exact hvne
  have husum : ∑ p : Fin n × Fin r, u p ≤ d * n * (r + 1) := by
    have h1 : ∑ p : Fin n × Fin r, u p = ∑ i : Fin (n * r), v i :=
      Fintype.sum_equiv e (fun p => v (e p)) (fun i => v i) (fun p => rfl)
    rw [h1]; exact hvsum
  have hsplit : ∑ p : Fin n × Fin r, u p = ∑ j : Fin r, ∑ i : Fin n, u (i, j) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_comm
  have hcol : ∀ j : Fin r, ∑ i : Fin n, u (i, j) ≤ d * n * (r + 1) := by
    intro j
    have hle : ∑ i : Fin n, u (i, j) ≤ ∑ j' : Fin r, ∑ i : Fin n, u (i, j') :=
      Finset.single_le_sum (f := fun j' => ∑ i : Fin n, u (i, j'))
        (fun j' _ => Nat.zero_le _) (Finset.mem_univ j)
    rw [← hsplit] at hle
    exact le_trans hle husum
  have hR0 : 0 ≤ R := (NumberField.house_nonneg _).trans (hR ⟨0, hnpos⟩)
  refine ⟨ptInt ωb u, ?_, ?_⟩
  · intro j
    have h1 : NumberField.house (((ptInt ωb u j : NumberField.RingOfIntegers K) : K))
        = NumberField.house (pt ωb (fun p => (u p : ℚ)) j) := by rw [ptInt_coe]
    rw [h1, pt]
    have h2 := NumberField.house_sum_le_sum_house (Finset.univ : Finset (Fin n))
      (fun i => (u (i, j) : ℚ) • (((ωb i : NumberField.RingOfIntegers K) : K)))
    have h3 : ∀ i : Fin n,
        NumberField.house ((u (i, j) : ℚ) • (((ωb i : NumberField.RingOfIntegers K) : K)))
        ≤ (u (i, j) : ℝ) * R := by
      intro i
      have hnn : (0 : ℝ) ≤ (u (i, j) : ℝ) := by positivity
      have hz : ((u (i, j) : ℤ) • (((ωb i : NumberField.RingOfIntegers K) : K)))
          = (u (i, j) : ℚ) • (((ωb i : NumberField.RingOfIntegers K) : K)) := by
        rw [zsmul_eq_mul, Algebra.smul_def]
        push_cast
        ring
      rw [← hz]
      refine le_trans (house_int_smul (u (i, j) : ℤ) _) ?_
      have habs : (|(((u (i, j) : ℤ) : ℝ))|) = (u (i, j) : ℝ) := by
        rw [← Int.cast_abs]; simp
      rw [habs]
      exact mul_le_mul_of_nonneg_left (hR i) hnn
    have h4 : ∑ i : Fin n, (u (i, j) : ℝ) * R ≤ (d : ℝ) * n * (r + 1) * R := by
      rw [← Finset.sum_mul]
      have hcast : (∑ i : Fin n, (u (i, j) : ℝ)) = ((∑ i : Fin n, u (i, j) : ℕ) : ℝ) := by
        push_cast; rfl
      rw [hcast]
      have h2' : ((∑ i : Fin n, u (i, j) : ℕ) : ℝ) ≤ ((d * n * (r + 1) : ℕ) : ℝ) := by
        exact_mod_cast hcol j
      calc ((∑ i : Fin n, u (i, j) : ℕ) : ℝ) * R
          ≤ ((d * n * (r + 1) : ℕ) : ℝ) * R := mul_le_mul_of_nonneg_right h2' hR0
        _ = (d : ℝ) * n * (r + 1) * R := by push_cast; ring
    calc NumberField.house (∑ i : Fin n, (u (i, j) : ℚ) • (((ωb i : NumberField.RingOfIntegers K) : K)))
        ≤ ∑ i : Fin n, NumberField.house ((u (i, j) : ℚ) • (((ωb i : NumberField.RingOfIntegers K) : K))) := h2
      _ ≤ ∑ i : Fin n, (u (i, j) : ℝ) * R := Finset.sum_le_sum (fun i _ => h3 i)
      _ ≤ (d : ℝ) * n * (r + 1) * R := h4
      _ = (↑d * ↑n * ↑(r + 1)) * R := by push_cast; ring
  · intro g
    have hpt : pt ωb (fun p => (u p : ℚ))
        = fun j => (((ptInt ωb u j : NumberField.RingOfIntegers K) : K)) := by
      funext j
      rw [ptInt_coe]
    obtain ⟨f, hfdeg, hf1, hf2⟩ := hcert (fun p => (u p : ℚ)) hueval g
    refine ⟨f, hfdeg, ?_, ?_⟩
    · rw [← hpt]; exact hf1
    · intro j; rw [← hpt]; exact hf2 j

/-- Main lemma: there is a well poised point of `𝓞 K^r` whose `house`s are bounded by
`d * n * (r+1) * R`, where `R` bounds the `house`s of the elements of the integral basis `ωb`. -/
theorem exists_wellPoised_point_bounded (K : Type*) [Field K] [NumberField K] (n r d : ℕ) (hn : Module.finrank ℚ K = n) (ωb : Module.Basis (Fin n) ℤ (NumberField.RingOfIntegers K)) (R : ℝ) (hR : ∀ i, NumberField.house (((ωb i : NumberField.RingOfIntegers K) : K)) ≤ R) (hd : 0 < d) (h : (n - 1) * (r + 1) < (d + r - 1).choose r) : ∃ κ : Fin r → NumberField.RingOfIntegers K, (∀ j, NumberField.house (((κ j : NumberField.RingOfIntegers K) : K)) ≤ (↑d * ↑n * ↑(r + 1)) * R) ∧ (∀ g : K × (Fin r → K), ∃ f : MvPolynomial (Fin r) ℚ, f.totalDegree ≤ d ∧ (MvPolynomial.aeval (fun j : Fin r => (((κ j : NumberField.RingOfIntegers K) : K)))) f = g.1 ∧ ∀ j : Fin r, (MvPolynomial.aeval (fun j : Fin r => (((κ j : NumberField.RingOfIntegers K) : K)))) (MvPolynomial.pderiv j f) = g.2 j) := by
  obtain ⟨Q, hQ, hQdeg, hcert⟩ :=
    Commons.NumberTheory.NumberField.exists_certificate_poly K n r d hn ωb hd h
  exact exists_wellPoised_point_bounded_of_certificate n r d hn ωb R hR hd Q hQ hQdeg hcert

end Commons.NumberTheory.NumberField
