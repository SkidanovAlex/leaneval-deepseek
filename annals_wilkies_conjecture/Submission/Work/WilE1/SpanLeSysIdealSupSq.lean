import Mathlib
import Submission.Work.WilE1.Setup

/-!
# The `m ⊆ (F) + m²` step of the Bezout bound (area E1)

Let `R = ℂ[X_1,…,X_k]`, let `l_j = X_j - C (x_j)` be the generators of the maximal ideal `𝔪` of
the point `x : Fin k → ℂ`, and let `F : Fin k → R`.  If an invertible matrix `C` expresses each
`F i` as the linear combination `∑ j, C i j * l j` modulo `𝔪²`, then `𝔪 ⊆ (F) + 𝔪²`.

Indeed, `w i := ∑ j, C i j • l j` lies in `J := (F) ⊔ 𝔪²` (it is `F i` minus an element of `𝔪²`),
and multiplying the system `w = C • l` by the adjugate of `C` gives `C.det • l j ∈ J` for every
`j`; since `C.det` is invertible in the field `ℂ`, this yields `l j ∈ J`.
-/

namespace Work.WilE1

/-- Linear-algebra core of the argument: if `C` is a square matrix over `S`, `v` a vector in an
`S`-algebra `A`, and every row `∑ j, C i j • v j` of the product `C · v` lies in an ideal `J ⊆ A`,
then `C.det • v j ∈ J` for every `j` (multiply the system by the adjugate of `C`). -/
theorem det_smul_mem_of_row_mem {ι S A : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing S] [CommRing A] [Algebra S A]
    (C : Matrix ι ι S) (v : ι → A) (J : Ideal A)
    (h : ∀ i, ∑ j, C i j • v j ∈ J) :
    ∀ j, C.det • v j ∈ J := by
  intro j
  have h1 : ∀ m, (∑ i, C.adjugate j i • (C i m • v m)) = (C.adjugate * C) j m • v m := by
    intro m
    rw [Matrix.mul_apply, Finset.sum_smul]
    simp only [smul_smul]
  have key : C.det • v j = ∑ i, C.adjugate j i • (∑ m, C i m • v m) := by
    calc C.det • v j
        = ∑ m, (C.adjugate * C) j m • v m := by
            rw [Matrix.adjugate_mul]
            simp [Matrix.smul_apply, Matrix.one_apply]
      _ = ∑ m, ∑ i, C.adjugate j i • (C i m • v m) := by
            exact Finset.sum_congr rfl (fun m _ => (h1 m).symm)
      _ = ∑ i, ∑ m, C.adjugate j i • (C i m • v m) := Finset.sum_comm
      _ = ∑ i, C.adjugate j i • (∑ m, C i m • v m) := by
            exact Finset.sum_congr rfl (fun i _ => (Finset.smul_sum).symm)
  rw [key]
  apply Ideal.sum_mem
  intro i _
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (h i)

/-- If an invertible matrix `C` makes each `F i` agree with the linear combination
`∑ j, C i j * (X j - C (x j))` modulo `𝔪²`, then the maximal ideal `𝔪` of the point `x` is
contained in `(F) + 𝔪²`. -/
theorem SpanLeSysIdealSupSq {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ) (x : Fin k → ℂ)
    (C : Matrix (Fin k) (Fin k) ℂ) (hC : C.det ≠ 0)
    (hrel : ∀ i, F i - ∑ j, MvPolynomial.C (C i j) * (MvPolynomial.X j - MvPolynomial.C (x j))
      ∈ (Ideal.span (Set.range fun j =>
          (MvPolynomial.X j - MvPolynomial.C (x j) : MvPolynomial (Fin k) ℂ)))^2) :
    Ideal.span (Set.range fun j =>
        (MvPolynomial.X j - MvPolynomial.C (x j) : MvPolynomial (Fin k) ℂ)) ≤
      sysIdeal F ⊔ (Ideal.span (Set.range fun j =>
          (MvPolynomial.X j - MvPolynomial.C (x j) : MvPolynomial (Fin k) ℂ)))^2 := by
  let l : Fin k → MvPolynomial (Fin k) ℂ := fun j => MvPolynomial.X j - MvPolynomial.C (x j)
  let J : Ideal (MvPolynomial (Fin k) ℂ) :=
    sysIdeal F ⊔ (Ideal.span (Set.range l)) ^ 2
  change Ideal.span (Set.range l) ≤ J
  -- Each row `∑ j, C i j • l j` differs from `F i` by an element of `𝔪²`, hence lies in `J`.
  have hrows : ∀ i, ∑ j, C i j • l j ∈ J := by
    intro i
    have hFi : F i ∈ J :=
      (le_sup_left : sysIdeal F ≤ J) (Ideal.subset_span (Set.mem_range_self i))
    have h2 : F i - ∑ j, C i j • l j ∈ J :=
      (le_sup_right : (Ideal.span (Set.range l)) ^ 2 ≤ J)
        (by simpa [l, MvPolynomial.smul_eq_C_mul] using hrel i)
    have := J.sub_mem hFi h2
    simpa using this
  -- Multiply by the adjugate of `C`, then by `(det C)⁻¹`, to solve for `l j`.
  have hdet : ∀ j, C.det • l j ∈ J := det_smul_mem_of_row_mem C l J hrows
  have hmem : ∀ j, l j ∈ J := by
    intro j
    have h := hdet j
    have hthis : (C.det)⁻¹ • (C.det • l j) = l j := by
      rw [smul_smul, inv_mul_cancel₀ hC, one_smul]
    rw [← hthis, Algebra.smul_def]
    exact Ideal.mul_mem_left J _ h
  rw [Ideal.span_le]
  intro y hy
  rw [Set.mem_range] at hy
  obtain ⟨j, rfl⟩ := hy
  exact hmem j

end Work.WilE1
