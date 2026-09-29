import Mathlib
import Submission.Work.ZeroEst.case_det_cramer

namespace Work.ZeroEst2

/-!
# Cramer's identity for a row-space relation (`Work.ZeroEst2.cramer_identity`)

Let `v Q : Fin r → Fin m → K` be two families of vectors in `Kᵐ` (here `K = ℚ(x)`) whose
`K`-row spaces coincide, and let `I : Fin r → Fin m` select `r` columns such that the
`r × r` minor `A = Q_{·I}` is invertible.  Writing `B = v_{·I}` for the same minor of `v`,
the *Cramer identity* says that for every row `i` and every `f : Fin m → R` into a ring `R`
receiving the coefficients,

  `det(A) · Σ_j v_{ij} f_j = Σ_k (B · adj(A))_{ik} · (Σ_j Q_{kj} f_j)`

(this is step L3 of the zero-estimate plan, see `Submission/Work/ZeroEst2/NOTES_H236_on_lead_plan.md`).

The mathematical content is that the row space of `v` equals the row space of `Q`, so on the
`r` selected columns the coefficient matrix `C` with `v = C·Q` satisfies `C·A = B`; multiplying
by `adj(A)` and using `A·adj(A) = det(A)·1` gives `det(A)·C = B·adj(A)`, whose entries are
polynomials, and the identity follows.

We prove the abstract field version first (`cramer_rows`), then transport it from `ℚ(x)` to
`ℚ⟦x⟧` along the (injective) coefficient embedding.
-/

/-- **Cramer's identity, field form.** If the rows of `v` are `K`-linear combinations of the rows
of `Q` and `A = Q_{·I}` has nonzero determinant, then `det A • v_{ij} = Σ_k (B·adj A)_{ik} Q_{kj}`
with `B = v_{·I}`. -/
theorem cramer_rows {K : Type*} [Field K] {r m : ℕ}
    (v Q : Fin r → Fin m → K) (I : Fin r → Fin m)
    (hrow : ∀ i, (fun j => v i j) ∈ Submodule.span K (Set.range Q)) :
    ∀ i j, (Matrix.of (fun k b => Q k (I b))).det * v i j =
      ∑ k, ((Matrix.of (fun a b => v a (I b))) *
            (Matrix.of (fun k b => Q k (I b))).adjugate) i k * Q k j := by
  classical
  -- coefficients expressing each row of `v` in the rows of `Q`
  have hex : ∀ i, ∃ C : Fin r → K, ∀ j, v i j = ∑ k, C k * Q k j := by
    intro i
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hrow i)
    refine ⟨c, fun j => ?_⟩
    have h := congr_fun hc j
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h.symm
  choose C hC using hex
  set A : Matrix (Fin r) (Fin r) K := Matrix.of (fun k b => Q k (I b)) with hA
  set B : Matrix (Fin r) (Fin r) K := Matrix.of (fun a b => v a (I b)) with hB
  -- `B = C * A`: restricting a combination of rows to the selected columns
  have hBA : B = Matrix.of C * A := by
    ext i b
    rw [hB, hA]
    simp only [Matrix.of_apply, Matrix.mul_apply]
    rw [hC i (I b)]
  -- `B * adj A = C * A * adj A = C * (det A • 1) = det A • C`
  have hprod : B * A.adjugate = A.det • Matrix.of C := by
    rw [hBA, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
  intro i j
  have hentry : ∀ k, (B * A.adjugate) i k = A.det * C i k := by
    intro k
    have h := congr_fun (congr_fun hprod i) k
    simpa [Matrix.smul_apply] using h
  rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => by rw [hentry k]), hC i j,
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- **Cramer's identity (CDT zero-estimate step L3).** For polynomial families `v, Q` whose
`ℚ(x)`-row spans coincide and whose `r × r` minor at the columns `I` is invertible, the rows of
`v` evaluated against any `f : Fin m → ℚ⟦x⟧` are determined by the rows of `Q` through the
adjugate of that minor, with `det (Q_{·I})` clearing the denominators. -/
theorem cramer_identity {r m : ℕ} (v Q : Fin r → Fin m → Polynomial ℚ) (I : Fin r → Fin m)
    (hspan : Submodule.span (RatFunc ℚ)
        (Set.range fun i => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (v i j)) =
      Submodule.span (RatFunc ℚ)
        (Set.range fun k => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (Q k j)))
    (hdet : (Matrix.of (fun k b : Fin r =>
        algebraMap (Polynomial ℚ) (RatFunc ℚ) (Q k (I b)))).det ≠ 0)
    (f : Fin m → PowerSeries ℚ) :
    ∀ i, ((Matrix.of (fun k b : Fin r => Q k (I b))).det : PowerSeries ℚ) *
          (∑ j, (v i j : PowerSeries ℚ) * f j) =
      ∑ k, (((Matrix.of (fun a b : Fin r => v a (I b))) *
              (Matrix.of (fun k b : Fin r => Q k (I b))).adjugate) i k : PowerSeries ℚ) *
          (∑ j, (Q k j : PowerSeries ℚ) * f j) := by
  classical
  -- each row of `v` lies in the `ℚ(x)`-row span of `Q`
  have hrowK : ∀ i, (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (v i j)) ∈
      Submodule.span (RatFunc ℚ)
        (Set.range fun k => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (Q k j)) := by
    intro i
    rw [← hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  set A : Matrix (Fin r) (Fin r) (Polynomial ℚ) := Matrix.of (fun k b => Q k (I b)) with hA
  set B : Matrix (Fin r) (Fin r) (Polynomial ℚ) := Matrix.of (fun a b => v a (I b)) with hB
  -- the identity over `ℚ(x)`
  have hK := cramer_rows (K := RatFunc ℚ)
      (v := fun i j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (v i j))
      (Q := fun k j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (Q k j)) I hrowK
  have hAK : (Matrix.of (fun k b => algebraMap (Polynomial ℚ) (RatFunc ℚ) (Q k (I b))))
      = A.map (algebraMap (Polynomial ℚ) (RatFunc ℚ)) := by
    ext k b; simp [hA, Matrix.map_apply]
  have hBK : (Matrix.of (fun a b => algebraMap (Polynomial ℚ) (RatFunc ℚ) (v a (I b))))
      = B.map (algebraMap (Polynomial ℚ) (RatFunc ℚ)) := by
    ext a b; simp [hB, Matrix.map_apply]
  rw [hAK, hBK] at hK
  have hadj : (A.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))).adjugate
      = (A.adjugate).map (algebraMap (Polynomial ℚ) (RatFunc ℚ)) := by
    rw [← RingHom.mapMatrix_apply (algebraMap (Polynomial ℚ) (RatFunc ℚ)) A,
        ← RingHom.mapMatrix_apply (algebraMap (Polynomial ℚ) (RatFunc ℚ)) A.adjugate,
        RingHom.map_adjugate]
  -- descend from `ℚ(x)` to `ℚ[x]` (the embedding is injective)
  have hpol : ∀ i j, A.det * v i j = ∑ k, (B * A.adjugate) i k * Q k j := by
    intro i j
    apply IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ)
    rw [map_mul, map_sum]
    rw [show algebraMap (Polynomial ℚ) (RatFunc ℚ) A.det
        = (A.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))).det from
      RingHom.map_det (algebraMap (Polynomial ℚ) (RatFunc ℚ)) A]
    rw [hK i j]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_mul]
    congr 1
    rw [hadj, ← Matrix.map_mul]
    rfl
  -- the coefficient embedding `ℚ[x] → ℚ⟦x⟧` is a ring hom
  have hcoe_mul : ∀ p q : Polynomial ℚ, ((p * q : Polynomial ℚ) : PowerSeries ℚ)
      = (p : PowerSeries ℚ) * (q : PowerSeries ℚ) :=
    fun p q => map_mul Polynomial.coeToPowerSeries.ringHom p q
  have hcoe_sum : ∀ (n : ℕ) (g : Fin n → Polynomial ℚ),
      ((∑ i, g i : Polynomial ℚ) : PowerSeries ℚ) = ∑ i, (g i : PowerSeries ℚ) :=
    fun n g => map_sum Polynomial.coeToPowerSeries.ringHom g Finset.univ
  intro i
  have hterm : ∀ j, ((A.det * v i j : Polynomial ℚ) : PowerSeries ℚ)
      = ∑ k, ((B * A.adjugate) i k : PowerSeries ℚ) * (Q k j : PowerSeries ℚ) := by
    intro j
    rw [hpol i j, hcoe_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact hcoe_mul ((B * A.adjugate) i k) (Q k j)
  calc (A.det : PowerSeries ℚ) * (∑ j, (v i j : PowerSeries ℚ) * f j)
      = ∑ j, ((A.det * v i j : Polynomial ℚ) : PowerSeries ℚ) * f j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [hcoe_mul]
        ring
    _ = ∑ j, (∑ k, ((B * A.adjugate) i k : PowerSeries ℚ) * (Q k j : PowerSeries ℚ)) * f j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hterm j]
    _ = ∑ j, ∑ k, ((B * A.adjugate) i k : PowerSeries ℚ) * (Q k j : PowerSeries ℚ) * f j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
    _ = ∑ k, ∑ j, ((B * A.adjugate) i k : PowerSeries ℚ) * (Q k j : PowerSeries ℚ) * f j :=
        Finset.sum_comm
    _ = ∑ k, ((B * A.adjugate) i k : PowerSeries ℚ) * (∑ j, (Q k j : PowerSeries ℚ) * f j) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring

end Work.ZeroEst2
