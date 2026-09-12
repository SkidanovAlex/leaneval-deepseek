import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace Commons.Algebra.MvPolynomial

/-- The "universal evaluation map" associated with a family `ωb : Fin n → K`: substituting
`X_j ↦ ∑_i ωb_i * X (i,j)` in `ℚ`-coefficient polynomials over `Fin r` variables. -/
theorem univEval_eval {K : Type*} [Field K] [CharZero K] {n r : ℕ} (ωb : Fin n → K) :
    ∃ ρ : MvPolynomial (Fin r) ℚ →ₐ[ℚ] MvPolynomial (Fin n × Fin r) K,
      (∀ f, (ρ f).totalDegree ≤ f.totalDegree) ∧
      ∀ (u : Fin n × Fin r → ℚ) (f : MvPolynomial (Fin r) ℚ),
        MvPolynomial.eval (fun p => (u p : K)) (ρ f)
          = MvPolynomial.aeval (fun j : Fin r => ∑ i : Fin n, (u (i, j) : ℚ) • ωb i) f := by
  classical
  let g : Fin r → MvPolynomial (Fin n × Fin r) K :=
    fun j => ∑ i : Fin n, MvPolynomial.C (ωb i) * MvPolynomial.X (i, j)
  refine ⟨MvPolynomial.aeval g, ?_, ?_⟩
  · intro f
    have hg : ∀ j : Fin r, (g j).IsHomogeneous 1 := by
      intro j
      have hg' : g j = ∑ i ∈ (Finset.univ : Finset (Fin n)),
          MvPolynomial.C (ωb i) * MvPolynomial.X (i, j) := rfl
      rw [hg']
      exact MvPolynomial.IsHomogeneous.sum _ _ _
        (fun i _ => (MvPolynomial.isHomogeneous_C _ _).mul (MvPolynomial.isHomogeneous_X _ _))
    have hdecomp : MvPolynomial.aeval g f =
        ∑ m ∈ Finset.range (f.totalDegree + 1),
          MvPolynomial.aeval g (MvPolynomial.homogeneousComponent m f) := by
      conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent (R := ℚ) f]
      rw [map_sum]
    rw [hdecomp]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro m hm
    have hmle : m ≤ f.totalDegree := by
      have := Finset.mem_range.mp hm
      omega
    calc (MvPolynomial.aeval g (MvPolynomial.homogeneousComponent m f)).totalDegree
        ≤ m := by
          apply MvPolynomial.IsHomogeneous.totalDegree_le
          have h := (MvPolynomial.homogeneousComponent_isHomogeneous (R := ℚ) m f).aeval g hg
          simpa using h
      _ ≤ f.totalDegree := hmle
  · intro u f
    let φ : MvPolynomial (Fin n × Fin r) K →ₐ[ℚ] K :=
      MvPolynomial.aevalTower (AlgHom.id ℚ K) (fun p => (u p : K))
    have hφ : ∀ p, φ p = MvPolynomial.eval (fun p => (u p : K)) p := fun p => rfl
    have hfun : (fun j => φ (g j)) =
        (fun j : Fin r => ∑ i : Fin n, (u (i, j) : ℚ) • ωb i) := by
      funext j
      have h1 : φ (g j) = ∑ i : Fin n, ωb i * (u (i, j) : K) := by
        rw [show g j = ∑ i : Fin n, MvPolynomial.C (ωb i) * MvPolynomial.X (i, j) from rfl,
          map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_mul, MvPolynomial.aevalTower_C, MvPolynomial.aevalTower_X, AlgHom.id_apply]
      rw [h1]
      apply Finset.sum_congr rfl
      intro i _
      simp [Algebra.smul_def, mul_comm]
    calc MvPolynomial.eval (fun p => (u p : K)) (MvPolynomial.aeval g f)
        = φ (MvPolynomial.aeval g f) := (hφ _).symm
      _ = (φ.comp (MvPolynomial.aeval g)) f := rfl
      _ = (MvPolynomial.aeval (fun j => φ (g j))) f := by
            rw [MvPolynomial.comp_aeval (f := g) φ]
      _ = MvPolynomial.aeval (fun j : Fin r => ∑ i : Fin n, (u (i, j) : ℚ) • ωb i) f := by
            rw [hfun]

end Commons.Algebra.MvPolynomial