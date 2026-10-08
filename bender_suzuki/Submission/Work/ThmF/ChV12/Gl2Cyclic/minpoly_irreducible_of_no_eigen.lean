import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12.Gl2Cyclic

theorem minpoly_irreducible_of_no_eigen {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (h2 : Module.finrank F V = 2) {x : V →ₗ[F] V}
    (hns : ∀ c : F, x ≠ c • (1 : V →ₗ[F] V))
    (hreg : ∀ c : F, ∀ v : V, v ≠ 0 → x v ≠ c • v) :
    Irreducible (minpoly F x) := by
  -- `minpoly F x` is monic (as `x` is integral over the field `F`).
  have hp_monic : (minpoly F x).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  -- It is not the constant polynomial `1`: otherwise `1 = 0` in `End F V`,
  -- forcing `V` to be a subsingleton, contradicting `finrank F V = 2`.
  have hp_ne1 : minpoly F x ≠ 1 := by
    intro hp1
    have hone : (1 : V →ₗ[F] V) = 0 := by
      have h := minpoly.aeval F x
      rw [hp1] at h
      simpa using h
    have hsub : Subsingleton V := by
      refine ⟨fun a b => ?_⟩
      have ha : a = 0 := by
        have h := congrArg (fun f : V →ₗ[F] V => f a) hone
        simpa using h
      have hb : b = 0 := by
        have h := congrArg (fun f : V →ₗ[F] V => f b) hone
        simpa using h
      rw [ha, hb]
    have hfr : Module.finrank F V = 0 :=
      @Module.finrank_zero_of_subsingleton F V _ _ _ _ hsub
    rw [h2] at hfr
    exact absurd hfr (by norm_num)
  -- Lower bound on the degree: a monic polynomial which is not `1` has positive degree.
  have hnatpos : 1 ≤ (minpoly F x).natDegree := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    exact hp_ne1 (by
      have hc := Polynomial.eq_C_of_natDegree_eq_zero h0
      have hcoeff : (minpoly F x).coeff 0 = 1 := by
        have h := hp_monic.coeff_natDegree
        rwa [h0] at h
      rw [hc, hcoeff, Polynomial.C_1])
  -- Upper bound on the degree: `minpoly F x ∣ charpoly F x`, whose degree is `finrank = 2`.
  have hledeg : (minpoly F x).natDegree ≤ 2 := by
    have hdvd : minpoly F x ∣ x.charpoly := LinearMap.minpoly_dvd_charpoly x
    have hchar : x.charpoly ≠ 0 := (LinearMap.charpoly_monic x).ne_zero
    have h := Polynomial.natDegree_le_of_dvd hdvd hchar
    rw [LinearMap.charpoly_natDegree x, h2] at h
    exact h
  -- `minpoly F x` has no root: a root would be an eigenvalue of `x`,
  -- contradicting the hypothesis that `x` has no eigenvectors.
  have hroot : ∀ c : F, ¬ (minpoly F x).IsRoot c := by
    intro c hc
    have hEv := Module.End.hasEigenvalue_of_isRoot hc
    obtain ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hEv
    exact hreg c v hv.2 hv.apply_eq_smul
  -- A polynomial of degree 2 or 3 over a field is irreducible iff it has no roots.
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (p := minpoly F x) ?_ hroot
  rw [Finset.mem_Icc]
  exact ⟨hnatpos, by omega⟩

end Work.ThmF.ChV12.Gl2Cyclic
