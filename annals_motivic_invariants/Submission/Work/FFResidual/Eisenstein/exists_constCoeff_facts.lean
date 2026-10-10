import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FFResidual.Eisenstein

open Polynomial

/-- **The constant-term functional of `AdjoinRoot f`.**  For `f` monic of positive degree there is an
`R`-linear functional `c` on `AdjoinRoot f` which reads off the `X ^ 0`-coefficient of the
representative of degree `< f.natDegree` (namely `c s = ((AdjoinRoot.modByMonicHom hmon) s).coeff 0`,
so `c` can be taken to be `(Polynomial.lcoeff R 0).comp (AdjoinRoot.modByMonicHom hmon)`; use
`AdjoinRoot.modByMonicHom_mk`, `AdjoinRoot.mk_leftInverse`, `Polynomial.modByMonic_eq_self_iff`,
`Polynomial.modByMonic_eq_of_dvd_sub`, `Polynomial.modByMonic_eq_sub_mul_div`, `Polynomial.divX`).
It satisfies: `c 1 = 1`, `c (x ^ i)` is `1` for `i = 0` and `0` for `0 < i < f.natDegree`,
`c (x * t) ∈ I` whenever `f.coeff 0 ∈ I`, `c (x ^ f.natDegree) = -f.coeff 0`, and `s - c s` is
divisible by `x`. -/
theorem exists_constCoeff_facts {R : Type} [CommRing R] {f : Polynomial R} (hmon : f.Monic)
    (hdeg : 0 < f.natDegree) :
    ∃ c : AdjoinRoot f →ₗ[R] R,
      c 1 = 1 ∧
      (∀ i, i < f.natDegree → c (AdjoinRoot.root f ^ i) = if i = 0 then 1 else 0) ∧
      (∀ (I : Ideal R), f.coeff 0 ∈ I → ∀ t : AdjoinRoot f, c (AdjoinRoot.root f * t) ∈ I) ∧
      c (AdjoinRoot.root f ^ f.natDegree) = -f.coeff 0 ∧
      (∀ s : AdjoinRoot f,
        ∃ t : AdjoinRoot f, s = algebraMap R (AdjoinRoot f) (c s) + AdjoinRoot.root f * t) := by
  -- `f ≠ 0` because it is monic of positive degree; consequently `R` is nontrivial.
  have hfne : f ≠ 0 := fun h => by
    rw [h, Polynomial.natDegree_zero] at hdeg
    exact Nat.lt_irrefl 0 hdeg
  have hR : Nontrivial R := Nontrivial.of_polynomial_ne hfne
  -- The constant-term functional on the canonical `%ₘ`-representative.
  refine ⟨(Polynomial.lcoeff R 0).comp (AdjoinRoot.modByMonicHom hmon), ?_, ?_, ?_, ?_, ?_⟩
  · -- `c 1 = 1`
    rw [LinearMap.comp_apply, Polynomial.lcoeff_apply]
    have h1 : (1 : AdjoinRoot f) = AdjoinRoot.mk f (1 : Polynomial R) := by
      rw [RingHom.map_one]
    rw [h1, AdjoinRoot.modByMonicHom_mk, (Polynomial.modByMonic_eq_self_iff hmon).mpr ?_]
    · simp
    · rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree hmon.ne_zero]
      exact_mod_cast hdeg
  · -- `c (x ^ i) = if i = 0 then 1 else 0` for `i < f.natDegree`
    intro i hi
    have hroot : (AdjoinRoot.root f) ^ i = AdjoinRoot.mk f (Polynomial.X ^ i) := by
      rw [← AdjoinRoot.mk_X, map_pow]
    rw [LinearMap.comp_apply, Polynomial.lcoeff_apply, hroot, AdjoinRoot.modByMonicHom_mk]
    have hmod : (Polynomial.X ^ i) %ₘ f = Polynomial.X ^ i :=
      (Polynomial.modByMonic_eq_self_iff hmon).mpr (by
        rw [Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree hmon.ne_zero]
        exact_mod_cast hi)
    rw [hmod, Polynomial.coeff_X_pow]
    by_cases h : i = 0 <;> simp [h, eq_comm]
  · -- `c (x * t) ∈ I` whenever `f.coeff 0 ∈ I`
    intro I hI t
    set g : Polynomial R := AdjoinRoot.modByMonicHom hmon t with hg
    have key : AdjoinRoot.mk f (Polynomial.X * g) = AdjoinRoot.root f * t := by
      rw [hg, map_mul, AdjoinRoot.mk_X]
      congr 1
      exact AdjoinRoot.mk_leftInverse hmon t
    rw [LinearMap.comp_apply, Polynomial.lcoeff_apply, ← key, AdjoinRoot.modByMonicHom_mk]
    -- the constant term of `X * g` is `0`, and reducing modulo `f` only adds a multiple of `f`:
    -- `(X * g) %ₘ f + f * ((X * g) /ₘ f) = X * g`.
    have hprod : (f * ((Polynomial.X * g) /ₘ f)).coeff 0
        = f.coeff 0 * ((Polynomial.X * g) /ₘ f).coeff 0 := by
      rw [Polynomial.coeff_mul]; simp
    have hcoeff := congrArg (fun p : Polynomial R => p.coeff 0)
      (Polynomial.modByMonic_add_div (Polynomial.X * g) f)
    rw [Polynomial.coeff_add, hprod, Polynomial.coeff_X_mul_zero] at hcoeff
    rw [eq_neg_of_add_eq_zero_left hcoeff]
    exact I.neg_mem (Ideal.mul_mem_right _ I hI)
  · -- `c (x ^ f.natDegree) = -f.coeff 0`
    have hroot : (AdjoinRoot.root f) ^ f.natDegree
        = AdjoinRoot.mk f (Polynomial.X ^ f.natDegree) := by
      rw [← AdjoinRoot.mk_X, map_pow]
    rw [LinearMap.comp_apply, Polynomial.lcoeff_apply, hroot, AdjoinRoot.modByMonicHom_mk]
    -- `X ^ n %ₘ f = X ^ n - f` for `n = f.natDegree`
    have hsub : (Polynomial.X ^ f.natDegree - f).degree < f.degree := by
      have h := Polynomial.degree_sub_lt_left
        (p := Polynomial.X ^ f.natDegree) (q := f)
        (by rw [Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree hmon.ne_zero])
        (Polynomial.monic_X_pow f.natDegree).ne_zero
        (by rw [Polynomial.leadingCoeff_X_pow]; exact hmon.leadingCoeff.symm ▸ rfl)
      simpa [Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree hmon.ne_zero] using h
    have hdvd : f ∣ Polynomial.X ^ f.natDegree - (Polynomial.X ^ f.natDegree - f) := by
      rw [sub_sub_cancel]
    have hmod : (Polynomial.X ^ f.natDegree) %ₘ f = Polynomial.X ^ f.natDegree - f := by
      rw [Polynomial.modByMonic_eq_of_dvd_sub hmon hdvd,
        (Polynomial.modByMonic_eq_self_iff hmon).mpr hsub]
    rw [hmod, Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    simp [ne_of_lt hdeg]
  · -- `s = c s + x * t` for a suitable `t`
    intro s
    refine ⟨AdjoinRoot.mk f (Polynomial.divX (AdjoinRoot.modByMonicHom hmon s)), ?_⟩
    have hcs : (Polynomial.lcoeff R 0).comp (AdjoinRoot.modByMonicHom hmon) s
        = (AdjoinRoot.modByMonicHom hmon s).coeff 0 := by
      rw [LinearMap.comp_apply, Polynomial.lcoeff_apply]
    rw [hcs, AdjoinRoot.algebraMap_eq f, ← AdjoinRoot.mk_C, ← AdjoinRoot.mk_X, ← map_mul]
    rw [← map_add, add_comm, Polynomial.X_mul_divX_add, AdjoinRoot.mk_leftInverse hmon s]

end Work.FFResidual.Eisenstein
