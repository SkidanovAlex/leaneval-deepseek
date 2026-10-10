import Mathlib

set_option linter.unusedVariables false -- v435-speed

/-!
# `Work.MotAS.satGraphComapGen`

The membership form of the graph-saturation: for `A = K[X₁,X₂]`, the `rename Fin.succ`-image of
`h ∈ A` lies in the `D`-saturation of the graph ideal `J = (E, D·X₀ + R) ⊆ K[X₀,X₁,X₂]` iff
`E ∣ h`.

The proof models the quotient `K[X₀,X₁,X₂]/J` by evaluating `X₀ ↦ −R/D` in the fraction field of
`A/(E)`:

* `σ : A →+* Frac(A/(E))` has kernel `(E)` (using `Irreducible E ⟹ Prime E`);
* `Ψ : K[X₀,X₁,X₂] →+* Frac(A/(E))` is `eval₂ σ (−σ R · (σ D)⁻¹) ∘ finSuccEquiv`;
* `Ψ` kills the two generators of `J` and `Ψ(D) = σ D ≠ 0` (this is exactly `hD`), so every
  element of the `D`-saturation of `J` is killed by `Ψ` (the target is a field);
* on `A` we have `Ψ ∘ rename Fin.succ = σ`, whence the result.
-/

set_option linter.style.haveILetI false

namespace Work.MotAS

open MvPolynomial

theorem satGraphComapGen {K : Type*} [Field K]
    (E D R : MvPolynomial (Fin 2) K) (hE : Irreducible E) (hD : ¬ E ∣ D)
    (h : MvPolynomial (Fin 2) K) :
    (MvPolynomial.rename Fin.succ h ∈
        Ideal.span {F : MvPolynomial (Fin 3) K |
          ∃ N : ℕ, (MvPolynomial.rename Fin.succ D) ^ N * F ∈
            Ideal.span {MvPolynomial.rename Fin.succ E,
              MvPolynomial.rename Fin.succ D * MvPolynomial.X 0
                + MvPolynomial.rename Fin.succ R}}) ↔ E ∣ h := by
  classical
  have hEprime : Prime E := hE.prime
  haveI hIprime : (Ideal.span {E} : Ideal (MvPolynomial (Fin 2) K)).IsPrime :=
    (Ideal.span_singleton_prime hE.ne_zero).mpr hEprime
  haveI hCdom : IsDomain (MvPolynomial (Fin 2) K ⧸ Ideal.span {E}) :=
    Ideal.Quotient.isDomain (Ideal.span {E})
  let Df := FractionRing (MvPolynomial (Fin 2) K ⧸ Ideal.span {E})
  haveI hDfield : Field Df := FractionRing.field _
  -- the quotient map `A →+* Frac(A/(E))`, whose kernel is `(E)`
  let σ : MvPolynomial (Fin 2) K →+* Df :=
    (algebraMap (MvPolynomial (Fin 2) K ⧸ Ideal.span {E}) Df).comp
      (Ideal.Quotient.mk (Ideal.span {E}))
  have hkerσ : ∀ x : MvPolynomial (Fin 2) K, σ x = 0 ↔ x ∈ Ideal.span {E} := by
    intro x
    change (algebraMap (MvPolynomial (Fin 2) K ⧸ Ideal.span {E}) Df)
        (Ideal.Quotient.mk (Ideal.span {E}) x) = 0 ↔ x ∈ Ideal.span {E}
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  have hσD : σ D ≠ 0 := fun h0 => hD (Ideal.mem_span_singleton.mp ((hkerσ D).mp h0))
  let u : Df := (σ D)⁻¹
  have hu : σ D * u = 1 := mul_inv_cancel₀ hσD
  -- the value assigned to `X₀`, namely `−R/D`
  let x : Df := -(σ R) * u
  let Φ : Polynomial (MvPolynomial (Fin 2) K) →+* Df := Polynomial.eval₂RingHom σ x
  let e : MvPolynomial (Fin 3) K ≃ₐ[K] Polynomial (MvPolynomial (Fin 2) K) :=
    MvPolynomial.finSuccEquiv K 2
  let Ψ : MvPolynomial (Fin 3) K →+* Df := Φ.comp (e : MvPolynomial (Fin 3) K →+* _)
  -- `finSuccEquiv` sends `rename Fin.succ p` to `C p` and `X 0` to `X`
  have he_rename : ∀ p : MvPolynomial (Fin 2) K,
      (e : MvPolynomial (Fin 3) K →+* Polynomial (MvPolynomial (Fin 2) K))
        (MvPolynomial.rename Fin.succ p) = Polynomial.C p := by
    have hcomp : ((e : MvPolynomial (Fin 3) K →+* Polynomial (MvPolynomial (Fin 2) K)).comp
        (MvPolynomial.rename Fin.succ).toRingHom) = Polynomial.C := by
      apply MvPolynomial.ringHom_ext
      · intro r
        show e (MvPolynomial.rename Fin.succ (MvPolynomial.C r)) = Polynomial.C (MvPolynomial.C r)
        rw [MvPolynomial.rename_C, ← MvPolynomial.algebraMap_eq (R := K) (σ := Fin 3),
          AlgEquiv.commutes e r, ← MvPolynomial.algebraMap_eq (R := K) (σ := Fin 2)]
        exact (AlgHom.commutes (Polynomial.CAlgHom (R := K) (A := MvPolynomial (Fin 2) K)) r).symm
      · intro i
        show e (MvPolynomial.rename Fin.succ (MvPolynomial.X i)) = Polynomial.C (MvPolynomial.X i)
        rw [MvPolynomial.rename_X, MvPolynomial.finSuccEquiv_X_succ]
    intro p
    exact RingHom.congr_fun hcomp p
  have heX0 : (e : MvPolynomial (Fin 3) K →+* Polynomial (MvPolynomial (Fin 2) K))
      (MvPolynomial.X 0 : MvPolynomial (Fin 3) K) = Polynomial.X := by
    simpa using MvPolynomial.finSuccEquiv_X_zero (R := K) (n := 2)
  have hΦC : ∀ p : MvPolynomial (Fin 2) K, Φ (Polynomial.C p) = σ p := by
    intro p; exact Polynomial.eval₂_C σ x
  have hΦX : Φ Polynomial.X = x := Polynomial.eval₂_X σ x
  have hΨ_rename : ∀ p : MvPolynomial (Fin 2) K, Ψ (MvPolynomial.rename Fin.succ p) = σ p := by
    intro p
    change Φ (e (MvPolynomial.rename Fin.succ p)) = σ p
    rw [show e (MvPolynomial.rename Fin.succ p) = Polynomial.C p from he_rename p, hΦC p]
  have hΨX0 : Ψ (MvPolynomial.X 0 : MvPolynomial (Fin 3) K) = x := by
    change Φ (e (MvPolynomial.X 0)) = x
    rw [show e (MvPolynomial.X 0) = Polynomial.X from heX0, hΦX]
  -- `Ψ` kills the two generators of the graph ideal
  have hgen1 : Ψ (MvPolynomial.rename Fin.succ E) = 0 := by
    rw [hΨ_rename E]
    exact (hkerσ E).mpr (Ideal.subset_span (Set.mem_singleton E))
  have hgen2 : Ψ (MvPolynomial.rename Fin.succ D * (MvPolynomial.X 0 : MvPolynomial (Fin 3) K)
      + MvPolynomial.rename Fin.succ R) = 0 := by
    rw [map_add, map_mul, hΨ_rename D, hΨX0, hΨ_rename R]
    change σ D * (-(σ R) * u) + σ R = 0
    have h1 : σ D * (-(σ R) * u) = -(σ R) := by
      rw [show σ D * (-(σ R) * u) = -(σ R) * (σ D * u) by ring, hu, mul_one]
    rw [h1, neg_add_cancel]
  have hJ_le : Ideal.span {MvPolynomial.rename Fin.succ E,
      MvPolynomial.rename Fin.succ D * MvPolynomial.X 0 + MvPolynomial.rename Fin.succ R}
      ≤ RingHom.ker Ψ := by
    rw [Ideal.span_le]
    intro y hy
    rw [Set.mem_insert_iff] at hy
    rcases hy with hy | hy
    · subst hy; exact RingHom.mem_ker.mpr hgen1
    · rw [Set.mem_singleton_iff] at hy; subst hy; exact RingHom.mem_ker.mpr hgen2
  -- every element of the saturation is killed by `Ψ` (`Ψ D = σ D ≠ 0` and the target is a field)
  have hS_ker : ∀ F : MvPolynomial (Fin 3) K,
      (∃ N : ℕ, (MvPolynomial.rename Fin.succ D) ^ N * F ∈
        Ideal.span {MvPolynomial.rename Fin.succ E,
          MvPolynomial.rename Fin.succ D * MvPolynomial.X 0
            + MvPolynomial.rename Fin.succ R}) → Ψ F = 0 := by
    rintro F ⟨N, hN⟩
    have h1 : Ψ ((MvPolynomial.rename Fin.succ D) ^ N * F) = 0 :=
      RingHom.mem_ker.mp (hJ_le hN)
    rw [map_mul, map_pow, hΨ_rename D] at h1
    exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hσD)
  have hspan_le : Ideal.span {F : MvPolynomial (Fin 3) K |
        ∃ N : ℕ, (MvPolynomial.rename Fin.succ D) ^ N * F ∈
          Ideal.span {MvPolynomial.rename Fin.succ E,
            MvPolynomial.rename Fin.succ D * MvPolynomial.X 0
              + MvPolynomial.rename Fin.succ R}} ≤ RingHom.ker Ψ := by
    rw [Ideal.span_le]
    intro F hF
    exact RingHom.mem_ker.mpr (hS_ker F hF)
  constructor
  · intro hmem
    have h0 : Ψ (MvPolynomial.rename Fin.succ h) = 0 := RingHom.mem_ker.mp (hspan_le hmem)
    rw [hΨ_rename h] at h0
    exact Ideal.mem_span_singleton.mp ((hkerσ h).mp h0)
  · intro hdvd
    obtain ⟨q, rfl⟩ := hdvd
    refine Ideal.subset_span ⟨0, ?_⟩
    rw [pow_zero, one_mul, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))

end Work.MotAS
