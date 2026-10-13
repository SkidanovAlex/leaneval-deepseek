import Mathlib
import Submission.Work.DSM2p.LamOne
import Submission.Work.DSM2p.N1_defs

/-!
# `Work.DSM2p.N1_quot_algEquiv_rootClosure`

The root-system ring `Λ = Lam1 A p = A[T^{1/p^n} | n ∈ ℕ]` (with `(T^{1/p^{n+1}})^p = T^{1/p^n}`,
the class of the variable `X_{⋆,n}` being `T1 A p n`) is the filtered colimit, along the
Frobenius `X ↦ X ^ p`, of the free `A`-algebra `A[X]`.  Consequently base change along
`A → A ⧸ I` is again a root-system ring:

* `(Λ_A ⧸ I·Λ_A) ≃+* Λ_{A ⧸ I}`,

compatibly with the variables `T^{1/p^n}` and with the `A`-algebra structure.  This is the
lemma `N1_quot_algEquiv_rootClosure`.

The proof is elementary and does not need the colimit description: the canonical map
`Φ : Λ_A → Λ_{A ⧸ I}` is induced by the coefficient reduction `MvPolynomial.map (A → A ⧸ I)`,
which carries the relation ideal `(X_{n+1}^p - X_n)` into the relation ideal over `A ⧸ I`.
In the reverse direction we evaluate the variables `X_n` of `Λ_{A ⧸ I}` at the classes of
`T1 A p n` and reduce the coefficients along `A → A ⧸ I`, obtaining
`Ψ : Λ_{A ⧸ I} → Λ_A ⧸ I·Λ_A`.  Both maps are ring homomorphisms killing the relevant
ideals, and they are mutually inverse because they are inverse on the algebra generators
`T^{1/p^n}` and on the coefficients — checked by `MvPolynomial`-extensionality.  The
resulting ring equivalence is the one required.
-/

set_option synthInstance.maxHeartbeats 400000

open scoped Classical

namespace Work.DSM2p

universe u

/-! ## The coefficient reduction `MvPolynomial (PUnit × ℕ) A → MvPolynomial (PUnit × ℕ) (A ⧸ I)` -/

/-- Reduction of coefficients of the polynomial ring on the variables `(⋆, n)`.
It sends `X_q` to `X_q` and a constant `a` to the class of `a` in `A ⧸ I`. -/
noncomputable def polyMap (A : Type u) [CommRing A] (I : Ideal A) :
    MvPolynomial (PUnit × ℕ) A →+* MvPolynomial (PUnit × ℕ) (A ⧸ I) :=
  MvPolynomial.map (Ideal.Quotient.mk I)

/-- The reduction of coefficients carries the defining relations of `Λ_A` into those of
`Λ_{A ⧸ I}`. -/
theorem rootClosureIdeal_map_le (A : Type u) [CommRing A] (p : ℕ) (I : Ideal A) :
    Ideal.map (polyMap A I) (rootClosureIdeal A p PUnit) ≤ rootClosureIdeal (A ⧸ I) p PUnit := by
  unfold rootClosureIdeal
  rw [Ideal.map_span]
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨y, ⟨q, rfl⟩, rfl⟩
  have h : polyMap A I (MvPolynomial.X (q.1, q.2 + 1) ^ p - MvPolynomial.X q) =
      MvPolynomial.X (q.1, q.2 + 1) ^ p - MvPolynomial.X q := by
    simp only [polyMap, map_sub, map_pow, MvPolynomial.map_X]
  rw [h]
  exact Ideal.subset_span ⟨q, rfl⟩

/-! ## The induced map `Φ : Λ_A → Λ_{A ⧸ I}` -/

/-- Base change `Λ_A → Λ_{A ⧸ I}` of the root-system ring along `A → A ⧸ I`. -/
noncomputable def lamMap (A : Type u) [CommRing A] (p : ℕ) (I : Ideal A) :
    Lam1 A p →+* Lam1 (A ⧸ I) p :=
  Ideal.Quotient.lift (rootClosureIdeal A p PUnit)
    ((Ideal.Quotient.mk (rootClosureIdeal (A ⧸ I) p PUnit)).comp (polyMap A I))
    (fun _ ha => Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_comap.mp ((Ideal.map_le_iff_le_comap.mp (rootClosureIdeal_map_le A p I)) ha)))

theorem lamMap_mk (A : Type u) [CommRing A] (p : ℕ) (I : Ideal A)
    (x : MvPolynomial (PUnit × ℕ) A) :
    lamMap A p I (Ideal.Quotient.mk (rootClosureIdeal A p PUnit) x) =
      Ideal.Quotient.mk (rootClosureIdeal (A ⧸ I) p PUnit) (polyMap A I x) := by
  simp only [lamMap, Ideal.Quotient.lift_mk, RingHom.comp_apply]

/-- `Φ` is compatible with the `A`-algebra structures. -/
theorem lamMap_algebraMap (A : Type u) [CommRing A] (p : ℕ) (I : Ideal A) (a : A) :
    lamMap A p I (algebraMap A (Lam1 A p) a) =
      algebraMap (A ⧸ I) (Lam1 (A ⧸ I) p) (Ideal.Quotient.mk I a) := by
  have h1 : algebraMap A (Lam1 A p) a =
      Ideal.Quotient.mk (rootClosureIdeal A p PUnit) (MvPolynomial.C a) := rfl
  have h2 : algebraMap (A ⧸ I) (Lam1 (A ⧸ I) p) (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (rootClosureIdeal (A ⧸ I) p PUnit)
        (MvPolynomial.C (Ideal.Quotient.mk I a)) := rfl
  rw [h1, h2, lamMap_mk]
  simp only [polyMap, MvPolynomial.map_C]

/-- `Φ` sends the variable `T^{1/p^n}` to the variable `T^{1/p^n}`. -/
theorem lamMap_T1 (A : Type u) [CommRing A] (p : ℕ) (I : Ideal A) (n : ℕ) :
    lamMap A p I (T1 A p n) = T1 (A ⧸ I) p n := by
  have h1 : T1 A p n =
      Ideal.Quotient.mk (rootClosureIdeal A p PUnit) (MvPolynomial.X (PUnit.unit, n)) := rfl
  have h2 : T1 (A ⧸ I) p n =
      Ideal.Quotient.mk (rootClosureIdeal (A ⧸ I) p PUnit) (MvPolynomial.X (PUnit.unit, n)) :=
    rfl
  rw [h1, h2, lamMap_mk]
  simp only [polyMap, MvPolynomial.map_X]

/-- `Φ` is `A`-linear. -/
theorem lamMap_comp_algebraMap (A : Type u) [CommRing A] (p : ℕ) (I : Ideal A) :
    (lamMap A p I).comp (algebraMap A (Lam1 A p)) =
      (algebraMap (A ⧸ I) (Lam1 (A ⧸ I) p)).comp (Ideal.Quotient.mk I) := by
  ext a
  rw [RingHom.comp_apply, RingHom.comp_apply, lamMap_algebraMap]

/-! ## `Φ` descends to `Λ_A ⧸ I·Λ_A` -/

/-- The image of `I` in `Λ_A` lies in the kernel of `Φ`. -/
theorem map_le_ker_lamMap (A : Type u) [CommRing A] (p : ℕ) (I : Ideal A) :
    Ideal.map (algebraMap A (Lam1 A p)) I ≤ RingHom.ker (lamMap A p I) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, RingHom.mem_ker, lamMap_algebraMap]
  have h : Ideal.Quotient.mk I a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
  rw [h, map_zero]

/-- The base-change map `Λ_A ⧸ I·Λ_A → Λ_{A ⧸ I}`. -/
noncomputable def quotMap (A : Type u) [CommRing A] (p : ℕ) (I : Ideal A) :
    (Lam1 A p ⧸ Ideal.map (algebraMap A (Lam1 A p)) I) →+* Lam1 (A ⧸ I) p :=
  Ideal.Quotient.lift (Ideal.map (algebraMap A (Lam1 A p)) I) (lamMap A p I)
    (fun _ ha => RingHom.mem_ker.mp (map_le_ker_lamMap A p I ha))

theorem quotMap_mk (A : Type u) [CommRing A] (p : ℕ) (I : Ideal A) (x : Lam1 A p) :
    quotMap A p I (Ideal.Quotient.mk (Ideal.map (algebraMap A (Lam1 A p)) I) x) =
      lamMap A p I x := by
  simp only [quotMap, Ideal.Quotient.lift_mk]

/-! ## The reverse map `Λ_{A ⧸ I} → Λ_A ⧸ I·Λ_A` -/

/-- The `A ⧸ I`-algebra structure on `Λ_A ⧸ I·Λ_A` transported along `A → A ⧸ I`. -/
noncomputable def coeffMap (A : Type u) [CommRing A] (p : ℕ) (I : Ideal A) :
    (A ⧸ I) →+* (Lam1 A p ⧸ Ideal.map (algebraMap A (Lam1 A p)) I) :=
  Ideal.Quotient.lift I
    ((Ideal.Quotient.mk (Ideal.map (algebraMap A (Lam1 A p)) I)).comp (algebraMap A (Lam1 A p)))
    (fun _ ha => Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_map_of_mem (algebraMap A (Lam1 A p)) ha))

theorem coeffMap_mk (A : Type u) [CommRing A] (p : ℕ) (I : Ideal A) (a : A) :
    coeffMap A p I (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (Ideal.map (algebraMap A (Lam1 A p)) I) (algebraMap A (Lam1 A p) a) := by
  simp only [coeffMap, Ideal.Quotient.lift_mk, RingHom.comp_apply]

/-- The variables `X_n` of `Λ_{A ⧸ I}`, evaluated at the classes of `T1 A p n`. -/
noncomputable def varMap (A : Type u) [CommRing A] (p : ℕ) (I : Ideal A) :
    PUnit × ℕ → (Lam1 A p ⧸ Ideal.map (algebraMap A (Lam1 A p)) I) :=
  fun q => Ideal.Quotient.mk (Ideal.map (algebraMap A (Lam1 A p)) I) (T1 A p q.2)

/-- The map `MvPolynomial (PUnit × ℕ) (A ⧸ I) → Λ_A ⧸ I·Λ_A` sending `X_n ↦ T^{1/p^n}`. -/
noncomputable def evalMap (A : Type u) [CommRing A] (p : ℕ) (I : Ideal A) :
    MvPolynomial (PUnit × ℕ) (A ⧸ I) →+*
      (Lam1 A p ⧸ Ideal.map (algebraMap A (Lam1 A p)) I) :=
  MvPolynomial.eval₂Hom (coeffMap A p I) (varMap A p I)

theorem evalMap_C (A : Type u) [CommRing A] (p : ℕ) (I : Ideal A) (b : A ⧸ I) :
    evalMap A p I (MvPolynomial.C b) = coeffMap A p I b :=
  MvPolynomial.eval₂Hom_C _ _ _

theorem evalMap_X (A : Type u) [CommRing A] (p : ℕ) (I : Ideal A) (q : PUnit × ℕ) :
    evalMap A p I (MvPolynomial.X q) = varMap A p I q :=
  MvPolynomial.eval₂Hom_X' _ _ _

/-- Extensionality for ring homomorphisms out of `MvPolynomial (PUnit × ℕ) R`, using only the
variables `X (⋆, n)`. -/
theorem mvPoly_ext {R : Type u} [CommSemiring R] {T : Type*} [Semiring T]
    (f g : MvPolynomial (PUnit × ℕ) R →+* T)
    (hC : ∀ a : R, f (MvPolynomial.C a) = g (MvPolynomial.C a))
    (hX : ∀ n : ℕ, f (MvPolynomial.X (PUnit.unit, n)) = g (MvPolynomial.X (PUnit.unit, n))) :
    f = g := by
  refine MvPolynomial.ringHom_ext hC (fun q => ?_)
  have hq : q = (PUnit.unit, q.2) := by ext <;> simp
  rw [hq]
  exact hX q.2

/-- The defining relations of `Λ_{A ⧸ I}` are killed by `evalMap`. -/
theorem evalMap_rel (A : Type u) [CommRing A] (p : ℕ) (I : Ideal A) (q : PUnit × ℕ) :
    evalMap A p I (MvPolynomial.X (q.1, q.2 + 1) ^ p - MvPolynomial.X q) = 0 := by
  rw [map_sub, map_pow, evalMap_X, evalMap_X]
  rw [show varMap A p I (q.1, q.2 + 1) =
        Ideal.Quotient.mk (Ideal.map (algebraMap A (Lam1 A p)) I) (T1 A p (q.2 + 1)) from rfl,
      show varMap A p I q =
        Ideal.Quotient.mk (Ideal.map (algebraMap A (Lam1 A p)) I) (T1 A p q.2) from rfl,
      ← map_pow, T1_pow A p q.2, sub_self]

theorem ker_evalMap (A : Type u) [CommRing A] (p : ℕ) (I : Ideal A) :
    rootClosureIdeal (A ⧸ I) p PUnit ≤ RingHom.ker (evalMap A p I) := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨q, rfl⟩
  exact RingHom.mem_ker.mpr (evalMap_rel A p I q)

/-- The reverse map `Λ_{A ⧸ I} → Λ_A ⧸ I·Λ_A`. -/
noncomputable def quotEvalMap (A : Type u) [CommRing A] (p : ℕ) (I : Ideal A) :
    Lam1 (A ⧸ I) p →+* (Lam1 A p ⧸ Ideal.map (algebraMap A (Lam1 A p)) I) :=
  Ideal.Quotient.lift (rootClosureIdeal (A ⧸ I) p PUnit) (evalMap A p I)
    (fun _ ha => RingHom.mem_ker.mp (ker_evalMap A p I ha))

theorem quotEvalMap_mk (A : Type u) [CommRing A] (p : ℕ) (I : Ideal A)
    (y : MvPolynomial (PUnit × ℕ) (A ⧸ I)) :
    quotEvalMap A p I (Ideal.Quotient.mk (rootClosureIdeal (A ⧸ I) p PUnit) y) =
      evalMap A p I y := by
  simp only [quotEvalMap, Ideal.Quotient.lift_mk]

/-- `quotMap` is compatible with the coefficient maps: it intertwines the `A ⧸ I`-algebra
structure on `Λ_A ⧸ I·Λ_A` with the standard one on `Λ_{A ⧸ I}`. -/
theorem quotMap_comp_coeffMap (A : Type u) [CommRing A] (p : ℕ) (I : Ideal A) :
    (quotMap A p I).comp (coeffMap A p I) = algebraMap (A ⧸ I) (Lam1 (A ⧸ I) p) := by
  apply Ideal.Quotient.ringHom_ext
  ext a
  rw [RingHom.comp_apply, RingHom.comp_apply, coeffMap_mk, quotMap_mk, lamMap_algebraMap]
  rfl

/-! ## `quotMap` and `quotEvalMap` are mutually inverse -/

theorem quotEvalMap_comp_quotMap (A : Type u) [CommRing A] (p : ℕ) (I : Ideal A) :
    (quotEvalMap A p I).comp (quotMap A p I) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply Ideal.Quotient.ringHom_ext
  apply mvPoly_ext
  · intro a
    simp only [RingHom.comp_apply, RingHom.id_apply]
    change quotEvalMap A p I (quotMap A p I (Ideal.Quotient.mk
        (Ideal.map (algebraMap A (Lam1 A p)) I) (algebraMap A (Lam1 A p) a))) =
      Ideal.Quotient.mk (Ideal.map (algebraMap A (Lam1 A p)) I) (algebraMap A (Lam1 A p) a)
    rw [quotMap_mk, lamMap_algebraMap]
    change quotEvalMap A p I (Ideal.Quotient.mk (rootClosureIdeal (A ⧸ I) p PUnit)
        (MvPolynomial.C (Ideal.Quotient.mk I a))) =
      Ideal.Quotient.mk (Ideal.map (algebraMap A (Lam1 A p)) I) (algebraMap A (Lam1 A p) a)
    rw [quotEvalMap_mk, evalMap_C, coeffMap_mk]
  · intro n
    simp only [RingHom.comp_apply, RingHom.id_apply]
    change quotEvalMap A p I (quotMap A p I (Ideal.Quotient.mk
        (Ideal.map (algebraMap A (Lam1 A p)) I) (T1 A p n))) =
      Ideal.Quotient.mk (Ideal.map (algebraMap A (Lam1 A p)) I) (T1 A p n)
    rw [quotMap_mk, lamMap_T1]
    change quotEvalMap A p I (Ideal.Quotient.mk (rootClosureIdeal (A ⧸ I) p PUnit)
        (MvPolynomial.X (PUnit.unit, n))) =
      Ideal.Quotient.mk (Ideal.map (algebraMap A (Lam1 A p)) I) (T1 A p n)
    rw [quotEvalMap_mk, evalMap_X]
    rfl

theorem quotMap_comp_quotEvalMap (A : Type u) [CommRing A] (p : ℕ) (I : Ideal A) :
    (quotMap A p I).comp (quotEvalMap A p I) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply mvPoly_ext
  · intro b
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [show quotEvalMap A p I (Ideal.Quotient.mk (rootClosureIdeal (A ⧸ I) p PUnit)
          (MvPolynomial.C b)) = coeffMap A p I b from by
      rw [quotEvalMap_mk, evalMap_C]]
    have h := DFunLike.congr_fun (quotMap_comp_coeffMap A p I) b
    simp only [RingHom.comp_apply] at h
    rw [h]
    rfl
  · intro n
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [show quotEvalMap A p I (Ideal.Quotient.mk (rootClosureIdeal (A ⧸ I) p PUnit)
          (MvPolynomial.X (PUnit.unit, n))) =
        Ideal.Quotient.mk (Ideal.map (algebraMap A (Lam1 A p)) I) (T1 A p n) from by
      rw [quotEvalMap_mk, evalMap_X]
      rfl]
    rw [quotMap_mk, lamMap_T1]
    rfl

/-! ## The main result -/

theorem N1_quot_algEquiv_rootClosure (A : Type*) [CommRing A] (p : ℕ) (I : Ideal A) :
    ∃ e : (Lam1 A p ⧸ I.map (algebraMap A (Lam1 A p))) ≃+* Lam1 (A ⧸ I) p,
      ∀ (n : ℕ) (g : Polynomial A),
        e (Ideal.Quotient.mk (I.map (algebraMap A (Lam1 A p)))
            (Polynomial.aeval (T1 A p n) g)) =
          Polynomial.aeval (T1 (A ⧸ I) p n) (g.map (Ideal.Quotient.mk I)) := by
  have hgf : ∀ z, quotEvalMap A p I (quotMap A p I z) = z :=
    fun z => DFunLike.congr_fun (quotEvalMap_comp_quotMap A p I) z
  have hfg : ∀ z, quotMap A p I (quotEvalMap A p I z) = z :=
    fun z => DFunLike.congr_fun (quotMap_comp_quotEvalMap A p I) z
  let e : (Lam1 A p ⧸ Ideal.map (algebraMap A (Lam1 A p)) I) ≃+* Lam1 (A ⧸ I) p :=
    { toFun := quotMap A p I
      invFun := quotEvalMap A p I
      left_inv := hgf
      right_inv := hfg
      map_mul' := map_mul (quotMap A p I)
      map_add' := map_add (quotMap A p I) }
  refine ⟨e, ?_⟩
  intro n g
  change quotMap A p I (Ideal.Quotient.mk (Ideal.map (algebraMap A (Lam1 A p)) I)
      (Polynomial.aeval (T1 A p n) g)) =
    Polynomial.aeval (T1 (A ⧸ I) p n) (g.map (Ideal.Quotient.mk I))
  rw [quotMap_mk]
  rw [show lamMap A p I (Polynomial.aeval (T1 A p n) g) =
      Polynomial.eval₂ ((lamMap A p I).comp (algebraMap A (Lam1 A p)))
        ((lamMap A p I) (T1 A p n)) g from
    Polynomial.hom_eval₂ g (algebraMap A (Lam1 A p)) (lamMap A p I) (T1 A p n)]
  rw [lamMap_comp_algebraMap, lamMap_T1]
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]

end Work.DSM2p
