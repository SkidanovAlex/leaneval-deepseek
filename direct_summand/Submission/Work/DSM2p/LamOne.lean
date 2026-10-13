import Submission.Work.DSM2p.Basic
import Submission.Work.DSM2p.RootClosure

/-!
# The one-variable root ring `Λ = A[T^{1/p^∞}]` and its localization

The single-polynomial form of the construction (lead design
`sources/dsmap/direct_summand_m2p_h2_design.md`, node R0) uses

* `Lam1 A p = rootClosure A p PUnit` — the root-system ring in one variable;
* `T1 A p n` — the class of `X_{(⋆,n)}`, i.e. `T^{1/p^n}`;
* `Lam1Loc A p ϖ = Λ[1/ϖ]`; `frac A p ϖ a m = a / ϖ^m`;
* `CSAlgOne A p ϖ F = Λ[F(T)/ϖ^m | m]`, the one-polynomial `A_∞`.

The definitions are the ones of the lead design file, restated here so that the design's nodes
`N1`, `N2b`, `N5c`, `N5d`, `N8a`, … can be stated and dispatched inside `Submission/Work/DSM2p`.
-/

open scoped Classical

namespace Work.DSM2p

universe u

/-- `Λ = A[T^{1/p^∞}]`, the root-system ring in one variable. -/
abbrev Lam1 (A : Type u) [CommRing A] (p : ℕ) : Type u := rootClosure A p PUnit.{u + 1}

/-- `T^{1/p^n} ∈ Λ`. -/
noncomputable def T1 (A : Type u) [CommRing A] (p : ℕ) (n : ℕ) : Lam1 A p :=
  Ideal.Quotient.mk (rootClosureIdeal A p PUnit.{u + 1}) (MvPolynomial.X (PUnit.unit, n))

/-- `T^{1/p^{n+1}}` is a `p`-th root of `T^{1/p^n}`. -/
theorem T1_pow (A : Type u) [CommRing A] (p : ℕ) (n : ℕ) :
    T1 A p (n + 1) ^ p = T1 A p n :=
  rootClosure.X_pow A p PUnit.{u + 1} PUnit.unit n

/-- `Λ[1/ϖ]`. -/
abbrev Lam1Loc (A : Type u) [CommRing A] (p : ℕ) (ϖ : A) : Type u :=
  Localization.Away (algebraMap A (Lam1 A p) ϖ)

/-- `a / ϖ^m ∈ Λ[1/ϖ]`. -/
noncomputable def frac (A : Type u) [CommRing A] (p : ℕ) (ϖ : A) (a : Lam1 A p) (m : ℕ) :
    Lam1Loc A p ϖ :=
  algebraMap (Lam1 A p) (Lam1Loc A p ϖ) a *
    IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) ϖ) ^ m

/-- The one-polynomial `A_∞ = Λ[F(T)/ϖ^m | m] ⊆ Λ[1/ϖ]`. -/
noncomputable def CSAlgOne (A : Type u) [CommRing A] (p : ℕ) (ϖ : A) (F : Polynomial A) :
    Subring (Lam1Loc A p ϖ) :=
  Subring.closure (Set.range (algebraMap (Lam1 A p) (Lam1Loc A p ϖ)) ∪
    Set.range (fun m : ℕ => frac A p ϖ (Polynomial.aeval (T1 A p 0) F) m))

/-- `T_F` in `Λ[1/ϖ]`: the variable `T^{1/p^0} = T` itself. -/
theorem aeval_T1_zero_mem_CSAlgOne (A : Type u) [CommRing A] (p : ℕ) (ϖ : A)
    (F : Polynomial A) :
    algebraMap (Lam1 A p) (Lam1Loc A p ϖ) (Polynomial.aeval (T1 A p 0) F) ∈ CSAlgOne A p ϖ F :=
  Subring.subset_closure (Set.mem_union_left _ ⟨_, rfl⟩)

/-- `F(T)/ϖ^m ∈ A_∞` for every `m`. -/
theorem frac_aeval_T1_zero_mem_CSAlgOne (A : Type u) [CommRing A] (p : ℕ) (ϖ : A)
    (F : Polynomial A) (m : ℕ) :
    frac A p ϖ (Polynomial.aeval (T1 A p 0) F) m ∈ CSAlgOne A p ϖ F :=
  Subring.subset_closure (Set.mem_union_right _ ⟨m, rfl⟩)

theorem aeval_T1_zero_mem_CSAlgOne' (A : Type u) [CommRing A] (p : ℕ) (ϖ : A)
    (F : Polynomial A) :
    frac A p ϖ (Polynomial.aeval (T1 A p 0) F) 0 ∈ CSAlgOne A p ϖ F :=
  frac_aeval_T1_zero_mem_CSAlgOne A p ϖ F 0

/-- The structure map `A → Λ → Λ[1/ϖ]`, whose image lies in `CSAlgOne` and hence in its
`p`-integral closure. -/
noncomputable def AAlgHomLamOne (A : Type u) [CommRing A] (p : ℕ) (ϖ : A) :
    A →+* Lam1Loc A p ϖ :=
  (algebraMap (Lam1 A p) (Lam1Loc A p ϖ)).comp (algebraMap A (Lam1 A p))

theorem AAlgHomLamOne_mem_CSAlgOne (A : Type u) [CommRing A] (p : ℕ) (ϖ : A)
    (F : Polynomial A) (a : A) :
    AAlgHomLamOne A p ϖ a ∈ CSAlgOne A p ϖ F :=
  Subring.subset_closure (Set.mem_union_left _ ⟨algebraMap A (Lam1 A p) a, rfl⟩)

/-- `A'_F = pIntClosure p (CSAlgOne A p ϖ F)` is an `A`-algebra, so that `Module.Flat A A'_F`
can be stated. -/
noncomputable instance (A : Type u) [CommRing A] (p : ℕ) (ϖ : A) (F : Polynomial A) :
    Algebra A ↥(pIntClosure p (CSAlgOne A p ϖ F)) :=
  (RingHom.codRestrict (AAlgHomLamOne A p ϖ) _
    (fun a => le_pIntClosure p _
      (AAlgHomLamOne_mem_CSAlgOne A p ϖ F a))).toAlgebra

end Work.DSM2p
