import Submission.Work.DSM2p.LamOne

/-!
# The one-polynomial Česnavičius–Scholze cover

This file records the *single-polynomial* instance of the construction (lead design
`sources/dsmap/direct_summand_m2p_h2_design.md`, node R0, specialised to `ι = PUnit`,
`pol = fun _ => F`): the root ring is `Λ = Lam1 A p = A[T^{1/p^∞}]` (`LamOne.lean`), the
"`A_∞`" is `CSAlgOne A p ϖ F = Λ[F(T)/ϖ^m]`, and

* `CSIntegralClosureOne A p ϖ F = pIntClosure p (CSAlgOne A p ϖ F)` — `A'_F`;
* `CSCompletionOne A p ϖ F = AdicCompletion (span {p}) A'_F` — `B_F`;
* `TOneInClosure`, `rootElementOne`, `rootElementOneK` — the root `T` of `F` in `B_F` and its
  compatible system of `p`-power roots.

`area_M2pos1` only ever needs *one* monic polynomial `F` at a time, and the ČS §2.3 computation
that produces `(H2)` (faithful flatness of `B ⧸ pB`) is carried out for a single polynomial in
`Submission/Work/DSM2p/N8_*.lean` / `N5_*.lean`.  This file supplies the vocabulary for that
instance so that the nodes can be stated.

Everything here is definitional; the analysis is in the node files.
-/

open scoped Classical

namespace Work.DSM2p

universe u

/-- `A'_F = pIntClosure p (Λ[F(T)/ϖ^m])`, the `p`-integral closure of the one-polynomial
`A_∞` inside `Λ[1/ϖ]`. -/
noncomputable abbrev CSIntegralClosureOne (A : Type u) [CommRing A] (p : ℕ) (ϖ : A)
    (F : Polynomial A) : Subring (Lam1Loc A p ϖ) :=
  pIntClosure p (CSAlgOne A p ϖ F)

theorem CSAlgOne_le_CSIntegralClosureOne (A : Type u) [CommRing A] (p : ℕ) (ϖ : A)
    (F : Polynomial A) : CSAlgOne A p ϖ F ≤ CSIntegralClosureOne A p ϖ F :=
  le_pIntClosure p (CSAlgOne A p ϖ F)

theorem CSIntegralClosureOne_isPIntegrallyClosed (A : Type u) [CommRing A] (p : ℕ) (ϖ : A)
    (F : Polynomial A) : IsPIntegrallyClosedIn p (CSIntegralClosureOne A p ϖ F) :=
  pIntClosure_isPIntegrallyClosed p (CSAlgOne A p ϖ F)

/-- `B_F = AdicCompletion (p) A'_F`, the candidate one-polynomial cover. -/
noncomputable abbrev CSCompletionOne (A : Type u) [CommRing A] (p : ℕ) (ϖ : A)
    (F : Polynomial A) :=
  AdicCompletion (Ideal.span {(p : CSIntegralClosureOne A p ϖ F)}) (CSIntegralClosureOne A p ϖ F)

theorem CSCompletionOne_isAdicComplete (A : Type u) [CommRing A] (p : ℕ) (ϖ : A)
    (F : Polynomial A) :
    IsAdicComplete (Ideal.span {(p : CSIntegralClosureOne A p ϖ F)})
      (CSCompletionOne A p ϖ F) :=
  AdicCompletion.isAdicComplete (Submodule.fg_span_singleton (p : CSIntegralClosureOne A p ϖ F))

/-- The `A ⧸ (p)`-module structure on `B_F ⧸ pB_F` of the candidate cover (recorded explicitly
for the same reason as in `ConstructionPos.lean`). -/
noncomputable instance (A : Type u) [CommRing A] (p : ℕ) (ϖ : A) (F : Polynomial A) :
    Module (A ⧸ Ideal.span {(p : A)})
      (CSCompletionOne A p ϖ F ⧸
        (Ideal.span {(p : A)}).map (algebraMap A (CSCompletionOne A p ϖ F))) :=
  (inferInstance : Algebra _ _).toModule

/-! ## The root `T` of `F` in `B_F`, and its `p`-power roots -/

/-- `T = T^{1/p^0} ∈ Λ`, viewed as an element of `A'_F`. -/
noncomputable def TOneInClosure (A : Type u) [CommRing A] (p : ℕ) (ϖ : A) (F : Polynomial A) :
    CSIntegralClosureOne A p ϖ F :=
  ⟨algebraMap (Lam1 A p) (Lam1Loc A p ϖ) (T1 A p 0),
    CSAlgOne_le_CSIntegralClosureOne A p ϖ F
      (Subring.subset_closure (Set.mem_union_left _ ⟨T1 A p 0, rfl⟩))⟩

/-- `T^{1/p^k} ∈ Λ`, viewed as an element of `A'_F`. -/
noncomputable def TOneInClosureK (A : Type u) [CommRing A] (p : ℕ) (ϖ : A) (F : Polynomial A)
    (k : ℕ) : CSIntegralClosureOne A p ϖ F :=
  ⟨algebraMap (Lam1 A p) (Lam1Loc A p ϖ) (T1 A p k),
    CSAlgOne_le_CSIntegralClosureOne A p ϖ F
      (Subring.subset_closure (Set.mem_union_left _ ⟨T1 A p k, rfl⟩))⟩

theorem TOneInClosureK_pow (A : Type u) [CommRing A] (p : ℕ) (ϖ : A) (F : Polynomial A)
    (k : ℕ) : (TOneInClosureK A p ϖ F (k + 1)) ^ p = TOneInClosureK A p ϖ F k := by
  apply Subtype.ext
  simp only [TOneInClosureK, Subring.coe_pow]
  rw [← map_pow, T1_pow]

theorem TOneInClosureK_zero (A : Type u) [CommRing A] (p : ℕ) (ϖ : A) (F : Polynomial A) :
    TOneInClosureK A p ϖ F 0 = TOneInClosure A p ϖ F := rfl

/-- The image of `T^{1/p^k}` in `B_F`. -/
noncomputable def rootElementOneK (A : Type u) [CommRing A] (p : ℕ) (ϖ : A) (F : Polynomial A)
    (k : ℕ) : CSCompletionOne A p ϖ F :=
  algebraMap (CSIntegralClosureOne A p ϖ F) (CSCompletionOne A p ϖ F)
    (TOneInClosureK A p ϖ F k)

theorem rootElementOneK_pow (A : Type u) [CommRing A] (p : ℕ) (ϖ : A) (F : Polynomial A)
    (k : ℕ) : (rootElementOneK A p ϖ F (k + 1)) ^ p = rootElementOneK A p ϖ F k := by
  simp only [rootElementOneK]
  rw [← map_pow, TOneInClosureK_pow]

end Work.DSM2p
