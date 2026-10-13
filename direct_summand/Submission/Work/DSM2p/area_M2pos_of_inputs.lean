import Mathlib
import Submission.Work.DSM2p.ConstructionPos
import Submission.Work.DSM2p.rootElementPos_aeval
import Submission.Work.DSM2p.CSIntegralClosurePos_isSMulRegular
import Submission.Work.DSM2p.adicCompletion_isSMulRegular

/-!
# DSM2p — assembly of the `PerfectoidData` structure on the completion `B`

## The requested lemma is mis-stated (universe defect)

The requested declaration

```
theorem area_M2pos_of_inputs (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A] … :
    ∃ (B : Type*) (_ : CommRing B) (_ : Algebra A B) (Q : DSMap.PerfectoidData p B), …
```

has `A : Type*` and, in the conclusion, `∃ B : Type*` **in independent universes**.  `Type*`
auto-binds a fresh universe parameter *eagerly*; `#print` of the verbatim statement gives

```
theorem area_M2pos_of_inputs.{u_1, u_2} : ∀ (p : ℕ) [Fact p.Prime] (A : Type u_1) [CommRing A] …,
  … → ∃ (B : Type u_2) …, …
```

The witness suggested by the mathematics — and by both referees of the request — is
`B = CSCompletionPos A p (P.ϖ 0)`, and *every* object named by the hypotheses (`h1`, `h2`, `h3`,
`hsmu`) lives in `Type u_1`.  Yet the proof obligation is `B : Type u_2` with `u_1`, `u_2` two
rigid, unrelated parameters, so the natural proof is rejected at elaboration:

```
Application type mismatch: The argument
  A
has type
  Type u_1
of sort `Type (u_1 + 1)` but is expected to have type
  Type u_2
of sort `Type (u_2 + 1)` in the application
  @CSCompletionPos A
```

No universe-lifting mechanism repairs this: `ULift.{v,u} α` lives in `Type (max v u)` and
`max u_2 u_1` is not definitionally `u_2` (there is no hypothesis `u_1 ≤ u_2`), so a `Type u_2`
witness cannot be manufactured from data in `Type u_1`.  The simpler test

```
theorem t (A : Type*) : ∃ (B : Type*), True := ⟨A, trivial⟩
```

fails for the same reason.  The defect is *only* the universes: the intended statement, with `A`
and `B` in a common universe `u`, is true and is proved below as
`area_M2pos_of_inputs_sameUniverse`.

The same universe defect in a sibling request (`Work.DSROOTS.exists_roots`) was reported and
accepted; see `Submission/Work/DSROOTS/exists_roots.lean`, "History".

## The intended (provable) form

`area_M2pos_of_inputs_sameUniverse` below is the requested statement with the universe *pinned*
(`A : Type u`, `∃ B : Type u`), which is exactly the shape used by the deliverable
`DSMap.Mix2Fix.area_M2pos` (`A : Type a`, `∃ B : Type a`).  It is proved in full: given the two
hard inputs `(H1)` Frobenius surjectivity modulo `ϖ ^ p` (`h1`) and `(H2)` faithful flatness of
`B ⧸ pB` over `A ⧸ pA` (`h2`), plus Frobenius injectivity (`h3`) and `p`-torsion-freeness
(`hsmu`), the ring `B = CSCompletionPos A p (P.ϖ 0)` carries a `PerfectoidData` structure with
pseudo-uniformizer the image of `P.ϖ`, is faithfully flat mod `p`, and every positive-degree
monic polynomial acquires a compatible system of `p`-power roots.

The `PerfectoidData` fields are assembled from:

* `root` — the compatibility of `P.ϖ` transported along `algebraMap A B`;
* `unit` — `ϖ ^ p = p · u`, `u` a unit of `A`, transported along `algebraMap A B`;
* `torsionFree` — `hsmu`;
* `complete` — `CSCompletionPos_isAdicComplete`, transported along the identification of the
  ideals `(p) B = (p) A' · B` (`IsAdicComplete.map_algebraMap_iff`);
* `frobSurj`, `frobInj` — `h1`, `h3`, using that `(algebraMap (P.ϖ 0 ^ p)) = (p)` in `B`
  because `P.ϖ 0 ^ p = p · u` with `u` a unit.

The roots clause uses the `p`-power root system `T_F^{1/p^k}` of the construction
(`rootVarPosK`, `rootElementPosK`), whose compatibility is `rootClosure.X_pow`.
-/

open scoped Classical

namespace Work.DSM2p

universe u

/-! ## The `p`-power root system of `T_F` inside the positive-degree construction -/

/-- The `k`-th `p`-power root `T_F^{1/p^k}` of the variable `T_F` in `Λ = RootAlgPos A p`. -/
noncomputable def rootVarPosK (A : Type u) [CommRing A] (p : ℕ) (F : MonicPolysPos A)
    (k : ℕ) : RootAlgPos A p :=
  Ideal.Quotient.mk (rootClosureIdeal A p (MonicPolysPos A)) (MvPolynomial.X (F, k))

/-- `T_F^{1/p^k}` inside `Λ[1/ϖ]`. -/
noncomputable def rootVarLocPosK (A : Type u) [CommRing A] (p : ℕ) (ϖ : A)
    (F : MonicPolysPos A) (k : ℕ) : RootAlgLocPos A p ϖ :=
  algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ) (rootVarPosK A p F k)

theorem rootVarLocPosK_mem_CSAlgPos (A : Type u) [CommRing A] (p : ℕ) (ϖ : A)
    (F : MonicPolysPos A) (k : ℕ) : rootVarLocPosK A p ϖ F k ∈ CSAlgPos A p ϖ :=
  Subring.subset_closure (Set.mem_union_left _ ⟨rootVarPosK A p F k, rfl⟩)

/-- `T_F^{1/p^k}` inside `A' = CSIntegralClosurePos A p ϖ`. -/
noncomputable def rootVarInClosurePosK (A : Type u) [CommRing A] (p : ℕ) (ϖ : A)
    (F : MonicPolysPos A) (k : ℕ) : CSIntegralClosurePos A p ϖ :=
  ⟨rootVarLocPosK A p ϖ F k,
    CSAlgPos_le_CSIntegralClosurePos A p ϖ (rootVarLocPosK_mem_CSAlgPos A p ϖ F k)⟩

/-- `T_F^{1/p^k}` inside `B = CSCompletionPos A p ϖ`. -/
noncomputable def rootElementPosK (A : Type u) [CommRing A] (p : ℕ) (ϖ : A)
    (F : MonicPolysPos A) (k : ℕ) : CSCompletionPos A p ϖ :=
  algebraMap (CSIntegralClosurePos A p ϖ) (CSCompletionPos A p ϖ) (rootVarInClosurePosK A p ϖ F k)

/-- At `k = 0` this is the root `T_F` of `F` already used in `rootElementPos_aeval`. -/
theorem rootElementPosK_zero (A : Type u) [CommRing A] (p : ℕ) (ϖ : A) (F : MonicPolysPos A) :
    rootElementPosK A p ϖ F 0 = rootElementPos A p ϖ F := rfl

/-- The defining relation of the root system, in `Λ[1/ϖ]`. -/
theorem rootVarLocPosK_pow (A : Type u) [CommRing A] (p : ℕ) (ϖ : A) (F : MonicPolysPos A)
    (k : ℕ) : (rootVarLocPosK A p ϖ F (k + 1)) ^ p = rootVarLocPosK A p ϖ F k := by
  simp only [rootVarLocPosK, rootVarPosK]
  rw [← map_pow, rootClosure.X_pow]

/-- The defining relation of the root system, in `A'`. -/
theorem rootVarInClosurePosK_pow (A : Type u) [CommRing A] (p : ℕ) (ϖ : A)
    (F : MonicPolysPos A) (k : ℕ) :
    (rootVarInClosurePosK A p ϖ F (k + 1)) ^ p = rootVarInClosurePosK A p ϖ F k := by
  apply Subtype.ext
  rw [Subring.coe_pow,
    show ((rootVarInClosurePosK A p ϖ F (k + 1) : CSIntegralClosurePos A p ϖ) :
        RootAlgLocPos A p ϖ) = rootVarLocPosK A p ϖ F (k + 1) from rfl,
    show ((rootVarInClosurePosK A p ϖ F k : CSIntegralClosurePos A p ϖ) :
        RootAlgLocPos A p ϖ) = rootVarLocPosK A p ϖ F k from rfl,
    rootVarLocPosK_pow]

/-- The defining relation of the root system, in `B`. -/
theorem rootElementPosK_pow (A : Type u) [CommRing A] (p : ℕ) (ϖ : A) (F : MonicPolysPos A)
    (k : ℕ) : (rootElementPosK A p ϖ F (k + 1)) ^ p = rootElementPosK A p ϖ F k := by
  simp only [rootElementPosK]
  rw [← map_pow, rootVarInClosurePosK_pow]

/-! ## The intended statement, with the universe pinned -/

/-- **Assembly of the `PerfectoidData` structure on `B = CSCompletionPos A p (P.ϖ 0)`** — the
requested lemma `area_M2pos_of_inputs` with the universe `u` of `A` pinned for `B` as well
(this is the shape needed by `DSMap.Mix2Fix.area_M2pos`).

`h1` is `(H1)` Frobenius surjectivity modulo `ϖ ^ p`, `h2` is `(H2)` faithful flatness of `B ⧸ pB`
over `A ⧸ pA`, `h3` is Frobenius injectivity, `hsmu` is `p`-torsion-freeness. -/
theorem area_M2pos_of_inputs_sameUniverse (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A]
    (P : DSMap.PerfectoidData p A)
    (h1 : ∀ x : CSCompletionPos A p (P.ϖ 0), ∃ y : CSCompletionPos A p (P.ϖ 0),
      x - y ^ p ∈ Ideal.span {algebraMap A (CSCompletionPos A p (P.ϖ 0)) (P.ϖ 0 ^ p)})
    (h2 : Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A)})
      (CSCompletionPos A p (P.ϖ 0) ⧸
        (Ideal.span {(p : A)}).map (algebraMap A (CSCompletionPos A p (P.ϖ 0)))))
    (h3 : ∀ x : CSCompletionPos A p (P.ϖ 0),
      x ^ p ∈ Ideal.span {algebraMap A (CSCompletionPos A p (P.ϖ 0)) (P.ϖ 0 ^ p)} →
      x ∈ Ideal.span {algebraMap A (CSCompletionPos A p (P.ϖ 0)) (P.ϖ 0)})
    (hsmu : IsSMulRegular (CSCompletionPos A p (P.ϖ 0)) (p : CSCompletionPos A p (P.ϖ 0))) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (Q : DSMap.PerfectoidData p B),
      (∀ k, Q.ϖ k = algebraMap A B (P.ϖ k)) ∧
      Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A)})
        (B ⧸ (Ideal.span {(p : A)}).map (algebraMap A B)) ∧
      ∀ F : Polynomial A, F.Monic → 0 < F.natDegree →
        ∃ r : ℕ → B, Polynomial.aeval (r 0) F = 0 ∧ ∀ k, r (k + 1) ^ p = r k := by
  -- In `B`, the ideal generated by the image of `P.ϖ 0 ^ p` is the ideal generated by `p`,
  -- because `P.ϖ 0 ^ p = p · u` with `u` a unit of `A`.
  have hspan : Ideal.span {algebraMap A (CSCompletionPos A p (P.ϖ 0)) (P.ϖ 0 ^ p)}
      = Ideal.span {(p : CSCompletionPos A p (P.ϖ 0))} := by
    obtain ⟨v, hv⟩ := P.unit
    have hkey : algebraMap A (CSCompletionPos A p (P.ϖ 0)) (P.ϖ 0 ^ p)
        = (p : CSCompletionPos A p (P.ϖ 0))
          * algebraMap A (CSCompletionPos A p (P.ϖ 0)) (↑v : A) := by
      rw [hv, map_mul, map_natCast]
    rw [hkey, Ideal.span_singleton_mul_right_unit (IsUnit.map _ v.isUnit)]
  -- `B` is `p`-adically complete: this is `p`-adic completeness of `A'`, transported along
  -- `A' → B` under the identification `(p) B = (p) A' · B`.
  have hcomplete : IsAdicComplete (Ideal.span {(p : CSCompletionPos A p (P.ϖ 0))})
      (CSCompletionPos A p (P.ϖ 0)) := by
    have hmap : (Ideal.span {(p : CSIntegralClosurePos A p (P.ϖ 0))}).map
        (algebraMap (CSIntegralClosurePos A p (P.ϖ 0)) (CSCompletionPos A p (P.ϖ 0)))
        = Ideal.span {(p : CSCompletionPos A p (P.ϖ 0))} := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
    rw [← hmap]
    exact (IsAdicComplete.map_algebraMap_iff
        (Ideal.span {(p : CSIntegralClosurePos A p (P.ϖ 0))})
        (CSCompletionPos A p (P.ϖ 0))).mpr (CSCompletionPos_isAdicComplete A p (P.ϖ 0))
  let Q : DSMap.PerfectoidData p (CSCompletionPos A p (P.ϖ 0)) :=
    { ϖ := fun k => algebraMap A (CSCompletionPos A p (P.ϖ 0)) (P.ϖ k)
      root := fun k => by
        show (algebraMap A (CSCompletionPos A p (P.ϖ 0)) (P.ϖ (k + 1))) ^ p
          = algebraMap A (CSCompletionPos A p (P.ϖ 0)) (P.ϖ k)
        rw [← map_pow, P.root k]
      unit := by
        obtain ⟨v, hv⟩ := P.unit
        refine ⟨Units.map (algebraMap A (CSCompletionPos A p (P.ϖ 0))) v, ?_⟩
        show (algebraMap A (CSCompletionPos A p (P.ϖ 0)) (P.ϖ 0)) ^ p
          = (p : CSCompletionPos A p (P.ϖ 0))
            * algebraMap A (CSCompletionPos A p (P.ϖ 0)) (↑v : A)
        rw [← map_pow, hv, map_mul, map_natCast]
      torsionFree := hsmu
      complete := hcomplete
      frobSurj := fun x => by
        obtain ⟨y, hy⟩ := h1 x
        exact ⟨y, by rwa [hspan] at hy⟩
      frobInj := fun y hy => h3 y (by rwa [← hspan] at hy) }
  refine ⟨CSCompletionPos A p (P.ϖ 0), inferInstance, inferInstance, Q, ?_, ?_, ?_⟩
  · intro k; rfl
  · exact h2
  · intro F hmon hdeg
    refine ⟨fun k => rootElementPosK A p (P.ϖ 0) ⟨F, hmon, hdeg⟩ k, ?_, ?_⟩
    · show Polynomial.aeval (rootElementPosK A p (P.ϖ 0) ⟨F, hmon, hdeg⟩ 0) F = 0
      exact rootElementPos_aeval A p (P.ϖ 0) P.unit ⟨F, hmon, hdeg⟩
    · intro k
      exact rootElementPosK_pow A p (P.ϖ 0) ⟨F, hmon, hdeg⟩ k

/-! ## The requested statement (kept verbatim; not provable as written)

The declaration below is the request **verbatim**.  Its `B` lives in a universe independent of
`A`'s (see the module docstring), so it is unprovable as written; the provable form with the
universe pinned is `area_M2pos_of_inputs_sameUniverse` above.  The `sorry` records the
unprovable request. -/

theorem area_M2pos_of_inputs (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A]
    (P : DSMap.PerfectoidData p A)
    (h1 : ∀ x : CSCompletionPos A p (P.ϖ 0), ∃ y : CSCompletionPos A p (P.ϖ 0),
      x - y ^ p ∈ Ideal.span {algebraMap A (CSCompletionPos A p (P.ϖ 0)) (P.ϖ 0 ^ p)})
    (h2 : Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A)})
      (CSCompletionPos A p (P.ϖ 0) ⧸
        (Ideal.span {(p : A)}).map (algebraMap A (CSCompletionPos A p (P.ϖ 0)))))
    (h3 : ∀ x : CSCompletionPos A p (P.ϖ 0),
      x ^ p ∈ Ideal.span {algebraMap A (CSCompletionPos A p (P.ϖ 0)) (P.ϖ 0 ^ p)} →
      x ∈ Ideal.span {algebraMap A (CSCompletionPos A p (P.ϖ 0)) (P.ϖ 0)})
    (hsmu : IsSMulRegular (CSCompletionPos A p (P.ϖ 0)) (p : CSCompletionPos A p (P.ϖ 0))) :
    ∃ (B : Type*) (_ : CommRing B) (_ : Algebra A B) (Q : DSMap.PerfectoidData p B),
      (∀ k, Q.ϖ k = algebraMap A B (P.ϖ k)) ∧
      Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A)})
        (B ⧸ (Ideal.span {(p : A)}).map (algebraMap A B)) ∧
      ∀ F : Polynomial A, F.Monic → 0 < F.natDegree →
        ∃ r : ℕ → B, Polynomial.aeval (r 0) F = 0 ∧ ∀ k, r (k + 1) ^ p = r k := by
  sorry

end Work.DSM2p
