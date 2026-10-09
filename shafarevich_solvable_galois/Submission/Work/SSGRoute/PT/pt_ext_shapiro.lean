import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PT.pt_pairing_ext
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node E2: Ext–Shapiro for coinduced modules, `Ext^r_G(M, CoInd_H^G N) ≅ Ext^r_H(res M, N)`

`DESIGN_EXT.md` §4 lists E2 (`ext_idele_shapiro`) as the Shapiro identification used by E9 and by
the reciprocity clause of `G1`: `𝕀_K` is (NK, `HassePrinciple.fiberIdelesRep_iso_coind`) the
coinduced product of the local unit groups `K_wˣ` over the places, so
`Ext^r_G(M, 𝕀_K) ≅ ∏'_w Ext^r_{D_w}(M, K_wˣ)` follows from Shapiro for coinduction at each place.

Mathlib has the **adjunction** `Rep.resFunctor φ ⊣ Rep.coindFunctor k φ` with its Hom-bijection
(`Rep.resCoindAdjunction`, `Rep.resCoindHomEquiv`), and restriction is exact
(`PreservesLimits`/`PreservesColimits` instances) and preserves projective objects for subgroup
inclusions (`(Rep.resFunctor S.subtype).PreservesProjectiveObjects`).  What Mathlib does **not** have
is the `Ext`-level Shapiro statement; that is the content of this file.

**Proof strategy (first-variable projective resolutions, i.e. dimension shifting).**  Mathlib's
`Ext (-) (-) n` is the `n`-th left-derived functor of `linearYoneda` in the *first* variable, so
* `Ext^r_G(P, ·) = 0` for `r ≥ 1` and `P` projective
  (`CategoryTheory.Abelian.isZero_Ext_succ_of_projective`);
* the first variable carries long exact sequences (`Ext.contravariant_sequence_exact₀/₁`).
Given a projective cover `0 → K → P → M → 0` in `Rep k G`, the restriction
`0 → res K → res P → res M → 0` is short exact (`Rep.shortExact_res`) with `res P` projective, and
the connecting maps of the two long exact sequences are isomorphisms by the vanishing above; the
base case is the adjunction
`Ext⁰_G(M, CoInd N) ≅ Hom_G(M, CoInd N) ≅ Hom_H(res M, N) ≅ Ext⁰_H(res M, N)`
(`Ext.homEquiv₀` twice plus `Rep.resCoindHomEquiv`).

**What is proved here.**
* `coindHomEquiv` — the adjunction bijection `Hom_S(res_S M, N) ≅ Hom_G(M, CoInd_S^G N)`.
* `extHomEquivZero` — `Ext⁰ ≅ Hom` (`Ext.homEquiv₀`).
* `extCoindShapiroZero` — **Ext–Shapiro in degree zero**.
* `ext_subsingleton_of_projective` — `Ext^r(P, Y) = 0` for `r ≥ 1`, `P` projective.
* `extClass_precomp_bijective` — **dimension shifting**: for `0 → X₁ → X₂ → X₃ → 0` short exact with
  `X₂` projective, the connecting map `Extⁿ(X₁, Y) → Extⁿ⁺¹(X₃, Y)` is a *bijection* for `n ≥ 1`
  (kernel = image of `Extⁿ(X₂, Y) = 0`, image = kernel of `Extⁿ⁺¹(X₂, Y) = 0`).

**What remains (the assembly), and how it goes.**  With `P := Projective.cover M ≅ M` (its kernel
sequence `0 → K → P → M → 0` is short exact with `P` projective):

* `r = 0`: `extCoindShapiroZero`, together with its **naturality in the first variable** (from the
  naturality of the adjunction `Rep.resCoindAdjunction` and of `Ext.homEquiv₀`);
* `r = 1`: the long exact sequences give
  `Ext¹(M, CoInd N) ≅ coker(Ext⁰(P, CoInd N) → Ext⁰(K, CoInd N))` and
  `Ext¹(res M, N) ≅ coker(Ext⁰(res P, N) → Ext⁰(res K, N))`, and the two cokernels agree by the
  naturality above;
* `r ≥ 2`: `Ext^r(M, CoInd N) ≅ Ext^{r-1}(K, CoInd N)` by `extClass_precomp_bijective`, and likewise
  for `res M`/`res K`, so one **recurses on `r`** with `K` in place of `M` (`res` preserves both
  projectives and exactness, so the same kernel sequence works on the `S`-side).  Equivalently: the
  composite `(δ')^{-1} ∘ e_{r-1}(K) ∘ δ` *defines* `e_r(M)` and is an isomorphism by construction.

The recursion terminates because `r` decreases; no independence-of-cover statement is needed, since
`e_r(M)` is only ever *used* at a fixed chosen cover.

**Note on scalar instances.**  `Coeff = ULift ℤ` carries two non-reducibly-equal semiring
structures (`ULift.semiring` versus `CommRing.toCommSemiring.toSemiring`), so the `≃ₗ[Coeff]` form of
Mathlib's adjunction bijection does not pin down at this use site.  We therefore record the
underlying equivalence (and use the additive structure where needed); this is the same class of
diamond that the E0b note records for `Ext` itself.
-/

open CategoryTheory

namespace SSGRoute.PTExt

-- The `Ext`-defeq checks in this file (Mathlib's `Rep.resCoindHomEquiv`, the `ext` of the class
-- formation) are expensive; raise the heartbeat budget for the whole file.
set_option maxHeartbeats 2000000



noncomputable section

variable {G : Type} [Group G] {S : Type} [Group S]

/-- **The adjunction bijection** `Hom_S(res_S M, N) ≅ Hom_G(M, CoInd_S^G N)` of
`Rep.resCoindAdjunction` (Mathlib `Rep.resCoindHomEquiv`), in the `PTExt` vocabulary.  This is the
first input of Ext–Shapiro and supplies its `r = 0` case. -/
def coindHomEquiv (ι : S →* G) (M : Rep.{0, 0, 0} Coeff G) (N : Rep.{0, 0, 0} Coeff S) :
    (Rep.res ι M ⟶ N) ≃ (M ⟶ Rep.coind ι N) :=
  (Rep.resCoindHomEquiv ι M N).toEquiv

/-- **`Ext⁰ ≅ Hom`** (Mathlib `Ext.homEquiv₀`): the degree-zero `Ext` class of a morphism *is* that
morphism. -/
def extHomEquivZero {A B : Rep.{0, 0, 0} Coeff G} :
    @Abelian.Ext.{0} (Rep.{0, 0, 0} Coeff G) _ _ (hasExt G) A B 0 ≃ (A ⟶ B) :=
  @Abelian.Ext.homEquiv₀ (Rep.{0, 0, 0} Coeff G) _ _ (hasExt G) A B

/-- **Ext–Shapiro in degree zero**: `Ext⁰_G(M, CoInd_S^G N) ≅ Ext⁰_S(res_S M, N)`, by combining
`Ext⁰ ≅ Hom` with the adjunction `res ⊣ coind`. -/
def extCoindShapiroZero (ι : S →* G) (M : Rep.{0, 0, 0} Coeff G) (N : Rep.{0, 0, 0} Coeff S) :
    Abelian.Ext.{0} M (Rep.coind ι N) 0 ≃ Abelian.Ext.{0} (Rep.res ι M) N 0 :=
  (extHomEquivZero (A := M) (B := Rep.coind ι N)).trans
    ((coindHomEquiv ι M N).symm.trans (extHomEquivZero (A := Rep.res ι M) (B := N)).symm)

/-! ## Naturality of the degree-zero comparison -/

section General

variable {C : Type} [Category C] [Abelian C] [HasExt C]

/-- `Ext⁰ ≅ Hom` inverts `mk₀`. -/
theorem homEquiv₀_mk₀ {X Y : C} (g : X ⟶ Y) :
    Abelian.Ext.homEquiv₀ (Abelian.Ext.mk₀ g) = g :=
  (Abelian.Ext.mk₀_bijective X Y).1 (by rw [Abelian.Ext.mk₀_homEquiv₀_apply])

/-- The inverse of `Ext⁰ ≅ Hom` is `mk₀`. -/
theorem homEquiv₀_symm_apply {X Y : C} (g : X ⟶ Y) :
    (Abelian.Ext.homEquiv₀ (X := X) (Y := Y)).symm g = Abelian.Ext.mk₀ g :=
  (Abelian.Ext.homEquiv₀ (X := X) (Y := Y)).injective
    (by rw [Equiv.apply_symm_apply, homEquiv₀_mk₀])

/-- **Naturality of `Ext⁰ ≅ Hom` in the first variable**: it is `mk₀` on morphisms. -/
theorem extHomEquivZero_naturality {X X' Y : C} (f : X' ⟶ X) (e : Abelian.Ext X Y 0) :
    Abelian.Ext.homEquiv₀ ((Abelian.Ext.mk₀ f).precomp Y (zero_add 0) e)
      = f ≫ Abelian.Ext.homEquiv₀ e := by
  apply (Abelian.Ext.mk₀_bijective X' Y).1
  rw [Abelian.Ext.mk₀_homEquiv₀_apply]
  rw [show (Abelian.Ext.mk₀ f).precomp Y (zero_add 0) e
      = (Abelian.Ext.mk₀ f).comp e (zero_add 0) from rfl]
  conv_lhs => rw [← Abelian.Ext.mk₀_homEquiv₀_apply (X := X) (Y := Y) e]
  rw [Abelian.Ext.mk₀_comp_mk₀]

end General

/-! ## Naturality of the degree-zero comparison: status

The `Ext⁰ ≅ Hom` half is proved above (`extHomEquivZero_naturality`, `homEquiv₀_mk₀`,
`homEquiv₀_symm_apply`); the adjunction half is `Adjunction.homEquiv_naturality_left_symm` of
`Rep.resCoindAdjunction`.  Composing the two to get the full square

`Ext⁰_G(M, CoInd N) → Ext⁰_G(M', CoInd N)` versus `Ext⁰_S(res M, N) → Ext⁰_S(res M', N)`

runs into a **universe-level instance mismatch on `Ext`**, the fourth face of the `HasExt` diamond
recorded in `pt_ext_cohomology.lean` (E0b) and in the header of this file: with the instance
argument of `Abelian.Ext` pinned explicitly (`@Abelian.Ext.{0} … (PTDefs.hasExt G) …`) the goal
still elaborates its `homEquiv₀` at value universe `1` (`homEquiv₀.{0, 0, 1}`), while the general
naturality lemma produces `homEquiv₀.{_, _, 0}`; the two do not unify.  Two ways out, both
mechanical:

* define a local abbreviation `extHT (A B : Rep Coeff G) (n : ℕ) : Type :=
  @Abelian.Ext.{0} (Rep.{0,0,0} Coeff G) _ _ (hasExt G) A B n` and state *all* of E2 through it
  (so the value universe is pinned at every occurrence), or
* develop E2 universe-generically over `[HasExt C]` (as all lemmas above already are) and instantiate
  once at the very end with the instance passed explicitly at the single top-level statement.

Note also that raising the priority of `PTDefs.hasExt` via `attribute [local instance]` *breaks*
elaboration here, because its synthesis (`hasExt_of_enoughProjectives`) exceeds the instance-search
heartbeat budget; explicit instance arguments, not priorities, are the fix.
-/

/-! ## Dimension shifting and the projective case -/

section General

variable {C : Type} [Category C] [Abelian C] [HasExt C]

/-- `Ext^r(P, Y)` is trivial for `r ≥ 1` and `P` projective (the `HasExt`-based form of
`CategoryTheory.Abelian.Ext.subsingleton_of_projective`). -/
theorem ext_subsingleton_of_projective {P Y : C} [Projective P] {r : ℕ} (hr : 1 ≤ r) :
    Subsingleton (Abelian.Ext P Y r) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  exact Abelian.Ext.subsingleton_of_projective P Y n

/-- **Dimension shifting.**  If `0 → S.X₁ → S.X₂ → S.X₃ → 0` is short exact and `S.X₂` is
projective, then the connecting map `Extⁿ(S.X₁, Y) → Extⁿ⁺¹(S.X₃, Y)` of the long exact sequence in
the first variable is a bijection for every `n ≥ 1`: its kernel is the image of `Extⁿ(S.X₂, Y) = 0`
and its image is the kernel of `Extⁿ⁺¹(S.X₂, Y) = 0`. -/
theorem extClass_precomp_bijective {S : ShortComplex C} (hS : S.ShortExact) [Projective S.X₂]
    (Y : C) {n : ℕ} (hn : 1 ≤ n) :
    Function.Bijective (hS.extClass.precomp Y (show 1 + n = n + 1 by omega)) := by
  have h₁ : Function.Exact (⇑((Abelian.Ext.mk₀ S.f).precomp Y (zero_add n) :
        Abelian.Ext S.X₂ Y n →+ Abelian.Ext S.X₁ Y n))
      (⇑(hS.extClass.precomp Y (show 1 + n = n + 1 by omega) :
        Abelian.Ext S.X₁ Y n →+ Abelian.Ext S.X₃ Y (n + 1))) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      (CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁' hS Y n (n + 1) (by omega))
  have h₂ : Function.Exact (⇑(hS.extClass.precomp Y (show 1 + n = n + 1 by omega) :
        Abelian.Ext S.X₁ Y n →+ Abelian.Ext S.X₃ Y (n + 1)))
      (⇑((Abelian.Ext.mk₀ S.g).precomp Y (zero_add (n + 1)) :
        Abelian.Ext S.X₃ Y (n + 1) →+ Abelian.Ext S.X₂ Y (n + 1))) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      (CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃' hS Y n (n + 1) (by omega))
  haveI hsub1 : Subsingleton (Abelian.Ext S.X₂ Y n) := ext_subsingleton_of_projective hn
  haveI hsub2 : Subsingleton (Abelian.Ext S.X₂ Y (n + 1)) :=
    ext_subsingleton_of_projective (by omega)
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have h : (hS.extClass.precomp Y (show 1 + n = n + 1 by omega)) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hmem : x - y ∈ Set.range ((Abelian.Ext.mk₀ S.f).precomp Y (zero_add n) :
        Abelian.Ext S.X₂ Y n →+ Abelian.Ext S.X₁ Y n) := (h₁ (x - y)).mp h
    obtain ⟨w, hw⟩ := hmem
    have hz : x - y = 0 := by
      have hw' : (0 : Abelian.Ext S.X₁ Y n) = x - y := by
        rw [← hw, show w = 0 from Subsingleton.elim w 0, map_zero]
      exact hw'.symm
    exact sub_eq_zero.mp hz
  · intro y
    have hmem : y ∈ Set.range (hS.extClass.precomp Y (show 1 + n = n + 1 by omega) :
        Abelian.Ext S.X₁ Y n →+ Abelian.Ext S.X₃ Y (n + 1)) :=
      (h₂ y).mp (Subsingleton.elim _ _)
    obtain ⟨x, hx⟩ := hmem
    exact ⟨x, hx⟩

end General

end

end SSGRoute.PTExt
