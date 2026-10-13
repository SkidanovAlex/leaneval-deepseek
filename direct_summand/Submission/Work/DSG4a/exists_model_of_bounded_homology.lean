import Mathlib
import Submission.Work.DSG4a.exists_model_concentrated
import Submission.Work.DSG4a.boundedAbove_free_model_of_shortExact
import Submission.Work.DSEQ0.exists_lift_of_quasiIso

namespace Work.DSG4a

open CategoryTheory AlgebraicGeometry Limits
universe u

set_option linter.style.haveILetI false

/-- A complex object of `ModuleCat A` which is zero is finitely generated as an `A`-module. -/
private lemma module_finite_of_isZero {A : Type u} [CommRing A] (M : ModuleCat.{u} A)
    (h : IsZero M) : Module.Finite A M := by
  haveI : Subsingleton M := ModuleCat.subsingleton_of_isZero h
  exact Module.finite_def.mpr ⟨∅, by simp [Subsingleton.elim (⊤ : Submodule A M) ⊥]⟩

/-- The induction statement behind `Work.DSG4a.exists_model_of_bounded_homology`: the bound
`N` on the cohomology is a natural number, and the construction is by induction on it. -/
private theorem exists_model_of_bounded_homology_aux {A : Type u} [CommRing A]
    [IsNoetherianRing A] (N : ℕ) :
    ∀ (C : CochainComplex (ModuleCat.{u} A) ℤ), C.IsStrictlyGE (0 : ℤ) →
      (∀ i, Module.Finite A (C.homology i)) →
      (∀ i, (N : ℤ) < i → IsZero (C.homology i)) →
      ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ) (q : P ⟶ C),
        (∀ j, Module.Finite A (P.X j)) ∧ (∀ j, Module.Free A (P.X j)) ∧
        P.IsStrictlyLE (N : ℤ) ∧ QuasiIso q := by
  induction N with
  | zero =>
    -- The cohomology is concentrated in degree `0`, so `C` is a model of itself.
    intro C hCge hfin hzero
    haveI : C.IsStrictlyGE (0 : ℤ) := hCge
    have hcon : ∀ i, i ≠ 0 → IsZero (C.homology i) := by
      intro i hi
      rcases lt_trichotomy i 0 with h | h | h
      · exact CochainComplex.isZero_of_isGE C 0 i h
      · exact absurd h hi
      · exact hzero i (by simpa using h)
    obtain ⟨F, hFfin, hFfree, hFle, q, hq⟩ :=
      exists_model_concentrated (A := A) C 0 hcon (hfin 0)
    exact ⟨F, q, hFfin, hFfree, hFle, hq⟩
  | succ m ih =>
    intro C hCge hfin hzero
    haveI : C.IsStrictlyGE (0 : ℤ) := hCge
    -- **(1)** The lower truncation `C.truncLE m` satisfies the induction hypothesis.
    have hfin₁ : ∀ i, Module.Finite A ((C.truncLE (m : ℤ)).homology i) := by
      intro i
      by_cases hi : i ≤ (m : ℤ)
      · haveI := hfin i
        haveI : IsIso (HomologicalComplex.homologyMap (C.ιTruncLE (m : ℤ)) i) :=
          (quasiIsoAt_iff_isIso_homologyMap _ _).mp
            (CochainComplex.quasiIsoAt_ιTruncLE C (m : ℤ) i hi)
        exact Module.Finite.equiv
          (asIso (HomologicalComplex.homologyMap (C.ιTruncLE (m : ℤ)) i)).symm.toLinearEquiv
      · exact module_finite_of_isZero _
          (CochainComplex.isZero_of_isLE (C.truncLE (m : ℤ)) (m : ℤ) i (by omega))
    have hzero₁ : ∀ i, (m : ℤ) < i → IsZero ((C.truncLE (m : ℤ)).homology i) :=
      fun i hi => CochainComplex.isZero_of_isLE (C.truncLE (m : ℤ)) (m : ℤ) i hi
    obtain ⟨Q, q, hQfin, hQfree, hQle, hq⟩ :=
      ih (C.truncLE (m : ℤ)) inferInstance hfin₁ hzero₁
    -- **(2)** The top part `D = C.truncGE (m+1)` has cohomology concentrated in degree `m+1`.
    have hcon : ∀ i, i ≠ (m : ℤ) + 1 →
        IsZero ((C.truncGE ((m : ℤ) + 1)).homology i) := by
      intro i hi
      rcases lt_trichotomy i ((m : ℤ) + 1) with h | h | h
      · exact CochainComplex.isZero_of_isGE (C.truncGE ((m : ℤ) + 1)) ((m : ℤ) + 1) i h
      · exact absurd h hi
      · haveI : IsIso (HomologicalComplex.homologyMap (C.πTruncGE ((m : ℤ) + 1)) i) :=
          (quasiIsoAt_iff_isIso_homologyMap _ _).mp
            (CochainComplex.quasiIsoAt_πTruncGE C ((m : ℤ) + 1) i (by omega))
        exact IsZero.of_iso (hzero i (by omega))
          (asIso (HomologicalComplex.homologyMap (C.πTruncGE ((m : ℤ) + 1)) i)).symm
    have hfinD : Module.Finite A ((C.truncGE ((m : ℤ) + 1)).homology ((m : ℤ) + 1)) := by
      haveI := hfin ((m : ℤ) + 1)
      haveI : IsIso (HomologicalComplex.homologyMap (C.πTruncGE ((m : ℤ) + 1))
          ((m : ℤ) + 1)) :=
        (quasiIsoAt_iff_isIso_homologyMap _ _).mp
          (CochainComplex.quasiIsoAt_πTruncGE C ((m : ℤ) + 1) ((m : ℤ) + 1) le_rfl)
      exact Module.Finite.equiv
        (asIso (HomologicalComplex.homologyMap (C.πTruncGE ((m : ℤ) + 1)) ((m : ℤ) + 1))).toLinearEquiv
    obtain ⟨F₀, hF₀fin, hF₀free, hF₀le, f₀, hf₀⟩ :=
      exists_model_concentrated (A := A) (C.truncGE ((m : ℤ) + 1)) ((m : ℤ) + 1) hcon hfinD
    -- **(3)** Transport the model of `D` to the third term `X₃` of the truncation sequence
    -- by lifting along the localisation to the derived category.
    letI : HasDerivedCategory (ModuleCat.{u} A) := HasDerivedCategory.standard _
    haveI : QuasiIso f₀ := hf₀
    haveI : IsIso (DerivedCategory.Q.map f₀) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} A) f₀).mpr inferInstance
    haveI hδ : QuasiIso (C.shortComplexTruncLEX₃ToTruncGE (m : ℤ) ((m : ℤ) + 1) rfl :
        (C.shortComplexTruncLE (m : ℤ)).X₃ ⟶ C.truncGE ((m : ℤ) + 1)) := inferInstance
    haveI : IsIso (DerivedCategory.Q.map
        (C.shortComplexTruncLEX₃ToTruncGE (m : ℤ) ((m : ℤ) + 1) rfl)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} A) _).mpr inferInstance
    haveI hF₀proj : CochainComplex.IsKProjective F₀ := by
      haveI : F₀.IsStrictlyLE ((m : ℤ) + 1) := hF₀le
      haveI : ∀ n : ℤ, Projective (F₀.X n) := fun n => by
        haveI := hF₀free n
        infer_instance
      exact CochainComplex.isKProjective_of_projective F₀ ((m : ℤ) + 1)
    obtain ⟨g, hg⟩ := Work.DSEQ0.Q_map_surjective_of_isKProjective (A := A) (K := F₀)
      ((C.shortComplexTruncLE (m : ℤ)).X₃)
      (asIso (DerivedCategory.Q.map f₀) ≪≫
        (asIso (DerivedCategory.Q.map
          (C.shortComplexTruncLEX₃ToTruncGE (m : ℤ) ((m : ℤ) + 1) rfl))).symm).hom
    have hgqi : QuasiIso g :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} A) g).mp (by rw [hg]; infer_instance)
    -- **(4)** The short exact sequence `0 → C.truncLE m → C → X₃ → 0` glues the two models.
    obtain ⟨P, q₂, hPfin, hPfree, hPle, hq₂⟩ :=
      Work.DSG4a.boundedAbove_free_model_of_shortExact (C.shortComplexTruncLE (m : ℤ))
        (C.shortComplexTruncLE_shortExact (m : ℤ))
        Q q hq hQfin hQfree hQle F₀ g hgqi hF₀fin hF₀free hF₀le
    refine ⟨P, q₂, hPfin, hPfree, ?_, hq₂⟩
    have hmax : (max (m : ℤ) ((m : ℤ) + 1)) = ((m + 1 : ℕ) : ℤ) := by
      rw [max_eq_right (by omega)]
      push_cast
      ring
    rw [← hmax]
    exact hPle

/-- **The model driver of area `G4a`.**  A cochain complex `C` of `A`-modules over a Noetherian
ring `A`, concentrated in degrees `≥ 0`, with finitely generated cohomology vanishing above `N`,
is quasi-isomorphic to a complex `P` of finitely generated free `A`-modules vanishing in degrees
`> N`.  (One-sided boundedness suffices: a bounded-above complex with projective terms is
K-projective, and the bound `> N` is what the construction gives.  A *two-sided* bound would be
false in general — it would force finite projective dimension — which is why
`Work.DSEQ0.exists_bounded_free_model`, whose hypotheses require two-sided bounded resolutions of
the cohomology, is not usable here; its one-sided companion
`Work.DSG4a.boundedAbove_free_model_of_shortExact` is.)

Recipe: induction on `N`.
* `N = 0`: apply `Work.DSG4a.exists_model_concentrated` at `n = 0` to `C` itself (its cohomology
  is concentrated in degree `0` and `C` is strictly `≥ 0`).
* step `N → N+1`: let `S := C.shortComplexTruncLE N` — the short exact sequence
  `0 → C.truncLE N → C → X₃ → 0` (`C.shortComplexTruncLE_shortExact N`), whose third term is
  quasi-isomorphic to `C.truncGE (N+1)` via `C.shortComplexTruncLEX₃ToTruncGE N (N+1) rfl`.
  The first term `C.truncLE N` satisfies the induction hypothesis (finitely generated cohomology,
  vanishing above `N`), giving `Q ⟶ C.truncLE N` with `Q.IsStrictlyLE N`.  The third term `X₃`
  is quasi-isomorphic to `D := C.truncGE (N+1)`, which is strictly `≥ N+1` with cohomology
  concentrated in degree `N+1` (degrees `> N+1`: use `CochainComplex.quasiIsoAt_πTruncGE`; degree
  `N+1`: finitely generated); `Work.DSG4a.exists_model_concentrated` applies to `D` and gives
  `F₀ ⟶ D` with `F₀.IsStrictlyLE (N+1)` and finitely generated free terms — hence K-projective —
  and then a quasi-isomorphism `g : F₀ ⟶ X₃` is obtained by lifting
  `Q(F₀) ≅ Q(D) ≅ Q(X₃)` along the localisation (`Work.DSEQ0.Q_map_surjective_of_isKProjective`
  with `DerivedCategory.isIso_Q_map_iff_quasiIso`).  Finally
  `Work.DSG4a.boundedAbove_free_model_of_shortExact S _ Q q hq F₀ g hg` produces the model of
  `S.X₂ = C`, bounded by `max N (N+1) = N+1`. -/
theorem exists_model_of_bounded_homology {A : Type u} [CommRing A] [IsNoetherianRing A]
    (C : CochainComplex (ModuleCat.{u} A) ℤ) (N : ℕ) [C.IsStrictlyGE 0]
    (hfin : ∀ i, Module.Finite A (C.homology i))
    (hzero : ∀ i, (N : ℤ) < i → IsZero (C.homology i)) :
    ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ) (q : P ⟶ C),
      (∀ j, Module.Finite A (P.X j)) ∧ (∀ j, Module.Free A (P.X j)) ∧
      P.IsStrictlyLE (N : ℤ) ∧ QuasiIso q :=
  exists_model_of_bounded_homology_aux (A := A) N C inferInstance hfin hzero

end Work.DSG4a
