import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Normality

open KaehlerDifferential Algebra

/-- Let `K → P → A` be a tower of commutative rings and suppose `A` is formally smooth over
`K`.  If the natural map `A ⊗[P] Ω[P⁄K] → Ω[A⁄K]` is bijective, then `A` is formally smooth
over `P`.

Proof (Jacobi–Zariski).  `Algebra.FormallySmooth` has two fields: `Module.Projective A Ω[A⁄P]`
and `Subsingleton (H1Cotangent P A)`.
* Surjectivity of `mapBaseChange` gives `LinearMap.ker (KaehlerDifferential.map K P A A) = ⊤`
  by `KaehlerDifferential.exact_mapBaseChange_map`, while `KaehlerDifferential.map K P A A` is
  itself surjective (`KaehlerDifferential.map_surjective`, or its range contains the spanning set
  `KaehlerDifferential.D P A _ = map K P A A (D K A _)` by `KaehlerDifferential.map_D` and
  `KaehlerDifferential.span_range_derivation`); hence `Subsingleton Ω[A⁄P]`, and a subsingleton
  module is projective.
* Injectivity of `mapBaseChange` gives `LinearMap.ker (mapBaseChange K P A) = ⊥`, so
  `range (Algebra.H1Cotangent.δ K P A) = ⊥` by
  `Algebra.H1Cotangent.exact_δ_mapBaseChange`, i.e. `δ = 0`; and `δ` is injective because
  `Subsingleton (H1Cotangent K A)` (from `Algebra.FormallySmooth K A`) makes its kernel
  `range (Algebra.H1Cotangent.map K P A A)` trivial by `Algebra.H1Cotangent.exact_map_δ`.
  Hence `Subsingleton (H1Cotangent P A)`. -/
theorem formallySmooth_of_bijective_mapBaseChange {K P A : Type*} [CommRing K] [CommRing P]
    [Algebra K P] [CommRing A] [Algebra K A] [Algebra P A] [IsScalarTower K P A]
    [Algebra.FormallySmooth K A]
    (h : Function.Bijective (KaehlerDifferential.mapBaseChange K P A)) :
    Algebra.FormallySmooth P A := by
  -- Step 1: the surjectivity of `mapBaseChange` forces `Ω[A⁄P] = 0`.
  have hmap : KaehlerDifferential.map K P A A = 0 := by
    rw [← LinearMap.ker_eq_top,
      LinearMap.exact_iff.mp (KaehlerDifferential.exact_mapBaseChange_map K P A),
      LinearMap.range_eq_top.mpr h.2]
  have hsub : Subsingleton Ω[A⁄P] := by
    refine ⟨fun x y => ?_⟩
    have hs := KaehlerDifferential.map_surjective K P A
    obtain ⟨x, rfl⟩ := hs x
    obtain ⟨y, rfl⟩ := hs y
    simp [hmap]
  -- A subsingleton module is projective, hence so is `Ω[A⁄P]`.
  have hproj : Module.Projective A Ω[A⁄P] := by
    rw [Module.projective_def]
    refine ⟨0, fun x => ?_⟩
    rw [LinearMap.zero_apply, map_zero]
    exact (@Subsingleton.elim _ hsub x 0).symm
  -- Step 2: `δ` has trivial kernel because `H1Cotangent K A = 0`.
  have hmapH1 : Algebra.H1Cotangent.map K P A A = 0 := by
    apply LinearMap.ext
    intro x
    rw [show x = 0 from Subsingleton.elim x 0]
    simp
  have hkerδ : LinearMap.ker (Algebra.H1Cotangent.δ K P A) = ⊥ := by
    rw [LinearMap.exact_iff.mp (Algebra.H1Cotangent.exact_map_δ K P A),
      LinearMap.range_eq_bot.mpr hmapH1]
  -- Step 3: the injectivity of `mapBaseChange` makes `δ` vanish, so `δ` is zero and injective.
  have hδ : Algebra.H1Cotangent.δ K P A = 0 := by
    rw [← LinearMap.range_eq_bot,
      ← LinearMap.exact_iff.mp (Algebra.H1Cotangent.exact_δ_mapBaseChange K P A),
      LinearMap.ker_eq_bot.mpr h.1]
  have hH1 : Subsingleton (Algebra.H1Cotangent P A) :=
    ⟨fun x y => (LinearMap.ker_eq_bot.mp hkerδ) (by simp [hδ])⟩
  exact ⟨hproj, hH1⟩

end Work.Normality
