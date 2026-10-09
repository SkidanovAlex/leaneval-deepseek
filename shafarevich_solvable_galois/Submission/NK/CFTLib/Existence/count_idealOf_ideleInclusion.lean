import Mathlib
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.GlobalCFT.Inclusion
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The exponent of the ideal of an idèle under the idèlic inclusion

For a finite extension `L / K` of number fields, a system of places `u w` of `K` below the places
`w` of `L` and the associated inclusion of idèles `φ : 𝕀 K →* 𝕀 L` (whose `w`-component is the
canonical local embedding `K_{u w}ˣ →* L_wˣ`), the exponent of a prime `𝔮` of `𝓞 L` in the
fractional ideal `idealOf (φ x)` is the ramification index `e(𝔮 | 𝔭)` times the exponent of `𝔭`
in `idealOf x`, for `𝔮` lying over `𝔭`:

`count L 𝔮 (idealOf (φ x)) = e(𝔮 | 𝔭) * count K 𝔭 (idealOf x)`.

Since `Place.ofFinite 𝔮` lies over both `u (Place.ofFinite 𝔮)` and `Place.ofFinite 𝔭`, the
uniqueness of the place of `K` below a place of `L` (`NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique`)
identifies `u (Place.ofFinite 𝔮)` with `Place.ofFinite 𝔭`, and the claim reduces to the local
computation `v (adicCompletionMap 𝔭 𝔮 y) = v y ^ e` for the map of adic completions
(`Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow`).

## Main result

* `NK.CFTLib.Existence.count_idealOf_ideleInclusion`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NK.GlobalCFT NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Existence

/-- The value of a dependent function at `a`, transported along an equality `a = b`, is the value
at `b`. -/
lemma eqRec_apply_dep {α : Type} {F : α → Type} (x : (a : α) → F a) {a b : α} (h : a = b) :
    h ▸ x a = x b := by
  cases h
  rfl

/-- The local algebra map on unit groups is compatible with transporting its source place along an
equality of places. -/
lemma localAlgebraMapUnits_eqRec {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (q : HeightOneSpectrum (𝓞 L)) (a b : Place K)
    (ha : Place.LiesOver (Place.ofFinite q) a) (hb : Place.LiesOver (Place.ofFinite q) b)
    (h : a = b) (y : (Place.localField K a)ˣ) :
    Place.localAlgebraMapUnits (Place.ofFinite q) b hb (h ▸ y)
      = Place.localAlgebraMapUnits (Place.ofFinite q) a ha y := by
  cases h
  rfl

/-- At a nonarchimedean place the local algebra map on unit groups is `Units.map` of the map of
adic completions. -/
lemma localAlgebraMapUnits_ofFinite_apply {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (h : Place.LiesOver (Place.ofFinite q) (Place.ofFinite Q)) :
    Place.localAlgebraMapUnits (Place.ofFinite q) (Place.ofFinite Q) h
      = Units.map ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).toMonoidHom) := by
  unfold Place.localAlgebraMapUnits
  simp only []
  rw [dif_pos hq]

/-- The valuation of a unit of `K_Q` after applying the local algebra map, in terms of the
ramification index. -/
lemma val_localAlgebraMapUnits_ofFinite {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (h : Place.LiesOver (Place.ofFinite q) (Place.ofFinite Q)) (y : (Q.adicCompletion K)ˣ) :
    Valued.v ((Place.localAlgebraMapUnits (Place.ofFinite q) (Place.ofFinite Q) h y :
        (q.adicCompletion L)ˣ) : q.adicCompletion L)
      = (Valued.v (y : Q.adicCompletion K)) ^ (q.asIdeal.ramificationIdx (𝓞 K)) := by
  rw [localAlgebraMapUnits_ofFinite_apply Q q hq h]
  rw [Units.coe_map]
  exact Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow Q q hq
    (y : Q.adicCompletion K)

theorem count_idealOf_ideleInclusion {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (u : NK.GlobalCFT.Place L → NK.GlobalCFT.Place K)
    (hu : ∀ w : NK.GlobalCFT.Place L, w.LiesOver (u w))
    (φ : NK.GlobalCFT.Idele K →* NK.GlobalCFT.Idele L)
    (hφ : ∀ (x : NK.GlobalCFT.Idele K) (w : NK.GlobalCFT.Place L),
      φ x w = NK.GlobalCFT.Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)))
    (x : NK.GlobalCFT.Idele K)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (h𝔮 : 𝔮.asIdeal.LiesOver 𝔭.asIdeal) :
    FractionalIdeal.count L 𝔮 (NK.GlobalCFT.Idele.idealOf (φ x)) =
      𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
        FractionalIdeal.count K 𝔭 (NK.GlobalCFT.Idele.idealOf x) := by
  -- rewrite both sides as exponents at the relevant finite places
  rw [NK.GlobalCFT.Idele.count_idealOf, NK.GlobalCFT.Idele.count_idealOf]
  rw [NK.GlobalCFT.Idele.exp_def, NK.GlobalCFT.Idele.exp_def]
  -- the place of `K` below `Place.ofFinite 𝔮` is `Place.ofFinite 𝔭`
  have hu_eq : u (Place.ofFinite 𝔮) = Place.ofFinite 𝔭 :=
    NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique (hu (Place.ofFinite 𝔮))
      (Place.liesOver_ofFinite h𝔮)
  -- the `𝔮`-component of `φ x`
  rw [hφ x (Place.ofFinite 𝔮)]
  -- transport the source place of the local map along `hu_eq`
  rw [← localAlgebraMapUnits_eqRec 𝔮 (u (Place.ofFinite 𝔮)) (Place.ofFinite 𝔭)
    (hu (Place.ofFinite 𝔮)) (Place.liesOver_ofFinite h𝔮) hu_eq (x (u (Place.ofFinite 𝔮)))]
  rw [eqRec_apply_dep x hu_eq]
  -- the local computation
  rw [val_localAlgebraMapUnits_ofFinite 𝔭 𝔮 h𝔮 (Place.liesOver_ofFinite h𝔮) (x (Place.ofFinite 𝔭))]
  rw [NK.GlobalCFT.Idele.exp_val 𝔭 x]
  -- elementary arithmetic in the value group
  rw [← WithZero.exp_nsmul, WithZero.log_exp]
  simp

end NK.CFTLib.Existence
