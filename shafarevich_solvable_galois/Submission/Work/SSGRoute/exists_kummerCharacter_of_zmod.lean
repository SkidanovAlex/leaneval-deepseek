import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.zmod_roots_of_unity
import Submission.Work.SSGRoute.zr_pow_castHom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- Evaluation of `zr` at an arbitrary element `k` of `Multiplicative (ZMod n)`, expressed via
the canonical representative `(Multiplicative.toAdd k).val` of its underlying class in `ZMod n`. -/
lemma zr_apply_toAdd {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} [NeZero n] {ζ : Rˣ}
    (hζ : IsPrimitiveRoot ζ n) (k : Multiplicative (ZMod n)) :
    ((zr hζ k : ↥(rootsOfUnity n R)) : Rˣ) = ζ ^ ((Multiplicative.toAdd k).val : ℤ) :=
  zr_apply_val hζ (Multiplicative.toAdd k)

/-- The value of `zr hζ k` transported along an injective algebra map `U → K'` of fields is the
`(Multiplicative.toAdd k).val`-th power of the transported primitive root. -/
lemma units_map_zr {U K' : Type*} [Field U] [Field K'] [Algebra U K'] {n : ℕ} [NeZero n]
    {ζ : Uˣ} (hζ : IsPrimitiveRoot ζ n) (k : Multiplicative (ZMod n)) :
    ((Units.map (algebraMap U K').toMonoidHom ((zr hζ k : ↥(rootsOfUnity n U)) : Uˣ) : K'ˣ) : K')
      = (algebraMap U K' (ζ : U)) ^ (Multiplicative.toAdd k).val := by
  rw [Units.coe_map, zr_apply_toAdd hζ k, Units.val_zpow_eq_zpow_val, zpow_natCast, map_pow]
  rfl

/-- **The `μ_n`-valued character attached to a `ZMod n`-valued character.**

Let `F : IntermediateField ℚ ℚ̄` contain a primitive `n`-th root of unity `ζ` (with `n ≠ 0`).
Then every character `χ : ↥F.fixingSubgroup →* Multiplicative (ZMod n)` is obtained by
exponentiating `ζ`: there is a monoid homomorphism `ω : ↥F.fixingSubgroup →* (↥F)ˣ` such that
`ω σ = ζ ^ (Multiplicative.toAdd (χ σ)).val` in `ℚ̄` for all `σ`.

Proof sketch: every `n`-th root of unity of `ℚ̄` is a power of `ζ`, hence lies in `F`; the
multiplicative isomorphism `Work.SSGRoute.zr` of
`Submission/Work/SSGRoute/zmod_roots_of_unity.lean` (`Multiplicative (ZMod n) ≃* μ_n(R)`, with
evaluation `zr_apply_int`) identifies `Multiplicative (ZMod n)` with the `n`-th roots of unity of
`F`. -/
theorem exists_kummerCharacter_of_zmod
    (F : IntermediateField ℚ SSGRoute.QBar) {n : ℕ} [NeZero n]
    (ζ : SSGRoute.QBar) (hζ : IsPrimitiveRoot ζ n) (hζF : ζ ∈ F)
    (χ : ↥(F.fixingSubgroup) →* Multiplicative (ZMod n)) :
    ∃ ω : ↥(F.fixingSubgroup) →* (↥F)ˣ,
      ∀ σ : ↥(F.fixingSubgroup),
        (((ω σ : (↥F)ˣ) : ↥F) : SSGRoute.QBar) = ζ ^ (Multiplicative.toAdd (χ σ)).val := by
  have hn : n ≠ 0 := NeZero.ne n
  have hζ_ne : (ζ : SSGRoute.QBar) ≠ 0 := hζ.ne_zero hn
  -- `ζ` viewed as a unit of `F`
  let ζF : (↥F)ˣ := Units.mk0 (⟨ζ, hζF⟩ : ↥F) (by
    intro h
    exact hζ_ne (by
      have := congrArg (fun x : ↥F => (x : SSGRoute.QBar)) h
      simpa using this))
  have hζF_val : (algebraMap ↥F SSGRoute.QBar) (ζF : ↥F) = ζ := rfl
  have hζF' : IsPrimitiveRoot ζF n := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    rw [show (ζF : ↥F) = (⟨ζ, hζF⟩ : ↥F) from rfl]
    exact IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ
  -- the character into the `n`-th roots of unity of `F`
  refine ⟨(Subgroup.subtype (rootsOfUnity n ↥F)).comp ((zr hζF').toMonoidHom.comp χ), ?_⟩
  intro σ
  show ((((zr hζF' (χ σ) : ↥(rootsOfUnity n ↥F)) : (↥F)ˣ) : ↥F) : SSGRoute.QBar)
      = ζ ^ (Multiplicative.toAdd (χ σ)).val
  have hcoe1 : ((Units.map (algebraMap ↥F SSGRoute.QBar).toMonoidHom
        ((zr hζF' (χ σ) : ↥(rootsOfUnity n ↥F)) : (↥F)ˣ) : SSGRoute.QBarˣ) : SSGRoute.QBar)
      = ((((zr hζF' (χ σ) : ↥(rootsOfUnity n ↥F)) : (↥F)ˣ) : ↥F) : SSGRoute.QBar) := by
    rw [Units.coe_map]; rfl
  rw [← hcoe1, units_map_zr (U := ↥F) (K' := SSGRoute.QBar) hζF' (χ σ), hζF_val]

end Work.SSGRoute
