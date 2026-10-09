import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
/-!
# Rank one of the extension of a valuation to the completion

If `v` is a rank one valuation on a field `K`, then its extension
`Valued.extensionValuation` to the completion `hat K` is again rank one.

The point is that `Valued.extensionValuation` has exactly the same image in `Γ₀` as `v`
(`Valued.extensionValuation_apply_coe` and `Valued.exists_coe_eq_v`), hence exactly the same
value group; so an order embedding of the value group of `v` into `ℝ≥0` induces one for the
value group of the extension.
-/

namespace NK.NeukirchUchida

theorem rankOne_extensionValuation_completion {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (h : hv.v.RankOne) :
    Nonempty ((Valued.extensionValuation (K := K) (Γ₀ := Γ₀)).RankOne) := by
  haveI := h
  obtain ⟨r, hr0, hr1⟩ := Valuation.RankOne.nontrivial (hv.v)
  -- The image of the extended valuation is the image of `v`.
  have hrange : Set.range (Valued.extensionValuation (K := K) (Γ₀ := Γ₀)) =
      Set.range (hv.v : K → Γ₀) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := hx
      obtain ⟨s, hs⟩ := Valued.exists_coe_eq_v (K := K) (Γ₀ := Γ₀) (hv := hv) y
      exact ⟨s, hs.symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨(s : UniformSpace.Completion K), Valued.extensionValuation_apply_coe (hv := hv) s⟩
  -- Hence the two value groups (subgroups of `Γ₀ˣ`) coincide.
  have hvg : MonoidWithZeroHom.valueGroup
        (MonoidWithZeroHom.ofClass (Valued.extensionValuation (K := K) (Γ₀ := Γ₀))) =
      MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass hv.v) := by
    have h1 : (Units.val '' ((MonoidWithZeroHom.valueGroup
          (MonoidWithZeroHom.ofClass (Valued.extensionValuation (K := K) (Γ₀ := Γ₀)))) : Set Γ₀ˣ))
        = Set.range (Valued.extensionValuation (K := K) (Γ₀ := Γ₀)) \ {0} := by
      simpa [MonoidWithZeroHom.coe_ofClass] using
        MonoidWithZeroHom.valueGroup_eq_range
          (MonoidWithZeroHom.ofClass (Valued.extensionValuation (K := K) (Γ₀ := Γ₀)))
    have h2 : (Units.val '' ((MonoidWithZeroHom.valueGroup
          (MonoidWithZeroHom.ofClass hv.v)) : Set Γ₀ˣ))
        = Set.range (hv.v : K → Γ₀) \ {0} := by
      simpa [MonoidWithZeroHom.coe_ofClass] using
        MonoidWithZeroHom.valueGroup_eq_range (MonoidWithZeroHom.ofClass hv.v)
    have h3 : (Units.val '' ((MonoidWithZeroHom.valueGroup
            (MonoidWithZeroHom.ofClass (Valued.extensionValuation (K := K) (Γ₀ := Γ₀)))) : Set Γ₀ˣ))
        = (Units.val '' ((MonoidWithZeroHom.valueGroup
            (MonoidWithZeroHom.ofClass hv.v)) : Set Γ₀ˣ)) := by
      rw [h1, h2, hrange]
    exact SetLike.coe_injective
      ((Set.image_injective (f := (Units.val : Γ₀ˣ → Γ₀))).mpr Units.val_injective h3)
  -- The identity on the common value group is strictly monotone for the induced orders.
  have hψ : StrictMono (Subgroup.inclusion hvg.le) := by
    intro a b hab
    exact hab
  have hφ : StrictMono (WithZero.map' (Subgroup.inclusion hvg.le)) :=
    WithZero.map'_strictMono hψ
  -- Compose with the order embedding coming from `RankOne v` to get `RankLeOne` for the
  -- extension, then use nontriviality.
  haveI : (Valued.extensionValuation (K := K) (Γ₀ := Γ₀)).RankLeOne :=
    { hom' := (Valuation.RankOne.hom hv.v).comp (WithZero.map' (Subgroup.inclusion hvg.le))
      strictMono' := (Valuation.RankOne.strictMono hv.v).comp hφ }
  refine ⟨Valuation.RankLeOne.rankOne_of_exists _ ⟨(r : UniformSpace.Completion K), ?_, ?_⟩⟩
  · intro hz
    apply hr0
    rw [← Valued.extensionValuation_apply_coe (hv := hv) r, hz, map_zero]
  · rw [Valued.extensionValuation_apply_coe (hv := hv)]
    exact hr1

end NK.NeukirchUchida
