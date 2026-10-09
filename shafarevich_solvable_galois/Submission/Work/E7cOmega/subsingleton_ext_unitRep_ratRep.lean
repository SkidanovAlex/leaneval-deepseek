import Mathlib
import Submission.Work.SSGRoute.E7cOmega.ratDivDefs
import Submission.Work.SSGRoute.e0b_bridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Ext¹_H(ℤ, ℚ) = 0` for a finite group `H`

For a finite group `H` and the trivial representations `ℤ = unitRep H` and `ℚ = ratRep H`
(`Work.SSGRoute.E7cOmega.ratRep`), the first `Ext` vanishes:

  `Subsingleton (Ext¹_H(unitRep H, ratRep H))`.

Two proofs of the same classical fact are combined:

* the group-cohomology model `groupCohomology (ratRep H) 1 = H¹(H, ℚ)`: with trivial coefficients
  the `1`-coboundaries vanish, and a `1`-cocycle is an additive character `H → ℚ`; the induction
  `f (g ^ n) = n • f g` together with `g ^ |H| = 1` gives `|H| • f g = 0`, so `f g = 0` because
  `ℚ` is torsion-free;
* the `E0b` bridge `groupCohomology A n ≃+ extH A n`
  (`Work.SSGRoute.Bridge.subsingleton_extH_of_subsingleton_groupCohomology`) transports this to
  the `Ext` core.
-/

namespace Work.E7cOmega

open CategoryTheory SSGRoute.PTExt

/-- **With coefficients in the trivial module `ℚ` every `1`-cocycle is zero.**  For trivial
coefficients the cocycle condition degenerates to `f (g * h) = f g + f h`, so `f` is an additive
character `H → ℚ`; the induction `f (g ^ n) = n • f g` together with `g ^ |H| = 1` and `f 1 = 0`
gives `|H| • f g = 0`, hence `f g = 0` by torsion-freeness of `ℚ`. -/
theorem cocycles_one_ratRep_eq_zero (H : Type) [Group H] [Fintype H]
    (f : H → ↥(Work.SSGRoute.E7cOmega.ratRep H))
    (hf : f ∈ groupCohomology.cocycles₁ (Work.SSGRoute.E7cOmega.ratRep H)) : f = 0 := by
  let A := Work.SSGRoute.E7cOmega.ratRep H
  let fc : groupCohomology.cocycles₁ A := ⟨f, hf⟩
  have hfmul : ∀ g h : H, f (g * h) = f g + f h :=
    fun g h => groupCohomology.cocycles₁_map_mul_of_isTrivial fc g h
  have hf1 : f 1 = 0 := groupCohomology.cocycles₁_map_one fc
  have hind : ∀ (g : H) (n : ℕ), f (g ^ n) = n • f g := by
    intro g n
    induction n with
    | zero => rw [pow_zero, hf1]; simp
    | succ n ih => rw [pow_succ, hfmul (g ^ n) g, ih, succ_nsmul]
  funext g
  have hcard : Fintype.card H • f g = 0 := by
    rw [← hind g (Fintype.card H), pow_card_eq_one, hf1]
  have hn : Fintype.card H ≠ 0 := (Fintype.card_pos).ne'
  rw [nsmul_eq_mul] at hcard
  exact (mul_eq_zero.mp hcard).resolve_left (by exact_mod_cast hn)

/-- **`H¹(H, ℚ) = 0` for a finite group `H`** (group-cohomology model).  For trivial coefficients
the `1`-coboundaries vanish identically, so every `1`-cocycle is a coboundary by
`cocycles_one_ratRep_eq_zero`, and `groupCohomology.H1π` is surjective. -/
theorem subsingleton_groupCohomology_ratRep_one (H : Type) [Group H] [Fintype H] :
    Subsingleton (groupCohomology (Work.SSGRoute.E7cOmega.ratRep H) 1) := by
  have hcob : ∀ f ∈ groupCohomology.cocycles₁ (Work.SSGRoute.E7cOmega.ratRep H),
      f ∈ groupCohomology.coboundaries₁ (Work.SSGRoute.E7cOmega.ratRep H) := by
    intro f hf
    rw [cocycles_one_ratRep_eq_zero H f hf]
    exact Submodule.zero_mem _
  have hsurj : Function.Surjective ⇑(groupCohomology.H1π (Work.SSGRoute.E7cOmega.ratRep H)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  refine ⟨fun x y => ?_⟩
  obtain ⟨x', rfl⟩ := hsurj x
  obtain ⟨y', rfl⟩ := hsurj y
  have hx : ⇑(groupCohomology.H1π (Work.SSGRoute.E7cOmega.ratRep H)) x' = 0 :=
    (groupCohomology.H1π_eq_zero_iff x').mpr (hcob x' x'.2)
  have hy : ⇑(groupCohomology.H1π (Work.SSGRoute.E7cOmega.ratRep H)) y' = 0 :=
    (groupCohomology.H1π_eq_zero_iff y').mpr (hcob y' y'.2)
  rw [hx, hy]

/-- The requested statement: `Ext¹_H(unitRep H, ratRep H) = 0` for `H` finite. -/
theorem subsingleton_ext_unitRep_ratRep (H : Type) [Group H] [Fintype H] :
    Subsingleton (CategoryTheory.Abelian.Ext (SSGRoute.PTExt.unitRep H)
      (Work.SSGRoute.E7cOmega.ratRep H) 1) :=
  Work.SSGRoute.Bridge.subsingleton_extH_of_subsingleton_groupCohomology 1 H
    (Work.SSGRoute.E7cOmega.ratRep H) (subsingleton_groupCohomology_ratRep_one H)

end Work.E7cOmega
