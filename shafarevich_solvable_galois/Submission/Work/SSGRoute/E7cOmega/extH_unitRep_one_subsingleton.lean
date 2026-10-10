import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Submission.Work.SSGRoute.e0b_bridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H¹(G, ℤ) = 0` for a finite group `G`, in the `Ext` core

For a finite group `G` and the trivial module `ℤ = unitRep G`, the first cohomology vanishes:

  `Subsingleton (extH (unitRep G) 1)`.

The mathematical content is the classical fact `H¹(G, ℤ) = 0` for `G` finite (a finite group has no
non-trivial additive character into the torsion-free group `ℤ`).  We prove it in the group-cohomology
model (`groupCohomology (unitRep G) 1`, whose `1`-cocycles are the crossed homomorphisms
`G → ↥(unitRep G)` and whose `1`-coboundaries vanish identically for trivial coefficients) and then
transport to the `Ext` core along the `E0b` bridge
`Work.SSGRoute.Bridge.subsingleton_extH_of_subsingleton_groupCohomology`.

## Main results

* `cocycles_one_unitRep_eq_zero` -- with trivial coefficients every `1`-cocycle is `0`;
* `subsingleton_groupCohomology_unitRep_one` -- `H¹(G, unitRep G) = 0` for `G` finite;
* `extH_unitRep_one_subsingleton` -- the requested `Ext`-core statement.
-/

namespace Work.SSGRoute.E7cOmega

open SSGRoute.PTExt

open CategoryTheory in
/-- **With coefficients in the trivial module `ℤ` (`unitRep G`) every `1`-cocycle is zero.**

For trivial coefficients the cocycle condition degenerates to `f (g * h) = f h + f g`, so that `f`
is an additive character `G → ↥(unitRep G)`; the induction `f (g ^ n) = n • f g` together with
`g ^ |G| = 1` and `f 1 = 0` gives `|G| • f g = 0`, and `↥(unitRep G) = ULift ℤ` is torsion-free. -/
theorem cocycles_one_unitRep_eq_zero (G : Type) [Group G] [Fintype G]
    (f : G → ↥(SSGRoute.PTExt.unitRep G))
    (hf : f ∈ groupCohomology.cocycles₁ (SSGRoute.PTExt.unitRep G)) : f = 0 := by
  have h := (groupCohomology.mem_cocycles₁_iff (A := SSGRoute.PTExt.unitRep G) f).mp hf
  have hρ : ∀ (g : G) (x : ↥(SSGRoute.PTExt.unitRep G)),
      (SSGRoute.PTExt.unitRep G).ρ g x = x := fun g x => Rep.trivial_ρ_apply g x
  -- the cocycle condition with trivial coefficients
  have h' : ∀ g hh, f (g * hh) = f hh + f g := by
    intro g hh
    rw [h g hh, hρ g (f hh)]
  -- `f 1 = 0`
  have hf1 : f 1 = 0 := by
    have h1 := h' 1 1
    rw [mul_one] at h1
    have hh := congrArg (fun x => x - f 1) h1
    have : (0 : ↥(SSGRoute.PTExt.unitRep G)) = f 1 := by simpa using hh
    exact this.symm
  -- the additive character is `f (g ^ n) = n • f g`
  have hind : ∀ (g : G) (n : ℕ), f (g ^ n) = n • f g := by
    intro g n
    induction n with
    | zero => rw [pow_zero, hf1]; simp
    | succ n ih =>
      rw [pow_succ, h' (g ^ n) g, ih, succ_nsmul]
      abel
  funext g
  -- `|G| • f g = 0`
  have hcard : Fintype.card G • f g = 0 := by
    rw [← hind g (Fintype.card G), pow_card_eq_one, hf1]
  have hn : Fintype.card G ≠ 0 := (Fintype.card_pos).ne'
  -- torsion-freeness of `↥(unitRep G) = ULift ℤ`
  have h'2 : (AddEquiv.ulift : ULift ℤ ≃+ ℤ) (f g) = 0 := by
    have h2 : Fintype.card G • ((AddEquiv.ulift : ULift ℤ ≃+ ℤ) (f g)) = 0 := by
      rw [← map_nsmul]
      exact congrArg (AddEquiv.ulift : ULift ℤ ≃+ ℤ) hcard
    rw [nsmul_eq_mul] at h2
    have hn' : ((Fintype.card G : ℤ)) ≠ 0 := by exact_mod_cast hn
    exact (mul_eq_zero.mp h2).resolve_left hn'
  exact (AddEquiv.ulift : ULift ℤ ≃+ ℤ).injective (by simpa using h'2)

open CategoryTheory in
/-- **`H¹(G, ℤ) = 0` for a finite group `G`** (group-cohomology model).  For trivial coefficients
the `1`-coboundaries vanish identically, so every `1`-cocycle is a coboundary by
`cocycles_one_unitRep_eq_zero`, and `groupCohomology.H1π` is surjective. -/
theorem subsingleton_groupCohomology_unitRep_one (G : Type) [Group G] [Fintype G] :
    Subsingleton (groupCohomology (SSGRoute.PTExt.unitRep G) 1) := by
  have hcob : ∀ f ∈ groupCohomology.cocycles₁ (SSGRoute.PTExt.unitRep G),
      f ∈ groupCohomology.coboundaries₁ (SSGRoute.PTExt.unitRep G) := by
    intro f hf
    rw [cocycles_one_unitRep_eq_zero G f hf]
    exact Submodule.zero_mem _
  have hsurj : Function.Surjective ⇑(groupCohomology.H1π (SSGRoute.PTExt.unitRep G)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  refine ⟨fun x y => ?_⟩
  obtain ⟨x', rfl⟩ := hsurj x
  obtain ⟨y', rfl⟩ := hsurj y
  have hx : ⇑(groupCohomology.H1π (SSGRoute.PTExt.unitRep G)) x' = 0 :=
    (groupCohomology.H1π_eq_zero_iff x').mpr (hcob x' x'.2)
  have hy : ⇑(groupCohomology.H1π (SSGRoute.PTExt.unitRep G)) y' = 0 :=
    (groupCohomology.H1π_eq_zero_iff y').mpr (hcob y' y'.2)
  rw [hx, hy]

/-- **The requested statement**: for a finite group `G`, `H¹(G, ℤ) = 0` in the `Ext` core,
i.e. `Ext¹_G(ℤ, ℤ) = 0`. -/
theorem extH_unitRep_one_subsingleton (G : Type) [Group G] [Fintype G] :
    Subsingleton (SSGRoute.PTExt.extH (SSGRoute.PTExt.unitRep G) 1) :=
  Work.SSGRoute.Bridge.subsingleton_extH_of_subsingleton_groupCohomology 1 G
    (SSGRoute.PTExt.unitRep G) (subsingleton_groupCohomology_unitRep_one G)

end Work.SSGRoute.E7cOmega
