import Mathlib
import Submission.Work.SSGRoute.sha2_hasse.locUnits_levelClass_eq_zero_infinitePlace
import Submission.Work.SSGRoute.HRec.archUnitsDefs
import Submission.Work.SSGRoute.HRec.localUnitsEquiv_mul_ne_neg_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean vanishing criterion for an explicitly given class

Let `L/k` be a finite Galois extension of number fields, `v` a *complex* infinite place of `L`, and
`c` a `2`-cocycle `Gal(L/k) × Gal(L/k) → Lˣ` with values in `μ₂(L) = {±1}` (`h2`) which is
normalised (`h1`).  If the decomposition group of `v` is the order-two group `⟨γ⟩` (`hstab`,
`hγ2`, `hγ1`), then the localisation of the class of `c` at the place `v` vanishes exactly when the
single value `c (γ, γ)` vanishes.

The proof has two halves, both reducing to the explicit coboundary criterion on a group of order
two (`Work.SSGRoute.sha2_hasse.locUnits_mkClass_eq_zero_iff`, reproved here in the general
"abstract level" form so as not to depend on the heavy `HRec` coefficient bundle):

* if `c (γ, γ) = 0` then the normalised cocycle vanishes on all of `⟨γ⟩ × ⟨γ⟩` (the remaining
  identity `c (γ, 1) = 0` is the cocycle condition), so the zero cochain is a coboundary;
* conversely, a coboundary `f` forces `ρ γ (f γ) + f γ = c (γ, γ)`, and at a complex place
  `ρ γ` is complex conjugation, so `x * (γ • x) ≠ -1` for every local unit `x`
  (`Work.SSGRoute.HRec.localUnitsEquiv_mul_ne_neg_one`); hence `c (γ, γ)` cannot be the nontrivial
  value `-1` and must vanish.

The coefficient map `Lˣ → L_vˣ` is packaged as the plain function `localCoeff` (rather than the
linear map `HassePrinciple.unitsToLocalUnits`, whose domain is the `Rep.res` of the global
representation) so that the rewrite steps below live in the group `Lˣ` itself.
-/

open CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace Work.SSGRoute.HRec

/-! ## The coefficient map `Lˣ → L_wˣ` as a plain function -/

/-- The local coefficient map `Lˣ → L_wˣ`, as a plain function of the global units. -/
noncomputable def localCoeff (k : Type) [Field k] [NumberField k]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place L) : Additive Lˣ → ↥(NK.HassePrinciple.localUnitsRep.{0} k L w) :=
  fun x => (NK.HassePrinciple.unitsToLocalUnits k L w).hom x

/-- The local units `L_wˣ` as a multiplicative group, viewed as the additive carrier of the
local representation. -/
noncomputable def toLocalUnit (k : Type) [Field k] [NumberField k]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place L) : (NK.GlobalCFT.Place.localField L w)ˣ →
      ↥(NK.HassePrinciple.localUnitsRep.{0} k L w) :=
  fun u => Additive.ofMul u

@[simp] theorem localCoeff_zero {k : Type} [Field k] [NumberField k]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place L) : localCoeff k L w (0 : Additive Lˣ) = 0 :=
  map_zero (NK.HassePrinciple.unitsToLocalUnits k L w).hom

theorem localCoeff_ofMul {k : Type} [Field k] [NumberField k]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place L) (u : Lˣ) :
    localCoeff k L w (Additive.ofMul u)
      = Additive.ofMul ((NK.HassePrinciple.unitsToLocalUnitsHom w) u) := by
  rw [show localCoeff k L w (Additive.ofMul u)
      = (NK.HassePrinciple.unitsToLocalUnits k L w).hom (Additive.ofMul u) from rfl]
  rw [NK.HassePrinciple.unitsToLocalUnits_apply]

/-- The coefficient map sends the nontrivial square root of unity `-1` to `-1`. -/
theorem localCoeff_negUnit {k : Type} [Field k] [NumberField k]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place L) :
    localCoeff k L w (Additive.ofMul (Work.SSGRoute.HRec.negUnit L))
      = Additive.ofMul (-1 : (NK.GlobalCFT.Place.localField L w)ˣ) := by
  rw [show localCoeff k L w (Additive.ofMul (Work.SSGRoute.HRec.negUnit L))
      = (NK.HassePrinciple.unitsToLocalUnits k L w).hom
          (Additive.ofMul (Work.SSGRoute.HRec.negUnit L)) from rfl]
  rw [NK.HassePrinciple.unitsToLocalUnits_apply]
  congr 1
  ext
  simp [Work.SSGRoute.HRec.negUnit, NK.HassePrinciple.unitsToLocalUnitsHom]

/-- **The additive form of the archimedean positivity computation.**  For a nontrivial element `σ`
of the decomposition group of an infinite place, the local action on the local units satisfies
`σ • u * u ≠ -1`: at a complex place `σ` acts by complex conjugation and `u * conj u = |u|² ≥ 0`. -/
theorem localUnitsRep_ρ_add_self_ne {k : Type} [Field k] [NumberField k]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (v : NumberField.InfinitePlace L)
    (σ : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite v)) (hσ : σ ≠ 1)
    (u : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite v))ˣ) :
    (NK.HassePrinciple.localUnitsRep.{0} k L (NK.GlobalCFT.Place.ofInfinite v)).ρ σ
        (toLocalUnit k L (NK.GlobalCFT.Place.ofInfinite v) u)
      + toLocalUnit k L (NK.GlobalCFT.Place.ofInfinite v) u
      ≠ toLocalUnit k L (NK.GlobalCFT.Place.ofInfinite v)
          (-1 : (NK.GlobalCFT.Place.localField L
            (NK.GlobalCFT.Place.ofInfinite v))ˣ) := by
  intro h
  have h2 : (NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
      (NK.GlobalCFT.Place.ofInfinite v) σ) u * u = -1 := Additive.ofMul.injective h
  have h3 : u * (NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
      (NK.GlobalCFT.Place.ofInfinite v) σ) u = -1 := by
    rw [mul_comm]; exact h2
  exact Work.SSGRoute.HRec.localUnitsEquiv_mul_ne_neg_one v σ hσ u h3

/-! ## The localisation of an explicitly given class at an abstract level -/

/-- **The localisation of an explicitly given class**: for a place `w` of a finite Galois number
field `L/k`, the localisation of the class of the explicit `2`-cocycle `c` is the class of the
pushed-forward cocycle `(γ,δ) ↦ (unitsToLocalUnits k L w) (c (γ, δ))` on the decomposition group
of `w`. -/
theorem locUnits_mkClass_apply_gen {k : Type} [Field k] [NumberField k]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place L)
    (c : (L ≃ₐ[k] L) × (L ≃ₐ[k] L) → Additive Lˣ)
    (hc : c ∈ groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k L)) :
    (NK.HassePrinciple.locUnits k L w).hom
        (Work.SSGRoute.sha2_hasse.mkClass (NK.HassePrinciple.unitsRep k L) c hc)
      = groupCohomology.H2π (NK.HassePrinciple.localUnitsRep.{0} k L w)
          (groupCohomology.mapCocycles₂ (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype
            (NK.HassePrinciple.unitsToLocalUnits k L w) ⟨c, hc⟩) := by
  have hloc : NK.HassePrinciple.locUnits k L w
      = groupCohomology.map (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype
          (NK.HassePrinciple.unitsToLocalUnits k L w) 2 := by
    rw [NK.HassePrinciple.locUnits, groupCohomology.resNatTrans_app]
    exact NK.NUV2.LC.RouteB.map_id_comp_apply (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype
      (NK.HassePrinciple.unitsToLocalUnits k L w) 2
  rw [hloc]
  rw [show Work.SSGRoute.sha2_hasse.mkClass (NK.HassePrinciple.unitsRep k L) c hc
      = (CategoryTheory.ConcreteCategory.hom (groupCohomology.H2π (NK.HassePrinciple.unitsRep k L)))
          (⟨c, hc⟩ : ↥(groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k L))) from rfl]
  conv_rhs => rw [← ModuleCat.comp_apply
    (groupCohomology.mapCocycles₂ (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype
      (NK.HassePrinciple.unitsToLocalUnits k L w))
    (groupCohomology.H2π (NK.HassePrinciple.localUnitsRep.{0} k L w)) ⟨c, hc⟩]
  rw [← groupCohomology.H2π_comp_map (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype
      (NK.HassePrinciple.unitsToLocalUnits k L w)]
  rw [ModuleCat.comp_apply]

/-- **The vanishing criterion for the localisation of an explicitly given class**: it vanishes
exactly when the pushed-forward cocycle `(γ,δ) ↦ (unitsToLocalUnits k L w) (c (γ, δ))` on the
decomposition group of `w` is a coboundary with values in the local units `L_wˣ`. -/
theorem locUnits_mkClass_eq_zero_iff_gen {k : Type} [Field k] [NumberField k]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place L)
    (c : (L ≃ₐ[k] L) × (L ≃ₐ[k] L) → Additive Lˣ)
    (hc : c ∈ groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k L)) :
    (NK.HassePrinciple.locUnits k L w).hom
        (Work.SSGRoute.sha2_hasse.mkClass (NK.HassePrinciple.unitsRep k L) c hc) = 0 ↔
      ∃ f : ↥(MulAction.stabilizer (L ≃ₐ[k] L) w) → ↥(NK.HassePrinciple.localUnitsRep.{0} k L w),
        ∀ γ δ, (NK.HassePrinciple.localUnitsRep.{0} k L w).ρ γ (f δ) - f (γ * δ) + f γ
          = localCoeff k L w (c (γ, δ)) := by
  rw [locUnits_mkClass_apply_gen L w c hc]
  rw [groupCohomology.H2π_eq_zero_iff, groupCohomology.coboundaries₂, LinearMap.mem_range]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, fun γ δ => ?_⟩
    have h1 := congrFun hf (γ, δ)
    rw [groupCohomology.d₁₂_hom_apply] at h1
    rw [show (⇑(groupCohomology.mapCocycles₂ (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype
            (NK.HassePrinciple.unitsToLocalUnits k L w) ⟨c, hc⟩)) (γ, δ)
        = localCoeff k L w (c (γ, δ)) from by
          rw [groupCohomology.coe_mapCocycles₂, Work.SSGRoute.sha2_hasse.cochainsMap₂_apply]
          rfl] at h1
    exact h1
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    funext p
    obtain ⟨γ, δ⟩ := p
    simp only [groupCohomology.d₁₂_hom_apply]
    rw [show (⇑(groupCohomology.mapCocycles₂ (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype
            (NK.HassePrinciple.unitsToLocalUnits k L w) ⟨c, hc⟩)) (γ, δ)
        = localCoeff k L w (c (γ, δ)) from by
          rw [groupCohomology.coe_mapCocycles₂, Work.SSGRoute.sha2_hasse.cochainsMap₂_apply]
          rfl]
    exact hf γ δ

/-! ## An elementary lemma on groups of order two -/

/-- **An element of `⟨γ⟩` is `1` or `γ` when `γ² = 1`.** -/
theorem mem_zpowers_eq_one_or_eq {G : Type*} [Group G] {γ : G} (hγ2 : γ ^ 2 = 1) {x : G}
    (hx : x ∈ Subgroup.zpowers γ) : x = 1 ∨ x = γ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  rcases Int.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
  · left
    rw [← hk, hr]
    have h2 : r + r = (2 : ℤ) * r := by ring
    rw [h2, zpow_mul]
    rw [show γ ^ (2 : ℤ) = γ ^ 2 by exact zpow_natCast γ 2, hγ2, one_zpow]
  · right
    rw [← hk, hr, zpow_add, zpow_mul]
    rw [show γ ^ (2 : ℤ) = γ ^ 2 by exact zpow_natCast γ 2, hγ2, one_zpow,
      show γ ^ (1 : ℤ) = γ by exact zpow_one γ, one_mul]

/-! ## The main theorem -/

theorem locUnits_mkClass_arch_eq_zero_iff {k : Type} [Field k] [NumberField k]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (v : NumberField.InfinitePlace L) (hv : v.IsComplex)
    (c : (L ≃ₐ[k] L) × (L ≃ₐ[k] L) → Additive Lˣ)
    (hc : c ∈ groupCohomology.cocycles₂ (NK.HassePrinciple.unitsRep k L))
    (h1 : ∀ g : L ≃ₐ[k] L, c (1, g) = 0)
    (h2 : ∀ g h : L ≃ₐ[k] L,
      c (g, h) = 0 ∨ c (g, h) = Additive.ofMul (Work.SSGRoute.HRec.negUnit L))
    (γ : L ≃ₐ[k] L) (hγ2 : γ ^ 2 = 1) (hγ1 : γ ≠ 1)
    (hstab : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite v)
      = Subgroup.zpowers γ) :
    (NK.HassePrinciple.locUnits k L (NK.GlobalCFT.Place.ofInfinite v)).hom
        (Work.SSGRoute.sha2_hasse.mkClass (NK.HassePrinciple.unitsRep k L) c hc) = 0 ↔
      c (γ, γ) = 0 := by
  classical
  rw [locUnits_mkClass_eq_zero_iff_gen L (NK.GlobalCFT.Place.ofInfinite v) c hc]
  constructor
  · -- a coboundary forces `c (γ, γ) = 0`
    rintro ⟨f, hf⟩
    have hγS : γ ∈ MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite v) := by
      rw [hstab]; exact Subgroup.mem_zpowers γ
    let s : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite v) := ⟨γ, hγS⟩
    have hscoe : (s : L ≃ₐ[k] L) = γ := rfl
    have hs2 : s * s = 1 := by
      apply Subtype.ext
      show γ * γ = 1
      rw [← pow_two, hγ2]
    have hsne : s ≠ 1 := by
      intro h
      apply hγ1
      have h' : (s : L ≃ₐ[k] L) = 1 := by rw [h]; rfl
      rwa [hscoe] at h'
    have hρ1 : ∀ x : ↥(NK.HassePrinciple.localUnitsRep.{0} k L
        (NK.GlobalCFT.Place.ofInfinite v)),
        (NK.HassePrinciple.localUnitsRep.{0} k L (NK.GlobalCFT.Place.ofInfinite v)).ρ (1 : _) x
          = x := by
      intro x
      rw [map_one]
      exact Module.End.one_apply x
    -- the value at `(1, 1)` vanishes, hence so does `f 1`
    have hf1 : f 1 = 0 := by
      have h := hf 1 1
      have hz : localCoeff k L (NK.GlobalCFT.Place.ofInfinite v)
          (c ((1 : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite v)),
            (1 : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite v)))) = 0 := by
        rw [show c ((1 : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite v)),
              (1 : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite v))) = 0
            from h1 1]
        exact localCoeff_zero (k := k) (L := L) (w := NK.GlobalCFT.Place.ofInfinite v)
      rw [hρ1 (f 1), one_mul] at h
      rw [hz] at h
      simpa using h
    -- the coboundary identity at `(γ, γ)`
    have hkey : (NK.HassePrinciple.localUnitsRep.{0} k L
            (NK.GlobalCFT.Place.ofInfinite v)).ρ s (f s) + f s
        = localCoeff k L (NK.GlobalCFT.Place.ofInfinite v) (c (γ, γ)) := by
      have h := hf s s
      rw [hs2, hf1, hscoe] at h
      simpa using h
    rcases h2 γ γ with h0 | hneg
    · exact h0
    · -- the nontrivial value is impossible: it would give `x * (γ • x) = -1`
      exfalso
      rw [hneg, localCoeff_negUnit] at hkey
      exact localUnitsRep_ρ_add_self_ne (k := k) (L := L) v s hsne
        ((f s) : (NK.GlobalCFT.Place.localField L
          (NK.GlobalCFT.Place.ofInfinite v))ˣ) hkey
  · -- `c (γ, γ) = 0` makes the zero cochain a coboundary
    intro hcγ
    have hcγ1 : c (γ, 1) = 0 := by
      have h := (Work.SSGRoute.sha2_hasse.mem_cocycles₂_iff
        (A := NK.HassePrinciple.unitsRep k L) (c := c)).mp hc γ 1 γ
      rw [mul_one, one_mul, h1 γ, map_zero] at h
      have h' : - c (γ, 1) = 0 := by
        have h2' : (0 : Additive Lˣ) - c (γ, γ) + c (γ, γ) - c (γ, 1) = - c (γ, 1) := by abel
        rwa [h2'] at h
      exact neg_eq_zero.mp h'
    refine ⟨fun _ => 0, fun a b => ?_⟩
    have ha : (a : L ≃ₐ[k] L) = 1 ∨ (a : L ≃ₐ[k] L) = γ := by
      apply mem_zpowers_eq_one_or_eq hγ2
      rw [← hstab]
      exact a.2
    have hb : (b : L ≃ₐ[k] L) = 1 ∨ (b : L ≃ₐ[k] L) = γ := by
      apply mem_zpowers_eq_one_or_eq hγ2
      rw [← hstab]
      exact b.2
    have hcab : c ((a : L ≃ₐ[k] L), (b : L ≃ₐ[k] L)) = 0 := by
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
      · exact h1 1
      · exact h1 γ
      · exact hcγ1
      · exact hcγ
    simp [hcab]

end Work.SSGRoute.HRec
