/-
DSM2b — the mixed-characteristic area's deliverable:
`DSMap.Mix.area_M2b_proved`, whose statement is identical to the frozen `DSMap.Mix.area_M2b`
(the `M2b` node of the MIX subtree: Bhatt Prop. 4.1 + composition).

Main results imported here:

* `Work.DSM2b.flat_of_flat_mod_base` : Bhatt Prop. 4.1 (flat part) — the crux.
* `Work.DSM2b.ff_quot_composite`    : `B₁` FF over `A`, `B₂/πB₂` FF over `B₁/πB₁` ⟹
  `B₂/πB₂` FF over `A/π`.
* `Work.DSM2b.maximalIdeal_smul_ne_top` : the maximal-ideal (faithfulness) condition.

The proof of `area_M2b_proved` is the composition: with `π = p` (a nonzerodivisor on `A` because
`A` is a domain of characteristic `0`, and on `B₂` because `PerfectoidData` says so, and `B₂` is
`p`-adically complete), the mod-`p` reduction `A/p → B₂/pB₂` is faithfully flat by
`ff_quot_composite`; Bhatt's Proposition then gives `Module.Flat A B₂`, and the maximal-ideal
condition upgrades it to faithful flatness.
-/
import Submission.Work.DSMap.Mix
import Submission.Work.DSREG.Main
import Submission.Work.DSM2b.flat_of_flat_mod_base
import Submission.Work.DSM2b.maximalIdeal_smul_ne_top
import Submission.Work.DSM2b.ff_quot_composite

open CategoryTheory AlgebraicGeometry IsLocalRing Limits

open Work.DSM2b

attribute [local instance] MvPolynomial.gradedAlgebra

namespace DSMap.Mix

universe a

/-- **M2b** (Bhatt Prop 4.1 + composition): faithful flatness of the composite perfectoid cover.
Identical statement to the frozen `DSMap.Mix.area_M2b`. -/
theorem area_M2b_proved (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] (p : ℕ) [Fact p.Prime] [CharZero A]
    [CharP (ResidueField A) p] (B₁ B₂ : Type a) [CommRing B₁] [CommRing B₂] [Algebra A B₁]
    [Algebra B₁ B₂] [Algebra A B₂] [IsScalarTower A B₁ B₂] [Module.FaithfullyFlat A B₁]
    (Q : PerfectoidData p B₂)
    (h : Module.FaithfullyFlat (B₁ ⧸ Ideal.span {(p : B₁)})
      (B₂ ⧸ (Ideal.span {(p : B₁)}).map (algebraMap B₁ B₂))) :
    Module.FaithfullyFlat A B₂ := by
  -- `A` is a domain (DSREG), so `p ≠ 0` is a nonzerodivisor
  have hdom : IsDomain A := area_REG_proved A
  have hp0 : (p : A) ≠ 0 := by
    intro h0
    have h1 : ((p : ℕ) : A) = ((0 : ℕ) : A) := by rw [h0, Nat.cast_zero]
    exact (Fact.out (p := p.Prime)).ne_zero (CharZero.cast_injective h1)
  have hpA : IsSMulRegular A (p : A) := fun x y hxy =>
    mul_left_cancel₀ hp0 (by simpa [smul_eq_mul] using hxy)
  -- `PerfectoidData` gives `p`-torsion-freeness and `p`-adic completeness of `B₂`
  have hpB : IsSMulRegular B₂ (algebraMap A B₂ (p : A)) := by simpa using Q.torsionFree
  have hcomp : IsAdicComplete (Ideal.span {(algebraMap A B₂ (p : A))}) B₂ := by
    simpa using Q.complete
  -- the mod-`p` reduction of `A → B₂` is faithfully flat
  have hffmod : Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A)})
      (B₂ ⧸ (Ideal.span {(p : A)}).map (algebraMap A B₂)) := by
    have h2 : (p : B₁) = (algebraMap A B₁) (p : A) := by simp
    rw [h2] at h
    exact ff_quot_composite (B₁ := B₁) (B₂ := B₂) (π := (p : A)) h
  -- Bhatt's Proposition 4.1
  have hflat : Module.Flat A B₂ := by
    have h' : Module.Flat (A ⧸ Ideal.span {(p : A)})
        (B₂ ⧸ (Ideal.span {(p : A)}).map (algebraMap A B₂)) := hffmod.toFlat
    haveI : IsAdicComplete (Ideal.span {(algebraMap A B₂ (p : A))}) B₂ := hcomp
    exact flat_of_flat_mod_base (π := (p : A)) hpA hpB h'
  -- the maximal ideal of the local ring `A` contains `p`
  have hp𝔪 : (p : A) ∈ IsLocalRing.maximalIdeal A := by
    refine (IsLocalRing.mem_maximalIdeal (p : A)).mpr ?_
    intro hu
    have hz : (p : ResidueField A) = 0 := by
      simpa using (CharP.cast_eq_zero (ResidueField A) p)
    have hz2 : (p : ResidueField A) = (algebraMap A (ResidueField A)) (p : A) := by simp
    have hz' : (algebraMap A (ResidueField A)) (p : A) = 0 := by rw [← hz2]; exact hz
    have hu' : IsUnit ((algebraMap A (ResidueField A)) (p : A)) :=
      IsUnit.map (algebraMap A (ResidueField A)) hu
    rw [hz'] at hu'
    exact not_isUnit_zero hu'
  -- faithful flatness
  haveI : Module.Flat A B₂ := hflat
  refine Module.FaithfullyFlat.mk fun 𝔪 h𝔪 => ?_
  have h𝔪' : 𝔪 = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal h𝔪
  rw [h𝔪']
  exact maximalIdeal_smul_ne_top (R := A) (B := B₂) (p : A) hffmod
    (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal.isMaximal A) hp𝔪

/-- `area_M2b_proved` has (definitionally) the same statement as the frozen `area_M2b`:
so it can be used in place of it, at every universe. -/
example : @area_M2b_proved = @area_M2b := Subsingleton.elim _ _

end DSMap.Mix
