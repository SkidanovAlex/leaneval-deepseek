import Mathlib
import Submission.Work.DSSEC.Basic

namespace Work.DSSEC

attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry
open DSMap DSMap.Mix2
universe u

/-- The localization map `W_{t_S} → W[1/(p·t_S)]` (i.e. `W_{t_S} → (W_{t_S})_p`, inverting the
image of `p`) is injective when `p` is a nonzerodivisor of `W`: localizing at `p` is injective
exactly when (the image of) `p` is a nonzerodivisor, and the image of a nonzerodivisor under a
localization of `W` is again a nonzerodivisor.  Here we argue directly through the explicit
description of both sides as localizations of `W` at the powers of `t_S`, resp. of `p·t_S`. -/
lemma cmpOfLoc_injective {W : Type u} [CommRing W] {ι : Type u} [DecidableEq ι] (p : ℕ)
    (t : ι → W) (hW : IsSMulRegular W p) (S : Finset ι) :
    Function.Injective (cmpOfLoc p t S) := by
  rw [cmpOfLoc, IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
  intro x y
  rw [IsLocalization.eq_iff_exists (Submonoid.powers (tS t S)) (Localization.Away (tS t S)),
      IsLocalization.eq_iff_exists (Submonoid.powers ((p : W) * tS t S)) (cmpRing p t S)]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (↑c) (tS t S)).1 c.2
    refine ⟨⟨((p : W) * tS t S)^n, (Submonoid.mem_powers_iff _ _).2 ⟨n, rfl⟩⟩, ?_⟩
    rw [← hn] at hc
    show ((p : W) * tS t S)^n * x = ((p : W) * tS t S)^n * y
    rw [mul_pow, mul_assoc, hc, ← mul_assoc]
  · rintro ⟨c, hc⟩
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (↑c) ((p : W) * tS t S)).1 c.2
    refine ⟨⟨tS t S ^ n, (Submonoid.mem_powers_iff _ _).2 ⟨n, rfl⟩⟩, ?_⟩
    rw [← hn] at hc
    have hreg : IsSMulRegular W ((p : W)^n) := by
      have h2 : IsSMulRegular W ((p : W)) :=
        (isSMulRegular_map (Nat.castRingHom W) (fun m : W => by
          rw [smul_eq_mul, nsmul_eq_mul]; rfl)).2 hW
      simpa using h2.pow n
    show tS t S ^ n * x = tS t S ^ n * y
    refine hreg ?_
    change ((p : W)^n) * (tS t S ^ n * x) = ((p : W)^n) * (tS t S ^ n * y)
    rw [← mul_assoc, ← mul_assoc, ← mul_pow]
    exact hc

/-- The comparison map `W[J/t_S] → W[1/(p·t_S)]` is injective when `W` is `p`-torsion-free: it
is the composite of the inclusion `chartRing t S ⊆ W_{t_S}` with the localization map
`W_{t_S} → W_{t_S}[1/p]` (i.e. `W → W[1/(p·t_S)]`), which is injective because `p` is a
nonzerodivisor of `W`, hence of `W_{t_S}`.  (`IsLocalization.injective_iff_isRegular`.) -/
theorem chartToCmp_injective {W : Type u} [CommRing W] {ι : Type u} [DecidableEq ι] (p : ℕ)
    (t : ι → W) (hW : IsSMulRegular W p) (S : Finset ι) :
    Function.Injective (Work.DSSEC.chartToCmp p t S) := by
  intro x y hxy
  exact Subtype.ext (cmpOfLoc_injective p t hW S hxy)

end Work.DSSEC
