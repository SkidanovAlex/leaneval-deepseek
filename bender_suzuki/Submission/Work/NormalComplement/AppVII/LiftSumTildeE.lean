import Mathlib
import Submission.Work.CharCore.Main
import Submission.Work.Hering.AppVII.brauer_lift_aux
import Submission.Work.Hering.AppVII.iota_injective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `∑_χ tildeE χ = |A| • 1` in `ℤ[ζ_|A|][A]`

Let `A` be a finite group, `n = |A|`, `R = ℤ[ζ_n] = ℤ[X]/(Φ_n)`, and for
`χ ∈ Work.CharCore.Irr A` let

`tildeE χ = (χ(1) : R) • ∑ g : A, charLift χ g⁻¹ • single g 1`

be the lift to `R[A]` of `|A| • e_χ`, `|A|` times the central primitive idempotent of `ℂ[A]`
attached to `χ` (`Submission/Work/Hering/AppVII/brauer_lift_aux.lean`).

The theorem `LiftSumTildeE` proved here is the last of the five standard identities satisfied by
the `tildeE χ`: the `tildeE χ` sum to `|A|`,

`∑_{χ ∈ Irr A} tildeE χ = (|A| : R) • 1`   in `R[A]`.

It is proved from scratch (the upstream statement `Work.Hering.AppVII.sum_tildeE` is still
`sorry`-ed and is *not* used).  Writing `tildeE χ = (irrDeg χ : R) • ∑_g charLift χ g⁻¹ • g` and
reassociating the double sum, the coefficient of `g ∈ A` on the left is

`∑_{χ ∈ Irr A} (irrDeg χ : R) * charLift χ g⁻¹ : R`.

Since `iota : R → ℂ` is injective (`Work.Hering.AppVII.iota_injective`), this integral coefficient
is determined by its image in `ℂ`, where it becomes

`∑_{χ ∈ Irr A} (irrDeg χ : ℂ) * χ g⁻¹ = regularChar A g⁻¹ = if g = 1 then |A| else 0`

(the decomposition of the regular character, `Work.CharCore.regularChar_eq_sum`).  Hence both
sides are `∑_g (if g = 1 then (|A| : R) else 0) • single g 1`.
-/

noncomputable section

open Classical

open scoped BigOperators

namespace Work.NormalComplement.AppVII

/- Two general rewritings of finite sums in a monoid algebra, used to evaluate the sum of the
`tildeE χ` coefficientwise. -/

/-- A sum of the form `∑ g, (if g = 1 then c else 0) • single g 1` collapses to `c • 1`. -/
theorem sum_ite_smul_single {R G : Type*} [CommSemiring R] [Group G] [Fintype G] [DecidableEq G]
    (c : R) :
    (∑ g : G, (if g = 1 then c else 0) • MonoidAlgebra.single g (1 : R))
      = c • (1 : MonoidAlgebra R G) := by
  rw [Finset.sum_eq_single (1 : G)]
  · simp [MonoidAlgebra.one_def]
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ 1) h

/-- A sum of scalar multiples of `∑ g, b i g • single g 1` may be reassociated so that the
coefficient of `single g 1` is `∑ i ∈ s, c i * b i g`. -/
theorem sum_smul_sum_single {R G ι : Type*} [CommSemiring R] [Group G] [Fintype G]
    (s : Finset ι) (c : ι → R) (b : ι → G → R) :
    (∑ i ∈ s, c i • (∑ g : G, b i g • MonoidAlgebra.single g (1 : R))) =
      ∑ g : G, (∑ i ∈ s, c i * b i g) • MonoidAlgebra.single g (1 : R) := by
  conv_lhs => enter [2, i, 2]
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]

/-- **The `tildeE χ` sum to `|A|`**: `∑_{χ ∈ Irr A} tildeE χ = (|A| : ℤ[ζ_|A|]) • 1` in
`ℤ[ζ_|A|][A]`. -/
theorem LiftSumTildeE {A : Type*} [Group A] [Fintype A] :
    Finset.sum (Work.CharCore.Irr A).attach (fun x => Work.Hering.AppVII.tildeE x.1 x.2) =
      (Nat.card A : Work.Hering.AppVII.CycloRing (Nat.card A)) •
        (1 : MonoidAlgebra (Work.Hering.AppVII.CycloRing (Nat.card A)) A) := by
  classical
  -- Reassociate the sum so that the coefficient of `single g 1` is displayed explicitly.
  have hkey : (∑ x ∈ (Work.CharCore.Irr A).attach, Work.Hering.AppVII.tildeE x.1 x.2)
      = ∑ g : A, (∑ x ∈ (Work.CharCore.Irr A).attach,
            (Work.CharCore.irrDeg x.1 : Work.Hering.AppVII.CycloRing (Nat.card A)) *
              Work.Hering.AppVII.charLift x.1 x.2 g⁻¹) •
          MonoidAlgebra.single g (1 : Work.Hering.AppVII.CycloRing (Nat.card A)) := by
    simp only [Work.Hering.AppVII.tildeE]
    exact sum_smul_sum_single _ _ _
  -- The coefficient of `single g 1`, computed in `ℂ` along the injective `iota`.
  have hF : ∀ g : A, (∑ x ∈ (Work.CharCore.Irr A).attach,
        (Work.CharCore.irrDeg x.1 : Work.Hering.AppVII.CycloRing (Nat.card A)) *
          Work.Hering.AppVII.charLift x.1 x.2 g⁻¹)
      = if g = 1 then (Nat.card A : Work.Hering.AppVII.CycloRing (Nat.card A)) else 0 := by
    intro g
    apply Work.Hering.AppVII.iota_injective
    -- the sum over `Irr A` instead of its `attach`
    have hattach := Finset.sum_attach (Work.CharCore.Irr A)
      (fun χ : A → ℂ => (Work.CharCore.irrDeg χ : ℂ) * χ g⁻¹)
    -- the decomposition of the regular character
    have hreg : (∑ χ ∈ Work.CharCore.Irr A, (Work.CharCore.irrDeg χ : ℂ) * χ g⁻¹)
        = Work.CharCore.regularChar A g⁻¹ := by
      rw [Work.CharCore.regularChar_eq_sum]
      simp [Finset.sum_apply]
    -- the image of the integral coefficient
    have h1 : (Work.Hering.AppVII.iota (Nat.card A))
        (∑ x ∈ (Work.CharCore.Irr A).attach,
          (Work.CharCore.irrDeg x.1 : Work.Hering.AppVII.CycloRing (Nat.card A)) *
            Work.Hering.AppVII.charLift x.1 x.2 g⁻¹)
        = if g = 1 then (Nat.card A : ℂ) else 0 := by
      rw [map_sum]
      simp only [map_mul, map_natCast, Work.Hering.AppVII.iota_charLift]
      rw [hattach, hreg, Work.CharCore.regularChar]
      simp [inv_eq_one]
    -- the image of `if g = 1 then (|A| : R) else 0`
    have h2 : (Work.Hering.AppVII.iota (Nat.card A))
        (if g = 1 then (Nat.card A : Work.Hering.AppVII.CycloRing (Nat.card A)) else 0)
        = if g = 1 then (Nat.card A : ℂ) else 0 := by
      by_cases h : g = 1 <;> simp [h]
    rw [h1, h2]
  rw [hkey]
  trans ∑ g : A, (if g = 1 then (Nat.card A : Work.Hering.AppVII.CycloRing (Nat.card A))
      else 0) • MonoidAlgebra.single g (1 : Work.Hering.AppVII.CycloRing (Nat.card A))
  · exact Finset.sum_congr rfl (fun g _ => by rw [hF g])
  · exact sum_ite_smul_single _

end Work.NormalComplement.AppVII
