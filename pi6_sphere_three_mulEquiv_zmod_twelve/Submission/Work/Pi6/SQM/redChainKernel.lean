import Mathlib
import Submission.Work.Pi6.SQM.RedDefs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `Pi6/SQM/redChainKernel`

The two arithmetic facts about the coefficientwise reduction `redChain : C_m(Y;ℤ) → C_m(Y;𝔽₂)`
of integral chains (`Work.Pi6.SQM.RedDefs`) that the `SQM` area uses:

* every integral chain whose mod-2 reduction vanishes is **twice** an integral chain
  (the reduction is `ℤ/2`-injective on `2`-divisible... more precisely its kernel is `2·C_m`);
* the integral chains in a fixed degree are **`2`-torsion-free**, `2 • x = 0 → x = 0`.

Both are the statement that, under the identification `eZ : C_m(Y;ℤ) ≅ (Y_m →₀ ℤ)` of the chains
with finitely supported integral families on the `m`-simplices, `redChain` becomes the
coefficientwise reduction `ℤ → 𝔽₂`.  That identification is `rck_mapRange` below; the two
conclusions are then the elementary facts `((n:ℤ):𝔽₂) = 0 ↔ 2 ∣ n` and `2 * n = 0 ↔ n = 0`
for the coefficients.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff chainC cochainC genElt)

namespace RCK

/-- The reduction `ℤ → 𝔽₂` as a `ℤ`-linear map. -/
def castF2 : ℤ →ₗ[ℤ] F2 := LinearMap.toSpanSingleton ℤ F2 1

theorem castF2_apply (z : ℤ) : castF2 z = (z : F2) := by
  rw [castF2, LinearMap.toSpanSingleton_apply, zsmul_eq_mul, mul_one]

/-- The identification of the integral `m`-chains with finitely supported integral families on
the `m`-simplices, as a `ℤ`-linear equivalence. -/
noncomputable def eZLE (Y : SSet) (m : ℕ) :
    (↥((chainC ℤ Y).X m)) ≃ₗ[ℤ] (Y _⦋m⦌ →₀ ℤ) := Iso.toLinearEquiv (eZ Y m)

/-- The coefficientwise reduction agrees with `redChain` on generators. -/
theorem genCast (Y : SSet) (m : ℕ) (σ : Y _⦋m⦌) :
    (Iso.toLinearEquiv (eF Y m)) (genElt F2 Y σ)
      = Finsupp.mapRange.linearMap castF2 ((Iso.toLinearEquiv (eZ Y m)) (genElt ℤ Y σ)) := by
  rw [Iso.toLinearEquiv_apply, eF_genElt, Iso.toLinearEquiv_apply, eZ_genElt,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, castF2_apply]
  simp

/-- `redChain` followed by the coordinates `eF`, as a `ℤ`-linear map. -/
noncomputable def redChainThenE (Y : SSet) (m : ℕ) :
    (↥((chainC ℤ Y).X m)) →ₗ[ℤ] (Y _⦋m⦌ →₀ F2) :=
  (((Iso.toLinearEquiv (eF Y m)).toLinearMap).restrictScalars ℤ).comp (redChain Y m)

/-- The coordinatewise reduction `ℤ → 𝔽₂`, as a `ℤ`-linear map. -/
noncomputable def coordCast (Y : SSet) (m : ℕ) :
    (↥((chainC ℤ Y).X m)) →ₗ[ℤ] (Y _⦋m⦌ →₀ F2) :=
  (Finsupp.mapRange.linearMap castF2).comp ((eZLE Y m).toLinearMap)

/-- **`redChain` is the coefficientwise reduction**: under the identifications `eZ`, `eF` of the
integral (resp. mod-2) chains with finitely supported families on the simplices, the reduction of
chains is exactly the reduction of the coefficients. -/
theorem mapRange_redChain (Y : SSet) (m : ℕ) (x : ↥((chainC ℤ Y).X m)) :
    (Iso.toLinearEquiv (eF Y m)) (redChain Y m x)
      = Finsupp.mapRange.linearMap castF2 (eZLE Y m x) := by
  have h : redChainThenE Y m = coordCast Y m := by
    apply chain_ext
    intro σ
    show (Iso.toLinearEquiv (eF Y m)) (redChain Y m (genElt ℤ Y σ))
      = (Finsupp.mapRange.linearMap castF2) ((Iso.toLinearEquiv (eZ Y m)) (genElt ℤ Y σ))
    rw [redChain_genElt]
    exact genCast Y m σ
  exact LinearMap.congr_fun h x

end RCK

open RCK

/-- The kernel of the reduction of integral chains mod `2` is `2 · C_m(Y;ℤ)`, and the integral
`m`-chains are torsion-free. -/
theorem redChainKernel {Y : SSet} (m : ℕ) :
    (∀ x : ↥((Work.Cohomology.chainC ℤ Y).X m), redChain Y m x = 0 →
        ∃ y : ↥((Work.Cohomology.chainC ℤ Y).X m), (2 : ℤ) • y = x) ∧
      (∀ x : ↥((Work.Cohomology.chainC ℤ Y).X m), (2 : ℤ) • x = 0 → x = 0) := by
  constructor
  · intro x hx
    have h1 : Finsupp.mapRange.linearMap castF2 (eZLE Y m x) = 0 := by
      rw [← mapRange_redChain Y m x, hx, map_zero]
    have hdiv : ∀ σ : Y _⦋m⦌, (2 : ℤ) ∣ eZLE Y m x σ := by
      intro σ
      have h3 : (Finsupp.mapRange.linearMap castF2 (eZLE Y m x)) σ = 0 := by rw [h1]; rfl
      rw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, castF2_apply] at h3
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (eZLE Y m x σ) 2).mp h3
    let d : Y _⦋m⦌ →₀ ℤ := (eZLE Y m x).mapRange (fun z : ℤ => z / 2) (by simp)
    have hd : (2 : ℤ) • d = eZLE Y m x := by
      ext σ
      rw [Finsupp.smul_apply]
      show (2 : ℤ) • (d σ) = eZLE Y m x σ
      rw [show d σ = eZLE Y m x σ / 2 from by simp [d, Finsupp.mapRange_apply], zsmul_eq_mul]
      exact two_mul_ediv_two _ (hdiv σ)
    refine ⟨(eZLE Y m).symm d, ?_⟩
    rw [← (eZLE Y m).symm_apply_apply x, ← hd]
    exact (map_zsmul ((eZLE Y m).symm) (2 : ℤ) d).symm
  · intro x hx
    have h1 : (2 : ℤ) • (eZLE Y m x) = 0 := by
      rw [← map_zsmul (eZLE Y m) (2 : ℤ) x, hx, map_zero]
    have hzero : eZLE Y m x = 0 := by
      ext σ
      have h3 : ((2 : ℤ) • eZLE Y m x) σ = 0 := by rw [h1]; rfl
      rw [Finsupp.smul_apply] at h3
      simpa using h3
    rw [← (eZLE Y m).symm_apply_apply x, hzero, map_zero]

end

end Work.Pi6.SQM
