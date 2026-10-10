import Mathlib
import Submission.Work.MotV5.RigAS.PlaceData

set_option linter.unusedVariables false -- v435-speed

/-!
# The Klein argument: a `σ'`-stable place has non-trivial residual action

Let `D` be Klein data with `ASGood D`, `g ∈ {fAS 𝕜, 2 • fAS 𝕜}`, `σS` a fifth-torsion shift
(`KleinData.ShiftOf`), and `h : ASTwistData 𝕜 D g τ σS σ`.  Let `V` be a `ℤᵐ⁰`-valued valuation of
`L = asFieldL D g` extending `v` on `F = asTwistFieldTrue D g τ σS` (`IsPlaceExtension`) and
**stable** under the twisted action `σ' = twistSigmaL D g τ σS σ h`.

**Claim.** `σ'` acts non-trivially on the residue field `κ(V)` of `V`: there is `z` with
`V z ≤ 1` and `V (σ' z - z) = 1`.

*Proof.*  Put `rᵢ = κᵢ/κ₀` for the Klein ratios `κᵢ = kleinCoord D (Kb 𝕜) i`; these lie in
`kleinField D ≤ L`.  On `kleinField D` the twisted action equals `σS`, so from
`σS (κᵢ) = λ κ_{i+1}` (`hσS`) we get

  `σ' (rᵢ) = r_{i+1} / r₁`,   hence   `r_{i+1} = σ'(rᵢ) · r₁`.

Since `V` is `σ'`-stable, `V (r_{i+1}) = V (r_{i+1}) = V (rᵢ) · V (r₁)`, and `r₀ = 1`, so
`V (r₁)^5 = V (r₄) · V (r₁) = V (r₀) = 1`; as `ℤᵐ⁰` is torsion-free, `V (r₁) = 1`, and then
`V (rᵢ) = 1` for all `i`.

Now suppose the residual action of `σ'` were trivial: `V (σ' z - z) < 1` for all `z` with
`V z ≤ 1`.  Applied to `z = rᵢ` this says `r_{i+1} ≡ rᵢ · r₁ (mod 𝔪_V)`, whence `rᵢ ≡ r₁ⁱ` for
all `i`.  The Pfaffian relation `p₁(a,b,κ) = 0` of the Klein model
(`KleinData.Good.klein_eq`), divided by `κ₀²`, reads

  `-ab r₂² + a² r₄ - b² r₁ r₃ = 0`.

Reducing it modulo `𝔪_V` and substituting `rᵢ ≡ r₁ⁱ` gives `r₁⁴ (a² - ab - b²) ≡ 0 (mod 𝔪_V)`,
i.e. `V (r₁⁴ (a² - ab - b²)) < 1`.  But `V (r₁) = 1` and `a² - ab - b²` is (the image of) a
**non-zero constant** (`ASGood`), so `V (a² - ab - b²) = 1` and the product has value `1` —
contradiction.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.MotV5.RigAS

open Work.MotV5
open scoped WithZero

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-- **The fifth power map of `ℤᵐ⁰` is injective at `1`.** -/
theorem zhat_pow_five_eq_one {x : ℤᵐ⁰} (h : x ^ 5 = 1) : x = 1 := by
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : (5 : ℕ) ≠ 0)] at h
    exact zero_ne_one h
  rcases lt_trichotomy x 1 with hlt | heq | hgt
  · have h1 : x ^ 5 < 1 := by
      have := pow_lt_pow_left₀ hlt (le_of_lt (pos_iff_ne_zero.mpr hx0))
        (by norm_num : (5 : ℕ) ≠ 0)
      simpa using this
    rw [h] at h1
    exact absurd h1 (lt_irrefl 1)
  · exact heq
  · have h1 : 1 < x ^ 5 := one_lt_pow₀ hgt (by norm_num : (5 : ℕ) ≠ 0)
    rw [h] at h1
    exact absurd h1 (lt_irrefl 1)

/-- The `i`-th Klein ratio `κᵢ/κ₀`, as an element of `L = asFieldL D g`. -/
noncomputable def kleinRatioL (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) (i : Fin 5) :
    ↥(asFieldL D g) :=
  ⟨Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0,
    (le_sup_left : Work.MotV5.kleinField D ≤ asFieldL D g)
      (IntermediateField.subset_adjoin _ _ (Set.mem_range_self i))⟩

@[simp]
theorem kleinRatioL_coe (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) (i : Fin 5) :
    ((kleinRatioL D g i : ↥(asFieldL D g)) : Work.MotV.Om D)
      = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 :=
  rfl

@[simp]
theorem kleinRatioL_div_coe (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) (i j : Fin 5) :
    (((kleinRatioL D g i) / (kleinRatioL D g j) : ↥(asFieldL D g)) : Work.MotV.Om D)
      = ((kleinRatioL D g i : ↥(asFieldL D g)) : Work.MotV.Om D)
        / ((kleinRatioL D g j : ↥(asFieldL D g)) : Work.MotV.Om D) :=
  rfl

/-- **The Klein ratios lie in `kleinField D`.** -/
theorem kleinRatioL_mem_kleinField (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) (i : Fin 5) :
    (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
      ∈ Work.MotV5.kleinField D :=
  IntermediateField.subset_adjoin _ _ (Set.mem_range_self i)

/-- `r₀ = κ₀/κ₀ = 1`. -/
theorem kleinRatioL_zero (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (g : RatFunc 𝕜) :
    kleinRatioL D g 0 = 1 := by
  apply Subtype.ext
  show (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0
      : Work.MotV.Om D) = 1
  exact div_self (hD.coord0_ne (Work.MotV.Kb 𝕜))

/-- **The shift formula**: `σ'(rᵢ) = r_{i+1}/r₁` in `L`. -/
theorem kleinRatioL_shift (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (g : RatFunc 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ) (i : Fin 5) :
    twistSigmaL D g τ σS σ h (kleinRatioL D g i)
      = kleinRatioL D g (i + 1) / kleinRatioL D g 1 := by
  obtain ⟨lam, hlam, hsh⟩ := h.hσS
  apply Subtype.ext
  rw [twistSigmaL_coe, kleinRatioL_div_coe, kleinRatioL_coe, kleinRatioL_coe, kleinRatioL_coe]
  -- goal: asTwistAction (κ_i/κ_0) = (κ_{i+1}/κ_0)/(κ_1/κ_0)
  rw [asTwistAction, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    h.hτk _ (kleinRatioL_mem_kleinField D g i), map_div₀, hsh i, hsh 0,
    mul_div_mul_left _ _ hlam]
  exact (div_div_div_cancel_right₀ (hD.coord0_ne (Work.MotV.Kb 𝕜)) _ _).symm

/-- `r₁ ≠ 0`. -/
theorem kleinRatioL_one_ne_zero (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (g : RatFunc 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ) :
    kleinRatioL D g 1 ≠ 0 := by
  intro hzero
  have h0 := kleinRatioL_shift D hD g τ σS σ h 0
  rw [kleinRatioL_zero D hD g, map_one, hzero, div_zero] at h0
  exact one_ne_zero h0

/-- **The recurrence** `r_{i+1} = σ'(rᵢ) · r₁`. -/
theorem kleinRatioL_rec (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (g : RatFunc 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ) (i : Fin 5) :
    kleinRatioL D g (i + 1) = twistSigmaL D g τ σS σ h (kleinRatioL D g i) * kleinRatioL D g 1 := by
  have hshift := kleinRatioL_shift D hD g τ σS σ h i
  have h1 := kleinRatioL_one_ne_zero D hD g τ σS σ h
  rw [hshift, div_mul_cancel₀ _ h1]

/-- **`V (rᵢ) = 1` for every `i`, for a `σ'`-stable place.** -/
theorem kleinRatioL_val_eq_one (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (g : RatFunc 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ)
    (V : Valuation ↥(asFieldL D g) (WithZero (Multiplicative ℤ)))
    (hstab : ∀ x : ↥(asFieldL D g), V (twistSigmaL D g τ σS σ h x) = V x) :
    ∀ i : Fin 5, V (kleinRatioL D g i) = 1 := by
  have hstep : ∀ i : Fin 5, V (kleinRatioL D g (i + 1))
      = V (kleinRatioL D g i) * V (kleinRatioL D g 1) := by
    intro i
    rw [kleinRatioL_rec D hD g τ σS σ h i, map_mul, hstab]
  have h2 : V (kleinRatioL D g 2) = V (kleinRatioL D g 1) ^ 2 := by
    have h1 := hstep 1
    rw [show (1 : Fin 5) + 1 = 2 from by decide] at h1
    rw [pow_two, h1]
  have h3 : V (kleinRatioL D g 3) = V (kleinRatioL D g 1) ^ 3 := by
    have h1 := hstep 2
    rw [show (2 : Fin 5) + 1 = 3 from by decide, h2] at h1
    rw [← pow_succ] at h1
    exact h1
  have h4 : V (kleinRatioL D g 4) = V (kleinRatioL D g 1) ^ 4 := by
    have h1 := hstep 3
    rw [show (3 : Fin 5) + 1 = 4 from by decide, h3] at h1
    rw [← pow_succ] at h1
    exact h1
  have h0 : V (kleinRatioL D g 0) = V (kleinRatioL D g 1) ^ 5 := by
    have h1 := hstep 4
    rw [show (4 : Fin 5) + 1 = 0 from by decide, h4] at h1
    rw [← pow_succ] at h1
    exact h1
  have hroot : V (kleinRatioL D g 1) ^ 5 = 1 := by
    rw [← h0, kleinRatioL_zero D hD g, map_one]
  have hV1 : V (kleinRatioL D g 1) = 1 := zhat_pow_five_eq_one hroot
  intro i
  fin_cases i
  · show V (kleinRatioL D g 0) = 1
    rw [kleinRatioL_zero D hD g, map_one]
  · show V (kleinRatioL D g 1) = 1
    exact hV1
  · show V (kleinRatioL D g 2) = 1
    rw [h2, hV1]; norm_num
  · show V (kleinRatioL D g 3) = 1
    rw [h3, hV1]; norm_num
  · show V (kleinRatioL D g 4) = 1
    rw [h4, hV1]; norm_num

/-- The coercion `↥(asFieldL D g) → Om D` commutes with the constants. -/
theorem coe_algebraMap_L (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) (c : 𝕜) :
    ((algebraMap 𝕜 ↥(asFieldL D g) c : ↥(asFieldL D g)) : Work.MotV.Om D)
      = algebraMap 𝕜 (Work.MotV.Om D) c := by
  rw [IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) ↥(asFieldL D g)]
  change algebraMap ↥(asFieldL D g) (Work.MotV.Om D)
      (algebraMap (RatFunc 𝕜) ↥(asFieldL D g) (algebraMap 𝕜 (RatFunc 𝕜) c))
    = algebraMap 𝕜 (Work.MotV.Om D) c
  rw [← IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(asFieldL D g) (Work.MotV.Om D),
    ← IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Om D)]

/-- The coercion `↥(asTwistFieldTrue D g τ σS) → Om D` commutes with the constants. -/
theorem coe_algebraMap_F (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D) (c : 𝕜) :
    ((algebraMap 𝕜 ↥(asTwistFieldTrue D g τ σS) c : ↥(asTwistFieldTrue D g τ σS))
        : Work.MotV.Om D) = algebraMap 𝕜 (Work.MotV.Om D) c := by
  rw [IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) ↥(asTwistFieldTrue D g τ σS)]
  change algebraMap ↥(asTwistFieldTrue D g τ σS) (Work.MotV.Om D)
      (algebraMap (RatFunc 𝕜) ↥(asTwistFieldTrue D g τ σS) (algebraMap 𝕜 (RatFunc 𝕜) c))
    = algebraMap 𝕜 (Work.MotV.Om D) c
  rw [← IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(asTwistFieldTrue D g τ σS)
        (Work.MotV.Om D),
    ← IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Om D)]

/-- **The image of a non-zero constant has value `1`.** -/
theorem val_algebraMap_const (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (v : Valuation ↥(asTwistFieldTrue D g τ σS) (WithZero (Multiplicative ℤ)))
    (V : Valuation ↥(asFieldL D g) (WithZero (Multiplicative ℤ)))
    (htriv : Work.MotV.TrivOn 𝕜 v)
    (hVext : ∀ x : ↥(asTwistFieldTrue D g τ σS), V (twistIncl D g τ σS x) = v x)
    (c : 𝕜) (hc : c ≠ 0) :
    V (algebraMap 𝕜 ↥(asFieldL D g) c) = 1 := by
  have heq : algebraMap 𝕜 ↥(asFieldL D g) c
      = twistIncl D g τ σS (algebraMap 𝕜 ↥(asTwistFieldTrue D g τ σS) c) := by
    apply Subtype.ext
    rw [twistIncl_coe, coe_algebraMap_L, coe_algebraMap_F]
  rw [heq, hVext, htriv c hc]

/-- **The Pfaffian relation of the Klein model, in terms of the ratios `rᵢ = κᵢ/κ₀`.** -/
theorem kleinRelationOm (D : Work.MotV.KleinData 𝕜) (hD : D.Good) :
    -(algebraMap 𝕜 (Work.MotV.Om D) D.a) * (algebraMap 𝕜 (Work.MotV.Om D) D.b)
        * (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 2 / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) ^ 2
      + (algebraMap 𝕜 (Work.MotV.Om D) D.a) ^ 2
          * (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 4 / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
      - (algebraMap 𝕜 (Work.MotV.Om D) D.b) ^ 2
          * (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 1 / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
          * (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 3 / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
      = 0 := by
  have hrel := hD.klein_eq (Work.MotV.Kb 𝕜) 1
  rw [Work.MotK.kleinP_one, Work.MotK.kleinP1] at hrel
  have hκ0 : Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 ≠ 0 := hD.coord0_ne _
  have hident : -(algebraMap 𝕜 (Work.MotV.Om D) D.a) * (algebraMap 𝕜 (Work.MotV.Om D) D.b)
        * (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 2 / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) ^ 2
      + (algebraMap 𝕜 (Work.MotV.Om D) D.a) ^ 2
          * (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 4 / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
      - (algebraMap 𝕜 (Work.MotV.Om D) D.b) ^ 2
          * (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 1 / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
          * (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 3 / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
      = ( -(algebraMap 𝕜 (Work.MotV.Om D) D.a) * (algebraMap 𝕜 (Work.MotV.Om D) D.b)
            * (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 2) ^ 2
          + (algebraMap 𝕜 (Work.MotV.Om D) D.a) ^ 2 * (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
              * (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 4)
          - (algebraMap 𝕜 (Work.MotV.Om D) D.b) ^ 2 * (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 1)
              * (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 3) )
        * (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)⁻¹ ^ 2 := by
    field_simp
  rw [hident, hrel, zero_mul]

/-- **The Pfaffian relation of the Klein model in `L`**, in terms of `rᵢ = κᵢ/κ₀`. -/
theorem kleinRelationL (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (g : RatFunc 𝕜) :
    -(algebraMap 𝕜 ↥(asFieldL D g) D.a) * (algebraMap 𝕜 ↥(asFieldL D g) D.b)
        * (kleinRatioL D g 2) ^ 2
      + (algebraMap 𝕜 ↥(asFieldL D g) D.a) ^ 2 * (kleinRatioL D g 4)
      - (algebraMap 𝕜 ↥(asFieldL D g) D.b) ^ 2 * (kleinRatioL D g 1) * (kleinRatioL D g 3)
      = 0 := by
  apply Subtype.ext
  push_cast
  rw [kleinRatioL_coe, kleinRatioL_coe, kleinRatioL_coe, kleinRatioL_coe,
    coe_algebraMap_L, coe_algebraMap_L]
  exact kleinRelationOm D hD

/-- **The Klein argument.**  If `V` is a `σ'`-stable prolongation of `v` to `L = asFieldL D g`,
then `σ'` acts non-trivially on the residue field of `V`: there is `z` with `V z ≤ 1` and
`V (σ' z - z) = 1`.  The proof uses the Pfaffian relation `p₁(a,b,κ) = 0` of the Klein model and
`a² - ab - b² ≠ 0` (which is part of `ASGood`). -/
theorem klein_residueAction_nontrivial (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ)
    (v : Valuation ↥(asTwistFieldTrue D g τ σS) (WithZero (Multiplicative ℤ)))
    (V : Valuation ↥(asFieldL D g) (WithZero (Multiplicative ℤ)))
    (htriv : Work.MotV.TrivOn 𝕜 v)
    (hV : IsPlaceExtension D g τ σS σ h v V)
    (hstab : ∀ x : ↥(asFieldL D g), V (twistSigmaL D g τ σS σ h x) = V x) :
    ∃ z : ↥(asFieldL D g), V z ≤ 1 ∧ V (twistSigmaL D g τ σS σ h z - z) = 1 := by
  have hval := kleinRatioL_val_eq_one D hD.1 g τ σS σ h V hstab
  have hval1 : V (kleinRatioL D g 1) = 1 := hval 1
  have ha_ne : D.a ≠ 0 := fun h0 => hD.1.ab_ne (by rw [h0, zero_mul])
  have hb_ne : D.b ≠ 0 := fun h0 => hD.1.ab_ne (by rw [h0, mul_zero])
  have key : ¬ (∀ z : ↥(asFieldL D g),
      V z ≤ 1 → V (twistSigmaL D g τ σS σ h z - z) < 1) := by
    intro htriv'
    -- ### congruence steps
    have hstep : ∀ i : Fin 5,
        V (kleinRatioL D g (i + 1) - kleinRatioL D g i * kleinRatioL D g 1) < 1 := by
      intro i
      have hrec := kleinRatioL_rec D hD.1 g τ σS σ h i
      have hsub : kleinRatioL D g (i + 1) - kleinRatioL D g i * kleinRatioL D g 1
          = (twistSigmaL D g τ σS σ h (kleinRatioL D g i) - kleinRatioL D g i)
            * kleinRatioL D g 1 := by
        rw [hrec]; ring
      rw [hsub, map_mul, hval1, mul_one]
      exact htriv' _ (le_of_eq (hval i))
    have hc2 : V (kleinRatioL D g 2 - kleinRatioL D g 1 ^ 2) < 1 := by
      have h1 := hstep 1
      rw [show (1 : Fin 5) + 1 = 2 from by decide] at h1
      rw [pow_two]
      exact h1
    have hc3 : V (kleinRatioL D g 3 - kleinRatioL D g 1 ^ 3) < 1 := by
      have h1 := hstep 2
      rw [show (2 : Fin 5) + 1 = 3 from by decide] at h1
      have hsplit : kleinRatioL D g 3 - kleinRatioL D g 1 ^ 3
          = (kleinRatioL D g 3 - kleinRatioL D g 2 * kleinRatioL D g 1)
            + (kleinRatioL D g 2 * kleinRatioL D g 1 - kleinRatioL D g 1 ^ 3) := by ring
      rw [hsplit]
      refine Valuation.map_add_lt V h1 ?_
      have hfac : kleinRatioL D g 2 * kleinRatioL D g 1 - kleinRatioL D g 1 ^ 3
          = (kleinRatioL D g 2 - kleinRatioL D g 1 ^ 2) * kleinRatioL D g 1 := by ring
      rw [hfac, map_mul, hval1, mul_one]
      exact hc2
    have hc4 : V (kleinRatioL D g 4 - kleinRatioL D g 1 ^ 4) < 1 := by
      have h1 := hstep 3
      rw [show (3 : Fin 5) + 1 = 4 from by decide] at h1
      have hsplit : kleinRatioL D g 4 - kleinRatioL D g 1 ^ 4
          = (kleinRatioL D g 4 - kleinRatioL D g 3 * kleinRatioL D g 1)
            + (kleinRatioL D g 3 * kleinRatioL D g 1 - kleinRatioL D g 1 ^ 4) := by ring
      rw [hsplit]
      refine Valuation.map_add_lt V h1 ?_
      have hfac : kleinRatioL D g 3 * kleinRatioL D g 1 - kleinRatioL D g 1 ^ 4
          = (kleinRatioL D g 3 - kleinRatioL D g 1 ^ 3) * kleinRatioL D g 1 := by ring
      rw [hfac, map_mul, hval1, mul_one]
      exact hc3
    -- ### the Pfaffian relation and the congruence substitution
    have hrel := kleinRelationL D hD.1 g
    set A := algebraMap 𝕜 ↥(asFieldL D g) D.a with hA
    set B := algebraMap 𝕜 ↥(asFieldL D g) D.b with hB
    have hA1 : V A = 1 := by
      rw [hA]; exact val_algebraMap_const D g τ σS v V htriv hV.1 D.a ha_ne
    have hB1 : V B = 1 := by
      rw [hB]; exact val_algebraMap_const D g τ σS v V htriv hV.1 D.b hb_ne
    have hsub : V ( (-(A) * (B) * (kleinRatioL D g 2) ^ 2 + (A) ^ 2 * (kleinRatioL D g 4)
            - (B) ^ 2 * (kleinRatioL D g 1) * (kleinRatioL D g 3))
          - (kleinRatioL D g 1) ^ 4 * ((A) ^ 2 - (A) * (B) - (B) ^ 2) ) < 1 := by
      have t1 : V ((A) ^ 2 * (kleinRatioL D g 4 - (kleinRatioL D g 1) ^ 4)) < 1 := by
        rw [map_mul, map_pow, hA1, one_pow, one_mul]
        exact hc4
      have hle2 : V (kleinRatioL D g 2 + (kleinRatioL D g 1) ^ 2) ≤ 1 := by
        refine le_trans (Valuation.map_add V _ _) (le_of_eq ?_)
        rw [hval 2, map_pow, hval1, one_pow, max_self]
      have t2 : V ((A) * (B) * ((kleinRatioL D g 2) ^ 2
            - ((kleinRatioL D g 1) ^ 2) ^ 2)) < 1 := by
        have hfac : (kleinRatioL D g 2) ^ 2 - ((kleinRatioL D g 1) ^ 2) ^ 2
            = (kleinRatioL D g 2 - (kleinRatioL D g 1) ^ 2)
              * (kleinRatioL D g 2 + (kleinRatioL D g 1) ^ 2) := by ring
        rw [hfac, map_mul, map_mul, map_mul, hA1, hB1, one_mul, one_mul]
        have h0 : (0 : ℤᵐ⁰) ≤ V (kleinRatioL D g 2 - (kleinRatioL D g 1) ^ 2) := zero_le
        have hb : V (kleinRatioL D g 2 - (kleinRatioL D g 1) ^ 2)
              * V (kleinRatioL D g 2 + (kleinRatioL D g 1) ^ 2)
            ≤ V (kleinRatioL D g 2 - (kleinRatioL D g 1) ^ 2) := by
          simpa using mul_le_mul_of_nonneg_left hle2 h0
        exact lt_of_le_of_lt hb hc2
      have t3 : V ((B) ^ 2 * ((kleinRatioL D g 1) * (kleinRatioL D g 3)
            - (kleinRatioL D g 1) ^ 4)) < 1 := by
        have hfac : (kleinRatioL D g 1) * (kleinRatioL D g 3) - (kleinRatioL D g 1) ^ 4
            = kleinRatioL D g 1 * (kleinRatioL D g 3 - (kleinRatioL D g 1) ^ 3) := by ring
        rw [hfac, map_mul, map_pow, map_mul, hB1, one_pow, one_mul, hval1, one_mul]
        exact hc3
      have hmid : V ((A) ^ 2 * (kleinRatioL D g 4 - (kleinRatioL D g 1) ^ 4)
            - (A) * (B) * ((kleinRatioL D g 2) ^ 2 - ((kleinRatioL D g 1) ^ 2) ^ 2)) < 1 :=
        lt_of_le_of_lt (Valuation.map_sub V _ _) (max_lt t1 t2)
      have hsp : (-(A) * (B) * (kleinRatioL D g 2) ^ 2 + (A) ^ 2 * (kleinRatioL D g 4)
            - (B) ^ 2 * (kleinRatioL D g 1) * (kleinRatioL D g 3))
          - (kleinRatioL D g 1) ^ 4 * ((A) ^ 2 - (A) * (B) - (B) ^ 2)
          = (A) ^ 2 * (kleinRatioL D g 4 - (kleinRatioL D g 1) ^ 4)
            - (A) * (B) * ((kleinRatioL D g 2) ^ 2 - ((kleinRatioL D g 1) ^ 2) ^ 2)
            - (B) ^ 2 * ((kleinRatioL D g 1) * (kleinRatioL D g 3)
                - (kleinRatioL D g 1) ^ 4) := by ring
      rw [hsp]
      exact lt_of_le_of_lt (Valuation.map_sub V _ _) (max_lt hmid t3)
    -- ### conclude
    have hX : V ((A) ^ 2 - (A) * (B) - (B) ^ 2) < 1 := by
      have h1 : V ((kleinRatioL D g 1) ^ 4 * ((A) ^ 2 - (A) * (B) - (B) ^ 2)) < 1 := by
        have h2 := hsub
        rw [hrel, zero_sub] at h2
        rwa [Valuation.map_neg V] at h2
      rw [map_mul, map_pow, hval1, one_pow, one_mul] at h1
      exact h1
    have hconst : V ((A) ^ 2 - (A) * (B) - (B) ^ 2) = 1 := by
      have hXeq : (A) ^ 2 - (A) * (B) - (B) ^ 2
          = algebraMap 𝕜 ↥(asFieldL D g) (D.a ^ 2 - D.a * D.b - D.b ^ 2) := by
        rw [hA, hB]
        simp only [map_sub, map_mul, map_pow]
      rw [hXeq]
      exact val_algebraMap_const D g τ σS v V htriv hV.1 _ hD.2.2.2
    rw [hconst] at hX
    exact lt_irrefl 1 hX
  obtain ⟨z, hz⟩ := not_forall.mp key
  rw [not_imp] at hz
  obtain ⟨hz1, hz2⟩ := hz
  refine ⟨z, hz1, le_antisymm ?_ (not_lt.mp hz2)⟩
  calc V (twistSigmaL D g τ σS σ h z - z)
      ≤ max (V (twistSigmaL D g τ σS σ h z)) (V z) := Valuation.map_sub V _ _
    _ ≤ 1 := max_le (by rw [hstab z]; exact hz1) hz1

end Work.MotV5.RigAS
