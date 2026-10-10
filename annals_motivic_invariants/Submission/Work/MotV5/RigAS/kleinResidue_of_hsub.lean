import Mathlib
import Submission.Work.MotV5.RigAS.kleinResidue

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# The Klein argument with the extension hypothesis weakened to `hsub`

This file proves `kleinResidue_of_hsub`, the form of the Klein argument in which the hypothesis
`IsPlaceExtension D g τ σS σ h v V` is weakened to the *valuation-ring* compatibility

  `hsub : ∀ x : ↥(asTwistFieldTrue D g τ σS), V (twistIncl D g τ σS x) ≤ 1 ↔ v x ≤ 1`.

The only place where `IsPlaceExtension` entered the original proof
(`Work.MotV5.RigAS.klein_residueAction_nontrivial`, module
`Submission.Work.MotV5.RigAS.kleinResidue`) was through its first conjunct
`V (twistIncl x) = v x`, used solely to conclude that `V` of a nonzero constant is `1`
(`val_algebraMap_const`).  The lemma `val_algebraMap_const_of_hsub` below obtains the same
conclusion from `hsub` and `htriv` alone: for `c ≠ 0`, `hsub` applied to
`algebraMap 𝕜 ↥F c` and to `algebraMap 𝕜 ↥F c⁻¹` gives `V y ≤ 1` and `V y⁻¹ ≤ 1` for the constant
`y = algebraMap 𝕜 ↥L c`, which forces `V y = 1`.

Every other step of the original proof uses only `hstab` and the Klein model, so the proof of
`kleinResidue_of_hsub` is the original proof with the three calls to `val_algebraMap_const`
replaced by calls to `val_algebraMap_const_of_hsub`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.MotV5.RigAS

open Work.MotV5
open scoped WithZero

/-- **The image of a non-zero constant has value `1`**, using only the valuation-ring compatibility
`hsub` of `V` with `v` (rather than the exact extension `V ∘ twistIncl = v`).

For `c ≠ 0`, `hsub` applied to `algebraMap 𝕜 ↥F c` and to `algebraMap 𝕜 ↥F c⁻¹` (both constants of
value `1` under `v`, by `htriv`) gives `V y ≤ 1` and `V y⁻¹ ≤ 1` for `y = algebraMap 𝕜 ↥L c`; since
`y ≠ 0`, `Valuation.one_le_val_iff` upgrades the second to `1 ≤ V y`, whence `V y = 1`. -/
theorem val_algebraMap_const_of_hsub {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]
    (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (v : Valuation ↥(asTwistFieldTrue D g τ σS) (WithZero (Multiplicative ℤ)))
    (V : Valuation ↥(asFieldL D g) (WithZero (Multiplicative ℤ)))
    (htriv : Work.MotV.TrivOn 𝕜 v)
    (hsub : ∀ x : ↥(asTwistFieldTrue D g τ σS),
      V (twistIncl D g τ σS x) ≤ 1 ↔ v x ≤ 1)
    (c : 𝕜) (hc : c ≠ 0) :
    V (algebraMap 𝕜 ↥(asFieldL D g) c) = 1 := by
  -- The two inclusions agree on the constants.
  have heq : ∀ c' : 𝕜, algebraMap 𝕜 ↥(asFieldL D g) c'
      = twistIncl D g τ σS (algebraMap 𝕜 ↥(asTwistFieldTrue D g τ σS) c') := by
    intro c'
    apply Subtype.ext
    rw [twistIncl_coe, coe_algebraMap_L, coe_algebraMap_F]
  have hy_le : V (algebraMap 𝕜 ↥(asFieldL D g) c) ≤ 1 := by
    have := (hsub (algebraMap 𝕜 ↥(asTwistFieldTrue D g τ σS) c)).mpr
      (le_of_eq (htriv c hc))
    rwa [← heq c] at this
  have hi_le : V ((algebraMap 𝕜 ↥(asFieldL D g) c)⁻¹) ≤ 1 := by
    have hc' : c⁻¹ ≠ 0 := inv_ne_zero hc
    have := (hsub (algebraMap 𝕜 ↥(asTwistFieldTrue D g τ σS) c⁻¹)).mpr
      (le_of_eq (htriv c⁻¹ hc'))
    rw [← heq c⁻¹, map_inv₀] at this
    exact this
  have hy_ne : algebraMap 𝕜 ↥(asFieldL D g) c ≠ 0 :=
    fun h => hc ((FaithfulSMul.algebraMap_eq_zero_iff 𝕜 ↥(asFieldL D g)).mp h)
  exact le_antisymm hy_le ((Valuation.one_le_val_iff V hy_ne).mpr hi_le)

/-- **The Klein argument, in the form needed for the ramification-index computation.**

Let `F = asTwistFieldTrue D g τ σS` and `L = asFieldL D g`, with `V` a `ℤᐟ⁰`-valued valuation of
`L` extending the valuation ring of `v` on `F` (`hsub`), trivial on the constants `𝕜` (`htriv`),
and **stable** under the twisted action `σ'` (`hstab`).  Then `σ'` acts non-trivially on the residue
field of `V`: there is `z` with `V z ≤ 1` and `V (σ' z - z) = 1`.

This is `Work.MotV5.RigAS.klein_residueAction_nontrivial` with the hypothesis
`IsPlaceExtension D g τ σS σ h v V` weakened to `hsub` (the extension hypothesis is used in that
proof only to see that `V` of a nonzero constant is `1`, which `hsub` plus `htriv` also give). -/
theorem kleinResidue_of_hsub (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ)
    (v : Valuation ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (WithZero (Multiplicative ℤ)))
    (V : Valuation ↥(Work.MotV5.asFieldL D g) (WithZero (Multiplicative ℤ)))
    (htriv : Work.MotV.TrivOn 𝕜 v)
    (hsub : ∀ x : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
      V (Work.MotV5.RigAS.twistIncl D g τ σS x) ≤ 1 ↔ v x ≤ 1)
    (hstab : ∀ x : ↥(Work.MotV5.asFieldL D g),
      V (Work.MotV5.RigAS.twistSigmaL D g τ σS σ h x) = V x) :
    ∃ z : ↥(Work.MotV5.asFieldL D g),
      V z ≤ 1 ∧ V (Work.MotV5.RigAS.twistSigmaL D g τ σS σ h z - z) = 1 := by
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
      have hsub' : kleinRatioL D g (i + 1) - kleinRatioL D g i * kleinRatioL D g 1
          = (twistSigmaL D g τ σS σ h (kleinRatioL D g i) - kleinRatioL D g i)
            * kleinRatioL D g 1 := by
        rw [hrec]; ring
      rw [hsub', map_mul, hval1, mul_one]
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
      rw [hA]; exact val_algebraMap_const_of_hsub D g τ σS v V htriv hsub D.a ha_ne
    have hB1 : V B = 1 := by
      rw [hB]; exact val_algebraMap_const_of_hsub D g τ σS v V htriv hsub D.b hb_ne
    have hsub2 : V ( (-(A) * (B) * (kleinRatioL D g 2) ^ 2 + (A) ^ 2 * (kleinRatioL D g 4)
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
        have h2 := hsub2
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
      exact val_algebraMap_const_of_hsub D g τ σS v V htriv hsub _ hD.2.2.2
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
