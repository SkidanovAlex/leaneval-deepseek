import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotV.kbAlgEquivExtend
import Submission.Work.MotV.coeffAutSemilinear
import Submission.Work.MotV.restrict_algEquiv
import Submission.Work.MotT.twistFieldTK_regular

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

namespace Work.MotV

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

set_option maxHeartbeats 1600000

noncomputable section

/-- Node NAT (naturality): a `𝕜`-algebra isomorphism `θ : F_{h₁} ≃ₐ[𝕜] F_{h₂}` of two twist fields
reduces to a `𝕜(t)`-linear isomorphism between `F_{h₁}` and the twist field of `α h₂`, for some
`𝕜`-automorphism `α` of `𝕜(t)`.

Route.
1. `Work.MotV.restrict_algEquiv` (node NAT, surjectivity half, using REG) gives the `𝕜`-algebra
   automorphism `φ : K ≃ₐ[𝕜] K` with `θ (algebraMap c) = algebraMap (φ c)`; we exhibit `α := φ⁻¹`.
2. `Work.MotV.kbAlgEquivExtend` extends `α` to a `𝕜`-algebra automorphism `τ` of `Kb 𝕜`, and
   `Work.MotV.coeffAutSemilinear` gives the coefficient action `g` of `τ` on `Om D`, fixing the
   Klein ratios `κ_i/κ_0` and sending `twCoord D h i` to `(g (root5 h))^{-i} κ_i/κ_0`.
3. The T-twist `κ_i/κ_0 ↦ ζ^i κ_i/κ_0` (`Work.MotT.exists_kleinScaling`, i.e. `T_diag`) with
   `ζ = τ (root5 h₂)/root5 (α h₂)`, `ζ^5 = 1`, corrects the fifth-root mismatch: with
   `δ` the corresponding `Kb 𝕜`-automorphism of `Om D`,
   `δ (g (twCoord D h₂ i)) = twCoord D (α h₂) i`.
4. Hence `x ↦ δ (g (θ x))` is a `K`-algebra homomorphism `F_{h₁} →ₐ[K] F_{α h₂}`: it is additive,
   multiplicative, and `K`-linear since `(δ ∘ g)(algebraMap (φ c)) = algebraMap c`.  It is injective
   (a composite of injections) and surjective (the target is the `K`-adjoin of the images
   `twCoord D (α h₂) i = δ (g (twCoord D h₂ i))` and of `K`). -/
theorem twist_natural {𝕜 : Type} [Field 𝕜] (D : KleinData 𝕜) (hD : D.Good)
    (hk : ringChar 𝕜 ≠ 5) (h₁ h₂ : RatFunc 𝕜) (h₁0 : h₁ ≠ 0) (h₂0 : h₂ ≠ 0)
    (θ : twistFieldT D h₁ ≃ₐ[𝕜] twistFieldT D h₂)
    (hθ : ∀ c : RatFunc 𝕜, ∃ d, θ (algebraMap (RatFunc 𝕜) _ c) = algebraMap (RatFunc 𝕜) _ d) :
    ∃ α : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜,
      Nonempty (twistFieldT D h₁ ≃ₐ[RatFunc 𝕜] twistFieldT D (α h₂)) := by
  -- Step 1: the restriction of `θ` to `K` is a `𝕜`-algebra automorphism of `K`
  obtain ⟨φ, hφ⟩ := restrict_algEquiv D hD hk h₁0 h₂0 θ hθ
  refine ⟨φ.symm, ?_⟩
  -- Step 2: extend `α = φ⁻¹` to `K̄` and take the coefficient action on `Ω = K̄(E)`
  obtain ⟨τ, hτ⟩ := kbAlgEquivExtend φ.symm
  obtain ⟨g, hgKb, hgRatio, hgTw⟩ := coeffAutSemilinear D τ
  -- the fifth roots of `h₂` and of `φ⁻¹ h₂` do not vanish
  have hroot5_ne : ∀ {g : RatFunc 𝕜}, g ≠ 0 → root5 g ≠ 0 := by
    intro g hg h0
    have h5 := root5_spec g
    rw [h0, zero_pow (by norm_num : (5 : ℕ) ≠ 0)] at h5
    exact hg ((algebraMap (RatFunc 𝕜) (Kb 𝕜)).injective (by rw [map_zero]; exact h5.symm))
  have hφs_ne : φ.symm h₂ ≠ 0 := by
    intro h0
    exact h₂0 (by simpa using congrArg φ h0)
  -- the Kummer ratio of the two fifth roots
  set ζ : Kb 𝕜 := τ (root5 h₂) / root5 (φ.symm h₂) with hζdef
  have hτw₂ : τ (root5 h₂) ≠ 0 := fun h0 =>
    hroot5_ne h₂0 (τ.injective (by simpa using h0))
  have hζ5 : ζ ^ 5 = 1 := by
    rw [hζdef, div_pow, ← map_pow, root5_spec h₂, hτ h₂, root5_spec (φ.symm h₂)]
    exact div_self (fun h0 => hφs_ne ((algebraMap (RatFunc 𝕜) (Kb 𝕜)).injective
      (by rw [h0, map_zero])))
  obtain ⟨δ, hδ⟩ := Work.MotT.exists_kleinScaling D hD ζ hζ5
  -- `δ` fixes the constants `K̄`
  have hδc : ∀ y : Kb 𝕜, δ (algebraMap (Kb 𝕜) (Om D) y) = algebraMap (Kb 𝕜) (Om D) y :=
    fun y => δ.commutes y
  -- the image of `ζ` in `Ω`
  have hζcoe : algebraMap (Kb 𝕜) (Om D) ζ
      = algebraMap (Kb 𝕜) (Om D) (τ (root5 h₂))
        * (algebraMap (Kb 𝕜) (Om D) (root5 (φ.symm h₂)))⁻¹ := by
    rw [hζdef, map_div₀, div_eq_mul_inv]
  have hA0 : algebraMap (Kb 𝕜) (Om D) (τ (root5 h₂)) ≠ 0 := fun h0 =>
    hτw₂ ((algebraMap (Kb 𝕜) (Om D)).injective (by rw [h0, map_zero]))
  -- Step 3: `δ ∘ g` carries the twisted coordinates of `h₂` to those of `φ⁻¹ h₂`
  have hgen : ∀ i : Fin 5, δ (g (twCoord D h₂ i)) = twCoord D (φ.symm h₂) i := by
    intro i
    have hkey : (algebraMap (Kb 𝕜) (Om D) (τ (root5 h₂)))⁻¹ ^ (i : ℕ)
          * (algebraMap (Kb 𝕜) (Om D) (τ (root5 h₂))
              * (algebraMap (Kb 𝕜) (Om D) (root5 (φ.symm h₂)))⁻¹) ^ (i : ℕ)
        = (algebraMap (Kb 𝕜) (Om D) (root5 (φ.symm h₂)))⁻¹ ^ (i : ℕ) := by
      rw [mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hA0, one_pow, one_mul]
    calc δ (g (twCoord D h₂ i))
        = δ ((g (algebraMap (Kb 𝕜) (Om D) (root5 h₂)))⁻¹ ^ (i : ℕ)
              * (kleinCoord D (Kb 𝕜) i / kleinCoord D (Kb 𝕜) 0)) := by rw [hgTw h₂ i]
      _ = δ ((algebraMap (Kb 𝕜) (Om D) (τ (root5 h₂)))⁻¹ ^ (i : ℕ)
              * (kleinCoord D (Kb 𝕜) i / kleinCoord D (Kb 𝕜) 0)) := by rw [hgKb]
      _ = (algebraMap (Kb 𝕜) (Om D) (τ (root5 h₂)))⁻¹ ^ (i : ℕ)
              * δ (kleinCoord D (Kb 𝕜) i / kleinCoord D (Kb 𝕜) 0) := by
            rw [map_mul, map_pow, map_inv₀, hδc]
      _ = (algebraMap (Kb 𝕜) (Om D) (τ (root5 h₂)))⁻¹ ^ (i : ℕ)
              * ((algebraMap (Kb 𝕜) (Om D) ζ) ^ (i : ℕ)
                * (kleinCoord D (Kb 𝕜) i / kleinCoord D (Kb 𝕜) 0)) := by rw [hδ i]
      _ = (algebraMap (Kb 𝕜) (Om D) (τ (root5 h₂)))⁻¹ ^ (i : ℕ)
              * ((algebraMap (Kb 𝕜) (Om D) (τ (root5 h₂))
                  * (algebraMap (Kb 𝕜) (Om D) (root5 (φ.symm h₂)))⁻¹) ^ (i : ℕ)
                * (kleinCoord D (Kb 𝕜) i / kleinCoord D (Kb 𝕜) 0)) := by rw [hζcoe]
      _ = ((algebraMap (Kb 𝕜) (Om D) (τ (root5 h₂)))⁻¹ ^ (i : ℕ)
              * (algebraMap (Kb 𝕜) (Om D) (τ (root5 h₂))
                  * (algebraMap (Kb 𝕜) (Om D) (root5 (φ.symm h₂)))⁻¹) ^ (i : ℕ))
              * (kleinCoord D (Kb 𝕜) i / kleinCoord D (Kb 𝕜) 0) := by rw [mul_assoc]
      _ = (algebraMap (Kb 𝕜) (Om D) (root5 (φ.symm h₂)))⁻¹ ^ (i : ℕ)
              * (kleinCoord D (Kb 𝕜) i / kleinCoord D (Kb 𝕜) 0) := by rw [hkey]
      _ = twCoord D (φ.symm h₂) i := by rw [twCoord]
  -- the constants are carried to the constants
  have hconst : ∀ c : RatFunc 𝕜, δ (g (algebraMap (RatFunc 𝕜) (Om D) c))
      = algebraMap (RatFunc 𝕜) (Om D) (φ.symm c) := by
    intro c
    rw [IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Kb 𝕜) (Om D) c, hgKb, hτ, hδc,
      ← IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Kb 𝕜) (Om D) (φ.symm c)]
  -- the coercions of the constants of the twist fields to `Ω`
  have hcoeS : ∀ (h : RatFunc 𝕜) (c : RatFunc 𝕜),
      ((algebraMap (RatFunc 𝕜) (twistFieldT D h) c : twistFieldT D h) : Om D)
        = algebraMap (RatFunc 𝕜) (Om D) c := by
    intro h c
    rw [← IntermediateField.algebraMap_apply (twistFieldT D h)
      (algebraMap (RatFunc 𝕜) (twistFieldT D h) c)]
    exact (IsScalarTower.algebraMap_apply (RatFunc 𝕜) (twistFieldT D h) (Om D) c).symm
  -- `θ` is `φ`-linear on constants, at the level of `Ω`
  have hθconst : ∀ c : RatFunc 𝕜,
      ((θ (algebraMap (RatFunc 𝕜) (twistFieldT D h₁) c) : twistFieldT D h₂) : Om D)
        = algebraMap (RatFunc 𝕜) (Om D) (φ c) := by
    intro c
    rw [congrArg (fun z : twistFieldT D h₂ => (z : Om D)) (hφ c)]
    exact hcoeS h₂ (φ c)
  -- Step 4a: `δ ∘ g` carries `F_{h₂}` into `F_{φ⁻¹ h₂}`
  have hmem : ∀ y : Om D, y ∈ twistFieldT D h₂ → δ (g y) ∈ twistFieldT D (φ.symm h₂) := by
    intro y hy
    refine IntermediateField.adjoin_induction (F := RatFunc 𝕜)
      (s := Set.range (twCoord D h₂))
      (p := fun y _ => δ (g y) ∈ twistFieldT D (φ.symm h₂)) ?_ ?_ ?_ ?_ ?_ hy
    · rintro y ⟨i, rfl⟩
      rw [hgen i]
      exact IntermediateField.subset_adjoin (RatFunc 𝕜) (Set.range (twCoord D (φ.symm h₂)))
        (Set.mem_range_self i)
    · intro c
      rw [hconst c]
      exact IntermediateField.algebraMap_mem _ _
    · intro a b ha hb ia ib
      rw [map_add, map_add]
      exact IntermediateField.add_mem _ ia ib
    · intro a ha ia
      rw [map_inv₀, map_inv₀]
      exact IntermediateField.inv_mem _ ia
    · intro a b ha hb ia ib
      rw [map_mul, map_mul]
      exact IntermediateField.mul_mem _ ia ib
  -- Step 4b: `K`-linearity on the constants
  have hcomm : ∀ c : RatFunc 𝕜,
      δ (g (θ (algebraMap (RatFunc 𝕜) (twistFieldT D h₁) c)))
        = algebraMap (RatFunc 𝕜) (Om D) c := by
    intro c
    rw [hθconst c, hconst (φ c), φ.symm_apply_apply c]
  -- Step 4c: the `K`-algebra homomorphism `Π`
  let Phi : twistFieldT D h₁ →ₐ[RatFunc 𝕜] twistFieldT D (φ.symm h₂) :=
    { toFun := fun x => ⟨δ (g (θ x)), hmem (θ x) (θ x).2⟩
      map_one' := by
        apply Subtype.ext
        show δ (g (θ (1 : twistFieldT D h₁))) = (1 : Om D)
        rw [map_one θ, show ((1 : twistFieldT D h₂) : Om D) = 1 from rfl, map_one g, map_one δ]
      map_zero' := by
        apply Subtype.ext
        show δ (g (θ (0 : twistFieldT D h₁))) = (0 : Om D)
        rw [map_zero θ, show ((0 : twistFieldT D h₂) : Om D) = 0 from rfl, map_zero g,
          map_zero δ]
      map_add' := by
        intro x y
        apply Subtype.ext
        show δ (g (θ (x + y))) = δ (g (θ x)) + δ (g (θ y))
        rw [map_add θ,
          show ((θ x + θ y : twistFieldT D h₂) : Om D) = (θ x : Om D) + (θ y : Om D) from rfl,
          map_add g, map_add δ]
      map_mul' := by
        intro x y
        apply Subtype.ext
        show δ (g (θ (x * y))) = δ (g (θ x)) * δ (g (θ y))
        rw [map_mul θ,
          show ((θ x * θ y : twistFieldT D h₂) : Om D) = (θ x : Om D) * (θ y : Om D) from rfl,
          map_mul g, map_mul δ]
      commutes' := by
        intro c
        apply Subtype.ext
        show δ (g (θ (algebraMap (RatFunc 𝕜) (twistFieldT D h₁) c)))
          = ((algebraMap (RatFunc 𝕜) (twistFieldT D (φ.symm h₂)) c
              : twistFieldT D (φ.symm h₂)) : Om D)
        rw [hcomm c]
        exact (hcoeS (φ.symm h₂) c).symm }
  refine ⟨AlgEquiv.ofBijective Phi ⟨?_, ?_⟩⟩
  · -- injectivity
    intro x y hxy
    have h1 : δ (g (θ x)) = δ (g (θ y)) := by
      have h2 : (Phi x : Om D) = (Phi y : Om D) := congrArg Subtype.val hxy
      exact h2
    exact θ.injective (Subtype.ext (g.injective (δ.injective h1)))
  · -- surjectivity
    intro y
    have key : ∀ z : Om D, z ∈ twistFieldT D (φ.symm h₂) →
        ∃ x : twistFieldT D h₁, δ (g (θ x)) = z := by
      intro z hz
      refine IntermediateField.adjoin_induction (F := RatFunc 𝕜)
        (s := Set.range (twCoord D (φ.symm h₂)))
        (p := fun z _ => ∃ x : twistFieldT D h₁, δ (g (θ x)) = z) ?_ ?_ ?_ ?_ ?_ hz
      · rintro z ⟨i, rfl⟩
        refine ⟨θ.symm ⟨twCoord D h₂ i,
          IntermediateField.subset_adjoin (RatFunc 𝕜) (Set.range (twCoord D h₂))
            (Set.mem_range_self i)⟩, ?_⟩
        rw [AlgEquiv.apply_symm_apply]
        exact hgen i
      · intro c
        exact ⟨algebraMap (RatFunc 𝕜) (twistFieldT D h₁) c, hcomm c⟩
      · intro a b ha hb ⟨x, hx⟩ ⟨y, hy⟩
        refine ⟨x + y, ?_⟩
        rw [map_add θ,
          show ((θ x + θ y : twistFieldT D h₂) : Om D) = (θ x : Om D) + (θ y : Om D) from rfl,
          map_add g, map_add δ, hx, hy]
      · intro a ha ⟨x, hx⟩
        refine ⟨x⁻¹, ?_⟩
        rw [map_inv₀ θ,
          show (((θ x)⁻¹ : twistFieldT D h₂) : Om D) = ((θ x : Om D))⁻¹ from rfl,
          map_inv₀ g, map_inv₀ δ, hx]
      · intro a b ha hb ⟨x, hx⟩ ⟨y, hy⟩
        refine ⟨x * y, ?_⟩
        rw [map_mul θ,
          show ((θ x * θ y : twistFieldT D h₂) : Om D) = (θ x : Om D) * (θ y : Om D) from rfl,
          map_mul g, map_mul δ, hx, hy]
    obtain ⟨x, hx⟩ := key (y : Om D) y.2
    exact ⟨x, Subtype.ext hx⟩

end

end Work.MotV
