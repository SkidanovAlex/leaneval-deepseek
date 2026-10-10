import Mathlib
import Submission.Work.MotV5.LamAS.asPsi
import Submission.Work.MotV5.LamAS.asF_transfer
import Submission.Work.MotV5.LamAS.asIota_range
import Submission.Work.MotV5.LamAS.root_eq_asRoot_add
import Submission.Work.MotV5.Alpha.TwistTransport
import Submission.Work.MotV5.Alpha.CoeffAct
import Submission.Work.MotV5.kleinField_eq_adjoin_genXY
import Submission.Work.MotV5.adjoin_genX_genY

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# Auxiliary lemmas for the twisted Galois action `ψ_γ` on `M = L(E)`

Helper layer for `Submission/Work/MotV5/LamAS/asPsi_fixes_asF.lean`.

The ambient field is `M = asML D f₁ f₂ = L(E)` with `L = asL2 f₁ f₂ ⊆ Kb 𝕜` the two-root
Artin–Schreier field, embedded into `Om D = Kb 𝕜(E)` by the base-change map `asIota`.

Contents:

* `asML_algHom_ext`, `asML_algEquiv_ext`, `asML_algHom_ext_om` — an `L`-algebra homomorphism out
  of `M = L(E)` is determined by its values on the two coordinates `genX`, `genY` (and on the
  constants), because `M = L(genX, genY)`;
* `asCoeff_one`, `asCoeff_mul`, `asCoeff_pow` — `asCoeff` is a monoid homomorphism
  `Gal(L/K) → Aut_K(M)`;
* `asIota_pow` — `asIota` intertwines powers of `σS'` and of `σS`;
* `asIota_coeffAction` — `asIota` intertwines the coefficient action of `γ ∈ Gal(L/K)` on `M` with
  the coefficient action of any `K`-automorphism `σ` of `Kb 𝕜` extending `γ`;
* `coeffAction_fixes_kleinCoord`, `coeffAction_fixes_kleinField` — the coefficient action fixes the
  Klein coordinates (and hence the field `kleinField D`) pointwise;
* `tau_eq_coeffAction_on_Omega` — a `K`-algebra automorphism of `Om D` acting on the constants by
  `σ` and fixing `kleinField D` pointwise agrees with the coefficient action of `σ` on
  `Ω = kleinField D ⊔ LImage D L`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.MotV5.LamAS

open WeierstrassCurve WeierstrassCurve.Affine

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-! ## §1 Generation of `M = L(E)` by `x, y` -/

/-- An `L`-algebra homomorphism out of `M = L(E)` is determined by its values on the constants `L`
and on the two coordinates `genX, genY`: `M = L(genX, genY)`. -/
theorem asML_algHom_ext {N : Type} [Field N] [Algebra (RatFunc 𝕜) N] (D : Work.MotV.KleinData 𝕜)
    (f₁ f₂ : RatFunc 𝕜) (φ ψ : asML D f₁ f₂ →ₐ[RatFunc 𝕜] N)
    (hconst : ∀ l : ↥(asL2 (𝕜 := 𝕜) f₁ f₂),
      φ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l)
        = ψ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l))
    (hX : φ (Work.MotV.genX (asE2 D f₁ f₂)) = ψ (Work.MotV.genX (asE2 D f₁ f₂)))
    (hY : φ (Work.MotV.genY (asE2 D f₁ f₂)) = ψ (Work.MotV.genY (asE2 D f₁ f₂))) :
    φ = ψ := by
  have hadj : IntermediateField.adjoin ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
      ({Work.MotV.genX (asE2 D f₁ f₂), Work.MotV.genY (asE2 D f₁ f₂)} :
        Set (asML D f₁ f₂)) = ⊤ :=
    Work.MotV5.adjoin_genX_genY ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asE2 D f₁ f₂)
  refine AlgHom.ext (fun x => ?_)
  refine IntermediateField.adjoin_induction ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
    (p := fun z _ => φ z = ψ z) (fun z hz => ?_) (fun c => ?_)
    (fun z w _ _ hz hw => ?_) (fun z _ hz => ?_) (fun z w _ _ hz hw => ?_)
    (by rw [hadj]; trivial)
  · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hX
    · exact hY
  · exact hconst c
  · rw [map_add, map_add, hz, hw]
  · rw [map_inv₀, map_inv₀, hz]
  · rw [map_mul, map_mul, hz, hw]

/-- An `L`-algebra homomorphism out of `M = L(E)` into `Om D` is determined by its values on the
constants `L` and on `genX, genY` (specialisation of `asML_algHom_ext`). -/
theorem asML_algHom_ext_om (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜)
    (φ ψ : asML D f₁ f₂ →ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (hconst : ∀ l : ↥(asL2 (𝕜 := 𝕜) f₁ f₂),
      φ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l)
        = ψ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l))
    (hX : φ (Work.MotV.genX (asE2 D f₁ f₂)) = ψ (Work.MotV.genX (asE2 D f₁ f₂)))
    (hY : φ (Work.MotV.genY (asE2 D f₁ f₂)) = ψ (Work.MotV.genY (asE2 D f₁ f₂))) :
    φ = ψ := asML_algHom_ext D f₁ f₂ φ ψ hconst hX hY

/-- An `L`-algebra automorphism of `M = L(E)` is determined by its values on the constants `L` and
on the two coordinates `genX, genY`. -/
theorem asML_algEquiv_ext (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜)
    (φ ψ : asML D f₁ f₂ ≃ₐ[RatFunc 𝕜] asML D f₁ f₂)
    (hconst : ∀ l : ↥(asL2 (𝕜 := 𝕜) f₁ f₂),
      φ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l)
        = ψ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l))
    (hX : φ (Work.MotV.genX (asE2 D f₁ f₂)) = ψ (Work.MotV.genX (asE2 D f₁ f₂)))
    (hY : φ (Work.MotV.genY (asE2 D f₁ f₂)) = ψ (Work.MotV.genY (asE2 D f₁ f₂))) :
    φ = ψ := by
  have hadj : IntermediateField.adjoin ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
      ({Work.MotV.genX (asE2 D f₁ f₂), Work.MotV.genY (asE2 D f₁ f₂)} :
        Set (asML D f₁ f₂)) = ⊤ :=
    Work.MotV5.adjoin_genX_genY ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asE2 D f₁ f₂)
  refine AlgEquiv.ext (fun x => ?_)
  refine IntermediateField.adjoin_induction ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
    (p := fun z _ => φ z = ψ z) (fun z hz => ?_) (fun c => ?_)
    (fun z w _ _ hz hw => ?_) (fun z _ hz => ?_) (fun z w _ _ hz hw => ?_)
    (by rw [hadj]; trivial)
  · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hX
    · exact hY
  · exact hconst c
  · rw [map_add, map_add, hz, hw]
  · rw [map_inv₀, map_inv₀, hz]
  · rw [map_mul, map_mul, hz, hw]

/-! ## §2 `asCoeff` is a monoid homomorphism -/

/-- The coefficient action of `1 ∈ Gal(L/K)` is the identity. -/
theorem asCoeff_one (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) :
    asCoeff D f₁ f₂ 1 = 1 :=
  asML_algEquiv_ext D f₁ f₂ _ _
    (fun l => by rw [asCoeff_algebraMap]; rfl)
    (by rw [asCoeff_genX]; rfl) (by rw [asCoeff_genY]; rfl)

/-- **`asCoeff` is a monoid homomorphism.**  The coefficient action of a product of Galois
automorphisms is the product of the coefficient actions. -/
theorem asCoeff_mul (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜)
    (γ δ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) :
    asCoeff D f₁ f₂ (γ * δ) = asCoeff D f₁ f₂ γ * asCoeff D f₁ f₂ δ :=
  asML_algEquiv_ext D f₁ f₂ _ _
    (fun l => by
      rw [asCoeff_algebraMap]
      simp only [AlgEquiv.mul_apply, asCoeff_algebraMap])
    (by rw [asCoeff_genX, AlgEquiv.mul_apply, asCoeff_genX, asCoeff_genX])
    (by rw [asCoeff_genY, AlgEquiv.mul_apply, asCoeff_genY, asCoeff_genY])

/-- The coefficient action preserves powers. -/
theorem asCoeff_pow (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜)
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (k : ℕ) :
    asCoeff D f₁ f₂ (γ ^ k) = (asCoeff D f₁ f₂ γ) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, asCoeff_one]
  | succ n ih => rw [pow_succ, pow_succ, asCoeff_mul, ih]

/-! ## §3 Compatibility of `asIota` with powers and coefficient actions -/

/-- `asIota` intertwines the powers of a lift `σS'` of `σS` to `M`. -/
theorem asIota_pow (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σS' : asML D f₁ f₂ ≃ₐ[↥(asL2 (𝕜 := 𝕜) f₁ f₂)] asML D f₁ f₂)
    (hσS' : ∀ x : asML D f₁ f₂, asIota D f₁ f₂ (σS' x) = σS (asIota D f₁ f₂ x))
    (k : ℕ) (x : asML D f₁ f₂) :
    asIota D f₁ f₂ ((σS' ^ k) x) = (σS ^ k) (asIota D f₁ f₂ x) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', AlgEquiv.mul_apply, hσS', ih, pow_succ', AlgEquiv.mul_apply]

/-- **`asIota` intertwines the coefficient action of `γ ∈ Gal(L/K)` on `M` with the coefficient
action of any `K`-automorphism `σ` of `Kb 𝕜` extending `γ`.** -/
theorem asIota_coeffAction (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜)
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (hγ : ∀ l : ↥(asL2 (𝕜 := 𝕜) f₁ f₂), σ (l : Work.MotV.Kb 𝕜) = (γ l : Work.MotV.Kb 𝕜)) :
    ∀ x : asML D f₁ f₂,
      asIota D f₁ f₂ (asCoeff D f₁ f₂ γ x) =
        Work.MotV5.coeffAction D.E σ (asIota D f₁ f₂ x) := by
  have key : ((asIota D f₁ f₂).comp (asCoeff D f₁ f₂ γ).toAlgHom)
      = ((Work.MotV5.coeffAction D.E σ).toAlgHom.comp (asIota D f₁ f₂)) := by
    refine asML_algHom_ext D f₁ f₂ _ _ (fun l => ?_) ?_ ?_
    · show asIota D f₁ f₂ (asCoeff D f₁ f₂ γ
          (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l))
        = Work.MotV5.coeffAction D.E σ
            (asIota D f₁ f₂ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l))
      rw [asCoeff_algebraMap, asIota_algebraMap, asIota_algebraMap,
        Work.MotV5.coeffAction_algebraMap, ← hγ l]
    · show asIota D f₁ f₂ (asCoeff D f₁ f₂ γ (Work.MotV.genX (asE2 D f₁ f₂)))
        = Work.MotV5.coeffAction D.E σ (asIota D f₁ f₂ (Work.MotV.genX (asE2 D f₁ f₂)))
      rw [asCoeff_genX, asIota_genX, Work.MotV5.coeffAction_genX]
    · show asIota D f₁ f₂ (asCoeff D f₁ f₂ γ (Work.MotV.genY (asE2 D f₁ f₂)))
        = Work.MotV5.coeffAction D.E σ (asIota D f₁ f₂ (Work.MotV.genY (asE2 D f₁ f₂)))
      rw [asCoeff_genY, asIota_genY, Work.MotV5.coeffAction_genY]
  intro x
  exact AlgHom.congr_fun key x

/-! ## §4 The coefficient action fixes the Klein coordinates -/

/-- The coefficient action of `σ` on `Om D` fixes the Klein coordinates. -/
theorem coeffAction_fixes_kleinCoord (D : Work.MotV.KleinData 𝕜)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜) (i : Fin 5) :
    Work.MotV5.coeffAction D.E σ (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i)
      = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i := by
  simp only [Work.MotV.kleinCoord_eq_sum, map_sum, map_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  · rw [← IsScalarTower.algebraMap_apply 𝕜 (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (D.coord i m),
      IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Om D) (D.coord i m)]
    exact (Work.MotV5.coeffAction D.E σ).commutes _
  · exact Work.MotV5.coeffAction_kleinBas D σ m

/-- The coefficient action of `σ` fixes the Klein ratios `asRatio D i`. -/
theorem coeffAction_fixes_asRatio (D : Work.MotV.KleinData 𝕜)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜) (i : Fin 5) :
    Work.MotV5.coeffAction D.E σ (Work.MotV5.asRatio D i) = Work.MotV5.asRatio D i := by
  rw [Work.MotV5.asRatio, map_div₀, coeffAction_fixes_kleinCoord D σ i,
    coeffAction_fixes_kleinCoord D σ 0]

/-- **The coefficient action of `σ` fixes `kleinField D` pointwise.** -/
theorem coeffAction_fixes_kleinField (D : Work.MotV.KleinData 𝕜)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜) :
    ∀ x ∈ Work.MotV5.kleinField D, Work.MotV5.coeffAction D.E σ x = x := by
  set S : IntermediateField (RatFunc 𝕜) (Work.MotV.Om D) :=
    { carrier := {x | Work.MotV5.coeffAction D.E σ x = x}
      zero_mem' := by simp
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add, ha, hb]
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_inv₀, ha]
      algebraMap_mem' := fun c => by
        show Work.MotV5.coeffAction D.E σ (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) c)
          = algebraMap (RatFunc 𝕜) (Work.MotV.Om D) c
        rw [IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c,
          Work.MotV5.coeffAction_algebraMap, AlgEquiv.commutes] } with hSdef
  have hle : Work.MotV5.kleinField D ≤ S := by
    rw [Work.MotV5.kleinField, IntermediateField.adjoin_le_iff]
    rintro y ⟨i, rfl⟩
    exact coeffAction_fixes_asRatio D σ i
  intro x hx
  exact hle hx

/-! ## §5 `τ = coeffAction σ` on `Ω = kleinField D ⊔ LImage D L` -/

/-- **A `K`-algebra automorphism of `Om D` acting on the constants by `σ` and fixing `kleinField D`
pointwise agrees with the coefficient action of `σ` on `Ω = kleinField D ⊔ LImage D L`.** -/
theorem tau_eq_coeffAction_on_Omega (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (hτ : ∀ c : Work.MotV.Kb 𝕜,
      τ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
        = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ c))
    (hτk : ∀ x ∈ Work.MotV5.kleinField D, τ x = x) :
    ∀ x ∈ Work.MotV5.kleinField D ⊔ LImage D (asL2 (𝕜 := 𝕜) f₁ f₂),
      τ x = Work.MotV5.coeffAction D.E σ x := by
  set S : IntermediateField (RatFunc 𝕜) (Work.MotV.Om D) :=
    { carrier := {x | τ x = Work.MotV5.coeffAction D.E σ x}
      zero_mem' := by simp
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add, map_add, ha, hb]
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_inv₀, map_inv₀, ha]
      algebraMap_mem' := fun c => by
        show τ (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) c)
          = Work.MotV5.coeffAction D.E σ (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) c)
        rw [IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c,
          hτ, Work.MotV5.coeffAction_algebraMap] } with hSdef
  have h1 : Work.MotV5.kleinField D ≤ S := by
    intro x hx
    exact (hτk x hx).trans (coeffAction_fixes_kleinField D σ x hx).symm
  have h2 : LImage D (asL2 (𝕜 := 𝕜) f₁ f₂) ≤ S := by
    intro x hx
    obtain ⟨c, -, rfl⟩ := (mem_LImage_iff D (asL2 (𝕜 := 𝕜) f₁ f₂) x).mp hx
    show τ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
      = Work.MotV5.coeffAction D.E σ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
    rw [hτ c, Work.MotV5.coeffAction_algebraMap]
  exact fun x hx => (sup_le h1 h2) hx

/-! ## §6 Extension and restriction of `K`-automorphisms of `Kb 𝕜` along `L = asL2 f₁ f₂` -/

/-- **Extension of a `K`-automorphism of `L = K⟮asRoot f₁, asRoot f₂⟯` to `Kb 𝕜`.** -/
theorem asExtend (f₁ f₂ : RatFunc 𝕜)
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) :
    ∃ σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜,
      ∀ l : ↥(asL2 (𝕜 := 𝕜) f₁ f₂), σ (l : Work.MotV.Kb 𝕜) = (γ l : Work.MotV.Kb 𝕜) := by
  let f : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) →ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜 :=
    (IsScalarTower.toAlgHom (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜)).comp
      γ.toAlgHom
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := RatFunc 𝕜)
    (L := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (E := Work.MotV.Kb 𝕜) (M := Work.MotV.Kb 𝕜) f
  refine ⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), fun l => ?_⟩
  have h := AlgHom.congr_fun hφ l
  exact h

/-- **Restriction of a `K`-automorphism of `Kb 𝕜` to `L = K⟮asRoot f₁, asRoot f₂⟯`.** -/
theorem asRestrict (f₁ f₂ : RatFunc 𝕜)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜) :
    ∃ σL : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂),
      ∀ l : ↥(asL2 (𝕜 := 𝕜) f₁ f₂),
        (σL l : Work.MotV.Kb 𝕜) = σ (l : Work.MotV.Kb 𝕜) := by
  have hroot : ∀ f : RatFunc 𝕜, f = f₁ ∨ f = f₂ →
      σ (Work.MotV5.asRoot f) ∈ asL2 (𝕜 := 𝕜) f₁ f₂ := by
    intro f hf
    have h : (σ (Work.MotV5.asRoot f)) ^ 5 - σ (Work.MotV5.asRoot f)
        = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) f := by
      have h1 := congrArg σ (Work.MotV5.asRoot_spec f)
      rw [map_sub, map_pow] at h1
      rw [h1, AlgEquiv.commutes]
    obtain ⟨k, hk⟩ := Work.MotV5.LamAS.root_eq_asRoot_add f h
    rw [hk]
    refine IntermediateField.add_mem _ ?_ ?_
    · rcases hf with hf | hf
      · rw [hf]; exact asRoot_mem_asL2_left f₁ f₂
      · rw [hf]; exact asRoot_mem_asL2_right f₁ f₂
    · rw [show algebraMap ℤ (Work.MotV.Kb 𝕜) ((k : Fin 5) : ℤ)
          = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜)
              (algebraMap ℤ (RatFunc 𝕜) ((k : Fin 5) : ℤ)) from
        (IsScalarTower.algebraMap_apply ℤ (RatFunc 𝕜) (Work.MotV.Kb 𝕜) _).symm]
      exact IntermediateField.algebraMap_mem _ _
  have hmap : ∀ x ∈ asL2 (𝕜 := 𝕜) f₁ f₂, σ x ∈ asL2 (𝕜 := 𝕜) f₁ f₂ := by
    intro x hx
    refine IntermediateField.adjoin_induction (RatFunc 𝕜)
      (p := fun z _ => σ z ∈ asL2 (𝕜 := 𝕜) f₁ f₂) (fun z hz => ?_) (fun c => ?_)
      (fun z w _ _ hz hw => ?_) (fun z _ hz => ?_) (fun z w _ _ hz hw => ?_) hx
    · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hroot f₁ (Or.inl rfl)
      · exact hroot f₂ (Or.inr rfl)
    · rw [AlgEquiv.commutes]
      exact IntermediateField.algebraMap_mem _ _
    · rw [map_add]; exact IntermediateField.add_mem _ hz hw
    · rw [map_inv₀]; exact IntermediateField.inv_mem _ hz
    · rw [map_mul]; exact IntermediateField.mul_mem _ hz hw
  let φ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) →ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂) :=
    { toFun := fun l => ⟨σ (l : Work.MotV.Kb 𝕜), hmap (l : Work.MotV.Kb 𝕜) l.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        push_cast
        rw [map_mul]
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := fun a b => by
        apply Subtype.ext
        push_cast
        rw [map_add]
      commutes' := fun c => by
        apply Subtype.ext
        push_cast
        rw [AlgEquiv.commutes] }
  exact ⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), fun l => rfl⟩

/-! ## §7 The coefficient action fixes `asFieldL D g` when it fixes `asRoot g` -/

/-- If `σ` fixes `asRoot g` then the coefficient action of `σ` fixes `asFieldL D g` pointwise. -/
theorem coeffAction_fixes_asFieldL (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (hσ : σ (Work.MotV5.asRoot g) = Work.MotV5.asRoot g) :
    ∀ x ∈ Work.MotV5.asFieldL D g, Work.MotV5.coeffAction D.E σ x = x := by
  set S : IntermediateField (RatFunc 𝕜) (Work.MotV.Om D) :=
    { carrier := {x | Work.MotV5.coeffAction D.E σ x = x}
      zero_mem' := by simp
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add, ha, hb]
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_inv₀, ha]
      algebraMap_mem' := fun c => by
        show Work.MotV5.coeffAction D.E σ (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) c)
          = algebraMap (RatFunc 𝕜) (Work.MotV.Om D) c
        rw [IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c,
          Work.MotV5.coeffAction_algebraMap, AlgEquiv.commutes] } with hSdef
  have h1 : Work.MotV5.kleinField D ≤ S := fun x hx =>
    coeffAction_fixes_kleinField D σ x hx
  have h2 : IntermediateField.adjoin (RatFunc 𝕜)
      {algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g)} ≤ S := by
    rw [IntermediateField.adjoin_le_iff]
    rintro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show Work.MotV5.coeffAction D.E σ
        (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g))
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g)
    rw [Work.MotV5.coeffAction_algebraMap, hσ]
  intro x hx
  rw [Work.MotV5.asFieldL] at hx
  exact (sup_le h1 h2) hx


end Work.MotV5.LamAS
