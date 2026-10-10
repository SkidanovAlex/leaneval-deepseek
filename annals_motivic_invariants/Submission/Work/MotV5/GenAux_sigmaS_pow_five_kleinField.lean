import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

/-- If an algebra automorphism `f` fixes a point `x`, then so does every integer power of `f`. -/
lemma zpow_apply_eq_self_of_apply_eq_self {K E : Type*} [Field K] [Field E] [Algebra K E]
    (f : E ≃ₐ[K] E) (x : E) (h1 : f x = x) : ∀ n : ℤ, (f ^ n) x = x := by
  have hnat : ∀ n : ℕ, (f ^ n) x = x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, h1]
  intro n
  rcases Int.eq_nat_or_neg n with ⟨m, hn | hn⟩
  · rw [hn, zpow_natCast]; exact hnat m
  · rw [hn, zpow_neg, zpow_natCast]
    have h2 : (f ^ m) (((f ^ m)⁻¹) x) = x := by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel]
      exact AlgEquiv.one_apply x
    have h3 : ((f ^ m)⁻¹) x = x := by
      apply (f ^ m).injective
      rw [h2, hnat m]
    exact h3

/-- **`σS ^ 5` fixes the Klein field pointwise.**

For good Klein data `D` and a projective fifth-torsion shift `σS` (`σS κ_i = λ κ_{i+1}`,
`λ ≠ 0`; `Work.MotV5.KleinData.ShiftOf D σS`), the fifth power of the `RatFunc 𝕜`-restriction of
`σS` is the identity on `Work.MotV5.kleinField D`.

Proof route.  Write `κ i := Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i` and
`r i := κ i / κ 0` (so `kleinField D = IntermediateField.adjoin (RatFunc 𝕜) (Set.range r)`,
definitionally); `κ 0 ≠ 0` comes from `D.Good.coord0_ne`.  Let `σ := σS.restrictScalars (RatFunc 𝕜)`
(so `σ x = σS x` as elements, `AlgEquiv.restrictScalars_apply`) and let
`cyc : Fin 5 → Fin 5 := fun i => i + 1`.  From `hσS` obtain `lam ≠ 0` with
`σS (κ i) = lam * κ (cyc i)` for all `i`.  Prove by induction on `k` that there is `μ : Om D` with
`∀ i : Fin 5, (σ^k) (κ i) = μ * κ (cyc^[k] i)`; the point of the formulation is that the scalar `μ`
is independent of `i` (induction step: `σ (μ * κ j) = σ μ * lam * κ (cyc j)`, so
`μ_{k+1} = σ μ_k * lam`).  Deducing, for `k = 5`, that `(σ^5) (κ i) = μ_5 * κ i` for all `i`
(because `cyc^[5] = id`, proved by `funext i; fin_cases i <;> rfl`); therefore
`(σ^5) (r i) = (μ_5 * κ i) / (μ_5 * κ 0) = r i` (`mul_div_mul_left`).  Finally `kleinField D` is
generated over `RatFunc 𝕜` by the `r i`, and the set of fixed points of an algebra automorphism is
a subfield containing the constants, so `σ^5` fixes all of `kleinField D`; for instance apply
`IntermediateField.adjoin_le_iff` with target `IntermediateField.fixedField`
`(Subgroup.zpowers ((σS.restrictScalars (RatFunc 𝕜)) ^ 5))` — membership there is
`IntermediateField.mem_fixedField_iff` plus `Subgroup.mem_zpowers_iff`, and for the negative powers
use that `σ^5` fixes `r i` (or `zpow_smul_eq_self_of_smul_eq_self` in
`Submission.Work.MotV5.RigAS.twistFieldTrue_sup_asRoot`).

Relevant existing statements: `Work.MotV5.sigmaS_mem_kleinField` (preservation, sorry-free),
`Work.MotV5.kleinField_eq_adjoin_range`, `Work.MotV.kleinCoord_eq_sum`, `Work.MotV.kleinBas`,
`Work.MotV5.asTwistAction`. -/
theorem GenAux_sigmaS_pow_five_kleinField (𝕜 : Type) [Field 𝕜]
    (D : Work.MotV.KleinData 𝕜) (hD : D.Good)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (hσS : Work.MotV5.KleinData.ShiftOf D σS) :
    ∀ z ∈ Work.MotV5.kleinField D,
      ((σS.restrictScalars (RatFunc 𝕜)) ^ 5) z = z := by
  obtain ⟨lam, hlam, hsh⟩ := hσS
  set κ : Fin 5 → Work.MotV.Om D := fun i => Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i with hκ
  set r : Fin 5 → Work.MotV.Om D := fun i => κ i / κ 0 with hr
  have hκ0 : κ 0 ≠ 0 := hD.coord0_ne (Work.MotV.Kb 𝕜)
  -- The scalar supplied by the shift satisfies `σS (κ i) = lam * κ (i + 1)`; iterating,
  -- `(σS^k) (κ i) = mu k * κ (cyc^[k] i)` with a scalar `mu k` independent of `i`.
  have keyS : ∀ k : ℕ, ∃ μ : Work.MotV.Om D, ∀ i : Fin 5,
      (σS^k) (κ i) = μ * κ ((fun i : Fin 5 => i + 1)^[k] i) := by
    intro k
    induction k with
    | zero =>
      refine ⟨1, fun i => ?_⟩
      simp
    | succ k ih =>
      obtain ⟨μ, hμ⟩ := ih
      refine ⟨σS μ * lam, fun i => ?_⟩
      rw [pow_succ', AlgEquiv.mul_apply, hμ i, map_mul, hsh ((fun i : Fin 5 => i + 1)^[k] i),
        show (fun i : Fin 5 => i + 1)^[k+1] i = (fun i : Fin 5 => i + 1)^[k] i + 1 from by
          simp only [Function.iterate_succ_apply']]
      first | refl_ring1 | ring
  obtain ⟨μ, hμ⟩ := keyS 5
  have hcyc : (fun i : Fin 5 => i + 1)^[5] = id := by funext i; fin_cases i <;> rfl
  have h5κ : ∀ i, (σS^5) (κ i) = μ * κ i := by
    intro i; rw [hμ i, hcyc]; simp
  have hμ0 : μ ≠ 0 := by
    have h : μ * κ 0 ≠ 0 := by rw [← h5κ 0]; exact (map_ne_zero (σS^5)).mpr hκ0
    exact (mul_ne_zero_iff.mp h).1
  have hr_fixed : ∀ i, (σS^5) (r i) = r i := by
    intro i
    show (σS^5) (κ i / κ 0) = κ i / κ 0
    rw [map_div₀, h5κ i, h5κ 0, mul_div_mul_left _ _ hμ0]
  -- `restrictScalars` does not change the underlying function, so the two powers agree.
  have hpow : ∀ n (x : Work.MotV.Om D),
      ((σS.restrictScalars (RatFunc 𝕜))^n) x = (σS^n) x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ', AlgEquiv.mul_apply, ih, pow_succ', AlgEquiv.mul_apply,
        AlgEquiv.restrictScalars_apply]
  -- `σ^5` fixes the generators `r i` of `kleinField D`, hence all of it.
  have hS : Work.MotV5.kleinField D ≤ IntermediateField.fixedField
      (Subgroup.zpowers ((σS.restrictScalars (RatFunc 𝕜))^5)) := by
    rw [show Work.MotV5.kleinField D = IntermediateField.adjoin (RatFunc 𝕜) (Set.range r)
      from rfl]
    rw [IntermediateField.adjoin_le_iff]
    rintro z ⟨i, rfl⟩
    refine (IntermediateField.mem_fixedField_iff
      (Subgroup.zpowers ((σS.restrictScalars (RatFunc 𝕜))^5)) (r i)).mpr ?_
    intro f hf
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hf
    rw [← hn]
    exact zpow_apply_eq_self_of_apply_eq_self ((σS.restrictScalars (RatFunc 𝕜))^5) (r i)
      (by rw [hpow 5 (r i)]; exact hr_fixed i) n
  intro z hz
  have hzS := (IntermediateField.mem_fixedField_iff
    (Subgroup.zpowers ((σS.restrictScalars (RatFunc 𝕜))^5)) z).mp (hS hz)
  exact hzS ((σS.restrictScalars (RatFunc 𝕜))^5) (Subgroup.mem_zpowers _)

end Work.MotV5
