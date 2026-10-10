import Mathlib
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.asCoord_asTwCoord
import Submission.Work.MotV5.tp_as
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

/-!
# The Klein point of the AS twist field: the `tp_as` route

The geometric input `Work.MotV5.Nodes.poleFibre_asTwist` (at every place above the pole of `t` the
value of `t` is a fifth power of the value group) is *not* the only route to the node: the master
valuation lemma `Work.MotV5.tp_as` gives it directly, applied to the twist field itself.

The point is that the Klein coordinates of the twist field do have `F`-coefficients in the
Artin–Schreier basis `1, W, …, W⁴`.  The interpolation coefficients of the Klein point
`(κᵢ/κ₀)ᵢ` at the nodes `W + i` are `asTwCoord D g j`, and although they are not `σ'`-fixed, their
*ratios* are: the algebraic core of this file is

  `σ' (asTwCoord D g j) * κ₁ = asTwCoord D g j * κ₀`   (`asTwistAction_asTwCoord`),

which follows from `σ' (W) = W + 1`, `σ' (κᵢ/κ₀) = (κ_{i+1}/κ₀)/(κ₁/κ₀)`, `σS (W) = W` and the
reindexing `∑ k_{i+1} ((W + i + 1)^m - δ) = ∑ k_i ((W + i)^m - δ)` in characteristic `5` (where the
`i = 4` term is the `W + 5 = W` twist).

Consequently, for `j₀` with `asTwCoord D g j₀ ≠ 0`, the elements
`y_i := asTwCoord D g i / asTwCoord D g j₀` lie in `F = asTwistFieldTrue D g τ σS`, and

  `asCoord W y = (asTwCoord D g j₀)⁻¹ · (κᵢ/κ₀)ᵢ`

is a scalar multiple of the Klein point, hence a Klein point.  With `w = W`, `a = D.a`, `b = D.b`
all hypotheses of `tp_as` are met, and its conclusion `∃ u ∈ F, v g = (v u)^5` is exactly what the
node consumes.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.MotV5.Nodes

open scoped WithZero

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-- The interpolation sum defining `asTwCoord D g j`, in abstract form: the coefficients `x` of the
interpolation polynomial of a Klein point at the nodes `W + i`. -/
def asTwCoordPoly {R : Type*} [CommRing R] (x : Fin 5 → R) (W : R) (j : Fin 5) : R :=
  -∑ i : Fin 5, x i *
    ((W + ((i : ℕ) : R)) ^ (4 - (j : ℕ)) - (if (j : ℕ) = 0 then 1 else 0))

/-- `asTwCoordPoly` is `asTwCoord` with `x i = κᵢ/κ₀` and `W = asRoot g`. -/
theorem asTwCoord_eq_poly (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) (j : Fin 5) :
    Work.MotV5.asTwCoord D g j
      = asTwCoordPoly (fun i => Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
          / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
        (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g)) j := rfl

/-- **The `Fin 5` reindexing identity of the interpolation sum.**  Reindexing the sum defining
`asTwCoord D g j` by `i ↦ i + 1` (modulo `5`), the `i = 4` term being the twist `W + 5 = W` of
characteristic `5`. -/
theorem sum_shift_five {R : Type*} [CommRing R] [CharP R 5] (k : Fin 5 → R) (W : R) (j : Fin 5) :
    (∑ i : Fin 5, k (i + 1) *
        ((W + ((i : ℕ) : R) + 1) ^ (4 - (j : ℕ)) - (if (j : ℕ) = 0 then 1 else 0)))
      = ∑ i : Fin 5, k i *
        ((W + ((i : ℕ) : R)) ^ (4 - (j : ℕ)) - (if (j : ℕ) = 0 then 1 else 0)) := by
  fin_cases j <;>
    simp only [Fin.sum_univ_five] <;>
    norm_num <;>
    ring_nf <;>
    reduce_mod_char! <;>
    refl_ring1

/-- **The algebraic core of `asTwistAction_asTwCoord`.**  If `T W = W + 1`, `S W = W`,
`T (x i) = x i` and `S (x i) = x (i+1)/x 1`, then applying `S ∘ T` to the interpolation sum
`asTwCoordPoly x W j` multiplies it by `x 1`: the interpolation coefficients acquire the factor
`1/x 1`, which is exactly the ratio `κ₀/κ₁`. -/
theorem asTwCoordPoly_act {R : Type*} [Field R] [CharP R 5] (S T : R →+* R) (W : R) (x : Fin 5 → R)
    (hT : T W = W + 1) (hS : S W = W) (hx1 : x 1 ≠ 0)
    (hxT : ∀ i, T (x i) = x i) (hxS : ∀ i, S (x i) = x (i + 1) / x 1) (j : Fin 5) :
    S (T (asTwCoordPoly x W j)) * x 1 = asTwCoordPoly x W j := by
  have hd : S (T (if (j : ℕ) = 0 then (1 : R) else 0))
      = (if (j : ℕ) = 0 then (1 : R) else 0) := by
    by_cases hj : (j : ℕ) = 0
    · simp only [hj, ite_true, map_one]
    · simp only [hj, ite_false, map_zero]
  rw [asTwCoordPoly]
  simp only [map_neg, map_sum, map_mul, map_sub, map_pow, hxT, hT, map_add, map_natCast,
    map_one, hS, hxS, hd]
  rw [neg_mul, Finset.sum_mul, neg_inj]
  rw [show (∑ i : Fin 5, x (i + 1) / x 1 *
      ((W + 1 + ((i : ℕ) : R)) ^ (4 - (j : ℕ)) - (if (j : ℕ) = 0 then 1 else 0)) * x 1)
      = ∑ i : Fin 5, x (i + 1) *
      ((W + ((i : ℕ) : R) + 1) ^ (4 - (j : ℕ)) - (if (j : ℕ) = 0 then 1 else 0)) from by
    apply Finset.sum_congr rfl
    intro i _
    field_simp
    ring]
  exact sum_shift_five x W j

/-- **The Klein coordinates in the Artin–Schreier basis.**  Contrary to the coefficients themselves,
the ratios of consecutive `asTwCoord D g j` are `σ'`-invariant: the twisted action multiplies
`asTwCoord D g j` by exactly the constant `κ₀/κ₁`. -/
theorem asTwistAction_asTwCoord (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) (hD : D.Good)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ) (j : Fin 5) :
    Work.MotV5.asTwistAction D τ σS (Work.MotV5.asTwCoord D g j) *
        Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 1
      = Work.MotV5.asTwCoord D g j * Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 := by
  haveI : CharP (Work.MotV.Om D) 5 := Work.MotV5.charP_Om 𝕜 D
  obtain ⟨lam, hlam, hsh⟩ := h.hσS
  have hk0 : Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 ≠ 0 := hD.coord0_ne (Work.MotV.Kb 𝕜)
  have hk1 : Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 1 ≠ 0 := by
    intro h0
    have h1 : σS (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) = 0 := by
      rw [hsh 0]
      rw [show (0 : Fin 5) + 1 = (1 : Fin 5) from by decide, h0, mul_zero]
    exact hk0 ((map_eq_zero σS).mp h1)
  have hτW : τ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g))
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g) + 1 := by
    rw [h.hτ (Work.MotV5.asRoot g), h.hσ, map_add, map_one]
  have hσW : σS (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g))
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g) :=
    σS.commutes (Work.MotV5.asRoot g)
  have hmem : ∀ i : Fin 5, Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
        / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 ∈ Work.MotV5.kleinField D :=
    fun i => IntermediateField.subset_adjoin _ _ (Set.mem_range_self i)
  have hτx : ∀ i : Fin 5, τ (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
        / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
      = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
        / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 :=
    fun i => h.hτk _ (hmem i)
  have hσx : ∀ i : Fin 5, σS (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
        / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
      = (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) (i + 1)
          / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
        / (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 1
          / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) := by
    intro i
    rw [map_div₀, hsh i, hsh 0]
    rw [show (0 : Fin 5) + 1 = (1 : Fin 5) from by decide]
    rw [mul_div_mul_left _ _ hlam]
    field_simp
  have hmain := asTwCoordPoly_act (S := (σS : Work.MotV.Om D →+* Work.MotV.Om D))
    (T := (τ : Work.MotV.Om D →+* Work.MotV.Om D))
    (W := algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g))
    (x := fun i => Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
      / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
    hτW hσW (by rw [div_eq_mul_inv]; exact mul_ne_zero hk1 (inv_ne_zero hk0)) hτx hσx j
  rw [Work.MotV5.asTwistAction, AlgEquiv.trans_apply]
  change σS (τ (asTwCoordPoly (fun i => Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
        / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
        (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g)) j))
      * Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 1
    = asTwCoordPoly (fun i => Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
        / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
        (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g)) j
      * Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0
  have h2 := congrArg (· * Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) hmain
  rw [div_eq_mul_inv] at h2
  simpa [mul_assoc, inv_mul_cancel₀ hk0] using h2

/-- **`asTwCoord D g i` lies in `L(E) = asFieldL D g`**: it is a polynomial in `W` of degree `≤ 4`
whose coefficients are Klein ratios. -/
theorem asTwCoord_mem_asFieldL (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) (i : Fin 5) :
    Work.MotV5.asTwCoord D g i ∈ Work.MotV5.asFieldL D g := by
  haveI : CharP (Work.MotV.Om D) 5 := Work.MotV5.charP_Om 𝕜 D
  have hmemK : ∀ i : Fin 5, Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
      / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 ∈ Work.MotV5.asFieldL D g :=
    fun i => (le_sup_left : Work.MotV5.kleinField D ≤ Work.MotV5.asFieldL D g)
      (IntermediateField.subset_adjoin _ _ (Set.mem_range_self i))
  have hmemW : algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g)
      ∈ Work.MotV5.asFieldL D g :=
    (le_sup_right : _ ≤ Work.MotV5.asFieldL D g)
      (IntermediateField.subset_adjoin _ _ (Set.mem_singleton _))
  simp only [Work.MotV5.asTwCoord]
  refine IntermediateField.neg_mem _ (IntermediateField.sum_mem _ (fun j _ => ?_))
  refine IntermediateField.mul_mem _ (hmemK j) ?_
  refine IntermediateField.sub_mem _ ?_ ?_
  · have h1 : algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g)
        + ((j : ℕ) : Work.MotV.Om D) ∈ Work.MotV5.asFieldL D g :=
      IntermediateField.add_mem _ hmemW (IntermediateField.natCast_mem _ _)
    rw [← zpow_natCast]
    exact IntermediateField.pow_mem _ h1 _
  · split_ifs
    · exact IntermediateField.one_mem _
    · exact IntermediateField.zero_mem _

/-- **Some interpolation coefficient is nonzero.**  The Klein point has `κ₀/κ₀ = 1` at the node
`W + 0`, so the interpolation coefficients `asTwCoord D g j` cannot all vanish. -/
theorem exists_asTwCoord_ne_zero (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) (hD : D.Good) :
    ∃ j : Fin 5, Work.MotV5.asTwCoord D g j ≠ 0 := by
  haveI : CharP (Work.MotV.Om D) 5 := Work.MotV5.charP_Om 𝕜 D
  by_contra h
  push_neg at h
  have hk0 : Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 ≠ 0 := hD.coord0_ne (Work.MotV.Kb 𝕜)
  have hsum := Work.MotV5.asCoord_asTwCoord 𝕜 D g 0
  rw [Work.MotV.asCoord] at hsum
  have hzero : (∑ j : Fin 5, Work.MotV5.asTwCoord D g j *
      (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g)
        + ((0 : Fin 5) : ℕ)) ^ (j : ℕ)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [h j, zero_mul]
  rw [hzero, div_self hk0] at hsum
  exact zero_ne_one hsum

/-- **The Klein point of the twist field.**  For `j₀` with `asTwCoord D g j₀ ≠ 0`, the ratios
`asTwCoord D g i / asTwCoord D g j₀` are elements of `F = asTwistFieldTrue D g τ σS`. -/
theorem asTwCoord_div_mem_asTwistFieldTrue (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) (hD : D.Good)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ) (j₀ : Fin 5)
    (hj₀ : Work.MotV5.asTwCoord D g j₀ ≠ 0) (i : Fin 5) :
    Work.MotV5.asTwCoord D g i / Work.MotV5.asTwCoord D g j₀
      ∈ Work.MotV5.asTwistFieldTrue D g τ σS := by
  haveI : CharP (Work.MotV.Om D) 5 := Work.MotV5.charP_Om 𝕜 D
  obtain ⟨lam, hlam, hsh⟩ := h.hσS
  have hk0 : Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 ≠ 0 := hD.coord0_ne (Work.MotV.Kb 𝕜)
  have hk1 : Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 1 ≠ 0 := by
    intro h0
    have h1 : σS (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) = 0 := by
      rw [hsh 0]
      rw [show (0 : Fin 5) + 1 = (1 : Fin 5) from by decide, h0, mul_zero]
    exact hk0 ((map_eq_zero σS).mp h1)
  have hmemFix : Work.MotV5.asTwistAction D τ σS
      (Work.MotV5.asTwCoord D g i / Work.MotV5.asTwCoord D g j₀)
      = Work.MotV5.asTwCoord D g i / Work.MotV5.asTwCoord D g j₀ := by
    have hσi := asTwistAction_asTwCoord D g hD τ σS σ h i
    have hσj := asTwistAction_asTwCoord D g hD τ σS σ h j₀
    have e1 : Work.MotV5.asTwistAction D τ σS (Work.MotV5.asTwCoord D g i)
        = Work.MotV5.asTwCoord D g i * Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0
          / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 1 := (eq_div_iff hk1).mpr hσi
    have e2 : Work.MotV5.asTwistAction D τ σS (Work.MotV5.asTwCoord D g j₀)
        = Work.MotV5.asTwCoord D g j₀ * Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0
          / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 1 := (eq_div_iff hk1).mpr hσj
    rw [map_div₀, e1, e2]
    field_simp
  have hmemL : Work.MotV5.asTwCoord D g i / Work.MotV5.asTwCoord D g j₀
      ∈ Work.MotV5.asFieldL D g :=
    IntermediateField.div_mem _ (asTwCoord_mem_asFieldL D g i) (asTwCoord_mem_asFieldL D g j₀)
  refine ⟨?_, hmemL⟩
  change Work.MotV5.asTwCoord D g i / Work.MotV5.asTwCoord D g j₀ ∈ IntermediateField.fixedField
    (Subgroup.zpowers (Work.MotV5.asTwistAction D τ σS))
  rw [IntermediateField.mem_fixedField_iff]
  intro f hf
  have hzp : Subgroup.zpowers (Work.MotV5.asTwistAction D τ σS) ≤
      MulAction.stabilizer (Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
        (Work.MotV5.asTwCoord D g i / Work.MotV5.asTwCoord D g j₀) := by
    rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
    exact hmemFix
  have hfx : f • (Work.MotV5.asTwCoord D g i / Work.MotV5.asTwCoord D g j₀)
      = Work.MotV5.asTwCoord D g i / Work.MotV5.asTwCoord D g j₀ := hzp hf
  simpa only [AlgEquiv.smul_def] using hfx

/-! ## §5 The `tp_as` application: the value of `fAS` at the pole is a fifth power

All hypotheses of the master valuation lemma `Work.MotV5.tp_as` are now available with `F` the twist
field, `L = Om D`, `w = W = asRoot g`, `a = D.a`, `b = D.b` and `y` the Klein point of §4: the
conclusion `∃ u ∈ F, v g = (v u) ^ 5` is the input of `Work.MotV5.Nodes.fifthPow_value_of_pole`. -/

theorem fifthPow_fAS_of_tp_as (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D)
    (hg : g = Work.MotV.fAS 𝕜 ∨ g = 2 • Work.MotV.fAS 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ)
    (v : Valuation ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (WithZero (Multiplicative ℤ)))
    (hv : Work.MotV.TrivOn 𝕜 v)
    (hvt : 1 < v (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X)) :
    ∃ u : ↥(Work.MotV5.asTwistFieldTrue D g τ σS), u ≠ 0 ∧
      v (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (Work.MotV.fAS 𝕜))
        = (v u)^5 := by
  haveI : CharP (Work.MotV.Om D) 5 := Work.MotV5.charP_Om 𝕜 D
  haveI : CharP ↥(Work.MotV5.asTwistFieldTrue D g τ σS) 5 := by
    refine CharP.mk fun n => ?_
    have hcoe : ((n : ↥(Work.MotV5.asTwistFieldTrue D g τ σS)) : Work.MotV.Om D)
        = (n : Work.MotV.Om D) := by simp
    constructor
    · intro hn
      exact (CharP.cast_eq_zero_iff (Work.MotV.Om D) 5 n).mp
        (by rw [← hcoe]; exact congrArg Subtype.val hn)
    · intro hn
      exact Subtype.ext (by rw [hcoe]; exact (CharP.cast_eq_zero_iff (Work.MotV.Om D) 5 n).mpr hn)
  obtain ⟨j₀, hj₀⟩ := exists_asTwCoord_ne_zero D g hD.1
  let y : Fin 5 → ↥(Work.MotV5.asTwistFieldTrue D g τ σS) := fun i =>
    ⟨Work.MotV5.asTwCoord D g i / Work.MotV5.asTwCoord D g j₀,
      asTwCoord_div_mem_asTwistFieldTrue D g hD.1 τ σS σ h j₀ hj₀ i⟩
  have hy : y ≠ 0 := by
    intro h0
    have h1 : Work.MotV5.asTwCoord D g j₀ / Work.MotV5.asTwCoord D g j₀ = 0 := by
      have h1' := congrArg (fun z : ↥(Work.MotV5.asTwistFieldTrue D g τ σS) => (z : Work.MotV.Om D))
        (congrFun h0 j₀)
      simpa [y] using h1'
    rw [div_self hj₀] at h1
    exact one_ne_zero h1
  have hw : (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g)) ^ 5
      - algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g)
      = algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (Work.MotV.Om D)
          (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) g) := by
    rw [show (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g)) ^ 5
          - algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g)
        = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D)
            ((Work.MotV5.asRoot g) ^ 5 - Work.MotV5.asRoot g) from by rw [map_sub, map_pow]]
    rw [Work.MotV5.asRoot_spec]
    rw [← IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D)]
    rfl
  have ha : v (algebraMap 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS) D.a) = 1 :=
    hv D.a (fun hh => hD.1.ab_ne (by rw [hh, zero_mul]))
  have hb : v (algebraMap 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS) D.b) = 1 :=
    hv D.b (fun hh => hD.1.ab_ne (by rw [hh, mul_zero]))
  have hab : v ((algebraMap 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS) D.a) ^ 2
      - (algebraMap 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS) D.a)
        * (algebraMap 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS) D.b)
      - (algebraMap 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS) D.b) ^ 2) = 1 := by
    have h0 : (algebraMap 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS) D.a) ^ 2
        - (algebraMap 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS) D.a)
          * (algebraMap 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS) D.b)
        - (algebraMap 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS) D.b) ^ 2
        = algebraMap 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
            (D.a ^ 2 - D.a * D.b - D.b ^ 2) := by
      simp only [map_sub, map_mul, map_pow]
    rw [h0]
    exact hv _ hD.2.2.2
  have hhom : ∀ (c : Work.MotV.Om D) (w : Fin 5 → Work.MotV.Om D) (k : Fin 5),
      Work.MotK.kleinP (algebraMap 𝕜 (Work.MotV.Om D) D.a) (algebraMap 𝕜 (Work.MotV.Om D) D.b)
          (fun i => c * w i) k
        = c ^ 2 * Work.MotK.kleinP (algebraMap 𝕜 (Work.MotV.Om D) D.a)
            (algebraMap 𝕜 (Work.MotV.Om D) D.b) w k := by
    intro c w k
    fin_cases k <;>
      simp only [Work.MotK.kleinP_zero', Work.MotK.kleinP_one', Work.MotK.kleinP_two',
        Work.MotK.kleinP_three', Work.MotK.kleinP_four', Work.MotK.kleinP0, Work.MotK.kleinP1,
        Work.MotK.kleinP2, Work.MotK.kleinP3, Work.MotK.kleinP4] <;>
      refl_ring1
  have hK : ∀ k : Fin 5, Work.MotK.kleinP (algebraMap 𝕜 (Work.MotV.Om D) D.a)
      (algebraMap 𝕜 (Work.MotV.Om D) D.b)
      (fun i => Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
        / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) k = 0 := by
    intro k
    have hk0 : Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 ≠ 0 := hD.1.coord0_ne (Work.MotV.Kb 𝕜)
    have h0 := hD.1.klein_eq (Work.MotV.Kb 𝕜) k
    have hsplit : Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜)
        = fun i => Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0
            * (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
              / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) := by
      funext i
      rw [mul_div_cancel₀ _ hk0]
    rw [hsplit] at h0
    rw [hhom] at h0
    exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero 2 hk0)
  have hsum : ∀ k : Fin 5, Work.MotV.asCoord
      (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g))
      (fun j => Work.MotV5.asTwCoord D g j / Work.MotV5.asTwCoord D g j₀) k
      = (Work.MotV5.asTwCoord D g j₀)⁻¹
        * (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) k
          / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) := by
    intro k
    rw [show Work.MotV.asCoord (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g))
          (fun j => Work.MotV5.asTwCoord D g j / Work.MotV5.asTwCoord D g j₀) k
        = ∑ j : Fin 5, (Work.MotV5.asTwCoord D g j / Work.MotV5.asTwCoord D g j₀)
            * (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g)
              + ((k : ℕ) : Work.MotV.Om D)) ^ (j : ℕ) from rfl]
    rw [← Work.MotV5.asCoord_asTwCoord 𝕜 D g k]
    rw [show Work.MotV.asCoord (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g))
          (Work.MotV5.asTwCoord D g) k
        = ∑ j : Fin 5, Work.MotV5.asTwCoord D g j
            * (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g)
              + ((k : ℕ) : Work.MotV.Om D)) ^ (j : ℕ) from rfl]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [div_eq_mul_inv]
    refl_ring1
  have heq : ∀ k : Fin 5, Work.MotK.kleinP
      (algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (Work.MotV.Om D)
        (algebraMap 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS) D.a))
      (algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (Work.MotV.Om D)
        (algebraMap 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS) D.b))
      (Work.MotV.asCoord (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g))
        (fun j => algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (Work.MotV.Om D)
          (y j))) k = 0 := by
    intro k
    have hab' : algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (Work.MotV.Om D)
        (algebraMap 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS) D.a)
        = algebraMap 𝕜 (Work.MotV.Om D) D.a := rfl
    have hbb' : algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (Work.MotV.Om D)
        (algebraMap 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS) D.b)
        = algebraMap 𝕜 (Work.MotV.Om D) D.b := rfl
    have hyc : (fun j => algebraMap ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (Work.MotV.Om D) (y j))
        = fun j => Work.MotV5.asTwCoord D g j / Work.MotV5.asTwCoord D g j₀ := by
      funext j
      rfl
    rw [hab', hbb', hyc]
    rw [show Work.MotV.asCoord (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g))
          (fun j => Work.MotV5.asTwCoord D g j / Work.MotV5.asTwCoord D g j₀)
        = fun k => (Work.MotV5.asTwCoord D g j₀)⁻¹
            * (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) k
              / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) from funext hsum]
    rw [hhom, hK, mul_zero]
  have hfAS : v (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
      (Work.MotV.fAS 𝕜))
      = (v (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X)) ^ 3 := by
    have ht3 : v (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X)
        < v ((algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X) ^ 3) := by
      rw [Valuation.map_pow]
      exact lt_self_pow₀ hvt (by norm_num : (1 : ℕ) < 3)
    rw [Work.MotV.fAS, map_add, map_pow,
      Valuation.map_add_eq_of_lt_left _ ht3, Valuation.map_pow]
  have hfAS1 : 1 < v (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
      (Work.MotV.fAS 𝕜)) := by
    rw [hfAS]
    exact one_lt_pow₀ hvt (by norm_num)
  have h2n : (2 : 𝕜) ≠ 0 := by
    intro hz
    have := (CharP.cast_eq_zero_iff 𝕜 5 2).mp hz
    norm_num at this
  have hv2 : v (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
      (2 : RatFunc 𝕜)) = 1 := by
    have h3 : algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (2 : RatFunc 𝕜)
        = algebraMap 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (2 : 𝕜) := by
      rw [show (2 : RatFunc 𝕜) = algebraMap 𝕜 (RatFunc 𝕜) (2 : 𝕜) from (map_ofNat _ 2).symm,
        ← IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (↥(Work.MotV5.asTwistFieldTrue D g τ σS))
          (2 : 𝕜)]
    rw [h3]
    exact hv (2 : 𝕜) h2n
  have htwosmul : (2 : ℕ) • Work.MotV.fAS 𝕜 = (2 : RatFunc 𝕜) * Work.MotV.fAS 𝕜 := by
    rw [nsmul_eq_mul, Nat.cast_ofNat]
  have hgv : 1 < v (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) g) := by
    rcases hg with hg | hg
    · rw [show algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) g
          = algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (Work.MotV.fAS 𝕜) from by
        rw [hg]]
      exact hfAS1
    · rw [show algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) g
          = algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
              ((2 : RatFunc 𝕜) * Work.MotV.fAS 𝕜) from by rw [hg, htwosmul]]
      rw [map_mul, Valuation.map_mul, hv2, one_mul]
      exact hfAS1
  obtain ⟨u, hu⟩ := Work.MotV5.tp_as v (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D)
    (Work.MotV5.asRoot g)) (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) g)
    hw ha hb hab hy heq hgv
  have hu0 : u ≠ 0 := by
    intro h0
    rw [hu] at hgv
    rw [h0, Valuation.map_zero, zero_pow (by norm_num : (5 : ℕ) ≠ 0)] at hgv
    exact absurd hgv (not_lt.mpr (zero_le : (0 : WithZero (Multiplicative ℤ)) ≤ 1))
  refine ⟨u, hu0, ?_⟩
  rcases hg with hg | hg
  · rw [show algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) g
        = algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (Work.MotV.fAS 𝕜) from by
      rw [hg]] at hu
    exact hu
  · rw [show algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) g
        = algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
            ((2 : RatFunc 𝕜) * Work.MotV.fAS 𝕜) from by rw [hg, htwosmul]] at hu
    rw [map_mul, Valuation.map_mul, hv2, one_mul] at hu
    exact hu

end Work.MotV5.Nodes
