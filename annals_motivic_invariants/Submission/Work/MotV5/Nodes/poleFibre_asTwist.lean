import Mathlib
import Submission.Work.MotV5.Nodes.fifthPowAtPoles_AS
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.asTwistFieldTrue_basic
import Submission.Work.MotV5.RigAS.twistFieldTrue_sup_asRoot
import Submission.Work.MotV5.RigAS.kleinField_le_twistFieldTrue
import Submission.Work.MotV5.GenAux_asTwistFieldTrue_finrank_and_isSeparable
import Submission.Work.MotV5.Nodes.valuation_extends_finiteDimensional
import Submission.Work.MotV5.Nodes.unique_extension_of_prime_ramified
import Submission.Work.MotV5.FlatDescent
import Submission.Work.MotV5.tp_as
import Submission.Work.MotV5.asCoord_asTwCoord
import Submission.Work.MotV5.Nodes.poleFibre_tp

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The fibre of the AS twist over the pole of `t`

Target of this file: `Work.MotV5.Nodes.poleFibre_asTwist`, the geometric input of the
characteristic-`5` Artin–Schreier branch
(`Work.MotV5.Nodes.PoleFibre 𝕜 ↥(asTwistFieldTrue D g τ σS) t`).  The file is **sorry-free**.

## The statement

`PoleFibre 𝕜 F t` asks, for every `ℤᵐ⁰`-valued valuation `v` of `F` trivial on `𝕜` at which `t` has a
pole, for an element `s ∈ F` with `v (t * s ^ 5) = 1`, i.e. `v t = (v s⁻¹) ^ 5`.  Equivalently: the
pole order of `t` is divisible by `5` at every place above the pole, i.e. the Artin–Schreier twist
`Ω'/F` is unramified at the pole.

## The proof chain

`fifthPow_fAS_of_tp_as ⟹ poleFifthPower_asTwist ⟹ fifthPow_value_of_pole ⟹ poleFibre_asTwist`

* `exists_mul_pow_five_eq_one`: if `v (t³ + t) = (v u) ^ 5` then the witness `s = t / u ^ 2` makes
  `t · s ^ 5` a unit; the arithmetic is `a ^ 3 = b ^ 5 ⟹ a * (a / b ^ 2) ^ 5 = 1` for `a = v t`,
  `b = v u`;
* `fifthPow_fAS_of_tp_as` (**the key input**, in `Nodes/poleFibre_tp.lean`): the master valuation
  lemma `tp_as` applied to the twist field itself.  Its Klein point is provided by the interpolation
  coefficients `asTwCoord D g j`: they are not `σ'`-fixed, but their ratios are
  (`Nodes.asTwistAction_asTwCoord`), so that `asTwCoord D g i / asTwCoord D g j₀ ∈ F` and
  `asCoord W y` is a scalar multiple of the Klein point `(κᵢ/κ₀)ᵢ`;
* `poleFifthPower_asTwist` (**the geometric core**): at every place above the pole of `t` the value
  of `t` itself is a fifth power of the value group — the conclusion of `tp_as` together with the
  pole bookkeeping `v (t³ + t) = (v t)³`;
* `fifthPow_value_of_pole` (from `poleFifthPower_asTwist`): the same for the two parameters
  `g = fAS 𝕜` and `g = 2 • fAS 𝕜`;
* `poleFibre_asTwist` (**the node**): `PoleFibre` for `t = RatFunc.X` over the twist field, from
  `fifthPow_value_of_pole` and `poleFibre_of_fifthPow_value` (the witness `t / u ^ 2`).

## The geometric route, kept for reference

The statement is equivalent to the surface computation `div(t) = [E₀] - 5·E'` on the quotient
`S = (C_L × E)/⟨(σ', T)⟩` (`5 ∣ ord_P(t)` at every place above the pole), and the corresponding
*ring-theoretic* form — the local relation `(t⁻¹)·B = (s ^ 5)·B` on a faithfully flat cover `B` of the
chart `𝒪_v` — is the flat descent `value_eq_fifthPow_of_span_eq` of §3, with the concrete cover
`chartCover = ⟥𝒪_v, Ω'⟧` (faithfully flat by `Nodes/chartCover_faithfullyFlat`) and the assembly in
`Nodes/chartCover_localRelation.lean`.  That route is not needed for the node: the `tp_as` route
above is complete.

## Contents

* `eta`, `eta_mul`, `eta_inv`, `eta_pow`, `eta_exp` — the logarithm of a `ℤᵐ⁰`-valued valuation,
  turning the multiplicative value group into `ℤ`;
* `exists_mul_pow_five_eq_one` — the witness computation above;
* `exists_fifth_pow_value_of_unramified`, `poleFibre_of_fifthPow_value` — the field-theoretic
  reduction of `PoleFibre` to the fifth-power-value statement;
* `inv_mem_valuationSubring`, `value_unit_of_valuationSubring`, `value_eq_fifthPow_of_span_eq` — the
  chart `𝒪_v` and the flat descent; `chartCover` — the cover of the chart at a place;
* `poleFifthPower_asTwist`, `algebraMap_fAS_eq`, `fifthPow_value_of_pole`, `poleFibre_asTwist` — the
  assembly (the node's statement is unchanged).
-/

set_option linter.unusedSectionVars false

namespace Work.MotV5.Nodes

open scoped WithZero

variable {F : Type*} [Field F]

/-- The logarithm of a `ℤᵐ⁰`-valued valuation: the additive value `η x = log (v x)`, so that
`v x = exp (η x)` and `v`-poles are the elements with `η x > 0`. -/
noncomputable def eta (v : Valuation F (WithZero (Multiplicative ℤ))) (x : F) : ℤ := (v x).log

lemma eta_exp (v : Valuation F (WithZero (Multiplicative ℤ))) {x : F} (hx : x ≠ 0) :
    WithZero.exp (eta v x) = v x := WithZero.exp_log (Valuation.ne_zero_iff v |>.mpr hx)

lemma eta_mul (v : Valuation F (WithZero (Multiplicative ℤ))) {x y : F} (hx : x ≠ 0)
    (hy : y ≠ 0) : eta v (x * y) = eta v x + eta v y := by
  rw [eta, Valuation.map_mul, WithZero.log_mul]
  · rfl
  · exact Valuation.ne_zero_iff v |>.mpr hx
  · exact Valuation.ne_zero_iff v |>.mpr hy

lemma eta_inv (v : Valuation F (WithZero (Multiplicative ℤ))) {x : F} (hx : x ≠ 0) :
    eta v x⁻¹ = - eta v x := by
  rw [eta, Valuation.map_inv, WithZero.log_inv]
  rfl

lemma eta_pow (v : Valuation F (WithZero (Multiplicative ℤ))) (x : F) (n : ℕ) :
    eta v (x ^ n) = n * eta v x := by
  rw [eta, Valuation.map_pow, WithZero.log_pow, nsmul_eq_mul]
  rfl

lemma eta_exp_pow (v : Valuation F (WithZero (Multiplicative ℤ))) {x : F} (hx : x ≠ 0) (n : ℕ) :
    WithZero.exp (n * eta v x) = (v x) ^ n := by
  rw [← nsmul_eq_mul, WithZero.exp_nsmul, eta_exp v hx]

/-- **The witness for a fifth-power value.**  If `v (t ^ 3 + t) = (v u) ^ 5` with `u ≠ 0` and
`t` has a pole at `v`, then `s = t / u ^ 2` satisfies `v (t * s ^ 5) = 1`.

The arithmetic is `a ^ 3 = b ^ 5 ⟹ a * (a / b ^ 2) ^ 5 = 1` for `a = v t`, `b = v u`. -/
theorem exists_mul_pow_five_eq_one (v : Valuation F (WithZero (Multiplicative ℤ)))
    (t u : F) (hu : u ≠ 0) (ht : 1 < v t) (h : v (t ^(3:ℕ) + t) = (v u) ^(5:ℕ)) :
    ∃ s : F, v (t * s ^(5:ℕ)) = 1 := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [Valuation.map_zero] at ht
    exact absurd ht (by norm_num)
  have hη : 0 < eta v t := by
    rw [show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from
      WithZero.exp_zero.symm, ← eta_exp v ht0] at ht
    exact WithZero.exp_lt_exp.mp ht
  have htv : v t < v (t ^(3:ℕ)) := by
    rw [Valuation.map_pow, ← eta_exp_pow v ht0 3, ← eta_exp v ht0, WithZero.exp_lt_exp]
    omega
  have hgt : v (t ^(3:ℕ) + t) = (v t) ^(3:ℕ) := by
    rw [Valuation.map_add_eq_of_lt_left v htv, Valuation.map_pow]
  have hrel : 3 * eta v t = 5 * eta v u := by
    have h2 : (v (t ^(3:ℕ) + t)).log = ((v u) ^(5:ℕ)).log := by rw [h]
    rw [hgt, WithZero.log_pow, WithZero.log_pow, nsmul_eq_mul, nsmul_eq_mul] at h2
    simpa only [eta, Nat.cast_ofNat] using h2
  have hu2 : u ^(2:ℕ) ≠ 0 := pow_ne_zero 2 hu
  refine ⟨t * (u ^(2:ℕ))⁻¹, ?_⟩
  have hval : eta v (t * (t * (u ^(2:ℕ))⁻¹) ^(5:ℕ)) = 0 := by
    rw [eta_mul v ht0 (pow_ne_zero 5 (mul_ne_zero ht0 (inv_ne_zero hu2))), eta_pow]
    rw [eta_mul v ht0 (inv_ne_zero hu2), eta_inv v hu2, eta_pow]
    omega
  have hne : t * (t * (u ^(2:ℕ))⁻¹) ^(5:ℕ) ≠ 0 :=
    mul_ne_zero ht0 (pow_ne_zero 5 (mul_ne_zero ht0 (inv_ne_zero hu2)))
  rw [← eta_exp v hne, hval, WithZero.exp_zero]

/-- **The `μ`-argument at an unramified place.**  Let `F ⊆ Ω` be a field extension, `v` a place of
`F`, and `w` an extension of `v` to `Ω` *with the same value group* (the hypothesis `hval`: every
value of `w` on `Ω^×` is the value of an element of `F^×`; for a degree-`5` extension this is the
statement that `w` is unramified over `v`).  If `t ∈ F` has a pole at `v` and `W ∈ Ω` satisfies
`W ^ 5 - W = t ^ 3 + t`, then `v (t ^ 3 + t)` is a fifth power of a value of `F`:

indeed `w W > 1` (otherwise `w (W ^ 5 - W) ≤ 1`), hence `w (W ^ 5 - W) = (w W) ^ 5`, and the
hypothesis gives `w W = f (v u)` for some `u ∈ F^×`; the relation `(w W) ^ 5 = (f (v t)) ^ 3`
and the injectivity of `f` give `(v u) ^ 5 = v (t ^ 3 + t)`. -/
theorem exists_fifth_pow_value_of_unramified {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    (v : Valuation F (WithZero (Multiplicative ℤ))) {Γ₁ : Type*} [LinearOrderedCommGroupWithZero Γ₁]
    (f : WithZero (Multiplicative ℤ) →*₀ Γ₁) (hf : StrictMono f)
    (w : Valuation Ω Γ₁) (hw : ∀ x : F, w (algebraMap F Ω x) = f (v x))
    (hval : ∀ y : Ω, y ≠ 0 → ∃ x : F, x ≠ 0 ∧ w y = f (v x))
    {t : F} (ht : 1 < v t) {W : Ω} (hW : W ^(5:ℕ) - W = algebraMap F Ω (t ^(3:ℕ) + t)) :
    ∃ u : F, u ≠ 0 ∧ (v u) ^(5:ℕ) = v (t ^(3:ℕ) + t) := by
  have hvt3 : v (t ^(3:ℕ) + t) = (v t) ^(3:ℕ) := by
    have htv : v t < v (t ^(3:ℕ)) := by
      rw [Valuation.map_pow]
      exact lt_self_pow₀ ht (by norm_num : (1 : ℕ) < 3)
    rw [Valuation.map_add_eq_of_lt_left v htv, Valuation.map_pow]
  have hft : 1 < f (v t) := by
    rw [← map_one f]
    exact hf ht
  have hwg : w (algebraMap F Ω (t ^(3:ℕ) + t)) = (f (v t)) ^(3:ℕ) := by
    rw [hw, hvt3, map_pow]
  have hgt1 : 1 < (f (v t)) ^(3:ℕ) := one_lt_pow₀ hft (by norm_num)
  have halg : algebraMap F Ω (t ^(3:ℕ) + t) ≠ 0 := by
    intro h0
    have h1 : w (algebraMap F Ω (t ^(3:ℕ) + t)) = 0 := by rw [h0, map_zero]
    rw [hwg] at h1
    exact (ne_of_gt (lt_trans zero_lt_one hgt1)) h1
  have hW0 : W ≠ 0 := by
    intro h0
    refine halg ?_
    rw [← hW, h0]
    simp
  have hμ1 : 1 < w W := by
    by_contra hle
    push_neg at hle
    have h5 : w (W ^(5:ℕ)) ≤ 1 := by
      rw [Valuation.map_pow]
      exact pow_le_one₀ (a := w W) zero_le hle
    have : w (W ^(5:ℕ) - W) ≤ 1 := Valuation.map_sub_le w h5 hle
    rw [hW, hwg] at this
    exact absurd this (not_le.mpr hgt1)
  have hval_μ : w (W ^(5:ℕ) - W) = (w W) ^(5:ℕ) := by
    have hlt : w (-W) < w (W ^(5:ℕ)) := by
      rw [Valuation.map_neg, Valuation.map_pow]
      exact lt_self_pow₀ hμ1 (by norm_num : (1 : ℕ) < 5)
    rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left w hlt, Valuation.map_pow]
  have hrel : (w W) ^(5:ℕ) = (f (v t)) ^(3:ℕ) := by
    rw [← hval_μ, hW, hwg]
  obtain ⟨u, hu, hu'⟩ := hval W hW0
  refine ⟨u, hu, ?_⟩
  have : f ((v u) ^(5:ℕ)) = f (v (t ^(3:ℕ) + t)) := by
    rw [map_pow, ← hu', hrel, ← hw (t ^(3:ℕ) + t), hwg]
  exact hf.injective this

/-- **`PoleFibre` follows from the fifth-power-value statement for `t ^ 3 + t`.**  This is the
reduction that isolates the geometric content of `PoleFibre` in the *value* statement: if at every
place above the pole of `t` the value of `t ^ 3 + t` is a fifth power of the value group (with a
witness in the field), then so is the value of `t`. -/
theorem poleFibre_of_fifthPow_value {𝕜 : Type} [Field 𝕜] {F : Type*} [Field F]
    [Algebra 𝕜 F] [Algebra (RatFunc 𝕜) F] (t : F)
    (h : ∀ v : Valuation F (WithZero (Multiplicative ℤ)), Work.MotV.TrivOn 𝕜 v → 1 < v t →
      ∃ u : F, u ≠ 0 ∧ v (t ^(3:ℕ) + t) = (v u) ^(5:ℕ)) :
    ∀ v : Valuation F (WithZero (Multiplicative ℤ)), Work.MotV.TrivOn 𝕜 v → 1 < v t →
      ∃ s : F, v (t * s ^(5:ℕ)) = 1 := by
  intro v hv hvt
  obtain ⟨u, hu, hu'⟩ := h v hv hvt
  exact exists_mul_pow_five_eq_one v t u hu hvt hu'

/-! ## §3 The descent on the chart of the pole

The flat-descent step of the *geometric* route to `poleFifthPower_asTwist`, kept for reference (the
proof of the node uses instead the `tp_as` route of §5):

* `value_eq_fifthPow_of_span_eq` — **the descent**: if `B` is a faithfully flat `𝒪_v`-algebra and
  `t⁻¹` and `s ^ 5` generate the same ideal of `B` (for some `s ∈ 𝒪_v`), then `v t = (v s⁻¹) ^ 5` is
  a fifth power of the value group.  The algebra is `exists_unit_of_map_span_eq` (flat descent of a
  principal-ideal equality to a unit);
* `value_fifthPow_of_localRelation` — the reduction: such a `B` and `s` at a place above the pole
  (the local relation `(t⁻¹)·B = (s ^ 5)·B`, i.e. the pole divisor of `t` has multiplicity `5`)
  `⟹` the geometric core;
* `chartCover` — the concrete cover `B = ⟥𝒪_v, Ω'⟧`, faithfully flat over `𝒪_v` by
  `Nodes/chartCover_faithfullyFlat` (the integral closure of `𝒪_v` in `Ω' = asFieldL D g`); the
  assembly with this cover is in `Nodes/chartCover_localRelation.lean`. -/

section Descent

/-- **`t⁻¹` lies in the valuation ring at a pole.** -/
theorem inv_mem_valuationSubring {F : Type*} [Field F]
    (v : Valuation F (WithZero (Multiplicative ℤ))) {t : F} (ht : 1 < v t) :
    t⁻¹ ∈ v.valuationSubring := by
  rw [Valuation.mem_valuationSubring_iff, Valuation.map_inv]
  exact le_of_lt (inv_lt_one_of_one_lt₀ ht)

/-- **The value of a unit of the valuation ring is `1`.** -/
theorem value_unit_of_valuationSubring {F : Type*} [Field F]
    (v : Valuation F (WithZero (Multiplicative ℤ))) (u : Units ↥(v.valuationSubring)) :
    v (((u : Units ↥(v.valuationSubring)) : ↥(v.valuationSubring)) : F) = 1 := by
  have hcoe : ∀ x y : ↥(v.valuationSubring),
      (((x * y : ↥(v.valuationSubring)) : ↥(v.valuationSubring)) : F) =
        (((x : ↥(v.valuationSubring)) : F)) * (((y : ↥(v.valuationSubring)) : F)) :=
    fun x y => rfl
  have h1 : v (((u : Units ↥(v.valuationSubring)) : ↥(v.valuationSubring)) : F) ≤ 1 :=
    (Valuation.mem_valuationSubring_iff v _).mp
      ((u : Units ↥(v.valuationSubring)) : ↥(v.valuationSubring)).2
  have h2 : v ((((u⁻¹ : Units ↥(v.valuationSubring)) : ↥(v.valuationSubring))) : F) ≤ 1 :=
    (Valuation.mem_valuationSubring_iff v _).mp
      ((u⁻¹ : Units ↥(v.valuationSubring)) : ↥(v.valuationSubring)).2
  have hmul : v (((u : Units ↥(v.valuationSubring)) : ↥(v.valuationSubring)) : F) *
      v ((((u⁻¹ : Units ↥(v.valuationSubring)) : ↥(v.valuationSubring))) : F) = 1 := by
    rw [← Valuation.map_mul, ← hcoe, Units.mul_inv]
    simpa using Valuation.map_one v
  have hne : v (((u : Units ↥(v.valuationSubring)) : ↥(v.valuationSubring)) : F) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact zero_ne_one hmul
  have h3 : (v (((u : Units ↥(v.valuationSubring)) : ↥(v.valuationSubring)) : F))⁻¹ ≤ 1 := by
    rw [← eq_inv_of_mul_eq_one_right hmul]
    exact h2
  exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr hne)).mp h3)

/-- **The descent step of the pole-fibre argument.**  Let `v` be a `ℤᵐ⁰`-valued valuation of the
field `F` at which `t` has a pole, and let `B` be a faithfully flat `𝒪_v`-algebra.  If, for some
`s ∈ 𝒪_v`, the principal ideals generated by `t⁻¹` and by `s ^ 5` coincide after extension to `B`,
then the value of `t` is a fifth power of the value group: `v t = (v (s⁻¹)) ^ 5`.

This is the *flat descent* of the local computation on the étale cover (`B`) to the base (`𝒪_v`):
the algebra is `exists_unit_of_map_span_eq`. -/
theorem value_eq_fifthPow_of_span_eq {F : Type*} [Field F]
    (v : Valuation F (WithZero (Multiplicative ℤ))) {t : F} (ht : 1 < v t)
    (B : Type*) [CommRing B] [Algebra ↥(v.valuationSubring) B]
    [Module.FaithfullyFlat ↥(v.valuationSubring) B] {s : ↥(v.valuationSubring)}
    (h : Ideal.map (algebraMap ↥(v.valuationSubring) B)
            (Ideal.span {⟨t⁻¹, inv_mem_valuationSubring v ht⟩}) =
          Ideal.map (algebraMap ↥(v.valuationSubring) B) (Ideal.span {s ^(5:ℕ)})) :
    v t = (v (algebraMap ↥(v.valuationSubring) F s)⁻¹) ^(5:ℕ) := by
  have ht0 : t ≠ 0 := fun h0 => by rw [h0, Valuation.map_zero] at ht; exact absurd ht (by norm_num)
  obtain ⟨u, hu⟩ := exists_unit_of_map_span_eq (A := ↥(v.valuationSubring)) (B := B)
    (by intro h0
        have h1 : t⁻¹ = 0 := by simpa using congrArg Subtype.val h0
        exact inv_ne_zero ht0 h1) h
  have hu' : algebraMap ↥(v.valuationSubring) F (s ^(5:ℕ)) =
      algebraMap ↥(v.valuationSubring) F (⟨t⁻¹, inv_mem_valuationSubring v ht⟩ *
        (u : ↥(v.valuationSubring))) := by rw [hu]
  have h2 : (v (algebraMap ↥(v.valuationSubring) F s)) ^(5:ℕ) = v t⁻¹ := by
    have h3 := congrArg v hu'
    simp only [map_pow (algebraMap ↥(v.valuationSubring) F), Valuation.map_pow,
      map_mul (algebraMap ↥(v.valuationSubring) F), Valuation.map_mul,
      ValuationSubring.algebraMap_apply, value_unit_of_valuationSubring v u, mul_one] at h3
    exact h3
  rw [Valuation.map_inv]
  have h6 : v t = ((v (algebraMap ↥(v.valuationSubring) F s)) ^(5:ℕ))⁻¹ := by
    rw [h2, Valuation.map_inv, inv_inv]
  rw [h6, inv_pow]

end Descent

section LocalRelation

open Work.MotV

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-- The algebra structure of `Ω' = asFieldL D g` over the chart `𝒪_v` (through
`F = asTwistFieldTrue D g τ σS`). -/
noncomputable def algebraChartAsFieldL (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (v : Valuation ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (WithZero (Multiplicative ℤ))) :
    Algebra ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g) :=
  RingHom.toAlgebra
    ((IntermediateField.inclusion
        (Work.MotV5.asTwistFieldTrue_le_asFieldL (𝕜 := 𝕜) D g τ σS)).toRingHom.comp
      (algebraMap ↥(v.valuationSubring) ↥(Work.MotV5.asTwistFieldTrue D g τ σS)))

/-- **The cover of the chart at a place.**  The chart is `A = 𝒪_v = v.valuationSubring` (its
fraction field is `F = asTwistFieldTrue D g τ σS`), and the cover is the integral closure of `A` in
`Ω' = asFieldL D g`, along the algebra structure `A → F → Ω'`.  It is a finite free `A`-module of
rank `5` (`[Ω' : F] = 5`) and carries the `ℤ/5`-action of `σ' = asTwistAction D τ σS`. -/
noncomputable def chartCover (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (v : Valuation ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (WithZero (Multiplicative ℤ))) :
    @Subalgebra ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g) _ _
      (algebraChartAsFieldL D g τ σS v) :=
  @integralClosure ↥(v.valuationSubring) ↥(Work.MotV5.asFieldL D g) _ _
    (algebraChartAsFieldL D g τ σS v)

/-- **The reduction of the geometric core to the local relation** (via the flat descent): the local
relation at the pole gives that the value of `t` at a place above the pole is a fifth power of the
value group. -/
theorem value_fifthPow_of_localRelation (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (v : Valuation ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (WithZero (Multiplicative ℤ)))
    (hvt : 1 < v (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X))
    (hrel : ∃ (B : Type) (_ : CommRing B) (_ : Algebra ↥(v.valuationSubring) B)
      (_ : Module.FaithfullyFlat ↥(v.valuationSubring) B) (s : ↥(v.valuationSubring)),
      Ideal.map (algebraMap ↥(v.valuationSubring) B)
          (Ideal.span {⟨(algebraMap (RatFunc 𝕜) _ RatFunc.X)⁻¹, inv_mem_valuationSubring v hvt⟩}) =
        Ideal.map (algebraMap ↥(v.valuationSubring) B) (Ideal.span {s ^(5:ℕ)})) :
    ∃ s' : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
      v (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X) = (v s') ^(5:ℕ) := by
  obtain ⟨B, hRing, hAlg, hFlat, s, hs⟩ := hrel
  letI := hRing
  letI := hAlg
  letI := hFlat
  refine ⟨(algebraMap ↥(v.valuationSubring) _ s)⁻¹, ?_⟩
  have h := value_eq_fifthPow_of_span_eq v hvt B hs
  simpa using h

end LocalRelation

/-- **The geometric core of `poleFibre_asTwist`, isolated.**  At every place `v` of the AS twist
field `F = asTwistFieldTrue D g τ σS` above the pole of `t = RatFunc.X`, the **pole order of `t`**
is a fifth power of the value group: `v t = (v s) ^ 5` for some `s ∈ F`.

Equivalently (`PoleFibre.fifthPow`): `5 ∣ ord_P(t)` at every place `P` above the pole of `t`, i.e.
the twist field is *totally ramified of index* `5` over the pole of `t`.

## The proof (the `tp_as` route)

The statement is equivalent to the geometric picture — `F` is the function field of the quotient
surface `S = (C_L × E)/⟨(deck, T)⟩` of the Artin–Schreier curve `C_L` (`℘(w) = t³ + t` over the
`t`-line) with the elliptic curve `E`, the five zero curves of `t` form a single orbit and the pole
divisor is `5 · E'`, so `5 ∣ ord_P(t)` — but it is *not* necessary to build the surface: the master
valuation lemma `Work.MotV5.tp_as` produces the divisibility directly.

Its input is exactly the Klein point of the twist field: the interpolation coefficients
`asTwCoord D g j` of the Klein point `(κᵢ/κ₀)ᵢ` at the nodes `W + i` are not `σ'`-fixed, but their
ratios are (`asTwistAction_asTwCoord`, the algebraic core of `Nodes/poleFibre_tp.lean`), and the
ratios of consecutive coefficients give back exactly the Klein point of the twist field.  Hence the
ratios `asTwCoord D g i / asTwCoord D g j₀ ∈ F` form a Klein point `asCoord W y`, all hypotheses of
`tp_as` are met, and its conclusion `∃ u ∈ F, v g = (v u) ^ 5` together with the pole bookkeeping
`v (t³ + t) = (v t)³` (`exists_mul_pow_five_eq_one`) gives the statement.

The same conclusion also follows from the *local relation* `(t⁻¹)·B = (s⁵)·B` on the faithfully flat
cover `B = ⟥𝒪_v, Ω'⟧` of the chart (`value_eq_fifthPow_of_span_eq`, and its concrete form in
`Nodes/chartCover_localRelation.lean`); that geometric form is the surface computation
`div(t) = E₀ - 5·E'`. -/
theorem poleFifthPower_asTwist (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜)
    (hg : g = Work.MotV.fAS 𝕜 ∨ g = 2 • Work.MotV.fAS 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ) :
    ∀ v : Valuation ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (WithZero (Multiplicative ℤ)),
      Work.MotV.TrivOn 𝕜 v →
      1 < v (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X) →
      ∃ s : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
        v (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X) = (v s) ^(5:ℕ) := by
  intro v hv hvt
  obtain ⟨u, hu, hu'⟩ := Work.MotV5.Nodes.fifthPow_fAS_of_tp_as D g hD hg τ σS σ h v hv hvt
  have ht3t : v ((algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X) ^(3:ℕ)
      + algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X) = (v u) ^(5:ℕ) := by
    rw [← map_pow, ← map_add, ← Work.MotV.fAS]
    exact hu'
  obtain ⟨s, hs⟩ := exists_mul_pow_five_eq_one v
    (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X) u hu hvt ht3t
  refine ⟨s⁻¹, ?_⟩
  have hsplit : v ((algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X) * s ^(5:ℕ))
      = v (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X) * (v s) ^(5:ℕ) := by
    rw [Valuation.map_mul, Valuation.map_pow]
  have hprod : v (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X)
      * (v s) ^(5:ℕ) = 1 := by
    rw [← hsplit]; exact hs
  have hvt' : v (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X)
      = ((v s) ^(5:ℕ))⁻¹ := eq_inv_of_mul_eq_one_left hprod
  rw [hvt', Valuation.map_inv, inv_pow]

/-- The image of the Artin–Schreier parameter is `t ^ 3 + t`. -/
theorem algebraMap_fAS_eq {𝕜 F : Type*} [Field 𝕜] [Field F] [Algebra (RatFunc 𝕜) F] :
    algebraMap (RatFunc 𝕜) F (Work.MotV.fAS 𝕜)
      = (algebraMap (RatFunc 𝕜) F RatFunc.X) ^(3:ℕ) + algebraMap (RatFunc 𝕜) F RatFunc.X := by
  rw [Work.MotV.fAS, map_add, map_pow]

/-- **The geometric input of `poleFibre_asTwist`, isolated.**  At every place `v` of the AS twist
field `F = asTwistFieldTrue D g τ σS` above the pole of `t = RatFunc.X`, the value of `g` is a
fifth power of the value group, realised by an element of `F`.

Note that `g = t ^ 3 + t` or `g = 2 * (t ^ 3 + t)`, and `2` is a unit at every place trivial on
`𝕜` (the base field has characteristic `5`), so the two cases are equivalent; the statement is
written for `g` itself because that is the form in which the fibre computation produces it.

This follows from the geometric core `poleFifthPower_asTwist` by the valuation bookkeeping
`v (t ^ 3 + t) = (v t) ^ 3` (the term `t ^ 3` strictly dominates `t` at a pole). -/
theorem fifthPow_value_of_pole (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜)
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
        = (v u) ^(5:ℕ) := by
  obtain ⟨s, hs⟩ := poleFifthPower_asTwist 𝕜 D hD g hg τ σS σ h v hv hvt
  obtain ⟨u, hu⟩ := fifthPow_pow_three_add v (algebraMap (RatFunc 𝕜) _ RatFunc.X) hvt ⟨s, hs⟩
  -- `v (t ^ 3 + t) = (v t) ^ 3` is a pole, hence nonzero, hence `u ≠ 0`
  have hne : v ((algebraMap (RatFunc 𝕜) _ RatFunc.X) ^(3:ℕ) + algebraMap (RatFunc 𝕜) _ RatFunc.X)
      ≠ 0 := by
    have hdom : v (algebraMap (RatFunc 𝕜) _ RatFunc.X) <
        v ((algebraMap (RatFunc 𝕜) _ RatFunc.X) ^(3:ℕ)) := by
      rw [Valuation.map_pow]
      exact lt_self_pow₀ hvt (by norm_num : (1 : ℕ) < 3)
    rw [Valuation.map_add_eq_of_lt_left v hdom, Valuation.map_pow]
    exact pow_ne_zero 3 (ne_of_gt (lt_trans zero_lt_one hvt))
  refine ⟨u, fun h0 => hne ?_, ?_⟩
  · rw [hu, h0, Valuation.map_zero v, zero_pow (by norm_num : (5 : ℕ) ≠ 0)]
  · simpa only [algebraMap_fAS_eq] using hu

theorem poleFibre_asTwist (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜)
    (hg : g = Work.MotV.fAS 𝕜 ∨ g = 2 • Work.MotV.fAS 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ) :
    Work.MotV5.Nodes.PoleFibre 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X) := by
  refine poleFibre_of_fifthPow_value _ fun v hv hvt => ?_
  obtain ⟨u, hu, hu'⟩ := fifthPow_value_of_pole 𝕜 D hD g hg τ σS σ h v hv hvt
  exact ⟨u, hu, by simpa only [algebraMap_fAS_eq] using hu'⟩

/-! ## §5 The Klein point of the twist field (the `tp_as` route)

The single geometric input `localRelation_asTwist` of §3 is in fact *not* the sharp form of the
statement: the whole content is recovered from the master valuation lemma `Work.MotV5.tp_as`,
applied to the twist field itself.  The Klein coordinates of the twist field do have `F`-coefficients
in the Artin–Schreier basis `1, W, …, W⁴`: the interpolation coefficients of the Klein point
`(κ_i/κ_0)_i` at the nodes `W + i` are `asTwCoord D g j`, they are not `σ'`-fixed, but their
*ratios* are (`Work.MotV5.Nodes.asTwistAction_asTwCoord`).  Hence
`y_j := asTwCoord D g k / asTwCoord D g j₀` lies in `F = asTwistFieldTrue D g τ σS` and
`asCoord W y = (asTwCoord D g j₀)⁻¹ · (κ_i/κ_0)_i` is a Klein point, so all hypotheses of `tp_as`
are met and its conclusion `∃ u ∈ F, v g = (v u) ^ 5` follows. -/

end Work.MotV5.Nodes
