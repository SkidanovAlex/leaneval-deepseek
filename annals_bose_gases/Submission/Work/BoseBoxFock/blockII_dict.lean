import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.aQ_aQ_sym_box
import Submission.Work.BoseBoxFock.abox_pair_split_integral
import Submission.Work.BoseBoxFock.boxProj_pairing
import Submission.Work.BoseBoxFock.boxRestrict_triple_reduce
import Submission.Work.BoseBoxFock.pairWeightMeas
import Submission.Work.BoseBoxFock.rowShape_pinCond_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.blockII_dict` — the block-`II` (`T₄`) dictionary of FS `lem:2ndQuand`

The per-pair identity `½ℓ⁻³(Re rowShape21 + Re rowShape23) = ∫_{abox}(PᵢPⱼΨ)(QⱼQᵢΨ)k(xᵢ,xⱼ)`:
the box row shape at the projected kernel `qmqKernel ℓ k = Q M_k Q` equals the first-quantised
`T₄` word at the **raw** kernel `k` — the box projections `Q` are absorbed by the `P`/`Q`
structure of the word.

The proof has three layers, all `sorry`-free in this file:

* `bII_rowShape21_re` / `bII_rowShape23_re`: the two row shapes, at the pinned condensate, are `ℓ⁻³` times
  the corresponding plain triple integrals over `abox × acube × acube` (the pinning factor is
  `c·c = ℓ⁻³`, resp. `c̄·c̄ = ℓ⁻³`; the real kernel `qmqKR` is the cast of `qmqKernel`);
* `bII_TermA_eq` / `bII_TermB_eq`: each triple integral is `ℓ⁶` times the pair word.  For block `II.1`
  this uses the projection pairing (`boxProj_pairing`) in the free variables, the slot
  self-adjointness of `PᵢPⱼ` (`bII_split_selfadj`), and the box splitting
  (`abox_pair_split_integral`); for block `II.2` it uses the kernel identity
  `qmqKR (x i) (x j) = (QᵢQⱼ k(·ᵢ,·ⱼ))(x)` (`bII_qmqKR_slot_eq_aQ`) plus the composite
  self-adjointness of `QᵢQⱼ` (`aQ_aQ_sym_box`);
* the final arithmetic `½ℓ⁻³(ℓ⁻³ + ℓ⁻³)ℓ⁶ = 1`.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## 1. Elementary auxiliary lemmas -/

theorem bII_cube_cancel (ℓ X : ℝ) (hℓ : ℓ ≠ 0) : ℓ ^ 3 * ((ℓ ^ 3)⁻¹ * X) = X := by
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 3 hℓ), one_mul]

theorem bII_eq_cube_mul_inv (ℓ X : ℝ) (hℓ : ℓ ≠ 0) : X = ℓ ^ 3 * ((ℓ ^ 3)⁻¹ * X) :=
  (bII_cube_cancel ℓ X hℓ).symm

/-- `∫ (1_s)·g = ∫_s g` for a measurable set. -/
theorem bII_integral_indicator_one_mul {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) (g : α → ℝ) :
    (∫ x, s.indicator (fun _ => (1 : ℝ)) x * g x ∂μ) = ∫ x in s, g x ∂μ := by
  rw [← MeasureTheory.integral_indicator (μ := μ) (f := g) hs]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ s
  · simp [Set.indicator_of_mem, hx]
  · simp [Set.indicator_of_notMem, hx]

/-- The real-valued box restriction, pointwise. -/
theorem bII_boxRestrictR_of_mem {n : ℕ} {ℓ : ℝ} {Ψ : Xn n → ℝ} {x : Xn n}
    (hx : x ∈ Submission.BoseGases.abox n ℓ) : boxRestrictR ℓ Ψ x = Ψ x := by
  rw [boxRestrictR, Set.indicator_of_mem hx, mul_one]

theorem bII_boxRestrictR_eq_zero {n : ℕ} {ℓ : ℝ} {Ψ : Xn n → ℝ} {x : Xn n}
    (hx : x ∉ Submission.BoseGases.abox n ℓ) : boxRestrictR ℓ Ψ x = 0 := by
  rw [boxRestrictR, Set.indicator_of_notMem hx, mul_zero]

theorem bII_boxRestrictR_eq_mul {n : ℕ} {ℓ : ℝ} (Ψ : Xn n → ℝ) (z : Xn n) :
    boxRestrictR ℓ Ψ z = Ψ z * boxRestrictR ℓ (fun _ => (1 : ℝ)) z := by
  rw [boxRestrictR, boxRestrictR]
  ring

theorem bII_boxRestrictR_one_apply {n : ℕ} {ℓ : ℝ} (z : Xn n) :
    boxRestrictR ℓ (fun _ => (1 : ℝ)) z
      = (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) z := by
  rw [boxRestrictR, one_mul]

/-- The `p.1`-slot of a twice-updated configuration. -/
theorem bII_update_apply_left {n : ℕ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    (x : Xn n) (y u : E3) :
    (Function.update (Function.update x p.1 y) p.2 u) p.1 = y := by
  simp [Function.update_apply, hp]

theorem bII_update_apply_right {n : ℕ} (x : Xn n) (y u : E3) (p : Fin n × Fin n) :
    (Function.update (Function.update x p.1 y) p.2 u) p.2 = u := by
  simp [Function.update_apply]

theorem bII_mem_acube_of_mem_abox_update {n : ℕ} {ℓ : ℝ} {p : Fin n × Fin n}
    {x : Xn n} {y u : E3}
    (h : Function.update (Function.update x p.1 y) p.2 u ∈ Submission.BoseGases.abox n ℓ) :
    u ∈ Submission.BoseGases.acube ℓ := by
  have h2 := (Submission.BoseGases.mem_abox_iff n ℓ _).mp h p.2
  rwa [bII_update_apply_right x y u p] at h2

theorem bII_mem_acube_of_mem_abox_update_left {n : ℕ} {ℓ : ℝ} {p : Fin n × Fin n}
    (hp : p.1 ≠ p.2) {x : Xn n} {y u : E3}
    (h : Function.update (Function.update x p.1 y) p.2 u ∈ Submission.BoseGases.abox n ℓ) :
    y ∈ Submission.BoseGases.acube ℓ := by
  have h1 := (Submission.BoseGases.mem_abox_iff n ℓ _).mp h p.1
  rwa [bII_update_apply_left hp x y u] at h1

/-- Membership of the twice-updated configuration. -/
theorem bII_mem_abox_update_update {n : ℕ} {ℓ : ℝ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {x : Xn n} (hx : x ∈ Submission.BoseGases.abox n ℓ) (y u : E3) :
    Function.update (Function.update x p.1 y) p.2 u ∈ Submission.BoseGases.abox n ℓ
      ↔ y ∈ Submission.BoseGases.acube ℓ ∧ u ∈ Submission.BoseGases.acube ℓ := by
  rw [Submission.BoseGases.mem_abox_iff]
  constructor
  · intro h
    exact ⟨bII_mem_acube_of_mem_abox_update_left hp h, bII_mem_acube_of_mem_abox_update h⟩
  · rintro ⟨hy, hu⟩ k
    rw [Function.update_apply]
    by_cases hk : k = p.2
    · rw [if_pos hk]
      exact hu
    · rw [if_neg hk, Function.update_apply]
      by_cases hk' : k = p.1
      · rw [if_pos hk']
        exact hy
      · rw [if_neg hk']
        exact (Submission.BoseGases.mem_abox_iff n ℓ x).mp hx k

/-! ## 2. Slot-mean algebra -/

/-- The slot mean of a product with a function that is constant in the slot. -/
theorem bII_aP_mul_of_const_coord {n : ℕ} {ℓ : ℝ} (i : Fin n) {c f : Xn n → ℝ}
    (hc : ∀ x z, c (Function.update x i z) = c x) :
    aP ℓ i (fun x => c x * f x) = fun x => c x * aP ℓ i f x := by
  funext x
  simp only [aP]
  rw [show (fun y : E3 => c (Function.update x i y) * f (Function.update x i y))
      = fun y : E3 => c x * f (Function.update x i y) from by
    funext y
    rw [hc x y]]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- The complementary slot of a product with a function constant in the slot. -/
theorem bII_aQ_mul_of_const_coord {n : ℕ} {ℓ : ℝ} (i : Fin n) {c f : Xn n → ℝ}
    (hc : ∀ x z, c (Function.update x i z) = c x) :
    aQ ℓ i (fun x => c x * f x) = fun x => c x * aQ ℓ i f x := by
  funext x
  have h : aP ℓ i (fun x => c x * f x) x = c x * aP ℓ i f x :=
    congrFun (bII_aP_mul_of_const_coord (ℓ := ℓ) (c := c) (f := f) i hc) x
  simp only [aQ]
  rw [h]
  ring

/-- The complementary slot of a product with a function constant in the *right* factor. -/
theorem bII_aQ_mul_const_right {n : ℕ} {ℓ : ℝ} (i : Fin n) {c f : Xn n → ℝ}
    (hc : ∀ x z, c (Function.update x i z) = c x) :
    aQ ℓ i (fun x => f x * c x) = fun x => c x * aQ ℓ i f x := by
  rw [show (fun x => f x * c x) = fun x => c x * f x from by funext x; ring]
  exact bII_aQ_mul_of_const_coord i hc

/-- The two nested slot means are the full double box integral of the twice-updated
configuration. -/
theorem bII_pair_mean {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    (Φ : Xn n → ℝ) (x : Xn n) :
    (∫ y in Submission.BoseGases.acube ℓ, ∫ u in Submission.BoseGases.acube ℓ,
        Φ (Function.update (Function.update x i y) j u))
      = (ℓ ^ 3) * (ℓ ^ 3) * aP ℓ i (aP ℓ j Φ) x := by
  have hinner : ∀ y : E3,
      (∫ u in Submission.BoseGases.acube ℓ,
          Φ (Function.update (Function.update x i y) j u))
        = (ℓ ^ 3) * (aP ℓ j Φ (Function.update x i y)) := by
    intro y
    rw [aP, one_div]
    exact (bII_cube_cancel ℓ _ (ne_of_gt hℓ)).symm
  rw [show (fun y : E3 => ∫ u in Submission.BoseGases.acube ℓ,
        Φ (Function.update (Function.update x i y) j u))
      = fun y : E3 => (ℓ ^ 3) * (aP ℓ j Φ (Function.update x i y)) from by
    funext y; exact hinner y]
  rw [MeasureTheory.integral_const_mul]
  have houter : (∫ y in Submission.BoseGases.acube ℓ, aP ℓ j Φ (Function.update x i y))
      = (ℓ ^ 3) * (aP ℓ i (aP ℓ j Φ) x) := by
    rw [aP, one_div]
    exact (bII_cube_cancel ℓ _ (ne_of_gt hℓ)).symm
  rw [houter]
  ring

/-! ## 3. Pointwise kernel identities -/

/-- **The slot form of the `Q M Q` kernel.** -/
theorem bII_qmqKR_slot_eq_aQ {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    (k : E3 → E3 → ℝ) (hkm : Measurable (Function.uncurry k)) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hkb : ∀ w y, |k w y| ≤ Cg) (x : Xn n) :
    qmqKR ℓ k (x i) (x j)
      = aQ ℓ i (aQ ℓ j (fun z : Xn n => k (z i) (z j))) x := by
  have hgm : Measurable (fun z : Xn n => k (z i) (z j)) := by
    have h3 : (fun z : Xn n => k (z i) (z j))
        = (Function.uncurry k) ∘ (fun z : Xn n => ((z i, z j) : E3 × E3)) := by
      funext z
      rfl
    rw [h3]
    exact hkm.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
  have hgb : ∀ z : Xn n, |k (z i) (z j)| ≤ Cg := fun z => hkb _ _
  have h1 : aP ℓ i (fun z : Xn n => k (z i) (z j)) x
      = ((ℓ ^ 3)⁻¹ : ℝ) * (∫ w' in Submission.BoseGases.acube ℓ, k w' (x j)) := by
    have hI : (∫ y in Submission.BoseGases.acube ℓ,
          k ((Function.update x i y) i) ((Function.update x i y) j))
        = ∫ w' in Submission.BoseGases.acube ℓ, k w' (x j) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp [hij, Ne.symm hij]
    simp only [aP]
    rw [one_div, hI]
  have h2 : aP ℓ j (fun z : Xn n => k (z i) (z j)) x
      = ((ℓ ^ 3)⁻¹ : ℝ) * (∫ y' in Submission.BoseGases.acube ℓ, k (x i) y') := by
    have hI : (∫ u in Submission.BoseGases.acube ℓ,
          k ((Function.update x j u) i) ((Function.update x j u) j))
        = ∫ y' in Submission.BoseGases.acube ℓ, k (x i) y' := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      simp [hij, Ne.symm hij]
    simp only [aP]
    rw [one_div, hI]
  have h3 : aP ℓ i (aP ℓ j (fun z : Xn n => k (z i) (z j))) x
      = ((ℓ ^ 3)⁻¹ : ℝ) ^ 2
        * (∫ w' in Submission.BoseGases.acube ℓ,
            ∫ y' in Submission.BoseGases.acube ℓ, k w' y') := by
    have hI : (fun y : E3 => 1 / ℓ ^ 3 * (∫ u in Submission.BoseGases.acube ℓ,
          k ((Function.update (Function.update x i y) j u) i)
            ((Function.update (Function.update x i y) j u) j)))
        = fun y : E3 => 1 / ℓ ^ 3 * (∫ u in Submission.BoseGases.acube ℓ, k y u) := by
      funext y
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      simp [hij, Ne.symm hij]
    simp only [aP]
    rw [hI]
    beta_reduce
    rw [MeasureTheory.integral_const_mul,
      show (∫ y in Submission.BoseGases.acube ℓ, ∫ u in Submission.BoseGases.acube ℓ, k y u)
        = (∫ w' in Submission.BoseGases.acube ℓ,
            ∫ y' in Submission.BoseGases.acube ℓ, k w' y') from rfl]
    ring
  have hsub : aP ℓ i (aQ ℓ j (fun z : Xn n => k (z i) (z j))) x
      = aP ℓ i (fun z : Xn n => k (z i) (z j)) x
        - aP ℓ i (aP ℓ j (fun z : Xn n => k (z i) (z j))) x := by
    have hfun : aQ ℓ j (fun z : Xn n => k (z i) (z j))
        = (fun z : Xn n => k (z i) (z j)) - aP ℓ j (fun z : Xn n => k (z i) (z j)) := rfl
    rw [hfun]
    exact Weak.aP_sub hℓ i (C := Cg) (D := Cg) hCg hCg hgm hgb
      (Weak.aP_measurable j hgm) (Weak.aP_abs_le hℓ j hCg hgb) x
  rw [qmqKR]
  simp only [aQ]
  rw [hsub, h1, h2, h3]
  ring

/-- The normalisation of a twice-nested update: the earlier updates are overwritten. -/
theorem bII_update_update_update {n : ℕ} {i j : Fin n} (hij : i ≠ j) (f : Xn n)
    (a b y : E3) :
    Function.update (Function.update (Function.update f i a) j b) i y
      = Function.update (Function.update f i y) j b := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [Function.update_apply, hij, Ne.symm hij]
  · by_cases hk' : k = j
    · subst hk'
      simp [Function.update_apply, hij, Ne.symm hij]
    · simp [Function.update_apply, hk, hk']

/-- The outermost of two equal updates is the identity. -/
theorem bII_update_update_idem_aux {n : ℕ} {i : Fin n} (f : Xn n) (a b y : E3) :
    Function.update (Function.update (Function.update f i a) i b) i y
      = Function.update (Function.update f i a) i y := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [Function.update_apply]
  · simp [Function.update_apply, hk]

theorem bII_update_update_update_update {n : ℕ} {i j : Fin n} (hij : i ≠ j) (f : Xn n)
    (a b y y₁ : E3) :
    Function.update (Function.update (Function.update (Function.update f i a) j b) i y) j y₁
      = Function.update (Function.update f i y) j y₁ := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [Function.update_apply, hij, Ne.symm hij]
  · by_cases hk' : k = j
    · subst hk'
      simp [Function.update_apply, hij, Ne.symm hij]
    · simp [Function.update_apply, hk, hk']

/-- `(ℓ³)⁻¹² (ℓ³·ℓ³·X) = X`. -/
theorem bII_cube_inv_sq_mul (ℓ X : ℝ) (hℓ : ℓ ≠ 0) :
    ((ℓ ^ 3)⁻¹ : ℝ) ^ 2 * (ℓ ^ 3 * ℓ ^ 3 * X) = X := by
  rw [show ((ℓ ^ 3)⁻¹ : ℝ) ^ 2 * (ℓ ^ 3 * ℓ ^ 3 * X)
      = ((ℓ ^ 3)⁻¹ * ℓ ^ 3) * ((ℓ ^ 3)⁻¹ * ℓ ^ 3) * X by ring]
  simp only [inv_mul_cancel₀ (pow_ne_zero 3 hℓ), one_mul]

/-- `QᵢQⱼΦ` in terms of the four slot means (for continuous `Φ`). -/
theorem bII_aQ_aQ_eq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    {Φ : Xn n → ℝ} (hΦc : Continuous Φ) (z : Xn n) :
    aQ ℓ i (aQ ℓ j Φ) z = Φ z - aP ℓ i Φ z - aP ℓ j Φ z + aP ℓ i (aP ℓ j Φ) z := by
  have h2 : aP ℓ i (aQ ℓ j Φ) z = aP ℓ i Φ z - aP ℓ i (aP ℓ j Φ) z := by
    have h1 : aQ ℓ j Φ = Φ - aP ℓ j Φ := rfl
    rw [h1]
    exact Submission.BoseGases.aP_sub hℓ i hΦc (Submission.BoseGases.aP_continuous hℓ j hΦc) z
  have h3 : aQ ℓ j Φ z = Φ z - aP ℓ j Φ z := rfl
  calc aQ ℓ i (aQ ℓ j Φ) z = (aQ ℓ j Φ) z - aP ℓ i (aQ ℓ j Φ) z := rfl
    _ = (Φ z - aP ℓ j Φ z) - (aP ℓ i Φ z - aP ℓ i (aP ℓ j Φ) z) := by rw [h2, h3]
    _ = Φ z - aP ℓ i Φ z - aP ℓ j Φ z + aP ℓ i (aP ℓ j Φ) z := by ring

/-- **The two-variable projection of the twice-updated state.** -/
theorem bII_boxProj_update_eq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    {Φ : Xn n → ℝ} (hΦc : Continuous Φ) (x : Xn n) (a b : E3) :
    boxProj ℓ (fun a b => Φ (Function.update (Function.update x i a) j b)) a b
      = aQ ℓ i (aQ ℓ j Φ) (Function.update (Function.update x i a) j b) := by
  have h1 : boxP1 ℓ (fun a b => Φ (Function.update (Function.update x i a) j b)) a b
      = aP ℓ i Φ (Function.update (Function.update x i a) j b) := by
    simp only [boxP1, aP]
    rw [show (∫ y in Submission.BoseGases.acube ℓ,
          Φ (Function.update (Function.update (Function.update x i a) j b) i y))
        = ∫ a' in Submission.BoseGases.acube ℓ,
          Φ (Function.update (Function.update x i a') j b) from by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      beta_reduce
      rw [bII_update_update_update hij x a b y]]
    rw [one_div]
  have h2 : boxP2 ℓ (fun a b => Φ (Function.update (Function.update x i a) j b)) a b
      = aP ℓ j Φ (Function.update (Function.update x i a) j b) := by
    simp only [boxP2, aP]
    rw [show (∫ y in Submission.BoseGases.acube ℓ,
          Φ (Function.update (Function.update (Function.update x i a) j b) j y))
        = ∫ y in Submission.BoseGases.acube ℓ,
          Φ (Function.update (Function.update x i a) j y) from by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      beta_reduce
      rw [Function.update_idem (a := j) (f := Function.update x i a) b y]]
    rw [one_div]
  have h3 : boxP12 ℓ (fun a b => Φ (Function.update (Function.update x i a) j b)) a b
      = aP ℓ i (aP ℓ j Φ) (Function.update (Function.update x i a) j b) := by
    have hXY := bII_pair_mean hℓ hij Φ (Function.update (Function.update x i a) j b)
    have hInt : (∫ y in Submission.BoseGases.acube ℓ, ∫ u in Submission.BoseGases.acube ℓ,
          Φ (Function.update
            (Function.update (Function.update (Function.update x i a) j b) i y) j u))
        = ∫ y in Submission.BoseGases.acube ℓ, ∫ u in Submission.BoseGases.acube ℓ,
          Φ (Function.update (Function.update x i y) j u) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      beta_reduce
      rw [bII_update_update_update_update hij x a b y u]
    rw [boxP12, ← hInt, hXY]
    exact bII_cube_inv_sq_mul ℓ _ (ne_of_gt hℓ)
  rw [boxProj, h1, h2, h3]
  exact (bII_aQ_aQ_eq hℓ hij hΦc (Function.update (Function.update x i a) j b)).symm

/-! ## 4. The support of the box restriction and the row-shape reductions -/

theorem bII_boxRestrictC_support {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (Ψ : Xn n → ℝ) :
    Function.support (boxRestrictC ℓ Ψ) ⊆ Work.MB.boxPow n ℓ := by
  intro x hx
  rw [Work.MB.mem_boxPow_iff]
  have hmem : x ∈ Submission.BoseGases.abox n ℓ := by
    by_contra h
    have h0 : boxRestrictC ℓ Ψ x = 0 := by
      simp [boxRestrictC, Set.indicator_of_notMem h]
    exact hx h0
  intro i
  rw [boxL_eq_acube hℓ]
  exact (Submission.BoseGases.mem_abox_iff n ℓ x).mp hmem i

/-- `QᵢQⱼΦ` in terms of the four slot means, for a continuous state. -/
theorem bII_aQ_aQ_mul_pairMean {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    {Φ : Xn n → ℝ} (hΦc : Continuous Φ) :
    aQ ℓ i (aQ ℓ j (fun x => Φ x * aP ℓ i (aP ℓ j Φ) x))
      = fun x => aP ℓ i (aP ℓ j Φ) x * aQ ℓ i (aQ ℓ j Φ) x := by
  have hPj : ∀ x z, aP ℓ i (aP ℓ j Φ) (Function.update x j z) = aP ℓ i (aP ℓ j Φ) x :=
    fun x z => Submission.BoseGases.aP_pair_const_in_j hℓ hij hΦc x z
  have hPi : ∀ x z, aP ℓ i (aP ℓ j Φ) (Function.update x i z) = aP ℓ i (aP ℓ j Φ) x :=
    fun x z => Weak.aP_const_in_coord i (aP ℓ j Φ) x z
  have hstep1 : aQ ℓ j (fun x => Φ x * aP ℓ i (aP ℓ j Φ) x)
      = fun x => aP ℓ i (aP ℓ j Φ) x * aQ ℓ j Φ x := bII_aQ_mul_const_right j hPj
  have hstep2 : aQ ℓ i (fun x => aP ℓ i (aP ℓ j Φ) x * aQ ℓ j Φ x)
      = fun x => aP ℓ i (aP ℓ j Φ) x * aQ ℓ i (aQ ℓ j Φ) x :=
    bII_aQ_mul_of_const_coord i hPi
  rw [hstep1, hstep2]

/-- Iterated integrals of a coerced real function. -/
theorem bII_integral_ofReal_iter {n : ℕ} {f : Xn n → E3 → E3 → ℝ} :
    (∫ x : Xn n, ∫ y : E3, ∫ u : E3, ((f x y u : ℝ) : ℂ))
      = ((∫ x : Xn n, ∫ y : E3, ∫ u : E3, f x y u : ℝ) : ℂ) := by
  have h2 : ∀ x : Xn n, (∫ y : E3, ∫ u : E3, ((f x y u : ℝ) : ℂ))
      = ((∫ y : E3, ∫ u : E3, f x y u : ℝ) : ℂ) := by
    intro x
    have h3 : ∀ y : E3, (∫ u : E3, ((f x y u : ℝ) : ℂ))
        = ((∫ u : E3, f x y u : ℝ) : ℂ) := fun y => integral_complex_ofReal
    rw [show (fun y : E3 => ∫ u : E3, ((f x y u : ℝ) : ℂ))
        = fun y : E3 => ((∫ u : E3, f x y u : ℝ) : ℂ) from funext h3]
    exact integral_complex_ofReal
  rw [show (fun x : Xn n => ∫ y : E3, ∫ u : E3, ((f x y u : ℝ) : ℂ))
      = fun x : Xn n => ((∫ y : E3, ∫ u : E3, f x y u : ℝ) : ℂ) from funext h2]
  exact integral_complex_ofReal

/-- The real box restriction of a triple integral over the configuration and the two free
variables: the box is the integration region. -/
theorem bII_rowShape21_re {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Xn n → ℝ} (hΨc : Continuous Ψ)
    {k : E3 → E3 → ℝ} (hkm : Measurable (Function.uncurry k))
    {c : ℂ} (hc : (starRingEnd ℂ) c * c * ((ℓ ^ 3 : ℝ) : ℂ) = 1) (hr : (starRingEnd ℂ) c = c)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    (rowShape21 (boxRestrictC ℓ Ψ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
        (qmqKernel ℓ k) p).re
      = ((ℓ ^ 3)⁻¹ : ℝ) * ∫ x in Submission.BoseGases.abox n ℓ,
          ∫ y in Submission.BoseGases.acube ℓ, ∫ u in Submission.BoseGases.acube ℓ,
            Ψ x * qmqKR ℓ k u y
              * Ψ (Function.update (Function.update x p.1 y) p.2 u) := by
  have hΘs := bII_boxRestrictC_support hℓ Ψ
  have h21 := (rowShape_pinCond_gen hℓ (c := c) (Θ := boxRestrictC ℓ Ψ)
      (K := qmqKernel ℓ k) (p := p) hp hΘs).1
  have hpt : ∀ (x : Xn n) (y u : E3),
      star (boxRestrictC ℓ Ψ x) * qmqKernel ℓ k u y
        * boxRestrictC ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u)
      = ((boxRestrictR ℓ Ψ x * qmqKR ℓ k u y
          * boxRestrictR ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u) : ℝ) : ℂ) := by
    intro x y u
    have h1 : star (boxRestrictC ℓ Ψ x) = ((boxRestrictR ℓ Ψ x : ℝ) : ℂ) := by
      rw [← ofReal_boxRestrictR]
      exact Complex.conj_ofReal _
    rw [qmqKernel_eq_ofRealKR, h1, ← ofReal_boxRestrictR]
    push_cast
    ring
  have hI : (∫ x : Xn n, ∫ y : E3, ∫ u : E3, star (boxRestrictC ℓ Ψ x) * qmqKernel ℓ k u y
        * boxRestrictC ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u))
      = (((∫ x : Xn n, ∫ y : E3, ∫ u : E3, boxRestrictR ℓ Ψ x * qmqKR ℓ k u y
          * boxRestrictR ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u)) : ℝ) : ℂ) := by
    simp only [hpt]
    exact bII_integral_ofReal_iter
  have hcc : c * c = (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) := by
    have h1 : c * c * ((ℓ ^ 3 : ℝ) : ℂ) = 1 := by
      have h2 := hc
      rw [hr] at h2
      exact h2
    rw [eq_inv_of_mul_eq_one_left h1, ← Complex.ofReal_inv]
  rw [h21, hI, hcc, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [boxRestrict_triple_reduce hℓ (q := fun _ y u => qmqKR ℓ k u y) hp]

theorem bII_rowShape23_re {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Xn n → ℝ} (hΨc : Continuous Ψ)
    {k : E3 → E3 → ℝ} (hkm : Measurable (Function.uncurry k))
    {c : ℂ} (hc : (starRingEnd ℂ) c * c * ((ℓ ^ 3 : ℝ) : ℂ) = 1) (hr : (starRingEnd ℂ) c = c)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    (rowShape23 (boxRestrictC ℓ Ψ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
        (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y) (qmqKernel ℓ k) p).re
      = ((ℓ ^ 3)⁻¹ : ℝ) * ∫ x in Submission.BoseGases.abox n ℓ,
          ∫ y in Submission.BoseGases.acube ℓ, ∫ u in Submission.BoseGases.acube ℓ,
            Ψ x * qmqKR ℓ k (x p.1) (x p.2)
              * Ψ (Function.update (Function.update x p.1 y) p.2 u) := by
  have hΘs := bII_boxRestrictC_support hℓ Ψ
  have h23 := (rowShape_pinCond_gen hℓ (c := c) (Θ := boxRestrictC ℓ Ψ)
      (K := qmqKernel ℓ k) (p := p) hp hΘs).2
  have hpt : ∀ (x : Xn n) (y u : E3),
      star (boxRestrictC ℓ Ψ x) * qmqKernel ℓ k (x p.1) (x p.2)
        * boxRestrictC ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u)
      = ((boxRestrictR ℓ Ψ x * qmqKR ℓ k (x p.1) (x p.2)
          * boxRestrictR ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u) : ℝ) : ℂ) := by
    intro x y u
    have h1 : star (boxRestrictC ℓ Ψ x) = ((boxRestrictR ℓ Ψ x : ℝ) : ℂ) := by
      rw [← ofReal_boxRestrictR]
      exact Complex.conj_ofReal _
    rw [qmqKernel_eq_ofRealKR, h1, ← ofReal_boxRestrictR]
    push_cast
    ring
  have hI : (∫ x : Xn n, ∫ y : E3, ∫ u : E3, star (boxRestrictC ℓ Ψ x)
        * qmqKernel ℓ k (x p.1) (x p.2)
        * boxRestrictC ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u))
      = (((∫ x : Xn n, ∫ y : E3, ∫ u : E3, boxRestrictR ℓ Ψ x * qmqKR ℓ k (x p.1) (x p.2)
          * boxRestrictR ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u)) : ℝ) : ℂ) := by
    simp only [hpt]
    exact bII_integral_ofReal_iter
  have hcc : c * c = (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) := by
    have h1 : c * c * ((ℓ ^ 3 : ℝ) : ℂ) = 1 := by
      have h2 := hc
      rw [hr] at h2
      exact h2
    rw [eq_inv_of_mul_eq_one_left h1, ← Complex.ofReal_inv]
  have hcc' : (starRingEnd ℂ) c * (starRingEnd ℂ) c = (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) := by
    simpa only [hr] using hcc
  rw [h23, hI, hcc', ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [boxRestrict_triple_reduce hℓ (q := fun x _ _ => qmqKR ℓ k (x p.1) (x p.2)) hp]

/-! ## 5. The two terms -/

/-- Two updates at the same slot. -/
theorem bII_update_update_same {n : ℕ} {i : Fin n} (f : Xn n) (a y : E3) :
    Function.update (Function.update f i a) i y = Function.update f i y := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [Function.update_apply]
  · simp [Function.update_apply, hk]

/-- A `j`-update followed by an `i`-update followed by a `j`-update. -/
theorem bII_update_update_update_same {n : ℕ} {i j : Fin n} (hij : i ≠ j) (f : Xn n)
    (z y u : E3) :
    Function.update (Function.update (Function.update f j z) i y) j u
      = Function.update (Function.update f i y) j u := by
  funext k
  by_cases hk : k = j
  · subst hk
    simp [Function.update_apply]
  · by_cases hk' : k = i
    · subst hk'
      simp [Function.update_apply, hij, Ne.symm hij]
    · simp [Function.update_apply, hk, hk']

/-- A function that is constant in slot `i` is fixed by `aP ℓ i`. -/
theorem bII_aP_eq_self_of_const {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) {H : Xn n → ℝ}
    (hH : ∀ x z, H (Function.update x i z) = H x) :
    aP ℓ i H = H := by
  funext x
  rw [aP]
  rw [show (fun y : E3 => H (Function.update x i y)) = fun _ => H x from by
    funext y
    exact hH x y]
  rw [Submission.BoseGases.integral_const_acube ℓ hℓ (H x), one_div, mul_comm (H x) (ℓ ^ 3),
    ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)), one_mul]

/-- **Self-adjointness of `PᵢPⱼ`** for a state that is constant in the slots `i`, `j`. -/
theorem bII_split_selfadj {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    {Ψ : Xn n → ℝ} (hΨc : Continuous Ψ) {H : Xn n → ℝ} (hHm : Measurable H) {CH : ℝ}
    (hCH : 0 ≤ CH) (hHb : ∀ x ∈ Submission.BoseGases.abox n ℓ, |H x| ≤ CH)
    (hHi : ∀ x z, H (Function.update x i z) = H x)
    (hHj : ∀ x z, H (Function.update x j z) = H x) :
    (∫ x in Submission.BoseGases.abox n ℓ, Ψ x * H x)
      = ∫ x in Submission.BoseGases.abox n ℓ, aP ℓ i (aP ℓ j Ψ) x * H x := by
  have hPi : aP ℓ i H = H := bII_aP_eq_self_of_const hℓ i hHi
  have hPj : aP ℓ j H = H := bII_aP_eq_self_of_const hℓ j hHj
  have hPjΨc : Continuous (aP ℓ j Ψ) := Submission.BoseGases.aP_continuous hℓ j hΨc
  have h1 : (∫ x in Submission.BoseGases.abox n ℓ, aP ℓ i (aP ℓ j Ψ) x * H x)
      = ∫ x in Submission.BoseGases.abox n ℓ, aP ℓ j Ψ x * (aP ℓ i H x) :=
    aP_sym_box_of_boundOn hℓ i hPjΨc hHm hCH hHb
  have h2 : (∫ x in Submission.BoseGases.abox n ℓ, aP ℓ j Ψ x * (aP ℓ i H x))
      = ∫ x in Submission.BoseGases.abox n ℓ, Ψ x * (aP ℓ j (aP ℓ i H) x) :=
    aP_sym_box_of_boundOn hℓ j hΨc (Weak.aP_measurable i hHm) hCH
      (fun x hx => by rw [hPi]; exact hHb x hx)
  have h3 : aP ℓ j (aP ℓ i H) = H := by rw [hPi, hPj]
  have h5 : (∫ x in Submission.BoseGases.abox n ℓ, Ψ x * H x)
      = ∫ x in Submission.BoseGases.abox n ℓ, Ψ x * (aP ℓ j (aP ℓ i H) x) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [h3]
  calc (∫ x in Submission.BoseGases.abox n ℓ, Ψ x * H x)
      = ∫ x in Submission.BoseGases.abox n ℓ, Ψ x * (aP ℓ j (aP ℓ i H) x) := h5
    _ = ∫ x in Submission.BoseGases.abox n ℓ, aP ℓ j Ψ x * (aP ℓ i H x) := h2.symm
    _ = ∫ x in Submission.BoseGases.abox n ℓ, aP ℓ i (aP ℓ j Ψ) x * H x := h1.symm

/-- The projection pairing applied to the twice-updated configuration. -/
theorem bII_pairStep {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Xn n → ℝ} (hΨc : Continuous Ψ)
    {k : E3 → E3 → ℝ} (hkm : Measurable (Function.uncurry k)) {Ck : ℝ}
    (hkb : ∀ w y, |k w y| ≤ Ck) {i j : Fin n} (hij : i ≠ j) (x : Xn n) :
    (∫ y in Submission.BoseGases.acube ℓ, ∫ u in Submission.BoseGases.acube ℓ,
        Ψ (Function.update (Function.update x i y) j u) * qmqKR ℓ k y u)
      = ∫ y in Submission.BoseGases.acube ℓ, ∫ u in Submission.BoseGases.acube ℓ,
          aQ ℓ i (aQ ℓ j Ψ) (Function.update (Function.update x i y) j u) * k y u := by
  have hupd : Continuous (fun p : E3 × E3 => Function.update (Function.update x i p.1) j p.2) :=
    ((continuous_const : Continuous fun _ : E3 × E3 => x).update i continuous_fst).update j
      continuous_snd
  have hFc : Continuous (Function.uncurry
      (fun a b : E3 => Ψ (Function.update (Function.update x i a) j b))) :=
    hΨc.comp hupd
  simp only [← boxProj_eq_qmqKR ℓ k]
  rw [boxProj_pairing hℓ
    (F := fun a b : E3 => Ψ (Function.update (Function.update x i a) j b)) hFc hkm hkb]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  beta_reduce
  rw [bII_boxProj_update_eq hℓ hij hΨc x y u]

/-- A `i`-update followed by an `i`-update followed by a `j`-update. -/
theorem bII_update_update_update_left {n : ℕ} {i j : Fin n} (hij : i ≠ j) (f : Xn n)
    (z y u : E3) :
    Function.update (Function.update (Function.update f i z) i y) j u
      = Function.update (Function.update f i y) j u := by
  funext kk
  by_cases h1 : kk = i
  · subst h1
    simp [Function.update_apply, hij, Ne.symm hij]
  · by_cases h2 : kk = j
    · subst h2
      simp [Function.update_apply, hij, Ne.symm hij]
    · simp [Function.update_apply, h1, h2]

/-- The slot-independence of `PᵢPⱼ`. -/
theorem bII_aP_pair_const_update {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    {Φ : Xn n → ℝ} (hΦc : Continuous Φ) (x : Xn n) (y u : E3) :
    aP ℓ i (aP ℓ j Φ) (Function.update (Function.update x i y) j u) = aP ℓ i (aP ℓ j Φ) x := by
  rw [Submission.BoseGases.aP_pair_const_in_j hℓ hij hΦc (Function.update x i y) u,
    Submission.BoseGases.aP_pair_const_in_i hℓ hij hΦc x y]

/-- **Term `A`** (block `II.1`): the `u,y`-averaged triple integral is `ℓ⁶` times the pair word. -/
theorem bII_TermA_eq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Xn n → ℝ} (hΨc : Continuous Ψ)
    {k : E3 → E3 → ℝ} (hkm : Measurable (Function.uncurry k)) {Ck : ℝ}
    (hkb : ∀ w y, |k w y| ≤ Ck) (hksym : ∀ w y, k w y = k y w)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    (∫ x in Submission.BoseGases.abox n ℓ, ∫ y in Submission.BoseGases.acube ℓ,
        ∫ u in Submission.BoseGases.acube ℓ,
          Ψ x * qmqKR ℓ k u y * Ψ (Function.update (Function.update x p.1 y) p.2 u))
      = (ℓ ^ 3) * (ℓ ^ 3) * ∫ x in Submission.BoseGases.abox n ℓ,
          aP ℓ p.1 (aP ℓ p.2 Ψ) x * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * k (x p.1) (x p.2) := by
  set G : Xn n → ℝ := aQ ℓ p.1 (aQ ℓ p.2 Ψ) with hG
  have hsym : (fun x : Xn n => ∫ y in Submission.BoseGases.acube ℓ,
        ∫ u in Submission.BoseGases.acube ℓ,
          Ψ x * qmqKR ℓ k u y * Ψ (Function.update (Function.update x p.1 y) p.2 u))
      = fun x : Xn n => ∫ y in Submission.BoseGases.acube ℓ,
        ∫ u in Submission.BoseGases.acube ℓ,
          Ψ x * qmqKR ℓ k y u * Ψ (Function.update (Function.update x p.1 y) p.2 u) := by
    funext x
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    beta_reduce
    rw [qmqKR_symm ℓ hksym u y]
  rw [hsym]
  have hpull1 : (fun x : Xn n => ∫ y in Submission.BoseGases.acube ℓ,
        ∫ u in Submission.BoseGases.acube ℓ,
          Ψ x * qmqKR ℓ k y u * Ψ (Function.update (Function.update x p.1 y) p.2 u))
      = fun x : Xn n => Ψ x * (∫ y in Submission.BoseGases.acube ℓ,
          ∫ u in Submission.BoseGases.acube ℓ,
            Ψ (Function.update (Function.update x p.1 y) p.2 u) * qmqKR ℓ k y u) := by
    funext x
    rw [show (fun y : E3 => ∫ u in Submission.BoseGases.acube ℓ,
          Ψ x * qmqKR ℓ k y u * Ψ (Function.update (Function.update x p.1 y) p.2 u))
        = fun y : E3 => Ψ x * (∫ u in Submission.BoseGases.acube ℓ,
            Ψ (Function.update (Function.update x p.1 y) p.2 u) * qmqKR ℓ k y u) from by
      funext y
      rw [show (fun u : E3 => Ψ x * qmqKR ℓ k y u
            * Ψ (Function.update (Function.update x p.1 y) p.2 u))
          = fun u : E3 => Ψ x * (Ψ (Function.update (Function.update x p.1 y) p.2 u)
              * qmqKR ℓ k y u) from by funext u; ring]
      rw [MeasureTheory.integral_const_mul]]
    rw [MeasureTheory.integral_const_mul]
  rw [hpull1]
  have hpair : ∀ x : Xn n, (∫ y in Submission.BoseGases.acube ℓ,
        ∫ u in Submission.BoseGases.acube ℓ,
          Ψ (Function.update (Function.update x p.1 y) p.2 u) * qmqKR ℓ k y u)
      = ∫ y in Submission.BoseGases.acube ℓ, ∫ u in Submission.BoseGases.acube ℓ,
          G (Function.update (Function.update x p.1 y) p.2 u) * k y u :=
    fun x => bII_pairStep hℓ hΨc hkm hkb hp x
  simp only [hpair]
  set H : Xn n → ℝ := fun x => ∫ y in Submission.BoseGases.acube ℓ,
      ∫ u in Submission.BoseGases.acube ℓ,
        G (Function.update (Function.update x p.1 y) p.2 u) * k y u with hH
  obtain ⟨hHm, CH, hCH, hHb⟩ := pairWeightMeas hℓ hΨc hkm hkb hp
  have hHm' : Measurable H := by simpa only [hH, hG] using hHm
  have hHb' : ∀ x ∈ Submission.BoseGases.abox n ℓ, |H x| ≤ CH := by
    intro x hx
    simpa only [hH, hG] using hHb x hx
  have hHi : ∀ x z, H (Function.update x p.1 z) = H x := by
    intro x z
    simp only [hH]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    beta_reduce
    rw [bII_update_update_update_left hp]
  have hHj : ∀ x z, H (Function.update x p.2 z) = H x := by
    intro x z
    simp only [hH]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    beta_reduce
    rw [bII_update_update_update_same hp]
  have h3 : (∫ x in Submission.BoseGases.abox n ℓ, Ψ x * H x)
      = ∫ x in Submission.BoseGases.abox n ℓ, aP ℓ p.1 (aP ℓ p.2 Ψ) x * H x :=
    bII_split_selfadj hℓ hp hΨc hHm' hCH hHb' hHi hHj
  rw [h3]
  have hGc : Continuous G := by
    simp only [hG]
    exact Submission.BoseGases.aQ_continuous hℓ p.1
      (Submission.BoseGases.aQ_continuous hℓ p.2 hΨc)
  have hPc : Continuous (fun z : Xn n => aP ℓ p.1 (aP ℓ p.2 Ψ) z) :=
    Submission.BoseGases.aP_continuous hℓ p.1
      (Submission.BoseGases.aP_continuous hℓ p.2 hΨc)
  have h4 : (fun x : Xn n => aP ℓ p.1 (aP ℓ p.2 Ψ) x * H x)
      = fun x : Xn n => ∫ y in Submission.BoseGases.acube ℓ,
          ∫ u in Submission.BoseGases.acube ℓ,
            (aP ℓ p.1 (aP ℓ p.2 Ψ) (Function.update (Function.update x p.1 y) p.2 u)
              * G (Function.update (Function.update x p.1 y) p.2 u)) * k y u := by
    funext x
    simp only [hH]
    rw [show aP ℓ p.1 (aP ℓ p.2 Ψ) x * (∫ y in Submission.BoseGases.acube ℓ,
          ∫ u in Submission.BoseGases.acube ℓ,
            G (Function.update (Function.update x p.1 y) p.2 u) * k y u)
        = ∫ y in Submission.BoseGases.acube ℓ, aP ℓ p.1 (aP ℓ p.2 Ψ) x
            * (∫ u in Submission.BoseGases.acube ℓ,
                G (Function.update (Function.update x p.1 y) p.2 u) * k y u) from by
      rw [← MeasureTheory.integral_const_mul]]
    rw [show (fun y : E3 => aP ℓ p.1 (aP ℓ p.2 Ψ) x
          * (∫ u in Submission.BoseGases.acube ℓ,
              G (Function.update (Function.update x p.1 y) p.2 u) * k y u))
        = fun y : E3 => ∫ u in Submission.BoseGases.acube ℓ,
            aP ℓ p.1 (aP ℓ p.2 Ψ) x
              * (G (Function.update (Function.update x p.1 y) p.2 u) * k y u) from by
      funext y
      rw [← MeasureTheory.integral_const_mul]]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    beta_reduce
    rw [← bII_aP_pair_const_update hℓ hp hΨc x y u]
    ring
  rw [h4]
  have h5c : Continuous (fun z : Xn n => aP ℓ p.1 (aP ℓ p.2 Ψ) z * G z) := hPc.mul hGc
  obtain ⟨CG, hCG⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox n ℓ) (f := fun z : Xn n => aP ℓ p.1 (aP ℓ p.2 Ψ) z * G z)
    h5c.continuousOn
  have h5b : ∀ z ∈ Submission.BoseGases.abox n ℓ,
      |(fun z : Xn n => aP ℓ p.1 (aP ℓ p.2 Ψ) z * G z) z| ≤ CG := fun z hz => by
    simpa [Real.norm_eq_abs] using hCG z hz
  have h5 : (fun x : Xn n => ∫ y in Submission.BoseGases.acube ℓ,
        ∫ u in Submission.BoseGases.acube ℓ,
          (fun z : Xn n => aP ℓ p.1 (aP ℓ p.2 Ψ) z * G z)
            (Function.update (Function.update x p.1 y) p.2 u) * k y u)
      = fun x : Xn n => ∫ y in Submission.BoseGases.acube ℓ,
          ∫ u in Submission.BoseGases.acube ℓ,
            (fun z : Xn n => aP ℓ p.1 (aP ℓ p.2 Ψ) z * aQ ℓ p.1 (aQ ℓ p.2 Ψ) z)
              (Function.update (Function.update x p.1 y) p.2 u) * k y u := by
    simp only [hG]
  rw [h5]
  rw [abox_pair_split_integral hℓ hp
    (G := fun z : Xn n => aP ℓ p.1 (aP ℓ p.2 Ψ) z * aQ ℓ p.1 (aQ ℓ p.2 Ψ) z)
    (h5c.measurable) h5b hkm hkb]
  rw [show (∫ x in Submission.BoseGases.abox n ℓ,
        (fun z : Xn n => aP ℓ p.1 (aP ℓ p.2 Ψ) z * aQ ℓ p.1 (aQ ℓ p.2 Ψ) z) x
          * k (x p.1) (x p.2))
      = ∫ x in Submission.BoseGases.abox n ℓ,
          aP ℓ p.1 (aP ℓ p.2 Ψ) x * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * k (x p.1) (x p.2) from by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [Submission.BoseGases.aQ_comm hℓ hp hΨc x]]

/-- **Term `B`** (block `II.2`): the triple integral is `ℓ⁶` times the pair word. -/
theorem bII_TermB_eq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Xn n → ℝ} (hΨc : Continuous Ψ)
    {k : E3 → E3 → ℝ} (hkm : Measurable (Function.uncurry k)) {Ck : ℝ} (hCk : 0 ≤ Ck)
    (hkb : ∀ w y, |k w y| ≤ Ck) {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    (∫ x in Submission.BoseGases.abox n ℓ, ∫ y in Submission.BoseGases.acube ℓ,
        ∫ u in Submission.BoseGases.acube ℓ,
          Ψ x * qmqKR ℓ k (x p.1) (x p.2)
            * Ψ (Function.update (Function.update x p.1 y) p.2 u))
      = (ℓ ^ 3) * (ℓ ^ 3) * ∫ x in Submission.BoseGases.abox n ℓ,
          aP ℓ p.1 (aP ℓ p.2 Ψ) x * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * k (x p.1) (x p.2) := by
  have hstep1 : (fun x : Xn n => ∫ y in Submission.BoseGases.acube ℓ,
        ∫ u in Submission.BoseGases.acube ℓ,
          Ψ x * qmqKR ℓ k (x p.1) (x p.2)
            * Ψ (Function.update (Function.update x p.1 y) p.2 u))
      = fun x : Xn n => (Ψ x * qmqKR ℓ k (x p.1) (x p.2))
          * (∫ y in Submission.BoseGases.acube ℓ, ∫ u in Submission.BoseGases.acube ℓ,
              Ψ (Function.update (Function.update x p.1 y) p.2 u)) := by
    funext x
    rw [show (fun y : E3 => ∫ u in Submission.BoseGases.acube ℓ,
          Ψ x * qmqKR ℓ k (x p.1) (x p.2)
            * Ψ (Function.update (Function.update x p.1 y) p.2 u))
        = fun y : E3 => (Ψ x * qmqKR ℓ k (x p.1) (x p.2))
            * (∫ u in Submission.BoseGases.acube ℓ,
                Ψ (Function.update (Function.update x p.1 y) p.2 u)) from by
      funext y
      rw [show (fun u : E3 => Ψ x * qmqKR ℓ k (x p.1) (x p.2)
            * Ψ (Function.update (Function.update x p.1 y) p.2 u))
          = fun u : E3 => (Ψ x * qmqKR ℓ k (x p.1) (x p.2))
              * Ψ (Function.update (Function.update x p.1 y) p.2 u) from by funext u; ring]
      rw [MeasureTheory.integral_const_mul]]
    rw [MeasureTheory.integral_const_mul]
  rw [hstep1]
  have hstep2 : (fun x : Xn n => (Ψ x * qmqKR ℓ k (x p.1) (x p.2))
        * (∫ y in Submission.BoseGases.acube ℓ, ∫ u in Submission.BoseGases.acube ℓ,
            Ψ (Function.update (Function.update x p.1 y) p.2 u)))
      = fun x : Xn n => (Ψ x * qmqKR ℓ k (x p.1) (x p.2))
          * ((ℓ ^ 3) * (ℓ ^ 3) * aP ℓ p.1 (aP ℓ p.2 Ψ) x) := by
    funext x
    rw [bII_pair_mean hℓ hp Ψ x]
  rw [hstep2]
  have hstep3 : (fun x : Xn n => (Ψ x * qmqKR ℓ k (x p.1) (x p.2))
        * ((ℓ ^ 3) * (ℓ ^ 3) * aP ℓ p.1 (aP ℓ p.2 Ψ) x))
      = fun x : Xn n => ((ℓ ^ 3) * (ℓ ^ 3))
          * ((Ψ x * qmqKR ℓ k (x p.1) (x p.2)) * aP ℓ p.1 (aP ℓ p.2 Ψ) x) := by
    funext x
    ring
  rw [show (∫ x in Submission.BoseGases.abox n ℓ, (Ψ x * qmqKR ℓ k (x p.1) (x p.2))
        * ((ℓ ^ 3) * (ℓ ^ 3) * aP ℓ p.1 (aP ℓ p.2 Ψ) x))
      = ((ℓ ^ 3) * (ℓ ^ 3)) * ∫ x in Submission.BoseGases.abox n ℓ,
          (Ψ x * qmqKR ℓ k (x p.1) (x p.2)) * aP ℓ p.1 (aP ℓ p.2 Ψ) x from by
    rw [hstep3, MeasureTheory.integral_const_mul]]
  have hmain : (∫ x in Submission.BoseGases.abox n ℓ,
        (Ψ x * qmqKR ℓ k (x p.1) (x p.2)) * aP ℓ p.1 (aP ℓ p.2 Ψ) x)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          aP ℓ p.1 (aP ℓ p.2 Ψ) x * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * k (x p.1) (x p.2) := by
    set v : Xn n → ℝ := fun x => Ψ x * aP ℓ p.1 (aP ℓ p.2 Ψ) x with hv
    set g : Xn n → ℝ := fun z => k (z p.1) (z p.2) with hg
    have hgm : Measurable g := by
      have h3 : g = (Function.uncurry k) ∘ (fun z : Xn n => ((z p.1, z p.2) : E3 × E3)) := by
        funext z
        rfl
      rw [h3]
      exact hkm.comp ((measurable_pi_apply p.1).prodMk (measurable_pi_apply p.2))
    have hgb : ∀ z : Xn n, |g z| ≤ Ck := fun z => hkb _ _
    have hvc : Continuous v := by
      simp only [hv]
      exact hΨc.mul (Submission.BoseGases.aP_continuous hℓ p.1
        (Submission.BoseGases.aP_continuous hℓ p.2 hΨc))
    have hker : ∀ x : Xn n, qmqKR ℓ k (x p.1) (x p.2) = aQ ℓ p.1 (aQ ℓ p.2 g) x := by
      intro x
      have h := bII_qmqKR_slot_eq_aQ hℓ hp k hkm hCk (fun w y => hkb w y) x
      simpa only [hg] using h
    have e1 : (∫ x in Submission.BoseGases.abox n ℓ,
          (Ψ x * qmqKR ℓ k (x p.1) (x p.2)) * aP ℓ p.1 (aP ℓ p.2 Ψ) x)
        = ∫ x in Submission.BoseGases.abox n ℓ, aQ ℓ p.1 (aQ ℓ p.2 g) x * v x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [hker x]
      simp only [hv]
      ring
    have e2 : (∫ x in Submission.BoseGases.abox n ℓ, aQ ℓ p.1 (aQ ℓ p.2 g) x * v x)
        = ∫ x in Submission.BoseGases.abox n ℓ, g x * aQ ℓ p.1 (aQ ℓ p.2 v) x :=
      aQ_aQ_sym_box hℓ hp hvc hgm hCk hgb
    have e3 : (∫ x in Submission.BoseGases.abox n ℓ, g x * aQ ℓ p.1 (aQ ℓ p.2 v) x)
        = ∫ x in Submission.BoseGases.abox n ℓ,
            aP ℓ p.1 (aP ℓ p.2 Ψ) x * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * k (x p.1) (x p.2) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [congrFun (bII_aQ_aQ_mul_pairMean hℓ hp hΨc) x,
        Submission.BoseGases.aQ_comm hℓ hp hΨc x]
      simp only [hv, hg]
      ring
    rw [e1, e2, e3]
  rw [hmain]


/-- **The block-`II` dictionary** — see the module header. -/
theorem blockII_dict {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Submission.BoseGases.X n → ℝ}
    (hΨc : Continuous Ψ) (hΨsym : Submission.BoseGases.PermInvariant n Ψ)
    {k : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hkm : Measurable (Function.uncurry k))
    (hkb : ∃ C : ℝ, ∀ w y, |k w y| ≤ C) (hksym : ∀ w y, k w y = k y w)
    {c : ℂ} (hc : (starRingEnd ℂ) c * c * ((ℓ ^ 3 : ℝ) : ℂ) = 1) (hr : (starRingEnd ℂ) c = c)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    (1 / 2) * ((ℓ ^ 3)⁻¹ : ℝ) *
        ((Work.BoseBoxFock.rowShape21 (Work.BoseBoxFock.boxRestrictC ℓ Ψ)
            (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
            (Work.BoseBoxFock.qmqKernel ℓ k) p).re
          + (Work.BoseBoxFock.rowShape23 (Work.BoseBoxFock.boxRestrictC ℓ Ψ)
              (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
              (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
              (Work.BoseBoxFock.qmqKernel ℓ k) p).re)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Ψ) x
            * Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Ψ) x
            * k (x p.1) (x p.2) := by
  obtain ⟨Ck, hkb'⟩ := hkb
  have hCk : 0 ≤ Ck := le_trans (abs_nonneg _) (hkb' 0 0)
  rw [bII_rowShape21_re hℓ hΨc hkm hc hr hp, bII_rowShape23_re hℓ hΨc hkm hc hr hp,
    bII_TermA_eq hℓ hΨc hkm hkb' hksym hp, bII_TermB_eq hℓ hΨc hkm hCk hkb' hp]
  have hℓ3 : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
  field_simp
  ring

end Work.BoseBoxFock
