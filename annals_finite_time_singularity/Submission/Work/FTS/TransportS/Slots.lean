/-
Copyright: work module for the Elgindi finite-time singularity project.

# The per-slot `IP4` transport facts

The coercive inner product `Work.FTS.CoercivityStep.IP4 α = HkIPStep 1 1 (HkIPStep 1 1
(HkIPStep 1 1 (H1IP α)))` is a positive combination of *elementary slot pairings*
`slotPairing ρ a b u v = ∫_z ∫_θ ρ · (D_z^bD_θ^a u) · (D_z^bD_θ^a v)`, where `(a,b)` ranges
over the slots with `a + b ≤ 4` and the weight `ρ` is one of the three *leaf weights* of
`H1IP`: `w² sin(2θ)^{-η}`, `w²` and `w² sin(2θ)^{-γ}`.  Each of them is smooth in `z` and
pointwise dominated by the slot weight `slotW α a` of the corresponding slot of
`HkIntegrand α 4` (`IsLeafW_le`).

This is the N3 → N2 seam: N4's `IP4_unfold` sums the per-slot transport estimates over the
leaves of `IP4`'s unfolding.  This module provides

* the definition `slotPairing`, the leaf weights `leafW`, `IsLeafW`, the leaf sum `leafSum`,
  and their elementary API (all proved);
* `T2Slot C`, `T3Slot C`: the per-slot transport bounds, i.e. the frozen statements
  `T2S`/`T3S_Dz` *one slot at a time*, for the leaf weights;
* `SlotDomIP α₂ K IP`: the purely algebraic statement that `IP` is dominated by `leafSum`
  (this is exactly what the unfolding of `IP4` produces).

**Important repair, 2026-10-04.**  An earlier version of `T2Slot` quantified over *arbitrary*
weights `ρ` with only the pointwise sandwich `0 ≤ ρ ≤ slotW α a`.  That form is **false**: with
a *discontinuous* weight `ρ = slotW α a · 1_E` the indicator carves the positive part out of an
oscillating integrand and the jumps of `z ρ f T²` in the radial integration by parts that
handles the five top slots (`a + b = 4`) contribute an unbounded factor.  The refutation
(explicit oscillating-bump family, `LHS/RHS ≍ N → ∞`, numerically verified) and its analysis
are in `Submission/Work/FTS/TransportS/NOTES_t2Slot_FALSE.md`.  The definitions below are
therefore restricted to the three leaf weights, all of which are smooth in `z` with
`z ∂_z(ρ)/ρ = (z-3)/(1+z)` bounded.

Everything is stated with the frozen hypothesis bundles `T2SF`/`T2SG` (`T2S.lean`) and
`T3SF`/`T3SG` (`T3S.lean`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.T2S
import Submission.Work.FTS.TransportS.T3S
import Submission.Work.FTS.H2.STEasyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The elementary slot pairing -/

/-- The elementary slot pairing `∫_z ∫_θ ρ · D_z^bD_θ^a u · D_z^bD_θ^a v`.  Every leaf of the
unfolding of the coercive `IP4` is one of these (up to a scalar), and every slot of the flat
pairing `H4Pair` is `slotPairing (slotW α a) a b u v`. -/
def slotPairing (ρ : ℝ → ℝ → ℝ) (a b : ℕ) (u v : Fn) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    ρ z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a v z θ

/-- The slot pairing is symmetric in its two function arguments. -/
theorem slotPairing_comm (ρ : ℝ → ℝ → ℝ) (a b : ℕ) (u v : Fn) :
    slotPairing ρ a b u v = slotPairing ρ a b v u := by
  unfold slotPairing
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  ring

/-! ## The leaf weights of `IP4` -/

/-- The three leaf weights of `H1IP`, as functions of `(z,θ)`:
`w² sin(2θ)^{-η}` (the `10`- and `10^10`-terms of `H1IP`), `w²` (the `10^17`-term) and
`w² sin(2θ)^{-γ}` (the `10^21`-term).  These are exactly the weights occurring in the unfolding
of `IP4`, and they are all smooth in `z` with `z ∂_z(ρ)/ρ = (z-3)/(1+z)` bounded — this is what
the radial integration by parts of the five top slots needs, and what the refuted
"arbitrary weight `ρ ≤ slotW α a`" version of the per-slot bound was missing
(`NOTES_t2Slot_FALSE.md`). -/
def leafEta : ℝ → ℝ → ℝ :=
  fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The σ-free leaf weight `w²`. -/
def leafOne : ℝ → ℝ → ℝ := fun z _ => (Work.Spaces.w z) ^ 2

/-- The `γ` leaf weight `w² sin(2θ)^{-γ}`. -/
def leafGam (α : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

theorem leafEta_nonneg {z θ : ℝ} (hθ : 0 ≤ Real.sin (2 * θ)) : 0 ≤ leafEta z θ :=
  mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hθ _)

theorem leafOne_nonneg (z θ : ℝ) : 0 ≤ leafOne z θ := sq_nonneg _

theorem leafGam_nonneg (α : ℝ) {z θ : ℝ} (hθ : 0 ≤ Real.sin (2 * θ)) :
    0 ≤ leafGam α z θ := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hθ _)

/-- For `0 < sin(2θ)` and `q ≥ 0` the weight `sin(2θ)^{-q}` is at least `1`. -/
theorem one_le_rpow_neg {q θ : ℝ} (hq : 0 ≤ q) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-q) := by
  have hσ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hσ1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h := Real.rpow_le_one hσ.le hσ1 hq
  have hpos : 0 < Real.sin (2 * θ) ^ q := Real.rpow_pos_of_pos hσ q
  rw [Real.rpow_neg hσ.le]
  exact (one_le_inv₀ hpos).mpr h

/-- `w²` is pointwise dominated by the slot weight `slotW α a` on the open quadrant. -/
theorem w_sq_le_slotW (α : ℝ) (hα : 0 < α) {a : ℕ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) : (Work.Spaces.w z) ^ 2 ≤ slotW α a z θ := by
  rcases eq_or_ne a 0 with ha | ha
  · subst ha
    rw [slotW_zero_eq α hθ]
    simpa using mul_le_mul_of_nonneg_left (one_le_rpow_neg Work.Spaces.eta_nonneg hθ)
      (sq_nonneg (Work.Spaces.w z))
  · have h1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    rw [slotW_of_pos_eq α h1 hθ]
    have hgam : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
    simpa using mul_le_mul_of_nonneg_left (one_le_rpow_neg hgam hθ)
      (sq_nonneg (Work.Spaces.w z))

/-- `leafEta` is dominated by the slot weight `slotW α a` for every `a`. -/
theorem leafEta_le_slotW (α : ℝ) (hα : 0 < α) {a : ℕ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) : leafEta z θ ≤ slotW α a z θ := by
  rcases eq_or_ne a 0 with ha | ha
  · subst ha; rw [leafEta, slotW_zero_eq α hθ]
  · have h1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    rw [leafEta, slotW_of_pos_eq α h1 hθ]
    exact mul_le_mul_of_nonneg_left (Work.FTS.H2.rpow_eta_le_gam hα
      ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) (sq_nonneg _)

/-- `leafOne` is dominated by the slot weight `slotW α a` for every `a`. -/
theorem leafOne_le_slotW (α : ℝ) (hα : 0 < α) {a : ℕ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) : leafOne z θ ≤ slotW α a z θ := by
  rw [leafOne]
  exact w_sq_le_slotW α hα hθ

/-- **The leaf weights of `IP4` for the slot with `a` angular derivatives**: `leafEta` and
`leafOne` for every slot, and `leafGam α` only for slots with `a ≥ 1` (the `σ^{-γ}`-term of
`H1IP` acts on `D_θ f`, which raises the number of angular derivatives by one).

The `a ≥ 1` guard is *essential*: the earlier `IsLeafW α ρ` (independent of `a`) was refuted by
the agent of `t2SlotRepaired` — at the slot `(a,b) = (0,4)` the weight `w²σ^{-γ}` is not the
slot weight `slotW α 0 = w²σ^{-η}` of `HkIntegrand α 4`, and `HkSq α 4 g` does not control
`|∫∫ w²σ^{-γ}(D_z^5 g)(D_z^4g)|` (analysis and numerics in
`Submission/Work/FTS/TransportS/SlotT2/NOTES_t2SlotRepaired_FALSE.md` and `_t2slot/`).  Every
instance the intended use consumes has the `γ`-weight only at slots with `a ≥ 1`, where
`slotW α a = w²σ^{-γ}` is exactly the mixed-slot weight. -/
def IsLeafW (α : ℝ) (a : ℕ) (ρ : ℝ → ℝ → ℝ) : Prop :=
  ρ = leafEta ∨ ρ = leafOne ∨ (1 ≤ a ∧ ρ = leafGam α)

/-- `leafGam α` is the slot weight `slotW α a` for `a ≥ 1` on the open quadrant. -/
theorem leafGam_le_slotW (α : ℝ) (hα : 0 < α) {a : ℕ} (ha : 1 ≤ a) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) : leafGam α z θ ≤ slotW α a z θ := by
  rw [leafGam, slotW_of_pos_eq α ha hθ]

/-- Every leaf weight of the slot `a` is nonnegative on the open quadrant and pointwise
dominated by the slot weight `slotW α a`. -/
theorem IsLeafW_le (α : ℝ) (hα : 0 < α) {a : ℕ} {ρ : ℝ → ℝ → ℝ} (h : IsLeafW α a ρ) :
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → 0 ≤ ρ z θ) ∧
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → ρ z θ ≤ slotW α a z θ) := by
  rcases h with rfl | rfl | ⟨ha, rfl⟩
  · exact ⟨fun z θ _ hθ0 hθ1 => leafEta_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith, by linarith [hθ1, Real.pi_pos]⟩),
      fun z θ _ hθ0 hθ1 => leafEta_le_slotW α hα (show θ ∈ Set.Ioo (0 : ℝ) (π / 2) from
        ⟨hθ0, hθ1⟩)⟩
  · exact ⟨fun _ _ _ _ _ => leafOne_nonneg _ _, fun z θ _ hθ0 hθ1 =>
      leafOne_le_slotW α hα (show θ ∈ Set.Ioo (0 : ℝ) (π / 2) from ⟨hθ0, hθ1⟩)⟩
  · refine ⟨fun z θ _ hθ0 hθ1 => ?_, fun z θ _ hθ0 hθ1 => ?_⟩
    · exact leafGam_nonneg α (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith, by linarith [hθ1, Real.pi_pos]⟩)
    · exact leafGam_le_slotW α hα ha (show θ ∈ Set.Ioo (0 : ℝ) (π / 2) from ⟨hθ0, hθ1⟩)

/-- The sum of the absolute values of all slot pairings occurring in the unfolding of `IP4`:
over the fifteen slots `(a,b)` of `ℋ⁴` (`a + b ≤ 4`) and the three leaf weights. -/
def leafSum (α : ℝ) (u v : Fn) : ℝ :=
  ∑ a ∈ Finset.range 5, ∑ b ∈ Finset.range 5,
    (if a + b ≤ 4 then
      |slotPairing leafEta a b u v| + |slotPairing leafOne a b u v|
        + (if 1 ≤ a then |slotPairing (leafGam α) a b u v| else 0)
    else 0)

/-- The leaf sum is nonnegative. -/
theorem leafSum_nonneg (α : ℝ) (u v : Fn) : 0 ≤ leafSum α u v := by
  unfold leafSum
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  by_cases hab : a + b ≤ 4
  · rw [if_pos hab]
    refine add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) ?_
    by_cases ha : 1 ≤ a
    · rw [if_pos ha]; exact abs_nonneg _
    · rw [if_neg ha]
  · rw [if_neg hab]

/-! ## The per-slot transport bounds -/

/-- **The per-slot `D_z` transport bound with an `ℋ⁴` coefficient** (the slot-by-slot form of
the frozen `T2S`): for every slot `(a,b)` of the flat pairing (`a + b ≤ 4`), every *leaf* weight
`ρ`, and the coefficient `f·D_z g`,

`|slotPairing ρ a b (f·D_z g) g| ≤ C·α^{-1/2}·(|f|_{ℋ⁴} + CoefTh 1 f)·|g|²_{ℋ⁴}`. -/
def T2Slot (C : ℝ) : Prop :=
  ∀ (α : ℝ) (f g : Fn), 0 < α → α ≤ 1 → T2SF α f → T2SG α g →
    ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 4 → IsLeafW α a ρ →
      |slotPairing ρ a b (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
        ≤ C * α ^ (-(1 / 2 : ℝ))
            * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
            * Work.FTS.Nonlin.Xn α g ^ 2

/-- **The per-slot `D_z` transport bound with a `𝒲^{4,∞}` coefficient** (the slot-by-slot form
of the frozen `T3S_Dz`). -/
def T3Slot (C : ℝ) : Prop :=
  ∀ (α : ℝ) (f g : Fn), 0 < α → α ≤ 1 → T3SF α f → T3SG α g →
    ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 4 → IsLeafW α a ρ →
      |slotPairing ρ a b (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
        ≤ C * α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f)
            * Work.FTS.Nonlin.Xn α g ^ 2

/-! ## The slot domination of the concrete `IP4` -/

/-- **The algebraic content of `IP4_unfold`**: the coercive inner product `IP` is dominated by
`leafSum`, i.e. by the sum of the absolute values of its slot pairings with the *leaf* weights
of `H1IP` (each of them pointwise dominated by the slot weight `slotW α a` of the corresponding
slot, `IsLeafW_le`).

For `IP α = Work.FTS.CoercivityStep.IP4 α` this is the unfolding of the four induction steps
`HkIPStep 1 1` together with the four elementary terms of `H1IP`. -/
def SlotDomIP (α₂ K : ℝ) (IP : ℝ → Fn → Fn → ℝ) : Prop :=
  0 < K ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ u v : Fn,
    Work.FTS.EllipticEst.SmoothOpen u → Work.FTS.EllipticEst.SmoothOpen v →
    |IP α u v| ≤ K * leafSum α u v

end Work.FTS.TransportS
