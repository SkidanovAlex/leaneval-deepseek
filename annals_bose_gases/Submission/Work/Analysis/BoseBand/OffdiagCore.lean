import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.BandDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.Analysis.BoseBand.OffdiagCore` — the shared mechanism of the
off-diagonal fibre vanishing of the localised kinetic word `fsT`

This module collects the elementary ingredients on which the off-diagonal vanishing
lemmas of FS §6's kinetic band argument (`fsT` = `neuWord + gapWord + momWord + mainWord`)
rest:

* **`peel_pair_abox`** — the Fubini/substitution identity that peels the integration over the
  slot `j` out of a *pair* of functions: integrating the slot variable of `x` against `z` and
  then over the box is the box integral of the product, with the volume `ℓ³` of the peeled
  slot as the factor.  This is the position-space half of "the slot-`j` fibre integral is the
  slot-`j` pairing with the identity";
* **`integral_fibre_jointProj_eq_zero`** / **`aQ_jointProj_eq_self_of_mem`** — the slot algebra
  of the joint sector projection `E_S = ∏_{i∈S}Q_i ∏_{i∉S}P_i`: for `j ∈ S` the slot-`j`
  fibre of `E_SΦ` has vanishing mean, and the slot-`j` mean-free projection is the identity
  on `E_SΦ`.

The vanishing itself is then, for each of the four terms of `fsT`, a statement about the
bilinear form of that term being a *slot-`j` form*: since `S ≠ T` with `j ∈ S ∩ T` there is a
slot `k ≠ j` at which the two sectors differ, at which one of the two fibres is mean-free
while the other is independent of that coordinate; integrating in the `k`-th coordinate then
kills the pairing.
-/

noncomputable section

open MeasureTheory

namespace Work.Analysis.BoseBand

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Elementary fibre algebra -/

/-- The slot-`j` fibre is additive in the state (pointwise, definitionally). -/
lemma fibre_add {N : ℕ} (j : Fin N) (A B : Submission.BoseGases.X N → ℝ)
    (x : Submission.BoseGases.X N) :
    Work.BoseKinLoc.fibre N j (fun y => A y + B y) x
      = fun z => Work.BoseKinLoc.fibre N j A x z + Work.BoseKinLoc.fibre N j B x z := rfl

/-- The slot-`j` fibre is subtractive in the state (pointwise, definitionally). -/
lemma fibre_sub {N : ℕ} (j : Fin N) (A B : Submission.BoseGases.X N → ℝ)
    (x : Submission.BoseGases.X N) :
    Work.BoseKinLoc.fibre N j (fun y => A y - B y) x
      = fun z => Work.BoseKinLoc.fibre N j A x z - Work.BoseKinLoc.fibre N j B x z := rfl

/-- The slot-`j` fibre of a continuous state is continuous. -/
lemma continuous_fibre {N : ℕ} (j : Fin N) {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : Continuous Ψ) (x : Submission.BoseGases.X N) :
    Continuous (Work.BoseKinLoc.fibre N j Ψ x) :=
  hΨ.comp (by fun_prop)

/-- The anchored moving box `Λ(0)` is the centred cube. -/
lemma lamBox_zero_eq_acube {ℓ : ℝ} :
    Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
  ext z
  simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]

/-- The box indicator `indU ℓ 0 (x j)` is `1` at every point of the configuration box. -/
lemma indU_eq_one_of_mem_abox {n : ℕ} {ℓ : ℝ} (j : Fin n) {x : Submission.BoseGases.X n}
    (hx : x ∈ Submission.BoseGases.abox n ℓ) :
    Work.BoseKinLoc.indU ℓ 0 (x j) = 1 := by
  have hmem : x j ∈ Work.BoseKinLoc.lamBox ℓ 0 := by
    rw [lamBox_zero_eq_acube]
    exact (Submission.BoseGases.mem_abox_iff n ℓ x).mp hx j
  rw [Work.BoseKinLoc.indU, Set.indicator_of_mem hmem]

/-! ## 2. Slot algebra of the joint sector projections -/

/-- **`Q_j` fixes the sector `E_SΦ` when the slot `j` belongs to `S`.**  In the recursion
`jointProj = blockOp` the slot-`j` operator is `Q_j`, and `P_j E_SΦ = 0`
(`Sector.aP_blockOp_eq_zero`), so `Q_j E_SΦ = (1 − P_j) E_SΦ = E_SΦ`. -/
lemma aQ_jointProj_eq_self_of_mem {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {S : Finset ℕ} {j : ℕ}
    (hjS : j ∈ S) (hjn : j < n) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    Submission.BoseGases.aQ ℓ ⟨j, hjn⟩ (Work.BoseFixB2.jointProj ℓ S Φ)
      = Work.BoseFixB2.jointProj ℓ S Φ := by
  have h := Work.BoseFixB2.Sector.aP_blockOp_eq_zero hℓ hjn hjS hΦ
  funext x
  simp only [Submission.BoseGases.aQ]
  rw [congrFun h x]
  simp

/-- **The slot-`j` mean of a sector projection vanishes when `j` lies in the sector.**

For `j ∈ S`, the fibre `z ↦ (E_SΦ)(x_{j←z})` of the joint sector projection has zero mean
over the centred cube `acube ℓ`: this is the pointwise form of the corpus's
`aP_blockOp_eq_zero` (`P_j E_S = 0`). -/
lemma integral_fibre_jointProj_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {S : Finset ℕ} (j : Fin n)
    (hjS : (j : ℕ) ∈ S) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ)
    (x : Submission.BoseGases.X n) :
    ∫ z in Submission.BoseGases.acube ℓ,
      (Work.BoseFixB2.jointProj ℓ S Φ) (Function.update x j z) = 0 := by
  have h := Work.BoseFixB2.Sector.aP_blockOp_eq_zero hℓ j.isLt hjS hΦ
  have hx := congrFun h x
  simp only [Submission.BoseGases.aP] at hx
  have hne : (1 / ℓ ^ 3 : ℝ) ≠ 0 := by positivity
  exact (mul_eq_zero.mp hx).resolve_left hne

/-! ## 3. The pair peel of the slot integral -/

/-- **Peeling the slot integral of a pair.**  For continuous `A B` on the `(m+1)`-body
configuration space,

    `∫_{abox (m+1) ℓ} c · ∫_{acube ℓ} A(x_{j←z}) B(x_{j←z}) dz dx = c ℓ³ ∫_{abox (m+1) ℓ} A B`.

Both integrals on the left only see `x` through the coordinates `≠ j` (the integrand of the
inner `z`-integral replaces the `j`-th coordinate by `z`), so the `j`-th coordinate integrates
to the volume `ℓ³`; what remains is the box integral of the product, which is the same
computation read backwards (`abox_integral_peel` of `A * B` in the slot `j`). -/
theorem peel_pair_abox {ℓ : ℝ} (hℓ : 0 < ℓ) {m : ℕ} (j : Fin (m + 1))
    {A B : Submission.BoseGases.X (m + 1) → ℝ} (hA : Continuous A) (hB : Continuous B)
    (c : ℝ) :
    (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
        c * ∫ z in Submission.BoseGases.acube ℓ,
          A (Function.update x j z) * B (Function.update x j z))
      = c * ℓ ^ 3 * ∫ x in Submission.BoseGases.abox (m + 1) ℓ, A x * B x := by
  set H : Submission.BoseGases.X (m + 1) → ℝ := fun x =>
    ∫ z in Submission.BoseGases.acube ℓ,
      A (Function.update x j z) * B (Function.update x j z) with hH
  have hHc : Continuous H := by
    rw [hH]
    refine continuous_parametric_integral_of_continuous
      (f := fun (x : Submission.BoseGases.X (m + 1)) (z : EuclideanSpace ℝ (Fin 3)) =>
        A (Function.update x j z) * B (Function.update x j z)) ?_
      (Submission.BoseGases.acube_compact hℓ)
    exact (hA.comp (continuous_fst.update j continuous_snd)).mul
      (hB.comp (continuous_fst.update j continuous_snd))
  -- the integrand of `H` does not see the inserted coordinate
  have hind : ∀ (r : Submission.BoseGases.X m) (y y' : EuclideanSpace ℝ (Fin 3)),
      H (Submission.BoseGases.kcInsN m j (y, r))
        = H (Submission.BoseGases.kcInsN m j (y', r)) := by
    intro r y y'
    simp only [hH]
    congr 1
    funext z
    rw [Submission.BoseGases.update_kcInsN, Submission.BoseGases.update_kcInsN]
  have hpeel := Work.SmallBoxBridge.Fourier.peel_slot_abox (n := m) (s := ℓ) hℓ j
    hHc hind
  -- the peel of `A * B` in the same slot
  have hABint : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (m + 1) => A x * B x)
      (Submission.BoseGases.abox (m + 1) ℓ) MeasureTheory.volume :=
    Submission.BoseGases.integrableOn_abox_of_continuous hℓ (hA.mul hB)
  have hABpeel := Submission.BoseGases.abox_integral_peel (n := m) (ℓ := ℓ) j
    (fun x : Submission.BoseGases.X (m + 1) => A x * B x) hABint
  -- the two right-hand sides coincide
  have hpoint : ∀ r : Submission.BoseGases.X m,
      H (Submission.BoseGases.kcInsN m j (0, r))
        = ∫ y in Submission.BoseGases.acube ℓ,
            A (Submission.BoseGases.kcInsN m j (y, r))
              * B (Submission.BoseGases.kcInsN m j (y, r)) := by
    intro r
    rw [hH]
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ) ?_
    intro z hz
    beta_reduce
    rw [Submission.BoseGases.update_kcInsN]
  have hright : (∫ r in Submission.BoseGases.abox m ℓ, H (Submission.BoseGases.kcInsN m j (0, r)))
      = ∫ x in Submission.BoseGases.abox (m + 1) ℓ, A x * B x := by
    rw [show (∫ r in Submission.BoseGases.abox m ℓ,
            H (Submission.BoseGases.kcInsN m j (0, r)))
          = ∫ r in Submission.BoseGases.abox m ℓ,
              ∫ y in Submission.BoseGases.acube ℓ,
                A (Submission.BoseGases.kcInsN m j (y, r))
                  * B (Submission.BoseGases.kcInsN m j (y, r)) from by
        exact MeasureTheory.setIntegral_congr_fun
          (Submission.BoseGases.abox_measurable m ℓ) (fun r hr => hpoint r)]
    rw [show (∫ r in Submission.BoseGases.abox m ℓ,
              ∫ y in Submission.BoseGases.acube ℓ,
                A (Submission.BoseGases.kcInsN m j (y, r))
                  * B (Submission.BoseGases.kcInsN m j (y, r)))
          = ∫ r in Submission.BoseGases.abox m ℓ,
              ∫ y in Submission.BoseGases.acube ℓ, (A * B) (Submission.BoseGases.kcInsN m j (y, r))
        from by
        refine MeasureTheory.setIntegral_congr_fun
          (Submission.BoseGases.abox_measurable m ℓ) (fun r hr => ?_)
        refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
          (fun y hy => rfl)]
    exact hABpeel.symm
  have hmul : (∫ x in Submission.BoseGases.abox (m + 1) ℓ, H x)
      = ℓ ^ 3 * ∫ x in Submission.BoseGases.abox (m + 1) ℓ, A x * B x := by
    have h2 : (ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox (m + 1) ℓ, H x)
        = ∫ x in Submission.BoseGases.abox (m + 1) ℓ, A x * B x := by
      rw [hpeel, hright]
    have h3 : (ℓ ^ 3 : ℝ) ≠ 0 := by positivity
    have := congrArg (fun t : ℝ => ℓ ^ 3 * t) h2
    rwa [← mul_assoc, mul_inv_cancel₀ h3, one_mul] at this
  rw [show (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
        c * ∫ z in Submission.BoseGases.acube ℓ,
          A (Function.update x j z) * B (Function.update x j z))
      = c * ∫ x in Submission.BoseGases.abox (m + 1) ℓ, H x from by
    rw [← hH]
    exact MeasureTheory.integral_const_mul c _]
  rw [hmul]
  ring

end Work.Analysis.BoseBand
