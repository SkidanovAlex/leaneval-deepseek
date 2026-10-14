import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.PmdbAux.SlotPriceAux
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundE
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- **The Leibniz expansion of `D_z^bD_θ^a(c₂ₘ·L₁₂(f)·D_z f)`** on the open quadrant. -/
theorem t5bExpand {f : ℝ → ℝ → ℝ} {a b : ℕ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hCsm : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Work.Construction.c2m θ))
    (hXsm : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi 0))
    (hab : a + b ≤ 6) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed b a (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 f z
        * Work.Spaces.Dz f z θ) z θ
        = ∑ k ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
            ((b.choose k : ℝ) * (a.choose i : ℝ))
              * (Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z
                  * (Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ
                      * Work.Spaces.mixed (b - k + 1) (a - i) f z θ)) := by
  intro z θ hz hθ0 hθ1
  have hb : b ≤ 6 := by omega
  have hbase := Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.mixedRadialThetaMul
    (X := fun z => Work.Construction.L12 f z) (γ := Work.Construction.c2m)
    (f := Work.Spaces.Dz f) hXsm hCsm hso.Dz b a hb z θ hz hθ0 hθ1
  have hfun : (fun z θ : ℝ => Work.Construction.c2m θ * Work.Construction.L12 f z
        * Work.Spaces.Dz f z θ)
      = fun z θ : ℝ => Work.Construction.L12 f z
          * (Work.Construction.c2m θ * Work.Spaces.Dz f z θ) := by
    funext z θ
    ring
  rw [hfun, hbase]
  refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun i hi => ?_
  rw [mixedDzShift hso (b - k) (a - i) hz hθ0 hθ1]

/-- **The paired form of the expansion**: the integrand of the slot pairing of the row, as the
finite sum of the `t5bPiece` summands. -/
theorem t5bPairExpand {f : ℝ → ℝ → ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hCsm : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Work.Construction.c2m θ))
    (hXsm : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi 0))
    (hab : a + b ≤ 6) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ * Work.Spaces.mixed b a (fun z θ => Work.Construction.c2m θ
          * Work.Construction.L12 f z * Work.Spaces.Dz f z θ) z θ
        * Work.Spaces.mixed b a f z θ
        = ∑ k ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
            ((b.choose k : ℝ) * (a.choose i : ℝ)) * t5bPiece f ρ a b k i (z, θ) := by
  intro z θ hz hθ0 hθ1
  rw [t5bExpand hso hCsm hXsm hab z θ hz hθ0 hθ1, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [t5bPiece]
  ring

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.leafSlotSliceIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

/-!
# The angular-slice integrability of a single leaf slot of `IP6`

Fix a leaf weight `ρ` (`Work.FTS.TransportS.IsLeafW α a ρ`) and a slot `(a,b)` of order
`a + b ≤ 6`.  For a datum `f` which is `C^∞` on the open quadrant and lies in the weighted
space `ℋ⁶` (`Work.Spaces.HkMem α 6 f`), the angular slice function

  `θ ↦ ρ z θ · (D_z^bD_θ^a f z θ)²`

is integrable on `Iθ = [0, π/2]`, for every `z ∈ Iz`.

The content is purely pointwise: on the open angular interval the two endpoints are null, every
leaf weight is dominated by one of the two block weights `(Whz)² = w²σ^{-η}` / `(Wm)² = w²σ^{-γ}`
of `HkIntegrand α 6 f`, so

  `ρ z θ · (D_z^bD_θ^a f z θ)² ≤ HkIntegrand α 6 f z θ`   a.e. on `Iθ`,

and the right-hand side is integrable by `HkMem α 6 f`.  This lemma is the angular half of the
single-slot energy bound (`slotEnergyLeHkSq`); it is the hypothesis `leafSlotZIntegrable`
consumes.
-/

/-- For `volume.restrict Iθ` the two endpoints `0`, `π/2` are null, so `θ` lies in the open
interval almost everywhere.  (`Icc 0 (π/2)` and `Ioo 0 (π/2)` agree a.e.) -/
theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have h : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm
  rw [h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-! ## Nonnegativity of the leaf weights on the closed quadrant -/

/-- Every leaf weight of `IP6` is nonnegative on `Iz × Iθ`. -/
theorem leaf_nonneg {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ ρ z θ := by
  rcases hρ with rfl | rfl | ⟨_, rfl⟩
  · intro z hz θ hθ
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)
  · intro z hz θ hθ
    exact sq_nonneg _
  · intro z hz θ hθ
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)

/-! ## The pointwise domination of a leaf weight -/

/-- The *two* leaf weights of a `D_z`-only slot (`a = 0`) — `leafEta` and `leafOne` — are
dominated by the square of the block weight `Whz`.

(`leafGam` is deliberately excluded: at `a = 0` it is not a leaf weight
(`Work.FTS.TransportS.IsLeafW` requires `1 ≤ a` for `leafGam`), and indeed
`w²σ^{-γ} ≤ w²σ^{-η}` is *false* on the open quadrant since `σ^{-γ} ≥ σ^{-η}`.) -/
theorem leaf_le_Whz_sq {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) (ha : a = 0) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    ρ z θ ≤ (Work.FTS.H2.Whz z θ) ^ 2 := by
  subst ha
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI
  rcases hρ with rfl | rfl | ⟨ha1, _⟩
  · rw [Work.FTS.TransportS.leafEta, Work.FTS.H2.hbi_Whz_sq z θ hs]
  · rw [Work.FTS.TransportS.leafOne, Work.FTS.H2.hbi_Whz_sq z θ hs]
    exact le_mul_of_one_le_right (sq_nonneg _)
      (Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ)
  · exfalso; omega

/-- Every leaf weight is dominated by the square of the block weight `Wm`. -/
theorem leaf_le_Wm_sq {α : ℝ} (hα : 0 < α) {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    ρ z θ ≤ (Work.FTS.H2.Wm α z θ) ^ 2 := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI
  rcases hρ with rfl | rfl | ⟨_, rfl⟩
  · rw [Work.FTS.TransportS.leafEta, Work.FTS.H2.hbi_Wm_sq α z θ hs]
    exact mul_le_mul_of_nonneg_left (Work.FTS.H2.rpow_eta_le_gam hα hθI) (sq_nonneg _)
  · rw [Work.FTS.TransportS.leafOne, Work.FTS.H2.hbi_Wm_sq α z θ hs]
    exact le_mul_of_one_le_right (sq_nonneg _)
      (Work.FTS.TransportS.one_le_rpow_neg (le_of_lt (Work.Spaces.gam_pos hα)) hθ)
  · rw [Work.FTS.TransportS.leafGam, Work.FTS.H2.hbi_Wm_sq α z θ hs]

/-- **The pointwise slot domination.**  For a leaf weight `ρ` of the slot `a` and any slot
`(a,b)` of order `≤ N`, the weighted slot of any datum `h` is dominated by the
`ℋ^N`-integrand of `h` on the open quadrant. -/
theorem leaf_dom_gen {α : ℝ} (hα : 0 < α) {N a b : ℕ} (hab : a + b ≤ N)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ) {h : ℝ → ℝ → ℝ}
    {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    ρ z θ * (Work.Spaces.mixed b a h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α N h z θ := by
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · subst h0
    rw [Work.Spaces.mixed_zero_right]
    have hb : b ≤ N := by omega
    calc ρ z θ * (Work.Spaces.DzIter b h z θ) ^ 2
        ≤ (Work.FTS.H2.Whz z θ) ^ 2 * (Work.Spaces.DzIter b h z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (leaf_le_Whz_sq hρ rfl hθ) (sq_nonneg _)
      _ = (Work.Spaces.DzIter b h z θ * Work.FTS.H2.Whz z θ) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α N h z θ :=
          Work.Spaces.sq_le_HkIntegrand_z α N h z θ b hb
  · have h1 : 1 ≤ a := hpos
    calc ρ z θ * (Work.Spaces.mixed b a h z θ) ^ 2
        ≤ (Work.FTS.H2.Wm α z θ) ^ 2 * (Work.Spaces.mixed b a h z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (leaf_le_Wm_sq hα hρ hθ) (sq_nonneg _)
      _ = (Work.Spaces.mixed b a h z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          simp only [Work.FTS.H2.Wm]; ring
      _ ≤ Work.Spaces.HkIntegrand α N h z θ :=
          Work.Spaces.sq_le_HkIntegrand_mixed α N h z θ a b h1 hab

/-! ## Continuity of the leaf weights in `θ` (for a.e. strong measurability) -/

/-- `θ ↦ sin(2θ)^{-q}` is continuous on the open interval `(0, π/2)` (where `sin(2θ) > 0`). -/
theorem continuousOn_sin_two_rpow_neg (q : ℝ) :
    ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q)) (Set.Ioo (0 : ℝ) (π / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (π / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  refine hsin.rpow_const fun θ hθ => Or.inl ?_
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos]))


/-! ## The requested slice integrability -/


end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
end
