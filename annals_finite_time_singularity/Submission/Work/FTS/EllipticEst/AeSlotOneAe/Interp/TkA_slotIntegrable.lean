import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AeSlotOneAe.Interp.TkA_cross_defs
import Submission.Work.FTS.EllipticEst.AeSlotOneAe.Interp.TkA_cross_ids
import Submission.Work.FTS.EllipticEst.integrable_prod_sq_restrict_open
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.integrable_prod_of_iterated

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Product integrability of the `Tk`-slot data of the `A`-slot

The cross-slot identity `TkA_le_cross` is ultimately an identity between integrals over the
half-open strip `(0,∞) × Iθ`, and both Fubini interchanges used in its proof need the slots
involved to be honestly integrable for the product measure
`(volume|_{(0,∞)}).prod (volume|_{Iθ})`.

For a function `F` which is `C^∞` on the open quadrant (`SmoothOpen F`) and honestly in
`ℋ^k` (`HkMem α k F`), this module proves:

* the whole `ℋ^k`-integrand `HkIntegrand α k F` is integrable for the product of the
  restrictions of Lebesgue measure to `Iz = [0,∞)` and `Iθ = [0,π/2]`
  (`integrable_uncurry_HkIntegrand`) — Tonelli applied to the two halves of the definition of
  `HkMem` (`Work.Spaces.integrable_prod_of_iterated`), the a.e. strong measurability coming
  from the joint continuity of `HkIntegrand` on the open quadrant;
* every single weighted `D_z`-slot `(D_z^i F · w/ sin(2θ)^{η/2})²` with `i ≤ k`
  (`integrable_uncurry_slot_z`) and every mixed slot `(D_z^j D_θ^i F · W)²` with `1 ≤ i`,
  `i + j ≤ k` (`integrable_uncurry_slot_mixed`) is integrable for that product measure, by
  domination against the `ℋ^k`-integrand;
* hence, by monotonicity of the measure (`Integrable.mono_measure`), the same holds for the
  measure `(volume|_{(0,∞)}).prod (volume|_{Iθ})` which the statement uses
  (`integrable_of_Iz_prod`).

The requested theorem `TkA_slotIntegrable` is then the three instances
`F = Az Ψ = z²∂_z²Ψ` (with the `D_z`-slots for `i = 0,1` and the mixed slot `mixed 0 1`)
and `F = Bz Ψ = ∂_θ²Ψ` (with the `D_z`-slots for `i = 0,1`), the hypotheses `hmemA`, `hmemB`
being exactly the `ℋ¹`-memberships.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeSlotOneAe.Interp

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## Continuity of the product weight on the open quadrant -/

/-- The product weight `W = w·sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
theorem continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hsinpos : ∀ p ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) : Set (ℝ × ℝ)),
      0 < Real.sin (2 * p.2) := by
    intro p hp
    rw [Set.mem_prod] at hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [hp.2.2, Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    rw [Set.mem_prod] at hp
    exact pow_ne_zero 2 (ne_of_gt hp.1)
  have hsin : ContinuousOn
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  exact hw.mul hsin

/-! ## The `ℋ^k`-integrand is integrable on the closed quadrant -/

/-- **Tonelli for the `ℋ^k`-integrand.**  If `F` is `C^∞` on the open quadrant and
`HkMem α k F`, then the uncurried `HkIntegrand α k F` is integrable for the product of the
restrictions of Lebesgue measure to `Iz` and `Iθ`.  This is the two halves of `HkMem`
(fibrewise integrability and integrability of the fibre integrals) read through
`Work.Spaces.integrable_prod_of_iterated`; the a.e. strong measurability of the joint
integrand is the continuity of `HkIntegrand` on the open quadrant. -/
theorem integrable_uncurry_HkIntegrand {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => Work.Spaces.HkIntegrand α k F z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  (Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun z θ : ℝ => Work.Spaces.HkIntegrand α k F z θ)
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k F z θ)
    (Work.Spaces.aesm_of_continuousOn_Qd _ (hF.continuousOn_HkIntegrand α k))
    (by
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
      exact hmem.1 z hz)
    hmem.2).1

/-! ## The single `D_z`-slot is integrable on the closed quadrant -/

/-- **Product integrability of a weighted `D_z`-slot.**  For `F` smooth on the open quadrant
and in `ℋ^k`, and every `i ≤ k`, the square `(D_z^i F · w/sin(2θ)^{η/2})²` is integrable for
the product measure on `Iz × Iθ`: it is pointwise dominated by `HkIntegrand α k F`. -/
theorem integrable_uncurry_slot_z {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (i : ℕ) (hi : i ≤ k) :
    MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => (Work.Spaces.DzIter i F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  refine MeasureTheory.Integrable.mono' (integrable_uncurry_HkIntegrand hF hmem)
    ((Work.Spaces.aesm_of_continuousOn_Qd _ (hF.continuousOn_summand i)).pow 2) ?_
  filter_upwards with p
  obtain ⟨z, θ⟩ := p
  change ‖(Work.Spaces.DzIter i F z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2‖
      ≤ Work.Spaces.HkIntegrand α k F z θ
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact Work.Spaces.sq_le_HkIntegrand_z α k F z θ i hi

/-! ## A single mixed slot is integrable on the closed quadrant -/

/-- **Product integrability of a mixed slot.**  For `F` smooth on the open quadrant and in
`ℋ^k`, and every `1 ≤ i`, `i + j ≤ k`, the square `(D_z^j D_θ^i F · W)²` is integrable for
the product measure on `Iz × Iθ`. -/
theorem integrable_uncurry_slot_mixed {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ k) :
    MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ =>
        (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  refine MeasureTheory.Integrable.mono' (integrable_uncurry_HkIntegrand hF hmem) ?_ ?_
  · have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        (Work.Spaces.mixed j i F p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      (((hF.mixed j i).continuousOn).mul (continuousOn_Wt_Q0 α)).pow 2
    exact Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  · filter_upwards with p
    obtain ⟨z, θ⟩ := p
    change ‖(Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2‖
      ≤ Work.Spaces.HkIntegrand α k F z θ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α k F z θ i j hi hij

/-! ## Passing to the half-open half-line `(0,∞)` -/

/-- The product measure `(volume|_{(0,∞)}).prod (volume|_{Iθ})` is dominated by the product
measure on the closed quadrant `Iz × Iθ` (they differ by the null slice `{0} × Iθ`), so any
function integrable for the latter is integrable for the former. -/
theorem integrable_of_Iz_prod {G : ℝ × ℝ → ℝ}
    (hG : MeasureTheory.Integrable G
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    MeasureTheory.Integrable G
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hsub : Set.Ioi (0 : ℝ) ⊆ Work.Spaces.Iz := by
    intro z hz
    simp only [Work.Spaces.Iz, Set.mem_Ici]
    exact le_of_lt hz
  have hle : (MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      ≤ (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.Measure.prod_mono (MeasureTheory.Measure.restrict_mono hsub le_rfl) le_rfl
  exact hG.mono_measure hle

/-! ## Smoothness of the two data of the `A`-slot -/

/-- `A = z²∂_z²Ψ` is smooth on the open quadrant. -/
theorem smoothOpen_Az_of_smoothOpen {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Az Ψ) :=
  Work.FTS.EllipticEst.H2W.AeDataAofAux.smoothOpen_zsq_mul (hΨ.pzIter 2)

/-- `B = ∂_θ²Ψ` is smooth on the open quadrant. -/
theorem smoothOpen_Bz_of_smoothOpen {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Bz Ψ) := by
  have hfun : Work.Spaces.pth (Work.Spaces.pth Ψ)
      = (fun z θ : ℝ => Work.Spaces.pthIter 2 Ψ z θ) := rfl
  have h : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => Work.Spaces.pthIter 2 Ψ z θ) := by
    rw [← hfun]
    exact hΨ.pth.pth
  exact h

/-! ## The requested statement -/

theorem TkA_slotIntegrable {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hmemA : Work.Spaces.HkMem α 1 (Az Ψ)) (hmemB : Work.Spaces.HkMem α 1 (Bz Ψ)) :
    (∀ i : ℕ, i ≤ 1 → MeasureTheory.Integrable
        (Function.uncurry (fun z θ : ℝ => (Work.Spaces.DzIter i (Az Ψ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      ∧ (∀ i : ℕ, i ≤ 1 → MeasureTheory.Integrable
        (Function.uncurry (fun z θ : ℝ => (Work.Spaces.DzIter i (Bz Ψ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      ∧ MeasureTheory.Integrable
        (Function.uncurry (fun z θ : ℝ => (Work.Spaces.mixed 0 1 (Az Ψ) z θ
          * Work.Spaces.Wt α z θ) ^ 2))
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hA : Work.FTS.EllipticEst.SmoothOpen (Az Ψ) := smoothOpen_Az_of_smoothOpen hΨ
  have hB : Work.FTS.EllipticEst.SmoothOpen (Bz Ψ) := smoothOpen_Bz_of_smoothOpen hΨ
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact integrable_of_Iz_prod (integrable_uncurry_slot_z hA hmemA i hi)
  · intro i hi
    exact integrable_of_Iz_prod (integrable_uncurry_slot_z hB hmemB i hi)
  · exact integrable_of_Iz_prod
      (integrable_uncurry_slot_mixed hA hmemA 0 1 (by norm_num) (by norm_num))

end Work.FTS.EllipticEst.AeSlotOneAe.Interp
