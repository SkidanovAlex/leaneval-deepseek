import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.Analysis.HoleVoidCost.chiBGradGe
import Submission.Work.BoseB1Cube.cubeKinPeel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.slotPoincare_dlBox`

The **slot Friedrichs/Poincaré inequality on the sliding box** `B(u) = dlBox ℓ d u`:

    ∫_{abox n ℓ} (χ(xᵢ)·(Q_{B,i}Ind Φ) x)²
      ≤ 4·(ℓd)²·gradConst² · ∫_{abox n ℓ} Σ_k (∂_{kcDir n i k} (χ(·ᵢ)·Q_{B,i}Ind Φ))² ,

i.e. the `S_Q`-half of the `(D-ROW)` of `Submission/Work/BoseB1Cube/FINDING_cubeHoleCapRow_session2.md`
§5bis.  It is the *fibre* Poincaré inequality: for fixed configuration `r` of the other slots, the
one-particle fibre

    y ↦ χ_{B(u)}(y)·(Q_{B,i}Ind Φ)(…, y at slot i, …)

is supported in the sliding box `B(u)` (of side `ℓd`), so the classical Friedrichs/GNS inequality
(`Work.Analysis.HoleVoidCost.integral_sq_le_of_support_subset_cube`, the PROVED Poincaré inequality
of the corpus at `R = ℓd/2`, centre `(ℓd)•u`) bounds its `L²` mass by `(ℓd)²·gradConst²` times its
Dirichlet energy.  Only the *slot* Dirichlet energy appears, because the fibre derivative is
exactly the `kcDir`-directional derivative (`Work.BoseB1Cube.fderiv_slot_eq_fibre_low_aux`).

## Route (all inputs are PROVED corpus facts)

* `Work.BoseB1Cube.slotPoincareFibre` — the one-particle fibre inequality, itself the Poincaré
  inequality `integral_sq_le_of_support_subset_cube` at `R = ℓd/2` combined with
  `Work.Analysis.HoleVoidCost.integralFderivNormSqLeSum`/`opNorm_sq_eq_sum_sq` (operator norm vs.
  sum of basis derivatives) and the fact that `fderiv g = 0` off the closed box `B(u)`;
* `Submission.BoseGases.abox_integral_peel` — the measure-preserving slot peel of the many-particle
  box, which turns both the mass slot and the Dirichlet slot into iterated fibre integrals;
* `Work.BoseB1Cube.fderiv_slot_eq_fibre_low_aux` — the `kcDir`-directional derivative at the slot
  `i` of a many-particle function is the `kcStdBasis`-directional derivative of the one-particle
  fibre;
* `Work.BoseB1Cube.chiSmallB_mul_boxQInd_eq` — the `Q_B`-indicator is invisible to `chiSmallB`;
* `Work.BoseFixB1.chiSmallB_contDiff_two` / `Work.SmallBoxTBWord.boxQ_contDiff_of_compact` —
  the regularity (`chiSmallB M` is `C²` for `M ≥ 3`) and smoothness of the projected fibre.
-/

namespace Work.BoseB1Cube

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal ContDiff

local notation "E3" => EuclideanSpace ℝ (Fin 3)

noncomputable section

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## 1. The one-particle fibre Poincaré inequality on `B(u)` -/

/-- **Poincaré on the sliding box `B(u)`, in its fibre form.**  If `g : ℝ³ → ℝ` is `C¹` and
vanishes off the sliding box `dlBox ℓ d u`, then

    ∫_{acube ℓ} g² ≤ (ℓd)²·gradConst²·∫_{acube ℓ} Σ_k (∂_k g)² .

Only two properties of `g` are used: its support lies in the *closed* box `B(u)` (of side `ℓd`),
which supplies both the compact support for the Poincaré inequality and the vanishing of
`fderiv g` off `B(u)` — the latter is what allows the gradient integral (which the Poincaré
inequality produces over all of `ℝ³`) to be moved onto the big box `acube ℓ`. -/
theorem slotPoincareFibre {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) {g : E3 → ℝ}
    (hg : ContDiff ℝ 1 g)
    (hsupp : ∀ z : E3, z ∉ Submission.BoseGases.dlBox ℓ d u → g z = 0) :
    (∫ y in Submission.BoseGases.acube ℓ, (g y) ^ 2)
      ≤ (ℓ * d) ^ 2 * Work.Analysis.HoleVoidCost.gradConst ^ 2 *
        (∫ y in Submission.BoseGases.acube ℓ,
          ∑ k : Fin 3, (fderiv ℝ g y (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  have hR : 0 < ℓ * d / 2 := by positivity
  -- support, compact support and the support cube
  have hsupp' : Function.support g ⊆ Submission.BoseGases.dlBox ℓ d u := by
    intro z hz
    by_contra h
    exact hz (hsupp z h)
  have hcs : HasCompactSupport g :=
    HasCompactSupport.of_support_subset_isCompact
      (Work.SmallBoxTBWord.isCompact_dlBox hℓ hd u) hsupp'
  have hsuppcube : Function.support g ⊆
      {z : E3 | z - (ℓ * d) • u ∈ Submission.BoseGases.acube (ℓ * d)} := by
    intro z hz
    exact ((Submission.BoseGases.mem_dlBox_iff ℓ d u z).mp (hsupp' hz)).2
  -- the Poincaré (Friedrichs) inequality at `R = ℓd/2`, centre `(ℓd)•u`
  have hp : ∫ z : E3, (g z) ^ 2
      ≤ (ℓ * d) ^ 2 * Work.Analysis.HoleVoidCost.gradConst ^ 2
        * ∫ z : E3, ‖fderiv ℝ g z‖ ^ 2 := by
    have h := Work.Analysis.HoleVoidCost.integral_sq_le_of_support_subset_cube g hg hcs
      ((ℓ * d) • u) (ℓ * d / 2) hR (by rwa [show 2 * (ℓ * d / 2) = ℓ * d by ring])
    rwa [show 2 * (ℓ * d / 2) = ℓ * d by ring] at h
  -- `g` vanishes off the big box `acube ℓ` (its support lies in `B(u) ⊆ acube ℓ`)
  have hg0 : ∀ z : E3, z ∉ Submission.BoseGases.acube ℓ → g z = 0 := by
    intro z hz
    exact hsupp z (fun hmem => hz ((Submission.BoseGases.mem_dlBox_iff ℓ d u z).mp hmem).1)
  -- `fderiv g` vanishes off the closed box `B(u)`, hence off `acube ℓ`
  have hf0 : ∀ z : E3, z ∉ Submission.BoseGases.dlBox ℓ d u → fderiv ℝ g z = 0 := by
    intro z hz
    have hcl : IsClosed (Submission.BoseGases.dlBox ℓ d u) :=
      (Work.SmallBoxTBWord.isCompact_dlBox hℓ hd u).isClosed
    have hev : g =ᶠ[𝓝 z] fun _ : E3 => (0 : ℝ) := by
      filter_upwards [hcl.isOpen_compl.mem_nhds hz] with w hw
      exact hsupp w hw
    rw [hev.fderiv_eq]
    simp
  have hf0' : ∀ z : E3, z ∉ Submission.BoseGases.acube ℓ → fderiv ℝ g z = 0 := by
    intro z hz
    refine hf0 z (fun hmem => hz ((Submission.BoseGases.mem_dlBox_iff ℓ d u z).mp hmem).1)
  -- the mass integral, moved to the full space
  have hL : (∫ y in Submission.BoseGases.acube ℓ, (g y) ^ 2) = ∫ z : E3, (g z) ^ 2 :=
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by simpa using hg0 z hz)
  -- the gradient integral: operator norm = sum of squares on the standard basis
  have hpt : ∀ z : E3, ‖fderiv ℝ g z‖ ^ 2
      = ∑ k : Fin 3, (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
    intro z
    rw [Work.Analysis.HoleVoidCost.opNorm_sq_eq_sum_sq]
    exact Finset.sum_congr rfl (fun k _ => by
      rw [show Submission.BoseGases.kcStdBasis k = EuclideanSpace.single k (1 : ℝ) from rfl])
  have hD : (∫ z : E3, ‖fderiv ℝ g z‖ ^ 2)
      = ∫ z : E3, ∑ k : Fin 3, (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2 :=
    integral_congr_ae (Eventually.of_forall hpt)
  have hD2 : (∫ z : E3, ∑ k : Fin 3, (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2)
      = ∫ y in Submission.BoseGases.acube ℓ,
          ∑ k : Fin 3, (fderiv ℝ g y (Submission.BoseGases.kcStdBasis k)) ^ 2 :=
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := fun z : E3 =>
        ∑ k : Fin 3, (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2)
      (fun z hz => by rw [hf0' z hz]; simp)).symm
  calc (∫ y in Submission.BoseGases.acube ℓ, (g y) ^ 2)
      = ∫ z : E3, (g z) ^ 2 := hL
    _ ≤ (ℓ * d) ^ 2 * Work.Analysis.HoleVoidCost.gradConst ^ 2
          * ∫ z : E3, ‖fderiv ℝ g z‖ ^ 2 := hp
    _ = (ℓ * d) ^ 2 * Work.Analysis.HoleVoidCost.gradConst ^ 2
          * ∫ z : E3, ∑ k : Fin 3, (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
        rw [hD]
    _ = (ℓ * d) ^ 2 * Work.Analysis.HoleVoidCost.gradConst ^ 2
          * (∫ y in Submission.BoseGases.acube ℓ,
              ∑ k : Fin 3, (fderiv ℝ g y (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
        rw [hD2]

/-! ## 2. The slot Poincaré inequality on the many-particle box -/

theorem slotPoincare_dlBox {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {M : ℕ} (hM : 3 ≤ M) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin n) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.chiSmallB M ℓ d u (x i)
          * Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2)
      ≤ 4 * (ℓ * d) ^ 2 * Work.Analysis.HoleVoidCost.gradConst ^ 2
          * ∫ x in Submission.BoseGases.abox n ℓ, ∑ k : Fin 3,
              ((fderiv ℝ (fun y : Submission.BoseGases.X n =>
                  Submission.BoseGases.chiSmallB M ℓ d u (y i)
                    * Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                        (Submission.BoseGases.dlBox ℓ d u) i Φ y) x)
                (Submission.BoseGases.kcDir n i k)) ^ 2 := by
  have hM1 : 1 ≤ M := by omega
  rcases n with _ | m
  · exact i.elim0
  -- the state is `Φ : X (m+1) → ℝ` from here on
  let W : E3 → ℝ := Submission.BoseGases.chiSmallB M ℓ d u
  let V : ℝ := Work.SmallBoxSliding.boxMass ℓ d u
  let S : Set E3 := Submission.BoseGases.dlBox ℓ d u
  let P : Submission.BoseGases.X (m + 1) → ℝ := Work.SmallBoxTBWord.boxQ V S i Φ
  let B : Submission.BoseGases.X (m + 1) → ℝ := fun y : Submission.BoseGases.X (m + 1) =>
    Submission.BoseGases.chiSmallB M ℓ d u (y i)
      * Work.UBBInputs8.boxQInd V S i Φ y
  let A : Submission.BoseGases.X (m + 1) → ℝ := fun y : Submission.BoseGases.X (m + 1) =>
    W (y i) * P y
  have hAB : B = A := by
    simp only [B, A, W, V, S, P]
    exact Work.BoseB1Cube.chiSmallB_mul_boxQInd_eq hℓ hd hM1 u i Φ
  -- the `boxQ`-form of the goal, proved below
  have hgoal : (∫ x in Submission.BoseGases.abox (m + 1) ℓ, (A x) ^ 2)
      ≤ 4 * (ℓ * d) ^ 2 * Work.Analysis.HoleVoidCost.gradConst ^ 2
          * ∫ x in Submission.BoseGases.abox (m + 1) ℓ, ∑ k : Fin 3,
              ((fderiv ℝ A x) (Submission.BoseGases.kcDir (m + 1) i k)) ^ 2 := by
    -- smoothness of the projected fibre and of the windowed state
    have hPcd : ContDiff ℝ (⊤ : ℕ∞) P := by
      simp only [P, V, S]
      exact Work.SmallBoxTBWord.boxQ_contDiff_of_compact
        (Work.SmallBoxTBWord.isCompact_dlBox hℓ hd u)
        (Work.SmallBoxSliding.boxMass ℓ d u) i hΦ
    have hW1 : ContDiff ℝ 1 W := by
      simp only [W]
      exact (Work.BoseFixB1.chiSmallB_contDiff_two hM u).of_le (by norm_num)
    have hAcd : ContDiff ℝ 1 A := by
      simp only [A]
      exact (hW1.comp (by fun_prop : ContDiff ℝ 1
          (fun y : Submission.BoseGases.X (m + 1) => y i))).mul (hPcd.of_le (by norm_num))
    -- the two integrands are continuous on the compact box
    have hIntL : IntegrableOn (fun x : Submission.BoseGases.X (m + 1) => (A x) ^ 2)
        (Submission.BoseGases.abox (m + 1) ℓ) volume :=
      ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact (m + 1) hℓ)
        (hAcd.continuous.pow 2).continuousOn
    have hcontR : Continuous (fun x : Submission.BoseGases.X (m + 1) => ∑ k : Fin 3,
        (fderiv ℝ A x (Submission.BoseGases.kcDir (m + 1) i k)) ^ 2) := by
      have hfd : Continuous (fun x : Submission.BoseGases.X (m + 1) => fderiv ℝ A x) :=
        hAcd.continuous_fderiv (by norm_num)
      exact continuous_finsetSum _ (fun k _ => ((hfd.clm_apply continuous_const).pow 2))
    have hIntR : IntegrableOn (fun x : Submission.BoseGases.X (m + 1) => ∑ k : Fin 3,
        (fderiv ℝ A x (Submission.BoseGases.kcDir (m + 1) i k)) ^ 2)
        (Submission.BoseGases.abox (m + 1) ℓ) volume :=
      ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact (m + 1) hℓ)
        hcontR.continuousOn
    -- the peel, mass slot
    have hpeelL : (∫ x in Submission.BoseGases.abox (m + 1) ℓ, (A x) ^ 2)
        = ∫ r in Submission.BoseGases.abox m ℓ, ∫ y in Submission.BoseGases.acube ℓ,
            (W y * P (Submission.BoseGases.kcInsN m i (y, r))) ^ 2 := by
      rw [Submission.BoseGases.abox_integral_peel (n := m) i
        (fun x : Submission.BoseGases.X (m + 1) => (A x) ^ 2) hIntL]
      refine integral_congr_ae (Eventually.of_forall (fun r => ?_))
      refine integral_congr_ae (Eventually.of_forall (fun y => ?_))
      show (A (Submission.BoseGases.kcInsN m i (y, r))) ^ 2
        = (W y * P (Submission.BoseGases.kcInsN m i (y, r))) ^ 2
      simp only [A, Submission.BoseGases.kc_insN_apply_same]
    -- the fibre form of the Dirichlet slot equals its `A`-form
    have hfibForm : (∫ r in Submission.BoseGases.abox m ℓ, ∫ y in Submission.BoseGases.acube ℓ,
          ∑ k : Fin 3,
            (fderiv ℝ
              (fun w : E3 => W w * P (Submission.BoseGases.kcInsN m i (w, r))) y
              (Submission.BoseGases.kcStdBasis k)) ^ 2)
        = ∫ r in Submission.BoseGases.abox m ℓ, ∫ y in Submission.BoseGases.acube ℓ,
            ∑ k : Fin 3,
              (fderiv ℝ A (Submission.BoseGases.kcInsN m i (y, r)))
                (Submission.BoseGases.kcDir (m + 1) i k) ^ 2 := by
      refine integral_congr_ae (Eventually.of_forall (fun r => ?_))
      refine integral_congr_ae (Eventually.of_forall (fun y => ?_))
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hstep : fderiv ℝ A (Submission.BoseGases.kcInsN m i (y, r))
            (Submission.BoseGases.kcDir (m + 1) i k)
          = fderiv ℝ (fun z : Submission.BoseGases.X (m + 1) => W (z i) * P z)
              (Submission.BoseGases.kcInsN m i (y, r)) (Submission.BoseGases.kcDir (m + 1) i k) := by
        simp only [A]
      rw [← hstep, ← Work.BoseB1Cube.fderiv_slot_eq_fibre_low_aux (n := m) hW1 hPcd i r y k]
    -- the peel, Dirichlet slot
    have hpeelR : (∫ r in Submission.BoseGases.abox m ℓ, ∫ y in Submission.BoseGases.acube ℓ,
          ∑ k : Fin 3,
            (fderiv ℝ
              (fun w : E3 => W w * P (Submission.BoseGases.kcInsN m i (w, r))) y
              (Submission.BoseGases.kcStdBasis k)) ^ 2)
        = ∫ x in Submission.BoseGases.abox (m + 1) ℓ, ∑ k : Fin 3,
            (fderiv ℝ A x (Submission.BoseGases.kcDir (m + 1) i k)) ^ 2 := by
      rw [hfibForm, Submission.BoseGases.abox_integral_peel (n := m) i
        (fun x : Submission.BoseGases.X (m + 1) => ∑ k : Fin 3,
          (fderiv ℝ A x (Submission.BoseGases.kcDir (m + 1) i k)) ^ 2) hIntR]
    -- the pointwise (in `r`) fibre Poincaré bound
    have hfib : ∀ r : Submission.BoseGases.X m,
        (∫ y in Submission.BoseGases.acube ℓ,
            (W y * P (Submission.BoseGases.kcInsN m i (y, r))) ^ 2)
          ≤ 4 * (ℓ * d) ^ 2 * Work.Analysis.HoleVoidCost.gradConst ^ 2 *
            ∫ y in Submission.BoseGases.acube ℓ, ∑ k : Fin 3,
              (fderiv ℝ
                (fun w : E3 => W w * P (Submission.BoseGases.kcInsN m i (w, r))) y
                (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
      intro r
      have hfibcd : ContDiff ℝ 1 (fun y : E3 =>
          W y * P (Submission.BoseGases.kcInsN m i (y, r))) :=
        hW1.mul (((hPcd.comp (Work.SmallBoxBridge.Fourier.contDiff_kcInsN_right i r))).of_le
          (by norm_num))
      have hfiber0 : ∀ z : E3, z ∉ Submission.BoseGases.dlBox ℓ d u →
          (fun y : E3 => W y * P (Submission.BoseGases.kcInsN m i (y, r))) z = 0 := by
        intro z hz
        have h0 : W z = 0 := by
          simp only [W]
          by_contra h
          exact hz (Work.SlotWord.chiSmallB_support_mem_dlBox hM1 hℓ hd h)
        show W z * P (Submission.BoseGases.kcInsN m i (z, r)) = 0
        rw [h0, zero_mul]
      have h1 := slotPoincareFibre hℓ hd u (g := fun y : E3 =>
        W y * P (Submission.BoseGases.kcInsN m i (y, r))) hfibcd hfiber0
      have h2 : 0 ≤ ∫ y in Submission.BoseGases.acube ℓ, ∑ k : Fin 3,
          (fderiv ℝ
            (fun w : E3 => W w * P (Submission.BoseGases.kcInsN m i (w, r))) y
            (Submission.BoseGases.kcStdBasis k)) ^ 2 :=
        MeasureTheory.setIntegral_nonneg (Submission.BoseGases.acube_measurable ℓ)
          (fun y _ => Finset.sum_nonneg (fun k _ => sq_nonneg _))
      have h3 : 0 ≤ (ℓ * d) ^ 2 * Work.Analysis.HoleVoidCost.gradConst ^ 2 := by positivity
      nlinarith [h1, h2, h3]
    -- integrability of the two fibre integrals: transport along the measure-preserving peel
    let ν : Measure (Submission.BoseGases.X m) :=
      (volume : Measure (Submission.BoseGases.X m)).restrict (Submission.BoseGases.abox m ℓ)
    have hmp : MeasurePreserving (⇑(Submission.BoseGases.kcInsN m i))
        (((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod ν)
        ((volume : Measure (Submission.BoseGases.X (m + 1))).restrict
          (Submission.BoseGases.abox (m + 1) ℓ)) := by
      have h := MeasurePreserving.symm
        (e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => E3) i))
        (Submission.BoseGases.abox_peel_mp (n := m) ℓ i)
      simpa only [Submission.BoseGases.kcInsN, ν] using h
    have hprodL : Integrable (fun p : E3 × Submission.BoseGases.X m =>
        (fun x : Submission.BoseGases.X (m + 1) => (A x) ^ 2)
          (Submission.BoseGases.kcInsN m i p)) (((volume : Measure E3).restrict
            (Submission.BoseGases.acube ℓ)).prod ν) :=
      (hmp.integrable_comp (hg := (hAcd.continuous.pow 2).aestronglyMeasurable)).mpr hIntL
    have hprodR : Integrable (fun p : E3 × Submission.BoseGases.X m =>
        (fun x : Submission.BoseGases.X (m + 1) => ∑ k : Fin 3,
          (fderiv ℝ A x (Submission.BoseGases.kcDir (m + 1) i k)) ^ 2)
          (Submission.BoseGases.kcInsN m i p)) (((volume : Measure E3).restrict
            (Submission.BoseGases.acube ℓ)).prod ν) :=
      (hmp.integrable_comp (hg := hcontR.aestronglyMeasurable)).mpr hIntR
    have hsecL : Integrable (fun r : Submission.BoseGases.X m => ∫ y : E3,
        (fun p : E3 × Submission.BoseGases.X m => (A (Submission.BoseGases.kcInsN m i p)) ^ 2)
          (y, r) ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) ν :=
      Integrable.integral_prod_right hprodL
    have hsecR : Integrable (fun r : Submission.BoseGases.X m => ∫ y : E3,
        (fun p : E3 × Submission.BoseGases.X m => ∑ k : Fin 3,
          (fderiv ℝ A (Submission.BoseGases.kcInsN m i p)
            (Submission.BoseGases.kcDir (m + 1) i k)) ^ 2)
          (y, r) ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) ν :=
      Integrable.integral_prod_right hprodR
    have hfibIntL : IntegrableOn (fun r : Submission.BoseGases.X m =>
        ∫ y in Submission.BoseGases.acube ℓ,
          (W y * P (Submission.BoseGases.kcInsN m i (y, r))) ^ 2)
        (Submission.BoseGases.abox m ℓ) volume := by
      refine hsecL.congr (Eventually.of_forall (fun r => ?_))
      refine integral_congr_ae (Eventually.of_forall (fun y => ?_))
      show (A (Submission.BoseGases.kcInsN m i (y, r))) ^ 2
        = (W y * P (Submission.BoseGases.kcInsN m i (y, r))) ^ 2
      simp only [A, Submission.BoseGases.kc_insN_apply_same]
    have hfibIntR : IntegrableOn (fun r : Submission.BoseGases.X m =>
        ∫ y in Submission.BoseGases.acube ℓ, ∑ k : Fin 3,
          (fderiv ℝ
            (fun w : E3 => W w * P (Submission.BoseGases.kcInsN m i (w, r))) y
            (Submission.BoseGases.kcStdBasis k)) ^ 2)
        (Submission.BoseGases.abox m ℓ) volume := by
      refine hsecR.congr (Eventually.of_forall (fun r => ?_))
      refine integral_congr_ae (Eventually.of_forall (fun y => ?_))
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hstep : fderiv ℝ A (Submission.BoseGases.kcInsN m i (y, r))
            (Submission.BoseGases.kcDir (m + 1) i k)
          = fderiv ℝ (fun z : Submission.BoseGases.X (m + 1) => W (z i) * P z)
              (Submission.BoseGases.kcInsN m i (y, r)) (Submission.BoseGases.kcDir (m + 1) i k) := by
        simp only [A]
      rw [hstep, Work.BoseB1Cube.fderiv_slot_eq_fibre_low_aux (n := m) hW1 hPcd i r y k]
    -- integrate the pointwise fibre bound
    have hfibIntR' : IntegrableOn (fun r : Submission.BoseGases.X m =>
        4 * (ℓ * d) ^ 2 * Work.Analysis.HoleVoidCost.gradConst ^ 2 *
          (∫ y in Submission.BoseGases.acube ℓ, ∑ k : Fin 3,
            (fderiv ℝ
              (fun w : E3 => W w * P (Submission.BoseGases.kcInsN m i (w, r))) y
              (Submission.BoseGases.kcStdBasis k)) ^ 2))
        (Submission.BoseGases.abox m ℓ) volume :=
      hfibIntR.const_mul _
    have hmono : (∫ r in Submission.BoseGases.abox m ℓ, ∫ y in Submission.BoseGases.acube ℓ,
          (W y * P (Submission.BoseGases.kcInsN m i (y, r))) ^ 2)
        ≤ ∫ r in Submission.BoseGases.abox m ℓ,
            (4 * (ℓ * d) ^ 2 * Work.Analysis.HoleVoidCost.gradConst ^ 2 *
              ∫ y in Submission.BoseGases.acube ℓ, ∑ k : Fin 3,
                (fderiv ℝ
                  (fun w : E3 => W w * P (Submission.BoseGases.kcInsN m i (w, r))) y
                  (Submission.BoseGases.kcStdBasis k)) ^ 2) :=
      integral_mono_ae hfibIntL hfibIntR' (Eventually.of_forall hfib)
    calc (∫ x in Submission.BoseGases.abox (m + 1) ℓ, (A x) ^ 2)
        = ∫ r in Submission.BoseGases.abox m ℓ, ∫ y in Submission.BoseGases.acube ℓ,
            (W y * P (Submission.BoseGases.kcInsN m i (y, r))) ^ 2 := hpeelL
      _ ≤ ∫ r in Submission.BoseGases.abox m ℓ,
            (4 * (ℓ * d) ^ 2 * Work.Analysis.HoleVoidCost.gradConst ^ 2 *
              ∫ y in Submission.BoseGases.acube ℓ, ∑ k : Fin 3,
                (fderiv ℝ
                  (fun w : E3 => W w * P (Submission.BoseGases.kcInsN m i (w, r))) y
                  (Submission.BoseGases.kcStdBasis k)) ^ 2) := hmono
      _ = 4 * (ℓ * d) ^ 2 * Work.Analysis.HoleVoidCost.gradConst ^ 2 *
            (∫ r in Submission.BoseGases.abox m ℓ, ∫ y in Submission.BoseGases.acube ℓ,
              ∑ k : Fin 3,
                (fderiv ℝ
                  (fun w : E3 => W w * P (Submission.BoseGases.kcInsN m i (w, r))) y
                  (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
          rw [MeasureTheory.integral_const_mul]
      _ = 4 * (ℓ * d) ^ 2 * Work.Analysis.HoleVoidCost.gradConst ^ 2 *
            (∫ x in Submission.BoseGases.abox (m + 1) ℓ, ∑ k : Fin 3,
              (fderiv ℝ A x (Submission.BoseGases.kcDir (m + 1) i k)) ^ 2) := by
          rw [hpeelR]
  change (∫ x in Submission.BoseGases.abox (m + 1) ℓ, (B x) ^ 2)
      ≤ 4 * (ℓ * d) ^ 2 * Work.Analysis.HoleVoidCost.gradConst ^ 2
        * ∫ x in Submission.BoseGases.abox (m + 1) ℓ, ∑ k : Fin 3,
            ((fderiv ℝ B x) (Submission.BoseGases.kcDir (m + 1) i k)) ^ 2
  rw [hAB]
  exact hgoal

end

end Work.BoseB1Cube
