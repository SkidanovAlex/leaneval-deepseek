import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Asm
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.t1SlotTermZ
import Submission.Work.FTS.StrongPersist.N6_L12H
import Submission.Work.FTS.StrongPersist.QangSq6
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.pz_DthIter_mul_eq
-- ===== merged: Submission.Work.FTS.StrongPersist.ClauseFields =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.VocabO (HQo)

set_option autoImplicit false
set_option linter.unusedVariables false


end Work.FTS.StrongPersist
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Rec7 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

/-- **The recurrence `D_z^{k+1} L₁₂(g) = -Qang g k` up to `k = 6`.**

`L₁₂(g)(z) = ∫_z^∞ L12dens g r dr` and `L12dens g r = Qang g 0 r / r`, so the fundamental
theorem of calculus gives the case `k = 0` (the differentiability of `L₁₂(g)` on `(0,∞)` is
`UopHk.contDiffOn_L12_of_smoothOpen_Hk`, whose only hypotheses are `SmoothOpen g` and
`HkMem α 6 g`), and the induction step differentiates the identity `D_z^{k+1} L₁₂(g) = -Qang g k`
near `z` using the supplied chain rule `∂_z (Qang g k) z = Qang g (k+1) z / z`. -/
theorem L12Rec7 {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 6 g)
    (hqder : ∀ j : ℕ, j ≤ 5 → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => Work.Elliptic.Qang g j w) (Work.Elliptic.Qang g (j + 1) z / z) z) :
    ∀ k : ℕ, k ≤ 6 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (k + 1) (fun z => Work.Elliptic.L12 g z) z = - Work.Elliptic.Qang g k z := by
  -- the derivative of `L₁₂(g)`, from `L₁₂(g) = 3 ∫_z^∞ F_*(r)/r dr`
  have hderiv : ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z => Work.Elliptic.L12 g z) (-(Work.Elliptic.L12dens g z)) z := by
    intro z hz
    have h12 := (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 6 g hO hmem
      (by norm_num : 2 ≤ 6)).2
    refine (h12 z hz).congr_deriv ?_
    rw [Work.Elliptic.L12dens_eq_three_Fstar_div]
    ring
  intro k
  induction k with
  | zero =>
      intro _ z hz
      have hd : deriv (fun z => Work.Elliptic.L12 g z) z = -(Work.Elliptic.L12dens g z) :=
        (hderiv z hz).deriv
      change z * deriv (fun z => Work.Elliptic.L12 g z) z = - Work.Elliptic.Qang g 0 z
      rw [hd, Work.Elliptic.L12dens_eq_Qang_div, mul_neg, neg_inj,
        mul_div_cancel₀ _ (ne_of_gt hz)]
  | succ n ih =>
      intro hn z hz
      have hev : Work.Elliptic.DzdIter (n + 1) (fun z => Work.Elliptic.L12 g z)
          =ᶠ[𝓝 z] (fun z' => - Work.Elliptic.Qang g n z') := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih (by omega) z' hz'
      have hdv : deriv (Work.Elliptic.DzdIter (n + 1) (fun z => Work.Elliptic.L12 g z)) z
          = - deriv (fun z' => Work.Elliptic.Qang g n z') z := by
        rw [hev.deriv_eq]
        exact deriv.neg
      change z * deriv (Work.Elliptic.DzdIter (n + 1) (fun z => Work.Elliptic.L12 g z)) z
          = - Work.Elliptic.Qang g (n + 1) z
      rw [hdv, mul_neg, neg_inj, (hqder n (by omega) z hz).deriv,
        mul_div_cancel₀ _ (ne_of_gt hz)]

end Work.FTS.StrongPersist.H6Pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6Aux.zeroTerm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6Aux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_gam_eq)

set_option maxHeartbeats 1600000

/-! ## Helpers for `zeroTerm` -/

/-- `SmoothOpen` gives continuity on the open quadrant. -/
theorem smoothOpen_continuousOn_Q0 {F : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.SmoothOpen F) :
    ContinuousOn (Function.uncurry F) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (h.forall 0).continuousOn

/-- The two angular endpoints of `Iθ` are null, so `θ ∈ (0, π/2)` almost everywhere. -/
theorem ae_Iθ_mem_Ioo :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hθ : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2)).symm
  rw [MeasureTheory.Measure.restrict_congr_set hθ]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- A `canonW q`-weighted mixed slot of order `a + b ≤ k` with `1 ≤ a` and `q ≤ γ` is dominated
by the `ℋ^k`-integrand, on the open angular interval. -/
theorem canonW_mul_mixed_le_hk (α q : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (a b : ℕ)
    (hqγ : q ≤ Work.Spaces.gam α) (ha : 1 ≤ a) (hab : a + b ≤ k) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hmono : canonW q z θ ≤ canonW (Work.Spaces.gam α) z θ :=
    Work.FTS.StrongPersist.N6Trans.SixAux.canonW_mono_open hqγ hθ
  have hWt : canonW (Work.Spaces.gam α) z θ = (Work.Spaces.Wt α z θ) ^ 2 :=
    canonW_gam_eq α z θ (Set.Ioo_subset_Icc_self hθ)
  calc canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
      ≤ canonW (Work.Spaces.gam α) z θ * (Work.Spaces.mixed b a g z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hmono (sq_nonneg _)
    _ = (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2 := by rw [hWt]; ring
    _ ≤ Work.Spaces.HkIntegrand α k g z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α k g z θ a b ha hab

/-- **The pointwise domination of the `zeroTerm` integrand** on the open quadrant:
`|canonW q · A · D_θ(mixed b a f) · mixed b a f|` is at most `(K0/2)` times the sum of the
level-`7` and the level-`6` integrands. -/
theorem zeroTerm_integrand_le (α q : ℝ) {A f : ℝ → ℝ → ℝ} {K0 : ℝ} {a b : ℕ}
    (hK0 : 0 ≤ K0) (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (hab : a + b ≤ 6)
    (hval : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0)
    (hfsm : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |canonW q z θ * A z θ * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
        * Work.Spaces.mixed b a f z θ|
      ≤ (K0 / 2) * (Work.Spaces.HkIntegrand α 7 f z θ
          + Work.Spaces.HkIntegrand α 6 f z θ) := by
  have hIθ : θ ∈ Work.Spaces.Iθ := Set.Ioo_subset_Icc_self hθ
  have hcw : 0 ≤ canonW q z θ := canonW_nonneg hIθ
  have hW2 : canonW q z θ * (Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 7 f z θ := by
    rw [Work.FTS.StrongPersist.N6Trans.T1Hon.Dth_mixed_eq hfsm b a hz hθ]
    exact canonW_mul_mixed_le_hk α q 7 f (a + 1) b hqγ (by omega) (by omega) hθ
  have hZ2 : canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.FTS.StrongPersist.N6Trans.SixAux.canonW_mixed_le6_open α q f a b hqγ hqη hab hθ
  have hA : |A z θ| ≤ K0 := hval z θ hz hθ.1 hθ.2
  have hAM : 2 * |Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ|
        * |Work.Spaces.mixed b a f z θ|
      ≤ (Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ) ^ 2
        + (Work.Spaces.mixed b a f z θ) ^ 2 := by
    have h := two_mul_le_add_sq |Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ|
      |Work.Spaces.mixed b a f z θ|
    rw [sq_abs, sq_abs] at h
    exact h
  have hstep : 2 * (canonW q z θ * |Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ|
        * |Work.Spaces.mixed b a f z θ|)
      ≤ canonW q z θ * (Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ) ^ 2
        + canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2 := by
    nlinarith [hAM, hcw]
  calc |canonW q z θ * A z θ * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
          * Work.Spaces.mixed b a f z θ|
      = canonW q z θ * |A z θ| * |Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ|
          * |Work.Spaces.mixed b a f z θ| := by
        simp only [abs_mul, abs_of_nonneg hcw]
    _ ≤ canonW q z θ * K0 * |Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ|
          * |Work.Spaces.mixed b a f z θ| := by
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        exact mul_le_mul_of_nonneg_left hA hcw
    _ = (K0 / 2) * (2 * (canonW q z θ * |Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ|
          * |Work.Spaces.mixed b a f z θ|)) := by ring
    _ ≤ (K0 / 2) * (canonW q z θ * (Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ) ^ 2
          + canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2) :=
        mul_le_mul_of_nonneg_left hstep (by linarith)
    _ ≤ (K0 / 2) * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ) :=
        mul_le_mul_of_nonneg_left (add_le_add hW2 hZ2) (by linarith)

/-- **The three conjuncts of `zeroTerm` for a single canonical weight `canonW q`.**  The constant
`C` and its slice-level hypothesis `hC` are the two components of
`Work.FTS.StrongPersist.N6Trans.T1SixAux.hardSlotSliceSixZero` (with the existential opened);
everything else is proved here. -/
theorem zeroTerm_canon {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ (q Kf z : ℝ) (F Y : ℝ → ℝ → ℝ),
      0 ≤ q → q ≤ 2 → 0 ≤ Kf → z ∈ Work.Spaces.Iz →
      Work.FTS.EllipticEst.SmoothOpen F → Work.FTS.EllipticEst.SmoothOpen Y →
      (∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → |F z θ| ≤ Kf) →
      (∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → |Work.Spaces.Dth F z θ| ≤ Kf) →
      MeasureTheory.IntegrableOn (fun θ : ℝ => canonW q z θ * (Y z θ) ^ 2) Work.Spaces.Iθ →
      |∫ θ in Work.Spaces.Iθ, canonW q z θ * F z θ * Work.Spaces.Dth Y z θ * Y z θ|
        ≤ C * Kf * ∫ θ in Work.Spaces.Iθ, canonW q z θ * (Y z θ) ^ 2)
    (α : ℝ) {A f : ℝ → ℝ → ℝ} {K0 : ℝ} {a b : ℕ} {q : ℝ}
    (hsmA : Work.FTS.EllipticEst.SmoothOpen A) (hK0 : 0 ≤ K0)
    (hval : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0)
    (hdb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.Dth A z θ| ≤ K0)
    (hfsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hf6 : Work.Spaces.HkMem α 6 f) (hf7 : Work.Spaces.HkMem α 7 f)
    (hab : a + b ≤ 6) (hq0 : 0 ≤ q) (hq2 : q ≤ 2)
    (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => canonW q z θ * A z θ
        * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ)
        Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, canonW q z θ * A z θ
        * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ)
        Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * A z θ
        * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ|
      ≤ C * K0 * Work.Spaces.HkSq α 6 f := by
  have hZsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.mixed b a f) := hfsm.mixed b a
  have hWsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dth (Work.Spaces.mixed b a f)) := hZsm.Dth
  have hsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ =>
      canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ :=
    fun z hz => Work.FTS.StrongPersist.N6Trans.T1SixAux.slotSliceIntegrable α q hfsm hf6
      hqγ hqη hab hz
  obtain ⟨henergyI, henergyB⟩ :=
    Work.FTS.StrongPersist.N6Trans.T1SixAux.slotEnergyZOuter α q hfsm hf6 hq0 hqγ hqη hab
  -- the slice-level bound, valid at every `z ∈ Iz` (trivially at `z = 0`)
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ, canonW q z θ * A z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ|
        ≤ C * K0 * ∫ θ in Work.Spaces.Iθ,
            canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2 := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      have h1 : (∫ θ in Work.Spaces.Iθ, canonW q 0 θ * A 0 θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) 0 θ
          * Work.Spaces.mixed b a f 0 θ) = 0 := by
        rw [show (fun θ : ℝ => canonW q 0 θ * A 0 θ
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) 0 θ
            * Work.Spaces.mixed b a f 0 θ) = fun _ => (0 : ℝ) from
          funext fun θ => by simp [canonW_zero_z], MeasureTheory.integral_zero]
      have h2 : (∫ θ in Work.Spaces.Iθ,
          canonW q 0 θ * (Work.Spaces.mixed b a f 0 θ) ^ 2) = 0 := by
        rw [show (fun θ : ℝ => canonW q 0 θ * (Work.Spaces.mixed b a f 0 θ) ^ 2)
            = fun _ => (0 : ℝ) from funext fun θ => by simp [canonW_zero_z],
          MeasureTheory.integral_zero]
      rw [h1, h2, abs_zero, mul_zero]
    · exact hC q K0 z A (Work.Spaces.mixed b a f) hq0 hq2 hK0 hz hsmA hZsm
        (fun θ hθ hθ2 => hval z θ hzpos hθ hθ2)
        (fun θ hθ hθ2 => hdb z θ hzpos hθ hθ2) (hsl z hz)
  refine ⟨?_, ?_, ?_⟩
  · -- first conjunct: `θ`-slice integrability of the integrand
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      rw [show (fun θ : ℝ => canonW q 0 θ * A 0 θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) 0 θ
          * Work.Spaces.mixed b a f 0 θ) = fun _ => (0 : ℝ) from
        funext fun θ => by simp [canonW_zero_z]]
      exact integrableOn_zero
    · have hcont : ContinuousOn (fun p : ℝ × ℝ => canonW q p.1 p.2 * A p.1 p.2
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2)
            (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        ((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
          (smoothOpen_continuousOn_Q0 hsmA)).mul
          (smoothOpen_continuousOn_Q0 hWsm) |>.mul (smoothOpen_continuousOn_Q0 hZsm)
      refine MeasureTheory.Integrable.mono'
        (((hf7.1 z hz).add (hf6.1 z hz)).const_mul (K0 / 2))
        (Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hzpos) ?_
      filter_upwards [ae_Iθ_mem_Ioo] with θ hθ
      rw [Real.norm_eq_abs]
      exact zeroTerm_integrand_le α q hK0 hqγ hqη hab hval hfsm hzpos hθ
  · -- second conjunct: integrability of the marginal
    have hcont : ContinuousOn (fun p : ℝ × ℝ => canonW q p.1 p.2 * A p.1 p.2
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      ((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
        (smoothOpen_continuousOn_Q0 hsmA)).mul
        (smoothOpen_continuousOn_Q0 hWsm) |>.mul (smoothOpen_continuousOn_Q0 hZsm)
    refine MeasureTheory.Integrable.mono' (henergyI.const_mul (C * K0))
      (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right' ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    rw [Real.norm_eq_abs]
    exact hslice z hz
  · -- third conjunct: the bound
    calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * A z θ
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ|
        ≤ ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, canonW q z θ * A z θ
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            * Work.Spaces.mixed b a f z θ| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ z in Work.Spaces.Iz, (C * K0) * (∫ θ in Work.Spaces.Iθ,
            canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2) := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun z => abs_nonneg _))
            (henergyI.const_mul (C * K0)) ?_
          exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
            (fun z hz => hslice z hz)
      _ = (C * K0) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2) :=
          MeasureTheory.integral_const_mul (C * K0) _
      _ ≤ (C * K0) * Work.Spaces.HkSq α 6 f :=
          mul_le_mul_of_nonneg_left henergyB (mul_nonneg hCpos.le hK0)

/-- ## Route (all listed ingredients are already proved in this workspace)

Let `Z := mixed b a f`, so `Dth Z = mixed b (a+1) f`.  The bound is the θ-transport estimate:
use the proved slice-level lemma `Work.FTS.StrongPersist.N6Trans.T1SixAux.hardSlotSliceSixZero`
with `q := qρ` (the exponent of the leaf weight, `ρ = canonW qρ`, `0 ≤ qρ ≤ 2`) and `Kf := K0`,
applied at every `z ∈ Iz`: it gives
`|∫_θ canonW qρ z θ * A z θ * Dth Z z θ * Z z θ| ≤ (3/2) K0 ∫_θ canonW qρ z θ * (Z z θ)²`,
its hypotheses being `0 ≤ K0`, the two pointwise bounds `|A| ≤ K0`, `|Dth A| ≤ K0`, `SmoothOpen A`,
`SmoothOpen Z` (from `DatHyp.sm` and `α ≤ 1`) and the θ-slice integrability of
`canonW qρ z · * (Z z ·)²` — which is `T1SixAux.slotSliceIntegrable` (`a ≥ 1`) resp.
`SlotT2.zslot_slice_integrable` (`a = 0`, `qρ ∈ {η,0}`), from `DatHyp.h6`.

Then `|∫_z ∫_θ ...| ≤ ∫_z |∫_θ ...| ≤ (3/2) K0 ∫_z ∫_θ canonW qρ z θ (Z z θ)²`
(`MeasureTheory.abs_integral_le_integral_abs` on the integrable marginal, then
`MeasureTheory.integral_mono_of_nonneg`), and the last quantity is `≤ (3/2) K0 HkSq α 6 f` by
`T1SixAux.energy_mixed6` (`a ≥ 1`) resp. `T1SixAux.energy_z6` (`a = 0`, weight `≤ η`).

For the integrability conjuncts: pointwise on the open quadrant
`ρ|A||Dth Z||Z| ≤ K0 (ρ|Dth Z|² + ρ|Z|²)/2`; `ρ|Z|² ≤ HkIntegrand α 6 f` and, since `a + b ≤ 6`,
`ρ|Dth Z|² ≤ HkIntegrand α 7 f` (`Z7 := Dth Z = mixed b (a+1) f` has order `≤ 7`, angular `≥ 1`
when `a ≥ 1`; when `a = 0` use the pure slot with the `η` weight and `HkIntegrand α 7 f` — note
`DatHyp.h7` is present exactly for this).  Hence both conjuncts follow with
`MeasureTheory.Integrable.mono'` and `DatHyp.h6`, `DatHyp.h7`. -/
theorem zeroTerm : ∃ C : ℝ, 0 < C ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ (A f : Work.FTS.Galerkin.Fn) (K0 M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → 0 ≤ K0 →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.Dth A z θ| ≤ K0) →
      Work.FTS.StrongPersist.H6Rows.Npair6Aux.DatHyp α f M → a + b ≤ 6 →
      Work.FTS.TransportS.IsLeafW α a ρ →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => ρ z θ * A z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ)
          Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, ρ z θ * A z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ)
          Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * A z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ|
        ≤ C * K0 * Work.Spaces.HkSq α 6 f := by
  obtain ⟨C6, hC6pos, hC6⟩ := Work.FTS.StrongPersist.N6Trans.T1SixAux.hardSlotSliceSixZero
  refine ⟨C6, hC6pos, ?_⟩
  intro α hαmem A f K0 M a b ρ hsmA hK0 hval hdb hdat hab hleaf
  obtain ⟨hα, hα1⟩ := hαmem
  obtain ⟨hfsm, hf6, hf7, -, -, -⟩ := hdat
  rcases hleaf with hρ | hρ | ⟨ha1, hρ⟩
  · -- `ρ = leafEta = canonW η`
    rw [hρ]
    exact zeroTerm_canon hC6pos hC6 α hsmA hK0 hval hdb hfsm hf6 hf7 hab
      (q := Work.Spaces.eta) (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta])
      (by rw [Work.Spaces.gam, Work.Spaces.eta]; linarith)
      (fun _ => by norm_num [Work.Spaces.eta])
  · -- `ρ = leafOne = canonW 0`
    rw [hρ]
    rw [show Work.FTS.TransportS.leafOne = canonW 0 from by
      funext z θ
      simp only [Work.FTS.TransportS.leafOne, canonW, neg_zero, Real.rpow_zero, mul_one]]
    exact zeroTerm_canon hC6pos hC6 α hsmA hK0 hval hdb hfsm hf6 hf7 hab
      (q := 0) (by norm_num) (by norm_num) (by rw [Work.Spaces.gam]; linarith)
      (fun _ => by norm_num [Work.Spaces.eta])
  · -- `ρ = leafGam α = canonW γ`, with `1 ≤ a`
    rw [hρ]
    exact zeroTerm_canon hC6pos hC6 α hsmA hK0 hval hdb hfsm hf6 hf7 hab
      (q := Work.Spaces.gam α) (by rw [Work.Spaces.gam]; linarith)
      (by rw [Work.Spaces.gam]; linarith) (le_refl _) (fun _ => False.elim (by omega))

end Work.FTS.StrongPersist.H6Rows.Npair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L6Aux.L12SlotSum6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L6Aux

/-- **The `H^6`-bound for the `z`-slots of `L₁₂(g)`.**

`L₁₂(g)` is a function of `z` alone; the `q`-th summand is the weighted square of its `q`-th
`D_z`-iterate, `D_z^q = (z ∂_z)^q`.  The `q = 0` slot is controlled by the weighted Hardy
inequality (`l12L6_bundle`), and the slots `1 ≤ q ≤ 6` by the index-raising recursion
`D_z^q L₁₂(g) = -Qang g (q-1)` together with the level-six angular-moment bound `QangSq6`.
The constant is `113 · ∫_θ K² + 1`, with `K(θ) = 3 sinθ cos²θ`. -/
theorem L12SlotSum6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ g : ℝ → ℝ → ℝ,
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
      Work.Construction.L12 g 0 = 0 →
      MeasureTheory.IntegrableOn
          (fun z => ∑ q ∈ Finset.range 7,
            (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 g z) z 0) ^ 2
              * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 7,
            (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 g z) z 0) ^ 2
              * (Work.Spaces.w z) ^ 2) ≤ C * Work.Spaces.HkSq α 6 g := by
  refine ⟨113 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1, ?_, ?_⟩
  · have h : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
      MeasureTheory.integral_nonneg fun θ => sq_nonneg _
    linarith
  intro α hα hα1 g hO hmem h0
  -- the elliptic spelling of the vanishing hypothesis
  have h0e : Work.Elliptic.L12 g 0 = 0 := by
    rw [← Work.FTS.H2.constructionL12_eq_ellipticL12 g]
    exact h0
  -- the level-six `L₁₂`-bundle: the recursion `D_z^{k+1} L₁₂(g) = -Qang g k` (`k ≤ 5`),
  -- the weighted Hardy slot `k = 0`, and the level-six angular-moment bound
  obtain ⟨hgen, hInt0, hBnd0⟩ :=
    Work.FTS.StrongPersist.l12L6_bundle (α := α) (g := g) hO hmem h0e
      (fun j hj z hz =>
        (Work.FTS.StrongPersist.QangDiff6 (α := α) (g := g) hO hmem).1 j hj z hz)
      ((Work.FTS.StrongPersist.QangSq6 (α := α) (g := g) hO hmem) 0 (by norm_num)).1
  have hQsq := Work.FTS.StrongPersist.QangSq6 (α := α) (g := g) hO hmem
  -- the abstract slot sum, for an arbitrary radial `u` satisfying the three facts
  have main : ∀ (u : ℝ → ℝ),
      (∀ k : ℕ, k ≤ 5 → ∀ z : ℝ, 0 < z →
        Work.Elliptic.DzdIter (k + 1) u z = - Work.Elliptic.Qang g k z) →
      MeasureTheory.IntegrableOn (fun z => (u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        Work.Spaces.Iz →
      (∫ z in Work.Spaces.Iz, (u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 107 * (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) →
      MeasureTheory.IntegrableOn
            (fun z => ∑ q ∈ Finset.range 7,
              (Work.Elliptic.DzdIter q u z) ^ 2 * (Work.Spaces.w z) ^ 2)
            Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 7,
              (Work.Elliptic.DzdIter q u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ 113 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * Work.Spaces.HkSq α 6 g) := by
    intro u hu hIntu hBndu
    -- the recursion identifies the slots `1 ≤ i ≤ 6` with the angular moments, a.e.
    have htr : ∀ i : ℕ, 1 ≤ i → i ≤ 6 →
        ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          (Work.Elliptic.Qang g (i - 1) z) ^ 2 * (Work.Spaces.w z) ^ 2
            = (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
      intro i hi hi6
      rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
      filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)]
        with z hz0 hzI
      have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz0)
      have key : Work.Elliptic.DzdIter i u z = - Work.Elliptic.Qang g (i - 1) z := by
        have h := hu (i - 1) (by omega) z hzpos
        rwa [show i - 1 + 1 = i by omega] at h
      rw [key, neg_sq]
    -- integrability of every slot
    have hslot : ∀ i : ℕ, i ≤ 6 → MeasureTheory.IntegrableOn
        (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        Work.Spaces.Iz := by
      intro i hi6
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h
        simpa only [Work.Elliptic.DzdIter_zero] using hIntu
      · exact ((hQsq (i - 1) (by omega)).1).congr (htr i h hi6)
    have hsum_int : ∀ i ∈ Finset.range 7, MeasureTheory.IntegrableOn
        (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        Work.Spaces.Iz :=
      fun i hi => hslot i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    -- the bounds of the individual slots
    have hBnd0' : (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter 0 u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 107 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkSq α 6 g) := by
      have hb : (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter 0 u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ 107 * (∫ z in Work.Spaces.Iz,
              (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
        simpa only [Work.Elliptic.DzdIter_zero] using hBndu
      exact le_trans hb (mul_le_mul_of_nonneg_left (hQsq 0 (by norm_num)).2 (by norm_num))
    have hBndI : ∀ i : ℕ, 1 ≤ i → i ≤ 6 →
        (∫ z in Work.Spaces.Iz, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 6 g := by
      intro i hi hi6
      rw [← MeasureTheory.integral_congr_ae (htr i hi hi6)]
      exact (hQsq (i - 1) (by omega)).2
    -- the sum of the slots
    have hsum_le : (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 7,
          (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 113 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkSq α 6 g) := by
      rw [MeasureTheory.integral_finsetSum (Finset.range 7) hsum_int, Finset.sum_range_succ']
      have h6 : (∑ i ∈ Finset.range 6, (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter (i + 1) u z) ^ 2 * (Work.Spaces.w z) ^ 2))
          ≤ ∑ _i ∈ Finset.range 6,
              ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
                * Work.Spaces.HkSq α 6 g) :=
        Finset.sum_le_sum fun i hi => by
          rw [Finset.mem_range] at hi
          exact hBndI (i + 1) (by omega) (by omega)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h6
      refine le_trans (add_le_add h6 hBnd0') (le_of_eq ?_)
      ring
    exact ⟨MeasureTheory.integrable_finsetSum (Finset.range 7) hsum_int, hsum_le⟩
  -- rewrite the goal into the elliptic spelling
  have hfun : (fun z (_ : ℝ) => Work.Construction.L12 g z)
      = (fun z (_ : ℝ) => Work.Elliptic.L12 g z) := by
    funext z θ
    exact congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 g) z
  rw [hfun]
  -- replace the `Spaces`-iterates by the one-dimensional `DzdIter`
  have hsumfun : (fun z => ∑ q ∈ Finset.range 7,
        (Work.Spaces.DzIter q (fun z _ => Work.Elliptic.L12 g z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2)
      = (fun z => ∑ q ∈ Finset.range 7,
        (Work.Elliptic.DzdIter q (fun z => Work.Elliptic.L12 g z) z) ^ 2
          * (Work.Spaces.w z) ^ 2) := by
    funext z
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Work.Elliptic.DzIter_rad]
  rw [hsumfun]
  obtain ⟨hI, hB⟩ :=
    main (fun z => Work.Elliptic.L12 g z) (fun k hk z hz => hgen k hk z hz) hInt0 hBnd0
  refine ⟨hI, ?_⟩
  refine le_trans hB ?_
  have hnn : 0 ≤ Work.Spaces.HkSq α 6 g := Work.Spaces.HkSq_nonneg α 6 g
  nlinarith [hnn]

end Work.FTS.StrongPersist.L6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixAux.ExcPairBranches =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The four exceptional branches of the level-6 `T2` per-summand bound

The Leibniz summands of `term_bound` in which the pointwise sup at order `5` would be needed,
handled instead by (i) the Cauchy–Schwarz pairing of two pure slots, (ii) the `σ`-gain of
`D_θf`, or (iii) the exceptional `L²` pairing `exc_pair_pm`.

Each lemma concludes exactly the shape of `term_bound`'s conclusion, so that `term_bound` can
invoke it directly.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_mono)
open Work.FTS.StrongPersist.N6Trans.T1SixAux (SlotW6 slotW6_z slotW6_mixed)

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- The `Kg·(√|f|²·√|g|²) ≤ Λ|g|²` bookkeeping, isolated for reuse. -/
theorem hcross_sqrt {α Λ Kg : ℝ} {f g : ℝ → ℝ → ℝ}
    (hΛ2 : Kg * Work.Spaces.HkNorm α 6 f ≤ Λ * Work.Spaces.HkNorm α 6 g) :
    Kg * (Real.sqrt (Work.Spaces.HkSq α 6 f) * Real.sqrt (Work.Spaces.HkSq α 6 g))
      ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
  have hsq : Work.Spaces.HkNorm α 6 g = Real.sqrt (Work.Spaces.HkSq α 6 g) := rfl
  rw [hsq]
  calc Kg * (Real.sqrt (Work.Spaces.HkSq α 6 f) * Real.sqrt (Work.Spaces.HkSq α 6 g))
      = (Kg * Real.sqrt (Work.Spaces.HkSq α 6 f)) * Real.sqrt (Work.Spaces.HkSq α 6 g) := by
        ring
    _ ≤ (Λ * Real.sqrt (Work.Spaces.HkSq α 6 g)) * Real.sqrt (Work.Spaces.HkSq α 6 g) :=
        mul_le_mul_of_nonneg_right hΛ2 (Real.sqrt_nonneg _)
    _ = Λ * Real.sqrt (Work.Spaces.HkSq α 6 g) ^ 2 := by ring

/-- **Branch `A5a`** (`a1 = 0`, `b1 = 5`, `a = 0`): the middle `g`-factor carries the sup, the
two pure slots are Cauchy–Schwarz'ed. -/
theorem term_bound_A5a {α Kf Kg q Λ : ℝ} {f g : ℝ → ℝ → ℝ} {a b a1 b1 : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.HkMem α 6 f)
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (h : SupPkg α f g Kf Kg) (hKf0 : 0 ≤ Kf) (hKg0 : 0 ≤ Kg)
    (hΛ1 : Kf ≤ Λ)
    (hΛ2 : Kg * Work.Spaces.HkNorm α 6 f ≤ Λ * Work.Spaces.HkNorm α 6 g)
    (hq0 : 0 < q) (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (hab : a + b ≤ 6) (ha : a = 0) (ha1 : a1 = 0) (hb1 : b1 = 5) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
        * |Work.Spaces.mixed b1 a1 f p.1 p.2|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
        * |Work.Spaces.mixed b a g p.1 p.2|) pm ∧
      (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
        * |Work.Spaces.mixed b a g p.1 p.2| ∂pm)
        ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
  subst ha1
  subst ha
  subst hb1
  have hqη' : q ≤ Work.Spaces.eta := hqη rfl
  have hmid : b - 5 + 1 ≤ 4 := by omega
  have hsl1 : SlotW6 α q (Work.Spaces.DzIter 5 f) f :=
    slotW6_z α (q := q) hq0 hqη' f 5 (by norm_num)
  have hsl2 : SlotW6 α q (Work.Spaces.DzIter b g) g :=
    slotW6_z α (q := q) hq0 hqη' g b (by omega)
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * |Work.Spaces.mixed 5 0 f z θ|
        * |Work.Spaces.mixed (b - 5 + 1) (0 - 0) g z θ|
        * |Work.Spaces.mixed b 0 g z θ| ≤ Kg * (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) := by
    intro z θ hz hθ hθ2
    have hzI : z ∈ Work.Spaces.Iz := hz.le
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
    simp only [Work.Spaces.mixed_zero_right, Nat.sub_zero]
    have hG : |Work.Spaces.DzIter (b - 5 + 1) g z θ| ≤ Kg :=
      h.gpure (b - 5 + 1) hmid z θ hz hθ hθ2
    have hpair := pair_cross_le (α := α) (q := q) hzI hθI hsl1 hsl2
    calc canonW q z θ * |Work.Spaces.DzIter 5 f z θ|
          * |Work.Spaces.DzIter (b - 5 + 1) g z θ| * |Work.Spaces.DzIter b g z θ|
        = (canonW q z θ * |Work.Spaces.DzIter 5 f z θ| * |Work.Spaces.DzIter b g z θ|)
          * |Work.Spaces.DzIter (b - 5 + 1) g z θ| := by ring
      _ ≤ (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) * Kg :=
          mul_le_mul hpair hG (abs_nonneg _)
            (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = Kg * (Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) := by ring
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      canonW q p.1 p.2 * |Work.Spaces.mixed 5 0 f p.1 p.2|
        * |Work.Spaces.mixed (b - 5 + 1) (0 - 0) g p.1 p.2|
        * |Work.Spaces.mixed b 0 g p.1 p.2|) pm :=
    aesm_canonW_abs_mul (q := q) ((hfs.mixed 5 0).continuousOn)
      ((hgs.mixed (b - 5 + 1) (0 - 0)).continuousOn) ((hgs.mixed b 0).continuousOn)
  have hcross := hcross_sqrt (α := α) (Λ := Λ) (Kg := Kg) hΛ2
  refine ⟨?_, ?_⟩
  · exact (integrable_of_pointwise_sqrt (f := f) (g := g) hfs hgs hfm hgm hKg0
      (F := fun z θ => canonW q z θ * |Work.Spaces.mixed 5 0 f z θ|
        * |Work.Spaces.mixed (b - 5 + 1) (0 - 0) g z θ|
        * |Work.Spaces.mixed b 0 g z θ|) haesm
      (fun z θ hz hθ hθ2 => by
        rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
        exact hpt z θ hz hθ hθ2)).1
  · exact (integrable_of_pointwise_sqrt (f := f) (g := g) hfs hgs hfm hgm hKg0
      (F := fun z θ => canonW q z θ * |Work.Spaces.mixed 5 0 f z θ|
        * |Work.Spaces.mixed (b - 5 + 1) (0 - 0) g z θ|
        * |Work.Spaces.mixed b 0 g z θ|) haesm
      (fun z θ hz hθ hθ2 => by
        rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
        exact hpt z θ hz hθ hθ2)).2.trans hcross

/-- **Branch `A5b`** (`a1 = 0`, `b1 = 5`, `a = 1`, `b = 5`): the exceptional configuration, with
the pure top slot `D_z⁵f` on the `f`-side. -/
theorem term_bound_A5b {α Kf Kg q Λ : ℝ} {f g : ℝ → ℝ → ℝ} {a b a1 b1 : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.HkMem α 6 f)
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (h : SupPkg α f g Kf Kg) (hKf0 : 0 ≤ Kf) (hKg0 : 0 ≤ Kg)
    (hΛ1 : Kf ≤ Λ)
    (hΛ2 : Kg * Work.Spaces.HkNorm α 6 f ≤ Λ * Work.Spaces.HkNorm α 6 g)
    (hq0 : 0 < q) (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (hab : a + b ≤ 6) (ha : a = 1) (ha1 : a1 = 0) (hb1 : b1 = 5) (hb : b = 5)
    (hΛE1 : Real.sqrt (10 * excC11) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
      ≤ Λ) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
        * |Work.Spaces.mixed b1 a1 f p.1 p.2|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
        * |Work.Spaces.mixed b a g p.1 p.2|) pm ∧
      (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
        * |Work.Spaces.mixed b a g p.1 p.2| ∂pm)
        ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
  subst ha
  subst ha1
  subst hb1
  subst hb
  obtain ⟨hL2mem, hL2sq⟩ :=
    excC11_spec (α := α) (p := f) (qq := g) hα hα1 hfs hfm hgs hgm
  obtain ⟨hint, hbound⟩ := exc_pair_pm (α := α) (q := q) (C1 := excC11) (p := f) (qq := g)
    (g := g) (b := 1) (a := 1) (B := 5) (A := 1) hα hα1 excC11_pos.le hfs hfm hgs hgm hgs hgm
    (by norm_num) (by norm_num) hq0 hqγ hL2mem hL2sq
  have hgoal_int : MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
      * |Work.Spaces.DzIter 5 f p.1 p.2| * |Work.Spaces.mixed 1 1 g p.1 p.2|
      * |Work.Spaces.mixed 5 1 g p.1 p.2|) pm := hint
  have hgoal_bnd : |∫ p, canonW q p.1 p.2 * |Work.Spaces.DzIter 5 f p.1 p.2|
      * |Work.Spaces.mixed 1 1 g p.1 p.2| * |Work.Spaces.mixed 5 1 g p.1 p.2| ∂pm|
      ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
    refine le_trans hbound ?_
    calc Real.sqrt (10 * excC11) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
          * Work.Spaces.HkNorm α 6 g * Work.Spaces.HkNorm α 6 g
        = (Real.sqrt (10 * excC11) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f)
          * (Work.Spaces.HkNorm α 6 g * Work.Spaces.HkNorm α 6 g) := by ring
      _ ≤ Λ * (Work.Spaces.HkNorm α 6 g * Work.Spaces.HkNorm α 6 g) :=
          mul_le_mul_of_nonneg_right hΛE1
            (mul_nonneg (Work.Spaces.HkNorm_nonneg α 6 g) (Work.Spaces.HkNorm_nonneg α 6 g))
      _ = Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by ring
  have hint' : MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
      * |Work.Spaces.mixed 5 0 f p.1 p.2|
      * |Work.Spaces.mixed (5 - 5 + 1) (1 - 0) g p.1 p.2|
      * |Work.Spaces.mixed 5 1 g p.1 p.2|) pm := by
    convert hgoal_int using 1 with p
    simp only [Work.Spaces.mixed_zero_right, Nat.sub_self, Nat.sub_zero]
  refine ⟨hint', ?_⟩
  have hbnd' : (∫ p, canonW q p.1 p.2
      * |Work.Spaces.mixed 5 0 f p.1 p.2|
      * |Work.Spaces.mixed (5 - 5 + 1) (1 - 0) g p.1 p.2|
      * |Work.Spaces.mixed 5 1 g p.1 p.2| ∂pm)
      ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
    have hcongr : (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed 5 0 f p.1 p.2|
          * |Work.Spaces.mixed (5 - 5 + 1) (1 - 0) g p.1 p.2|
          * |Work.Spaces.mixed 5 1 g p.1 p.2| ∂pm)
        = ∫ p, canonW q p.1 p.2 * |Work.Spaces.DzIter 5 f p.1 p.2|
          * |Work.Spaces.mixed 1 1 g p.1 p.2| * |Work.Spaces.mixed 5 1 g p.1 p.2| ∂pm := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      simp only [Work.Spaces.mixed_zero_right, Nat.sub_self, Nat.sub_zero]
    rw [hcongr]
    exact le_trans (le_abs_self _) hgoal_bnd
  exact hbnd'

/-- **The `σ`-branch of case `C1`** (`a1 = a = 1`, `b1 = 0`, `b = 4`): the `f`-factor is
`D_θf`, whose `σ`-gain converts the weight `q` into the lighter `η`. -/
theorem term_bound_C1sigma {α Kf Kg q Λ : ℝ} {f g : ℝ → ℝ → ℝ} {a b a1 b1 : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.HkMem α 6 f)
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (h : SupPkg α f g Kf Kg) (hKf0 : 0 ≤ Kf) (hKg0 : 0 ≤ Kg)
    (hΛ1 : Kf ≤ Λ)
    (hΛ2 : Kg * Work.Spaces.HkNorm α 6 f ≤ Λ * Work.Spaces.HkNorm α 6 g)
    (hq0 : 0 < q) (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (hab : a + b ≤ 6) (ha : a = 1) (ha1 : a1 = 1) (hb1 : b1 = 0) (hb : b = 4) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
        * |Work.Spaces.mixed b1 a1 f p.1 p.2|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
        * |Work.Spaces.mixed b a g p.1 p.2|) pm ∧
      (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
        * |Work.Spaces.mixed b a g p.1 p.2| ∂pm)
        ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
  subst ha
  subst ha1
  subst hb1
  subst hb
  have hηγ : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    rw [Work.Spaces.gam, Work.Spaces.eta]; linarith [hα.le]
  have hsl1 : SlotW6 α Work.Spaces.eta (Work.Spaces.DzIter 5 g) g :=
    slotW6_z α (q := Work.Spaces.eta) Work.Spaces.eta_pos le_rfl g 5 (by norm_num)
  have hsl2 : SlotW6 α Work.Spaces.eta (Work.Spaces.mixed 4 1 g) g :=
    slotW6_mixed α (q := Work.Spaces.eta) Work.Spaces.eta_pos hηγ g 4 1
      (by norm_num) (by norm_num)
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * |Work.Spaces.mixed 0 1 f z θ|
        * |Work.Spaces.mixed (4 - 0 + 1) (1 - 1) g z θ|
        * |Work.Spaces.mixed 4 1 g z θ| ≤ Kf * Work.Spaces.HkIntegrand α 6 g z θ := by
    intro z θ hz hθ hθ2
    have hzI : z ∈ Work.Spaces.Iz := hz.le
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
    have hidx : (4 - 0 + 1 : ℕ) = 5 := by norm_num
    have hidx2 : (1 - 1 : ℕ) = 0 := by norm_num
    rw [hidx, hidx2, Work.Spaces.mixed_zero_right]
    have hDth : Work.Spaces.mixed 0 1 f z θ
        = Real.sin (2 * θ) * Work.Spaces.pth f z θ := rfl
    have hσ0 : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hσ1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hσt : Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-q)
        ≤ Real.sin (2 * θ) ^ (-Work.Spaces.eta) := by
      have h1 : Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-q)
          = Real.sin (2 * θ) ^ (1 - q) := by
        rw [show (1 : ℝ) - q = 1 + (-q) by ring, Real.rpow_add hσ0, Real.rpow_one]
      rw [h1]
      exact Real.rpow_le_rpow_of_exponent_ge hσ0 hσ1 (by
        have hγη : Work.Spaces.gam α ≤ 1 + Work.Spaces.eta := by
          rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
        linarith)
    have hpth : |Work.Spaces.pth f z θ| ≤ Kf := h.pthf z θ hz hθ hθ2
    have hstep1 : canonW q z θ * |Work.Spaces.mixed 0 1 f z θ|
        ≤ Kf * canonW Work.Spaces.eta z θ := by
      rw [hDth, abs_mul, abs_of_nonneg hσ0.le]
      simp only [canonW]
      calc (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-q)
            * (Real.sin (2 * θ) * |Work.Spaces.pth f z θ|)
          = (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-q))
              * |Work.Spaces.pth f z θ| := by ring
        _ ≤ (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
              * Kf := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hσt (sq_nonneg _)) hpth
              (abs_nonneg _) (by positivity)
        _ = Kf * ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)) := by
            ring
    have hpair := slotW6_pair_le (α := α) (q := Work.Spaces.eta) hzI hθI hsl1 hsl2
    calc canonW q z θ * |Work.Spaces.mixed 0 1 f z θ| * |Work.Spaces.DzIter 5 g z θ|
          * |Work.Spaces.mixed 4 1 g z θ|
        = (canonW q z θ * |Work.Spaces.mixed 0 1 f z θ|)
          * (|Work.Spaces.DzIter 5 g z θ| * |Work.Spaces.mixed 4 1 g z θ|) := by ring
      _ ≤ (Kf * canonW Work.Spaces.eta z θ)
          * (|Work.Spaces.DzIter 5 g z θ| * |Work.Spaces.mixed 4 1 g z θ|) :=
          mul_le_mul_of_nonneg_right hstep1 (by positivity)
      _ = Kf * (canonW Work.Spaces.eta z θ * |Work.Spaces.DzIter 5 g z θ|
            * |Work.Spaces.mixed 4 1 g z θ|) := by ring
      _ ≤ Kf * Work.Spaces.HkIntegrand α 6 g z θ :=
          mul_le_mul_of_nonneg_left hpair hKf0
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      canonW q p.1 p.2 * |Work.Spaces.mixed 0 1 f p.1 p.2|
        * |Work.Spaces.mixed (4 - 0 + 1) (1 - 1) g p.1 p.2|
        * |Work.Spaces.mixed 4 1 g p.1 p.2|) pm :=
    aesm_canonW_abs_mul (q := q) ((hfs.mixed 0 1).continuousOn)
      ((hgs.mixed (4 - 0 + 1) (1 - 1)).continuousOn) ((hgs.mixed 4 1).continuousOn)
  have hsq : Work.Spaces.HkSq α 6 g = (Work.Spaces.HkNorm α 6 g) ^ 2 :=
    (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 g)).symm
  refine ⟨?_, ?_⟩
  · exact (integrable_of_pointwise (g := g) hgs hgm hKf0
      (F := fun z θ => canonW q z θ * |Work.Spaces.mixed 0 1 f z θ|
        * |Work.Spaces.mixed (4 - 0 + 1) (1 - 1) g z θ|
        * |Work.Spaces.mixed 4 1 g z θ|) haesm
      (fun z θ hz hθ hθ2 => by
        rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
        exact hpt z θ hz hθ hθ2)).1
  · refine (integrable_of_pointwise (g := g) hgs hgm hKf0
      (F := fun z θ => canonW q z θ * |Work.Spaces.mixed 0 1 f z θ|
        * |Work.Spaces.mixed (4 - 0 + 1) (1 - 1) g z θ|
        * |Work.Spaces.mixed 4 1 g z θ|) haesm
      (fun z θ hz hθ hθ2 => by
        rw [abs_of_nonneg (canonW_mul_abs3_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ) _ _ _)]
        exact hpt z θ hz hθ hθ2)).2.trans ?_
    rw [hsq]
    exact mul_le_mul_of_nonneg_right hΛ1 (sq_nonneg _)

/-- **The exceptional branch of case `C1`** (`a1 = a = 1`, `b1 = 1`, `b = 5`): the pure top slot
`D_z⁵g` is paired with the mixed slot `D_zD_θf` of `f`. -/
theorem term_bound_C1E11 {α Kf Kg q Λ : ℝ} {f g : ℝ → ℝ → ℝ} {a b a1 b1 : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.HkMem α 6 f)
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (h : SupPkg α f g Kf Kg) (hKf0 : 0 ≤ Kf) (hKg0 : 0 ≤ Kg)
    (hΛ1 : Kf ≤ Λ)
    (hΛ2 : Kg * Work.Spaces.HkNorm α 6 f ≤ Λ * Work.Spaces.HkNorm α 6 g)
    (hq0 : 0 < q) (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (hab : a + b ≤ 6) (ha : a = 1) (ha1 : a1 = 1) (hb1 : b1 = 1) (hb : b = 5)
    (hΛE1 : Real.sqrt (10 * excC11) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
      ≤ Λ) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
        * |Work.Spaces.mixed b1 a1 f p.1 p.2|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
        * |Work.Spaces.mixed b a g p.1 p.2|) pm ∧
      (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
        * |Work.Spaces.mixed b a g p.1 p.2| ∂pm)
        ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
  subst ha
  subst ha1
  subst hb1
  subst hb
  obtain ⟨hL2mem, hL2sq⟩ :=
    excC11_spec (α := α) (p := g) (qq := f) hα hα1 hgs hgm hfs hfm
  obtain ⟨hint, hbound⟩ := exc_pair_pm (α := α) (q := q) (C1 := excC11) (p := g) (qq := f)
    (g := g) (b := 1) (a := 1) (B := 5) (A := 1) hα hα1 excC11_pos.le hgs hgm hfs hfm hgs hgm
    (by norm_num) (by norm_num) hq0 hqγ hL2mem hL2sq
  have hgoal_int : MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
      * |Work.Spaces.mixed 1 1 f p.1 p.2| * |Work.Spaces.DzIter 5 g p.1 p.2|
      * |Work.Spaces.mixed 5 1 g p.1 p.2|) pm :=
    hint.congr (Filter.Eventually.of_forall fun p => by ring)
  have hiff : (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed 1 1 f p.1 p.2|
        * |Work.Spaces.DzIter 5 g p.1 p.2| * |Work.Spaces.mixed 5 1 g p.1 p.2| ∂pm)
      = ∫ p, canonW q p.1 p.2 * |Work.Spaces.DzIter 5 g p.1 p.2|
        * |Work.Spaces.mixed 1 1 f p.1 p.2| * |Work.Spaces.mixed 5 1 g p.1 p.2| ∂pm := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    ring
  have hgoal_bnd : |∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed 1 1 f p.1 p.2|
      * |Work.Spaces.DzIter 5 g p.1 p.2| * |Work.Spaces.mixed 5 1 g p.1 p.2| ∂pm|
      ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
    rw [hiff]
    refine le_trans hbound ?_
    calc Real.sqrt (10 * excC11) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 g
          * Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 g
        = (Real.sqrt (10 * excC11) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f)
          * (Work.Spaces.HkNorm α 6 g * Work.Spaces.HkNorm α 6 g) := by ring
      _ ≤ Λ * (Work.Spaces.HkNorm α 6 g * Work.Spaces.HkNorm α 6 g) :=
          mul_le_mul_of_nonneg_right hΛE1
            (mul_nonneg (Work.Spaces.HkNorm_nonneg α 6 g) (Work.Spaces.HkNorm_nonneg α 6 g))
      _ = Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by ring
  have hint' : MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
      * |Work.Spaces.mixed 1 1 f p.1 p.2|
      * |Work.Spaces.mixed (5 - 1 + 1) (1 - 1) g p.1 p.2|
      * |Work.Spaces.mixed 5 1 g p.1 p.2|) pm := by
    convert hgoal_int using 1 with p
    simp only [Work.Spaces.mixed_zero_right, Nat.sub_self, Nat.sub_zero]
  refine ⟨hint', ?_⟩
  have hcongr : (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed 1 1 f p.1 p.2|
        * |Work.Spaces.mixed (5 - 1 + 1) (1 - 1) g p.1 p.2|
        * |Work.Spaces.mixed 5 1 g p.1 p.2| ∂pm)
      = ∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed 1 1 f p.1 p.2|
        * |Work.Spaces.DzIter 5 g p.1 p.2| * |Work.Spaces.mixed 5 1 g p.1 p.2| ∂pm := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [Work.Spaces.mixed_zero_right, Nat.sub_self, Nat.sub_zero]
  rw [hcongr]
  exact le_trans (le_abs_self _) hgoal_bnd

/-- **The exceptional branch of case `C1`** (`a1 = a = 2`, `b1 = 0`, `b = 4`): the pure top slot
`D_z⁵g` is paired with the mixed slot `D_θ²f` of `f`. -/
theorem term_bound_C1E02 {α Kf Kg q Λ : ℝ} {f g : ℝ → ℝ → ℝ} {a b a1 b1 : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.HkMem α 6 f)
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (h : SupPkg α f g Kf Kg) (hKf0 : 0 ≤ Kf) (hKg0 : 0 ≤ Kg)
    (hΛ1 : Kf ≤ Λ)
    (hΛ2 : Kg * Work.Spaces.HkNorm α 6 f ≤ Λ * Work.Spaces.HkNorm α 6 g)
    (hq0 : 0 < q) (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (hab : a + b ≤ 6) (ha : a = 2) (ha1 : a1 = 2) (hb1 : b1 = 0) (hb : b = 4)
    (hΛE2 : Real.sqrt (10 * excC02) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
      ≤ Λ) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
        * |Work.Spaces.mixed b1 a1 f p.1 p.2|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
        * |Work.Spaces.mixed b a g p.1 p.2|) pm ∧
      (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
        * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
        * |Work.Spaces.mixed b a g p.1 p.2| ∂pm)
        ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
  subst ha
  subst ha1
  subst hb1
  subst hb
  obtain ⟨hL2mem, hL2sq⟩ :=
    excC02_spec (α := α) (p := g) (qq := f) hα hα1 hgs hgm hfs hfm
  obtain ⟨hint, hbound⟩ := exc_pair_pm (α := α) (q := q) (C1 := excC02) (p := g) (qq := f)
    (g := g) (b := 0) (a := 2) (B := 4) (A := 2) hα hα1 excC02_pos.le hgs hgm hfs hfm hgs hgm
    (by norm_num) (by norm_num) hq0 hqγ hL2mem hL2sq
  have hgoal_int : MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
      * |Work.Spaces.mixed 0 2 f p.1 p.2| * |Work.Spaces.DzIter 5 g p.1 p.2|
      * |Work.Spaces.mixed 4 2 g p.1 p.2|) pm :=
    hint.congr (Filter.Eventually.of_forall fun p => by ring)
  have hiff : (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed 0 2 f p.1 p.2|
        * |Work.Spaces.DzIter 5 g p.1 p.2| * |Work.Spaces.mixed 4 2 g p.1 p.2| ∂pm)
      = ∫ p, canonW q p.1 p.2 * |Work.Spaces.DzIter 5 g p.1 p.2|
        * |Work.Spaces.mixed 0 2 f p.1 p.2| * |Work.Spaces.mixed 4 2 g p.1 p.2| ∂pm := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    ring
  have hgoal_bnd : |∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed 0 2 f p.1 p.2|
      * |Work.Spaces.DzIter 5 g p.1 p.2| * |Work.Spaces.mixed 4 2 g p.1 p.2| ∂pm|
      ≤ Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
    rw [hiff]
    refine le_trans hbound ?_
    calc Real.sqrt (10 * excC02) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 g
          * Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 g
        = (Real.sqrt (10 * excC02) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f)
          * (Work.Spaces.HkNorm α 6 g * Work.Spaces.HkNorm α 6 g) := by ring
      _ ≤ Λ * (Work.Spaces.HkNorm α 6 g * Work.Spaces.HkNorm α 6 g) :=
          mul_le_mul_of_nonneg_right hΛE2
            (mul_nonneg (Work.Spaces.HkNorm_nonneg α 6 g) (Work.Spaces.HkNorm_nonneg α 6 g))
      _ = Λ * (Work.Spaces.HkNorm α 6 g) ^ 2 := by ring
  have hint' : MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
      * |Work.Spaces.mixed 0 2 f p.1 p.2|
      * |Work.Spaces.mixed (4 - 0 + 1) (2 - 2) g p.1 p.2|
      * |Work.Spaces.mixed 4 2 g p.1 p.2|) pm := by
    convert hgoal_int using 1 with p
    simp only [Work.Spaces.mixed_zero_right, Nat.sub_self, Nat.sub_zero]
  refine ⟨hint', ?_⟩
  have hcongr : (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed 0 2 f p.1 p.2|
        * |Work.Spaces.mixed (4 - 0 + 1) (2 - 2) g p.1 p.2|
        * |Work.Spaces.mixed 4 2 g p.1 p.2| ∂pm)
      = ∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed 0 2 f p.1 p.2|
        * |Work.Spaces.DzIter 5 g p.1 p.2| * |Work.Spaces.mixed 4 2 g p.1 p.2| ∂pm := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [Work.Spaces.mixed_zero_right, Nat.sub_self, Nat.sub_zero]
  rw [hcongr]
  exact le_trans (le_abs_self _) hgoal_bnd

end Work.FTS.StrongPersist.N6Trans.SixAux
end
end
