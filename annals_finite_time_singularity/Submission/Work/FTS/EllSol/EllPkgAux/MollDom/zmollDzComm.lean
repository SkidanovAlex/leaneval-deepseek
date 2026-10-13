import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.KernelDefs
import Submission.Work.FTS.EllSol.EllPkgAux.KernelAux
import Submission.Work.FTS.EllSol.EllPkgAux.thMollSliceL2
import Submission.Work.FTS.EllSol.EllPkgAux.thMollTransfer2
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.MollDzAux.zmollKernel_hasDerivAt
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.sliceIbp
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.swapFubini
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.aeStronglyMeasurable_exp
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.thMoll_locInt
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.prod_integrable_of_slice_bound
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.integrableOn_exp_comp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

local notation "Iθ" => Work.Spaces.Iθ

/-! ## The engine -/

theorem zmoll_dz_comm {u : ℝ → ℝ → ℝ} {δ ε : ℝ} (hP : Params δ ε)
    (h0 : ∀ w : ℝ, u w 0 = 0) (hp : ∀ w : ℝ, u w (Real.pi / 2) = 0)
    (hcont : ∀ w : ℝ, 0 < w → ContinuousOn (fun s : ℝ => u w s) Iθ)
    (huc : ContinuousOn (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hder : ∀ w : ℝ, 0 < w → ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun w' : ℝ => u w' s) (Work.Spaces.pz u w s) w)
    (hderc : ContinuousOn (Function.uncurry (Work.Spaces.pz u)) Work.FTS.EllipticEst.Q0)
    {F : ℝ → ℝ} (hFint : ∀ a b : ℝ, 0 < a → a ≤ b → IntegrableOn F (Set.Icc a b))
    (hFb : ∀ w : ℝ, 0 < w → ∫ s in Iθ, |u w s| ≤ F w)
    (hFb' : ∀ w : ℝ, 0 < w → ∫ s in Iθ, |Work.Spaces.Dz u w s| ≤ F w)
    (hIntg' : ∀ w : ℝ, 0 < w → IntegrableOn (fun s : ℝ => Work.Spaces.Dz u w s) Iθ) :
    ∀ z : ℝ, 0 < z → ∀ θ ∈ Iθ,
      Work.Spaces.Dz (Work.FTS.EllSol.PkgK5.K5c.zmoll u δ ε) z θ
        = ∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t)
            * (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
                * Work.Spaces.Dz u (Real.exp t) s) := by
  obtain ⟨hε0, hε1, hδ0, hδ1⟩ := hP
  intro z hz θ hθ
  have hz0 : z ≠ 0 := ne_of_gt hz
  -- ## Step 0: the local integrability of the datum and the bound for the derivative kernel
  have hHli : LocallyIntegrable
      (fun t : ℝ => Work.FTS.EllSol.PkgK5.K5c.thMoll u ε (Real.exp t) θ) volume :=
    thMoll_locInt hε0 hε1 hθ h0 hp hcont huc hFint hFb
  obtain ⟨M, hM⟩ := Work.FTS.EllSol.EllPkgAux.exists_bound_deriv_sKer (ε := δ) hδ0
  -- ## Step 1: the derivative in `z` lands on the derived kernel
  have hDz : Work.Spaces.Dz (Work.FTS.EllSol.PkgK5.K5c.zmoll u δ ε) z θ
      = ∫ t : ℝ, deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (Real.log z - t)
          * Work.FTS.EllSol.PkgK5.K5c.thMoll u ε (Real.exp t) θ := by
    have hderiv := Work.FTS.EllSol.EllPkgAux.MollDzAux.zmollKernel_hasDerivAt
      (H := fun t : ℝ => Work.FTS.EllSol.PkgK5.K5c.thMoll u ε (Real.exp t) θ) hHli hδ0 hδ1 hM hz
    have hd : deriv (fun z' : ℝ => ∫ t : ℝ,
          Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z' - t)
            * Work.FTS.EllSol.PkgK5.K5c.thMoll u ε (Real.exp t) θ) z
        = z⁻¹ * ∫ t : ℝ, deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (Real.log z - t)
            * Work.FTS.EllSol.PkgK5.K5c.thMoll u ε (Real.exp t) θ := by
      simpa only [Work.FTS.EllSol.EllPkgAux.sKerd] using hderiv.deriv
    rw [Work.Spaces.Dz, Work.Spaces.pz]
    rw [show (fun z' : ℝ => Work.FTS.EllSol.PkgK5.K5c.zmoll u δ ε z' θ)
        = (fun z' : ℝ => ∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z' - t)
            * Work.FTS.EllSol.PkgK5.K5c.thMoll u ε (Real.exp t) θ) from rfl]
    rw [hd, ← mul_assoc, mul_inv_cancel₀ hz0, one_mul]
  -- ## Step 2: the fold of the angular mollification
  have hfold : ∀ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.thMoll u ε (Real.exp t) θ
      = ∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
          * u (Real.exp t) s := by
    intro t
    exact Work.FTS.EllSol.EllPkgAux.thMoll_fold hε0 hε1 (h0 (Real.exp t)) (hp (Real.exp t))
      (hcont (Real.exp t) (Real.exp_pos t))
      (by linarith [hθ.1, Real.pi_pos]) (by linarith [hθ.2])
  have hcongr : (∫ t : ℝ, deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (Real.log z - t)
        * Work.FTS.EllSol.PkgK5.K5c.thMoll u ε (Real.exp t) θ)
      = ∫ t : ℝ, deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (Real.log z - t)
          * (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
              * u (Real.exp t) s) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (Real.log z - t)
        * Work.FTS.EllSol.PkgK5.K5c.thMoll u ε (Real.exp t) θ
      = deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (Real.log z - t)
        * (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
            * u (Real.exp t) s)
    rw [hfold t]
  -- ## The kernel bound
  have hKpos : 0 ≤ (3 : ℝ) * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ := by
    have : 0 < ε * Work.FTS.EllSol.PkgK5.K5c.sMass :=
      mul_pos hε0 Work.FTS.EllSol.PkgK5.K5c.sMass_pos
    positivity
  have hKern : ∀ s : ℝ,
      |Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s|
        ≤ 3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ := by
    intro s
    have hb : ∀ x : ℝ, |Work.FTS.EllSol.PkgK5.K5c.sKer ε x|
        ≤ (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ := by
      intro x
      rw [abs_of_nonneg (Work.FTS.EllSol.PkgK5.K5c.sKer_nonneg hε0 x)]
      exact Work.FTS.EllSol.K5cAux.sKer_le_inv hε0 x
    have h1 : |Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s)
          - Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s)|
        ≤ |Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s)|
          + |Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s))
          (-(Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s)))
    have h2 : |(Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s)
          - Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s))
          - Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s - Real.pi)|
        ≤ |Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s)
            - Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s)|
          + |Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s - Real.pi)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s)
          - Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s))
          (-(Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s - Real.pi)))
    rw [Work.FTS.EllSol.EllPkgAux.Kern_apply]
    linarith [h1, h2, hb (θ - s), hb (θ + s), hb (θ + s - Real.pi)]
  have hcKern : Continuous (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.Kern
      (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s) := by
    have hker : Continuous (Work.FTS.EllSol.PkgK5.K5c.sKer ε) :=
      (Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).continuous
    have hc : Continuous (fun s : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s)
        - Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s)
        - Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s - Real.pi)) :=
      ((hker.comp (continuous_const.sub continuous_id)).sub
        (hker.comp (continuous_const.add continuous_id))).sub
        (hker.comp ((continuous_const.add continuous_id).sub continuous_const))
    exact hc
  have hSker0 : ∀ x : ℝ, 1 < |x| → Work.FTS.EllSol.PkgK5.K5c.sKer δ x = 0 := by
    intro x hx
    exact Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ0
      (le_trans (by linarith [hδ1]) (le_of_lt hx))
  have hSkerd0 : ∀ x : ℝ, 1 < |x| → deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) x = 0 := by
    intro x hx
    exact Work.FTS.EllSol.EllPkgAux.deriv_sKer_eq_zero_of_lt_abs (ε := δ) hδ0
      (lt_of_lt_of_le (by linarith [hδ1]) (le_of_lt hx))
  -- ## Step 3: the first Fubini
  have hmeasw : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ p.2
        * u (Real.exp p.1) p.2)
      (volume.prod (volume.restrict Iθ)) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => u (Real.exp p.1) p.2)
        (volume.prod (volume.restrict Iθ)) := aeStronglyMeasurable_exp huc
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.Kern
        (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ p.2)
        (volume.prod (volume.restrict Iθ)) :=
      (hcKern.comp continuous_snd).aestronglyMeasurable
    refine (h2.mul h1).congr (Filter.Eventually.of_forall fun p => ?_)
    rfl
  have hintK : ∀ t : ℝ, IntegrableOn
      (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
        * u (Real.exp t) s) Iθ := by
    intro t
    exact ((hcKern.continuousOn).mul (hcont (Real.exp t) (Real.exp_pos t))).integrableOn_compact
      isCompact_Icc
  have hbdK : ∀ t : ℝ, ∫ s in Iθ,
        |Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
          * u (Real.exp t) s|
      ≤ (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹) * F (Real.exp t) := by
    intro t
    have ht : 0 < Real.exp t := Real.exp_pos t
    have h1 : ∀ s : ℝ, |Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
          * u (Real.exp t) s|
        ≤ (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹) * |u (Real.exp t) s| := by
      intro s
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hKern s) (abs_nonneg _)
    have hint1 : IntegrableOn (fun s : ℝ => |Work.FTS.EllSol.EllPkgAux.Kern
        (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s * u (Real.exp t) s|) Iθ :=
      (hintK t).abs
    have hint2 : IntegrableOn
        (fun s : ℝ => (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹) * |u (Real.exp t) s|) Iθ :=
      ((hcont (Real.exp t) ht).abs.integrableOn_compact isCompact_Icc).const_mul _
    calc ∫ s in Iθ, |Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
          * u (Real.exp t) s|
        ≤ ∫ s in Iθ, (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹) * |u (Real.exp t) s| :=
          setIntegral_mono_on hint1 hint2 measurableSet_Icc (fun s _ => h1 s)
      _ = (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹) * ∫ s in Iθ, |u (Real.exp t) s| :=
          integral_const_mul _ _
      _ ≤ (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹) * F (Real.exp t) :=
          mul_le_mul_of_nonneg_left (hFb (Real.exp t) ht) hKpos
  have hint1 : Integrable
      (fun p : ℝ × ℝ => deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (Real.log z - p.1)
        * Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ p.2
        * u (Real.exp p.1) p.2)
      (volume.prod (volume.restrict Iθ)) := by
    have hmain := prod_integrable_of_slice_bound
      (k := fun x : ℝ => deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) x)
      (w := fun t s : ℝ => Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
        * u (Real.exp t) s)
      (Φ := fun t : ℝ => (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹) * F (Real.exp t))
      (M := M) (σ := Real.log z)
      (Work.FTS.EllSol.EllPkgAux.continuous_deriv_sKer δ).measurable
      (fun x => hM x) hSkerd0 hmeasw hintK hbdK
      ((integrableOn_exp_comp hFint (Real.log z - 1) (Real.log z + 1)).const_mul _)
    exact hmain.congr (Filter.Eventually.of_forall fun p => by ring)
  have hswap1 := swapFubini (k := fun x : ℝ => deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) x)
    (v := fun t s : ℝ => u (Real.exp t) s) (ε := ε) (θ := θ) (σ := Real.log z) hint1
  -- ## Step 4: the a.e. integration by parts in `t`
  have hibp : ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ t : ℝ, deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (Real.log z - t) * u (Real.exp t) s)
        = ∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t)
            * Work.Spaces.Dz u (Real.exp t) s := by
    intro s hs
    refine sliceIbp hδ0 hδ1 ?_ ?_
    · intro t
      have ht : 0 < Real.exp t := Real.exp_pos t
      have h1 : HasDerivAt (fun w : ℝ => u w s) (Work.Spaces.pz u (Real.exp t) s) (Real.exp t) :=
        hder (Real.exp t) ht s hs
      have h2 : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
      have h3 := h1.comp t h2
      refine h3.congr_deriv ?_
      show Work.Spaces.pz u (Real.exp t) s * Real.exp t = Work.Spaces.Dz u (Real.exp t) s
      rw [Work.Spaces.Dz]; ring
    · have hg : Continuous (fun t : ℝ => (Real.exp t, s)) :=
        Real.continuous_exp.prodMk continuous_const
      have hmem : ∀ t : ℝ, (Real.exp t, s) ∈ Work.FTS.EllipticEst.Q0 :=
        fun t => ⟨Real.exp_pos t, hs⟩
      have hcomp := ContinuousOn.comp_continuous
        (f := fun t : ℝ => (Real.exp t, s)) hderc hg hmem
      have hc : Continuous (fun t : ℝ => Work.Spaces.pz u (Real.exp t) s) := hcomp
      have hmul : Continuous (fun t : ℝ => Real.exp t * Work.Spaces.pz u (Real.exp t) s) :=
        Real.continuous_exp.mul hc
      simpa only [Work.Spaces.Dz] using hmul
  have hagree : (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
        * (∫ t : ℝ, deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (Real.log z - t) * u (Real.exp t) s))
      = ∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
          * (∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t)
              * Work.Spaces.Dz u (Real.exp t) s) := by
    refine setIntegral_congr_ae (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc) ?_
    have hnull : ∀ᵐ s ∂(volume : Measure ℝ),
        s ∈ Iθ → s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      rw [MeasureTheory.ae_iff]
      have hsub : {a : ℝ | ¬(a ∈ Iθ → a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))} ⊆
          ({0, Real.pi / 2} : Set ℝ) := by
        intro s hs
        simp only [Set.mem_setOf_eq, not_imp] at hs
        obtain ⟨hs1, hs2⟩ := hs
        rw [Work.Spaces.Iθ, Set.mem_Icc] at hs1
        rw [Set.mem_Ioo] at hs2
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases lt_or_ge (0 : ℝ) s with h | h
        · right
          have hle : Real.pi / 2 ≤ s := by
            by_contra hc
            exact hs2 ⟨h, lt_of_not_ge hc⟩
          exact le_antisymm hs1.2 hle
        · left
          exact le_antisymm h hs1.1
      have hzero : (volume : Measure ℝ) ({0, Real.pi / 2} : Set ℝ) = 0 := by
        rw [show ({0, Real.pi / 2} : Set ℝ) = {0} ∪ {Real.pi / 2} by
          ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
        exact measure_union_null Real.volume_singleton Real.volume_singleton
      exact measure_mono_null hsub hzero
    filter_upwards [hnull] with s hs
    intro hsIθ
    exact congrArg (fun x => Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε)
      θ s * x) (hibp s (hs hsIθ))
  -- ## Step 5: the second Fubini
  have hmeasw2 : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ p.2
        * Work.Spaces.Dz u (Real.exp p.1) p.2)
      (volume.prod (volume.restrict Iθ)) := by
    have h1 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.pz u (Real.exp p.1) p.2)
        (volume.prod (volume.restrict Iθ)) := aeStronglyMeasurable_exp hderc
    have hexp : AEStronglyMeasurable (fun p : ℝ × ℝ => Real.exp p.1)
        (volume.prod (volume.restrict Iθ)) :=
      (Real.measurable_exp.comp measurable_fst).aestronglyMeasurable
    have h3 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.Dz u (Real.exp p.1) p.2)
        (volume.prod (volume.restrict Iθ)) := by
      refine (hexp.mul h1).congr (Filter.Eventually.of_forall fun p => ?_)
      show Real.exp p.1 * Work.Spaces.pz u (Real.exp p.1) p.2
        = Work.Spaces.Dz u (Real.exp p.1) p.2
      rw [Work.Spaces.Dz]
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.Kern
        (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ p.2)
        (volume.prod (volume.restrict Iθ)) :=
      (hcKern.comp continuous_snd).aestronglyMeasurable
    refine (h2.mul h3).congr (Filter.Eventually.of_forall fun p => ?_)
    rfl
  have hintK2 : ∀ t : ℝ, IntegrableOn
      (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
        * Work.Spaces.Dz u (Real.exp t) s) Iθ := by
    intro t
    have h := (hIntg' (Real.exp t) (Real.exp_pos t)).mul_continuousOn hcKern.continuousOn
      isCompact_Icc
    refine h.congr_fun ?_ measurableSet_Icc
    intro s _
    ring
  have hbdK2 : ∀ t : ℝ, ∫ s in Iθ,
        |Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
          * Work.Spaces.Dz u (Real.exp t) s|
      ≤ (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹) * F (Real.exp t) := by
    intro t
    have ht : 0 < Real.exp t := Real.exp_pos t
    have h1 : ∀ s : ℝ, |Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
          * Work.Spaces.Dz u (Real.exp t) s|
        ≤ (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹) * |Work.Spaces.Dz u (Real.exp t) s| := by
      intro s
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hKern s) (abs_nonneg _)
    have hint1 : IntegrableOn (fun s : ℝ => |Work.FTS.EllSol.EllPkgAux.Kern
        (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s * Work.Spaces.Dz u (Real.exp t) s|) Iθ :=
      (hintK2 t).abs
    have hint2 : IntegrableOn
        (fun s : ℝ => (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹)
          * |Work.Spaces.Dz u (Real.exp t) s|) Iθ :=
      ((hIntg' (Real.exp t) ht).abs).const_mul _
    calc ∫ s in Iθ, |Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
          * Work.Spaces.Dz u (Real.exp t) s|
        ≤ ∫ s in Iθ, (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹)
            * |Work.Spaces.Dz u (Real.exp t) s| :=
          setIntegral_mono_on hint1 hint2 measurableSet_Icc (fun s _ => h1 s)
      _ = (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹)
            * ∫ s in Iθ, |Work.Spaces.Dz u (Real.exp t) s| := integral_const_mul _ _
      _ ≤ (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹) * F (Real.exp t) :=
          mul_le_mul_of_nonneg_left (hFb' (Real.exp t) ht) hKpos
  have hint2 : Integrable
      (fun p : ℝ × ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - p.1)
        * Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ p.2
        * Work.Spaces.Dz u (Real.exp p.1) p.2)
      (volume.prod (volume.restrict Iθ)) := by
    have hmain := prod_integrable_of_slice_bound
      (k := fun x : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ x)
      (w := fun t s : ℝ => Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
        * Work.Spaces.Dz u (Real.exp t) s)
      (Φ := fun t : ℝ => (3 * (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹) * F (Real.exp t))
      (M := (δ * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹) (σ := Real.log z)
      ((Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 1)).continuous.measurable)
      (fun x => by
        rw [abs_of_nonneg (Work.FTS.EllSol.PkgK5.K5c.sKer_nonneg hδ0 x)]
        exact Work.FTS.EllSol.K5cAux.sKer_le_inv hδ0 x)
      hSker0 hmeasw2 hintK2 hbdK2
      ((integrableOn_exp_comp hFint (Real.log z - 1) (Real.log z + 1)).const_mul _)
    exact hmain.congr (Filter.Eventually.of_forall fun p => by ring)
  have hswap2 := swapFubini (k := fun x : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ x)
    (v := fun t s : ℝ => Work.Spaces.Dz u (Real.exp t) s) (ε := ε) (θ := θ)
    (σ := Real.log z) hint2
  -- ## Assembly
  calc Work.Spaces.Dz (Work.FTS.EllSol.PkgK5.K5c.zmoll u δ ε) z θ
      = ∫ t : ℝ, deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (Real.log z - t)
          * Work.FTS.EllSol.PkgK5.K5c.thMoll u ε (Real.exp t) θ := hDz
    _ = ∫ t : ℝ, deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (Real.log z - t)
          * (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
              * u (Real.exp t) s) := hcongr
    _ = ∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
          * (∫ t : ℝ, deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (Real.log z - t)
              * u (Real.exp t) s) := hswap1
    _ = ∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
          * (∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t)
              * Work.Spaces.Dz u (Real.exp t) s) := hagree
    _ = ∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t)
          * (∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s
              * Work.Spaces.Dz u (Real.exp t) s) := hswap2.symm

end Work.FTS.EllSol.EllPkgAux.MollDom
