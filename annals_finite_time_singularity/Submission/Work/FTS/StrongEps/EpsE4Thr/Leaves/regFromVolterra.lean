import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.RingTheory.Finiteness.Prod
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
import Submission.Work.FTS.StrongPersist.N6Trans.HonestHardSlotLem
import Submission.Work.FTS.StrongPersist.SP6.F0SixYblk
import Submission.Work.FTS_RegExport.RXA1.abs_mixed_le_HkNorm_C4_proved
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.EpsEngine.IterContMeas =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps
open Work.FTS.StrongEps.EpsLocalPStar
open Classical

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The open quadrant `(0,∞) × (0,π/2)`, in the shape in which the Carathéodory lemma states it. -/
private abbrev Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

/-! ## The three steps of the induction -/

/-- **Carathéodory step**: continuity in the fake time of the level-`n` curve yields the joint
measurability of its `F`-image on the horizon. -/
theorem aesm_of_contIter {α δ : ℝ} {F : Fn → Fn} {h₀ : Fn} {P : Fn → Prop} (n : ℕ)
    (hcontP : ∀ u : Fn, P u → ContinuousOn (fun q : ℝ × ℝ => F u q.1 q.2) Qd)
    (hzeroP : ∀ u : Fn, P u → ∀ q : ℝ × ℝ, q ∉ Qd → F u q.1 q.2 = 0)
    (hPn : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → P (slice (iter F h₀ n) τ))
    (hcont : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ContinuousOn (fun s : ℝ => F (slice (iter F h₀ n) s) z θ) (Set.Icc 0 δ)) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => F (slice (iter F h₀ n) p.1) p.2.1 p.2.2)
      (((volume : Measure ℝ).restrict (Set.Icc 0 δ)).prod volume) := by
  refine aesm_uncurry_restricted (A := Set.Icc 0 δ)
    (g := fun s z θ => F (slice (iter F h₀ n) s) z θ) measurableSet_Icc ?_ ?_ ?_
  · intro s hs
    exact hcontP _ (hPn s hs)
  · intro s hs q hq
    exact hzeroP _ (hPn s hs) q hq
  · intro q
    by_cases hq : q ∈ Qd
    · exact (hcont q.1 q.2 hq.1 hq.2.1 hq.2.2).aestronglyMeasurable measurableSet_Icc
    · exact (continuousOn_const.congr
        (fun s hs => hzeroP _ (hPn s hs) q hq)).aestronglyMeasurable measurableSet_Icc

/-- **Minkowski step** (the time-Lipschitz bound of the curves): the increment of the `(n+1)`-st
Picard iterate over `(a,b] ⊆ [0,δ]` is the parametric integral of the level-`n` curve, whose
weighted `L²`-size is bounded by `L` a.e.; `EpsSq_intervalIntegral_le_gen` then gives the bound
`(b−a)²·L`. -/
theorem EpsSq_integral_iter_le {α L δ : ℝ} {F : Fn → Fn} {h₀ : Fn} {P : Fn → Prop} (n : ℕ)
    (hL : 0 ≤ L)
    (hPn : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → P (slice (iter F h₀ n) τ))
    (hbd : ∀ u : Fn, P u → EpsMem α (F u) ∧ EpsSq α (F u) ≤ L)
    (haesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => F (slice (iter F h₀ n) p.1) p.2.1 p.2.2)
      (((volume : Measure ℝ).restrict (Set.Icc 0 δ)).prod volume)) :
    ∀ a ∈ Set.Icc 0 δ, ∀ b ∈ Set.Icc 0 δ, a ≤ b →
      EpsSq α (fun z' θ' => ∫ t in a..b, F (slice (iter F h₀ n) t) z' θ')
        ≤ (b - a) * ((b - a) * L) := by
  intro a ha b hb hab
  have hm0 : AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => F (slice (iter F h₀ n) p.1) p.2.1 p.2.2)
      (((volume : Measure ℝ).restrict (Set.uIoc a b)).prod volume) := by
    refine haesm.mono_measure ?_
    refine Measure.prod_mono ?_ le_rfl
    refine Measure.restrict_mono ?_ le_rfl
    rw [Set.uIoc_of_le hab]
    exact fun x hx => ⟨le_trans ha.1 (le_of_lt hx.1), le_trans hx.2 hb.2⟩
  have hm := aesm_weighted_prod_restricted (α := α)
    (Φ := fun t => F (slice (iter F h₀ n) t)) hm0
  have hbdd : ∀ᵐ t ∂(volume.restrict (Set.uIoc a b)),
      epsL2 α (F (slice (iter F h₀ n) t)) ≤ ENNReal.ofReal L := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc ?_
    intro t ht
    have htIcc : t ∈ Set.Icc 0 δ := by
      rw [Set.uIoc_of_le hab] at ht
      exact ⟨le_trans ha.1 (le_of_lt ht.1), le_trans ht.2 hb.2⟩
    exact epsL2_le_ofReal_of_mem (hbd _ (hPn t htIcc)).1 (hbd _ (hPn t htIcc)).2
  exact (EpsSq_intervalIntegral_le_gen hab hL hm hbdd).2

/-- **One Picard step**: from the continuity in the fake time at level `n` (and the class data at
levels `n` and `n+1`) one gets both conclusions at level `n+1`. -/
theorem cont_iter_succ {α Cpt L δ : ℝ} {F : Fn → Fn} {h₀ : Fn} {P : Fn → Prop} (n : ℕ)
    (hL : 0 ≤ L) (hCpt : 0 ≤ Cpt)
    (hcontP : ∀ u : Fn, P u → ContinuousOn (fun q : ℝ × ℝ => F u q.1 q.2) Qd)
    (hzeroP : ∀ u : Fn, P u → ∀ q : ℝ × ℝ, q ∉ Qd → F u q.1 q.2 = 0)
    (hbd : ∀ u : Fn, P u → EpsMem α (F u) ∧ EpsSq α (F u) ≤ L)
    (hpt : ∀ u v : Fn, P u → P v → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F u z θ - F v z θ| ≤ Cpt * Real.sqrt (EpsSq α (fun z θ => u z θ - v z θ)))
    (hPn : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → P (slice (iter F h₀ n) τ))
    (hPn1 : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → P (slice (iter F h₀ (n + 1)) τ))
    (hcont_n : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ContinuousOn (fun s : ℝ => F (slice (iter F h₀ n) s) z θ) (Set.Icc 0 δ)) :
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ContinuousOn (fun s : ℝ => F (slice (iter F h₀ (n + 1)) s) z θ) (Set.Icc 0 δ)) ∧
    AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => F (slice (iter F h₀ (n + 1)) p.1) p.2.1 p.2.2)
      (((volume : Measure ℝ).restrict (Set.Icc 0 δ)).prod volume) := by
  have haesm_n := aesm_of_contIter (α := α) (δ := δ) (F := F) (h₀ := h₀) (P := P) n
    hcontP hzeroP hPn hcont_n
  have hbound := EpsSq_integral_iter_le (α := α) (L := L) (δ := δ) (F := F) (h₀ := h₀) (P := P)
    n hL hPn hbd haesm_n
  have hcont_succ : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ContinuousOn (fun s : ℝ => F (slice (iter F h₀ (n + 1)) s) z θ) (Set.Icc 0 δ) := by
    intro z θ hz hθ0 hθ1
    -- the `(n+1)`-st iterate is `h₀` plus the parametric integral of the level-`n` curve
    have hiter : ∀ τ z' θ' : ℝ, slice (iter F h₀ (n + 1)) τ z' θ'
        = h₀ z' θ' + ∫ t in (0 : ℝ)..τ, F (slice (iter F h₀ n) t) z' θ' := by
      intro τ z' θ'
      rw [iter_succ F h₀ n]
      simp only [Work.FTS.Galerkin.slice_apply]
    -- the Lipschitz bound for the `(n+1)`-st curve
    have key : ∀ a ∈ Set.Icc 0 δ, ∀ b ∈ Set.Icc 0 δ, a ≤ b →
        dist (F (slice (iter F h₀ (n + 1)) a) z θ)
             (F (slice (iter F h₀ (n + 1)) b) z θ)
          ≤ (Cpt * Real.sqrt L) * dist a b := by
      intro a ha b hb hab
      have hdiff : ∀ᵐ p ∂DomM,
          (fun z' θ' => slice (iter F h₀ (n + 1)) a z' θ'
            - slice (iter F h₀ (n + 1)) b z' θ') p.1 p.2
            = (fun z' θ' => -∫ t in a..b, F (slice (iter F h₀ n) t) z' θ') p.1 p.2 := by
        filter_upwards [ae_open_DomM] with p hp
        obtain ⟨hz', hθ'0, hθ'1⟩ := hp
        have hc : ContinuousOn (fun t : ℝ => F (slice (iter F h₀ n) t) p.1 p.2)
            (Set.Icc 0 δ) := hcont_n p.1 p.2 hz' hθ'0 hθ'1
        rw [hiter a p.1 p.2, hiter b p.1 p.2]
        have h1 : IntervalIntegrable (fun t : ℝ => F (slice (iter F h₀ n) t) p.1 p.2) volume 0 a :=
          ContinuousOn.intervalIntegrable_of_Icc ha.1 (hc.mono (Set.Icc_subset_Icc_right ha.2))
        have h2 : IntervalIntegrable (fun t : ℝ => F (slice (iter F h₀ n) t) p.1 p.2) volume a b :=
          ContinuousOn.intervalIntegrable_of_Icc hab
            (hc.mono (fun x hx => ⟨le_trans ha.1 hx.1, le_trans hx.2 hb.2⟩))
        have hadj := (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
        rw [hadj]
        ring
      have heps : EpsSq α (fun z' θ' => slice (iter F h₀ (n + 1)) a z' θ'
            - slice (iter F h₀ (n + 1)) b z' θ') ≤ (b - a) * ((b - a) * L) := by
        have h0 := EpsSq_congr_ae (α := α)
          (f := fun z' θ' => slice (iter F h₀ (n + 1)) a z' θ'
            - slice (iter F h₀ (n + 1)) b z' θ')
          (g := fun z' θ' => -∫ t in a..b, F (slice (iter F h₀ n) t) z' θ') hdiff
        rw [h0, EpsSq_neg2]
        exact hbound a ha b hb hab
      have hmain := hpt (slice (iter F h₀ (n + 1)) a) (slice (iter F h₀ (n + 1)) b)
        (hPn1 a ha) (hPn1 b hb) z θ hz hθ0 hθ1
      calc dist (F (slice (iter F h₀ (n + 1)) a) z θ)
            (F (slice (iter F h₀ (n + 1)) b) z θ)
          = |F (slice (iter F h₀ (n + 1)) a) z θ
              - F (slice (iter F h₀ (n + 1)) b) z θ| := Real.dist_eq _ _
        _ ≤ Cpt * Real.sqrt (EpsSq α (fun z' θ' => slice (iter F h₀ (n + 1)) a z' θ'
              - slice (iter F h₀ (n + 1)) b z' θ')) := hmain
        _ ≤ Cpt * Real.sqrt ((b - a) * ((b - a) * L)) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt heps) hCpt
        _ = (Cpt * Real.sqrt L) * (b - a) := by
            rw [show (b - a) * ((b - a) * L) = (b - a) ^ 2 * L by ring,
              Real.sqrt_mul (sq_nonneg (b - a)), Real.sqrt_sq_eq_abs,
              abs_of_nonneg (sub_nonneg.mpr hab)]
            ring
        _ = (Cpt * Real.sqrt L) * dist a b := by
            rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab)]
            ring
    have hlip : LipschitzOnWith ⟨Cpt * Real.sqrt L, mul_nonneg hCpt (Real.sqrt_nonneg L)⟩
        (fun s : ℝ => F (slice (iter F h₀ (n + 1)) s) z θ) (Set.Icc 0 δ) :=
      LipschitzOnWith.of_dist_le_mul (fun s hs s₀ hs₀ => by
        rcases le_total s₀ s with hle | hle
        · rw [dist_comm (F (slice (iter F h₀ (n + 1)) s) z θ)
              (F (slice (iter F h₀ (n + 1)) s₀) z θ), dist_comm s s₀]
          exact key s₀ hs₀ s hs hle
        · exact key s hs s₀ hs₀ hle)
    exact hlip.continuousOn
  exact ⟨hcont_succ, aesm_of_contIter (α := α) (δ := δ) (F := F) (h₀ := h₀) (P := P) (n + 1)
    hcontP hzeroP hPn1 hcont_succ⟩

/-! ## The main theorems -/

/-- **Continuity in the fake time and joint measurability of the Picard curves, from the class
data** (all iterate levels).  See the module docstring for the induction and for why the measure is
horizon-restricted. -/
theorem iter_cont_meas {α Cpt L δ : ℝ} {F : Fn → Fn} {h₀ : Fn} {P : Fn → Prop}
    (hδ : 0 < δ) (hL : 0 ≤ L) (hCpt : 0 ≤ Cpt)
    (hP : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → P (slice (iter F h₀ n) τ))
    (hcontP : ∀ u : Fn, P u → ContinuousOn (fun q : ℝ × ℝ => F u q.1 q.2) Qd)
    (hzeroP : ∀ u : Fn, P u → ∀ q : ℝ × ℝ, q ∉ Qd → F u q.1 q.2 = 0)
    (hbd : ∀ u : Fn, P u → EpsMem α (F u) ∧ EpsSq α (F u) ≤ L)
    (hpt : ∀ u v : Fn, P u → P v → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F u z θ - F v z θ| ≤ Cpt * Real.sqrt (EpsSq α (fun z θ => u z θ - v z θ))) :
    (∀ n : ℕ, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ContinuousOn (fun s : ℝ => F (slice (iter F h₀ n) s) z θ) (Set.Icc 0 δ)) ∧
    (∀ n : ℕ, AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => F (slice (iter F h₀ n) p.1) p.2.1 p.2.2)
      (((volume : Measure ℝ).restrict (Set.Icc 0 δ)).prod volume)) := by
  have hcontAll : ∀ n : ℕ, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ContinuousOn (fun s : ℝ => F (slice (iter F h₀ n) s) z θ) (Set.Icc 0 δ) := by
    intro n
    induction n with
    | zero =>
      intro z θ _ _ _
      have hfun : (fun s : ℝ => F (slice (iter F h₀ 0) s) z θ) = fun _ : ℝ => F h₀ z θ := by
        funext s; rfl
      rw [hfun]; exact continuousOn_const
    | succ n ih =>
      exact (cont_iter_succ (δ := δ) (F := F) (h₀ := h₀) (P := P) n hL hCpt hcontP hzeroP
        hbd hpt (hP n) (hP (n + 1)) ih).1
  exact ⟨hcontAll, fun n => aesm_of_contIter (α := α) (δ := δ) (F := F) (h₀ := h₀) (P := P) n
    hcontP hzeroP (hP n) (hcontAll n)⟩

/-- **The prefix form** (the lead's ruling on finding (XXIII)): the class hypothesis is needed only
up to the level `N`, and the conclusion is drawn only up to `N`.  This is what the *inductive*
production of `hkeepIter` needs (`EpsEngine/SmoothOpenIter.lean`): at level `n` one only knows the
class data of the levels `≤ n`. -/
theorem iter_cont_meas_prefix {α Cpt L δ : ℝ} {F : Fn → Fn} {h₀ : Fn} {P : Fn → Prop} (N : ℕ)
    (hδ : 0 < δ) (hL : 0 ≤ L) (hCpt : 0 ≤ Cpt)
    (hP : ∀ n : ℕ, n ≤ N → ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → P (slice (iter F h₀ n) τ))
    (hcontP : ∀ u : Fn, P u → ContinuousOn (fun q : ℝ × ℝ => F u q.1 q.2) Qd)
    (hzeroP : ∀ u : Fn, P u → ∀ q : ℝ × ℝ, q ∉ Qd → F u q.1 q.2 = 0)
    (hbd : ∀ u : Fn, P u → EpsMem α (F u) ∧ EpsSq α (F u) ≤ L)
    (hpt : ∀ u v : Fn, P u → P v → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F u z θ - F v z θ| ≤ Cpt * Real.sqrt (EpsSq α (fun z θ => u z θ - v z θ))) :
    (∀ n : ℕ, n ≤ N → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ContinuousOn (fun s : ℝ => F (slice (iter F h₀ n) s) z θ) (Set.Icc 0 δ)) ∧
    (∀ n : ℕ, n ≤ N → AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => F (slice (iter F h₀ n) p.1) p.2.1 p.2.2)
      (((volume : Measure ℝ).restrict (Set.Icc 0 δ)).prod volume)) := by
  have hcontAll : ∀ n : ℕ, n ≤ N → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ContinuousOn (fun s : ℝ => F (slice (iter F h₀ n) s) z θ) (Set.Icc 0 δ) := by
    intro n hn
    induction n with
    | zero =>
      intro z θ _ _ _
      have hfun : (fun s : ℝ => F (slice (iter F h₀ 0) s) z θ) = fun _ : ℝ => F h₀ z θ := by
        funext s; rfl
      rw [hfun]; exact continuousOn_const
    | succ k ih =>
      exact (cont_iter_succ (δ := δ) (F := F) (h₀ := h₀) (P := P) k hL hCpt hcontP hzeroP
        hbd hpt (hP k (by omega)) (hP (k + 1) hn) (ih (by omega))).1
  exact ⟨hcontAll, fun n hn => aesm_of_contIter (α := α) (δ := δ) (F := F) (h₀ := h₀) (P := P) n
    hcontP hzeroP (hP n hn) (hcontAll n hn)⟩

end Work.FTS.EpsEngine

/-! ## Measure bookkeeping: from the horizon `Icc 0 δ` to the integration interval `(0,τ]` -/

namespace Work.FTS.EpsEngine

/-- The fake-time measures of the shrinking intervals `(0,τ]`, `τ ∈ [0,δ]`, are subordinate to the
horizon measure on `[0,δ]`. -/
theorem restrict_uIoc_le_Icc {δ τ : ℝ} (hτ : τ ∈ Set.Icc 0 δ) :
    (volume.restrict (Set.uIoc 0 τ)) ≤ (volume.restrict (Set.Icc 0 δ)) := by
  refine Measure.restrict_mono (s := Set.uIoc 0 τ) (s' := Set.Icc 0 δ) ?_ le_rfl
  rw [Set.uIoc_of_le hτ.1]
  exact fun x hx => ⟨le_of_lt hx.1, le_trans hx.2 hτ.2⟩

/-- An a.e.-strongly-measurable family on the horizon is a.e.-strongly measurable for the
integration measure of any `(0,τ] ⊆ [0,δ]`. -/
theorem aesm_uIoc_of_restrict {δ τ : ℝ} (hτ : τ ∈ Set.Icc 0 δ) {Φ : ℝ → Fn}
    (h : AEStronglyMeasurable (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2)
      (((volume : Measure ℝ).restrict (Set.Icc 0 δ)).prod (volume : Measure (ℝ × ℝ)))) :
    AEStronglyMeasurable (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2)
      (((volume : Measure ℝ).restrict (Set.uIoc 0 τ)).prod (volume : Measure (ℝ × ℝ))) :=
  h.mono_measure (Measure.prod_mono (restrict_uIoc_le_Icc hτ) le_rfl)

/-- The weighted version of `aesm_uIoc_of_restrict` — the form in which the Minkowski bound
`EpsSq_intervalIntegral_le_gen` consumes the joint measurability. -/
theorem aesm_weighted_uIoc_of_restrict {α δ τ : ℝ} (hτ : τ ∈ Set.Icc 0 δ) {Φ : ℝ → Fn}
    (h : AEStronglyMeasurable (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2)
      (((volume : Measure ℝ).restrict (Set.Icc 0 δ)).prod (volume : Measure (ℝ × ℝ)))) :
    AEStronglyMeasurable (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2 * epsW α p.2.1 p.2.2)
      (((volume : Measure ℝ).restrict (Set.uIoc 0 τ)).prod DomM) :=
  aesm_weighted_prod_restricted (aesm_uIoc_of_restrict hτ h)

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsConvSubseq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

theorem EpsConvSubseq {α B : ℝ} (hα : 0 < α) {G : ℕ → Work.FTS.Galerkin.Fn}
    (hsm : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry (G n))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 6 (G n) ≤ B) :
    ∃ (φ : ℕ → ℕ) (f : Work.FTS.Galerkin.Fn), StrictMono φ ∧
      Work.FTS.StrongEps.ConvLocUnifH6 α B (fun n => G (φ n)) f := by
  classical
  -- the `C⁴`-extraction, with the slot convergence at levels `≤ 4`
  obtain ⟨φ, hφ, f, hconv0, hf4, hconv4⟩ :=
    LocUnif.exists_subseq_deriv4_of_uniform_H6 hα hsm hmem hb
  -- the a.e. level-`5` extraction, needed for the energy bound
  obtain ⟨ψ, hψ, hconv5⟩ :=
    LocUnif.exists_subseq_deriv5_ae hα hφ hsm hmem hb hconv0 hconv4 hf4
  let Φ : ℕ → ℕ := fun n => φ (ψ n)
  have hΦmono : StrictMono Φ := fun a b hab => hφ (hψ hab)
  -- the a.e. level-`5` convergence along the composed subsequence, in the quantifier order that
  -- `LocUnif.HkSq_le` consumes
  have hconv5' : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))),
      ∀ (j i : ℕ), j + i = 5 →
        Filter.Tendsto (fun n => Work.Spaces.mixed j i (G (Φ n)) p.1 p.2) Filter.atTop
          (nhds (Work.Spaces.mixed j i f p.1 p.2)) := by
    have hfin : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))),
        ∀ t : Fin 6, Filter.Tendsto
          (fun n => Work.Spaces.mixed (5 - (t : ℕ)) (t : ℕ) (G (Φ n)) p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.mixed (5 - (t : ℕ)) (t : ℕ) f p.1 p.2)) := by
      rw [Filter.eventually_all]
      intro t
      have h := hconv5 (5 - (t : ℕ)) (t : ℕ) (by have := t.isLt; omega)
      simpa only [Φ] using h
    filter_upwards [hfin] with p hp j i hji
    have hi : i < 6 := by omega
    have hj : j = 5 - i := by omega
    subst hj
    exact hp ⟨i, hi⟩
  -- the slot convergence at levels `≤ 4` along the composed subsequence
  have hconv4' : ∀ (j i : ℕ), j + i ≤ 4 → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ Work.FTS.EllipticEst.Q0 →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => Work.Spaces.mixed j i (G (Φ n)) p.1 p.2)
        (fun p => Work.Spaces.mixed j i f p.1 p.2) Filter.atTop K := by
    intro j i hji K hK hKQ
    have h := hconv4 j i hji K hK hKQ
    simpa only [Φ] using tendstoUniformlyOn_comp_strictMono h hψ
  -- the hypotheses of `LocUnif.HkSq_le` for the composed subsequence
  have hmem' : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G (Φ n)) := fun n => hmem _
  have hbsq' : ∀ n : ℕ, Work.Spaces.HkSq α 6 (G (Φ n)) ≤ B ^ 2 := by
    intro n
    have hn := hb (Φ n)
    have hknn : 0 ≤ Work.Spaces.HkSq α 6 (G (Φ n)) :=
      integral_nonneg fun z => integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 6 (G (Φ n)) z θ
    rw [Work.Spaces.HkNorm] at hn
    calc Work.Spaces.HkSq α 6 (G (Φ n))
        = (Real.sqrt (Work.Spaces.HkSq α 6 (G (Φ n)))) ^ 2 :=
          (Real.sq_sqrt hknn).symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hn 2
  have hSq : Work.Spaces.HkSq α 6 f ≤ B ^ 2 :=
    LocUnif.HkSq_le (α := α) (B := B) (G := G) (Φ := Φ) (f := f)
      hsm hconv4' hconv5' hmem' hbsq'
  have hBnn : 0 ≤ B := le_trans (Real.sqrt_nonneg _) (hb 0)
  have hNorm : Work.Spaces.HkNorm α 6 f ≤ B := by
    rw [Work.Spaces.HkNorm]
    exact (Real.sqrt_le_left hBnn).mpr hSq
  -- the package `ConvLocUnifH6` lists the compact sets before the slot indices
  refine ⟨Φ, f, hΦmono, ?_, hf4, hNorm⟩
  intro K hK hKQ j i hji
  exact hconv4' j i hji K hK hKQ

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.regFromVolterra =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `EpsE4Thr/Leaves/regFromVolterra.lean` — the joint `C¹` of a Volterra curve

The Volterra curve `τ ↦ h₀ + ∫₀^τ A (w_σ) dσ` is jointly `C¹` in `(z, θ, τ)` on the slab
`(0,∞) × (0,π/2) × [0,δ]` provided only that

* the `τ`-slices `(z,θ) ↦ A (w_τ) (z,θ)` are `C¹` (hypothesis `hAy`, on the open quadrant, which
  is exactly where the `τ`-integral is taken),
* the integrand `(z,θ,τ) ↦ A (w_τ) (z,θ)` is continuous on the slab (hypothesis `hAc`), and
* the *spatial* derivative `(z,θ,τ) ↦ ∂_{(z,θ)} A (w_τ) (z,θ)` is continuous on the slab
  (hypothesis `hB`).

No `C¹`-regularity in the *fake time* `τ` is needed — this is the corrected (LEAF-D) form of the
interface item, cf. `EpsE4Thr/RegFromVolterraD.lean`.
-/

noncomputable section
open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.Leaves

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ## The key integral-differentiation lemma, with only the two-slice data -/

/-- **Differentiation under the `τ`-integral, from the slice data alone.**  This is the analogue of
`Work.FTS.StrongEps.EpsE4Thr.RegSlab.hasFDerivAt_intervalIntegral_slab` in which the hypothesis
`ContDiffOn ℝ 1 A (slab)` is replaced by the two weaker ones that the paper's setting actually
provides: joint *continuity* of `A` on the slab (`hAc`) and the `C¹`-regularity of each `τ`-slice
(`hslice`).  The uniform bound on the derivatives along the `(z,θ)`-direction comes from the
continuity of the derivative field (`hB`) on the compact `(z,θ) × [0,δ]` box. -/
theorem hasFDerivAt_intervalIntegral_slab_of_slice {Z Θ : Set ℝ} (hZ : IsOpen Z) (hΘ : IsOpen Θ)
    {δ : ℝ} {A : ℝ × ℝ × ℝ → ℝ}
    (hAc : ContinuousOn (fun p : ℝ × ℝ × ℝ => A (p.1, p.2.1, p.2.2))
      (Z ×ˢ (Θ ×ˢ Set.Icc (0 : ℝ) δ)))
    (hslice : ∀ σ ∈ Set.Icc (0 : ℝ) δ, ∀ z ∈ Z, ∀ θ ∈ Θ,
      HasFDerivAt (fun q : ℝ × ℝ => A (q.1, q.2, σ))
        (fderiv ℝ (fun q : ℝ × ℝ => A (q.1, q.2, σ)) (z, θ)) (z, θ))
    (hB : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        fderiv ℝ (fun q : ℝ × ℝ => A (q.1, q.2, p.2.2)) (p.1, p.2.1))
      (Z ×ˢ (Θ ×ˢ Set.Icc (0 : ℝ) δ)))
    {z θ τ : ℝ} (hz : z ∈ Z) (hθ : θ ∈ Θ) (hτ : τ ∈ Set.Icc (0 : ℝ) δ) :
    HasFDerivAt (fun q : ℝ × ℝ => ∫ σ in (0 : ℝ)..τ, A (q.1, q.2, σ))
      (∫ σ in (0 : ℝ)..τ, fderiv ℝ (fun q : ℝ × ℝ => A (q.1, q.2, σ)) (z, θ)) (z, θ) := by
  have h0τ : (0 : ℝ) ≤ τ := hτ.1
  have hτδ : τ ≤ δ := hτ.2
  -- the `σ`-slice derivative as a function of the point
  let B : ℝ × ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) :=
    fun p => fderiv ℝ (fun q : ℝ × ℝ => A (q.1, q.2, p.2.2)) (p.1, p.2.1)
  let F' : ℝ × ℝ → ℝ → (ℝ × ℝ →L[ℝ] ℝ) :=
    fun x t => fderiv ℝ (fun q : ℝ × ℝ => A (q.1, q.2, t)) x
  have hBc : ContinuousOn B (Z ×ˢ (Θ ×ˢ Set.Icc (0 : ℝ) δ)) := hB
  -- openness: a neighbourhood `s` of `(z, θ)` inside `Z ×ˢ Θ`
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.isOpen_iff.mp hZ z hz
  obtain ⟨ε₂, hε₂pos, hε₂⟩ := Metric.isOpen_iff.mp hΘ θ hθ
  let s : Set (ℝ × ℝ) := Metric.closedBall z (ε₁ / 2) ×ˢ Metric.closedBall θ (ε₂ / 2)
  have hs : s ⊆ Z ×ˢ Θ := by
    intro x hx
    exact ⟨hε₁ (Metric.closedBall_subset_ball (by linarith) hx.1),
      hε₂ (Metric.closedBall_subset_ball (by linarith) hx.2)⟩
  have hs_nhds : ∀ᶠ x in 𝓝 (z, θ), x ∈ s := by
    rw [nhds_prod_eq]
    exact prod_mem_prod (Metric.closedBall_mem_nhds z (by linarith))
      (Metric.closedBall_mem_nhds θ (by linarith))
  -- the compact set on which the derivative field is bounded
  have hKsub : Metric.closedBall z (ε₁ / 2) ×ˢ (Metric.closedBall θ (ε₂ / 2) ×ˢ Set.Icc (0 : ℝ) δ)
      ⊆ Z ×ˢ (Θ ×ˢ Set.Icc (0 : ℝ) δ) := by
    intro p hp
    exact ⟨hε₁ (Metric.closedBall_subset_ball (by linarith) hp.1),
      hε₂ (Metric.closedBall_subset_ball (by linarith) hp.2.1), hp.2.2⟩
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z (ε₁ / 2)).prod
      ((isCompact_closedBall θ (ε₂ / 2)).prod isCompact_Icc)).exists_bound_of_continuousOn
        (hBc.mono hKsub)
  -- the slices are continuous in the integration variable (joint continuity on the slab)
  have slice_cont : ∀ x ∈ s, ContinuousOn (fun t : ℝ => A (x.1, x.2, t)) (Set.Icc (0 : ℝ) δ) := by
    intro x hx
    have hxZ : x.1 ∈ Z := (hs hx).1
    have hxΘ : x.2 ∈ Θ := (hs hx).2
    have hinner : ContinuousOn (fun t : ℝ => (x.1, x.2, t)) (Set.Icc (0 : ℝ) δ) := by fun_prop
    exact hAc.comp hinner (fun t ht => ⟨hxZ, hxΘ, ht⟩)
  have huIoc_sub : Set.uIoc (0 : ℝ) τ ⊆ Set.Icc (0 : ℝ) δ := by
    intro t ht
    rw [Set.uIoc_of_le h0τ] at ht
    exact ⟨le_of_lt ht.1, ht.2.trans hτδ⟩
  have hzθ_mem_s : (z, θ) ∈ s :=
    ⟨Metric.mem_closedBall_self (by linarith), Metric.mem_closedBall_self (by linarith)⟩
  -- measurability hypotheses
  have hF_meas : ∀ᶠ x in 𝓝 (z, θ),
      AEStronglyMeasurable (fun t : ℝ => A (x.1, x.2, t))
        (volume.restrict (Set.uIoc (0 : ℝ) τ)) :=
    hs_nhds.mono fun x hx =>
      ((slice_cont x hx).mono huIoc_sub).aestronglyMeasurable measurableSet_uIoc
  have hF_int : IntervalIntegrable (fun t : ℝ => A (z, θ, t)) volume (0 : ℝ) τ :=
    ((slice_cont (z, θ) hzθ_mem_s).mono (Set.Icc_subset_Icc le_rfl hτδ)).intervalIntegrable_of_Icc
      h0τ
  have hBz : ContinuousOn (fun t : ℝ => B (z, θ, t)) (Set.Icc (0 : ℝ) δ) := by
    have hinner : ContinuousOn (fun t : ℝ => (z, θ, t)) (Set.Icc (0 : ℝ) δ) := by fun_prop
    exact hBc.comp hinner (fun t ht => ⟨hz, hθ, ht⟩)
  have hF'_meas : AEStronglyMeasurable (F' (z, θ)) (volume.restrict (Set.uIoc (0 : ℝ) τ)) :=
    (hBz.mono huIoc_sub).aestronglyMeasurable measurableSet_uIoc
  -- the uniform bound on the derivative
  have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) τ → ∀ x ∈ s, ‖F' x t‖ ≤ C := by
    refine Filter.Eventually.of_forall fun t ht x hx => ?_
    have htIcc : t ∈ Set.Icc (0 : ℝ) δ := huIoc_sub ht
    have hmemK : (x.1, x.2, t) ∈ Metric.closedBall z (ε₁ / 2) ×ˢ
        (Metric.closedBall θ (ε₂ / 2) ×ˢ Set.Icc (0 : ℝ) δ) := ⟨hx.1, hx.2, htIcc⟩
    have h := hC (x.1, x.2, t) hmemK
    simpa [F'] using h
  -- the pointwise slice differentiability (from the slice hypothesis, `hAy`)
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) τ →
      ∀ x ∈ s, HasFDerivAt (fun x : ℝ × ℝ => A (x.1, x.2, t)) (F' x t) x := by
    refine Filter.Eventually.of_forall fun t ht x hx => ?_
    exact hslice t (huIoc_sub ht) x.1 (hs hx).1 x.2 (hs hx).2
  have hbound_int : IntervalIntegrable (fun _ : ℝ => C) volume (0 : ℝ) τ := intervalIntegrable_const
  have key := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ) (μ := volume) (s := s) (a := (0 : ℝ)) (b := τ) (bound := fun _ : ℝ => C)
    (F := fun (x : ℝ × ℝ) (t : ℝ) => A (x.1, x.2, t)) (F' := F') (x₀ := (z, θ))
    hs_nhds hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  simpa [F'] using key

/-! ## The slab data -/

/-- The right-hand side of the Volterra equation, as a function on the slab. -/
private def slabA (F : Fn → Fn) (h₀ : Fn) : ℝ → ℝ → ℝ → ℝ :=
  fun z θ σ => F (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) σ) z θ

/-- The Volterra curve, as a function on the slab. -/
private def slabF (F : Fn → Fn) (h₀ : Fn) : ℝ → ℝ → ℝ → ℝ :=
  fun z θ τ => h₀ z θ + ∫ σ in (0 : ℝ)..τ, slabA F h₀ z θ σ

/-- The candidate `(z,θ)`-derivative of the `τ`-slice, as a function on the slab. -/
private def slabL (F : Fn → Fn) (h₀ : Fn) : ℝ × ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ :=
  fun p => fderiv ℝ (Function.uncurry h₀) (p.1, p.2.1)
    + ∫ σ in (0 : ℝ)..p.2.2, fderiv ℝ (fun q : ℝ × ℝ => slabA F h₀ q.1 q.2 σ) (p.1, p.2.1)

/-! ## The target -/

theorem regFromVolterra {F : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {h₀ : Work.FTS.Galerkin.Fn} {δ : ℝ} (hδ : 0 < δ)
    (hsm0 : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hvol : ∀ z θ τ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → τ ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀ z θ τ
        = h₀ z θ + ∫ s in (0 : ℝ)..τ,
            F (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) s) z θ)
    (hAc : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        F (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) p.2.2) p.1 p.2.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 δ))
    (hAy : ∀ σ ∈ Set.Icc 0 δ, ContDiffOn ℝ 1 (Function.uncurry
        (F (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) σ))) Work.FTS.EllipticEst.Q0)
    (hB : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        fderiv ℝ (Function.uncurry
          (F (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) p.2.2))) (p.1, p.2.1))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 δ)) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ =>
        Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀ p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 δ) := by
  set U : Set (ℝ × ℝ × ℝ) :=
    Set.Ioi 0 ×ˢ (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc (0 : ℝ) δ) with hUdef
  have hmemU : ∀ p : ℝ × ℝ × ℝ, p ∈ U ↔ 0 < p.1 ∧ 0 < p.2.1 ∧ p.2.1 < Real.pi / 2 ∧
      0 ≤ p.2.2 ∧ p.2.2 ≤ δ := by
    intro p
    simp only [hUdef, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc]
    tauto
  -- the integrand is continuous on the slab
  have hAcont : ContinuousOn (fun p : ℝ × ℝ × ℝ => slabA F h₀ p.1 p.2.1 p.2.2) U := hAc
  -- the `(z,θ)`-derivative of the `τ`-slice is continuous on the slab
  have hBcont : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      fderiv ℝ (fun q : ℝ × ℝ => slabA F h₀ q.1 q.2 p.2.2) (p.1, p.2.1)) U := hB
  -- each `τ`-slice is `C¹` on the open quadrant
  have hslice : ∀ σ ∈ Set.Icc (0 : ℝ) δ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasFDerivAt (fun q : ℝ × ℝ => slabA F h₀ q.1 q.2 σ)
        (fderiv ℝ (fun q : ℝ × ℝ => slabA F h₀ q.1 q.2 σ) (z, θ)) (z, θ) := by
    intro σ hσ z hz θ hθ
    have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
    have hcd : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => slabA F h₀ q.1 q.2 σ)
        Work.FTS.EllipticEst.Q0 := hAy σ hσ
    have hca : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => slabA F h₀ q.1 q.2 σ) (z, θ) :=
      hcd.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
    exact (hca.differentiableAt (by norm_num)).hasFDerivAt
  -- the `τ`-slice is differentiable in `(z,θ)` with derivative `slabL`
  have hd : ∀ p ∈ U, HasFDerivAt (fun q : ℝ × ℝ => slabF F h₀ q.1 q.2 p.2.2)
      (slabL F h₀ p) (p.1, p.2.1) := by
    intro p hp
    obtain ⟨hz, hθ, hθ2, hτ0, hτδ⟩ := (hmemU p).mp hp
    -- the `h₀` part
    have hcont0 : ContDiffAt ℝ 1 (Function.uncurry h₀) (p.1, p.2.1) :=
      (((hsm0.forall 1).contDiffWithinAt (x := (p.1, p.2.1)) ⟨hz, hθ, hθ2⟩).contDiffAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds ⟨hz, hθ, hθ2⟩))
    have h1 : HasFDerivAt (fun q : ℝ × ℝ => h₀ q.1 q.2)
        (fderiv ℝ (Function.uncurry h₀) (p.1, p.2.1)) (p.1, p.2.1) :=
      (hcont0.differentiableAt (by norm_num)).hasFDerivAt
    -- the integral part
    have h2 : HasFDerivAt (fun q : ℝ × ℝ => ∫ σ in (0 : ℝ)..p.2.2, slabA F h₀ q.1 q.2 σ)
        (∫ σ in (0 : ℝ)..p.2.2,
          fderiv ℝ (fun q : ℝ × ℝ => slabA F h₀ q.1 q.2 σ) (p.1, p.2.1)) (p.1, p.2.1) :=
      hasFDerivAt_intervalIntegral_slab_of_slice (Z := Set.Ioi (0 : ℝ))
        (Θ := Set.Ioo (0 : ℝ) (Real.pi / 2))
        (A := fun p : ℝ × ℝ × ℝ => slabA F h₀ p.1 p.2.1 p.2.2)
        isOpen_Ioi isOpen_Ioo hAcont hslice hBcont
        hz ⟨hθ, hθ2⟩ ⟨hτ0, hτδ⟩
    have hsum := h1.add h2
    refine HasFDerivAt.congr_of_eventuallyEq (f₁ := fun q : ℝ × ℝ => slabF F h₀ q.1 q.2 p.2.2)
      (f := (fun q : ℝ × ℝ => h₀ q.1 q.2) + fun q : ℝ × ℝ =>
        ∫ σ in (0 : ℝ)..p.2.2, slabA F h₀ q.1 q.2 σ)
      (f' := fderiv ℝ (Function.uncurry h₀) (p.1, p.2.1)
        + ∫ σ in (0 : ℝ)..p.2.2, fderiv ℝ (fun q : ℝ × ℝ => slabA F h₀ q.1 q.2 σ) (p.1, p.2.1))
      (x := (p.1, p.2.1)) hsum ?_
    filter_upwards with q
    simp only [slabF, slabA, Pi.add_apply]
  -- the derivative function is continuous on the slab
  have hL : ContinuousOn (slabL F h₀) U := by
    have hQ0 : ContDiffOn ℝ 1 (Function.uncurry h₀) Work.FTS.EllipticEst.Q0 := hsm0.forall 1
    have hc0 : ContinuousOn (fderiv ℝ (Function.uncurry h₀)) Work.FTS.EllipticEst.Q0 :=
      hQ0.continuousOn_fderiv_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 le_rfl
    have hproj : ContinuousOn (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) U :=
      ((continuous_fst.prodMk (continuous_fst.comp continuous_snd))).continuousOn
    have hmaps : MapsTo (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) U Work.FTS.EllipticEst.Q0 :=
      fun p hp => by
        obtain ⟨hz, hθ, hθ2, hτ0, hτδ⟩ := (hmemU p).mp hp
        exact ⟨hz, hθ, hθ2⟩
    have hL1 : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        fderiv ℝ (Function.uncurry h₀) (p.1, p.2.1)) U := hc0.comp hproj hmaps
    have hL2 : ContinuousOn (fun p : ℝ × ℝ × ℝ => ∫ σ in (0 : ℝ)..p.2.2,
        fderiv ℝ (fun q : ℝ × ℝ => slabA F h₀ q.1 q.2 σ) (p.1, p.2.1)) U :=
      RegSlab.continuousOn_intervalIntegral_slab_normed (B := fun p : ℝ × ℝ × ℝ =>
        fderiv ℝ (fun q : ℝ × ℝ => slabA F h₀ q.1 q.2 p.2.2) (p.1, p.2.1)) hBcont
    have heq : slabL F h₀ = (fun p : ℝ × ℝ × ℝ => fderiv ℝ (Function.uncurry h₀) (p.1, p.2.1))
        + fun p : ℝ × ℝ × ℝ => ∫ σ in (0 : ℝ)..p.2.2,
            fderiv ℝ (fun q : ℝ × ℝ => slabA F h₀ q.1 q.2 σ) (p.1, p.2.1) := by
      funext p
      simp only [slabL, Pi.add_apply]
    rw [heq]
    exact hL1.add hL2
  -- the identity of the Volterra representation
  have hId : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ → τ ≤ δ →
      slabF F h₀ z θ τ = slabF F h₀ z θ 0 + ∫ σ in (0 : ℝ)..τ, slabA F h₀ z θ σ := by
    intro z θ τ hz hθ hθ2 hτ0 hτδ
    simp only [slabF]
    rw [intervalIntegral.integral_same, add_zero]
  -- the abstract slab `C¹`-lemma
  have hmain : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => slabF F h₀ p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc (0 : ℝ) δ)) :=
    (Work.FTS_RegExport.RXT0.slabC1Flat (S := δ) (A := slabA F h₀) (f := slabF F h₀)
      (L := slabL F h₀) hδ hAcont hId hd hL).1
  -- transfer to the Volterra curve
  have hUeq : U = Set.Ioi 0 ×ˢ (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc (0 : ℝ) δ) := rfl
  rw [hUeq]
  refine hmain.congr fun p hp => ?_
  obtain ⟨hz, hθ, hθ2, hτ0, hτδ⟩ := (hmemU p).mp (hUeq ▸ hp)
  simpa only [slabF, slabA] using hvol p.1 p.2.1 p.2.2 hz ⟨hθ, hθ2⟩ ⟨hτ0, hτδ⟩

end Work.FTS.StrongEps.EpsE4Thr.Leaves
end
end
