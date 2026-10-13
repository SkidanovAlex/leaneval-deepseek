/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/IterContMeas.lean` — continuity in the fake time and joint
# measurability of the Picard curves are **derived** from the class data

The applicable Volterra engine `Work.FTS.EpsEngine.exists_volterra_v4` consumes two iterate-indexed
hypotheses

* `hcontIter : ∀ n, ∀ z θ, 0 < z → 0 < θ → θ < π/2 →
    ContinuousOn (fun s => F (slice (iter F h₀ n) s) z θ) (Icc 0 δ)`,
* `hmeasIter : ∀ n, AEStronglyMeasurable (fun p : ℝ × ℝ × ℝ => F (slice (iter F h₀ n) p.1) p.2.1 p.2.2) volume`

(the second one in the *global* form).  This module proves that **both are consequences** of the
data that the application actually has:

* the *class* `P` is preserved along the iteration (`hP`: `P (slice (iter F h₀ n) τ)` for
  `τ ∈ Icc 0 δ`) — the engine's `hkeepIter` obligation, and
* `F` is continuous on the open quadrant `Q0` *and vanishes off it* at every class profile
  (`hcontP`, `hzeroP`), bounded in the weighted `L²`-metric on `P` (`hbd`), and pointwise
  Lipschitz in the `EpsSq`-metric on `P` (`hpt`) — all four of which hold for the concrete
  right-hand side `Feps` of the projected `ε`-scheme.

## The induction

The two properties are proved jointly by induction on the iterate index, in the interleaved order

  `cont(n)`  ⟹  `aesm(n)`  ⟹  Minkowski  ⟹  `cont(n+1)`,

* `cont(n) ⟹ aesm(n)` (`aesm_of_contIter`): for each fixed `(z,θ) ∈ Q0` the function
  `s ↦ F (slice (iter F h₀ n) s) z θ` is *continuous* on `Icc 0 δ`, hence measurable in `s`;
  together with the per-profile continuity and vanishing on `Q0` this is exactly the hypothesis list
  of the Carathéodory lemma (`aesm_uncurry_restricted`, the horizon-restricted form of the proved
  `aesm_uncurry_of_continuousOn_of_zero`).  **This is the step that was missing** — see finding
  (XVII) of `StrongEps/NOTES.md`, where only the *parametric-integral* half was available;
* `aesm(n) ⟹ cont(n+1)` (`cont_iter_succ`, via `EpsSq_integral_iter_le`): the `(n+1)`-st Picard
  curve is `h₀ + ∫₀^s F (slice (iter F h₀ n) t) dt`, so for `a ≤ b` in `[0,δ]` the increment is the
  parametric interval integral of the level-`n` curve; measurability of the weighted integrand (the
  restriction of `aesm(n)`) feeds the *Minkowski* bound `EpsSq_intervalIntegral_le_gen`, giving
  `EpsSq (slice (iter F h₀ (n+1)) a − slice (iter F h₀ (n+1)) b) ≤ (b−a)² L`, and the pointwise
  Lipschitz bound `hpt` then gives `|F … a − F … b| ≤ Cpt √L (b−a)`, i.e. continuity in `s`.

Note the measure: `aesm` is stated against the **horizon-restricted** measure
`(volume.restrict (Icc 0 δ)).prod volume`, which is the honest form (the class data is available
only on `[0,δ]`, and `F` is unconstrained off `P`; the global form is refutable — finding (XXI)).

## The prefix form

`iter_cont_meas_prefix` is the same statement with the class hypothesis available only up to a bound
`N` (and the conclusion only up to `N`).  This is what the *inductive* production of `hkeepIter`
needs (the lead's ruling on finding (XXIII), `EpsEngine/SmoothOpenIter.lean`): at level `n` one only
knows the class data of the levels `≤ n`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.Defs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.Iter
import Submission.Work.FTS.EpsEngine.EpsSq_intervalIntegral_le_gen
import Submission.Work.FTS.EpsEngine.aesm_uncurry_restricted
import Submission.Work.FTS.EpsEngine.aesm_weighted_prod_restricted
import Submission.Work.FTS.EllipticEst.OpenQDefs

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
