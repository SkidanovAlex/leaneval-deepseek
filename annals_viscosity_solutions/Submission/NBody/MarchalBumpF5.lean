import Submission.NBody.MarchalBumpAction
import Submission.NBody.EnergyAe

/-!
# The last plumbing pieces of the symmetric-bump argument

The module `MarchalBumpAction` converts the strict negativity of the window integral into a
contradiction with minimality, but it takes several technical hypotheses (interval integrability of
the two Lagrangian integrands, the a.e. vanishing of the bump outside the window, the a.e.
collision-freeness of the competitor, ...).  This module derives them from the natural data:

* `aestronglyMeasurable_lagR_of_absolutelyContinuousOnInterval`;
* `integrable_lagR_of_actionOn_lt_top_of_ae` and `intervalIntegrable_lagR_of_actionOn_lt_top_of_ae`
  (the a.e.-collision-free version of `FirstVariation.integrable_lagR_of_actionOn_lt_top`);
* `deriv_bumpCurve_eq_of_lt` and `ae_lagR_bumpCurve_sub_self_eq_zero` (the bump does not change the
  Lagrangian outside its window, almost everywhere);
* `isHMinimizer_false_of_bump_window`, the single-call contradiction.

All results in this file are fully proved.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- The real Lagrangian along an absolutely continuous curve is almost everywhere strongly
measurable. -/
lemma aestronglyMeasurable_lagR_of_absolutelyContinuousOnInterval {m : Fin N → ℝ} {h : ℝ}
    {γ : ℝ → EN E N} {a b : ℝ} (hac : AbsolutelyContinuousOnInterval γ a b) :
    AEStronglyMeasurable (fun t => lagR m h (γ t) (deriv γ t))
      (volume.restrict (Set.Ioc a b)) := by
  letI : MeasurableSpace (EN E N) := borel (EN E N)
  haveI : BorelSpace (EN E N) := ⟨rfl⟩
  have hγmeas : AEMeasurable γ (volume.restrict (Set.Ioc a b)) :=
    (hac.continuousOn.mono (fun t ht => Set.mem_uIcc.mpr (Or.inl ⟨ht.1.le, ht.2⟩))).aestronglyMeasurable
      measurableSet_Ioc |>.aemeasurable
  have hK : AEStronglyMeasurable (fun t => kinetic m (deriv γ t))
      (volume.restrict (Set.Ioc a b)) :=
    (continuous_kinetic m).aestronglyMeasurable.comp_aemeasurable
      (Commons.MeasureTheory.Integral.aestronglyMeasurable_deriv_of_absolutelyContinuousOnInterval
        hac).aemeasurable
  have hU : AEStronglyMeasurable (fun t => U m (γ t)) (volume.restrict (Set.Ioc a b)) :=
    (measurable_U m).aestronglyMeasurable.comp_aemeasurable hγmeas
  have hconst : AEStronglyMeasurable (fun _ : ℝ => h) (volume.restrict (Set.Ioc a b)) :=
    aestronglyMeasurable_const
  have hfun : (fun t : ℝ => lagR m h (γ t) (deriv γ t))
      = (fun t : ℝ => kinetic m (deriv γ t)) + ((fun t : ℝ => U m (γ t)) + fun _ => h) := by
    funext t
    simp only [lagR, kinetic, Pi.add_apply]
    ring
  rw [hfun]
  exact hK.add (hU.add hconst)

/-- **The Lagrangian is integrable along an absolutely continuous curve of finite action** (only
almost-everywhere collision freeness is assumed). -/
theorem integrable_lagR_of_actionOn_lt_top_of_ae {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N}
    {a b : ℝ} (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hnc : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), WithoutCollisions (γ t))
    (hfin : actionOn m h γ a b < ⊤) :
    Integrable (fun t => lagR m h (γ t) (deriv γ t)) (volume.restrict (Set.Ioc a b)) := by
  letI : MeasurableSpace (EN E N) := borel (EN E N)
  haveI : BorelSpace (EN E N) := ⟨rfl⟩
  have hnn : ∀ t, 0 ≤ lagR m h (γ t) (deriv γ t) := by
    intro t
    rw [lagR]
    have hU := U_nonneg hm (γ t)
    have hK := kinetic_nonneg m hm (deriv γ t)
    rw [kinetic] at hK
    linarith
  have hpt : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      lagrangian m h (γ t) (deriv γ t) = ENNReal.ofReal (lagR m h (γ t) (deriv γ t)) :=
    hnc.mono fun t ht => lagrangian_eq_ofReal_lagR ht
  have h1 : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (lagR m h (γ t) (deriv γ t)))
      = actionOn m h γ a b := by
    rw [actionOn]
    exact (lintegral_congr_ae hpt).symm
  refine ⟨aestronglyMeasurable_lagR_of_absolutelyContinuousOnInterval hac, ?_⟩
  have h4 : (∫⁻ t in Set.Ioc a b, ‖lagR m h (γ t) (deriv γ t)‖ₑ)
      = ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (lagR m h (γ t) (deriv γ t)) :=
    lintegral_congr fun t => by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn t)]
  have h3 : (∫⁻ t in Set.Ioc a b, ‖lagR m h (γ t) (deriv γ t)‖ₑ) < ⊤ := by
    rw [h4, h1]; exact hfin
  simpa only [HasFiniteIntegral] using h3

/-- The interval-integrability form. -/
theorem intervalIntegrable_lagR_of_actionOn_lt_top_of_ae {m : Fin N → ℝ} {h : ℝ}
    {γ : ℝ → EN E N} {a b : ℝ} (hab : a ≤ b) (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hnc : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), WithoutCollisions (γ t))
    (hfin : actionOn m h γ a b < ⊤) :
    IntervalIntegrable (fun t => lagR m h (γ t) (deriv γ t)) volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    (integrable_lagR_of_actionOn_lt_top_of_ae hm hh hac hnc hfin)

/-! ## The bump does not change the Lagrangian off its window -/

/-- Outside the open window the bump leaves the derivative of the curve unchanged (the perturbation
vanishes on a whole neighbourhood). -/
lemma deriv_bumpCurve_eq_of_lt {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ : Fin N} {δ : E}
    (hδ : δ ≠ 0) {lam T t₀ : ℝ} (hlam : 0 < lam) {γ : ℝ → EN E N} {s : ℝ}
    (h : lam * T < |s - t₀|) :
    deriv (bumpCurve m k i₀ δ T lam t₀ γ) s = deriv γ s := by
  refine Filter.EventuallyEq.deriv_eq ?_
  have hset : {u : ℝ | lam * T < |u - t₀|} ∈ 𝓝 s := by
    refine IsOpen.mem_nhds ?_ h
    exact isOpen_lt continuous_const (continuous_abs.comp (continuous_id.sub continuous_const))
  filter_upwards [hset] with u hu
  exact bumpCurve_eq_of_le hδ hlam (le_of_lt hu)

/-- The set on which the window bound is an equality is finite. -/
lemma finite_set_abs_eq {c t₀ : ℝ} (hc : 0 ≤ c) : {s : ℝ | |s - t₀| = c}.Finite := by
  have hsub : {s : ℝ | |s - t₀| = c} ⊆ ({t₀ - c, t₀ + c} : Set ℝ) := by
    intro s hs
    rcases (abs_eq hc).mp hs with h1 | h1
    · exact Set.mem_insert_iff.mpr (Or.inr (by rw [Set.mem_singleton_iff]; linarith))
    · exact Set.mem_insert_iff.mpr (Or.inl (by linarith))
  exact (Set.finite_singleton _).insert _ |>.subset hsub

/-- **The bump and the original curve have the same Lagrangian, almost everywhere outside the
window.** -/
lemma ae_lagR_bumpCurve_sub_self_eq_zero {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ : Fin N}
    {δ : E} (hδ : δ ≠ 0) {lam T t₀ h : ℝ} (hlam : 0 < lam) (hT : 0 ≤ T) {γ : ℝ → EN E N}
    {c d : ℝ} (hcd : ∀ s ∈ Set.Ioc c d, lam * T ≤ |s - t₀|) :
    (fun t => lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
        (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t) - lagR m h (γ t) (deriv γ t))
      =ᵐ[volume.restrict (Set.Ioc c d)] (fun _ : ℝ => (0:ℝ)) := by
  have hc0 : 0 ≤ lam * T := mul_nonneg hlam.le hT
  have hnull : (volume : Measure ℝ) {s : ℝ | |s - t₀| = lam * T} = 0 :=
    (finite_set_abs_eq (t₀ := t₀) hc0).measure_zero volume
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∉ {s : ℝ | |s - t₀| = lam * T} := by
    rw [MeasureTheory.ae_iff]
    simpa using hnull
  have hae' : ∀ᵐ s ∂volume.restrict (Set.Ioc c d), s ∉ {s : ℝ | |s - t₀| = lam * T} :=
    ae_restrict_of_ae hae
  filter_upwards [hae', MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hsnot hs
  have hlt : lam * T < |s - t₀| := lt_of_le_of_ne (hcd s hs) (fun hh => hsnot hh.symm)
  rw [deriv_bumpCurve_eq_of_lt hδ hlam hlt, bumpCurve_eq_of_le hδ hlam (le_of_lt hlt)]
  ring


/-- **The single-call contradiction of the symmetric-bump argument.**  Given an `h`-minimiser `γ`
on `[a,b]`, a window `[t₀-λT, t₀+λT]` inside `[a,b]`, a cluster `k ∋ i₀` and a displacement `δ`, if
the symmetric bump of `γ` inside the window has strictly smaller action (and finite action, and is
a.e. collision free), then `False`. -/
theorem isHMinimizer_false_of_bump_window {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {h : ℝ}
    (hh : 0 ≤ h) {γ : ℝ → EN E N} {a b t₀ T lam : ℝ} (hab : a < b)
    {k : Finset (Fin N)} {i₀ : Fin N} (hi₀ : i₀ ∈ k) {δ : E} (hδ : δ ≠ 0) (hlam : 0 < lam)
    (hT : 0 ≤ T)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b)
    (hfin : actionOn m h γ a b < ⊤)
    (hfinη : actionOn m h (bumpCurve m k i₀ δ T lam t₀ γ) a b < ⊤)
    (hint : IntervalIntegrable (fun t => lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
        (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t) - lagR m h (γ t) (deriv γ t))
      volume (t₀ - lam * T) (t₀ + lam * T))
    (horders : a ≤ t₀ - lam * T) (horders2 : t₀ + lam * T ≤ b)
    (hwin : ∫ t in (t₀ - lam * T)..(t₀ + lam * T),
        (lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
          (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t) - lagR m h (γ t) (deriv γ t)) < 0) :
    False := by
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hnc : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), WithoutCollisions (γ t) :=
    ae_withoutCollisions_of_actionOn_lt_top hac hfin
  have hacη : AbsolutelyContinuousOnInterval (bumpCurve m k i₀ δ T lam t₀ γ) a b :=
    absolutelyContinuousOnInterval_bumpCurve (m := m) (k := k) (i₀ := i₀) hδ hlam hac
  -- the bumped curve is collision free almost everywhere (it has finite action)
  have hncη : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      WithoutCollisions (bumpCurve m k i₀ δ T lam t₀ γ t) :=
    ae_withoutCollisions_of_actionOn_lt_top hacη hfinη
  have hint2 : IntervalIntegrable (fun t => lagR m h (γ t) (deriv γ t)) volume a b :=
    intervalIntegrable_lagR_of_actionOn_lt_top_of_ae hab.le hm0 hh hac hnc hfin
  have hint1 : IntervalIntegrable (fun t => lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
      (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t)) volume a b :=
    intervalIntegrable_lagR_of_actionOn_lt_top_of_ae hab.le hm0 hh hacη hncη hfinη
  have hleft : (fun t => lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
        (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t) - lagR m h (γ t) (deriv γ t))
      =ᵐ[volume.restrict (Set.Ioc a (t₀ - lam * T))] (fun _ : ℝ => (0:ℝ)) :=
    ae_lagR_bumpCurve_sub_self_eq_zero (m := m) (k := k) (i₀ := i₀) hδ hlam hT
      (fun s hs => by
        have h1 : s ≤ t₀ - lam * T := hs.2
        have h2 : 0 ≤ lam * T := mul_nonneg hlam.le hT
        rw [abs_of_nonpos (by linarith : s - t₀ ≤ 0)]
        linarith)
  have hright : (fun t => lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
        (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t) - lagR m h (γ t) (deriv γ t))
      =ᵐ[volume.restrict (Set.Ioc (t₀ + lam * T) b)] (fun _ : ℝ => (0:ℝ)) :=
    ae_lagR_bumpCurve_sub_self_eq_zero (m := m) (k := k) (i₀ := i₀) hδ hlam hT
      (fun s hs => by
        have h1 : t₀ + lam * T ≤ s := le_of_lt hs.1
        have h2 : 0 ≤ lam * T := mul_nonneg hlam.le hT
        rw [abs_of_nonneg (by linarith : 0 ≤ s - t₀)]
        linarith)
  exact not_isHMinimizer_of_window_negative hm hh hab hδ hlam hT hac hacη hnc hncη hfin hfinη
    hint1 hint2 hleft hint hright horders horders2 hwin hmin

/-- **Combining an eventually-true property with an existential one.**  If `P` holds for all
sufficiently small positive `l` and one has a positive `l₀`, then some `l < l₀` (positive) satisfies
`P`. -/
lemma exists_pos_lt_of_eventually {P : ℝ → Prop} {l₀ : ℝ} (hl₀ : 0 < l₀)
    (h : ∀ᶠ l in nhdsWithin (0:ℝ) (Ioi 0), P l) :
    ∃ l ∈ Ioi (0:ℝ), l < l₀ ∧ P l := by
  obtain ⟨ε, hε, hε'⟩ : ∃ ε > 0, ∀ l, 0 < l → l < ε → P l := by
    have h' := (eventually_nhdsWithin_iff.mp h)
    obtain ⟨ε, hε, hε''⟩ := Metric.eventually_nhds_iff.mp h'
    refine ⟨ε, hε, fun l hl hle => ?_⟩
    exact hε'' (by rw [Real.dist_eq, sub_zero, abs_of_pos hl]; exact hle) hl
  refine ⟨min ε l₀ / 2, ?_, ?_, ?_⟩
  · exact Set.mem_Ioi.mpr (by positivity)
  · have h1 : min ε l₀ ≤ l₀ := min_le_right _ _
    linarith
  · have h1 : min ε l₀ ≤ ε := min_le_left _ _
    exact hε' _ (by positivity) (by linarith)

end Submission.NBody
