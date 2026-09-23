import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.longHomotopy.exists_local_lift
import Submission.Work.OddBound.longHomotopy.exists_lift_of_short
import Submission.Work.OddBound.longHomotopy.curveLength_toolkit

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

namespace Work.OddBound.liftPiecewise

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open LeanEval.Geometry.SphereTheorem Submission.Geodesic Submission.JacobiGlobal
  Submission.GlobalExp Submission.Length Submission.InjRadius

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E]

/-! ## 1. Integrability of the speed of a `C¹` curve on a general interval `[α,β]`

This is the integrability half of `Submission.Length.curveLength_toolkit`
(`Submission/Work/OddBound/longHomotopy/curveLength_toolkit.lean`), with the interval `[0,S]`
replaced by an arbitrary interval `[α,β]`, `α < β`.  It is needed below for a piecewise `C¹` curve,
where each *piece* is only `C¹` on its own interval. -/

theorem intervalIntegrable_curveSpeed_of_contMDiffOn_Icc {h : ℝ → M} {α β : ℝ} (hαβ : α < β)
    (hc : ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc α β)) :
    ∀ c d : ℝ, α ≤ c → c ≤ d → d ≤ β →
      IntervalIntegrable (curveSpeed (I := I) h) MeasureTheory.volume c d := by
  haveI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) := by
    obtain ⟨Φ, hΦsm, hΦ⟩ :=
      (inferInstance : IsContMDiffRiemannianBundle I ∞ E
        (fun x : M ↦ TangentSpace I x)).exists_contMDiff
    exact ⟨Φ, hΦsm.continuous, hΦ⟩
  set s : Set ℝ := Set.Icc α β with hsdef
  have hs_umd : UniqueMDiff[s] := UniqueDiffOn.uniqueMDiffOn (uniqueDiffOn_Icc hαβ)
  have htan : ContinuousOn (tangentMapWithin 𝓘(ℝ) I h s) (Bundle.TotalSpace.proj ⁻¹' s) :=
    hc.continuousOn_tangentMapWithin le_rfl hs_umd
  have hκ : ContinuousOn (fun t : ℝ => (Bundle.TotalSpace.mk' ℝ t (1 : TangentSpace 𝓘(ℝ) t) :
      TangentBundle 𝓘(ℝ) ℝ)) s :=
    ((contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ) (n := ∞) (E := ℝ)
      (V := fun t : ℝ => (1 : TangentSpace 𝓘(ℝ) t))).mpr contDiff_const).continuous.continuousOn
  have hcomp : ContinuousOn (fun t : ℝ =>
      (⟨h t, (mfderivWithin 𝓘(ℝ) I h s t) (1 : ℝ)⟩ : TangentBundle I M)) s :=
    htan.comp hκ (fun t ht => by simpa using ht)
  set g : ℝ → ℝ := fun t => Real.sqrt
    (inner ℝ ((mfderivWithin 𝓘(ℝ) I h s t) (1 : ℝ))
      ((mfderivWithin 𝓘(ℝ) I h s t) (1 : ℝ))) with hgdef
  have hgcont : ContinuousOn g s := (ContinuousOn.inner_bundle (b := h) hcomp hcomp).sqrt
  have hgspeed : ∀ t ∈ Set.Ioo α β, g t = curveSpeed (I := I) h t := by
    intro t ht
    have hmem : s ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    show Real.sqrt (inner ℝ ((mfderivWithin 𝓘(ℝ) I h s t) (1 : ℝ))
      ((mfderivWithin 𝓘(ℝ) I h s t) (1 : ℝ))) = curveSpeed (I := I) h t
    rw [mfderivWithin_of_mem_nhds hmem, Submission.Length.curveSpeed_def,
      Submission.Geodesic.curveVelocity_apply]
  have hae : ∀ a b : ℝ, α ≤ a → a ≤ b → b ≤ β →
      curveSpeed (I := I) h =ᵐ[volume.restrict (Set.Icc a b)] g := by
    intro a b ha hab hbβ
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null (t := ({α} ∪ {β} : Set ℝ)) ?_ ?_
    · intro t ht
      rw [Set.mem_ofPred_eq] at ht
      by_contra hcon
      simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at hcon
      have htab : t ∈ Set.Icc a b := by
        by_contra hmem
        exact ht (fun h' => absurd h' hmem)
      have hne : curveSpeed (I := I) h t ≠ g t := fun heq => ht (fun _ => heq)
      exact hne (hgspeed t ⟨lt_of_le_of_ne (le_trans ha htab.1) (Ne.symm hcon.1),
        lt_of_le_of_ne (le_trans htab.2 hbβ) hcon.2⟩).symm
    · rw [measure_union_null_iff]
      exact ⟨measure_singleton α, measure_singleton β⟩
  intro c d hαc hcd hdβ
  have hsub : Set.Icc c d ⊆ s := Icc_subset_Icc hαc hdβ
  have hintg : IntegrableOn g (Set.Icc c d) volume := (hgcont.mono hsub).integrableOn_Icc
  have hintcs : IntegrableOn (curveSpeed (I := I) h) (Set.Icc c d) volume :=
    hintg.congr_fun_ae (hae c d hαc hcd hdβ).symm
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hcd).mpr
    (hintcs.mono_set Set.Ioc_subset_Icc_self)

/-! ## 2. The length toolkit for a piecewise `C¹` curve

For a curve `h` that is `C¹` on each piece `[a j.castSucc, a j.succ]` of a strictly increasing
partition `0 = a 0 < a 1 < ⋯ < a k = S`, the Riemannian speed `curveSpeed h` is interval integrable
on every subinterval of `[0,S]`, and consequently the length `s ↦ curveLength h 0 s` is monotone and
additive. -/

section Piecewise

variable {h : ℝ → M} {S : ℝ} {k : ℕ} {a : Fin (k + 1) → ℝ}

theorem intervalIntegrable_curveSpeed_piecewise
    (hamono : StrictMono a) (ha0 : a 0 = 0) (haS : a (Fin.last k) = S)
    (hpiece : ∀ j : Fin k, ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc (a j.castSucc) (a j.succ))) :
    ∀ c d : ℝ, 0 ≤ c → c ≤ d → d ≤ S →
      IntervalIntegrable (curveSpeed (I := I) h) MeasureTheory.volume c d := by
  have key : ∀ i : Fin (k + 1), ∀ c d : ℝ, 0 ≤ c → c ≤ d → d ≤ a i →
      IntervalIntegrable (curveSpeed (I := I) h) MeasureTheory.volume c d := by
    refine Fin.induction ?base ?step
    · intro c d hc0 hcd hd
      have hd0 : d = 0 := le_antisymm (by rw [ha0] at hd; exact hd) (le_trans hc0 hcd)
      subst hd0
      have hc0' : c = 0 := le_antisymm hcd hc0
      subst hc0'
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le le_rfl]; simp
    · intro i ih c d hc0 hcd hd
      have hlt : a i.castSucc < a i.succ := hamono (Fin.castSucc_lt_succ_iff.mpr le_rfl)
      rcases le_or_gt d (a i.castSucc) with hdle | hdlt
      · exact ih c d hc0 hcd hdle
      · rcases le_or_gt (a i.castSucc) c with hcle | hclt
        · exact intervalIntegrable_curveSpeed_of_contMDiffOn_Icc (hαβ := hlt) (hpiece i) c d hcle hcd hd
        · have h1 : IntervalIntegrable (curveSpeed (I := I) h) volume c (a i.castSucc) :=
            ih c (a i.castSucc) hc0 hclt.le le_rfl
          have h2 : IntervalIntegrable (curveSpeed (I := I) h) volume (a i.castSucc) d :=
            intervalIntegrable_curveSpeed_of_contMDiffOn_Icc (hαβ := hlt) (hpiece i)
              (a i.castSucc) d le_rfl hdlt.le hd
          refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hcd).mpr ?_
          have hI1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le hclt.le).mp h1
          have hI2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le hdlt.le).mp h2
          rw [← Set.Ioc_union_Ioc_eq_Ioc hclt.le hdlt.le]
          exact hI1.union hI2
  intro c d hc0 hcd hd
  exact key (Fin.last k) c d hc0 hcd (by rw [haS]; exact hd)

theorem curveLength_mono_piecewise
    (hamono : StrictMono a) (ha0 : a 0 = 0) (haS : a (Fin.last k) = S)
    (hpiece : ∀ j : Fin k, ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc (a j.castSucc) (a j.succ))) :
    ∀ c d : ℝ, 0 ≤ c → c ≤ d → d ≤ S →
      Submission.Length.curveLength (I := I) h 0 c ≤
        Submission.Length.curveLength (I := I) h 0 d := by
  intro c d hc0 hcd hdS
  have h1 := intervalIntegrable_curveSpeed_piecewise (I := I) (h := h) hamono ha0 haS hpiece
    0 c le_rfl hc0 (le_trans hcd hdS)
  have h2 := intervalIntegrable_curveSpeed_piecewise (I := I) (h := h) hamono ha0 haS hpiece
    c d hc0 hcd hdS
  have hadd := Submission.Length.curveLength_add_of_integrable (I := I) h h1 h2
  have hnn : 0 ≤ Submission.Length.curveLength (I := I) h c d :=
    Submission.Length.curveLength_nonneg (I := I) h hcd
  linarith

theorem curveLength_add_piecewise
    (hamono : StrictMono a) (ha0 : a 0 = 0) (haS : a (Fin.last k) = S)
    (hpiece : ∀ j : Fin k, ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc (a j.castSucc) (a j.succ)))
    {c d : ℝ} (hc0 : 0 ≤ c) (hcd : c ≤ d) (hdS : d ≤ S) :
    Submission.Length.curveLength (I := I) h 0 c +
      Submission.Length.curveLength (I := I) h c d =
      Submission.Length.curveLength (I := I) h 0 d := by
  have h1 := intervalIntegrable_curveSpeed_piecewise (I := I) (h := h) hamono ha0 haS hpiece
    0 c le_rfl hc0 (le_trans hcd hdS)
  have h2 := intervalIntegrable_curveSpeed_piecewise (I := I) (h := h) hamono ha0 haS hpiece
    c d hc0 hcd hdS
  exact Submission.Length.curveLength_add_of_integrable (I := I) h h1 h2

/-- **The index of the piece of the partition containing a point `T ∈ [0,S)`.** -/
private theorem exists_piece_index {k : ℕ} {a : Fin (k + 1) → ℝ} (hmono : StrictMono a)
    {T : ℝ} (h0 : a 0 ≤ T) (hT : T < a (Fin.last k)) :
    ∃ j : Fin k, a j.castSucc ≤ T ∧ T < a j.succ := by
  classical
  have hfin : ({i : Fin (k + 1) | a i ≤ T}).Finite := Set.finite_univ.subset (Set.subset_univ _)
  have hne : ({i : Fin (k + 1) | a i ≤ T}).Nonempty := ⟨0, h0⟩
  obtain ⟨i₀, hi₀mem, hi₀max⟩ :=
    Set.exists_max_image (s := {i : Fin (k + 1) | a i ≤ T}) (f := a) hfin hne
  have hilt : i₀.val < k := by
    have h1 : a i₀ < a (Fin.last k) := lt_of_le_of_lt hi₀mem hT
    have h2 : i₀ < Fin.last k := hmono.lt_iff_lt.mp h1
    simpa [Fin.lt_def] using h2
  refine ⟨⟨i₀.val, hilt⟩, ?_, ?_⟩
  · have hcast : (⟨i₀.val, hilt⟩ : Fin k).castSucc = i₀ := Fin.ext rfl
    rw [hcast]; exact hi₀mem
  · have hsucc : (⟨i₀.val, hilt⟩ : Fin k).succ = ⟨i₀.val + 1, Nat.succ_lt_succ hilt⟩ := Fin.ext rfl
    rw [hsucc]
    by_contra hcon
    have hmem : (⟨i₀.val + 1, Nat.succ_lt_succ hilt⟩ : Fin (k + 1)) ∈ {i | a i ≤ T} :=
      not_lt.mp hcon
    have hle := hi₀max _ hmem
    have hlt : a i₀ < a ⟨i₀.val + 1, Nat.succ_lt_succ hilt⟩ :=
      hmono (by simp [Fin.lt_def])
    linarith

end Piecewise

/-! ## 3. Continuity of the truncation of a continuous curve -/

private theorem nhdsWithin_Iic_eq_nhdsWithin_Icc' {S : ℝ} (hS : 0 < S) :
    𝓝[Set.Iic S] S = 𝓝[Set.Icc (0 : ℝ) S] S := by
  have hkey : ∀ t : ℝ, t ∈ Metric.ball S (S / 2) → (0 : ℝ) < t := by
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq] at ht
    have h1 := (abs_lt.mp ht).1
    linarith
  have hmemIic : Set.Ioi (0 : ℝ) ∈ 𝓝[Set.Iic S] S := by
    refine Metric.mem_nhdsWithin_iff.mpr ⟨S / 2, by linarith, ?_⟩
    rintro t ⟨ht1, ht2⟩
    exact hkey t ht1
  have hmemIcc : Set.Ioi (0 : ℝ) ∈ 𝓝[Set.Icc (0 : ℝ) S] S := by
    refine Metric.mem_nhdsWithin_iff.mpr ⟨S / 2, by linarith, ?_⟩
    rintro t ⟨ht1, ht2⟩
    exact hkey t ht1
  have e1 : 𝓝[Set.Ioi (0 : ℝ) ∩ Set.Iic S] S = 𝓝[Set.Iic S] S :=
    nhdsWithin_inter_of_mem hmemIic
  have e2 : 𝓝[Set.Ioi (0 : ℝ) ∩ Set.Icc (0 : ℝ) S] S = 𝓝[Set.Icc (0 : ℝ) S] S :=
    nhdsWithin_inter_of_mem hmemIcc
  have hset : Set.Ioi (0 : ℝ) ∩ Set.Iic S = Set.Ioi (0 : ℝ) ∩ Set.Icc (0 : ℝ) S := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, le_of_lt h1, h2⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3⟩
  rw [← e1, ← e2, hset]

/-- **The curve truncated at `S` is continuous at every `T ∈ (0, S]`, for a curve that is only
assumed continuous on `[0,S]`.** -/
theorem continuousAt_trunc_of_continuousOn {h : ℝ → M} {S : ℝ}
    (hc : ContinuousOn h (Set.Icc (0 : ℝ) S)) (hS : 0 < S)
    {T : ℝ} (hT0 : 0 < T) (hTS : T ≤ S) :
    ContinuousAt (fun t : ℝ => if t ≤ S then h t else h S) T := by
  set h' : ℝ → M := fun t => if t ≤ S then h t else h S with hh'
  rcases lt_or_eq_of_le hTS with hlt | heq
  · have hnb : Set.Icc (0 : ℝ) S ∈ 𝓝 T :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ⟨hT0, hlt⟩)
        (fun t ht => ⟨ht.1.le, ht.2.le⟩)
    have hcont : ContinuousAt h T :=
      (hc.continuousWithinAt ⟨hT0.le, hTS⟩).continuousAt hnb
    refine hcont.congr ?_
    filter_upwards [Iio_mem_nhds hlt] with t ht
    have htle : t ≤ S := (Set.mem_Iio.mp ht).le
    show h t = h' t
    rw [hh']
    simp only [htle, if_true]
  · rw [heq]
    have hleft : ContinuousWithinAt h' (Set.Iic S) S := by
      have h2 : ContinuousWithinAt h (Set.Icc (0 : ℝ) S) S := hc S ⟨hS.le, le_rfl⟩
      have h3 : ContinuousWithinAt h (Set.Iic S) S := by
        have ht : Tendsto h (𝓝[Set.Iic S] S) (𝓝 (h S)) := by
          rw [nhdsWithin_Iic_eq_nhdsWithin_Icc' hS]
          exact h2
        exact ht
      refine h3.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with t ht
        rw [hh']; simp only [Set.mem_Iic.mp ht, if_true]
      · rw [hh']; simp
    have hright : ContinuousWithinAt h' (Set.Ici S) S := by
      have hconst : ContinuousWithinAt (fun _ : ℝ => h S) (Set.Ici S) S :=
        continuousWithinAt_const
      refine hconst.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with t ht
        rw [hh']
        by_cases hle : t ≤ S
        · have : t = S := le_antisymm hle ht
          simp only [this, le_refl, if_true]
        · simp only [hle, if_false]
      · rw [hh']; simp
    have hgoal : ContinuousWithinAt h' (Set.Iic S ∪ Set.Ici S) S := hleft.union hright
    rw [Set.Iic_union_Ici, continuousWithinAt_univ] at hgoal
    exact hgoal

/-! ## 4. The local lift, on an interval `[α,β]`

This is `Submission.Work.OddBound.longHomotopy.exists_local_lift` with the interval `[0,S]` replaced
by an arbitrary interval `[α,β]`, `α < β`, and the hypothesis `h 0 = p` dropped (it is not used in
that proof).  It is needed to extend a partial lift beyond the supremum `T` when `h` is only
piecewise `C¹`: the piece containing `T` provides the `C¹` interval. -/

private lemma nhdsWithin_Icc_zero_eq' {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    𝓝[Set.Icc (0 : ℝ) a] 0 = 𝓝[Set.Icc (0 : ℝ) b] 0 := by
  have hcont : ∀ {c : ℝ}, 0 < c → Set.Icc (0 : ℝ) c ∈ 𝓝[Set.Ici (0 : ℝ)] 0 := by
    intro c hc
    refine Metric.mem_nhdsWithin_iff.mpr ⟨c / 2, by linarith, ?_⟩
    rintro t ⟨ht1, ht2⟩
    rw [Metric.mem_ball, Real.dist_eq] at ht1
    refine ⟨Set.mem_Ici.mp ht2, ?_⟩
    have := (abs_lt.mp ht1).2
    linarith
  have e1 : 𝓝[Set.Icc (0 : ℝ) a] 0 = 𝓝[Set.Ici (0 : ℝ)] 0 := by
    have h := nhdsWithin_inter_of_mem (hcont ha)
    rwa [show Set.Icc (0 : ℝ) a ∩ Set.Ici (0 : ℝ) = Set.Icc (0 : ℝ) a from
      by ext u; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]; tauto] at h
  have e2 : 𝓝[Set.Icc (0 : ℝ) b] 0 = 𝓝[Set.Ici (0 : ℝ)] 0 := by
    have h := nhdsWithin_inter_of_mem (hcont hb)
    rwa [show Set.Icc (0 : ℝ) b ∩ Set.Ici (0 : ℝ) = Set.Icc (0 : ℝ) b from
      by ext u; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]; tauto] at h
  rw [e1, e2]

private lemma symmL_trivializationAt_self_pw {p : M} (u : E) :
    (trivializationAt E (TangentSpace I) p).symmL ℝ p u = (show TangentSpace I p from u) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (𝕜 := ℝ) (b₀ := p) (b := p)
    (mem_chart_source H p)]
  exact tangentCoordChange_self (I := I) (x := p) (z := p) (v := u)
    (mem_extChartAt_source (I := I) p)

private lemma contDiffOn_tangentSpace_pw {p : M} {F : ℝ → E} {s : Set ℝ}
    (hF : ContDiffOn ℝ 1 F s) :
    ContDiffOn ℝ 1 (fun x : ℝ => (show TangentSpace I p from F x)) s := by
  have hcm : ContDiff ℝ 1
      (fun u : E => (trivializationAt E (TangentSpace I) p).symmL ℝ p u) :=
    ContinuousLinearMap.contDiff ((trivializationAt E (TangentSpace I) p).symmL ℝ p)
  have h1 : ContDiffOn ℝ 1
      (fun x : ℝ => (trivializationAt E (TangentSpace I) p).symmL ℝ p (F x)) s :=
    hcm.comp_contDiffOn hF
  refine h1.congr (fun x _ => ?_)
  show (show TangentSpace I p from F x)
    = (trivializationAt E (TangentSpace I) p).symmL ℝ p (F x)
  rw [symmL_trivializationAt_self_pw (I := I) (p := p) (u := F x)]

private lemma curveLength_congr_of_eventuallyEq_pw {u v : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (huv : ∀ t ∈ Set.Ioo a b, u =ᶠ[𝓝 t] v) :
    curveLength (I := I) u a b = curveLength (I := I) v a b := by
  rw [Submission.Length.curveLength_def, Submission.Length.curveLength_def]
  refine intervalIntegral.integral_congr_Ioo_of_le hab (fun t ht => ?_)
  exact Submission.GeodesicSpeed.curveSpeed_congr_of_eventuallyEq (I := I) (huv t ht)

private lemma isInvertible_mfderiv_GExp_of_norm_lt_pw
    [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    {p : M} {v : TangentSpace I p} (hv : ‖v‖ < Real.pi / Real.sqrt K) :
    (mfderiv 𝓘(ℝ, E) I
      (fun u : E => GExp (cov := cov) hmet p (show TangentSpace I p from u))
      (show E from v)).IsInvertible := by
  rcases eq_or_ne v 0 with hv0 | hv0
  · subst hv0
    change (mfderiv 𝓘(ℝ, E) I
      (fun u : E => GExp (cov := cov) hmet p (show TangentSpace I p from u))
      (0 : E)).IsInvertible
    rw [Submission.GExpLocalInj.mfderiv_GExp_zero (cov := cov) hmet p]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  · exact Submission.ConjCut.isInvertible_mfderiv_GExp_of_norm_lt_pi_div_sqrt
      (cov := cov) hmet htor hcurv hK hv0 hv

theorem exists_local_lift_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    {p : M} {h : ℝ → M} {α β t : ℝ} (hαβ : α < β)
    (hc : ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc α β))
    (ht : t ∈ Set.Icc α β) (htβ : t < β)
    {v : TangentSpace I p} (hv : ‖v‖ < Real.pi / Real.sqrt K)
    (hvt : GExp (cov := cov) hmet p v = h t)
    (hGauss : ∀ (v η : TangentSpace I p) (u : ℝ),
      Inner.inner ℝ
        (curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet p (u • (v + r • η))) 0)
        (curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • v)) u)
        = u * Inner.inner ℝ η v)
    (hD2 : ∀ {W : ℝ → TangentSpace I p} {a b : ℝ}, a ≤ b → ContDiffOn ℝ 1 W (Set.Icc a b) →
      ‖W b‖ ≤ ‖W a‖ + curveLength (I := I)
        (fun s : ℝ => GExp (cov := cov) hmet p (W s)) a b) :
    ∃ t' : ℝ, t < t' ∧ t' ≤ β ∧ ∃ W : ℝ → TangentSpace I p,
      ContinuousOn W (Set.Icc t t') ∧ W t = v ∧
      (∀ s ∈ Set.Icc t t', GExp (cov := cov) hmet p (W s) = h s) ∧
      (∀ s ∈ Set.Icc t t', ‖W s‖ ≤ ‖v‖ + curveLength (I := I) h t s) := by
  classical
  -- ## Step 1: the differential of the exponential map at `v` is invertible, and `GExp p` is a
  -- local diffeomorphism there
  have hinv := isInvertible_mfderiv_GExp_of_norm_lt_pw (cov := cov) hmet htor hK hcurv
    (p := p) (v := v) hv
  have hf : IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞
      (Submission.XuLift.gexpMap (cov := cov) hmet p) (show E from v) :=
    Submission.XuLift.isLocalDiffeomorphAt_GExp (cov := cov) hmet p hinv
  -- ## Step 2: `h t` lies in the source of the local inverse
  have hsrc : h t ∈ hf.localInverse.source := by
    rw [← hvt]
    exact hf.localInverse_mem_source
  -- ## Step 3: a right-neighbourhood of `t` on which `h` stays in the source
  have hmem : {s : ℝ | h s ∈ hf.localInverse.source} ∈ 𝓝[Set.Icc α β] t :=
    (hc.continuousOn.continuousWithinAt ht).preimage_mem_nhdsWithin
      (hf.localInverse.open_source.mem_nhds hsrc)
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhdsWithin_iff.mp hmem
  set t' : ℝ := min (t + ε / 2) ((t + β) / 2) with ht'def
  have htt' : t < t' := by
    rw [ht'def]; exact lt_min (by linarith) (by linarith)
  have ht'β : t' ≤ β := by
    rw [ht'def]; exact le_trans (min_le_right _ _) (by linarith)
  have hsub : ∀ s ∈ Set.Icc t t', h s ∈ hf.localInverse.source := by
    intro s hs
    refine hεsub ⟨?_, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hs.1, hεpos], by
        have h2 : t' ≤ t + ε / 2 := by rw [ht'def]; exact min_le_left _ _
        linarith [hs.2, h2, hεpos]⟩
    · exact ⟨le_trans ht.1 hs.1, le_trans hs.2 ht'β⟩
  -- ## Step 4: the lift
  let W : ℝ → TangentSpace I p := fun s => (show TangentSpace I p from hf.localInverse (h s))
  have hWt : W t = v := by
    show (show TangentSpace I p from hf.localInverse (h t)) = v
    rw [← hvt]
    exact congrArg (fun u : E => (show TangentSpace I p from u))
      (hf.localInverse_left_inv (x' := (show E from v)) hf.localInverse_mem_target)
  have hWG : ∀ s ∈ Set.Icc t t', GExp (cov := cov) hmet p (W s) = h s := by
    intro s hs
    exact hf.localInverse_right_inv (hsub s hs)
  have hWc : ContinuousOn W (Set.Icc t t') := by
    have hcontΨ : ContinuousOn (fun y : M => hf.localInverse y) hf.localInverse.source :=
      hf.localInverse_contMDiffOn.continuousOn
    have h1 : ContinuousOn (fun s : ℝ => hf.localInverse (h s)) (Set.Icc t t') :=
      hcontΨ.comp (hc.continuousOn.mono (fun u hu => ⟨le_trans ht.1 hu.1, le_trans hu.2 ht'β⟩))
        (fun u hu => hsub u hu)
    exact h1
  have hWcd : ContDiffOn ℝ 1 W (Set.Icc t t') := by
    have hΨ1 : ContMDiffOn I 𝓘(ℝ, E) 1 (fun y : M => hf.localInverse y)
        hf.localInverse.source :=
      hf.localInverse_contMDiffOn.of_le
        (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from WithTop.coe_le_coe.mpr le_top)
    have hhc : ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc t t') :=
      hc.mono (fun u hu => ⟨le_trans ht.1 hu.1, le_trans hu.2 ht'β⟩)
    have hcomp : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 (fun u : ℝ => hf.localInverse (h u))
        (Set.Icc t t') :=
      hΨ1.comp hhc (fun u hu => hsub u hu)
    have hcd : ContDiffOn ℝ 1 (fun u : ℝ => hf.localInverse (h u)) (Set.Icc t t') :=
      hcomp.contDiffOn
    exact contDiffOn_tangentSpace_pw (p := p) hcd
  refine ⟨t', htt', ht'β, W, hWc, hWt, hWG, ?_⟩
  -- ## Step 5: the radial estimate
  intro s hs
  have hts : t ≤ s := hs.1
  have hWcd' : ContDiffOn ℝ 1 W (Set.Icc t s) :=
    hWcd.mono (Set.Icc_subset_Icc_right hs.2)
  have hb := hD2 hts hWcd'
  have hlen : curveLength (I := I)
      (fun u : ℝ => GExp (cov := cov) hmet p (W u)) t s = curveLength (I := I) h t s := by
    refine curveLength_congr_of_eventuallyEq_pw (I := I) hts (fun u hu => ?_)
    have hmem' : Set.Ioo t t' ∈ 𝓝 u :=
      isOpen_Ioo.mem_nhds ⟨hu.1, lt_of_lt_of_le hu.2 hs.2⟩
    filter_upwards [hmem'] with u' hu''
    exact hWG u' ⟨hu''.1.le, hu''.2.le⟩
  rw [hlen, hWt] at hb
  exact hb

/-! ## 5. The piecewise lifting lemma -/

theorem exists_lift_of_piecewise_short
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    {p : M} {h : ℝ → M} {S : ℝ} (hS : 0 < S) {k : ℕ} {a : Fin (k + 1) → ℝ}
    (hamono : StrictMono a) (ha0 : a 0 = 0) (haS : a (Fin.last k) = S)
    (hc : ContinuousOn h (Set.Icc (0 : ℝ) S))
    (hpiece : ∀ j : Fin k, ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc (a j.castSucc) (a j.succ)))
    (h0 : h 0 = p)
    (hlen : Submission.Length.curveLength (I := I) h 0 S < Real.pi / Real.sqrt K) :
    ∃ W : ℝ → TangentSpace I p, ContinuousOn W (Set.Icc (0 : ℝ) S) ∧ W 0 = 0 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) S,
        Submission.GlobalExp.GExp (cov := cov) hmet p (W s) = h s) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) S, ‖W s‖ ≤ Submission.Length.curveLength (I := I) h 0 s) := by
  classical
  -- ## 0. Setup
  set R : ℝ := Real.pi / Real.sqrt K with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]; exact div_pos Real.pi_pos (Real.sqrt_pos.mpr hK)
  set ℓ : ℝ → ℝ := fun s => Submission.Length.curveLength (I := I) h 0 s with hℓdef
  have hℓ0 : ℓ 0 = 0 := by
    rw [hℓdef]; exact Submission.Length.curveLength_self (I := I) h 0
  have hℓS : ℓ S < R := by rw [hℓdef, hRdef]; exact hlen
  have hintI : ∀ c d : ℝ, 0 ≤ c → c ≤ d → d ≤ S →
      IntervalIntegrable (curveSpeed (I := I) h) MeasureTheory.volume c d :=
    intervalIntegrable_curveSpeed_piecewise (I := I) (h := h) (S := S) (k := k) (a := a)
      hamono ha0 haS hpiece
  have hℓmono : ∀ {c d : ℝ}, 0 ≤ c → c ≤ d → d ≤ S → ℓ c ≤ ℓ d := by
    intro c d hc0 hcd hdS
    rw [hℓdef]
    exact curveLength_mono_piecewise (I := I) (h := h) (S := S) (k := k) (a := a)
      hamono ha0 haS hpiece c d hc0 hcd hdS
  have hℓadd : ∀ {c d : ℝ}, 0 ≤ c → c ≤ d → d ≤ S →
      ℓ c + Submission.Length.curveLength (I := I) h c d = ℓ d := by
    intro c d hc0 hcd hdS
    rw [hℓdef]
    exact curveLength_add_piecewise (I := I) (h := h) (S := S) (k := k) (a := a)
      hamono ha0 haS hpiece hc0 hcd hdS
  have haS' : ∀ j : Fin k, a j.succ ≤ S := fun j => by
    rw [← haS]; exact hamono.monotone (Fin.le_last j.succ)
  have hGaussAll : ∀ (v η : TangentSpace I p) (t : ℝ),
      Inner.inner ℝ
        (curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet p (t • (v + r • η))) 0)
        (curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • v)) t)
      = t * Inner.inner ℝ η v :=
    fun v η t => Work.OddBound.longHomotopy.gauss_pairing_fibre (cov := cov) (p := p) (v := v)
      (η := η) hmet htor t
  have hD2 : ∀ {W : ℝ → TangentSpace I p} {a b : ℝ}, a ≤ b → ContDiffOn ℝ 1 W (Set.Icc a b) →
      ‖W b‖ ≤ ‖W a‖ + curveLength (I := I)
        (fun s : ℝ => GExp (cov := cov) hmet p (W s)) a b :=
    fun {W} {a} {b} hab hW =>
      Work.OddBound.longHomotopy.radial_estimate_of_lift (cov := cov) (p := p) (W := W) hmet htor
        hab hW hGaussAll
  let Good : ℝ → Prop := fun t => ∃ W : ℝ → TangentSpace I p,
      ContinuousOn W (Set.Icc (0:ℝ) t) ∧ W 0 = 0 ∧
      (∀ s ∈ Set.Icc (0:ℝ) t, GExp (cov := cov) hmet p (W s) = h s) ∧
      (∀ s ∈ Set.Icc (0:ℝ) t, ‖W s‖ ≤ ℓ s)
  have hGood0 : Good 0 := by
    refine ⟨fun _ => 0, continuousOn_const, rfl, ?_, ?_⟩
    · intro s hs
      have hs0 : s = 0 := le_antisymm hs.2 hs.1
      rw [hs0, h0, Submission.GlobalExp.GExp_zero]
    · intro s hs
      have hs0 : s = 0 := le_antisymm hs.2 hs.1
      rw [hs0, norm_zero, hℓ0]
  have hDown : ∀ {t t' : ℝ}, Good t → 0 ≤ t' → t' ≤ t → Good t' := by
    intro t t' ht ht'0 ht't
    obtain ⟨W, hWc, hW0, hWG, hWb⟩ := ht
    exact ⟨W, hWc.mono (fun s hs => ⟨hs.1, le_trans hs.2 ht't⟩), hW0,
      fun s hs => hWG s ⟨hs.1, le_trans hs.2 ht't⟩,
      fun s hs => hWb s ⟨hs.1, le_trans hs.2 ht't⟩⟩
  -- ## 1. Maximal interval
  set Gset : Set ℝ := {t | t ∈ Set.Icc (0:ℝ) S ∧ Good t} with hGsetdef
  have h0mem : (0:ℝ) ∈ Gset := by
    rw [hGsetdef]; exact ⟨⟨le_refl 0, hS.le⟩, hGood0⟩
  have hGset_ne : Gset.Nonempty := ⟨0, h0mem⟩
  have hGset_bdd : BddAbove Gset := ⟨S, fun t ht => (by rw [hGsetdef] at ht; exact ht.1.2)⟩
  set T : ℝ := sSup Gset with hTdef
  have hT0 : 0 ≤ T := by rw [hTdef]; exact le_csSup hGset_bdd h0mem
  have hTS : T ≤ S := by
    rw [hTdef]
    exact csSup_le hGset_ne (fun t ht => (by rw [hGsetdef] at ht; exact ht.1.2))
  have hTpos_or : 0 < T ∨ T = 0 := (lt_or_eq_of_le hT0).elim Or.inl (fun h => Or.inr h.symm)
  -- ## 2. `Good T`
  have hGT : Good T := by
    rcases hTpos_or with hTpos | hT_eq0
    swap
    · rw [hT_eq0]; exact hGood0
    have hlt : ∀ t : ℝ, 0 ≤ t → t < T → Good t := by
      intro t ht0 htT
      obtain ⟨t', ht'G, htt'⟩ := exists_lt_of_lt_csSup hGset_ne htT
      rw [hGsetdef] at ht'G
      exact hDown ht'G.2 ht0 htt'.le
    let Wf : ℝ → ℝ → TangentSpace I p :=
      fun t => if h : Good t then Classical.choose h else 0
    have hWf_spec : ∀ (t : ℝ) (ht : Good t),
        ContinuousOn (Wf t) (Set.Icc (0:ℝ) t) ∧ (Wf t) 0 = 0 ∧
        (∀ s ∈ Set.Icc (0:ℝ) t, GExp (cov := cov) hmet p ((Wf t) s) = h s) ∧
        (∀ s ∈ Set.Icc (0:ℝ) t, ‖(Wf t) s‖ ≤ ℓ s) := by
      intro t ht
      have hval : Wf t = Classical.choose ht := by
        simp only [Wf]
        rw [dif_pos ht]
      rw [hval]
      exact Classical.choose_spec ht
    have hbnd : ∀ (t : ℝ) (ht : t < T) (u : ℝ), 0 ≤ u → u ≤ t → ‖(Wf t) u‖ < R := by
      intro t ht u hu0 hut
      have ht0 : 0 ≤ t := le_trans hu0 hut
      exact lt_of_le_of_lt ((hWf_spec t (hlt t ht0 ht)).2.2.2 u ⟨hu0, hut⟩)
        (lt_of_le_of_lt (hℓmono hu0 (le_trans hut (le_trans ht.le hTS)) le_rfl) hℓS)
    have hagree : ∀ t₁ t₂ : ℝ, t₁ < T → t₂ < T → t₁ ≤ t₂ →
        ∀ s ∈ Set.Icc (0:ℝ) t₁, (Wf t₁) s = (Wf t₂) s := by
      intro t₁ t₂ h₁ h₂ hle s hs
      have hG₁ : Good t₁ := hlt t₁ (le_trans hs.1 hs.2) h₁
      have hG₂ : Good t₂ := hlt t₂ (le_trans hs.1 (le_trans hs.2 hle)) h₂
      obtain ⟨hc₁, h0₁, hG₁', hb₁⟩ := hWf_spec t₁ hG₁
      obtain ⟨hc₂, h0₂, hG₂', hb₂⟩ := hWf_spec t₂ hG₂
      exact Work.OddBound.longHomotopy.lift_eqOn_of_agrees (K := K) hK hcurv hmet htor (a := 0)
        (b := t₁) (le_trans hs.1 hs.2)
        hc₁ (hc₂.mono (Set.Icc_subset_Icc_right hle))
        hG₁' (fun u hu => hG₂' u ⟨hu.1, le_trans hu.2 hle⟩)
        (fun u hu => hbnd t₁ h₁ u hu.1 hu.2)
        (fun u hu => hbnd t₂ h₂ u hu.1 (le_trans hu.2 hle))
        (by rw [h0₁, h0₂]) s hs
    let Ww : ℝ → TangentSpace I p := fun s => (Wf s) s
    have hWw_eq : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < T → Ww s = (Wf t) s := by
      intro s t hs0 hst htT
      have hGs : Good s := hlt s hs0 (lt_of_le_of_lt hst htT)
      have hGt : Good t := hlt t (le_trans hs0 hst) htT
      show (Wf s) s = (Wf t) s
      exact hagree s t (lt_of_le_of_lt hst htT) htT hst s ⟨hs0, le_refl s⟩
    have hWw_cont : ContinuousOn Ww (Set.Ioo (0:ℝ) T) := by
      rw [IsOpen.continuousOn_iff isOpen_Ioo]
      intro s₀ hs₀
      obtain ⟨t, hs₀t, htT⟩ := exists_between hs₀.2
      have ht0 : 0 < t := lt_trans hs₀.1 hs₀t
      have hev : Ww =ᶠ[𝓝 s₀] (Wf t) := by
        have hδ : 0 < min s₀ (t - s₀) := lt_min hs₀.1 (by linarith)
        filter_upwards [Metric.ball_mem_nhds s₀ hδ] with s hs
        rw [Metric.mem_ball, Real.dist_eq] at hs
        have hs1 : 0 < s := by
          have := (abs_lt.mp hs).1
          have hle : min s₀ (t - s₀) ≤ s₀ := min_le_left _ _
          linarith
        have hs2 : s < t := by
          have := (abs_lt.mp hs).2
          have hle : min s₀ (t - s₀) ≤ t - s₀ := min_le_right _ _
          linarith
        exact hWw_eq s t hs1.le hs2.le htT
      exact ContinuousAt.congr
        ((hWf_spec t (hlt t ht0.le htT)).1.continuousAt
          (Filter.mem_of_superset (isOpen_Ioo.mem_nhds ⟨hs₀.1, hs₀t⟩)
            (fun u hu => ⟨hu.1.le, hu.2.le⟩)))
        hev.symm
    have hWw_G : ∀ s ∈ Set.Ioo (0:ℝ) T, GExp (cov := cov) hmet p (Ww s) = h s := by
      intro s hs
      have hGs : Good s := hlt s hs.1.le hs.2
      show GExp (cov := cov) hmet p ((Wf s) s) = h s
      exact (hWf_spec s hGs).2.2.1 s ⟨hs.1.le, le_refl s⟩
    have hWw_b : ∀ s ∈ Set.Ioo (0:ℝ) T, ‖Ww s‖ ≤ ℓ s := by
      intro s hs
      have hGs : Good s := hlt s hs.1.le hs.2
      show ‖(Wf s) s‖ ≤ ℓ s
      exact (hWf_spec s hGs).2.2.2 s ⟨hs.1.le, le_refl s⟩
    -- ## 3. the limit at `T`
    set H : ℝ → M := fun t => if t ≤ S then h t else h S with hHdef
    have hHcont : ContinuousAt H T := by
      rw [hHdef]
      exact continuousAt_trunc_of_continuousOn hc hS hTpos hTS
    have hHmem : ∀ s ∈ Set.Ioo (0:ℝ) T, Ww s ∈ Metric.closedBall (0 : TangentSpace I p) (ℓ S) := by
      intro s hs
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_trans (hWw_b s hs) (hℓmono hs.1.le (le_trans hs.2.le hTS) le_rfl)
    have hHWG : ∀ s ∈ Set.Ioo (0:ℝ) T, GExp (cov := cov) hmet p (Ww s) = H s := by
      intro s hs
      have hsS : s < S := lt_of_lt_of_le hs.2 hTS
      rw [hHdef]
      simp only [hsS.le, if_true]
      exact hWw_G s hs
    obtain ⟨v, hvlim⟩ := Work.OddBound.longHomotopy.exists_tendsto_of_lift (cov := cov) (p := p)
      (h := H) (T := T) (a := 0)
      hmet htor hK hcurv (hρ := by rw [hRdef] at hℓS; exact hℓS) hTpos hHcont
      hWw_cont hHmem hHWG
    have hneT : (𝓝[<] T).NeBot := by
      rw [nhdsWithin_neBot]
      intro t ht
      obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp ht
      refine ⟨T - ε/2, hsub ?_, ?_⟩
      · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith
      · simp only [Set.mem_Iio]; linarith
    have hpos : ∀ᶠ s in (𝓝[<] T), 0 < s := by
      have hmem : Set.Ioi (0:ℝ) ∈ 𝓝[Set.Iio T] T := by
        refine Metric.mem_nhdsWithin_iff.mpr ⟨T/2, by linarith, ?_⟩
        rintro t ⟨ht1, ht2⟩
        rw [Metric.mem_ball, Real.dist_eq] at ht1
        have := (abs_lt.mp ht1).1
        simp only [Set.mem_Ioi]
        linarith
      filter_upwards [hmem] with s hs
      exact hs
    have hltT : ∀ᶠ s in (𝓝[<] T), s < T := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact hs
    have hHh : H T = h T := by
      rw [hHdef]; simp only [hTS, if_true]
    have hGv : GExp (cov := cov) hmet p v = h T := by
      have hGcont : Tendsto (fun w : TangentSpace I p => GExp (cov := cov) hmet p w) (𝓝 v)
          (𝓝 (GExp (cov := cov) hmet p v)) :=
        (Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet p v).continuousAt
      have h2 : Tendsto (fun s : ℝ => GExp (cov := cov) hmet p (Ww s)) (𝓝[<] T)
          (𝓝 (GExp (cov := cov) hmet p v)) := hGcont.comp hvlim
      have h4 : Tendsto (fun s : ℝ => GExp (cov := cov) hmet p (Ww s)) (𝓝[<] T) (𝓝 (h T)) := by
        have h5 : Tendsto (fun s : ℝ => GExp (cov := cov) hmet p (Ww s)) (𝓝[<] T) (𝓝 (H T)) :=
          (hHcont.tendsto.mono_left nhdsWithin_le_nhds).congr'
            (by filter_upwards [hpos, hltT] with s hs0 hsT
                exact (hHWG s ⟨hs0, hsT⟩).symm)
        rw [hHh] at h5
        exact h5
      exact tendsto_nhds_unique h2 h4
    have hvb : ‖v‖ ≤ ℓ T := by
      have h1 : Tendsto (fun s : ℝ => ‖Ww s‖) (𝓝[<] T) (𝓝 ‖v‖) :=
        (tendsto_norm (x := v)).comp hvlim
      have h2 : ∀ᶠ s in (𝓝[<] T), ‖Ww s‖ ≤ ℓ T := by
        filter_upwards [hpos, hltT] with s hs0 hsT
        exact le_trans (hWw_b s ⟨hs0, hsT⟩) (hℓmono hs0.le hsT.le hTS)
      exact le_of_tendsto h1 h2
    -- ## 4. assembling `Good T`
    have hcont0 : ContinuousWithinAt Ww (Set.Icc (0:ℝ) T) 0 := by
      have hhalf : (0:ℝ) < T/2 := by linarith
      have hev2 : Ww =ᶠ[𝓝[Set.Icc (0:ℝ) T] (0:ℝ)] (Wf (T/2)) := by
        have hmem : Set.Iio (T/2) ∈ 𝓝[Set.Icc (0:ℝ) T] (0:ℝ) := by
          refine Metric.mem_nhdsWithin_iff.mpr ⟨T/4, by linarith, ?_⟩
          rintro u ⟨hu1, hu2⟩
          rw [Metric.mem_ball, Real.dist_eq] at hu1
          have := (abs_lt.mp hu1).2
          simp only [Set.mem_Iio]
          linarith
        filter_upwards [self_mem_nhdsWithin, hmem] with u hu hu2
        exact hWw_eq u (T/2) hu.1 hu2.le (by linarith)
      refine ContinuousWithinAt.congr_of_eventuallyEq ?_ hev2 ?_
      · show Tendsto (Wf (T/2)) (𝓝[Set.Icc (0:ℝ) T] (0:ℝ)) (𝓝 ((Wf (T/2)) 0))
        rw [← nhdsWithin_Icc_zero_eq' hhalf hTpos]
        exact (hWf_spec (T/2) (hlt (T/2) hhalf.le (by linarith))).1.continuousWithinAt
          ⟨le_refl 0, by linarith⟩
      · show Ww 0 = (Wf (T/2)) 0
        rw [show Ww 0 = (Wf 0) 0 from rfl, (hWf_spec 0 hGood0).2.1,
          (hWf_spec (T/2) (hlt (T/2) hhalf.le (by linarith))).2.1]
    have hWwIco : ContinuousOn Ww (Set.Icc (0:ℝ) T ∩ {u : ℝ | u < T}) := by
      intro s hs
      by_cases hs0 : s = 0
      · subst hs0
        exact hcont0.mono (fun u hu => hu.1)
      · exact (hWw_cont.continuousAt (isOpen_Ioo.mem_nhds
          ⟨lt_of_le_of_ne hs.1.1 (fun h => hs0 h.symm), hs.2⟩)).continuousWithinAt
    refine ⟨fun s => if s < T then Ww s else v, ?_, ?_, ?_, ?_⟩
    · refine ContinuousOn.if' ?_ ?_ hWwIco ?_
      · intro a ha
        have haT : a = T := by
          have h1 : a ∈ frontier (Set.Iio T) := ha.2
          rw [frontier_Iio] at h1
          simpa using h1
        subst haT
        simp only [lt_irrefl, if_false]
        exact hvlim.mono_left (nhdsWithin_mono T (fun u hu => hu.2))
      · intro a ha
        have haT : a = T := by
          have h1 : a ∈ frontier (Set.Iio T) := ha.2
          rw [frontier_Iio] at h1
          simpa using h1
        subst haT
        simp only [lt_irrefl, if_false]
        exact tendsto_const_nhds
      · have hset : Set.Icc (0:ℝ) T ∩ {u : ℝ | ¬ u < T} = {T} := by
          ext u
          simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
          constructor
          · rintro ⟨⟨h1, h2⟩, h3⟩
            exact le_antisymm h2 (not_lt.mp h3)
          · rintro rfl
            exact ⟨⟨hT0, le_refl T⟩, lt_irrefl T⟩
        rw [hset]
        exact continuousOn_const
    · show (if (0:ℝ) < T then Ww 0 else v) = 0
      rw [if_pos hTpos, show Ww 0 = (Wf 0) 0 from rfl, (hWf_spec 0 hGood0).2.1]
    · intro s hs
      show GExp (cov := cov) hmet p (if s < T then Ww s else v) = h s
      by_cases hcase : s < T
      · rw [if_pos hcase]
        by_cases hs0 : s = 0
        · subst hs0
          rw [show Ww 0 = (Wf 0) 0 from rfl, (hWf_spec 0 hGood0).2.1, h0,
            Submission.GlobalExp.GExp_zero]
        · exact hWw_G s ⟨lt_of_le_of_ne hs.1 (fun h => hs0 h.symm), hcase⟩
      · have hsT : s = T := le_antisymm hs.2 (not_lt.mp hcase)
        rw [if_neg hcase, hsT]
        exact hGv
    · intro s hs
      show ‖(if s < T then Ww s else v)‖ ≤ ℓ s
      by_cases hcase : s < T
      · rw [if_pos hcase]
        by_cases hs0 : s = 0
        · subst hs0
          rw [show Ww 0 = (Wf 0) 0 from rfl, (hWf_spec 0 hGood0).2.1, norm_zero, hℓ0]
        · exact hWw_b s ⟨lt_of_le_of_ne hs.1 (fun h => hs0 h.symm), hcase⟩
      · have hsT : s = T := le_antisymm hs.2 (not_lt.mp hcase)
        rw [if_neg hcase, hsT]
        exact hvb
  -- ## 5. `T = S` and the conclusion
  have hTS' : T = S := by
    by_contra hne
    have hltTS : T < S := lt_of_le_of_ne hTS hne
    obtain ⟨W, hWc, hW0, hWG, hWb⟩ := hGT
    have hTmem : T ∈ Set.Icc (0:ℝ) S := ⟨hT0, hTS⟩
    have hvR : ‖W T‖ < R :=
      lt_of_le_of_lt (hWb T ⟨hT0, le_refl T⟩) (lt_of_le_of_lt (hℓmono hT0 hTS le_rfl) hℓS)
    have hvT : GExp (cov := cov) hmet p (W T) = h T := hWG T ⟨hT0, le_refl T⟩
    obtain ⟨j, hjle, hjlt⟩ :=
      exists_piece_index (T := T) (a := a) hamono (by rw [ha0]; exact hT0) (by rw [haS]; exact hltTS)
    have hpcβ : a j.castSucc < a j.succ := hamono (Fin.castSucc_lt_succ_iff.mpr le_rfl)
    obtain ⟨t', hTt', ht'β, W', hW'c, hW'T, hW'G, hW'b⟩ :=
      exists_local_lift_Icc (cov := cov) (p := p) (h := h) (α := a j.castSucc) (β := a j.succ)
        (t := T) hmet htor hK hcurv hpcβ (hpiece j) ⟨hjle, hjlt.le⟩ hjlt
        (by rw [hRdef] at hvR; exact hvR) hvT hGaussAll hD2
    have ht'S : t' ≤ S := le_trans ht'β (haS' j)
    have hGood' : Good t' := by
      refine ⟨fun s => if s < T then W s else W' s, ?_, ?_, ?_, ?_⟩
      · have hsetR : Set.Icc (0:ℝ) t' ∩ {u : ℝ | ¬ u < T} = Set.Icc T t' := by
          ext u
          simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_setOf_eq]
          constructor
          · rintro ⟨⟨h1, h2⟩, h3⟩
            exact ⟨not_lt.mp h3, h2⟩
          · rintro ⟨h1, h2⟩
            exact ⟨⟨le_trans hT0 h1, h2⟩, not_lt.mpr h1⟩
        refine ContinuousOn.if' ?_ ?_ ?_ ?_
        · intro a ha
          have haT : a = T := by
            have h1 : a ∈ frontier (Set.Iio T) := ha.2
            rw [frontier_Iio] at h1
            simpa using h1
          subst haT
          simp only [lt_irrefl, if_false]
          rw [hW'T]
          exact (hWc.continuousWithinAt ⟨hT0, le_refl T⟩).mono_left
            (nhdsWithin_mono T (fun u hu => ⟨hu.1.1, hu.2.le⟩))
        · intro a ha
          have haT : a = T := by
            have h1 : a ∈ frontier (Set.Iio T) := ha.2
            rw [frontier_Iio] at h1
            simpa using h1
          subst haT
          simp only [lt_irrefl, if_false]
          rw [hsetR]
          exact hW'c.continuousWithinAt ⟨le_refl T, hTt'.le⟩
        · have hsub : Set.Icc (0:ℝ) t' ∩ {u : ℝ | u < T} ⊆ Set.Icc (0:ℝ) T :=
            fun u hu => ⟨hu.1.1, hu.2.le⟩
          exact hWc.mono hsub
        · rw [hsetR]
          exact hW'c
      · show (if (0:ℝ) < T then W 0 else W' 0) = 0
        by_cases h0T : (0:ℝ) < T
        · rw [if_pos h0T]
          exact hW0
        · have hT_eq0 : T = 0 := le_antisymm (not_lt.mp h0T) hT0
          have h1 : W' 0 = W T := by rw [show (0:ℝ) = T from hT_eq0.symm, hW'T]
          rw [if_neg h0T, h1]
          rw [hT_eq0]
          exact hW0
      · intro s hs
        show GExp (cov := cov) hmet p (if s < T then W s else W' s) = h s
        by_cases hcase : s < T
        · rw [if_pos hcase]
          exact hWG s ⟨hs.1, hcase.le⟩
        · rw [if_neg hcase]
          exact hW'G s ⟨not_lt.mp hcase, hs.2⟩
      · intro s hs
        show ‖(if s < T then W s else W' s)‖ ≤ ℓ s
        by_cases hcase : s < T
        · rw [if_pos hcase]
          exact hWb s ⟨hs.1, hcase.le⟩
        · rw [if_neg hcase]
          have hsT : T ≤ s := not_lt.mp hcase
          have hb1 : ‖W' s‖ ≤ ‖W T‖ + curveLength (I := I) h T s := hW'b s ⟨hsT, hs.2⟩
          have hb2 : ‖W T‖ ≤ ℓ T := hWb T ⟨hT0, le_refl T⟩
          have hadd : curveLength (I := I) h T s = ℓ s - ℓ T := by
            have hsum := hℓadd (c := T) (d := s) hT0 hsT (le_trans hs.2 ht'S)
            linarith
          rw [hadd] at hb1
          linarith
    have hmem' : t' ∈ Gset := by
      rw [hGsetdef]
      exact ⟨⟨le_of_lt (lt_of_le_of_lt hT0 hTt'), ht'S⟩, hGood'⟩
    have hle : t' ≤ T := le_csSup hGset_bdd hmem'
    linarith
  rw [hTS'] at hGT
  obtain ⟨W, hWc, hW0, hWG, hWb⟩ := hGT
  refine ⟨W, hWc, hW0, hWG, ?_⟩
  intro s hs
  rw [hℓdef] at hWb
  exact hWb s hs

end Work.OddBound.liftPiecewise
