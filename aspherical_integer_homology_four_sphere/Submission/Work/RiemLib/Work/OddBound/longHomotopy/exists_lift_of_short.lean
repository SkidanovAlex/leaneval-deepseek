import Mathlib
import Submission.Work.RiemLib.RauchK
import Submission.Work.RiemLib.Geodesic
import Submission.Work.RiemLib.GeodesicSpeed
import Submission.Work.RiemLib.Length
import Submission.Work.RiemLib.Distance
import Submission.Work.RiemLib.InjRadius
import Submission.Work.RiemLib.InjBall
import Submission.Work.RiemLib.SegmentDomain
import Submission.Work.RiemLib.XuMain
import Submission.Work.RiemLib.EDist
import Submission.Work.RiemLib.GExpRay2
import Submission.Work.RiemLib.GExpJoint
import Submission.Work.RiemLib.GExpFlow
import Submission.Work.RiemLib.Commons.Geometry.Manifold.exists_finite_cover_isCompact_subset_chartAt
import Submission.Work.RiemLib.GeodesicGlobal
import Submission.Work.RiemLib.GExpLocalInj
import Submission.Work.RiemLib.CutStep2
import Submission.Work.RiemLib.XuLift
import Submission.Work.RiemLib.ChartPieces
import Submission.Work.RiemLib.ChartIndep
import Submission.Work.RiemLib.CoeffSmooth2
import Submission.Work.RiemLib.JacobiGlobal
import Submission.Work.RiemLib.Commons.Analysis.ODE.exists_linearODE_solution_Icc
import Submission.Work.RiemLib.IndexCorner2
import Submission.Work.RiemLib.InjHalf
import Submission.Work.RiemLib.LensLoop
import Submission.Work.RiemLib.UniformInj
import Submission.Work.RiemLib.ConjRadius
import Submission.Work.RiemLib.ConjCut
import Submission.Work.RiemLib.SingularConj
import Submission.Work.RiemLib.RayConj
import Submission.Work.RiemLib.Gauss
import Submission.Work.RiemLib.ExpBound2
import Submission.Work.RiemLib.JacobiGauss
import Submission.Work.RiemLib.Minimal
import Submission.Work.RiemLib.Work.OddBound.longHomotopy.lift_of_geodesic_ray
import Submission.Work.RiemLib.Work.OddBound.longHomotopy.curveLength_toolkit
import Submission.Work.RiemLib.Work.OddBound.longHomotopy.exists_local_lift
import Submission.Work.RiemLib.Work.OddBound.longHomotopy.exists_tendsto_of_lift
import Submission.Work.RiemLib.Work.OddBound.longHomotopy.gauss_pairing_fibre
import Submission.Work.RiemLib.Work.OddBound.longHomotopy.radial_estimate_of_lift

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 3000000

namespace Work.OddBound.longHomotopy

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open LeanEval.Geometry.SphereTheorem Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length Submission.InjRadius

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

/-! ## Uniqueness of lifts on a common interval -/

/-- **Two continuous lifts of the same curve under `GExp p`, whose values stay in the open ball of
radius `π/√K` and which agree at the left endpoint, agree everywhere.** -/
theorem lift_eqOn_of_agrees {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {h : ℝ → M} {W₁ W₂ : ℝ → TangentSpace I p} {a b : ℝ} (hab : a ≤ b)
    (h₁ : ContinuousOn W₁ (Set.Icc a b)) (h₂ : ContinuousOn W₂ (Set.Icc a b))
    (hG₁ : ∀ s ∈ Set.Icc a b, GExp (cov := cov) hmet p (W₁ s) = h s)
    (hG₂ : ∀ s ∈ Set.Icc a b, GExp (cov := cov) hmet p (W₂ s) = h s)
    (hb₁ : ∀ s ∈ Set.Icc a b, ‖W₁ s‖ < Real.pi / Real.sqrt K)
    (hb₂ : ∀ s ∈ Set.Icc a b, ‖W₂ s‖ < Real.pi / Real.sqrt K)
    (ha : W₁ a = W₂ a) :
    ∀ s ∈ Set.Icc a b, W₁ s = W₂ s := by
  classical
  have hloc : ∀ v : TangentSpace I p, ‖v‖ < Real.pi / Real.sqrt K →
      Submission.CutStep2.LocallyInjectiveAtGExp (I := I) hmet p v :=
    fun v hv => locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt' (cov := cov) hmet htor hK hcurv hv
  set A : Set ↥(Set.Icc a b) := {t | W₁ (t : ℝ) = W₂ (t : ℝ)} with hA
  have hcont₁ : Continuous fun t : ↥(Set.Icc a b) => W₁ (t : ℝ) := h₁.domRestrict
  have hcont₂ : Continuous fun t : ↥(Set.Icc a b) => W₂ (t : ℝ) := h₂.domRestrict
  have hAclosed : IsClosed A := by
    have hpre : A = (fun t : ↥(Set.Icc a b) => W₁ (t : ℝ) - W₂ (t : ℝ)) ⁻¹' {0} := by
      ext t
      rw [hA]
      simp [sub_eq_zero]
    rw [hpre]
    exact isClosed_singleton.preimage (hcont₁.sub hcont₂)
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    rw [hA] at ht
    obtain ⟨V, hV, hVinj⟩ := hloc (W₁ (t : ℝ)) (hb₁ (t : ℝ) t.2)
    have h1' : (fun s : ↥(Set.Icc a b) => W₁ (s : ℝ)) ⁻¹' V ∈ 𝓝 t :=
      hcont₁.continuousAt.preimage_mem_nhds hV
    have h2' : (fun s : ↥(Set.Icc a b) => W₂ (s : ℝ)) ⁻¹' V ∈ 𝓝 t :=
      hcont₂.continuousAt.preimage_mem_nhds (ht ▸ hV)
    refine Filter.mem_of_superset (Filter.inter_mem h1' h2') ?_
    rintro s ⟨hs1, hs2⟩
    rw [hA]
    exact hVinj (W₁ (s : ℝ)) hs1 (W₂ (s : ℝ)) hs2 (by rw [hG₁ _ s.2, hG₂ _ s.2])
  have hAne : A.Nonempty := ⟨⟨a, ⟨le_refl a, hab⟩⟩, by rw [hA]; simpa using ha⟩
  haveI : PreconnectedSpace ↥(Set.Icc a b) :=
    Subtype.preconnectedSpace (isPreconnected_Icc (a := a) (b := b))
  have hAuniv : A = Set.univ := IsClopen.eq_univ ⟨hAclosed, hAopen⟩ hAne
  intro s hs
  have hmem : (⟨s, hs⟩ : ↥(Set.Icc a b)) ∈ A := by rw [hAuniv]; exact Set.mem_univ _
  rw [hA] at hmem
  exact hmem


/-! ## Neighbourhood filters at the endpoints -/

private theorem nhdsWithin_Iic_eq_nhdsWithin_Icc {S : ℝ} (hS : 0 < S) :
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

/-- At a positive point `T`, restricted to `[0,T]`, the neighbourhood filter of `T` is the
left filter together with the principal filter of the point. -/
private theorem nhdsWithin_Icc_eq_left_sup {T : ℝ} (hT : 0 < T) :
    𝓝[Set.Icc (0 : ℝ) T] T = 𝓝[Set.Iio T] T ⊔ 𝓟 {T} := by
  calc 𝓝[Set.Icc (0 : ℝ) T] T = 𝓝[Set.Iic T] T := (nhdsWithin_Iic_eq_nhdsWithin_Icc hT).symm
    _ = 𝓝[Set.Iio T ∪ {T}] T := by
          have hIoi : Set.Iio T ∪ {T} = Set.Iic T := by
            ext u
            simp only [Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff, Set.mem_Iic,
              le_iff_lt_or_eq]
          rw [hIoi]
    _ = 𝓝[Set.Iio T] T ⊔ 𝓝[{T}] T := nhdsWithin_union T (Set.Iio T) {T}
    _ = 𝓝[Set.Iio T] T ⊔ 𝓟 {T} := by rw [nhdsWithin_singleton, principal_singleton]

/-- The neighbourhood filters of `0` restricted to `[0,a]` and to `[0,b]` agree (`a,b > 0`). -/
private theorem nhdsWithin_Icc_zero_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
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

/-! ## Continuity of the truncated curve at an interior point -/

/-- **The curve truncated at `S` is continuous at every `T ∈ (0, S]`.**  The truncation only matters
at `T = S`, where `h` is only known to be continuous from the left. -/
theorem continuousAt_trunc {h : ℝ → M} {S : ℝ}
    (hc : ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc (0 : ℝ) S)) (hS : 0 < S)
    {T : ℝ} (hT0 : 0 < T) (hTS : T ≤ S) :
    ContinuousAt (fun t : ℝ => if t ≤ S then h t else h S) T := by
  set h' : ℝ → M := fun t => if t ≤ S then h t else h S with hh'
  rcases lt_or_eq_of_le hTS with hlt | heq
  · have hnb : Set.Icc (0 : ℝ) S ∈ 𝓝 T :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ⟨hT0, hlt⟩)
        (fun t ht => ⟨ht.1.le, ht.2.le⟩)
    have hcont : ContinuousAt h T :=
      ((hc T ⟨hT0.le, hTS⟩).contMDiffAt hnb).continuousAt
    refine hcont.congr ?_
    filter_upwards [Iio_mem_nhds hlt] with t ht
    have htle : t ≤ S := (Set.mem_Iio.mp ht).le
    show h t = h' t
    rw [hh']
    simp only [htle, if_true]
  · rw [heq]
    have hleft : ContinuousWithinAt h' (Set.Iic S) S := by
      have h2 : ContinuousWithinAt h (Set.Icc (0 : ℝ) S) S :=
        (hc S ⟨hS.le, le_rfl⟩).continuousWithinAt
      have h3 : ContinuousWithinAt h (Set.Iic S) S := by
        have ht : Tendsto h (𝓝[Set.Iic S] S) (𝓝 (h S)) := by
          rw [nhdsWithin_Iic_eq_nhdsWithin_Icc hS]
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

/-! ## The main statement -/

theorem exists_lift_of_short
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
    {p : M} {h : ℝ → M} {S : ℝ} (hS : 0 < S)
    (hc : ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc (0 : ℝ) S)) (h0 : h 0 = p)
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
    rw [hℓdef]; exact curveLength_self (I := I) h 0
  have hℓS : ℓ S < R := by rw [hℓdef, hRdef]; exact hlen
  obtain ⟨hintI, hmono, hbridge⟩ := curveLength_toolkit (I := I) (h := h) (S := S) hc
  have hℓmono : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ S → ℓ a ≤ ℓ b := by
    intro a b ha hab hbS
    rw [hℓdef]
    exact hmono a b ha hab hbS
  have hGaussAll : ∀ (v η : TangentSpace I p) (t : ℝ),
      Inner.inner ℝ
        (curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet p (t • (v + r • η))) 0)
        (curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • v)) t)
      = t * Inner.inner ℝ η v :=
    fun v η t => gauss_pairing_fibre (cov := cov) (p := p) (v := v) (η := η) hmet htor t
  have hD2 : ∀ {W : ℝ → TangentSpace I p} {a b : ℝ}, a ≤ b → ContDiffOn ℝ 1 W (Set.Icc a b) →
      ‖W b‖ ≤ ‖W a‖ + curveLength (I := I)
        (fun s : ℝ => GExp (cov := cov) hmet p (W s)) a b :=
    fun {W} {a} {b} hab hW =>
      radial_estimate_of_lift (cov := cov) (p := p) (W := W) hmet htor hab hW hGaussAll
  let Good : ℝ → Prop := fun t => ∃ W : ℝ → TangentSpace I p,
      ContinuousOn W (Set.Icc (0:ℝ) t) ∧ W 0 = 0 ∧
      (∀ s ∈ Set.Icc (0:ℝ) t, GExp (cov := cov) hmet p (W s) = h s) ∧
      (∀ s ∈ Set.Icc (0:ℝ) t, ‖W s‖ ≤ ℓ s)
  have hGood0 : Good 0 := by
    refine ⟨fun _ => 0, continuousOn_const, rfl, ?_, ?_⟩
    · intro s hs
      have hs0 : s = 0 := le_antisymm hs.2 hs.1
      rw [hs0, h0, GExp_zero]
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
      exact lift_eqOn_of_agrees (K := K) hK hcurv hmet htor (a := 0) (b := t₁)
        (le_trans hs.1 hs.2)
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
      exact continuousAt_trunc (I := I) hc hS hTpos hTS
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
    obtain ⟨v, hvlim⟩ := exists_tendsto_of_lift (cov := cov) (p := p) (h := H) (T := T) (a := 0)
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
        rw [← nhdsWithin_Icc_zero_eq hhalf hTpos]
        exact (hWf_spec (T/2) (hlt (T/2) hhalf.le (by linarith))).1.continuousWithinAt
          ⟨le_refl 0, by linarith⟩
      · show Ww 0 = (Wf (T/2)) 0
        rw [show Ww 0 = (Wf 0) 0 from rfl, (hWf_spec 0 hGood0).2.1,
          (hWf_spec (T/2) (hlt (T/2) hhalf.le (by linarith))).2.1]
    have hWwIco : ContinuousOn Ww (Set.Icc (0:ℝ) T ∩ {a : ℝ | a < T}) := by
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
      · have hset : Set.Icc (0:ℝ) T ∩ {a : ℝ | ¬ a < T} = {T} := by
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
          rw [show Ww 0 = (Wf 0) 0 from rfl, (hWf_spec 0 hGood0).2.1, h0, GExp_zero]
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
    obtain ⟨t', hTt', ht'S, W', hW'c, hW'T, hW'G, hW'b⟩ :=
      exists_local_lift (cov := cov) (p := p) (h := h) (S := S) (t := T) hmet htor hK hcurv hS hc
        h0 hTmem hltTS (by rw [hRdef] at hvR; exact hvR) hvT hGaussAll hD2
    have hGood' : Good t' := by
      refine ⟨fun s => if s < T then W s else W' s, ?_, ?_, ?_, ?_⟩
      · have hsetR : Set.Icc (0:ℝ) t' ∩ {a : ℝ | ¬ a < T} = Set.Icc T t' := by
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
        · have hsub : Set.Icc (0:ℝ) t' ∩ {a : ℝ | a < T} ⊆ Set.Icc (0:ℝ) T :=
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
            have h1 : curveLength (I := I) h 0 T + curveLength (I := I) h T s
                = curveLength (I := I) h 0 s :=
              curveLength_add_of_integrable (I := I) h (hintI 0 T le_rfl hT0 hTS)
                (hintI T s hT0 hsT (le_trans hs.2 ht'S))
            rw [hℓdef]
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

end Work.OddBound.longHomotopy
