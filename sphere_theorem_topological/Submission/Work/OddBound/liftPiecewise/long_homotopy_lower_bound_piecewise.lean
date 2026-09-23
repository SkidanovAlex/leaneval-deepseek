import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.liftPiecewise.exists_lift_of_piecewise_short
import Submission.Work.OddBound.relaxedLHL.long_homotopy_lower_bound_relaxed
import Submission.Work.OddBound.longHomotopy.lift_family_continuity_core
import Submission.Work.OddBound.longHomotopy.eq_at_zero_of_continuous_lift_eq
import Submission.Work.OddBound.longHomotopy.lift_of_geodesic_ray
import Submission.Work.OddBound.longHomotopy.curveLength_comp_sub
import Submission.Work.OddBound.liftPiecewise.curveLength_comp_sub_piecewise
import Submission.Work.OddBound.liftPiecewise.exists_piecewise_partitions_halves

namespace Work.OddBound.liftPiecewise

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval

set_option linter.style.haveILetI false



/-! ## Elementary reparametrisation helpers -/

/-- Velocity of an affinely reparametrised curve at time `0`. -/
private lemma curveVelocity_comp_mul_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {γ : ℝ → M} (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ) (a : ℝ) :
    Submission.Geodesic.curveVelocity (I := I) (fun s : ℝ => γ (a * s)) 0
      = a • Submission.Geodesic.curveVelocity (I := I) γ 0 := by
  have hd : MDifferentiableAt 𝓘(ℝ) I γ (a * 0 + 0) :=
    hγsm.contMDiffAt.mdifferentiableAt (by simp)
  have h := Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := γ) (c := a) (d := 0)
    (t := 0) hd
  rw [show a * 0 + 0 = (0 : ℝ) by ring] at h
  have hfun : (fun s : ℝ => γ (a * s + 0)) = (fun s : ℝ => γ (a * s)) := by
    funext s; rw [add_zero]
  rw [hfun] at h
  rw [show a * 0 = (0 : ℝ) by ring]
  exact h

/-- Smoothness of an affinely reparametrised curve. -/
private lemma contMDiff_comp_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {γ : ℝ → M} (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ) (a : ℝ) :
    ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => γ (a * s)) := by
  have h1 : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun s : ℝ => a * s) := by
    rw [contMDiff_iff_contDiff]; fun_prop
  have h := hγsm.comp h1
  simpa [Function.comp_def] using h

/-- A geodesic reparametrised affinely is a geodesic. -/
private lemma isGeodesicAt_comp_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {γ : ℝ → M} (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hgeo : ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt (I := I) cov γ t) {a : ℝ} (ha : a ≠ 0) :
    ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt (I := I) cov (fun s : ℝ => γ (a * s)) t := by
  intro t
  have h := Submission.HopfRinow.isGeodesicAt_comp_affine (cov := cov) (σ := γ) (a := a) (b := 0)
    (c := a * t - 1) (d := a * t + 1) ha hγsm.contMDiffOn (fun y _ => hgeo y) (r := t)
    (by constructor <;> linarith)
  simpa using h

theorem long_homotopy_lower_bound_piecewise
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
    {p : M} {L : ℝ} (hL : 0 < L) {γ : ℝ → M}
    (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hgeo : ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt (I := I) cov γ t)
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0)
    (hper : ∀ t : ℝ, γ (t + L) = γ t) (h0 : γ 0 = p)
    {c : ℝ → ℝ → M}
    (hcont : Continuous (fun u : ℝ × ℝ => c u.1 u.2))
    (hcper : ∀ s t : ℝ, c (s + 1) t = c s t) (hcbase : ∀ t : ℝ, c 0 t = p)
    (hc0 : ∀ s : ℝ, c s 0 = γ (L * s))
    (hc1 : ∀ s : ℝ, c s 1 = p)
    (hpiece : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ (k : ℕ) (a : Fin (k + 1) → ℝ),
        StrictMono a ∧ a 0 = 0 ∧ a (Fin.last k) = 1 ∧
        ∀ j : Fin k, ContMDiffOn 𝓘(ℝ) I 1 (fun s : ℝ => c s t) (Set.Icc (a j.castSucc) (a j.succ)))
    (hlen : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Submission.Length.curveLength (I := I) (fun s : ℝ => c s t) 0 (1 / 2) < Real.pi / Real.sqrt K ∧
      Submission.Length.curveLength (I := I) (fun s : ℝ => c s t) (1 / 2) 1 < Real.pi / Real.sqrt K) :
    False := by
  classical
  haveI : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : CompleteSpace (TangentSpace I p) := inferInstance
  -- ## 1. The slice-wise lifts of the two half-families
  have hexP : ∀ t : ℝ, ∃ W : ℝ → TangentSpace I p,
      (t ∈ Set.Icc (0 : ℝ) 1 →
        ContinuousOn W (Set.Icc (0 : ℝ) (1 / 2)) ∧ W 0 = 0 ∧
        (∀ s ∈ Set.Icc (0 : ℝ) (1 / 2),
          Submission.GlobalExp.GExp (cov := cov) hmet p (W s) = c s t) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) (1 / 2), ‖W s‖ < Real.pi / Real.sqrt K)) := by
    intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · obtain ⟨k, a, hamono, ha0, ha1, hpw⟩ := hpiece t ht
      obtain ⟨hpart1, -, -⟩ := exists_piecewise_partitions_halves (I := I) hamono ha0 ha1 hpw
      obtain ⟨k1, b, hbmono, hb0, hb1, hbpiece⟩ := hpart1
      have hcont1 : ContinuousOn (fun s : ℝ => c s t) (Set.Icc (0 : ℝ) (1 / 2)) :=
        (hcont.comp (continuous_id.prodMk continuous_const)).continuousOn
      obtain ⟨W, hWc, hW0, hWG, hWb⟩ := exists_lift_of_piecewise_short (I := I) (cov := cov)
        hmet htor hK hcurv (p := p) (h := fun s : ℝ => c s t) (S := 1 / 2) (by norm_num)
        hbmono hb0 hb1 hcont1 hbpiece (hcbase t) (hlen t ht).1
      refine ⟨W, fun _ => ⟨hWc, hW0, hWG, ?_⟩⟩
      intro s hs
      refine lt_of_le_of_lt (hWb s hs) ?_
      have hmono := curveLength_mono_piecewise (I := I) (h := fun r : ℝ => c r t) (S := 1 / 2)
        (k := k1) (a := b) hbmono hb0 hb1 hbpiece s (1 / 2) hs.1 hs.2 le_rfl
      linarith [(hlen t ht).1]
    · exact ⟨fun _ => 0, fun h => absurd h ht⟩
  have hexM : ∀ t : ℝ, ∃ W : ℝ → TangentSpace I p,
      (t ∈ Set.Icc (0 : ℝ) 1 →
        ContinuousOn W (Set.Icc (0 : ℝ) (1 / 2)) ∧ W 0 = 0 ∧
        (∀ s ∈ Set.Icc (0 : ℝ) (1 / 2),
          Submission.GlobalExp.GExp (cov := cov) hmet p (W s) = c (1 - s) t) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) (1 / 2), ‖W s‖ < Real.pi / Real.sqrt K)) := by
    intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · obtain ⟨k, a, hamono, ha0, ha1, hpw⟩ := hpiece t ht
      obtain ⟨-, hpart2, hpart3⟩ := exists_piecewise_partitions_halves (I := I) hamono ha0 ha1 hpw
      obtain ⟨k2, d, hdmono, hd0, hd1, hdpiece⟩ := hpart2
      obtain ⟨k3, e, hemono, he0, he1, hepiece⟩ := hpart3
      have hcont2 : ContinuousOn (fun s : ℝ => c (1 - s) t) (Set.Icc (0 : ℝ) (1 / 2)) :=
        (hcont.comp ((continuous_const.sub continuous_id).prodMk continuous_const)).continuousOn
      have hbaseM : (fun s : ℝ => c (1 - s) t) 0 = p := by
        have h1 : c 1 t = p := by simpa using (hcper 0 t).trans (hcbase t)
        simpa using h1
      have hlenM : Submission.Length.curveLength (I := I) (fun s : ℝ => c (1 - s) t) 0 (1 / 2)
          < Real.pi / Real.sqrt K := by
        have h := curveLength_comp_sub_piecewise (I := I) (c := fun r : ℝ => c r t)
          (a := (1 : ℝ) / 2) (b := 1) (by norm_num) hdmono hd0 hd1 hdpiece
        rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h
        rw [h]
        exact (hlen t ht).2
      obtain ⟨W, hWc, hW0, hWG, hWb⟩ := exists_lift_of_piecewise_short (I := I) (cov := cov)
        hmet htor hK hcurv (p := p) (h := fun s : ℝ => c (1 - s) t) (S := 1 / 2) (by norm_num)
        hemono he0 he1 hcont2 hepiece hbaseM hlenM
      refine ⟨W, fun _ => ⟨hWc, hW0, hWG, ?_⟩⟩
      intro s hs
      refine lt_of_le_of_lt (hWb s hs) ?_
      have hmono := curveLength_mono_piecewise (I := I) (h := fun r : ℝ => c (1 - r) t)
        (S := 1 / 2) (k := k3) (a := e) hemono he0 he1 hepiece s (1 / 2) hs.1 hs.2 le_rfl
      linarith [hmono, hlenM]
    · exact ⟨fun _ => 0, fun h => absurd h ht⟩
  -- ## 2. The two families of slice-wise lifts
  let Wp : ℝ → ℝ → TangentSpace I p := fun s t => Classical.choose (hexP t) s
  have hWp : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ContinuousOn (fun s : ℝ => Wp s t) (Set.Icc (0 : ℝ) (1 / 2)) ∧ Wp 0 t = 0 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) (1 / 2),
        Submission.GlobalExp.GExp (cov := cov) hmet p (Wp s t) = c s t) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) (1 / 2), ‖Wp s t‖ < Real.pi / Real.sqrt K) :=
    fun t ht => Classical.choose_spec (hexP t) ht
  have hWpC : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContinuousOn (fun s : ℝ => Wp s t) (Set.Icc (0 : ℝ) (1 / 2)) := fun t ht => (hWp t ht).1
  have hWp0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Wp 0 t = 0 := fun t ht => (hWp t ht).2.1
  have hWpG : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) (1 / 2),
      Submission.GlobalExp.GExp (cov := cov) hmet p (Wp s t) = c s t :=
    fun t ht s hs => (hWp t ht).2.2.1 s hs
  have hWpb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) (1 / 2),
      ‖Wp s t‖ < Real.pi / Real.sqrt K := fun t ht s hs => (hWp t ht).2.2.2 s hs
  let Wm : ℝ → ℝ → TangentSpace I p := fun s t => Classical.choose (hexM t) s
  have hWm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ContinuousOn (fun s : ℝ => Wm s t) (Set.Icc (0 : ℝ) (1 / 2)) ∧ Wm 0 t = 0 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) (1 / 2),
        Submission.GlobalExp.GExp (cov := cov) hmet p (Wm s t) = c (1 - s) t) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) (1 / 2), ‖Wm s t‖ < Real.pi / Real.sqrt K) :=
    fun t ht => Classical.choose_spec (hexM t) ht
  have hWmC : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContinuousOn (fun s : ℝ => Wm s t) (Set.Icc (0 : ℝ) (1 / 2)) := fun t ht => (hWm t ht).1
  have hWm0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Wm 0 t = 0 := fun t ht => (hWm t ht).2.1
  have hWmG : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) (1 / 2),
      Submission.GlobalExp.GExp (cov := cov) hmet p (Wm s t) = c (1 - s) t :=
    fun t ht s hs => (hWm t ht).2.2.1 s hs
  have hWmb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) (1 / 2),
      ‖Wm s t‖ < Real.pi / Real.sqrt K := fun t ht s hs => (hWm t ht).2.2.2 s hs
  -- ## 3. Joint continuity of the two lift families
  have hWpc : ContinuousOn (fun u : ℝ × ℝ => Wp u.1 u.2)
      (Set.Icc (0 : ℝ) (1 / 2) ×ˢ Set.Icc (0 : ℝ) 1) :=
    Work.OddBound.longHomotopy.lift_family_continuity_core
      (X := TangentSpace I p) (Y := M)
      (f := fun v : TangentSpace I p => Submission.GlobalExp.GExp (cov := cov) hmet p v)
      (R := Real.pi / Real.sqrt K)
      (hf := continuous_iff_continuousAt.mpr (fun v =>
        (Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet p v).continuousAt))
      (hloc := fun v hv =>
        Work.OddBound.longHomotopy.locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt
          (cov := cov) hmet htor hK hcurv hv)
      (Φ := fun u : ℝ × ℝ => c u.1 u.2) (hΦ := hcont)
      (W := Wp) (S := 1 / 2)
      (fun t ht => hWpC t ht) (fun t ht => hWp0 t ht)
      (fun t ht s hs => hWpG t ht s hs) (fun t ht s hs => hWpb t ht s hs)
  have hcontΦ₂ : Continuous (fun u : ℝ × ℝ => c (1 - u.1) u.2) :=
    hcont.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)
  have hWmc : ContinuousOn (fun u : ℝ × ℝ => Wm u.1 u.2)
      (Set.Icc (0 : ℝ) (1 / 2) ×ˢ Set.Icc (0 : ℝ) 1) :=
    Work.OddBound.longHomotopy.lift_family_continuity_core
      (X := TangentSpace I p) (Y := M)
      (f := fun v : TangentSpace I p => Submission.GlobalExp.GExp (cov := cov) hmet p v)
      (R := Real.pi / Real.sqrt K)
      (hf := continuous_iff_continuousAt.mpr (fun v =>
        (Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet p v).continuousAt))
      (hloc := fun v hv =>
        Work.OddBound.longHomotopy.locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt
          (cov := cov) hmet htor hK hcurv hv)
      (Φ := fun u : ℝ × ℝ => c (1 - u.1) u.2) (hΦ := hcontΦ₂)
      (W := Wm) (S := 1 / 2)
      (fun t ht => hWmC t ht) (fun t ht => hWm0 t ht)
      (fun t ht s hs => hWmG t ht s hs) (fun t ht s hs => hWmb t ht s hs)
  -- ## 4. The two lifts of the midpoint curve
  have hsec₁ : ContinuousOn (fun t : ℝ => Wp (1 / 2) t) (Set.Icc (0 : ℝ) 1) :=
    hWpc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨⟨by norm_num, le_refl _⟩, ht⟩)
  have hsec₂ : ContinuousOn (fun t : ℝ => Wm (1 / 2) t) (Set.Icc (0 : ℝ) 1) :=
    hWmc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨⟨by norm_num, le_refl _⟩, ht⟩)
  have hb₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Wp (1 / 2) t‖ < Real.pi / Real.sqrt K :=
    fun t ht => hWpb t ht (1 / 2) ⟨by norm_num, le_refl _⟩
  have hb₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Wm (1 / 2) t‖ < Real.pi / Real.sqrt K :=
    fun t ht => hWmb t ht (1 / 2) ⟨by norm_num, le_refl _⟩
  have hG : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Submission.GlobalExp.GExp (cov := cov) hmet p (Wp (1 / 2) t)
        = Submission.GlobalExp.GExp (cov := cov) hmet p (Wm (1 / 2) t) := by
    intro t ht
    rw [hWpG t ht (1 / 2) ⟨by norm_num, le_refl _⟩,
      hWmG t ht (1 / 2) ⟨by norm_num, le_refl _⟩]
    norm_num
  have hend1 : Wp (1 / 2) 1
      = (1 / 2 : ℝ) • Submission.Geodesic.curveVelocity (I := I) (fun _ : ℝ => p) 0 := by
    have hconst : (fun s : ℝ => c s 1) = (fun _ : ℝ => p) := funext (fun s => hc1 s)
    have hgeo' : ∀ t : ℝ,
        Submission.Geodesic.IsGeodesicAt (I := I) cov (fun s : ℝ => c s 1) t := by
      intro t
      rw [hconst]
      exact Submission.Geodesic.isGeodesic_const (I := I) cov p t
    have hsm' : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => c s 1) := by
      rw [hconst]
      exact contMDiff_const
    have hWc : ContinuousOn (fun s : ℝ => Wp s 1) (Set.Icc (0 : ℝ) (1 / 2)) :=
      hWpc.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun s hs => ⟨hs, ⟨by norm_num, le_refl 1⟩⟩)
    have hspec := Work.OddBound.longHomotopy.lift_of_geodesic_ray (I := I) (cov := cov)
      hmet htor hK hcurv (p := p) (h := fun s : ℝ => c s 1) (S := 1 / 2) (by norm_num)
      hgeo' hsm' (hc1 0) (W := fun s : ℝ => Wp s 1) hWc
      (hWp0 1 ⟨by norm_num, le_refl 1⟩)
      (fun s hs => hWpG 1 ⟨by norm_num, le_refl 1⟩ s hs)
      (fun s hs => hWpb 1 ⟨by norm_num, le_refl 1⟩ s hs)
    have hv : Submission.Geodesic.curveVelocity (I := I) (fun s : ℝ => c s 1) 0
        = Submission.Geodesic.curveVelocity (I := I) (fun _ : ℝ => p) 0 := by
      rw [hconst]
    exact (hspec (1 / 2) ⟨by norm_num, le_refl _⟩).trans
      (congrArg (fun w => (1 / 2 : ℝ) • w) hv)
  have hend2 : Wm (1 / 2) 1
      = (1 / 2 : ℝ) • Submission.Geodesic.curveVelocity (I := I) (fun _ : ℝ => p) 0 := by
    have hconst : (fun s : ℝ => c (1 - s) 1) = (fun _ : ℝ => p) := funext fun s => hc1 (1 - s)
    have hgeo' : ∀ t : ℝ,
        Submission.Geodesic.IsGeodesicAt (I := I) cov (fun s : ℝ => c (1 - s) 1) t := by
      intro t
      rw [hconst]
      exact Submission.Geodesic.isGeodesic_const (I := I) cov p t
    have hsm' : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => c (1 - s) 1) := by
      rw [hconst]
      exact contMDiff_const
    have hWc : ContinuousOn (fun s : ℝ => Wm s 1) (Set.Icc (0 : ℝ) (1 / 2)) :=
      hWmc.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun s hs => ⟨hs, ⟨by norm_num, le_refl 1⟩⟩)
    have hspec := Work.OddBound.longHomotopy.lift_of_geodesic_ray (I := I) (cov := cov)
      hmet htor hK hcurv (p := p) (h := fun s : ℝ => c (1 - s) 1) (S := 1 / 2) (by norm_num)
      hgeo' hsm' (hc1 (1 - 0)) (W := fun s : ℝ => Wm s 1) hWc
      (hWm0 1 ⟨by norm_num, le_refl 1⟩)
      (fun s hs => hWmG 1 ⟨by norm_num, le_refl 1⟩ s hs)
      (fun s hs => hWmb 1 ⟨by norm_num, le_refl 1⟩ s hs)
    have hv : Submission.Geodesic.curveVelocity (I := I) (fun s : ℝ => c (1 - s) 1) 0
        = Submission.Geodesic.curveVelocity (I := I) (fun _ : ℝ => p) 0 := by
      rw [hconst]
    exact (hspec (1 / 2) ⟨by norm_num, le_refl _⟩).trans
      (congrArg (fun w => (1 / 2 : ℝ) • w) hv)
  have h1eq : Wp (1 / 2) 1 = Wm (1 / 2) 1 := hend1.trans hend2.symm
  -- ## 5. the open-and-closed step
  have hclopen : Wp (1 / 2) 0 = Wm (1 / 2) 0 :=
    Work.OddBound.longHomotopy.eq_at_zero_of_continuous_lift_eq (I := I) (cov := cov) hmet htor hK
      hcurv hsec₁ hsec₂ hb₁ hb₂ hG h1eq
  -- ## 6. at `t = 0` the lifts are the straight rays of the two halves of `γ`
  have hgeo₁ : ∀ t : ℝ,
      Submission.Geodesic.IsGeodesicAt (I := I) cov (fun s : ℝ => γ (L * s)) t :=
    isGeodesicAt_comp_mul (I := I) (cov := cov) hγsm hgeo (ne_of_gt hL)
  have hsm₁ : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => γ (L * s)) :=
    contMDiff_comp_mul (I := I) hγsm L
  have hsecP : ContinuousOn (fun s : ℝ => Wp s 0) (Set.Icc (0 : ℝ) (1 / 2)) :=
    hWpc.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, ⟨le_refl 0, by norm_num⟩⟩)
  have hP : Wp (1 / 2) 0
      = (1 / 2 : ℝ) • (L • Submission.Geodesic.curveVelocity (I := I) γ 0) := by
    have hspec := Work.OddBound.longHomotopy.lift_of_geodesic_ray (I := I) (cov := cov)
      hmet htor hK hcurv (p := p) (h := fun s : ℝ => γ (L * s)) (S := 1 / 2) (by norm_num)
      hgeo₁ hsm₁ (by simp [h0])
      (W := fun s : ℝ => Wp s 0) hsecP
      (hWp0 0 ⟨le_refl 0, by norm_num⟩)
      (fun s hs => (hWpG 0 ⟨le_refl 0, by norm_num⟩ s hs).trans (hc0 s))
      (fun s hs => hWpb 0 ⟨le_refl 0, by norm_num⟩ s hs)
    exact (hspec (1 / 2) ⟨by norm_num, le_refl _⟩).trans
      (congrArg (fun w => (1 / 2 : ℝ) • w) (curveVelocity_comp_mul_zero (I := I) hγsm L))
  have hgeo₂ : ∀ t : ℝ,
      Submission.Geodesic.IsGeodesicAt (I := I) cov (fun s : ℝ => γ ((-L) * s)) t :=
    isGeodesicAt_comp_mul (I := I) (cov := cov) hγsm hgeo (neg_ne_zero.mpr (ne_of_gt hL))
  have hsm₂ : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => γ ((-L) * s)) :=
    contMDiff_comp_mul (I := I) hγsm (-L)
  have hper' : ∀ s : ℝ, γ (L * (1 - s)) = γ ((-L) * s) := by
    intro s
    have h := hper ((-L) * s)
    have he : (-L) * s + L = L * (1 - s) := by ring
    rw [he] at h
    exact h
  have hsecM : ContinuousOn (fun s : ℝ => Wm s 0) (Set.Icc (0 : ℝ) (1 / 2)) :=
    hWmc.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, ⟨le_refl 0, by norm_num⟩⟩)
  have hM : Wm (1 / 2) 0
      = (1 / 2 : ℝ) • ((-L) • Submission.Geodesic.curveVelocity (I := I) γ 0) := by
    have hspec := Work.OddBound.longHomotopy.lift_of_geodesic_ray (I := I) (cov := cov)
      hmet htor hK hcurv (p := p) (h := fun s : ℝ => γ ((-L) * s)) (S := 1 / 2) (by norm_num)
      hgeo₂ hsm₂ (by simp [h0])
      (W := fun s : ℝ => Wm s 0) hsecM
      (hWm0 0 ⟨le_refl 0, by norm_num⟩)
      (fun s hs => (hWmG 0 ⟨le_refl 0, by norm_num⟩ s hs).trans (by rw [hc0 (1 - s), hper' s]))
      (fun s hs => hWmb 0 ⟨le_refl 0, by norm_num⟩ s hs)
    exact (hspec (1 / 2) ⟨by norm_num, le_refl _⟩).trans
      (congrArg (fun w => (1 / 2 : ℝ) • w) (curveVelocity_comp_mul_zero (I := I) hγsm (-L)))
  -- ## 7. contradiction: `L • γ'(0) = -(L • γ'(0))` forces `γ'(0) = 0`
  have hvv : (1 / 2 : ℝ) • (L • Submission.Geodesic.curveVelocity (I := I) γ 0)
      = (1 / 2 : ℝ) • ((-L) • Submission.Geodesic.curveVelocity (I := I) γ 0) :=
    hP.symm.trans (hclopen.trans hM)
  have hLv : L • Submission.Geodesic.curveVelocity (I := I) γ 0 = 0 := by
    have h1 : (1 / 2 : ℝ) • (L • Submission.Geodesic.curveVelocity (I := I) γ 0)
        = -((1 / 2 : ℝ) • (L • Submission.Geodesic.curveVelocity (I := I) γ 0)) := by
      nth_rewrite 1 [hvv]
      rw [neg_smul, smul_neg]
    have h3 : (1 / 2 : ℝ) • (L • Submission.Geodesic.curveVelocity (I := I) γ 0)
        + (1 / 2 : ℝ) • (L • Submission.Geodesic.curveVelocity (I := I) γ 0) = 0 := by
      nth_rewrite 1 [h1]
      rw [neg_add_cancel]
    have h4 : (2 : ℝ) • ((1 / 2 : ℝ) • (L • Submission.Geodesic.curveVelocity (I := I) γ 0))
        = 0 := by
      rw [two_smul]
      exact h3
    have h5 : (1 / 2 : ℝ) • (L • Submission.Geodesic.curveVelocity (I := I) γ 0) = 0 := by
      rcases (smul_eq_zero.mp h4) with h | h
      · norm_num at h
      · exact h
    rcases (smul_eq_zero.mp h5) with h | h
    · norm_num at h
    · exact h
  have hv : Submission.Geodesic.curveVelocity (I := I) γ 0 = 0 := by
    rcases (smul_eq_zero.mp hLv) with h | h
    · exact absurd h (ne_of_gt hL)
    · exact h
  exact hne 0 hv

end Work.OddBound.liftPiecewise
