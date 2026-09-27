import Mathlib
import Submission.Work.Drive.sepJointSmooth
import Submission.Work.Drive.goodFaceMulti
import Submission.Work.Drive.chartDiffRangeBridge

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# The parametric-Sard regularity of the *separated* germ family

The analytic helpers are in `Submission.Work.Drive.sepJointSmooth`; here the multi-chart parametric
Sard `Work.Drive.goodFaceMulti` is applied to the two sides of the family of the straight path
between two configurations, and its conclusion is converted into the regularity clauses `SepTrans`
and `SepFace` of the parity engine.
-/

namespace Work.Drive

open Manifold Filter Set Pointwise
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {m : ℕ}

/-- **The parametric-Sard regularity of the separated family.**  For every pair of configurations
`A`, `B`, every pair of angle lifts `tR`, `t'R` and every `ε' > 0` there is a shift `τ` of norm
`< ε'` such that the straight-path family with the loop's chart shifted by `τ` (and the sweep's chart
unshifted) satisfies the regularity clauses `SepTrans`, `SepFace` of the parity engine. -/
theorem sep_fam_regular_core {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ)
    (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tR t'R : ℝ)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ τ : EuclideanSpace ℝ (Fin m), ‖τ‖ < ε' ∧
      SepTrans Ξ Q c tR t'R A B τ 0 ∧ SepFace Ξ Q c tR t'R A B τ 0 := by
  classical
  have htop : Ctop ≠ 0 := by
    rw [ne_eq, ← WithTop.coe_zero]
    exact fun h => ENat.top_ne_zero (WithTop.coe_injective h)
  have hQsm : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q := hQ
  have hΞcont : Continuous (fun q : EuclideanSpace ℝ (Fin m) × CappingSpace => Ξ q.1 q.2) :=
    hΞ.2.1.continuous
  have hLfam_sm := sepLfam_contMDiff Ξ Q hΞ hQ A B
  have hNfam_sm := sepNfam_contMDiff Ξ Q c hΞ hQ A B tR t'R
  have hNfam_cont := sepNfam_cont Ξ Q c hΞ hQ A B tR t'R
  have hLfam_apply := sepLfam_apply Ξ Q A B
  -- ### the compact sets of values
  set S : Set CappingSpace := coreLoop Q '' Set.Icc 0 1 with hSdef
  have hS : IsCompact S := isCompact_Icc.image (contMDiff_coreLoop hQsm).continuous
  set Kp : Set (EuclideanSpace ℝ (Fin m)) := sepPathL A B '' Set.Icc 0 1 with hKpdef
  have hKp : IsCompact Kp := isCompact_Icc.image (by
    show Continuous fun s : ℝ => (1 - s) • A.1 + s • B.1
    fun_prop)
  set Ab : Set CappingSpace := sepNfam Ξ Q c A B tR t'R 0 '' Submission.Drive.unitBox 4 with hAbdef
  have hAb : IsCompact Ab := (isCompact_unitBox 4).image hNfam_cont
  -- ### the chart cover of the meeting values
  obtain ⟨r, pch, C0, C1, hC0c, hC1c, hC0int, hC1sub, hcover⟩ :=
    exists_compact_chart_cover Ab hAb
  -- ### the smallness constants
  have hfact1 : ∀ i : Fin r, ∃ ε : ℝ, 0 < ε ∧
      ∀ p ∈ Kp + Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (1 : ℝ),
        ∀ x ∈ S, ∀ σ : EuclideanSpace ℝ (Fin m), ‖σ‖ < ε → Ξ p x ∈ C0 i →
          Ξ (p + σ) x ∈ interior (C1 i) := fun i =>
    sep_shift_mem_of_compact Ξ hΞcont
      (hKp.add (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) (1 : ℝ))) hS (hC0c i)
      isOpen_interior (hC0int i)
  have hfact2 : ∀ i : Fin r, ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ Kp, ∀ x ∈ S,
      ∀ σ : EuclideanSpace ℝ (Fin m), ‖σ‖ < ε → Ξ p x ∈ C1 i →
        Ξ (p + σ) x ∈ (chr (pch i)).source := fun i =>
    sep_shift_mem_of_compact Ξ hΞcont hKp hS (hC1c i) (chr (pch i)).open_source (hC1sub i)
  choose εa hεapos hεa using hfact1
  choose εb hεbpos hεb using hfact2
  obtain ⟨ε2, hε2pos, hε2⟩ := exists_pos_le_all_fin (fun i => min (εa i) (εb i))
    (fun i => lt_min (hεapos i) (hεbpos i))
  have hε2a : ∀ i, ε2 ≤ εa i := fun i => le_trans (hε2 i) (min_le_left _ _)
  have hε2b : ∀ i, ε2 ≤ εb i := fun i => le_trans (hε2 i) (min_le_right _ _)
  -- ### the radii
  set εone : ℝ := ε2 / 4 with hone
  set εtwo : ℝ := ε2 / 2 with htwo
  set εbr : ℝ := min (min (ε' / 2) (1 / 2)) (ε2 / 16) with hbr
  have hεbrpos : 0 < εbr := by
    rw [hbr]
    exact lt_min (lt_min (by linarith) (by norm_num)) (by linarith)
  have hεbr' : εbr < ε' := by
    rw [hbr]
    have h := min_le_left (min (ε' / 2) (1 / 2)) (ε2 / 16)
    have h2 := min_le_left (ε' / 2) (1 / 2)
    linarith
  have hεbr1 : εbr < 1 := by
    rw [hbr]
    have h := min_le_left (min (ε' / 2) (1 / 2)) (ε2 / 16)
    have h2 := min_le_right (ε' / 2) (1 / 2)
    linarith
  have hεbr_one : εbr < εone := by
    rw [hbr, hone]
    have h := min_le_right (min (ε' / 2) (1 / 2)) (ε2 / 16)
    linarith
  have hεbr_two : εbr < εtwo := by
    rw [hbr, htwo]
    have h := min_le_right (min (ε' / 2) (1 / 2)) (ε2 / 16)
    linarith
  have hεtwo_a : ∀ i, εtwo < εa i := fun i => lt_of_lt_of_le (by rw [htwo]; linarith) (hε2a i)
  have hεtwo_b : ∀ i, εtwo < εb i := fun i => lt_of_lt_of_le (by rw [htwo]; linarith) (hε2b i)
  -- ### the parameter cut-offs
  have hγ : ∀ _i : Fin r, ∃ γ : EuclideanSpace ℝ (Fin m) → ℝ, ContDiff ℝ Ctop γ ∧
      (∀ p ∈ Metric.closedBall 0 εone, γ p = 1) ∧ tsupport γ ⊆ Metric.ball 0 εtwo := fun _ =>
    sep_exists_cutoff_one_on_of_subset (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) εone)
      Metric.isOpen_ball (fun p hp => by
        have h2 : ‖p‖ < εtwo := by
          rw [htwo]
          have h1 := Metric.mem_closedBall.mp hp
          rw [dist_zero_right, hone] at h1
          linarith
        simpa only [Metric.mem_ball, dist_zero_right] using h2)
  choose γi hγism hγione hγisupp using hγ
  -- ### the `O`-sets
  set Oset : Fin r → Set (EuclideanSpace ℝ (Fin m) × CappingSpace) := fun i =>
    {q | ∀ τ : EuclideanSpace ℝ (Fin m), ‖τ‖ ≤ εtwo → Ξ (q.1 + τ) q.2 ∈ (chr (pch i)).source}
    with hOsetdef
  have hOset_open : ∀ i : Fin r, IsOpen (Oset i) := by
    intro i
    rw [isOpen_iff_mem_nhds]
    intro q₀ hq₀
    have hopen : IsOpen {r : EuclideanSpace ℝ (Fin m) ×
        (EuclideanSpace ℝ (Fin m) × CappingSpace) |
        Ξ (r.2.1 + r.1) r.2.2 ∈ (chr (pch i)).source} := by
      have hcont : Continuous (fun r : EuclideanSpace ℝ (Fin m) ×
          (EuclideanSpace ℝ (Fin m) × CappingSpace) => Ξ (r.2.1 + r.1) r.2.2) :=
        hΞcont.comp ((continuous_snd.fst.add continuous_fst).prodMk continuous_snd.snd)
      exact hcont.isOpen_preimage _ (chr (pch i)).open_source
    have hsub : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) εtwo ×ˢ
        ({q₀} : Set (EuclideanSpace ℝ (Fin m) × CappingSpace)) ⊆
        {r : EuclideanSpace ℝ (Fin m) × (EuclideanSpace ℝ (Fin m) × CappingSpace) |
          Ξ (r.2.1 + r.1) r.2.2 ∈ (chr (pch i)).source} := by
      rintro ⟨τ, q⟩ ⟨hτ, rfl⟩
      exact hq₀ τ (by rwa [Metric.mem_closedBall, dist_zero_right] at hτ)
    obtain ⟨U, V, -, hVo, hUc, hqV, hUV⟩ := generalized_tube_lemma
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) εtwo)
      (isCompact_singleton (x := q₀)) hopen hsub
    refine Filter.mem_of_superset (hVo.mem_nhds (hqV (Set.mem_singleton q₀))) ?_
    intro q hq τ hτ
    exact hUV (Set.mk_mem_prod
      (hUc (by rw [Metric.mem_closedBall, dist_zero_right]; exact hτ)) hq)
  -- ### the two continuous maps of the loop's base data
  have hpath_cont : Continuous (fun z : Amb 4 => sepPathL A B (z 0)) := by
    have h2 : Continuous fun s : ℝ => sepPathL A B s := by
      show Continuous fun s : ℝ => (1 - s) • A.1 + s • B.1
      fun_prop
    exact h2.comp ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 => ℝ) 0).continuous)
  have hcore_cont : Continuous (fun z : Amb 4 => coreLoop Q (z 1)) :=
    (contMDiff_coreLoop hQsm).continuous.comp
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 => ℝ) 1).continuous)
  have hpair_cont : Continuous (fun z : Amb 4 => (sepPathL A B (z 0), coreLoop Q (z 1))) :=
    hpath_cont.prodMk hcore_cont
  -- ### the `K`-sets
  set Kset : Fin r → Set (Amb 4) := fun i => {z : Amb 4 |
      z ∈ Submission.Drive.unitBox 4 ∧
      Ξ (sepPathL A B (z 0)) (coreLoop Q (z 1)) ∈ C1 i ∧
      sepNfam Ξ Q c A B tR t'R 0 z ∈ C1 i} with hKsetdef
  have hKset_compact : ∀ i : Fin r, IsCompact (Kset i) := by
    intro i
    refine IsCompact.of_isClosed_subset (isCompact_unitBox 4) ?_ (fun z hz => hz.1)
    have h1 : IsClosed {z : Amb 4 | Ξ (sepPathL A B (z 0)) (coreLoop Q (z 1)) ∈ C1 i} :=
      (hC1c i).isClosed.preimage (hΞcont.comp hpair_cont)
    have h2 : IsClosed {z : Amb 4 | sepNfam Ξ Q c A B tR t'R 0 z ∈ C1 i} :=
      (hC1c i).isClosed.preimage hNfam_cont
    have h3 : IsClosed {z : Amb 4 | z ∈ Submission.Drive.unitBox 4} := isClosed_unitBox 4
    have h := h3.inter (h1.inter h2)
    simpa only [hKsetdef, Set.ofPred_and] using h
  -- ### the `V`-sets
  set Vset : Fin r → Set (Amb 4) := fun i => {z : Amb 4 |
      (sepPathL A B (z 0), coreLoop Q (z 1)) ∈ Oset i ∧
      sepNfam Ξ Q c A B tR t'R 0 z ∈ (chr (pch i)).source} with hVsetdef
  have hVset_open : ∀ i : Fin r, IsOpen (Vset i) := by
    intro i
    have h1 : IsOpen {z : Amb 4 | (sepPathL A B (z 0), coreLoop Q (z 1)) ∈ Oset i} :=
      (hOset_open i).preimage hpair_cont
    have h2 : IsOpen {z : Amb 4 | sepNfam Ξ Q c A B tR t'R 0 z ∈ (chr (pch i)).source} :=
      (chr (pch i)).open_source.preimage hNfam_cont
    have h := h1.inter h2
    simpa only [hVsetdef, Set.ofPred_and] using h
  have hKsetVset : ∀ i : Fin r, Kset i ⊆ Vset i := by
    intro i z hz
    refine ⟨fun τ hτ => hεb i (sepPathL A B (z 0)) ⟨z 0, hz.1 0, rfl⟩ (coreLoop Q (z 1))
      ⟨z 1, hz.1 1, rfl⟩ τ (lt_of_le_of_lt hτ (hεtwo_b i)) hz.2.1, hC1sub i hz.2.2⟩
  -- ### the box cut-offs
  have hβ : ∀ i : Fin r, ∃ β : Amb 4 → ℝ, ContDiff ℝ Ctop β ∧ (∀ z ∈ Kset i, β z = 1) ∧
      tsupport β ⊆ Vset i := fun i =>
    sep_exists_cutoff_one_on_of_subset (hKset_compact i) (hVset_open i) (hKsetVset i)
  choose βi hβism hβione hβisupp using hβ
  -- ### the chart containment of the systems
  have hUV : ∀ (i : Fin r) (q : EuclideanSpace ℝ (Fin m) × Amb 4),
      q.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) εtwo → q.2 ∈ Vset i →
      sepLfam Ξ Q A B q.1 q.2 ∈ (chr (pch i)).source ∧
        sepNfam Ξ Q c A B tR t'R q.1 q.2 ∈ (chr (pch i)).source := by
    intro i q hτ hz
    refine ⟨?_, hz.2⟩
    rw [hLfam_apply]
    exact hz.1 q.1 (le_of_lt (by rwa [Metric.mem_ball, dist_zero_right] at hτ))
  -- ### the smoothness of the systems
  have hΦsm : ∀ i : Fin r, ContDiff ℝ Ctop (sepSys Ξ Q c A B tR t'R (γi i) (βi i) (pch i)) := by
    intro i
    have hΦeq : sepSys Ξ Q c A B tR t'R (γi i) (βi i) (pch i)
        = fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
            (γi i q.1 * βi i q.2) • FamBox.chartDif (pch i) (sepLfam Ξ Q A B q.1)
              (sepNfam Ξ Q c A B tR t'R q.1) q.2 := by
      funext q
      simp only [sepSys]
    rw [hΦeq, contDiff_iff_contDiffAt]
    intro q₀
    by_cases hγ0 : q₀.1 ∈ tsupport (γi i)
    · by_cases hβ0 : q₀.2 ∈ tsupport (βi i)
      · have hmem : q₀.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) εtwo :=
          hγisupp i hγ0
        have hreg := hUV i q₀ hmem (hβisupp i hβ0)
        have hχ := sep_chartDif_contDiffAt Ξ Q c hΞ hQ A B tR t'R (pch i) q₀ hreg.1 hreg.2
        have hg : ContDiffAt ℝ Ctop (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
            γi i q.1 * βi i q.2) q₀ :=
          ((hγism i).contDiffAt.comp q₀ contDiffAt_fst).mul
            ((hβism i).contDiffAt.comp q₀ contDiffAt_snd)
        exact hg.smul hχ
      · refine (contDiffAt_const (c := (0 : Tgt 4))).congr_of_eventuallyEq ?_
        filter_upwards [(continuous_snd.tendsto q₀).eventually
          (sep_eventually_eq_zero_of_notMem_tsupport hβ0)] with q hq
        simp only [hq, mul_zero, zero_smul]
    · refine (contDiffAt_const (c := (0 : Tgt 4))).congr_of_eventuallyEq ?_
      filter_upwards [(continuous_fst.tendsto q₀).eventually
        (sep_eventually_eq_zero_of_notMem_tsupport hγ0)] with q hq
      simp only [hq, zero_mul, zero_smul]
  clear hSdef hKpdef hAbdef hOsetdef hKsetdef hVsetdef hone htwo
  -- ### the parameter-derivative of the systems is onto at their zeros
  have hsurj : ∀ (i : Fin r) (p : EuclideanSpace ℝ (Fin m)) (z : Amb 4),
      ‖p‖ < εbr → (z ∈ Kset i ∨ ∃ j : FaceIdx4,
        z ∈ (fun l : Fdir4 j => Fbase4 j + (l : Amb 4)) '' Fcov4 (Kset i) j) →
      sepSys Ξ Q c A B tR t'R (γi i) (βi i) (pch i) (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) =>
        sepSys Ξ Q c A B tR t'R (γi i) (βi i) (pch i) (p', z)) p) := by
    intro i p z hp hz h0
    have hzK : z ∈ Kset i := by
      rcases hz with h | h
      · exact h
      · obtain ⟨j, l, hl, rfl⟩ := h
        exact hl
    have hzV : z ∈ Vset i := hKsetVset i hzK
    have hγ1 : γi i p = 1 := hγione i p (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt (lt_trans hp hεbr_one))
    have hβ1 : βi i z = 1 := hβione i z hzK
    have hreg : sepLfam Ξ Q A B p z ∈ (chr (pch i)).source ∧
        sepNfam Ξ Q c A B tR t'R p z ∈ (chr (pch i)).source :=
      hUV i (p, z) (by rw [Metric.mem_ball, dist_zero_right]; exact lt_trans hp hεbr_two) hzV
    exact sep_sys_surj Ξ Q c hΞ hQ A B tR t'R (hγism i) (hβism i) (pch i) p z
      hγ1 hβ1 hreg.1 hreg.2 h0
  -- ### the parametric Sard
  obtain ⟨τ, hτnorm, hgood, hface, havoid⟩ :=
    goodFaceMulti m 4 r Kset hKset_compact (fun _ : Fin r => FaceIdx4)
      (fun _ : Fin r => fun t : FaceIdx4 => ↥(Fdir4 t)) (fun _ t => Fdir4_finrank_lt t)
      (fun _ : Fin r => fun t : FaceIdx4 => fun l : Fdir4 t => Fbase4 t + (l : Amb 4))
      (fun _ t => contDiff_Fparam4 t)
      (fun i : Fin r => fun t : FaceIdx4 => Fcov4 (Kset i) t)
      (fun i t => Fcov4_isCompact (Kset i) (hKset_compact i) t)
      (fun i => sepSys Ξ Q c A B tR t'R (γi i) (βi i) (pch i)) hΦsm εbr hεbrpos hsurj
  refine ⟨τ, lt_trans hτnorm hεbr', ?_, ?_⟩
  · -- ### the transversality clause
    refine ⟨fun z hzbox hmeet => ?_⟩
    have hv : sepNfam Ξ Q c A B tR t'R 0 z ∈ Ab := ⟨z, hzbox, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hv)
    -- the unperturbed (base) loop value lies in `C1 i`
    have hshift : Ξ (sepPathL A B (z 0) + τ) (coreLoop Q (z 1))
        = sepNfam Ξ Q c A B tR t'R 0 z := by
      rw [← sepLfam_apply Ξ Q A B τ z]
      exact hmeet
    have hbase : Ξ (sepPathL A B (z 0)) (coreLoop Q (z 1)) ∈ C1 i := by
      have hσ := hεa i (sepPathL A B (z 0) + τ)
        ⟨sepPathL A B (z 0), ⟨z 0, hzbox 0, rfl⟩, τ, by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact le_of_lt (lt_trans hτnorm hεbr1), rfl⟩
        (coreLoop Q (z 1)) ⟨z 1, hzbox 1, rfl⟩ (-τ)
        (by
          rw [norm_neg]
          exact lt_of_lt_of_le (lt_trans hτnorm hεbr_two) (le_of_lt (hεtwo_a i)))
        (by rw [hshift]; exact hi)
      simpa only [add_assoc, add_neg_cancel, add_zero] using interior_subset hσ
    have hzK : z ∈ Kset i := ⟨hzbox, hbase, interior_subset (hC0int i hi)⟩
    have hzV : z ∈ Vset i := hKsetVset i hzK
    have hγ1 : γi i τ = 1 := hγione i τ (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt (lt_of_lt_of_le hτnorm (le_of_lt hεbr_one)))
    have hβ1 : βi i z = 1 := hβione i z hzK
    have hregUV := hUV i (τ, z)
      (by rw [Metric.mem_ball, dist_zero_right]; exact lt_trans hτnorm hεbr_two) hzV
    have hcd0 : FamBox.chartDif (pch i) (sepLfam Ξ Q A B τ)
        (sepNfam Ξ Q c A B tR t'R τ) z = 0 := by
      rw [FamBox.chartDif_eq_zero_iff hregUV, sepLfam_apply Ξ Q A B τ z]
      exact hmeet
    have hΦ0 : sepSys Ξ Q c A B tR t'R (γi i) (βi i) (pch i) (τ, z) = 0 := by
      show (γi i τ * βi i z) • FamBox.chartDif (pch i) (sepLfam Ξ Q A B τ)
        (sepNfam Ξ Q c A B tR t'R τ) z = 0
      rw [hγ1, hβ1, mul_one, hcd0, smul_zero]
    have hgoodz := hgood i z hzK hΦ0
    have hχsurj : Function.Surjective (fderiv ℝ (fun z' : Amb 4 =>
        FamBox.chartDif (pch i) (sepLfam Ξ Q A B τ) (sepNfam Ξ Q c A B tR t'R τ) z') z) := by
      rw [← sep_sys_zderiv_eq Ξ Q c hΞ hQ A B tR t'R (hβism i) (pch i) τ z hγ1 hβ1
        hregUV.1 hregUV.2 hΦ0]
      exact hgoodz
    have heq : sepLfam Ξ Q A B τ z = sepNfam Ξ Q c A B tR t'R τ z := by
      rw [sepLfam_apply Ξ Q A B τ z]
      exact hmeet
    have hLf := sep_Lf_surj Ξ Q c hΞ hQ A B tR t'R (pch i) τ z hregUV.1 hregUV.2 heq hχsurj
    have hF : sepLfam Ξ Q A B τ = famLoop (chartLoopFam (sepQfam Ξ Q A B τ)) := by
      funext z'
      rw [sepLfam]
    have hG : sepNfam Ξ Q c A B tR t'R τ
        = famChain (sweepFam c (fun u => 1 - u) (sepPfam Ξ Q tR t'R A B 0)) := by
      funext z'
      rw [sepNfam, sepNc]
    rw [hF, hG] at hLf
    exact hLf
  · -- ### the face clause
    refine ⟨fun z hzbox hmeet hbdry => ?_⟩
    have hv : sepNfam Ξ Q c A B tR t'R 0 z ∈ Ab := ⟨z, hzbox, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hv)
    have hshift : Ξ (sepPathL A B (z 0) + τ) (coreLoop Q (z 1))
        = sepNfam Ξ Q c A B tR t'R 0 z := by
      rw [← sepLfam_apply Ξ Q A B τ z]
      exact hmeet
    have hbase : Ξ (sepPathL A B (z 0)) (coreLoop Q (z 1)) ∈ C1 i := by
      have hσ := hεa i (sepPathL A B (z 0) + τ)
        ⟨sepPathL A B (z 0), ⟨z 0, hzbox 0, rfl⟩, τ, by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact le_of_lt (lt_trans hτnorm hεbr1), rfl⟩
        (coreLoop Q (z 1)) ⟨z 1, hzbox 1, rfl⟩ (-τ)
        (by
          rw [norm_neg]
          exact lt_of_lt_of_le (lt_trans hτnorm hεbr_two) (le_of_lt (hεtwo_a i)))
        (by rw [hshift]; exact hi)
      simpa only [add_assoc, add_neg_cancel, add_zero] using interior_subset hσ
    have hzK : z ∈ Kset i := ⟨hzbox, hbase, interior_subset (hC0int i hi)⟩
    have hzV : z ∈ Vset i := hKsetVset i hzK
    have hγ1 : γi i τ = 1 := hγione i τ (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt (lt_of_lt_of_le hτnorm (le_of_lt hεbr_one)))
    have hβ1 : βi i z = 1 := hβione i z hzK
    have hregUV := hUV i (τ, z)
      (by rw [Metric.mem_ball, dist_zero_right]; exact lt_trans hτnorm hεbr_two) hzV
    have hcd0 : FamBox.chartDif (pch i) (sepLfam Ξ Q A B τ)
        (sepNfam Ξ Q c A B tR t'R τ) z = 0 := by
      rw [FamBox.chartDif_eq_zero_iff hregUV, sepLfam_apply Ξ Q A B τ z]
      exact hmeet
    have hΦ0 : sepSys Ξ Q c A B tR t'R (γi i) (βi i) (pch i) (τ, z) = 0 := by
      show (γi i τ * βi i z) • FamBox.chartDif (pch i) (sepLfam Ξ Q A B τ)
        (sepNfam Ξ Q c A B tR t'R τ) z = 0
      rw [hγ1, hβ1, mul_one, hcd0, smul_zero]
    -- no meet at two faces
    have hnoTwo : ¬ ∃ (i' j' : Fin 5), i' ≠ j' ∧ (z i' = 0 ∨ z i' = 1) ∧ (z j' = 0 ∨ z j' = 1) := by
      rintro ⟨i', j', hne, hi', hj'⟩
      obtain ⟨t', l, hl, hlz⟩ := Fcov4_cover (Kset i) hzK ⟨i', j', hne, hi', hj'⟩
      have hne0 := havoid i t' l hl
      rw [hlz] at hne0
      exact hne0 hΦ0
    -- exactly one face coordinate
    obtain ⟨i0, hi0⟩ := hbdry.2
    have hrest : ∀ j : Fin 5, j ≠ i0 → z j ∈ Set.Ioo (0 : ℝ) 1 := by
      intro j hj
      have hboxj := hzbox j
      refine ⟨?_, ?_⟩
      · rcases lt_or_eq_of_le hboxj.1 with h | h
        · exact h
        · exact absurd h (fun hh => hnoTwo ⟨i0, j, hj.symm, hi0, Or.inl hh.symm⟩)
      · rcases lt_or_eq_of_le hboxj.2 with h | h
        · exact h
        · exact absurd h (fun hh => hnoTwo ⟨i0, j, hj.symm, hi0, Or.inr hh⟩)
    -- the crossing
    have hgoodz := hgood i z hzK hΦ0
    have hχsurj : Function.Surjective (fderiv ℝ (fun z' : Amb 4 =>
        FamBox.chartDif (pch i) (sepLfam Ξ Q A B τ) (sepNfam Ξ Q c A B tR t'R τ) z') z) := by
      rw [← sep_sys_zderiv_eq Ξ Q c hΞ hQ A B tR t'R (hβism i) (pch i) τ z hγ1 hβ1
        hregUV.1 hregUV.2 hΦ0]
      exact hgoodz
    have hface0 : Function.Surjective (fun v : {v : Amb 4 // v i0 = 0} =>
        fderiv ℝ (fun z' : Amb 4 => sepSys Ξ Q c A B tR t'R (γi i) (βi i) (pch i)
          (τ, z')) z v.1) :=
      hface i i0 z hzK hΦ0 (by rcases hi0 with h | h <;> [exact Or.inl h; exact Or.inr h])
    have hfaceχ : Function.Surjective (fun v : {v : Amb 4 // v i0 = 0} =>
        fderiv ℝ (fun z' : Amb 4 => FamBox.chartDif (pch i) (sepLfam Ξ Q A B τ)
          (sepNfam Ξ Q c A B tR t'R τ) z') z v.1) := by
      rw [sep_sys_zderiv_eq Ξ Q c hΞ hQ A B tR t'R (hβism i) (pch i) τ z hγ1 hβ1
        hregUV.1 hregUV.2 hΦ0] at hface0
      exact hface0
    have heq : sepLfam Ξ Q A B τ z = sepNfam Ξ Q c A B tR t'R τ z := by
      rw [sepLfam_apply Ξ Q A B τ z]
      exact hmeet
    obtain ⟨σ, hσker, hσi⟩ := sep_exists_sigma_of_faceSurjective (pch i)
      (sepLfam Ξ Q A B τ) (sepNfam Ξ Q c A B tR t'R τ)
      (sepLfam_slice_contMDiff Ξ Q hΞ hQ A B τ)
      (sepNfam_slice_contMDiff Ξ Q c hΞ hQ A B tR t'R τ) hregUV heq hχsurj hfaceχ
    refine ⟨i0, ?_, hrest, σ, ?_, hσi⟩
    · rcases hi0 with h | h
      · exact Or.inl h
      · exact Or.inr h
    · have h : FamBox.Lf (sepLfam Ξ Q A B τ) (sepNfam Ξ Q c A B tR t'R τ) z σ = 0 := hσker
      have hF : sepLfam Ξ Q A B τ = famLoop (chartLoopFam (sepQfam Ξ Q A B τ)) := by
        funext z'
        rw [sepLfam]
      have hG : sepNfam Ξ Q c A B tR t'R τ
          = famChain (sweepFam c (fun u => 1 - u) (sepPfam Ξ Q tR t'R A B 0)) := by
        funext z'
        rw [sepNfam, sepNc]
      rw [hF, hG, FamBox.Lf, sub_apply, sub_eq_zero] at h
      exact h


/-- **The Sard obligation `Work.Drive.sep_fam_regular` of the separated germ route.** -/
theorem sep_fam_regular_proof {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ)
    (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q) (hc : 0 < c)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tR t'R : ℝ)
    (ε' : ℝ) (hε' : 0 < ε') :
    ∃ τ₁ τ₂ : EuclideanSpace ℝ (Fin m), ‖τ₁‖ < ε' ∧ ‖τ₂‖ < ε' ∧
      SepRegular Ξ Q c tR t'R A B τ₁ τ₂ := by
  obtain ⟨τ, hτ, ht, hf⟩ := sep_fam_regular_core Ξ Q c hΞ hQ A B tR t'R hε'
  exact ⟨τ, 0, hτ, by simpa using hε',
    SepRegular.of_pieces (sep_fam_smooth Ξ Q c hΞ hQ hc A B tR t'R τ 0) ht hf⟩

end

end Work.Drive
