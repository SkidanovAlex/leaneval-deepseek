import Mathlib
import Submission.Work.Drive.Final.dentOut_resolvedCond
import Submission.Work.Drive.Final.dentOut_trace
import Submission.Work.Drive.Final.dentOut_hgen
import Submission.Work.Drive.Final.dentOut_sweep_subset
import Submission.Work.Drive.Final.dentOut_resolvedCond_of_families
import Submission.Work.Drive.Final.exists_dentOut_trace_family
import Submission.Work.Drive.Final.windingSpan_dentOutRegion_eq_bot
import Submission.Work.Drive.Final.dentOut_hgen_of_trace
import Submission.Work.Drive.Final.gates_local
import Submission.Work.Drive.Final.windingSpan_dentOutRegion_bot_or_top
import Submission.Work.Drive.Final.eventGates
import Submission.Work.Drive.Final.faceEventGates
import Submission.Work.Drive.Final.cornerGates
import Submission.Work.Drive.Mono.SweepGeom3
import Submission.Work.InnermostDisk.exists_ball_not_isEssential

open scoped Topology

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion Set
open scoped ENNReal

noncomputable section

theorem exists_section_nhds_param (P : Work.CoreTopology.ParamTorus) (X : R3)
    (hX : X ∈ P.carrier) :
    ∃ (s : Set R3) (σ : C(s, ℝ × ℝ)), X ∈ s ∧ (∀ x ∈ s, x ∈ P.carrier) ∧
      (∀ x : s, P.psi (σ x).1 (σ x).2 = (x : R3)) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ P.carrier, dist x X < ε → x ∈ s) := by
  have hcarrier : P.carrier = Set.range (Work.TorusCover.psiMap P.psi) := rfl
  set FS : Set R3 := Set.range (Work.TorusCover.psiMap P.psi) with hFS
  have hcov : IsCoveringMap (Work.TorusCover.psiMapToRange P.psi) :=
    Work.TorusCover.isCoveringMap_psiMapToRange_param P
  have hf : IsLocalHomeomorph (Work.TorusCover.psiMapToRange P.psi) :=
    hcov.isLocalHomeomorph
  have hXψ : X ∈ FS := hcarrier ▸ hX
  let X' : FS := ⟨X, hXψ⟩
  obtain ⟨p, hp⟩ : ∃ p : ℝ × ℝ, Work.TorusCover.psiMapToRange P.psi p = X' := by
    obtain ⟨p, hp⟩ := Set.mem_range.mp X'.2
    exact ⟨p, Subtype.ext hp⟩
  let e : OpenPartialHomeomorph FS (ℝ × ℝ) := hf.localInverseAt p
  have hX'_source : X' ∈ e.source := by
    have h := hf.apply_self_mem_localInverseAt_source (x := p)
    rw [← hp]; exact h
  have hsec : ∀ y ∈ e.source, Work.TorusCover.psiMapToRange P.psi (e y) = y := by
    intro y hy
    exact hf.apply_localInverseAt_of_mem (x := p) hy
  have hEmb : _root_.Topology.IsEmbedding (Subtype.val : FS → R3) :=
    _root_.Topology.IsEmbedding.subtypeVal
  have hpre : (Subtype.val ⁻¹' (Subtype.val '' e.source) : Set FS) = e.source :=
    Set.preimage_image_eq e.source hEmb.injective
  have hs_range : (Subtype.val '' e.source : Set R3) ⊆ Set.range (Subtype.val : FS → R3) :=
    Set.image_subset_range _ _
  let homeo : (Subtype.val ⁻¹' (Subtype.val '' e.source) : Set FS) ≃ₜ
      (Subtype.val '' e.source : Set R3) := hEmb.homeomorphOfSubsetRange hs_range
  have hσcont : Continuous (fun x : (Subtype.val '' e.source : Set R3) => e (homeo.symm x)) := by
    have hcont : Continuous ((Subtype.val ⁻¹' (Subtype.val '' e.source) : Set FS).domRestrict
        (fun y : FS => (e : FS → ℝ × ℝ) y)) := by
      have h := e.continuousOn
      rw [← hpre] at h
      exact h.domRestrict
    exact hcont.comp homeo.symm.continuous
  refine ⟨Subtype.val '' e.source, ⟨fun x => e (homeo.symm x), hσcont⟩, ?_, ?_, ?_, ?_⟩
  · exact ⟨X', hX'_source, rfl⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hcarrier.symm ▸ y.2
  · intro x
    have h1 : (homeo (homeo.symm x) : R3) = (homeo.symm x : R3) :=
      hEmb.homeomorphOfSubsetRange_apply_coe hs_range (homeo.symm x)
    have h2 : (homeo (homeo.symm x) : R3) = (x : R3) :=
      congrArg Subtype.val (homeo.apply_symm_apply x)
    have hxy : (x : R3) = (homeo.symm x : R3) := h2.symm.trans h1
    have hy_src : (homeo.symm x : FS) ∈ e.source := by
      obtain ⟨z, hz, hzx⟩ := (homeo.symm x).2
      have hz' : z = (homeo.symm x : FS) := hEmb.injective hzx
      rwa [hz'] at hz
    have hsecx := hsec (↑(homeo.symm x)) hy_src
    have hfinal : Work.TorusCover.psiMap P.psi (e ↑(homeo.symm x)) = (x : R3) := by
      trans (homeo.symm x : R3)
      · exact congrArg Subtype.val hsecx
      · exact hxy.symm
    simpa [Work.TorusCover.psiMap] using hfinal
  · obtain ⟨V, hVopen, hVpre⟩ := isOpen_induced_iff.mp e.open_source
    have hs_eq : (Subtype.val '' e.source : Set R3) = V ∩ P.carrier := by
      rw [← hVpre, Set.image_preimage_eq_inter_range, Subtype.range_val, ← hcarrier]
    have hX_in_V : X ∈ V := by
      have hmem : X ∈ (Subtype.val '' e.source : Set R3) := ⟨X', hX'_source, rfl⟩
      rw [hs_eq] at hmem
      exact hmem.1
    obtain ⟨ε, hεpos, hεball⟩ := (Metric.isOpen_iff.mp hVopen) X hX_in_V
    refine ⟨ε, hεpos, ?_⟩
    intro x hxcarrier hdist
    have hxV : x ∈ V := hεball (by rw [Metric.mem_ball]; exact hdist)
    rw [hs_eq]
    exact ⟨hxV, hxcarrier⟩

theorem exists_ball_not_isEssential_param (P : Work.CoreTopology.ParamTorus) (X : R3)
    (hX : X ∈ P.carrier) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ γ : Work.CoreTopology.ClosedCurve P,
      (∀ t : ℝ, γ.γ t ∈ Metric.ball X ε) → ¬ Work.CoreTopology.IsEssential P γ := by
  obtain ⟨s, σ, -, -, hσ, ε, hεpos, hε⟩ := exists_section_nhds_param P X hX
  refine ⟨ε, hεpos, fun γ hγ => ?_⟩
  exact Work.InnermostDisk.not_isEssential_of_section (P := P) σ hσ (γ := γ)
    (fun t => hε (γ.γ t) (γ.mem t) (Metric.mem_ball.mp (hγ t)))

theorem windingSpan_carrier_inter_ball_eq_bot (P : Work.CoreTopology.ParamTorus) {X : R3}
    (hX : X ∈ P.carrier) :
    ∃ ε : ℝ, 0 < ε ∧
      Work.SurgeryInvariance.WindingSpan P (P.carrier ∩ Metric.ball X ε) = ⊥ := by
  obtain ⟨ε, hεpos, hε⟩ := exists_ball_not_isEssential_param P X hX
  refine ⟨ε, hεpos, ?_⟩
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  rintro ⟨γ, hγess, hγ⟩
  exact hε γ (fun t => (hγ t).2) hγess

/-- **A disjoint union of two carrier-open inessential regions is inessential.**  A closed curve of
the surface whose image lies in `A ∪ E` with `A ∩ E = ∅` lies in `A` or in `E`: its image is
connected and covered by the two disjoint carrier-open sets. -/
theorem windingSpan_union_eq_bot_of_disjoint {P : Work.CoreTopology.ParamTorus} {A E : Set R3}
    (hdisj : A ∩ E = ∅) (hAopen : Work.SurgeryInvariance.IsOpenInCarrier P A)
    (hEopen : Work.SurgeryInvariance.IsOpenInCarrier P E)
    (hA : Work.SurgeryInvariance.WindingSpan P A = ⊥)
    (hE : Work.SurgeryInvariance.WindingSpan P E = ⊥) :
    Work.SurgeryInvariance.WindingSpan P (A ∪ E) = ⊥ := by
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff] at hA hE ⊢
  rintro ⟨γ, hγess, hγ⟩
  set γ' : ℝ → P.carrier := fun t => ⟨γ.γ t, γ.mem t⟩ with hγ'def
  have hcont : Continuous γ' := by
    rw [continuous_induced_rng]
    exact γ.cont
  have hpc : IsPreconnected (Set.range γ') := isPreconnected_range hcont
  have hsub : Set.range γ' ⊆ {x : P.carrier | (x : R3) ∈ A} ∪ {x : P.carrier | (x : R3) ∈ E} := by
    rintro _ ⟨t, rfl⟩
    rcases hγ t with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hdisj' : Disjoint {x : P.carrier | (x : R3) ∈ A} {x : P.carrier | (x : R3) ∈ E} := by
    rw [Set.disjoint_left]
    rintro x hx1 hx2
    have hmem : (x : R3) ∈ A ∩ E := ⟨hx1, hx2⟩
    rw [hdisj] at hmem
    exact hmem
  have hAopen' : IsOpen {x : P.carrier | (x : R3) ∈ A} := hAopen
  have hEopen' : IsOpen {x : P.carrier | (x : R3) ∈ E} := hEopen
  rcases IsPreconnected.subset_or_subset hAopen' hEopen' hdisj' hsub hpc with h | h
  · exact hA ⟨γ, hγess, fun t => h ⟨t, rfl⟩⟩
  · exact hE ⟨γ, hγess, fun t => h ⟨t, rfl⟩⟩

/-- **The two-gates condition** consumed by
`Work.Drive.Final.finrank_union_le_one_of_two_gates_nonconn`, from a gate decomposition
`A ∩ E = U₁ ∪ U₂` with `U₁`, `U₂` empty or path connected and contained in `E`. -/
theorem two_gates_cond {P : Work.CoreTopology.ParamTorus} {A E U₁ U₂ : Set R3}
    (hAc : A ⊆ P.carrier) (hEc : E ⊆ P.carrier)
    (hAopen : Work.SurgeryInvariance.IsOpenInCarrier P A)
    (hEopen : Work.SurgeryInvariance.IsOpenInCarrier P E)
    (hAE : A ∩ E = U₁ ∪ U₂) (hU₁ : U₁ = ∅ ∨ IsPathConnected U₁)
    (hU₂ : U₂ = ∅ ∨ IsPathConnected U₂) (hU₁E : U₁ ⊆ E) (hU₂E : U₂ ⊆ E)
    (hne : (A ∩ E).Nonempty) :
    ∃ a b : R3, IsPathConnected (A ∩ E ∩ connectedComponentIn (A ∩ E) a) ∧
      A ∩ E ⊆ connectedComponentIn (A ∩ E) a ∪ connectedComponentIn (A ∩ E) b := by
  classical
  have hABopen : Work.SurgeryInvariance.IsOpenInCarrier P (A ∩ E) :=
    Work.SurgeryInvariance.isOpenInCarrier_inter P hAopen hEopen
  have hABc : A ∩ E ⊆ P.carrier := fun z hz => hAc hz.1
  have key : ∀ a : R3, a ∈ A ∩ E →
      IsPathConnected (A ∩ E ∩ connectedComponentIn (A ∩ E) a) := by
    intro a ha
    rw [Set.inter_eq_right.mpr (connectedComponentIn_subset (A ∩ E) a)]
    exact Work.PinchLemma3.ClosedDiscA.isPathConnected_connectedComponentIn_carrier
      hABopen hABc ha
  by_cases h1 : U₁ = ∅
  · have hAE' : A ∩ E = U₂ := by rw [hAE, h1, Set.empty_union]
    have hUne : U₂ ≠ ∅ := fun h => by
      obtain ⟨x, hx⟩ := (show U₂.Nonempty from hAE' ▸ hne)
      rw [h] at hx
      exact hx
    obtain ⟨a, haU⟩ := (show U₂.Nonempty from hAE' ▸ hne)
    have hU₂pc : IsPathConnected U₂ := by
      rcases hU₂ with h | h
      · exact absurd h hUne
      · exact h
    refine ⟨a, a, key a (by rw [hAE']; exact haU), ?_⟩
    intro z hz
    have hzU : z ∈ U₂ := by rw [← hAE']; exact hz
    have hsub : U₂ ⊆ A ∩ E := fun w hw => by rw [hAE']; exact hw
    have hmem : U₂ ⊆ connectedComponentIn (A ∩ E) a :=
      hU₂pc.isConnected.isPreconnected.subset_connectedComponentIn haU hsub
    exact Or.inl (hmem hzU)
  · obtain ⟨a, haU₁⟩ := Set.nonempty_iff_ne_empty.mpr h1
    have hU₁pc : IsPathConnected U₁ := by
      rcases hU₁ with h | h
      · exact absurd h h1
      · exact h
    have haAE : a ∈ A ∩ E := by rw [hAE]; exact Or.inl haU₁
    have hsub₁ : U₁ ⊆ A ∩ E := fun w hw => by rw [hAE]; exact Or.inl hw
    have hmem₁ : U₁ ⊆ connectedComponentIn (A ∩ E) a :=
      hU₁pc.isConnected.isPreconnected.subset_connectedComponentIn haU₁ hsub₁
    by_cases h2 : U₂ = ∅
    · have hAE' : A ∩ E = U₁ := by rw [hAE, h2, Set.union_empty]
      refine ⟨a, a, key a (by rw [hAE']; exact haU₁), ?_⟩
      intro z hz
      exact Or.inl (hmem₁ (by rw [← hAE']; exact hz))
    · obtain ⟨b, hbU₂⟩ := Set.nonempty_iff_ne_empty.mpr h2
      have hU₂pc : IsPathConnected U₂ := by
        rcases hU₂ with h | h
        · exact absurd h h2
        · exact h
      have hsub₂ : U₂ ⊆ A ∩ E := fun w hw => by rw [hAE]; exact Or.inr hw
      have hmem₂ : U₂ ⊆ connectedComponentIn (A ∩ E) b :=
        hU₂pc.isConnected.isPreconnected.subset_connectedComponentIn hbU₂ hsub₂
      refine ⟨a, b, key a haAE, ?_⟩
      intro z hz
      have hzU : z ∈ U₁ ∪ U₂ := by rw [← hAE]; exact hz
      rcases hzU with hz | hz
      · exact Or.inl (hmem₁ hz)
      · exact Or.inr (hmem₂ hz)

theorem noJumpAtAnyEventCond_of_eventTraceData
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ}
    {exc : Finset ℝ} {lam0 lam1 : ℝ}
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    (hwin : ∀ pp : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp →
      ℓ (Work.BoxShrink.Pinch.par ψ pp) ∈ Set.Icc lam0 lam1)
    {d : ℝ} (hd : 0 ≤ d) (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (hs : 0 < s)
    (hS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)))
    (hslice : Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
      {y : R3 | Submission.boxNorm c σ y = s})
    (hdata : Work.Drive.Final.EventTraceData ψ K s c σ u v h R ℓ) :
    Work.Drive.Final.NoJumpAtAnyEventCond ψ K s c σ u v h R ℓ := by
  classical
  intro p₀ hp₀ U₀ hU₀
  -- ## 0. the tilt data and the descent direction
  obtain ⟨-, hv1, hℓne, hℓv, -⟩ := hDP.1.tilt
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv1
    exact one_ne_zero hv1.symm
  have hdesc : ∃ w : R3, inner ℝ v w = 0 ∧ ℓ w < 0 :=
    Work.Drive.Final.exists_descend_of_inner_eq_zero hv0 hℓne hℓv
  have hG3 : Work.Drive.Final.GoodSweepData3 ψ K s c σ u v h R ℓ exc lam0 lam1 := hDP.2.1
  have hcarr : Work.BoxShrink.Pinch.par ψ p₀ ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier :=
    Work.BoxShrink.Pinch.par_mem_carrier ψ p₀
  -- ## 1. the local inessentiality radius at the event's image
  obtain ⟨ε₁, hε₁pos, hε₁bot⟩ :=
    windingSpan_carrier_inter_ball_eq_bot (Work.Drive.EpsSphere.torusOf ψ) hcarr
  -- ## 2. the localised gates at radius `ε₁ / 2`
  have hgates := Work.Drive.Final.gates_local hG3 hp₀ (ρ := ε₁ / 2) (by positivity)
  obtain ⟨E, U₁, U₂, hEopen, hEinner, hEsmall, hU₁pc, hU₂pc, hU₁E, hU₂E, hgate⟩ := hgates
  obtain ⟨ε₂, hε₂pos, hε₂⟩ := hEinner
  -- ## 3. the datum, at a neighbourhood inside both balls
  set ε₃ : ℝ := min ε₂ (ε₁ / 2) with hε₃def
  have hε₃pos : 0 < ε₃ := lt_min hε₂pos (by linarith)
  set U : Set R3 := U₀ ∩ Metric.ball (Work.BoxShrink.Pinch.par ψ p₀) ε₃ with hUdef
  have hU : U ∈ nhds (Work.BoxShrink.Pinch.par ψ p₀) :=
    Filter.inter_mem hU₀ (Metric.ball_mem_nhds _ hε₃pos)
  obtain ⟨D, hDp, hr4, ha', m, Ss, hsph, hfront, hdisj, htame⟩ := hdata p₀ hp₀ U hU
  -- ## 4. the trace family of the deformed level
  have hlev : ℓ D.centre ∈ Set.Icc lam0 lam1 := by
    rw [D.centre_eq, hDp]
    exact hwin p₀ hp₀
  have hcnt := hDP.2.2 (ℓ D.centre) hlev
  obtain ⟨n, cs, hsimple, hess, hdisjcs, hcsZ⟩ :=
    Work.Drive.Final.exists_dentOut_trace_family (ψ := ψ) (K := K) p q hp hq hc himg hcl D ha'
      hsph hdisj hfront hcnt htame
  have hUsub : U ⊆ U₀ := fun z hz => hz.1
  have hsub_cover : (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) ⊆
      ⋃ i, Set.range (cs i).γ := le_of_eq hcsZ
  have hdisjΩ : Disjoint (Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D)
      (⋃ i, Set.range (cs i).γ) := by
    rw [← hcsZ, Set.disjoint_left]
    intro z hzΩ hzT
    exact Set.disjoint_left.mp disjoint_interior_frontier hzΩ.2 hzT.2
  have hgen : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ closure (Submission.PBox s c σ) →
      |Work.Drive.Final.slabFn c u v z| ≤ h → ℓ z = ℓ D.centre →
      z ∈ closure (Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D) ∪ ⋃ i, Set.range (cs i).γ := by
    intro z hzc hzbox hzslab hzℓ
    exact Work.Drive.Final.dentOut_hgen_of_trace hG3 D (le_of_eq hcsZ) hzc hzbox hzslab hzℓ
  have hspan : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
      (Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ
        (ℓ D.centre)) = ⊥ →
      Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D) = ⊥ := by

    intro hXbot
    set X : Set R3 := Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ)
      s c σ u v h ℓ (ℓ D.centre) with hXdef
    set Ω : Set R3 := Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D with hΩdef
    have hXc : X ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier := fun z hz => hz.1
    have hXopen : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ) X :=
      Work.Drive.EpsFormSphere.isOpenInCarrier_openTiltedSweepRegion
    have hE'open : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ)
        (E ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) := by
      rw [Work.SurgeryInvariance.IsOpenInCarrier] at hEopen ⊢
      have heq : (Subtype.val ⁻¹' (E ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) :
          Set (Work.Drive.EpsSphere.torusOf ψ).carrier) = Subtype.val ⁻¹' E := by
        ext x
        exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩
      rw [heq]
      exact hEopen
    have hE'bot : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (E ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) = ⊥ := by
      rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff] at hε₁bot
      rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
      rintro ⟨γ, hγess, hγ⟩
      refine hε₁bot ⟨γ, hγess, fun t => ⟨γ.mem t, ?_⟩⟩
      have h1 : γ.γ t ∈ Metric.ball (Work.BoxShrink.Pinch.par ψ p₀) (ε₁ / 2) :=
        hEsmall (hγ t).1
      rw [Metric.mem_ball] at h1 ⊢
      linarith
    have hcoverΩ : Ω ⊆ X ∪ (E ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) := by
      intro z hz
      rcases Work.Drive.Final.dentOutRegion_subset_sweepRegion_union_ball D hdesc hz with hh | hh
      · exact Or.inl hh
      · refine Or.inr ⟨?_, Work.Drive.Final.dentOutRegion_subset_carrier D hz⟩
        have h1 : z ∈ U := D.ball_sub z (by
          have hb : ‖z - D.centre‖ ≤ D.r := by
            rw [Metric.mem_closedBall, dist_eq_norm] at hh
            exact hh
          linarith [hb, D.δ_pos])
        have h2 : z ∈ Metric.ball (Work.BoxShrink.Pinch.par ψ p₀) ε₃ := h1.2
        have h3 : z ∈ Metric.ball (Work.BoxShrink.Pinch.par ψ p₀) ε₂ := by
          rw [Metric.mem_ball] at h2 ⊢
          have := min_le_left ε₂ (ε₁ / 2)
          linarith
        exact hε₂ ⟨h3, Work.Drive.Final.dentOutRegion_subset_carrier D hz⟩
    -- the gate decomposition of `X ∩ E`
    have hU₁c : U₁ ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier := by
      intro w hw
      have h1 : w ∈ Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ)
          s c σ u v h ℓ (Work.Drive.Final.eventValue ψ ℓ p₀) ∩ E := by
        rw [hgate]
        exact Or.inl hw
      exact h1.1.1
    have hU₂c : U₂ ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier := by
      intro w hw
      have h1 : w ∈ Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ)
          s c σ u v h ℓ (Work.Drive.Final.eventValue ψ ℓ p₀) ∩ E := by
        rw [hgate]
        exact Or.inr hw
      exact h1.1.1
    have hEV : Work.Drive.Final.eventValue ψ ℓ p₀ = ℓ D.centre := by
      rw [Work.Drive.Final.eventValue, ← hDp, ← D.centre_eq]
    have hAE : X ∩ (E ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) = U₁ ∪ U₂ := by
      rw [hXdef, ← Set.inter_assoc, ← hEV, hgate, Set.union_inter_distrib_right,
        Set.inter_eq_left.mpr hU₁c, Set.inter_eq_left.mpr hU₂c]
    -- the rank bound
    have hfin : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan
        (Work.Drive.EpsSphere.torusOf ψ) (X ∪ (E ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier))) ≤ 1 := by
      by_cases hne : (X ∩ (E ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)).Nonempty
      · refine Work.Drive.Final.finrank_union_le_one_of_two_gates_nonconn hXc
          Set.inter_subset_right hXopen hE'open hXbot hE'bot ?_
        exact two_gates_cond hXc Set.inter_subset_right hXopen hE'open hAE hU₁pc hU₂pc
          (fun w hw => ⟨hU₁E hw, hU₁c hw⟩) (fun w hw => ⟨hU₂E hw, hU₂c hw⟩) hne
      · rw [Set.not_nonempty_iff_eq_empty] at hne
        have hbot : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
            (X ∪ (E ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)) = ⊥ := by
          refine windingSpan_union_eq_bot_of_disjoint ?_ hXopen hE'open hXbot hE'bot
          rw [hne]
        rw [hbot]
        simp
    -- the dichotomy for `Ω₁` and the conclusion
    have hdich : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ) Ω = ⊥ ∨
        Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ) Ω = ⊤ := by
      have hnoF : ¬ (Work.Drive.EpsSphere.torusOf ψ).ContainsEssentialLoop
          (frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))) :=
        Work.Drive.Final.dentOut_trace_noEssential_of_sphereCover (ψ := ψ) (K := K) p q hp hq hc
          himg hcl D ha' hsph hdisj hfront hcnt htame
      have hno : ¬ (Work.Drive.EpsSphere.torusOf ψ).ContainsEssentialLoop
          ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
            frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))) :=
        fun hcon => hnoF (Work.CoreTopology.ParamTorus.containsEssentialLoop_mono _
          Set.inter_subset_right hcon)
      exact Work.Drive.Final.windingSpan_dentOutRegion_bot_or_top D ha' hsph hfront hdisj htame hno
    rcases hdich with hbot | htop
    · exact hbot
    · exfalso
      have hle := Work.SurgeryInvariance.WindingSpan_mono (Work.Drive.EpsSphere.torusOf ψ) hcoverΩ
      have h2 := le_trans (Submodule.finrank_mono hle) hfin
      rw [htop, finrank_top, Module.finrank_prod, Module.finrank_self] at h2
      norm_num at h2

  refine ⟨{ D with ball_sub := fun z hz => hUsub (D.ball_sub z hz) }, hDp, ?_⟩
  exact ⟨⟨n, cs, hsimple, hess, hdisjcs, hsub_cover, hdisjΩ, hgen⟩, hspan⟩

end

end Work.Drive.Final
