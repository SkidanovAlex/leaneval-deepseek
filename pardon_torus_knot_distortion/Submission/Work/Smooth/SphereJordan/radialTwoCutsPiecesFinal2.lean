import Mathlib
import Submission.Work.Smooth.SphereJordan.radialTwoCutsSetup
import Submission.Work.Smooth.SphereJordan.radialTwoCutsComponents

namespace Work.Smooth.SphereJordan

open Set Metric

noncomputable section

/-- **The preimage of a closure is the closure of the preimage**, for a set of the finite part of
the sphere.  (Local copy, under a fresh name, of `Work.Smooth.SphereJordan.preimage_closure_coe`
from `plane_pieces`; this module must not import that family.) -/
theorem preimage_closure_coe_pieces2 {Q : Set RiemannSphere}
    (hQ : Q ⊆ Set.range ((↑) : ℂ → RiemannSphere)) :
    ((↑) ⁻¹' closure Q : Set ℂ) = closure ((↑) ⁻¹' Q : Set ℂ) := by
  refine Subset.antisymm ?_ ?_
  · intro z hz
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hVopen : IsOpen (((↑) : ℂ → RiemannSphere) '' Metric.ball z ε) :=
      OnePoint.isOpenMap_coe _ Metric.isOpen_ball
    have hVmem : ((z : ℂ) : RiemannSphere) ∈ ((↑) : ℂ → RiemannSphere) '' Metric.ball z ε :=
      ⟨z, Metric.mem_ball_self hε, rfl⟩
    obtain ⟨y, ⟨w, hw, hwy⟩, hyQ⟩ := mem_closure_iff.mp hz _ hVopen hVmem
    refine ⟨w, ?_, ?_⟩
    · show ((w : ℂ) : RiemannSphere) ∈ Q
      rw [hwy]; exact hyQ
    · simpa [Metric.mem_ball, dist_comm] using hw
  · exact closure_minimal (fun y hy => subset_closure hy)
      (isClosed_closure.preimage OnePoint.continuous_coe)

/-- **Transporting a disc-closure statement from the sphere to the plane.**  If `Q` lies in the
image of the open unit ball, so that `closure Q` lies in the image of the closed unit ball (a
compact, hence finite, subset of the sphere), then a disc parametrisation of `closure Q` in the
sphere yields a disc parametrisation of the closure of the preimage `↑ ⁻¹' Q`. -/
theorem exists_disc_closure_preimage_coe_pieces2 {Q : Set RiemannSphere}
    (hQ : Q ⊆ ((↑) : ℂ → RiemannSphere) '' Metric.ball (0 : ℂ) 1)
    (hcl : ∃ Φ : C(Disc, RiemannSphere), Function.Injective Φ ∧ Set.range Φ = closure Q) :
    ∃ Ξ : C(Disc, ℂ), Function.Injective Ξ ∧ Set.range Ξ = closure ((↑) ⁻¹' Q : Set ℂ) := by
  obtain ⟨Φ, hΦinj, hΦrange⟩ := hcl
  have hrange : Q ⊆ Set.range ((↑) : ℂ → RiemannSphere) :=
    hQ.trans (Set.image_subset_range _ _)
  have hclos : closure Q ⊆ Set.range ((↑) : ℂ → RiemannSphere) :=
    (closure_minimal (hQ.trans (Set.image_mono Metric.ball_subset_closedBall))
      (((isCompact_closedBall (0 : ℂ) 1).image OnePoint.continuous_coe).isClosed)).trans
      (Set.image_subset_range _ _)
  have hΦsub : Set.range Φ ⊆ Set.range ((↑) : ℂ → RiemannSphere) := hΦrange ▸ hclos
  have hEmb : Topology.IsEmbedding ((↑) : ℂ → RiemannSphere) :=
    OnePoint.isOpenEmbedding_coe.toIsEmbedding
  let f : Disc → ℂ := fun z => hEmb.toHomeomorph.symm ⟨Φ z, hΦsub ⟨z, rfl⟩⟩
  have hfcoe : ∀ z : Disc, ((f z : ℂ) : RiemannSphere) = Φ z := by
    intro z
    have h1 : hEmb.toHomeomorph (hEmb.toHomeomorph.symm ⟨Φ z, hΦsub ⟨z, rfl⟩⟩)
        = ⟨Φ z, hΦsub ⟨z, rfl⟩⟩ := Homeomorph.apply_symm_apply _ _
    have h2 : ((hEmb.toHomeomorph (hEmb.toHomeomorph.symm ⟨Φ z, hΦsub ⟨z, rfl⟩⟩) :
        Set.range ((↑) : ℂ → RiemannSphere)) : RiemannSphere)
        = (((hEmb.toHomeomorph.symm ⟨Φ z, hΦsub ⟨z, rfl⟩⟩ : ℂ)) : RiemannSphere) := rfl
    rw [← h2, h1]
  have hcont_f : Continuous f :=
    hEmb.toHomeomorph.symm.continuous.comp
      (Continuous.subtype_mk Φ.continuous (fun z => hΦsub ⟨z, rfl⟩))
  have hinj_f : Function.Injective f := by
    intro a b hab
    apply hΦinj
    have h := congrArg (fun z : ℂ => ((z : ℂ) : RiemannSphere)) hab
    rwa [hfcoe, hfcoe] at h
  have hrange_f : Set.range f = ((↑) ⁻¹' Set.range Φ : Set ℂ) := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, (hfcoe a).symm⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, OnePoint.coe_injective (by rw [hfcoe a, ha])⟩
  refine ⟨⟨f, hcont_f⟩, hinj_f, ?_⟩
  show Set.range f = closure ((↑) ⁻¹' Q : Set ℂ)
  rw [hrange_f, hΦrange, preimage_closure_coe_pieces2 hrange]

/-- **Two cuts of the annulus along two radial crosscuts: the pieces are closed discs.**

Verbatim copy of the statement of `Work.Smooth.SphereJordan.radialTwoCutsPiecesFinal`
(`Submission/Work/Smooth/SphereJordan/radialTwoCutsPiecesFinal.lean`), which is already fully proved
and axiom-clean, under a new name.

PROOF INSTRUCTIONS: copy the body of `radialTwoCutsPiecesFinal` from that file, but do NOT import
`Submission.Work.Smooth.SphereJordan.radialTwoCutsPieces` (that module will import THIS one, so
importing it would create a cycle).  Instead import `Submission.Work.Smooth.SphereJordan
.radialTwoCutsSetup`, which contains exactly the auxiliary material that module provides (the curve
`radialBoundaryCurve`, its simplicity, the corestriction `corestrictDisc`, the bounded-side lemma
`planeSeparation_V_subset_closedBall'` and the setup lemma `exists_curve_of_disc`), and import
`Submission.Work.Smooth.SphereJordan.radialTwoCutsComponents` (the θ-graph family, which supplies
`thetaTwoComponentsSpansH` and the other ingredients the existing proof uses).  Those two import
families are compatible. -/
theorem radialTwoCutsPiecesFinal2 (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    (W : Set ℂ) (hWcl : IsClosed W) (hWsub : W ⊆ Metric.ball (0 : ℂ) 1)
    (hWdisc : ∃ e : C(Work.Smooth.SphereJordan.Disc, ℂ),
      Function.Injective e ∧ Set.range e = W)
    (h0 : (0 : ℂ) ∈ W)
    (w₁ w₂ : ℂ) (hw₁ : ‖w₁‖ = 1) (hw₂ : ‖w₂‖ = 1) (hne : w₁ ≠ w₂)
    (t₁ t₂ : ℝ) (ht₁ : 0 < t₁) (ht₁' : t₁ < 1) (ht₂ : 0 < t₂) (ht₂' : t₂ < 1)
    (hm₁ : t₁ • w₁ ∈ W) (hm₂ : t₂ • w₂ ∈ W)
    (hf₁ : ∀ r : ℝ, t₁ < r → r < 1 → r • w₁ ∉ W)
    (hf₂ : ∀ r : ℝ, t₂ < r → r < 1 → r • w₂ ∉ W) :
    ∃ P₁ P₂ : Set ℂ, P₁.Nonempty ∧ P₂.Nonempty ∧ IsOpen P₁ ∧ IsOpen P₂ ∧ Disjoint P₁ P₂ ∧
      P₁ ∪ P₂ = Metric.ball (0 : ℂ) 1 \
        (W ∪ (fun r : ℝ => r • w₁) '' Set.Ioo t₁ 1 ∪ (fun r : ℝ => r • w₂) '' Set.Ioo t₂ 1) ∧
      IsPreconnected P₁ ∧ IsPreconnected P₂ ∧
      (∃ Φ : C(Work.Smooth.SphereJordan.Disc, ℂ),
        Function.Injective Φ ∧ Set.range Φ = closure P₁) ∧
      (∃ Ψ : C(Work.Smooth.SphereJordan.Disc, ℂ),
        Function.Injective Ψ ∧ Set.range Ψ = closure P₂) := by
  classical
  obtain ⟨e, he_inj, he_range⟩ := hWdisc
  have hw₁ne : w₁ ≠ 0 := by intro hh; rw [hh, norm_zero] at hw₁; norm_num at hw₁
  have hw₂ne : w₂ ≠ 0 := by intro hh; rw [hh, norm_zero] at hw₂; norm_num at hw₂
  set D₁ : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' W with hD₁
  set D₂ : Set RiemannSphere := {x : RiemannSphere | ¬ InOpenDisc x} with hD₂
  have hdisj : Disjoint D₁ D₂ := by
    rw [Set.disjoint_left]
    rintro x ⟨y, hyW, rfl⟩ hx
    have hy : ‖y‖ < 1 := by
      have h := hWsub hyW
      rwa [Metric.mem_ball, dist_zero_right] at h
    exact hx ⟨y, hy, rfl⟩
  have hF : ∃ f : C(Disc, RiemannSphere), Function.Injective f ∧ Set.range f = D₁ :=
    ⟨⟨fun z => ((e z : ℂ) : RiemannSphere), OnePoint.continuous_coe.comp e.continuous⟩,
     OnePoint.coe_injective.comp he_inj, by
      rw [hD₁]
      ext x; constructor
      · rintro ⟨z, rfl⟩
        exact ⟨e z, by rw [← he_range]; exact ⟨z, rfl⟩, rfl⟩
      · rintro ⟨y, hyW, rfl⟩
        have hy : y ∈ Set.range e := by rwa [he_range]
        obtain ⟨z, rfl⟩ := hy
        exact ⟨z, rfl⟩⟩
  -- the two inner endpoints lie in `D₁`
  have hα₀ : radArc w₁ t₁ zeroIcc ∈ D₁ := by
    rw [hD₁, radArc_zero]
    exact ⟨t₁ • w₁, hm₁, rfl⟩
  have hβ₀ : radArc w₂ t₂ zeroIcc ∈ D₁ := by
    rw [hD₁, radArc_zero]
    exact ⟨t₂ • w₂, hm₂, rfl⟩
  -- the two outer endpoints lie in `D₂`
  have hα₁ : radArc w₁ t₁ oneIcc ∈ D₂ := by
    rw [hD₂, radArc_one, Set.mem_setOf_eq, inOpenDisc_coe_aux, hw₁]
    norm_num
  have hβ₁ : radArc w₂ t₂ oneIcc ∈ D₂ := by
    rw [hD₂, radArc_one, Set.mem_setOf_eq, inOpenDisc_coe_aux, hw₂]
    norm_num
  -- the interiors of the arcs avoid the two discs
  have hαint : ∀ s : Set.Icc (0:ℝ) 1, (s:ℝ) ∈ Set.Ioo 0 1 → radArc w₁ t₁ s ∉ D₁ ∪ D₂ := by
    intro s hs hmem
    rw [hD₁, hD₂] at hmem
    rcases hmem with hmem | hmem
    · simp only [Set.mem_image, radArc_apply] at hmem
      obtain ⟨y, hyW, hy⟩ := hmem
      have hy' : y = rayPar t₁ (s:ℝ) • w₁ := OnePoint.coe_injective hy
      have hr := rayPar_mem_Ioo ht₁ ht₁' hs
      exact hf₁ _ hr.1 hr.2 (hy' ▸ hyW)
    · simp only [Set.mem_setOf_eq, radArc_apply, inOpenDisc_coe_aux] at hmem
      have hr := rayPar_mem_Ioo ht₁ ht₁' hs
      rw [norm_smul_of_norm_eq_one hw₁ (le_of_lt (lt_trans ht₁ hr.1))] at hmem
      exact hmem hr.2
  have hβint : ∀ s : Set.Icc (0:ℝ) 1, (s:ℝ) ∈ Set.Ioo 0 1 → radArc w₂ t₂ s ∉ D₁ ∪ D₂ := by
    intro s hs hmem
    rw [hD₁, hD₂] at hmem
    rcases hmem with hmem | hmem
    · simp only [Set.mem_image, radArc_apply] at hmem
      obtain ⟨y, hyW, hy⟩ := hmem
      have hy' : y = rayPar t₂ (s:ℝ) • w₂ := OnePoint.coe_injective hy
      have hr := rayPar_mem_Ioo ht₂ ht₂' hs
      exact hf₂ _ hr.1 hr.2 (hy' ▸ hyW)
    · simp only [Set.mem_setOf_eq, radArc_apply, inOpenDisc_coe_aux] at hmem
      have hr := rayPar_mem_Ioo ht₂ ht₂' hs
      rw [norm_smul_of_norm_eq_one hw₂ (le_of_lt (lt_trans ht₂ hr.1))] at hmem
      exact hmem hr.2
  -- the arcs are injective
  have hαinj : Function.Injective (radArc w₁ t₁) := by
    intro s s' hss
    have h1 : ((rayPar t₁ (s:ℝ) • w₁ : ℂ)) = rayPar t₁ (s':ℝ) • w₁ := OnePoint.coe_injective hss
    rw [Complex.real_smul, Complex.real_smul] at h1
    have h2 : rayPar t₁ (s:ℝ) = rayPar t₁ (s':ℝ) := by
      have h3 := mul_right_cancel₀ hw₁ne h1
      exact_mod_cast h3
    exact Subtype.ext (rayPar_injOn ht₁' s.2 s'.2 h2)
  have hβinj : Function.Injective (radArc w₂ t₂) := by
    intro s s' hss
    have h1 : ((rayPar t₂ (s:ℝ) • w₂ : ℂ)) = rayPar t₂ (s':ℝ) • w₂ := OnePoint.coe_injective hss
    rw [Complex.real_smul, Complex.real_smul] at h1
    have h2 : rayPar t₂ (s:ℝ) = rayPar t₂ (s':ℝ) := by
      have h3 := mul_right_cancel₀ hw₂ne h1
      exact_mod_cast h3
    exact Subtype.ext (rayPar_injOn ht₂' s.2 s'.2 h2)
  -- the two arcs are disjoint, apart from their endpoints
  have hsep : ∀ s u : Set.Icc (0:ℝ) 1, (s:ℝ) ∈ Set.Ioo 0 1 → (u:ℝ) ∈ Set.Ioo 0 1 →
      radArc w₁ t₁ s ≠ radArc w₂ t₂ u := by
    intro s u hs hu hEq
    have h1 : ((rayPar t₁ (s:ℝ) • w₁ : ℂ)) = rayPar t₂ (u:ℝ) • w₂ := OnePoint.coe_injective hEq
    have hr₁ := rayPar_mem_Ioo ht₁ ht₁' hs
    have hr₂ := rayPar_mem_Ioo ht₂ ht₂' hu
    have h2 : rayPar t₁ (s:ℝ) = rayPar t₂ (u:ℝ) := by
      have h3 := congrArg norm h1
      rwa [norm_smul_of_norm_eq_one hw₁ (le_of_lt (lt_trans ht₁ hr₁.1)),
           norm_smul_of_norm_eq_one hw₂ (le_of_lt (lt_trans ht₂ hr₂.1))] at h3
    have h4 : w₁ = w₂ := by
      have h5 : rayPar t₁ (s:ℝ) • w₁ = rayPar t₁ (s:ℝ) • w₂ := by rw [h1, h2]
      rw [Complex.real_smul, Complex.real_smul] at h5
      exact mul_left_cancel₀ (by exact_mod_cast (ne_of_gt (lt_trans ht₁ hr₁.1))) h5
    exact hne h4
  have hαβ₀ : radArc w₁ t₁ zeroIcc ≠ radArc w₂ t₂ zeroIcc := by
    rw [radArc_zero, radArc_zero]
    intro hEq
    have h1 : ((t₁ • w₁ : ℂ)) = t₂ • w₂ := OnePoint.coe_injective hEq
    have h2 : t₁ = t₂ := by
      have h3 := congrArg norm h1
      rwa [norm_smul_of_norm_eq_one hw₁ (le_of_lt ht₁),
           norm_smul_of_norm_eq_one hw₂ (le_of_lt ht₂)] at h3
    exact hne (by
      rw [Complex.real_smul, Complex.real_smul, h2] at h1
      exact mul_left_cancel₀ (by exact_mod_cast (ne_of_gt ht₂)) h1)
  have hαβ₁ : radArc w₁ t₁ oneIcc ≠ radArc w₂ t₂ oneIcc := by
    rw [radArc_one, radArc_one]
    exact fun hEq => hne (OnePoint.coe_injective hEq)
  -- the two-component theorem on the Riemann sphere
  obtain ⟨Q₁, Q₂, hQ₁ne, hQ₂ne, hQ₁o, hQ₂o, hQd, hQu, hQ₁c, hQ₂c, hΦ, hΨ⟩ :=
    thetaTwoComponentsSpansH h hF
      ⟨exteriorDisc, exteriorDisc_injective, range_exteriorDisc⟩ hdisj
      (radArc w₁ t₁) (radArc w₂ t₂) hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint hβint hsep hαβ₀ hαβ₁
  have hQsub₁ : Q₁ ⊆ Set.range ((↑) : ℂ → RiemannSphere) := by
    intro x hx
    have hx' : x ∈ Set.univ \
        (D₁ ∪ D₂ ∪ Set.range (radArc w₁ t₁) ∪ Set.range (radArc w₂ t₂)) := by
      rw [← hQu]; exact Or.inl hx
    have hxnD₂ : x ∉ D₂ := fun hD => hx'.2 (Or.inl (Or.inl (Or.inr hD)))
    rw [hD₂] at hxnD₂
    simp only [Set.mem_setOf_eq, not_not] at hxnD₂
    obtain ⟨z, -, hz⟩ := hxnD₂
    exact ⟨z, hz⟩
  have hQsub₂ : Q₂ ⊆ Set.range ((↑) : ℂ → RiemannSphere) := by
    intro x hx
    have hx' : x ∈ Set.univ \
        (D₁ ∪ D₂ ∪ Set.range (radArc w₁ t₁) ∪ Set.range (radArc w₂ t₂)) := by
      rw [← hQu]; exact Or.inr hx
    have hxnD₂ : x ∉ D₂ := fun hD => hx'.2 (Or.inl (Or.inl (Or.inr hD)))
    rw [hD₂] at hxnD₂
    simp only [Set.mem_setOf_eq, not_not] at hxnD₂
    obtain ⟨z, -, hz⟩ := hxnD₂
    exact ⟨z, hz⟩
  -- identify the complement with the target set
  have hD₁mem : ∀ z : ℂ, ((z:ℂ):RiemannSphere) ∈ D₁ ↔ z ∈ W := by
    intro z
    rw [hD₁]
    exact ⟨fun hh => by
      obtain ⟨y, hyW, hy⟩ := hh
      rwa [← OnePoint.coe_injective hy], fun hh => ⟨z, hh, rfl⟩⟩
  have hD₂mem : ∀ z : ℂ, ((z:ℂ):RiemannSphere) ∈ D₂ ↔ ¬ (‖z‖ < 1) := by
    intro z
    rw [hD₂]
    simp only [Set.mem_setOf_eq, inOpenDisc_coe_aux]
  have hnotα : ∀ z : ℂ, ((z:ℂ):RiemannSphere) ∉ Set.range (radArc w₁ t₁) ↔
      ∀ s : Set.Icc (0:ℝ) 1, rayPar t₁ (s:ℝ) • w₁ ≠ z := by
    intro z
    constructor
    · intro hh s hcon
      refine hh ⟨s, ?_⟩
      show ((rayPar t₁ (s:ℝ) • w₁ : ℂ) : RiemannSphere) = ((z:ℂ):RiemannSphere)
      rw [hcon]
    · rintro hh ⟨s, hs⟩
      exact hh s (OnePoint.coe_injective hs)
  have hnotβ : ∀ z : ℂ, ((z:ℂ):RiemannSphere) ∉ Set.range (radArc w₂ t₂) ↔
      ∀ s : Set.Icc (0:ℝ) 1, rayPar t₂ (s:ℝ) • w₂ ≠ z := by
    intro z
    constructor
    · intro hh s hcon
      refine hh ⟨s, ?_⟩
      show ((rayPar t₂ (s:ℝ) • w₂ : ℂ) : RiemannSphere) = ((z:ℂ):RiemannSphere)
      rw [hcon]
    · rintro hh ⟨s, hs⟩
      exact hh s (OnePoint.coe_injective hs)
  have hA : ∀ z : ℂ, ((z:ℂ):RiemannSphere) ∈
        (Set.univ \ (D₁ ∪ D₂ ∪ Set.range (radArc w₁ t₁) ∪ Set.range (radArc w₂ t₂)))
      ↔ (z ∉ W) ∧ (‖z‖ < 1) ∧ (∀ s : Set.Icc (0:ℝ) 1, rayPar t₁ (s:ℝ) • w₁ ≠ z)
          ∧ (∀ u : Set.Icc (0:ℝ) 1, rayPar t₂ (u:ℝ) • w₂ ≠ z) := by
    intro z
    have hun : ((z:ℂ):RiemannSphere) ∉
        (D₁ ∪ D₂ ∪ Set.range (radArc w₁ t₁) ∪ Set.range (radArc w₂ t₂))
        ↔ ((¬((z:ℂ):RiemannSphere) ∈ D₁ ∧ ¬((z:ℂ):RiemannSphere) ∈ D₂)
            ∧ ¬((z:ℂ):RiemannSphere) ∈ Set.range (radArc w₁ t₁))
            ∧ ¬((z:ℂ):RiemannSphere) ∈ Set.range (radArc w₂ t₂) := by
      simp only [Set.mem_union, not_or]
    rw [Set.mem_sdiff]
    simp only [Set.mem_univ, true_and]
    rw [hun, hD₁mem z, hD₂mem z, hnotα z, hnotβ z]
    simp only [not_not]
    tauto
  have hB : ∀ z : ℂ, z ∈ Metric.ball (0:ℂ) 1 \ (W ∪ (fun r : ℝ => r • w₁) '' Set.Ioo t₁ 1
        ∪ (fun r : ℝ => r • w₂) '' Set.Ioo t₂ 1)
      ↔ (z ∉ W) ∧ (‖z‖ < 1) ∧ (∀ r : ℝ, t₁ < r → r < 1 → r • w₁ ≠ z)
          ∧ (∀ r : ℝ, t₂ < r → r < 1 → r • w₂ ≠ z) := by
    intro z
    have hball : z ∈ Metric.ball (0:ℂ) 1 ↔ ‖z‖ < 1 := by
      rw [Metric.mem_ball, dist_zero_right]
    have hun : z ∉ (W ∪ (fun r : ℝ => r • w₁) '' Set.Ioo t₁ 1
        ∪ (fun r : ℝ => r • w₂) '' Set.Ioo t₂ 1)
        ↔ ((z ∉ W ∧ z ∉ (fun r : ℝ => r • w₁) '' Set.Ioo t₁ 1)
            ∧ z ∉ (fun r : ℝ => r • w₂) '' Set.Ioo t₂ 1) := by
      simp only [Set.mem_union, not_or]
    have himg₁ : z ∉ (fun r : ℝ => r • w₁) '' Set.Ioo t₁ 1
        ↔ ∀ r : ℝ, t₁ < r → r < 1 → r • w₁ ≠ z := by
      rw [Set.mem_image]; simp only [not_exists, not_and]
      constructor
      · intro hh r hr hr1; exact hh r ⟨hr, hr1⟩
      · intro hh r hr; exact hh r hr.1 hr.2
    have himg₂ : z ∉ (fun r : ℝ => r • w₂) '' Set.Ioo t₂ 1
        ↔ ∀ r : ℝ, t₂ < r → r < 1 → r • w₂ ≠ z := by
      rw [Set.mem_image]; simp only [not_exists, not_and]
      constructor
      · intro hh r hr hr1; exact hh r ⟨hr, hr1⟩
      · intro hh r hr; exact hh r hr.1 hr.2
    rw [Set.mem_sdiff, hball, hun, himg₁, himg₂]
    tauto
  have hset : ((↑) ⁻¹' (Set.univ \
        (D₁ ∪ D₂ ∪ Set.range (radArc w₁ t₁) ∪ Set.range (radArc w₂ t₂))) : Set ℂ)
      = Metric.ball (0:ℂ) 1 \ (W ∪ (fun r : ℝ => r • w₁) '' Set.Ioo t₁ 1
          ∪ (fun r : ℝ => r • w₂) '' Set.Ioo t₂ 1) := by
    ext z
    rw [Set.mem_preimage, hA z, hB z]
    constructor
    · rintro ⟨hW', hzn, hα, hβ⟩
      exact ⟨hW', hzn, (forall_rayPar_ne_iff ht₁' hw₁ hm₁ hW' hzn).mp hα,
        (forall_rayPar_ne_iff ht₂' hw₂ hm₂ hW' hzn).mp hβ⟩
    · rintro ⟨hW', hzn, hα, hβ⟩
      exact ⟨hW', hzn, (forall_rayPar_ne_iff ht₁' hw₁ hm₁ hW' hzn).mpr hα,
        (forall_rayPar_ne_iff ht₂' hw₂ hm₂ hW' hzn).mpr hβ⟩
  have hQ₁fin : Q₁ ⊆ ((↑) : ℂ → RiemannSphere) '' Metric.ball (0 : ℂ) 1 := by
    intro x hx
    have hx' : x ∈ Set.univ \
        (D₁ ∪ D₂ ∪ Set.range (radArc w₁ t₁) ∪ Set.range (radArc w₂ t₂)) := by
      rw [← hQu]; exact Or.inl hx
    have hxnD₂ : x ∉ D₂ := fun hD => hx'.2 (Or.inl (Or.inl (Or.inr hD)))
    rw [hD₂] at hxnD₂
    simp only [Set.mem_setOf_eq, not_not] at hxnD₂
    obtain ⟨z, hz, hzx⟩ := hxnD₂
    exact ⟨z, by rwa [Metric.mem_ball, dist_zero_right], hzx⟩
  have hQ₂fin : Q₂ ⊆ ((↑) : ℂ → RiemannSphere) '' Metric.ball (0 : ℂ) 1 := by
    intro x hx
    have hx' : x ∈ Set.univ \
        (D₁ ∪ D₂ ∪ Set.range (radArc w₁ t₁) ∪ Set.range (radArc w₂ t₂)) := by
      rw [← hQu]; exact Or.inr hx
    have hxnD₂ : x ∉ D₂ := fun hD => hx'.2 (Or.inl (Or.inl (Or.inr hD)))
    rw [hD₂] at hxnD₂
    simp only [Set.mem_setOf_eq, not_not] at hxnD₂
    obtain ⟨z, hz, hzx⟩ := hxnD₂
    exact ⟨z, by rwa [Metric.mem_ball, dist_zero_right], hzx⟩
  refine ⟨(↑) ⁻¹' Q₁, (↑) ⁻¹' Q₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hQ₁ne
    obtain ⟨z, hz⟩ := hQsub₁ hx
    exact ⟨z, by show ((z:ℂ):RiemannSphere) ∈ Q₁; rw [hz]; exact hx⟩
  · obtain ⟨x, hx⟩ := hQ₂ne
    obtain ⟨z, hz⟩ := hQsub₂ hx
    exact ⟨z, by show ((z:ℂ):RiemannSphere) ∈ Q₂; rw [hz]; exact hx⟩
  · exact isOpen_pullback_coe hQ₁o
  · exact isOpen_pullback_coe hQ₂o
  · rw [Set.disjoint_iff_inter_eq_empty] at hQd ⊢
    rw [← Set.preimage_inter, hQd, Set.preimage_empty]
  · rw [← Set.preimage_union, hQu]
    exact hset
  · exact isPreconnected_preimage_coe hQ₁c hQ₁ne hQsub₁
  · exact isPreconnected_preimage_coe hQ₂c hQ₂ne hQsub₂
  · exact exists_disc_closure_preimage_coe_pieces2 hQ₁fin hΦ
  · exact exists_disc_closure_preimage_coe_pieces2 hQ₂fin hΨ

end

end Work.Smooth.SphereJordan
