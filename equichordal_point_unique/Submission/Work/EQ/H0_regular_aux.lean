import Mathlib
import Submission.UnifDeps
import Submission.Work.EQ.DefsCore

/-!
# Preparatory lemmas for `H0_regular` (Rychlik Theorems 10–11)

This file sets up the geometry of a connected component `S` of Rychlik's connection surface
`H0 a h` (`DefsCore.lean`), in the form needed for the Fatou–Riesz argument of Rychlik's
Theorems 10 and 11:

* `psi_local_chart`: on a neighbourhood of every point of `H0`, the invariant parameter
  `psi = ψ₁ψ₂` is an analytic function of `ψ₁` alone.  This is the local structure of the étale
  surface (`H0_structure`), extracted in the exact form the analytic argument consumes.
* `not_compactSpace_connectedComponent`: no component of `H0` is compact.  The proof is purely
  topological: `ψ₁` is an open map on `H0` and never vanishes, so if a component were compact its
  `ψ₁`-image would be a nonempty clopen (hence all of `ℂ`) subset of `ℂ*` — impossible.

The inputs (`LocalSections`, `IsLocalHomeomorph`) are exactly the two halves of the workspace
lemma `Work.EQ.H0_structure`.
-/

namespace Work.EQ

open Filter _root_.Topology

/-- The invariant parameter `ψ = ψ₁ψ₂` of a chain. -/
def psi (q : ChainData) : ℂ := q.2.1 * q.2.2

theorem continuous_psi : Continuous psi := by
  show Continuous fun q : ChainData => q.2.1 * q.2.2
  fun_prop

/-- `ψ` as a function on a component of `H0`. -/
def psiC {a : ℝ} {h : ℂ → ℂ} {P : H0 a h} (q : ↥(connectedComponent P)) : ℂ :=
  psi ((q : H0 a h) : ChainData)

@[simp] theorem psiC_apply {a : ℝ} {h : ℂ → ℂ} {P : H0 a h}
    (q : ↥(connectedComponent P)) : psiC q = psi ((q : H0 a h) : ChainData) := rfl

/-- The local-section data for `H0` (the second conjunct of `H0_structure`): through every point
of `H0` there is a continuous family of chains parametrised by `ψ₁`, whose coordinates are
analytic, and whose image is a neighbourhood of the point in `H0`. -/
def LocalSections (a : ℝ) (h : ℂ → ℂ) : Prop :=
  ∀ p ∈ H0 a h, ∃ ρ : ℝ, 0 < ρ ∧ ∃ f : ℂ → ChainData, f p.2.1 = p ∧
    (∀ u ∈ Metric.ball p.2.1 ρ, f u ∈ H0 a h ∧ (f u).2.1 = u) ∧
    (∀ n : ℤ, AnalyticOnNhd ℂ (fun u => (f u).1 n) (Metric.ball p.2.1 ρ)) ∧
    AnalyticOnNhd ℂ (fun u => (f u).2.2) (Metric.ball p.2.1 ρ) ∧
    f '' Metric.ball p.2.1 ρ ∈ 𝓝[H0 a h] p

/-- **Local chart of the invariant parameter.** Near every point of `H0`, `psi = ψ₁ψ₂` agrees
with an analytic function of `ψ₁`. -/
theorem psi_local_chart {a : ℝ} {h : ℂ → ℂ} (hsect : LocalSections a h)
    (p : ChainData) (hp : p ∈ H0 a h) :
    ∃ (ρ : ℝ) (Γ : ℂ → ℂ), 0 < ρ ∧ AnalyticOnNhd ℂ Γ (Metric.ball p.2.1 ρ) ∧
      Γ p.2.1 = psi p ∧
      ∀ᶠ q : ChainData in 𝓝 p, q ∈ H0 a h → psi q = Γ (q.2.1) := by
  obtain ⟨ρ, hρ, f, hf0, hfmem, -, hfana, hfnbhd⟩ := hsect p hp
  refine ⟨ρ, fun u => u * (f u).2.2, hρ, ?_, ?_, ?_⟩
  · intro u hu
    exact analyticAt_id.mul (hfana u hu)
  · show p.2.1 * (f p.2.1).2.2 = psi p
    rw [hf0]
    rfl
  · refine (eventually_nhdsWithin_iff).mp ?_
    filter_upwards [hfnbhd] with q hq
    obtain ⟨u, hu, rfl⟩ := hq
    rw [psi, (hfmem u hu).2]

/-- The `ψ₁`-coordinate of a point of `H0` never vanishes. -/
theorem psi1_ne_zero_of_mem {a : ℝ} {h : ℂ → ℂ} {q : ChainData} (hq : q ∈ H0 a h) :
    q.2.1 ≠ 0 := by
  obtain ⟨ε, hε, f, -, hf0, hfam⟩ := hq
  have hmem : q.2.1 ∈ Metric.ball q.2.1 ε := by
    rw [Metric.mem_ball, dist_self]; exact hε
  have hchain : IsChain a h q := by
    rw [← hf0]
    exact (hfam q.2.1 hmem).1
  exact hchain.2.1

/-- **No component of `H0` is compact.** `ψ₁` is an open map (`IsLocalHomeomorph`) and never
vanishes on `H0`, so the `ψ₁`-image of a component is a nonempty open set of `ℂ*`; were the
component compact that image would also be compact, hence clopen in the connected space `ℂ`,
hence all of `ℂ` — contradicting `ψ₁ ≠ 0`. -/
theorem not_compactSpace_connectedComponent {a : ℝ} {h : ℂ → ℂ}
    (hstruct : IsLocalHomeomorph (fun q : H0 a h => (q : ChainData).2.1))
    (hlocconn : LocallyConnectedSpace (H0 a h)) (P : H0 a h) :
    ¬ CompactSpace ↥(connectedComponent P) := by
  intro hcomp
  haveI := hcomp
  set φ : ↥(connectedComponent P) → ℂ := fun q => ((q : H0 a h) : ChainData).2.1 with hφ
  have hφcont : Continuous φ :=
    (hstruct.continuous).comp (continuous_subtype_val :
      Continuous fun q : ↥(connectedComponent P) => (q : H0 a h))
  have hUopen : IsOpen (Set.range φ) := by
    have hopen : IsOpen ((fun q : H0 a h => (q : ChainData).2.1) '' (connectedComponent P)) :=
      hstruct.isOpenMap _ (isOpen_connectedComponent)
    have : Set.range φ = (fun q : H0 a h => (q : ChainData).2.1) '' (connectedComponent P) := by
      ext z
      constructor
      · rintro ⟨q, rfl⟩; exact ⟨(q : H0 a h), q.2, rfl⟩
      · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩
    rw [this]; exact hopen
  have hUcompact : IsCompact (Set.range φ) := isCompact_range hφcont
  have hne : (Set.range φ).Nonempty := ⟨φ ⟨P, mem_connectedComponent⟩, ⟨⟨P, mem_connectedComponent⟩, rfl⟩⟩
  have hclopen : IsClopen (Set.range φ) := ⟨hUcompact.isClosed, hUopen⟩
  have huniv : Set.range φ = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    exact isPreconnected_univ.subset_isClopen hclopen (by simpa using hne)
  have hzero : (0 : ℂ) ∈ Set.range φ := by rw [huniv]; exact Set.mem_univ 0
  obtain ⟨q, hq⟩ := hzero
  exact psi1_ne_zero_of_mem (q : H0 a h).2 hq

/-- **Rychlik Theorem 10, parabolic case.** If a component `S` of `H0` is covered by `ℂ` and
`psi = ψ₁ψ₂` is bounded below by `ρ > 0` on `S`, then `psi` is constant on `S`: `1/psi` pulls
back to a bounded entire function, which is constant by Liouville. -/
theorem plane_cover_const {a : ℝ} {h : ℂ → ℂ} (hsect : LocalSections a h) {P : H0 a h}
    {ρ : ℝ} (hρ : 0 < ρ) (hbd : ∀ q : ↥(connectedComponent P), ρ ≤ ‖psi q‖)
    {p : ℂ → ↥(connectedComponent P)} (hp : IsCoveringMap p)
    (hpψ : Differentiable ℂ fun z => ((p z : H0 a h) : ChainData).2.1) :
    ∃ c, ∀ q : ↥(connectedComponent P), psi q = c := by
  have hcontp : Continuous fun w : ℂ => ((p w : H0 a h) : ChainData) :=
    (continuous_subtype_val : Continuous fun q : ↥(H0 a h) => (q : ChainData)).comp
      ((continuous_subtype_val : Continuous fun q : ↥(connectedComponent P) => (q : H0 a h)).comp
        hp.continuous)
  -- every point of the base is in the range of the covering
  have hsurj : Function.Surjective p := by
    have hclosed : IsClosed (Set.range p) := by
      rw [← closure_subset_iff_isClosed]
      intro y hy
      obtain ⟨-, U, hyU, hUo, -, H, hH⟩ := hp y
      obtain ⟨z, hzU, hz⟩ := mem_closure_iff.mp hy U hUo hyU
      obtain ⟨w, rfl⟩ := hz
      refine ⟨((H.symm ((⟨y, hyU⟩ : ↥U), (H ⟨w, by simpa using hzU⟩).2) : ↥(p ⁻¹' U)) : ℂ), ?_⟩
      show p ((H.symm ((⟨y, hyU⟩ : ↥U), (H ⟨w, by simpa using hzU⟩).2) : ↥(p ⁻¹' U)) : ℂ) = y
      rw [← hH (H.symm ((⟨y, hyU⟩ : ↥U), (H ⟨w, by simpa using hzU⟩).2))]
      simp
    have hopen : IsOpen (Set.range p) := by
      simpa [Set.image_univ] using hp.isOpenMap Set.univ isOpen_univ
    have hne : (Set.range p).Nonempty := ⟨p 0, ⟨0, rfl⟩⟩
    haveI : PreconnectedSpace ↥(connectedComponent P) :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponent
    have huniv : Set.range p = Set.univ := by
      refine Set.eq_univ_of_univ_subset ?_
      exact isPreconnected_univ.subset_isClopen ⟨hclosed, hopen⟩ (by simpa using hne)
    intro y
    have : y ∈ Set.range p := by rw [huniv]; exact Set.mem_univ y
    exact this
  -- the inverse of `psi` along the covering
  have hne : ∀ z : ℂ, psi (((p z : H0 a h) : ChainData)) ≠ 0 := by
    intro z h
    have := hbd (p z)
    rw [h, norm_zero] at this
    linarith
  have hg : Differentiable ℂ (fun z : ℂ => (psi (((p z : H0 a h) : ChainData)))⁻¹) := by
    intro z
    obtain ⟨ρ', Γ, hρ', hΓ, -, hchart⟩ :=
      psi_local_chart hsect (((p z : H0 a h) : ChainData)) (p z : H0 a h).2
    have hev : ∀ᶠ w in 𝓝 z, psi (((p w : H0 a h) : ChainData))
        = Γ ((((p w : H0 a h) : ChainData)).2.1) := by
      have hpull := (hcontp.continuousAt (x := z)).eventually hchart
      filter_upwards [hpull] with w hw
      have hmem : (((p w : H0 a h) : ChainData)) ∈ H0 a h := (p w : H0 a h).2
      exact hw hmem
    have hΓat : DifferentiableAt ℂ Γ ((((p z : H0 a h) : ChainData)).2.1) :=
      (hΓ _ (by rw [Metric.mem_ball, dist_self]; exact hρ')).differentiableAt
    have h1 : DifferentiableAt ℂ
        (fun w : ℂ => Γ ((((p w : H0 a h) : ChainData)).2.1)) z :=
      hΓat.comp z (hpψ.differentiableAt (x := z))
    have h2 : DifferentiableAt ℂ (fun w : ℂ => psi (((p w : H0 a h) : ChainData))) z :=
      h1.congr_of_eventuallyEq hev
    exact h2.inv (hne z)
  have hbdd : Bornology.IsBounded
      (Set.range fun z : ℂ => (psi (((p z : H0 a h) : ChainData)))⁻¹) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨ρ⁻¹, ?_⟩
    rintro y ⟨z, rfl⟩
    rw [norm_inv]
    refine (inv_le_inv₀ (norm_pos_iff.mpr (hne z)) hρ).mpr ?_
    exact hbd (p z)
  obtain ⟨c, hc⟩ := Differentiable.exists_eq_const_of_bounded hg hbdd
  refine ⟨psi (((p 0 : H0 a h) : ChainData)), fun q => ?_⟩
  obtain ⟨z, rfl⟩ := hsurj q
  have h1 : (psi (((p z : H0 a h) : ChainData)))⁻¹ = c := congrFun hc z
  have h2 : (psi (((p 0 : H0 a h) : ChainData)))⁻¹ = c := congrFun hc 0
  exact inv_injective (h1.trans h2.symm)

end Work.EQ
