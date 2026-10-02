import Mathlib
import Submission.Work.ThomBordism.Transversality.TransverseSard.LocalRep

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.PTGeometric

open scoped ContDiff Topology

/-- **Straightening of a map with surjective derivative, preserving a vanishing functional.**

Let `g : E → E'` be `C^∞` on an open set `U ∋ c`, with `fderiv ℝ g c = L`.  Suppose `L` admits a
right inverse `σ` (`L (σ y) = y`) and that a continuous linear functional `χ : E → ℝ` kills the
image of `σ` (`χ (σ y) = 0`).

Then there is a `C^∞` local diffeomorphism `T : E → E` around `c` (with `C^∞` inverse) such that
* `χ (T v) = χ v` (the "coordinate" `χ` is preserved), and
* `L (T v) = g v`, i.e. `g` becomes the linear map `L` after the change of coordinates `T`.

The straightening map is the explicit `T v = v + σ (g v - L v)`, whose derivative at `c` is the
identity since `fderiv ℝ g c = L`; the invariance of `χ` is exactly `χ (σ y) = 0`.

This is the `C^∞` (= `∞`) version of `exists_localDiffeomorph_eq_linear_of_coord_preserving`
(which is stated for analytic `g`, `⊤ : WithTop ℕ∞ = ω`). -/
theorem exists_localDiffeomorph_eq_linear_of_coord_preserving_smooth
    {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {g : E → E'} {L : E →L[ℝ] E'} {c : E} {U : Set E} (hU : IsOpen U) (hc : c ∈ U)
    (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g U) (hL : fderiv ℝ g c = L)
    {χ : E →L[ℝ] ℝ} {σ : E' →L[ℝ] E} (hσ : ∀ y, L (σ y) = y) (hχσ : ∀ y, χ (σ y) = 0) :
    ∃ T : OpenPartialHomeomorph E E, c ∈ T.source ∧
      (∀ v ∈ T.source, χ (T v) = χ v) ∧
      (∀ v ∈ T.source, L (T v) = g v) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (T : E → E) T.source ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (T.symm : E → E) T.target := by
  -- The straightening map.
  set Φ : E → E := fun x => x + σ (g x - L x) with hΦdef
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hgc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g c := hg.contDiffAt (hU.mem_nhds hc)
  have hgd : HasFDerivAt g L c := by
    have h := (hgc.differentiableAt hne).hasFDerivAt
    rw [hL] at h
    exact h
  -- Smoothness of `Φ` at `c`.
  have hΦc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ c := by
    rw [hΦdef]
    fun_prop
  -- The derivative of `Φ` at `c` is the identity.
  have hid : HasFDerivAt Φ ((1 : E ≃L[ℝ] E) : E →L[ℝ] E) c := by
    rw [hΦdef]
    have h1 : HasFDerivAt (g - ⇑L) (0 : E →L[ℝ] E') c := by
      have h := hgd.sub (L.hasFDerivAt (x := c))
      simpa using h
    have h2 : HasFDerivAt (⇑σ ∘ (g - ⇑L)) (0 : E →L[ℝ] E) c := by
      have h := (σ.hasFDerivAt (x := g c - L c)).comp c h1
      simpa using h
    have h3 := (hasFDerivAt_id (𝕜 := ℝ) (x := c)).add h2
    convert h3 using 1
    · ext x
      simp [Pi.add_apply, Pi.sub_apply, Function.comp_apply]
    · rw [add_zero]
      rfl
  -- The inverse function theorem at `c`.
  let hT₀ : OpenPartialHomeomorph E E := hΦc.toOpenPartialHomeomorph Φ hid hne
  have hT₀coe : ⇑hT₀ = Φ := ContDiffAt.toOpenPartialHomeomorph_coe hΦc hid hne
  have hmemc : c ∈ hT₀.source := ContDiffAt.mem_toOpenPartialHomeomorph_source hΦc hid hne
  -- Restrict so that the source lies in `U` and the derivative stays invertible.
  have hΦanU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ (interior U) := by
    have hgU' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (interior U) := hg.mono interior_subset
    rw [hΦdef]
    fun_prop
  have hcont : ContinuousOn (fderiv ℝ Φ) (interior U) :=
    hΦanU.continuousOn_fderiv_of_isOpen isOpen_interior (by simp)
  set s : Set E :=
    interior U ∩ (fderiv ℝ Φ) ⁻¹' Set.range ((↑) : (E ≃L[ℝ] E) → E →L[ℝ] E) with hsdef
  have hsopen : IsOpen s := hcont.isOpen_inter_preimage isOpen_interior ContinuousLinearEquiv.isOpen
  have hcs : c ∈ s := by
    refine ⟨mem_interior_iff_mem_nhds.mpr (hU.mem_nhds hc), ?_⟩
    rw [Set.mem_preimage, Set.mem_range]
    exact ⟨1, hid.fderiv.symm⟩
  refine ⟨hT₀.restrOpen s hsopen, ?_, ?_, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hmemc, hcs⟩
  · intro v hv
    rw [OpenPartialHomeomorph.coe_restrOpen, hT₀coe, hΦdef]
    show χ (v + σ (g v - L v)) = χ v
    rw [map_add, hχσ (g v - L v), add_zero]
  · intro v hv
    rw [OpenPartialHomeomorph.coe_restrOpen, hT₀coe, hΦdef]
    show L (v + σ (g v - L v)) = g v
    rw [map_add, hσ (g v - L v)]
    abel
  · have hsub : (hT₀.restrOpen s hsopen).source ⊆ interior U := by
      rw [OpenPartialHomeomorph.restrOpen_source]
      exact fun x hx => hx.2.1
    refine (hΦanU.mono hsub).congr (fun x hx => ?_)
    rw [OpenPartialHomeomorph.coe_restrOpen, hT₀coe]
  · have htgt : (hT₀.restrOpen s hsopen).target = hT₀.target ∩ (hT₀.symm) ⁻¹' s := by
      rw [OpenPartialHomeomorph.restrOpen_toPartialEquiv]
      exact PartialEquiv.restr_target _ _
    have hbody : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑(hT₀.symm) : E → E)
        (hT₀.restrOpen s hsopen).target := by
      intro a ha
      rw [htgt] at ha
      have ha₀ : a ∈ hT₀.target := ha.1
      have hxa : hT₀.symm a ∈ s := ha.2
      have hxU : hT₀.symm a ∈ interior U := hxa.1
      have hΦx : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ (hT₀.symm a) :=
        hΦanU.contDiffAt (isOpen_interior.mem_nhds hxU)
      have hderiv : HasFDerivAt Φ (fderiv ℝ Φ (hT₀.symm a)) (hT₀.symm a) :=
        (hΦx.differentiableAt hne).hasFDerivAt
      obtain ⟨e', he'⟩ := hxa.2
      have hderiv' : HasFDerivAt Φ (↑e' : E →L[ℝ] E) (hT₀.symm a) := by
        rw [he']
        exact hderiv
      have hderiv'' : HasFDerivAt (⇑hT₀) (↑e' : E →L[ℝ] E) (⇑hT₀.symm a) := by
        rw [hT₀coe]
        exact hderiv'
      have hsmooth : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑hT₀) (⇑hT₀.symm a) := by
        rw [hT₀coe]
        exact hΦx
      exact (hT₀.contDiffAt_symm ha₀ hderiv'' hsmooth).contDiffWithinAt
    refine hbody.congr (fun x hx => ?_)
    rw [OpenPartialHomeomorph.coe_restrOpen_symm]

end Work.PTGeometric
