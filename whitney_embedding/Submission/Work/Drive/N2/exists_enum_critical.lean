import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.isCritical_iff_chartRep
import Submission.Work.Embedding.finite_of_isClosed_forall_isolated

/-!
# The critical set of a Morse function on a compact surface is finite

The target of this file is `Work.Drive.N2.exists_enum_critical`: a smooth function whose critical
points are all nondegenerate (a Morse function) on a compact surface has finitely many critical
points, hence these can be enumerated.

The two ingredients are proved here:

* the critical set is **closed**: `Work.Drive.N2.isClosed_isCriticalSet`.  In a chart at `p` the
  condition "`z` is critical" becomes "`fderiv ℝ g_p (e_p z) = 0`" where `g_p = f ∘ e_p.symm` is the
  chart representation (`Work.Drive.N2.isCritical_iff_chartRep`), and `fderiv ℝ g_p` is continuous;

* every critical point is **isolated** in the critical set: `Work.Drive.N2.isCritical_isolated`.
  In the chart at a nondegenerate critical point `x` the map `y ↦ fderiv ℝ g_x y` has an injective
  strict derivative at the chart point (the Hessian, injective by nondegeneracy and hence
  antilipschitz because the model space is finite dimensional), so it is locally injective there.

A closed subset of a compact space all of whose points are isolated is finite
(`Work.Embedding.finite_of_isClosed_forall_isolated`), which gives the enumeration.
-/

-- The finite-type instance for the critical set is introduced with `letI` (a local instance is
-- needed for `Fintype.equivFin` below); the style linter's suggestion to use `let` does not apply.
set_option linter.style.haveILetI false

namespace Work.Drive.N2

open scoped Manifold ContDiff
open Filter Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M]

/-- The chart representation of a smooth function is smooth on the chart target. -/
lemma contDiffOn_chartRep (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (p : M) :
    ContDiffOn ℝ ∞ (fun y : EuclideanSpace ℝ (Fin 2) => f ((extChartAt (𝓡 2) p).symm y))
      (extChartAt (𝓡 2) p).target := by
  rw [← contMDiffOn_iff_contDiffOn]
  intro y hy
  exact (hf.contMDiffAt (x := (extChartAt (𝓡 2) p).symm y)).comp_contMDiffWithinAt y
    (contMDiffWithinAt_extChartAt_symm_target (I := 𝓡 2) p hy)

/-- If `g` has a strict derivative `H` at `z` and `H` is injective, then `g` is injective near `z`
(no completeness assumption is needed: an injective linear map on a finite dimensional space is
antilipschitz). -/
lemma eventually_eq_of_hasStrictFDerivAt_injective {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {z : E} {H : E →L[ℝ] F}
    (hg : HasStrictFDerivAt g H z) (hH : Function.Injective H) :
    ∀ᶠ y in 𝓝 z, g y = g z → y = z := by
  obtain ⟨K, hKpos, hK⟩ :=
    LinearMap.exists_antilipschitzWith H.toLinearMap (LinearMap.ker_eq_bot.2 hH)
  have hcpos : (0 : ℝ) < (2 * (K : ℝ))⁻¹ := by
    apply inv_pos.2; positivity
  have hio := hg.isLittleO.def hcpos
  have htend : Tendsto (fun y : E => (y, z)) (𝓝 z) (𝓝 (z, z)) :=
    Filter.Tendsto.prodMk_nhds tendsto_id tendsto_const_nhds
  filter_upwards [htend.eventually hio] with y hy
  intro hgy
  have hKc : (K : ℝ) * (2 * (K : ℝ))⁻¹ = 1 / 2 := by
    have hKne : (K : ℝ) ≠ 0 := by positivity
    field_simp
  have h1 : dist y z ≤ (K : ℝ) * dist (H y) (H z) := AntilipschitzWith.le_mul_dist hK y z
  have h2 : dist (H y) (H z) ≤ (2 * (K : ℝ))⁻¹ * dist y z := by
    have hHsub : H y - H z = H (y - z) := by rw [map_sub]
    rw [dist_eq_norm, hHsub, dist_eq_norm]
    calc ‖H (y - z)‖ = ‖(H (y - z) - (g y - g z)) + (g y - g z)‖ := by rw [sub_add_cancel]
      _ ≤ ‖H (y - z) - (g y - g z)‖ + ‖g y - g z‖ := norm_add_le _ _
      _ = ‖g y - g z - H (y - z)‖ + ‖g y - g z‖ := by
            rw [show H (y - z) - (g y - g z) = -(g y - g z - H (y - z)) by rw [neg_sub],
              norm_neg]
      _ = ‖g y - g z - H (y - z)‖ := by rw [hgy]; simp
      _ ≤ (2 * (K : ℝ))⁻¹ * ‖y - z‖ := hy
  have h3 : dist y z ≤ (1 / 2) * dist y z := by
    calc dist y z ≤ (K : ℝ) * ((2 * (K : ℝ))⁻¹ * dist y z) :=
          le_trans h1 (mul_le_mul_of_nonneg_left h2 K.2)
      _ = ((K : ℝ) * (2 * (K : ℝ))⁻¹) * dist y z := by ring
      _ = (1 / 2) * dist y z := by rw [hKc]
  have h5 : dist y z = 0 := by nlinarith [dist_nonneg (x := y) (y := z)]
  exact dist_eq_zero.1 h5

/-- A nondegenerate critical point of `f` is isolated in the critical set. -/
lemma isCritical_isolated (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hcrit : Work.Drive.Morse.IsCritical f x)
    (hnd : Work.Drive.Morse.NondegCrit f x) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      U ∩ {y | Work.Drive.Morse.IsCritical f y} ⊆ {x} := by
  set e := extChartAt (𝓡 2) x with he
  have hsrc : x ∈ e.source := mem_extChartAt_source x
  have htgt : e x ∈ e.target := e.map_source hsrc
  set g : EuclideanSpace ℝ (Fin 2) → ℝ := fun y => f (e.symm y) with hg
  set G : EuclideanSpace ℝ (Fin 2) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) := fderiv ℝ g
    with hGG
  -- criticality is the vanishing of `G` at the chart point
  have hcrit_iff : ∀ z ∈ e.source, Work.Drive.Morse.IsCritical f z ↔ G (e z) = 0 := by
    intro z hz
    have hcrit_chart : Work.Drive.Morse.IsCritical f z ↔
        fderiv ℝ (fun y => f (e.symm y)) (e z) = 0 := by
      rw [he]
      exact Work.Drive.N2.isCritical_iff_chartRep f hf x z (by rwa [he] at hz)
    rw [hcrit_chart, hGG, hg]
  have hGz : G (e x) = 0 := (hcrit_iff x hsrc).1 hcrit
  -- smoothness of the chart representation and of its derivative
  have hgsm : ContDiffOn ℝ ∞ g e.target := by
    rw [hg, he]; exact contDiffOn_chartRep f hf x
  have hgAt : ContDiffAt ℝ ∞ g (e x) :=
    hgsm.contDiffAt ((isOpen_extChartAt_target x).mem_nhds (by rw [← he]; exact htgt))
  have hGAt : ContDiffAt ℝ 1 G (e x) := by
    rw [hGG]
    exact hgAt.fderiv_right (by decide)
  have hGstrict : HasStrictFDerivAt G (fderiv ℝ G (e x)) (e x) :=
    hGAt.hasStrictFDerivAt (by simp)
  -- the Hessian is injective by nondegeneracy
  have hHinj : Function.Injective (fderiv ℝ G (e x)) := by
    rw [hGG, hg, he]
    simpa only [Function.comp_def] using hnd.2
  have hlocinj : ∀ᶠ y in 𝓝 (e x), G y = G (e x) → y = e x :=
    eventually_eq_of_hasStrictFDerivAt_injective hGstrict hHinj
  obtain ⟨s, hsub, hsopen, hxs⟩ := mem_nhds_iff.mp hlocinj
  have hU₀ : e.source ∩ e ⁻¹' s ∈ 𝓝 x :=
    Filter.inter_mem
      ((isOpen_extChartAt_source x).mem_nhds (by rw [← he]; exact hsrc))
      ((continuousAt_extChartAt (I := 𝓡 2) x).preimage_mem_nhds
        (hsopen.mem_nhds (by rw [← he]; exact hxs)))
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hU₀
  refine ⟨U, hUopen, hxU, ?_⟩
  rintro y ⟨hyU, hycrit⟩
  simp only [Set.mem_singleton_iff]
  obtain ⟨hyS, hys⟩ := hUsub hyU
  have hyG : G (e y) = 0 := (hcrit_iff y hyS).1 hycrit
  have hey : e y = e x := hsub hys (by rw [hyG, hGz])
  rw [← e.left_inv hyS, hey, e.left_inv hsrc]

/-- The set of critical points of a smooth function is closed. -/
lemma isClosed_isCriticalSet (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) :
    IsClosed {x | Work.Drive.Morse.IsCritical f x} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  set e := extChartAt (𝓡 2) x with he
  have hsrc : x ∈ e.source := mem_extChartAt_source x
  have htgt : e x ∈ e.target := e.map_source hsrc
  set g : EuclideanSpace ℝ (Fin 2) → ℝ := fun y => f (e.symm y) with hg
  set G : EuclideanSpace ℝ (Fin 2) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) := fderiv ℝ g
    with hGG
  have hcrit_iff : ∀ z ∈ e.source, Work.Drive.Morse.IsCritical f z ↔ G (e z) = 0 := by
    intro z hz
    have hcrit_chart : Work.Drive.Morse.IsCritical f z ↔
        fderiv ℝ (fun y => f (e.symm y)) (e z) = 0 := by
      rw [he]
      exact Work.Drive.N2.isCritical_iff_chartRep f hf x z (by rwa [he] at hz)
    rw [hcrit_chart, hGG, hg]
  have hne : G (e x) ≠ 0 := fun h => hx ((hcrit_iff x hsrc).2 h)
  have hgsm : ContDiffOn ℝ ∞ g e.target := by
    rw [hg, he]; exact contDiffOn_chartRep f hf x
  have hgAt : ContDiffAt ℝ ∞ g (e x) :=
    hgsm.contDiffAt ((isOpen_extChartAt_target x).mem_nhds (by rw [← he]; exact htgt))
  have hGcont : ContinuousAt G (e x) := hgAt.continuousAt_fderiv (by simp)
  have hnhds : {y | G y ≠ 0} ∈ 𝓝 (e x) := hGcont.eventually (isOpen_ne.mem_nhds hne)
  have hU₀ : e.source ∩ e ⁻¹' {y | G y ≠ 0} ∈ 𝓝 x :=
    Filter.inter_mem
      ((isOpen_extChartAt_source x).mem_nhds (by rw [← he]; exact hsrc))
      ((continuousAt_extChartAt (I := 𝓡 2) x).preimage_mem_nhds (by rw [← he]; exact hnhds))
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hU₀
  refine Filter.mem_of_superset (hUopen.mem_nhds hxU) fun y hyU hycrit => ?_
  obtain ⟨hyS, hyG⟩ := hUsub hyU
  exact hyG ((hcrit_iff y hyS).1 hycrit)

open scoped Manifold ContDiff in
/-- A Morse function on a compact manifold has only finitely many critical points, which can
therefore be enumerated. -/
theorem exists_enum_critical {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M] (f : M → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hnd : ∀ x, Work.Drive.Morse.IsCritical f x → Work.Drive.Morse.NondegCrit f x) :
    ∃ (k : ℕ) (p : Fin k → M),
      (∀ i, Work.Drive.Morse.IsCritical f (p i)) ∧
      (∀ x, Work.Drive.Morse.IsCritical f x → ∃ i, p i = x) := by
  classical
  let S : Set M := {x : M | Work.Drive.Morse.IsCritical f x}
  have hclosed : IsClosed S := isClosed_isCriticalSet f hf
  have hiso : ∀ p ∈ S, ∃ W : Set M, IsOpen W ∧ p ∈ W ∧ W ∩ S ⊆ {p} :=
    fun p hp => isCritical_isolated f hf p hp (hnd p hp)
  have hfin : S.Finite := Work.Embedding.finite_of_isClosed_forall_isolated hclosed hiso
  letI := hfin.fintype
  let e := Fintype.equivFin S
  refine ⟨Fintype.card S, fun i => (e.symm i).1, fun i => (e.symm i).2, fun x hx => ?_⟩
  refine ⟨e ⟨x, hx⟩, ?_⟩
  exact congrArg Subtype.val (Equiv.symm_apply_apply e ⟨x, hx⟩)

end Work.Drive.N2
