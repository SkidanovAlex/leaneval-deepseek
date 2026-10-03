import Mathlib
import Submission.Work.Pert.RBlock4.retOf_holo
import Submission.Work.Pert.RBlock
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.Gates

namespace Work.Pert.pert2v2

open Filter
open scoped Topology

/-- **The image of an open set under a holomorphic map with nowhere vanishing derivative is
open.**  At a point `z` of `U ⊆ Q`, holomorphy of `Φ` at `z` makes `Φ` strictly differentiable
there; its local inverse `g` is continuous at `Φ z` with `g (Φ z) = z` and is a right inverse of `Φ`
near `Φ z`, so `g` maps a neighbourhood of `Φ z` into `U` and `Φ` maps that neighbourhood onto a
neighbourhood of `Φ z` contained in `Φ '' U`. -/
theorem isOpen_image_of_open {Φ : ℂ → ℂ} {Q U : Set ℂ} (hQ : IsOpen Q)
    (hΦ : DifferentiableOn ℂ Φ Q) (hder : ∀ z ∈ Q, deriv Φ z ≠ 0) (hU : IsOpen U)
    (hUQ : U ⊆ Q) : IsOpen (Φ '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨z, hzU, rfl⟩
  have hzQ : z ∈ Q := hUQ hzU
  have hana : AnalyticAt ℂ Φ z := hΦ.analyticAt (hQ.mem_nhds hzQ)
  have hstr : HasStrictDerivAt Φ (deriv Φ z) z := hana.hasStrictDerivAt
  have hcne : deriv Φ z ≠ 0 := hder z hzQ
  set g : ℂ → ℂ := hstr.localInverse Φ (deriv Φ z) z hcne with hgdef
  have hright : ∀ᶠ w in 𝓝 (Φ z), Φ (g w) = w := by
    have h := hstr.eventually_right_inverse hcne
    rwa [← hgdef] at h
  have hg0 : g (Φ z) = z := by
    have h := (hstr.eventually_left_inverse hcne).self_of_nhds
    rwa [← hgdef] at h
  have hcont : ContinuousAt g (Φ z) :=
    HasDerivAt.continuousAt (HasStrictDerivAt.hasDerivAt (hstr.to_localInverse hcne))
  have hmem : ∀ᶠ w in 𝓝 (Φ z), g w ∈ U := by
    have h : Tendsto g (𝓝 (Φ z)) (𝓝 (g (Φ z))) := hcont
    rw [hg0] at h
    exact h.eventually (hU.mem_nhds hzU)
  filter_upwards [hright, hmem] with w h1 h2
  exact ⟨g w, h2, h1⟩

/-- **The high piece of the two-piece glue (openness + holomorphy).**  With
`Uhigh := {w | |w.re| < 1/2 ∧ Tb < |w.im|} ∩ Φ '' (Qm Ξ α ∩ Qp Ξ α)` and
`Rhigh := Work.Pert.retOf Φ (Qm Ξ α) α`, these are the two inputs `tSat_glue_window` needs for this
chart: `Uhigh` is open and `Rhigh` is holomorphic on it.

* Second conjunct: `Work.Pert.RBlock4.retOf_holo` (proved) gives
  `DifferentiableOn ℂ (retOf Φ (Qm Ξ α) α) (Φ '' (Qm Ξ α ∩ Qp Ξ α))` from the three hypotheses
  verbatim; conclude by `DifferentiableOn.mono`.
* First conjunct: `Qm Ξ α`, `Qp Ξ α` are open (`Work.Fatou.Qreg.isOpen_Qreg`), and the strip
  `{|Re| < 1/2 ∧ Tb < |Im|}` is open for any `Tb`, so only `Φ '' (Qm ∩ Qp)` needs work: at each
  `z ∈ Qm ∩ Qp` use the local inverse of `Φ` at `z` (the `HasStrictDerivAt.localInverse` /
  `invOn_eventuallyEq_localInverse` pattern of `Submission/Work/Pert/MaxDom.lean`, which needs
  holomorphy at `z`, `hder` and injectivity) to get a neighbourhood of `Φ z` inside
  `Φ '' (Qm ∩ Qp)`; take the union. -/
theorem high_piece_data {Φ : ℂ → ℂ} {Ξ : ℝ} {α : ℂ} {Tb : ℝ}
    (hΦm : DifferentiableOn ℂ Φ (Work.Pert.Qm Ξ α))
    (hinj : Set.InjOn Φ (Work.Pert.Qm Ξ α))
    (hder : ∀ z ∈ Work.Pert.Qm Ξ α, deriv Φ z ≠ 0) :
    IsOpen ({w : ℂ | |w.re| < 1 / 2 ∧ Tb < |w.im|} ∩
        Φ '' (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α)) ∧
      DifferentiableOn ℂ (Work.Pert.retOf Φ (Work.Pert.Qm Ξ α) α)
        ({w : ℂ | |w.re| < 1 / 2 ∧ Tb < |w.im|} ∩
          Φ '' (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α)) := by
  -- the open window `{|Re w| < 1/2, Tb < |Im w|}`
  have hstrip : IsOpen {w : ℂ | |w.re| < 1 / 2 ∧ Tb < |w.im|} :=
    (isOpen_lt Complex.continuous_re.abs continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im.abs)
  -- the two gates are open, hence so is their intersection and its image under `Φ`
  have hQp : IsOpen (Work.Pert.Qp Ξ α) := by
    unfold Work.Pert.Qp
    exact Work.Fatou.Qreg.isOpen_Qreg _ _
  have hII : IsOpen (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) :=
    (Work.Pert.RBlock4.isOpen_Qm Ξ α).inter hQp
  have himg : IsOpen (Φ '' (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α)) :=
    isOpen_image_of_open (Work.Pert.RBlock4.isOpen_Qm Ξ α) hΦm hder hII Set.inter_subset_left
  refine ⟨hstrip.inter himg, ?_⟩
  exact (Work.Pert.RBlock4.retOf_holo hΦm hinj hder).mono Set.inter_subset_right

end Work.Pert.pert2v2
