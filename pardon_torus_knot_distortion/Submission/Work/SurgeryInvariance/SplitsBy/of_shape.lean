import Mathlib
import Submission.Work.SurgeryInvariance.Defs

namespace Work.SurgeryInvariance.SplitsBy

theorem of_shape {P : Work.CoreTopology.ParamTorus}
    {A A' : Set LeanEval.KnotTheory.PardonDistortion.R3}
    {D : Work.SurgeryInvariance.DiscRegion P}
    (hopen : Work.SurgeryInvariance.IsOpenInCarrier P A')
    (hcover : A = A' ∪ D.interior) (hdisj : Disjoint A' D.interior) :
    Work.SurgeryInvariance.SplitsBy P A A' D := by
  intro γ hγ
  -- Transport the closed curve to a continuous curve into the surface `P.carrier`, so that
  -- "open in the carrier" becomes ordinary openness of a preimage in `ℝ`.
  let g : ℝ → P.carrier := fun t => ⟨γ t, γ.mem t⟩
  have hgcont : Continuous g := γ.cont.subtype_mk γ.mem
  set u : Set ℝ := {t | γ t ∈ A'} with hu_def
  set v : Set ℝ := {t | γ t ∈ D.interior} with hv_def
  have hu : IsOpen u := by
    have h : u = g ⁻¹' (Subtype.val ⁻¹' A') := by ext t; simp [u, g]
    rw [h]; exact hopen.preimage hgcont
  have hv : IsOpen v := by
    have h : v = g ⁻¹' (Subtype.val ⁻¹' D.interior) := by ext t; simp [v, g]
    rw [h]; exact D.open_interior.preimage hgcont
  have huv : Disjoint u v := by
    rw [Set.disjoint_left]
    intro t htu htv
    have hmem : γ t ∈ A' ∩ D.interior := ⟨htu, htv⟩
    rw [Set.disjoint_iff_inter_eq_empty] at hdisj
    rw [hdisj] at hmem
    exact hmem
  have hsuv : (Set.univ : Set ℝ) ⊆ u ∪ v := by
    intro t _
    have : γ t ∈ A := hγ t
    rw [hcover] at this
    rcases this with h | h
    · left; exact h
    · right; exact h
  -- `ℝ` is preconnected, so the image of `γ` lies entirely in one of the two disjoint open
  -- pieces `A'` and `D.interior`.
  rcases IsPreconnected.subset_or_subset hu hv huv hsuv isPreconnected_univ with h | h
  · left; intro t; exact h (Set.mem_univ t)
  · right; intro t; exact D.interior_subset_carrier (h (Set.mem_univ t))

end Work.SurgeryInvariance.SplitsBy
