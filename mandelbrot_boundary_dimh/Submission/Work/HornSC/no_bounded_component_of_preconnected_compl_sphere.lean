import Mathlib
import Submission.Work.HornSC.Tools
import Submission.Work.Topology.Continuum.boundary_bumping_theorem
import Submission.Work.Topology.OnePoint.some_image_closure_infty_iff
import Submission.Work.Topology.Connected.connectedComponentIn_image_some
import Submission.Work.Topology.Connected.subtype_val_image_connectedComponentIn

namespace Work.HornSC

open Set

/-- **A preconnected sphere-complement has no bounded complementary component.**
If `X` is open in `ℂ` and `(OnePoint.some '' X)ᶜ = Xᶜ ∪ {∞}` is preconnected in the Riemann sphere,
then no connected component of `Xᶜ` is bounded.

Route: `K := (OnePoint.some '' X)ᶜ` is a closed (hence compact) preconnected subset of the Riemann
sphere, i.e. the subtype `↥K` is a continuum.  With `p := ∞ ∈ K` and `c := some z ∈ K` (for
`z ∉ X`), the classical *boundary bumping theorem*
(`Work.Topology.Continuum.boundary_bumping_theorem`) says that `p` lies in the closure of the
connected component of `c` in `K \ {p}`.  Transporting this closure statement from the subtype to
the sphere (`closure_subtype`), and identifying `K \ {∞} = some '' Xᶜ` with the component of `c` as
the image under `some` of `connectedComponentIn Xᶜ z`, gives
`∞ ∈ closure (some '' connectedComponentIn Xᶜ z)`, which by
`Work.Topology.OnePoint.some_image_closure_infty_iff` is exactly the unboundedness of
`connectedComponentIn Xᶜ z`. -/
theorem no_bounded_component_of_preconnected_compl_sphere {X : Set ℂ} (hX : IsOpen X)
    (h : IsPreconnected ((OnePoint.some '' X : Set (OnePoint ℂ))ᶜ)) :
    ∀ z : ℂ, z ∉ X → ¬ Bornology.IsBounded (connectedComponentIn Xᶜ z) := by
  intro z hz
  -- the complement of `some '' X` in the sphere, its description, and its compactness
  set K : Set (OnePoint ℂ) := (OnePoint.some '' X)ᶜ with hK
  have hK_eq : K = OnePoint.some '' (Xᶜ) ∪ {OnePoint.infty} := by
    rw [hK, OnePoint.compl_image_coe]
  have hKclosed : IsClosed K := by
    rw [hK]; exact isClosed_compl_iff.mpr (OnePoint.isOpen_image_coe.mpr hX)
  have hKcompact : IsCompact K := hKclosed.isCompact
  -- the subtype `↥K` is a continuum, since `K` is compact and preconnected
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hKcompact
  haveI : PreconnectedSpace ↥K := isPreconnected_iff_preconnectedSpace.mp h
  have hsz : (OnePoint.some z) ∈ K := by
    rw [hK_eq]; exact Or.inl ⟨z, hz, rfl⟩
  have hinf : (OnePoint.infty) ∈ K := by
    rw [hK_eq]; exact Or.inr rfl
  set c : ↥K := ⟨OnePoint.some z, hsz⟩ with hcdef
  set p : ↥K := ⟨OnePoint.infty, hinf⟩ with hp
  haveI : ConnectedSpace ↥K := ConnectedSpace.mk ⟨c⟩
  have hcne : c ≠ p := by
    intro hcp
    have h1 : (OnePoint.some z : OnePoint ℂ) = OnePoint.infty := by
      have h2 := congrArg Subtype.val hcp
      rw [hcdef, hp] at h2
      exact h2
    exact OnePoint.coe_ne_infty z h1
  -- boundary bumping inside the continuum `↥K`
  have hbump : p ∈ closure (connectedComponentIn ({p}ᶜ : Set ↥K) c) :=
    Work.Topology.Continuum.boundary_bumping_theorem (Z := ↥K) p c hcne
  -- move the statement to the ambient sphere
  have hclos : (OnePoint.infty) ∈
      closure (Subtype.val '' (connectedComponentIn ({p}ᶜ : Set ↥K) c)) := by
    have h2 := (closure_subtype (x := p) (s := connectedComponentIn ({p}ᶜ : Set ↥K) c)).mp hbump
    rw [hp] at h2
    exact h2
  -- identify `Subtype.val '' {p}ᶜ` with `K \ {∞} = some '' Xᶜ`
  have hF1 : (Subtype.val '' ({p}ᶜ : Set ↥K)) = K \ {OnePoint.infty} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.2, ?_⟩
      intro hcon
      exact hx (Subtype.ext (by rw [hp]; exact hcon))
    · rintro ⟨hyK, hyne⟩
      refine ⟨⟨y, hyK⟩, ?_, rfl⟩
      intro hcon
      have h5 : y = OnePoint.infty := by
        have h6 := congrArg Subtype.val hcon
        rw [hp] at h6
        exact h6
      exact hyne h5
  have hF2 : K \ {OnePoint.infty} = OnePoint.some '' (Xᶜ) := by
    rw [hK_eq]
    ext y
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h | h, hne⟩
      · exact h
      · exact absurd h hne
    · intro hh; exact ⟨Or.inl hh, fun hc => OnePoint.infty_notMem_image_coe (hc ▸ hh)⟩
  -- the transported component is the image of `connectedComponentIn Xᶜ z`
  have hcomp : Subtype.val '' (connectedComponentIn ({p}ᶜ : Set ↥K) c)
      = OnePoint.some '' connectedComponentIn Xᶜ z := by
    have hDc := Work.Topology.Connected.subtype_val_image_connectedComponentIn
      (K := K) (F := ({p}ᶜ : Set ↥K)) (x := c)
    rw [hDc, hF1, hF2]
    have h3 : (↑c : OnePoint ℂ) = OnePoint.some z := by rw [hcdef]
    rw [h3]
    exact Work.Topology.Connected.connectedComponentIn_image_some hz
  rw [hcomp] at hclos
  exact (Work.Topology.OnePoint.some_image_closure_infty_iff).mp hclos

end Work.HornSC
