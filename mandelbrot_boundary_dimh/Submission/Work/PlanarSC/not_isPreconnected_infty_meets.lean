import Mathlib
import Submission.Work.PlanarSC.Tools
import Submission.Work.HornSC.no_bounded_component_of_preconnected_compl_sphere

/-!
# No preconnected set of `Ωᶜ ∪ {∞}` joins a compact component of `Ωᶜ` to `∞`

Let `Ω ⊆ ℂ` be an open domain and let `K ⊆ Ωᶜ` be a compact connected set which is *maximal*
preconnected inside `Ωᶜ` (i.e. a connected component of `Ωᶜ`).  Then no preconnected subset `L` of
the one-point compactification `ℂ* = OnePoint ℂ`, contained in `Ωᶜ ∪ {∞}` and meeting `K`, can also
contain the point at infinity.

The mathematical content is the classical *boundary bumping* phenomenon: if `C` is a continuum and
`p ∈ C`, then `p` lies in the closure of the connected component of any other point in `C \ {p}`
(`Work.Topology.Continuum.boundary_bumping_theorem`) — transported to the plane it says that a
preconnected sphere-complement has no bounded complementary component
(`Work.HornSC.no_bounded_component_of_preconnected_compl_sphere`).  Since `K` is *compact*, it is
bounded, and this is exactly the contradiction.
-/

namespace Work.PlanarSC

open Set

theorem not_isPreconnected_infty_meets {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    {K : Set ℂ} (hKcpt : IsCompact K)
    (hKconn : IsConnected K) (hKsub : K ⊆ Ωᶜ)
    (hKmax : ∀ S : Set ℂ, IsPreconnected S → K ⊆ S → S ⊆ Ωᶜ → S = K) {a : ℂ} (haK : a ∈ K) :
    ¬ ∃ L : Set (OnePoint ℂ), IsPreconnected L ∧ (a : OnePoint ℂ) ∈ L ∧
      (OnePoint.infty : OnePoint ℂ) ∈ L ∧ L ⊆ ((↑) '' Ωᶜ) ∪ {OnePoint.infty} := by
  rintro ⟨L, hLpre, haL, hinfL, hLsub⟩
  -- The compact space `X := ↑''Ωᶜ ∪ {∞} = (↑''Ω)ᶜ` in which everything happens.
  set X : Set (OnePoint ℂ) := (OnePoint.some '' Ωᶜ) ∪ {OnePoint.infty} with hXdef
  have hXclosed : IsClosed X := by
    rw [hXdef, ← OnePoint.compl_image_coe Ω]
    exact (OnePoint.isOpen_image_coe.mpr hΩo).isClosed_compl
  -- Step 1: we may assume `L` is closed.
  have hLpre' : IsPreconnected (closure L) := hLpre.closure
  have hLsub' : closure L ⊆ X := closure_minimal hLsub hXclosed
  have haL' : (a : OnePoint ℂ) ∈ closure L := subset_closure haL
  have hinfL' : (OnePoint.infty : OnePoint ℂ) ∈ closure L := subset_closure hinfL
  -- Step 2: `C := closure L ∪ ↑''K` is a continuum inside `X`.
  set C : Set (OnePoint ℂ) := closure L ∪ (OnePoint.some '' K) with hCdef
  have hKC : (a : OnePoint ℂ) ∈ OnePoint.some '' K := ⟨a, haK, rfl⟩
  have hK'pre : IsPreconnected (OnePoint.some '' K) :=
    hKconn.isPreconnected.image _ OnePoint.continuous_coe.continuousOn
  have hCpre : IsPreconnected C := by
    rw [hCdef]
    exact IsPreconnected.union' ⟨(a : OnePoint ℂ), haL', hKC⟩ hLpre' hK'pre
  have hK'cpt : IsCompact (OnePoint.some '' K) := hKcpt.image OnePoint.continuous_coe
  have hCclosed : IsClosed C := by
    rw [hCdef]
    exact isClosed_closure.union hK'cpt.isClosed
  have hCsub : C ⊆ X := by
    rw [hCdef]
    refine union_subset hLsub' ?_
    rintro _ ⟨k, hk, rfl⟩
    exact Or.inl ⟨k, hKsub hk, rfl⟩
  -- Step 3: the part `D` of `C` lying in `ℂ`: a closed subset of `Ωᶜ`.
  set D : Set ℂ := OnePoint.some ⁻¹' C with hDdef
  have hDclosed : IsClosed D := hCclosed.preimage OnePoint.continuous_coe
  have hDsub : D ⊆ Ωᶜ := by
    intro z hz
    rcases hCsub hz with h | h
    · obtain ⟨w, hw, hwz⟩ := h
      rwa [OnePoint.coe_injective hwz] at hw
    · exact absurd h (OnePoint.coe_ne_infty z)
  have hCD : (OnePoint.some '' D) ∪ {OnePoint.infty} = C := by
    apply Set.Subset.antisymm
    · rintro z (⟨x, hx, rfl⟩ | rfl)
      · exact hx
      · rw [hCdef]; exact Or.inl (subset_closure hinfL)
    · intro z hz
      rcases hCsub hz with h | h
      · obtain ⟨w, hw, hwz⟩ := h
        refine Or.inl ⟨w, ?_, hwz⟩
        rw [hDdef, Set.mem_preimage, hwz]
        exact hz
      · exact Or.inr h
  -- Step 4: boundary bumping, in the form "a preconnected sphere-complement has no bounded
  -- complementary component".
  have hpre : IsPreconnected ((OnePoint.some '' Dᶜ : Set (OnePoint ℂ))ᶜ) := by
    rw [OnePoint.compl_image_coe, compl_compl, hCD]
    exact hCpre
  have hnb := Work.HornSC.no_bounded_component_of_preconnected_compl_sphere
    (X := Dᶜ) hDclosed.isOpen_compl hpre
  -- Step 5: `K` is the connected component of `a` inside `D`, hence bounded — contradiction.
  have haD : a ∈ D := by
    rw [hDdef, Set.mem_preimage, hCdef]
    exact Or.inr ⟨a, haK, rfl⟩
  have hKD : K ⊆ D := by
    intro k hk
    rw [hDdef, Set.mem_preimage, hCdef]
    exact Or.inr ⟨k, hk, rfl⟩
  have hcomp : connectedComponentIn D a = K := by
    refine Set.Subset.antisymm ?_ ?_
    · have hunion : K ∪ connectedComponentIn D a = K :=
        hKmax _ (hKconn.isPreconnected.union a haK (mem_connectedComponentIn haD)
            isPreconnected_connectedComponentIn)
          subset_union_left
          (union_subset hKsub ((connectedComponentIn_subset D a).trans hDsub))
      intro z hz
      rw [← hunion]
      exact Or.inr hz
    · exact hKconn.isPreconnected.subset_connectedComponentIn haK hKD
  have hbdd : ¬ Bornology.IsBounded K := by
    have h1 : ¬ Bornology.IsBounded (connectedComponentIn D a) := by
      have h2 := hnb a (by simp [haD])
      rwa [compl_compl] at h2
    rwa [hcomp] at h1
  exact hbdd hKcpt.isBounded

end Work.PlanarSC
