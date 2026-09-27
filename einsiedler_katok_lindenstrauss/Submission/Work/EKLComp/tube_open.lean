import Mathlib
import Submission.Work.EKLComp.USCBasic

namespace Work.EKLComp

open Work.EKLContract

/-!
# The "tube" around a compact set of `SL₃(ℝ)` acting on `X₃`

For `K ⊆ SL₃(ℝ)` compact and `U ⊆ X₃` open, the set of `z : X₃` whose entire `K`-orbit lies in
`U` is open.  The proof is the classical tube lemma: the action map
`F : SL₃(ℝ) × X₃ → X₃`, `F(g, z) = g • z`, is continuous, `F ⁻¹' U` is an open neighbourhood of
the compact product `K × {z}`, and `generalized_tube_lemma` produces an open neighbourhood `v` of
`z` with `K × v ⊆ F ⁻¹' U`.
-/

theorem tube_open {K : Set Work.EKLContract.SL3} (hK : IsCompact K) {U : Set Work.EKLContract.X3} (hU : IsOpen U) : IsOpen {z : Work.EKLContract.X3 | ∀ g ∈ K, g • z ∈ U} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hcont : Continuous fun p : Work.EKLContract.SL3 × Work.EKLContract.X3 => p.1 • p.2 := by
    continuity
  have hn : IsOpen ((fun p : Work.EKLContract.SL3 × Work.EKLContract.X3 => p.1 • p.2) ⁻¹' U) :=
    hU.preimage hcont
  have hsub : K ×ˢ ({z} : Set Work.EKLContract.X3) ⊆
      (fun p : Work.EKLContract.SL3 × Work.EKLContract.X3 => p.1 • p.2) ⁻¹' U := by
    rintro ⟨g, y⟩ ⟨hg, hy⟩
    simp only [Set.mem_singleton_iff] at hy
    subst hy
    exact hz g hg
  obtain ⟨u, v, -, hv, hKu, hzv, huv⟩ :=
    generalized_tube_lemma hK isCompact_singleton hn hsub
  refine Filter.mem_of_superset (hv.mem_nhds (hzv (Set.mem_singleton z))) ?_
  intro y hy g hg
  exact huv (Set.mk_mem_prod (hKu hg) hy)

end Work.EKLComp
