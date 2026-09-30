import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.transl_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Phase 4 helper for `coset_minimalPrime` and `coset_length` (`V ⋆ G_V = V`). If `v ∈ ZG 𝔓` and
`u ∈ stabG 𝔓` then `v u ∈ ZG 𝔓`: for `F ∈ 𝔓`, `F(v u) = (τ_u F)(v)` and `τ_u F ∈ map τ_u 𝔓 = 𝔓`
(`transl_basic`, commutativity of `gmul`). Size 0.2–0.4k. -/
theorem gmul_mem_ZG_of_stab {N : ℕ} (𝔓 : Ideal (MR N)) (v u : Fin (N + 1) → ℂ)
    (hv : v ∈ ZG 𝔓) (hu : u ∈ stabG 𝔓) : gmul v u ∈ ZG 𝔓 := by
  obtain ⟨hvG, hvF⟩ := hv
  obtain ⟨huG, huF⟩ := hu
  refine ⟨?_, ?_⟩
  · -- `InG` is closed under the group law.
    intro i
    simp only [gmul, Fin.cons_succ]
    exact mul_ne_zero (hvG i) (huG i)
  · -- `F ↦ F ∘ conePt` turns the group law into the translation action.
    intro F hF
    have htu : transl u F ∈ 𝔓 := by
      have h : transl u F ∈ Ideal.map (transl u) 𝔓 := Ideal.mem_map_of_mem _ hF
      rwa [huF] at h
    have h1 := (transl_basic u v).1 (conePt N v) F
    have h2 := (transl_basic u v).2.1 v
    have hzero : MvPolynomial.eval (conePt N (gmul u v)) F = 0 := by
      rw [← h2, ← h1]
      exact hvF (transl u F) htu
    have hcomm : gmul u v = gmul v u := by
      funext j
      refine Fin.cases ?_ ?_ j
      · simp only [gmul, Fin.cons_zero]; ring
      · intro i; simp only [gmul, Fin.cons_succ]; ring
    rwa [hcomm] at hzero

end Work.BW
