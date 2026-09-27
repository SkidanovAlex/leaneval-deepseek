import Submission.Work.EKLNonExc.DinjAux.Basic

/-!
# `V δ` is a neighbourhood basis of the identity in `SL₃(ℝ)`

The boxes `V δ = {g | |g_ij - δ_ij| < δ}` shrink to `{1}` and every neighbourhood of `1`
contains some `V δ`.  This is the only place where the entrywise (product) topology of the
matrix space is unfolded.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Work.EKLNonExc
namespace DinjAux

open Work.EKLContract Filter Topology

noncomputable section

/-- Every neighbourhood of `1` in `SL₃(ℝ)` contains a box `V δ` (`δ > 0`). -/
lemma VNhds {B : Set SL3} (hB : B ∈ 𝓝 (1 : SL3)) : ∃ ε > 0, V ε ⊆ B := by
  obtain ⟨U, hUsub, hUopen, hU1⟩ := mem_nhds_iff.mp hB
  obtain ⟨U', hU'open, hU'eq⟩ := isOpen_induced_iff.mp hUopen
  have h1U' : (1 : M3) ∈ U' := by
    have hh : ((1 : SL3) : M3) ∈ U' := by
      rw [← Set.mem_preimage, hU'eq]
      exact hU1
    simpa using hh
  obtain ⟨u, hu, hu_sub⟩ := (isOpen_pi_iff').mp hU'open (1 : M3) h1U'
  have hbox : ∀ i : Fin 3, ∃ v : Fin 3 → Set ℝ,
      (∀ j, IsOpen (v j) ∧ (1 : M3) i j ∈ v j) ∧ Set.univ.pi v ⊆ u i :=
    fun i => (isOpen_pi_iff').mp (hu i).1 ((1 : M3) i) (hu i).2
  choose v hv hv_sub using hbox
  have hε : ∀ i j : Fin 3, ∃ e : ℝ, 0 < e ∧
      Set.Ioo (((1 : M3) i j) - e) (((1 : M3) i j) + e) ⊆ v i j := by
    intro i j
    have hmem : v i j ∈ 𝓝 ((1 : M3) i j) := (hv i j).1.mem_nhds (hv i j).2
    obtain ⟨e, he, hsub⟩ := Metric.mem_nhds_iff.mp hmem
    exact ⟨e, he, by rwa [Real.ball_eq_Ioo] at hsub⟩
  choose e hepos hεsub using hε
  refine ⟨(Finset.univ : Finset (Fin 3)).inf' Finset.univ_nonempty
      (fun i => (Finset.univ : Finset (Fin 3)).inf' Finset.univ_nonempty (fun j => e i j)), ?_, ?_⟩
  · refine (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ => ?_)
    refine (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun j _ => ?_)
    exact hepos i j
  · intro g hg
    have hmemU' : (↑g : M3) ∈ U' := by
      refine hu_sub (Set.mem_univ_pi.mpr (fun i => ?_))
      refine hv_sub i (Set.mem_univ_pi.mpr (fun j => ?_))
      exact hεsub i j (by
        rw [Set.mem_Ioo]
        have hgij := hg i j
        have hle : (Finset.univ : Finset (Fin 3)).inf' Finset.univ_nonempty
            (fun i => (Finset.univ : Finset (Fin 3)).inf' Finset.univ_nonempty (fun j => e i j))
            ≤ e i j :=
          le_trans (Finset.inf'_le _ (Finset.mem_univ i)) (Finset.inf'_le _ (Finset.mem_univ j))
        rw [abs_lt] at hgij
        exact ⟨by linarith [hgij.1, hle], by linarith [hgij.2, hle]⟩)
    have hgU : g ∈ U := by
      rw [← hU'eq]
      exact hmemU'
    exact hUsub hgU

end

end DinjAux
end Work.EKLNonExc
