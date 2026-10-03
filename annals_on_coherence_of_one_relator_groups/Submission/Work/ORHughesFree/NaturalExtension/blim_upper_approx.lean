import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.Defs

namespace Work.ORHughesFree.NaturalExtension

/-- Upper approximation of the ultralimit: for a bounded sequence `f`, the set of indices where `f`
is at most `blim ω f + ε` is `ω`-large. This is the order-theoretic content of the definition
`blim ω f = sSup {r | {i | r ≤ f i} ∈ ω}` together with the ultrafilter dichotomy. -/
theorem blim_upper_approx (ω : Ultrafilter ℕ) {f : ℕ → ℝ} {M : ℝ} (hf : ∀ i, |f i| ≤ M)
    {ε : ℝ} (hε : 0 < ε) : {i : ℕ | f i ≤ blim ω f + ε} ∈ ω := by
  -- `S` is the set whose supremum defines the ultralimit.
  set S : Set ℝ := {r : ℝ | {i | r ≤ f i} ∈ ω} with hS
  have hb : blim ω f = sSup S := rfl
  -- Boundedness of the sequence makes `S` bounded above, with bound `M`.
  have hbdd : BddAbove S := by
    refine ⟨M, fun r hr => ?_⟩
    rw [hS] at hr
    obtain ⟨i, hi⟩ := Ultrafilter.nonempty_of_mem hr
    exact le_trans hi (abs_le.mp (hf i)).2
  by_contra hcon
  -- If the desired set were not in `ω`, its complement would be, and on that complement `f`
  -- strictly exceeds `blim ω f + ε`.
  have hmem : {i : ℕ | blim ω f + ε < f i} ∈ ω := by
    have hc : {i : ℕ | f i ≤ blim ω f + ε}ᶜ ∈ ω :=
      Ultrafilter.compl_mem_iff_notMem.mpr hcon
    refine Filter.mem_of_superset hc (fun i hi => ?_)
    show blim ω f + ε < f i
    exact not_le.mp hi
  -- Then `blim ω f + ε` lies in `S`, contradicting that it is the supremum.
  have hmem2 : {i : ℕ | blim ω f + ε ≤ f i} ∈ ω :=
    Filter.mem_of_superset hmem (fun i hi => show blim ω f + ε ≤ f i from le_of_lt hi)
  have hSmem : blim ω f + ε ∈ S := by
    rw [hS] at *
    exact hmem2
  have hle := le_csSup hbdd hSmem
  rw [hb] at hle
  linarith

end Work.ORHughesFree.NaturalExtension
