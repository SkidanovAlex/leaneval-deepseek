import Mathlib
import Submission.Work.WilkiesH.Strat.omega_closure_defs

/-!
# The image of the joint set under the last `n + 1` coordinates

The joint set `jointSet W` lives in `ℝ^(n + (n+1))`: the first `n` coordinates carry the witness
`y ∈ W`, the next `n` the point `x` and the last one the radius `t`.  Projecting onto the *last*
`n + 1` coordinates (the map `Fin.natAdd n`, whose image consists of the point/radius block)
yields exactly the set of pairs `(x, t)` with `t > 0` and `|x - y|² < t²` for some `y ∈ W`:

`omega_closure_coordImage` identifies that projection with the set written in the target.
The whole content is the identity `xIdx n i = Fin.natAdd n (Fin.castAdd 1 i)` (resp.
`tIdx n = Fin.natAdd n (Fin.last n)`), i.e. the point/radius coordinates are the `Fin.natAdd`
block, together with the reading of a function on `Fin (n + (n+1))` as `Fin.append y u`.
-/

set_option autoImplicit false

namespace Work.WilkiesH.Strat

theorem omega_closure_coordImage {n : ℕ} (W : Set (Fin n → ℝ)) :
    Work.WilG5.coordImage (Fin.natAdd n) (jointSet W) =
      {u : Fin (n + 1) → ℝ | 0 < u (Fin.last n) ∧
        ∃ y, y ∈ W ∧ ∀ i, (u (Fin.castAdd 1 i) - y i) ^ 2 < (u (Fin.last n)) ^ 2} := by
  ext u
  constructor
  · -- a point of the image comes from some `z ∈ jointSet W`
    intro hu
    simp only [Work.WilG5.coordImage, Set.mem_ofPred_eq] at hu
    obtain ⟨z, hz, hzu⟩ := hu
    simp only [jointSet, Set.mem_inter_iff, Set.mem_iInter, Work.WilG5.coordPre, boxSet, posSet,
      Set.mem_ofPred_eq] at hz
    obtain ⟨⟨hzW, hzbox⟩, hzt⟩ := hz
    refine ⟨?_, z ∘ yIdx n, hzW, fun i => ?_⟩
    · -- positivity of the radius: `u (last n) = z (tIdx n)`
      have h : u (Fin.last n) = z (tIdx n) := (congrFun hzu (Fin.last n)).symm
      rw [h]; exact hzt
    · -- the box inequalities transport along `z ∘ Fin.natAdd n = u`
      have hb := hzbox i
      rw [boxPoly_eval] at hb
      have hx : z (xIdx n i) = u (Fin.castAdd 1 i) := congrFun hzu (Fin.castAdd 1 i)
      have ht : z (tIdx n) = u (Fin.last n) := congrFun hzu (Fin.last n)
      rw [hx, ht] at hb
      show (u (Fin.castAdd 1 i) - z (yIdx n i)) ^ 2 < (u (Fin.last n)) ^ 2
      linarith
  · -- conversely, build the witness in the joint space as `Fin.append y u`
    intro hu
    simp only [Set.mem_ofPred_eq] at hu
    obtain ⟨hpos, y, hyW, hybox⟩ := hu
    refine ⟨Fin.append y u, ?_, ?_⟩
    · simp only [jointSet, Set.mem_inter_iff, Set.mem_iInter, Work.WilG5.coordPre, boxSet, posSet,
        Set.mem_ofPred_eq]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · -- the witness block of `Fin.append y u` is `y ∈ W`
        have h : Fin.append y u ∘ yIdx n = y := by
          funext i; exact Fin.append_left y u i
        rw [h]; exact hyW
      · intro i
        rw [boxPoly_eval]
        have hx : Fin.append y u (xIdx n i) = u (Fin.castAdd 1 i) :=
          Fin.append_right y u (Fin.castAdd 1 i)
        have hyy : Fin.append y u (yIdx n i) = y i := Fin.append_left y u i
        have ht : Fin.append y u (tIdx n) = u (Fin.last n) := Fin.append_right y u (Fin.last n)
        rw [hx, hyy, ht]
        linarith [hybox i]
      · have ht : Fin.append y u (tIdx n) = u (Fin.last n) := Fin.append_right y u (Fin.last n)
        rw [ht]; exact hpos
    · funext j
      exact Fin.append_right y u j

end Work.WilkiesH.Strat
