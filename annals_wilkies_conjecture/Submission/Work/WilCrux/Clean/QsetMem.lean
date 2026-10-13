import Mathlib
import Submission.Work.WilCrux.Clean.AccSetDefs

namespace Work.WilCrux.Clean

open WilkiesDesign WilkiesConjecture

/--
The auxiliary set `Qset a b E ⊆ ℝ^{(a+1)+b}` is `Ω`-definable whenever `E` is.

Its defining conjuncts are `Ω`-definable separately:

* the pullback `{x | x ∘ iIdx a b ∈ E}` of `E` along the coordinate embedding `iIdx a b`
  (`Work.WilG5.coordPre_mem`);
* the half-space `{x | 0 < x (dIdx a b)}` (`Work.WilG5.ltSet_mem`);
* the remaining condition block `z ≠ 0 ∧ ∀ j, |z j| < δ`, which is the empty-`α`/`β` case of
  `Work.WilCrux.TripleMem`.

They are glued with the binary intersection lemma `inter2_mem`.
-/
theorem QsetMem (S : WilkiesDesign.SOMin) {a b F D : ℕ} {E : Set (Fin (a+b) → ℝ)}
    (hE : E ∈ S.Ω F D (a+b)) :
    ∃ F' D' : ℕ, Work.WilCrux.Clean.Qset a b E ∈ S.Ω F' D' ((a+1)+b) := by
  classical
  -- The pullback of `E` along `iIdx a b`.
  have hA : ({x : Fin ((a+1)+b) → ℝ | x ∘ iIdx a b ∈ E}) ∈
      S.Ω (F + 64 * (((a+1)+b) + (a+b)) + 64)
        (D + 32 * (((a+1)+b) + (a+b)) + 32) ((a+1)+b) :=
    Work.WilG5.coordPre_mem (S := S) (ι := iIdx a b) (A := E) hE
  -- The half-space `0 < δ`.
  have hB : ({x : Fin ((a+1)+b) → ℝ | 0 < x (dIdx a b)}) ∈
      S.Ω (4 * ((a+1)+b) + 20) 8 ((a+1)+b) :=
    Work.WilG5.ltSet_mem (S := S) (dIdx a b) 0
  -- The z-block conditions `z ≠ 0` and `|z j| < δ`, from `TripleMem` with no `α`/`β` block.
  obtain ⟨AT, qT, hqT⟩ := Work.WilCrux.TripleMem S
    (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0)
    (fun j : Fin b => zIdx a b j) (dIdx a b)
  have hCD : ({x : Fin ((a+1)+b) → ℝ | (fun j : Fin b => x (zIdx a b j)) ≠ 0} ∩
      {x : Fin ((a+1)+b) → ℝ | ∀ j : Fin b, |x (zIdx a b j)| < x (dIdx a b)}) ∈
      S.Ω AT (qT.eval 0) ((a+1)+b) := by
    have h := hqT 0
    convert h using 2
    -- `TripleMem`'s empty `∀ i : Fin 0` block is vacuous.
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨fun i => i.elim0, h1, h2⟩, fun ⟨_, h1, h2⟩ => ⟨h1, h2⟩⟩
  have h1 := inter2_mem (S := S) hA hB
  have h2 := inter2_mem (S := S) h1 hCD
  exact ⟨_, _, h2⟩

end Work.WilCrux.Clean
