import Mathlib
import Submission.Work.WilG4c.SlicePinnedDefs
import Submission.Work.WilG4c.GraphOfComp

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- The coordinate substitution realising `padFam`: it sends the `p+(n+1)` "input"
coordinates `(l, x, y)` of `famGraph f` to the same coordinates of the padded layout and the
value coordinate to the value coordinate, leaving out the *dummy* coordinate `p+n+1` of the
padded layout.  In other words it is the identity on `0..p+n` and sends `Fin.last` to
`Fin.last`. -/
def padSig2 (p n : ℕ) : Fin (p + (n + 1) + 1) → Fin ((p + 1) + (n + 1) + 1) :=
  Fin.snoc (fun k : Fin (p + (n + 1)) => Fin.castLE (by omega) k)
    (Fin.last ((p + 1) + (n + 1)))

@[simp] theorem padSig2_castSucc (p n : ℕ) (i : Fin (p + (n + 1))) :
    padSig2 p n (Fin.castSucc i) = Fin.castLE (by omega) i := by
  simp [padSig2, Fin.snoc_castSucc]

@[simp] theorem padSig2_last (p n : ℕ) :
    padSig2 p n (Fin.last (p + (n + 1))) = Fin.last ((p + 1) + (n + 1)) := by
  simp [padSig2, Fin.snoc_last]

/-- The graph of `padFam p n f` is the graph of `f` read through the coordinate substitution
`padSig2`: the distinguished coordinate `x` is moved into the parameter block, and the extra
cube coordinate (which `padFam` ignores) is the coordinate dropped by `padSig2`. -/
theorem famGraph_padFam_eq (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    famGraph (WilkG4c.padFam p n f) =
      {x : Fin ((p + 1) + (n + 1) + 1) → ℝ | x ∘ padSig2 p n ∈ famGraph f} := by
  ext x
  simp only [famGraph, graphOf, Set.mem_ofPred_eq, Function.comp_apply, padSig2_last,
    WilkG4c.padFam_apply, Fin.init_def]
  have hA : (fun i : Fin p => x (Fin.castSucc (Fin.castAdd (n + 1) (Fin.castSucc i))))
      = (fun i : Fin p => x (padSig2 p n (Fin.castSucc (Fin.castAdd (n + 1) i)))) := by
    funext i
    simp only [padSig2_castSucc]
    congr 1
  have hB : Fin.cons (x (Fin.castSucc (Fin.castAdd (n + 1) (Fin.last p))))
        (fun k : Fin n => x (Fin.castSucc (Fin.natAdd (p + 1) (Fin.castSucc k))))
      = (fun j : Fin (n + 1) => x (padSig2 p n (Fin.castSucc (Fin.natAdd p j)))) := by
    funext j
    rw [padSig2_castSucc]
    refine Fin.cases ?_ ?_ j
    · rfl
    · intro j'
      simp only [Fin.cons_succ]
      congr 1
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_natAdd, Fin.val_castLE, Fin.val_succ]
      omega
  rw [hA, hB]

/-- `padFam p n f` is `f` with the distinguished coordinate `x` moved into the parameter list and
one *ignored* cube coordinate appended (`Work.WilkG4c.padFam`); its graph is the graph of `f` read
through a coordinate substitution, so `Ω`-boundedness transfers at the cost of constants only.
(`Work.WilkG4c.subst_mem` in `GraphOfComp.lean` applies with the index map
`σ : Fin (p+(n+1)+1) → Fin ((p+1)+(n+1)+1)` that fixes `0..p+n` and sends `Fin.last ↦ Fin.last`.) -/
theorem padFam_famGraph_mem (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ (C C' : ℕ), ∀ (F0 D : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      WilkiesDesign.CG.famGraph (Work.WilkG4c.padFam p n f) ∈
        S.Ω (F0 + C) (D + C') ((p + 1) + (n + 1) + 1) := by
  refine ⟨2 * (((p + 1) + (n + 1) + 1) + (p + (n + 1) + 1)) + 1, 2, ?_⟩
  intro F0 D f hf
  have h := GraphComp.subst_mem S (padSig2 p n) hf
  rw [← famGraph_padFam_eq p n f] at h
  exact Work.WilG0.Omega_mono_FD (by omega) (le_refl _) h

end Work.WilG4c
