/-
  WilG1 / Cell / Junk / fibBad_mem.

  `fibBad h i` (the parameters at which the fibre of `h` in direction `i` fails to be
  differentiable) is an `Ω`-set whenever the graph of `h` is.

  The proof does not re-run the `ε`-`δ` construction: the derivative set of the fibre is
  already available, in the `Plumb` part of the workspace, as

    `Sset n i h = {(x, c) | HasDerivAt (t ↦ h (update x i t)) c (x i)}  ⊆ ℝ^{n+1}`,

  which is an `Ω`-set by `Sset_omega_aux`.  Its projection to the first `n` coordinates is the
  differentiability locus of the fibre, so `fibBad h i` is the complement of a projection of an
  `Ω`-set: `S.proj` and `S.compl` do the rest.
-/
import Mathlib
import Submission.Work.WilG1.Cell.JunkDefs
import Submission.Work.WilG1.Plumb.DerivDefs
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG5.Basic
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Plumb.SsetCore
import Submission.Work.WilG1.Plumb.SsetMem
import Submission.Work.WilG1.Plumb.junkPartial_mem

namespace Work.WilG1.Cell.Junk

/-- An explicit point `(x, c)` of `ℝ^{n+2}` lies in the derivative set `Sset (n+1) i f` exactly
when the one-variable fibre `t ↦ f (i.insertNth t (i.removeNth x))` has derivative `c` at `x i`. -/
theorem mem_Sset_snoc {k : ℕ} (i : Fin (k + 1)) (f : (Fin (k + 1) → ℝ) → ℝ)
    (x : Fin (k + 1) → ℝ) (c : ℝ) :
    Fin.snoc x c ∈ Work.WilG1.Plumb.Sset (k + 1) i f ↔
      HasDerivAt (fun t : ℝ => f (i.insertNth t (i.removeNth x))) c (x i) := by
  rw [Work.WilG1.Plumb.Sset_char (n := k) i f]
  simp only [Set.mem_ofPred_eq]
  rw [Fin.init_snoc, Fin.snoc_last]
  exact Work.WilG1.Plumb.hasDerivAt_iff_epsDeriv.symm

/-- The projection of the derivative set `Sset (n+1) i f` (dropping the derivative value) is
the set of parameters at which the fibre in direction `i` is differentiable. -/
theorem mem_projLast_Sset_iff {k : ℕ} (i : Fin (k + 1)) (f : (Fin (k + 1) → ℝ) → ℝ)
    (x : Fin (k + 1) → ℝ) :
    x ∈ WilkiesDesign.projLast (Work.WilG1.Plumb.Sset (k + 1) i f) ↔
      DifferentiableAt ℝ (fibreMap f i x) (x i) := by
  simp only [WilkiesDesign.projLast, Set.mem_ofPred_eq]
  have hiff : (∃ t : ℝ, Fin.snoc x t ∈ Work.WilG1.Plumb.Sset (k + 1) i f) ↔
      (∃ t : ℝ, HasDerivAt (fun s : ℝ => f (i.insertNth s (i.removeNth x))) t (x i)) :=
    exists_congr fun t => mem_Sset_snoc i f x t
  rw [hiff]
  have hg : (fun s : ℝ => f (i.insertNth s (i.removeNth x))) = fibreMap f i x := by
    funext s
    show f (i.insertNth s (i.removeNth x)) = f (Function.update x i s)
    rw [Fin.insertNth_removeNth]
  rw [hg]
  exact Work.WilG1.Plumb.exists_hasDerivAt_iff

theorem fibBad_mem (S : WilkiesDesign.SOMin) {n F D : ℕ} (h : (Fin n → ℝ) → ℝ)
    (hh : WilkiesDesign.graphOf h ∈ S.Ω F D (n + 1)) (i : Fin n) :
    ∃ (a : ℕ) (b : Polynomial ℕ), fibBad h i ∈ S.Ω a (b.eval D) n := by
  rcases n with _ | k
  · exact i.elim0
  · obtain ⟨a, b, hS⟩ :=
      Work.WilG1.Plumb.Sset_omega_aux (S := S) (N := k + 1) (f := h) i hh
    refine ⟨a + 1 + 1, b, ?_⟩
    have hset : fibBad h i =
        (WilkiesDesign.projLast (Work.WilG1.Plumb.Sset (k + 1) i h))ᶜ := by
      ext x
      simp only [fibBad, Set.mem_ofPred_eq, Set.mem_compl_iff]
      rw [mem_projLast_Sset_iff]
    rw [hset]
    exact S.compl (S.proj hS)

end Work.WilG1.Cell.Junk
