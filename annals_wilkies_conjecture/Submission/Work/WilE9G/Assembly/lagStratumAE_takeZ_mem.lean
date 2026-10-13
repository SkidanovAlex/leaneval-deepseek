import Mathlib
import Submission.Work.WilE9G.Assembly.Defs

namespace Work.WilE9G.Assembly

theorem lagStratumAE_takeZ_mem {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : WilkiesDesign.E.EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (w : Fin (n + (1 + (m + S.j + 1))) → ℝ)
    (hw : w ∈ (Work.WilE9G.Assembly.lagStratumAE S Phi c).X.set) :
    Work.WilE7.takeZ (by omega : n + (1 + m) ≤ n + (1 + (m + S.j + 1))) w ∈ S.X.set := by
  -- `w` satisfies one disjunct of `lagStratumAE`, i.e. there is a basic `B0` of `S` such that
  -- `w` satisfies `B0`'s conditions (padded) together with the Lagrange equations.
  rw [WilkiesDesign.E.SemiPf.set] at hw
  obtain ⟨hwc, B, hBmem, hBholds⟩ := hw
  simp only [lagStratumAE] at hBmem hBholds
  obtain ⟨B0, hB0mem, hBeq⟩ := List.mem_map.mp hBmem
  rw [← hBeq] at hBholds
  -- Every polynomial of `B0` occurs, padded, among the equations/inequalities of that disjunct, so
  -- evaluating it at `takeZ w` is the same as evaluating the padded polynomial at `w`.
  rw [WilkiesDesign.E.SemiPf.set]
  refine ⟨fun i => hwc (Fin.castLE (by omega) i), B0, hB0mem, ?_⟩
  obtain ⟨h1, h2⟩ := hBholds
  refine ⟨fun f hf => ?_, fun g hg => ?_⟩
  · have h := h1 (Work.WilE7.EAPoly.pad (by omega) f)
      (List.mem_append.mpr (Or.inr (List.mem_map_of_mem hf)))
    rw [← Work.WilE7.padAux.eaEval_pad (by omega) S.X.c f w]
    exact h
  · have h := h2 (Work.WilE7.EAPoly.pad (by omega) g)
      (List.mem_append.mpr (Or.inr (List.mem_map_of_mem hg)))
    rw [← Work.WilE7.padAux.eaEval_pad (by omega) S.X.c g w]
    exact h

end Work.WilE9G.Assembly
