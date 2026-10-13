/-
  WilG4a : the affine-combination lemma (BNZ §5.1, the `n = 1` base case).

  If the graphs of `lo` and `hi` are `Ω`-definable with format `F` and degree `D`, then so is
  the graph of any affine combination `l ↦ c₁ + c₂ * lo l + c₃ * hi l`, with a format
  depending only on `F` and `p` and a degree bounded by a polynomial in `D` and `r`.

  The construction (see `Submission.Work.WilG4a.affine_comb_defs`) works in `ℝ^{p+3}` with
  coordinates `(x, y, u, v)`: `x` are the `p` parameters, `y` the output, `u` a copy of `lo x`
  and `v` a copy of `hi x`.  The three sets

  * `SA p (graphOf lo) = {z | (parameters, z (uIdx p)) ∈ graphOf lo}`,
  * `SB p (graphOf hi) = {z | (parameters, z (vIdx p)) ∈ graphOf hi}`,
  * `Seq p c₁ c₂ c₃ = {z | z (yIdx p) = c₁ + c₂ * z (uIdx p) + c₃ * z (vIdx p)}`

  are `Ω`-definable (two balanced reindexings `Work.WilG5.reindex_mem` and one hypersurface),
  and the projection `Work.WilG5.projN 2` of their intersection along the last two
  coordinates is exactly the graph of the affine combination.
-/
import Mathlib
import Submission.Work.WilG4a.affine_comb_defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
open WilkiesDesign

namespace Work.WilG4a

theorem affine_comb_graph_mem (S : WilkiesDesign.SOMin) (p : ℕ) (F : ℕ) : ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D r : ℕ) {lo hi : (Fin p → ℝ) → ℝ}, WilkiesDesign.graphOf lo ∈ S.Ω F D (p + 1) → WilkiesDesign.graphOf hi ∈ S.Ω F D (p + 1) → ∀ (c₁ c₂ c₃ : ℝ), WilkiesDesign.graphOf (fun l => c₁ + c₂ * lo l + c₃ * hi l) ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1) := by
  refine ⟨omegaFmt p F + 4, bpoly p, ?_⟩
  intro D r lo hi hlo hhi c₁ c₂ c₃
  -- the two reindexed graph pieces and the affine relation set are `Ω`-definable
  have hSA : SA p (graphOf lo) ∈ S.Ω (omegaFmt p F) (omegaDeg p D) (p+3) := SA_mem hlo
  have hSB : SB p (graphOf hi) ∈ S.Ω (omegaFmt p F) (omegaDeg p D) (p+3) := SB_mem hhi
  have hSeq : Seq p c₁ c₂ c₃ ∈ S.Ω (omegaFmt p F) 1 (p+3) := Seq_mem (S := S) p F c₁ c₂ c₃
  have hSeq' : Seq p c₁ c₂ c₃ ∈ S.Ω (omegaFmt p F + 1) 1 (p+3) :=
    Work.WilG5.mem_mono hSeq (omegaFmt p F + 1) 1 (by omega) le_rfl
  -- combine them and project the last two coordinates away
  have hInter : SA p (graphOf lo) ∩ SB p (graphOf hi) ∩ Seq p c₁ c₂ c₃ ∈
      S.Ω (omegaFmt p F + 2) (omegaDeg p D + omegaDeg p D + 1) (p+3) :=
    inter_mem (inter_mem hSA hSB) hSeq'
  have hProj : Work.WilG5.projN (n := p+1) 2
      (SA p (graphOf lo) ∩ SB p (graphOf hi) ∩ Seq p c₁ c₂ c₃) ∈
      S.Ω (omegaFmt p F + 4) (omegaDeg p D + omegaDeg p D + 1) (p+1) := by
    have h := Work.WilG5.projN_mem (S := S) (n := p+1) 2 (omegaFmt p F + 2)
      (omegaDeg p D + omegaDeg p D + 1) hInter
    exact Work.WilG5.mem_mono h (omegaFmt p F + 4) _ (by omega) le_rfl
  -- identify the constructed set with the graph of the affine combination
  have hSeqset : Seq p c₁ c₂ c₃ =
      {z : Fin (p+3) → ℝ | z (yIdx p) = c₁ + c₂ * z (uIdx p) + c₃ * z (vIdx p)} := rfl
  rw [sa_char p lo, sb_char p hi, hSeqset, proj_comb_eq p lo hi c₁ c₂ c₃] at hProj
  rw [bpoly_eval]
  exact Work.WilG5.mem_mono hProj (omegaFmt p F + 4) (2 * D + (4 * (p + 3) + 9)) le_rfl
    (by simp only [omegaDeg]; omega)

end Work.WilG4a
