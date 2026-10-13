import Mathlib
import Submission.Work.WilE7.Endgame.E2Aux
import Submission.Work.WilE7.DecompDefs
import Submission.Work.CoreStep.projTop_graph_union_cyl
import Submission.Work.WilE7.coreLT_succ.SigmaCase

namespace Work.WilE7.Endgame

set_option autoImplicit false
open Classical Filter Topology
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt vertCoord)

/-! ## The graph of one sheet is inside the `π_{n+1}`-projection of the stratum

If the graph of a sheet `s` over the base cell `b` is contained in `absSet S` and `absSet S`
is contained in `absSet T`, then the *vertical* graph `{(x, vertCoord (s x)) | x ∈ b}` of the
last coordinate of `s` is contained in `projTopSet T = projTop '' absSet T`.

This is the "easy" direction of the description of `projTopSet T ∩ cyl b` as the union of the
sheet graphs: the preimage of a point of the graph is the point `Fin.append x (s x)` of the
stratum. -/
theorem E2_gr_subset_projTopSet {n m : ℕ} {b : Set (Fin n → ℝ)}
    {S T : WilkiesDesign.E.Stratum 0 (n + (m + 1))}
    (s : (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hsub : ∀ x : Fin n → ℝ, x ∈ b → Fin.append x (s x) ∈ Work.WilE7.MainDesign.absSet S)
    (hST : Work.WilE7.MainDesign.absSet S ⊆ Work.WilE7.MainDesign.absSet T) :
    Work.WilE7.gr b (fun x => (s x) (Fin.last m)) ⊆ Work.WilE7.CoreStep.projTopSet T := by
  intro y hy
  rw [Work.WilE7.gr, Set.mem_ofPred_eq] at hy
  obtain ⟨hyb, hylast⟩ := hy
  refine ⟨Fin.append (Fin.init y) (s (Fin.init y)), hST (hsub (Fin.init y) hyb), ?_⟩
  have hproj : projTop n m (Fin.append (Fin.init y) (s (Fin.init y)))
      = Fin.snoc (Fin.init y) (vertCoord (s (Fin.init y))) := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · rw [Work.WilE7.CoreStep.projTop_last, vertCoord, Fin.snoc_last]
      simp only [projSnd]
      rw [Fin.append_right]
    · intro i'
      rw [Work.WilE7.CoreStep.projTop_castSucc, Fin.snoc_castSucc]
      simp only [projFirst]
      rw [Fin.append_left]
  rw [hproj]
  rw [show vertCoord (s (Fin.init y)) = y (Fin.last n) from ?_]
  · exact Fin.snoc_init_self y
  · rw [vertCoord]; exact hylast.symm

/-- **E2, union compatibility.**

The cells of the level family `cfs b TT` are compatible with the `π_{n+1}`-projection `projTopSet T`
of a stratum `T` which, over the base cell `b`, is covered by strata `S t` whose sheet graphs are
the `s t j`: every cell is either contained in `projTopSet T` or disjoint from it.

The proof is a dichotomy.  A cell `κ` has `Fin.init '' κ = b`, so all its points have base in `b`.
If `κ` meets `projTopSet T` in a point `w`, then `w = projTop z` with `z ∈ absSet T` and
`projFirst z ∈ b`; by `hcovT` resp. `hcovS` the point `z` lies on the sheet graph of some `s t j`,
which exhibits `w` as a point of `gr b (fun x => (s t j x) (Fin.last m))`; by `hgr` the cell `κ`
is then contained in that graph, and `E2_gr_subset_projTopSet` (`hsub`, `hSsub`) puts the graph
inside `projTopSet T`.  If `κ` does not meet `projTopSet T`, the conclusion is disjointness. -/
theorem E2_union_compat {n m r K : ℕ} {b : Set (Fin n → ℝ)}
    {T : WilkiesDesign.E.Stratum 0 (n + (m + 1))}
    (S : Fin r → WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (k : Fin r → ℕ) (s : (t : Fin r) → Fin (k t) → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hsub : ∀ (t : Fin r) (j : Fin (k t)) (x : Fin n → ℝ), x ∈ b →
      Fin.append x (s t j x) ∈ Work.WilE7.MainDesign.absSet (S t))
    (hSsub : ∀ t : Fin r, Work.WilE7.MainDesign.absSet (S t) ⊆ Work.WilE7.MainDesign.absSet T)
    (hcovS : ∀ (t : Fin r), ∀ z ∈ Work.WilE7.MainDesign.absSet (S t),
      WilkiesDesign.E.projFirst n (m + 1) z ∈ b →
      ∃ j : Fin (k t), s t j (WilkiesDesign.E.projFirst n (m + 1) z) =
        WilkiesDesign.E.projSnd n (m + 1) z)
    (hcovT : ∀ z ∈ Work.WilE7.MainDesign.absSet T,
      WilkiesDesign.E.projFirst n (m + 1) z ∈ b →
      ∃ t : Fin r, z ∈ Work.WilE7.MainDesign.absSet (S t))
    (TT : Fin K → (Fin n → ℝ) → ℝ)
    (hgr : ∀ κ ∈ Work.WilE7.cfs b TT, ∀ (t : Fin r) (j : Fin (k t)),
      κ ⊆ Work.WilE7.gr b (fun x => (s t j x) (Fin.last m)) ∨
        Disjoint κ (Work.WilE7.gr b (fun x => (s t j x) (Fin.last m))))
    (hcell : ∀ κ ∈ Work.WilE7.cfs b TT, Fin.init '' κ = b) :
    ∀ κ ∈ Work.WilE7.cfs b TT,
      κ ⊆ Work.WilE7.CoreStep.projTopSet T ∨
        Disjoint κ (Work.WilE7.CoreStep.projTopSet T) := by
  intro κ hκ
  by_cases h : (κ ∩ Work.WilE7.CoreStep.projTopSet T).Nonempty
  · -- `κ` meets the projection: it is one of the sheet graphs of the family, hence inside it.
    left
    obtain ⟨w, hwκ, hwT⟩ := h
    rw [Work.WilE7.CoreStep.projTopSet, Set.mem_image] at hwT
    obtain ⟨z, hzT, hzw⟩ := hwT
    have hbw : Fin.init w ∈ b := by
      have hmem : Fin.init w ∈ Fin.init '' κ := ⟨w, hwκ, rfl⟩
      rwa [hcell κ hκ] at hmem
    have hb : projFirst n (m + 1) z ∈ b := by
      rw [← Work.WilE7.CoreStep.projTop_init n m z, hzw]; exact hbw
    obtain ⟨t, hzt⟩ := hcovT z hzT hb
    obtain ⟨j, hjs⟩ := hcovS t z hzt hb
    have hlastw : w (Fin.last n) = (s t j (Fin.init w)) (Fin.last m) := by
      rw [← hzw, Work.WilE7.CoreStep.projTop_last, Work.WilE7.CoreStep.projTop_init, hjs]
    have hwgr : w ∈ Work.WilE7.gr b (fun x => (s t j x) (Fin.last m)) := by
      rw [Work.WilE7.gr, Set.mem_ofPred_eq]
      exact ⟨hbw, hlastw⟩
    rcases hgr κ hκ t j with hsubgr | hdis
    · intro y hy
      exact E2_gr_subset_projTopSet (fun x => s t j x) (fun x hx => hsub t j x hx) (hSsub t)
        (hsubgr hy)
    · exact absurd hwgr (Set.disjoint_left.mp hdis hwκ)
  · -- `κ` misses the projection.
    right
    rw [Set.disjoint_iff_inter_eq_empty]
    exact Set.not_nonempty_iff_eq_empty.mp h

end Work.WilE7.Endgame
