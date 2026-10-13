/-
  Subproject WilE9G / Assembly — `ambCat` preserves the point set, the `Good` predicate, the
  degrees and the format (up to the gap `r₂` added by the adjoined chain).

  `ambCat S c₂` adjoins a chain `c₂` to the chain of `S`, so that the polynomials of *other*
  chains (in particular the weight `Φ_β · e^{c·(y,t)}` of a Lagrange stratum) become available in
  the ambient stratum, while the set, the `Good` predicate and the complexity bounds are untouched.

  The mathematical content is:

  * `SemiPf.unionSet` with an *empty* DNF has empty point set, so adjoining an unused chain to a
    semi-Pfaffian set does not change its set (`Work.WilE7.SubPfAux.unionSet_set`);
  * the evaluation of a polynomial of the old chain inside the concatenated chain is unchanged
    (`Work.WilE7.SubPfAux.eaEval_cat_inl`), and the matrix of Jacobian entries is unchanged —
    this is where the honest derivative enters: a Jacobian entry of the concatenated stratum is
    `(fderiv (eaEval (cat) (inl Q)) z) (single l 1)`, and the *function* whose derivative is taken
    is the same as before (`Work.WilE5.Strat.fderiv_eaEval_apply_single`);
  * the atom degree of a polynomial is preserved by the reindexing `EAPoly.inl`
    (`Work.WilE9.Ift.OneShot.atomDeg_inl`), whence `unionSet` adds degrees.
-/
import Mathlib
import Submission.Work.WilE9G.Assembly.Defs
import Submission.Work.WilE7.SubPfAux.unionSet_set
import Submission.Work.WilE5.Strat.flatConormalTools
import Submission.Work.WilE9.Ift.OneShot.oneShotSet_deg_le

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE9G.Assembly
open WilkiesDesign WilkiesDesign.E

/-! ## Elementary facts about the union of semi-Pfaffian sets -/

/-- A semi-Pfaffian set whose DNF is empty has empty point set. -/
theorem semiPf_set_empty_basics {k r : ℕ} (c : EAChain k r) :
    (⟨r, c, ([] : List (Basic k r))⟩ : SemiPf k).set = ∅ := by
  ext x
  simp [SemiPf.set]

/-- Concatenating the chains of two semi-Pfaffian sets adds their degrees: the reindexings
`EAPoly.inl`, `EAPoly.inr` preserve atom degrees. -/
theorem semiPf_deg_unionSet {k : ℕ} (X Y : SemiPf k) :
    (Work.WilE7.SemiPf.unionSet X Y).deg = X.deg + Y.deg := by
  have hX : (X.basics.map (Basic.deg ∘ (Work.WilE7.Basic.inl (r₂ := Y.r)))).sum
      = (X.basics.map Basic.deg).sum :=
    congrArg List.sum (List.map_congr_left (fun B _ => Work.WilE9.Ift.OneShot.basic_deg_inl B))
  have hY : (Y.basics.map (Basic.deg ∘ (Work.WilE7.Basic.inr (r₁ := X.r)))).sum
      = (Y.basics.map Basic.deg).sum :=
    congrArg List.sum (List.map_congr_left (fun C _ => Work.WilE9.Ift.OneShot.basic_deg_inr C))
  simp only [SemiPf.deg, Work.WilE7.SemiPf.unionSet, List.map_append, List.sum_append,
    List.map_map]
  rw [hX, hY]

/-- The format of a union of two semi-Pfaffian sets: the ambient dimension `k` is counted once
and the chain lengths add. -/
theorem semiPf_fmt_unionSet {k : ℕ} (X Y : SemiPf k) :
    (Work.WilE7.SemiPf.unionSet X Y).fmt = X.fmt + Y.r := by
  simp only [SemiPf.fmt, Work.WilE7.SemiPf.unionSet]
  omega

/-! ## The Jacobian entries of `ambCat` -/

/-- A Jacobian entry of the ambient stratum `ambCat S c₂` is the corresponding Jacobian entry of
`S`: both are the derivative of the *same* function `eaEval S.X.c (S.h a)` in the direction
`Pi.single l 1`, once the polynomials are read in the concatenated chain. -/
theorem ambCat_jac_entry {N r₂ : ℕ} (S : Work.WilE9G.AmbStratum N) (c₂ : EAChain N r₂)
    (z : Fin N → ℝ) (a : Fin S.j) (l : Fin N) :
    eaEval (Work.WilE7.EAChain.cat S.X.c c₂)
        (eaD (Work.WilE7.EAChain.cat S.X.c c₂) l (Work.WilE7.EAPoly.inl (S.h a))) z =
      eaEval S.X.c (eaD S.X.c l (S.h a)) z := by
  have hfun : (fun w : Fin N → ℝ =>
        eaEval (Work.WilE7.EAChain.cat S.X.c c₂) (Work.WilE7.EAPoly.inl (S.h a)) w)
      = (fun w : Fin N → ℝ => eaEval S.X.c (S.h a) w) := by
    funext w
    exact Work.WilE7.SubPfAux.eaEval_cat_inl S.X.c c₂ (S.h a) w
  rw [← Work.WilE5.Strat.fderiv_eaEval_apply_single (Work.WilE7.EAChain.cat S.X.c c₂)
        (Work.WilE7.EAPoly.inl (S.h a)) z l,
      ← Work.WilE5.Strat.fderiv_eaEval_apply_single S.X.c (S.h a) z l, hfun]

/-! ## The main statement -/

theorem ambCat_set_good_deg {N r₂ : ℕ} (S : Work.WilE9G.AmbStratum N)
    (c₂ : WilkiesDesign.E.EAChain N r₂) :
    (Work.WilE9G.Assembly.ambCat S c₂).X.set = S.X.set ∧
    ((Work.WilE9G.Assembly.ambCat S c₂).Good ↔ S.Good) ∧
    (Work.WilE9G.Assembly.ambCat S c₂).deg = S.deg ∧
    (Work.WilE9G.Assembly.ambCat S c₂).X.deg = S.X.deg ∧
    (Work.WilE9G.Assembly.ambCat S c₂).X.fmt = S.X.fmt + r₂ ∧
    (Work.WilE9G.Assembly.ambCat S c₂).X.basics.length = S.X.basics.length := by
  have hset : (ambCat S c₂).X.set = S.X.set := by
    show (Work.WilE7.SemiPf.unionSet S.X ⟨r₂, c₂, []⟩).set = S.X.set
    rw [Work.WilE7.SubPfAux.unionSet_set, semiPf_set_empty_basics c₂, Set.union_empty]
  have hXdeg : (ambCat S c₂).X.deg = S.X.deg :=
    (semiPf_deg_unionSet S.X (⟨r₂, c₂, []⟩ : SemiPf N)).trans (by simp [SemiPf.deg])
  refine ⟨hset, ?_, ?_, hXdeg, ?_, ?_⟩
  · constructor
    · intro h z hz
      have hz' : z ∈ (ambCat S c₂).X.set := by rw [hset]; exact hz
      have hh := h z hz'
      refine ⟨?_, ?_, ?_⟩
      · intro a
        exact (Work.WilE7.SubPfAux.eaEval_cat_inl S.X.c c₂ (S.h a) z).symm.trans (hh.1 a)
      · have hmat : (Matrix.of fun (a : Fin S.j) (l : Fin N) =>
            eaEval (Work.WilE7.EAChain.cat S.X.c c₂)
              (eaD (Work.WilE7.EAChain.cat S.X.c c₂) l (Work.WilE7.EAPoly.inl (S.h a))) z) =
            (Matrix.of fun (a : Fin S.j) (l : Fin N) =>
              eaEval S.X.c (eaD S.X.c l (S.h a)) z) := by
          ext a l
          exact ambCat_jac_entry S c₂ z a l
        have hmem : (Matrix.of fun (a : Fin S.j) (l : Fin N) =>
              eaEval (Work.WilE7.EAChain.cat S.X.c c₂)
                (eaD (Work.WilE7.EAChain.cat S.X.c c₂) l
                  (Work.WilE7.EAPoly.inl (S.h a))) z).rank = S.j := hh.2.1
        rw [hmat] at hmem
        exact hmem
      · refine hh.2.2.mono ?_
        intro z' hz'' h0
        rw [← hset]
        exact hz'' (fun a =>
          (Work.WilE7.SubPfAux.eaEval_cat_inl S.X.c c₂ (S.h a) z').trans (h0 a))
    · intro h z hz'
      have hz : z ∈ S.X.set := by rw [hset] at hz'; exact hz'
      have hh := h z hz
      refine ⟨?_, ?_, ?_⟩
      · intro a
        exact (Work.WilE7.SubPfAux.eaEval_cat_inl S.X.c c₂ (S.h a) z).trans (hh.1 a)
      · have hmat : (Matrix.of fun (a : Fin S.j) (l : Fin N) =>
            eaEval (Work.WilE7.EAChain.cat S.X.c c₂)
              (eaD (Work.WilE7.EAChain.cat S.X.c c₂) l (Work.WilE7.EAPoly.inl (S.h a))) z) =
            (Matrix.of fun (a : Fin S.j) (l : Fin N) =>
              eaEval S.X.c (eaD S.X.c l (S.h a)) z) := by
          ext a l
          exact ambCat_jac_entry S c₂ z a l
        have hmem : (Matrix.of fun (a : Fin S.j) (l : Fin N) =>
              eaEval S.X.c (eaD S.X.c l (S.h a)) z).rank = S.j := hh.2.1
        rw [← hmat] at hmem
        exact hmem
      · refine hh.2.2.mono ?_
        intro z' hz'' h0
        rw [hset]
        exact hz'' (fun a =>
          (Work.WilE7.SubPfAux.eaEval_cat_inl S.X.c c₂ (S.h a) z').symm.trans (h0 a))
  · show (Work.WilE7.SemiPf.unionSet S.X ⟨r₂, c₂, []⟩).deg +
        ∑ a : Fin S.j, atomDeg (Work.WilE7.EAPoly.inl (r₂ := r₂) (S.h a)) = S.deg
    have h1 : (Work.WilE7.SemiPf.unionSet S.X ⟨r₂, c₂, []⟩).deg = S.X.deg := hXdeg
    have h2 : (∑ a : Fin S.j, atomDeg (Work.WilE7.EAPoly.inl (r₂ := r₂) (S.h a)))
        = ∑ a : Fin S.j, atomDeg (S.h a) :=
      Finset.sum_congr rfl
        (fun a _ => Work.WilE9.Ift.OneShot.atomDeg_inl (r₂ := r₂) (S.h a))
    rw [h1, h2, Work.WilE9G.AmbStratum.deg]
  · show (Work.WilE7.SemiPf.unionSet S.X ⟨r₂, c₂, []⟩).fmt = S.X.fmt + r₂
    exact semiPf_fmt_unionSet S.X (⟨r₂, c₂, []⟩ : SemiPf N)
  · show (Work.WilE7.SemiPf.unionSet S.X ⟨r₂, c₂, []⟩).basics.length = S.X.basics.length
    simp [Work.WilE7.SemiPf.unionSet]

end Work.WilE9G.Assembly
