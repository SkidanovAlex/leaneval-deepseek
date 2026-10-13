/-
  WilE7: ambient locality for strata that are `Good` at the *absolute* split.

  ## The observation

  The frozen hypothesis `hE5` (`E5_strat`) produces, for a semi-Pfaffian set `X : SemiPf (p+q)`,
  a list of `Good` strata `S : Stratum p q`.  The predicate `Stratum.Good` is *fibrewise*: its
  third clause reads

  ```
  ∀ᶠ z' in 𝓝 z, projFirst p q z' = projFirst p q z →
      (∀ a, eaEval c (h a) z' = 0) → z' ∈ S.X.set
  ```

  i.e. the equations of the stratum vanish only at stratum points *with the same base point*.

  The previous sessions (S26 §11.3, E7main_DESIGN §4bis) needed the corresponding *ambient*
  statement

  ```
  hloc : ∀ᶠ z' in 𝓝 z, (∀ a, eaEval c (h a) z' = 0) → z' ∈ S.X.set                      (hloc)
  ```

  (called `hloc` / "ambient locality"), and obtained it only from *avoidance* hypotheses
  (`Work.WilE7.ambientLocality_of_strat`), which are not available on every base cell — the
  "bad cell" obstruction of `NOTES_S26_level_step.md` §10/§11 and `NOTES_S27_*` §1–§3.

  The point of this file is that the **same frozen `hE5` supplies `hloc` for free**, provided one
  stratifies `X` at the *absolute* split `(0, p+q)` instead of the fibrewise split `(p, q)`:
  `Stratum 0 K` and `Stratum p q` with `p + q = K` carry the *same data* (`X : SemiPf K`, `j`, and
  `h : Fin j → EAPoly K X.r`), and the only difference is which coordinates the fibre Jacobian and
  the third clause of `Good` range over.  At the absolute split the fibre over the unique point of
  `Fin 0 → ℝ` is *everything*, so the third clause has no base restriction at all and *is* `hloc`.

  Consequence (the reason this matters for the assembly): a stratum that is `Good` at the absolute
  split is locally *exactly* the zero set of its own equations, i.e. (given the rank clause) a
  genuine submanifold, and its *ambient* frontier (available from `hE6` via
  `Work.WilE7.E6closure`) catches the "escape" points at which the fibre count of a piece jumps --
  including the escapes through the *faces of the ambient cube*, which `NOTES_S27` §7 identified as
  uncuttable within the complexity budget (`2 (m+1)` face-cuts per stratum, and `m` is universally
  quantified in the target).
-/
import Mathlib
import Submission.Work.WilE7.Defs

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- **The third clause of `Good` at the absolute split is ambient locality.**

For a stratum `S : Stratum 0 K` that is `Good` (i.e. `Good` for the split `(0, K)`, whose fibre
over the unique point of `Fin 0 → ℝ` is all of `ℝ^K`), the third clause of `Good` says that near
every stratum point, every zero of the stratum's equations is a stratum point.  This is exactly the
`hloc` hypothesis consumed by `Work.WilE7.sheetAssembly` and `Work.WilE7.sheets_of_constCount`
(where it is stated for an arbitrary split `(p, q)`; this statement is *stronger*, since it drops
the condition `projFirst p q z' = projFirst p q z`). -/
theorem hloc_of_good_abs {K : ℕ} (S : WilkiesDesign.E.Stratum 0 K) (hG : S.Good) :
    ∀ z ∈ S.X.set, ∀ᶠ z' in 𝓝 z,
      (∀ a : Fin S.j, WilkiesDesign.E.eaEval S.X.c (S.h a) z' = 0) → z' ∈ S.X.set := by
  intro z hz
  have h3 := (hG z hz).2.2
  refine h3.mono fun z' hz' hzero => ?_
  exact hz' (Subsingleton.elim _ _) hzero

/-- The first clause of `Good` at any split: the equations of the stratum vanish on it. -/
theorem hzero_of_good {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (hG : S.Good) :
    ∀ z ∈ S.X.set, ∀ a : Fin S.j,
      WilkiesDesign.E.eaEval S.X.c (S.h a) z = 0 :=
  fun z hz => (hG z hz).1

/-- **A stratum with `hloc` is locally exactly the zero set of its equations.**

`Good` gives `S.X.set ⊆ {h = 0}` pointwise on `S.X.set`; `hloc` gives the converse locally at every
point of `S.X.set`.  Consequently such a stratum is locally a smooth (indeed, by the rank clause of
`Good`, an implicit-function-theorem) manifold. -/
theorem eventually_mem_iff_hzero {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (hG : S.Good)
    (hloc : ∀ z ∈ S.X.set, ∀ᶠ z' in 𝓝 z,
      (∀ a : Fin S.j, WilkiesDesign.E.eaEval S.X.c (S.h a) z' = 0) → z' ∈ S.X.set) :
    ∀ z ∈ S.X.set, ∀ᶠ z' in 𝓝 z,
      (z' ∈ S.X.set ↔ ∀ a : Fin S.j, WilkiesDesign.E.eaEval S.X.c (S.h a) z' = 0) := by
  intro z hz
  refine (hloc z hz).mono fun z' hz' => ⟨fun hmem => (hG z' hmem).1, hz'⟩

/-- **The full Jacobian of the equations has rank `S.j` (`S.h` is a submersion).**

`Good` gives that the *fibrewise* Jacobian — the last `q` columns — is a `S.j × q` matrix of rank
`S.j`.  Its columns are a subset of the columns of the full `S.j × (p+q)` Jacobian, and taking
subsets of columns cannot increase the rank, so the full Jacobian has rank at least `S.j`; the
reverse inequality is the row bound.  (When moreover `S.j = q`, as for the strata of a piece with
finite fibres — `Work.WilE7.strat_j_of_finite` — the fibrewise block is invertible and the full
Jacobian has rank `q`, i.e. `S.h` is a submersion.) -/
theorem rank_full_jacobian_eq {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (hGood : S.Good)
    {z : Fin (p + q) → ℝ} (hz : z ∈ S.X.set) :
    (Matrix.of fun (a : Fin S.j) (l : Fin (p + q)) =>
      WilkiesDesign.E.eaEval S.X.c (WilkiesDesign.E.eaD S.X.c l (S.h a)) z).rank = S.j := by
  classical
  set M : Matrix (Fin S.j) (Fin (p + q)) ℝ :=
    Matrix.of fun (a : Fin S.j) (l : Fin (p + q)) =>
      WilkiesDesign.E.eaEval S.X.c (WilkiesDesign.E.eaD S.X.c l (S.h a)) z with hM
  -- the fibrewise Jacobian is the submatrix given by the last `q` columns
  have hsub : (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
      WilkiesDesign.E.eaEval S.X.c (WilkiesDesign.E.eaD S.X.c (Fin.natAdd p l) (S.h a)) z)
      = M.submatrix id (Fin.natAdd p) := by
    ext a l; rfl
  have hrank : (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
      WilkiesDesign.E.eaEval S.X.c (WilkiesDesign.E.eaD S.X.c (Fin.natAdd p l) (S.h a)) z).rank
      = S.j := (hGood z hz).2.1
  refine le_antisymm (Matrix.rank_le_height M) ?_
  have h2 : (M.submatrix id (Fin.natAdd p)).rank ≤ M.rank := Matrix.rank_submatrix_le M _ _
  rw [← hsub, hrank] at h2
  exact h2

end Work.WilE7
