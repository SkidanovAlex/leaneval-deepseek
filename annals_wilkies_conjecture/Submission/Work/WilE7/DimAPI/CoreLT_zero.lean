/-
  WilE7 / DimAPI — `CoreLT_zero`: the base case `K = 0` of the inner (lexicographic) induction.

  At `K = 0` the measure `NullDimLT · 0` says that the base projection `π_n (X i)` of every member
  of the `X`-family is empty, so the `X`-compatibility requirement is vacuous and the only
  constraint on the level-`(n+1)` decomposition is compatibility with the *base* family `Y`.
  That is supplied by the induction hypothesis `Core n` applied to `Y`: it produces a cylindrical
  decomposition `C'` of `cubeC n` whose cells are `*`-pieces with a uniform format and degree
  bound and are compatible with the base projections `π_n (Y i)`.

  Lifting `C'` to `cubeC (n+1)` is the only remaining step.  Each cell `γ ∈ C'` is lifted to the
  three cells of `ℝ^{n+1}` over it (the graphs at the levels `±1` and the open band `(-1,1)`) —
  the cells of `Work.WilE7.decomp_of_sections` over `γ` with no sections.  The union is
  `{Fin.init · ∈ γ ∧ |last ·| ≤ 1}`, so the lifted family is a cylindrical decomposition of
  `cubeC (n+1)` (`Work.WilE7.DimAPI.isCylDecompOn_liftFam`), its cardinality is at most thrice
  that of `C'`, and every lifted cell has `Fin.init`-image `γ`, which gives the compatibility with
  `Y`.

  Each lifted cell carries its own `*`-piece presentation, with format and degree controlled by
  those of the base piece:

  * the open band is `Work.WilE7.cylOpenBand` (the strict cylindrical lift `Work.WilE7.bandExt`);
  * the graphs at the levels `±1` are `Work.WilE7.DimAPI.cylFacePiece` (the pinned extension
    `Work.WilE7.FaceAux.insertCoord`);
  * the `SubPf` half comes with both.

  The format bound is `max Aband Aface` and the degree bound the sum of the two degree polynomials
  composed with the base degree polynomial `c₀`; the cardinality bound is `3 * b₀`, three cells per
  base cell.
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.DimAPI.LiftCells
import Submission.Work.WilE7.DimAPI.isCylDecompOn_liftFam
import Submission.Work.WilE7.DimAPI.cylFacePiece
import Submission.Work.WilE7.cylOpenBand
import Submission.Work.WilE7.cells

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.DimAPI
open WilkiesDesign WilkiesDesign.E

/-! ## Two elementary helpers -/

/-- A `*`-piece with a nonempty set has its base point in its semi-Pfaffian set. -/
theorem p_mem_of_nonempty {n : ℕ} (P : StarPiece n) (h : P.set.Nonempty) : P.p ∈ P.X.set := by
  by_contra hp
  have hcomp : connectedComponentIn P.X.set P.p = ∅ := connectedComponentIn_eq_empty hp
  have hset : P.set = ∅ := by
    simp only [WilkiesDesign.E.StarPiece.set, hcomp, Set.image_empty]
  exact h.ne_empty hset

/-- Evaluating a two-variable polynomial in which the pair `(D, k)` occupies the first two
positions and `l` the third is the evaluation of the corresponding two-variable polynomial at
`(D, l)`: the three-variable bound `b` of `CoreLT` is obtained from the two-variable bound `b₀` of
`Core` by `b := 3 * rename (0 ↦ 0, 1 ↦ 2) b₀`, and that multiplies the value by `3`. -/
theorem eval_lift3 (p : MvPolynomial (Fin 2) ℕ) (D k l : ℕ) :
    MvPolynomial.eval ![D, k, l]
        (MvPolynomial.C 3 * MvPolynomial.rename (![0, 2] : Fin 2 → Fin 3) p)
      = 3 * MvPolynomial.eval ![D, l] p := by
  have hcomp : ((![D, k, l] : Fin 3 → ℕ) ∘ (![0, 2] : Fin 2 → Fin 3)) = ![D, l] := by
    funext i
    fin_cases i <;> simp
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_rename, hcomp]

/-! ## The base case `K = 0` -/

theorem CoreLT_zero {n : ℕ} (h : Work.WilE7.Core n) : Work.WilE7.MainDesign.CoreLT n 0 := by
  intro F
  obtain ⟨a₀, b₀, c₀, hbase⟩ := h F
  obtain ⟨Aband, Cband, hband⟩ := Work.WilE7.cylOpenBand a₀
  obtain ⟨Aface, Cface, hface⟩ := cylFacePiece a₀
  refine ⟨max Aband Aface,
    MvPolynomial.C 3 * MvPolynomial.rename (![0, 2] : Fin 2 → Fin 3) b₀,
    Cband.comp c₀ + Cface.comp c₀, ?_⟩
  intro D k l m m' X Y hX hY hXnull
  -- `NullDimLT · 0` says that the base projection of `X i` is empty, hence `X i` itself is empty
  have hXempty : ∀ i, (X i).set = ∅ := by
    intro i
    by_contra hne
    obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hz' : MainDesign.basePr n m z ∈ MainDesign.basePr n m '' (X i).set := ⟨z, hz, rfl⟩
    have h0 : MainDesign.basePr n m '' (X i).set = ∅ := hXnull i
    rw [h0] at hz'
    exact hz'
  -- the base decomposition, supplied by `Core n` applied to the base family `Y`
  obtain ⟨C', hC'cyl, hC'compat, hC'card, hC'cell⟩ := hbase D l m' Y hY
  obtain ⟨hliftCyl, hliftCard, -⟩ := isCylDecompOn_liftFam hC'cyl
  refine ⟨liftFam n C', hliftCyl, ?_, ?_, ?_, ?_⟩
  · -- compatibility with the (empty) `X`-family
    intro i κ hκ
    refine Or.inr ?_
    rw [hXempty i, Set.image_empty]
    simp
  · -- compatibility with the base family `Y`, through the `Fin.init`-images
    intro i κ hκ
    obtain ⟨γ, hγ, hκγ⟩ := mem_liftFam.mp hκ
    have hγne : γ.Nonempty := Work.WilE7.isCylDecompOn_nonempty hC'cyl γ hγ
    rw [finInit_liftCells hγne hκγ]
    exact hC'compat i γ hγ
  · -- cardinality: three cells per base cell
    have h2 : C'.card ≤ MvPolynomial.eval ![D, l] b₀ := hC'card
    rw [eval_lift3 b₀ D k l]
    omega
  · -- the cells, with their `*`-piece presentations
    intro κ hκ
    obtain ⟨γ, hγ, hκγ⟩ := mem_liftFam.mp hκ
    obtain ⟨⟨P₀, hP₀set, hP₀fmt, hP₀deg⟩, hP₀sub⟩ := hC'cell γ hγ
    have hγne : γ.Nonempty := Work.WilE7.isCylDecompOn_nonempty hC'cyl γ hγ
    have hP₀ne : P₀.set.Nonempty := by rw [hP₀set]; exact hγne
    have hP₀p : P₀.p ∈ P₀.X.set := p_mem_of_nonempty P₀ hP₀ne
    rw [mem_liftCells] at hκγ
    rcases hκγ with hκ1 | hκ2 | hκ3
    · -- the graph at the level `-1`
      obtain ⟨⟨Q, hQset, hQfmt, hQdeg⟩, hQsub⟩ :=
        hface n P₀.m P₀.X P₀.p hP₀p γ hP₀set.symm hP₀sub (-1) (by norm_num) (c₀.eval D)
          hP₀fmt hP₀deg
      refine ⟨⟨Q, ?_, ?_, ?_⟩, ?_⟩
      · rw [hκ1]; exact hQset
      · exact le_trans hQfmt (le_max_right _ _)
      · rw [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_comp]
        exact le_trans hQdeg (le_add_of_nonneg_left (Nat.zero_le _))
      · rw [hκ1]; exact hQsub
    · -- the open band
      obtain ⟨⟨Q, hQset, hQfmt, hQdeg⟩, hQsub⟩ :=
        hband n P₀.m P₀.X P₀.p hP₀p γ hP₀set.symm hP₀sub (c₀.eval D) hP₀fmt hP₀deg
      refine ⟨⟨Q, ?_, ?_, ?_⟩, ?_⟩
      · rw [hκ2]; exact hQset
      · exact le_trans hQfmt (le_max_left _ _)
      · rw [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_comp]
        exact le_trans hQdeg (le_add_of_nonneg_right (Nat.zero_le _))
      · rw [hκ2]; exact hQsub
    · -- the graph at the level `1`
      obtain ⟨⟨Q, hQset, hQfmt, hQdeg⟩, hQsub⟩ :=
        hface n P₀.m P₀.X P₀.p hP₀p γ hP₀set.symm hP₀sub 1 (by norm_num) (c₀.eval D)
          hP₀fmt hP₀deg
      refine ⟨⟨Q, ?_, ?_, ?_⟩, ?_⟩
      · rw [hκ3]; exact hQset
      · exact le_trans hQfmt (le_max_right _ _)
      · rw [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_comp]
        exact le_trans hQdeg (le_add_of_nonneg_left (Nat.zero_le _))
      · rw [hκ3]; exact hQsub

end Work.WilE7.DimAPI
