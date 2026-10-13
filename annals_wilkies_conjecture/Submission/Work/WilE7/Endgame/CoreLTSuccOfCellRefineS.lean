/-
  E3 of the `CoreLT_succ` endgame design (`sources/wilkiesE7end/wilkies_e7_coreltsucc.md`):

    `CoreLT n K → CellRefineS n K → CoreLT n (K+1)`.

  Pure bookkeeping.  `CellRefineS n K` hands back an inner instance `(F', P, Nk, Nl, Ng)` together
  with the refinement: for every bound `(Fq, Qq)` on the presentations of the cells of the
  decomposition to be refined there are bounds `(AB, CB)`, so that for families `X'`, `Y'` of
  formats `≤ F'` and degrees `≤ P.eval D` (with `k'` and `l'` members, bounded by `Nk.eval ![D,k,l]`,
  `Nl.eval ![D,k,l]`) every compatible decomposition `B` is refined, base cell by base cell, with at
  most `Ng.eval ![D,k,l]` new cells per base cell (each a single `StarPiece` of format `≤ AB` and
  degree `≤ CB.eval D` — the `Fq`-dependence of `AB` is what repairs Defect 2 of the plan's
  `CellRefine`, see the header of `CellRefineS.lean`).  The level-`(n+1)` step therefore

  * calls `CoreLT n K` at format `F'` and degree bound `P.eval D` for the inner families `X'`, `Y'`,
    obtaining a decomposition `B` of `cubeC (n+1)` together with `StarPiece` presentations of its
    cells of format `≤ ai` and degree `≤ ci.eval (P.eval D)`,
  * refines `B` base cell by base cell via `CellRefineS` instantiated at `Fq := ai`,
    `Qq := ci.comp P`, and
  * glues the per-cell families with `DimAPI.cylDecomp_union_restricted`.

  Cardinality: `|C| ≤ |B| · (|B| + Ng.eval ![D,k,l])`, and `|B| ≤ bi.eval ![P.eval D, k', l']`
  with `k' ≤ Nk.eval ![D,k,l]`, `l' ≤ Nl.eval ![D,k,l]`; the resulting expression is realised by a
  three-variable polynomial `tb * (tb + Ng)` (`tb` = `bi` with the first variable substituted by
  `P.eval D` and the other two by `Nk`, `Nl`).  The outer format/degree bounds are
  `max ai AB` and `(ci.comp P) + CB`, dominating both the returned cells and the kept ones.
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.WilE7.DimAPI.cylDecomp_union_restricted
import Submission.Work.WilE7.poly_embed
import Submission.Work.WilE7.Endgame.CellRefineS

set_option autoImplicit false
noncomputable section
open Classical Filter Topology

namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt)

/-! ## Helper lemmas (polynomial bookkeeping and cell-decomposition surgery) -/

/-- Composition of variables in `MvPolynomial (Fin 3) ℕ`: evaluating `aeval ψ g` at `v` is
evaluating `g` at the three values `v · ψ`. -/
lemma eval_aeval3S {g : MvPolynomial (Fin 3) ℕ} {ψ : Fin 3 → MvPolynomial (Fin 3) ℕ}
    {v : Fin 3 → ℕ} :
    MvPolynomial.eval v (MvPolynomial.aeval ψ g)
      = MvPolynomial.eval (fun i => MvPolynomial.eval v (ψ i)) g := by
  rw [← MvPolynomial.aeval_eq_eval (f := v)]
  rw [← MvPolynomial.aeval_eq_eval (f := fun i => MvPolynomial.aeval v (ψ i))]
  exact MvPolynomial.comp_aeval_apply ψ (MvPolynomial.aeval v) g

/-- A one-variable polynomial embedded in the three-variable algebra, evaluated. -/
lemma eval_aeval_X_zero3S (q : Polynomial ℕ) (v : Fin 3 → ℕ) :
    MvPolynomial.eval v (Polynomial.aeval (MvPolynomial.X (0 : Fin 3)) q) = q.eval (v 0) := by
  have h := Polynomial.aeval_algHom_apply
      (f := (MvPolynomial.aeval v : MvPolynomial (Fin 3) ℕ →ₐ[ℕ] ℕ))
      (x := MvPolynomial.X (0 : Fin 3)) (p := q)
  simp only [MvPolynomial.aeval_X] at h
  rw [← MvPolynomial.aeval_eq_eval, ← h]
  rfl

/-- Evaluation of a polynomial with `ℕ` coefficients is monotone in the arguments. -/
lemma eval_mono3S (b : MvPolynomial (Fin 3) ℕ) {v w : Fin 3 → ℕ} (h : ∀ i, v i ≤ w i) :
    MvPolynomial.eval v b ≤ MvPolynomial.eval w b := by
  induction b using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add]; exact Nat.add_le_add hp hq
  | mul_X p i hp =>
      rw [map_mul, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X]
      exact Nat.mul_le_mul hp (h i)

/-- A nonempty cylindrical decomposition in dimension `m+1` has at least one cell. -/
lemma nonempty_of_isCylDecompOn_succS {m : ℕ} {A : Set (Fin (m + 1) → ℝ)}
    {C : Finset (Set (Fin (m + 1) → ℝ))} (h : IsCylDecompOn (m + 1) A C) (hA : A.Nonempty) :
    C.Nonempty := by
  obtain ⟨z, hz⟩ := hA
  have hz' : z ∈ ⋃₀ (C : Set (Set (Fin (m + 1) → ℝ))) := by rw [h.2.2.1]; exact hz
  obtain ⟨c, hc, -⟩ := Set.mem_sUnion.mp hz'
  exact ⟨c, hc⟩

theorem coreLT_succ_of_cellRefineS {n K : ℕ} (h : CoreLT n K) (hR : CellRefineS n K) :
    CoreLT n (K + 1) := by
  intro F
  obtain ⟨F', P, Nk, Nl, Ng, hbound⟩ := hR F
  obtain ⟨ai, bi, ci, hCore⟩ := h F'
  -- the produced-cell bounds, at the presentation bounds `ai`, `ci.comp P` supplied by the inner call
  obtain ⟨AB, CB, href⟩ := hbound ai (ci.comp P)
  -- the composite cardinality polynomial
  let ψ : Fin 3 → MvPolynomial (Fin 3) ℕ :=
    ![Polynomial.aeval (MvPolynomial.X (0 : Fin 3)) P, Nk, Nl]
  let tb : MvPolynomial (Fin 3) ℕ := MvPolynomial.aeval ψ bi
  refine ⟨max ai AB, tb * (tb + Ng), ci.comp P + CB, ?_⟩
  intro D k l m m' X Y hX hY hND
  -- the refinement of the inner instance
  obtain ⟨k', l', m₁, m₂, X', Y', hk', hl', hX', hY', hND', hYeq, hrefine⟩ :=
    href D k l m m' X Y hX hY hND
  -- the inner call
  obtain ⟨B, hBdec, hBX', hBY', hBcard, hBpiece⟩ :=
    hCore (P.eval D) k' l' m₁ m₂ X' Y' hX' hY' hND'
  let S : Finset (Set (Fin n → ℝ)) := B.image (fun κ => Fin.init '' κ)
  have hBbase : IsCylDecompOn n (Fin.init '' (cubeC (n + 1))) S := hBdec.2.2.2
  -- the presentations of `B`'s cells, which the inner call provides with the bounds `ai`, `ci ∘ P`
  have hcompD : (ci.comp P).eval D = ci.eval (P.eval D) := by rw [Polynomial.eval_comp]
  have hBp : ∀ κ ∈ B, (∃ P₀ : StarPiece (n + 1), P₀.set = κ ∧ P₀.X.fmt ≤ ai ∧
      P₀.X.deg ≤ (ci.comp P).eval D) ∧ SubPf (n + 1) κ := by
    intro κ hκ
    obtain ⟨⟨P₀, hset, hfmt, hdeg⟩, hsub⟩ := hBpiece κ hκ
    exact ⟨⟨P₀, hset, hfmt, by rw [hcompD]; exact hdeg⟩, hsub⟩
  -- the per-base-cell refined families
  let B'f : Set (Fin n → ℝ) → Finset (Set (Fin (n + 1) → ℝ)) :=
    fun b => dite (b ∈ S) (fun hb => Classical.choose (hrefine B hBdec hBX' hBY' hBp b hb))
      (fun _ => ∅)
  have hspec : ∀ b ∈ S, ((∀ κ ∈ B'f b, κ ∈ B) ∨
        ((∀ κ ∈ B'f b, (∃ P₀ : StarPiece (n + 1), P₀.set = κ ∧ P₀.X.fmt ≤ AB ∧
            P₀.X.deg ≤ CB.eval D) ∧ SubPf (n + 1) κ) ∧
          (B'f b).card ≤ MvPolynomial.eval ![D, k, l] Ng)) ∧
      IsCylDecompOn (n + 1) (cubeC (n + 1) ∩ {z | Fin.init z ∈ b}) (B'f b) ∧
      (∀ κ ∈ B'f b, Fin.init '' κ = b) ∧
      (∀ i, ∀ κ ∈ B'f b, κ ⊆ projFirst (n + 1) m '' (X i).set ∨
        Disjoint κ (projFirst (n + 1) m '' (X i).set)) := by
    intro b hb
    have h := Classical.choose_spec (hrefine B hBdec hBX' hBY' hBp b hb)
    have hval : B'f b = Classical.choose (hrefine B hBdec hBX' hBY' hBp b hb) := by
      dsimp only [B'f]
      exact dite_eq_left hb
    rwa [hval]
  -- nonemptiness (needed by the gluing lemma)
  have hne : ∀ b ∈ S, (B'f b).Nonempty := by
    intro b hb
    refine nonempty_of_isCylDecompOn_succS (hspec b hb).2.1 ?_
    obtain ⟨c, hcB, hcb⟩ := Finset.mem_image.mp hb
    obtain ⟨z, hz⟩ := (hBdec.1 c hcB).2
    refine ⟨z, ?_, ?_⟩
    · have hcov : (⋃₀ (B : Set (Set (Fin (n + 1) → ℝ)))) = cubeC (n + 1) := hBdec.2.2.1
      rw [← hcov]
      exact Set.mem_sUnion.mpr ⟨c, hcB, hz⟩
    · show Fin.init z ∈ b
      rw [← hcb]
      exact ⟨z, hz, rfl⟩
  -- containment in the cube (needed by the gluing lemma)
  have hsub : ∀ b ∈ S, ∀ κ ∈ B'f b, κ ⊆ cubeC (n + 1) := by
    intro b hb κ hκ
    have h1 : κ ⊆ ⋃₀ ((B'f b : Finset (Set (Fin (n + 1) → ℝ))) : Set (Set (Fin (n + 1) → ℝ))) :=
      Set.subset_sUnion_of_mem hκ
    rw [(hspec b hb).2.1.2.2.1] at h1
    exact fun z hz => (h1 hz).1
  have hproj : ∀ b ∈ S, ∀ κ ∈ B'f b, Fin.init '' κ = b := fun b hb => (hspec b hb).2.2.1
  have hB' : ∀ b ∈ S, IsCylDecompOn (n + 1) (cubeC (n + 1) ∩ {z | Fin.init z ∈ b}) (B'f b) :=
    fun b hb => (hspec b hb).2.1
  have hglue : IsCylDecompOn (n + 1) (cubeC (n + 1)) (S.biUnion B'f) :=
    Work.WilE7.DimAPI.cylDecomp_union_restricted (cubeC (n + 1)) S B'f hBbase hne hsub hproj hB'
  refine ⟨S.biUnion B'f, hglue, ?_, ?_, ?_, ?_⟩
  · -- compatibility with the outer `X`
    intro i κ hκ
    obtain ⟨b, hb, hκb⟩ := Finset.mem_biUnion.mp hκ
    exact (hspec b hb).2.2.2 i κ hκb
  · -- compatibility with the outer `Y`
    intro i κ hκ
    obtain ⟨b, hb, hκb⟩ := Finset.mem_biUnion.mp hκ
    obtain ⟨c, hcB, hcb⟩ := Finset.mem_image.mp hb
    obtain ⟨j', hj'⟩ := hYeq i
    have hinner := hBY' j' c hcB
    rw [hcb] at hinner
    have hκproj : Fin.init '' κ = b := (hspec b hb).2.2.1 κ hκb
    rw [hκproj, hj']
    exact hinner
  · -- the cardinality bound
    have hterm : ∀ b ∈ S, (B'f b).card ≤ B.card + MvPolynomial.eval ![D, k, l] Ng := by
      intro b hb
      rcases (hspec b hb).1 with hkeep | ⟨-, hcard⟩
      · exact le_trans (Finset.card_le_card (fun κ hκ => hkeep κ hκ)) (Nat.le_add_right _ _)
      · exact le_trans hcard (Nat.le_add_left _ _)
    have hmono := eval_mono3S bi (v := ![P.eval D, k', l'])
      (w := ![P.eval D, MvPolynomial.eval ![D, k, l] Nk, MvPolynomial.eval ![D, k, l] Nl]) (by
        intro i
        fin_cases i
        · simp
        · simpa using hk'
        · simpa using hl')
    have hBt : B.card ≤ MvPolynomial.eval
        ![P.eval D, MvPolynomial.eval ![D, k, l] Nk, MvPolynomial.eval ![D, k, l] Nl] bi :=
      le_trans hBcard hmono
    have htb : MvPolynomial.eval ![D, k, l] tb = MvPolynomial.eval
        ![P.eval D, MvPolynomial.eval ![D, k, l] Nk, MvPolynomial.eval ![D, k, l] Nl] bi := by
      have hfun : (fun i : Fin 3 => MvPolynomial.eval ![D, k, l] (ψ i)) =
          ![P.eval D, MvPolynomial.eval ![D, k, l] Nk, MvPolynomial.eval ![D, k, l] Nl] := by
        funext i
        fin_cases i <;> simp [ψ, eval_aeval_X_zero3S]
      simp only [tb]
      rw [eval_aeval3S, hfun]
    have hbOut : MvPolynomial.eval ![D, k, l] (tb * (tb + Ng)) = MvPolynomial.eval
        ![P.eval D, MvPolynomial.eval ![D, k, l] Nk, MvPolynomial.eval ![D, k, l] Nl] bi *
        (MvPolynomial.eval
          ![P.eval D, MvPolynomial.eval ![D, k, l] Nk, MvPolynomial.eval ![D, k, l] Nl] bi
          + MvPolynomial.eval ![D, k, l] Ng) := by
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_add, htb]
    calc (S.biUnion B'f).card
        ≤ ∑ b ∈ S, (B'f b).card := Finset.card_biUnion_le
      _ ≤ ∑ b ∈ S, (B.card + MvPolynomial.eval ![D, k, l] Ng) := Finset.sum_le_sum hterm
      _ = S.card * (B.card + MvPolynomial.eval ![D, k, l] Ng) := by
            rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
      _ ≤ B.card * (B.card + MvPolynomial.eval ![D, k, l] Ng) :=
            Nat.mul_le_mul_right _ Finset.card_image_le
      _ ≤ MvPolynomial.eval
            ![P.eval D, MvPolynomial.eval ![D, k, l] Nk, MvPolynomial.eval ![D, k, l] Nl] bi *
          (MvPolynomial.eval
            ![P.eval D, MvPolynomial.eval ![D, k, l] Nk, MvPolynomial.eval ![D, k, l] Nl] bi
            + MvPolynomial.eval ![D, k, l] Ng) :=
            Nat.mul_le_mul hBt (Nat.add_le_add_right hBt _)
      _ = MvPolynomial.eval ![D, k, l] (tb * (tb + Ng)) := hbOut.symm
  · -- the single-`StarPiece` presentations
    intro κ hκ
    obtain ⟨b, hb, hκb⟩ := Finset.mem_biUnion.mp hκ
    have hceval : (ci.comp P + CB).eval D = ci.eval (P.eval D) + CB.eval D := by
      rw [Polynomial.eval_add, Polynomial.eval_comp]
    rcases (hspec b hb).1 with hkeep | hnew
    · obtain ⟨⟨P0, hP0set, hP0fmt, hP0deg⟩, hP0sub⟩ := hBpiece κ (hkeep κ hκb)
      refine ⟨⟨P0, hP0set, ?_, ?_⟩, hP0sub⟩
      · exact le_trans hP0fmt (le_max_left _ _)
      · rw [hceval]
        exact le_trans hP0deg (Nat.le_add_right _ _)
    · obtain ⟨⟨P0, hP0set, hP0fmt, hP0deg⟩, hP0sub⟩ := hnew.1 κ hκb
      refine ⟨⟨P0, hP0set, ?_, ?_⟩, hP0sub⟩
      · exact le_trans hP0fmt (le_max_right _ _)
      · rw [hceval]
        exact le_trans hP0deg (Nat.le_add_left _ _)

end Work.WilE7.Endgame
