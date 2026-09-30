import Mathlib
import Submission.Work.BridgeSquare.subdivCell_two_apply
import Submission.Work.BridgeSquare.sum_chiSummand_eq_subtype
import Submission.Work.BridgeSquare.SlabBuild.Data
import Submission.Work.BridgeSquare.Psi1Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.BridgeSquare.WallCollar

open Convexity
open Work.Subdivision
open Work.MbarHomology

noncomputable section

/-! ## §1  Regrouping a sum by the value of the index map -/

/-- **Regrouping lemma.**  A sum of `ℤ`-multiples of the values of `X : β → M` can be grouped
by the value of the index map `g : ι → β`. -/
theorem sum_smul_regroup {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq β] {M : Type*}
    [AddCommMonoid M] [Module ℤ M]
    (g : ι → β) (c : ι → ℤ) (X : β → M) :
    (∑ j : ι, c j • X (g j))
      = ∑ l : β, (∑ j ∈ Finset.univ.filter (fun j => g j = l), c j) • X l := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := g)
    (f := fun j : ι => c j • X (g j))]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun j hj => by rw [(Finset.mem_filter.mp hj).2]

/-- **A sum all of whose coefficients vanish is zero.** -/
theorem sum_smul_eq_zero {β : Type*} [Fintype β] {M : Type*}
    [AddCommMonoid M] [Module ℤ M] (D : β → ℤ) (X : β → M) (h : ∀ l, D l = 0) :
    (∑ l : β, D l • X l) = 0 := by
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [h l, zero_smul]

/-! ## §2  The `(f,u)`-chains of a `2`-cell and the simplices they carry -/

/-- A strictly increasing triple. -/
theorem strictMono_vec3 {α : Type*} [Preorder α] {a b c : α} (hab : a < b) (hac : a < c)
    (hbc : b < c) : StrictMono ![a, b, c] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;>
    first
      | exact hab
      | exact hac
      | exact hbc
      | exact absurd hij (by decide)

/-- The `(f,u)`-chains `u ⋖ f ⋖ R` of a cell `R`: the index set of the `2`-simplices of the
barycentric subdivision of `R` supported on `R`. -/
abbrev PairIdx (R : QbarCW.Cell) : Type :=
  {p : QbarCW.Cell × QbarCW.Cell // p.1 ∈ QbarCW.facets R ∧ p.2 ∈ QbarCW.facets p.1}

instance (R : QbarCW.Cell) : Fintype (PairIdx R) :=
  inferInstanceAs (Fintype {p : QbarCW.Cell × QbarCW.Cell //
    p.1 ∈ QbarCW.facets R ∧ p.2 ∈ QbarCW.facets p.1})

/-- The `2`-simplex `u < f < R` carried by the chain `(f,u)`. -/
abbrev mkSimplex (R : QbarCW.Cell) (p : PairIdx R) : Simplex QbarCW.Cell 2 where
  toFun := ![p.1.2, p.1.1, R]
  strictMono := strictMono_vec3 (QbarCW.facet_lt p.2.2)
    (lt_trans (QbarCW.facet_lt p.2.2) (QbarCW.facet_lt p.2.1)) (QbarCW.facet_lt p.2.1)

theorem mkSimplex_apply_zero (R : QbarCW.Cell) (p : PairIdx R) :
    (mkSimplex R p) (0 : Fin 3) = p.1.2 := rfl

theorem mkSimplex_apply_one (R : QbarCW.Cell) (p : PairIdx R) :
    (mkSimplex R p) (1 : Fin 3) = p.1.1 := rfl

theorem mkSimplex_apply_last (R : QbarCW.Cell) (p : PairIdx R) :
    (mkSimplex R p) (Fin.last 2) = R := rfl

/-- **The `2`-simplices supported on a `2`-cell are the `(f,u)`-chains.** -/
theorem sum_subtype_last_eq_pairIdx {M : Type*} [AddCommMonoid M] (R : QbarCW.Cell)
    (hR : QbarCW.dim R = 2) (G : Simplex QbarCW.Cell 2 → M) :
    (∑ s : {s : Simplex QbarCW.Cell 2 // s (Fin.last 2) = R}, G s.1)
      = ∑ p : PairIdx R, G (mkSimplex R p) := by
  classical
  have hmem : ∀ (σ : Simplex QbarCW.Cell 2) (hσ : σ (Fin.last 2) = R),
      (σ 1) ∈ QbarCW.facets R ∧ (σ 0) ∈ QbarCW.facets (σ 1) := by
    intro σ hσ
    have hlt1 : σ 1 < R := by
      rw [← hσ]
      exact σ.strictMono (show (1 : Fin 3) < Fin.last 2 by decide)
    have h01 : QbarCW.dim (σ 0) < QbarCW.dim (σ 1) :=
      QbarCW.dim_lt' (σ.strictMono (show (0 : Fin 3) < 1 by decide))
    have h1R : QbarCW.dim (σ 1) < QbarCW.dim R := QbarCW.dim_lt' hlt1
    have hd1 : QbarCW.dim (σ 1) = 1 := by omega
    have hd0 : QbarCW.dim (σ 0) = 0 := by omega
    have hlt0 : σ 0 < σ 1 := σ.strictMono (show (0 : Fin 3) < 1 by decide)
    refine ⟨?_, ?_⟩
    · rw [QbarCW.mem_facets]
      exact ⟨hlt1, by rw [hR, hd1]⟩
    · rw [QbarCW.mem_facets]
      exact ⟨hlt0, by rw [hd1, hd0]⟩
  have hclass : ∀ (σ : Simplex QbarCW.Cell 2) (hσ : σ (Fin.last 2) = R),
      mkSimplex R (⟨(σ 1, σ 0), hmem σ hσ⟩ : PairIdx R) = σ := by
    intro σ hσ
    ext i
    fin_cases i
    · exact mkSimplex_apply_zero R _
    · exact mkSimplex_apply_one R _
    · show (mkSimplex R _) (Fin.last 2) = σ (Fin.last 2)
      exact (mkSimplex_apply_last R _).trans hσ.symm
  refine Finset.sum_bij' (fun s _ => (⟨(s.1 1, s.1 0), hmem s.1 s.2⟩ : PairIdx R))
    (fun p _ => (⟨mkSimplex R p, mkSimplex_apply_last R p⟩ :
      {s : Simplex QbarCW.Cell 2 // s (Fin.last 2) = R}))
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)
    (fun s _ => Subtype.ext (hclass s.1 s.2))
    (fun p _ => Subtype.ext (Prod.ext (mkSimplex_apply_one R p) (mkSimplex_apply_zero R p)))
    (fun s _ => by rw [hclass s.1 s.2])

/-! ## §3  `Ψ_M` of a `2`-cell, expanded in the subdivision -/

/-- **The expansion of `Ψ_M` of a `2`-cell of `Gen.mbarCx`** in the `(f,u)`-chains of its root
face. -/
theorem PsiM_rootCx_expand (e : Fin (Work.HomologyIso.Gen.mbarDim 2)) :
    (PsiM.f 2) (Pi.single e (1 : ℤ)) =
      ∑ p : PairIdx (Mbar.rootCx 2 e),
        (-(qInc (Mbar.rootCx 2 e).idx (p.1.1).idx) * qInc (p.1.1).idx (p.1.2).idx) •
          singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num) e
            (mkSimplex (Mbar.rootCx 2 e) p))) := by
  have hn : (2 : ℕ) < 5 := by norm_num
  rw [PsiM_f_piSingle_eq_sum 2 hn e, sum_chiSummand_eq_subtype 2 hn e]
  rw [sum_subtype_last_eq_pairIdx (Mbar.rootCx 2 e) (Mbar.rootCx_dim 2 e)
    (fun s => CellAtlas.rootCoeff Mbar.mbarAtlasOf 2 e s •
      singGen (Mbar.chi 2 (Mbar.rootSimplex 2 hn e s)))]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [subdivCell_two_apply, dif_pos (mkSimplex_apply_last (Mbar.rootCx 2 e) p),
    mkSimplex_apply_one, mkSimplex_apply_zero]

/-- **Scalar subtraction on affine chains.** -/
theorem smul_sub_aff (a b : ℤ) (X : AffC 1) : a • X - b • X = (a - b) • X := by
  ext y
  simp only [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, sub_mul]

/-- A sum over the `(f,u)`-chains of a `2`-cell, reindexed by an explicit bijection from `Fin 8`. -/
theorem sum_pairIdx_fin8' {M : Type*} [AddCommMonoid M] (R : QbarCW.Cell) (G : PairIdx R → M)
    (L : Fin 8 → PairIdx R) (hinj : Function.Injective L) (hsurj : Function.Surjective L) :
    ∑ p, G p = ∑ i, G (L i) :=
  (Fintype.sum_bijective L ⟨hinj, hsurj⟩ (fun i => G (L i)) G (fun _ => rfl)).symm

/-- **A difference of two `ℤ`-weighted sums over `AffC 1` is the sum of the differences.** -/
theorem sum_smul_sub_aff {β : Type*} [Fintype β] [DecidableEq β] (D D' : β → ℤ)
    (X : β → AffC 1) :
    (∑ l : β, D l • X l) - (∑ l : β, D' l • X l) = ∑ l : β, (D l - D' l) • X l := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun l _ => smul_sub_aff (D l) (D' l) (X l)

/-- **Equal coefficients give equal weighted sums (over `AffC 1`).** -/
theorem sum_smul_congr {β : Type*} [Fintype β] [DecidableEq β] (D D' : β → ℤ)
    (X : β → AffC 1) (h : ∀ l, D l = D' l) :
    (∑ l : β, D l • X l) = ∑ l : β, D' l • X l := by
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [h l]

/-- **The combination of the five pieces of the collar identity.** -/
theorem sum_smul_four {β : Type*} [Fintype β] [DecidableEq β] (A B C D E : β → ℤ)
    (X : β → AffC 1) (h : ∀ l, A l - B l = C l - (D l - E l)) :
    (∑ l, A l • X l) - (∑ l, B l • X l)
      = (∑ l, C l • X l) - ((∑ l, D l • X l) - (∑ l, E l • X l)) := by
  rw [sum_smul_sub_aff A B X, sum_smul_sub_aff D E X,
    sum_smul_sub_aff C (fun l => D l - E l) X]
  exact sum_smul_congr _ _ X h

end

end Work.BridgeSquare.WallCollar
