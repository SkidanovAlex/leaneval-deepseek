import Mathlib
import Submission.Work.WilE4.CAD.Decomp
import Submission.Work.WilE4.CAD.Level
import Submission.Work.WilE4.CAD.Ops
import Submission.Work.WilE4.CAD.Bounds
import Submission.Work.WilE4.CAD.BoundsClosed
import Submission.Work.WilE4.CAD.Size
import Submission.Work.WilE4.CAD.CadCells_covers
import Submission.Work.WilE4.CAD.CadCells_isUnionOf
import Submission.Work.WilE4.CAD.CellsUnion
import Submission.Work.WilE4.CAD.BasePreconnected
import Submission.Work.WilE4.CAD.Proj
import Submission.Work.WilE4.CAD.exists_projSeq
import Submission.Work.WilE4.CAD.FiberClosureDefs
import Submission.Work.WilE4.CAD.projSeq_unionCells
import Submission.Work.WilE4.CAD.famDeg_projSeq_le
import Submission.Work.WilE4.CAD.FiberClosureProjSet
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical
namespace Work.WilE4.CAD

open MvPolynomial Polynomial
open Work.WilE4 (rot spec tower)

variable {k m n : ℕ}

/-! ## The `hUn` input for the iterated projection -/

/-- Every cell of the decomposition at the final level of the iterated projection is contained in the
projection or disjoint from it.  For `j = 0` this is `CadCells_isUnionOf`; for `j ≥ 1` it follows
from the fact that the projection is a union of cells (`projSeq_unionCells`) and the laminarity of
the decomposition (`cell_subset_unionCells_or_disjoint`). -/
theorem projSeq_hUn (k j : ℕ) (Z : SAd (k+(j+1))) (H : List (MvPolynomial (Fin (k+(j+1))) ℝ))
    (hatoms : ∀ B ∈ Z.basics, ∀ P ∈ B.eqs ++ B.pos, P ∈ H) :
    ∀ C ∈ CadCells (k+1) (projSeq k j (Z,H)).2,
      C.set ⊆ (projSeq k j (Z,H)).1.set ∨ Disjoint C.set (projSeq k j (Z,H)).1.set := by
  match j with
  | 0 =>
    intro C hC
    exact CadCells_isUnionOf H Z hatoms C hC
  | (j+1) =>
    intro C hC
    obtain ⟨L, hL, hZ1⟩ := projSeq_unionCells k j Z H hatoms
    rw [hZ1]
    exact cell_subset_unionCells_or_disjoint (projSeq k (j+1) (Z,H)).2 L hL C hC

/-! ## Closure of the family at the final level -/

/-- Once at least one projection step has been taken, the family at the final level is
`projDataT (k+1)` applied to a family, hence `tower (projData ·) ++ [0]`, hence strongly closed. -/
theorem projSeq_closed_aux (k : ℕ) :
    ∀ (j : ℕ) (S : ProjState k j), 1 ≤ j →
      ∀ i : Fin (projSeq k j S).2.length,
        ∃ i' : Fin (projSeq k j S).2.length,
          (projSeq k j S).2.get i'
            = MvPolynomial.pderiv (Fin.last k) ((projSeq k j S).2.get i) := by
  intro j
  induction j with
  | zero => intro S h; exact absurd h (by omega)
  | succ m ih =>
    intro S _
    rw [projSeq_succ]
    rcases m with _ | m
    · exact projDataT_deriv_closed S.2
    · exact ih (downStep k (m+1) S) (by omega)

/-- Strong derivative closure of the family at the final level of the iterated projection. -/
theorem projSeq_closed (k j : ℕ) (Z : SAd (k+(j+1))) (H : List (MvPolynomial (Fin (k+(j+1))) ℝ))
    (hcl : ∀ i : Fin H.length, ∃ i' : Fin H.length,
      H.get i' = MvPolynomial.pderiv (Fin.last (k+j)) (H.get i)) :
    ∀ i : Fin (projSeq k j (Z,H)).2.length,
      ∃ i' : Fin (projSeq k j (Z,H)).2.length,
        (projSeq k j (Z,H)).2.get i' = MvPolynomial.pderiv (Fin.last k) ((projSeq k j (Z,H)).2.get i) := by
  rcases j with _ | j
  · simp only [projSeq_zero, Nat.add_zero] at hcl ⊢
    exact hcl
  · exact projSeq_closed_aux k (j+1) (Z, H) (by omega)

/-! ## Length of the decomposition of the projection data -/

/-- The number of cells at the base level of the last projection is bounded by `bCellLen`.  At
level `0` the decomposition is the single cell `ℝ⁰`; at level `m+1` the family is
`projDataT (m+1) H = tower (projData ·) ++ [0]`, so `CadCells_length_le_closed` applies. -/
theorem cadCells_length_projDataT_le (n : ℕ) (H : List (MvPolynomial (Fin (n+1)) ℝ)) :
    (CadCells n (projDataT n H)).length ≤ (bCellLen n).eval (famDeg (projDataT n H)) := by
  cases n with
  | zero => simp [CadCells, bCellLen]
  | succ m =>
    exact CadCells_length_le_closed m (projDataT (m+1) H) (projDataT_deriv_closed (m := m) H)

/-! ## The last coordinate of a `Fin.snoc` -/

theorem snoc_last_apply {n : ℕ} (x : Fin n → ℝ) (ε : ℝ) :
    ((Fin.snoc x ε : Fin (n+1) → ℝ)) (Fin.last n) = ε := by
  simp [Fin.snoc]

/-! ## The `ε`-coordinate survives the projection -/

/-- The specialisation of the variable `X_ℓ` (which does not involve the last variable) is the
constant polynomial `X_ℓ`. -/
theorem F_epsPoly (ℓ q : ℕ) :
    F (epsPoly ℓ (q+1)) = Polynomial.C (epsPoly ℓ q) := by
  have hrot : rot (ℓ+q+1) (⟨ℓ, by omega⟩ : Fin (ℓ+q+2))
      = Fin.succ (⟨ℓ, by omega⟩ : Fin (ℓ+q+1)) := by
    apply Fin.ext
    rw [rot_apply, Fin.val_add_one_of_lt (by simp only [Fin.lt_def, Fin.val_last]; omega),
      Fin.val_succ]
  show MvPolynomial.finSuccEquiv ℝ (ℓ+q+1)
      (MvPolynomial.rename (rot (ℓ+q+1)) (epsPoly ℓ (q+1))) = Polynomial.C (epsPoly ℓ q)
  simp only [epsPoly]
  rw [MvPolynomial.rename_X, hrot, MvPolynomial.finSuccEquiv_X_succ]

/-- The degree-`0` coefficient of the specialisation of the variable `X_ℓ` is again `X_ℓ`. -/
theorem F_epsPoly_coeff_zero (ℓ q : ℕ) :
    (F (epsPoly ℓ (q+1))).coeff 0 = epsPoly ℓ q := by
  rw [F_epsPoly]
  simp

/-- The variable `X_ℓ` is preserved by one step of the projection data, as long as it is not the
last variable. -/
theorem epsPoly_mem_projDataT (ℓ q : ℕ)
    (H : List (MvPolynomial (Fin (ℓ + (q + 2))) ℝ)) (hε : epsPoly ℓ (q+1) ∈ H) :
    epsPoly ℓ q ∈ projDataT (ℓ + q + 1) H := by
  have hmem : epsPoly ℓ q ∈ projData H := by
    rw [projData]
    refine List.mem_append_left _ (List.mem_append_left _ ?_)
    rw [← F_epsPoly_coeff_zero ℓ q]
    exact coeffFam_mem hε (Nat.zero_le _)
  show epsPoly ℓ q ∈ tower (projData H) ++ [(0 : MvPolynomial (Fin (ℓ + q + 1)) ℝ)]
  exact List.mem_append_left _
    (List.mem_flatMap.mpr ⟨epsPoly ℓ q, hmem,
      List.mem_map.mpr ⟨0, List.mem_range.mpr (Nat.succ_pos _), rfl⟩⟩)

/-- `epsPoly ℓ 0 = epsBase ℓ`. -/
theorem epsPoly_zero_eq_epsBase (ℓ : ℕ) : epsPoly ℓ 0 = epsBase ℓ :=
  congrArg MvPolynomial.X (Fin.ext rfl)

/-- The `ε`-coordinate propagates down the iterated projection. -/
theorem epsPoly_mem_projSeq (ℓ q : ℕ) (Z : SAd (ℓ+(q+1)))
    (H : List (MvPolynomial (Fin (ℓ+(q+1))) ℝ)) (hε : epsPoly ℓ q ∈ H) :
    epsBase ℓ ∈ (projSeq ℓ q (Z,H)).2 := by
  induction q with
  | zero =>
    simpa [projSeq_zero, epsPoly_zero_eq_epsBase] using hε
  | succ q ih =>
    rw [projSeq_succ]
    exact ih (downStep ℓ q (Z,H)).1 (downStep ℓ q (Z,H)).2
      (epsPoly_mem_projDataT ℓ q H hε)

/-! ## The auxiliary statement, for an arbitrary top family -/

/-- The `∀ε>0 ∃y'` step of the fibrewise closure for an arbitrary top family `H` containing the
`ε`-coordinate: the projection out of the `y'`-block, the complement, the intersection with
`{ε > 0}`, the projection out of `ε` and the complement again. -/
theorem fiberClosure_aux (ℓ q : ℕ) (Z : SAd (ℓ+(q+1)))
    (H : List (MvPolynomial (Fin (ℓ+(q+1))) ℝ))
    (hcl : ∀ i : Fin H.length, ∃ i' : Fin H.length,
      H.get i' = MvPolynomial.pderiv (Fin.last (ℓ+q)) (H.get i))
    (hε : epsPoly ℓ q ∈ H)
    (hatoms : ∀ B ∈ Z.basics, ∀ P ∈ B.eqs ++ B.pos, P ∈ H) :
    ∃ Y : SAd ℓ,
      Y.set = {x : Fin ℓ → ℝ | ∀ ε : ℝ, 0 < ε → ∃ y' : Fin q → ℝ,
        Fin.append x (Fin.cons ε y') ∈ Z.set} ∧
      Y.deg ≤ (fiberClosureBound ℓ q).eval (famDeg H) := by
  -- the iterated projection removing the `y'` block
  let Z₁ : SAd (ℓ+1) := (projSeq ℓ q (Z, H)).1
  let Gq : List (MvPolynomial (Fin (ℓ+1)) ℝ) := (projSeq ℓ q (Z, H)).2
  have hZ1set : Z₁.set = {w : Fin (ℓ+1) → ℝ | ∃ y' : Fin q → ℝ, extend ℓ q w y' ∈ Z.set} :=
    projSeq_set_apply ℓ q Z H hcl hatoms
  have hUn1 : ∀ C ∈ CadCells (ℓ+1) Gq, C.set ⊆ Z₁.set ∨ Disjoint C.set Z₁.set :=
    projSeq_hUn ℓ q Z H hatoms
  have hclGq : ∀ i : Fin Gq.length, ∃ i' : Fin Gq.length,
      Gq.get i' = MvPolynomial.pderiv (Fin.last ℓ) (Gq.get i) :=
    projSeq_closed ℓ q Z H hcl
  have hfamGq : famDeg Gq ≤ (PBiter q).eval (famDeg H) := famDeg_projSeq_le ℓ q Z H
  have hεGq : epsBase ℓ ∈ Gq := epsPoly_mem_projSeq ℓ q Z H hε
  -- the complement at level `ℓ+1`
  let Z₂ : SAd (ℓ+1) := complSAd Gq Z₁
  have hZ2set : Z₂.set = Z₁.setᶜ := complSAd_set Gq Z₁ (CadCells_covers Gq) hUn1
  have hUn2 : ∀ C ∈ CadCells (ℓ+1) Gq, C.set ⊆ Z₂.set ∨ Disjoint C.set Z₂.set := by
    intro C hC
    exact cell_subset_unionCells_or_disjoint Gq (complCells Gq Z₁)
      (fun D hD => (complCells_mem Gq Z₁ D hD).1) C hC
  -- the intersection with `ε > 0`
  let Z₃ : SAd (ℓ+1) := Z₂.interBasic ⟨[], [epsBase ℓ]⟩
  have hZ3set : Z₃.set = Z₂.set ∩ {z : Fin (ℓ+1) → ℝ | 0 < z (Fin.last ℓ)} := by
    show (Z₂.interBasic ⟨[], [epsBase ℓ]⟩).set = Z₂.set ∩ _
    rw [SAd.interBasic_set]
    congr 1
    ext z
    simp [BasicD.set, BasicD.Holds, epsBase]
  have hεpos : ∀ C ∈ CadCells (ℓ+1) Gq,
      C.set ⊆ {z : Fin (ℓ+1) → ℝ | 0 < z (Fin.last ℓ)} ∨
        Disjoint C.set {z : Fin (ℓ+1) → ℝ | 0 < z (Fin.last ℓ)} := by
    intro C hC
    obtain ⟨v, hv⟩ := exists_signCond_of_mem_CadCells (ℓ+1) Gq hC
    obtain ⟨i, hi⟩ := List.get_of_mem hεGq
    have hsi : ∀ z ∈ C.set,
        SignType.sign (z (Fin.last ℓ)) = v i := by
      intro z hz
      have h := hv hz i
      rw [hi] at h
      simpa only [epsBase, MvPolynomial.eval_X] using h
    by_cases hvi : v i = 1
    · left
      intro z hz
      exact sign_eq_one_iff.mp ((hsi z hz).trans hvi)
    · right
      rw [Set.disjoint_left]
      intro z hz hzpos
      exact hvi (by rw [← hsi z hz, sign_pos hzpos])
  have hUn3 : ∀ C ∈ CadCells (ℓ+1) Gq, C.set ⊆ Z₃.set ∨ Disjoint C.set Z₃.set := by
    intro C hC
    rcases hUn2 C hC with hsub | hdis
    · rcases hεpos C hC with hpos | hdpos
      · left; rw [hZ3set]; intro z hz; exact ⟨hsub hz, hpos hz⟩
      · right; rw [hZ3set, Set.disjoint_left]
        intro z hz hz3
        exact Set.disjoint_left.mp hdpos hz hz3.2
    · right; rw [hZ3set, Set.disjoint_left]
      intro z hz hz3
      exact Set.disjoint_left.mp hdis hz hz3.1
  -- the projection out of `ε`
  let H_Y : List (MvPolynomial (Fin ℓ) ℝ) := projDataT ℓ Gq
  let Z₄ : SAd ℓ := projSAd (k := ℓ) Gq Z₃
  have hZ4set : Z₄.set = WilkiesDesign.projLast Z₃.set :=
    projSAd_set Gq Z₃ (CadCells_covers (projDataT ℓ Gq)) hUn3
      (realizedOn_all_projDataT ℓ Gq hclGq)
  have hUn4 : ∀ C ∈ CadCells ℓ H_Y, C.set ⊆ Z₄.set ∨ Disjoint C.set Z₄.set := by
    intro C hC
    exact cell_subset_unionCells_or_disjoint H_Y (projCells Gq Z₃)
      (fun D hD => (projCells_mem Gq Z₃ D hD).1) C hC
  -- the final complement
  let Y : SAd ℓ := complSAd H_Y Z₄
  have hYset : Y.set = Z₄.setᶜ := complSAd_set H_Y Z₄ (CadCells_covers H_Y) hUn4
  refine ⟨Y, ?_, ?_⟩
  · rw [hYset, hZ4set]
    ext x
    simp only [Set.mem_compl_iff, WilkiesDesign.projLast, Set.mem_ofPred_eq, Set.mem_setOf_eq]
    constructor
    · intro hx ε hε
      have h1 : Fin.snoc x ε ∉ Z₃.set := fun h => hx ⟨ε, h⟩
      have hnu : Fin.snoc x ε ∉ Z₂.set := by
        intro hmem
        apply h1
        rw [hZ3set, Set.mem_inter_iff]
        refine ⟨hmem, ?_⟩
        show 0 < (Fin.snoc x ε : Fin (ℓ+1) → ℝ) (Fin.last ℓ)
        rw [snoc_last_apply]; exact hε
      have h2 : Fin.snoc x ε ∈ Z₁.set := by
        have h3 := hnu
        rw [hZ2set] at h3
        simpa only [Set.mem_compl_iff, not_not] using h3
      rw [hZ1set] at h2
      obtain ⟨y', hy'⟩ := h2
      exact ⟨y', by simpa only [extend_snoc_cons] using hy'⟩
    · intro hx ht
      obtain ⟨t, ht⟩ := ht
      have ht' := ht
      rw [hZ3set, Set.mem_inter_iff] at ht'
      obtain ⟨htZ2, htpos⟩ := ht'
      have htpos' : 0 < t := by
        have h := htpos
        simp only [Set.mem_ofPred_eq] at h
        rwa [snoc_last_apply] at h
      have hZ1not : Fin.snoc x t ∉ Z₁.set := by
        have h3 := htZ2
        rw [hZ2set] at h3
        simpa only [Set.mem_compl_iff] using h3
      rw [hZ1set] at hZ1not
      simp only [Set.mem_setOf_eq] at hZ1not
      obtain ⟨y', hy'⟩ := hx t htpos'
      exact hZ1not ⟨y', by simpa only [extend_snoc_cons] using hy'⟩
  · -- degree bound
    have hB : Y.deg ≤ (CadCells ℓ H_Y).length * (bCellDeg ℓ).eval (famDeg H_Y) :=
      complSAd_deg_le H_Y Z₄ (fun C hC => (CadCells_deg_basics_le ℓ H_Y C hC).1)
    have hlen : (CadCells ℓ H_Y).length ≤ (bCellLen ℓ).eval (famDeg H_Y) :=
      cadCells_length_projDataT_le ℓ Gq
    have hfamY : famDeg H_Y ≤ (EYbound q).eval (famDeg H) := by
      have h1 := famDeg_projDataT_le_bound (n := ℓ) Gq
      have hmono := polynomial_eval_mono projDataTBound hfamGq
      calc famDeg H_Y = famDeg (projDataT ℓ Gq) := rfl
        _ ≤ projDataTBound.eval (famDeg Gq) := h1
        _ ≤ projDataTBound.eval ((PBiter q).eval (famDeg H)) := hmono
        _ = (EYbound q).eval (famDeg H) := by rw [EYbound, Polynomial.eval_comp]
    have hmonoL := polynomial_eval_mono (bCellLen ℓ) hfamY
    have hmonoD := polynomial_eval_mono (bCellDeg ℓ) hfamY
    calc Y.deg
        ≤ (CadCells ℓ H_Y).length * (bCellDeg ℓ).eval (famDeg H_Y) := hB
      _ ≤ (bCellLen ℓ).eval ((EYbound q).eval (famDeg H))
            * (bCellDeg ℓ).eval ((EYbound q).eval (famDeg H)) :=
          Nat.mul_le_mul (hlen.trans hmonoL) hmonoD
      _ = (fiberClosureBound ℓ q).eval (famDeg H) := by
          rw [fiberClosureBound, Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_comp]

/-! ## The `ε`-membership, closure and atoms of the top family -/

theorem epsPoly_mem_topFam {ℓ q : ℕ} (H₀ : List (MvPolynomial (Fin (ℓ+(q+1))) ℝ)) :
    epsPoly ℓ q ∈ topFam H₀ := by
  rw [topFam]
  refine List.mem_append_left _ ?_
  rw [tower, List.mem_flatMap]
  exact ⟨epsPoly ℓ q, List.mem_cons_self,
    List.mem_map.mpr ⟨0, List.mem_range.mpr (Nat.succ_pos _), rfl⟩⟩

theorem topFam_closed {ℓ q : ℕ} (H₀ : List (MvPolynomial (Fin (ℓ+(q+1))) ℝ)) :
    ∀ i : Fin (topFam H₀).length, ∃ i' : Fin (topFam H₀).length,
      (topFam H₀).get i' = MvPolynomial.pderiv (Fin.last (ℓ+q)) ((topFam H₀).get i) := by
  have hdef : topFam H₀ = tower (epsPoly ℓ q :: H₀) ++ [(0 : MvPolynomial (Fin (ℓ+(q+1))) ℝ)] := rfl
  rw [hdef]
  intro i
  have hmem : (tower (epsPoly ℓ q :: H₀) ++ [(0 : MvPolynomial (Fin (ℓ+(q+1))) ℝ)]).get i
      ∈ tower (epsPoly ℓ q :: H₀) ++ [(0 : MvPolynomial (Fin (ℓ+(q+1))) ℝ)] := List.get_mem _ i
  rcases List.mem_append.mp hmem with hm | hm
  · rcases tower_deriv_closed (epsPoly ℓ q :: H₀) _ hm with h0 | hmem2
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp
        (List.mem_append_right _ (List.mem_singleton.mpr (rfl : (0 : MvPolynomial (Fin (ℓ+(q+1))) ℝ) = 0)))
      exact ⟨j, hj.trans h0.symm⟩
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp (List.mem_append_left _ hmem2)
      exact ⟨j, hj⟩
  · rw [List.mem_singleton] at hm
    exact ⟨i, by rw [hm]; simp⟩

theorem topFam_atoms {ℓ q : ℕ} (Z : SAd (ℓ+(q+1)))
    (H₀ : List (MvPolynomial (Fin (ℓ+(q+1))) ℝ))
    (hZ : ∀ B ∈ Z.basics, ∀ P ∈ B.eqs ++ B.pos, P ∈ H₀) :
    ∀ B ∈ Z.basics, ∀ P ∈ B.eqs ++ B.pos, P ∈ topFam H₀ := by
  intro B hB P hP
  rw [topFam]
  refine List.mem_append_left _ ?_
  rw [tower, List.mem_flatMap]
  exact ⟨P, List.mem_cons_of_mem _ (hZ B hB P hP),
    List.mem_map.mpr ⟨0, List.mem_range.mpr (Nat.succ_pos _), rfl⟩⟩

/-! ## The main theorem -/

/-- **The `∀ε>0 ∃y'` step of the fibrewise closure, with a polynomial degree bound.**

Given a semialgebraic set `Z ⊆ ℝ^{ℓ + q + 1}` in disjunctive normal form, presented in the
coordinates `(x, ε, y')` with `x : Fin ℓ`, `ε : Fin 1` and `y' : Fin q` (so that a point is
`Fin.append x (Fin.cons ε y')`), and a family `H₀` of polynomials containing all the atoms of `Z`,
there is a semialgebraic set `Y ⊆ ℝ^ℓ` in disjunctive normal form with

`Y = {x | ∀ ε > 0, ∃ y', (x, ε, y') ∈ Z}`

and whose degree is bounded by a fixed polynomial `B` in `famDeg H₀` depending only on `ℓ` and `q`.

This is the middle step of `E4_sa_fiber_closure`: instantiated at `ℓ = p + q`, `q = q`,
`Z = {((x,y),ε,y') : (x, y') ∈ X ∧ ε > 0 ∧ Σᵢ (y'ᵢ - yᵢ)² < ε²}`, it produces exactly the
`∀ε>0 ∃y'`-form of the fibrewise closure of `X` (`Work.WilE4.CAD.fiberClosure_eq_sq`), and the
degree bound composes with the (elementary) bound on the degree of `Z` in terms of `X.deg`.

Route.  Work with the family `H := tower (ε :: H₀) ++ [0]`, where `ε` is the coordinate of index
`ℓ` (a single variable): `H` contains `H₀` and `ε`, and is *strongly* closed under `pderiv` in the
last variable (every derivative of a member is a member; `0` is its own derivative), by
`tower_deriv_closed`.  (The coordinate `ε` must be *in* the family: the cell that straddles `ε = 0`
otherwise has no sign condition on `ε`, and the intersection with `{0 < ε}` would not be a union of
cells.  It propagates down the levels because `coeffFam` keeps the degree-`0` coefficient.)  The
cost of this enlargement is absorbed in `B` (a fixed polynomial depending only on `ℓ, q`).

* `Z₁ :=` the `q`-fold projection of `Z` removing the `y'`-block (the last `q` coordinates), by
  `projSAd` (`Ops.lean`) with the families `H`, `projDataT … H`, …; its set is
  `{(x,ε) | ∃y', (x,ε,y') ∈ Z}`.
* `Z₂ := complSAd … Z₁`, whose set is the complement (`complSAd_set`).
* `Z₃ := Z₂.interBasic ⟨[], [ε]⟩`, whose set is `{(x,ε) ∈ Z₂ | ε > 0}`.
* `Z₄ :=` the projection of `Z₃` removing `ε` (then the last coordinate), whose set is
  `{x | ∃ε>0, (x,ε) ∉ Z₁}`, again with `projSAd`.
* `Y := complSAd … Z₄`, whose set is `{x | ∀ε>0 ∃y', (x,ε,y') ∈ Z}`, as claimed.

The hypotheses of `projSAd_set` / `complSAd_set` at each stage: the covers come from
`CadCells_covers`; the type constancy from `syl_minor_type_const` (the `∀x ∈ C.set` form, obtained
as in `baseCell_type_const`) with `hpre` from `Work.WilE4.CAD.projDataT_base_preconnected`
(`BasePreconnected.lean`) and the strong closure of the family at each level from
`projDataT_deriv_closed`; and the "every cell is contained in the set or disjoint from it" input
`hUn` comes from `CadCells_isUnionOf` for the initial `Z₃` (whose atoms lie in `H`) and from
`Work.WilE4.CAD.cell_subset_unionCells_or_disjoint` (`CellsUnion.lean`) for the later stages (a
`projSAd` or `complSAd` is a `unionCells` of a sub-list of `CadCells`).

The degree bound is the composition of the per-level bounds: `projSAd_deg_le` and
`complSAd_deg_le` bound the degree by `(CadCells …).length` times the cell-degree bound, and
`CadCells_length_le_closed` (`BoundsClosed.lean`) plus `CadCells_deg_basics_le` turn these into
explicit polynomials in the size of the family at that level, which grows by `projDataTBound` at
each step (`famDeg_projDataT_le_bound`).  All constants are symbolic — no `decide`/`norm_num` on
polynomial bounds, and the bound is *not* expanded. -/
theorem exists_fiberClosure_step (ℓ q : ℕ) :
    ∃ B : Polynomial ℕ,
      ∀ (Z : SAd (ℓ + (q + 1))) (H₀ : List (MvPolynomial (Fin (ℓ + (q + 1))) ℝ)),
        (∀ B₀ ∈ Z.basics, ∀ P ∈ B₀.eqs ++ B₀.pos, P ∈ H₀) →
        ∃ Y : SAd ℓ,
          Y.set = {x : Fin ℓ → ℝ | ∀ ε : ℝ, 0 < ε → ∃ y' : Fin q → ℝ,
            Fin.append x (Fin.cons ε y') ∈ Z.set} ∧
          Y.deg ≤ B.eval (famDeg H₀) := by
  refine ⟨fiberClosureBoundTop ℓ q, fun Z H₀ hZ => ?_⟩
  obtain ⟨Y, hYset, hYdeg⟩ :=
    fiberClosure_aux ℓ q Z (topFam H₀) (topFam_closed H₀) (epsPoly_mem_topFam H₀)
      (topFam_atoms Z H₀ hZ)
  refine ⟨Y, hYset, ?_⟩
  refine hYdeg.trans ?_
  have hmono := polynomial_eval_mono (fiberClosureBound ℓ q) (famDeg_topFam_le (ℓ := ℓ) (q := q) H₀)
  rw [fiberClosureBoundTop, Polynomial.eval_comp]
  exact hmono

end Work.WilE4.CAD
