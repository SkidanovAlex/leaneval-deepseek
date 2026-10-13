/-
  WilG4c / `FibClosureAux` — the explicit `Ω`-description of the fibre-wise closure of a set
  `Z ⊆ ℝ^{p+N}`, together with the coordinate plumbing and the set identity

    `aux Z = fibrewiseClosure Z`.

  ## The layout

  Work in the auxiliary space `ℝ^{p+N+1+N}` with coordinates `(w, ε, z')`: the point `w` in the
  first `p+N` slots, the radius `ε`, and the witness `z'` in the last `N` slots.  The pieces are

  * `pre Z` — the pullback `{(w,ε,z') | (l(w), z') ∈ Z}` along `iota`,
  * `sq`    — the strict polynomial condition `∑_j (z'_j - w_{p+j})² < ε²`,
  * `Inner Z = sq ∩ pre Z`,

  and then

    `aux Z = (projLast ( {ε > 0} ∩ (projLastIter_{N} (Inner Z))ᶜ ))ᶜ`.

  The universal quantifier over `ε` is `compl ∘ projLast ∘ compl`, and the existential over
  `z'` is `projLastIter ∘ compl` (negated).
-/
import Mathlib
import Submission.Work.WilG4c.FibreCoreDefs
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG0.Defs
import Submission.Work.WilG0.snocIt_castAdd
import Submission.Work.WilG0.snocIt_natAdd
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG0.projLastIter_mem
import Submission.Work.WilG1.Basic
import Submission.Work.WilG4a.CD.fibLimDefs
import Submission.Work.WilkiesH.Omega.omega_poly_lt

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilG4c.FibC

open WilkiesDesign

/-! ## 1. Coordinates of the auxiliary space `ℝ^{p+N+1+N} = (w, ε, z')` -/

/-- The index of the `i`-th parameter coordinate `l i` (`i : Fin p`). -/
def lIdx (p N : ℕ) (i : Fin p) : Fin (p + N + 1 + N) :=
  Fin.castAdd N (Fin.castAdd 1 (Fin.castAdd N i))

/-- The index of the `j`-th fibre coordinate `w (p+j)` of `w` (`j : Fin N`). -/
def zFibIdx (p N : ℕ) (j : Fin N) : Fin (p + N + 1 + N) :=
  Fin.castAdd N (Fin.castAdd 1 (Fin.natAdd p j))

/-- The index of the radius coordinate `ε`. -/
def eIdx (p N : ℕ) : Fin (p + N + 1 + N) :=
  Fin.castAdd N (Fin.last (p + N))

/-- The index of the `j`-th witness coordinate `z' j`. -/
def zIdx (p N : ℕ) (j : Fin N) : Fin (p + N + 1 + N) :=
  Fin.natAdd (p + N + 1) j

/-- The pullback index `(l, z') ↦ (l, zFib, ε, z')` for the `Ω`-set `Z`. -/
def iota (p N : ℕ) : Fin (p + N) → Fin (p + N + 1 + N) :=
  Fin.append (fun i : Fin p => lIdx p N i) (fun j : Fin N => zIdx p N j)

/-! ## 2. The pieces of the big set -/

/-- The pullback of `Z` along `iota`. -/
def pre (p N : ℕ) (Z : Set (Fin (p + N) → ℝ)) : Set (Fin (p + N + 1 + N) → ℝ) :=
  Work.WilG5.coordPre (iota p N) Z

/-- The strict condition `∑_j (z' j - w (p+j))² < ε²`. -/
def sq (p N : ℕ) : Set (Fin (p + N + 1 + N) → ℝ) :=
  {q | (∑ j : Fin N, (q (zIdx p N j) - q (zFibIdx p N j)) ^ 2) < (q (eIdx p N)) ^ 2}

/-- The polynomial `∑_j (Z'_j - W_{p+j})² - ε²`. -/
def sqPoly (p N : ℕ) : MvPolynomial (Fin (p + N + 1 + N)) ℝ :=
  (∑ j : Fin N,
      (MvPolynomial.X (zIdx p N j) - MvPolynomial.X (zFibIdx p N j)) ^ 2) -
    (MvPolynomial.X (eIdx p N)) ^ 2

/-- The big set `sq ∩ pre`. -/
def Inner (p N : ℕ) (Z : Set (Fin (p + N) → ℝ)) : Set (Fin (p + N + 1 + N) → ℝ) :=
  sq p N ∩ pre p N Z

/-- The middle radius condition `ε > 0`. -/
def posEps (p N : ℕ) : Set (Fin (p + N + 1) → ℝ) :=
  {q | 0 < q (Fin.last (p + N))}

/-- The explicit `Ω`-description of the fibre-wise closure. -/
def aux (p N : ℕ) (Z : Set (Fin (p + N) → ℝ)) : Set (Fin (p + N) → ℝ) :=
  (projLast (posEps p N ∩
    (Work.WilG0.projLastIter (p + N + 1) N (Inner p N Z))ᶜ))ᶜ

/-! ## 3. The Fin plumbing -/

theorem snocIt_eq_append (n m : ℕ) (x : Fin n → ℝ) (w : Fin m → ℝ) :
    Work.WilG0.snocIt n m x w = Fin.append x w := by
  funext i
  cases i using Fin.addCases with
  | left i' => rw [Work.WilG0.snocIt_castAdd, Fin.append_left]
  | right j => rw [Work.WilG0.snocIt_natAdd, Fin.append_right]

/-- `Fin.snoc x t` at the index `Fin.castAdd 1 i`. -/
theorem snoc_castAdd_one {n : ℕ} (x : Fin n → ℝ) (t : ℝ) (i : Fin n) :
    (Fin.snoc x t : Fin (n + 1) → ℝ) (Fin.castAdd 1 i) = x i := by
  rw [show (Fin.castAdd 1 i : Fin (n + 1)) = Fin.castSucc i from Fin.ext rfl,
    Fin.snoc_castSucc]

/-! ## 4. Reading the coordinates on the auxiliary point -/

/-- The defining property of the pullback index `iota`. -/
theorem comp_iota (p N : ℕ) (q : Fin (p + N + 1) → ℝ) (z' : Fin N → ℝ) :
    Work.WilG0.snocIt (p + N + 1) N q z' ∘ (iota p N) =
      Fin.append (fun i : Fin p => q (Fin.castAdd 1 (Fin.castAdd N i))) z' := by
  funext k
  cases k using Fin.addCases with
  | left i' =>
      simp only [Function.comp_apply, iota, lIdx, Fin.append_left,
        Work.WilG0.snocIt_castAdd]
  | right j =>
      simp only [Function.comp_apply, iota, zIdx, Fin.append_right,
        Work.WilG0.snocIt_natAdd]

/-- Reading the `sq` condition on the auxiliary point. -/
theorem mem_sq_iff (p N : ℕ) (q : Fin (p + N + 1) → ℝ) (z' : Fin N → ℝ) :
    Work.WilG0.snocIt (p + N + 1) N q z' ∈ sq p N ↔
      (∑ j : Fin N, (z' j - q (Fin.castAdd 1 (Fin.natAdd p j))) ^ 2) <
        (q (Fin.last (p + N))) ^ 2 := by
  have h1 : ∀ j : Fin N, Work.WilG0.snocIt (p + N + 1) N q z' (zIdx p N j) = z' j :=
    fun j => Work.WilG0.snocIt_natAdd (p + N + 1) N q z' j
  have h2 : ∀ j : Fin N,
      Work.WilG0.snocIt (p + N + 1) N q z' (zFibIdx p N j) =
        q (Fin.castAdd 1 (Fin.natAdd p j)) :=
    fun j => Work.WilG0.snocIt_castAdd (p + N + 1) N q z' (Fin.castAdd 1 (Fin.natAdd p j))
  have h3 : Work.WilG0.snocIt (p + N + 1) N q z' (eIdx p N) = q (Fin.last (p + N)) :=
    Work.WilG0.snocIt_castAdd (p + N + 1) N q z' (Fin.last (p + N))
  simp only [sq, Set.mem_ofPred_eq, h1, h2, h3]

/-- Reading the `pre` condition on the auxiliary point. -/
theorem mem_pre_iff (p N : ℕ) (Z : Set (Fin (p + N) → ℝ))
    (q : Fin (p + N + 1) → ℝ) (z' : Fin N → ℝ) :
    Work.WilG0.snocIt (p + N + 1) N q z' ∈ pre p N Z ↔
      Fin.append (fun i : Fin p => q (Fin.castAdd 1 (Fin.castAdd N i))) z' ∈ Z := by
  rw [pre, Work.WilG5.coordPre, Set.mem_ofPred_eq, comp_iota]

/-- The `sq` reading specialised to the outer projection point `Fin.snoc v ε`. -/
theorem snoc_sq_mem (p N : ℕ) (v : Fin (p + N) → ℝ) (ε : ℝ) (z' : Fin N → ℝ) :
    Work.WilG0.snocIt (p + N + 1) N (Fin.snoc v ε) z' ∈ sq p N ↔
      (∑ j : Fin N, (z' j - v (Fin.natAdd p j)) ^ 2) < ε ^ 2 := by
  rw [mem_sq_iff]
  simp only [snoc_castAdd_one, Fin.snoc_last]

/-- The `pre` reading specialised to the outer projection point `Fin.snoc v ε`. -/
theorem snoc_pre_mem (p N : ℕ) (Z : Set (Fin (p + N) → ℝ)) (v : Fin (p + N) → ℝ)
    (ε : ℝ) (z' : Fin N → ℝ) :
    Work.WilG0.snocIt (p + N + 1) N (Fin.snoc v ε) z' ∈ pre p N Z ↔
      Fin.append (fun i : Fin p => v (Fin.castAdd N i)) z' ∈ Z := by
  rw [mem_pre_iff]
  simp only [snoc_castAdd_one]

/-! ## 5. The set identity -/

/-- `aux Z` is the fibre-wise closure of `Z`. -/
theorem mem_aux_iff (p N : ℕ) (Z : Set (Fin (p + N) → ℝ)) (v : Fin (p + N) → ℝ) :
    v ∈ aux p N Z ↔
      ∀ ε : ℝ, 0 < ε → ∃ z' : Fin N → ℝ,
        (∑ j : Fin N, (z' j - v (Fin.natAdd p j)) ^ 2) < ε ^ 2 ∧
          Fin.append (fun i : Fin p => v (Fin.castAdd N i)) z' ∈ Z := by
  rw [aux, Set.mem_compl_iff, projLast]
  constructor
  · intro h ε hε
    have hmem : Fin.snoc v ε ∈ Work.WilG0.projLastIter (p + N + 1) N (Inner p N Z) := by
      by_contra hc
      exact h ⟨ε, by
        refine ⟨?_, hc⟩
        simpa [posEps] using hε⟩
    rw [Work.WilG0.projLastIter_eq] at hmem
    obtain ⟨z', hsq, hpre⟩ := hmem
    exact ⟨z', (snoc_sq_mem p N v ε z').mp hsq, (snoc_pre_mem p N Z v ε z').mp hpre⟩
  · intro h
    rintro ⟨t, ht⟩
    rw [Set.mem_inter_iff] at ht
    obtain ⟨hpos, hnotmem⟩ := ht
    rw [Set.mem_compl_iff, Work.WilG0.projLastIter_eq] at hnotmem
    obtain ⟨z', hsq, hpre⟩ := h t (by simpa [posEps] using hpos)
    exact hnotmem ⟨z', by
      exact ⟨(snoc_sq_mem p N v t z').mpr hsq, (snoc_pre_mem p N Z v t z').mpr hpre⟩⟩

/-- **The set identity:** `aux Z` is `fibrewiseClosure Z`. -/
theorem aux_eq (p N : ℕ) (Z : Set (Fin (p + N) → ℝ)) :
    aux p N Z = fibrewiseClosure Z := by
  ext v
  rw [mem_aux_iff]
  rfl

/-! ## 6. The polynomial -/

theorem sqPoly_eval (p N : ℕ) (q : Fin (p + N + 1 + N) → ℝ) :
    (sqPoly p N).eval q =
      (∑ j : Fin N, (q (zIdx p N j) - q (zFibIdx p N j)) ^ 2) - (q (eIdx p N)) ^ 2 := by
  simp only [sqPoly, MvPolynomial.eval_sub, MvPolynomial.eval_sum, MvPolynomial.eval_pow,
    MvPolynomial.eval_X]

theorem sqPoly_totalDegree_le (p N : ℕ) : (sqPoly p N).totalDegree ≤ 2 := by
  rw [sqPoly]
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  rw [max_le_iff]
  refine ⟨?_, ?_⟩
  · refine le_trans (MvPolynomial.totalDegree_finsetSum (Finset.univ)
      (fun j : Fin N => (MvPolynomial.X (zIdx p N j) - MvPolynomial.X (zFibIdx p N j)) ^ 2)) ?_
    rw [Finset.sup_le_iff]
    intro j _
    refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
    have h : (MvPolynomial.X (zIdx p N j) - MvPolynomial.X (zFibIdx p N j) :
        MvPolynomial (Fin (p + N + 1 + N)) ℝ).totalDegree ≤ 1 := by
      refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
      rw [max_le_iff]
      exact ⟨le_of_eq (MvPolynomial.totalDegree_X _),
        le_of_eq (MvPolynomial.totalDegree_X _)⟩
    omega
  · refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
    rw [MvPolynomial.totalDegree_X]

theorem sqPoly_zero (p N : ℕ) :
    {q : Fin (p + N + 1 + N) → ℝ | (sqPoly p N).eval q < 0} = sq p N := by
  ext q
  simp only [Set.mem_ofPred_eq, sqPoly_eval, sq]
  constructor <;> intro h <;> linarith

/-! ## 7. `Ω`-membership of `aux` -/

theorem aux_mem (S : WilkiesDesign.SOMin) (p N : ℕ) :
    ∃ K c : ℕ, ∀ (F D : ℕ) (Z : Set (Fin (p + N) → ℝ)), Z ∈ S.Ω F D (p + N) →
      aux p N Z ∈ S.Ω (F + K) (D + c) (p + N) := by
  refine ⟨64 * ((p + N + 1 + N) + (p + N)) + 64 + 1 + N + (p + N + 1) + 4,
    32 * ((p + N + 1 + N) + (p + N)) + 32 + 4 + 8, ?_⟩
  intro F D Z hZ
  have hPre : pre p N Z ∈ S.Ω (F + 64 * ((p + N + 1 + N) + (p + N)) + 64)
      (D + 32 * ((p + N + 1 + N) + (p + N)) + 32) (p + N + 1 + N) :=
    Work.WilG5.coordPre_mem (S := S) (m := p + N) (N := p + N + 1 + N)
      (F := F) (D := D) (ι := iota p N) (A := Z) hZ
  have hSq : sq p N ∈ S.Ω (p + N + 1 + N + 3) 4 (p + N + 1 + N) := by
    have h := Work.WilkiesH.Omega.omega_poly_lt S (p + N + 1 + N) (sqPoly p N)
    rw [sqPoly_zero] at h
    exact Work.WilG1.Omega.mono h le_rfl (by have := sqPoly_totalDegree_le p N; omega)
  have hSq' : sq p N ∈ S.Ω (F + 64 * ((p + N + 1 + N) + (p + N)) + 64) 4
      (p + N + 1 + N) :=
    Work.WilG1.Omega.mono hSq (by omega) le_rfl
  have hInner : Inner p N Z ∈ S.Ω ((F + 64 * ((p + N + 1 + N) + (p + N)) + 64) + 1)
      (4 + (D + 32 * ((p + N + 1 + N) + (p + N)) + 32)) (p + N + 1 + N) :=
    Work.WilG4a.CD.inter2_same (S := S) hSq' hPre
  have hProj : Work.WilG0.projLastIter (p + N + 1) N (Inner p N Z) ∈
      S.Ω (((F + 64 * ((p + N + 1 + N) + (p + N)) + 64) + 1) + N + (p + N + 1))
        (4 + (D + 32 * ((p + N + 1 + N) + (p + N)) + 32)) (p + N + 1) :=
    Work.WilG0.projLastIter_mem S (p + N + 1) N _ _ _ hInner
  have hProjC : (Work.WilG0.projLastIter (p + N + 1) N (Inner p N Z))ᶜ ∈
      S.Ω ((((F + 64 * ((p + N + 1 + N) + (p + N)) + 64) + 1) + N + (p + N + 1)) + 1)
        (4 + (D + 32 * ((p + N + 1 + N) + (p + N)) + 32)) (p + N + 1) :=
    S.compl hProj
  have hPos : posEps p N ∈ S.Ω (4 * (p + N + 1) + 20) 8 (p + N + 1) :=
    Work.WilG5.ltSet_mem (S := S) (Fin.last (p + N)) (0 : ℝ)
  have hPos' : posEps p N ∈
      S.Ω ((((F + 64 * ((p + N + 1 + N) + (p + N)) + 64) + 1) + N + (p + N + 1)) + 1) 8
        (p + N + 1) :=
    Work.WilG1.Omega.mono hPos (by omega) le_rfl
  have hM : posEps p N ∩ (Work.WilG0.projLastIter (p + N + 1) N (Inner p N Z))ᶜ ∈
      S.Ω (((((F + 64 * ((p + N + 1 + N) + (p + N)) + 64) + 1) + N + (p + N + 1)) + 1) + 1)
        (8 + (4 + (D + 32 * ((p + N + 1 + N) + (p + N)) + 32))) (p + N + 1) :=
    Work.WilG4a.CD.inter2_same (S := S) hPos' hProjC
  have hmain : projLast (posEps p N ∩
      (Work.WilG0.projLastIter (p + N + 1) N (Inner p N Z))ᶜ) ∈
      S.Ω ((((((F + 64 * ((p + N + 1 + N) + (p + N)) + 64) + 1) + N + (p + N + 1)) + 1) + 1) + 1)
        (8 + (4 + (D + 32 * ((p + N + 1 + N) + (p + N)) + 32))) (p + N) :=
    S.proj hM
  have hfinal : aux p N Z ∈
      S.Ω (((((((F + 64 * ((p + N + 1 + N) + (p + N)) + 64) + 1) + N + (p + N + 1)) + 1) + 1) + 1) + 1)
        (8 + (4 + (D + 32 * ((p + N + 1 + N) + (p + N)) + 32))) (p + N) :=
    S.compl hmain
  refine Work.WilG1.Omega.mono hfinal (by omega) (by omega)

end Work.WilG4c.FibC
