import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.SellingDefs
import Submission.Work.SG.SellingAux
import Submission.Work.SG.exists_invariant_form
import Submission.Work.SG.supp_connected
import Submission.Work.SG.permMat_isUnit
import Submission.Work.SG.sb_permMat
import Submission.Work.SG.minVecs_eq_sellingVecs
import Submission.Work.SG.graph_classify
import Submission.Work.SG.selling_reduce
import Submission.Work.SG.sellingVecs_suppGraph_mul_permMat

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/SG/DESIGN.md first (orchestrator design; your lemma is one node of its DAG). Shared definitions + generated data: Submission/Work/SG/Defs.lean (namespace Work.SG) — do NOT edit it. native_decide is NOT permitted (only kernel decide / rfl); keep certificate checks kernel-cheap. Siblings run in parallel; import them when they land.

# exists_conj_into_sellingStab — Selling reduction (medium–hard, ~1–2k lines)

**Claim.** Every finite `P ≤ GL₃(ℤ)` is `SL₃(ℤ)`-conjugate into `sellingStab (sellingGraph i)`
for some `i : Fin 6`.

**Route (all elementary, integer arithmetic).**
1. `Q := ∑_{A∈P} AᵀA` is an integer, symmetric, positive-definite, `P`-invariant form
   (`AᵀQA = Q`).
2. **Selling reduction.** A *superbase* is `v₀..v₃` with `v₁,v₂,v₃` a `ℤ`-basis and
   `v₀ = −(v₁+v₂+v₃)`. It is *obtuse* if `p_ij := vᵢ·_Q vⱼ ≤ 0` for all `i ≠ j`. If some
   `p_ij > 0`, replace `(vᵢ, vⱼ, v_k, v_l)` by `(−vᵢ, vⱼ, v_k + vᵢ, v_l + vᵢ)`. This is again a
   superbase, and `∑ Q(v_m)` drops by exactly `2 p_ij > 0`. It is a natural number, so
   well-founded recursion terminates. Result: `W ∈ GL₃(ℤ)` (columns `v₁,v₂,v₃`; make `det = 1`
   by using `−W` if needed, which is harmless since `−1` is central) with `Q' := WᵀQW` obtuse.
3. **Norm formula.** With `qᵢⱼ := −p_ij ≥ 0` and `x = (0, y)`:
   `Q'(y) = ∑_{i<j} q_ij (x_i − x_j)²`. The support graph `Γ = {ij | q_ij > 0}` is connected,
   since otherwise the indicator of a component gives `Q' = 0` on a nonzero vector.
4. **Coset-minimal vectors.** For `y` in the class `c ∈ ℤ³/2ℤ³ \ {0}`, the parities of `x`
   define a cut `S`, and `Q'(y) ≥ ∑_{ij ∈ cut} q_ij`, with equality iff `|x_i − x_j| ≤ 1` on
   every edge of `Γ`. The minimum is attained (by `∑_{i∈S} vᵢ`). So the set of coset-minimal
   vectors of all nonzero classes is exactly `sellingVecs Γ`, which depends only on `Γ`.
5. Every `A ∈ Aut(Q') ∩ GL₃(ℤ)` preserves `Q'` and `2ℤ³`, so it permutes coset minima:
   `A (sellingVecs Γ) ⊆ sellingVecs Γ`. Hence `W⁻¹ P W ⊆ sellingStab Γ`.
6. **Relabel.** `Γ` is one of the 38 connected labelled graphs on `{0,1,2,3}`. A permutation `σ`
   of the superbase is an explicit `T_σ ∈ GL₃(ℤ)` (24 matrices) mapping
   `sellingVecs Γ ↔ sellingVecs (σΓ)`. Pick `σ` taking `Γ` to one of the 6 listed graphs. This is
   a finite check, fine for `decide` over `Fin 4` data.

**Validated** (Python, `scripts/s1.py`): the six stabilisers have orders 48 (K₄, bcc),
16 (K₄−e), 48 (C₄, fcc), 24 (paw, hexagonal), 48 (P₄), 48 (star, primitive cubic). All
entries are in `{−2..2}` (`{−1,0,1}` except P₄).

**Pitfalls.** Work with the integer Gram matrix and integer superbasics throughout; no reals.
The termination measure is `∑_m Q(v_m)` (a `ℕ`), not a lexicographic order.
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

open scoped Matrix

/-- Negating a matrix negates each superbase vector. -/
theorem sb_neg (W : IMat) (m : Fin 4) : sb (-W) m = -sb W m := by
  rcases Fin.eq_zero_or_eq_succ m with rfl | ⟨i, rfl⟩
  · funext k
    fin_cases k <;> simp [sb] <;> ring
  · rw [sb_succ, sb_succ]
    funext k
    simp

/-- The obtuse condition is invariant under negating the basis matrix. -/
theorem obSbase_neg {Q W : IMat} (h : ObSbase Q W) : ObSbase Q (-W) := by
  intro m n hmn
  have h1 : bf Q (sb (-W) m) (sb (-W) n) = bf Q (sb W m) (sb W n) := by
    rw [sb_neg, sb_neg, bf_neg_left, bf_neg_right, neg_neg]
  rw [h1]
  exact h m n hmn

/-- The obtuse condition is invariant under relabelling the superbase. -/
theorem obSbase_mul_permMat (Q W : IMat) (σ : Equiv.Perm (Fin 4)) :
    ObSbase Q (W * permMat σ) ↔ ObSbase Q W := by
  have h := sb_permMat W σ
  constructor
  · intro hob m n hmn
    have hmn' : σ.symm m ≠ σ.symm n := fun hc =>
      hmn (by rw [← Equiv.apply_symm_apply σ m, hc, Equiv.apply_symm_apply σ n])
    have h1 := hob (σ.symm m) (σ.symm n) hmn'
    rw [h (σ.symm m), h (σ.symm n), Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1
    exact h1
  · intro hob m n hmn
    have hmn' : σ m ≠ σ n := fun hc => hmn (σ.injective hc)
    have h1 := hob (σ m) (σ n) hmn'
    rw [h m, h n]
    exact h1

/-- Selling reduction: every finite subgroup of `GL₃(ℤ)` is `SL₃(ℤ)`-conjugate into the
stabiliser of the coset-minimal vector set of one of the six Selling support graphs. -/
theorem exists_conj_into_sellingStab {P : Set IMat} (hP : IsIntPointGroup P) :
    ∃ U : IMat, U.det = 1 ∧ ∃ i : Fin 6, ∀ A ∈ P, U * A * U⁻¹ ∈ sellingStab (sellingGraph i) := by
  classical
  -- Step 1: an invariant, positive definite integer form for `P`.
  obtain ⟨Q, hQsym, hinv, hQpsd, hQpd⟩ := exists_invariant_form P hP
  -- Step 2: Selling reduction.
  obtain ⟨W₀, hW₀u, hW₀ob⟩ := selling_reduce Q hQsym hQpsd
  -- normalise the determinant to `1`
  obtain ⟨W, hWdet, hWob⟩ : ∃ W : IMat, W.det = 1 ∧ ObSbase Q W := by
    rcases det_eq_one_or_neg_one hW₀u with h | h
    · exact ⟨W₀, h, hW₀ob⟩
    · refine ⟨-W₀, ?_, obSbase_neg hW₀ob⟩
      rw [Matrix.det_neg, h]
      norm_num
  have hWu : IsUnit W.det := by rw [hWdet]; exact isUnit_one
  have hWminv : W * W⁻¹ = 1 := mul_inv_of_isUnit hWu
  have hWminv' : W⁻¹ * W = 1 := inv_mul_of_isUnit hWu
  have hWdetInv : (W⁻¹).det = 1 := by
    rw [Matrix.inv_def, hWdet, Ring.inverse_one, one_smul, Matrix.det_adjugate, hWdet]
    norm_num
  -- Step 3/4: the coset-minimal vectors are those of the support graph.
  set Γ : List (Fin 4 × Fin 4) := suppGraph Q W with hΓdef
  have hminΓ : minVecs (Wᵀ * Q * W) = sellingVecs Γ := by
    rw [hΓdef]
    exact minVecs_eq_sellingVecs Q W hQsym hWob
  have hΓnd : ∀ p ∈ Γ, p.1 < p.2 := fun _ hp => (mem_suppGraph.mp (hΓdef ▸ hp)).1
  have hconn : IsConnGraph Γ := by
    rw [hΓdef]
    exact supp_connected Q W hQsym hWu hQpd
  -- Step 6: relabel `Γ` to one of the six graphs.
  obtain ⟨τ, i, hτ⟩ := graph_classify Γ hΓnd hconn
  -- the relabelled superbase
  have hobτ : ObSbase Q (W * permMat τ) := (obSbase_mul_permMat Q W τ).mpr hWob
  have hminτ : minVecs ((W * permMat τ)ᵀ * Q * (W * permMat τ)) =
      sellingVecs (suppGraph Q (W * permMat τ)) :=
    minVecs_eq_sellingVecs Q (W * permMat τ) hQsym hobτ
  have hbridge : sellingVecs (suppGraph Q (W * permMat τ)) = sellingVecs (sellingGraph i) := by
    have hnd : ∀ p ∈ sellingGraph i, p.1 < p.2 := by fin_cases i <;> decide
    exact sellingVecs_suppGraph_mul_permMat (Q := Q) (W := W) (τ := τ) (E := sellingGraph i)
      hQsym hnd hτ
  -- the relabelling matrix maps the six-graph minimal vectors onto those of `Γ`
  have hNdet : IsUnit (permMat τ).det := permMat_isUnit τ
  have hNQ : (permMat τ)ᵀ * (Wᵀ * Q * W) * (permMat τ) =
      (W * permMat τ)ᵀ * Q * (W * permMat τ) := by
    rw [Matrix.transpose_mul]
    noncomm_ring
  have himage : ∀ y : IVec,
      y ∈ sellingVecs (sellingGraph i) ↔ (permMat τ).mulVec y ∈ sellingVecs Γ := by
    intro y
    rw [← hbridge, ← hminτ, minVecs_map_iff hNdet hNQ y, hminΓ]
  -- choose `C` with determinant `1` and `C '' sellingVecs (sellingGraph i) = sellingVecs Γ`
  obtain ⟨C, hCdet, hCimage⟩ : ∃ C : IMat, C.det = 1 ∧
      ∀ y : IVec, y ∈ sellingVecs (sellingGraph i) ↔ C.mulVec y ∈ sellingVecs Γ := by
    rcases det_eq_one_or_neg_one hNdet with h | h
    · exact ⟨permMat τ, h, himage⟩
    · refine ⟨-permMat τ, ?_, ?_⟩
      · rw [Matrix.det_neg, h]
        norm_num
      · intro y
        rw [Matrix.neg_mulVec]
        exact (himage y).trans (sellingVecs_neg Γ ((permMat τ).mulVec y))
  have hCu : IsUnit C.det := by rw [hCdet]; exact isUnit_one
  have hCminv : C * C⁻¹ = 1 := mul_inv_of_isUnit hCu
  have hCminv' : C⁻¹ * C = 1 := inv_mul_of_isUnit hCu
  have hCdetInv : (C⁻¹).det = 1 := by
    rw [Matrix.inv_def, hCdet, Ring.inverse_one, one_smul, Matrix.det_adjugate, hCdet]
    norm_num
  -- the conjugating matrix (chosen so that it conjugates `B` into the stabiliser of the
  -- six-graph minimal vectors)
  refine ⟨C⁻¹ * W⁻¹, ?_, i, ?_⟩
  · rw [Matrix.det_mul, hCdetInv, hWdetInv, mul_one]
  · intro A hA
    have hAinv : Aᵀ * Q * A = Q := hinv A hA
    have hBdet : IsUnit (W⁻¹ * A * W).det := by
      rw [Matrix.det_mul, Matrix.det_mul]
      exact IsUnit.mul (IsUnit.mul (by rw [hWdetInv]; exact isUnit_one) (hP.2.2.2 A hA))
        (by rw [hWdet]; exact isUnit_one)
    have hBQ : (W⁻¹ * A * W)ᵀ * (Wᵀ * Q * W) * (W⁻¹ * A * W) = Wᵀ * Q * W :=
      conjugate_invariant hWminv hWminv' hAinv
    have hBpres : ∀ y ∈ sellingVecs Γ, (W⁻¹ * A * W).mulVec y ∈ sellingVecs Γ := by
      intro y hy
      have hy' : y ∈ minVecs (Wᵀ * Q * W) := by rw [hminΓ]; exact hy
      have h2 := (minVecs_map_iff hBdet hBQ y).mp hy'
      rwa [hminΓ] at h2
    have hUinv : (C⁻¹ * W⁻¹)⁻¹ = W * C := by
      refine Matrix.inv_eq_left_inv ?_
      calc W * C * (C⁻¹ * W⁻¹) = W * (C * C⁻¹) * W⁻¹ := by noncomm_ring
        _ = W * 1 * W⁻¹ := by rw [hCminv]
        _ = 1 := by rw [Matrix.mul_one, hWminv]
    refine ⟨?_, ?_⟩
    · have h1 : ((C⁻¹ * W⁻¹) * A * (C⁻¹ * W⁻¹)⁻¹).det =
          ((C⁻¹ * W⁻¹).det) * A.det * (((C⁻¹ * W⁻¹)⁻¹).det) := by
        rw [Matrix.det_mul, Matrix.det_mul]
      have h2 : (C⁻¹ * W⁻¹).det = 1 := by rw [Matrix.det_mul, hCdetInv, hWdetInv, mul_one]
      have h3 : ((C⁻¹ * W⁻¹)⁻¹).det = 1 := by rw [hUinv, Matrix.det_mul, hWdet, hCdet, mul_one]
      rw [h1, h2, h3, one_mul, mul_one]
      exact hP.2.2.2 A hA
    · intro y hy
      have hu : C.mulVec y ∈ sellingVecs Γ := (hCimage y).mp hy
      have hu' : (W⁻¹ * A * W).mulVec (C.mulVec y) ∈ sellingVecs Γ := hBpres _ hu
      have hz : (C⁻¹).mulVec ((W⁻¹ * A * W).mulVec (C.mulVec y)) ∈
          sellingVecs (sellingGraph i) :=
        (hCimage _).mpr (by rw [Matrix.mulVec_mulVec, hCminv, Matrix.one_mulVec]; exact hu')
      have hmat : (C⁻¹ * W⁻¹) * A * (C⁻¹ * W⁻¹)⁻¹ = C⁻¹ * (W⁻¹ * (A * (W * C))) := by
        rw [hUinv]; noncomm_ring
      rw [hmat]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec]
      have hBmv : (W⁻¹ * A * W).mulVec (C.mulVec y) =
          W⁻¹.mulVec (A.mulVec (W.mulVec (C.mulVec y))) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      rw [← hBmv]
      exact hz

end Work.SG
