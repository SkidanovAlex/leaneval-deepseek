import Mathlib
import Submission.Work.Cohomology.Subdivision

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The sign-free cone formula for affine chains of `Δᴺ`

For the barycentric subdivision of the standard simplices one needs the algebraic identity

`boundaryLC (coneLC b c) = c - coneLC b (boundaryLC c)`

for affine chains (`Submission/Work/Cohomology/Subdivision.lean`).  Both sides are `ℤ`-linear in
`c`, so it suffices to check it on the generators `Finsupp.single w a`, i.e. on a single affine
simplex.  There the identity is pure `Fin`-combinatorics: the face maps of a cone `Fin.cons b w`
remove either the cone point (giving `w`) or one of the vertices of `w` (giving the cone over the
corresponding face), with the standard alternating signs.

## Main results

* `coneLC_single`, `boundaryLC_single` — the two chain maps on a generator;
* `boundaryLC_coneLC_single` — the cone formula on a generator;
* `boundaryLC_coneLC` — the cone formula on all affine chains.
-/

set_option backward.isDefEq.respectTransparency false

namespace Work.Cohomology

noncomputable section

/-- The `Fin`-level identity `succAbove i.succ (j.succ) = (succAbove i j).succ`. -/
lemma succAbove_succ_succ {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    (i.succ).succAbove (j.succ) = (i.succAbove j).succ := by
  rcases lt_or_ge i j.succ with h | h
  · rw [Fin.succAbove_of_lt_succ _ _ (Fin.succ_lt_succ_iff.mpr h),
        Fin.succAbove_of_lt_succ _ _ h]
  · rw [Fin.succAbove_of_succ_le _ _ (Fin.succ_le_succ_iff.mpr h),
        Fin.succAbove_of_succ_le _ _ h, Fin.castSucc_succ]

/-- The `0`-th face of a cone forgets the cone point. -/
lemma faceVF_zero_cons {N k : ℕ} (b : stdSimplex ℝ (Fin (N+1)))
    (w : Fin (k+2) → stdSimplex ℝ (Fin (N+1))) :
    faceVF (N := N) (0 : Fin (k+3)) (coneVF b w) = w := by
  funext j
  simp [faceVF, coneVF]

/-- The `(i+1)`-st face of a cone is the cone over the `i`-th face. -/
lemma faceVF_cons_succ {N k : ℕ} (i : Fin (k+2)) (b : stdSimplex ℝ (Fin (N+1)))
    (w : Fin (k+2) → stdSimplex ℝ (Fin (N+1))) :
    faceVF (N := N) i.succ (coneVF b w) = coneVF b (faceVF (N := N) i w) := by
  funext j
  induction j using Fin.cases with
  | zero => simp [faceVF, coneVF]
  | succ j' =>
      simp only [faceVF, coneVF, Fin.cons_succ]
      rw [succAbove_succ_succ]
      simp

/-- `(-1)^{i+1} = -(-1)^i` for the alternating signs of the boundary. -/
lemma neg_one_pow_fin_succ {k : ℕ} (i : Fin (k+2)) :
    ((-1 : ℤ) ^ (i.succ : ℕ)) = -((-1 : ℤ) ^ (i : ℕ)) := by
  rw [Fin.val_succ, pow_succ]
  ring

/-- The cone map on a generator of the affine chains. -/
lemma coneLC_single {N k : ℕ} (b : stdSimplex ℝ (Fin (N+1)))
    (v : Fin (k+1) → stdSimplex ℝ (Fin (N+1))) (a : ℤ) :
    coneLC N k b (Finsupp.single v a) = Finsupp.single (coneVF b v) a := by
  simp [coneLC, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- The boundary of a generator of the affine chains. -/
lemma boundaryLC_single (N j : ℕ) (v : Fin (j+2) → stdSimplex ℝ (Fin (N+1))) (a : ℤ) :
    boundaryLC N j (Finsupp.single v a) =
      ∑ i : Fin (j+2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (faceVF (N:=N) i v) a := by
  simp only [boundaryLC, LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]

/-- The cone over the boundary of a generator. -/
lemma coneLC_boundaryLC_single (N k : ℕ) (b : stdSimplex ℝ (Fin (N+1)))
    (w : Fin (k+2) → stdSimplex ℝ (Fin (N+1))) (a : ℤ) :
    coneLC N k b (boundaryLC N k (Finsupp.single w a)) =
      ∑ i : Fin (k+2), ((-1 : ℤ)^(i : ℕ)) • Finsupp.single (coneVF b (faceVF (N:=N) i w)) a := by
  rw [boundaryLC_single]
  simp only [map_sum, map_smul, coneLC_single]

/-- The boundary of the cone over a generator. -/
lemma boundaryLC_coneLC_single (N k : ℕ) (b : stdSimplex ℝ (Fin (N+1)))
    (w : Fin (k+2) → stdSimplex ℝ (Fin (N+1))) (a : ℤ) :
    boundaryLC N (k+1) (Finsupp.single (coneVF b w) a) =
      Finsupp.single w a -
        ∑ i : Fin (k+2), ((-1 : ℤ)^(i : ℕ)) • Finsupp.single (coneVF b (faceVF (N:=N) i w)) a := by
  rw [boundaryLC_single]
  rw [Fin.sum_univ_succ]
  rw [faceVF_zero_cons]
  simp only [Fin.val_zero, pow_zero, one_smul, neg_one_pow_fin_succ, faceVF_cons_succ, neg_smul]
  rw [Finset.sum_neg_distrib]
  rw [sub_eq_add_neg]

/-- The cone formula on a generator of the affine chains. -/
lemma boundaryLC_coneLC_single' (N k : ℕ) (b : stdSimplex ℝ (Fin (N+1)))
    (w : Fin (k+2) → stdSimplex ℝ (Fin (N+1))) (a : ℤ) :
    boundaryLC N (k+1) (coneLC N (k+1) b (Finsupp.single w a)) =
      Finsupp.single w a - coneLC N k b (boundaryLC N k (Finsupp.single w a)) := by
  rw [coneLC_single, boundaryLC_coneLC_single, coneLC_boundaryLC_single]

/-- **The sign-free cone formula**: `∂(b * c) = c - b * (∂c)` for affine chains of `Δᴺ`.
This is what makes the coned chain `coneLC (bary v) (Σᵢ (-1)ⁱ • …)` a cycle in the subdivision
recursion. -/
theorem boundaryLC_coneLC (N k : ℕ) (b : stdSimplex ℝ (Fin (N + 1))) (c : LinChain N (k + 1)) :
    boundaryLC N (k + 1) (coneLC N (k + 1) b c) =
      c - coneLC N k b (boundaryLC N k c) := by
  refine Finsupp.induction c ?h0 ?hstep
  · simp
  · intro a b' f ha hb hf
    simp only [map_add]
    rw [boundaryLC_coneLC_single' N k b a b', hf]
    abel

end

end Work.Cohomology
