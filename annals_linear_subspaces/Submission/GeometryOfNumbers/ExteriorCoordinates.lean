import Mathlib
import Submission.Commons.Analysis.InnerProductSpace.orthonormalBasis_normSq_sum
import Submission.Commons.Analysis.InnerProductSpace.orthonormalBasis_normSq_sum_smul

/-!
# Exterior-power coordinates along a coordinate subspace (Grassmannian dictionary, Part 0)

For `ℝᵈ = EuclideanSpace ℝ (Fin d)` with the standard orthonormal basis, we record the
coordinate machinery on the exterior power `⋀^k ℝᵈ` needed to describe how a `k`-subspace
sits with respect to an `ℓ`-subspace spanned by the first `ℓ` standard vectors:

* `wcoord w s` is the Plücker coordinate of the `k`-vector `w` at the `k`-subset `s`
  (equivalently the inner product of `w` with the standard basis `k`-vector `e_s`);
* for `ℓ ≤ d`, `blockElem w j` is the part of `w` whose subsets contain exactly `j` indices
  `≥ ℓ`, i.e. the component in `(∧^{k-j} x) ⊗ (∧^j xᗮ)` for `x = span {e i | i < ℓ}`.

All results here are Mathlib-only.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry
set_option autoImplicit false

namespace Submission.ExteriorCoordinates

abbrev RD (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)
abbrev WK (d k : ℕ) : Type := ⋀[ℝ]^k (RD d)
abbrev IDX (d k : ℕ) : Type := Set.powersetCard (Fin d) k
abbrev B (d : ℕ) : OrthonormalBasis (Fin d) ℝ (RD d) := EuclideanSpace.basisFun (Fin d) ℝ

/-- The exterior-power orthonormal basis of `⋀^k ℝᵈ` induced by the standard basis. -/
abbrev Bk (d k : ℕ) : OrthonormalBasis (IDX d k) ℝ (WK d k) := (B d).exteriorPower k

/-- Plücker coordinate of a `k`-vector at the `k`-subset `s` of indices (coordinate w.r.t. the
standard basis of the exterior power). -/
def wcoord {d k : ℕ} (w : WK d k) (s : IDX d k) : ℝ :=
  (Bk d k).repr w s

/-- The `k`-subsets of indices with exactly `j` elements `≥ ℓ` (i.e. `j` elements outside the
span of `e i, i < ℓ`). -/
def blockFinset {d k ℓ : ℕ} (j : ℕ) : Finset (IDX d k) := by
  classical
  exact Finset.univ.filter (fun s : IDX d k =>
    (((s : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card = j))

/-- The component of `w` living in the "`j` complement directions" block. -/
def blockElem {d k ℓ : ℕ} (w : WK d k) (j : ℕ) : WK d k :=
  (blockFinset (d := d) (k := k) (ℓ := ℓ) j).sum (fun s =>
    wcoord (d := d) (k := k) w s • ((Bk d k) s : WK d k))

/-- Norm squared of a block equals the sum of the squares of the coordinates in the block. -/
lemma blockElem_normSq {d k ℓ : ℕ} (w : WK d k) (j : ℕ) :
    ‖blockElem (d := d) (k := k) (ℓ := ℓ) w j‖ ^ 2 =
      (blockFinset (d := d) (k := k) (ℓ := ℓ) j).sum
        (fun s => (wcoord (d := d) (k := k) w s) ^ 2) := by
  unfold blockElem
  exact Commons.Analysis.InnerProductSpace.orthonormalBasis_normSq_sum_smul (Bk d k)
    (blockFinset (d := d) (k := k) (ℓ := ℓ) j) (fun s => wcoord (d := d) (k := k) w s)

/-- Full coordinate expansion of a `k`-vector in the standard exterior-power basis. -/
lemma sum_wcoord_smul_basis {d k : ℕ} (w : WK d k) :
    (Finset.univ : Finset (IDX d k)).sum (fun s =>
      wcoord (d := d) (k := k) w s • ((Bk d k) s : WK d k)) = w := by
  simpa [wcoord] using ((Bk d k).sum_repr w)

/-- Square of the norm of a `k`-vector equals the sum of the squares of all its Plücker
coordinates (instantiation of the general orthonormal-basis formula). -/
lemma normSq_eq_sum_wcoord {d k : ℕ} (w : WK d k) :
    ‖w‖ ^ 2 = (Finset.univ : Finset (IDX d k)).sum
      (fun s => (wcoord (d := d) (k := k) w s) ^ 2) := by
  simpa [wcoord] using
    (Commons.Analysis.InnerProductSpace.orthonormalBasis_normSq_sum (Bk d k) w)

/-- Any `k`-subset contains at most `k` indices `≥ ℓ`. -/
lemma count_ge_le {d k ℓ : ℕ} (s : IDX d k) :
    (((s : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card) ≤ k := by
  have hcard : (s : Finset (Fin d)).card = k := by
    exact s.2
  have hle : ((s : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card ≤
      (s : Finset (Fin d)).card := Finset.card_filter_le _ _
  omega

/-- Finset version of "summing over the fibres of a map `c : α → ℕ` of bounded value":
`Σⱼ Σ_{a : c a = j} f a = Σ_a f a` for `j` ranging over `0..k`. -/
lemma fiber_sum_range {α : Type*} [Fintype α] (k : ℕ) (c : α → ℕ) {M : Type*} [AddCommMonoid M]
    (f : α → M) (hc : ∀ a, c a ≤ k) :
    (Finset.range (k + 1)).sum (fun j : ℕ =>
      (Finset.univ.filter (fun a => c a = j)).sum (fun a => f a)) = Finset.univ.sum f := by
  classical
  calc
    (Finset.range (k + 1)).sum (fun j : ℕ =>
        (Finset.univ.filter (fun a => c a = j)).sum (fun a => f a))
        = (Finset.range (k + 1)).sum (fun j : ℕ =>
            Finset.univ.sum (fun a => if c a = j then f a else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [Finset.sum_filter]
    _ = Finset.univ.sum (fun a : α =>
          (Finset.range (k + 1)).sum (fun j : ℕ => if c a = j then f a else 0)) := by
          rw [Finset.sum_comm]
    _ = Finset.univ.sum (fun a : α => f a) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          have hca : c a ∈ Finset.range (k + 1) := by
            exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (hc a))
          have h1 : (Finset.range (k + 1)).sum (fun j : ℕ => if c a = j then f a else 0) = f a := by
            simpa using (Finset.sum_eq_single (M := M) (s := Finset.range (k + 1))
              (f := fun j : ℕ => if c a = j then f a else 0) (c a)
              (by
                intro b hb hneq
                simp [hneq.symm])
              (by
                intro hnot
                exact (hnot hca).elim))
          exact h1

/-- The decomposition `w = Σⱼ blockElem w j`: the blocks labelled by the number `j` of
indices `≥ ℓ` partition the basis of the exterior power. -/
lemma sum_blockElem {d k ℓ : ℕ} (w : WK d k) :
    (Finset.range (k + 1)).sum (fun j : ℕ =>
      blockElem (d := d) (k := k) (ℓ := ℓ) w j) = w := by
  classical
  let c : IDX d k → ℕ := fun s => ((s : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card
  have hc : ∀ s : IDX d k, c s ≤ k := by
    intro s
    exact count_ge_le (d := d) (k := k) (ℓ := ℓ) s
  calc
    (Finset.range (k + 1)).sum (fun j : ℕ => blockElem (d := d) (k := k) (ℓ := ℓ) w j)
        = (Finset.range (k + 1)).sum (fun j : ℕ =>
            (Finset.univ.filter (fun s => c s = j)).sum (fun s =>
              wcoord (d := d) (k := k) w s • ((Bk d k) s : WK d k))) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            apply Finset.sum_congr
            · ext s
              simp [blockFinset, c]
            · intro s hs
              rfl
    _ = (Finset.univ : Finset (IDX d k)).sum (fun s =>
          wcoord (d := d) (k := k) w s • ((Bk d k) s : WK d k)) := by
          exact fiber_sum_range k c (fun s => wcoord (d := d) (k := k) w s • ((Bk d k) s : WK d k)) hc
    _ = w := by
          exact sum_wcoord_smul_basis (d := d) (k := k) w

/-- Pythagoras for the block decomposition: the sum of the squared norms of the blocks of `w`
equals the squared norm of `w`. -/
lemma sum_normSq_blockElem {d k ℓ : ℕ} (w : WK d k) :
    (Finset.range (k + 1)).sum (fun j : ℕ =>
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) w j‖ ^ 2) = ‖w‖ ^ 2 := by
  classical
  calc
    (Finset.range (k + 1)).sum (fun j : ℕ => ‖blockElem (d := d) (k := k) (ℓ := ℓ) w j‖ ^ 2)
        = (Finset.range (k + 1)).sum (fun j : ℕ =>
            (blockFinset (d := d) (k := k) (ℓ := ℓ) j).sum
              (fun s => (wcoord (d := d) (k := k) w s) ^ 2)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            exact blockElem_normSq (d := d) (k := k) (ℓ := ℓ) w j
    _ = (Finset.univ : Finset (IDX d k)).sum (fun s => (wcoord (d := d) (k := k) w s) ^ 2) := by
          let c : IDX d k → ℕ := fun s => ((s : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card
          have hc : ∀ s : IDX d k, c s ≤ k := by
            intro s
            exact count_ge_le (d := d) (k := k) (ℓ := ℓ) s
          calc
            (Finset.range (k + 1)).sum (fun j : ℕ =>
                (blockFinset (d := d) (k := k) (ℓ := ℓ) j).sum
                  (fun s => (wcoord (d := d) (k := k) w s) ^ 2))
                = (Finset.range (k + 1)).sum (fun j : ℕ =>
                    (Finset.univ.filter (fun s => c s = j)).sum
                      (fun s => (wcoord (d := d) (k := k) w s) ^ 2)) := by
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    apply Finset.sum_congr
                    · ext s
                      simp [blockFinset, c]
                    · intro s hs
                      rfl
            _ = (Finset.univ : Finset (IDX d k)).sum
                  (fun s => (wcoord (d := d) (k := k) w s) ^ 2) := by
                  exact fiber_sum_range k c (fun s => (wcoord (d := d) (k := k) w s) ^ 2) hc
    _ = ‖w‖ ^ 2 := by
          exact (normSq_eq_sum_wcoord (d := d) (k := k) w).symm

end Submission.ExteriorCoordinates
