/-
  WilG4c — vocabulary for `FDerivDirGraphMem`.

  Given `φ : ℝ^N → ℝ` and a direction `e : ℝ^N`, the graph of the *total* directional
  derivative `w ↦ fderiv ℝ φ w e` splits into two `Ω`-definable pieces:

  * the **good piece** `dirGraphSet N φ e = {x | ∃ c, HasFDerivAt φ (Lin c) (Fin.init x) ∧
    x (last N) = Lin c e}`: where `φ` is differentiable the total `fderiv` *is* the true
    derivative `Lin c`, and the directional derivative is `Lin c e = Σᵢ cᵢ eᵢ`;
  * the **bad piece** `badGraphSet N φ = {x | ¬(∃ c, HasFDerivAt φ (Lin c) (Fin.init x)) ∧
    x (last N) = 0}`: off the differentiability locus the total `fderiv` is `0`.

  The good piece is the projection, along the `N`-element coefficient block, of the set
  `dirRelSet N φ e ⊆ ℝ^{(N+1)+N}`: the pullback of `epsFDerivSet N φ` along `dirSub N`
  (reading the `(w,u)`-block as the `N` arguments and the trailing block as the coefficients)
  intersected with the single linear hypersurface `u = Σᵢ cᵢ eᵢ`.

  This file contains the vocabulary and the elementary (analysis-free, `Ω`-free) membership
  lemmas.  The `Ω`-memberships live in `Work.WilG4c.dirGraphSetMem` /
  `Work.WilG4c.badGraphSetMem`, and the graph decomposition in
  `Work.WilG4c.fderivDirGraph_eq`.
-/
import Mathlib
import Submission.Work.WilG4c.SgnEqDefs
import Submission.Work.WilG0.projLastIter_mem
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG0.snocIt_castAdd
import Submission.Work.WilG0.snocIt_natAdd
import Submission.Work.WilG1.Basic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG Work.WilG0

/-! ## 1. The ambient layout `ℝ^{(N+1)+N}`

`snocIt (N+1) N x c : Fin ((N+1)+N) → ℝ` has the `(w,u)`-block `x` in the first `N+1`
coordinates and the coefficient block `c` in the last `N`.  The map `dirSub N` re-reads such a
vector as an element of `ℝ^{N+N}`: its first `N` coordinates (the `x`-arguments of `φ`) and its
last `N` (the coefficients). -/

/-- The map sending the `(w,u)`-block and the coefficient block to the `(x,c)`-layout of
`epsFDerivSet`: coordinates `0..N-1` (the arguments) and `N+1..2N` (the coefficients). -/
def dirSub (N : ℕ) : Fin (N + N) → Fin ((N + 1) + N) :=
  Fin.append (fun i : Fin N => Fin.castAdd N (Fin.castSucc i))
    (fun j : Fin N => Fin.natAdd (N + 1) j)

@[simp]
theorem dirSub_castAdd (N : ℕ) (i : Fin N) :
    dirSub N (Fin.castAdd N i) = Fin.castAdd N (Fin.castSucc i) :=
  Fin.append_left _ _ i

@[simp]
theorem dirSub_natAdd (N : ℕ) (j : Fin N) :
    dirSub N (Fin.natAdd N j) = Fin.natAdd (N + 1) j :=
  Fin.append_right _ _ j

/-- The argument block of a glued vector: the first `N` coordinates. -/
theorem snocIt_castAdd_fun (N : ℕ) (w c : Fin N → ℝ) :
    (fun i : Fin N => snocIt N N w c (Fin.castAdd N i)) = w := by
  funext i
  exact snocIt_castAdd N N w c i

/-- The coefficient block of a glued vector: the last `N` coordinates. -/
theorem snocIt_natAdd_fun (N : ℕ) (w c : Fin N → ℝ) :
    (fun i : Fin N => snocIt N N w c (Fin.natAdd N i)) = c := by
  funext i
  exact snocIt_natAdd N N w c i

/-- The argument block of a glued vector, evaluated at a coordinate (the `Fin.castSucc` form
used by `epsFDerivSet`). -/
theorem snocIt_castAdd_init (N : ℕ) (x : Fin (N + 1) → ℝ) (c : Fin N → ℝ) (i : Fin N) :
    snocIt N N (Fin.init x) c (Fin.castAdd N i) = x (Fin.castSucc i) :=
  snocIt_castAdd N N (Fin.init x) c i

/-- Re-reading a glued point along `dirSub` gives the glued point of `epsFDerivSet`. -/
theorem snocIt_comp_dirSub (N : ℕ) (x : Fin (N + 1) → ℝ) (c : Fin N → ℝ) :
    snocIt (N + 1) N x c ∘ dirSub N = snocIt N N (Fin.init x) c := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro i'
    show snocIt (N + 1) N x c (dirSub N (Fin.castAdd N i')) =
      snocIt N N (Fin.init x) c (Fin.castAdd N i')
    rw [dirSub_castAdd, snocIt_castAdd, snocIt_castAdd_init]
  · intro j
    show snocIt (N + 1) N x c (dirSub N (Fin.natAdd N j)) =
      snocIt N N (Fin.init x) c (Fin.natAdd N j)
    rw [dirSub_natAdd, snocIt_natAdd, snocIt_natAdd]

/-- Membership in `epsFDerivSet` of a glued point. -/
theorem mem_epsFDerivSet_snocIt (N : ℕ) (φ : (Fin N → ℝ) → ℝ) (w c : Fin N → ℝ) :
    snocIt N N w c ∈ epsFDerivSet N φ ↔ HasFDerivAt φ (Lin c) w := by
  rw [mem_epsFDerivSet]
  simp only [snocIt_natAdd_fun, snocIt_castAdd_fun]

/-! ## 2. The linear hypersurface `u = Σᵢ cᵢ eᵢ` -/

/-- The linear polynomial `u - Σⱼ cⱼ eⱼ` in `ℝ^{(N+1)+N}`, where `u` is the last coordinate of
the `(w,u)`-block and `cⱼ` are the coordinates of the coefficient block. -/
def dirLinPoly (N : ℕ) (e : Fin N → ℝ) : MvPolynomial (Fin ((N + 1) + N)) ℝ :=
  MvPolynomial.X (Fin.castAdd N (Fin.last N)) -
    ∑ j : Fin N, MvPolynomial.C (e j) * MvPolynomial.X (Fin.natAdd (N + 1) j)

/-- `dirLinPoly` has total degree at most one. -/
theorem dirLinPoly_totalDegree_le (N : ℕ) (e : Fin N → ℝ) :
    (dirLinPoly N e).totalDegree ≤ 1 := by
  have hterm : ∀ j : Fin N,
      (MvPolynomial.C (e j) * MvPolynomial.X (Fin.natAdd (N + 1) j) :
        MvPolynomial (Fin ((N + 1) + N)) ℝ).totalDegree ≤ 1 := by
    intro j
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
    omega
  refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
  · exact le_of_eq (MvPolynomial.totalDegree_X (Fin.castAdd N (Fin.last N)))
  · refine le_trans (MvPolynomial.totalDegree_finsetSum Finset.univ
      (fun j : Fin N => MvPolynomial.C (e j) * MvPolynomial.X (Fin.natAdd (N + 1) j))) ?_
    exact Finset.sup_le (fun j _ => hterm j)

/-- Evaluating `dirLinPoly` on a glued point: the hypersurface reads `u = Lin c e`. -/
theorem eval_dirLinPoly (N : ℕ) (e : Fin N → ℝ) (x : Fin (N + 1) → ℝ) (c : Fin N → ℝ) :
    MvPolynomial.eval (snocIt (N + 1) N x c) (dirLinPoly N e) = x (Fin.last N) - Lin c e := by
  have h1 : MvPolynomial.eval (snocIt (N + 1) N x c)
      (MvPolynomial.X (Fin.castAdd N (Fin.last N)) :
        MvPolynomial (Fin ((N + 1) + N)) ℝ) = x (Fin.last N) := by
    rw [MvPolynomial.eval_X]
    exact snocIt_castAdd (N + 1) N x c (Fin.last N)
  have h2 : MvPolynomial.eval (snocIt (N + 1) N x c)
      (∑ j : Fin N, MvPolynomial.C (e j) * MvPolynomial.X (Fin.natAdd (N + 1) j)) =
        Lin c e := by
    rw [Lin_apply]
    simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X, snocIt_natAdd]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact mul_comm _ _
  simp only [dirLinPoly, MvPolynomial.eval_sub, h1, h2]

/-! ## 3. The relation set and its projection -/

/-- The pullback of `epsFDerivSet N φ` along `dirSub N`, intersected with the hypersurface
`u = Lin c e`.  Its points are the triples `(w, u, c)` with `Lin c` a derivative of `φ` at `w`
and `u = Lin c e`. -/
def dirRelSet (N : ℕ) (φ : (Fin N → ℝ) → ℝ) (e : Fin N → ℝ) :
    Set (Fin ((N + 1) + N) → ℝ) :=
  {p | p ∘ dirSub N ∈ epsFDerivSet N φ} ∩
    {p | MvPolynomial.eval p (dirLinPoly N e) = 0}

/-- Membership of a glued point in `dirRelSet`. -/
theorem mem_dirRelSet (N : ℕ) (φ : (Fin N → ℝ) → ℝ) (e : Fin N → ℝ)
    (x : Fin (N + 1) → ℝ) (c : Fin N → ℝ) :
    snocIt (N + 1) N x c ∈ dirRelSet N φ e ↔
      HasFDerivAt φ (Lin c) (Fin.init x) ∧ x (Fin.last N) = Lin c e := by
  have h1 : (snocIt (N + 1) N x c ∘ dirSub N) ∈ epsFDerivSet N φ ↔
      HasFDerivAt φ (Lin c) (Fin.init x) := by
    rw [snocIt_comp_dirSub]
    exact mem_epsFDerivSet_snocIt N φ (Fin.init x) c
  have h2 : MvPolynomial.eval (snocIt (N + 1) N x c) (dirLinPoly N e) = 0 ↔
      x (Fin.last N) = Lin c e := by
    rw [eval_dirLinPoly, sub_eq_zero]
  constructor
  · intro h
    rw [dirRelSet, Set.mem_inter_iff, Set.mem_ofPred_eq] at h
    exact ⟨h1.mp h.1, h2.mp h.2⟩
  · rintro ⟨ha, hb⟩
    rw [dirRelSet, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨h1.mpr ha, h2.mpr hb⟩

/-- The **good piece** of the graph of the directional derivative. -/
def dirGraphSet (N : ℕ) (φ : (Fin N → ℝ) → ℝ) (e : Fin N → ℝ) : Set (Fin (N + 1) → ℝ) :=
  {x | ∃ c : Fin N → ℝ, HasFDerivAt φ (Lin c) (Fin.init x) ∧ x (Fin.last N) = Lin c e}

/-- The **bad piece**: where `φ` is not differentiable the total `fderiv` vanishes. -/
def badGraphSet (N : ℕ) (φ : (Fin N → ℝ) → ℝ) : Set (Fin (N + 1) → ℝ) :=
  {x | ¬ (∃ c : Fin N → ℝ, HasFDerivAt φ (Lin c) (Fin.init x)) ∧ x (Fin.last N) = 0}

@[simp]
theorem mem_badGraphSet (N : ℕ) (φ : (Fin N → ℝ) → ℝ) (x : Fin (N + 1) → ℝ) :
    x ∈ badGraphSet N φ ↔
      ¬ (∃ c : Fin N → ℝ, HasFDerivAt φ (Lin c) (Fin.init x)) ∧ x (Fin.last N) = 0 :=
  Iff.rfl

/-- The projection of `dirRelSet` along the coefficient block is the good piece. -/
theorem projLastIter_dirRelSet (N : ℕ) (φ : (Fin N → ℝ) → ℝ) (e : Fin N → ℝ) :
    projLastIter (N + 1) N (dirRelSet N φ e) = dirGraphSet N φ e := by
  rw [projLastIter_eq]
  ext x
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, (mem_dirRelSet N φ e x c).mp hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, (mem_dirRelSet N φ e x c).mpr hc⟩

/-! ## 4. The differentiability locus -/

/-- The differentiability locus of `φ` is the projection of `epsFDerivSet` along the
coefficient block. -/
theorem projLastIter_epsFDerivSet (N : ℕ) (φ : (Fin N → ℝ) → ℝ) :
    projLastIter N N (epsFDerivSet N φ) =
      {w : Fin N → ℝ | ∃ c : Fin N → ℝ, HasFDerivAt φ (Lin c) w} := by
  rw [projLastIter_eq]
  ext w
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, (mem_epsFDerivSet_snocIt N φ w c).mp hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, (mem_epsFDerivSet_snocIt N φ w c).mpr hc⟩

/-- The bad piece, written as the pullback of the complement of the differentiability locus
along the base-point projection. -/
theorem badGraphSet_eq (N : ℕ) (φ : (Fin N → ℝ) → ℝ) :
    badGraphSet N φ =
      {x : Fin (N + 1) → ℝ |
        Fin.init x ∈ (projLastIter N N (epsFDerivSet N φ))ᶜ ∧ x (Fin.last N) = 0} := by
  ext x
  simp only [badGraphSet, projLastIter_epsFDerivSet, Set.mem_compl_iff, Set.mem_ofPred_eq]

end Work.WilG4c
