import Mathlib
import Submission.Work.RTOwed.CuspRigid
import Submission.Work.HypModel.Basic
import Submission.Work.RTOwed.reflWallDefs
import Submission.Work.RTOwed.hypOfUHS_reflWall4
import Submission.Work.RTOwed.uhsOfHyp_diagNeg5

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Matrix
open scoped Matrix

namespace Work.RTOwed

open Work.FoldInst

/-! ### Elementary Lorentz algebra for the proof

These are the few `J`-computations that the argument needs: `J` is an involution, and it fixes
the basis vector `e_t` (`t : Fin 3` is a *spatial* index). -/

lemma f3to5_ne_three (t : Fin 3) : (f3to5 t : Fin 5) ≠ 3 := by
  intro h
  have := congrArg Fin.val h
  simp [f3to5] at this
  omega

lemma f3to5_ne_four (t : Fin 3) : (f3to5 t : Fin 5) ≠ 4 := by
  intro h
  have := congrArg Fin.val h
  simp [f3to5] at this
  omega

lemma J_mul_J : Work.HypModel.J * Work.HypModel.J = (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Work.HypModel.J]

lemma J_mulVec_J_mulVec (v : Work.HypModel.V5) :
    Work.HypModel.J *ᵥ (Work.HypModel.J *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, J_mul_J, Matrix.one_mulVec]

lemma J_mulVec_basis (t : Fin 3) :
    Work.HypModel.J *ᵥ (Pi.single (f3to5 t) 1 : Work.HypModel.V5)
      = Pi.single (f3to5 t) 1 := by
  funext i
  rw [Work.HypModel.J_mulVec]
  by_cases h : i = f3to5 t
  · subst h
    simp [Pi.single_eq_same, f3to5_ne_four]
  · simp [Pi.single_eq_of_ne h]

lemma lorentz_basis_self (t : Fin 3) :
    Work.HypModel.lorentz (Pi.single (f3to5 t) 1 : Work.HypModel.V5)
      (Pi.single (f3to5 t) 1) = 1 := by
  fin_cases t <;> simp [Work.HypModel.lorentz, f3to5]

/-- A Lorentz matrix is invertible: its transpose acts injectively.  This is the only place where
the invertibility of `A` (equivalently, that `A` is a bijection of `ℝ⁵`) enters the argument. -/
lemma transpose_mulVec_injective {A : Matrix (Fin 5) (Fin 5) ℝ}
    (hA : Work.HypModel.IsLorentzMat A) :
    Function.Injective fun w : Work.HypModel.V5 => Aᵀ *ᵥ w := by
  have hCA : (Work.HypModel.J * Aᵀ * Work.HypModel.J) * A = 1 := by
    have h : (Work.HypModel.J * Aᵀ * Work.HypModel.J) * A
        = Work.HypModel.J * (Aᵀ * Work.HypModel.J * A) := by noncomm_ring
    rw [h, hA.1, J_mul_J]
  have hAinj : Function.Injective fun x : Work.HypModel.V5 => A *ᵥ x := by
    intro x y hxy
    have hxy' : A *ᵥ x = A *ᵥ y := hxy
    have h0 : A *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy', sub_self]
    have h2 : x - y = 0 := by
      have h3 := congrArg (fun v : Work.HypModel.V5 =>
        (Work.HypModel.J * Aᵀ * Work.HypModel.J) *ᵥ v) h0
      rw [Matrix.mulVec_mulVec, hCA, Matrix.one_mulVec, Matrix.mulVec_zero] at h3
      exact h3
    exact sub_eq_zero.mp h2
  have hunit : IsUnit A := (Matrix.mulVec_injective_iff_isUnit (A := A)).1 hAinj
  exact (Matrix.mulVec_injective_iff_isUnit (A := Aᵀ)).2 ((isUnit_transpose A).2 hunit)

/-! ### The row relation forced by the wall hypothesis -/

/-- The chart point of height `1` with `k`-th coordinate `c` and `i`-th coordinate `s`. -/
def wpt (k i : Fin 3) (c s : ℝ) : Work.Cusp.E4 :=
  !₂[ (if (0 : Fin 3) = k then c else if (0 : Fin 3) = i then s else 0),
      (if (1 : Fin 3) = k then c else if (1 : Fin 3) = i then s else 0),
      (if (2 : Fin 3) = k then c else if (2 : Fin 3) = i then s else 0),
      1 ]

lemma norm_sq_wpt (k i : Fin 3) (c s : ℝ) (hi : i ≠ k) :
    ‖wpt k i c s‖ ^ 2 = c ^ 2 + s ^ 2 + 1 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four]
  simp only [Real.norm_eq_abs, sq_abs, wpt]
  fin_cases k <;> fin_cases i <;> simp_all <;> ring

/-- **The row relation.**  The wall hypothesis `hW` says that the hyperplane `{z k = c}` of the
upper half space model is mapped by `A` into the coordinate hyperplane `{y t = 0}`.  Evaluating at
the height-one points of the wall and comparing coefficients of the resulting quadratic polynomial
shows that the `t`-th row of `A` is a multiple of `wallDual k c`. -/
lemma wall_row_structure {A : Matrix (Fin 5) (Fin 5) ℝ} (k t : Fin 3) (c : ℝ)
    (hW : ∀ z : Work.Cusp.E4, 0 < z 3 → z (f3to4 k) = c →
      Matrix.mulVec A (Work.HypModel.hypOfUHS z) (f3to5 t) = 0) (j : Fin 5) :
    A (f3to5 t) j = A (f3to5 t) (f3to5 k) * wallDual k c j := by
  have heval : ∀ (i : Fin 3), i ≠ k → ∀ s : ℝ,
      A (f3to5 t) (f3to5 k) * c + A (f3to5 t) (f3to5 i) * s
        + A (f3to5 t) 3 * ((c ^ 2 + s ^ 2) / 2)
        + A (f3to5 t) 4 * ((c ^ 2 + s ^ 2) / 2 + 1) = 0 := by
    intro i hi s
    have h1 : 0 < (wpt k i c s) 3 := by simp [wpt]
    have h2 : (wpt k i c s) (f3to4 k) = c := by fin_cases k <;> simp [wpt, f3to4]
    have h := hW (wpt k i c s) h1 h2
    have hnorm := norm_sq_wpt k i c s hi
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_five] at h
    simp only [Work.HypModel.hypOfUHS_apply_zero, Work.HypModel.hypOfUHS_apply_one,
      Work.HypModel.hypOfUHS_apply_two, Work.HypModel.hypOfUHS_apply_three,
      Work.HypModel.hypOfUHS_apply_four] at h
    rw [hnorm] at h
    simp only [wpt] at h
    fin_cases k <;> fin_cases i <;> simp_all [f3to5, f3to4] <;> ring_nf at h ⊢ <;> linarith
  fin_cases k
  · have e1 : ∀ s : ℝ, A (f3to5 t) 0 * c + A (f3to5 t) 1 * s
        + A (f3to5 t) 3 * ((c ^ 2 + s ^ 2) / 2)
        + A (f3to5 t) 4 * ((c ^ 2 + s ^ 2) / 2 + 1) = 0 := fun s => heval 1 (by decide) s
    have e2 : ∀ s : ℝ, A (f3to5 t) 0 * c + A (f3to5 t) 2 * s
        + A (f3to5 t) 3 * ((c ^ 2 + s ^ 2) / 2)
        + A (f3to5 t) 4 * ((c ^ 2 + s ^ 2) / 2 + 1) = 0 := fun s => heval 2 (by decide) s
    have h1 : A (f3to5 t) 1 = 0 := by nlinarith [e1 1, e1 (-1)]
    have h2 : A (f3to5 t) 2 = 0 := by nlinarith [e2 1, e2 (-1)]
    have h34 : A (f3to5 t) 3 + A (f3to5 t) 4 = 0 := by nlinarith [e1 0, e1 1, e1 (-1)]
    have h3 : A (f3to5 t) 3 = c * A (f3to5 t) 0 := by nlinarith [e1 0, h34]
    have key : ∀ j : Fin 5, A (f3to5 t) j = A (f3to5 t) 0 * wallDual 0 c j := by
      intro j
      fin_cases j <;> simp [wallDual, f3to5_zero, f3to5_one, f3to5_two] <;>
        linarith [h1, h2, h34, h3]
    simp only [f3to5_zero]
    exact key j
  · have e1 : ∀ s : ℝ, A (f3to5 t) 1 * c + A (f3to5 t) 0 * s
        + A (f3to5 t) 3 * ((c ^ 2 + s ^ 2) / 2)
        + A (f3to5 t) 4 * ((c ^ 2 + s ^ 2) / 2 + 1) = 0 := fun s => heval 0 (by decide) s
    have e2 : ∀ s : ℝ, A (f3to5 t) 1 * c + A (f3to5 t) 2 * s
        + A (f3to5 t) 3 * ((c ^ 2 + s ^ 2) / 2)
        + A (f3to5 t) 4 * ((c ^ 2 + s ^ 2) / 2 + 1) = 0 := fun s => heval 2 (by decide) s
    have h1 : A (f3to5 t) 0 = 0 := by nlinarith [e1 1, e1 (-1)]
    have h2 : A (f3to5 t) 2 = 0 := by nlinarith [e2 1, e2 (-1)]
    have h34 : A (f3to5 t) 3 + A (f3to5 t) 4 = 0 := by nlinarith [e1 0, e1 1, e1 (-1)]
    have h3 : A (f3to5 t) 3 = c * A (f3to5 t) 1 := by nlinarith [e1 0, h34]
    have key : ∀ j : Fin 5, A (f3to5 t) j = A (f3to5 t) 1 * wallDual 1 c j := by
      intro j
      fin_cases j <;> simp [wallDual, f3to5_zero, f3to5_one, f3to5_two] <;>
        linarith [h1, h2, h34, h3]
    simp only [f3to5_one]
    exact key j
  · have e1 : ∀ s : ℝ, A (f3to5 t) 2 * c + A (f3to5 t) 0 * s
        + A (f3to5 t) 3 * ((c ^ 2 + s ^ 2) / 2)
        + A (f3to5 t) 4 * ((c ^ 2 + s ^ 2) / 2 + 1) = 0 := fun s => heval 0 (by decide) s
    have e2 : ∀ s : ℝ, A (f3to5 t) 2 * c + A (f3to5 t) 1 * s
        + A (f3to5 t) 3 * ((c ^ 2 + s ^ 2) / 2)
        + A (f3to5 t) 4 * ((c ^ 2 + s ^ 2) / 2 + 1) = 0 := fun s => heval 1 (by decide) s
    have h1 : A (f3to5 t) 0 = 0 := by nlinarith [e1 1, e1 (-1)]
    have h2 : A (f3to5 t) 1 = 0 := by nlinarith [e2 1, e2 (-1)]
    have h34 : A (f3to5 t) 3 + A (f3to5 t) 4 = 0 := by nlinarith [e1 0, e1 1, e1 (-1)]
    have h3 : A (f3to5 t) 3 = c * A (f3to5 t) 2 := by nlinarith [e1 0, h34]
    have key : ∀ j : Fin 5, A (f3to5 t) j = A (f3to5 t) 2 * wallDual 2 c j := by
      intro j
      fin_cases j <;> simp [wallDual, f3to5_zero, f3to5_one, f3to5_two] <;>
        linarith [h1, h2, h34, h3]
    simp only [f3to5_two]
    exact key j

/-! ### The main identity -/

/-- **Lemma R.**  Let `A` be a Lorentz matrix of `ℝ^{1,4}` which maps the wall `{z : z k = c}` of the
upper half space model of hyperbolic 4-space into the coordinate hyperplane `{y t = 0}` (equivalently,
into the geodesic hyperplane `{y : y t = 0}`).  Then `A` intertwines the reflection in the wall with
the reflection of the `t`-th coordinate:

  `mobius A (reflWall4 k c z) = reflCoord t (mobius A z)`  for every `z` of the upper half space.

The proof has four steps:
* (1) *row relation*: the wall hypothesis forces the `t`-th row of `A` to be a multiple
  `lam • wallDual k c` of the Lorentz dual of the wall normal (`wall_row_structure`);
* (2) *normal vector*: hence `Aᵀ e_t = lam (J n_{k,c})`, and since `Aᵀ` is injective
  (`transpose_mulVec_injective`) and `Aᵀ J A = J`, one gets `lam • (A n_{k,c}) = e_t`, so with
  `lam² = 1` from `⟨A n, A n⟩ = ⟨n,n⟩ = 1` also `A n_{k,c} = lam • e_t`;
* (3) *matrices*: therefore `A * wallMat k c = diagNeg5 (f3to5 t) * A`;
* (4) the two sides are the Möbius maps of these two matrices. -/
theorem mobius_reflWall {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : Work.HypModel.IsLorentzMat A)
    (k t : Fin 3) (c : ℝ)
    (hW : ∀ z : Work.Cusp.E4, 0 < z 3 → z (Work.FoldInst.f3to4 k) = c →
      Matrix.mulVec A (Work.HypModel.hypOfUHS z) (Work.FoldInst.f3to5 t) = 0) :
    ∀ z : Work.Cusp.E4, 0 < z 3 →
      Work.HypModel.mobius A (Work.RTOwed.reflWall4 k c z) =
        Work.RTOwed.reflCoord t (Work.HypModel.mobius A z) := by
  intro z hz
  have hz0 : z 3 ≠ 0 := ne_of_gt hz
  set lam : ℝ := A (f3to5 t) (f3to5 k) with hlam
  -- Step 1: the `t`-th row of `A` is `lam` times the wall dual.
  have hrow : ∀ j : Fin 5, A (f3to5 t) j = lam * wallDual k c j := by
    intro j
    rw [hlam]
    exact wall_row_structure k t c hW j
  -- Step 2a: `Aᵀ *ᵥ e_t = lam • wallDual k c`.
  have hATe : Aᵀ *ᵥ (Pi.single (f3to5 t) 1 : Work.HypModel.V5) = lam • wallDual k c := by
    rw [Matrix.mulVec_single_one, Matrix.col_transpose]
    funext j
    rw [Matrix.row_apply, hrow j, Pi.smul_apply, smul_eq_mul]
  -- Step 2b: `Aᵀ *ᵥ (J *ᵥ (A *ᵥ n)) = wallDual k c`.
  have h1 : Aᵀ *ᵥ (Work.HypModel.J *ᵥ (A *ᵥ wallVec k c)) = wallDual k c := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA.1, J_mulVec_wallVec]
  -- Step 2c: `lam • (J *ᵥ (A *ᵥ n)) = e_t` by injectivity of `Aᵀ`.
  have hkey : lam • (Work.HypModel.J *ᵥ (A *ᵥ wallVec k c)) = Pi.single (f3to5 t) 1 := by
    have h3 : Aᵀ *ᵥ (lam • (Work.HypModel.J *ᵥ (A *ᵥ wallVec k c))
        - Pi.single (f3to5 t) 1) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, h1, hATe, sub_self]
    have h4 : lam • (Work.HypModel.J *ᵥ (A *ᵥ wallVec k c))
        - Pi.single (f3to5 t) 1 = 0 := by
      refine transpose_mulVec_injective hA ?_
      show Aᵀ *ᵥ (lam • (Work.HypModel.J *ᵥ (A *ᵥ wallVec k c))
        - Pi.single (f3to5 t) 1) = Aᵀ *ᵥ (0 : Work.HypModel.V5)
      rw [h3, Matrix.mulVec_zero]
    exact sub_eq_zero.mp h4
  -- Step 2d: apply `J` to get `lam • (A *ᵥ n) = e_t`.
  have hYs : lam • (A *ᵥ wallVec k c) = Pi.single (f3to5 t) 1 := by
    have h := congrArg (fun v : Work.HypModel.V5 => Work.HypModel.J *ᵥ v) hkey
    rw [Matrix.mulVec_smul, J_mulVec_J_mulVec, J_mulVec_basis] at h
    exact h
  -- Step 2e: `lam ^ 2 = 1`.
  have hlamsq : lam * lam = 1 := by
    have hL : Work.HypModel.lorentz (lam • (A *ᵥ wallVec k c))
        (lam • (A *ᵥ wallVec k c)) = 1 := by
      rw [hYs, lorentz_basis_self]
    rw [Work.HypModel.lorentz_smul_left, Work.HypModel.lorentz_smul_right,
      Work.HypModel.lorentz_mulVec hA, lorentz_wallVec_self] at hL
    nlinarith [hL]
  -- Step 2f: `A *ᵥ n = lam • e_t`.
  have hY : A *ᵥ wallVec k c = lam • (Pi.single (f3to5 t) 1 : Work.HypModel.V5) := by
    have h := congrArg (fun v : Work.HypModel.V5 => lam • v) hYs
    rw [smul_smul, hlamsq, one_smul] at h
    exact h
  -- Step 3a: the `t`-th coordinate of `A *ᵥ P` is `lam` times the wall function of `P`.
  have hAP : ∀ P : Work.HypModel.V5,
      (A *ᵥ P) (f3to5 t) = lam * (P (f3to5 k) + c * P 3 - c * P 4) := by
    intro P
    have hsum : (A *ᵥ P) (f3to5 t) = ∑ j : Fin 5, A (f3to5 t) j * P j := by
      simp [Matrix.mulVec, dotProduct]
    rw [hsum]
    rw [show (∑ j : Fin 5, A (f3to5 t) j * P j)
        = ∑ j : Fin 5, lam * (wallDual k c j * P j) from
      Finset.sum_congr rfl (fun j _ => by rw [hrow j]; ring)]
    rw [← Finset.mul_sum]
    rw [show (∑ j : Fin 5, wallDual k c j * P j) = wallDual k c ⬝ᵥ P from rfl]
    rw [wallDual_dotProduct]
  -- Step 3b: the matrix identity `A *ᵥ (wallMat k c *ᵥ P) = diagNeg5 (f3to5 t) *ᵥ (A *ᵥ P)`.
  have hstep : ∀ P : Work.HypModel.V5,
      A *ᵥ (wallMat k c *ᵥ P) = diagNeg5 (f3to5 t) *ᵥ (A *ᵥ P) := by
    intro P
    rw [wallMat_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, hY, diagNeg5_mulVec, hAP P]
    rw [smul_smul]
    rw [show (2 * (P (f3to5 k) + c * P 3 - c * P 4)) * lam
        = 2 * (lam * (P (f3to5 k) + c * P 3 - c * P 4)) from by ring]
  -- Step 4: assemble.
  rw [Work.HypModel.mobius, Work.HypModel.mobius, hypOfUHS_reflWall4 k c z hz0]
  rw [hstep (Work.HypModel.hypOfUHS z)]
  exact uhsOfHyp_diagNeg5 t (A *ᵥ Work.HypModel.hypOfUHS z)

end Work.RTOwed
