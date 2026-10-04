import Mathlib
import Submission.Work.Diff.STE.deTurck.ChartCompDefs
import Submission.Work.Diff.EXT.contMDiffAt_matrix_inv
import Submission.Work.Diff.STE.deTurck.pPhi_symm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The coordinate derivative of the chart expression of the DeTurck field

This module computes the Fréchet derivatives (in the chart coordinates of the chart at `x₀`) of the
coordinate expressions `coGamU` and `coPhi` of `Submission/Work/Diff/STE/deTurck/ChartCompDefs.lean`:

* `coGamU A c a b y = ∑_p γ^{cp}(y) Γ_{abp}(y)` with `γ = (A y)⁻¹`, `Γ = jKz (fderiv ℝ A y)`; its
  derivative in the direction `bB m` is `jdGamU (A y) (fderiv ℝ A y) (fderiv ℝ (fderiv ℝ A) y) m c a b`
  (`fderiv_coGamU`);
* `coPhi A Ā c y = ∑_{ab} γ^{ab}(y)(Γ^c_{ab}(y) - Γ̃^c_{ab}(y))`; its derivative in the direction
  `bB m` is `jdWU (A y) (fderiv ℝ A y) (fderiv ℝ (fderiv ℝ A) y) (Ā y) (fderiv ℝ Ā y)
  (fderiv ℝ (fderiv ℝ Ā) y) m c` (`fderiv_coPhi`).

The two analytic ingredients are

* `fderiv_coPhi_kz`: the chain rule `∂_m jKz (fderiv ℝ A ·) a b p = jKzD (fderiv ℝ (fderiv ℝ A) y) m a b p`
  (linearity of `jKz` in its first argument);
* `fderiv_coPhi_inv`: `∂_m (A·)⁻¹ = -(A y)⁻¹ (∂_m A) (A y)⁻¹`, in the index convention of `jdInv`.
  This is done by differentiating the *constant* matrix identity `A · * (A ·)⁻¹ = 1` entrywise and
  solving for the derivative of the inverse, so that no normed-ring structure on `Matrix` (which the
  default `Pi` norm does not provide) is needed; the differentiability of the inverse entries comes
  from `Work.Diff.EXT.contDiffAt_matrix_inv_pi`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set

namespace Work.Diff.STE.deTurck

open Work.Diff.EXT Work.Diff.STE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

noncomputable section

/-- **The `(i,j)`-component of the Fréchet derivative of a matrix-valued function.** -/
lemma fderiv_entry (A : E → MatE (E := E)) (y : E) (m i j : Idx E)
    (hdA : DifferentiableAt ℝ A y) :
    fderiv ℝ (fun y' : E => A y' i j) y (bB (E := E) m) = fderiv ℝ A y (bB (E := E) m) i j := by
  have hd1 : DifferentiableAt ℝ (fun x : E => A x i) y := differentiableAt_pi.mp hdA i
  have hd2 : DifferentiableAt ℝ (fun x : E => A x i j) y := differentiableAt_pi.mp hd1 j
  rw [fderiv_apply hd1 j, fderiv_apply hdA i]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

/-- **Chain rule for the lowered Koszul pairing in its first argument.** -/
theorem fderiv_coPhi_kz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    (A : E → Work.Diff.EXT.MatE (E := E)) (y : E) (m a b p : Fin (Module.finrank ℝ E))
    (hA : ContDiffAt ℝ 2 A y) :
    fderiv ℝ (fun y' : E => Work.Diff.EXT.jKz (fderiv ℝ A y') a b p) y
        (Work.Diff.EXT.bB (E := E) m)
      = Work.Diff.EXT.jKzD (fderiv ℝ (fderiv ℝ A) y) m a b p := by
  have hfun : (fun y' : E => Work.Diff.EXT.jKz (fderiv ℝ A y') a b p)
      = (1 / 2 : ℝ) • (((fun y' : E => (fderiv ℝ A y' (Work.Diff.EXT.bB (E := E) a)) b p)
            + (fun y' : E => (fderiv ℝ A y' (Work.Diff.EXT.bB (E := E) b)) a p))
          - (fun y' : E => (fderiv ℝ A y' (Work.Diff.EXT.bB (E := E) p)) a b)) := by
    funext y'
    simp only [Work.Diff.EXT.jKz, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hdA : DifferentiableAt ℝ (fun y' : E => fderiv ℝ A y') y :=
    ((hA.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have hd1 : DifferentiableAt ℝ
      (fun y' : E => (fderiv ℝ A y' (Work.Diff.EXT.bB (E := E) a)) b p) y :=
    differentiableAt_pi.mp (differentiableAt_pi.mp
      ((ContinuousLinearMap.apply ℝ (Work.Diff.EXT.MatE (E := E))
        (Work.Diff.EXT.bB (E := E) a)).differentiableAt.comp y hdA) b) p
  have hd2 : DifferentiableAt ℝ
      (fun y' : E => (fderiv ℝ A y' (Work.Diff.EXT.bB (E := E) b)) a p) y :=
    differentiableAt_pi.mp (differentiableAt_pi.mp
      ((ContinuousLinearMap.apply ℝ (Work.Diff.EXT.MatE (E := E))
        (Work.Diff.EXT.bB (E := E) b)).differentiableAt.comp y hdA) a) p
  have hd3 : DifferentiableAt ℝ
      (fun y' : E => (fderiv ℝ A y' (Work.Diff.EXT.bB (E := E) p)) a b) y :=
    differentiableAt_pi.mp (differentiableAt_pi.mp
      ((ContinuousLinearMap.apply ℝ (Work.Diff.EXT.MatE (E := E))
        (Work.Diff.EXT.bB (E := E) p)).differentiableAt.comp y hdA) a) b
  rw [hfun, fderiv_const_smul (hd1.add hd2 |>.sub hd3) (1 / 2 : ℝ),
    fderiv_sub (hd1.add hd2) hd3, fderiv_add hd1 hd2]
  simp only [smul_apply, add_apply, sub_apply]
  rw [Work.Diff.EXT.kz_fderiv_fderiv_apply_coord hA (Work.Diff.EXT.bB (E := E) a)
      (Work.Diff.EXT.bB (E := E) m) b p,
    Work.Diff.EXT.kz_fderiv_fderiv_apply_coord hA (Work.Diff.EXT.bB (E := E) b)
      (Work.Diff.EXT.bB (E := E) m) a p,
    Work.Diff.EXT.kz_fderiv_fderiv_apply_coord hA (Work.Diff.EXT.bB (E := E) p)
      (Work.Diff.EXT.bB (E := E) m) a b]
  simp only [Work.Diff.EXT.jKzD, smul_eq_mul]

/-- **The derivative of the inverse Gram matrix**, in the index convention of `jdInv`:
`∂_m (A ·)⁻¹ = -(A y)⁻¹ (∂_m A) (A y)⁻¹`.
The identity `A y' * (A y')⁻¹ = 1` holds for all `y'` near `y` (`Matrix.mul_nonsing_inv`, using that
the determinant does not vanish near `y`); differentiating its `(i,b)`-entry and solving for the
derivative of the inverse (multiplying the resulting matrix equation by `(A y)⁻¹` on the left) gives
the claim.  The symmetry of `(A y)⁻¹` (`hsym`) is what turns the result into `jdInv`'s index order. -/
theorem fderiv_coPhi_inv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    (A : E → Work.Diff.EXT.MatE (E := E)) (y : E) (m r s : Fin (Module.finrank ℝ E))
    (hA : ContDiffAt ℝ 1 A y)
    (hdet : (Matrix.of (A y)).det ≠ 0)
    (hsym : ∀ i j : Fin (Module.finrank ℝ E), A y i j = A y j i) :
    fderiv ℝ (fun y' : E => Work.Diff.EXT.jInv (A y') r s) y (Work.Diff.EXT.bB (E := E) m)
      = Work.Diff.STE.DeTurck.jdInv (A y) (fderiv ℝ A y) m r s := by
  classical
  have hdA : DifferentiableAt ℝ A y := hA.differentiableAt (by norm_num)
  have hdAc : ∀ i j : Idx E, DifferentiableAt ℝ (fun y' : E => A y' i j) y := by
    intro i j
    exact differentiableAt_pi.mp (differentiableAt_pi.mp hdA i) j
  have hinv_sm : ContDiffAt ℝ 1
      (fun A' : MatE (E := E) => fun i j : Idx E => (Matrix.of A')⁻¹ i j) (A y) :=
    (Work.Diff.EXT.contDiffAt_matrix_inv_pi (A y) hdet).of_le (WithTop.coe_le_coe.mpr le_top)
  have hcomp : ContDiffAt ℝ 1
      (fun y' : E => fun i j : Idx E => (Matrix.of (A y'))⁻¹ i j) y :=
    hinv_sm.comp y hA
  have hdγ : ∀ i j : Idx E, DifferentiableAt ℝ (fun y' : E => jInv (A y') i j) y := by
    intro i j
    have h1 : DifferentiableAt ℝ
        (fun y' : E => fun i j : Idx E => (Matrix.of (A y'))⁻¹ i j) y :=
      hcomp.differentiableAt (by norm_num)
    have h2 := (differentiableAt_pi.mp h1) i
    exact differentiableAt_pi.mp h2 j
  have hdet_cont : ContinuousAt (fun y' : E => (Matrix.of (A y')).det) y :=
    (((Work.Diff.EXT.contDiff_matrix_det_pi (n := Module.finrank ℝ E)).of_le
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp y hA).continuousAt
  have hnear : ∀ᶠ y' in 𝓝 y, (Matrix.of (A y')).det ≠ 0 :=
    hdet_cont.preimage_mem_nhds (isOpen_ne.mem_nhds hdet)
  have hconstM : ∀ᶠ y' in 𝓝 y, Matrix.of (A y') * (Matrix.of (A y'))⁻¹ = 1 := by
    filter_upwards [hnear] with y' hy'
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hy')
  -- ## The key equation: the derivative of the constancy `A · * (A ·)⁻¹ = 1`
  have hkey : ∀ i b : Idx E,
      ∑ j, (fderiv ℝ A y (bB (E := E) m) i j * jInv (A y) j b
        + A y i j * fderiv ℝ (fun y' => jInv (A y') j b) y (bB (E := E) m)) = 0 := by
    intro i b
    have hentry : (fun y' : E => ∑ j, A y' i j * jInv (A y') j b)
        =ᶠ[𝓝 y] fun _ => if i = b then (1 : ℝ) else 0 := by
      filter_upwards [hconstM] with y' hy'
      have h1 := congrFun (congrFun hy' i) b
      rw [Matrix.mul_apply, Matrix.one_apply] at h1
      simpa only [Matrix.of_apply, jInv] using h1
    have hzero : fderiv ℝ (fun y' : E => ∑ j, A y' i j * jInv (A y') j b) y
        (bB (E := E) m) = 0 := by
      rw [hentry.fderiv_eq]
      simp
    have hhd : HasFDerivAt (fun y' : E => ∑ j, A y' i j * jInv (A y') j b)
        (∑ j, ((A y i j) • (fderiv ℝ (fun y' : E => jInv (A y') j b) y)
            + (jInv (A y) j b) • (fderiv ℝ (fun y' : E => A y' i j) y))) y := by
      refine HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => ?_)
      exact (hdAc i j).hasFDerivAt.mul (hdγ j b).hasFDerivAt
    rw [hhd.fderiv] at hzero
    rw [sum_apply] at hzero
    have hval : (∑ j, ((A y i j) • (fderiv ℝ (fun y' : E => jInv (A y') j b) y)
            + (jInv (A y) j b) • (fderiv ℝ (fun y' : E => A y' i j) y)) (bB (E := E) m))
        = ∑ j, (fderiv ℝ A y (bB (E := E) m) i j * jInv (A y) j b
            + A y i j * fderiv ℝ (fun y' => jInv (A y') j b) y (bB (E := E) m)) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [add_apply, smul_apply, smul_eq_mul, fderiv_entry A y m i j hdA]
      ring
    rw [hval] at hzero
    exact hzero
  -- ## The same equation, as a matrix equation
  let X : Matrix (Idx E) (Idx E) ℝ := Matrix.of (fun i j => fderiv ℝ A y (bB (E := E) m) i j)
  let Y : Matrix (Idx E) (Idx E) ℝ :=
    Matrix.of (fun i j => fderiv ℝ (fun y' : E => jInv (A y') i j) y (bB (E := E) m))
  have hmat : X * (Matrix.of (A y))⁻¹ + Matrix.of (A y) * Y = 0 := by
    ext i b
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.zero_apply]
    simp only [X, Y, Matrix.of_apply]
    rw [← Finset.sum_add_distrib]
    simpa only [jInv] using hkey i b
  -- ## Solve for the derivative of the inverse
  have hYeq : Y = -((Matrix.of (A y))⁻¹ * X * (Matrix.of (A y))⁻¹) := by
    have h1 : Matrix.of (A y) * Y = -(X * (Matrix.of (A y))⁻¹) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hmat
    have h3 : (Matrix.of (A y))⁻¹ * (Matrix.of (A y) * Y)
        = -((Matrix.of (A y))⁻¹ * (X * (Matrix.of (A y))⁻¹)) := by
      rw [h1, Matrix.mul_neg]
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul (Matrix.of (A y))
      (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mul] at h3
    exact h3.trans (congrArg Neg.neg (Matrix.mul_assoc _ _ _).symm)
  have hYval : ∀ a b : Idx E, Y a b
      = -∑ i, ∑ j, jInv (A y) a i * fderiv ℝ A y (bB (E := E) m) i j * jInv (A y) j b := by
    intro a b
    rw [hYeq, Matrix.neg_apply]
    congr 1
    rw [Matrix.mul_apply]
    refine Eq.trans (Finset.sum_congr rfl (fun j _ => ?_)) Finset.sum_comm
    rw [Matrix.mul_apply, Finset.sum_mul]
    simp only [X, Matrix.of_apply, jInv]
  -- ## Identify with `jdInv`
  change Y r s = jdInv (A y) (fderiv ℝ A y) m r s
  rw [hYval r s, jdInv]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [PPhiSymm.jInv_symm (A y) hsym j s]
  ring

/-! ## Differentiability of the building blocks -/

/-- The entries of the inverse of a `C^1` family of matrices are differentiable, as long as the
determinant does not vanish. -/
lemma differentiableAt_jInv (A : E → MatE (E := E)) (y : E) (hA : ContDiffAt ℝ 1 A y)
    (hdet : (Matrix.of (A y)).det ≠ 0) (i j : Idx E) :
    DifferentiableAt ℝ (fun y' : E => jInv (A y') i j) y := by
  have hinv_sm : ContDiffAt ℝ 1
      (fun A' : MatE (E := E) => fun i j : Idx E => (Matrix.of A')⁻¹ i j) (A y) :=
    (Work.Diff.EXT.contDiffAt_matrix_inv_pi (A y) hdet).of_le (WithTop.coe_le_coe.mpr le_top)
  have hcomp : ContDiffAt ℝ 1
      (fun y' : E => fun i j : Idx E => (Matrix.of (A y'))⁻¹ i j) y :=
    hinv_sm.comp y hA
  have h1 : DifferentiableAt ℝ
      (fun y' : E => fun i j : Idx E => (Matrix.of (A y'))⁻¹ i j) y :=
    hcomp.differentiableAt (by norm_num)
  have h2 := (differentiableAt_pi.mp h1) i
  exact differentiableAt_pi.mp h2 j

/-- The lowered Koszul pairing of the first jet of a `C^2` family of matrices is differentiable. -/
lemma differentiableAt_jKz (A : E → MatE (E := E)) (y : E) (hA : ContDiffAt ℝ 2 A y)
    (a b p : Idx E) :
    DifferentiableAt ℝ (fun y' : E => jKz (fderiv ℝ A y') a b p) y := by
  have hdA : DifferentiableAt ℝ (fun y' : E => fderiv ℝ A y') y :=
    ((hA.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have hcomp : ∀ v : E, ∀ i j : Idx E,
      DifferentiableAt ℝ (fun y' : E => (fderiv ℝ A y' v) i j) y := by
    intro v i j
    have hc : DifferentiableAt ℝ (fun y' : E => fderiv ℝ A y' v) y :=
      (ContinuousLinearMap.apply ℝ (MatE (E := E)) v).differentiableAt.comp y hdA
    exact differentiableAt_pi.mp (differentiableAt_pi.mp hc i) j
  have hfun : (fun y' : E => jKz (fderiv ℝ A y') a b p)
      = (1 / 2 : ℝ) • (((fun y' : E => (fderiv ℝ A y' (bB (E := E) a)) b p)
            + (fun y' : E => (fderiv ℝ A y' (bB (E := E) b)) a p))
          - (fun y' : E => (fderiv ℝ A y' (bB (E := E) p)) a b)) := by
    funext y'
    simp only [jKz, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact (((hcomp (bB (E := E) a) b p).add (hcomp (bB (E := E) b) a p)).sub
    (hcomp (bB (E := E) p) a b)).const_smul (1 / 2 : ℝ)

/-- The upper Christoffel symbol `coGamU A c a b` is differentiable. -/
lemma differentiableAt_coGamU (A : E → MatE (E := E)) (y : E) (c a b : Idx E)
    (hA : ContDiffAt ℝ 2 A y) (hdet : (Matrix.of (A y)).det ≠ 0) :
    DifferentiableAt ℝ (coGamU A c a b) y := by
  have h1 : ContDiffAt ℝ 1 A y := hA.of_le (by norm_num)
  rw [show coGamU A c a b
      = fun y' : E => ∑ p, jInv (A y') c p * jKz (fderiv ℝ A y') a b p from rfl]
  exact DifferentiableAt.fun_sum (u := Finset.univ)
    (fun p _ => (differentiableAt_jInv A y h1 hdet c p).mul (differentiableAt_jKz A y hA a b p))

/-- **The coordinate derivative of the upper Christoffel symbol.** -/
theorem fderiv_coGamU (A : E → MatE (E := E)) (y : E) (m c a b : Idx E)
    (hA : ContDiffAt ℝ 2 A y) (hdet : (Matrix.of (A y)).det ≠ 0)
    (hsym : ∀ i j : Idx E, A y i j = A y j i) :
    fderiv ℝ (coGamU A c a b) y (bB (E := E) m)
      = jdGamU (A y) (fderiv ℝ A y) (fderiv ℝ (fderiv ℝ A) y) m c a b := by
  have h1 : ContDiffAt ℝ 1 A y := hA.of_le (by norm_num)
  have hhd : HasFDerivAt (coGamU A c a b)
      (∑ p, ((jInv (A y) c p) • (fderiv ℝ (fun y' : E => jKz (fderiv ℝ A y') a b p) y)
        + (jKz (fderiv ℝ A y) a b p) • (fderiv ℝ (fun y' : E => jInv (A y') c p) y))) y := by
    rw [show coGamU A c a b
        = fun y' : E => ∑ p, jInv (A y') c p * jKz (fderiv ℝ A y') a b p from rfl]
    refine HasFDerivAt.fun_sum (u := Finset.univ) (fun p _ => ?_)
    exact (differentiableAt_jInv A y h1 hdet c p).hasFDerivAt.mul
      (differentiableAt_jKz A y hA a b p).hasFDerivAt
  rw [hhd.fderiv]
  simp only [sum_apply, add_apply, smul_apply, smul_eq_mul]
  rw [jdGamU]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [fderiv_coPhi_inv A y m c p h1 hdet hsym, fderiv_coPhi_kz A y m a b p hA]
  ring

/-- The chart expression `coPhi A Ā c` of the DeTurck field is differentiable. -/
lemma differentiableAt_coPhi (A Ā : E → MatE (E := E)) (y : E) (c : Idx E)
    (hA : ContDiffAt ℝ 2 A y) (hĀ : ContDiffAt ℝ 2 Ā y)
    (hdetA : (Matrix.of (A y)).det ≠ 0) (hdetĀ : (Matrix.of (Ā y)).det ≠ 0) :
    DifferentiableAt ℝ (coPhi A Ā c) y := by
  have h1 : ContDiffAt ℝ 1 A y := hA.of_le (by norm_num)
  rw [show coPhi A Ā c
      = fun y' : E => ∑ a, ∑ b,
          jInv (A y') a b * (coGamU A c a b y' - coGamU Ā c a b y') from rfl]
  refine DifferentiableAt.fun_sum (u := Finset.univ) (fun a _ => ?_)
  refine DifferentiableAt.fun_sum (u := Finset.univ) (fun b _ => ?_)
  exact (differentiableAt_jInv A y h1 hdetA a b).mul
    ((differentiableAt_coGamU A y c a b hA hdetA).sub
      (differentiableAt_coGamU Ā y c a b hĀ hdetĀ))

/-- **The coordinate derivative of the DeTurck chart expression**: the derivative of
`coPhi A Ā c` in the direction `bB m` is `jdWU` of the `2`-jets of `A` and `Ā`. -/
theorem fderiv_coPhi (A Ā : E → MatE (E := E)) (y : E) (c m : Idx E)
    (hA : ContDiffAt ℝ 2 A y) (hĀ : ContDiffAt ℝ 2 Ā y)
    (hdetA : (Matrix.of (A y)).det ≠ 0) (hdetĀ : (Matrix.of (Ā y)).det ≠ 0)
    (hsymA : ∀ i j : Idx E, A y i j = A y j i)
    (hsymĀ : ∀ i j : Idx E, Ā y i j = Ā y j i) :
    fderiv ℝ (coPhi A Ā c) y (bB (E := E) m)
      = jdWU (A y) (fderiv ℝ A y) (fderiv ℝ (fderiv ℝ A) y)
          (Ā y) (fderiv ℝ Ā y) (fderiv ℝ (fderiv ℝ Ā) y) m c := by
  have h1A : ContDiffAt ℝ 1 A y := hA.of_le (by norm_num)
  have h1Ā : ContDiffAt ℝ 1 Ā y := hĀ.of_le (by norm_num)
  have hhd : HasFDerivAt (coPhi A Ā c)
      (∑ a, ∑ b, ((jInv (A y) a b)
            • (fderiv ℝ (coGamU A c a b - coGamU Ā c a b) y)
          + (coGamU A c a b y - coGamU Ā c a b y)
            • (fderiv ℝ (fun y' : E => jInv (A y') a b) y))) y := by
    rw [show coPhi A Ā c
        = fun y' : E => ∑ a, ∑ b,
            jInv (A y') a b * (coGamU A c a b y' - coGamU Ā c a b y') from rfl]
    refine HasFDerivAt.fun_sum (u := Finset.univ) (fun a _ => ?_)
    refine HasFDerivAt.fun_sum (u := Finset.univ) (fun b _ => ?_)
    exact (differentiableAt_jInv A y h1A hdetA a b).hasFDerivAt.mul
      ((differentiableAt_coGamU A y c a b hA hdetA).sub
        (differentiableAt_coGamU Ā y c a b hĀ hdetĀ)).hasFDerivAt
  rw [hhd.fderiv]
  simp only [sum_apply, add_apply, sub_apply, smul_apply, smul_eq_mul]
  rw [jdWU]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [fderiv_sub (differentiableAt_coGamU A y c a b hA hdetA)
      (differentiableAt_coGamU Ā y c a b hĀ hdetĀ),
    fderiv_coPhi_inv A y m a b h1A hdetA hsymA]
  simp only [sub_apply]
  rw [fderiv_coGamU A y m c a b hA hdetA hsymA, fderiv_coGamU Ā y m c a b hĀ hdetĀ hsymĀ]
  simp only [coGamU, Work.Diff.EXT.jGamU]
  ring

end

end Work.Diff.STE.deTurck
