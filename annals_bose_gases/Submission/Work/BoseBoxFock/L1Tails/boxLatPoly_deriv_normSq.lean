import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseBoxFock.L1Tails.boxWave_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.boxLatPoly_deriv_normSq`

The Dirichlet (derivative) companion of `boxLatPoly_normSq`: for the lattice trigonometric
polynomial `P = Σ_{n ∈ S} c n · e^{i⟪κ_n,x⟫}` on the box `boxL ℓ` of side `ℓ`, the
`L²`-norm of the `j`-th derivative is diagonal,

    ∫_{boxL ℓ} ‖∂_j P(x)‖² dx  =  ℓ³ Σ_{n ∈ S} ‖c n‖² ((κ_n)_j)² ,

because the plane waves `e^{i⟪κ_n,x⟫}` at lattice momenta are orthogonal over the box
(`∫_{boxL ℓ} e^{i⟪κ_k,x⟫} = ℓ³ δ_{k,0}` for `k ∈ ℤ³`, the `boxWave_integral` identity).

The proof is the standard `L²` computation: the derivative of the polynomial is again a
trigonometric polynomial with coefficients `i (κ_n)_j c n`; the squared norm is the product
`P'·conj P'` expanded as a double sum, and the orthogonality kills every off-diagonal term.

## Contents

* `latWave_mul`, `latWave_star`, `latWave_mul_star` — the multiplicative structure of the
  plane waves (the star of a plane wave is the plane wave at the opposite frequency);
* `kappaL_sub` — `κ_m − κ_n = κ_{m−n}`, the additivity of the lattice momentum;
* `bpSumLatWaveNormSq` — the pointwise `L²` expansion of `‖Σ A_n e^{i⟪κ_n,x⟫}‖²`;
* `bpIntegralUnitCellCexp`, `bpIntegralUnitCellVec`, `bpSetIntegralSmul`, `bpIntegralBoxL` —
  the orthogonality integral `∫_{boxL ℓ} e^{i⟪κ_k,x⟫} = ℓ³ δ_{k,0}`, proved by scaling to
  the unit cell and the one-dimensional Fourier orthogonality `cos_lattice_1d`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Pointwise

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The multiplicative structure of the plane waves -/

/-- The plane waves are multiplicative in the frequency. -/
lemma latWave_mul (v w : E3) (x : E3) : latWave v x * latWave w x = latWave (v + w) x := by
  simp only [latWave]
  rw [← Complex.exp_add]
  congr 1
  rw [inner_add_left]
  push_cast
  ring

/-- The complex conjugate of a plane wave is the plane wave at the opposite frequency. -/
lemma latWave_star (v : E3) (x : E3) : (starRingEnd ℂ) (latWave v x) = latWave (-v) x := by
  simp only [latWave]
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal, inner_neg_left]
  push_cast
  ring

/-- `e^{i⟪v,x⟫} conj (e^{i⟪w,x⟫}) = e^{i⟪v−w,x⟫}`: the kernel of the `L²` computation. -/
lemma latWave_mul_star (v w : E3) (x : E3) :
    latWave v x * (starRingEnd ℂ) (latWave w x) = latWave (v - w) x := by
  rw [latWave_star, latWave_mul, sub_eq_add_neg]

/-- The lattice momenta are additive: `κ_m − κ_n = κ_{m−n}`. -/
lemma kappaL_sub (ℓ : ℝ) (m n : Fin 3 → ℤ) :
    kappaL ℓ m - kappaL ℓ n = kappaL ℓ (m - n) := by
  rw [kappaL_eq, kappaL_eq, kappaL_eq, ← smul_sub, Work.BoseB4.vec_sub]
  congr 2

/-! ## 2. The pointwise `L²` expansion -/

/-- **The squared norm of a trigonometric polynomial as a double sum.**  For arbitrary
coefficients `A`,

    ‖Σ_{n ∈ S} A n · e^{i⟪κ_n,x⟫}‖² = Re Σ_{m,n ∈ S} A m · conj (A n) · e^{i⟪κ_m−κ_n,x⟫} .

(The complex double sum is real, and its real part is the squared norm.) -/
lemma bpSumLatWaveNormSq (ℓ : ℝ) (S : Finset (Fin 3 → ℤ)) (A : (Fin 3 → ℤ) → ℂ) (x : E3) :
    ‖∑ n ∈ S, A n * latWave (kappaL ℓ n) x‖ ^ 2
      = (∑ m ∈ S, ∑ n ∈ S,
          (A m * (starRingEnd ℂ) (A n)) * latWave (kappaL ℓ (m - n)) x).re := by
  have hp : ‖∑ n ∈ S, A n * latWave (kappaL ℓ n) x‖ ^ 2
      = ((∑ n ∈ S, A n * latWave (kappaL ℓ n) x)
          * (starRingEnd ℂ) (∑ n ∈ S, A n * latWave (kappaL ℓ n) x)).re := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  rw [hp]
  congr 1
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  have h1 : (A m * latWave (kappaL ℓ m) x) * (starRingEnd ℂ) (A n * latWave (kappaL ℓ n) x)
      = (A m * (starRingEnd ℂ) (A n))
        * (latWave (kappaL ℓ m) x * (starRingEnd ℂ) (latWave (kappaL ℓ n) x)) := by
    rw [map_mul]
    ring
  rw [h1, latWave_mul_star, kappaL_sub]

/-! ## 3. The orthogonality integral `∫_{boxL ℓ} e^{i⟪κ_k,x⟫} = ℓ³ δ_{k,0}` -/

/-- The real inner product of `WithLp.toLp 2 a` with `x` is `∑ i, a i * x i`. -/
lemma bpInnerToLp (a : Fin 3 → ℝ) (x : E3) :
    inner ℝ (WithLp.toLp 2 a) x = ∑ i, a i * x.ofLp i := by
  rw [PiLp.inner_apply]
  simp [mul_comm]

/-- `exp` of a sum is the product of the exponentials: the plane waves factorise over the
coordinates of the unit cube. -/
lemma bpProdCexp (a : Fin 3 → ℝ) (y : Fin 3 → ℝ) :
    (∏ i, Complex.exp (Complex.I * (a i * y i)))
      = Complex.exp (Complex.I * (∑ i, a i * y i)) := by
  rw [← Complex.exp_sum Finset.univ (fun i => Complex.I * ((a i : ℂ) * (y i : ℂ)))]
  congr 1
  push_cast
  rw [← Finset.mul_sum]

/-- **The plane-wave integral over the unit cell, in frequency coordinates.**  The integral
factorises into the product of the one-dimensional integrals
`∫_{-1/2}^{1/2} e^{i aᵢ t} dt`. -/
lemma bpIntegralUnitCellCexp (a : Fin 3 → ℝ) :
    ∫ x in Work.BoseB4.unitCell, latWave (WithLp.toLp 2 a) x
      = ∏ i, ∫ t in Set.Icc (-(1/2) : ℝ) (1/2), Complex.exp (Complex.I * (a i * t)) := by
  calc ∫ x in Work.BoseB4.unitCell, latWave (WithLp.toLp 2 a) x
      = ∫ x in Work.BoseB4.unitCell,
          Complex.exp (Complex.I * (inner ℝ (WithLp.toLp 2 a) x : ℝ)) := rfl
    _ = ∫ x in Work.BoseB4.unitCell,
          Complex.exp (Complex.I * (∑ i, a i * x.ofLp i : ℝ)) := by
          apply setIntegral_congr_fun Work.BoseB4.isClosed_unitCell.measurableSet
          intro x _
          simp only [bpInnerToLp]
    _ = ∫ y in Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-(1/2) : ℝ) (1/2)),
          Complex.exp (Complex.I * (∑ i, a i * y i : ℝ)) := by
          rw [show Work.BoseB4.unitCell = {x : E3 | ∀ i, |x i| ≤ (1/2 : ℝ)} from rfl]
          exact Work.BoseB4.ofLp_unitCell_integral
            (F := fun y : Fin 3 → ℝ => Complex.exp (Complex.I * (∑ i, a i * y i : ℝ)))
    _ = ∫ y in Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-(1/2) : ℝ) (1/2)),
          (∏ i, Complex.exp (Complex.I * (a i * y i))) := by
          apply setIntegral_congr_fun
            (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc))
          intro y _
          exact (bpProdCexp a y).symm
    _ = ∏ i, ∫ t in Set.Icc (-(1/2) : ℝ) (1/2),
          Complex.exp (Complex.I * (a i * t)) :=
          Work.BoseB4.prod_integral_unitCube (fun i t => Complex.exp (Complex.I * (a i * t)))

/-- **Lattice orthogonality on the unit cell**, in the complex exponential form:
`∫_{unitCell} e^{i⟪2πn,x⟫} dx = δ_{n,0}`. -/
lemma bpIntegralUnitCellVec (n : Fin 3 → ℤ) :
    ∫ x in Work.BoseB4.unitCell, latWave (Work.BoseB4.vec n) x
      = if n = 0 then (1 : ℂ) else 0 := by
  rw [show Work.BoseB4.vec n
      = WithLp.toLp 2 (fun i : Fin 3 => 2 * Real.pi * (n i : ℝ)) from rfl]
  rw [bpIntegralUnitCellCexp (fun i : Fin 3 => 2 * Real.pi * (n i : ℝ))]
  have hprod1 : (∏ i : Fin 3, (∫ t in Set.Icc (-(1/2) : ℝ) (1/2),
        Complex.exp (Complex.I * (((2 * Real.pi * (n i : ℝ) : ℝ) : ℂ) * (t : ℂ)))))
      = ∏ i : Fin 3, (if n i = 0 then (1 : ℂ) else 0) := by
    apply Finset.prod_congr rfl
    intro i _
    have hpoint : ∀ t : ℝ,
        Complex.exp (Complex.I * (((2 * Real.pi * (n i : ℝ) : ℝ) : ℂ) * (t : ℂ)))
          = Complex.exp (Complex.I * ((2 * Real.pi * (n i : ℝ)) * t)) := by
      intro t
      congr 1
      push_cast
      ring
    rw [setIntegral_congr_fun measurableSet_Icc (fun t _ => hpoint t)]
    exact Work.BoseB4.cos_lattice_1d (n i)
  rw [hprod1]
  have hlast : (∏ i : Fin 3, (if n i = 0 then (1 : ℂ) else 0))
      = (if n = 0 then (1 : ℂ) else 0) := by
    by_cases hn : n = 0
    · subst hn; simp
    · rw [if_neg hn]
      obtain ⟨i, hi⟩ : ∃ i : Fin 3, n i ≠ 0 := by
        by_contra h; push Not at h; exact hn (funext h)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  rw [hlast]

/-- **The scaling identity for set integrals.**  For `ℓ > 0`,
`∫_{ℓ·s} f = ℓ³ ∫_s f(ℓ·)`. -/
lemma bpSetIntegralSmul {ℓ : ℝ} (hℓ : 0 < ℓ) (f : E3 → ℂ) (s : Set E3) :
    ∫ x in ℓ • s, f x = ((ℓ ^ 3 : ℝ) : ℂ) * ∫ x in s, f (ℓ • x) := by
  have hsc := MeasureTheory.Measure.setIntegral_comp_smul_of_pos (μ := volume) (f := f) (s := s) hℓ
  rw [finrank_euclideanSpace_fin] at hsc
  rw [hsc, Complex.real_smul, Complex.ofReal_inv, ← mul_assoc,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (pow_ne_zero 3 (ne_of_gt hℓ))), one_mul]

/-- **The orthogonality integral on the box of side `ℓ`:**
`∫_{boxL ℓ} e^{i⟪κ_k,x⟫} dx = ℓ³ δ_{k,0}`. -/
lemma bpIntegralBoxL {ℓ : ℝ} (hℓ : 0 < ℓ) (k : Fin 3 → ℤ) :
    ∫ x in Work.BoseK15.corpusBox.boxL ℓ, latWave (kappaL ℓ k) x
      = if k = 0 then ((ℓ ^ 3 : ℝ) : ℂ) else 0 := by
  have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
  have hkey : ∫ x in Work.BoseB4.unitCell, latWave (kappaL ℓ k) (ℓ • x)
      = if k = 0 then (1 : ℂ) else 0 := by
    have hcongr : (∫ x in Work.BoseB4.unitCell, latWave (kappaL ℓ k) (ℓ • x))
        = ∫ x in Work.BoseB4.unitCell, latWave (Work.BoseB4.vec k) x := by
      apply setIntegral_congr_fun Work.BoseB4.isClosed_unitCell.measurableSet
      intro x _
      simp only [latWave]
      congr 1
      congr 1
      rw [kappaL_eq, real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
        inv_mul_cancel₀ hℓ0, one_mul]
    rw [hcongr, bpIntegralUnitCellVec k]
  have hbox : Work.BoseK15.corpusBox.boxL ℓ = ℓ • Work.BoseB4.unitCell := by
    simp only [Work.BoseB4.BoxData.boxL]
    rfl
  rw [hbox, bpSetIntegralSmul hℓ (fun x => latWave (kappaL ℓ k) x) Work.BoseB4.unitCell, hkey]
  by_cases hk : k = 0 <;> simp [hk]

theorem boxLatPoly_deriv_normSq {ℓ : ℝ} (hℓ : 0 < ℓ) (S : Finset (Fin 3 → ℤ))
    (c : (Fin 3 → ℤ) → ℂ) (j : Fin 3) :
    ∫ x in Work.BoseK15.corpusBox.boxL ℓ,
        ‖fderiv ℝ (Work.BoseBoxFock.L1Tails.latPoly ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      = ℓ ^ 3 * ∑ n ∈ S, ‖c n‖ ^ 2 * ((Work.BoseBoxFock.kappaL ℓ n) j) ^ 2 := by
  set A : (Fin 3 → ℤ) → ℂ := fun n => c n * (Complex.I * (((kappaL ℓ n) j : ℝ) : ℂ)) with hAdef
  -- the derivative of the trigonometric polynomial is again a trigonometric polynomial
  have hderiv : ∀ x : E3,
      fderiv ℝ (latPoly ℓ S c) x (EuclideanSpace.single j (1 : ℝ))
        = ∑ n ∈ S, A n * latWave (kappaL ℓ n) x := by
    intro x
    rw [fderiv_latPoly_apply]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [inner_single_right_eq]
    simp only [hAdef]
    ring
  -- pointwise: the squared norm as a double sum
  have hpt : ∀ x : E3,
      ‖fderiv ℝ (latPoly ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        = (∑ m ∈ S, ∑ n ∈ S,
            (A m * (starRingEnd ℂ) (A n)) * latWave (kappaL ℓ (m - n)) x).re := by
    intro x
    rw [hderiv x]
    exact bpSumLatWaveNormSq ℓ S A x
  set G : E3 → ℂ := fun x => ∑ m ∈ S, ∑ n ∈ S,
      (A m * (starRingEnd ℂ) (A n)) * latWave (kappaL ℓ (m - n)) x with hGdef
  have hGcont : Continuous G := by
    rw [hGdef]
    refine continuous_finsetSum S fun m _ => continuous_finsetSum S fun n _ => ?_
    exact continuous_const.mul ((latWave_contDiff (kappaL ℓ (m - n))).continuous)
  have hGint : IntegrableOn G (Work.BoseK15.corpusBox.boxL ℓ) volume :=
    hGcont.continuousOn.integrableOn_compact (Work.BoseK15.corpusBox.boxL_compact ℓ)
  have hIntOut : ∀ m : Fin 3 → ℤ, IntegrableOn
      (fun x : E3 => ∑ n ∈ S, (A m * (starRingEnd ℂ) (A n)) * latWave (kappaL ℓ (m - n)) x)
      (Work.BoseK15.corpusBox.boxL ℓ) volume := by
    intro m
    refine (continuous_finsetSum S fun n _ => ?_).continuousOn.integrableOn_compact
      (Work.BoseK15.corpusBox.boxL_compact ℓ)
    exact continuous_const.mul ((latWave_contDiff (kappaL ℓ (m - n))).continuous)
  have hIntIn : ∀ m n : Fin 3 → ℤ, IntegrableOn
      (fun x : E3 => (A m * (starRingEnd ℂ) (A n)) * latWave (kappaL ℓ (m - n)) x)
      (Work.BoseK15.corpusBox.boxL ℓ) volume := by
    intro m n
    exact (continuous_const.mul
        ((latWave_contDiff (kappaL ℓ (m - n))).continuous)).continuousOn.integrableOn_compact
      (Work.BoseK15.corpusBox.boxL_compact ℓ)
  have hstep1 : ∫ x in Work.BoseK15.corpusBox.boxL ℓ,
        ‖fderiv ℝ (latPoly ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      = ∫ x in Work.BoseK15.corpusBox.boxL ℓ, (G x).re := by
    apply setIntegral_congr_fun (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)
    intro x _
    exact hpt x
  have hstep2 : ∫ x in Work.BoseK15.corpusBox.boxL ℓ, (G x).re
      = (∫ x in Work.BoseK15.corpusBox.boxL ℓ, G x).re :=
    Work.BoseB4.setIntegral_re (Work.BoseK15.corpusBox.boxL_measurableSet ℓ) G hGint
  have hstep3 : ∫ x in Work.BoseK15.corpusBox.boxL ℓ, G x
      = ∑ m ∈ S, ∑ n ∈ S, (A m * (starRingEnd ℂ) (A n))
          * ∫ x in Work.BoseK15.corpusBox.boxL ℓ, latWave (kappaL ℓ (m - n)) x := by
    rw [hGdef]
    rw [MeasureTheory.integral_finsetSum (μ := volume.restrict (Work.BoseK15.corpusBox.boxL ℓ))
      (s := S)
      (f := fun m x => ∑ n ∈ S, (A m * (starRingEnd ℂ) (A n)) * latWave (kappaL ℓ (m - n)) x)
      (fun m _ => hIntOut m)]
    apply Finset.sum_congr rfl
    intro m _
    rw [MeasureTheory.integral_finsetSum (μ := volume.restrict (Work.BoseK15.corpusBox.boxL ℓ))
      (s := S)
      (f := fun n x => (A m * (starRingEnd ℂ) (A n)) * latWave (kappaL ℓ (m - n)) x)
      (fun n _ => hIntIn m n)]
    apply Finset.sum_congr rfl
    intro n _
    exact MeasureTheory.integral_const_mul _ _
  have hint : ∀ k : Fin 3 → ℤ, ∫ x in Work.BoseK15.corpusBox.boxL ℓ, latWave (kappaL ℓ k) x
      = if k = 0 then ((ℓ ^ 3 : ℝ) : ℂ) else 0 := fun k => bpIntegralBoxL hℓ k
  -- the double sum collapses onto the diagonal
  have hstep4 : (∑ m ∈ S, ∑ n ∈ S, (A m * (starRingEnd ℂ) (A n))
        * ∫ x in Work.BoseK15.corpusBox.boxL ℓ, latWave (kappaL ℓ (m - n)) x)
      = ((ℓ ^ 3 : ℝ) : ℂ) * ((∑ m ∈ S, ‖A m‖ ^ 2 : ℝ) : ℂ) := by
    have hinner : ∀ m ∈ S, (∑ n ∈ S, (A m * (starRingEnd ℂ) (A n))
        * ∫ x in Work.BoseK15.corpusBox.boxL ℓ, latWave (kappaL ℓ (m - n)) x)
        = (A m * (starRingEnd ℂ) (A m)) * ((ℓ ^ 3 : ℝ) : ℂ) := by
      intro m hm
      refine (Finset.sum_eq_single m ?_ ?_).trans ?_
      · intro b _ hbm
        rw [hint (m - b), if_neg (sub_ne_zero.mpr (Ne.symm hbm)), mul_zero]
      · intro hm'
        exact absurd hm hm'
      · rw [hint (m - m), if_pos (sub_self m)]
    rw [Finset.sum_congr rfl hinner]
    have hterm : ∀ m : Fin 3 → ℤ, (A m * (starRingEnd ℂ) (A m)) * ((ℓ ^ 3 : ℝ) : ℂ)
        = ((ℓ ^ 3 : ℝ) : ℂ) * ((‖A m‖ ^ 2 : ℝ) : ℂ) := by
      intro m
      have h1 : A m * (starRingEnd ℂ) (A m) = ((‖A m‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [h1]; ring
    rw [Finset.sum_congr rfl (fun m _ => hterm m), Complex.ofReal_sum, ← Finset.mul_sum]
  have hstep5 : (((ℓ ^ 3 : ℝ) : ℂ) * ((∑ m ∈ S, ‖A m‖ ^ 2 : ℝ) : ℂ)).re
      = ℓ ^ 3 * ∑ m ∈ S, ‖A m‖ ^ 2 := by
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  have hstep6 : ∑ m ∈ S, ‖A m‖ ^ 2 = ∑ n ∈ S, ‖c n‖ ^ 2 * ((kappaL ℓ n) j) ^ 2 := by
    apply Finset.sum_congr rfl
    intro m _
    simp only [hAdef]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_I,
      one_mul, Complex.normSq_ofReal, ← Complex.normSq_eq_norm_sq]
    ring
  rw [hstep1, hstep2, hstep3, hstep4, hstep5, hstep6]

end Work.BoseBoxFock.L1Tails
