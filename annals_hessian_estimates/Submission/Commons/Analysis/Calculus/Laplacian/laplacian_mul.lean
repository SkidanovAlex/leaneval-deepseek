import Mathlib.Analysis.Calculus.FDeriv.Mul
import Submission.Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials

namespace Commons.Analysis.Calculus.Laplacian

open scoped RealInnerProductSpace InnerProductSpace BigOperators Topology

/-- The second iterated derivative applied twice in the same direction equals the wedge of the
bilinear form `bilinearIteratedFDerivTwo`. -/
private lemma bilinear_apply_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℝ) (x v : E) :
    ((bilinearIteratedFDerivTwo ℝ u x) v) v = (fderiv ℝ (fderiv ℝ u) x) v v := by
  rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv, iteratedFDeriv_two_apply]
  simp

/-- Second-order product rule: the second derivative of a product of two real-valued functions,
evaluated in two directions. -/
private lemma fderiv_fderiv_mul_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (v w : E) :
    (fderiv ℝ (fderiv ℝ (f * g)) x) v w =
      f x * (fderiv ℝ (fderiv ℝ g) x) v w + g x * (fderiv ℝ (fderiv ℝ f) x) v w
        + (fderiv ℝ f x v) * (fderiv ℝ g x w) + (fderiv ℝ g x v) * (fderiv ℝ f x w) := by
  -- first and second derivatives of `f` and `g` at `x`
  have hd2f : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    ((hf.fderiv_right_succ (n := 1)).differentiableAt (by norm_num)).hasFDerivAt
  have hd2g : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) x) x :=
    ((hg.fderiv_right_succ (n := 1)).differentiableAt (by norm_num)).hasFDerivAt
  have hdf : HasFDerivAt f (fderiv ℝ f x) x := (hf.differentiableAt (by norm_num)).hasFDerivAt
  have hdg : HasFDerivAt g (fderiv ℝ g x) x := (hg.differentiableAt (by norm_num)).hasFDerivAt
  -- the derivative of `y ↦ f y • fderiv g y + g y • fderiv f y`
  have h1 : HasFDerivAt (fun y => f y • fderiv ℝ g y)
      (f x • fderiv ℝ (fderiv ℝ g) x + (fderiv ℝ f x).smulRight (fderiv ℝ g x)) x :=
    hdf.smul hd2g
  have h2 : HasFDerivAt (fun y => g y • fderiv ℝ f y)
      (g x • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x)) x :=
    hdg.smul hd2f
  have hΦ : HasFDerivAt (fun y => f y • fderiv ℝ g y + g y • fderiv ℝ f y)
      ((f x • fderiv ℝ (fderiv ℝ g) x + (fderiv ℝ f x).smulRight (fderiv ℝ g x))
        + (g x • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x))) x :=
    h1.add h2
  -- `fderiv (f * g)` agrees near `x` with the above function
  have heq : fderiv ℝ (f * g) =ᶠ[𝓝 x]
      (fun y => f y • fderiv ℝ g y + g y • fderiv ℝ f y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    change fderiv ℝ (fun y => f y * g y) y = f y • fderiv ℝ g y + g y • fderiv ℝ f y
    rw [fderiv_fun_mul (hyf.differentiableAt (by norm_num))
      (hyg.differentiableAt (by norm_num))]
  rw [heq.fderiv_eq, hΦ.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

/-- **Product rule for the Laplacian (Leibniz rule).**
For `C²` functions `f g : E → ℝ` on a finite-dimensional real inner product space and any
orthonormal basis `b`,
`Δ(f * g)(x) = f x * Δg x + g x * Δf x + 2 * ∑ i, (Df x (b i)) * (Dg x (b i))`. -/
theorem laplacian_mul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    Laplacian.laplacian (f * g) x = f x * Laplacian.laplacian g x + g x * Laplacian.laplacian f x
      + 2 * ∑ i, (fderiv ℝ f x) (b i) * (fderiv ℝ g x) (b i) := by
  rw [Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials b (f * g) x,
    Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials b g x,
    Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials b f x]
  have hkey : ∀ i, ((bilinearIteratedFDerivTwo ℝ (f * g) x) (b i)) (b i)
      = f x * ((bilinearIteratedFDerivTwo ℝ g x) (b i)) (b i)
        + g x * ((bilinearIteratedFDerivTwo ℝ f x) (b i)) (b i)
        + 2 * ((fderiv ℝ f x) (b i) * (fderiv ℝ g x) (b i)) := by
    intro i
    have h := fderiv_fderiv_mul_apply hf hg (b i) (b i)
    rw [bilinear_apply_self (f * g) x (b i), bilinear_apply_self g x (b i),
      bilinear_apply_self f x (b i)]
    rw [h]; ring
  rw [Finset.sum_congr rfl (fun i _ => hkey i)]
  simp only [Finset.sum_add_distrib, Finset.mul_sum]

end Commons.Analysis.Calculus.Laplacian