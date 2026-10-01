/-
# ZeroFreeTables/XY/LamPrimeData

Data for the order-2 supremum estimates (`LamPrimeSup`): the auxiliary function
`g = tf72g (4/3)`, the test function `f = tf72f (4/3) = xyT.f`, and the four
oscillatory integrals `Cc, Ec, Bc, Sc` into which `Gfun`/`Hfun` decompose, together
with the auxiliary quantities `Yc, E0c, Esc` and the Laplace transform `Ac` of `g`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XY.LamPrimeDefs
import Submission.Work.ZeroFreeTables.testFn72_defs
import Submission.Work.ZeroFreeTables.tf72conv_eq_f

open DirichletCharacter Complex MeasureTheory
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.XY

open Work.ZeroFreeTables

/-- HB's auxiliary function `g` for `λ = 4/3` (even, supported in `[-3/4,3/4]`). -/
def xyG (x : ℝ) : ℝ := tf72g (4/3) x

/-- HB's test function `f` for `λ = 4/3` (equal to `xyT.f`). -/
def xyFf (x : ℝ) : ℝ := tf72f (4/3) x

lemma xyG_nonneg (x : ℝ) : 0 ≤ xyG x := by
  have h : 0 < (4:ℝ)/3 := by norm_num
  simpa [xyG] using tf72g_nonneg (4/3) h x

lemma xyG_supp (x : ℝ) (hx : 3/4 ≤ |x|) : xyG x = 0 := by
  have h : 0 < (4:ℝ)/3 := by norm_num
  have hx' : 1/(4/3) ≤ |x| := by norm_num at hx ⊢; exact hx
  simpa [xyG] using tf72g_supp (4/3) h x hx'

lemma xyG_even (x : ℝ) : xyG (-x) = xyG x := by
  simpa [xyG] using tf72g_even (4/3) x

lemma xyG_cont : Continuous xyG := by
  change Continuous (tf72g (4/3))
  exact tf72g_cont (4/3)

lemma xyG_eq_poly (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) (3/4)) :
    xyG x = (4/3) * (1 - (16/9) * x^2) := by
  unfold xyG tf72g
  rw [max_eq_right]
  · ring
  · nlinarith [hx.1, hx.2]

/-- `f = xyT.f`. -/
lemma xyFf_eq_testFn : xyFf = xyT.f := rfl

lemma xyFf_nonneg (x : ℝ) : 0 ≤ xyFf x := by
  have h : 0 < (4:ℝ)/3 := by norm_num
  simpa [xyFf] using tf72f_nonneg (4/3) h x

lemma xyFf_supp (x : ℝ) (hx : 3/2 ≤ x) : xyFf x = 0 := by
  have h : 0 < (4:ℝ)/3 := by norm_num
  have hx' : 2/(4/3) ≤ x := by norm_num at hx ⊢; exact hx
  simpa [xyFf] using tf72f_supp (4/3) h x hx'

lemma xyFf_eq_poly (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) (3/2)) :
    xyFf x = (2/45) * (2 - (4/3)*x)^3 * (4 + 8*x + (16/9)*x^2) := by
  have h : 0 < (4:ℝ)/3 := by norm_num
  have hx' : x ∈ Set.Icc (0:ℝ) (2/(4/3)) := by norm_num at hx ⊢; exact hx
  have h2 := tf72f_eq_poly (4/3) h x hx'
  rw [xyFf, h2]
  ring

/-- `C(t) = ∫₀^{3/4} g(x) cos(tx) dx`. -/
def Cc (t : ℝ) : ℝ := ∫ x in (0:ℝ)..(3/4), xyG x * Real.cos (t*x)

/-- `E(λ,t) = ∫₀^{3/4} g(x)(cosh(λx) - 1)cos(tx) dx`. -/
def Ec (lam t : ℝ) : ℝ := ∫ x in (0:ℝ)..(3/4), xyG x * (Real.cosh (lam*x) - 1) * Real.cos (t*x)

/-- `B(λ,t) = ∫₀^{3/4} g(x) sinh(λx) sin(tx) dx`. -/
def Bc (lam t : ℝ) : ℝ := ∫ x in (0:ℝ)..(3/4), xyG x * Real.sinh (lam*x) * Real.sin (t*x)

/-- `S(λ,t) = ∫₀^{3/2} sinh(λx) cos(tx) f(x) dx`. -/
def Sc (lam t : ℝ) : ℝ := ∫ x in (0:ℝ)..(3/2), Real.sinh (lam*x) * Real.cos (t*x) * xyFf x

/-- `Y(t) = ∫₀^{3/2} x cos(tx) f(x) dx`. -/
def Yc (t : ℝ) : ℝ := ∫ x in (0:ℝ)..(3/2), x * Real.cos (t*x) * xyFf x

/-- `E₀(λ) = ∫₀^{3/4} g(x)(cosh(λx) - 1) dx`. -/
def E0c (lam : ℝ) : ℝ := ∫ x in (0:ℝ)..(3/4), xyG x * (Real.cosh (lam*x) - 1)

/-- `Eₛ(λ) = ∫₀^{3/2} (sinh(λx) - λx) f(x) dx`. -/
def Esc (lam : ℝ) : ℝ := ∫ x in (0:ℝ)..(3/2), (Real.sinh (lam*x) - lam*x) * xyFf x

/-- `A(z) = ∫_ℝ g(x) e^{-zx} dx` (the Laplace transform of the even function `g`). -/
def Ac (z : ℂ) : ℂ := ∫ x : ℝ, ((xyG x : ℝ) : ℂ) * Complex.exp (-(z * (x : ℂ)))

end Work.ZeroFreeTables.XY
