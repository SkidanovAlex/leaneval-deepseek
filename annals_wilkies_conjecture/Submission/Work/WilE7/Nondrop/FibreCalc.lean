/-
  Area E7 (non-drop frontier step): the fibre calculus of a `Good` stratum.

  For a stratum `S : Stratum p q` and a base point `x : Fin p → ℝ` we collect the basic facts
  about the *fibre map*

      `fnpFibre S x : (Fin q → ℝ) → (Fin S.j → ℝ)`,  `y ↦ (a ↦ eaEval S.X.c (S.h a) (x, y))`,

  namely analyticity, the identification of its derivative with the `pi` of the fibrewise
  Jacobian rows, the resulting surjectivity of the derivative at points where the Jacobian has
  full row rank, the rank–nullity consequences, and the two elementary consequences of
  `Stratum.Good` (the fibre map vanishes on the fibre, and the fibre level set of `S'` is
  contained in the fibre level set of `S` near a point of `S'` when `S'` lies in the fibrewise
  frontier of `S`).
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE5.Basic
import Submission.Work.WilE5.Strat.flatConormalTools
import Submission.Work.WilE9.Ift.AppendCLM

set_option autoImplicit false

noncomputable section
open Classical Filter Topology
open scoped Topology
namespace Work.WilE7.Nondrop

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- `z` is the gluing of its first `p` and its last `q` coordinates. -/
theorem fnpAppend_proj {p q : ℕ} (z : Fin (p + q) → ℝ) :
    Fin.append (projFirst p q z) (projSnd p q z) = z := by
  funext i
  refine Fin.addCases (motive := fun i =>
    Fin.append (projFirst p q z) (projSnd p q z) i = z i) (fun i' => ?_) (fun l => ?_) i <;>
    simp [projFirst, projSnd]

/-- The fibre map of a stratum `S` over the base point `x`. -/
def fnpFibre {p q : ℕ} (S : Stratum p q) (x : Fin p → ℝ) : (Fin q → ℝ) → (Fin S.j → ℝ) :=
  fun y a => eaEval S.X.c (S.h a) (Fin.append x y)

@[simp]
theorem fnpFibre_apply {p q : ℕ} (S : Stratum p q) (x : Fin p → ℝ) (y : Fin q → ℝ)
    (a : Fin S.j) : fnpFibre S x y a = eaEval S.X.c (S.h a) (Fin.append x y) := rfl

/-- **Full row rank of a matrix gives a surjective `pi` of its rows.** -/
theorem fnpRangePiEqTopOfRank {m q : ℕ} (M : Fin m → Fin q → ℝ)
    (hrank : (Matrix.of M).rank = m) :
    (ContinuousLinearMap.pi (fun a : Fin m =>
      (∑ j : Fin q, M a j • (ContinuousLinearMap.proj j : (Fin q → ℝ) →L[ℝ] ℝ)))).range
      = ⊤ := by
  let f : (Fin q → ℝ) →L[ℝ] (Fin m → ℝ) := ContinuousLinearMap.pi (fun a : Fin m =>
      (∑ j : Fin q, M a j • (ContinuousLinearMap.proj j : (Fin q → ℝ) →L[ℝ] ℝ)))
  have hcoe : (f : (Fin q → ℝ) →ₗ[ℝ] (Fin m → ℝ)) = (Matrix.of M).mulVecLin := by
    ext v a
    simp [f, ContinuousLinearMap.coe_pi, LinearMap.pi_apply, Matrix.mulVec, dotProduct]
  show f.range = ⊤
  rw [show f.range = LinearMap.range (f : (Fin q → ℝ) →ₗ[ℝ] (Fin m → ℝ)) from rfl, hcoe]
  apply Submodule.eq_top_of_finrank_eq
  rw [Matrix.rank] at hrank
  rw [hrank]
  simp

/-- A finite sum of multiples of the coordinate projections, evaluated at a vector. -/
theorem fnpSum_smul_proj_apply {k : ℕ} (cs : Fin k → ℝ) (w : Fin k → ℝ) :
    (∑ i : Fin k, cs i • (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)) w
      = ∑ i, cs i * w i := by
  rw [ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => by
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul])

/-- The fibre embedding `y ↦ Fin.append x y` is differentiable, with linear part
`appendCLM p q ∘ inr`. -/
theorem fnpAppend_hasFDerivAt {p q : ℕ} (x : Fin p → ℝ) (y : Fin q → ℝ) :
    HasFDerivAt (fun y' : Fin q → ℝ => Fin.append x y')
      ((Work.WilE9.Ift.appendCLM p q).comp
        (ContinuousLinearMap.inr ℝ (Fin p → ℝ) (Fin q → ℝ))) y := by
  have h1 : HasFDerivAt (fun y' : Fin q → ℝ => (x, y'))
      ((0 : (Fin q → ℝ) →L[ℝ] (Fin p → ℝ)).prod
        (1 : (Fin q → ℝ) →L[ℝ] (Fin q → ℝ))) y :=
    (hasFDerivAt_const x y).prodMk (hasFDerivAt_id (𝕜 := ℝ) y)
  have h2 : ((0 : (Fin q → ℝ) →L[ℝ] (Fin p → ℝ)).prod
        (1 : (Fin q → ℝ) →L[ℝ] (Fin q → ℝ)))
      = ContinuousLinearMap.inr ℝ (Fin p → ℝ) (Fin q → ℝ) := rfl
  rw [h2] at h1
  have h3 := (ContinuousLinearMap.hasFDerivAt (Work.WilE9.Ift.appendCLM p q)).comp y h1
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun y' => ?_)
  simp [Function.comp_apply, Work.WilE9.Ift.appendCLM_apply]

/-- Evaluating the fibre embedding's derivative at a vector. -/
theorem fnpAppend_deriv_apply {p q : ℕ} (x : Fin p → ℝ) (y : Fin q → ℝ) (v : Fin q → ℝ) :
    (((Work.WilE9.Ift.appendCLM p q).comp
      (ContinuousLinearMap.inr ℝ (Fin p → ℝ) (Fin q → ℝ))) v)
      = Fin.append (0 : Fin p → ℝ) v := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    Work.WilE9.Ift.appendCLM_apply]

/-- The single fibre equation `y ↦ eaEval S.X.c (S.h a) (x, y)` is analytic. -/
theorem fnpEval_analytic {p q : ℕ} (S : Stratum p q) (x : Fin p → ℝ) (a : Fin S.j)
    (y : Fin q → ℝ) :
    AnalyticAt ℝ (fun y' : Fin q → ℝ => eaEval S.X.c (S.h a) (Fin.append x y')) y := by
  have happ : AnalyticAt ℝ (fun y' : Fin q → ℝ => Fin.append x y') y := by
    have h1 : (fun y' : Fin q → ℝ => Fin.append x y')
        = (Work.WilE9.Ift.appendCLM p q) ∘ (fun y' : Fin q → ℝ => (x, y')) := by
      funext y'
      simp [Function.comp_apply, Work.WilE9.Ift.appendCLM_apply]
    rw [h1]
    exact ((Work.WilE9.Ift.appendCLM p q).analyticAt (x, y)).comp
      ((analyticAt_const (v := x)).prod (analyticAt_id (z := y)))
  exact (Work.WilE5.Strat.analyticAt_eaEval S.X.c (S.h a) (Fin.append x y)).comp happ

/-- The single fibre equation is continuous. -/
theorem fnpEval_continuous {p q : ℕ} (S : Stratum p q) (x : Fin p → ℝ) (a : Fin S.j) :
    Continuous (fun y' : Fin q → ℝ => eaEval S.X.c (S.h a) (Fin.append x y')) :=
  continuous_iff_continuousAt.mpr fun y => (fnpEval_analytic S x a y).continuousAt

/-- The fibre map of a stratum is analytic. -/
theorem fnpFibre_analytic {p q : ℕ} (S : Stratum p q) (x : Fin p → ℝ) :
    ∀ y, AnalyticAt ℝ (fnpFibre S x) y := by
  intro y
  refine AnalyticAt.pi (fun a => ?_)
  exact fnpEval_analytic S x a y

/-- **The derivative of the fibre map** is the `pi` of the rows of the fibrewise Jacobian. -/
theorem fnpFibre_fderiv {p q : ℕ} (S : Stratum p q) (x : Fin p → ℝ) (y : Fin q → ℝ) :
    fderiv ℝ (fnpFibre S x) y
      = ContinuousLinearMap.pi (fun a : Fin S.j =>
          ∑ l : Fin q, eaEval S.X.c (eaD S.X.c (Work.WilE5.yDir p l) (S.h a)) (Fin.append x y) •
            (ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ)) := by
  classical
  have hG : HasFDerivAt
      (fun w : Fin (p + q) → ℝ => fun a : Fin S.j => eaEval S.X.c (S.h a) w)
      (ContinuousLinearMap.pi (fun a : Fin S.j => ∑ i : Fin (p + q),
        eaEval S.X.c (eaD S.X.c i (S.h a)) (Fin.append x y) •
          (ContinuousLinearMap.proj i : (Fin (p + q) → ℝ) →L[ℝ] ℝ)))
      (Fin.append x y) :=
    hasFDerivAt_pi.mpr fun a =>
      Work.WilE5.Calc.hasFDerivAt_eaEval S.X.c (S.h a) (Fin.append x y)
  have hcomp := hG.comp y (fnpAppend_hasFDerivAt x y)
  have hfun : (fun w : Fin (p + q) → ℝ => fun a : Fin S.j => eaEval S.X.c (S.h a) w)
      ∘ (fun y' : Fin q → ℝ => Fin.append x y') = fnpFibre S x := rfl
  rw [← hfun, hcomp.fderiv]
  ext v a
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.inr_apply, Work.WilE9.Ift.appendCLM_apply, fnpSum_smul_proj_apply]
  rw [Fin.sum_univ_add]
  have hzero : (∑ i : Fin p, eaEval S.X.c (eaD S.X.c (Fin.castAdd q i) (S.h a))
      (Fin.append x y) * (Fin.append (0 : Fin p → ℝ) v) (Fin.castAdd q i)) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [Fin.append_left, Pi.zero_apply, mul_zero]
  rw [hzero, zero_add]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Fin.append_right]
  simp only [Work.WilE5.yDir]

/-- **Surjectivity of the fibre derivative from full row rank of the fibrewise Jacobian.** -/
theorem fnpFibre_range_eq_top_of_rank {p q : ℕ} (S : Stratum p q) (x : Fin p → ℝ)
    (y : Fin q → ℝ)
    (hrank : (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
      eaEval S.X.c (eaD S.X.c (Work.WilE5.yDir p l) (S.h a)) (Fin.append x y)).rank = S.j) :
    (fderiv ℝ (fnpFibre S x) y).range = ⊤ := by
  rw [fnpFibre_fderiv]
  exact fnpRangePiEqTopOfRank
    (fun (a : Fin S.j) (l : Fin q) =>
      eaEval S.X.c (eaD S.X.c (Work.WilE5.yDir p l) (S.h a)) (Fin.append x y)) hrank

/-- Rank–nullity for the fibre derivative: the fibre kernel has dimension `q - S.j`. -/
theorem fnpFinrank_ker {p q : ℕ} (S : Stratum p q) (x : Fin p → ℝ) (y : Fin q → ℝ)
    (htop : (fderiv ℝ (fnpFibre S x) y).range = ⊤) :
    Module.finrank ℝ (fderiv ℝ (fnpFibre S x) y).ker = q - S.j := by
  have h1 : Module.finrank ℝ (fderiv ℝ (fnpFibre S x) y).range
      + Module.finrank ℝ (fderiv ℝ (fnpFibre S x) y).ker
      = Module.finrank ℝ (Fin q → ℝ) :=
    LinearMap.finrank_range_add_finrank_ker
      ((fderiv ℝ (fnpFibre S x) y : (Fin q → ℝ) →L[ℝ] (Fin S.j → ℝ)) :
        (Fin q → ℝ) →ₗ[ℝ] (Fin S.j → ℝ))
  have h2 : Module.finrank ℝ (fderiv ℝ (fnpFibre S x) y).range = S.j := by
    rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card]
    simp
  have h3 : Module.finrank ℝ (Fin q → ℝ) = q := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  omega

/-- The number of equations of a stratum with surjective fibre derivative is at most `q`. -/
theorem fnpRank_le {p q : ℕ} (S : Stratum p q) (x : Fin p → ℝ) (y : Fin q → ℝ)
    (htop : (fderiv ℝ (fnpFibre S x) y).range = ⊤) : S.j ≤ q := by
  have h1 : Module.finrank ℝ (fderiv ℝ (fnpFibre S x) y).range
      ≤ Module.finrank ℝ (Fin q → ℝ) :=
    LinearMap.finrank_range_le
      ((fderiv ℝ (fnpFibre S x) y : (Fin q → ℝ) →L[ℝ] (Fin S.j → ℝ)) :
        (Fin q → ℝ) →ₗ[ℝ] (Fin S.j → ℝ))
  rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card] at h1
  rw [Module.finrank_fintype_fun_eq_card] at h1
  simpa using h1

/-- A `Good` stratum's equations vanish on its fibre. -/
theorem fnpFibre_eq_zero_of_mem {p q : ℕ} (S : Stratum p q) (hGood : S.Good) (x : Fin p → ℝ)
    (y : Fin q → ℝ) (hy : y ∈ fiber S.X.set x) : fnpFibre S x y = 0 :=
  funext fun a => Work.WilE5.Stratum.good_eqs hGood hy a

/-- A `Good` stratum's equations vanish on the closure of its fibre. -/
theorem fnpFibre_eq_zero_of_mem_closure {p q : ℕ} (S : Stratum p q) (hGood : S.Good)
    (x : Fin p → ℝ) (y : Fin q → ℝ) (hy : y ∈ closure (fiber S.X.set x)) :
    fnpFibre S x y = 0 := by
  funext a
  have hclosed : IsClosed {y' : Fin q → ℝ | eaEval S.X.c (S.h a) (Fin.append x y') = 0} :=
    isClosed_eq (fnpEval_continuous S x a) continuous_const
  refine hclosed.closure_subset_iff.mpr (fun y' hy' => ?_) hy
  exact congrFun (fnpFibre_eq_zero_of_mem S hGood x y' hy') a

/-- **The fibre level set of `S'` is contained in that of `S` near the base point**, whenever
`S'.X.set` lies in the fibrewise frontier of `S.X.set`. -/
theorem fnpFibre_eventually {p q : ℕ} (S S' : Stratum p q) (hGood : S.Good) (hGood' : S'.Good)
    (hsub : S'.X.set ⊆ fiberClosure S.X.set \ S.X.set) (x : Fin p → ℝ) (y : Fin q → ℝ)
    (hy : Fin.append x y ∈ S'.X.set) :
    ∀ᶠ y' in nhds y, fnpFibre S' x y' = 0 → fnpFibre S x y' = 0 := by
  have hcont : Tendsto (fun y' : Fin q → ℝ => Fin.append x y') (nhds y)
      (nhds (Fin.append x y)) := (fnpAppend_hasFDerivAt x y).continuousAt
  have hfull := hcont.eventually ((hGood' (Fin.append x y) hy).2.2)
  filter_upwards [hfull] with y' hyfull h0
  have hmem' : Fin.append x y' ∈ S'.X.set := by
    refine hyfull ?_ ?_
    · funext i
      simp [projFirst, Fin.append_left]
    · intro b
      exact congrFun h0 b
  have hfc : Fin.append x y' ∈ fiberClosure S.X.set := (hsub hmem').1
  have hcl : y' ∈ closure (fiber S.X.set x) := by
    have h1 : projFirst p q (Fin.append x y') = x := by
      funext i; simp [projFirst, Fin.append_left]
    have h2 : projSnd p q (Fin.append x y') = y' := by
      funext i; simp [projSnd, Fin.append_right]
    simpa [fiberClosure, h1, h2] using hfc
  exact fnpFibre_eq_zero_of_mem_closure S hGood x y' hcl

end Work.WilE7.Nondrop
