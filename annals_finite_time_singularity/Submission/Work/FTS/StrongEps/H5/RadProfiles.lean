import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FTS.StrongEps.ClassCRHS.StarAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Polynomial

namespace Work.FTS.StrongEps.H5

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The substitution `x = z/(1+z)`

Under `x = z/(1+z)` the operator `D_z = z ∂_z` becomes `x(1-x) ∂_x`: the chain rule gives
`∂_z (F ∘ Xd) = (1+z)^{-2} · (F' ∘ Xd)` and `z (1+z)^{-2} = x(1-x)`.

All three profiles have the shape `z² p(x)/(1+z)³` with `p` a polynomial in `x`, i.e.
`f z = x²(1-x)·r(x)`.  Since `x²(1-x) = z²/(1+z)³`, the whole problem reduces to iterating
the purely polynomial operator `Red r = (2-3x)·r + x(1-x)·r'` on the cofactor `r`, together
with a bound for the (polynomial) cofactors on the compact interval `[0,1]`.
-/

/-- The substitution `x = z/(1+z)`. -/
def Xd (z : ℝ) : ℝ := z / (1 + z)

lemma hasDerivAt_Xd (z : ℝ) (hz : 1 + z ≠ 0) : HasDerivAt Xd (1 / (1 + z) ^ 2) z := by
  have hden : HasDerivAt (fun w : ℝ => 1 + w) 1 z := by
    convert ((hasDerivAt_const z (1 : ℝ)).add (hasDerivAt_id z)) using 1
    · funext w; simp
    · simp
  have h2 : HasDerivAt (fun w : ℝ => w / (1 + w)) (1 / (1 + z) ^ 2) z := by
    have h := (hasDerivAt_id z).div hden (by simpa using hz)
    convert h using 1
    · funext w
      simp [Pi.div_apply]
    · simp only [id_eq]
      field_simp
      ring
  exact h2

lemma Xd_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ Xd z := by
  simp only [Xd]; positivity

lemma Xd_le_one {z : ℝ} (hz : 0 ≤ z) : Xd z ≤ 1 := by
  simp only [Xd]
  rw [div_le_one (by linarith : (0 : ℝ) < 1 + z)]
  linarith

lemma one_sub_Xd (z : ℝ) (hz : 1 + z ≠ 0) : 1 - Xd z = 1 / (1 + z) := by
  simp only [Xd]
  field_simp
  ring

lemma mul_Xd (z : ℝ) (hz : 1 + z ≠ 0) : z * (1 / (1 + z) ^ 2) = Xd z * (1 - Xd z) := by
  simp only [Xd]
  field_simp
  ring

lemma Xd_sq_mul (z : ℝ) (hz : 1 + z ≠ 0) : Xd z ^ 2 * (1 - Xd z) = z ^ 2 / (1 + z) ^ 3 := by
  simp only [Xd]
  field_simp
  ring

/-! ## The polynomial operator `Red` -/

/-- The operator on the cofactor: if `p = X²(1-X)·r`, then `X(1-X)·p' = X²(1-X)·Red r`. -/
def Red (r : ℝ[X]) : ℝ[X] := (C 2 - C 3 * X) * r + X * (1 - X) * r.derivative

/-- The iterates of `Red`. -/
def RedIter : ℕ → ℝ[X] → ℝ[X]
  | 0, r => r
  | k + 1, r => Red (RedIter k r)

@[simp] lemma RedIter_zero (r : ℝ[X]) : RedIter 0 r = r := rfl

@[simp] lemma RedIter_succ (k : ℕ) (r : ℝ[X]) : RedIter (k + 1) r = Red (RedIter k r) := rfl

/-- The commuting square for `Red`: `X(1-X) ∂(X²(1-X)r) = X²(1-X)·Red r`. -/
lemma Red_spec (r : ℝ[X]) (x : ℝ) :
    ((X * (1 - X) * (X ^ 2 * (1 - X) * r).derivative : ℝ[X]).eval x)
      = ((X ^ 2 * (1 - X) * Red r : ℝ[X]).eval x) := by
  simp only [Red, derivative_mul, derivative_sub, derivative_one, derivative_X, derivative_X_pow,
    derivative_C, derivative_ofNat, eval_mul, eval_sub, eval_add, eval_pow, eval_C, eval_X,
    eval_natCast, eval_zero, eval_one]
  ring

/-- One step of the `D_z`-iteration, in the variable `x = z/(1+z)`. -/
lemma Red_step (r : ℝ[X]) (z : ℝ) (hz : 1 + z ≠ 0) :
    z * (((X ^ 2 * (1 - X) * r : ℝ[X]).derivative).eval (Xd z) * (1 / (1 + z) ^ 2))
      = ((X ^ 2 * (1 - X) * Red r : ℝ[X]).eval (Xd z)) := by
  have h1 : z * (((X ^ 2 * (1 - X) * r : ℝ[X]).derivative).eval (Xd z) * (1 / (1 + z) ^ 2))
      = (Xd z * (1 - Xd z)) * ((X ^ 2 * (1 - X) * r : ℝ[X]).derivative).eval (Xd z) := by
    calc z * (((X ^ 2 * (1 - X) * r : ℝ[X]).derivative).eval (Xd z) * (1 / (1 + z) ^ 2))
        = (z * (1 / (1 + z) ^ 2)) * ((X ^ 2 * (1 - X) * r : ℝ[X]).derivative).eval (Xd z) :=
          by ring
      _ = (Xd z * (1 - Xd z)) * ((X ^ 2 * (1 - X) * r : ℝ[X]).derivative).eval (Xd z) := by
          rw [mul_Xd z hz]
  have h2 : (Xd z * (1 - Xd z)) * ((X ^ 2 * (1 - X) * r : ℝ[X]).derivative).eval (Xd z)
      = ((X * (1 - X) * (X ^ 2 * (1 - X) * r).derivative : ℝ[X]).eval (Xd z)) := by
    simp only [eval_mul, eval_sub, eval_X, eval_one]
  rw [h1, h2, Red_spec r (Xd z)]

/-- **The `D_z`-iterates of a profile in the variable `x = z/(1+z)`.**  If `f z = p(x)` with
`p = X²(1-X)·r`, then `D_z^i f z = (X²(1-X)·RedIter i r)(x)`. -/
theorem DzdIter_Red (i : ℕ) (r : ℝ[X]) (z : ℝ) (hz : 1 + z ≠ 0) :
    Work.Elliptic.DzdIter i (fun w => ((X ^ 2 * (1 - X) * r : ℝ[X]).eval (Xd w))) z
      = ((X ^ 2 * (1 - X) * RedIter i r : ℝ[X]).eval (Xd z)) := by
  induction i generalizing z with
  | zero => simp only [Work.Elliptic.DzdIter_zero, RedIter_zero]
  | succ k ih =>
      have hz' : z ≠ -1 := by intro h; exact hz (by linarith)
      have hev : Work.Elliptic.DzdIter k
            (fun w => ((X ^ 2 * (1 - X) * r : ℝ[X]).eval (Xd w)))
          =ᶠ[𝓝 z] fun w => ((X ^ 2 * (1 - X) * RedIter k r : ℝ[X]).eval (Xd w)) := by
        filter_upwards [eventually_ne_nhds hz'] with w hw
        exact ih w (by intro h; exact hw (by linarith))
      have hcomp : HasDerivAt
          (fun w => ((X ^ 2 * (1 - X) * RedIter k r : ℝ[X]).eval (Xd w)))
          (((X ^ 2 * (1 - X) * RedIter k r : ℝ[X]).derivative).eval (Xd z)
            * (1 / (1 + z) ^ 2)) z :=
        (Polynomial.hasDerivAt (X ^ 2 * (1 - X) * RedIter k r) (Xd z)).comp z
          (hasDerivAt_Xd z hz)
      rw [show Work.Elliptic.DzdIter (k + 1)
            (fun w => ((X ^ 2 * (1 - X) * r : ℝ[X]).eval (Xd w))) z
            = z * deriv (Work.Elliptic.DzdIter k
                (fun w => ((X ^ 2 * (1 - X) * r : ℝ[X]).eval (Xd w)))) z from rfl,
        hev.deriv_eq, hcomp.deriv, Red_step (RedIter k r) z hz]
      rfl

/-! ## Congruence of `D_z`-iterates on open sets -/

/-- The `D_z`-iterates agree on an open set on which the functions agree. -/
lemma DzdIter_congr_of_eqOn {f g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (h : Set.EqOn f g U)
    (i : ℕ) : Set.EqOn (Work.Elliptic.DzdIter i f) (Work.Elliptic.DzdIter i g) U := by
  induction i with
  | zero => simpa using h
  | succ k ih =>
      intro z hz
      have hev : Work.Elliptic.DzdIter k f =ᶠ[𝓝 z] Work.Elliptic.DzdIter k g := by
        filter_upwards [hU.mem_nhds hz] with w hw
        exact ih hw
      simp only [Work.Elliptic.DzdIter_succ, Work.Elliptic.Dzd]
      rw [hev.deriv_eq]

/-! ## The three profiles in the variable `x = z/(1+z)`

* `SR0 z = 2z²/(1+z)³ = x²(1-x)·2`,
* `SR2 z = 2z²(1-z)/(1+z)⁴ = x²(1-x)·(2-4x)`,
* `hKer z ^ 2 = z²/(1+z)⁴ = x²(1-x)·(1-x)`. -/

lemma SR0_eq (z : ℝ) (hz : 1 + z ≠ 0) :
    Work.FTS.StrongEps.ClassCRHS.SR0 z
      = ((X ^ 2 * (1 - X) * (C 2) : ℝ[X]).eval (Xd z)) := by
  simp only [Work.FTS.StrongEps.ClassCRHS.SR0, Xd, eval_mul, eval_sub, eval_pow, eval_X,
    eval_one, eval_C]
  field_simp
  ring

lemma SR2_eq (z : ℝ) (hz : 1 + z ≠ 0) :
    Work.FTS.StrongEps.ClassCRHS.SR2 z
      = ((X ^ 2 * (1 - X) * (C 2 - C 4 * X) : ℝ[X]).eval (Xd z)) := by
  simp only [Work.FTS.StrongEps.ClassCRHS.SR2, Xd, eval_mul, eval_sub, eval_pow, eval_X,
    eval_one, eval_C]
  field_simp
  ring

lemma hKer_sq_eq (z : ℝ) (hz : 1 + z ≠ 0) :
    (Work.Spaces.hKer z) ^ 2 = ((X ^ 2 * (1 - X) * (1 - X) : ℝ[X]).eval (Xd z)) := by
  simp only [Work.Spaces.hKer, Xd, eval_mul, eval_sub, eval_pow, eval_X, eval_one, eval_C]
  field_simp
  ring

/-! ## The cofactors are bounded on `[0,1]` -/

/-- For a fixed polynomial cofactor `r`, the six cofactors `RedIter i r` (`i ≤ 5`) are
bounded on `[0,1]` by a common constant: each is a polynomial, hence continuous. -/
lemma RedIter_bound_single (r : ℝ[X]) :
    ∃ C : ℝ, 0 < C ∧ ∀ i : ℕ, i ≤ 5 → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |(RedIter i r).eval x| ≤ C := by
  have hcont : Continuous fun x : ℝ => ∑ j ∈ Finset.range 6, |(RedIter j r).eval x| := by
    refine continuous_finsetSum _ (fun j _ => ?_)
    exact (Polynomial.continuous (RedIter j r)).abs
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hcont.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 (by norm_num))
  refine ⟨C + 1, by linarith, fun i hi x hx => ?_⟩
  have hsum_nonneg : 0 ≤ ∑ j ∈ Finset.range 6, |(RedIter j r).eval x| :=
    Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hCx : (∑ j ∈ Finset.range 6, |(RedIter j r).eval x|) ≤ C := by
    have := hC x hx
    rwa [Real.norm_eq_abs, abs_of_nonneg hsum_nonneg] at this
  have hi6 : i ∈ Finset.range 6 := Finset.mem_range.mpr (by omega)
  have hsingle := Finset.single_le_sum (s := Finset.range 6) (a := i)
    (f := fun j => |(RedIter j r).eval x|) (fun j _ => abs_nonneg _) hi6
  linarith

/-- The cofactors of the three profiles are bounded by a common constant on `[0,1]`. -/
lemma RedIter_bound :
    ∃ K : ℝ, 0 < K ∧
      (∀ i : ℕ, i ≤ 5 → ∀ x ∈ Set.Icc (0 : ℝ) 1, |(RedIter i (C 2 : ℝ[X])).eval x| ≤ K) ∧
      (∀ i : ℕ, i ≤ 5 → ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |(RedIter i (C 2 - C 4 * X : ℝ[X])).eval x| ≤ K) ∧
      (∀ i : ℕ, i ≤ 5 → ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |(RedIter i (1 - X : ℝ[X])).eval x| ≤ K) := by
  obtain ⟨C1, h1pos, h1⟩ := RedIter_bound_single (C 2 : ℝ[X])
  obtain ⟨C2, h2pos, h2⟩ := RedIter_bound_single (C 2 - C 4 * X : ℝ[X])
  obtain ⟨C3, h3pos, h3⟩ := RedIter_bound_single (1 - X : ℝ[X])
  have hKpos : 0 < max (max C1 C2) C3 + 1 := by
    linarith [h1pos, le_max_left C1 C2, le_max_left (max C1 C2) C3]
  refine ⟨max (max C1 C2) C3 + 1, hKpos, ?_, ?_, ?_⟩
  · exact fun i hi x hx => le_trans (h1 i hi x hx)
      (by linarith [le_max_left (max C1 C2) C3, le_max_left C1 C2])
  · exact fun i hi x hx => le_trans (h2 i hi x hx)
      (by linarith [le_max_left (max C1 C2) C3, le_max_right C1 C2])
  · exact fun i hi x hx => le_trans (h3 i hi x hx)
      (by linarith [le_max_right (max C1 C2) C3])

/-! ## The main theorem -/

theorem RadProfiles : ∃ C : ℝ, 0 < C ∧
    (∀ i : ℕ, i ≤ 5 → ∀ z : ℝ, 0 ≤ z →
      |Work.Elliptic.DzdIter i Work.FTS.StrongEps.ClassCRHS.SR0 z| ≤ C * z ^ 2 / (1 + z) ^ 3) ∧
    (∀ i : ℕ, i ≤ 5 → ∀ z : ℝ, 0 ≤ z →
      |Work.Elliptic.DzdIter i Work.FTS.StrongEps.ClassCRHS.SR2 z| ≤ C * z ^ 2 / (1 + z) ^ 3) ∧
    (∀ i : ℕ, i ≤ 5 → ∀ z : ℝ, 0 ≤ z →
      |Work.Elliptic.DzdIter i (fun z => (Work.Spaces.hKer z) ^ 2) z|
        ≤ C * z ^ 2 / (1 + z) ^ 3) := by
  obtain ⟨M, hMpos, hM1, hM2, hM3⟩ := RedIter_bound
  refine ⟨M, hMpos, ?_, ?_, ?_⟩
  · intro i hi z hz
    have hz1 : 1 + z ≠ 0 := by positivity
    have hzU : z ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi]; linarith
    have heq : Work.Elliptic.DzdIter i Work.FTS.StrongEps.ClassCRHS.SR0 z
        = Work.Elliptic.DzdIter i
            (fun w => ((X ^ 2 * (1 - X) * (C 2) : ℝ[X]).eval (Xd w))) z :=
      DzdIter_congr_of_eqOn isOpen_Ioi (fun w hw => by
        simp only [Set.mem_Ioi] at hw
        exact SR0_eq w (by intro h; linarith)) i hzU
    rw [heq, DzdIter_Red i (C 2) z hz1]
    have hmem : Xd z ∈ Set.Icc (0 : ℝ) 1 := ⟨Xd_nonneg hz, Xd_le_one hz⟩
    have hb := hM1 i hi (Xd z) hmem
    have hnn : 0 ≤ Xd z ^ 2 * (1 - Xd z) := by nlinarith [sq_nonneg (Xd z), Xd_le_one hz]
    have hfac : ((X ^ 2 * (1 - X) * RedIter i (C 2) : ℝ[X]).eval (Xd z))
        = Xd z ^ 2 * (1 - Xd z) * (RedIter i (C 2 : ℝ[X])).eval (Xd z) := by
      simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one]
    rw [hfac, abs_mul, abs_of_nonneg hnn]
    calc Xd z ^ 2 * (1 - Xd z) * |(RedIter i (C 2 : ℝ[X])).eval (Xd z)|
        ≤ Xd z ^ 2 * (1 - Xd z) * M := mul_le_mul_of_nonneg_left hb hnn
      _ = M * z ^ 2 / (1 + z) ^ 3 := by rw [Xd_sq_mul z hz1]; ring
  · intro i hi z hz
    have hz1 : 1 + z ≠ 0 := by positivity
    have hzU : z ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi]; linarith
    have heq : Work.Elliptic.DzdIter i Work.FTS.StrongEps.ClassCRHS.SR2 z
        = Work.Elliptic.DzdIter i
            (fun w => ((X ^ 2 * (1 - X) * (C 2 - C 4 * X) : ℝ[X]).eval (Xd w))) z :=
      DzdIter_congr_of_eqOn isOpen_Ioi (fun w hw => by
        simp only [Set.mem_Ioi] at hw
        exact SR2_eq w (by intro h; linarith)) i hzU
    rw [heq, DzdIter_Red i (C 2 - C 4 * X) z hz1]
    have hmem : Xd z ∈ Set.Icc (0 : ℝ) 1 := ⟨Xd_nonneg hz, Xd_le_one hz⟩
    have hb := hM2 i hi (Xd z) hmem
    have hnn : 0 ≤ Xd z ^ 2 * (1 - Xd z) := by nlinarith [sq_nonneg (Xd z), Xd_le_one hz]
    have hfac : ((X ^ 2 * (1 - X) * RedIter i (C 2 - C 4 * X) : ℝ[X]).eval (Xd z))
        = Xd z ^ 2 * (1 - Xd z) * (RedIter i (C 2 - C 4 * X : ℝ[X])).eval (Xd z) := by
      simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one]
    rw [hfac, abs_mul, abs_of_nonneg hnn]
    calc Xd z ^ 2 * (1 - Xd z) * |(RedIter i (C 2 - C 4 * X : ℝ[X])).eval (Xd z)|
        ≤ Xd z ^ 2 * (1 - Xd z) * M := mul_le_mul_of_nonneg_left hb hnn
      _ = M * z ^ 2 / (1 + z) ^ 3 := by rw [Xd_sq_mul z hz1]; ring
  · intro i hi z hz
    have hz1 : 1 + z ≠ 0 := by positivity
    have hzU : z ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi]; linarith
    have heq : Work.Elliptic.DzdIter i (fun z => (Work.Spaces.hKer z) ^ 2) z
        = Work.Elliptic.DzdIter i
            (fun w => ((X ^ 2 * (1 - X) * (1 - X) : ℝ[X]).eval (Xd w))) z :=
      DzdIter_congr_of_eqOn isOpen_Ioi (fun w hw => by
        simp only [Set.mem_Ioi] at hw
        exact hKer_sq_eq w (by intro h; linarith)) i hzU
    rw [heq, DzdIter_Red i (1 - X) z hz1]
    have hmem : Xd z ∈ Set.Icc (0 : ℝ) 1 := ⟨Xd_nonneg hz, Xd_le_one hz⟩
    have hb := hM3 i hi (Xd z) hmem
    have hnn : 0 ≤ Xd z ^ 2 * (1 - Xd z) := by nlinarith [sq_nonneg (Xd z), Xd_le_one hz]
    have hfac : ((X ^ 2 * (1 - X) * RedIter i (1 - X) : ℝ[X]).eval (Xd z))
        = Xd z ^ 2 * (1 - Xd z) * (RedIter i (1 - X : ℝ[X])).eval (Xd z) := by
      simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one]
    rw [hfac, abs_mul, abs_of_nonneg hnn]
    calc Xd z ^ 2 * (1 - Xd z) * |(RedIter i (1 - X : ℝ[X])).eval (Xd z)|
        ≤ Xd z ^ 2 * (1 - Xd z) * M := mul_le_mul_of_nonneg_left hb hnn
      _ = M * z ^ 2 / (1 + z) ^ 3 := by rw [Xd_sq_mul z hz1]; ring

end Work.FTS.StrongEps.H5
