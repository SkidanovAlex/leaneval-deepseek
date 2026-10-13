/-
# `Work.FTS.PhiStar.Gegenbauer.gC_ode` — the Gegenbauer differential equation

`gC n = C_n^{(3/2)}` (the Gegenbauer polynomial of order `3/2`, equivalently `P_{n+1}'` with
`P` the Legendre polynomial) satisfies the Gegenbauer equation

  `(1-x²) q'' - 4 x q' + n(n+3) q = 0`.

The proof follows the classical route: from the three-term recurrence

  `(n+2) C_{n+2} = (2n+5) x C_{n+1} - (n+3) C_n`   (`gC_rec`)

one derives *simultaneously*, by two-step induction, the first order ("ladder") relations

  `(D_k)`  `(1-x²) C_k' + k x C_k = (k+2) C_{k-1}`        (k ≥ 1)

and the differential equation itself

  `(M_k)`  `(1-x²) C_k'' - 4x C_k' + k(k+3) C_k = 0`.

The two algebraic identities driving the induction are (relations `R_m` = recurrence at index
`m`, `R'_m` = its derivative, `D_k`, `M_k` as expressions vanishing by hypothesis):

  `(m+3) D_{m+3} = (1-x²)·R'_{m+1} + (2m+7)x·D_{m+2} - (m+4)·D_{m+1} - (m+4)·R_m
                     + (m+3)x·R_{m+1}`

  `(n+2) M_{n+2} = (2n+5)x·M_{n+1} - (n+3)·M_n + 2(2n+5)·D_{n+1}`,

both pure polynomial identities in `x`, `n` and the (derivatives of the) `C_k`, closed below by
`linear_combination` + `ring`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.PhiStar.Gegenbauer

set_option autoImplicit false

/-! ## The three-term recurrence -/

/-- The recurrence for `gC`, multiplied out by `n+2`:
`(n+2) C_{n+2} = (2n+5) x C_{n+1} - (n+3) C_n`. -/
lemma gC_rec (n : ℕ) (x : ℝ) :
    ((n : ℝ) + 2) * gC (n + 2) x
      = (2 * (n : ℝ) + 5) * x * gC (n + 1) x - ((n : ℝ) + 3) * gC n x := by
  have h : ((n : ℝ) + 2) ≠ 0 := by positivity
  rw [show gC (n + 2) = (fun x => (2 * ((n : ℝ) + 5 / 2) * x * gC (n + 1) x
      - ((n : ℝ) + 3) * gC n x) / ((n : ℝ) + 2)) from rfl]
  field_simp

/-! ## Smoothness -/

lemma contDiff_gC : ∀ n : ℕ, ContDiff ℝ 3 (gC n) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [show gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
    exact contDiff_const
  | one =>
    rw [show gC 1 = (fun x : ℝ => 3 * x) from rfl]
    exact contDiff_const.mul contDiff_id
  | more n ih1 ih2 =>
    rw [show gC (n + 2) = (fun x => (2 * ((n : ℝ) + 5 / 2) * x * gC (n + 1) x
      - ((n : ℝ) + 3) * gC n x) / ((n : ℝ) + 2)) from rfl]
    exact (((contDiff_const.mul contDiff_id).mul ih2).sub (contDiff_const.mul ih1)).div_const _

/-! ## The first and second derivatives of the recurrence -/

/-- First derivative of the recurrence, divided form. -/
lemma gC_rec_deriv_div (n : ℕ) :
    deriv (gC (n + 2)) = fun x => (2 * ((n : ℝ) + 5 / 2) * gC (n + 1) x
      + 2 * ((n : ℝ) + 5 / 2) * x * deriv (gC (n + 1)) x
      - ((n : ℝ) + 3) * deriv (gC n) x) / ((n : ℝ) + 2) := by
  funext x
  have hd1 : DifferentiableAt ℝ (gC (n + 1)) x :=
    ((contDiff_gC (n + 1)).differentiable (by norm_num)).differentiableAt
  have hd0 : DifferentiableAt ℝ (gC n) x :=
    ((contDiff_gC n).differentiable (by norm_num)).differentiableAt
  rw [show gC (n + 2) = (fun y => (2 * ((n : ℝ) + 5 / 2) * y * gC (n + 1) y
      - ((n : ℝ) + 3) * gC n y) / ((n : ℝ) + 2)) from rfl]
  rw [deriv_div_const]
  change (deriv ((fun y : ℝ => 2 * ((n : ℝ) + 5 / 2) * y * gC (n + 1) y)
      - (fun y : ℝ => ((n : ℝ) + 3) * gC n y)) x) / ((n : ℝ) + 2) = _
  rw [deriv_sub (by fun_prop) (by fun_prop)]
  change (deriv ((fun y : ℝ => 2 * ((n : ℝ) + 5 / 2) * y) * gC (n + 1)) x
      - deriv (fun y : ℝ => ((n : ℝ) + 3) * gC n y) x) / ((n : ℝ) + 2) = _
  rw [deriv_mul (by fun_prop) hd1]
  change (deriv (fun y : ℝ => 2 * ((n : ℝ) + 5 / 2) * y) x * gC (n + 1) x
      + (fun y : ℝ => 2 * ((n : ℝ) + 5 / 2) * y) x * deriv (gC (n + 1)) x
      - deriv (fun y : ℝ => ((n : ℝ) + 3) * gC n y) x) / ((n : ℝ) + 2) = _
  rw [deriv_const_mul _ hd0]
  rw [show deriv (fun y : ℝ => 2 * ((n : ℝ) + 5 / 2) * y) x = 2 * ((n : ℝ) + 5 / 2) from by
    rw [deriv_const_mul_field]; simp]

/-- First derivative of the recurrence, multiplied form. -/
lemma gC_rec_deriv (n : ℕ) (x : ℝ) :
    ((n : ℝ) + 2) * deriv (gC (n + 2)) x = (2 * (n : ℝ) + 5) * gC (n + 1) x
      + (2 * (n : ℝ) + 5) * x * deriv (gC (n + 1)) x
      - ((n : ℝ) + 3) * deriv (gC n) x := by
  have h : ((n : ℝ) + 2) ≠ 0 := by positivity
  have hd := congrFun (gC_rec_deriv_div n) x
  rw [hd]
  field_simp

/-- Second derivative of the recurrence, divided form. -/
lemma gC_rec_deriv2_div (n : ℕ) :
    deriv (deriv (gC (n + 2))) = fun x =>
      (2 * (2 * ((n : ℝ) + 5 / 2)) * deriv (gC (n + 1)) x
        + 2 * ((n : ℝ) + 5 / 2) * x * deriv (deriv (gC (n + 1))) x
        - ((n : ℝ) + 3) * deriv (deriv (gC n)) x) / ((n : ℝ) + 2) := by
  rw [gC_rec_deriv_div n]
  funext x
  have hdd1 : DifferentiableAt ℝ (deriv (gC (n + 1))) x :=
    (((ContDiff.deriv' (n := 2) (contDiff_gC (n + 1)))).differentiable
      (by norm_num)).differentiableAt
  have hdd0 : DifferentiableAt ℝ (deriv (gC n)) x :=
    (((ContDiff.deriv' (n := 2) (contDiff_gC n))).differentiable
      (by norm_num)).differentiableAt
  have hcg : HasDerivAt (gC (n + 1)) (deriv (gC (n + 1)) x) x :=
    (((contDiff_gC (n + 1)).differentiable (by norm_num)).differentiableAt).hasDerivAt
  have hlin : HasDerivAt (fun y : ℝ => 2 * ((n : ℝ) + 5 / 2) * y)
      (2 * ((n : ℝ) + 5 / 2)) x := by
    simpa using (hasDerivAt_id x).const_mul (2 * ((n : ℝ) + 5 / 2))
  have h1 : HasDerivAt (fun y : ℝ => (2 * ((n : ℝ) + 5 / 2) * y) * deriv (gC (n + 1)) y)
      (2 * ((n : ℝ) + 5 / 2) * deriv (gC (n + 1)) x
        + (2 * ((n : ℝ) + 5 / 2) * x) * deriv (deriv (gC (n + 1))) x) x :=
    hlin.mul hdd1.hasDerivAt
  have h2 : HasDerivAt (fun y : ℝ => 2 * ((n : ℝ) + 5 / 2) * gC (n + 1) y)
      (2 * ((n : ℝ) + 5 / 2) * deriv (gC (n + 1)) x) x :=
    hcg.const_mul (2 * ((n : ℝ) + 5 / 2))
  have h3 : HasDerivAt (fun y : ℝ => ((n : ℝ) + 3) * deriv (gC n) y)
      (((n : ℝ) + 3) * deriv (deriv (gC n)) x) x :=
    hdd0.hasDerivAt.const_mul ((n : ℝ) + 3)
  have h4 : HasDerivAt (fun y : ℝ =>
      (2 * ((n : ℝ) + 5 / 2) * gC (n + 1) y + (2 * ((n : ℝ) + 5 / 2) * y)
        * deriv (gC (n + 1)) y - ((n : ℝ) + 3) * deriv (gC n) y) / ((n : ℝ) + 2))
      ((2 * ((n : ℝ) + 5 / 2) * deriv (gC (n + 1)) x
        + (2 * ((n : ℝ) + 5 / 2) * deriv (gC (n + 1)) x
          + (2 * ((n : ℝ) + 5 / 2) * x) * deriv (deriv (gC (n + 1))) x)
        - ((n : ℝ) + 3) * deriv (deriv (gC n)) x) / ((n : ℝ) + 2)) x :=
    ((h2.add h1).sub h3).div_const _
  rw [h4.deriv]
  ring

/-- Second derivative of the recurrence, multiplied form. -/
lemma gC_rec_deriv2 (n : ℕ) (x : ℝ) :
    ((n : ℝ) + 2) * deriv (deriv (gC (n + 2))) x = 2 * (2 * (n : ℝ) + 5) * deriv (gC (n + 1)) x
      + (2 * (n : ℝ) + 5) * x * deriv (deriv (gC (n + 1))) x
      - ((n : ℝ) + 3) * deriv (deriv (gC n)) x := by
  have h : ((n : ℝ) + 2) ≠ 0 := by positivity
  have hd := congrFun (gC_rec_deriv2_div n) x
  rw [hd]
  field_simp

/-! ## The two families of relations -/

/-- The first-order ("ladder") relation `D_k`:
`(1-x²) C_k' + k x C_k - (k+2) C_{k-1}`. -/
def Drel (k : ℕ) (x : ℝ) : ℝ :=
  (1 - x ^ 2) * deriv (gC k) x + (k : ℝ) * x * gC k x - ((k : ℝ) + 2) * gC (k - 1) x

/-- The Gegenbauer operator applied to `C_k`:
`(1-x²) C_k'' - 4x C_k' + k(k+3) C_k`. -/
def Mrel (k : ℕ) (x : ℝ) : ℝ :=
  (1 - x ^ 2) * deriv (deriv (gC k)) x - 4 * x * deriv (gC k) x
    + (k : ℝ) * ((k : ℝ) + 3) * gC k x

/-- `D_{m+3}` follows from `D_{m+1}`, `D_{m+2}` and the recurrences. -/
lemma Drel_step (m : ℕ) (x : ℝ) (h1 : Drel (m + 1) x = 0) (h2 : Drel (m + 2) x = 0) :
    Drel (m + 3) x = 0 := by
  have hR1 : ((m : ℝ) + 3) * gC (m + 3) x
      = (2 * (m : ℝ) + 7) * x * gC (m + 2) x - ((m : ℝ) + 4) * gC (m + 1) x := by
    have h := gC_rec (m + 1) x
    push_cast at h
    rw [show (m + 1) + 2 = m + 3 from rfl, show (m + 1) + 1 = m + 2 from rfl] at h
    linear_combination h
  have hR1' : ((m : ℝ) + 3) * deriv (gC (m + 3)) x = (2 * (m : ℝ) + 7) * gC (m + 2) x
      + (2 * (m : ℝ) + 7) * x * deriv (gC (m + 2)) x
      - ((m : ℝ) + 4) * deriv (gC (m + 1)) x := by
    have h := gC_rec_deriv (m + 1) x
    push_cast at h
    rw [show (m + 1) + 2 = m + 3 from rfl, show (m + 1) + 1 = m + 2 from rfl] at h
    linear_combination h
  have hR0 : ((m : ℝ) + 2) * gC (m + 2) x
      = (2 * (m : ℝ) + 5) * x * gC (m + 1) x - ((m : ℝ) + 3) * gC m x := gC_rec m x
  have hkey : ((m : ℝ) + 3) * Drel (m + 3) x = 0 := by
    simp only [Drel, show m + 1 - 1 = m from rfl, show m + 2 - 1 = m + 1 from rfl,
      show m + 3 - 1 = m + 2 from rfl] at h1 h2 ⊢
    push_cast at h1 h2 ⊢
    linear_combination (1 - x ^ 2) * hR1' + (2 * (m : ℝ) + 7) * x * h2 - ((m : ℝ) + 4) * h1
      - ((m : ℝ) + 4) * hR0 + ((m : ℝ) + 3) * x * hR1
  have hpos : ((m : ℝ) + 3) ≠ 0 := by positivity
  exact (mul_eq_zero.mp hkey).resolve_left hpos

/-- `M_{n+2}` follows from `M_n`, `M_{n+1}`, `D_{n+1}` and the recurrences. -/
lemma Mrel_step (n : ℕ) (x : ℝ) (h1 : Mrel (n + 1) x = 0) (h0 : Mrel n x = 0)
    (hd : Drel (n + 1) x = 0) : Mrel (n + 2) x = 0 := by
  have hA1 := gC_rec n x
  have hA2 := gC_rec_deriv n x
  have hA3 := gC_rec_deriv2 n x
  have hkey2 : ((n : ℝ) + 2) * Mrel (n + 2) x - (2 * (n : ℝ) + 5) * x * Mrel (n + 1) x
      + ((n : ℝ) + 3) * Mrel n x - 2 * (2 * (n : ℝ) + 5) * Drel (n + 1) x = 0 := by
    simp only [Mrel, Drel, show n + 1 - 1 = n from rfl] at h1 h0 hd ⊢
    push_cast at h1 h0 hd ⊢
    linear_combination (1 - x ^ 2) * hA3 - 4 * x * hA2 + ((n : ℝ) + 2) * ((n : ℝ) + 5) * hA1
  have hkey : ((n : ℝ) + 2) * Mrel (n + 2) x = 0 := by
    rw [h1, h0, hd] at hkey2
    simpa using hkey2
  exact (mul_eq_zero.mp hkey).resolve_left (by positivity)

/-! ## The two inductions -/

/-- `D_1`: `(1-x²)·3 + x·3x - 3 = 0`. -/
lemma Drel_one (x : ℝ) : Drel 1 x = 0 := by
  have hd1 : deriv (gC 1) x = 3 := by
    rw [show gC 1 = (fun y : ℝ => 3 * y) from rfl, deriv_const_mul_field]
    simp
  simp only [Drel]
  push_cast
  rw [hd1, show gC 1 x = 3 * x from rfl, show gC 0 x = 1 from rfl]
  ring

/-- `D_2`: `(1-x²)·15x + 2x·(15x²-3)/2 - 4·3x = 0`. -/
lemma Drel_two (x : ℝ) : Drel 2 x = 0 := by
  have hd1 : deriv (gC 1) x = 3 := by
    rw [show gC 1 = (fun y : ℝ => 3 * y) from rfl, deriv_const_mul_field]
    simp
  have hd0 : deriv (gC 0) x = 0 := by
    rw [show gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
    simp
  have hd2 : deriv (gC 2) x = 15 * x := by
    have h := congrFun (gC_rec_deriv_div 0) x
    rw [show (0 : ℕ) + 2 = 2 from rfl, show (0 : ℕ) + 1 = 1 from rfl] at h
    rw [h, hd1, hd0]
    simp only [show gC 1 x = 3 * x from rfl]
    norm_num
    ring
  have h2 : gC 2 x = (15 * x ^ 2 - 3) / 2 := by
    simp only [gC]
    norm_num
    ring
  simp only [Drel]
  push_cast
  rw [hd2, h2, show gC 1 x = 3 * x from rfl]
  ring

/-- `Erel m := D_{m+1}`; all of them vanish. -/
def Erel (m : ℕ) (x : ℝ) : ℝ := Drel (m + 1) x

lemma Erel_all : ∀ m : ℕ, ∀ x : ℝ, Erel m x = 0 := by
  intro m
  induction m using Nat.twoStepInduction with
  | zero => intro x; exact Drel_one x
  | one => intro x; exact Drel_two x
  | more m ih1 ih2 => intro x; exact Drel_step m x (ih1 x) (ih2 x)

/-- `M_0`: `C_0 = 1` is constant, so everything but the vanishing terms is `0`. -/
lemma Mrel_zero (x : ℝ) : Mrel 0 x = 0 := by
  have hd0 : deriv (gC 0) x = 0 := by
    rw [show gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
    simp
  have hdd0 : deriv (deriv (gC 0)) x = 0 := by
    rw [show deriv (gC 0) = (fun _ : ℝ => (0 : ℝ)) from by
      rw [show gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
      simp]
    simp
  simp only [Mrel]
  push_cast
  rw [hdd0, hd0, show gC 0 x = 1 from rfl]
  ring

/-- `M_1`: `C_1 = 3x` is linear, giving `-12x + 4·3x = 0`. -/
lemma Mrel_one (x : ℝ) : Mrel 1 x = 0 := by
  have hd1 : deriv (gC 1) x = 3 := by
    rw [show gC 1 = (fun y : ℝ => 3 * y) from rfl, deriv_const_mul_field]
    simp
  have hdd1 : deriv (deriv (gC 1)) x = 0 := by
    rw [show deriv (gC 1) = (fun _ : ℝ => (3 : ℝ)) from by
      funext y
      rw [show gC 1 = (fun y : ℝ => 3 * y) from rfl, deriv_const_mul_field]
      simp]
    simp
  simp only [Mrel]
  push_cast
  rw [hdd1, hd1, show gC 1 x = 3 * x from rfl]
  ring

lemma Mrel_all : ∀ n : ℕ, ∀ x : ℝ, Mrel n x = 0 := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro x; exact Mrel_zero x
  | one => intro x; exact Mrel_one x
  | more n ih1 ih2 => intro x; exact Mrel_step n x (ih2 x) (ih1 x) (Erel_all n x)

/-! ## The target -/

theorem gC_ode (n : ℕ) :
    ContDiff ℝ 3 (Work.FTS.PhiStar.Gegenbauer.gC n) ∧ ∀ x : ℝ,
      (1 - x ^ 2) * deriv (deriv (Work.FTS.PhiStar.Gegenbauer.gC n)) x
        - 4 * x * deriv (Work.FTS.PhiStar.Gegenbauer.gC n) x
        + (n : ℝ) * ((n : ℝ) + 3) * Work.FTS.PhiStar.Gegenbauer.gC n x = 0 := by
  refine ⟨contDiff_gC n, fun x => ?_⟩
  simpa only [Mrel] using Mrel_all n x

end Work.FTS.PhiStar.Gegenbauer
