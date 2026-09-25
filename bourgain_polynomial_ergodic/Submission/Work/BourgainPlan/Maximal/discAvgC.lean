import Mathlib
import Submission.Work.BourgainPlan.Maximal.foundations

/-!
# The complex-valued density average, and the difference operators of the dyadic scales

`Submission.BourgainPlan.discAvg P N g n = Σ_j polyKernel P N j · g (n+j)` is defined for real
`g`.  The Marcinkiewicz–Zygmund square-function lemma
(`Work.BourgainPlan.IonescuWainger.mz_square_function`) — the step that converts a *square function*
into a *signed sum*, which is the form in which the Ionescu–Wainger theorem is available — is stated
for `ℂ`-valued functions and `IsLinearMap ℂ`.  This file provides the `ℂ`-linear extension
`discAvgC` of the density average, its agreement with `discAvg` on real-valued input, and the
`ℂ`-linearity of the **difference operators** `D_{l,m} = discAvgC P N_{m+1} − discAvgC P N_m` of two
consecutive dyadic scales.

The difference operators are the objects to which the signed-sum (Ionescu–Wainger) hypothesis is
applied: for a family of scales `N_0 < N_1 < … < N_{M-1}`, the level square function
`(Σ_{m<M} ‖D_m f‖²)^{1/2}` is bounded in `Lᵠ` by `C·A·‖f‖_{Lᵠ}` (`C` absolute, `A` the constant of
the uniform-in-signs bound `Σ_m ω_m D_m`) — uniformly in `M` and in the choice of scales.  That is
Kosz–Mirek–Słomian–Zhang §5.1 Step 1 (their condition (2) + Khintchine + Theorem 1.9), and it is the
step that produces the `log log N₀` loss of Bourgain's (7.35) as the *number of levels* of the
Rademacher–Menshov inequality.
-/

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators

set_option autoImplicit false

noncomputable section

/-- The complex-valued polynomial density average `Σ_j k_N(j) · g (n+j)`: the `ℂ`-linear extension
of `discAvg` (the coefficients `polyKernel P N j` are real). -/
def discAvgC (P : Polynomial ℤ) (N : ℕ) (g : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (Submission.polySupport P N),
    (Submission.polyKernel P N j : ℂ) * g (n + j)

lemma discAvgC_add (P : Polynomial ℤ) (N : ℕ) (f g : ℕ → ℂ) :
    discAvgC P N (f + g) = discAvgC P N f + discAvgC P N g := by
  funext n
  simp only [discAvgC, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma discAvgC_smul (P : Polynomial ℤ) (N : ℕ) (c : ℂ) (g : ℕ → ℂ) :
    discAvgC P N (c • g) = c • discAvgC P N g := by
  funext n
  simp only [discAvgC, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- `discAvgC` agrees with the real density average `discAvg` on real-valued input. -/
lemma discAvgC_ofReal (P : Polynomial ℤ) (N : ℕ) (g : ℕ → ℝ) (n : ℕ) :
    discAvgC P N (fun k => (g k : ℂ)) n
      = ((Submission.BourgainPlan.discAvg P N g n : ℝ) : ℂ) := by
  simp only [discAvgC, Submission.BourgainPlan.discAvg, Complex.ofReal_sum, Complex.ofReal_mul]

/-- The density average is `ℂ`-linear in its argument. -/
lemma isLinearMap_discAvgC (P : Polynomial ℤ) (N : ℕ) :
    IsLinearMap ℂ (fun g : ℕ → ℂ => discAvgC P N g) :=
  ⟨fun f g => discAvgC_add P N f g, fun c g => discAvgC_smul P N c g⟩

/-- **The difference operator of two consecutive density averages is `ℂ`-linear.**  These are the
operators whose signed sums the Ionescu–Wainger theorem controls. -/
lemma isLinearMap_discAvgC_sub (P : Polynomial ℤ) (N N' : ℕ) :
    IsLinearMap ℂ (fun g : ℕ → ℂ => fun n => discAvgC P N' g n - discAvgC P N g n) := by
  refine ⟨fun f g => ?_, fun c g => ?_⟩
  · funext n
    simp only [Pi.sub_apply, Pi.add_apply, discAvgC_add]
    ring
  · funext n
    simp only [Pi.sub_apply, Pi.smul_apply, discAvgC_smul]
    ring

end

end Work.BourgainPlan.Maximal
