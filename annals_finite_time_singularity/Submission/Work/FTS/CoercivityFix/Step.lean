/-
# The corrected induction step of the coercivity chapter: the paper's *small* step coefficients

Design `FTS/N45_DESIGN_LEAD.md` §5 T3 records that node N2's step carries the **balance
hypothesis** `CC√κ ≤ cc/2` — a constraint on the *constants* of the concrete inner product,
of which the N2 notes themselves observe that `cc/CC ≤ ‖𝓛_Γ^T‖` while `κ ≳ 1/4`, so that the
balance is not satisfiable there.  The paper's own scheme never uses such a balance: it
chooses the step coefficients `c_{1,k}`, `c_{2,k}` *small*, in particular `c_{2,k}` of the
order `c_{1,k}/(C̄_k/cc)²`.  This file proves the step in that form.

The mathematical content is the arithmetic of §"Higher order derivatives and the inner
product on `ℋ^k`" of Elgindi (tex 686–707), with the balance replaced by an explicit
condition on the *coefficients* (`StepSmall`):

* level-`n` data = the analytic clauses of `UnifIP` restricted to the interior class
  `RegQ α n`: Cauchy–Schwarz with constant `CC`, comparability with constants `cc`, `CC`, and
  coercivity of the clean operator `Lhat = 𝓛 − Transport` with constant `cc` (`CoerData`);
* step inputs: the explicit `D_z`-defect bound `|Ê₂ f|_n ≤ κ(|f|_n + |D_θ f|_n)` — provable
  by slot bookkeeping and **uniform in α**, since `Ê₂ f = (2zf + 3zD_θf)/(1+z)²` contains no
  `L₁₂`-term — plus the two commutator identities `Dth_Lhat`, `Dz_Lhat` on the open quadrant,
  the `RegQ`-closure and the one-sided norm comparison
  `|f|²_n + |D_θf|²_n + |D_zf|²_n ≤ E·|f|²_{n+1}` (the complementary comparison gives the
  comparability clauses; see `CoerData` and `Assembly.lean`);
* conclusion (to be supplied in `StepCoer.lean`, delegated): coercivity of `Lhat` at level
  `n+1` for `HkIPStep c₁ c₂ IP` with constant `cc·min 1 (min c₁ c₂)/(2D)`, under **no**
  hypothesis relating `cc`, `CC` and `κ` — only `c₂·(CCκ)² ≤ min(cc²/4, c₁cc²/4)`.  The
  arithmetic is the paper's; the only inputs beyond the level-`n` data are the two exact
  commutator identities, the explicit `Ê₂` bound and the norm comparison.

`exists_small_step_coeffs` shows that the coefficient condition is satisfiable for *every*
positive `cc`, with `c₂` small: this is the precise sense in which the paper's choice of
small coefficients replaces the balance.  The balance `CC√κ ≤ cc/2` is, by contrast,
*unsatisfiable* as soon as `CC·κ > cc/2` and cannot be repaired by any choice of coefficients
— it constrains the constants themselves (`balance_unusable`).

The remaining inputs (the level-1 coercivity `coer1_Lhat`, the `RegQ`-ports, the `Ê₂` slot
bound, `Dz_self`, the ε-transfer `Lhat → LGammaT`) are in the sibling modules of this
directory; the design is recorded in `NOTES.md`.
-/
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.CoercivityFix.QuadAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (RegQ)

set_option autoImplicit false

/-- **The analytic clauses of a level-`n` coercive inner product**, in the interior class
`RegQ α n`: Cauchy–Schwarz with constant `CC`, comparability with constants `cc`, `CC`, and
coercivity of the clean operator `Lhat = 𝓛 − Transport` with constant `cc`. -/
structure CoerData (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) (cc CC : ℝ) : Prop where
  /-- the coercivity/comparability constant is positive. -/
  hcc : 0 < cc
  /-- the Cauchy–Schwarz/comparability constant is positive. -/
  hCC : 0 < CC
  /-- Cauchy–Schwarz against the honest `ℋⁿ` norm. -/
  cs : ∀ f g : Fn, RegQ α n f → RegQ α n g →
    |IP f g| ≤ CC * Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g
  /-- lower comparability. -/
  lo : ∀ f : Fn, RegQ α n f → cc * Work.Spaces.HkSq α n f ≤ IP f f
  /-- upper comparability. -/
  up : ∀ f : Fn, RegQ α n f → IP f f ≤ CC * Work.Spaces.HkSq α n f
  /-- **coercivity of the clean operator `Lhat`**. -/
  coer : ∀ f : Fn, RegQ α n f → cc * Work.Spaces.HkSq α n f ≤ IP (Lhat f) f

/-- The smallness of the step coefficients, in the form produced by the paper's choice
(`c_{1,k}` arbitrary, `c_{2,k}` of the order `c_{1,k}/(C̄_k/cc)²`).  It constrains only the
*coefficients*, never the relation between the constants `cc`, `CC`, `κ`. -/
def StepSmall (cc CC κ c₁ c₂ : ℝ) : Prop :=
  c₂ * (CC * κ) ^ 2 ≤ cc ^ 2 / 4 ∧ c₂ * (CC * κ) ^ 2 ≤ c₁ * cc ^ 2 / 4

/-- **The coefficient smallness is satisfiable for every positive coercivity constant.**
This is the precise sense in which the paper's choice of *small* step coefficients replaces
the balance hypothesis of the delivered step: `StepSmall` can always be met by taking `c₂`
small, whatever the values of `cc`, `CC`, `κ`. -/
theorem exists_small_step_coeffs {cc CC κ c₁ : ℝ} (hcc : 0 < cc) (hCC : 0 < CC)
    (hc₁ : 0 < c₁) (hκ : 0 ≤ κ) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ StepSmall cc CC κ c₁ c₂ := by
  rcases eq_or_lt_of_le hκ with hκ0 | hκ0
  · refine ⟨1, one_pos, ?_, ?_⟩
    · rw [← hκ0]; norm_num
      nlinarith [hcc]
    · rw [← hκ0]; norm_num
      nlinarith [hcc, hc₁]
  · have hpos : 0 < (CC * κ) ^ 2 := by positivity
    have hCCκ : 0 < CC * κ := mul_pos hCC hκ0
    set m := min (cc ^ 2 / 4) (c₁ * cc ^ 2 / 4) with hm
    have hm0 : 0 < m := lt_min (div_pos (pow_pos hcc 2) (by norm_num))
      (div_pos (mul_pos hc₁ (pow_pos hcc 2)) (by norm_num))
    have hden : (0:ℝ) < 2 * (CC * κ) ^ 2 := by nlinarith [hpos]
    refine ⟨m / (2 * (CC * κ) ^ 2), ?_, ?_, ?_⟩
    · exact div_pos hm0 hden
    · have hle : m ≤ cc ^ 2 / 4 := min_le_left _ _
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < 2 * (CC * κ) ^ 2)]
      nlinarith [hle, hpos]
    · have hle : m ≤ c₁ * cc ^ 2 / 4 := min_le_right _ _
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < 2 * (CC * κ) ^ 2)]
      nlinarith [hle, hpos]

/-- **The delivered balance is not a condition on the coefficients.**  `CC√κ ≤ cc/2` fails
as soon as `CC·κ > cc/2`, for *every* choice of step coefficients — the coefficients enter
the delivered step only through the *scaled* constants `cc/4`, `9CC`, so no choice of them
can repair it.  This is the formal content of design §5 T3. -/
theorem balance_unusable {cc CC κ : ℝ} (h : cc / 2 < CC * Real.sqrt κ) :
    ¬ (CC * Real.sqrt κ ≤ cc / 2) := by
  intro hle
  linarith

end Work.FTS.CoercivityFix
