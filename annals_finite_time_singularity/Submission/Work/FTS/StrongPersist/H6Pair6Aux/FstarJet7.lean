/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FstarJet7` — the order-`7` jet of the fundamental-model profile is bounded on `[0,∞)`

`Work.FM.Fstar z = 2z/(1+z)²` is the radial factor of the reference profile and
`DzdIter j` is the `j`-fold iterate of `D_z = z ∂_z` on functions of `z` alone.  We prove

  `∃ M > 0, ∀ j ≤ 7, ∀ z ≥ 0, |D_z^j F_*(z)| ≤ M`,

i.e. the first eight `D_z`-jets of `F_*` are *uniformly* bounded on the whole half-line
`[0,∞)` (not merely of size `O(1/z)` at infinity, as in the delivered
`Work.FTS.LocData6.FM_Fstar_jet_le6`, which covers `j ≤ 6` and `z ≥ 1`).

## The route

* `F_*` is a rational function with its only pole at `z = -1`, hence analytic on `(-1,∞)`
  (`contDiffOn_FM_Fstar_analytic`);
* every plain derivative of `F_*` has the closed form
  `∂_z^j F_* z = 2·(-1)^j·j!·(z-j)/(1+z)^(j+2)` (`deriv_iter_FM_Fstar_eq`, proved here from
  Mathlib only, by the one-step recursion `φ_j' = φ_{j+1}`);
* for `z ≥ 0` this gives the *global* bound `|z^k ∂_z^k F_* z| ≤ 2·k!·(k+1)`
  (`zpow_deriv_FM_Fstar_le`): indeed `z^k/(1+z)^k ≤ 1` and `|z-k| ≤ (k+1)(1+z)²`;
* the Stirling expansion `D_z^j = ∑_{k≤j} S(j,k) z^k ∂_z^k`
  (`Spaces.DzIter_eq_sum_scoef`) and the coefficient bound `Spaces.abs_sum_scoef_mul_le`
  (`|∑_k S(j,k) x_k| ≤ bell j · max|x_k|`) then turn this into
  `|D_z^j F_* z| ≤ bell j · 2·7!·8 ≤ 877 · 80640` for every `j ≤ 7` and every `z ≥ 0`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.LocData6.FM_Fstar_jet_le6
import Submission.Work.FTS.LocDataExt.FMJet5
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.Spaces.DzIter_le_of_pzIter

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Analyticity of the profile on `(-1,∞)` -/

/-- `F_*` is a rational function whose only pole is at `z = -1`, hence analytic (order `⊤`)
on the half-line `(-1,∞)`. -/
theorem contDiffOn_FM_Fstar_analytic :
    ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun z : ℝ => Work.FM.Fstar z) (Set.Ioi (-1)) := by
  have hnum : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun z : ℝ => 2 * z) (Set.Ioi (-1)) :=
    contDiffOn_const.mul contDiffOn_id
  have hden : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi (-1)) :=
    (contDiffOn_const.add contDiffOn_id).pow 2
  have h := hnum.div hden
    (fun z hz => pow_ne_zero 2 (by have hz' : (-1 : ℝ) < z := hz; linarith))
  change ContDiffOn ℝ (⊤ : WithTop ℕ∞) ((fun z : ℝ => 2 * z) / (fun z : ℝ => (1 + z) ^ 2))
    (Set.Ioi (-1))
  exact h

/-! ## The closed form of the iterated derivatives -/

/-- **The one-step derivative of the closed form**: with
`φ_j(w) = 2·(-1)^j·j!·(w-j)/(1+w)^(j+2)`, one has `φ_j' = φ_{j+1}`. -/
theorem hasDerivAt_FM_Fstar_formula (j : ℕ) {z : ℝ} (hz : z ∈ Set.Ioi (-1)) :
    HasDerivAt (fun w : ℝ => 2 * (-1 : ℝ) ^ j * (j.factorial : ℝ) * (w - (j : ℝ))
        / (1 + w) ^ (j + 2))
      (2 * (-1 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ) * (z - ((j + 1 : ℕ) : ℝ))
        / (1 + z) ^ (j + 1 + 2)) z := by
  have hz' : (1 : ℝ) + z ≠ 0 := by simp only [Set.mem_Ioi] at hz; linarith
  have hnum : HasDerivAt (fun w : ℝ => 2 * (-1 : ℝ) ^ j * (j.factorial : ℝ) * (w - (j : ℝ)))
      (2 * (-1 : ℝ) ^ j * (j.factorial : ℝ)) z := by
    have h : HasDerivAt (fun w : ℝ => w - ((j : ℕ) : ℝ)) 1 z :=
      (hasDerivAt_id z).sub_const ((j : ℕ) : ℝ)
    have h2 := h.const_mul (2 * (-1 : ℝ) ^ j * (j.factorial : ℝ))
    simpa [mul_assoc] using h2
  have hden : HasDerivAt (fun w : ℝ => (1 + w) ^ (j + 2))
      (((j + 2 : ℕ) : ℝ) * (1 + z) ^ (j + 1)) z := by
    have h : HasDerivAt (fun w : ℝ => 1 + w) 1 z := (hasDerivAt_id z).const_add 1
    have h2 := h.pow (j + 2)
    rw [show (fun w : ℝ => (1 + w) ^ (j + 2)) = (fun w : ℝ => 1 + w) ^ (j + 2) from by
      funext w; simp [Pi.pow_apply]]
    simpa using h2
  have hdiv := hnum.div hden (pow_ne_zero _ hz')
  convert hdiv using 1
  · have h1 : (1 + z) ^ (j + 1 + 2) = (1 + z) ^ (j + 1) * (1 + z) ^ 2 := by
      rw [show j + 1 + 2 = (j + 1) + 2 by omega, pow_add]
    have h2 : ((1 + z) ^ (j + 2)) ^ 2 = (1 + z) ^ (j + 2) * (1 + z) ^ (j + 2) := pow_two _
    have h3 : (1 + z) ^ (j + 2) = (1 + z) ^ (j + 1) * (1 + z) := by
      rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
    rw [h1, h2, h3]
    have hu : (1 + z) ^ (j + 1) ≠ 0 := pow_ne_zero _ hz'
    field_simp
    rw [show (-1 : ℝ) ^ (j + 1) = -(-1) ^ j by rw [pow_succ]; ring]
    rw [show ((j + 1).factorial : ℝ) = ((j : ℝ) + 1) * (j.factorial : ℝ) by
      rw [Nat.factorial_succ]; push_cast; ring]
    push_cast
    ring

/-- **The closed form of the iterated derivatives of the plain profile**:
`∂^j F_* z = 2·(-1)^j·j!·(z-j)/(1+z)^(j+2)` on `(-1,∞)`. -/
theorem deriv_iter_FM_Fstar_eq (j : ℕ) {z : ℝ} (hz : z ∈ Set.Ioi (-1)) :
    deriv^[j] (fun z => Work.FM.Fstar z) z
      = 2 * (-1 : ℝ) ^ j * (j.factorial : ℝ) * (z - (j : ℝ)) / (1 + z) ^ (j + 2) := by
  induction j generalizing z with
  | zero =>
      rw [Function.iterate_zero_apply]
      simp only [Work.FM.Fstar]
      norm_num
  | succ n ih =>
      have hEqOn : Set.EqOn (deriv^[n] (fun z => Work.FM.Fstar z))
          (fun w : ℝ => 2 * (-1 : ℝ) ^ n * (n.factorial : ℝ) * (w - (n : ℝ))
            / (1 + w) ^ (n + 2)) (Set.Ioi (-1)) := fun w hw => ih hw
      rw [Function.iterate_succ_apply', hEqOn.deriv isOpen_Ioi hz]
      exact (hasDerivAt_FM_Fstar_formula n hz).deriv

/-! ## The slices of the iterated `z`-derivatives -/

/-- The iterated plain derivative of a function of `z` alone, as a `pzIter`. -/
theorem pzIter_zonly_eq_FM_deriv_iter (Φ : ℝ → ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (fun z _ => Φ z) z θ = deriv^[k] Φ z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.pzIter_succ, Work.Spaces.pz]
      congr 1
      funext z'
      exact ih z'

/-! ## The global bound `|z^k ∂_z^k F_* z| ≤ 2·k!·(k+1)` for `z ≥ 0` -/

/-- **The weighted plain derivatives of the profile are uniformly bounded on `[0,∞)`**:
`|z^k ∂_z^k F_* z| ≤ 2·k!·(k+1)` for every `z ≥ 0`.  (For `z ≥ 1` the sharper `O(1/z)`
bound is available in `Work.FTS.LocData6.FM_Fstar_jet_le6`; here we need the whole
half-line, including the endpoint `z = 0`.) -/
theorem zpow_deriv_FM_Fstar_le (k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |z ^ k * deriv^[k] (fun z => Work.FM.Fstar z) z| ≤ 2 * (k.factorial : ℝ) * ((k : ℝ) + 1) := by
  have hzI : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hden : (0 : ℝ) < (1 + z) ^ (k + 2) := pow_pos h1z _
  rw [deriv_iter_FM_Fstar_eq k hzI]
  have hrw : z ^ k * (2 * (-1 : ℝ) ^ k * (k.factorial : ℝ) * (z - (k : ℝ)) / (1 + z) ^ (k + 2))
      = (-1 : ℝ) ^ k
          * (2 * (k.factorial : ℝ) * (z ^ k * (z - (k : ℝ))) / (1 + z) ^ (k + 2)) := by
    ring
  rw [hrw, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_div, abs_of_pos hden]
  have hnum : |2 * (k.factorial : ℝ) * (z ^ k * (z - (k : ℝ)))|
      = 2 * (k.factorial : ℝ) * (z ^ k * |z - (k : ℝ)|) := by
    rw [abs_mul, abs_mul, abs_mul]
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k.factorial : ℝ)),
      abs_of_nonneg (pow_nonneg hz k)]
  rw [hnum]
  rw [div_le_iff₀ hden]
  have h1 : z ^ k ≤ (1 + z) ^ k := pow_le_pow_left₀ hz (by linarith) k
  have h2 : |z - (k : ℝ)| ≤ ((k : ℝ) + 1) * (1 + z) ^ 2 := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg z, hz, hk0]
  have h3 : z ^ k * |z - (k : ℝ)| ≤ ((k : ℝ) + 1) * (1 + z) ^ (k + 2) := by
    calc z ^ k * |z - (k : ℝ)| ≤ (1 + z) ^ k * (((k : ℝ) + 1) * (1 + z) ^ 2) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = ((k : ℝ) + 1) * (1 + z) ^ (k + 2) := by rw [pow_add]; ring
  have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * (k.factorial : ℝ))
  linarith [h4]

/-! ## The Bell number of row `7` -/

/-- The Bell numbers of the rows `j ≤ 7` are at most `877` (`B₇ = 877`). -/
theorem bell_le_seven (j : ℕ) (hj : j ≤ 7) : Work.Spaces.bell j ≤ 877 := by
  interval_cases j <;> decide

/-! ## The jet bound -/

/-- **The first eight `D_z`-jets of `F_*` are uniformly bounded on `[0,∞)`.** -/
theorem FstarJet7 : ∃ M : ℝ, 0 < M ∧ ∀ j : ℕ, j ≤ 7 → ∀ z : ℝ, 0 ≤ z →
    |Work.Elliptic.DzdIter j Work.FM.Fstar z| ≤ M := by
  refine ⟨877 * (2 * ((Nat.factorial 7) : ℝ) * ((7 : ℝ) + 1)), ?_, ?_⟩
  · have h : (0 : ℝ) < ((Nat.factorial 7) : ℝ) := by exact_mod_cast Nat.factorial_pos 7
    positivity
  · intro j hj z hz
    have hzI : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
    have h0I : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by positivity⟩
    have hsmooth : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ (⊤ : WithTop ℕ∞)
        (fun z => (fun z _ => Work.FM.Fstar z) z θ) (Set.Ioi (-1)) :=
      fun _ _ => contDiffOn_FM_Fstar_analytic
    rw [show Work.Elliptic.DzdIter j Work.FM.Fstar z
        = Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z 0 from
      (Work.Elliptic.DzIter_rad (fun z => Work.FM.Fstar z) j z 0).symm]
    rw [Work.Spaces.DzIter_eq_sum_scoef (h := fun z _ => Work.FM.Fstar z) hsmooth j z hzI 0 h0I]
    have hx : ∀ k ≤ j, |z ^ k * Work.Spaces.pzIter k (fun z _ => Work.FM.Fstar z) z 0|
        ≤ 2 * ((Nat.factorial 7) : ℝ) * ((7 : ℝ) + 1) := by
      intro k hk
      rw [pzIter_zonly_eq_FM_deriv_iter]
      refine (zpow_deriv_FM_Fstar_le k hz).trans ?_
      have hk7 : k ≤ 7 := le_trans hk hj
      have hfac : (k.factorial : ℝ) ≤ ((Nat.factorial 7) : ℝ) := by
        exact_mod_cast Nat.factorial_le hk7
      have hk1 : (k : ℝ) + 1 ≤ (7 : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hk7
      have h2k : 2 * (k.factorial : ℝ) ≤ 2 * ((Nat.factorial 7) : ℝ) := by linarith
      exact mul_le_mul h2k hk1 (by linarith) (by positivity)
    have hsum := Work.Spaces.abs_sum_scoef_mul_le j
      (2 * ((Nat.factorial 7) : ℝ) * ((7 : ℝ) + 1))
      (fun k => z ^ k * Work.Spaces.pzIter k (fun z _ => Work.FM.Fstar z) z 0) hx
    refine hsum.trans ?_
    have hbell : (Work.Spaces.bell j : ℝ) ≤ 877 := by
      exact_mod_cast bell_le_seven j hj
    have hM : (0 : ℝ) ≤ 2 * ((Nat.factorial 7) : ℝ) * ((7 : ℝ) + 1) := by
      have h : (0 : ℝ) ≤ ((Nat.factorial 7) : ℝ) := by
        exact_mod_cast (Nat.factorial_pos 7).le
      positivity
    exact mul_le_mul_of_nonneg_right hbell hM

end Work.FTS.StrongPersist.H6Pair6Aux
