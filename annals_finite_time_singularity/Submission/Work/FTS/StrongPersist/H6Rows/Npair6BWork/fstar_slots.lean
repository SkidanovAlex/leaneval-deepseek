import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.Construction.GammaTermAux
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Spaces.GammaW_Prelim
import Submission.Work.Spaces.pzIter_hKer_bound
import Submission.Work.FTS.Nonlinear.FstarPkg.FK_Fstar
import Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_phiZ_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `fstar_slots` --- the pointwise slot bounds for the profile `F_*` and its family

For `α ∈ (0,1]`, `z > 0`, `θ ∈ (0,π/2)` and all `j + i ≤ 6`,

  `|D_z^jD_θ^i F_*| ≤ Cα·z/(1+z)²`

and likewise for `D_θF_*`, `D_zF_*` and `z ↦ FK(F_*)`, while for `i ≥ 1` the same slots
gain a factor `sin(2θ)^{α/3}` (the factor `Γ(θ) = (sinθcos²θ)^{α/3} ≤ sin(2θ)^{α/3}`).

## Route

`F_* = c₀·(Γ ⊗ φ)` with `c₀ = 2α/c(α) ≤ 20α`, `Γ(θ) = (sinθcos²θ)^{α/3}` and
`φ(z) = z/(1+z)²` (`Work.Spaces.hKer`), so every slot is a product of an angular
`D_θ`-iterate of `Γ` (bounded by `dthU_Gam_le` and `Γ ≤ sin(2θ)^{α/3}`) and a radial
`D_z`-iterate of `φ`.  The radial factor is the crux: `D_z = z·d/dz` in the Möbius chart
`x = (z-1)/(z+1)` becomes `Tmul P = ½(1-X²)P'` (`Work.FTS.CoercivityFix.E2Bound`), and
`Zop^[b] φ = φ·(R_b ∘ x)` where `R_b` is the polynomial recursion
`R_{b+1} = -X R_b + ½(1-X²)R_b'`; since `|x| ≤ 1` on `z > 0`, the coefficient sum of `R_b`
bounds the ratio.  Everything is then combined by the two master lemmas `FS.slot_le` /
`FS.slot_le_sin` and the arithmetic of `FS.Cst`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

namespace FS

open Work.FTS.CoercivityFix.E2Bound

/-! ## §1 The radial chart bound -/

/-- The polynomial recursion whose chart-side evaluation is the ratio
`Zop^[b] φ / φ` for `φ = z/(1+z)²`. -/
noncomputable def R : ℕ → Polynomial ℝ
  | 0 => 1
  | (b + 1) => -(Polynomial.X * R b)
      + Polynomial.C (1 / 2) * (1 - Polynomial.X ^ 2) * Polynomial.derivative (R b)

lemma R_succ (b : ℕ) :
    R (b + 1) = -(Polynomial.X * R b)
      + Polynomial.C (1 / 2) * (1 - Polynomial.X ^ 2) * Polynomial.derivative (R b) := rfl

lemma R_zero : R 0 = 1 := rfl

lemma deriv_Pphi : Polynomial.derivative Pphi = Polynomial.C (-(1 / 2)) * Polynomial.X := by
  simp only [Pphi_eq, Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_one, Polynomial.derivative_pow, Polynomial.derivative_C,
    Polynomial.derivative_X]
  simp only [zero_mul, zero_sub, mul_one, Nat.reduceSub, pow_one]
  rw [zero_add, mul_neg, ← mul_assoc, ← Polynomial.C_mul]
  norm_num

lemma hC : Polynomial.C (1 / 2) * (1 - Polynomial.X ^ 2) * Polynomial.derivative Pphi
    = -(Polynomial.X * Pphi) := by
  rw [deriv_Pphi, Pphi_eq]
  apply Polynomial.funext
  intro y
  simp only [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_one]
  ring

lemma Tmul_Pphi_mul (Q : Polynomial ℝ) :
    Tmul (Pphi * Q) = Pphi * (-(Polynomial.X * Q)
      + Polynomial.C (1 / 2) * (1 - Polynomial.X ^ 2) * Polynomial.derivative Q) := by
  rw [Tmul_apply, Polynomial.derivative_mul]
  rw [show Polynomial.C (1 / 2) * (1 - Polynomial.X ^ 2)
        * (Polynomial.derivative Pphi * Q + Pphi * Polynomial.derivative Q)
      = (Polynomial.C (1 / 2) * (1 - Polynomial.X ^ 2) * Polynomial.derivative Pphi) * Q
        + Pphi * (Polynomial.C (1 / 2) * (1 - Polynomial.X ^ 2)
            * Polynomial.derivative Q) from by ring]
  rw [hC]
  ring

lemma Tmul_iter_R (b : ℕ) : Tmul^[b] Pphi = Pphi * R b := by
  induction b with
  | zero => rw [Function.iterate_zero_apply, R_zero, mul_one]
  | succ b ih =>
      rw [Function.iterate_succ_apply', ih, Tmul_Pphi_mul, R_succ]

/-- The `Zop`-iterates of the profile `φ = z/(1+z)²` are the chart evaluations of
`Tmul^[b] Pphi`. -/
lemma Zop_iter_hKer_gpoly (b : ℕ) {z : ℝ} (hz : 0 < z) :
    Work.Spaces.Zop^[b] Work.Spaces.hKer z = gpoly (Tmul^[b] Pphi) z := by
  have hz1 : z ∈ Set.Ioi (-1) := by rw [Set.mem_Ioi]; linarith
  have hEqOn : Set.EqOn Work.Spaces.hKer (gpoly Pphi) (Set.Ioi (-1)) := by
    intro w hw
    rw [Set.mem_Ioi] at hw
    rw [Work.Spaces.hKer_apply]
    exact (Work.FTS.CoercivityFix.E2Bound.SlotMul.phiZ_gpoly_eq
      (show 1 + w ≠ 0 by intro h; linarith)).symm
  rw [Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_eqOn_of_eqOn b isOpen_Ioi hEqOn hz1]
  exact Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_gpoly_iterate Pphi b z hz

/-- The coefficient-sum constant bounding the `b`-th iterate of the chart variable. -/
noncomputable def RadK (b : ℕ) : ℝ :=
  ∑ k ∈ Finset.range ((R b).natDegree + 1), |(R b).coeff k|

lemma RadK_nonneg (b : ℕ) : 0 ≤ RadK b :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma hKer_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.hKer z := by
  rw [Work.Spaces.hKer_apply]
  positivity

/-- **The radial slot bound.**  For `z > 0` every `Zop`-iterate of the profile
`φ(z) = z/(1+z)²` is bounded by its own value. -/
lemma Zop_iter_hKer_le (b : ℕ) {z : ℝ} (hz : 0 < z) :
    |Work.Spaces.Zop^[b] Work.Spaces.hKer z| ≤ RadK b * Work.Spaces.hKer z := by
  rw [Zop_iter_hKer_gpoly b hz, Tmul_iter_R b]
  have hz1 : 1 + z ≠ 0 := by positivity
  have hp : gpoly (Pphi * R b) z = gpoly Pphi z * gpoly (R b) z := by
    simp only [gpoly_apply, Polynomial.eval_mul]
  rw [hp, Work.FTS.CoercivityFix.E2Bound.SlotMul.phiZ_gpoly_eq hz1,
    Work.Spaces.hKer_apply]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ z / (1 + z) ^ 2)]
  have hx : |zchart z| ≤ 1 := Work.FTS.CoercivityFix.E2Bound.abs_zchart_le_one hz
  have hb := Work.FTS.CoercivityFix.E2Bound.SlotMul.Polynomial_abs_eval_le_sum_abs_coeff
    (R b) hx
  calc z / (1 + z) ^ 2 * |(R b).eval (zchart z)| ≤ z / (1 + z) ^ 2 * RadK b :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = RadK b * (z / (1 + z) ^ 2) := by ring

/-! ## §2 The constants -/

/-- The common radial constant: dominates `RadK j` for all `j ≤ 7`. -/
noncomputable def CK : ℝ := 1 + ∑ j ∈ Finset.range 8, RadK j

/-- The common angular constant: dominates `tBound i 0` for all `i ≤ 7`. -/
noncomputable def CT : ℝ := 1 + ∑ i ∈ Finset.range 8, Work.Spaces.tBound i 0

/-- The final constant of the slot estimate. -/
noncomputable def Cst : ℝ := 10000 * CK * CT

lemma CK_pos : 0 < CK := by
  have h0 : 0 ≤ ∑ j ∈ Finset.range 8, RadK j :=
    Finset.sum_nonneg (fun j _ => RadK_nonneg j)
  rw [CK]; linarith

lemma CT_pos : 0 < CT := by
  have h0 : 0 ≤ ∑ i ∈ Finset.range 8, Work.Spaces.tBound i 0 :=
    Finset.sum_nonneg (fun i _ => Work.Spaces.tBound_nonneg i 0)
  rw [CT]; linarith

lemma one_le_CT : 1 ≤ CT := by
  have h0 : 0 ≤ ∑ i ∈ Finset.range 8, Work.Spaces.tBound i 0 :=
    Finset.sum_nonneg (fun i _ => Work.Spaces.tBound_nonneg i 0)
  rw [CT]; linarith

lemma Cst_pos : 0 < Cst := by
  rw [Cst]; exact mul_pos (mul_pos (by norm_num) CK_pos) CT_pos

lemma RadK_le_CK {j : ℕ} (hj : j ≤ 7) : RadK j ≤ CK := by
  have hmem : j ∈ Finset.range 8 := Finset.mem_range.mpr (by omega)
  have hsum : RadK j ≤ ∑ i ∈ Finset.range 8, RadK i :=
    Finset.single_le_sum (fun i _ => RadK_nonneg i) hmem
  rw [CK]
  have h0 : 0 ≤ ∑ i ∈ Finset.range 8, RadK i :=
    Finset.sum_nonneg fun i _ => RadK_nonneg i
  linarith

lemma tBound_le_CT {i : ℕ} (hi : i ≤ 7) : Work.Spaces.tBound i 0 ≤ CT := by
  have hmem : i ∈ Finset.range 8 := Finset.mem_range.mpr (by omega)
  have hsum : Work.Spaces.tBound i 0
      ≤ ∑ k ∈ Finset.range 8, Work.Spaces.tBound k 0 :=
    Finset.single_le_sum (fun k _ => Work.Spaces.tBound_nonneg k 0) hmem
  rw [CT]
  have h0 : 0 ≤ ∑ k ∈ Finset.range 8, Work.Spaces.tBound k 0 :=
    Finset.sum_nonneg fun k _ => Work.Spaces.tBound_nonneg k 0
  linarith

/-! ## §3 Angular bounds for the profile `Γ` -/

/-- The angular constant `max 1 (tBound (i-1) 0)`. -/
noncomputable def Amax (i : ℕ) : ℝ := max 1 (Work.Spaces.tBound (i - 1) 0)

lemma Amax_nonneg (i : ℕ) : 0 ≤ Amax i := by
  rw [Amax]; exact le_trans zero_le_one (le_max_left _ _)

lemma Amax_le_CT {i : ℕ} (hi : i ≤ 7) : Amax i ≤ CT := by
  rw [Amax]
  refine max_le ?_ ?_
  · rw [CT]
    have h0 : 0 ≤ ∑ k ∈ Finset.range 8, Work.Spaces.tBound k 0 :=
      Finset.sum_nonneg fun k _ => Work.Spaces.tBound_nonneg k 0
    linarith
  · exact tBound_le_CT (by omega)

/-- **The angular `i`-th `D_θ`-iterate of `Γ` is bounded by `Amax i`.** -/
lemma Lop_Gam_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (i : ℕ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.Lop^[i] (fun t => Work.Spaces.Gam α t) θ| ≤ Amax i := by
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    simp only [Function.iterate_zero, id_eq]
    have hG := Work.Spaces.Gam_bounds α θ hα hθ
    rw [abs_of_nonneg hG.1]
    calc Work.Spaces.Gam α θ ≤ 1 := hG.2
      _ ≤ Amax 0 := by
          rw [Amax]; exact le_max_left _ _
  · have h := Work.Spaces.dthU_Gam_le i hpos α hα hα1 θ hθ
    rw [Amax]
    have hG := Work.Spaces.Gam_bounds α θ hα hθ
    have hT := Work.Spaces.tBound_nonneg (i - 1) 0
    have hαΓ : α * Work.Spaces.Gam α θ ≤ 1 := by nlinarith [hG.1, hG.2, hα.le, hα1]
    have h1 : α * Work.Spaces.tBound (i - 1) 0 * Work.Spaces.Gam α θ
        ≤ Work.Spaces.tBound (i - 1) 0 := by nlinarith [hT, hαΓ, hG.1]
    exact le_trans (le_trans h h1) (le_max_right _ _)

/-- **The angular `i`-th `D_θ`-iterate of `Γ` with the `sin(2θ)^{α/3}` weight.** -/
lemma Lop_Gam_le_sin (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {i : ℕ} (hi : 1 ≤ i) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.Lop^[i] (fun t => Work.Spaces.Gam α t) θ|
      ≤ α * Work.Spaces.tBound (i - 1) 0 * (Real.sin (2 * θ)) ^ (α / 3) := by
  refine le_trans (Work.Spaces.dthU_Gam_le i hi α hα hα1 θ hθ) ?_
  have hG := Work.Construction.Gam_le_sin_two_rpow hα hθ
  calc α * Work.Spaces.tBound (i - 1) 0 * Work.Spaces.Gam α θ
      ≤ α * Work.Spaces.tBound (i - 1) 0 * (Real.sin (2 * θ)) ^ (α / 3) :=
        mul_le_mul_of_nonneg_left hG
          (mul_nonneg hα.le (Work.Spaces.tBound_nonneg (i - 1) 0))

/-- Nonnegativity of the angular weight `sin(2θ)^{α/3}` on `Iθ`. -/
lemma sin_rpow_nonneg {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (Real.sin (2 * θ)) ^ (α / 3) :=
  Real.rpow_nonneg (Work.Construction.sin_two_nonneg_of_mem_Iθ hθ) _

/-- The angular factor of the `FK`-slot: every `D_θ`-iterate of the constant `1` is
bounded by `1`. -/
lemma Lop_iter_const_one_abs (i : ℕ) (θ : ℝ) :
    |Work.Spaces.Lop^[i] (fun _ : ℝ => (1 : ℝ)) θ| ≤ 1 := by
  have hzero : ∀ n : ℕ,
      Work.Spaces.Lop^[n] (fun _ : ℝ => (0 : ℝ)) = (fun _ : ℝ => (0 : ℝ)) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply,
          show Work.Spaces.Lop (fun _ : ℝ => (0 : ℝ)) = (fun _ : ℝ => (0 : ℝ)) from by
            funext t; simp [Work.Spaces.Lop], ih]
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    simp
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    rw [Function.iterate_succ_apply,
      show Work.Spaces.Lop (fun _ : ℝ => (1 : ℝ)) = (fun _ : ℝ => (0 : ℝ)) from by
        funext t; simp [Work.Spaces.Lop], hzero k]
    simp

/-! ## §4 The slot arithmetic -/

lemma slot_arith {α M φ CK' CT' : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hM : 0 ≤ M)
    (hMle : M ≤ CT') (hφ : 0 ≤ φ) (hCK : 0 ≤ CK') (hCT : 0 ≤ CT') :
    20 * α * M * (CK' * φ) ≤ 10000 * CK' * CT' * α * φ := by
  have hX : 0 ≤ CK' * CT' * φ := by positivity
  have hY : 0 ≤ 20 * α * (CK' * φ) := by positivity
  have step1 : 20 * α * M * (CK' * φ) ≤ 20 * α * CT' * (CK' * φ) := by
    nlinarith [hMle, hY]
  have step4 : 20 * α * CT' * (CK' * φ) = 20 * (CK' * CT' * φ) * α := by ring
  have step5 : 10000 * CK' * CT' * α * φ = 10000 * (CK' * CT' * φ) * α := by ring
  have step6 : 20 * α * CT' * (CK' * φ) ≤ 10000 * (CK' * CT' * φ) * α := by
    rw [step4]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hX) hα.le
  rw [step5]
  exact le_trans step1 step6

lemma slot_arith_sin {α TB s φ CK' CT' : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hTB : 0 ≤ TB)
    (hTBle : TB ≤ CT') (hs : 0 ≤ s) (hφ : 0 ≤ φ) (hCK : 0 ≤ CK') (hCT : 0 ≤ CT') :
    20 * α * (α * TB * s) * (CK' * φ) ≤ 10000 * CK' * CT' * α * s * φ := by
  have hα2 : α * α ≤ α := by nlinarith [hα1, hα.le]
  have hX : 0 ≤ CK' * CT' * φ := by positivity
  have hY : 0 ≤ 20 * TB * s * (CK' * φ) := by positivity
  have hY3 : 0 ≤ 20 * α * s * (CK' * φ) := by positivity
  have hY4 : 0 ≤ α * s := by positivity
  have step1 : 20 * α * (α * TB * s) * (CK' * φ) = 20 * (α * α) * TB * s * (CK' * φ) := by ring
  rw [step1]
  have step2 : 20 * (α * α) * TB * s * (CK' * φ) ≤ 20 * α * TB * s * (CK' * φ) := by
    nlinarith [hα.le, hα2, hY]
  have step3 : 20 * α * TB * s * (CK' * φ) ≤ 20 * α * CT' * s * (CK' * φ) := by
    nlinarith [hTBle, hY3]
  have step4 : 20 * α * CT' * s * (CK' * φ) = 20 * (CK' * CT' * φ) * (α * s) := by ring
  have step5 : 10000 * CK' * CT' * α * s * φ = 10000 * (CK' * CT' * φ) * (α * s) := by ring
  have step6 : 20 * (α * α) * TB * s * (CK' * φ) ≤ 20 * (CK' * CT' * φ) * (α * s) := by
    rw [← step4]
    exact le_trans step2 step3
  have hfin : 20 * (CK' * CT' * φ) * (α * s) ≤ 10000 * (CK' * CT' * φ) * (α * s) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hX) hY4
  rw [step5]
  exact le_trans step6 hfin

/-! ## §5 The master slot bounds -/

open Work.Construction in
/-- **The master slot bound.** -/
lemma slot_le {α c₀ MA K z θ : ℝ} {A ψ : ℝ → ℝ} {m : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hc₀ : |c₀| ≤ 20 * α)
    (hA : |A θ| ≤ MA) (hMA : 0 ≤ MA) (hMAle : MA ≤ CT)
    (hrad : |Work.Spaces.Zop^[m] ψ z| ≤ K * Work.Spaces.hKer z)
    (hK : 0 ≤ K) (hKle : K ≤ CK) (hφ : 0 ≤ Work.Spaces.hKer z) :
    |(Work.Spaces.Zop^[m] (fun z => c₀ * ψ z) z) * A θ|
      ≤ Cst * α * Work.Spaces.hKer z := by
  rw [Work.Construction.Zop_iter_const_mul m c₀ ψ]
  have hrad' : |Work.Spaces.Zop^[m] ψ z| ≤ CK * Work.Spaces.hKer z :=
    le_trans hrad (mul_le_mul_of_nonneg_right hKle hφ)
  have h20 : 0 ≤ 20 * α * (CK * Work.Spaces.hKer z) :=
    mul_nonneg (by positivity) (mul_nonneg (le_of_lt CK_pos) hφ)
  have h2 : |c₀ * Work.Spaces.Zop^[m] ψ z| ≤ 20 * α * (CK * Work.Spaces.hKer z) := by
    rw [abs_mul]
    exact le_trans (mul_le_mul hc₀ hrad' (abs_nonneg _) (mul_nonneg (by norm_num) hα.le))
      (le_of_eq (by ring))
  calc |c₀ * Work.Spaces.Zop^[m] ψ z * A θ|
      = |c₀ * Work.Spaces.Zop^[m] ψ z| * |A θ| := by rw [abs_mul]
    _ ≤ (20 * α * (CK * Work.Spaces.hKer z)) * MA :=
        mul_le_mul h2 hA (abs_nonneg _) h20
    _ = 20 * α * MA * (CK * Work.Spaces.hKer z) := by ring
    _ ≤ 10000 * CK * CT * α * Work.Spaces.hKer z :=
        slot_arith hα hα1 hMA hMAle hφ (le_of_lt CK_pos) (le_of_lt CT_pos)
    _ = Cst * α * Work.Spaces.hKer z := by rw [Cst]

open Work.Construction in
/-- **The master slot bound, with the angular `sin(2θ)^{α/3}` weight.** -/
lemma slot_le_sin {α c₀ TB s K z θ : ℝ} {A ψ : ℝ → ℝ} {m : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hc₀ : |c₀| ≤ 20 * α)
    (hA : |A θ| ≤ α * TB * s) (hTB : 0 ≤ TB) (hTBle : TB ≤ CT) (hs : 0 ≤ s)
    (hrad : |Work.Spaces.Zop^[m] ψ z| ≤ K * Work.Spaces.hKer z)
    (hK : 0 ≤ K) (hKle : K ≤ CK) (hφ : 0 ≤ Work.Spaces.hKer z) :
    |(Work.Spaces.Zop^[m] (fun z => c₀ * ψ z) z) * A θ|
      ≤ Cst * α * s * Work.Spaces.hKer z := by
  rw [Work.Construction.Zop_iter_const_mul m c₀ ψ]
  have hrad' : |Work.Spaces.Zop^[m] ψ z| ≤ CK * Work.Spaces.hKer z :=
    le_trans hrad (mul_le_mul_of_nonneg_right hKle hφ)
  have h20 : 0 ≤ 20 * α * (CK * Work.Spaces.hKer z) :=
    mul_nonneg (by positivity) (mul_nonneg (le_of_lt CK_pos) hφ)
  have h2 : |c₀ * Work.Spaces.Zop^[m] ψ z| ≤ 20 * α * (CK * Work.Spaces.hKer z) := by
    rw [abs_mul]
    exact le_trans (mul_le_mul hc₀ hrad' (abs_nonneg _) (mul_nonneg (by norm_num) hα.le))
      (le_of_eq (by ring))
  calc |c₀ * Work.Spaces.Zop^[m] ψ z * A θ|
      = |c₀ * Work.Spaces.Zop^[m] ψ z| * |A θ| := by rw [abs_mul]
    _ ≤ (20 * α * (CK * Work.Spaces.hKer z)) * (α * TB * s) :=
        mul_le_mul h2 hA (abs_nonneg _) h20
    _ = 20 * α * (α * TB * s) * (CK * Work.Spaces.hKer z) := by ring
    _ ≤ 10000 * CK * CT * α * s * Work.Spaces.hKer z :=
        slot_arith_sin hα hα1 hTB hTBle hs hφ (le_of_lt CK_pos) (le_of_lt CT_pos)
    _ = Cst * α * s * Work.Spaces.hKer z := by rw [Cst]

/-! ## §6 The four profiles in separated form -/

open Work.Construction in
/-- `F_* = c₀·(Γ ⊗ φ)` with `c₀ = 2α/c(α)` and `φ = z/(1+z)²`. -/
lemma fstar_sep (α : ℝ) :
    Work.Construction.Fstar α
      = Work.Construction.sepF (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.hKer z)
          (fun θ => Work.Spaces.Gam α θ) := by
  funext z θ
  simp only [Work.Construction.sepF, Work.Construction.Fstar, Work.FM.Fstar,
    Work.Spaces.hKer_apply]
  ring

open Work.Construction in
/-- `D_θ F_* = c₀·(D_θΓ ⊗ φ)`. -/
lemma dth_fstar_sep (α : ℝ) :
    Work.Spaces.Dth (Work.Construction.Fstar α)
      = Work.Construction.sepF (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.hKer z)
          (Work.Spaces.Lop (fun θ => Work.Spaces.Gam α θ)) := by
  have h := Work.Construction.sepF_DthIter 1
    (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.hKer z) (fun θ => Work.Spaces.Gam α θ)
  rw [← fstar_sep α] at h
  simpa using h

open Work.Construction in
/-- `D_z F_* = c₀·(Γ ⊗ D_zφ)`. -/
lemma dz_fstar_sep (α : ℝ) :
    Work.Spaces.Dz (Work.Construction.Fstar α)
      = Work.Construction.sepF
          (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.Zop Work.Spaces.hKer z)
          (fun θ => Work.Spaces.Gam α θ) := by
  have h := Work.Construction.sepF_DzIter 1
    (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.hKer z) (fun θ => Work.Spaces.Gam α θ)
  rw [← fstar_sep α] at h
  rw [show Work.Spaces.Zop^[1] (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.hKer z)
      = fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.Zop^[1] Work.Spaces.hKer z from
        Work.Construction.Zop_iter_const_mul 1 (2 * α / Work.Spaces.c α) Work.Spaces.hKer]
    at h
  simpa using h

open Work.Construction in
/-- `FK(F_*) = 2α·φ`, independently of `θ`. -/
lemma fk_fstar_sep (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z)
      = Work.Construction.sepF (fun z => (2 * α) * Work.Spaces.hKer z) (fun _ => 1) := by
  funext z θ
  simp only [Work.Construction.sepF]
  rw [Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1, Work.Spaces.hKer_apply]
  ring

/-! ## §7 The six slot lemmas -/

lemma coef_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    |2 * α / Work.Spaces.c α| ≤ 20 * α := by
  have hc := (Work.Spaces.c_bounds α hα hα1).1
  have hc0 : 0 < Work.Spaces.c α := by linarith
  rw [abs_of_nonneg (div_nonneg (by linarith) (le_of_lt hc0)), div_le_iff₀ hc0]
  nlinarith

lemma coef_le' (α : ℝ) (hα : 0 < α) : |2 * α| ≤ 20 * α := by
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- The `D_θ`-iterate of `Γ` of index `i`, seen as the angular factor of `D_θ F_*`. -/
lemma Lop_succ_eq (i : ℕ) (Γ : ℝ → ℝ) :
    Work.Spaces.Lop^[i] (Work.Spaces.Lop Γ) = Work.Spaces.Lop^[i + 1] Γ :=
  (Function.iterate_succ_apply Work.Spaces.Lop i Γ).symm

lemma Zop_comp_hKer (j : ℕ) :
    Work.Spaces.Zop^[j] (Work.Spaces.Zop Work.Spaces.hKer)
      = Work.Spaces.Zop^[j + 1] Work.Spaces.hKer := by
  have h1 : Work.Spaces.Zop Work.Spaces.hKer
      = Work.Spaces.Zop^[1] Work.Spaces.hKer := (Function.iterate_one _).symm
  rw [h1]
  exact (Function.iterate_succ_apply Work.Spaces.Zop j Work.Spaces.hKer).symm

open Work.Construction in
lemma G0_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {j i : ℕ} (hji : j + i ≤ 6)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.mixed j i (Work.Construction.Fstar α) z θ|
      ≤ FS.Cst * α * Work.Spaces.hKer z := by
  have hmix : Work.Spaces.mixed j i (Work.Construction.Fstar α) z θ
      = (Work.Spaces.Zop^[j] (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.hKer z) z)
        * (Work.Spaces.Lop^[i] (fun t => Work.Spaces.Gam α t) θ) := by
    rw [fstar_sep α, Work.Construction.sepF_mixed]
    rfl
  rw [hmix]
  exact slot_le hα hα1 (coef_le α hα hα1) (Lop_Gam_le α hα hα1 i hθ) (Amax_nonneg i)
    (Amax_le_CT (by omega)) (Zop_iter_hKer_le j hz) (RadK_nonneg j)
    (RadK_le_CK (by omega)) (le_of_lt (hKer_pos hz))

open Work.Construction in
lemma G0_le_sin {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {j i : ℕ} (hi : 1 ≤ i)
    (hji : j + i ≤ 6) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.mixed j i (Work.Construction.Fstar α) z θ|
      ≤ FS.Cst * α * (Real.sin (2 * θ)) ^ (α / 3) * Work.Spaces.hKer z := by
  have hmix : Work.Spaces.mixed j i (Work.Construction.Fstar α) z θ
      = (Work.Spaces.Zop^[j] (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.hKer z) z)
        * (Work.Spaces.Lop^[i] (fun t => Work.Spaces.Gam α t) θ) := by
    rw [fstar_sep α, Work.Construction.sepF_mixed]
    rfl
  rw [hmix]
  exact slot_le_sin hα hα1 (coef_le α hα hα1) (Lop_Gam_le_sin α hα hα1 hi hθ)
    (Work.Spaces.tBound_nonneg _ _) (tBound_le_CT (by omega)) (sin_rpow_nonneg hθ)
    (Zop_iter_hKer_le j hz) (RadK_nonneg j) (RadK_le_CK (by omega))
    (le_of_lt (hKer_pos hz))

open Work.Construction in
lemma G1_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {j i : ℕ} (hji : j + i ≤ 6)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.mixed j i (Work.Spaces.Dth (Work.Construction.Fstar α)) z θ|
      ≤ FS.Cst * α * Work.Spaces.hKer z := by
  have hmix : Work.Spaces.mixed j i (Work.Spaces.Dth (Work.Construction.Fstar α)) z θ
      = (Work.Spaces.Zop^[j] (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.hKer z) z)
        * (Work.Spaces.Lop^[i + 1] (fun t => Work.Spaces.Gam α t) θ) := by
    rw [dth_fstar_sep α, Work.Construction.sepF_mixed,
      Lop_succ_eq i (fun t => Work.Spaces.Gam α t)]
    rfl
  rw [hmix]
  refine slot_le hα hα1 (coef_le α hα hα1) ?_ (Amax_nonneg (i + 1))
    (Amax_le_CT (by omega)) (Zop_iter_hKer_le j hz) (RadK_nonneg j)
    (RadK_le_CK (by omega)) (le_of_lt (hKer_pos hz))
  exact Lop_Gam_le α hα hα1 (i + 1) hθ

open Work.Construction in
lemma G1_le_sin {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {j i : ℕ} (hi : 1 ≤ i)
    (hji : j + i ≤ 6) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.mixed j i (Work.Spaces.Dth (Work.Construction.Fstar α)) z θ|
      ≤ FS.Cst * α * (Real.sin (2 * θ)) ^ (α / 3) * Work.Spaces.hKer z := by
  have hmix : Work.Spaces.mixed j i (Work.Spaces.Dth (Work.Construction.Fstar α)) z θ
      = (Work.Spaces.Zop^[j] (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.hKer z) z)
        * (Work.Spaces.Lop^[i + 1] (fun t => Work.Spaces.Gam α t) θ) := by
    rw [dth_fstar_sep α, Work.Construction.sepF_mixed,
      Lop_succ_eq i (fun t => Work.Spaces.Gam α t)]
    rfl
  rw [hmix]
  have hA : |Work.Spaces.Lop^[i + 1] (fun t => Work.Spaces.Gam α t) θ|
      ≤ α * Work.Spaces.tBound i 0 * (Real.sin (2 * θ)) ^ (α / 3) := by
    simpa using Lop_Gam_le_sin α hα hα1 (i := i + 1) (by omega) hθ
  exact slot_le_sin hα hα1 (coef_le α hα hα1) hA
    (Work.Spaces.tBound_nonneg i 0) (tBound_le_CT (by omega)) (sin_rpow_nonneg hθ)
    (Zop_iter_hKer_le j hz) (RadK_nonneg j) (RadK_le_CK (by omega))
    (le_of_lt (hKer_pos hz))

open Work.Construction in
lemma G2_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {j i : ℕ} (hji : j + i ≤ 6)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.mixed j i (Work.Spaces.Dz (Work.Construction.Fstar α)) z θ|
      ≤ FS.Cst * α * Work.Spaces.hKer z := by
  have hmix : Work.Spaces.mixed j i (Work.Spaces.Dz (Work.Construction.Fstar α)) z θ
      = (Work.Spaces.Zop^[j]
          (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.Zop Work.Spaces.hKer z) z)
        * (Work.Spaces.Lop^[i] (fun t => Work.Spaces.Gam α t) θ) := by
    rw [dz_fstar_sep α, Work.Construction.sepF_mixed]
    rfl
  rw [hmix]
  have hrad : |Work.Spaces.Zop^[j] (Work.Spaces.Zop Work.Spaces.hKer) z|
      ≤ RadK (j + 1) * Work.Spaces.hKer z := by
    rw [Zop_comp_hKer j]
    exact Zop_iter_hKer_le (j + 1) hz
  exact slot_le hα hα1 (coef_le α hα hα1) (Lop_Gam_le α hα hα1 i hθ) (Amax_nonneg i)
    (Amax_le_CT (by omega)) hrad (RadK_nonneg (j + 1))
    (RadK_le_CK (by omega)) (le_of_lt (hKer_pos hz))

open Work.Construction in
lemma G2_le_sin {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {j i : ℕ} (hi : 1 ≤ i)
    (hji : j + i ≤ 6) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.mixed j i (Work.Spaces.Dz (Work.Construction.Fstar α)) z θ|
      ≤ FS.Cst * α * (Real.sin (2 * θ)) ^ (α / 3) * Work.Spaces.hKer z := by
  have hmix : Work.Spaces.mixed j i (Work.Spaces.Dz (Work.Construction.Fstar α)) z θ
      = (Work.Spaces.Zop^[j]
          (fun z => (2 * α / Work.Spaces.c α) * Work.Spaces.Zop Work.Spaces.hKer z) z)
        * (Work.Spaces.Lop^[i] (fun t => Work.Spaces.Gam α t) θ) := by
    rw [dz_fstar_sep α, Work.Construction.sepF_mixed]
    rfl
  rw [hmix]
  have hrad : |Work.Spaces.Zop^[j] (Work.Spaces.Zop Work.Spaces.hKer) z|
      ≤ RadK (j + 1) * Work.Spaces.hKer z := by
    rw [Zop_comp_hKer j]
    exact Zop_iter_hKer_le (j + 1) hz
  exact slot_le_sin hα hα1 (coef_le α hα hα1) (Lop_Gam_le_sin α hα hα1 hi hθ)
    (Work.Spaces.tBound_nonneg _ _) (tBound_le_CT (by omega)) (sin_rpow_nonneg hθ)
    hrad (RadK_nonneg (j + 1)) (RadK_le_CK (by omega))
    (le_of_lt (hKer_pos hz))

open Work.Construction in
lemma G3_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {j i : ℕ} (hji : j + i ≤ 6)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.mixed j i (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z)
        z θ| ≤ FS.Cst * α * Work.Spaces.hKer z := by
  have hmix : Work.Spaces.mixed j i
        (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) z θ
      = (Work.Spaces.Zop^[j] (fun z => (2 * α) * Work.Spaces.hKer z) z)
        * (Work.Spaces.Lop^[i] (fun _ : ℝ => (1 : ℝ)) θ) := by
    rw [fk_fstar_sep α hα hα1, Work.Construction.sepF_mixed]
    rfl
  rw [hmix]
  exact slot_le hα hα1 (coef_le' α hα) (Lop_iter_const_one_abs i θ) zero_le_one
    one_le_CT (Zop_iter_hKer_le j hz) (RadK_nonneg j)
    (RadK_le_CK (by omega)) (le_of_lt (hKer_pos hz))


end FS

/-! ## The target -/

/-- The pointwise slot bounds for the family of the fundamental profile `F_*`. -/
theorem fstar_slots : ∃ C α₂ : ℝ, 0 < C ∧ 0 < α₂ ∧ α₂ ≤ 1 ∧ ∀ α ∈ Set.Ioc 0 α₂,
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (∀ j i : ℕ, j + i ≤ 6 →
          |Work.Spaces.mixed j i (Work.Construction.Fstar α) z θ| ≤ C * α * (z / (1 + z) ^ 2) ∧
          |Work.Spaces.mixed j i (Work.Spaces.Dth (Work.Construction.Fstar α)) z θ| ≤ C * α * (z / (1 + z) ^ 2) ∧
          |Work.Spaces.mixed j i (Work.Spaces.Dz (Work.Construction.Fstar α)) z θ| ≤ C * α * (z / (1 + z) ^ 2) ∧
          |Work.Spaces.mixed j i (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) z θ| ≤ C * α * (z / (1 + z) ^ 2)) ∧
      (∀ j i : ℕ, 1 ≤ i → j + i ≤ 6 →
          |Work.Spaces.mixed j i (Work.Construction.Fstar α) z θ|
            ≤ C * α * (Real.sin (2 * θ)) ^ (α / 3) * (z / (1 + z) ^ 2) ∧
          |Work.Spaces.mixed j i (Work.Spaces.Dth (Work.Construction.Fstar α)) z θ|
            ≤ C * α * (Real.sin (2 * θ)) ^ (α / 3) * (z / (1 + z) ^ 2) ∧
          |Work.Spaces.mixed j i (Work.Spaces.Dz (Work.Construction.Fstar α)) z θ|
            ≤ C * α * (Real.sin (2 * θ)) ^ (α / 3) * (z / (1 + z) ^ 2) ∧
          |Work.Spaces.mixed j i (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) z θ|
            ≤ C * α * (z / (1 + z) ^ 2)) := by
  refine ⟨FS.Cst, 1, FS.Cst_pos, one_pos, le_refl 1, ?_⟩
  intro α hαIoc
  obtain ⟨hα, hα1⟩ := hαIoc
  intro z θ hz hθ1 hθ2
  have hθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ1, le_of_lt hθ2⟩
  refine ⟨fun j i hji => ⟨?_, ?_, ?_, ?_⟩, fun j i hi hji => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact FS.G0_le hα hα1 hji hz hθ
  · exact FS.G1_le hα hα1 hji hz hθ
  · exact FS.G2_le hα hα1 hji hz hθ
  · exact FS.G3_le hα hα1 hji hz hθ
  · exact FS.G0_le_sin hα hα1 hi hji hz hθ
  · exact FS.G1_le_sin hα hα1 hi hji hz hθ
  · exact FS.G2_le_sin hα hα1 hi hji hz hθ
  · exact FS.G3_le hα hα1 hji hz hθ

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
