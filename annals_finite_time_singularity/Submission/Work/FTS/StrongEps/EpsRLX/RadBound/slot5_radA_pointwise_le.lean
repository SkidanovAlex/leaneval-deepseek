import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAZop
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.GalFields.Norm.Xn_LGammaT_le
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.RadSAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `RadBound/slot5_radA_pointwise_le` — the pointwise slot-`5` bound for `radA α f`

The radial profile of the transfer defect is

  `radA α f z = −ampA α z · L₁₂ f(z) + (ampB α z / c α) · L₁₂(Transport f)(0)`

(`Transfer.radA`), a sum of a product of the two `z`-profiles `ampA α`, `L₁₂ f` and a *constant*
multiple of the profile `ampB α`.  This file proves the pointwise estimate

  `Σ_{q<5} (D_z^q (radA α f)(z))² w(z)²
    ≤ 2·(6400·K²)·Σ_{q<5} (D_z^q (L₁₂ f)(z))² w(z)²
      + 2·(L₁₂(Transport f)(0)/c α)²·Σ_{q<5} (D_z^q (ampB α)(z))² w(z)²`

for every `z > 0`, under the sole hypothesis that the `(z∂_z)`-iterates of `ampA α` up to order
`4` are bounded by `K`; the two differentiability hypotheses are exactly what the Leibniz rule
for `D_z = z∂_z` needs at level `≤ 4`.

The three steps are:

* `radA_split_open` / `radA_expansion_open` — the pointwise expansion of `D_z^q (radA α f)`,
  `q ≤ 4`, obtained from the additivity of the `D_z`-iterates (`E1Parts.DzdIter_add_of_diff`,
  the differentiability of the `ampA α·L₁₂ f` iterates being the hypothesis `hAdiff` and that of
  the `ampB α` iterates coming from the smoothness `contDiffOn_ampB_five`) and the Leibniz rule
  (`Nonlinear.Pieces.dzdIter_mul_leibniz`);
* `radA_iter_sq_le` — the per-slot bound, from `(a+b)² ≤ 2a²+2b²`, `|D_z^b (ampA α)| ≤ K`,
  `Σ_b C(q,b) = 2^q` and the Cauchy–Schwarz estimate `(Σ|y_i|)² ≤ #s·Σy_i²`
  (`sq_sum_le_card_mul_sum_sq`);
* the assembly, where the numerical bound `2·4^q·(q+1) ≤ 2560` for `q ≤ 4` gives exactly the
  constant `2·6400 = 12800` when summed over the five slots.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
noncomputable section

open scoped Real Topology

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Work.FTS.StrongEps.EpsRLX.RadBound

/-! ## The two summands of `radA α f` -/

/-- First summand of `radA α f`: `−ampA α · L₁₂ f`.  (The `(−1)·`-form is what
`E2pkg.dzdIter_const_mul` rewrites.) -/
abbrev radAU1 (α : ℝ) (f : Work.FTS.Galerkin.Fn) : ℝ → ℝ :=
  fun z => -1 * (Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z)

/-- Second summand of `radA α f`: the constant multiple of `ampB α`. -/
abbrev radAU2 (α : ℝ) (f : Work.FTS.Galerkin.Fn) : ℝ → ℝ :=
  fun z => (Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
    * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0

/-- **The decomposition of `radA` on `(0,∞)`** into its two summands. -/
theorem radA_split_open (α : ℝ) (f : Work.FTS.Galerkin.Fn) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.FTS.CoercivityFix.Transfer.radA α f z
        = (radAU1 α f + radAU2 α f) z := by
  intro z hz
  simp only [radAU1, radAU2, Pi.add_apply, Work.FTS.CoercivityFix.Transfer.radA]
  ring

/-! ## The pointwise expansion of the `D_z`-iterates of `radA` -/

/-- **The pointwise expansion of `D_z^q (radA α f)`**, `q ≤ 4`, on `(0,∞)`: the Leibniz sum of
the product `ampA α · L₁₂ f` plus the constant multiple of `D_z^q (ampB α)`. -/
theorem radA_expansion_open (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (f : Work.FTS.Galerkin.Fn)
    (hL12diff : ∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (Work.Coercivity.L12f f)) z)
    (hAdiff : ∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b
        (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.ampA α z
          * Work.Coercivity.L12f f z)) z) :
    ∀ q : ℕ, q ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z
        = -(∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
              * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
              * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z)
          + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
              * Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z := by
  intro q hq z hz
  have hU1diff : ∀ b < q, ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (radAU1 α f)) z' := by
    intro b hb z' hz'
    rw [show radAU1 α f = fun z => -1 * (Work.FTS.CoercivityFix.Transfer.ampA α z
          * Work.Coercivity.L12f f z) from rfl,
      Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_const_mul]
    exact (hAdiff b (by omega) z' hz').const_mul (-1)
  have hU2diff : ∀ b < q, ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (radAU2 α f)) z' := by
    intro b hb z' hz'
    have hU2 : radAU2 α f = fun z => (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
        / Work.Spaces.c α) * Work.FTS.CoercivityFix.Transfer.ampB α z := by
      funext w; simp only [radAU2]; ring
    rw [hU2, Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_const_mul]
    exact (Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_of_contDiffOn_five
      (Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_ampB_five α) (by omega) hz').const_mul _
  have hLeib : Work.Elliptic.DzdIter q (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z'
        * Work.Coercivity.L12f f z') z
      = ∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ) * (Work.Elliptic.DzdIter b
          (Work.FTS.CoercivityFix.Transfer.ampA α) z
          * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z) :=
    Work.FTS.Nonlinear.Pieces.dzdIter_mul_leibniz q
      (Work.FTS.CoercivityFix.Transfer.ampA α) (Work.Coercivity.L12f f)
      (fun b hb z' hz' =>
        Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_of_contDiffOn_five
          (Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_ampA_five α) (by omega) hz')
      (fun b hb z' hz' => hL12diff b (by omega) z' hz') z hz
  have hU1val : Work.Elliptic.DzdIter q (radAU1 α f) z = -1 * (Work.Elliptic.DzdIter q
      (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z' * Work.Coercivity.L12f f z') z) := by
    rw [show radAU1 α f = fun z => -1 * (Work.FTS.CoercivityFix.Transfer.ampA α z
        * Work.Coercivity.L12f f z) from rfl,
      Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_const_mul]
  have hU2val : Work.Elliptic.DzdIter q (radAU2 α f) z
      = (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
        * Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z := by
    have hU2 : radAU2 α f = fun z => (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
        / Work.Spaces.c α) * Work.FTS.CoercivityFix.Transfer.ampB α z := by
      funext w; simp only [radAU2]; ring
    rw [hU2, Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_const_mul]
  have hsumcongr : (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ) * (Work.Elliptic.DzdIter b
        (Work.FTS.CoercivityFix.Transfer.ampA α) z
        * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z))
      = (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
          * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
          * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z) :=
    Finset.sum_congr rfl (fun b hb => by ring)
  calc Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z
      = Work.Elliptic.DzdIter q (radAU1 α f + radAU2 α f) z :=
        Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_congr_of_eqOn _ _
          (radA_split_open α f) q z hz
    _ = Work.Elliptic.DzdIter q (radAU1 α f) z + Work.Elliptic.DzdIter q (radAU2 α f) z :=
        Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_add_of_diff q _ _ hU1diff hU2diff z hz
    _ = _ := by rw [hU1val, hU2val, hLeib, hsumcongr]; ring

/-! ## The per-slot bound -/

/-- **The pointwise bound for one `z∂_z`-slot of `radA α f`**, `q ≤ 4`: the squared iterate
weighted by `w²` is dominated by the full Leibniz slot sum of `L₁₂ f` (with the constant
`2·(K·2^q)²·(q+1)`) plus the constant-multiple slot of `ampB α`. -/
theorem radA_iter_sq_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : Work.FTS.Galerkin.Fn)
    (hL12diff : ∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (Work.Coercivity.L12f f)) z)
    (hAdiff : ∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b
        (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.ampA α z
          * Work.Coercivity.L12f f z)) z)
    {K : ℝ} (hKnn : 0 ≤ K)
    (hKbd : ∀ b : ℕ, b ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K) :
    ∀ q : ℕ, q ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2
        ≤ 2 * (K * (2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1)
            * (∑ c ∈ Finset.range (q + 1),
                (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
                  * (Work.Spaces.w z) ^ 2)
          + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
              / Work.Spaces.c α) ^ 2)
            * ((Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
              * (Work.Spaces.w z) ^ 2) := by
  intro q hq z hz
  have hexp := radA_expansion_open α hα hα1 f hL12diff hAdiff q hq z hz
  have hw2nn : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hchoose : (∑ b ∈ Finset.range (q + 1), ((q.choose b : ℕ) : ℝ)) = (2 : ℝ) ^ q := by
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
  have hSbound : |∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
        * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
        * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z|
      ≤ K * 2 ^ q * ∑ c ∈ Finset.range (q + 1),
          |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z| := by
    have hterm : ∀ b ∈ Finset.range (q + 1),
        |(q.choose b : ℝ)
          * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
          * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z|
        ≤ K * ((q.choose b : ℝ) * ∑ c ∈ Finset.range (q + 1),
            |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|) := by
      intro b hb
      have hC : 0 ≤ (q.choose b : ℝ) := Nat.cast_nonneg _
      have hb4 : b ≤ 4 := by
        have := Finset.mem_range.mp hb
        omega
      have hAb : |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K :=
        hKbd b hb4 z hz
      have hXb : |Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z|
          ≤ ∑ c ∈ Finset.range (q + 1),
              |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z| :=
        Finset.single_le_sum (f := fun c => |Work.Elliptic.DzdIter c
            (Work.Coercivity.L12f f) z|) (fun c _ => abs_nonneg _) (Finset.mem_range.mpr (by
          have := Finset.mem_range.mp hb
          omega))
      calc |(q.choose b : ℝ)
            * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
            * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z|
          = (q.choose b : ℝ) * |Work.Elliptic.DzdIter b
              (Work.FTS.CoercivityFix.Transfer.ampA α) z|
            * |Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hC]
        _ ≤ (q.choose b : ℝ) * K * ∑ c ∈ Finset.range (q + 1),
              |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z| := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hAb hC) hXb (abs_nonneg _) ?_
            exact mul_nonneg hC hKnn
        _ = K * ((q.choose b : ℝ) * ∑ c ∈ Finset.range (q + 1),
              |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|) := by ring
    have h3 : ∑ b ∈ Finset.range (q + 1), K * ((q.choose b : ℝ)
          * ∑ c ∈ Finset.range (q + 1), |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|)
        = K * 2 ^ q * ∑ c ∈ Finset.range (q + 1),
            |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z| := by
      rw [← Finset.mul_sum, ← Finset.sum_mul, hchoose]
      ring
    have h2 := Finset.sum_le_sum hterm
    have h1 := Finset.abs_sum_le_sum_abs (s := Finset.range (q + 1))
      (f := fun b => (q.choose b : ℝ)
        * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
        * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z)
    linarith [h1, h2, h3.le, h3.ge]
  have hcs : (∑ c ∈ Finset.range (q + 1),
        |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|) ^ 2
      ≤ ((q : ℝ) + 1) * ∑ c ∈ Finset.range (q + 1),
          (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (q + 1))
      (f := fun c => |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|)
    rw [Finset.card_range] at h
    simpa only [nsmul_eq_mul, sq_abs, Nat.cast_add, Nat.cast_one] using h
  have hAmaj : (K * 2 ^ q * (∑ c ∈ Finset.range (q + 1),
        |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|)) ^ 2
      ≤ (K * 2 ^ q) ^ 2 * ((q : ℝ) + 1) * ∑ c ∈ Finset.range (q + 1),
          (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 := by
    calc (K * 2 ^ q * (∑ c ∈ Finset.range (q + 1),
          |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|)) ^ 2
        = (K * 2 ^ q) ^ 2 * (∑ c ∈ Finset.range (q + 1),
            |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|) ^ 2 := by ring
      _ ≤ (K * 2 ^ q) ^ 2 * (((q : ℝ) + 1) * ∑ c ∈ Finset.range (q + 1),
            (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = (K * 2 ^ q) ^ 2 * ((q : ℝ) + 1) * ∑ c ∈ Finset.range (q + 1),
            (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 := by ring
  have hSsq : (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
        * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
        * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z) ^ 2
      ≤ (K * 2 ^ q * (∑ c ∈ Finset.range (q + 1),
          |Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z|)) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
        * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
        * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z)) hSbound 2
    rwa [sq_abs] at h
  have hmaj : (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
        * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
        * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z) ^ 2
      ≤ (K * 2 ^ q) ^ 2 * ((q : ℝ) + 1) * ∑ c ∈ Finset.range (q + 1),
          (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 := le_trans hSsq hAmaj
  have hmain : (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
      ≤ 2 * (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
            * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
            * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z) ^ 2
        + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
            * (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z)) ^ 2 := by
    rw [hexp]
    nlinarith [sq_nonneg ((∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
          * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
          * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z)
        + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
          * (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z))]
  calc (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2
      ≤ (2 * (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
            * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
            * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z) ^ 2
        + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
            * (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z)) ^ 2)
          * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hmain hw2nn
    _ = 2 * ((∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
            * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
            * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z) ^ 2
              * (Work.Spaces.w z) ^ 2)
        + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
            * ((Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
              * (Work.Spaces.w z) ^ 2) := by ring
    _ ≤ 2 * (((K * 2 ^ q) ^ 2 * ((q : ℝ) + 1) * ∑ c ∈ Finset.range (q + 1),
            (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2)
              * (Work.Spaces.w z) ^ 2)
        + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
            * ((Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
              * (Work.Spaces.w z) ^ 2) := by
        refine add_le_add ?_ le_rfl
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmaj hw2nn) (by norm_num)
    _ = 2 * (K * (2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1)
            * (∑ c ∈ Finset.range (q + 1),
                (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
                  * (Work.Spaces.w z) ^ 2)
          + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
              / Work.Spaces.c α) ^ 2)
            * ((Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
              * (Work.Spaces.w z) ^ 2) := by
        rw [← Finset.sum_mul]; ring

/-- The numerical bound behind the constant `6400`: for `q ≤ 4`,
`2·(K·2^q)²·(q+1) ≤ 2560·K²`, and `5·2560 = 12800 = 2·6400`. -/
theorem radA_slot_coeff_le {K : ℝ} (hKnn : 0 ≤ K) {q : ℕ} (hq : q ≤ 4) :
    2 * (K * (2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1) ≤ 2560 * K ^ 2 := by
  have h2q : (2 : ℝ) ^ q ≤ 16 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hq
    norm_num at h
    exact h
  have h2qnn : (0 : ℝ) ≤ (2 : ℝ) ^ q := by positivity
  have hsq : ((2 : ℝ) ^ q) ^ 2 ≤ 256 := by
    nlinarith [h2q, h2qnn, sq_nonneg ((2 : ℝ) ^ q - 16)]
  have hq5 : ((q : ℝ) + 1) ≤ 5 := by
    have h : (q : ℝ) ≤ 4 := by exact_mod_cast hq
    linarith
  have hmul : ((2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1) ≤ 256 * 5 :=
    mul_le_mul hsq hq5 (by positivity) (by norm_num)
  calc 2 * (K * (2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1)
      = 2 * K ^ 2 * (((2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1)) := by ring
    _ ≤ 2 * K ^ 2 * (256 * 5) := mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = 2560 * K ^ 2 := by ring

/-! ## The target -/

theorem slot5_radA_pointwise_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (f : Work.FTS.Galerkin.Fn)
    (hL12diff : ∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (Work.Coercivity.L12f f)) z)
    (hAdiff : ∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b
        (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.ampA α z
          * Work.Coercivity.L12f f z)) z)
    {K : ℝ} (hKnn : 0 ≤ K)
    (hKbd : ∀ b : ℕ, b ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K)
    {z : ℝ} (hz : 0 < z) :
    Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α f) z
      ≤ 2 * (6400 * K ^ 2) * Work.FTS.GalFields.Norm.slot5 (Work.Coercivity.L12f f) z
        + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
            * Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.ampB α) z := by
  have hw2nn : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hslotnn : (0 : ℝ) ≤ Work.FTS.GalFields.Norm.slot5 (Work.Coercivity.L12f f) z :=
    Work.FTS.GalFields.Norm.slot5_nonneg _ _
  -- the per-slot bounds
  have hper : ∀ q ∈ Finset.range 5,
      (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2
        ≤ 2 * (K * (2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1)
            * (∑ c ∈ Finset.range (q + 1),
                (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
                  * (Work.Spaces.w z) ^ 2)
          + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
              / Work.Spaces.c α) ^ 2)
            * ((Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
              * (Work.Spaces.w z) ^ 2) :=
    fun q hq => radA_iter_sq_le α hα hα1 f hL12diff hAdiff hKnn hKbd q
      (Nat.le_of_lt_succ (Finset.mem_range.mp hq)) z hz
  -- the tail of the `L₁₂ f`-slot sum is dominated by the full slot sum
  have hslot : ∀ q : ℕ, q ≤ 4 →
      (∑ c ∈ Finset.range (q + 1),
          (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ Work.FTS.GalFields.Norm.slot5 (Work.Coercivity.L12f f) z := by
    intro q hq
    simp only [Work.FTS.GalFields.Norm.slot5]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro c hc
      simp only [Finset.mem_range] at hc ⊢
      omega
    · intro c hc _
      exact mul_nonneg (sq_nonneg _) hw2nn
  calc Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.radA α f) z
      = ∑ q ∈ Finset.range 5,
          (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2 := by
        simp only [Work.FTS.GalFields.Norm.slot5]
    _ ≤ ∑ q ∈ Finset.range 5,
          (2 * (K * (2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1)
              * (∑ c ∈ Finset.range (q + 1),
                  (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
                    * (Work.Spaces.w z) ^ 2)
            + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
                / Work.Spaces.c α) ^ 2)
              * ((Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
                * (Work.Spaces.w z) ^ 2)) := Finset.sum_le_sum hper
    _ = (∑ q ∈ Finset.range 5,
          (2 * (K * (2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1)
              * (∑ c ∈ Finset.range (q + 1),
                  (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
                    * (Work.Spaces.w z) ^ 2)))
        + (∑ q ∈ Finset.range 5,
            2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
                / Work.Spaces.c α) ^ 2)
              * ((Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
                * (Work.Spaces.w z) ^ 2)) := Finset.sum_add_distrib
    _ ≤ (∑ _q ∈ Finset.range 5,
          2560 * K ^ 2 * Work.FTS.GalFields.Norm.slot5 (Work.Coercivity.L12f f) z)
        + (∑ q ∈ Finset.range 5,
            2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
                / Work.Spaces.c α) ^ 2)
              * ((Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
                * (Work.Spaces.w z) ^ 2)) := by
        refine add_le_add (Finset.sum_le_sum ?_) le_rfl
        intro q hq
        have hq4 : q ≤ 4 := Nat.le_of_lt_succ (Finset.mem_range.mp hq)
        have hcoefnn : (0 : ℝ) ≤ 2 * (K * (2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1) := by positivity
        calc 2 * (K * (2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1)
              * (∑ c ∈ Finset.range (q + 1),
                  (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
                    * (Work.Spaces.w z) ^ 2)
            ≤ 2 * (K * (2 : ℝ) ^ q) ^ 2 * ((q : ℝ) + 1)
                * Work.FTS.GalFields.Norm.slot5 (Work.Coercivity.L12f f) z :=
              mul_le_mul_of_nonneg_left (hslot q hq4) hcoefnn
          _ ≤ 2560 * K ^ 2 * Work.FTS.GalFields.Norm.slot5 (Work.Coercivity.L12f f) z :=
              mul_le_mul_of_nonneg_right (radA_slot_coeff_le hKnn hq4) hslotnn
    _ = (∑ _q ∈ Finset.range 5,
          2560 * K ^ 2 * Work.FTS.GalFields.Norm.slot5 (Work.Coercivity.L12f f) z)
        + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
            * Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.ampB α) z := by
        have hsumB : (∑ q ∈ Finset.range 5,
              2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
                * ((Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
                  * (Work.Spaces.w z) ^ 2))
            = 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
                * Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.ampB α) z := by
          rw [← Finset.mul_sum]
          rfl
        rw [hsumB]
    _ = 2 * (6400 * K ^ 2) * Work.FTS.GalFields.Norm.slot5 (Work.Coercivity.L12f f) z
        + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
            * Work.FTS.GalFields.Norm.slot5 (Work.FTS.CoercivityFix.Transfer.ampB α) z := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        norm_num
        ring

end Work.FTS.StrongEps.EpsRLX.RadBound
