/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `ℋᵐ`-integrand of `𝓛̂g` is dominated by the `ℋ^{m+1}`-integrand of `g`

This file proves

  `Lhat_integrand_le`:  `HkIntegrand α m (Lhat g) z θ ≤ C · HkIntegrand α (m+1) g z θ`

for `g` of class `C^∞` on the open quadrant `(0,∞) × (0,π/2)`, `z > 0`, `θ ∈ (0,π/2)` and
every `α > 0`, with a constant `C` depending only on `α` and `m`.

The operator is `Work.FTS.CoercivityFix.Lhat g = 𝓛 g − Transport g`, unfolded as
(`Work.FTS.CoercivityFix.Lhat_eq`)

  `𝓛̂g = g + D_z g − 2·g/(1+z) − 3·D_θ g/(1+z) = (g + D_z g) + (−2/3)·(φ·g) + (−1)·(φ·D_θ g)`

with the *radial* multiplier `φ(z) = 3/(1+z)`.

## The four ingredients (all pre-existing, all `sorry`-free)

* **the index shifts** `Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift`:
  `HkIntegrand α k (D_z^b D_θ^a g) ≤ HkIntegrand α (k+a+b) g` for `SmoothOpen g` — this is
  what turns `HkIntegrand α m (D_z g)` and `HkIntegrand α m (D_θ g)` into
  `HkIntegrand α (m+1) g` (the `D_θ`-case uses `η ≤ γ`, i.e. `α > 0`);
* **the multiplier estimate** `Work.FTS.StrongPersist.L3Aux.zmul_open`: multiplication by a
  `z`-only factor whose `Zop`-iterates up to order `m` are bounded by `K` costs
  `zmulConst m·(1+K)²`;
* **the subadditivity** `Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain`
  of the integrand at finite order `m` on the *closed* quadrant, and its **homogeneity**
  `Work.FTS.LocData.HkIntegrand_const_mul`;
* **the monotonicity** `Work.FTS.StrongPersist.HkIntegrand_le_of_le` in the order, which
  gives `HkIntegrand α m g ≤ HkIntegrand α (m+1) g`.

The `Zop`-bound for the specific multiplier `φ(z) = 3/(1+z)` is `three_div_zop_bound`, the
level-`m` version of `Work.FTS.StrongPersist.L6Aux.PhiZopBound6`: under the Möbius chart
`zchart`, `φ` is the chart evaluation of the linear polynomial `P3 = (3/2)(1−X)`, so
`Zop^[b] φ = (Tmul^[b] P3).eval ∘ zchart` and `|Zop^[b] φ| ≤ coeffSum (Tmul^[b] P3)`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.CoercivityFix.E2Bound.HkIntegrand_zmul_le
import Submission.Work.FTS.StrongPersist.Basic
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift
import Submission.Work.FTS.StrongPersist.L6Aux.LinMem6Aux
import Submission.Work.FTS.StrongPersist.L6Aux.PhiZopBound6
import Submission.Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.PthIter2VftsAux
import Submission.Work.FTS.LocData.HkIntegrand_neg
import Submission.Work.FTS.LocData.HkIntegrand_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.StrongPersist.H6Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.FTS.StrongPersist.L6Aux (coeffSum P3 coeffSum_nonneg eqOn_three_div_gpoly
  abs_eval_le_coeffSum)
open Work.FTS.CoercivityFix.E2Bound (Tmul gpoly zchart)

/-! ## The `Zop`-iterates of `z ↦ 3/(1+z)` up to order `m` -/

/-- **The `Zop`-iterates of the multiplier `z ↦ 3/(1+z)` up to order `m` are uniformly
bounded**, the bound depending on `m`.  This is `PhiZopBound6` with the level six replaced by
the general level `m`. -/
lemma three_div_zop_bound (m : ℕ) : ∃ K : ℝ, 0 < K ∧ ∀ b ≤ m, ∀ z ∈ Set.Ioi (0 : ℝ),
    |Work.Spaces.Zop^[b] (fun z : ℝ => 3 / (1 + z)) z| ≤ K := by
  refine ⟨max 3 (∑ b ∈ Finset.range (m + 1), coeffSum (Tmul^[b] P3)) + 1,
    by positivity, ?_⟩
  intro b hb z hz
  have hbmem : b ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hb)
  have hle : coeffSum (Tmul^[b] P3)
      ≤ ∑ b' ∈ Finset.range (m + 1), coeffSum (Tmul^[b'] P3) :=
    Finset.single_le_sum (f := fun b' => coeffSum (Tmul^[b'] P3))
      (fun i _ => coeffSum_nonneg _) hbmem
  have hBig : (∑ b' ∈ Finset.range (m + 1), coeffSum (Tmul^[b'] P3))
      ≤ max 3 (∑ b' ∈ Finset.range (m + 1), coeffSum (Tmul^[b'] P3)) + 1 := by
    have := le_max_right (3 : ℝ) (∑ b' ∈ Finset.range (m + 1), coeffSum (Tmul^[b'] P3))
    linarith
  have h1 : Work.Spaces.Zop^[b] (fun z : ℝ => 3 / (1 + z)) z
      = (Tmul^[b] P3).eval (zchart z) := by
    rw [Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_eqOn_of_eqOn b isOpen_Ioi
          eqOn_three_div_gpoly hz,
        Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_gpoly_iterate P3 b z hz]
    rfl
  rw [h1]
  have h2 : |(Tmul^[b] P3).eval (zchart z)| ≤ coeffSum (Tmul^[b] P3) :=
    abs_eval_le_coeffSum _ (Work.FTS.CoercivityFix.E2Bound.abs_zchart_le_one hz)
  linarith

/-! ## The integrand bound -/

theorem Lhat_integrand_le (α : ℝ) (hα : 0 < α) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℝ → ℝ → ℝ, Work.FTS.EllipticEst.SmoothOpen g →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.Spaces.HkIntegrand α m (Work.FTS.CoercivityFix.Lhat g) z θ
          ≤ C * Work.Spaces.HkIntegrand α (m + 1) g z θ := by
  obtain ⟨K, hKpos, hKb⟩ := three_div_zop_bound m
  have hK : (0 : ℝ) ≤ K := hKpos.le
  refine ⟨8 * (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2) + 9, ?_, ?_⟩
  · have h1 : 0 ≤ Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2 :=
      mul_nonneg (Work.FTS.StrongPersist.L3Aux.zmulConst_pos m).le (sq_nonneg _)
    linarith
  · intro g hg z hz θ hθ
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr (le_of_lt hz)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hZnn : 0 ≤ Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2 :=
      mul_nonneg (Work.FTS.StrongPersist.L3Aux.zmulConst_pos m).le (sq_nonneg _)
    have hRnn : 0 ≤ Work.Spaces.HkIntegrand α (m + 1) g z θ :=
      Work.Spaces.HkIntegrand_nonneg α (m + 1) g z θ
    have hφsm : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 3 / (1 + z))
        (Set.Ioi (-1)) :=
      contDiffOn_iff_forall_nat_le.mpr (fun k _ => Work.FTS.FinalClock.contDiffOn_phiThree k)
    -- the multiplier estimate for `φ(z) = 3/(1+z)`, for an arbitrary `SmoothOpen` factor
    have hmul (X : ℝ → ℝ → ℝ) (hX : Work.FTS.EllipticEst.SmoothOpen X) :
        Work.Spaces.HkIntegrand α m (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * X z θ) z θ
          ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α m X z θ :=
      Work.FTS.StrongPersist.L3Aux.zmul_open α m (fun z : ℝ => 3 / (1 + z)) X hK hKb hφsm hX
        z hz θ hθ
    -- the index shifts
    have hshiftZ : Work.Spaces.HkIntegrand α m (Work.Spaces.Dz g) z θ
        ≤ Work.Spaces.HkIntegrand α (m + 1) g z θ := by
      have h := Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift α hα m 0 1 hg z hzIz θ hθI
      simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
        Nat.reduceAdd] using h
    have hshiftT : Work.Spaces.HkIntegrand α m (Work.Spaces.Dth g) z θ
        ≤ Work.Spaces.HkIntegrand α (m + 1) g z θ := by
      have h := Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift α hα m 1 0 hg z hzIz θ hθI
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero,
        Nat.reduceAdd, Nat.add_zero] using h
    have hmono : Work.Spaces.HkIntegrand α m g z θ ≤ Work.Spaces.HkIntegrand α (m + 1) g z θ :=
      Work.FTS.StrongPersist.HkIntegrand_le_of_le α (Nat.le_succ m) g z θ
    -- smoothness of the three new summands of the decomposition
    have hφopen : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => (fun z : ℝ => 3 / (1 + z)) z) :=
      Work.FTS.StrongPersist.linMem_radial hφsm
    have hBsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ)) :=
      Work.FTS.StrongPersist.linMem_const_mul (-(2 / 3))
        (Work.FTS.StrongPersist.linMem_mul hφopen hg)
    have hDsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ)) :=
      Work.FTS.StrongPersist.linMem_const_mul (-1)
        (Work.FTS.StrongPersist.linMem_mul hφopen hg.Dth)
    -- the bound for each of the three summands
    have hA : Work.Spaces.HkIntegrand α m (fun z θ => g z θ + Work.Spaces.Dz g z θ) z θ
        ≤ 4 * Work.Spaces.HkIntegrand α (m + 1) g z θ := by
      have h := Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α m
        (f := g) (g := Work.Spaces.Dz g) (hg.forall m) ((hg.Dz).forall m) z hzIz θ hθI
      linarith [h, hmono, hshiftZ]
    have hB : Work.Spaces.HkIntegrand α m
        (fun z θ => (-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ)) z θ
        ≤ (4 / 9) * ((Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
            * Work.Spaces.HkIntegrand α (m + 1) g z θ) := by
      rw [Work.FTS.LocData.HkIntegrand_const_mul]
      have hsq : (-(2 / 3) : ℝ) ^ 2 = 4 / 9 := by norm_num
      rw [hsq]
      have h2 : Work.Spaces.HkIntegrand α m
            (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * g z θ) z θ
          ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α (m + 1) g z θ :=
        le_trans (hmul g hg) (mul_le_mul_of_nonneg_left hmono hZnn)
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    have hD : Work.Spaces.HkIntegrand α m
        (fun z θ => (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ)) z θ
        ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
            * Work.Spaces.HkIntegrand α (m + 1) g z θ := by
      rw [Work.FTS.LocData.HkIntegrand_const_mul]
      have h2 : Work.Spaces.HkIntegrand α m
            (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ) z θ
          ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α (m + 1) g z θ :=
        le_trans (hmul (Work.Spaces.Dth g) hg.Dth)
          (mul_le_mul_of_nonneg_left hshiftT hZnn)
      norm_num
      exact h2
    have hBD : Work.Spaces.HkIntegrand α m
        (fun z θ => (-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ)
          + (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ)) z θ
        ≤ 2 * ((4 / 9) * ((Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α (m + 1) g z θ))
          + 2 * ((Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α (m + 1) g z θ) := by
      have h := Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α m
        (f := fun z θ => (-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ))
        (g := fun z θ => (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ))
        (hBsm.forall m) (hDsm.forall m) z hzIz θ hθI
      linarith [h, hB, hD]
    -- assemble along `𝓛̂g = (g + D_z g) + [(−2/3)·(φ g) + (−1)·(φ D_θ g)]`
    have hLhat : Work.FTS.CoercivityFix.Lhat g
        = fun z θ => (g z θ + Work.Spaces.Dz g z θ)
            + ((-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ)
               + (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ)) := by
      funext z θ
      rw [Work.FTS.CoercivityFix.Lhat_eq]
      ring
    rw [hLhat]
    have hfinal := Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α m
      (f := fun z θ => g z θ + Work.Spaces.Dz g z θ)
      (g := fun z θ => (-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ)
        + (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ))
      ((hg.forall m).add ((hg.Dz).forall m)) ((hBsm.forall m).add (hDsm.forall m)) z hzIz θ hθI
    have hkey : 2 * (4 * Work.Spaces.HkIntegrand α (m + 1) g z θ)
        + 2 * (2 * ((4 / 9) * ((Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
                * Work.Spaces.HkIntegrand α (m + 1) g z θ))
          + 2 * ((Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α (m + 1) g z θ))
        ≤ (8 * (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2) + 9)
            * Work.Spaces.HkIntegrand α (m + 1) g z θ := by
      nlinarith [hRnn, hZnn]
    linarith [hfinal, hA, hBD, hkey]

end Work.FTS.StrongPersist.H6Aux
