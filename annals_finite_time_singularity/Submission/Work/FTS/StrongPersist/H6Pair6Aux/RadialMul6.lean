import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Blocks.HkMul_ang_le
import Submission.Work.FTS.OpenPkg.radialMul_field
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.FkSlots
import Submission.Work.FTS.StrongPersist.H6Aux.DzdIter_mul_of_diff
import Submission.Work.FTS.StrongPersist.L6Aux.HkIntegrandSepLeGen
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.CoercivityFix.Assembly.RegQAux
import Submission.Work.Coercivity.HkMem_congr_Ioi
import Submission.Work.FTS.IPGen.OpenBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The radial multiplier at level six

For a *radial* factor `X` (`z ↦ X z`, smooth on `(0,∞)`, with all its `D_z`-jets up to order
six bounded by `M`) and any datum `ψ` which is `C^∞` on the open quadrant and honest in `ℋ⁶`,
the product `(z,θ) ↦ X z * ψ z θ` is again in `ℋ⁶`.

This is the level-six instance of the naive Leibniz bound: the level-six slots of the product
are dominated by `C·M²·HkIntegrand α 6 ψ`, because *every* radial derivative `D_z^b X`, `b ≤ 6`,
is bounded (the sibling `Work.FTS.StrongPersist.hkIntegrand_prod_le_rad_uniform6` needs a
radial Hardy bound for the single top slot `b = 6` instead, which is only available for data
with decay; here the bound on `D_z^6 X` comes for free from `L12Sup6` for `X = L₁₂ f`).
-/

/-- Every binomial coefficient occurring in the level-six Leibniz expansions is at most
`2⁶ = 64`, hence its square is at most `4096`. -/
theorem choose_sq_le_4096 {i b : ℕ} (hi : i ≤ 6) :
    (((i.choose b : ℕ) : ℝ)) ^ 2 ≤ 4096 := by
  have h1 : i.choose b ≤ 2 ^ i := Nat.choose_le_two_pow i b
  have h2 : 2 ^ i ≤ 64 := by
    calc 2 ^ i ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hi
      _ = 64 := by norm_num
  have h3 : ((i.choose b : ℕ) : ℝ) ≤ 64 := by exact_mod_cast le_trans h1 h2
  have h0 : (0 : ℝ) ≤ ((i.choose b : ℕ) : ℝ) := by positivity
  nlinarith [h3, h0]

/-- **One pure `D_z`-slot of the radial product.**  All the radial derivatives occurring in the
Leibniz expansion have order `b ≤ i ≤ 6`, hence are controlled by the pointwise bound `M`. -/
theorem light_slot_le_M6 {α M : ℝ} (hM0 : 0 ≤ M) {R : ℝ → ℝ} {h : ℝ → ℝ → ℝ}
    (hM : ∀ b ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ), (Work.Elliptic.DzdIter b R z) ^ 2 ≤ M)
    (hDz : ∀ i ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
        = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Elliptic.DzdIter b R z * Work.Spaces.DzIter (i - b) h z θ))
    {i : ℕ} (hi : i ≤ 6) {θ z : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (hz : 0 < z) :
    (Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 262144 * M * Work.Spaces.HkIntegrand α 6 h z θ := by
  have hzI : z ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr hz
  have hDz' := hDz i hi z hzI θ hθ
  set F : ℕ → ℝ := fun b => (i.choose b : ℝ)
    * (Work.Elliptic.DzdIter b R z
        * (Work.Spaces.DzIter (i - b) h z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) with hF
  have hkey : Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      = ∑ b ∈ Finset.range (i + 1), F b := by
    rw [hDz', Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by simp only [hF]; ring
  rw [hkey]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1)) (f := F)
  have hcard : ((Finset.range (i + 1)).card : ℝ) ≤ 7 := by
    rw [Finset.card_range]; exact_mod_cast (by omega : i + 1 ≤ 7)
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α 6 h z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 h z θ
  have hterm : ∀ b ∈ Finset.range (i + 1),
      F b ^ 2 ≤ 4096 * (M * Work.Spaces.HkIntegrand α 6 h z θ) := by
    intro b hb
    have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hb6 : b ≤ 6 := le_trans hbi hi
    have hib : i - b ≤ 6 := by omega
    have h1 : (((i.choose b : ℕ) : ℝ)) ^ 2 ≤ 4096 := choose_sq_le_4096 hi
    have h2 : (Work.Elliptic.DzdIter b R z) ^ 2 ≤ M := hM b hb6 z hzI
    have h3 : (Work.Spaces.DzIter (i - b) h z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 h z θ :=
      Work.Spaces.sq_le_HkIntegrand_z α 6 h z θ (i - b) hib
    have hprod : (Work.Elliptic.DzdIter b R z) ^ 2
          * (Work.Spaces.DzIter (i - b) h z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ M * Work.Spaces.HkIntegrand α 6 h z θ :=
      mul_le_mul h2 h3 (sq_nonneg _) hM0
    have hprod2 : (((i.choose b : ℕ) : ℝ)) ^ 2
          * ((Work.Elliptic.DzdIter b R z) ^ 2
              * (Work.Spaces.DzIter (i - b) h z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ 4096 * (M * Work.Spaces.HkIntegrand α 6 h z θ) :=
      mul_le_mul h1 hprod (by positivity) (by norm_num)
    rw [hF]
    have hgoal : (((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b R z
            * (Work.Spaces.DzIter (i - b) h z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
        = (((i.choose b : ℕ) : ℝ)) ^ 2
          * ((Work.Elliptic.DzdIter b R z) ^ 2
              * (Work.Spaces.DzIter (i - b) h z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
      ring
    rw [hgoal]
    exact hprod2
  have hsum : (∑ b ∈ Finset.range (i + 1), F b ^ 2)
      ≤ 7 * (4096 * (M * Work.Spaces.HkIntegrand α 6 h z θ)) := by
    calc (∑ b ∈ Finset.range (i + 1), F b ^ 2)
        ≤ ∑ _b ∈ Finset.range (i + 1), (4096 * (M * Work.Spaces.HkIntegrand α 6 h z θ)) :=
          Finset.sum_le_sum hterm
      _ = ((Finset.range (i + 1)).card : ℝ)
            * (4096 * (M * Work.Spaces.HkIntegrand α 6 h z θ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 7 * (4096 * (M * Work.Spaces.HkIntegrand α 6 h z θ)) := by
          have h0 : 0 ≤ 4096 * (M * Work.Spaces.HkIntegrand α 6 h z θ) :=
            mul_nonneg (by norm_num) (mul_nonneg hM0 hHnn)
          exact mul_le_mul_of_nonneg_right hcard h0
  nlinarith [hcs, hcard, hsum, hM0, hHnn]

/-- **One mixed slot of the radial product.**  Here `i ≥ 1` and `i + j ≤ 6`, so every radial
derivative in the Leibniz expansion has order `b ≤ j ≤ 6`. -/
theorem heavy_slot_le_M6 {α M : ℝ} (hM0 : 0 ≤ M) {R : ℝ → ℝ} {h : ℝ → ℝ → ℝ}
    (hM : ∀ b ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ), (Work.Elliptic.DzdIter b R z) ^ 2 ≤ M)
    (hMx : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 6 → ∀ z ∈ Set.Ioi (0 : ℝ),
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b R z * Work.Spaces.mixed (j - b) i h z θ))
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 6) {θ z : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (hz : 0 < z) :
    (Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 262144 * M * Work.Spaces.HkIntegrand α 6 h z θ := by
  have hzI : z ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr hz
  have hj6 : j ≤ 6 := by omega
  have hMx' := hMx i j hi hij z hzI θ hθ
  set F : ℕ → ℝ := fun b => (j.choose b : ℝ)
    * (Work.Elliptic.DzdIter b R z * (Work.Spaces.mixed (j - b) i h z θ
        * Work.Spaces.Wt α z θ)) with hF
  have hkey : Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ * Work.Spaces.Wt α z θ
      = ∑ b ∈ Finset.range (j + 1), F b := by
    rw [hMx', Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by simp only [hF]; ring
  rw [hkey]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1)) (f := F)
  have hcard : ((Finset.range (j + 1)).card : ℝ) ≤ 7 := by
    rw [Finset.card_range]; exact_mod_cast (by omega : j + 1 ≤ 7)
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α 6 h z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 h z θ
  have hterm : ∀ b ∈ Finset.range (j + 1),
      F b ^ 2 ≤ 4096 * (M * Work.Spaces.HkIntegrand α 6 h z θ) := by
    intro b hb
    have hbj : b ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hb6 : b ≤ 6 := le_trans hbj hj6
    have h1 : (((j.choose b : ℕ) : ℝ)) ^ 2 ≤ 4096 := choose_sq_le_4096 hj6
    have h2 : (Work.Elliptic.DzdIter b R z) ^ 2 ≤ M := hM b hb6 z hzI
    have h3 : (Work.Spaces.mixed (j - b) i h z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 h z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α 6 h z θ i (j - b) hi (by omega)
    have hprod : (Work.Elliptic.DzdIter b R z) ^ 2
          * (Work.Spaces.mixed (j - b) i h z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ M * Work.Spaces.HkIntegrand α 6 h z θ :=
      mul_le_mul h2 h3 (sq_nonneg _) hM0
    have hprod2 := mul_le_mul h1 hprod (by positivity) (by norm_num : (0 : ℝ) ≤ 4096)
    rw [hF]
    have hgoal : (((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b R z
            * (Work.Spaces.mixed (j - b) i h z θ * Work.Spaces.Wt α z θ))) ^ 2
        = (((j.choose b : ℕ) : ℝ)) ^ 2
          * ((Work.Elliptic.DzdIter b R z) ^ 2
              * (Work.Spaces.mixed (j - b) i h z θ * Work.Spaces.Wt α z θ) ^ 2) := by
      ring
    rw [hgoal]
    exact hprod2
  have hsum : (∑ b ∈ Finset.range (j + 1), F b ^ 2)
      ≤ 7 * (4096 * (M * Work.Spaces.HkIntegrand α 6 h z θ)) := by
    calc (∑ b ∈ Finset.range (j + 1), F b ^ 2)
        ≤ ∑ _b ∈ Finset.range (j + 1), (4096 * (M * Work.Spaces.HkIntegrand α 6 h z θ)) :=
          Finset.sum_le_sum hterm
      _ = ((Finset.range (j + 1)).card : ℝ)
            * (4096 * (M * Work.Spaces.HkIntegrand α 6 h z θ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 7 * (4096 * (M * Work.Spaces.HkIntegrand α 6 h z θ)) := by
          have h0 : 0 ≤ 4096 * (M * Work.Spaces.HkIntegrand α 6 h z θ) :=
            mul_nonneg (by norm_num) (mul_nonneg hM0 hHnn)
          exact mul_le_mul_of_nonneg_right hcard h0
  nlinarith [hcs, hcard, hsum, hM0, hHnn]

/-- **The pointwise level-six bound for the radial product.** -/
theorem radial_mul6_pt {α M : ℝ} (hM0 : 0 ≤ M) {R : ℝ → ℝ} {h : ℝ → ℝ → ℝ}
    (hM : ∀ b ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ), (Work.Elliptic.DzdIter b R z) ^ 2 ≤ M)
    (hDz : ∀ i ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
        = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Elliptic.DzdIter b R z * Work.Spaces.DzIter (i - b) h z θ))
    (hMx : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 6 → ∀ z ∈ Set.Ioi (0 : ℝ),
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b R z * Work.Spaces.mixed (j - b) i h z θ))
    {θ z : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (hz : 0 < z) :
    Work.Spaces.HkIntegrand α 6 (fun z θ => R z * h z θ) z θ
      ≤ (14680064 * M + 1) * Work.Spaces.HkIntegrand α 6 h z θ := by
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α 6 h z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 h z θ
  have hMHnn : 0 ≤ M * Work.Spaces.HkIntegrand α 6 h z θ := mul_nonneg hM0 hHnn
  have hHkR : Work.Spaces.HkIntegrand α 6 (fun z θ => R z * h z θ) z θ
      = (∑ i ∈ Finset.range 7, (Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
            (if 1 ≤ i ∧ i + j ≤ 6 then
              (Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2
            else 0) := by
    rw [Work.Spaces.HkIntegrand]
  rw [hHkR]
  have hZ : (∑ i ∈ Finset.range 7, (Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 7 * (262144 * M * Work.Spaces.HkIntegrand α 6 h z θ) := by
    calc (∑ i ∈ Finset.range 7, (Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range 7, (262144 * M * Work.Spaces.HkIntegrand α 6 h z θ) :=
          Finset.sum_le_sum fun i hi =>
            light_slot_le_M6 hM0 hM hDz (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hθ hz
      _ = 7 * (262144 * M * Work.Spaces.HkIntegrand α 6 h z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
  have hMxsum : (∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
        (if 1 ≤ i ∧ i + j ≤ 6 then
          (Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0))
      ≤ 49 * (262144 * M * Work.Spaces.HkIntegrand α 6 h z θ) := by
    have hone : ∀ i j : ℕ,
        (if 1 ≤ i ∧ i + j ≤ 6 then
          (Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0) ≤ 262144 * M * Work.Spaces.HkIntegrand α 6 h z θ := by
      intro i j
      by_cases hc : 1 ≤ i ∧ i + j ≤ 6
      · rw [if_pos hc]
        exact heavy_slot_le_M6 hM0 hM hMx hc.1 hc.2 hθ hz
      · rw [if_neg hc]
        positivity
    calc (∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
          (if 1 ≤ i ∧ i + j ≤ 6 then
            (Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2
          else 0))
        ≤ ∑ _i ∈ Finset.range 7, ∑ _j ∈ Finset.range 7,
            (262144 * M * Work.Spaces.HkIntegrand α 6 h z θ) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hone i j
      _ = 49 * (262144 * M * Work.Spaces.HkIntegrand α 6 h z θ) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
          ring
  have hmain : Work.Spaces.HkIntegrand α 6 (fun z θ => R z * h z θ) z θ
      ≤ 7 * (262144 * M * Work.Spaces.HkIntegrand α 6 h z θ)
        + 49 * (262144 * M * Work.Spaces.HkIntegrand α 6 h z θ) := add_le_add hZ hMxsum
  nlinarith [hmain, hHnn, hM0]

/-- **The radial multiplier at level six**: for a radial factor `X` (`C^∞` on the open
quadrant as a function of `z`, with `D_z`-jets of order `≤ 6` bounded by `M`) and a datum `ψ`
which is `C^∞` on the open quadrant and honest in `ℋ⁶`, the product is honest in `ℋ⁶`. -/
theorem RadialMul6 {α M : ℝ} (hM : 0 ≤ M) {X : ℝ → ℝ} {ψ : ℝ → ℝ → ℝ}
    (hXsm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => X z))
    (hXb : ∀ b ≤ 6, ∀ z : ℝ, 0 < z → |Work.Elliptic.DzdIter b X z| ≤ M)
    (hψ : Work.FTS.EllipticEst.SmoothOpen ψ) (hψmem : Work.Spaces.HkMem α 6 ψ) :
    Work.Spaces.HkMem α 6 (fun z θ => X z * ψ z θ) := by
  have hXd : ContDiffOn ℝ 6 X (Set.Ioi 0) :=
    (hXsm.curry_z (θ := 1/2) (by constructor <;> linarith [Real.pi_gt_three])).of_le
      (by simp [Work.Stability.smoothOrder])
  have hM2 : ∀ b ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ), (Work.Elliptic.DzdIter b X z) ^ 2 ≤ M ^ 2 :=
    fun b hb z hz => by
      have h := hXb b hb z hz
      have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      rwa [sq_abs] at h2
  have hDz : ∀ i ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.DzIter i (fun z θ => X z * ψ z θ) z θ
        = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Elliptic.DzdIter b X z * Work.Spaces.DzIter (i - b) ψ z θ) := by
    intro i hi z hz θ hθ
    have h := leibniz_radial_mul (X := X) (f := ψ) hXd hψ i 0 hi z θ hz hθ.1 hθ.2
    simpa only [Work.Spaces.mixed_zero_right] using h
  have hMx : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 6 → ∀ z ∈ Set.Ioi (0 : ℝ),
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.mixed j i (fun z θ => X z * ψ z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b X z * Work.Spaces.mixed (j - b) i ψ z θ) :=
    fun i j _ hij z hz θ hθ =>
      leibniz_radial_mul (X := X) (f := ψ) hXd hψ j i (by omega) z θ hz hθ.1 hθ.2
  have hMnn : 0 ≤ M ^ 2 := sq_nonneg M
  set C : ℝ := 14680064 * M ^ 2 + 1 with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  refine Work.FTS.LocData.HkMem_of_majorant α 6
    (f := fun z θ => X z * ψ z θ) (M := fun z θ => C * Work.Spaces.HkIntegrand α 6 ψ z θ)
    ((Work.FTS.OpenPkg.smoothOpen_sepMul hXsm hψ).continuousOn_HkIntegrand α 6)
    (fun z hz => (hψmem.1 z hz).const_mul C) ?_ ?_
  · have h := hψmem.2.const_mul C
    have hkey : (fun z => ∫ θ in Work.Spaces.Iθ,
          C * Work.Spaces.HkIntegrand α 6 ψ z θ)
        = fun z => C * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 ψ z θ := by
      funext z
      rw [MeasureTheory.integral_const_mul]
    rw [hkey]
    exact h
  · intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · subst hz0
      rw [Work.FTS.LocData.HkIntegrand_zero_fst, Work.FTS.LocData.HkIntegrand_zero_fst,
        mul_zero]
    · by_cases hs : Real.sin (2 * θ) = 0
      · rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α 6 _ z θ hs,
          Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α 6 _ z θ hs, mul_zero]
      · have hθb : 0 < θ ∧ θ < Real.pi / 2 := by
          constructor
          · rcases eq_or_lt_of_le (show (0 : ℝ) ≤ θ from hθ.1) with h | h
            · exfalso
              apply hs
              rw [← h, mul_zero, Real.sin_zero]
            · exact h
          · rcases lt_or_eq_of_le (show θ ≤ Real.pi / 2 from hθ.2) with h | h
            · exact h
            · exfalso
              apply hs
              rw [h, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        have hpt := radial_mul6_pt (α := α) (M := M ^ 2) hMnn hM2 hDz hMx
          (θ := θ) (z := z) hθb hzpos
        have hCge : 14680064 * M ^ 2 + 1 ≤ C := le_of_eq hC
        calc Work.Spaces.HkIntegrand α 6 (fun z θ => X z * ψ z θ) z θ
            ≤ (14680064 * M ^ 2 + 1) * Work.Spaces.HkIntegrand α 6 ψ z θ := hpt
          _ ≤ C * Work.Spaces.HkIntegrand α 6 ψ z θ :=
              mul_le_mul_of_nonneg_right hCge
                (Work.Spaces.HkIntegrand_nonneg α 6 ψ z θ)
end Work.FTS.StrongPersist.H6Pair6Aux
