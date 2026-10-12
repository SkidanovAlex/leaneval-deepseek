import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixR.LatGreen.latRowLeTsum
import Submission.Work.BoseFixR.debCredit_lintegral_le_sixBall
import Submission.Work.BoseFixR.farLatFoldCell
import Submission.Work.BoseFixR.farLatFourier
import Submission.Work.BoseFixR.farLatParseval
import Submission.Work.BoseFixR.volume_infDist_lat_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # `Work.BoseFixR.farLatRow` — the weighted lattice sampling bound

**Read `FINDING_farLatRow_sharp4.md` FIRST** (it supersedes `sharp3` and corrects it: the
per-`r` route `G(r) ≤ 2H(r)` there is FALSE, see §2 of `sharp4`).

## Status (session 2614)

Everything in the chain is proved except the single position-space crux:

| step | statement | status |
|---|---|---|
| `LatGreen.latRowLeTsum` + `W1funRowSummable` (below) | `latRow ≤ Q/2` | proved |
| `Work.BoseFixR.farLatParseval` | `Q ≤ ℓ³/(4π)·D`, `D = ∫ A_W/d_ℓ` | proved |
| `Work.BoseFixR.farLatPosCrux` | `D ≤ 3F`, `F = ∫ A_W/‖·‖` | delegated, open |
| `Work.BoseFixR.farLatFourier` | `F = 8π·farMass` | proved |
| `Work.BoseFixR.chiR0LtHalf` | **`chiR0 < 1/2`** | **proved** |
| `Work.BoseFixR.farLatAux` | `d_ℓ z ≥ ‖z‖/3` for `‖z‖ ≤ 3ℓ/4` | **proved** |
| `Work.BoseFixR.cruxAeBridge` | `max V 0`-replacement for the crux | delegated, open |

`chiR0LtHalf` replaces the corpus's `chiR0 ≤ 1` / `≤ 2/3` / `chiR0³ ≤ 1/4` and gives
`2R ≤ 2ℓ·chiR0 < ℓ` from the hypothesis `hRℓ`, so the crux applies at the given scale `ℓ`
(the rescaling `farLatScale`/`farLatScaleL2` is *not* needed).
The assembly is `latRow ≤ Q/2 ≤ ℓ³/(4π)·3F/… = 6ℓ³·farMass·(1/2) = 3ℓ³·farMass`, using
`farMass = (2π)^{-3}∫Ŵ²/(2‖q‖²)`.

**BLOCKER (environment, not mathematics):** this module's import cone contains
`Submission/Work/BoseFixR/RB5FSFixAux.lean`, which has been broken since 06:32 by another
agent's in-progress `CloseCond` vs `CloseCondFS` refactor (`RB5FSFixAux.lean:142`,
`hker μ hclose`), so `lake build Submission.Work.BoseFixR.farLatRow` cannot succeed until that
is repaired.  `FarZPDefs.lean` genuinely uses `farEnv`, `pairOpFar`, `cCoefFar` from it, so the
import cannot simply be dropped.  See `FINDING_farLatRow_sharp4.md` §5.

**Read `FINDING_farLatRow_sharp3.md` (previous session; superseded in its §2/§3b) next.**
The file was rewritten after `FINDING_farLatRow_sharp2.md`: the *old* route (through
`latRow_le_folded`, i.e. through the pointwise kernel bound `K_♯(z) = ℓ²·latGreen(z/ℓ) ≤ ℓ³G₀(z)`
applied on the *double* cell) is **invalid**, and its intermediate statement is **false** (the
two-point witness of `FINDING_farLatRow_sharp2.md` §1).  Those lemmas have been deleted.

## The corrected chain (all steps but the crux are PROVED in the tree)

With `W := W1fun v h (ell v μ)`, `ℓ := ell v μ`, `q_k := ℓ⁻¹ • vec k` (`vec k = 2πk`):

* `latRow v h μ N ≤ (1/2)·Σ'_{k≠0}Ŵ(q_k)²/‖q_k‖²` — `LatGreen.latRowLeTsum` (proved; the honest
  cube sum is a sub-sum of the nonnegative full-lattice sum).  Its summability hypothesis is
  discharged here by `W1funRowSummable` (from `LatGreen.W1funDecay` + the lattice decay
  `BoseK15.sum_inv_one_add_norm_le`).
* `Σ'_{k≠0}Ŵ(q_k)²/‖q_k‖² = ∬_{cell ℓ × cell ℓ} P P · ℓ²latGreen(ℓ⁻¹•(x−y))` —
  `LatGreen.LatGreenParsevalB` (proved, sorry-free).
* `latGreen u ≤ 1/(4π·dist(u,ℤ³))` for `u ≠ 0` — `LatGreen.latGreen_le_inv_fourpi_infDist`
  (proved, from `MadelungSharp`).
* `∫ z, A_W(z)/‖z‖ = 8π·farMass v h μ` — `Rb5Lin.chat_sq_div_integral_eq_coulomb` +
  `LatGreen.coulomb_pair_eq_autocorr_integral` (both proved).

So **`latSampling_le` ⟸ `D ≤ 3F`** where `A_W(u) = ∫ x, W x * W (x+u)`,
`D = ∫ z, A_W(z)/dist(z,ℓℤ³)dz`, `F = ∫ z, A_W(z)/‖z‖dz`; and by the scaling
`V(x) := W(ℓx)` (delegated as `BoseFixR/farLatScale`) the statement `D ≤ 3F` is *scale-free*, so
the whole crux is the **ℓ = 1 position-space statement** `farLatPos` below (see
`FINDING_farLatRow_sharp3.md` §1–§2: equivalently `∫_{dist(z)<r}A ≤ 3∫_{‖z‖<r}A` for every `r`,
sharp constant `2`, mechanism = lattice-partner *matching* + AM–GM).

The `(2π)^{-3}∫Ŵ²/(2‖q‖²) = farMass` identification and the arithmetic are done in `farLatRow`.
-/

namespace Work.BoseFixR

open scoped Real BigOperators
open MeasureTheory

/-- `farMass ≥ 0`: the integrand `Ŵ(q)²/(2‖q‖²)` is pointwise nonnegative and `(2π)^{-3} > 0`.
(No integrability hypothesis needed: the Bochner integral of a nonnegative function is
nonnegative unconditionally.) -/
theorem farMass_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ) :
    0 ≤ Work.BoseFixR.farMass v h μ := by
  unfold Work.BoseFixR.farMass
  refine mul_nonneg (by positivity) ?_
  exact MeasureTheory.integral_nonneg (fun q => by positivity)

/-- **The un-halved row of `latRow`.**  `latRow` is `(1/2)` times the un-halved weighted sum
(definitional unfolding, `Finset.mul_sum` + `ring`). -/
theorem latRow_eq_half_sum {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) {μ : ℝ}
    (N : ℕ) :
    Work.BoseFixR.latRow v h μ N
      = (1 / 2) * ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
          (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
            (Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) N k)) ^ 2
            / ‖Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) N k‖ ^ 2 := by
  rw [Work.BoseFixR.latRow, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ## The lattice decay majorant and the row summability -/

/-- `Σ_{k ∈ ℤ³}(1 + ‖vec k‖²)^{-2} < ∞` — the lattice decay of `BoseK15` in the shape used
below.  (`sum_inv_one_add_norm_le 2` bounds the finite partial sums; nonnegative terms and
`summable_of_sum_le` give the `Summable` statement.) -/
theorem vec_onePlusSq_inv_sq_summable :
    Summable (fun k : Fin 3 → ℤ => (((1 : ℝ) + ‖Work.BoseB4.vec k‖ ^ 2) ^ 2)⁻¹) := by
  obtain ⟨C, _hC0, hCle⟩ := Work.BoseK15.sum_inv_one_add_norm_le 2 (by norm_num)
  exact summable_of_sum_le
    (f := fun k : Fin 3 → ℤ => (((1 : ℝ) + ‖Work.BoseB4.vec k‖ ^ 2) ^ 2)⁻¹)
    (c := C) (fun k => by positivity) hCle

/-- A nonzero lattice label has `‖vec k‖ ≥ 2π ≥ 1`. -/
theorem one_le_norm_vec {k : Fin 3 → ℤ} (hk : k ≠ 0) : 1 ≤ ‖Work.BoseB4.vec k‖ := by
  classical
  have hex : ∃ i : Fin 3, k i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hk (funext fun i => hcon i)
  obtain ⟨i, hi⟩ := hex
  have hcoord : (1 : ℝ) ≤ |((k i : ℤ) : ℝ)| := by
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · have h2 : (1 : ℤ) ≤ -k i := by omega
      have h3 : |((k i : ℤ) : ℝ)| = -((k i : ℤ) : ℝ) := by
        rw [abs_of_neg]
        exact_mod_cast hlt
      rw [h3]
      exact_mod_cast h2
    · have h2 : (1 : ℤ) ≤ k i := by omega
      have h3 : |((k i : ℤ) : ℝ)| = ((k i : ℤ) : ℝ) := by
        rw [abs_of_nonneg]
        exact_mod_cast hgt.le
      rw [h3]
      exact_mod_cast h2
  have hle := Work.BoseK15.two_pi_mul_abs_coord_le_norm_vec k i
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hprod : (1 : ℝ) ≤ 2 * Real.pi * |((k i : ℤ) : ℝ)| := by
    have h := mul_le_mul hpi hcoord (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    simpa using h
  linarith

/-- For `x ≥ 1`, `x^{-4} ≤ 4(1+x²)^{-2}`. -/
theorem inv_four_le_inv_sq_sq {x : ℝ} (hx : 1 ≤ x) : 1 / x ^ 4 ≤ 4 / (1 + x ^ 2) ^ 2 := by
  have h0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hx2 : 1 ≤ x ^ 2 := by nlinarith [hx]
  have hfac : 0 ≤ (3 * x ^ 2 + 1) * (x ^ 2 - 1) :=
    mul_nonneg (by positivity) (by linarith)
  have h1 : (1 + x ^ 2) ^ 2 ≤ 4 * x ^ 4 := by nlinarith [hfac]
  have h2 : 0 < (1 + x ^ 2) ^ 2 / 4 := by positivity
  have h3 : 1 / x ^ 4 ≤ 1 / ((1 + x ^ 2) ^ 2 / 4) := by
    apply one_div_le_one_div_of_le h2
    linarith
  rwa [one_div_div] at h3

/-- **Summability of the weighted full-lattice row** (the `hsum` input of
`LatGreen.latRowLeTsum` and of `LatGreen.LatGreenParsevalB`).

From `LatGreen.W1funDecay`, `|Ŵ(q)| ≤ C/(1+‖q‖)`, so with `q = ℓ⁻¹ • vec k` and `‖vec k‖ ≥ 1`:
`Ŵ(q)²/‖q‖² ≤ C²/((1+‖q‖)²‖q‖²) ≤ C²ℓ⁴/‖vec k‖⁴ ≤ 4C²ℓ⁴(1+‖vec k‖²)^{-2}`, and the last family is
summable (`vec_onePlusSq_inv_sq_summable`). -/
theorem W1funRowSummable {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    Summable (fun k : Fin 3 → ℤ => if k = 0 then 0 else
      (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec k)) ^ 2
        / ‖ℓ⁻¹ • Work.BoseB4.vec k‖ ^ 2) := by
  obtain ⟨C, _hC0, hC⟩ := Work.BoseFixR.LatGreen.W1funDecay h hv hvrad hR hℓ hv_supp hRℓ
  have hmaj : Summable (fun k : Fin 3 → ℤ =>
      (4 * C ^ 2 * ℓ ^ 4) * (((1 : ℝ) + ‖Work.BoseB4.vec k‖ ^ 2) ^ 2)⁻¹) :=
    vec_onePlusSq_inv_sq_summable.mul_left _
  refine Summable.of_nonneg_of_le
    (f := fun k : Fin 3 → ℤ =>
      (4 * C ^ 2 * ℓ ^ 4) * (((1 : ℝ) + ‖Work.BoseB4.vec k‖ ^ 2) ^ 2)⁻¹)
    (g := fun k : Fin 3 → ℤ => if k = 0 then 0 else
      (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec k)) ^ 2
        / ‖ℓ⁻¹ • Work.BoseB4.vec k‖ ^ 2) ?_ ?_ hmaj
  · intro k
    by_cases hk : k = 0
    · rw [if_pos hk]
    · rw [if_neg hk]
      positivity
  · intro k
    by_cases hk : k = 0
    · rw [if_pos hk]
      have h0 : 0 ≤ (4 * C ^ 2 * ℓ ^ 4) * (((1 : ℝ) + ‖Work.BoseB4.vec k‖ ^ 2) ^ 2)⁻¹ := by
        positivity
      linarith
    · rw [if_neg hk]
      set q : EuclideanSpace ℝ (Fin 3) := ℓ⁻¹ • Work.BoseB4.vec k with hqdef
      have hvk : 1 ≤ ‖Work.BoseB4.vec k‖ := one_le_norm_vec hk
      have hqnorm : ‖q‖ = ℓ⁻¹ * ‖Work.BoseB4.vec k‖ := by
        rw [hqdef, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ℓ⁻¹)]
      have hqpos : 0 < ‖q‖ := by
        rw [hqnorm]
        exact mul_pos (inv_pos.mpr hℓ) (lt_of_lt_of_le zero_lt_one hvk)
      -- the decay bound at `q`
      have hsq : (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2
          ≤ C ^ 2 / (1 + ‖q‖) ^ 2 := by
        have h1 := hC q
        have h2 : |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q| ^ 2
            ≤ (C / (1 + ‖q‖)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        rwa [sq_abs, div_pow] at h2
      -- step 1: divide by `‖q‖²`
      have hstep1 : (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / ‖q‖ ^ 2
          ≤ C ^ 2 / ((1 + ‖q‖) ^ 2 * ‖q‖ ^ 2) := by
        calc (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / ‖q‖ ^ 2
            = (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 * (1 / ‖q‖ ^ 2) := by ring
          _ ≤ (C ^ 2 / (1 + ‖q‖) ^ 2) * (1 / ‖q‖ ^ 2) :=
              mul_le_mul_of_nonneg_right hsq (by positivity)
          _ = C ^ 2 / ((1 + ‖q‖) ^ 2 * ‖q‖ ^ 2) := by
            simp only [div_eq_mul_inv, one_div, mul_inv, mul_assoc, one_mul]
      -- step 2: compare `(1+‖q‖)²‖q‖²` with `‖vec k‖⁴`
      have hstep2 : C ^ 2 / ((1 + ‖q‖) ^ 2 * ‖q‖ ^ 2)
          ≤ C ^ 2 * ℓ ^ 4 / ‖Work.BoseB4.vec k‖ ^ 4 := by
        have hden : (ℓ ^ 4)⁻¹ * ‖Work.BoseB4.vec k‖ ^ 4 ≤ (1 + ‖q‖) ^ 2 * ‖q‖ ^ 2 := by
          have h1 : ℓ⁻¹ * ‖Work.BoseB4.vec k‖ ≤ 1 + ‖q‖ := by rw [← hqnorm]; linarith [hqpos]
          have h2 : (ℓ⁻¹ * ‖Work.BoseB4.vec k‖) ^ 2 ≤ (1 + ‖q‖) ^ 2 := by
            exact pow_le_pow_left₀ (by positivity) h1 2
          have h3 : ((ℓ⁻¹ * ‖Work.BoseB4.vec k‖) ^ 2) * ‖q‖ ^ 2 ≤ (1 + ‖q‖) ^ 2 * ‖q‖ ^ 2 :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
          have h4 : ((ℓ⁻¹ * ‖Work.BoseB4.vec k‖) ^ 2) * ‖q‖ ^ 2
              = (ℓ ^ 4)⁻¹ * ‖Work.BoseB4.vec k‖ ^ 4 := by
            rw [hqnorm, ← inv_pow]
            ring
          rw [← h4]
          exact h3
        have hkey : 1 / ((1 + ‖q‖) ^ 2 * ‖q‖ ^ 2) ≤ ℓ ^ 4 / ‖Work.BoseB4.vec k‖ ^ 4 := by
          have hpos : 0 < (ℓ ^ 4)⁻¹ * ‖Work.BoseB4.vec k‖ ^ 4 := by
            have : 0 < ‖Work.BoseB4.vec k‖ := lt_of_lt_of_le zero_lt_one hvk
            positivity
          have h1 : 1 / ((1 + ‖q‖) ^ 2 * ‖q‖ ^ 2) ≤ 1 / ((ℓ ^ 4)⁻¹ * ‖Work.BoseB4.vec k‖ ^ 4) :=
            one_div_le_one_div_of_le hpos hden
          have h2 : 1 / ((ℓ ^ 4)⁻¹ * ‖Work.BoseB4.vec k‖ ^ 4)
              = ℓ ^ 4 / ‖Work.BoseB4.vec k‖ ^ 4 := by
            simp only [div_eq_mul_inv, one_div, mul_inv, inv_inv, mul_one, one_mul]
          rwa [h2] at h1
        calc C ^ 2 / ((1 + ‖q‖) ^ 2 * ‖q‖ ^ 2)
            = C ^ 2 * (1 / ((1 + ‖q‖) ^ 2 * ‖q‖ ^ 2)) := by ring
          _ ≤ C ^ 2 * (ℓ ^ 4 / ‖Work.BoseB4.vec k‖ ^ 4) :=
              mul_le_mul_of_nonneg_left hkey (sq_nonneg C)
          _ = C ^ 2 * ℓ ^ 4 / ‖Work.BoseB4.vec k‖ ^ 4 := by ring
      -- step 3: the lattice decay
      have hstep3 : C ^ 2 * ℓ ^ 4 / ‖Work.BoseB4.vec k‖ ^ 4
          ≤ (4 * C ^ 2 * ℓ ^ 4) * (((1 : ℝ) + ‖Work.BoseB4.vec k‖ ^ 2) ^ 2)⁻¹ := by
        have h1 := inv_four_le_inv_sq_sq hvk
        have h2 : C ^ 2 * ℓ ^ 4 / ‖Work.BoseB4.vec k‖ ^ 4
            = C ^ 2 * ℓ ^ 4 * (1 / ‖Work.BoseB4.vec k‖ ^ 4) := by ring
        have h3 : (4 * C ^ 2 * ℓ ^ 4) * (((1 : ℝ) + ‖Work.BoseB4.vec k‖ ^ 2) ^ 2)⁻¹
            = C ^ 2 * ℓ ^ 4 * (4 / (1 + ‖Work.BoseB4.vec k‖ ^ 2) ^ 2) := by
          rw [inv_eq_one_div]
          ring_nf
        rw [h2, h3]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith [hstep1, hstep2, hstep3]

/-! ## The crux: the weighted lattice sampling inequality

Everything below is the *single* remaining mathematical content of `farLatRow`.  Its sharp constant
is `≈ 2.06` over all admissible charges (`FINDING_farLatRow_sharp2.md` §3); the stated `3` has room.
The two *sub-regimes* in which it is provable with the available pointwise Madelung input are noted
in `FINDING_farLatRow_sharp2.md` §6.
-/

/-! The position-space crux `(POS)` used to be restated here (the ℓ = 1, `R ≤ chiR0` form).  It is
now *deleted*: the assembly below does not use it.  `Work.BoseFixR.chiR0LtHalf` (`chiR0 < 1/2`,
proved) turns the hypothesis `hRℓ : R ≤ ℓ·chiR0` into `2R ≤ ℓ`, so the ℓ-scale crux
`Work.BoseFixR.farLatPosCrux` (applied to `V' = max V 0`, transported by
`Work.BoseFixR.cruxAeBridge`) gives `D ≤ 3F` directly at scale `ℓ`, and the rescaling
`farLatScale`/`farLatScaleL2` is not needed.  The sharp constant of that statement is `≈ 2`
(two equal point charges at a lattice distance); numerically `D/F ≤ 2.06` over all tested
admissible charges, so the stated `3` has room.  Known-dead routes (do not retry): the per-`r`
comparison `Σ_{n≠0}∫_{B(lat ℓ n,r)}A_V ≤ 2∫_{B(0,r)}A_V` (counterexample with four bumps,
`FINDING_farLatRow_sharp4.md` §2), pointwise kernel comparison on the image cells, and crude AM–GM
over a full ball. -/

/-! ## The `∫⁻` route to the crux `D ≤ 3F`

Read `FINDING_farLatRow_hWb_and_integral_route.md` first.  The auxiliary targets
`Work.BoseFixR.deb_le_sixBall` and `Work.BoseFixR.K_shift_le` are stated for a **bounded** charge,
and boundedness of `W₁ = W1fun v h (ell v μ)` is *not* available under the target's hypotheses
(`v` is only `L¹` with compact support).  The `∫⁻` formulation of the same mathematics needs only
`Integrable`, a.e.-nonnegativity and the support condition — exactly what the target provides.
We develop it here and convert back to Bochner integrals at the very end with
`MeasureTheory.integral_eq_lintegral_of_nonneg_ae`, which needs no integrability. -/

section IntegralRoute

open scoped ENNReal

/-- The autocorrelation of an a.e.-nonnegative charge is nonnegative **everywhere**. -/
theorem debPair_nonneg_ae {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWnn : 0 ≤ᵐ[MeasureTheory.volume] W) (u : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ debPair W u := by
  rw [debPair]
  refine MeasureTheory.integral_nonneg_of_ae ?_
  have h2 : ∀ᵐ x ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))),
      0 ≤ W (x + u) :=
    (MeasureTheory.measurePreserving_add_right MeasureTheory.volume u).quasiMeasurePreserving
      |>.tendsto_ae.eventually hWnn
  filter_upwards [hWnn, h2] with x hx hxu
  exact mul_nonneg hx hxu

/-- `1/‖u‖ ≤ 1/d_ℓ u` off the lattice, hence the a.e. dominance of `A/‖·‖` by `A/d_ℓ`
(`A = debPair W`); this is what transfers integrability in the final conversion. -/
theorem debPair_div_norm_le_div_debLatD_ae {ℓ R : ℝ} (hℓ : 0 < ℓ) (h2R : 2 * R < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW1 : MeasureTheory.Integrable W)
    (hWnn : 0 ≤ᵐ[MeasureTheory.volume] W)
    (hsupp : tsupport W ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    (fun u => debPair W u / ‖u‖) ≤ᵐ[MeasureTheory.volume]
      (fun u => debPair W u / debLatD ℓ u) := by
  have hnull : ∀ᵐ u ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))),
      debLatD ℓ u ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa [debLatD] using Work.BoseFixR.volume_infDist_lat_eq_zero hℓ
  filter_upwards [hnull] with u hd
  have hdpos : 0 < debLatD ℓ u := lt_of_le_of_ne (debLatD_nonneg ℓ u) (Ne.symm hd)
  have hAle : 0 ≤ debPair W u := debPair_nonneg_ae hWnn u
  have hdle : debLatD ℓ u ≤ ‖u‖ := by
    have h := debLatD_le_dist (ℓ := ℓ) (z := u) (n := 0)
    simpa [Work.BoseFixR.lat_zero] using h
  exact div_le_div_of_nonneg_left hAle hdpos hdle

/-- The `∫⁻` debit carried by the crescent `{d_ℓ < ‖u‖/3}`. -/
noncomputable def crescentDebitLin (ℓ : ℝ) (W : EuclideanSpace ℝ (Fin 3) → ℝ) : ℝ≥0∞ :=
  ∫⁻ u in {u : EuclideanSpace ℝ (Fin 3) | debLatD ℓ u < ‖u‖ / 3},
    ENNReal.ofReal (debPair W u / debLatD ℓ u)

/-- The `∫⁻` credit carried by the ball of radius `ℓ/2`. -/
noncomputable def ballCreditLin (ℓ : ℝ) (W : EuclideanSpace ℝ (Fin 3) → ℝ) : ℝ≥0∞ :=
  ∫⁻ u in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (ℓ / 2),
    ENNReal.ofReal (debPair W u / ‖u‖)

/-- The `∫⁻` six-ball debit (the shape produced by `debCredit_lintegral_le_sixBall` and consumed
by `crescentSixBallCredit`). -/
noncomputable def sixBallDebitLin (ℓ : ℝ) (W : EuclideanSpace ℝ (Fin 3) → ℝ) : ℝ≥0∞ :=
  (∑ i : Fin 3, ∫⁻ u in Metric.ball (debLC ℓ i) (ℓ / 2),
      ENNReal.ofReal (debPair W u / ‖u - debLC ℓ i‖))
    + (∑ i : Fin 3, ∫⁻ u in Metric.ball (-(debLC ℓ i)) (ℓ / 2),
      ENNReal.ofReal (debPair W u / ‖u + debLC ℓ i‖))

/-- **The `∫⁻` crux.**  From the crescent capture `hdeb` and the six-ball credit `hcredit` follows
the lintegral form of `D ≤ 3F`.  No boundedness and no integrability is used anywhere. -/
theorem farLatPosGen_lintegral_of_credits {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R) (h2R : 2 * R < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW1 : MeasureTheory.Integrable W)
    (hWnn : 0 ≤ᵐ[MeasureTheory.volume] W)
    (hsupp : tsupport W ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hdeb : crescentDebitLin ℓ W ≤ sixBallDebitLin ℓ W)
    (hcredit : sixBallDebitLin ℓ W ≤ 2 * ballCreditLin ℓ W) :
    (∫⁻ z, ENNReal.ofReal (debPair W z / debLatD ℓ z))
      ≤ 3 * ∫⁻ z, ENNReal.ofReal (debPair W z / ‖z‖) := by
  classical
  have hAmeas : AEMeasurable (debPair W) MeasureTheory.volume :=
    (debPair_aestronglyMeasurable hW1).aemeasurable
  have hdmeas : AEMeasurable (fun z : EuclideanSpace ℝ (Fin 3) => debLatD ℓ z)
      MeasureTheory.volume := by
    have hcont : Continuous fun z : EuclideanSpace ℝ (Fin 3) =>
        Metric.infDist z (Set.range (fun n : Fin 3 → ℤ => Work.BoseFixR.lat ℓ n)) :=
      Metric.continuous_infDist_pt _
    simpa [debLatD] using hcont.aemeasurable
  have hg_ae : AEMeasurable (fun z : EuclideanSpace ℝ (Fin 3) =>
      ENNReal.ofReal (debPair W z / debLatD ℓ z)) MeasureTheory.volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hAmeas.div hdmeas)
  have hh_ae : AEMeasurable (fun z : EuclideanSpace ℝ (Fin 3) =>
      ENNReal.ofReal (debPair W z / ‖z‖)) MeasureTheory.volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hAmeas.div continuous_norm.aemeasurable)
  set B : Set (EuclideanSpace ℝ (Fin 3)) := Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (ℓ / 2)
    with hB
  set Cr : Set (EuclideanSpace ℝ (Fin 3)) :=
    {u : EuclideanSpace ℝ (Fin 3) | debLatD ℓ u < ‖u‖ / 3} with hCr
  set g : EuclideanSpace ℝ (Fin 3) → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (debPair W z / debLatD ℓ z) with hg
  set h : EuclideanSpace ℝ (Fin 3) → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (debPair W z / ‖z‖) with hh
  set p : ℝ≥0∞ := ∫⁻ z in B, h z with hp
  set q : ℝ≥0∞ := ∫⁻ z in Bᶜ, h z with hq
  -- the credit hypothesis, in terms of `p`
  have hcred : crescentDebitLin ℓ W ≤ 2 * p := by
    refine hdeb.trans (hcredit.trans (le_of_eq ?_))
    simp only [ballCreditLin, hp, h, hB]
  -- (1) the split at `B` for `g`
  have hsplitg : (∫⁻ z, g z) = (∫⁻ z in B, g z) + (∫⁻ z in Bᶜ, g z) :=
    (MeasureTheory.lintegral_add_compl (μ := MeasureTheory.volume) g measurableSet_ball).symm
  -- (2) on `B` the two integrands coincide
  have hBg : (∫⁻ z in B, g z) = p := by
    have heq : (fun z => g z) =ᵐ[MeasureTheory.volume.restrict B] h := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with z hz
      have hcoord : ∀ i : Fin 3, |z i| ≤ ‖z‖ := fun i => by
        have h' := PiLp.norm_apply_le (β := fun _ : Fin 3 => ℝ) z i
        simpa using h'
      have hzi : ∀ i : Fin 3, |z i| ≤ ℓ / 2 := by
        intro i
        have hz' : ‖z‖ < ℓ / 2 := by
          simpa [B, hB, Metric.mem_ball, dist_eq_norm] using hz
        linarith [hcoord i, hz']
      have hd : debLatD ℓ z = ‖z‖ := FarFold.infDist_lat_eq_norm_cell hℓ hzi
      simp only [hg, hh, hd]
    rw [hp]
    exact MeasureTheory.lintegral_congr_ae heq
  -- (3) on `Bᶜ` the deficit is paid by the crescent plus `3 * h`
  have hBcg : (∫⁻ z in Bᶜ, g z) ≤ crescentDebitLin ℓ W + 3 * q := by
    have hpt : g ≤ᵐ[MeasureTheory.volume.restrict Bᶜ]
        (fun z => Cr.indicator g z + 3 * h z) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball.compl] with z hz
      by_cases hzcr : z ∈ Cr
      · rw [Set.indicator_of_mem hzcr]
        exact le_add_of_nonneg_right (by positivity)
      · rw [Set.indicator_of_notMem hzcr, zero_add]
        have hdle : ‖z‖ / 3 ≤ debLatD ℓ z := le_of_not_gt hzcr
        have hAle : 0 ≤ debPair W z := debPair_nonneg_ae hWnn z
        have hzn : 0 < ‖z‖ := by
          rcases eq_or_lt_of_le (norm_nonneg z) with h0 | hpos
          · exfalso
            have hz0 : z = 0 := norm_eq_zero.mp h0.symm
            subst hz0
            refine hz ?_
            simp only [B, hB, Metric.mem_ball, dist_zero_right, norm_zero]
            positivity
          · exact hpos
        have hdpos : 0 < debLatD ℓ z := lt_of_lt_of_le (by positivity) hdle
        have hle : (1 : ℝ) / debLatD ℓ z ≤ 3 / ‖z‖ := by
          have h1 : (1 : ℝ) / debLatD ℓ z ≤ 1 / (‖z‖ / 3) :=
            one_div_le_one_div_of_le (by positivity) hdle
          rwa [one_div_div] at h1
        have hfac : debPair W z / debLatD ℓ z = debPair W z * (1 / debLatD ℓ z) := by ring
        have hfac2 : 3 * (debPair W z / ‖z‖) = debPair W z * (3 / ‖z‖) := by ring
        have hreal : debPair W z / debLatD ℓ z ≤ 3 * (debPair W z / ‖z‖) := by
          rw [hfac, hfac2]
          exact mul_le_mul_of_nonneg_left hle hAle
        calc g z = ENNReal.ofReal (debPair W z / debLatD ℓ z) := by rw [hg]
          _ ≤ ENNReal.ofReal (3 * (debPair W z / ‖z‖)) := ENNReal.ofReal_le_ofReal hreal
          _ = 3 * h z := by
              rw [hh, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
              norm_num
    have hmeas_ind : AEMeasurable (fun z => Cr.indicator g z)
        (MeasureTheory.volume.restrict Bᶜ) := by
      rw [hCr]
      exact (aemeasurable_indicator_iff (debSet_measurable ℓ)).mpr
        (hg_ae.mono_measure
          (le_trans Measure.restrict_le_self Measure.restrict_le_self))
    calc (∫⁻ z in Bᶜ, g z)
        ≤ ∫⁻ z in Bᶜ, (Cr.indicator g z + 3 * h z) := MeasureTheory.lintegral_mono_ae hpt
      _ = (∫⁻ z in Bᶜ, Cr.indicator g z) + 3 * (∫⁻ z in Bᶜ, h z) := by
          rw [MeasureTheory.lintegral_add_left' hmeas_ind,
            MeasureTheory.lintegral_const_mul'' 3
              (hh_ae.mono_measure Measure.restrict_le_self)]
      _ ≤ crescentDebitLin ℓ W + 3 * q := by
          refine add_le_add ?_ (le_of_eq (by rw [hq]))
          calc (∫⁻ z in Bᶜ, Cr.indicator g z)
              ≤ ∫⁻ z, Cr.indicator g z := by
                have hmono := MeasureTheory.lintegral_mono_set (μ := MeasureTheory.volume)
                  (f := fun z => Cr.indicator g z) (s := Bᶜ) (t := Set.univ) (Set.subset_univ _)
                simpa using hmono
            _ = ∫⁻ z in Cr, g z := MeasureTheory.lintegral_indicator (debSet_measurable ℓ) g
            _ = crescentDebitLin ℓ W := by
                rw [hCr, hg]
                rfl
  -- (4) the same split for `h`
  have hsplit_h : (∫⁻ z, h z) = p + q :=
    (MeasureTheory.lintegral_add_compl (μ := MeasureTheory.volume) h measurableSet_ball).symm
  calc (∫⁻ z, g z) = (∫⁻ z in B, g z) + (∫⁻ z in Bᶜ, g z) := hsplitg
    _ = p + (∫⁻ z in Bᶜ, g z) := by rw [hBg]
    _ ≤ p + (crescentDebitLin ℓ W + 3 * q) := add_le_add le_rfl hBcg
    _ ≤ p + (2 * p + 3 * q) := add_le_add le_rfl (add_le_add hcred le_rfl)
    _ = 3 * (p + q) := by ring
    _ = 3 * ∫⁻ z, h z := by
        congr 1
        exact hsplit_h.symm

/-- **Translation invariance of the `∫⁻` over a ball.**  Used to pass between the `ball c (ℓ/2)`
normalisation (six balls around `±ℓeᵢ`) and the `ball 0 (ℓ/2)` normalisation of
`crescentSixBallCredit`. -/
theorem lintegral_ball_add_eq {r : ℝ} (c : EuclideanSpace ℝ (Fin 3))
    {f : EuclideanSpace ℝ (Fin 3) → ℝ≥0∞} (hf : AEMeasurable f MeasureTheory.volume) :
    (∫⁻ v in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r, f (c + v))
      = ∫⁻ u in Metric.ball c r, f u := by
  classical
  have hmap : MeasureTheory.Measure.map (fun v : EuclideanSpace ℝ (Fin 3) => v + c)
      MeasureTheory.volume = MeasureTheory.volume :=
    MeasureTheory.map_add_right_eq_self MeasureTheory.volume c
  have hg : AEMeasurable (fun v : EuclideanSpace ℝ (Fin 3) => v + c) MeasureTheory.volume :=
    (measurable_id.add_const c).aemeasurable
  have hFae : AEMeasurable ((Metric.ball c r).indicator f) MeasureTheory.volume :=
    hf.indicator measurableSet_ball
  have key : (∫⁻ u, (Metric.ball c r).indicator f u)
      = ∫⁻ v, (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r).indicator (fun v => f (c + v)) v := by
    have h1 : (∫⁻ u, (Metric.ball c r).indicator f u)
        = ∫⁻ v, (Metric.ball c r).indicator f v
            ∂(MeasureTheory.Measure.map (fun v : EuclideanSpace ℝ (Fin 3) => v + c)
              MeasureTheory.volume) := by
      rw [hmap]
    have h2 : (∫⁻ v, (Metric.ball c r).indicator f v
            ∂(MeasureTheory.Measure.map (fun v : EuclideanSpace ℝ (Fin 3) => v + c)
              MeasureTheory.volume))
        = ∫⁻ v, (Metric.ball c r).indicator f (v + c) :=
      MeasureTheory.lintegral_map' (hFae.mono_measure (le_of_eq hmap)) hg
    have h3 : (∫⁻ v, (Metric.ball c r).indicator f (v + c))
        = ∫⁻ v, (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r).indicator (fun v => f (c + v)) v := by
      refine MeasureTheory.lintegral_congr fun v => ?_
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hv : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r
      · have hv' : v + c ∈ Metric.ball c r := by
          simpa [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right] using hv
        rw [if_pos hv', if_pos hv]
        congr 1
        abel
      · have hv' : v + c ∉ Metric.ball c r := by
          intro hh
          exact hv (by simpa [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right] using hh)
        rw [if_neg hv', if_neg hv]
    rw [h1, h2, h3]
  rw [← MeasureTheory.lintegral_indicator (μ := MeasureTheory.volume) measurableSet_ball
      (fun v => f (c + v)), ← key,
    MeasureTheory.lintegral_indicator (μ := MeasureTheory.volume) measurableSet_ball f]

/-- **The `∫⁻` crux from the six-ball credit alone**, the crescent capture being the proved
`Work.BoseFixR.debCredit_lintegral_le_sixBall`. -/
theorem farLatPosGen_lintegral_of_sixBallCredit {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R)
    (h2R : 2 * R < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW1 : MeasureTheory.Integrable W)
    (hWnn : 0 ≤ᵐ[MeasureTheory.volume] W)
    (hsupp : tsupport W ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hcredit : sixBallDebitLin ℓ W ≤ 2 * ballCreditLin ℓ W) :
    (∫⁻ z, ENNReal.ofReal (debPair W z / debLatD ℓ z))
      ≤ 3 * ∫⁻ z, ENNReal.ofReal (debPair W z / ‖z‖) :=
  farLatPosGen_lintegral_of_credits hℓ hR h2R hW1 hWnn hsupp
    (debCredit_lintegral_le_sixBall hℓ hR h2R hW1 hWnn hsupp) hcredit

/-- **From the `∫⁻` crux to the Bochner crux.**  Both sides are integrals of a.e.-nonnegative
functions, so `MeasureTheory.integral_eq_lintegral_of_nonneg_ae` (no integrability needed) plus
the a.e. dominance `A/‖·‖ ≤ A/d_ℓ` (which transfers `= ∞`) gives the statement. -/
theorem farLatPosGen_of_lintegral {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R) (h2R : 2 * R < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW1 : MeasureTheory.Integrable W)
    (hWnn : 0 ≤ᵐ[MeasureTheory.volume] W)
    (hsupp : tsupport W ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hlin : (∫⁻ z, ENNReal.ofReal (debPair W z / debLatD ℓ z))
      ≤ 3 * ∫⁻ z, ENNReal.ofReal (debPair W z / ‖z‖)) :
    (∫ z, debPair W z / debLatD ℓ z) ≤ 3 * ∫ z, debPair W z / ‖z‖ := by
  classical
  have hAmeas : AEMeasurable (debPair W) MeasureTheory.volume :=
    (debPair_aestronglyMeasurable hW1).aemeasurable
  have hdcont : Continuous fun z : EuclideanSpace ℝ (Fin 3) => debLatD ℓ z := by
    have h1 : Continuous fun z : EuclideanSpace ℝ (Fin 3) =>
        Metric.infDist z (Set.range (fun n : Fin 3 → ℤ => Work.BoseFixR.lat ℓ n)) :=
      Metric.continuous_infDist_pt _
    simpa [debLatD] using h1
  have hg1 : ∫ z, debPair W z / debLatD ℓ z
      = (∫⁻ z, ENNReal.ofReal (debPair W z / debLatD ℓ z)).toReal := by
    refine MeasureTheory.integral_eq_lintegral_of_nonneg_ae ?_ ?_
    · filter_upwards with z
      exact div_nonneg (debPair_nonneg_ae hWnn z) (debLatD_nonneg ℓ z)
    · exact (hAmeas.div hdcont.aemeasurable).aestronglyMeasurable
  have hg2 : ∫ z, debPair W z / ‖z‖
      = (∫⁻ z, ENNReal.ofReal (debPair W z / ‖z‖)).toReal := by
    refine MeasureTheory.integral_eq_lintegral_of_nonneg_ae ?_ ?_
    · filter_upwards with z
      exact div_nonneg (debPair_nonneg_ae hWnn z) (norm_nonneg z)
    · exact (hAmeas.div (continuous_norm.aemeasurable)).aestronglyMeasurable
  have hdom : (fun z => ENNReal.ofReal (debPair W z / ‖z‖))
      ≤ᵐ[MeasureTheory.volume] (fun z => ENNReal.ofReal (debPair W z / debLatD ℓ z)) := by
    filter_upwards [debPair_div_norm_le_div_debLatD_ae hℓ h2R hW1 hWnn hsupp] with z hz
    exact ENNReal.ofReal_le_ofReal hz
  have hle : (∫⁻ z, ENNReal.ofReal (debPair W z / ‖z‖))
      ≤ ∫⁻ z, ENNReal.ofReal (debPair W z / debLatD ℓ z) :=
    MeasureTheory.lintegral_mono_ae hdom
  have htop : (3 * ∫⁻ z, ENNReal.ofReal (debPair W z / ‖z‖)) = ⊤ →
      (∫⁻ z, ENNReal.ofReal (debPair W z / debLatD ℓ z)) = ⊤ := by
    intro h3
    have h2 : (∫⁻ z, ENNReal.ofReal (debPair W z / ‖z‖)) = ⊤ := by
      by_contra hne
      exact (ENNReal.mul_ne_top (by norm_num) hne) h3
    exact top_le_iff.mp (h2 ▸ hle)
  have hkey : (∫⁻ z, ENNReal.ofReal (debPair W z / debLatD ℓ z)).toReal
      ≤ (3 * ∫⁻ z, ENNReal.ofReal (debPair W z / ‖z‖)).toReal :=
    ENNReal.toReal_mono' hlin htop
  calc ∫ z, debPair W z / debLatD ℓ z
      = (∫⁻ z, ENNReal.ofReal (debPair W z / debLatD ℓ z)).toReal := hg1
    _ ≤ (3 * ∫⁻ z, ENNReal.ofReal (debPair W z / ‖z‖)).toReal := hkey
    _ = 3 * (∫⁻ z, ENNReal.ofReal (debPair W z / ‖z‖)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat]
    _ = 3 * ∫ z, debPair W z / ‖z‖ := by rw [hg2]

end IntegralRoute

/-- **THE GAP, isolated and generalised (the crux in the shape everything else produces).**

For `ℓ > 0`, `R > 0`, `R ≤ ℓ·chiR0` (the dilute regime) and a **nonnegative a.e. integrable** charge
`W` with `tsupport W ⊆ ball 0 R`:

`∫ z, (∫ x, W x · W (x+z)) / d_ℓ(z)  ≤  3 · ∫ z, (∫ x, W x · W (x+z)) / ‖z‖`,  `d_ℓ = infDist · (lat ℓ ·)`.

This is the *only* remaining input of `latSampling_le` (hence of `farLatRow`): the two other steps
are PROVED (`Work.BoseFixR.farLatParseval` : `Q ≤ (ℓ³/4π)·LHS`, `Work.BoseFixR.farLatFourier` :
`RHS = 8π·farMass`), so the constant `3` here is exactly the target's constant.  The hypotheses
(`Integrable W`, `0 ≤ᵐ W`, `tsupport W ⊆ ball 0 R`, `R ≤ ℓ·chiR0`) are the minimal ones used by the
sibling "nearest image" project (`Submission/Work/BoseFixR/FZW/NearestImageCoulomb_lintegral_le.lean`,
same inequality in the `∫⁻`-product form): no evenness, no `MemLp W 2`.

**Truth.**  TRUE, sharp constant `2` (two equal clumps at a lattice separation `±ℓeᵢ/2`; unequal
masses `q₁,q₂` give `1 + 2q₁q₂/(q₁²+q₂²) ≤ 2`).  Numerically `D/F ≤ 2` on every profile tested
(`FINDING_farLatRow_sharp6.md` §3–§4 and the FZW tables).

**Do not retry** (`FINDING_farLatRow_sharp6.md` §3, §6, `FZW/FINDING_crescent.md` §B/§E/§F):
the per-`r`/per-`ρ` layer cake (FALSE), any pointwise-in-`δ`-or-`u` comparison (FALSE, ratios up
to 500 resp. 3), the heat-`t` comparison (FALSE), the sphere average (FALSE), the per-`x` potential
comparison (FALSE), and the "six signed unit directions" mass bound `Σ_{|n|=1}ν(ℓn+δ) ≤ ν(0)` —
that one is PROVED (`Work.BoseFixR.FZW.sum_signedUnitShift_autocorr_le_self`, and
`Work.BoseFixR.LatGreen.matchingHalf` for the three positive directions) but is 2.8× too lossy
once integrated, because `ν(ℓn+·)` is concentrated on a far thinner `δ`-set than `ν(0)` suggests.
Surviving shapes: the genuinely two-variable integrated ones — the `u`-resolved reduction `(T′)`
(`FZW/FINDING_badRegionCoulomb.md` §1) and its uniform-in-`ρ` form (D1)
(`FZW/FINDING_crescent.md` §E), and the cluster ledger of `FZW` §R.2 (debit = image interactions,
credit = cluster self-energies, AM–GM `m_im_j/D_ij ≤ (√(ρ_iρ_j)/2D_ij)(m_i²/ρ_i + m_j²/ρ_j)`,
closing because `D_ij ≥ ρ_i + ρ_j`).

**SESSION 2618 — the state of this crux; read `FINDING_farLatRow_sharp8.md` FIRST.**  The crux is
now reduced to *two* clean delegated statements, but *this* statement must be **restated with two
extra hypotheses** before it can be consumed:

* add `(hWb : ∃ C, ∀ x, |W x| ≤ C)` (boundedness — needed for the finiteness of the
  `1/‖·‖`-weighted integrals of the pieces).  For `W = W1fun v h (ell v μ)` this is available from
  `Submission.BoseGases.abs_w_scaled_le`;
* replace `hWnn : 0 ≤ᵐ W` by the *pointwise* `0 ≤ W`, or keep the a.e. form and bridge at the end:
  `Work.BoseFixR.cruxAeBridge` (**proved**) identifies *both* sides of the crux for `W` and for
  `W' := fun x => max (W x) 0` (pointwise `≥ 0`, bounded by `|W|`, same `tsupport`, equal a.e.).

The route is then: crescent capture **(CAP)** = `Work.BoseFixR.deb_le_sixBall`
(`Deb ≤ Σ_{‖n‖=1}∫_{B(0,ℓ/2)}A(ℓn+v)/‖v‖dv`) `→` **(Q)** = `Work.BoseFixR.K_shift_le`
(`Σ_{‖n‖=1}⟨W,T_{ℓn}W⟩_K ≤ 2⟨W,W⟩_K` with `K = 1_{B(0,ℓ/2)}/‖·‖`: the *weighted*
matching/AM–GM statement, numerically true with ≈ `2.5×` of margin) `→` `Deb ≤ 2S`
(`B(0,ℓ/2) ⊆ V₀`) `→` `D ≤ 3F` (two lines of algebra, `sharp8` §2).
**Do NOT consume `Work.BoseFixR.latPairMass_far_le_near`: it is FALSE
(`FINDING_latPairMass_far_le_near_FALSE.md`, six point masses, ratio 1.52), and the layer-cake
route through it is dead.** -/
theorem farLatPosGen {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW1 : MeasureTheory.Integrable W)
    (hWnn : 0 ≤ᵐ[MeasureTheory.volume] W)
    (hsupp : tsupport W ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    (∫ z : EuclideanSpace ℝ (Fin 3),
        (∫ x : EuclideanSpace ℝ (Fin 3), W x * W (x + z))
        / Metric.infDist z (Set.range (fun n : Fin 3 → ℤ => Work.BoseFixR.lat ℓ n)))
      ≤ 3 * ∫ z : EuclideanSpace ℝ (Fin 3),
          (∫ x : EuclideanSpace ℝ (Fin 3), W x * W (x + z)) / ‖z‖ := by
  sorry

/-- **The crux at the far-leg charge `W = W₁ = W1fun v h (ell v μ)`**, an immediate instance of
`farLatPosGen`: the three hypotheses it consumes are available for `W₁` — `Integrable W₁`
(`Submission.BoseGases.wScaled_g0_integrable`), `0 ≤ᵐ W₁`
(`Submission.BoseGases.wScaled_g0_nonneg_ae`) and `tsupport W₁ ⊆ ball 0 R`
(`Work.BoseFixR.tsupport_W1fun_subset`). -/
theorem farLatPosW1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) {μ : ℝ} (hμ : 0 < μ)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0) :
    (∫ z : EuclideanSpace ℝ (Fin 3),
        (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ) x
          * Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ) (x + z))
        / Metric.infDist z (Set.range (fun n : Fin 3 → ℤ => Work.BoseFixR.lat (Work.BoseFixR.ell v μ) n)))
      ≤ 3 * ∫ z : EuclideanSpace ℝ (Fin 3),
          (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ) x
            * Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ) (x + z)) / ‖z‖ :=
  farLatPosGen (Work.BoseFixR.ell_pos' v hμ hav) hR hRℓ
    (Submission.BoseGases.wScaled_g0_integrable hR hv_supp h (Work.BoseFixR.ell_pos' v hμ hav) hRℓ)
    (Submission.BoseGases.wScaled_g0_nonneg_ae hR hv hvrad hv_supp h)
    (Work.BoseFixR.tsupport_W1fun_subset h hv_supp (Work.BoseFixR.ell v μ))

/-- **The weighted lattice sampling inequality.**

`Σ'_{k≠0} Ŵ(q_k)²/‖q_k‖² ≤ 3·ℓ³·(2π)^{-3}·∫_q Ŵ(q)²/‖q‖² dq` with `q_k = ℓ⁻¹ • vec k`, `ℓ = ell v μ`.

**Proved here from `farLatPosW1` (the crux) and the two *proved* inputs
`Work.BoseFixR.farLatParseval` (`Q ≤ (ℓ³/4π)·D`) and `Work.BoseFixR.farLatFourier`
(`F = 8π·farMass`); the arithmetic is exactly `(1/2)·(ℓ³/4π)·3·8π = 3ℓ³`.**  The pointwise kernel
bound `K_♯(z) ≤ ℓ³K₀(z)` is false on the image cells (`FINDING_farLatRow_sharp2.md` §1), which is
why the crux is needed. -/
theorem latSampling_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) {μ : ℝ} (hμ : 0 < μ)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0) :
    (∑' k : Fin 3 → ℤ, if k = 0 then 0 else
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
            ((Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec k)) ^ 2
          / ‖(Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec k‖ ^ 2)
      ≤ 3 * (Work.BoseFixR.ell v μ) ^ 3 * ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ q : EuclideanSpace ℝ (Fin 3),
            (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) q) ^ 2
              / ‖q‖ ^ 2 := by
  have hℓ : 0 < Work.BoseFixR.ell v μ := Work.BoseFixR.ell_pos' v hμ hav
  have hP := Work.BoseFixR.farLatParseval h hv hvrad hR hv_supp hav hμ hRℓ
  have hC := farLatPosW1 h hv hvrad hR hv_supp hav hμ hRℓ
  have hF := Work.BoseFixR.farLatFourier h hv hvrad hR hv_supp hav hμ hRℓ
  have hfar : Work.BoseFixR.farMass v h μ
      = ((2 * Real.pi) ^ 3)⁻¹ * (1 / 2) * ∫ q : EuclideanSpace ℝ (Fin 3),
          (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) q) ^ 2
            / ‖q‖ ^ 2 := by
    rw [Work.BoseFixR.farMass]
    have hcongr : (∫ q : EuclideanSpace ℝ (Fin 3),
          (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) q) ^ 2
            / (2 * ‖q‖ ^ 2))
        = (1 / 2) * ∫ q : EuclideanSpace ℝ (Fin 3),
            (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) q) ^ 2
              / ‖q‖ ^ 2 := by
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun q => by ring)
    rw [hcongr]
    ring
  calc (∑' k : Fin 3 → ℤ, if k = 0 then 0 else
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
            ((Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec k)) ^ 2
          / ‖(Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec k‖ ^ 2)
      ≤ (Work.BoseFixR.ell v μ) ^ 3 / (4 * Real.pi) *
          ∫ z : EuclideanSpace ℝ (Fin 3),
            (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ) x
              * Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ) (x + z))
            / Metric.infDist z (Set.range (fun n : Fin 3 → ℤ =>
                Work.BoseFixR.lat (Work.BoseFixR.ell v μ) n)) := hP
    _ ≤ (Work.BoseFixR.ell v μ) ^ 3 / (4 * Real.pi) *
          (3 * ∫ z : EuclideanSpace ℝ (Fin 3),
            (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ) x
              * Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ) (x + z)) / ‖z‖) :=
        mul_le_mul_of_nonneg_left hC (by positivity)
    _ = 3 * (Work.BoseFixR.ell v μ) ^ 3 * ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ q : EuclideanSpace ℝ (Fin 3),
            (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) q) ^ 2
              / ‖q‖ ^ 2 := by
        rw [hF, hfar]
        have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
        field_simp
        ring

/-! ## The target

`farLatRow` is now pure bookkeeping: `latRowLeTsum` (the honest cube `≤` the full lattice) and
`latSampling_le`, together with the identification `farMass = (2π)^{-3}∫Ŵ²/(2‖q‖²)`. -/

theorem farLatRow {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) {μ : ℝ} (hμ : 0 < μ)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0) (N : ℕ) :
    Work.BoseFixR.latRow v h μ N ≤ 3 * (Work.BoseFixR.ell v μ) ^ 3 * Work.BoseFixR.farMass v h μ := by
  have hell : 0 < Work.BoseFixR.ell v μ := Work.BoseFixR.ell_pos' v hμ hav
  have hsum := W1funRowSummable h hv hvrad hR hell hv_supp hRℓ
  have h1 := Work.BoseFixR.LatGreen.latRowLeTsum (h := h) (μ := μ) N hsum
  have h2 := latSampling_le h hv hvrad hR hv_supp hav hμ hRℓ
  -- `farMass` in terms of the un-halved integral
  have hfar : Work.BoseFixR.farMass v h μ
      = ((2 * Real.pi) ^ 3)⁻¹ * (1 / 2) * ∫ q : EuclideanSpace ℝ (Fin 3),
          (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) q) ^ 2
            / ‖q‖ ^ 2 := by
    rw [Work.BoseFixR.farMass]
    have hcongr : (∫ q : EuclideanSpace ℝ (Fin 3),
          (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) q) ^ 2
            / (2 * ‖q‖ ^ 2))
        = (1 / 2) * ∫ q : EuclideanSpace ℝ (Fin 3),
            (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) q) ^ 2
              / ‖q‖ ^ 2 := by
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun q => by ring)
    rw [hcongr]
    ring
  rw [hfar]
  calc Work.BoseFixR.latRow v h μ N
      ≤ (1 / 2) * (∑' k : Fin 3 → ℤ, if k = 0 then 0 else
          (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
              ((Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec k)) ^ 2
            / ‖(Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec k‖ ^ 2) := h1
    _ ≤ (1 / 2) * (3 * (Work.BoseFixR.ell v μ) ^ 3 * ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ q : EuclideanSpace ℝ (Fin 3),
            (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) q) ^ 2
              / ‖q‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ = 3 * (Work.BoseFixR.ell v μ) ^ 3 *
          (((2 * Real.pi) ^ 3)⁻¹ * (1 / 2) * ∫ q : EuclideanSpace ℝ (Fin 3),
            (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) q) ^ 2
              / ‖q‖ ^ 2) := by ring

end Work.BoseFixR
