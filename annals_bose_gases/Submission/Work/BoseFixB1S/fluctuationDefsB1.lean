import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.rPsiB_nonneg
import Submission.Work.BoseFixB1B.RsbSide_sq_le_holds
import Submission.Work.BoseFixB1B.integratedOfPointwise
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.fluctuationDefsB1` — the vocabulary of the two-count
fluctuation bound (`FINDING_sectorPassageLowB1_session2.md` §3.1)

The target `Work.BoseFixB1S.sectorPassageLowB1` reduces (modulo proved corpus material) to the
`IsLowB`-restricted flat arm, whose only new analytic input is the comparison of the **smooth**
per-box count `t = nCountB/chiMass` with the **sharp** (indicator) per-box count
`s = n_B/boxMass`.  This module fixes the vocabulary of that comparison:

* `boxSharpCountB` — FS's `n_{B(u)} = Σᵢ1_{B(u)}(xᵢ)`;
* `inBoxIndN` — the indicator of the box sector `B(u)^n`;
* `smoothDensB`, `sharpDensB` — the two densities `t`, `s`;
* `boxAmpB` — the uniform pointwise bound `K₀ = sup|χ_{B(u)}|²/chiMass + 1/boxMass` on the
  difference density `χ_{B(u)}²/chiMass − 1_{B(u)}/boxMass`.

Everything is stated with the corpus's own objects (`Work.BoseFixB1.nCountB`,
`Work.SmallBoxSliding.chiMass`, `Work.SmallBoxSliding.boxMass`,
`Work.UBBInputs8.cnPlusBoxInd`), so no new analysis is introduced here.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- FS's **sharp** per-box count `n_{B(u)}(x) = Σᵢ 1_{B(u)}(xᵢ)` (`eq:smallboxnn0n+`). -/
noncomputable def boxSharpCountB {n : ℕ} (ℓ d : ℝ) (u : E3)
    (x : Submission.BoseGases.X n) : ℝ :=
  ∑ i : Fin n, (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)

/-- The indicator of the box sector `B(u)^n` (all coordinates in the sliding box). -/
noncomputable def inBoxIndN (n : ℕ) (ℓ d : ℝ) (u : E3) :
    Submission.BoseGases.X n → ℝ :=
  (Set.univ.pi (fun _ : Fin n => Submission.BoseGases.dlBox ℓ d u)).indicator
    (fun _ => (1 : ℝ))

/-- The **smooth** per-box density `t = nCountB/chiMass`. -/
noncomputable def smoothDensB {n : ℕ} (M : ℕ) (ℓ d : ℝ) (u : E3)
    (x : Submission.BoseGases.X n) : ℝ :=
  Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u

/-- The **sharp** per-box density `s = n_{B(u)}/|B(u)|`. -/
noncomputable def sharpDensB {n : ℕ} (ℓ d : ℝ) (u : E3)
    (x : Submission.BoseGases.X n) : ℝ :=
  boxSharpCountB ℓ d u x / Work.SmallBoxSliding.boxMass ℓ d u

/-- The uniform bound on the difference density
`χ_{B(u)}(z)²/chiMass − 1_{B(u)}(z)/|B(u)|`: `K₀ = (chiSupAbs·chiSmallDecay M)²/chiMass + 1/|B(u)|`,
from `|χ_{B(u)}| ≤ chiSupAbs·chiSmallDecay M` (`Work.SmallBoxSliding.abs_chiSmallB_le`) and
`1_{B(u)}/|B(u)| ≤ 1/|B(u)|`. -/
noncomputable def boxAmpB (M : ℕ) (ℓ d : ℝ) (u : E3) : ℝ :=
  (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
      / Work.SmallBoxSliding.chiMass M ℓ d u
    + 1 / Work.SmallBoxSliding.boxMass ℓ d u

/-- The same difference density as a function of `z`. -/
noncomputable def boxDiffDensB (M : ℕ) (ℓ d : ℝ) (u : E3) (z : E3) : ℝ :=
  (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2 / Work.SmallBoxSliding.chiMass M ℓ d u
    - (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) z
        / Work.SmallBoxSliding.boxMass ℓ d u

/-! ## 1. The pointwise bounds -/

lemma boxSharpCountB_nonneg {n : ℕ} (ℓ d : ℝ) (u : E3)
    (x : Submission.BoseGases.X n) : 0 ≤ boxSharpCountB ℓ d u x := by
  refine Finset.sum_nonneg (fun i _ => ?_)
  by_cases h : x i ∈ Submission.BoseGases.dlBox ℓ d u
  · rw [Set.indicator_of_mem h]; norm_num
  · rw [Set.indicator_of_notMem h]

lemma boxSharpCountB_le_card {n : ℕ} (ℓ d : ℝ) (u : E3)
    (x : Submission.BoseGases.X n) : boxSharpCountB ℓ d u x ≤ (n : ℝ) := by
  calc boxSharpCountB ℓ d u x ≤ ∑ _i : Fin n, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        by_cases h : x i ∈ Submission.BoseGases.dlBox ℓ d u
        · rw [Set.indicator_of_mem h]
        · rw [Set.indicator_of_notMem h]; norm_num
    _ = (n : ℝ) := by simp

/-- `|chiSmallB M ℓ d u z| ≤ chiSupAbs · chiSmallDecay M` (the corpus sup bound). -/
lemma abs_chiSmallB_le_supB {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (u z : E3) :
    |Submission.BoseGases.chiSmallB M ℓ d u z|
      ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
  refine (Work.SmallBoxSliding.abs_chiSmallB_le hM u z).trans ?_
  have h2 : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z - u)
      ≤ Submission.BoseGases.chiSmallDecay M := by
    have h := Submission.BoseGases.chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • z - u)
    rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at h
  exact mul_le_mul_of_nonneg_left h2 Submission.BoseGases.chiSupAbs_nonneg

/-- **The pointwise bound on the difference density**: `|χ²/chiMass − 1_B/|B|| ≤ boxAmpB`. -/
theorem boxDiffDensB_abs_le_amp {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (u : E3)
    (hχ : 0 < Work.SmallBoxSliding.chiMass M ℓ d u)
    (hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u) (z : E3) :
    |boxDiffDensB M ℓ d u z| ≤ boxAmpB M ℓ d u := by
  have hle := abs_chiSmallB_le_supB hM (ℓ := ℓ) (d := d) u z
  have hsq : (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2
      ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hle 2
  have hind : (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) z ≤ 1 := by
    by_cases h : z ∈ Submission.BoseGases.dlBox ℓ d u
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h]; norm_num
  have hind0 : 0 ≤ (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) z := by
    by_cases h : z ∈ Submission.BoseGases.dlBox ℓ d u
    · rw [Set.indicator_of_mem h]; norm_num
    · rw [Set.indicator_of_notMem h]
  calc |boxDiffDensB M ℓ d u z|
      ≤ |(Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2
            / Work.SmallBoxSliding.chiMass M ℓ d u|
          + |(Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) z
              / Work.SmallBoxSliding.boxMass ℓ d u| :=
        abs_sub _ _
    _ = (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2
            / Work.SmallBoxSliding.chiMass M ℓ d u
          + (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) z
              / Work.SmallBoxSliding.boxMass ℓ d u := by
        rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hχ.le),
          abs_of_nonneg (div_nonneg hind0 hV.le)]
    _ ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
            / Work.SmallBoxSliding.chiMass M ℓ d u + 1 / Work.SmallBoxSliding.boxMass ℓ d u :=
        add_le_add (div_le_div_of_nonneg_right hsq hχ.le)
          (div_le_div_of_nonneg_right hind hV.le)
    _ = boxAmpB M ℓ d u := rfl

/-- The smooth density as a sum of per-slot densities. -/
lemma smoothDensB_eq_sum {M n : ℕ} (ℓ d : ℝ) (u : E3) (x : Submission.BoseGases.X n) :
    smoothDensB M ℓ d u x
      = ∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
          / Work.SmallBoxSliding.chiMass M ℓ d u := by
  rw [smoothDensB, Work.BoseFixB1.nCountB, Finset.sum_div]

/-- The sharp density as a sum of per-slot densities. -/
lemma sharpDensB_eq_sum {n : ℕ} (ℓ d : ℝ) (u : E3) (x : Submission.BoseGases.X n) :
    sharpDensB ℓ d u x
      = ∑ i : Fin n, (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)
          / Work.SmallBoxSliding.boxMass ℓ d u := by
  rw [sharpDensB, boxSharpCountB, Finset.sum_div]

/-- **The two counts differ by at most `n·boxAmpB`**: `|t − s| ≤ n·K₀`. -/
theorem smoothDensB_sub_sharpDensB_abs_le {M n : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (u : E3)
    (hχ : 0 < Work.SmallBoxSliding.chiMass M ℓ d u)
    (hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u) (x : Submission.BoseGases.X n) :
    |smoothDensB M ℓ d u x - sharpDensB ℓ d u x| ≤ (n : ℝ) * boxAmpB M ℓ d u := by
  rw [smoothDensB_eq_sum, sharpDensB_eq_sum, ← Finset.sum_sub_distrib]
  calc |∑ i : Fin n, ((Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
          / Work.SmallBoxSliding.chiMass M ℓ d u
        - (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)
          / Work.SmallBoxSliding.boxMass ℓ d u)|
      = |∑ i : Fin n, boxDiffDensB M ℓ d u (x i)| :=
        congrArg abs (Finset.sum_congr rfl (fun i _ => (rfl : _ = boxDiffDensB M ℓ d u (x i))))
    _ ≤ ∑ i : Fin n, |boxDiffDensB M ℓ d u (x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, boxAmpB M ℓ d u :=
        Finset.sum_le_sum (fun i _ => boxDiffDensB_abs_le_amp hM u hχ hV (x i))
    _ = (n : ℝ) * boxAmpB M ℓ d u := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## 2. The pointwise algebraic comparison of the two `F`-weights -/

/-- **The `F`-comparison**: writing `F = psiWeight 1 μ`, for `t, s ≥ 0` and `μ > 0`,

    F(t) ≤ 2(t − s)² + 2(1 + s/μ)·F(s) .

Proof: `F(t) ≤ (t−μ)² ≤ 2(t−s)² + 2(s−μ)²` and `(s−μ)² = F(s)·(μ+s)/μ = F(s)(1+s/μ)`. -/
theorem psiWeight_le_two_sq_add {μ t s : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    Work.SmallBoxSliding.psiWeight 1 μ t
      ≤ 2 * (t - s) ^ 2 + 2 * (1 + s / μ) * Work.SmallBoxSliding.psiWeight 1 μ s := by
  have hden : (1 : ℝ) + t * μ⁻¹ = (μ + t) / μ := by field_simp
  have hpos : 0 < 1 + t * μ⁻¹ := by
    rw [hden]; positivity
  have h1 : Work.SmallBoxSliding.psiWeight 1 μ t ≤ (t - μ) ^ 2 := by
    rw [Work.SmallBoxSliding.psiWeight, one_mul, div_le_iff₀ hpos]
    nlinarith [sq_nonneg (t - μ), mul_nonneg (sq_nonneg (t - μ)) (by positivity : (0:ℝ) ≤ t * μ⁻¹)]
  have hspos : (0 : ℝ) < 1 + s * μ⁻¹ := by
    have : (1 : ℝ) + s * μ⁻¹ = (μ + s) / μ := by field_simp
    rw [this]; positivity
  have h2 : (s - μ) ^ 2 = (1 + s / μ) * Work.SmallBoxSliding.psiWeight 1 μ s := by
    rw [Work.SmallBoxSliding.psiWeight, one_mul]
    field_simp
  have h3 : (t - μ) ^ 2 ≤ 2 * (t - s) ^ 2 + 2 * (s - μ) ^ 2 := by
    nlinarith [sq_nonneg ((t - s) - (s - μ))]
  linarith [h1, h3, h2]

end Work.BoseFixB1S
