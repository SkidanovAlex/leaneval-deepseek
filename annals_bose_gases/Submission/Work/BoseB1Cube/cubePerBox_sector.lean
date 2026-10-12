import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.CubeRows
import Submission.Work.BoseB1Cube.sbWordCube_sectorAdditive
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.cubePerBox_sector` — the **left-hand half** of the sector
# (arity) additivity of the cube per-box row

FS's proof of `thm:smallbox` splits a state by the number `n_B(u)` of particles in the sliding box
`B(u)`, proves the per-box bound on each *sector piece*, and adds.  The corpus has the **right-hand
half** of that argument: the word is sector-additive,

    `Work.BoseFixB1B.sbWordCube_sectorAdditive`
      `sbWordCube v h μ u Φ = Σ_k (sbKinCube v h μ u Φ_k + sbPot h μ u Φ_k)` ,
    `Φ_k = Work.FockBridge.sectorPiece (dlBox ℓ d u) k Φ`  (`= 1_{n_{B(u)} = k}·Φ`),

(`Submission/Work/BoseB1Cube/sbWordCube_sectorAdditive.lean`, PROVED; its ball-window twin
`Work.BoseFixB1.sbWordSectorAdditiveAdm` is likewise PROVED).

What was **missing** — and is proved here — is the matching statement for the *demand side*: the
number `perBoxCubeLHS` is sector-additive as well.  The reason it is not formal bookkeeping is that
`perBoxCubeLHS` is **not linear in the state**: its `F`-weight is evaluated at the *configuration*
density `nCountB(x)/chiMass`, so the identity `∫Φ²W = Σ_k ∫Φ_k²W` needs both the disjointness of
the sectors (`Φ² = Σ_k Φ_k²` pointwise, `Work.FockBridge.sum_sectorPiece_sq`) and the fact that the
weight `W` is a function of the *configuration*, not of the amplitude.

## What this gives

* `perBoxCubeLHSFun` — the demand as a number for an *arbitrary* function (the `Prop`
  `PerBoxFCube` is stated for `BoxState`s; the sector pieces are **not** smooth — `1_{n_B = k}` is
  an indicator — so the arity step needs the numeric form on the wider class);
* `Work.BoseB1Cube.integral_sq_mul_eq_sum_sectorPiece` — the weight identity;
* `Work.BoseB1Cube.normB_eq_sum_sectorPiece` — the `L²`-mass identity;
* **`Work.BoseB1Cube.perBoxCubeLHSFun_eq_sum_sectorPiece`** — the demand additivity;
* `Work.BoseB1Cube.perBoxFCube_of_sectorPieces` — the row for `Φ` from the rows for its sector
  pieces (the assembly the arity step needs; the word additivity is a *hypothesis* here so that the
  two halves compose at the caller's `ε₀`).

## Status of the arity step after this module

With both halves in place, the remaining content of "`CubePerBoxLocal ⟹ CubePerBox`" (recorded in
`Submission/Work/BoseB1Cube/FINDING_cube_chapter.md` §4 and `WordRow.lean` as the fleet's open
arity step) is **not** additivity but the passage from `Φ_k` to the *in-box* state: a sector piece
has `k` slots in `B(u)` and `n − k` outside it, and every box functional of `Φ_k` is a functional
of the *partial trace* of `|Φ_k|²` over the out-of-box slots (equivalently: of the `k`-particle
reduced density matrix on the box).  That passage — conditioning, plus the fact that the row is a
*linear* inequality in that partial trace, so that it transfers from pure in-box states to the
reduced state — is what a consumer of this module still has to supply.  The linearity is what makes
it viable at all, and it is the reason the two halves below must both be available.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 0. A local nonnegativity brick -/

/-- `nCountB ≥ 0` — local, to keep this module's cone free of `BoseFixB1S`'s copy. -/
lemma nCountB_nonneg_loc {M : ℕ} (ℓ d : ℝ) (u : E3) {n : ℕ} (x : X n) :
    0 ≤ Work.BoseFixB1.nCountB M ℓ d u x := by
  rw [Work.BoseFixB1.nCountB]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-! ## 1. The demand as a number, on an arbitrary function -/

/-- The demand side of `PerBoxFCube`, as a number, for an arbitrary function `Φ : X n → ℝ`. -/
noncomputable def perBoxCubeLHSFun (v : E3 → ℝ) (h : ScatSol v) (R c₁ C : ℝ) (μ : ℝ) (n : ℕ)
    (Φ : X n → ℝ) (u : E3) : ℝ :=
  c₁ * (Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u *
        (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
          Work.SmallBoxSliding.psiWeight 1 μ
            (Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
              Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u)))
    - (1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u * normB v μ n Φ
    - C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
            + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u * normB v μ n Φ
        + μ * (a v) * normB v μ n Φ)

/-- `perBoxCubeLHS` is `perBoxCubeLHSFun` on the underlying function. -/
theorem perBoxCubeLHS_eq_fun (v : E3 → ℝ) (h : ScatSol v) (R c₁ C μ : ℝ) (n : ℕ)
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3) :
    perBoxCubeLHS v h R c₁ C μ n Φ u = perBoxCubeLHSFun v h R c₁ C μ n (Φ : X n → ℝ) u := rfl

/-! ## 2. The weight identity: `∫ Φ² W = Σ_k ∫ Φ_k² W`

The weight `W` is a function of the *configuration* (not of the amplitude), and the sector pieces
have disjointly supported squares (`Work.FockBridge.sum_sectorPiece_sq`), so the identity is exact.
It is stated for a *continuous* `W ≥ 0` on a *nondegenerate* box `abox n ℓ` (`0 < ℓ`): continuity
gives the measurability of `W` and the integrability of the whole integrand on the compact `abox`.
-/

theorem integral_sq_mul_eq_sum_sectorPiece {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hA : MeasurableSet A) {Φ W : X n → ℝ} (hΦ : Continuous Φ) (hW : Continuous W)
    (hWnn : ∀ x, 0 ≤ W x) :
    ∫ x in abox n ℓ, (Φ x) ^ 2 * W x
      = ∑ k ∈ Finset.range (n + 1),
          ∫ x in abox n ℓ, (Work.FockBridge.sectorPiece A k Φ x) ^ 2 * W x := by
  have hInt : IntegrableOn (fun x : X n => (Φ x) ^ 2 * W x) (abox n ℓ) :=
    ContinuousOn.integrableOn_compact (abox_compact n hℓ) ((hΦ.pow 2).mul hW).continuousOn
  have hpt : ∀ x : X n, (Φ x) ^ 2 * W x
      = ∑ k ∈ Finset.range (n + 1), (Work.FockBridge.sectorPiece A k Φ x) ^ 2 * W x := by
    intro x
    rw [← Finset.sum_mul, Work.FockBridge.sum_sectorPiece_sq]
  rw [show (∫ x in abox n ℓ, (Φ x) ^ 2 * W x)
        = ∫ x in abox n ℓ,
            ∑ k ∈ Finset.range (n + 1), (Work.FockBridge.sectorPiece A k Φ x) ^ 2 * W x from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [MeasureTheory.integral_finsetSum]
  intro k _
  have hpiece : Measurable (fun x : X n => Work.FockBridge.sectorPiece A k Φ x) := by
    rw [Work.FockBridge.sectorPiece]
    exact hΦ.measurable.indicator (Work.FockBridge.sectorSet_measurable A hA k)
  have hmeas : AEStronglyMeasurable
      (fun x : X n => (Work.FockBridge.sectorPiece A k Φ x) ^ 2 * W x)
      ((volume : Measure (X n)).restrict (abox n ℓ)) :=
    ((hpiece.pow_const 2).mul hW.measurable).aestronglyMeasurable
  refine hInt.mono' hmeas (Filter.Eventually.of_forall fun x => ?_)
  have habs : |Work.FockBridge.sectorPiece A k Φ x| ≤ |Φ x| := by
    rw [Work.FockBridge.sectorPiece]
    by_cases hx : x ∈ Work.FockBridge.sectorSet A k
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, abs_zero]
      exact abs_nonneg _
  have hsq : (Work.FockBridge.sectorPiece A k Φ x) ^ 2 ≤ (Φ x) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) habs 2
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (hWnn x)]
  exact mul_le_mul_of_nonneg_right hsq (hWnn x)

/-! ## 3. The `L²`-mass identity -/

/-- The squared norm is sector-additive (the `W ≡ 1` case of
`integral_sq_mul_eq_sum_sectorPiece`). -/
theorem normB_eq_sum_sectorPiece {v : E3 → ℝ} {μ : ℝ} {ε₀ : ℝ} (hAdm : Adm v ε₀ μ) {n : ℕ}
    {A : Set E3} (hA : MeasurableSet A) {Φ : X n → ℝ} (hΦ : Continuous Φ) :
    normB v μ n Φ
      = ∑ k ∈ Finset.range (n + 1),
          normB v μ n (Work.FockBridge.sectorPiece A k Φ) := by
  have h := integral_sq_mul_eq_sum_sectorPiece (n := n) (ℓ := sideAt μ (a v))
    (Work.BoseFixB1.adm_ell_pos hAdm) hA hΦ continuous_const (fun _ => zero_le_one)
  simpa only [mul_one, Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB] using h

/-! ## 4. The demand additivity — the headline -/

/-- **The demand `perBoxCubeLHS` is additive over the `n_{B(u)}`-sectors.** -/
theorem perBoxCubeLHSFun_eq_sum_sectorPiece {v : E3 → ℝ} (h : ScatSol v) {R c₁ C μ : ℝ} {ε₀ : ℝ}
    (hAdm : Adm v ε₀ μ) {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3) :
    perBoxCubeLHSFun v h R c₁ C μ n (Φ : X n → ℝ) u
      = ∑ k ∈ Finset.range (n + 1),
          perBoxCubeLHSFun v h R c₁ C μ n
            (Work.FockBridge.sectorPiece (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) k
              (Φ : X n → ℝ)) u := by
  have hℓ : 0 < sideAt μ (a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hA : MeasurableSet (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) :=
    measurableSet_dlBox _ _ _
  have hΦc : Continuous (Φ : X n → ℝ) := Φ.contDiff.continuous
  -- ## the weight is continuous and nonnegative
  have hchi : Continuous (fun x : E3 => chiSmallB (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u x) := by
    rw [show (fun x : E3 => chiSmallB (paramsAt μ (a v)).M (sideAt μ (a v))
          (paramsAt μ (a v)).d u x)
        = fun x => chiScale (sideAt μ (a v)) x
            * chiSmall (paramsAt μ (a v)).M
                (((sideAt μ (a v)) * (paramsAt μ (a v)).d)⁻¹ • x - u) from by
      funext x; rw [chiSmallB]]
    exact (chiScale_continuous _).mul
      ((Work.SmallBoxSliding.chiSmall_continuous_all _).comp (by fun_prop))
  have hnc : Continuous (fun x : X n =>
      Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x) := by
    rw [show (fun x : X n =>
          Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
        = fun x => ∑ i : Fin n, (chiSmallB (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u (x i)) ^ 2 from by
      funext x; rw [Work.BoseFixB1.nCountB]]
    exact continuous_finsetSum _ fun i _ => (hchi.comp (continuous_apply i)).pow 2
  have ht : Continuous (fun x : X n =>
      Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x
        / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) := by
    by_cases hc : chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u = 0
    · rw [show (fun x : X n =>
          Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x
            / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)
          = fun _ => (0 : ℝ) from by funext x; rw [hc, div_zero]]
      exact continuous_const
    · exact hnc.div continuous_const (fun _ => hc)
  have ht0 : ∀ x : X n, 0 ≤ Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u x / chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u := fun x =>
    div_nonneg (nCountB_nonneg_loc _ _ _ x) (chiMass_nonneg _ _ _ _)
  have hWc : Continuous (fun x : X n => psiWeight 1 μ
      (Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x
        / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)) := by
    have hfun : (fun x : X n => psiWeight 1 μ
          (Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x
            / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u))
        = fun x : X n =>
            (Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x
              / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u - μ) ^ 2
            / (1 + (Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u x
              / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) * μ⁻¹) := by
      funext x; rw [Work.SmallBoxSliding.psiWeight]; ring
    rw [hfun]
    refine Continuous.div ((ht.sub continuous_const).pow 2)
      (continuous_const.add (ht.mul continuous_const)) ?_
    intro x
    have h1 : 0 ≤ (Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u x
        / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) * μ⁻¹ :=
      mul_nonneg (ht0 x) (inv_nonneg.mpr hμ.le)
    linarith
  have hWnn : ∀ x : X n, 0 ≤ psiWeight 1 μ
      (Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x
        / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) := by
    intro x
    rw [Work.SmallBoxSliding.psiWeight]
    refine div_nonneg (mul_nonneg zero_le_one (sq_nonneg _)) ?_
    have h2 := mul_nonneg (ht0 x) (inv_nonneg.mpr hμ.le)
    linarith
  -- ## the two identities
  have hI : (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 *
        psiWeight 1 μ (Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u x
          / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u))
      = ∑ k ∈ Finset.range (n + 1),
          ∫ x in abox n (sideAt μ (a v)),
            (Work.FockBridge.sectorPiece (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) k
              (Φ : X n → ℝ) x) ^ 2
            * psiWeight 1 μ (Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u x
              / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) :=
    integral_sq_mul_eq_sum_sectorPiece (n := n) (ℓ := sideAt μ (a v)) hℓ hA hΦc hWc hWnn
  have hN : normB v μ n (Φ : X n → ℝ)
      = ∑ k ∈ Finset.range (n + 1),
          normB v μ n (Work.FockBridge.sectorPiece (dlBox (sideAt μ (a v))
            (paramsAt μ (a v)).d u) k (Φ : X n → ℝ)) :=
    normB_eq_sum_sectorPiece (v := v) (μ := μ) hAdm (n := n) hA hΦc
  simp only [perBoxCubeLHSFun]
  rw [hI, hN]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]

/-! ## 5. The row-level assembly: the per-box row from the sector rows -/

/-- **The per-box row for `Φ` follows from the per-box rows for its sector pieces**, given the
sector additivity of the word.  Both sides are sums over the same sectors, so this is
`Finset.sum_le_sum` after the demand additivity of §4; the word additivity is a *hypothesis* here
so that the caller can supply it at its own `ε₀` (`Work.BoseFixB1B.sbWordCube_sectorAdditive`). -/
theorem perBoxFCube_of_sectorPieces {v : E3 → ℝ} (h : ScatSol v) {R c₁ C μ : ℝ} {ε₀ : ℝ}
    (hAdm : Adm v ε₀ μ) {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3)
    (hword : Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)
      = ∑ k ∈ Finset.range (n + 1),
          Work.BoseFixB1B.sbWordCube v h μ u
            (Work.FockBridge.sectorPiece (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) k
              (Φ : X n → ℝ)))
    (hrows : ∀ k ∈ Finset.range (n + 1), perBoxCubeLHSFun v h R c₁ C μ n
        (Work.FockBridge.sectorPiece (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) k
          (Φ : X n → ℝ)) u
      ≤ Work.BoseFixB1B.sbWordCube v h μ u
          (Work.FockBridge.sectorPiece (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) k
            (Φ : X n → ℝ))) :
    Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u := by
  rw [perBoxFCube_iff, perBoxCubeLHS_eq_fun,
    perBoxCubeLHSFun_eq_sum_sectorPiece h hAdm Φ u, hword]
  exact Finset.sum_le_sum hrows

end Work.BoseB1Cube
