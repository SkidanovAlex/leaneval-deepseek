import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1B.trimOffInterior
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.trimInteriorOfPerBoxFLow` — FS `eq:badset` from the LOW-state `PerBoxF`

**Copy of `Submission/Work/BoseFixB1S/trimInteriorOfPerBoxF.lean`** (holder of
`Submission/Work/BoseFixB1B/lowCountBound.lean`): the per-box provider `PerBoxF` on the good set is
required only for **low** states of **positive box norm** (`IsLowB v h J μ n Φ`,
`0 < normB`), because `PerBoxF` without those restrictions is FALSE (see
`Submission/Work/BoseFixB1B/FINDING_perBoxF_refuted_lowB_survives.md`).  The `J`-quantifier stays
inside the existential so that a single pair of constants serves all `J ≤ K_B³`, and the band
input `hshell` carries the same two restrictions.  Apart from those slots the statement, the proof
and the (private) good-set crude bound are unchanged.

Original header follows.

## `Work.BoseFixB1S.trimInteriorOfPerBoxF` — FS `eq:badset` from `PerBoxF` + the band bound

The node of the a-priori chapter which extracts the `I₋` → `ℝ³` trim **from the two per-box
inputs** rather than from a pre-packaged crude per-box bound:

* `hF` — FS `thm:smallbox` at the sliding box `B(u)` in its `F`-weighted form
  (`Work.BoseFixB1.PerBoxF`), assumed on the *good set* `G` (where FS's theorem is stated);
* `hshell` — the *band-restricted, low-state* crude per-box bound on `bandSet \ goodSet`
  (FS `eq:badset`), whose packaged form is `Work.BoseFixB1B.thinShellCrude`.

From these two the target follows.  The route:

1. **Good-set crude bound** (`perBoxCrudeGood_noJ`): the `F`-weight gives, on the whole good set
   and for *every* state, the crude bound `sbWord ≥ −C' (μ²(a v)χ_{B(u)} + μ(a v))‖Φ‖²`
   (drop the nonnegative `F`-remainder, absorb `∬w_{1,B} ≤ C(a v)χ_{B(u)}`, bound the FS error
   bracket `Γ_B ≤ 2`).  This is `Work.BoseFixB1B.perBoxCrudeGoodOfPerBoxF` with its two *unused*
   hypotheses (`J ≤ K_B³`, `IsLowB`) removed — the target quantifies `J` *inside* the `∃`, so no
   such hypothesis may be needed.
2. **The pointwise bound on the slice** `S = (I₋)ᶜ ∩ cube`: on `S ∩ G` the bound of step 1 applies
   (with no low-state hypothesis), and `S \ G ⊆ bandSet \ goodSet` gives the second input
   `hshell`.  This uses `I₋ ⊆ G` and `(I₋)ᶜ ∩ cube ⊆ bandSet`
   (`Work.BoseFixB1B.compl_inter_cube_subset_bandSet`).
3. **Bookkeeping** (`trim_of_inputs_cube`, the `Work.BoseFixB1B.trimOffInterior` reduction with the
   pointwise input restricted to `S` and with `J` quantified inside the `∃`): split
   `∫_{I₋} = ∫_{ℝ³} − ∫_{(I₋)ᶜ}`, decompose `(I₋)ᶜ = ((I₋)ᶜ ∩ cube) ⊔ ((I₋)ᶜ \ cube)`, note
   `sbWord = sbKin ≥ 0` off the cube (there the localised kernels vanish identically), bound the
   slice integral by `−C·(band cost)·‖Φ‖²` (the `χ`-mass and the volume are monotone on
   `S ⊆ bandSet`), and absorb the band cost into the LHY monomial via
   `Work.BoseFixB1B.bandCostAbsorb`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1 Work.BoseKinLoc

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. A monotonicity glue for the crude bound

The crude lower bound carries its constant on the left of a `≤`; enlarging the constant keeps
it true. -/

private lemma negMul_le_negMul {C C' X N : ℝ} (hC : C ≤ C') (hX : 0 ≤ X) (hN : 0 ≤ N) :
    -(C' * X) * N ≤ -(C * X) * N := by
  have h1 : C * X * N ≤ C' * X * N :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hX) hN
  nlinarith [h1]

/-! ## 1. The crude per-box bound on the good set, without the `J`-hypotheses

This is `Work.BoseFixB1B.perBoxCrudeGoodOfPerBoxF` with its two unused hypotheses dropped:
neither `J ≤ K_B³` nor `IsLowB` is used in that proof (`u ∈ goodSet` is used only to invoke
`PerBoxF`).  Dropping them is what the present node needs, because the target quantifies `J`
*inside* the existential. -/

/-- FS's weight `F(t) = c(t−μ)²/(1+tμ⁻¹)` is nonnegative on the physical range `t ≥ 0`. -/
private lemma psiWeight_nonneg_good {c μ t : ℝ} (hc : 0 ≤ c) (hμ : 0 < μ) (ht : 0 ≤ t) :
    0 ≤ Work.SmallBoxSliding.psiWeight c μ t := by
  rw [Work.SmallBoxSliding.psiWeight]
  have hd : 0 < 1 + t * μ⁻¹ := by positivity
  exact div_nonneg (mul_nonneg hc (sq_nonneg _)) hd.le

/-- The per-configuration small-box particle count is a sum of squares, hence nonnegative. -/
private lemma nCountB_nonneg_good (M : ℕ) (ℓ d : ℝ) (u : E3) {n : ℕ}
    (x : Submission.BoseGases.X n) : 0 ≤ Work.BoseFixB1.nCountB M ℓ d u x := by
  rw [Work.BoseFixB1.nCountB]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- **The arithmetic core.**  If the `F`-weighted per-box bound holds in the shape produced by
`PerBoxF`, then the crude lower bound `−C'(μ²(a v)χ + μ(a v))‖Φ‖² ≤ sbWord` follows with
`C' = Cm/2 + 3C`, where `Cm` is the constant of the mass bound `W ≤ Cm·a·V` (here `a = a v`,
`V = χ_M(u)`) and `2` dominates the FS error bracket. -/
private lemma perBoxCrude_arith_good {c₁ W I G μ a V N C Cm sb : ℝ}
    (h : c₁ * (W * I) - (1 / 2) * μ ^ 2 * W * N - C * (μ ^ 2 * a * G * V * N + μ * a * N) ≤ sb)
    (hc₁ : 0 ≤ c₁) (hW : 0 ≤ W) (hI : 0 ≤ I) (hC : 0 ≤ C) (hCm : 0 ≤ Cm)
    (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hV : 0 ≤ V) (hN : 0 ≤ N)
    (hWb : W ≤ Cm * a * V) (hG : G ≤ 2) :
    -((Cm / 2 + 3 * C) * (μ ^ 2 * a * V + μ * a)) * N ≤ sb := by
  -- the dropped `F`-remainder is nonnegative
  have hdrop : 0 ≤ c₁ * (W * I) := mul_nonneg hc₁ (mul_nonneg hW hI)
  have hX : 0 ≤ μ ^ 2 * a * V * N := mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) ha) hV) hN
  have hY : 0 ≤ μ * a * N := mul_nonneg (mul_nonneg hμ ha) hN
  have hcoef : 0 ≤ (1 / 2 : ℝ) * μ ^ 2 * N :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg μ)) hN
  -- (i) the half-mass term against the mass bound
  have h1 : (1 / 2) * μ ^ 2 * W * N ≤ (Cm / 2) * (μ ^ 2 * a * V * N) := by
    calc (1 / 2) * μ ^ 2 * W * N = ((1 / 2) * μ ^ 2 * N) * W := by ring
      _ ≤ ((1 / 2) * μ ^ 2 * N) * (Cm * a * V) := mul_le_mul_of_nonneg_left hWb hcoef
      _ = (Cm / 2) * (μ ^ 2 * a * V * N) := by ring
  -- (ii) the error bracket against `G ≤ 2`
  have h2 : C * (μ ^ 2 * a * G * V * N) ≤ (2 * C) * (μ ^ 2 * a * V * N) := by
    have hstep : μ ^ 2 * a * G * V * N ≤ μ ^ 2 * a * 2 * V * N := by
      calc μ ^ 2 * a * G * V * N = (μ ^ 2 * a * V * N) * G := by ring
        _ ≤ (μ ^ 2 * a * V * N) * 2 := mul_le_mul_of_nonneg_left hG hX
        _ = μ ^ 2 * a * 2 * V * N := by ring
    calc C * (μ ^ 2 * a * G * V * N) ≤ C * (μ ^ 2 * a * 2 * V * N) :=
          mul_le_mul_of_nonneg_left hstep hC
      _ = (2 * C) * (μ ^ 2 * a * V * N) := by ring
  -- the two pieces against the allowance `(Cm/2 + 3C)(μ²aV + μa)N`
  have hk1 : 0 ≤ C * (μ ^ 2 * a * V * N) := mul_nonneg hC hX
  have hk2 : 0 ≤ (Cm / 2) * (μ * a * N) := mul_nonneg (by linarith) hY
  have hk3 : 0 ≤ 2 * C * (μ * a * N) := mul_nonneg (by linarith) hY
  have hK : (1 / 2) * μ ^ 2 * W * N + C * (μ ^ 2 * a * G * V * N + μ * a * N)
      ≤ (Cm / 2 + 3 * C) * (μ ^ 2 * a * V + μ * a) * N := by
    have h1' : (1 / 2) * μ ^ 2 * W * N ≤ (Cm / 2) * (μ ^ 2 * a * V * N) := h1
    have h2' : C * (μ ^ 2 * a * G * V * N) ≤ (2 * C) * (μ ^ 2 * a * V * N) := h2
    nlinarith [h1', h2', hk1, hk2, hk3]
  linarith [h, hdrop, hK]

/-- **The crude per-box lower bound on the good set**, from `PerBoxF` on the good set.
No low-state (`IsLowB`) and no `J`-hypothesis is used. -/
theorem perBoxCrudeGoodLow {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ}
    {ε₀ c₁ C : ℝ} (hε₀ : 0 < ε₀) (hc₁ : 0 < c₁) (hC : 0 ≤ C)
    (hper : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        ∀ (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        Work.BoseFixB1.PerBoxF v h R c₁ C μ n Φ u) :
    ∃ ε₀' C' : ℝ, 0 < ε₀' ∧ 0 ≤ C' ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀' μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          ∀ u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
            -(C' * (μ ^ 2 * (_root_.BoseGases.a v)
                  * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                  + μ * (_root_.BoseGases.a v)))
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  classical
  -- the mass-bound threshold and constant
  obtain ⟨εm, Cm, hεm, hCm, hmass⟩ :=
    Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime (v := v) h hv hvrad hR hv_supp
  -- the regime threshold `R ≤ ℓ d / 16`
  obtain ⟨εr, hεr, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min ε₀ (min εm (min εr 1)), Cm / 2 + 3 * C,
    lt_min hε₀ (lt_min hεm (lt_min hεr one_pos)), by positivity, ?_⟩
  intro μ hAdm hJK n Φ hN hlow u hmem
  -- ## the admissible data
  have hAdm₀ : Work.BoseBoxFix.Adm v ε₀ μ :=
    Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdm_m : Work.BoseBoxFix.Adm v εm μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hdil_m : μ * (_root_.BoseGases.a v) ^ 3 ≤ εm :=
    Work.BoseFixB1.adm_dilute hAdm_m
  have hdil_r : μ * (_root_.BoseGases.a v) ^ 3 ≤ εr :=
    le_trans (Work.BoseFixB1.adm_dilute hAdm)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hdil_1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 :=
    le_trans (Work.BoseFixB1.adm_dilute hAdm)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have ht_pos : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
  -- ## the `F`-weighted per-box bound (unfolded), on the good set
  have hs := hper μ hAdm₀ hJK n Φ hN hlow u hmem
  rw [Work.BoseFixB1.PerBoxF] at hs
  -- ## the mass bound at this `μ`
  have hmassμ := hmass μ hAdm_m u
  -- ## the FS regime bracket `Γ_B ≤ 2`
  obtain ⟨hR16, _hRχ⟩ := hreg μ hμ hdil_r
  have hℓd : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := mul_pos hℓ hd
  have hratio : R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ≤ 1 / 16 := by
    rw [div_le_iff₀ hℓd]
    linarith
  have hsq : (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2 ≤ (1 / 16) ^ 2 := by
    have h0 : 0 ≤ R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) := by positivity
    nlinarith [hratio, h0]
  have hKB3 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
      * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) ≤ 1 := by
    rw [Work.BoseFixB1.KB3_half_eq hav hμ]
    exact Work.BoseBox.fsXp_le_one ht_pos hdil_1 (by norm_num)
  have hG : (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
      + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
        * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) ≤ 2 := by
    nlinarith [hsq, hKB3]
  -- ## the nonnegativity facts
  have hW : 0 ≤ Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
    Work.BoseFixB1.w1MassB_nonneg (v := v) h hv hvrad hR hv_supp hℓ hd u
  have hV : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
    Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hI : 0 ≤ ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
        (Work.BoseFixB1.nCountB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x
          / Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) := by
    apply integral_nonneg
    intro x
    exact mul_nonneg (sq_nonneg _)
      (psiWeight_nonneg_good (by norm_num) hμ
        (div_nonneg (nCountB_nonneg_good _ _ _ _ x) hV))
  have hN : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseFixB1.normB_nonneg _
  -- ## the arithmetic
  exact perBoxCrude_arith_good hs hc₁.le hW hI hC hCm hμ.le hav.le hV hN hmassμ hG

/-! ## 2. The `I₋` → `ℝ³` bookkeeping with the pointwise input only on `(I₋)ᶜ ∩ cube`

Transcription of `Work.BoseFixB1B.trimOffInterior_of_inputs` with two changes: the pointwise input
`hpb` carries the low-state hypothesis and is required only on the slice `(I₋)ᶜ ∩ cube` (where the
two available inputs live), and the `J`-quantifier is *inside* the existential (so that a single
`ε₀` serves all `J`, which is the shape of the target). -/

/-- **The reduction.**  A pointwise per-box bound on `(I₋)ᶜ ∩ cube` for low states, plus the
numerical absorption of the band cost, give the `I₋`-to-`ℝ³` trim. -/
theorem trim_of_inputs_cube
    {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ}
    {ε₁ C₁ : ℝ} (hε₁ : 0 < ε₁) (hC₁ : 0 ≤ C₁)
    (hpb : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₁ μ →
      J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        ∀ u ∈ (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ
              ∩ Work.BoseFixB1B.cube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d,
          -(C₁ * (μ ^ 2 * (_root_.BoseGases.a v)
                * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                + μ * (_root_.BoseGases.a v)))
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
    {ε₂ C₂ : ℝ} (hε₂ : 0 < ε₂) (hC₂ : 0 ≤ C₂)
    (habs : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₂ μ →
      C₁ * (μ ^ 2 * (_root_.BoseGases.a v)
              * (∫ u in Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                    Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            + μ * (_root_.BoseGases.a v)
              * (MeasureTheory.volume (Work.SmallBoxSliding.bandSet
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal)
        ≤ C₂ * (μ ^ 2 * (_root_.BoseGases.a v) * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          (∫ u in Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
              Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
            ≤ (∫ u : E3, Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
              + C * (μ ^ 2 * (_root_.BoseGases.a v)
                      * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
                      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                      * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
  obtain ⟨ε_R, hε_R, hregR⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  obtain ⟨ε_F, hε_F, hFS⟩ := Work.BoseFixB1.fsRegimeAt (A := _root_.BoseGases.a v) (R := R) hav hR
  refine ⟨min (min (min ε₁ ε₂) ε_R) (min ε_F 1), C₂,
    lt_min (lt_min (lt_min hε₁ hε₂) hε_R) (lt_min hε_F one_pos), hC₂, ?_⟩
  intro μ hAdm hJK n Φ hN hlow
  have hA1 : (min (min (min ε₁ ε₂) ε_R) (min ε_F 1) : ℝ) ≤ ε₁ :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hA2 : (min (min (min ε₁ ε₂) ε_R) (min ε_F 1) : ℝ) ≤ ε₂ :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hAR : (min (min (min ε₁ ε₂) ε_R) (min ε_F 1) : ℝ) ≤ ε_R :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hAF : (min (min (min ε₁ ε₂) ε_R) (min ε_F 1) : ℝ) ≤ ε_F :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hAdm1 : Work.BoseBoxFix.Adm v ε₁ μ := Work.BoseFixB1.Adm.mono hAdm hA1
  have hAdm2 : Work.BoseBoxFix.Adm v ε₂ μ := Work.BoseFixB1.Adm.mono hAdm hA2
  have hAdmR : Work.BoseBoxFix.Adm v ε_R μ := Work.BoseFixB1.Adm.mono hAdm hAR
  have htR : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε_R := Work.BoseFixB1.adm_dilute hAdmR
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  obtain ⟨hRd, hRchi⟩ := hregR μ hμ htR
  have hFSμ := hFS μ hμ (le_trans (Work.BoseFixB1.adm_dilute hAdm) hAF)
  obtain ⟨_, _, _, _, _, _, _, _, hμinv, hA0, hM⟩ := hFSμ
  have hμa : 0 ≤ μ * (_root_.BoseGases.a v) := mul_nonneg hμ.le (le_of_lt hav)
  -- the `u`-marginal integrability of the word (corpus lemmas)
  have hIntK : Integrable (fun u : E3 =>
      Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
        (Φ : Submission.BoseGases.X n → ℝ)) :=
    Work.BoseFixB1.integrable_sbKin_marginal (v := v) (μ := μ) hℓ hd Φ
  have hIntP : Integrable (fun u : E3 => Work.BoseFixB1.sbPot h μ u
      (Φ : Submission.BoseGases.X n → ℝ)) :=
    (Work.BoseFixB1.sbPot_integral_le_potWordU (v := v) (h := h) hv1 hvrad hR hv_supp hav
      hℓ hd hM hRd hRchi Φ).1
  have hIntW : Integrable (fun u : E3 => Work.BoseFixB1.sbWord h μ u
      (Φ : Submission.BoseGases.X n → ℝ)) := by
    have heq : (fun u : E3 => Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
        = (fun u : E3 => Work.BoseFixB1.sbKin (v := v) μ
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
              (Φ : Submission.BoseGases.X n → ℝ))
          + (fun u : E3 => Work.BoseFixB1.sbPot h μ u (Φ : Submission.BoseGases.X n → ℝ)) := by
      funext u; rw [Pi.add_apply, Work.BoseFixB1B.sbWord_eq_add]
    rw [heq]; exact hIntK.add hIntP
  have hImeas : MeasurableSet
      (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ) :=
    Work.SmallBoxSliding.measurableSet_interiorSet _ _ _
  have hsplit := integral_add_compl hImeas hIntW
  -- the pointwise bound, on the slice, from the two per-box inputs
  have hpt : ∀ u ∈ (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ
        ∩ Work.BoseFixB1B.cube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d,
      -(C₁ * (μ ^ 2 * (_root_.BoseGases.a v)
              * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              + μ * (_root_.BoseGases.a v)))
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) :=
    fun u hu => hpb μ hAdm1 hJK n Φ hN hlow u hu
  -- the finiteness of the cube slice
  have hcube_meas : MeasurableSet
      (Work.BoseFixB1B.cube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) :=
    Work.BoseFixB1B.measurableSet_cube _ _
  have hslice_meas : MeasurableSet
      ((Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ
        ∩ Work.BoseFixB1B.cube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) := hImeas.compl.inter hcube_meas
  have hslice_fin : volume
      ((Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ
        ∩ Work.BoseFixB1B.cube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) < ⊤ := by
    refine lt_of_le_of_lt (measure_mono Work.BoseFixB1B.compl_inter_cube_subset_bandSet) ?_
    refine lt_of_le_of_lt (Work.SmallBoxSliding.bandSet_volume_le_d3 hℓ hd hμ
      (by simpa only [neg_div] using hμinv) (by simpa only [neg_div] using hA0))
      ENNReal.ofReal_lt_top
  -- the `bandSet`-restricted integrability of `chiMass`
  have hchi_int : Integrable (fun u : E3 =>
      Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) := by
    simpa only [Work.SmallBoxSliding.chiMass_def] using
      Work.SmallBoxSliding.integrable_chiSmallB_mass hM hℓ hd
  -- the truncated bound is integrable on the slice
  have h2b : Integrable (fun u : E3 =>
      μ ^ 2 * (_root_.BoseGases.a v)
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        + μ * (_root_.BoseGases.a v))
      (volume.restrict ((Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ
        ∩ Work.BoseFixB1B.cube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) :=
    ((hchi_int.integrableOn).const_mul (μ ^ 2 * (_root_.BoseGases.a v))).add
      (integrableOn_const (s :=
        (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ
          ∩ Work.BoseFixB1B.cube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
        (μ := volume) (C := μ * (_root_.BoseGases.a v)) (ne_of_lt hslice_fin))
  have hslice_int : Integrable (fun u : E3 =>
      -(C₁ * (μ ^ 2 * (_root_.BoseGases.a v)
              * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              + μ * (_root_.BoseGases.a v)))
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
      (volume.restrict ((Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ
        ∩ Work.BoseFixB1B.cube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) :=
    ((Integrable.const_mul h2b C₁).neg).mul_const
      (Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
  -- the monotonicity on the slice
  have hmono : (∫ u in
        (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ
          ∩ Work.BoseFixB1B.cube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d,
        -(C₁ * (μ ^ 2 * (_root_.BoseGases.a v)
                * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                + μ * (_root_.BoseGases.a v)))
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
      ≤ ∫ u in
        (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ
          ∩ Work.BoseFixB1B.cube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d,
        Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
    refine integral_mono_ae hslice_int hIntW.integrableOn ?_
    filter_upwards [ae_restrict_mem hslice_meas] with u hu
    exact hpt u hu
  -- the value of the truncated integral, bounded by minus the band cost
  have hband : (∫ u in
        (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ
          ∩ Work.BoseFixB1B.cube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d,
        -(C₁ * (μ ^ 2 * (_root_.BoseGases.a v)
                * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                + μ * (_root_.BoseGases.a v)))
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
      ≥ -(C₁ * (μ ^ 2 * (_root_.BoseGases.a v)
            * (∫ u in Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                  Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          + μ * (_root_.BoseGases.a v)
            * (volume (Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal))
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    set nB := Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) with hnBdef
    set S := (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ
        ∩ Work.BoseFixB1B.cube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d with hSdef
    have hSfin : volume S < ⊤ := hslice_fin
    have hSmeas : MeasurableSet S := hslice_meas
    -- expand the slice integral
    have hval : (∫ u in S, -(C₁ * (μ ^ 2 * (_root_.BoseGases.a v)
            * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u + μ * (_root_.BoseGases.a v)))
            * nB)
        = -(C₁ * nB) * ((μ ^ 2 * (_root_.BoseGases.a v))
              * (∫ u in S, Work.SmallBoxSliding.chiMass
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            + (μ * (_root_.BoseGases.a v)) * (volume S).toReal) := by
      rw [show (fun u : E3 =>
            -(C₁ * (μ ^ 2 * (_root_.BoseGases.a v)
              * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              + μ * (_root_.BoseGases.a v))) * nB)
          = (fun u => (-(C₁ * nB)) * (μ ^ 2 * (_root_.BoseGases.a v)
              * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              + μ * (_root_.BoseGases.a v))) from by
        funext u; ring_nf]
      rw [integral_const_mul, integral_add, integral_const_mul, setIntegral_const]
      all_goals first
        | (simp only [MeasureTheory.measureReal_def]; ring_nf)
        | exact (hchi_int.integrableOn).const_mul _
        | exact integrableOn_const (s := S) (μ := volume) (C := μ * (_root_.BoseGases.a v))
            (ne_of_lt hSfin)
    have hχmono : (∫ u in S, Work.SmallBoxSliding.chiMass
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        ≤ ∫ u in Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
            Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u := by
      refine setIntegral_mono_set (hchi_int.integrableOn) ?_ ?_
      · exact Eventually.of_forall fun u => Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
      · exact Eventually.of_forall fun u hu => Work.BoseFixB1B.compl_inter_cube_subset_bandSet hu
    have hvolmono : (volume S).toReal
        ≤ (volume (Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal := by
      refine ENNReal.toReal_mono ?_ (measure_mono Work.BoseFixB1B.compl_inter_cube_subset_bandSet)
      exact ne_of_lt (lt_of_le_of_lt (Work.SmallBoxSliding.bandSet_volume_le_d3 hℓ hd hμ
        (by simpa only [neg_div] using hμinv) (by simpa only [neg_div] using hA0))
        ENNReal.ofReal_lt_top)
    -- assemble
    have hcomb : (μ ^ 2 * (_root_.BoseGases.a v)) * (∫ u in S, Work.SmallBoxSliding.chiMass
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          + (μ * (_root_.BoseGases.a v)) * (volume S).toReal
        ≤ (μ ^ 2 * (_root_.BoseGases.a v))
            * (∫ u in Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                  Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          + (μ * (_root_.BoseGases.a v))
            * (volume (Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal := by
      have h0 : 0 ≤ (μ ^ 2 * (_root_.BoseGases.a v)) := by positivity
      have h1 : 0 ≤ (μ * (_root_.BoseGases.a v)) := hμa
      nlinarith [hχmono, hvolmono, h0, h1]
    rw [hval]
    have hC1nBnn : 0 ≤ C₁ * nB := mul_nonneg hC₁ (Work.BoseFixB1.normB_nonneg _)
    nlinarith [hcomb, hC1nBnn]
  -- `sbWord ≥ 0` off the cube, hence the complement integral dominates the slice integral
  have hnonneg_off : 0 ≤ ∫ u in
      (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ
        \ Work.BoseFixB1B.cube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d,
      Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem (hImeas.compl.diff hcube_meas)] with u hu
    have hc : u ∉ Work.BoseFixB1B.cube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := hu.2
    have hfar : u ∈ Work.SmallBoxSliding.farSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ :=
      Work.BoseFixB1B.cube_compl_subset_farSet hc
    have hz := Work.BoseFixB1B.sbPot_eq_zero_of_mem_farSet (v := v) (h := h) (μ := μ) (n := n)
      hℓ hd hfar (Φ : Submission.BoseGases.X n → ℝ)
    rw [Work.BoseFixB1B.sbWord_eq_add, hz, add_zero]
    exact Work.BoseFixB1B.sbKin_nonneg_local hAdm1 u (Φ : Submission.BoseGases.X n → ℝ)
  have hdecomp : (∫ u in
        (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ,
        Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
      = (∫ u in
          (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ
            ∩ Work.BoseFixB1B.cube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d,
          Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
        + ∫ u in
          (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ
            \ Work.BoseFixB1B.cube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d,
          Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
    have hdisj : Disjoint
        ((Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ
          ∩ Work.BoseFixB1B.cube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
        ((Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ
          \ Work.BoseFixB1B.cube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      exact hx2.2 hx1.2
    rw [← setIntegral_union hdisj (hImeas.compl.diff hcube_meas)
      (hIntW.integrableOn.mono_set Set.inter_subset_left)
      (hIntW.integrableOn.mono_set Set.sdiff_subset)]
    congr 1
    ext x
    simp [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
  have habsμ := habs μ hAdm2
  have hstep : -(C₁ * (μ ^ 2 * (_root_.BoseGases.a v)
          * (∫ u in Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        + μ * (_root_.BoseGases.a v)
          * (volume (Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal))
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      ≥ -(C₂ * (μ ^ 2 * (_root_.BoseGases.a v) * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
          * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)))
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    have h1 : C₁ * (μ ^ 2 * (_root_.BoseGases.a v)
          * (∫ u in Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        + μ * (_root_.BoseGases.a v)
          * (volume (Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal)
        ≤ C₂ * (μ ^ 2 * (_root_.BoseGases.a v) * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
          * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) := habsμ
    nlinarith [h1, Work.BoseFixB1.normB_nonneg (v := v) (μ := μ)
      (Φ : Submission.BoseGases.X n → ℝ)]
  have hkey : -(C₂ * (μ ^ 2 * (_root_.BoseGases.a v) * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
        * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)))
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      ≤ ∫ u in (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ,
          Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
    linarith [hdecomp, hmono, hband, hnonneg_off, hstep]
  linarith [hsplit, hkey]

/-! ## 3. The target -/

theorem trimInteriorOfPerBoxFLow {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ}
    {ε₁ c₁ C₁ : ℝ} (hε₁ : 0 < ε₁) (hc₁ : 0 < c₁) (hC₁ : 0 ≤ C₁)
    (hF : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₁ μ →
      J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        ∀ (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        Work.BoseFixB1.PerBoxF v h R c₁ C₁ μ n Φ u)
    {ε₂ C₂ : ℝ} (hε₂ : 0 < ε₂) (hC₂ : 0 ≤ C₂)
    (hshell : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₂ μ →
      J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        ∀ u : EuclideanSpace ℝ (Fin 3),
          u ∈ Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          u ∉ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          -(C₂ * (μ ^ 2 * (_root_.BoseGases.a v)
                * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                + μ * (_root_.BoseGases.a v)))
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)) :
    ∃ ε₃ C₃ : ℝ, 0 < ε₃ ∧ 0 ≤ C₃ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₃ μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          (∫ u in Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
              Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
            ≤ (∫ u : EuclideanSpace ℝ (Fin 3),
                Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
              + C₃ * (μ ^ 2 * (_root_.BoseGases.a v)
                      * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
                      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                      * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
  -- the crude bound on the good set, from `hF` (no low-state hypothesis involved)
  obtain ⟨εg, Cg, hεg, hCg, hgood⟩ :=
    perBoxCrudeGoodLow h hv hv1 hvrad hR hv_supp hav hε₁ hc₁ hC₁ hF
  -- the absorption of the band cost for the resulting crude constant
  obtain ⟨εa, Ca, hεa, hCa, habs⟩ :=
    Work.BoseFixB1B.bandCostAbsorb h hv hvrad hR hv_supp hav (max Cg C₂)
  refine trim_of_inputs_cube h hv hv1 hvrad hR hv_supp hav (ε₁ := min εg ε₂)
    (C₁ := max Cg C₂) (lt_min hεg hε₂) (le_trans hCg (le_max_left _ _)) ?_ hεa hCa habs
  -- the pointwise bound on `(I₋)ᶜ ∩ cube`: the good part from `hF`, the band part from `hshell`
  intro μ hAdm1 hJK n Φ hN hlow u hu
  have hAdm_g : Work.BoseBoxFix.Adm v εg μ := Work.BoseFixB1.Adm.mono hAdm1 (min_le_left _ _)
  have hAdm_2 : Work.BoseBoxFix.Adm v ε₂ μ := Work.BoseFixB1.Adm.mono hAdm1 (min_le_right _ _)
  have hXnn : 0 ≤ μ ^ 2 * (_root_.BoseGases.a v)
      * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      + μ * (_root_.BoseGases.a v) := by
    refine add_nonneg
      (mul_nonneg (mul_nonneg (sq_nonneg μ) (le_of_lt hav))
        (Work.SmallBoxSliding.chiMass_nonneg _ _ _ _))
      (mul_nonneg (Work.BoseFixB1.adm_mu_pos hAdm1).le (le_of_lt hav))
  have hNnn : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseFixB1.normB_nonneg _
  by_cases hmem : u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ
  · exact le_trans (negMul_le_negMul (C := Cg) (C' := max Cg C₂) (le_max_left _ _) hXnn hNnn)
      (hgood μ hAdm_g hJK n Φ hN hlow u hmem)
  · exact le_trans (negMul_le_negMul (C := C₂) (C' := max Cg C₂) (le_max_right _ _) hXnn hNnn)
      (hshell μ hAdm_2 hJK n Φ hN hlow u
        (Work.BoseFixB1B.compl_inter_cube_subset_bandSet hu) hmem)

end Work.BoseFixB1B
