import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.CountWindowCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.NominalPerBox` — FS `thm:smallbox` in FS's **own** spelling

**Why this module exists.**  FS `thm:smallbox` (`FSsrc/final_v2.tex:3907`) states the per-box
lower bound with the demand written at the **nominal / indicator local density**
`n/|B|`, where `n` is the particle-number operator of the box — i.e. on a configuration `x` the
weight is

    F( #{i : xᵢ ∈ B(u)} / |B(u)| ) ,     F(t) = c (t − μ)² /(1 + t/μ) ,

with `#` the **indicator count**.  The corpus's frozen `Work.BoseFixB1S.PerBoxFCube` reads the same
row at the **smooth windowed density** `nCountB(x)/chiMass` (with `nCountB = Σᵢ χ_B(xᵢ)²` and
`chiMass = ∫χ_B²`).  `FINDING_cubeCrudeBand_session5.md` §9/§9bis records that (i) the passage
between the two spellings is exactly the bookkeeping that drags the count window into the dense-arm
ledger, and (ii) FS's own use of `thm:smallbox` (`eq:appsliding` + the layer split, with the
chemical-potential slot `m(u)μ`) only ever needs the **rough** corollary, in which the `F`-term is
*dropped* — so the *value* of `F`'s argument, and hence the spelling, is irrelevant there.

This module supplies the two objects FS's argument needs and that the corpus really uses:

* `PerBoxFNom` — `thm:smallbox` at the nominal density **and with a separate chemical-potential
  slot** `μp` (the box/knobs stay at FS's parameter block for `μ`), which is what makes FS's
  `m(u)μ` substitution (`m(u) = 1` on `I₋`, `m(u) = 4` on the boundary layer, `eq:appsliding`
  `FSsrc/final_v2.tex:3639`) writable;
* `perBoxFNom_crude` — its **rough corollary on FS's good set**: dropping the nonnegative `F`-term
  and absorbing `½μp²∬w₁` through the proved mass law `w1MassB_le_const_mul_chiMass_regime` gives

      sbWordCube v h μ u Φ ≥ −C(μp²·a v·chiMass + μp·a v)·‖Φ‖²      (u ∈ goodSet, μp = μ),

  i.e. the *good-set* half of `CubeCrudeGood` with **no** count window, **no** `(R1)/(R2)`, and
  **no** smoothing input — this is FS's `eq:badset`/layer step in the corpus's vocabulary.

The outer band `cube ∖ goodSet` is deliberately *not* treated here: by `eq:appsliding` FS never
integrate over it (`FINDING_cubeCrudeBand_session5.md` §9bis).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical

/-- **The indicator count of the sliding box**: `#{i : xᵢ ∈ dlBox ℓ d u}` — FS's `n` of
`eq:smallboxnn0n+` (`final_v2.tex:3653`) at the box `B(u)`, in the corpus's `dlBox` currency. -/
noncomputable def boxIndCount {n : ℕ} (ℓ d : ℝ) (u : E3) (x : X n) : ℝ :=
  ∑ i : Fin n, (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)

lemma boxIndCount_nonneg {n : ℕ} (ℓ d : ℝ) (u : E3) (x : X n) : 0 ≤ boxIndCount ℓ d u x :=
  Finset.sum_nonneg fun i _ =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) (x i)

/-- **FS `thm:smallbox` at the sliding box `B(u)` of the parameter block of `μ`, in FS's *nominal*
(indicator-count) spelling, with the chemical-potential slot `μp`.**

This is `Work.BoseFixB1S.PerBoxFCube` with the two differences FS's own statement has:

* the mean-field weight is read at `boxIndCount/boxMass` (`= n/|B|`) instead of `nCountB/chiMass`;
* the chemical-potential slot `μp` is separated from the parameter block `μ` (only the `F`-weight,
  the `½μ²∬w₁` term and the `μa` error carry `μp`; the box, the window, the cutoffs and the word
  `sbWordCube v h μ u` stay at the block `μ`).

At `μp = μ` and with the smooth density in place of the indicator count this is (up to the
spelling, `FINDING_cubeCrudeBand_session5.md` §9) `PerBoxFCube`; at `μp = 4μ` it is the row FS use
on the boundary layer `I = goodSet ∖ interiorSet` (`eq:appsliding`). -/
def PerBoxFNom (v : E3 → ℝ) (h : ScatSol v) (R c₁ C : ℝ) (μp μ : ℝ) (n : ℕ)
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3) : Prop :=
  c₁ * (Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
        * (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
            Work.SmallBoxSliding.psiWeight 1 μp
              (boxIndCount (sideAt μ (a v)) (paramsAt μ (a v)).d u x
                / Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)))
    - (1 / 2) * μp ^ 2 * Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
    - C * (μp ^ 2 * (a v)
            * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
                + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
        + μp * (a v) * normB v μ n (Φ : X n → ℝ))
  ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)

/-- **The chemical-potential slot on the word.**  FS's `H_{B(u)}(μp)` at the *fixed* box of the
parameter block of `μ`: the matched word `sbWordCube` with its one-body slot moved from `μ` to
`μp`.  (`sbPot = pairSum − μ·fibSum`, and the kinetic slot `sbKinCube` carries no
chemical-potential slot.) -/
noncomputable def sbWordSlot (v : E3 → ℝ) (h : ScatSol v) (μp μ : ℝ) (u : E3)
    {n : ℕ} (Φ : X n → ℝ) : ℝ :=
  Work.BoseFixB1B.sbKinCube v μ u Φ
    + (Work.BoseFixB1.pairSum v (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u Φ
        - μp * Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
            Φ)

/-- The slot identity FS's `m(u)`-substitution uses: moving the chemical-potential slot from `μ` to
`μp` costs exactly `−(μp − μ)·fibSum`.  Pure algebra. -/
theorem sbWordSlot_eq_sub {v : E3 → ℝ} {h : ScatSol v} {μp μ : ℝ} {u : E3} {n : ℕ}
    (Φ : X n → ℝ) :
    sbWordSlot v h μp μ u Φ
      = sbWordSlot v h μ μ u Φ
        - (μp - μ) * Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u Φ := by
  unfold sbWordSlot
  ring

/-- At the slot `μ` the slot-generic word is the matched word (needs the proved splitting
`sbPot = pairSum − μ fibSum`, hence `sbPot_split`'s interface hypotheses). -/
theorem sbWordSlot_self {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {εr μ : ℝ} (hadmr : Work.BoseBoxFix.Adm v εr μ)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) {u : E3}
    (hRd : R ≤ sideAt μ (a v) * (paramsAt μ (a v)).d / 16)
    (hRχ : R ≤ sideAt μ (a v) * Submission.BoseGases.chiR0) :
    sbWordSlot v h μ μ u (Φ : X n → ℝ) = Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) := by
  have hcont : Continuous (Φ : X n → ℝ) := Φ.contDiff.continuous
  have hsplit := sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1 hadmr hcont u
    hRd hRχ
  unfold sbWordSlot
  rw [Work.BoseFixB1C.sbWordCube_eq_add u (Φ : X n → ℝ), hsplit]
  ring

/-! ## The rough corollary from the nominal row (FS's layer / `eq:badset` step) -/


/-- The pure-real arithmetic of `perBoxFNom_crude` (the same computation as
`perBoxCubeCrude_arith`, at the chemical-potential slot `μp`). -/
private lemma perBoxFNomArith {c₁ W I G μp a V N C Cm sb : ℝ}
    (h : c₁ * (W * I) - (1 / 2) * μp ^ 2 * W * N - C * (μp ^ 2 * a * G * V * N + μp * a * N) ≤ sb)
    (hc₁ : 0 ≤ c₁) (hW : 0 ≤ W) (hI : 0 ≤ I) (hC : 0 ≤ C) (hCm : 0 ≤ Cm)
    (hμp : 0 ≤ μp) (ha : 0 ≤ a) (hV : 0 ≤ V) (hN : 0 ≤ N)
    (hWb : W ≤ Cm * a * V) (hG : G ≤ 2) :
    -((Cm / 2 + 3 * C) * (μp ^ 2 * a * V + μp * a)) * N ≤ sb := by
  have hdrop : 0 ≤ c₁ * (W * I) := mul_nonneg hc₁ (mul_nonneg hW hI)
  have hX : 0 ≤ μp ^ 2 * a * V * N := mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μp) ha) hV) hN
  have hY : 0 ≤ μp * a * N := mul_nonneg (mul_nonneg hμp ha) hN
  have hcoef : 0 ≤ (1 / 2 : ℝ) * μp ^ 2 * N :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg μp)) hN
  have h1 : (1 / 2) * μp ^ 2 * W * N ≤ (Cm / 2) * (μp ^ 2 * a * V * N) := by
    calc (1 / 2) * μp ^ 2 * W * N = ((1 / 2) * μp ^ 2 * N) * W := by ring
      _ ≤ ((1 / 2) * μp ^ 2 * N) * (Cm * a * V) := mul_le_mul_of_nonneg_left hWb hcoef
      _ = (Cm / 2) * (μp ^ 2 * a * V * N) := by ring
  have h2 : C * (μp ^ 2 * a * G * V * N) ≤ (2 * C) * (μp ^ 2 * a * V * N) := by
    have hstep : μp ^ 2 * a * G * V * N ≤ μp ^ 2 * a * 2 * V * N := by
      calc μp ^ 2 * a * G * V * N = (μp ^ 2 * a * V * N) * G := by ring
        _ ≤ (μp ^ 2 * a * V * N) * 2 := mul_le_mul_of_nonneg_left hG hX
        _ = μp ^ 2 * a * 2 * V * N := by ring
    calc C * (μp ^ 2 * a * G * V * N) ≤ C * (μp ^ 2 * a * 2 * V * N) :=
          mul_le_mul_of_nonneg_left hstep hC
      _ = (2 * C) * (μp ^ 2 * a * V * N) := by ring
  have hk1 : 0 ≤ C * (μp ^ 2 * a * V * N) := mul_nonneg hC hX
  have hk2 : 0 ≤ (Cm / 2) * (μp * a * N) := mul_nonneg (by linarith) hY
  have hk3 : 0 ≤ 2 * C * (μp * a * N) := mul_nonneg (by linarith) hY
  have hK : (1 / 2) * μp ^ 2 * W * N + C * (μp ^ 2 * a * G * V * N + μp * a * N)
      ≤ (Cm / 2 + 3 * C) * (μp ^ 2 * a * V + μp * a) * N := by
    nlinarith [h1, h2, hk1, hk2, hk3]
  linarith [h, hdrop, hK]

/-- FS's `psiWeight` is nonnegative on the physical range `t ≥ 0`. -/
private lemma psiWeight_nonneg_aux {c μ t : ℝ} (hc : 0 ≤ c) (hμ : 0 < μ) (ht : 0 ≤ t) :
    0 ≤ Work.SmallBoxSliding.psiWeight c μ t := by
  rw [Work.SmallBoxSliding.psiWeight]
  exact div_nonneg (mul_nonneg hc (sq_nonneg _)) (by positivity)

/-- **The rough corollary of the nominal per-box row on FS's good set.**  From `PerBoxFNom` at the
slot `μ` one gets, for every `u` on the good set,

    sbWordCube v h μ u Φ ≥ −C'·(μ²·(a v)·chiMass + μ·(a v))·‖Φ‖² .

Proof: drop the nonnegative `F`-term (`psiWeight ≥ 0`, `w1MassB ≥ 0`, `c₁ > 0`), bound the surviving
`½μ²∬w₁` through the proved mass law `w1MassB_le_const_mul_chiMass_regime`, and bound the bracket
`(R/(ℓd))² + K_B³(μa³)^{1/2}` by `2` (the regime facts `R ≤ ℓd/16` and `K_B³(μa³)^{1/2} ≤ 1`).

The constant is `C' = Cm/2 + 3C` with `Cm` the mass-law constant; `ε₀` is the `min` of the three
thresholds (the row's, the mass law's and `regime_sideAt_ge`'s). -/
theorem perBoxFNom_crude {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < a v)
    (hF : ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
          u ∈ Work.SmallBoxSliding.goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
          PerBoxFNom v h R c₁ C μ μ n Φ u) :
    ∃ ε₀ C' : ℝ, 0 < ε₀ ∧ 0 ≤ C' ∧
      ∀ μ : ℝ, Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
          u ∈ Work.SmallBoxSliding.goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
          - (C' * (μ ^ 2 * (a v) * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M
                    (sideAt μ (a v)) (paramsAt μ (a v)).d u
                  + μ * (a v)))
              * normB v μ n (Φ : X n → ℝ)
            ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) := by
  classical
  obtain ⟨ε₀, c₁, C, hε₀, hc₁, hC, hper⟩ := hF
  obtain ⟨εm, Cm, hεm, hCm, hmass⟩ :=
    Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime (v := v) h hv hvrad hR hv_supp
  obtain ⟨εr, hεr, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min ε₀ (min εm (min εr 1)), Cm / 2 + 3 * C,
    lt_min hε₀ (lt_min hεm (lt_min hεr one_pos)), by positivity, ?_⟩
  intro μ hAdm n Φ u hmem
  have hAdm₀ : Adm v ε₀ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdm_m : Adm v εm μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hdil_r : μ * (a v) ^ 3 ≤ εr :=
    le_trans (Work.BoseFixB1.adm_dilute hAdm)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hdil_1 : μ * (a v) ^ 3 ≤ 1 :=
    le_trans (Work.BoseFixB1.adm_dilute hAdm)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hℓ : 0 < sideAt μ (a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (paramsAt μ (a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have ht_pos : 0 < μ * (a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
  -- the row, at the slot `μ`
  have hs := hper μ hAdm₀ n Φ u hmem
  rw [PerBoxFNom] at hs
  -- the rough arithmetic
  have hℓd : 0 < sideAt μ (a v) * (paramsAt μ (a v)).d := mul_pos hℓ hd
  have hmassμ := hmass μ hAdm_m u
  obtain ⟨hR16, _⟩ := hreg μ hμ hdil_r
  have hratio : R / (sideAt μ (a v) * (paramsAt μ (a v)).d) ≤ 1 / 16 := by
    rw [div_le_iff₀ hℓd]
    linarith
  have hsq : (R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2 ≤ (1 / 16) ^ 2 := by
    have h0 : 0 ≤ R / (sideAt μ (a v) * (paramsAt μ (a v)).d) := by positivity
    nlinarith [hratio, h0]
  have hKB3 : (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) ≤ 1 := by
    rw [Work.BoseFixB1.KB3_half_eq hav hμ]
    exact Work.BoseBox.fsXp_le_one ht_pos hdil_1 (by norm_num)
  have hG : (R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
      + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) ≤ 2 := by
    nlinarith [hsq, hKB3]
  have hW : 0 ≤ Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u :=
    Work.BoseFixB1.w1MassB_nonneg (v := v) h hv hvrad hR hv_supp hℓ hd u
  have hV : 0 ≤ Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u := Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hbm : 0 ≤ Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u := by
    rw [Work.SmallBoxSliding.boxMass]
    exact integral_nonneg (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x)
  have hI : 0 ≤ ∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
      Work.SmallBoxSliding.psiWeight 1 μ
        (boxIndCount (sideAt μ (a v)) (paramsAt μ (a v)).d u x
          / Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) := by
    apply integral_nonneg
    intro x
    exact mul_nonneg (sq_nonneg _)
      (psiWeight_nonneg_aux (by norm_num) hμ
        (div_nonneg (boxIndCount_nonneg _ _ _ x) hbm))
  have hN : 0 ≤ normB v μ n (Φ : X n → ℝ) := Work.BoseFixB1.normB_nonneg _
  -- the pure-real arithmetic (the same shape as `perBoxCubeCrude_arith`)
  have hdrop : 0 ≤ c₁ * (Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u * (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
      Work.SmallBoxSliding.psiWeight 1 μ
        (boxIndCount (sideAt μ (a v)) (paramsAt μ (a v)).d u x
          / Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u))) :=
    mul_nonneg hc₁.le (mul_nonneg hW hI)
  have h1 : (1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
      ≤ (Cm / 2) * (μ ^ 2 * (a v) * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M
          (sideAt μ (a v)) (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)) := by
    have hcoef : 0 ≤ (1 / 2 : ℝ) * μ ^ 2 * normB v μ n (Φ : X n → ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg μ)) hN
    calc (1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
          (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
        = ((1 / 2) * μ ^ 2 * normB v μ n (Φ : X n → ℝ))
            * Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u := by ring
      _ ≤ ((1 / 2) * μ ^ 2 * normB v μ n (Φ : X n → ℝ))
            * (Cm * (a v) * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M
                (sideAt μ (a v)) (paramsAt μ (a v)).d u) :=
          mul_le_mul_of_nonneg_left hmassμ hcoef
      _ = (Cm / 2) * (μ ^ 2 * (a v) * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M
          (sideAt μ (a v)) (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)) := by ring
  have hX : 0 ≤ μ ^ 2 * (a v) * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M
      (sideAt μ (a v)) (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav.le) hV) hN
  have hY : 0 ≤ (a v) * normB v μ n (Φ : X n → ℝ) := mul_nonneg hav.le hN
  have h2 : C * (μ ^ 2 * (a v)
        * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
            + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
        * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ))
      ≤ (2 * C) * (μ ^ 2 * (a v) * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M
          (sideAt μ (a v)) (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)) := by
    have hstep : μ ^ 2 * (a v)
        * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
            + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
        * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
      ≤ μ ^ 2 * (a v) * 2 * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M
          (sideAt μ (a v)) (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ) := by
      have hb : μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
            + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          ≤ μ ^ 2 * (a v) * 2 :=
        mul_le_mul_of_nonneg_left hG (mul_nonneg (sq_nonneg μ) hav.le)
      calc μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
              + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
            * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
          = (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
              + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
              * (Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                  (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)) := by ring
        _ ≤ (μ ^ 2 * (a v) * 2) * (Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M
              (sideAt μ (a v)) (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)) :=
            mul_le_mul_of_nonneg_right hb (mul_nonneg hV hN)
        _ = μ ^ 2 * (a v) * 2 * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M
              (sideAt μ (a v)) (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ) := by ring
    calc C * (μ ^ 2 * (a v)
          * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
              + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ))
        ≤ C * (μ ^ 2 * (a v) * 2 * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M
            (sideAt μ (a v)) (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)) :=
          mul_le_mul_of_nonneg_left hstep hC
      _ = (2 * C) * (μ ^ 2 * (a v) * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M
            (sideAt μ (a v)) (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)) := by ring
  have hfin := perBoxFNomArith hs hc₁.le hW hI hC hCm hμ.le hav.le hV hN hmassμ hG
  exact hfin

/-- **FS's `eq:appsliding` at the matched cube cutoff** (`FSsrc/final_v2.tex:3639`): the *global*
matched word dominates the localised words integrated over FS's **good set only**, with the
chemical-potential slot `m(u)μ` on the boundary layer `goodSet ∖ interiorSet` (`m(u) = 4`) and `μ`
on `interiorSet`.

The domain is the point: FS never integrate over the outer band `cube ∖ goodSet`
(`FINDING_cubeCrudeBand_session5.md` §9bis), so this statement — unlike
`Work.BoseFixB1B.SlidingBCube` (which integrates over all of `E3`) — needs **no bound on the outer
band**.

This is the one new analytic statement of the FS route to `CountWindow`; the rest of FS's argument
(the `I₋` F-row, the layer's rough bound from `PerBoxFNom`, the convexity `U`-argument and the
arithmetic) is on disk.  It is *stated* here so that its prover has a stable name; its proof (the
per-`u` kinetic/potential estimates of FS l.3600–3640, at the corpus's `sbWordSlot`) is delegated. -/
def SlidingGoodCube (v : E3 → ℝ) (h : ScatSol v) : Prop :=
  ∃ ε₀ C : ℝ, 1 ≤ C ∧ 0 < ε₀ ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
        (paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2)
            * Submission.BoseGases.cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
          + (1 / C) * ∫ u in Work.SmallBoxSliding.goodSet (sideAt μ (a v))
                (paramsAt μ (a v)).d μ,
              sbWordSlot v h (if u ∈ Work.SmallBoxSliding.interiorSet (sideAt μ (a v))
                  (paramsAt μ (a v)).d μ then μ else 4 * μ) μ u (Φ : X n → ℝ)
        ≤ Work.BoseBoxFix.wordB v h μ n (Φ : X n → ℝ)

end Work.BoseB1Cube
