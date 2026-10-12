import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.cubeFibRowManifest
import Submission.Work.BoseSWE.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node E of the `BoseSWE` route (`LightBoxENode`) — proved

The target `Work.BoseSWE.LightBoxENode` says: on a **light** box
(`chiMass < d^{108}(ℓd)³`, i.e. the small cube `B(u)` sits far outside the ball of radius `ℓ/2`
supporting the large-box cutoff `chiScale ℓ`), the vanishing slack
`ErrE v C μ n = C·(a v)·μ·n·d^{80}` pays the demand `Dem = (1/18)μ(n/|B|)w₁`.

## The ledger proved here

With `V = |B(u)|`, `W = w₁MassB = ∬_{B×B}w₁` (`= boxM1`, the bridge `boxM1_eq_PBW`), `S = boxFlatCount`,
`n₊ = cnPlusBoxInd`, `G = bGapCoeff v μ`, `a = a v`, `d = bD v μ`, `A := a`:

* **word** (`sbPot_split` + signs): `G·n₊ − μ·fibSum ≤ sbWordCube`
  (`cubeSpectral ≥ 0` is FS's sum of squares, `pairSum ≥ 0`);
* **manifest fibre row** (`fibSum_le_manifest`):
  `fibSum ≤ (W/V)·S + Cf·a·(√(n₊·(W/V)·S) + n₊)`;
* **box bound** (light hypothesis + `w1MassB_le_sharp` + the corner-box mass bound): with
  `1/V ≤ μ` (from `bV ≥ (μ^{-1/3})³`) and `d^{108}·μ·(ℓd)³ ≤ d^{80}` (the `fsXp` arithmetic
  `fsXp t 500 ≤ fsXp t 480`), one gets `W/V ≤ KA·a·d^{80}` with `KA = 16π` — hence
  `μ(W/V)S ≤ KA·Q` and `Dem ≤ (1/18)KA·Q` for `Q := a·μ·n·d^{80}`;
* **cross row**: with `Z := KA·a·d^{80}·n` and AM–GM at weight `G`,
  `Cf·a·μ·√(n₊(W/V)S) ≤ G·n₊/2 + Cf²a²μ²Z/(2G)`, and the gate `2Cfμa ≤ G` gives
  `Cf²a²μ²Z/(2G) ≤ (Cf·KA·a/4)·Q`;
* **gate row** (`PerBoxGapAbsorbB1` at `K = 2Cf`): `Cf·a·μ·n₊ ≤ G·n₊/2`.

Summing: `sbWordCube ≥ −KA·Q − (Cf·KA·a/4)·Q`, so
`C := (19/18)·KA + Cf·KA·a/4 + 3` works (the `19/18 = 1 + 1/18` pays the demand plus the fibre
manifest row).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseSWE

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. Two elementary tools -/

/-- **The closed form of the gap coefficient**: `bGapCoeff v μ = ½·(1+π⁻²)⁻¹·(μa³)^{1279/(4·323)}·a⁻²`.
(This is `tbGapCoeff` at `s = dℓ = a·fsXp t(-157)` and `ε = ε_T = fsXp t(23/4)`.) -/
private lemma bGapCoeff_eq {v : E3 → ℝ} {μ : ℝ} (hav : 0 < _root_.BoseGases.a v) (hμ : 0 < μ) :
    Work.BoseFixB1.bGapCoeff v μ
      = (1 / 2) * Work.SmallBoxTBWord.tbPiFactor
          * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (1279 / 4)
        * ((_root_.BoseGases.a v) ^ 2)⁻¹ := by
  have ht : (0 : ℝ) < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
  have hS' : Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ
      = (_root_.BoseGases.a v) * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-157) := by
    show Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d = _
    rw [mul_comm, Work.BoseFixB1.d_mul_sideAt_eq hav hμ]
  have hsq : (((_root_.BoseGases.a v)
        * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-157)) ^ 2)⁻¹
      = ((_root_.BoseGases.a v) ^ 2)⁻¹
        * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 314 := by
    rw [mul_pow, Work.BoseBox.fsXp_pow ht.le, mul_inv, Work.BoseBox.fsXp_inv ht]
    norm_num
  have heT : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (23 / 4) := rfl
  have hmul : Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (23 / 4)
      * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 314
      = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (1279 / 4) := by
    rw [Work.BoseBox.fsXp_mul ht]; norm_num
  rw [Work.BoseFixB1.bGapCoeff, Work.SmallBoxTBWord.tbGapCoeff, hS', hsq, heT, ← hmul]
  ring

/-- The weighted AM–GM: `√(xy) ≤ (λx + y/λ)/2` for `x, y ≥ 0`, `λ > 0`. -/
private lemma sqrt_amgm {x y lam : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hlam : 0 < lam) :
    Real.sqrt (x * y) ≤ (lam * x + y / lam) / 2 := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hkey : ((lam * x + y / lam) / 2) ^ 2
      = ((lam * x - y / lam) / 2) ^ 2 + x * y := by
    field_simp
    ring
  nlinarith [hkey, sq_nonneg ((lam * x - y / lam) / 2)]

/-- **The cross-row arithmetic**: from the gate `2·Cf·μ·a ≤ bGapCoeff`,
`Cf²a²μ²Z/(2·bGapCoeff) ≤ (Cf·KA·a/4 + 1)·Q` with `Z = KA·a·d^{80}n` and `Q = a·μ·n·d^{80}`. -/
private lemma cross_arith {v : E3 → ℝ} {μ Cf KA : ℝ} (hCf : 0 ≤ Cf)
    (hav : 0 < _root_.BoseGases.a v) (hμ : 0 < μ) (hKA : 0 ≤ KA) {n : ℕ}
    (hgate : 2 * Cf * μ * (_root_.BoseGases.a v) ≤ Work.BoseFixB1.bGapCoeff v μ) :
    Cf ^ 2 * (_root_.BoseGases.a v) ^ 2 * μ ^ 2
        * (KA * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80 * (n : ℝ))
        / (2 * Work.BoseFixB1.bGapCoeff v μ)
      ≤ (Cf * KA * (_root_.BoseGases.a v) / 4 + 1)
          * ((_root_.BoseGases.a v) * μ * (n : ℝ) * (Work.BoseFixB1.bD v μ) ^ 80) := by
  set Z : ℝ := KA * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80 * (n : ℝ) with hZdef
  set Q : ℝ := (_root_.BoseGases.a v) * μ * (n : ℝ) * (Work.BoseFixB1.bD v μ) ^ 80 with hQdef
  have hA0 : 0 < _root_.BoseGases.a v := hav
  have hGpos : 0 < Work.BoseFixB1.bGapCoeff v μ := by
    rw [bGapCoeff_eq hav hμ]
    refine mul_pos (mul_pos (mul_pos (by norm_num)
      Work.SmallBoxTBWord.tbPiFactor_pos)
      (Work.BoseBox.fsXp_pos (mul_pos hμ (pow_pos hav 3)))) (inv_pos.mpr (pow_pos hav 2))
  have hZ0 : 0 ≤ Z := by simp only [hZdef]; positivity
  have hQ0 : 0 ≤ Q := by simp only [hQdef]; positivity
  have hkey : Cf * (_root_.BoseGases.a v) * μ / Work.BoseFixB1.bGapCoeff v μ ≤ 1 / 2 := by
    rw [div_le_iff₀ hGpos]
    linarith [hgate]
  have hCfA0 : 0 ≤ Cf * (_root_.BoseGases.a v) * μ := by positivity
  have hstep : (Cf * (_root_.BoseGases.a v) * μ) * Z / (2 * Work.BoseFixB1.bGapCoeff v μ)
      ≤ Z / 4 := by
    have h3 : (Cf * (_root_.BoseGases.a v) * μ) * Z / Work.BoseFixB1.bGapCoeff v μ
        ≤ Z / 2 := by
      have h4 := mul_le_mul_of_nonneg_right hkey hZ0
      calc (Cf * (_root_.BoseGases.a v) * μ) * Z / Work.BoseFixB1.bGapCoeff v μ
          = (Cf * (_root_.BoseGases.a v) * μ / Work.BoseFixB1.bGapCoeff v μ) * Z := by ring
        _ ≤ (1 / 2) * Z := h4
        _ = Z / 2 := by ring
    calc (Cf * (_root_.BoseGases.a v) * μ) * Z / (2 * Work.BoseFixB1.bGapCoeff v μ)
        = ((Cf * (_root_.BoseGases.a v) * μ) * Z / Work.BoseFixB1.bGapCoeff v μ) / 2 := by
          ring
      _ ≤ (Z / 2) / 2 := div_le_div_of_nonneg_right h3 (by norm_num)
      _ = Z / 4 := by ring
  calc Cf ^ 2 * (_root_.BoseGases.a v) ^ 2 * μ ^ 2 * Z
        / (2 * Work.BoseFixB1.bGapCoeff v μ)
      = (Cf * (_root_.BoseGases.a v) * μ)
          * ((Cf * (_root_.BoseGases.a v) * μ) * Z / (2 * Work.BoseFixB1.bGapCoeff v μ)) := by
        ring
    _ ≤ (Cf * (_root_.BoseGases.a v) * μ) * (Z / 4) := mul_le_mul_of_nonneg_left hstep hCfA0
    _ = Cf * KA * (_root_.BoseGases.a v) / 4 * Q := by rw [hZdef, hQdef]; ring
    _ ≤ (Cf * KA * (_root_.BoseGases.a v) / 4 + 1) * Q := by
        have h1 : 0 ≤ Cf * KA * (_root_.BoseGases.a v) / 4 := by positivity
        nlinarith [hQ0]

/-! ## 2. Node E -/

/-- **Node E of the `BoseSWE` route**: on a light box (`χ_m < d^108·(ℓd)³`) the vanishing slack
`ErrE v C μ n = C·a·μ·n·d^80` pays the demand.  Recipe (see `Submission/Work/BoseSWE/BRIEF.md` §4):
`sbWordCube ≥ bGapCoeff·n₊ − μ·fibSum` (pairSum ≥ 0, cubeSpectral ≥ 0);
`μ·fibSum ≤ μ(n/V)W + C a(√(n₊(W/V)n) + n₊)` (`Work.BoseFixB1S.fibSum_le_manifest`); the `n₊`-rows
by the gate `PerBoxGapAbsorbB1`; then `W ≤ (1+δ)8πa·χ_m` (`w1MassB_le_sharp`), the light hypothesis,
and `(ℓd)³/bV ≤ μ(ℓd)³ = X^{−148}` (from `bV ≥ (min ℓ (ℓd) (μ^{-1/3}))³`, the corner-box interior
argument of `Work.BoseFixB1.boxMass_pos_of_goodSet`) give
`W/V ≤ 8πa·X^{648}·X^{−148} = 8πa·X^{500} ≤ C_E·a·X^{480}`. -/
theorem lightBoxENode_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) : Work.BoseSWE.LightBoxENode v h := by
  intro Cn hCn
  -- ## 0. the constants
  obtain ⟨Cf, hCf0, hman⟩ := Work.BoseFixB1S.fibSum_le_manifest (v := v) h hv hv1 hvrad hR hv_supp
    hav (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue])
  obtain ⟨εg, hεg, hgate⟩ := Work.BoseFixB1S.PerBoxGapAbsorbB1 (v := v) hav (2 * Cf) (by linarith)
  obtain ⟨εr, hεr, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  obtain ⟨εsh, hεsh, hsharp⟩ := Work.BoseB1Cube.w1MassB_le_sharp (v := v) h hv hv1 hvrad hR hv_supp
    hav (δ := 1) (by norm_num)
  have hKA0 : 0 ≤ 8 * Real.pi * (1 + 1) := by positivity
  refine ⟨min (min εg εr) (min εsh 1),
    (19 / 18) * (8 * Real.pi * (1 + 1)) + (Cf * (8 * Real.pi * (1 + 1)) * (_root_.BoseGases.a v) / 4 + 1) + 2,
    ?_, ?_, ?_⟩
  · exact lt_min (lt_min hεg hεr) (lt_min hεsh one_pos)
  · positivity
  · intro μ hAdm n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2 hlight
    -- ## 1. basic facts
    have hμ : 0 < μ := hAdm.1
    have ht_le : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 :=
      le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_right _ _))
    have ht_pos : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
    have hAdmg : Work.BoseBoxFix.Adm v εg μ :=
      Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_left _ _))
    have hAdmsh : Work.BoseBoxFix.Adm v εsh μ :=
      Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
    obtain ⟨hR16, hRχ⟩ := hreg μ hμ
      (le_trans hAdm.2.1 (le_trans (min_le_left _ _) (min_le_right _ _)))
    have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
    have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
    have hd1 : Work.BoseFixB1.bD v μ ≤ 1 := by
      show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1
      rw [Work.BoseFixB1.d_eq_fsXp]
      exact Work.BoseBox.fsXp_le_one ht_pos ht_le (by norm_num)
    have hV : 0 < Work.BoseFixB1.bV v μ u := by
      show 0 < Work.SmallBoxSliding.boxMass (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
      exact Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμ hu
    have hΨcont : Continuous Ψ := hΨc.continuous
    -- ## 2. the box-volume lower bound `1/μ ≤ v`
    have hreg3 : μ ^ (-(1 / 3) : ℝ) ≤ Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ := by
      have h1 : μ ^ (-(1 / 3) : ℝ) = (_root_.BoseGases.a v)
          * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-(323 / 3)) :=
        Work.BoseFixB1.mu_inv_third_eq hav hμ
      have h2 : Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ
          = (_root_.BoseGases.a v)
            * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-157) := by
        show Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d = _
        rw [mul_comm, Work.BoseFixB1.d_mul_sideAt_eq hav hμ]
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_left
        (Work.BoseBox.fsXp_le_fsXp ht_pos ht_le (by norm_num)) hav.le
    have hVinv : (Work.BoseFixB1.bV v μ u)⁻¹ ≤ μ := by
      have h3 : μ⁻¹ ≤ Work.BoseFixB1.bV v μ u := by
        have hh := Work.BoseFixB1.boxMass_ge_deltaScale_of_goodSet hℓ hd hd1 hμ hreg3 hu
        have hcube : (μ ^ (-(1 / 3) : ℝ)) ^ 3 = μ⁻¹ := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hμ.le]
          rw [show (-(1 / 3 : ℝ)) * ((3 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
        rwa [hcube] at hh
      have h4 : 1 ≤ μ * Work.BoseFixB1.bV v μ u := by
        have hh := mul_le_mul_of_nonneg_left h3 hμ.le
        rwa [mul_inv_cancel₀ (ne_of_gt hμ)] at hh
      rw [inv_le_iff_one_le_mul₀ hV]
      linarith
    -- ## 3. the `fsXp` arithmetic of the light hypothesis
    have hd108 : (Work.BoseFixB1.bD v μ) ^ 108
        = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 648 := by
      show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 108 = _
      rw [Work.BoseFixB1.d_eq_fsXp, Work.BoseBox.fsXp_pow ht_pos.le]
      norm_num
    have hd80 : (Work.BoseFixB1.bD v μ) ^ 80
        = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 480 := by
      show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 80 = _
      rw [Work.BoseFixB1.d_eq_fsXp, Work.BoseBox.fsXp_pow ht_pos.le]
      norm_num
    have hmu_ld : μ * (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) ^ 3
        = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-148) := by
      have h2 : Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ
          = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
        show Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d = _
        rw [mul_comm]
      rw [h2]
      exact Work.BoseFixB1.mu_d_mul_sideAt_cube_eq hav hμ
    have hblk : (Work.BoseFixB1.bD v μ) ^ 108
        * (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) ^ 3 / Work.BoseFixB1.bV v μ u
        ≤ (Work.BoseFixB1.bD v μ) ^ 80 := by
      have hld0 : 0 ≤ (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) ^ 3 := by positivity
      have hstep : (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) ^ 3
            / Work.BoseFixB1.bV v μ u
          ≤ (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) ^ 3 * μ := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hVinv hld0
      have hd0 : 0 ≤ (Work.BoseFixB1.bD v μ) ^ 108 := by positivity
      calc (Work.BoseFixB1.bD v μ) ^ 108
            * (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) ^ 3 / Work.BoseFixB1.bV v μ u
          = (Work.BoseFixB1.bD v μ) ^ 108
              * ((Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) ^ 3
                  / Work.BoseFixB1.bV v μ u) := by ring
        _ ≤ (Work.BoseFixB1.bD v μ) ^ 108
              * ((Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) ^ 3 * μ) :=
            mul_le_mul_of_nonneg_left hstep hd0
        _ = (Work.BoseFixB1.bD v μ) ^ 108
              * (μ * (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) ^ 3) := by ring
        _ = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 648
              * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-148) := by
            rw [hd108, hmu_ld]
        _ = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 500 := by
            rw [Work.BoseBox.fsXp_mul ht_pos]; norm_num
        _ ≤ Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 480 :=
            Work.BoseBox.fsXp_le_fsXp ht_pos ht_le (by norm_num)
        _ = (Work.BoseFixB1.bD v μ) ^ 80 := hd80.symm
    have hchi : Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u / Work.BoseFixB1.bV v μ u ≤ (Work.BoseFixB1.bD v μ) ^ 80 := by
      have h1 := div_lt_div_of_pos_right hlight hV
      linarith [hblk]
    -- ## 4. the box mass bound `W/V ≤ KA·a·d^80`
    have hWsharp : Work.BoseFixB1.bW v h μ u
        ≤ (8 * Real.pi * (1 + 1)) * (_root_.BoseGases.a v)
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u := by
      have h1 : Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u = Work.BoseFixB1.bW v h μ u := rfl
      have h2 : Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u
          = Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u := rfl
      have h3 := hsharp μ hAdmsh u
      rw [h1, h2] at h3
      have h4 : (1 + 1) * (8 * Real.pi * (_root_.BoseGases.a v))
          = (8 * Real.pi * (1 + 1)) * (_root_.BoseGases.a v) := by ring
      rwa [h4] at h3
    have hWV : Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u
        ≤ (8 * Real.pi * (1 + 1)) * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80 := by
      have h4 : Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u
          ≤ ((8 * Real.pi * (1 + 1)) * (_root_.BoseGases.a v)
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u) / Work.BoseFixB1.bV v μ u :=
        div_le_div_of_nonneg_right hWsharp hV.le
      have h5 : ((8 * Real.pi * (1 + 1)) * (_root_.BoseGases.a v)
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u) / Work.BoseFixB1.bV v μ u
          = (8 * Real.pi * (1 + 1)) * (_root_.BoseGases.a v)
            * (Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u / Work.BoseFixB1.bV v μ u) := by
        ring
      have h6 : 0 ≤ (8 * Real.pi * (1 + 1)) * (_root_.BoseGases.a v) := by positivity
      calc Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u
          ≤ (8 * Real.pi * (1 + 1)) * (_root_.BoseGases.a v)
            * (Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u / Work.BoseFixB1.bV v μ u) := by rw [← h5]; exact h4
        _ ≤ (8 * Real.pi * (1 + 1)) * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80 :=
            mul_le_mul_of_nonneg_left hchi h6
    -- ## 5. the counters, the gap coefficient and the two remaining inputs
    have hS0 : 0 ≤ Work.BoseFixB1.bFlat v μ Ψ u := by
      rw [Work.BoseFixB1.bFlat, Work.BoseFixB1S.boxFlatCount]
      exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
    have hNp0 : 0 ≤ Work.BoseFixB1.bQ v μ Ψ u := by
      rw [Work.BoseFixB1.bQ, Work.BoseFixB1S.boxQCount]
      exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
    have hG : 0 < Work.BoseFixB1.bGapCoeff v μ := by
      rw [bGapCoeff_eq hav hμ]
      refine mul_pos (mul_pos (mul_pos (by norm_num)
        Work.SmallBoxTBWord.tbPiFactor_pos)
        (Work.BoseBox.fsXp_pos (mul_pos hμ (pow_pos hav 3)))) (inv_pos.mpr (pow_pos hav 2))
    have hS_le : Work.BoseFixB1.bFlat v μ Ψ u ≤ (n : ℝ) := by
      have hh := Work.BoseFixB1S.boxFlatCount_le_NB1 (N := n) (ℓ := Work.BoseFixB1.bSide v μ)
        (volA := Work.BoseFixB1.bV v μ u) (Ac := Work.BoseFixB1.bA v μ u) hℓ hV
        (by rw [Work.BoseFixB1.bA]; exact Work.SmallBoxSliding.measurableSet_dlBox _ _ _)
        (by rw [Work.BoseFixB1.bA]; exact Work.SmallBoxSliding.dlBox_subset_acube _ _ _)
        (by rw [Work.BoseFixB1.bV, Work.BoseFixB1.bA,
          Work.SmallBoxSliding.boxMass_eq_measureReal, Measure.real_def])
        hΨcont
      rw [hnorm, mul_one] at hh
      simpa only [Work.BoseFixB1.bFlat] using hh
    -- ## 6. the word lower bound
    have hword : Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1.bQ v μ Ψ u
          - μ * Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u Ψ
        ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
      have hsplit := Work.BoseFixB1.sbPot_split (v := v) (h := h) hv_supp hR hv hvrad hv1 hAdm
        hΨcont u hR16 hRχ
      have hcs : 0 ≤ Work.BoseFixB1B.cubeSpectral v μ Ψ u := by
        rw [Work.BoseFixB1B.cubeSpectral]
        exact Work.BoseFixB1.tBwordKinInd_nonneg Ψ
      have hp : 0 ≤ Work.BoseFixB1.pairSum v (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u Ψ :=
        Work.BoseFixB1.pairSum_nonneg (v := v) hv (M := Work.BoseFixB1.bM v μ) (u := u)
          (ℓ := Work.BoseFixB1.bSide v μ) (d := Work.BoseFixB1.bD v μ) Ψ
      rw [Work.BoseFixB1B.sbWordCube, Work.BoseFixB1B.sbKinCube, hsplit]
      simp only [Work.BoseFixB1.bQ, Work.BoseFixB1.bM, Work.BoseFixB1.bSide, Work.BoseFixB1.bD,
        Work.BoseFixB1.bA, Work.BoseFixB1.bV, Work.BoseFixB1S.boxQCount,
        Work.UBBInputs8.cnPlusBoxInd] at hcs hp ⊢
      linarith [hcs, hp]
    -- ## 7. the manifest fibre row
    have hM1 : Work.BoseFixB1S.boxM1 (Work.BoseFixB1.bSide v μ)
        (Submission.BoseGases.dlBox (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
        (Submission.BoseGases.wSmall1Pair h Work.BoseBox.mValue (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u) = Work.BoseFixB1.bW v h μ u := by
      rw [Work.BoseB1Cube.boxM1WSmall1Pair_eq_w1MassB (v := v) h (M := Work.BoseBox.mValue)
        (by norm_num [Work.BoseBox.mValue]) hℓ hd u]
      rfl
    have hfib : Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u Ψ
        ≤ (Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bFlat v μ Ψ u
          + Cf * (_root_.BoseGases.a v)
              * (Real.sqrt (Work.BoseFixB1.bQ v μ Ψ u
                    * ((Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u)
                      * Work.BoseFixB1.bFlat v μ Ψ u))
                + Work.BoseFixB1.bQ v μ Ψ u) := by
      have hh := hman (ℓ := Work.BoseFixB1.bSide v μ) (d := Work.BoseFixB1.bD v μ) (μ := 0)
        hℓ hd hR16 hRχ u hV (n := n) (Φ := Ψ) hΨcont
      rw [hM1] at hh
      exact hh
    -- ## 8. the final ledger
    set Q : ℝ := (_root_.BoseGases.a v) * μ * (n : ℝ) * (Work.BoseFixB1.bD v μ) ^ 80 with hQ
    set KA : ℝ := 8 * Real.pi * (1 + 1) with hKA
    have hKA0' : 0 ≤ KA := by simp only [hKA]; positivity
    have hQ0 : 0 ≤ Q := by
      simp only [hQ]
      have h1 : 0 ≤ (Work.BoseFixB1.bD v μ) ^ 80 := by positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg hav.le hμ.le) (Nat.cast_nonneg n)) h1
    have hcomm : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        = Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ := by
      show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          * Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        = Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
      rw [mul_comm]
    have hgateB : 2 * Cf * μ * (_root_.BoseGases.a v) ≤ Work.BoseFixB1.bGapCoeff v μ := by
      have hh := hgate μ hAdmg
      simp only [hcomm] at hh
      exact hh
    have hGA : Cf * (_root_.BoseGases.a v) * μ ≤ Work.BoseFixB1.bGapCoeff v μ / 2 := by
      linarith [hgateB]
    have hd80nn : 0 ≤ (Work.BoseFixB1.bD v μ) ^ 80 := by positivity
    have hKAd0 : 0 ≤ KA * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80 :=
      mul_nonneg (mul_nonneg hKA0' hav.le) hd80nn
    have hY0 : 0 ≤ KA * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80 * (n : ℝ) :=
      mul_nonneg hKAd0 (Nat.cast_nonneg n)
    -- the manifest square is bounded by `KA·a·d^80·n`
    have hSm : (Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u)
          * Work.BoseFixB1.bFlat v μ Ψ u
        ≤ KA * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80 * (n : ℝ) := by
      have h1 : (Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u)
          ≤ KA * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80 := by
        simp only [hKA]; exact hWV
      calc (Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bFlat v μ Ψ u
          ≤ (KA * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80)
            * Work.BoseFixB1.bFlat v μ Ψ u := mul_le_mul_of_nonneg_right h1 hS0
        _ ≤ (KA * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80) * (n : ℝ) :=
            mul_le_mul_of_nonneg_left hS_le hKAd0
        _ = KA * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80 * (n : ℝ) := by ring
    -- (a) the demand
    have hDem : Dem v h μ n u ≤ (1 / 18) * KA * Q := by
      have h2 : Dem v h μ n u = (1 / 18) * (μ * ((Work.BoseFixB1.bW v h μ u
            / Work.BoseFixB1.bV v μ u) * (n : ℝ))) := by
        rw [Dem]; field_simp
      rw [h2]
      have h1 : (Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u) * (n : ℝ)
          ≤ (KA * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80) * (n : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg n)
        simp only [hKA]; exact hWV
      calc (1 / 18) * (μ * ((Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u) * (n : ℝ)))
          ≤ (1 / 18) * (μ * ((KA * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80)
              * (n : ℝ))) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hμ.le) (by norm_num)
        _ = (1 / 18) * KA * Q := by simp only [hQ]; ring
    -- (b) the manifest flat row
    have hA1 : μ * ((Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u)
          * Work.BoseFixB1.bFlat v μ Ψ u) ≤ KA * Q := by
      calc μ * ((Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u)
            * Work.BoseFixB1.bFlat v μ Ψ u)
          ≤ μ * (KA * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80 * (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hSm hμ.le
        _ = KA * Q := by simp only [hQ]; ring
    -- (c) the gate row
    have hA3 : Cf * (_root_.BoseGases.a v) * μ * Work.BoseFixB1.bQ v μ Ψ u
        ≤ Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1.bQ v μ Ψ u / 2 := by
      calc Cf * (_root_.BoseGases.a v) * μ * Work.BoseFixB1.bQ v μ Ψ u
          ≤ (Work.BoseFixB1.bGapCoeff v μ / 2) * Work.BoseFixB1.bQ v μ Ψ u :=
            mul_le_mul_of_nonneg_right hGA hNp0
        _ = Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1.bQ v μ Ψ u / 2 := by ring
    -- (d) the cross row
    have hA2 : Cf * (_root_.BoseGases.a v) * μ
          * Real.sqrt (Work.BoseFixB1.bQ v μ Ψ u
              * ((Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u)
                * Work.BoseFixB1.bFlat v μ Ψ u))
        ≤ Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1.bQ v μ Ψ u / 2
          + (Cf * KA * (_root_.BoseGases.a v) / 4 + 1) * Q := by
      have hCfA0 : 0 ≤ Cf * (_root_.BoseGases.a v) * μ := by positivity
      have hsq : Real.sqrt (Work.BoseFixB1.bQ v μ Ψ u
            * ((Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u)
              * Work.BoseFixB1.bFlat v μ Ψ u))
          ≤ Real.sqrt (Work.BoseFixB1.bQ v μ Ψ u
              * (KA * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80 * (n : ℝ))) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hSm hNp0)
      have hstep1 : Cf * (_root_.BoseGases.a v) * μ
            * Real.sqrt (Work.BoseFixB1.bQ v μ Ψ u
              * ((Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u)
                * Work.BoseFixB1.bFlat v μ Ψ u))
          ≤ Cf * (_root_.BoseGases.a v) * μ
            * Real.sqrt (Work.BoseFixB1.bQ v μ Ψ u
              * (KA * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80 * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hsq hCfA0
      -- the AM–GM at weight `bGapCoeff`, after moving the prefactor inside the square root
      have hs : Real.sqrt (Work.BoseFixB1.bQ v μ Ψ u
            * ((Cf * (_root_.BoseGases.a v) * μ) ^ 2
              * (KA * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80 * (n : ℝ))))
          = Cf * (_root_.BoseGases.a v) * μ
            * Real.sqrt (Work.BoseFixB1.bQ v μ Ψ u
              * (KA * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80 * (n : ℝ))) := by
        rw [Real.sqrt_mul hNp0, Real.sqrt_mul (sq_nonneg (Cf * (_root_.BoseGases.a v) * μ)),
          Real.sqrt_sq hCfA0]
        rw [Real.sqrt_mul hNp0]
        ring
      have hAM := sqrt_amgm (x := Work.BoseFixB1.bQ v μ Ψ u)
        (y := (Cf * (_root_.BoseGases.a v) * μ) ^ 2
          * (KA * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80 * (n : ℝ)))
        (lam := Work.BoseFixB1.bGapCoeff v μ) hNp0 (mul_nonneg (sq_nonneg _) hY0) hG
      have hstep2 : Cf * (_root_.BoseGases.a v) * μ
            * Real.sqrt (Work.BoseFixB1.bQ v μ Ψ u
              * (KA * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80 * (n : ℝ)))
          ≤ Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1.bQ v μ Ψ u / 2
            + Cf ^ 2 * (_root_.BoseGases.a v) ^ 2 * μ ^ 2
              * (KA * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80 * (n : ℝ))
              / (2 * Work.BoseFixB1.bGapCoeff v μ) := by
        rw [← hs]
        calc Real.sqrt (Work.BoseFixB1.bQ v μ Ψ u
              * ((Cf * (_root_.BoseGases.a v) * μ) ^ 2
                * (KA * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80 * (n : ℝ))))
            ≤ (Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1.bQ v μ Ψ u
                + ((Cf * (_root_.BoseGases.a v) * μ) ^ 2
                    * (KA * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80 * (n : ℝ)))
                  / Work.BoseFixB1.bGapCoeff v μ) / 2 := hAM
          _ = Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1.bQ v μ Ψ u / 2
              + Cf ^ 2 * (_root_.BoseGases.a v) ^ 2 * μ ^ 2
                * (KA * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80 * (n : ℝ))
                / (2 * Work.BoseFixB1.bGapCoeff v μ) := by
              field_simp
              try ring
      have hstep3 := cross_arith (v := v) (μ := μ) (Cf := Cf) (KA := KA) hCf0 hav hμ hKA0'
        (n := n) hgateB
      calc Cf * (_root_.BoseGases.a v) * μ
            * Real.sqrt (Work.BoseFixB1.bQ v μ Ψ u
              * ((Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u)
                * Work.BoseFixB1.bFlat v μ Ψ u))
          ≤ Cf * (_root_.BoseGases.a v) * μ
            * Real.sqrt (Work.BoseFixB1.bQ v μ Ψ u
              * (KA * (_root_.BoseGases.a v) * (Work.BoseFixB1.bD v μ) ^ 80 * (n : ℝ))) := hstep1
        _ ≤ _ := hstep2
        _ ≤ Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1.bQ v μ Ψ u / 2
              + (Cf * KA * (_root_.BoseGases.a v) / 4 + 1) * Q := by
            simp only [hQ] at hstep3 ⊢
            linarith [hstep3]
    -- (e) the assembly
    have hfibμ : μ * Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u Ψ
        ≤ KA * Q
          + (Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1.bQ v μ Ψ u / 2
              + (Cf * KA * (_root_.BoseGases.a v) / 4 + 1) * Q)
          + Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1.bQ v μ Ψ u / 2 := by
      have h1 : μ * Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u Ψ
          ≤ μ * ((Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u)
              * Work.BoseFixB1.bFlat v μ Ψ u
            + Cf * (_root_.BoseGases.a v)
              * (Real.sqrt (Work.BoseFixB1.bQ v μ Ψ u
                    * ((Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u)
                      * Work.BoseFixB1.bFlat v μ Ψ u))
                + Work.BoseFixB1.bQ v μ Ψ u)) :=
        mul_le_mul_of_nonneg_left hfib hμ.le
      have h2 : μ * ((Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u)
              * Work.BoseFixB1.bFlat v μ Ψ u
            + Cf * (_root_.BoseGases.a v)
              * (Real.sqrt (Work.BoseFixB1.bQ v μ Ψ u
                    * ((Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u)
                      * Work.BoseFixB1.bFlat v μ Ψ u))
                + Work.BoseFixB1.bQ v μ Ψ u))
          = μ * ((Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u)
              * Work.BoseFixB1.bFlat v μ Ψ u)
            + Cf * (_root_.BoseGases.a v) * μ
              * Real.sqrt (Work.BoseFixB1.bQ v μ Ψ u
                * ((Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u)
                  * Work.BoseFixB1.bFlat v μ Ψ u))
            + Cf * (_root_.BoseGases.a v) * μ * Work.BoseFixB1.bQ v μ Ψ u := by
        ring
      rw [h2] at h1
      linarith [h1, hA1, hA2, hA3]
    -- (f) the word applied to the fibre row
    have hfinal : -(KA * Q) - (Cf * KA * (_root_.BoseGases.a v) / 4 + 1) * Q
        ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
      linarith [hword, hfibμ]
    -- (g) the demand minus the slack
    have hEE : ErrE v ((19 / 18) * KA + (Cf * KA * (_root_.BoseGases.a v) / 4 + 1) + 2) μ n
        = ((19 / 18) * KA + (Cf * KA * (_root_.BoseGases.a v) / 4 + 1) + 2) * Q := by
      rw [ErrE, hQ]; ring
    rw [hEE]
    linarith [hDem, hfinal, hQ0]

end Work.BoseSWE
