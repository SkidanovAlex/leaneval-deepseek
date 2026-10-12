import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.inBoxCubeRowLarge_of_smallNArb
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.cubeSmallNArb12` — the **weakened** per-size node (items (1) and (2)
# only), which is *all* the large half of A4 consumes

`inBoxCubeRowLarge_of_smallNArb` (`inBoxCubeRowLarge_of_smallNArb.lean`, PROVED) derives
`InBoxCubeRowLarge` from `CubeSmallNArbEx`, but its proof uses only the **first two** of
`CubeSmallNArb`'s three state-independent per-size rows: the third (the `n < Cn·μV` crude row) is
destructured as `_hB3all` and never used.  Consequently the *honest* residual of the large half is
the strictly weaker node

    CubeSmallNArb12Ex v h  :=  ∃ Cn C, 2 ≤ Cn ∧ 0 ≤ C ∧ CubeSmallNArb12 v h Cn C ,

where `CubeSmallNArb12` is `CubeSmallNArb` with its third conjunct deleted (the texts of the two
surviving conjuncts are copied verbatim from `Submission/Work/BoseB1Cube/cubeSmallNArb.lean`).

This module contains the definitions, the (trivial) comparison
`CubeSmallNArbEx v h → CubeSmallNArb12Ex v h`, and the one-line-changed copy
`inBoxCubeRowLarge_of_smallNArb12` of that reduction — so the target of this chapter's large half is
`CubeSmallNArb12Ex`, not `CubeSmallNArbEx`.

## ⚠ `CubeSmallNArbEx` itself is FALSE as frozen (session 12, prover's `declare_false`)

The deleted third conjunct is not merely unused — it is a **false strengthening** of FS
`thm:smallbox`.  `Work.BoseFixB1B.boxLHS h c C μ n u = (c·ψ(1,μ,n/|B|) − (1/2 − c)·μ²)·W₁ − C·(…)`
(`sectorCountBoxDefs.lean:41`), so item (3) with the frozen `c = 1/20` reads

    (1/20·ψ(1,μ,n/|B|) − (9/20)μ²)·W₁·∫Ψ² − C(…) ≤ sbWordCube ,

whereas FS's row — and every FS-faithful twin in this workspace (`PerBoxFNom`, `perBoxCubeLHS`,
`PerBoxFCube`) — carries `(c·ψ − 1/2·μ²)`.  Item (3) is therefore FS's row **plus** the extra row
`(1/20)·μ²·W₁·∫Ψ²`, which is not payable (the prover's family: `u = 0`, `n = ⌈μ|B|⌉`, `Ψ` a product
state flat up to a fixed-width transition layer: there `ψ(1,μ,n/|B|) → 0`, `sbKinCube = o(μ²W₁)` and
the potential word reduces to `μ²(∬w₂(g₂)/2 − ∬w₁)`, so the row would demand that the
`Γ`-vanishing error bracket pay a positive `μ²W₁`-multiple).

**Consequence.**  `Work.BoseB1Cube.CubeSmallNArbEx` must **not** be targeted (the frozen Prop is
unprovable); the honest node of the large half is `CubeSmallNArb12Ex` — items (1) and (2) only —
which is exactly what `inBoxCubeRowLarge_of_smallNArb12` consumes.  (`cubeSmallNArb12Ex_of_ex` still
holds, but it is *not* a route: the strong node has no proof.)
-/

namespace Work.BoseB1Cube

open MeasureTheory Metric
open scoped Topology Real BigOperators ENNReal

open _root_.BoseGases Submission.BoseGases Work.SmallBoxSliding Work.BoseBox Work.UBB
  Work.BoseFixB1 Work.BoseFixB1B Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- **The weakened per-size node**: `Work.BoseB1Cube.CubeSmallNArb` with its third conjunct (the
`n < Cn·μV` crude row, unused by the descent) deleted. -/
def CubeSmallNArb12 (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (Cn C : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : E3, u ∈ goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ →
        (∀ {n' : ℕ}, Cn * μ * Work.BoseFixB1B.PBBV v μ u ≤ (n' : ℝ) →
            (n' : ℝ) < (Cn + 1) * μ * Work.BoseFixB1B.PBBV v μ u →
            ∀ (Ψ : X n' → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ → Work.BoseFixB1B.InBox v μ u Ψ →
              (1 / 18) * μ * ((n' : ℝ) / Work.BoseFixB1B.PBBV v μ u) * Work.BoseFixB1B.PBW h μ u
                  * (∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ), (Ψ x) ^ 2)
                ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ)
        ∧ (∀ {n'' : ℕ}, (n'' : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1B.PBBV v μ u →
            ∀ (Ψ : X n'' → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ → Work.BoseFixB1B.InBox v μ u Ψ →
              ((1 / 4) * (((n'' : ℝ) / Work.BoseFixB1B.PBBV v μ u) - μ) ^ 2 * Work.BoseFixB1B.PBW h μ u
                  - (1 / 2) * μ ^ 2 * Work.BoseFixB1B.PBW h μ u
                  - C * (μ ^ 2 * (_root_.BoseGases.a v) * Work.BoseFixB1B.PBΓ v μ * Work.BoseFixB1B.PBW h μ u
                      + μ * (_root_.BoseGases.a v)))
                  * (∫ x in Submission.BoseGases.abox n'' (Work.BoseFixB1B.PBℓ v μ), (Ψ x) ^ 2)
                ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ)

/-- **The weakened per-size node, existentially packaged** — the honest residual of the large half
of A4 (`InBoxCubeRowLarge`), strictly weaker than `CubeSmallNArbEx`. -/
def CubeSmallNArb12Ex (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∃ Cn C : ℝ, 2 ≤ Cn ∧ 0 ≤ C ∧ CubeSmallNArb12 v h Cn C

/-- **`CubeSmallNArbEx` implies the weakened node** (drop the third conjunct). -/
theorem cubeSmallNArb12Ex_of_ex {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    (hSN : Work.BoseB1Cube.CubeSmallNArbEx v h) : CubeSmallNArb12Ex v h := by
  obtain ⟨Cn, C, hCn, hC, ε₀, hε₀, hitems⟩ := hSN
  exact ⟨Cn, C, hCn, hC, ε₀, hε₀, fun μ hAdm u hu => ⟨(hitems μ hAdm u hu).1,
    (hitems μ hAdm u hu).2.1⟩⟩

theorem inBoxCubeRowLarge_of_smallNArb12 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (hSN : CubeSmallNArb12Ex v h) :
    Work.BoseB1Cube.InBoxCubeRowLarge v h R := by
  classical
  obtain ⟨Cn_h, C_h, hCn_h, hC_h0, hSNb⟩ := hSN
  obtain ⟨ε_sn, hε_sn, hSNitems⟩ := hSNb
  -- the pointwise bound constant `Ξ`
  set Ξ : ℝ := (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay
    Work.BoseBox.mValue) ^ 2 + 1 with hΞdef
  have hΞ0 : 0 ≤ Ξ := by rw [hΞdef]; positivity
  have hΞpos : 0 < Ξ := by rw [hΞdef]; positivity
  have hΞbd : ∀ (ℓ d : ℝ) (u z : E3),
      (Submission.BoseGases.chiSmallB Work.BoseBox.mValue ℓ d u z) ^ 2 ≤ Ξ := by
    intro ℓ d u z
    have h1 : |Submission.BoseGases.chiSmallB Work.BoseBox.mValue ℓ d u z|
        ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue := by
      refine le_trans (Work.SmallBoxSliding.abs_chiSmallB_le (M := Work.BoseBox.mValue)
        (by norm_num [Work.BoseBox.mValue]) u z) ?_
      refine mul_le_mul_of_nonneg_left ?_ Submission.BoseGases.chiSupAbs_nonneg
      have hb := Submission.BoseGases.chiSmall_decay_coord_le_decay
        (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue]) ((ℓ * d)⁻¹ • z - u)
      rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg _ _)] at hb
    rw [← sq_abs]
    refine le_trans (pow_le_pow_left₀ (abs_nonneg _) h1 2) ?_
    rw [hΞdef]; linarith
  -- the gates
  obtain ⟨ε_w, C_w, hε_w, hC_w0, hWle⟩ :=
    Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime (v := v) h hv hvrad hR hv_supp
  obtain ⟨ε_r, hε_r, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  obtain ⟨Cman, hCman0, hman⟩ := Work.BoseFixB1S.fibSum_le_manifest (v := v) h hv hv1 hvrad
    hR hv_supp hav (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue])
  -- the constants
  set c1 : ℝ := 1 / 10 ^ 6 with hc1def
  have hc1pos : 0 < c1 := by rw [hc1def]; norm_num
  have hc1le100 : c1 ≤ 1 / 100 := by rw [hc1def]; norm_num
  set A : ℝ := _root_.BoseGases.a v with hAdef
  have hApos : 0 < A := hav
  have hΞ1 : 1 ≤ Ξ := by rw [hΞdef]; nlinarith [sq_nonneg (Submission.BoseGases.chiSupAbs
    * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue)]
  -- the free gap coefficient `Kg`: a *sum* of `4·`(each of the four case-2 requirements) `+ 1`,
  -- so that the four requirement inequalities (`scB1_Kg_of_sum`) are immediate.
  set K1 : ℝ := c1 * C_w * Ξ * (2 * 432 ^ 2 + 864 + 1) with hK1def
  set K2 : ℝ := C_w * 432 ^ 2 * Ξ with hK2def
  set K3 : ℝ := 432 * Cman * (1 + C_w * Ξ) * (1 + A) with hK3def
  set K4 : ℝ := Cman with hK4def
  set Kg : ℝ := 4 * K1 + 4 * K2 + 4 * K3 + 4 * K4 + 1 with hKgdef
  have hK1nn : 0 ≤ K1 := by
    rw [hK1def]
    exact mul_nonneg (mul_nonneg (mul_nonneg hc1pos.le hC_w0) hΞ0) (by norm_num)
  have hK2nn : 0 ≤ K2 := by rw [hK2def]; exact mul_nonneg (mul_nonneg hC_w0 (by norm_num)) hΞ0
  have hK3nn : 0 ≤ K3 := by
    rw [hK3def]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCman0)
      (by linarith [mul_nonneg hC_w0 hΞ0])) (by linarith [hApos.le])
  have hK4nn : 0 ≤ K4 := by rw [hK4def]; exact hCman0
  have hKg0 : 0 ≤ Kg := by rw [hKgdef]; linarith only [hK1nn, hK2nn, hK3nn, hK4nn]
  obtain ⟨ε_g, hε_g, hgate⟩ := Work.BoseB1Cube.bGapCoeff_gate (v := v) hav Kg hKg0
  set Cn : ℝ := 2 * (Cn_h + 1) with hCndef
  have hCn2 : 2 ≤ Cn := by rw [hCndef]; linarith
  set Cc : ℝ := C_h * max (C_w * A) 1 with hCcdef
  have hCc0 : 0 ≤ Cc := by
    rw [hCcdef]
    exact mul_nonneg hC_h0 (le_max_of_le_left (by positivity))
  refine ⟨min (min (min ε_w ε_r) ε_g) (min ε_sn 1), Cn, c1, Cc, hCn2, ?_, hc1pos, hCc0, ?_⟩
  · exact lt_min (lt_min (lt_min hε_w hε_r) hε_g) (lt_min hε_sn one_pos)
  intro μ hAdm n Φ u hu hlt hin hnorm
  -- ## standing data
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < PBℓ v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < PBd v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hM1 : 1 ≤ PBM v μ := by
    simp only [PBM, Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.mValue]
    norm_num
  have hVpos : 0 < PBBV v μ u := by
    rw [PBBV]
    exact Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμ hu
  have hVnn : 0 ≤ PBBV v μ u := hVpos.le
  -- the `Adm`-gates
  have hAdm_w : Work.BoseBoxFix.Adm v ε_w μ :=
    Work.BoseFixB1.Adm.mono hAdm
      (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hAdm_r : Work.BoseBoxFix.Adm v ε_r μ :=
    Work.BoseFixB1.Adm.mono hAdm
      (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hAdm_g : Work.BoseBoxFix.Adm v ε_g μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hAdm_s : Work.BoseBoxFix.Adm v ε_sn μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hAdm_ε : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε_r :=
    le_trans hAdm.2.1
      (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  obtain ⟨hR16, hRχ⟩ := hreg μ hμ hAdm_ε
  -- the two quantitative gates
  have hWle' : PBW h μ u ≤ C_w * A * chiMass (PBM v μ) (PBℓ v μ) (PBd v μ) u :=
    hWle μ hAdm_w u
  have hgat : Kg * (μ * (_root_.BoseGases.a v)) ≤ Work.BoseFixB1.bGapCoeff v μ := hgate μ hAdm_g
  -- ## the group sizes
  set X₀ : ℝ := Cn_h * μ * PBBV v μ u with hX0def
  have hCnh : (0:ℝ) < Cn_h := by linarith
  have hX0pos : 0 < X₀ := by
    rw [hX0def]
    exact mul_pos (mul_pos hCnh hμ) hVpos
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 :=
    le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hd1 : PBd v μ ≤ 1 := by
    rw [PBd, Work.BoseFixB1.d_eq_fsXp]
    exact Work.BoseBox.fsXp_le_one (mul_pos hμ (pow_pos hav 3)) ht1 (by norm_num)
  have hμcube : 1 ≤ μ * (PBℓ v μ * PBd v μ) ^ 3 := by
    have hh := Work.BoseFixB1.Regime.one_le_mu_d_mul_sideAt_cube (A := _root_.BoseGases.a v)
      (μ := μ) hav hμ ht1
    simpa only [PBℓ, PBd, mul_comm] using hh
  have hμV : 1 ≤ μ * PBBV v μ u := by
    rw [PBBV]
    have hld : 0 < PBℓ v μ * PBd v μ := mul_pos hℓ hd
    have h13 : μ ^ (-(1 / 3 : ℝ)) ≤ PBℓ v μ * PBd v μ := by
      rw [Work.BoseFixB1S.rpow_neg_third_eq]
      exact Work.BoseFixB1S.inv_third_le_of_one_le_mul_cube hμ hld.le hμcube
    have hvol := Work.BoseFixB1.boxMass_ge_deltaScale_of_goodSet hℓ hd hd1 hμ h13 hu
    have hcube : μ * (μ ^ (-(1 / 3 : ℝ))) ^ 3 = 1 := by
      rw [Work.BoseFixB1S.rpow_neg_third_eq μ]
      rw [← Real.rpow_natCast (μ ^ (-1 / 3 : ℝ)) 3,
        ← Real.rpow_mul (x := μ) hμ.le (-1 / 3) ((3 : ℕ) : ℝ),
        show ((-1 / 3 : ℝ) * ((3 : ℕ) : ℝ)) = -1 by norm_num, Real.rpow_neg_one,
        mul_inv_cancel₀ (ne_of_gt hμ)]
    calc (1 : ℝ) = μ * (μ ^ (-(1 / 3 : ℝ))) ^ 3 := hcube.symm
      _ ≤ μ * Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u :=
          mul_le_mul_of_nonneg_left hvol hμ.le
  set n' : ℕ := ⌈X₀⌉₊ with hn'def
  have hn'pos : 0 < n' := by rw [hn'def]; exact Nat.ceil_pos.mpr hX0pos
  have hn'ge : X₀ ≤ (n' : ℝ) := by rw [hn'def]; exact Nat.le_ceil X₀
  have hn'lt : (n' : ℝ) < X₀ + 1 := by rw [hn'def]; exact Nat.ceil_lt_add_one hX0pos.le
  have hn'le2 : (n' : ℝ) < (Cn_h + 1) * μ * PBBV v μ u := by
    rw [hX0def] at hn'lt
    have hle : X₀ + 1 ≤ (Cn_h + 1) * μ * PBBV v μ u := by
      rw [hX0def]
      have h1 : Cn_h * μ * PBBV v μ u + 1 ≤ Cn_h * μ * PBBV v μ u + μ * PBBV v μ u := by
        linarith [hμV]
      have h2 : Cn_h * μ * PBBV v μ u + μ * PBBV v μ u = (Cn_h + 1) * μ * PBBV v μ u := by ring
      linarith [h1, h2.symm.le, h2.le]
    linarith
  obtain ⟨m : ℕ, hmdef⟩ : ∃ m : ℕ, m = n / n' := ⟨n / n', rfl⟩
  obtain ⟨n'' : ℕ, hn''def⟩ : ∃ n'' : ℕ, n'' = n % n' := ⟨n % n', rfl⟩
  have hn''lt : n'' < n' := by rw [hn''def]; exact Nat.mod_lt n hn'pos
  have hCnle : (Cn_h + 1) * μ * PBBV v μ u ≤ Cn * μ * PBBV v μ u := by
    have h1 : Cn_h + 1 ≤ Cn := by rw [hCndef]; linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hμ.le) hVnn
  have hn'ltn : n' < n := by
    have h1 : (n' : ℝ) < (n : ℝ) := lt_trans hn'le2 (lt_of_le_of_lt hCnle hlt)
    exact_mod_cast h1
  have hm1 : 1 ≤ m := by
    rw [hmdef]; exact (Nat.one_le_div_iff hn'pos).mpr hn'ltn.le
  have hn''V : (n'' : ℝ) ≤ 2 * Cn_h * μ * PBBV v μ u := by
    have h1 : (n'' : ℝ) < (n' : ℝ) := by exact_mod_cast hn''lt
    have h3 : (Cn_h + 1) * μ * PBBV v μ u ≤ 2 * Cn_h * μ * PBBV v μ u := by
      nlinarith [hCnh, hμ, hVpos, mul_pos hμ hVpos]
    linarith
  have hmn : m * n' + n'' = n := by
    rw [hmdef, hn''def, mul_comm]
    exact Nat.div_add_mod n n'
  -- ## the per-size bounds, from the hypothesis
  obtain ⟨hB1all, hB2all⟩ := hSNitems μ hAdm_s u hu
  have hB1 : ∀ (Ψ : Submission.BoseGases.X n' → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
      (∀ᵐ x ∂(MeasureTheory.volume.restrict
          (Submission.BoseGases.abox n' (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
        Ψ x ≠ 0 → ∀ i : Fin n', x i ∈ Submission.BoseGases.dlBox
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
      (1 / 18) * μ * ((n' : ℝ) / PBBV v μ u) * PBW h μ u
          * (∫ x in Submission.BoseGases.abox n' (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Ψ x) ^ 2) ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
    intro Ψ hΨ hloc
    exact hB1all hn'ge hn'le2 Ψ hΨ hloc
  have hB2 : ∀ (Ψ : Submission.BoseGases.X n'' → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
      (∀ᵐ x ∂(MeasureTheory.volume.restrict
          (Submission.BoseGases.abox n'' (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
        Ψ x ≠ 0 → ∀ i : Fin n'', x i ∈ Submission.BoseGases.dlBox
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
      ((1 / 4) * (((n'' : ℝ) / PBBV v μ u) - μ) ^ 2 * PBW h μ u
          - (1 / 2) * μ ^ 2 * PBW h μ u
          - C_h * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
              + μ * (_root_.BoseGases.a v)))
          * (∫ x in Submission.BoseGases.abox n'' (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Ψ x) ^ 2) ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
    intro Ψ hΨ hloc
    exact hB2all hn''V Ψ hΨ hloc
  clear hmdef hn''def
  subst n
  -- ## the descent
  have hdesc := Work.BoseB1Cube.sbWordCube_descent_atSizes (v := v) h hv hv1 hvrad hR hv_supp hav
    hAdm hR16 hRχ u (n' := n') (n'' := n'') (m := m)
    ((1 / 18) * μ * ((n' : ℝ) / PBBV v μ u) * PBW h μ u)
    ((1 / 4) * (((n'' : ℝ) / PBBV v μ u) - μ) ^ 2 * PBW h μ u - (1 / 2) * μ ^ 2 * PBW h μ u
      - C_h * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
          + μ * (_root_.BoseGases.a v)))
    hB1 hB2 Φ.contDiff hin
  rw [hnorm, mul_one] at hdesc
  -- ## abbreviations
  set V : ℝ := Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u with hVdef
  set W : ℝ := PBW h μ u with hWdef
  set χ : ℝ := chiMass (PBM v μ) (PBℓ v μ) (PBd v μ) u with hχdef
  set S : ℝ := Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
      (PBℓ v μ) (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) Φ with hSdef
  set Q : ℝ := Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u)
      (PBℓ v μ) (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u) Φ with hQdef
  -- the count law
  have hVeq : V = (MeasureTheory.volume (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u)).toReal := by
    rw [hVdef, Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  have hvol0 : (0:ℝ)
      < (MeasureTheory.volume (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u)).toReal := by
    rw [← hVeq]; exact hVpos
  have hSQ : S + Q = (m * n' + n'' : ℕ) := by
    have := Work.BoseFixB1S.countIdentityNeutralB1 (N := m * n' + n'') (ℓ := PBℓ v μ) (V := V)
      hℓ hVpos (Work.SmallBoxSliding.measurableSet_dlBox _ _ _) hVeq
      (Work.SmallBoxSliding.dlBox_subset_acube _ _ _) Φ.contDiff.continuous hnorm hin
    rw [hSdef, hQdef]; exact this
  have hQS : 0 ≤ Q := by
    rw [hQdef]
    unfold Work.BoseFixB1S.boxQCount
    exact Finset.sum_nonneg fun i _ => MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have hSS : 0 ≤ S := by
    rw [hSdef]
    unfold Work.BoseFixB1S.boxFlatCount
    exact Finset.sum_nonneg fun i _ => MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have hSle : S ≤ (m * n' + n'' : ℕ) := by linarith [hSQ, hQS]
  have hQle : Q ≤ (m * n' + n'' : ℕ) := by linarith [hSQ, hSS]
  have hW0 : 0 ≤ W := by
    rw [hWdef]; exact Work.BoseFixB1.w1MassB_nonneg (v := v) h hv hvrad hR hv_supp hℓ hd u
  have hχ0 : 0 ≤ χ := by rw [hχdef]; exact Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  -- ## the demand side
  set 𝔉 : ℝ := ∫ x in Submission.BoseGases.abox (m * n' + n'') (PBℓ v μ),
      (Φ x) ^ 2 * demandWeight (v := v) μ u x with hFdef
  have hN1 : Work.BoseBoxFix.normB v μ (m * n' + n'') Φ = 1 := by
    rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]; exact hnorm
  have hΞbd' : ∀ z : E3,
      (Submission.BoseGases.chiSmallB (PBM v μ) (PBℓ v μ) (PBd v μ) u z) ^ 2 ≤ Ξ := by
    intro z
    rw [show PBM v μ = Work.BoseBox.mValue from Work.BoseFixB1.M_eq_mValue μ (_root_.BoseGases.a v)]
    exact hΞbd (PBℓ v μ) (PBd v μ) u z
  have hQd : Work.BoseFixB1.flatScountB (PBM v μ) (PBℓ v μ) (PBd v μ) u Φ
      ≤ (χ / V) * S + 2 * Real.sqrt (Ξ * χ / V) * Real.sqrt (S * Q) + Ξ * Q := by
    have := flatScountB_le_Qdecomp (M := PBM v μ) hM1 hℓ hd u hVpos Φ.contDiff.continuous
      hΞ0 hΞbd'
    rw [← hSdef, ← hQdef, ← hχdef, ← hVdef] at this
    exact this
  have hτ : Work.BoseFixB1.flatScountB (PBM v μ) (PBℓ v μ) (PBd v μ) u Φ / χ
      ≤ S / V + 2 * Real.sqrt (Ξ * χ / V) * Real.sqrt (S * Q) / χ + Ξ * Q / χ := by
    have h1 : ((χ / V) * S) / χ ≤ S / V := by
      have h3 : χ * χ⁻¹ ≤ 1 := by
        rcases eq_or_lt_of_le hχ0 with h | h
        · rw [← h, zero_mul]; norm_num
        · rw [mul_inv_cancel₀ (ne_of_gt h)]
      calc ((χ / V) * S) / χ = (χ * χ⁻¹) * (S / V) := by
            rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]; ring
        _ ≤ 1 * (S / V) := mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = S / V := one_mul _
    calc Work.BoseFixB1.flatScountB (PBM v μ) (PBℓ v μ) (PBd v μ) u Φ / χ
        ≤ ((χ / V) * S + 2 * Real.sqrt (Ξ * χ / V) * Real.sqrt (S * Q) + Ξ * Q) / χ :=
          div_le_div_of_nonneg_right hQd hχ0
      _ = ((χ / V) * S) / χ + (2 * Real.sqrt (Ξ * χ / V) * Real.sqrt (S * Q)) / χ
            + (Ξ * Q) / χ := by rw [add_div, add_div]
      _ ≤ S / V + 2 * Real.sqrt (Ξ * χ / V) * Real.sqrt (S * Q) / χ + Ξ * Q / χ := by
          linarith [h1]
  have hFr : 𝔉 ≤ μ * (Work.BoseFixB1.flatScountB (PBM v μ) (PBℓ v μ) (PBd v μ) u Φ / χ)
      + μ ^ 2 := by
    rw [hFdef]
    have h := Work.BoseB1Cube.flatFterm_le_mu_sq_add (M := PBM v μ) (ℓ := PBℓ v μ)
      (d := PBd v μ) (μ := μ) hμ (Φ : Submission.BoseGases.X (m * n' + n'') → ℝ)
      Φ.contDiff.continuous u
    rw [← hχdef] at h
    have hdiv : (∫ x in Submission.BoseGases.abox (m * n' + n'') (PBℓ v μ),
          (Φ x) ^ 2 * Work.BoseFixB1.nCountB (PBM v μ) (PBℓ v μ) (PBd v μ) u x / χ)
        = Work.BoseFixB1.flatScountB (PBM v μ) (PBℓ v μ) (PBd v μ) u Φ / χ := by
      rw [Work.BoseFixB1.flatScountB, MeasureTheory.integral_div]
    rw [hdiv, hnorm] at h
    simpa only [demandWeight, ← hχdef, mul_one] using h
  -- ## the gap lower bound
  have hsbword : Kg * μ * A * Q - μ * Work.BoseFixB1.fibSum h (PBM v μ) (PBℓ v μ) (PBd v μ) u Φ
      ≤ Work.BoseFixB1B.sbWordCube v h μ u Φ := by
    rw [Work.BoseFixB1B.sbWordCube, Work.BoseFixB1B.sbKinCube]
    have hsp := Work.BoseFixB1.sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1
      hAdm Φ.contDiff.continuous u hR16 hRχ
    have hspn : 0 ≤ Work.BoseFixB1.pairSum v (PBM v μ) (PBℓ v μ) (PBd v μ) u Φ :=
      Work.BoseFixB1.pairSum_nonneg (v := v) hv (M := PBM v μ) u Φ
    have hcs : 0 ≤ Work.BoseFixB1B.cubeSpectral v μ Φ u :=
      Work.BoseFixB1.tBwordKinInd_nonneg (Φ : Submission.BoseGases.X (m * n' + n'') → ℝ)
    have hcn : Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
        (Work.BoseFixB1.bV v μ u) Φ = Q := by
      rw [hQdef]; rfl
    have hgat' : Kg * μ * A ≤ Work.BoseFixB1.bGapCoeff v μ := by
      rw [hAdef]; rw [mul_assoc]; exact hgat
    rw [hcn, hsp]
    nlinarith [hgat', hspn, hcs, hQle, hSQ, hμ.le, hW0]
  -- ## the fibre bound
  have hman' : Work.BoseFixB1.fibSum h (PBM v μ) (PBℓ v μ) (PBd v μ) u Φ
      ≤ (W / V) * S + Cman * A * (Real.sqrt (Q * (W / V * S)) + Q) := by
    have hf := hman (ℓ := PBℓ v μ) (d := PBd v μ) (μ := μ) hℓ hd hR16 hRχ u hVpos
      (n := m * n' + n'') (Φ := (Φ : Submission.BoseGases.X (m * n' + n'') → ℝ))
      Φ.contDiff.continuous
    have hbridge : W = Work.BoseFixB1S.boxM1 (PBℓ v μ)
        (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u)
        (Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u) := by
      rw [hWdef, PBW_eq_boxM1 (v := v) (h := h) hℓ hd hM1]
    have hQcn : Q = Work.UBBInputs8.cnPlusBoxInd (PBℓ v μ)
        (Submission.BoseGases.dlBox (PBℓ v μ) (PBd v μ) u)
        (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u) Φ := by
      rw [hQdef]; rfl
    rw [← Work.BoseFixB1.M_eq_mValue μ (_root_.BoseGases.a v)] at hf
    rw [← hbridge] at hf
    rw [← hSdef, ← hQcn, ← hVdef] at hf
    exact hf
  -- ## the reduced scalars and the goal shape
  set Nn : ℝ := ((m * n' + n'' : ℕ) : ℝ) with hNndef
  have hNn0 : 0 ≤ Nn := by rw [hNndef]; positivity
  set ρc : ℝ := Nn / V with hρcdef
  have hρc0 : 0 ≤ ρc := by rw [hρcdef]; exact div_nonneg hNn0 hVpos.le
  have hWdef' : W = w1MassB h (PBM v μ) (PBℓ v μ) (PBd v μ) u := hWdef
  have hχdef' : χ = chiMass (PBM v μ) (PBℓ v μ) (PBd v μ) u := hχdef
  have hmle : ((n'' : ℝ)) ≤ ((m * n' : ℕ) : ℝ) := by
    have h1 : n'' ≤ m * n' := by
      have h2 : n' ≤ m * n' := by simpa using Nat.mul_le_mul_right n' hm1
      omega
    exact_mod_cast h1
  have hSleN : S ≤ Nn := by rw [hNndef]; exact hSle
  have hQleN : Q ≤ Nn := by rw [hNndef]; exact hQle
  have hnnR : (n'' : ℝ) ≤ (m : ℝ) * (n' : ℝ) := by
    have h := hmle; push_cast at h ⊢; exact h
  have hρcR : ρc = ((m : ℝ) * (n' : ℝ) + (n'' : ℝ)) / V := by
    rw [hρcdef, hNndef]; push_cast; ring
  have hμVn : μ * V ≤ Nn := by
    have hCn1 : (1 : ℝ) ≤ Cn_h := by linarith [hCnh]
    have h2 : μ * V ≤ Cn_h * (μ * V) :=
      le_mul_of_one_le_left (mul_nonneg hμ.le hVpos.le) hCn1
    have h3 : Cn_h * (μ * V) = X₀ := by rw [hX0def]; ring
    have h4 : (n' : ℝ) ≤ Nn := by
      rw [hNndef]; push_cast
      have h5 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have h6 : (0 : ℝ) ≤ (n' : ℝ) := by positivity
      have h7 : (0 : ℝ) ≤ (n'' : ℝ) := by positivity
      nlinarith only [h5, h6, h7]
    linarith only [h2, h3.le, h3.ge, hn'ge, h4]
  set εs : ℝ := χ / (432 ^ 2 * Ξ * V) with hεsdef
  have hεsnn : 0 ≤ εs := by rw [hεsdef]; exact div_nonneg hχ0 (by positivity)
  set Λ : ℝ := 2 * Real.sqrt (Ξ * χ / V) * Real.sqrt (S * Q) / χ with hΛdef
  have hΛ0 : 0 ≤ Λ := by rw [hΛdef]; exact scB1_Lambda_nonneg hΞ0 hχ0 hSS hQS
  set τf : ℝ := S / V + Λ + Ξ * Q / χ with hτfdef
  have hτf0 : 0 ≤ τf := by
    rw [hτfdef]; exact scB1_tau_nonneg hVpos hΞ0 hχ0 hSS hΛ0 hQS
  have hτ : Work.BoseFixB1.flatScountB (PBM v μ) (PBℓ v μ) (PBd v μ) u Φ / χ ≤ τf := by
    rw [hτfdef, hΛdef]; exact scB1_tau_bound hVpos hχ0 hSS hQd
  have hF : 𝔉 ≤ μ * τf + μ ^ 2 := by
    have h1 : μ * (Work.BoseFixB1.flatScountB (PBM v μ) (PBℓ v μ) (PBd v μ) u Φ / χ)
        ≤ μ * τf := mul_le_mul_of_nonneg_left hτ hμ.le
    linarith only [hFr, h1]
  set Γ : ℝ := PBΓ v μ with hΓdef
  have hΓ0 : 0 ≤ Γ := by
    rw [hΓdef, PBΓ, Work.FockBridge.dlGamma]
    exact mul_nonneg (pow_nonneg (le_of_lt (Work.BoseFixB1.paramsAt_KB_pos hAdm)) 3)
      (Real.rpow_nonneg (mul_nonneg hμ.le (pow_nonneg hApos.le 3)) _)
  -- the goal, unfolded
  rw [Work.BoseB1Cube.perBoxFCube_iff, Work.BoseB1Cube.perBoxCubeLHS_eq_fun,
    Work.BoseB1Cube.perBoxCubeLHSFun_eq]
  rw [← hFdef, hN1, ← hWdef', ← hχdef']
  simp only [mul_one]
  -- the reduced form of the goal's error bracket (`Γ`-unfolded, as `perBoxCubeLHSFun_eq` yields it)
  set Γg : ℝ := (R / (PBℓ v μ * PBd v μ)) ^ 2
    + PBKB v μ ^ 3 * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) with hΓgdef
  have hΓg0 : 0 ≤ Γg := by
    rw [hΓgdef]
    exact add_nonneg (sq_nonneg _)
      (mul_nonneg (pow_nonneg (Work.BoseFixB1.paramsAt_KB_pos hAdm).le 3)
        (Real.rpow_nonneg (mul_nonneg hμ.le (pow_nonneg hApos.le 3)) _))
  have hΓle : Γ ≤ Γg := by
    rw [hΓgdef, hΓdef, PBΓ, Work.FockBridge.dlGamma]
    exact le_add_of_nonneg_left (sq_nonneg _)
  have hav0 : (0 : ℝ) ≤ _root_.BoseGases.a v := by rw [← hAdef]; exact hApos.le
  by_cases hcase : Q ≤ εs * Nn
  · -- ### Case 1: the descent pays
    have hSV : S / V ≤ ρc := by
      rw [hρcdef]; exact div_le_div_of_nonneg_right hSleN hVpos.le
    have hSQm : Λ ≤ Nn / (216 * V) := by
      rw [hΛdef]
      exact scB1_case1_sqrtpiece hVpos hΞpos hχ0 hSS hQS hNn0 hSleN hcase hεsdef
    have hSQp : Λ ≤ ρc / 216 := by
      have h2 : ρc / 216 = Nn / (216 * V) := by rw [hρcdef, div_div, mul_comm]
      rw [h2]; exact hSQm
    have hΞQm : Ξ * Q / χ ≤ Nn / (432 ^ 2 * V) :=
      scB1_case1_chiQpiece hVpos hΞpos hχ0 hQS hNn0 hcase hεsdef
    have hΞQp : Ξ * Q / χ ≤ ρc / 432 ^ 2 := by
      have h2 : ρc / 432 ^ 2 = Nn / (432 ^ 2 * V) := by rw [hρcdef, div_div, mul_comm]
      rw [h2]; exact hΞQm
    have hτ1 : τf ≤ ρc * (1 + 1 / 216 + 1 / 432 ^ 2) := by
      rw [hτfdef]; linarith only [hSV, hSQp, hΞQp]
    have hμρ : μ ≤ ρc := by
      rw [hρcdef, le_div_iff₀ hVpos]
      linarith only [hμVn]
    have hD : c1 * (W * 𝔉) ≤ μ * ρc * W / 36 :=
      scB1_case1_D hc1pos.le hc1le100 hW0 hμ.le hρc0 hμρ hF hτ1
    have hM1p : μ * ρc * W / 36 ≤ (m : ℝ) * ((1 / 18) * μ * ((n' : ℝ) / V) * W)
        + (1 / 4) * (((n'' : ℝ) / V) - μ) ^ 2 * W :=
      scB1_case1_M1 hVpos hμ.le hW0 hρcR hnnR
    have hCc1 : C_h * (C_w * (_root_.BoseGases.a v)) ≤ Cc := by
      rw [← hAdef]; rw [hCcdef]
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) hC_h0
    have hCc2 : C_h ≤ Cc := by
      rw [hCcdef]
      calc C_h = C_h * 1 := (mul_one C_h).symm
        _ ≤ C_h * max (C_w * A) 1 := mul_le_mul_of_nonneg_left (le_max_right _ _) hC_h0
    have hWle'' : W ≤ C_w * (_root_.BoseGases.a v) * χ := by
      rw [← hAdef]; exact hWle'
    have hE : C_h * (μ ^ 2 * (_root_.BoseGases.a v) * Γ * W + μ * (_root_.BoseGases.a v))
        ≤ Cc * (μ ^ 2 * (_root_.BoseGases.a v) * Γg * χ + μ * (_root_.BoseGases.a v)) :=
      scB1_case1_E2 hCc1 hCc2 hC_h0 hW0 hWle'' hμ.le hav0 hΓ0 hΓg0 hχ0 hΓle
    exact scB1_case1_close hD hM1p hE hdesc
  · -- ### Case 2: the gap pays
    push Not at hcase
    have hSε : S * εs < Q := by
      have h1 : εs * S ≤ εs * Nn := mul_le_mul_of_nonneg_left hSleN hεsnn
      nlinarith only [h1, hcase]
    have hA1 : χ * S ≤ 432 ^ 2 * Ξ * V * Q := scB1_chiS_of hVpos hΞpos hεsdef hSε
    have hA2 : χ * μ ≤ 432 ^ 2 * Ξ * Q :=
      scB1_chiMu_of hVpos hΞpos hχ0 hμ.le hεsdef hμVn hcase
    have hA3 : χ * Λ ≤ 864 * Ξ * Q := by
      rw [hΛdef]; exact scB1_case2_chiLambda hVpos hΞpos hχ0 hQS hεsdef hSε.le
    obtain ⟨hK1, hK2, hK3, hK4⟩ := scB1_Kg_of_sum hK1nn hK2nn hK3nn hK4nn hKgdef
    have hcase2main : c1 * (W * 𝔉) + μ * Work.BoseFixB1.fibSum h (PBM v μ) (PBℓ v μ) (PBd v μ)
        u Φ ≤ Kg * μ * A * Q :=
      scB1Case2CoreB1 hApos hμ hVpos hΞ1 hC_w0 hCman0 hc1pos hW0 hWle' hSS hQS hχ0 hτf0
        hA1 hA2 hA3 hτfdef.le hF hman' hK1 hK2 hK3 hK4
    have hnn2 : 0 ≤ (1 / 2) * μ ^ 2 * W
        + Cc * (μ ^ 2 * (_root_.BoseGases.a v) * Γg * χ + μ * (_root_.BoseGases.a v)) :=
      add_nonneg (by positivity)
        (mul_nonneg hCc0 (add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav0)
          hΓg0) hχ0) (mul_nonneg hμ.le hav0)))
    exact scB1_case2_close hcase2main hsbword hnn2


end Work.BoseB1Cube
