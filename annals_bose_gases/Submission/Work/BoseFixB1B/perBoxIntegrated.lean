import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.perBoxFWeight_holds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.perBoxIntegrated` — FS `thm:smallbox` integrated, in
collected form

This is the node `Work.BoseFixB1B.perBoxIntegrated` of the a-priori chapter: FS
`thm:smallbox` (`final_v2.tex` 3907) integrated over the sliding boxes `B(u)`, `u ∈ I₋`,
with the error terms **collected** into the single FS scale
`μ²(a v)ℓ³K_B³(μ(a v)³)^{1/2}` of the a-priori bounds:

    c₁·R_Ψ ≤ ∫_{I₋} H_{B(u)}(μ)(Φ) du + ½μ²(∫_{I₋}∬w_{1,B(u)} du)·‖Φ‖²
              + C·μ²(a v)ℓ³K_B³(μ(a v)³)^{1/2}·‖Φ‖² .

## Route

`Submission/Work/BoseFixB1B/integratedOfPointwise.lean` (ours, `sorry`-free and
axiom-clean) delivers the *integrated* per-box bound with the error terms of FS
`thm:smallbox` **uncollected**:

    c₁·R_Ψ ≤ ∫_{I₋}H_{B(u)} du + ½μ²(∫_{I₋}∬w_{1,B(u)})‖Φ‖²
              + C·( μ²(a v)((R/(dℓ))² + K_B³(μ(a v)³)^{1/2})·∫_{I₋}χ_{B(u)}²
                    + μ(a v)·|I₋| )·‖Φ‖² ,

from the *pointwise* per-box bound on `I₋` (FS `thm:smallbox` in the `F`-weighted state
form, `Work.BoseFixB1.PerBoxF`, here obtained by restricting
`Work.BoseFixB1.perBoxFWeight_holds` to the interior) together with the corpus's
`∃ ε₀`-form integrability inputs
(`Work.BoseFixB1.integrableOn_sbWord_interiorSet_regime`,
`Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime`).  Doing the `∫_{I₋}`-bookkeeping
ourselves keeps this node independent of `Work.BoseFixB1.perBoxF_integrated`, and the
three-variable measurability of the localised kernel it needs is supplied `sorry`-free in
`Submission/Work/BoseFixB1B/MeasurabilityGlobal.lean`.

The whole further content of this file is the **constant collection**, i.e. the three
elementary facts (all at FS's parameters, `ℓ = sideAt μ (a v)`, `d = (paramsAt μ (a v)).d`,
`t = μ(a v)³`):

* `∫_{I₋}χ_{B(u)}² ≤ ℓ³` (`interiorChiMass_le_cube`, from
  `Work.SmallBoxSliding.integral_chiMass_eq`, `∫_u χ_{B(u)}² = ℓ³`);
* `(R/(dℓ))² ≤ K_B³ t^{1/2}` (`Work.BoseFixB1.Regime.RsbSide_sq_le`, FS
  `eq:appRassumption`) — so that `(R/(dℓ))² + K_B³t^{1/2} ≤ 2K_B³ t^{1/2}`;
* `|I₋| ≤ 8d^{-3}` (`volume_interiorSet_le_aux`) and `d^{-3} ≤ μℓ³K_B³t^{1/2}`
  (`inv_d_cube_le`) — so that `μ(a v)|I₋| ≤ 8μ²(a v)ℓ³K_B³t^{1/2}`;

whence `C·(…) ≤ (10C)·μ²(a v)ℓ³K_B³t^{1/2}` (`coef_absorb`), the pure-real
arithmetic at the heart of the file.

All the analytic content (`PerBoxF` on the good set, the integrability of the sliding
word and of the masses, the `u`-bookkeeping) is consumed from
`Work.BoseFixB1.perBoxF_integrated` and its own dispatched inputs.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The pure-real coefficient absorption -/

/-- **The constant collection.**  If `X ≤ ℓ³`, `Γ ≤ 2κ` and `Y ≤ 8μℓ³κ` then, for `C ≥ 0`,

    C·(μ²(av)·Γ·X + μ(av)·Y) ≤ (10C)·μ²(av)ℓ³κ .

This is exactly the passage from the *uncollected* error terms of FS `thm:smallbox`
(`μ²aΓ∫χ² + μa|I₋|`) to its collected scale `μ²aℓ³K_B³t^{1/2}` at FS's parameters. -/
private lemma coef_absorb {C μ av ℓ X Y G kap : ℝ}
    (hC : 0 ≤ C) (hμ : 0 ≤ μ) (hav : 0 ≤ av) (hℓ : 0 ≤ ℓ) (hX : 0 ≤ X)
    (hkap : 0 ≤ kap) (hG : 0 ≤ G)
    (hXle : X ≤ ℓ ^ 3) (hGle : G ≤ 2 * kap) (hYle : Y ≤ 8 * (μ * ℓ ^ 3 * kap)) :
    C * (μ ^ 2 * av * G * X + μ * av * Y)
      ≤ (10 * C) * (μ ^ 2 * av * ℓ ^ 3 * kap) := by
  have h1 : μ ^ 2 * av * G * X ≤ μ ^ 2 * av * (2 * kap) * ℓ ^ 3 := by
    have hGX : G * X ≤ (2 * kap) * ℓ ^ 3 := by
      calc G * X ≤ (2 * kap) * X := mul_le_mul_of_nonneg_right hGle hX
        _ ≤ (2 * kap) * ℓ ^ 3 := mul_le_mul_of_nonneg_left hXle (by linarith)
    calc μ ^ 2 * av * G * X = μ ^ 2 * av * (G * X) := by ring
      _ ≤ μ ^ 2 * av * ((2 * kap) * ℓ ^ 3) := mul_le_mul_of_nonneg_left hGX (by positivity)
      _ = μ ^ 2 * av * (2 * kap) * ℓ ^ 3 := by ring
  have h2 : μ * av * Y ≤ μ * av * (8 * (μ * ℓ ^ 3 * kap)) :=
    mul_le_mul_of_nonneg_left hYle (by positivity)
  have h3 : μ ^ 2 * av * (2 * kap) * ℓ ^ 3 + μ * av * (8 * (μ * ℓ ^ 3 * kap))
      = 10 * (μ ^ 2 * av * ℓ ^ 3 * kap) := by ring
  have h4 : μ ^ 2 * av * G * X + μ * av * Y ≤ 10 * (μ ^ 2 * av * ℓ ^ 3 * kap) := by
    linarith [h1, h2, h3]
  calc C * (μ ^ 2 * av * G * X + μ * av * Y)
      ≤ C * (10 * (μ ^ 2 * av * ℓ ^ 3 * kap)) := mul_le_mul_of_nonneg_left h4 hC
    _ = (10 * C) * (μ ^ 2 * av * ℓ ^ 3 * kap) := by ring

/-! ## 2. The `χ_{B(u)}²`-mass of the interior -/

/-- `∫_{I₋} χ_{B(u)}² ≤ ℓ³`: the full `u`-mass is `ℓ³`
(`Work.SmallBoxSliding.integral_chiMass_eq`) and the integrand is nonnegative. -/
private lemma interiorChiMass_le_cube {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) :
    (∫ u in Work.SmallBoxSliding.interiorSet ℓ d μ, Work.SmallBoxSliding.chiMass M ℓ d u)
      ≤ ℓ ^ 3 := by
  have hint : MeasureTheory.Integrable
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.SmallBoxSliding.chiMass M ℓ d u)
      MeasureTheory.volume :=
    (Work.SmallBoxSliding.integrable_chiSmallB_mass hM hℓ hd).congr
      (Filter.Eventually.of_forall fun u => (Work.SmallBoxSliding.chiMass_def M ℓ d u).symm)
  calc (∫ u in Work.SmallBoxSliding.interiorSet ℓ d μ, Work.SmallBoxSliding.chiMass M ℓ d u)
      ≤ ∫ u : EuclideanSpace ℝ (Fin 3), Work.SmallBoxSliding.chiMass M ℓ d u :=
        setIntegral_le_integral hint
          (Filter.Eventually.of_forall fun u => Work.SmallBoxSliding.chiMass_nonneg M ℓ d u)
    _ = ℓ ^ 3 := Work.SmallBoxSliding.integral_chiMass_eq hM hℓ hd

/-! ## 3. The two monomial bounds on `d^{-3}` and on the volume of `I₋` -/

/-- `d^{-3} ≤ μℓ³K_B³t^{1/2}` at FS's parameters (`t = μA³ ≤ 1`): both sides are the
monomials `t^{-18/323}` and `t^{-45/646}` of `Work.BoseFixB1.RegimeAux`. -/
private lemma inv_d_cube_le {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) (ht : μ * A ^ 3 ≤ 1) :
    ((Work.BoseBox.paramsAt μ A).d ^ 3)⁻¹
      ≤ μ * Work.BoseBox.sideAt μ A ^ 3 * (Work.BoseBox.paramsAt μ A).KB ^ 3
          * (μ * A ^ 3) ^ (1 / 2 : ℝ) := by
  have ht0 : 0 < μ * A ^ 3 := mul_pos hμ (pow_pos hA 3)
  have h1 : (Work.BoseBox.paramsAt μ A).d ^ 3 = Work.BoseBox.fsXp (μ * A ^ 3) 18 :=
    Work.BoseFixB1.d_cube_eq hA hμ
  have h2 : μ * Work.BoseBox.sideAt μ A ^ 3 * (Work.BoseBox.paramsAt μ A).KB ^ 3
      * (μ * A ^ 3) ^ (1 / 2 : ℝ) = Work.BoseBox.fsXp (μ * A ^ 3) (-(45 / 2)) :=
    Work.BoseFixB1.mu_ell_cube_KB3_half_eq hA hμ
  rw [h1, h2, Work.BoseBox.fsXp_inv ht0]
  exact Work.BoseBox.fsXp_le_fsXp ht0 ht (by norm_num)

/-- **The volume of the interior.**  `I₋ = interiorSet ℓ d μ` is contained in the cube
`{|u_j| ≤ (1+d)/(2d)}`, whose volume is `((1+d)/d)³ ≤ 8d^{-3}` for `0 < d ≤ 1`. -/
private lemma volume_interiorSet_le_aux {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hμ : 0 < μ) :
    MeasureTheory.volume (Work.SmallBoxSliding.interiorSet ℓ d μ)
      ≤ ENNReal.ofReal (8 * (d ^ 3)⁻¹) := by
  have hℓd : 0 < ℓ * d := mul_pos hℓ hd0
  have h2μ : 0 ≤ 2 * μ ^ (-(1 / 3) : ℝ) :=
    (mul_pos two_pos (Real.rpow_pos_of_pos hμ _)).le
  have hsub : Work.SmallBoxSliding.interiorSet ℓ d μ
      ⊆ Submission.BoseGases.acube ((1 + d) / d) := by
    intro u hu
    rw [Work.SmallBoxSliding.mem_interiorSet_iff] at hu
    rw [Submission.BoseGases.mem_acube_iff]
    intro j
    have hb : (ℓ * d) * |u.ofLp j| ≤ (1 / 2) * ℓ * (1 + d) := by
      have h := hu j
      rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hℓd] at h
      linarith
    have huj : |u.ofLp j| ≤ ((1 + d) / d) / 2 := by
      have hdiv : |u.ofLp j| ≤ ((1 / 2) * ℓ * (1 + d)) / (ℓ * d) := by
        rw [le_div_iff₀ hℓd]
        linarith
      have heq : ((1 / 2) * ℓ * (1 + d)) / (ℓ * d) = ((1 + d) / d) / 2 := by
        field_simp
      rw [← heq]
      exact hdiv
    have habs := abs_le.mp huj
    rw [Set.mem_Icc]
    constructor <;> linarith [habs.1, habs.2]
  calc MeasureTheory.volume (Work.SmallBoxSliding.interiorSet ℓ d μ)
      ≤ MeasureTheory.volume (Submission.BoseGases.acube ((1 + d) / d)) :=
        measure_mono hsub
    _ = ENNReal.ofReal (((1 + d) / d) ^ 3) :=
        Submission.BoseGases.acube_volume _ (by positivity)
    _ ≤ ENNReal.ofReal (8 * (d ^ 3)⁻¹) := by
        apply ENNReal.ofReal_le_ofReal
        have hd3 : 0 < d ^ 3 := by positivity
        rw [div_pow, div_le_iff₀ hd3]
        have h2 : (1 + d) ^ 3 ≤ 8 := by
          have h1 : 1 + d ≤ 2 := by linarith
          have h0 : 0 ≤ 1 + d := by linarith
          calc (1 + d) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ h0 h1 3
            _ = 8 := by norm_num
        calc (1 + d) ^ 3 ≤ 8 := h2
          _ = 8 * (d ^ 3)⁻¹ * d ^ 3 := by
              rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hd3), mul_one]

/-! ## 4. The node -/

theorem perBoxIntegrated {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ} (hJ : Work.UBB.lhyC ≤ J) :
    ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
            c₁ * Work.BoseFixB1.RPsi v h μ (Φ : Submission.BoseGases.X n → ℝ)
              ≤ (∫ u in Work.SmallBoxSliding.interiorSet
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                    Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
                + (1 / 2) * μ ^ 2
                    * (∫ u in Work.SmallBoxSliding.interiorSet
                        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                        Work.BoseFixB1.w1MassB h
                          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                    * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                + C * (μ ^ 2 * (_root_.BoseGases.a v)
                          * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
                          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                          * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
                    * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
  -- The integrated per-box bound, from our own integration (`integratedOfPointwise`); its
  -- only non-elementary input is the *pointwise* per-box bound on `I₋ ⊆ goodSet`
  -- (`Work.BoseFixB1.perBoxFWeight_holds`, FS `thm:smallbox` in the `F`-weighted state form),
  -- restricted here to the interior; the integrability inputs are the corpus's corrected
  -- `∃ ε₀`-form statements.
  have hperI : ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          ∀ (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          Work.BoseFixB1.PerBoxF v h R c₁ C μ n Φ u := by
    obtain ⟨ε₀, c₁, C, hε₀, hc₁, hC, hmain⟩ :=
      Work.BoseFixB1.perBoxFWeight_holds (v := v) h hv hv1 hvrad hR hv_supp hav
    refine ⟨ε₀, c₁, C, hε₀, hc₁, hC, ?_⟩
    intro μ hAdm n Φ _ u hu
    exact hmain μ hAdm n Φ u
      (Work.SmallBoxSliding.interiorSet_subset_goodSet (Work.BoseFixB1.adm_mu_pos hAdm) hu)
  obtain ⟨ε₁, c₁, C, hε₁, hc₁, hC, hmain⟩ :=
    Work.BoseFixB1B.integratedPerBox_of_pointwise (v := v) h hv hv1 hvrad hR hv_supp hav hJ
      hperI
      (Work.BoseFixB1.integrableOn_sbWord_interiorSet_regime (v := v) h hv hv1 hvrad hR hv_supp hav)
      (Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime (v := v) h hv hvrad hR hv_supp)
  have hTpos : 0 < ((_root_.BoseGases.a v) ^ 2 / R ^ 2) ^ (646 / 341 : ℝ) :=
    Real.rpow_pos_of_pos (by positivity) _
  refine ⟨min ε₁ (min 1 (((_root_.BoseGases.a v) ^ 2 / R ^ 2) ^ (646 / 341 : ℝ))),
    c₁, 10 * C, lt_min hε₁ (lt_min one_pos hTpos), hc₁, by linarith, ?_⟩
  intro μ hAdm n Φ hlow
  -- ## the ambient data
  have hμ : 0 < μ := hAdm.1
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₁ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hcore := hmain μ hAdm₁ n Φ hlow
  have ht_min : μ * (_root_.BoseGases.a v) ^ 3
      ≤ min ε₁ (min 1 (((_root_.BoseGases.a v) ^ 2 / R ^ 2) ^ (646 / 341 : ℝ))) :=
    Work.BoseFixB1.adm_dilute hAdm
  have ht_one : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 :=
    le_trans ht_min (le_trans (min_le_right _ _) (min_le_left _ _))
  have ht_T : μ * (_root_.BoseGases.a v) ^ 3
      ≤ ((_root_.BoseGases.a v) ^ 2 / R ^ 2) ^ (646 / 341 : ℝ) :=
    le_trans ht_min (le_trans (min_le_right _ _) (min_le_right _ _))
  have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hd1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 :=
    Work.BoseBox.fsXp_le_one ht0 ht_one (by norm_num)
  have hKB : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB :=
    Work.BoseFixB1.paramsAt_KB_pos hAdm
  have hM1 : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.paramsAt_eq_fsParams]
    norm_num [Work.BoseBox.fsParams, Work.BoseBox.mValue]
  -- ## the three collection facts
  have hkap_nn : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
      * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) :=
    mul_nonneg (pow_nonneg hKB.le 3) (Real.rpow_nonneg ht0.le _)
  have hG_nn : 0 ≤ (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
      + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
          * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) :=
    add_nonneg (sq_nonneg _) hkap_nn
  have hGle : (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
      + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
          * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)
      ≤ 2 * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
          * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) := by
    have hRsb0 := Work.BoseFixB1B.RsbSide_sq_le_holds (A := _root_.BoseGases.a v) (R := R)
      (μ := μ) hav hR hμ ht_T
    have hRsb : (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
        ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) := by
      rw [mul_comm (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d]
      exact hRsb0
    linarith
  have hXle : (∫ u in Work.SmallBoxSliding.interiorSet
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
        Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      ≤ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 :=
    interiorChiMass_le_cube hM1 hℓ hd
  have hYle : (MeasureTheory.volume (Work.SmallBoxSliding.interiorSet
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal
      ≤ 8 * (μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
          * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))) := by
    have h1 : (MeasureTheory.volume (Work.SmallBoxSliding.interiorSet
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal
        ≤ 8 * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 3)⁻¹ := by
      have hvol := volume_interiorSet_le_aux hℓ hd hd1 hμ
      calc (MeasureTheory.volume (Work.SmallBoxSliding.interiorSet
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal
          ≤ (ENNReal.ofReal (8 * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 3)⁻¹)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
        _ = 8 * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 3)⁻¹ :=
            ENNReal.toReal_ofReal (by positivity)
    have h2 : 8 * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 3)⁻¹
        ≤ 8 * (μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
            * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))) := by
      have hinv := inv_d_cube_le (A := _root_.BoseGases.a v) (μ := μ) hav hμ ht_one
      linarith [hinv]
    linarith [h1, h2]
  -- ## the coefficient inequality and the assembly
  have hnb : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseFixB1.normB_nonneg _
  have hXnn : 0 ≤ ∫ u in Work.SmallBoxSliding.interiorSet
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
        Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
    setIntegral_nonneg
      (Work.SmallBoxSliding.measurableSet_interiorSet
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)
      (fun u _ => Work.SmallBoxSliding.chiMass_nonneg _ _ _ u)
  have hcoef := coef_absorb (C := C) (μ := μ) (av := _root_.BoseGases.a v)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (X := ∫ u in Work.SmallBoxSliding.interiorSet
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
          Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (Y := (MeasureTheory.volume (Work.SmallBoxSliding.interiorSet
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal)
    (G := (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
          + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
    (kap := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
    hC (le_of_lt hμ) (le_of_lt hav) (le_of_lt hℓ)
    hXnn hkap_nn hG_nn hXle hGle hYle
  calc c₁ * Work.BoseFixB1.RPsi v h μ (Φ : Submission.BoseGases.X n → ℝ)
      ≤ (∫ u in Work.SmallBoxSliding.interiorSet
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
            Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
        + (1 / 2) * μ ^ 2
            * (∫ u in Work.SmallBoxSliding.interiorSet
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                Work.BoseFixB1.w1MassB h
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        + C * (μ ^ 2 * (_root_.BoseGases.a v)
                  * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
                      + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                        * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
                  * (∫ u in Work.SmallBoxSliding.interiorSet
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                      Work.SmallBoxSliding.chiMass
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                + μ * (_root_.BoseGases.a v)
                  * (MeasureTheory.volume (Work.SmallBoxSliding.interiorSet
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := hcore
    _ ≤ (∫ u in Work.SmallBoxSliding.interiorSet
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
            Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
        + (1 / 2) * μ ^ 2
            * (∫ u in Work.SmallBoxSliding.interiorSet
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                Work.BoseFixB1.w1MassB h
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        + (10 * C) * (μ ^ 2 * (_root_.BoseGases.a v)
                  * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
                  * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                  * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
        have hstep := mul_le_mul_of_nonneg_right hcoef hnb
        linarith [hstep]

end Work.BoseFixB1B
