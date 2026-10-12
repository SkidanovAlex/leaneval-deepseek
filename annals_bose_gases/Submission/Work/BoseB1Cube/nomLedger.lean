import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseB1Cube.NomDefs
import Submission.Work.BoseB1Cube.NominalPerBox
import Submission.Work.BoseB1Cube.aestronglyMeasurable_fibSum
import Submission.Work.BoseB1Cube.fibSum_le_bandS_sq_atParams
import Submission.Work.BoseB1Cube.nomRegimeParams
import Submission.Work.BoseB1Cube.volume_interiorSet_bandSet_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.nomLedger` — FS `thm:aprioriHLambda`'s ledger at the nominal spelling

The a-priori bounds of FS `eq:aprioriRn+` (the remainder `R_Ψ` and the excited count `n₊`), obtained
from FS's own route: the localisation `eq:appsliding` (`Work.BoseB1Cube.SlidingGoodCube`, which
integrates the slot word `sbWordSlot (m(u)μ)` over the **good set** only) together with FS
`thm:smallbox` in the nominal (indicator-count) spelling (`Work.BoseB1Cube.PerBoxFNom`) at the slot
`μ` on the whole good set.

Two points of the formalisation:

* the localisation and the row use **the same box** and **the same slot** for every `u ∈ goodSet`;
  FS's `m(u) = 4` on the boundary layer is `sbWordSlot (4μ) = sbWordCube − 3μ·fibSum`, and the
  slot-`μ` row applied on the layer too (`u ∈ goodSet` suffices) is enough for the ledger — the
  only thing the layer contributes is the small `χ`-mass `∫_{I₋ᶜ} χ_B² ≤ C(μa³)^{M/3}ℓ³`
  (`WB.interior_compl_mass_le`) which is absorbed in the a-priori scale `μ²aℓ³κ`;
* the fibre deviation `fibSum` on the layer is paid by the **proved** bad-band smallness
  `Work.BoseB1Cube.bandErrSmall_holds`: `fibSum ≤ bandK·bandS²·n‖Φ‖²` on the band, and
  `C·bandErr ≤ (a v)·κ` for every prescribed `C`, so the fibre term costs `E·μ(a v)κ·n‖Φ‖²`
  with `E > 0` **as small as we like** (at the price of `ε₀`).

The conclusion is exactly the pair of FS a-priori rows at the nominal remainder `nomRPsi`:
`c₁·nomRPsi ≤ C_A·μ²(a v)ℓ³κ·‖Φ‖² + E·μ(a v)κ·n‖Φ‖²` and the same for `n₊`, with `κ = K_B³(μa³)^{1/2}`.
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
open Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- `κ = K_B³(μ(a v)³)^{1/2}`, FS's a-priori error scale. -/
noncomputable def kappa (v : E3 → ℝ) (μ : ℝ) : ℝ :=
  (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)

/-- **The bad-band decay cost is smaller than `κ`**: the sharp form of
`Work.BoseB1Cube.bandDecaySmall`, with the *diluteness power* kept instead of being absorbed in a
constant.  `d = (μa³)^{6/323}` and `chiSmallBandDecay 48 d = χ_∞²(χ_d(48))²(d⁻¹)^{96}`, so the
product `12(1+d)²·chiSmallBandDecay 48 d·(μa³)^{16}` equals
`12(1+d)²χ_∞²χ_d²(μa³)^{4592/323} ≤ 48χ_∞²χ_d²·κ` because `4592/323 ≥ 287/646`. -/
theorem bandDecayKappa {a : ℝ} (ha : 0 < a) :
    ∃ ε₀ Kb : ℝ, 0 < ε₀ ∧ 0 ≤ Kb ∧ ∀ μ : ℝ, 0 < μ → μ * a ^ 3 ≤ ε₀ →
      12 * (1 + (Work.BoseBox.paramsAt μ a).d) ^ 2
          * Submission.BoseGases.chiSmallBandDecay (Work.BoseBox.paramsAt μ a).M
              (Work.BoseBox.paramsAt μ a).d
          * (μ * a ^ 3) ^ (((Work.BoseBox.paramsAt μ a).M : ℕ) / 3 : ℝ)
        ≤ Kb * ((Work.BoseBox.paramsAt μ a).KB ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ)) := by
  refine ⟨1, 48 * Submission.BoseGases.chiSupAbs ^ 2
    * (Submission.BoseGases.chiSmallDecay 48) ^ 2, one_pos, by positivity, ?_⟩
  intro μ hμ ht
  have hexp : (((Work.BoseBox.paramsAt μ a).M : ℕ) / 3 : ℝ) = 16 := by
    rw [Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  set t : ℝ := μ * a ^ 3 with ht_def
  have ht0 : 0 < t := by rw [ht_def]; positivity
  have ht1 : t ≤ 1 := by rw [ht_def] at ht; exact ht
  set d : ℝ := (Work.BoseBox.paramsAt μ a).d with hd_def
  have hdeq : d = Work.BoseBox.fsXp t 6 := by
    rw [hd_def, ht_def]; exact Work.BoseFixB1.d_eq_fsXp μ a
  have hd0 : 0 ≤ d := hdeq ▸ Work.BoseBox.fsXp_nonneg ht0.le
  have h96 : (d⁻¹) ^ 96 = Work.BoseBox.fsXp t (-576) := by
    rw [hdeq, Work.BoseBox.fsXp_inv ht0, Work.BoseBox.fsXp_pow ht0.le]
    norm_num
  have h16 : t ^ (16 : ℝ) = Work.BoseBox.fsXp t 5168 := by
    rw [Work.BoseBox.fsXp]; norm_num
  have hk : (Work.BoseBox.paramsAt μ a).KB ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ)
      = Work.BoseBox.fsXp t (287 / 2) := by
    rw [← ht_def]
    exact Work.BoseFixB1.KB3_half_eq (A := a) (μ := μ) ha hμ
  have hprod : (d⁻¹) ^ 96 * t ^ (16 : ℝ)
      ≤ (Work.BoseBox.paramsAt μ a).KB ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ) := by
    rw [h96, h16, hk, Work.BoseBox.fsXp_mul ht0]
    rw [Work.BoseBox.fsXp, Work.BoseBox.fsXp]
    have e1 : ((-576 + 5168 : ℝ) / 323) = (4592 : ℝ) / 323 := by norm_num
    have e2 : ((287 : ℝ) / 2 / 323) = (287 : ℝ) / 646 := by norm_num
    rw [e1, e2]
    exact Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by norm_num)
  have hd1 : d ≤ 1 := hdeq ▸ Work.BoseBox.fsXp_le_one ht0 ht1 (by norm_num)
  have h4 : (1 + d) ^ 2 ≤ 4 := by
    have h2 : 1 + d ≤ 2 := by linarith
    have h2' : 0 ≤ 1 + d := by linarith
    calc (1 + d) ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ h2' h2 2
      _ = 4 := by norm_num
  have hprod0 : 0 ≤ (d⁻¹) ^ 96 * t ^ (16 : ℝ) :=
    mul_nonneg (pow_nonneg (inv_nonneg.mpr hd0) 96) (Real.rpow_nonneg ht0.le 16)
  have hband : Submission.BoseGases.chiSmallBandDecay (Work.BoseBox.paramsAt μ a).M d
      = Submission.BoseGases.chiSupAbs ^ 2 * (Submission.BoseGases.chiSmallDecay 48) ^ 2
          * (d⁻¹) ^ 96 := rfl
  have hκnn : 0 ≤ (Work.BoseBox.paramsAt μ a).KB ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ) := by
    rw [hk]; exact Work.BoseBox.fsXp_nonneg ht0.le
  rw [hexp]
  calc 12 * (1 + d) ^ 2
        * Submission.BoseGases.chiSmallBandDecay (Work.BoseBox.paramsAt μ a).M d
        * t ^ (16 : ℝ)
      = 12 * (Submission.BoseGases.chiSupAbs ^ 2
            * (Submission.BoseGases.chiSmallDecay 48) ^ 2)
          * ((1 + d) ^ 2 * ((d⁻¹) ^ 96 * t ^ (16 : ℝ))) := by rw [hband]; ring
    _ ≤ 12 * (Submission.BoseGases.chiSupAbs ^ 2
            * (Submission.BoseGases.chiSmallDecay 48) ^ 2)
          * (4 * ((Work.BoseBox.paramsAt μ a).KB ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc (1 + d) ^ 2 * ((d⁻¹) ^ 96 * t ^ (16 : ℝ))
            ≤ 4 * ((d⁻¹) ^ 96 * t ^ (16 : ℝ)) := mul_le_mul_of_nonneg_right h4 hprod0
          _ ≤ 4 * ((Work.BoseBox.paramsAt μ a).KB ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = 48 * Submission.BoseGases.chiSupAbs ^ 2 * (Submission.BoseGases.chiSmallDecay 48) ^ 2
          * ((Work.BoseBox.paramsAt μ a).KB ^ 3 * (μ * a ^ 3) ^ (1 / 2 : ℝ)) := by ring
/-- The band set has finite measure (it sits in the cube `acube ((1+d)/d)`). -/
theorem bandSet_volume_lt_top {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    (volume : Measure E3) (Work.SmallBoxSliding.bandSet ℓ d μ) < ⊤ := by
  have hA : (0 : ℝ) < (1 + d) / d := by positivity
  have hvol : volume (Submission.BoseGases.acube ((1 + d) / d))
      = ENNReal.ofReal (((1 + d) / d) ^ 3) :=
    Submission.BoseGases.acube_volume _ hA.le
  have hsub : Work.SmallBoxSliding.bandSet ℓ d μ ⊆ Submission.BoseGases.acube ((1 + d) / d) := by
    intro u hu
    rw [Work.SmallBoxSliding.mem_bandSet_iff] at hu
    rw [Submission.BoseGases.mem_acube_iff]
    intro j
    have h1 := hu.2 j
    have hℓd : 0 < ℓ * d := mul_pos hℓ hd
    rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hℓd] at h1
    have h2 : |u.ofLp j| ≤ (1 / 2 * ℓ * (1 + d)) / (ℓ * d) := (le_div_iff₀ hℓd).2 (by linarith [h1])
    have h3 : (1 / 2 * ℓ * (1 + d)) / (ℓ * d) = ((1 + d) / d) / 2 := by
      field_simp
    rw [h3] at h2
    have h4 := abs_le.mp h2
    rw [Set.mem_Icc]
    constructor <;> linarith [h4.1, h4.2]
  exact lt_of_le_of_lt (measure_mono hsub) (by rw [hvol]; exact ENNReal.ofReal_lt_top)

/-- Monotonicity of set integrals for a nonnegative integrand. -/
lemma setIntegral_mono_of_subset {f : E3 → ℝ} {s t : Set E3} (hst : s ⊆ t)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hf : Integrable f volume)
    (h0 : ∀ x, 0 ≤ f x) :
    (∫ x in s, f x) ≤ ∫ x in t, f x := by
  rw [← MeasureTheory.integral_indicator hs, ← MeasureTheory.integral_indicator ht]
  refine MeasureTheory.integral_mono (hf.indicator hs) (hf.indicator ht) fun x => ?_
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hst hx)]
  · rw [Set.indicator_of_notMem hx]
    exact Set.indicator_nonneg (fun _ _ => h0 _) x

/-- The nominal count is the indicator count of the sliding box. -/
lemma nomCnt_eq_boxIndCount (ℓ d : ℝ) (u : E3) {n : ℕ} (x : X n) :
    nomCnt ℓ d u x = boxIndCount ℓ d u x := by
  simp only [nomCnt, boxIndCount, Work.SmallBoxSliding.boxInd]

/-- `fibSum ≥ 0` (the localised one-body fibre kernel is a.e. nonnegative). -/
lemma fibSum_nonneg {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) {n : ℕ} (Φ : X n → ℝ) :
    0 ≤ Work.BoseFixB1.fibSum h M ℓ d u Φ := by
  rw [Work.BoseFixB1.fibSum]
  refine integral_nonneg_of_ae (Eventually.of_forall fun x => ?_)
  refine mul_nonneg (sq_nonneg _) ?_
  refine Finset.sum_nonneg fun i _ => integral_nonneg_of_ae ?_
  have hae : ∀ᵐ y : E3, 0 ≤ Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y :=
    (Work.SmallBoxSliding.ae_g0_comp_sub hv hvrad hv_supp hR h (x i)).mono
      (fun y hy => Work.BoseFixB1B.wSmall1Pair_nonneg_of_g0 hy)
  exact Filter.Eventually.filter_mono (MeasureTheory.ae_mono Measure.restrict_le_self) hae

set_option maxHeartbeats 16000000 in
/-- **The nominal a-priori ledger** (FS `thm:aprioriHLambda`, the two rows `eq:aprioriRn+` at the
nominal remainder).  From FS's localisation `SlidingGoodCube` and the per-box row `PerBoxFNom`
at the slot `μ` on the good set: for every low state, the nominal remainder `nomRPsi` and the
excited count `n₊` are bounded by `C_A·μ²(a v)ℓ³κ·‖Φ‖² + E·μ(a v)κ·n‖Φ‖²`, with `E > 0`
**prescribed** (the fibre-band term is paid by `bandErrSmall_holds`). -/
theorem ledgerNom {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < a v)
    {c₁ C E : ℝ} (hc₁ : 0 < c₁) (hC : 0 ≤ C) (hE : 0 < E)
    (hper : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
          u ∈ goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
          ∀ μp : ℝ, (μp = μ ∨ μp = 4 * μ) → PerBoxFNom v h R c₁ C μp μ n Φ u)
    (hS : SlidingGoodCube v h) :
    ∃ ε₀ C_A : ℝ, 0 < ε₀ ∧ 0 ≤ C_A ∧
      ∀ (J μ : ℝ), Adm v ε₀ μ → J ≤ (paramsAt μ (a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
          0 < normB v μ n (Φ : X n → ℝ) → IsLowB v h J μ n Φ →
            c₁ * nomRPsi h μ (Φ : X n → ℝ)
                ≤ C_A * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * kappa v μ)
                    * normB v μ n (Φ : X n → ℝ)
                  + E * (μ * (a v) * kappa v μ) * (n : ℝ) * normB v μ n (Φ : X n → ℝ)
            ∧ ((paramsAt μ (a v)).b / (2 * (sideAt μ (a v)) ^ 2))
                  * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
                ≤ C_A * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * kappa v μ)
                    * normB v μ n (Φ : X n → ℝ)
                  + E * (μ * (a v) * kappa v μ) * (n : ℝ) * normB v μ n (Φ : X n → ℝ) := by
  classical
  obtain ⟨εp, hεp, hperAll⟩ := hper
  obtain ⟨εS, CS, hCS1, hεS, hSfun⟩ := hS
  obtain ⟨εm, Cm, hεm, hCm, hmassm⟩ :=
    Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime (v := v) h hv hvrad hR hv_supp
  obtain ⟨εR, hεR, hreg⟩ :=
    Work.BoseFixB1.WB.window_regime (v := v) (R := R) (C₁ := max Cm 1) (C_A := 1) hav hR
      (lt_of_lt_of_le one_pos (le_max_right _ _)) one_pos
  obtain ⟨εW, CW, hεW, hCW, hWup⟩ :=
    Work.BoseFixB1B.w1MassB_integral_le_holds (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εb, Kb, hεb, hKb, hbsharp⟩ := bandDecayKappa (a := a v) hav
  obtain ⟨εg, hεg, hεgle, hp⟩ := nomRegimeParams (a := a v) (R := R) hav hR
  obtain ⟨εK, hεK, hKerr⟩ :=
    Work.BoseB1Cube.bandErrSmall_holds h hv hv1 hvrad hR hv_supp hav (3 / E) (by positivity)
  obtain ⟨εsbw, hεsbw, hsbwInt⟩ :=
    Work.BoseFixB1S.sbWordCubeIntegrable (v := v) h hv hv1 hvrad hR hv_supp hav
  -- the threshold for `ell_residual_nonneg_fb`
  set εθ : ℝ := min ((1 / 4 : ℝ) ^ (969 / 166 : ℝ)) 1 with hεθdef
  have hεθpos : 0 < εθ := by
    rw [hεθdef]
    exact lt_min (Real.rpow_pos_of_pos (by norm_num) _) one_pos
  -- the main threshold
  set E₀ : ℝ := min (min (min (min εp εS) (min εm εR))
      (min (min εW εb) (min εg εK))) εsbw with hE₀def
  have hE₀pos : 0 < E₀ := by
    rw [hE₀def]
    exact lt_min (lt_min (lt_min (lt_min hεp hεS) (lt_min hεm hεR))
      (lt_min (lt_min hεW hεb) (lt_min hεg hεK))) hεsbw
  have hEεp : E₀ ≤ εp := by
    rw [hE₀def]
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hEεS : E₀ ≤ εS := by
    rw [hE₀def]
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hEεm : E₀ ≤ εm := by
    rw [hE₀def]
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hEεR : E₀ ≤ εR := by
    rw [hE₀def]
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hEεW : E₀ ≤ εW := by
    rw [hE₀def]
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hEεb : E₀ ≤ εb := by
    rw [hE₀def]
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hEεg : E₀ ≤ εg := by
    rw [hE₀def]
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hEεK : E₀ ≤ εK := by
    rw [hE₀def]
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hEεsbw : E₀ ≤ εsbw := by rw [hE₀def]; exact min_le_right _ _
  refine ⟨min E₀ εθ, 4 * Real.pi * (1 + CW) + 18 * C + (1 / 2) * Cm * (2 : ℝ) ^ 96 * Kb
      + 2 * C * (2 : ℝ) ^ 96 * Kb,
    lt_min hE₀pos hεθpos, by positivity, ?_⟩
  intro J μ hAdm hJK n Φ hNpos hlow
  have hAdmE₀ : Adm v E₀ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmθ : Adm v εθ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hAdmp : Adm v εp μ := Work.BoseFixB1.Adm.mono hAdmE₀ hEεp
  have hAdmS : Adm v εS μ := Work.BoseFixB1.Adm.mono hAdmE₀ hEεS
  have hAdmm : Adm v εm μ := Work.BoseFixB1.Adm.mono hAdmE₀ hEεm
  have hAdmR : Adm v εR μ := Work.BoseFixB1.Adm.mono hAdmE₀ hEεR
  have hAdmW : Adm v εW μ := Work.BoseFixB1.Adm.mono hAdmE₀ hEεW
  have hAdmb : Adm v εb μ := Work.BoseFixB1.Adm.mono hAdmE₀ hEεb
  have hAdmg : Adm v εg μ := Work.BoseFixB1.Adm.mono hAdmE₀ hEεg
  have hAdmK : Adm v εK μ := Work.BoseFixB1.Adm.mono hAdmE₀ hEεK
  have hAdmsbw : Adm v εsbw μ := Work.BoseFixB1.Adm.mono hAdmE₀ hEεsbw
  -- ### parameters
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hℓ : 0 < sideAt μ (a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (paramsAt μ (a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hM1 : 1 ≤ (paramsAt μ (a v)).M := Work.BoseFixB1.M_ge_one μ (a v)
  have hdil1 : μ * (a v) ^ 3 ≤ 1 :=
    Work.BoseFixB1.adm_dilute_le_one hAdm (le_trans (min_le_left _ _) (le_trans hEεg hεgle))
  obtain ⟨hpκ, hpKl, hpKB, hpd, hpR, hpV, hpE⟩ :=
    hp μ hμ (le_trans (Work.BoseFixB1.adm_dilute hAdmE₀) hEεg)
  obtain ⟨hRχ, hRd, hM3, ht1, hEpshalf, hKB3, hθ, hcomp⟩ := hreg μ hAdmR
  have hd1 : (paramsAt μ (a v)).d ≤ 1 := hpd
  have hNnn : 0 ≤ normB v μ n (Φ : X n → ℝ) := Work.BoseFixB1.normB_nonneg _
  have hcPnn : 0 ≤ cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) := by
    rw [Submission.BoseGases.cnPlus]
    exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  have hκ' : (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) ≤ 1 := hpκ
  have hJκ : J * Real.sqrt (μ * (a v) ^ 3)
      ≤ (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_right hJK (Real.sqrt_nonneg _)
  -- ### the bounding function `PB` (its three additive pieces, left-associated) and the rows
  let PB1 : E3 → ℝ := fun u =>
    ((1 / 2) * μ ^ 2 * normB v μ n (Φ : X n → ℝ)) * wbMass v h μ u
  let PB2 : E3 → ℝ := fun u =>
    (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
        + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
        * normB v μ n (Φ : X n → ℝ)))
      * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
  let PB3 : E3 → ℝ := fun _ => C * μ * (a v) * normB v μ n (Φ : X n → ℝ)
  let PB : E3 → ℝ := PB1 + PB2 + PB3
  have hpt1 : ∀ u ∈ interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
      c₁ * (wbMass v h μ u * nomBoxInner h μ (Φ : X n → ℝ) u)
        ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) + PB u := by
    intro u hu
    change c₁ * (wbMass v h μ u * nomBoxInner h μ (Φ : X n → ℝ) u)
        ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)
          + (((1 / 2) * μ ^ 2 * normB v μ n (Φ : X n → ℝ)) * wbMass v h μ u
            + (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
                + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
                * normB v μ n (Φ : X n → ℝ)))
                * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
            + C * μ * (a v) * normB v μ n (Φ : X n → ℝ))
    have h1 := hperAll μ hAdmp n Φ u
      (Work.SmallBoxSliding.interiorSet_subset_goodSet hμ hu) μ (Or.inl rfl)
    rw [PerBoxFNom] at h1
    simp only [nomBoxInner, wbMass, nomCnt_eq_boxIndCount, Work.SmallBoxSliding.boxMass] at h1 ⊢
    linarith [h1]
  have hpt2 : ∀ u ∈ goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ
        \ interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
      -(PB u) ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) := by
    intro u hu
    change -(((1 / 2) * μ ^ 2 * normB v μ n (Φ : X n → ℝ)) * wbMass v h μ u
            + (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
                + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
                * normB v μ n (Φ : X n → ℝ)))
                * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
            + C * μ * (a v) * normB v μ n (Φ : X n → ℝ))
        ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)
    have h1 := hperAll μ hAdmp n Φ u hu.1 μ (Or.inl rfl)
    rw [PerBoxFNom] at h1
    simp only [wbMass, nomCnt_eq_boxIndCount] at h1 ⊢
    have hnn : 0 ≤ c₁ * (Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u *
        (∫ x in Submission.BoseGases.abox n (sideAt μ (a v)),
        (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
          (boxIndCount (sideAt μ (a v)) (paramsAt μ (a v)).d u x
            / Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u))) := by
      refine mul_nonneg hc₁.le (mul_nonneg
        (Work.BoseFixB1.wbMass_nonneg hv hvrad hv_supp hR hM1 hℓ hd u) ?_)
      refine integral_nonneg fun x => mul_nonneg (sq_nonneg _) ?_
      rw [Work.SmallBoxSliding.psiWeight]
      refine div_nonneg (mul_nonneg zero_le_one (sq_nonneg _)) ?_
      have hbm : 0 ≤ Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u := by
        rw [Work.SmallBoxSliding.boxMass]
        exact integral_nonneg fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
      have h2 : 0 ≤ boxIndCount (sideAt μ (a v)) (paramsAt μ (a v)).d u x
          / Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u :=
        div_nonneg (boxIndCount_nonneg _ _ _ _) hbm
      have h4 : 0 ≤ (boxIndCount (sideAt μ (a v)) (paramsAt μ (a v)).d u x
          / Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) * μ⁻¹ :=
        mul_nonneg h2 (inv_nonneg.mpr hμ.le)
      linarith
    linarith [h1, hnn]
  -- ### the integral abbreviations
  set 𝕀 : Set E3 := interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ with h𝕀def
  set 𝔾 : Set E3 := goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ with h𝔾def
  set 𝕃 : Set E3 := goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ
      \ interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ with h𝕃def
  set 𝒞 : ℝ := ∫ u in 𝕀, wbMass v h μ u with h𝒞def
  set 𝒞I : ℝ := ∫ u in 𝕀, chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
    with h𝒞Idef
  set VI : ℝ := (volume 𝕀).toReal with hVIdef
  set 𝒞L : ℝ := ∫ u in 𝕃, wbMass v h μ u with h𝒞Ldef
  set 𝒞Lc : ℝ := ∫ u in 𝕃, chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
    with h𝒞Lcdef
  set VL : ℝ := (volume 𝕃).toReal with hVLdef
  set Fb : ℝ := ∫ u in 𝕃, Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u (Φ : X n → ℝ) with hFbdef
  -- ### measurability and integrability
  have h𝕀meas : MeasurableSet 𝕀 := by rw [h𝕀def]; exact Work.SmallBoxSliding.measurableSet_interiorSet _ _ _
  have h𝔾meas : MeasurableSet 𝔾 := by rw [h𝔾def]; exact Work.SmallBoxSliding.measurableSet_goodSet _ _ _
  have h𝕃meas : MeasurableSet 𝕃 := by rw [h𝕃def]; exact h𝔾meas.diff h𝕀meas
  have hLsub : 𝕃 ⊆ (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ := by
    rw [h𝕃def]
    intro u hu
    exact hu.2
  have hLband : 𝕃 ⊆ Work.SmallBoxSliding.bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ := by
    rw [h𝕃def]
    exact Work.SmallBoxSliding.diff_goodSet_interiorSet_subset_bandSet hμ
  have hIgood : 𝕀 ⊆ 𝔾 := by
    rw [h𝕀def, h𝔾def]
    exact Work.SmallBoxSliding.interiorSet_subset_goodSet hμ
  have h𝕀sub : 𝕀 ⊆ Submission.BoseGases.acube ((1 + (paramsAt μ (a v)).d)
      / (paramsAt μ (a v)).d) := by
    rw [h𝕀def]
    intro u hu
    rw [Work.SmallBoxSliding.mem_interiorSet_iff] at hu
    rw [Submission.BoseGases.mem_acube_iff]
    intro j
    have h1 := hu j
    have hℓd : 0 < sideAt μ (a v) * (paramsAt μ (a v)).d := mul_pos hℓ hd
    rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hℓd] at h1
    have h2 : |u.ofLp j| ≤ (1 / 2 * sideAt μ (a v) * (1 + (paramsAt μ (a v)).d))
        / (sideAt μ (a v) * (paramsAt μ (a v)).d) := by
      rw [le_div_iff₀ hℓd]
      nlinarith [h1, (by positivity : (0 : ℝ) ≤ 2 * μ ^ (-(1 / 3) : ℝ))]
    have h3 : (1 / 2 * sideAt μ (a v) * (1 + (paramsAt μ (a v)).d))
        / (sideAt μ (a v) * (paramsAt μ (a v)).d)
        = ((1 + (paramsAt μ (a v)).d) / (paramsAt μ (a v)).d) / 2 := by
      field_simp
    rw [h3] at h2
    have h4 := abs_le.mp h2
    rw [Set.mem_Icc]
    constructor <;> linarith [h4.1, h4.2]
  have h𝕀fin : (volume : Measure E3) 𝕀 ≠ ⊤ := by
    have hcube : (volume : Measure E3) (Submission.BoseGases.acube ((1 + (paramsAt μ (a v)).d)
        / (paramsAt μ (a v)).d)) < ⊤ := by
      rw [Submission.BoseGases.acube_volume _ (by positivity)]
      exact ENNReal.ofReal_lt_top
    exact ne_of_lt (lt_of_le_of_lt (measure_mono h𝕀sub) hcube)
  have h𝕃fin : (volume : Measure E3) 𝕃 ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono hLband) (bandSet_volume_lt_top hℓ hd))
  have haesm_g : AEStronglyMeasurable (fun u : E3 => wbMass v h μ u) volume :=
    Work.BoseFixB1.WB.w1MassB_aeStronglyMeasurable_local hR hv_supp (paramsAt μ (a v)).M hM1
      (sideAt μ (a v)) (paramsAt μ (a v)).d
  have hmassU' : ∀ u : E3, wbMass v h μ u
      ≤ max Cm 1 * (a v) * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u := by
    intro u
    have hm := hmassm μ hAdmm u
    have h2 : Cm * (a v) ≤ max Cm 1 * (a v) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hav.le
    exact le_trans hm (mul_le_mul_of_nonneg_right h2 (Work.SmallBoxSliding.chiMass_nonneg _ _ _ _))
  have hmassL' : ∀ u : E3, 0 ≤ wbMass v h μ u :=
    fun u => Work.BoseFixB1.wbMass_nonneg hv hvrad hv_supp hR hM1 hℓ hd u
  have hIntWvol : Integrable (fun u : E3 => wbMass v h μ u) volume :=
    Work.BoseFixB1.WB.integrable_w1MassB haesm_g hM1 hℓ hd hmassL' hmassU'
  have hIntW𝕀 : IntegrableOn (fun u : E3 => wbMass v h μ u) 𝕀 := hIntWvol.integrableOn
  have hIntW𝕃 : IntegrableOn (fun u : E3 => wbMass v h μ u) 𝕃 := hIntWvol.integrableOn
  have hIntChvol : Integrable (fun u : E3 =>
      chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) volume :=
    Work.SmallBoxSliding.integrable_chiSmallB_mass hM1 hℓ hd
  have hIntCh𝕀 : IntegrableOn (fun u : E3 =>
      chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) 𝕀 := hIntChvol.integrableOn
  have hIntCh𝕃 : IntegrableOn (fun u : E3 =>
      chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) 𝕃 := hIntChvol.integrableOn
  have hIntSW𝕀 : IntegrableOn (fun u => Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)) 𝕀 :=
    ((hsbwInt μ hAdmsbw Φ)).integrableOn
  have hIntSW𝕃 : IntegrableOn (fun u => Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)) 𝕃 :=
    ((hsbwInt μ hAdmsbw Φ)).integrableOn
  have hIntFib𝕃 : IntegrableOn (fun u => Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M
      (sideAt μ (a v)) (paramsAt μ (a v)).d u (Φ : X n → ℝ)) 𝕃 := by
    refine Integrable.mono' (MeasureTheory.integrableOn_const (C := Work.BoseFixB1.bandK v h
      (paramsAt μ (a v)).M * Work.BoseFixB1.bandS (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d μ ^ 2 * (n : ℝ) * normB v μ n (Φ : X n → ℝ))) ?_ ?_
    · exact (aestronglyMeasurable_fibSum h hR hv_supp hM1 (Φ : X n → ℝ)
        Φ.contDiff.continuous.measurable).mono_measure Measure.restrict_le_self
    · filter_upwards [MeasureTheory.self_mem_ae_restrict h𝕃meas] with u hu
      have hfnn : 0 ≤ Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v))
          (paramsAt μ (a v)).d u (Φ : X n → ℝ) :=
        fibSum_nonneg (v := v) h hv hvrad hR hv_supp (M := (paramsAt μ (a v)).M) hM1
          (ℓ := sideAt μ (a v)) (d := (paramsAt μ (a v)).d) (μ := μ) hℓ hd u (Φ : X n → ℝ)
      rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
      exact fibSum_le_bandS_sq_atParams (v := v) h hv hvrad hR hv_supp hμ hav hM1 hℓ hd hRd hRχ
        (hLband hu) Φ
  -- ### the three integrability pieces of `PB`
  have hPB1int𝕀 : IntegrableOn PB1 𝕀 := by
    change IntegrableOn (fun u : E3 =>
      ((1 / 2) * μ ^ 2 * normB v μ n (Φ : X n → ℝ)) * wbMass v h μ u) 𝕀
    exact hIntW𝕀.const_mul _
  have hPB2int𝕀 : IntegrableOn PB2 𝕀 := by
    change IntegrableOn (fun u : E3 =>
      (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
          + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          * normB v μ n (Φ : X n → ℝ)))
        * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) 𝕀
    exact hIntCh𝕀.const_mul _
  have hPB3int𝕀 : IntegrableOn PB3 𝕀 := by
    change IntegrableOn (fun _ : E3 => C * μ * (a v) * normB v μ n (Φ : X n → ℝ)) 𝕀
    exact MeasureTheory.integrableOn_const (s := 𝕀) (C := C * μ * (a v)
      * normB v μ n (Φ : X n → ℝ)) (by simpa using h𝕀fin)
  have hB1int𝕀 : IntegrableOn PB 𝕀 := (hPB1int𝕀.add hPB2int𝕀).add hPB3int𝕀
  have hPB1int𝕃 : IntegrableOn PB1 𝕃 := by
    change IntegrableOn (fun u : E3 =>
      ((1 / 2) * μ ^ 2 * normB v μ n (Φ : X n → ℝ)) * wbMass v h μ u) 𝕃
    exact hIntW𝕃.const_mul _
  have hPB2int𝕃 : IntegrableOn PB2 𝕃 := by
    change IntegrableOn (fun u : E3 =>
      (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
          + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          * normB v μ n (Φ : X n → ℝ)))
        * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) 𝕃
    exact hIntCh𝕃.const_mul _
  have hPB3int𝕃 : IntegrableOn PB3 𝕃 := by
    change IntegrableOn (fun _ : E3 => C * μ * (a v) * normB v μ n (Φ : X n → ℝ)) 𝕃
    exact MeasureTheory.integrableOn_const (s := 𝕃) (C := C * μ * (a v)
      * normB v μ n (Φ : X n → ℝ)) (by simpa using h𝕃fin)
  have hB2int𝕃 : IntegrableOn PB 𝕃 := (hPB1int𝕃.add hPB2int𝕃).add hPB3int𝕃
  -- ### the slot identities
  have hslot𝕀 : Set.EqOn (fun u => sbWordSlot v h (if u ∈ 𝕀 then μ else 4 * μ) μ u (Φ : X n → ℝ))
      (fun u => Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)) 𝕀 := by
    intro u hu
    simp only []
    rw [if_pos hu]
    exact sbWordSlot_self h hv hv1 hvrad hR hv_supp hAdmE₀ Φ hRd hRχ
  have hslot𝕃 : Set.EqOn (fun u => sbWordSlot v h (if u ∈ 𝕀 then μ else 4 * μ) μ u (Φ : X n → ℝ))
      (fun u => Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)
        - 3 * μ * Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u (Φ : X n → ℝ)) 𝕃 := by
    intro u hu
    simp only []
    rw [if_neg (fun hx => hu.2 hx), sbWordSlot_eq_sub,
      sbWordSlot_self h hv hv1 hvrad hR hv_supp hAdmE₀ Φ hRd hRχ]
    ring
  have hIntSWS𝕀 : IntegrableOn (fun u => sbWordSlot v h (if u ∈ 𝕀 then μ else 4 * μ) μ u
      (Φ : X n → ℝ)) 𝕀 :=
    hIntSW𝕀.congr_fun (fun u hu => (hslot𝕀 (x := u) hu).symm) h𝕀meas
  have hIntSWS𝕃 : IntegrableOn (fun u => sbWordSlot v h (if u ∈ 𝕀 then μ else 4 * μ) μ u
      (Φ : X n → ℝ)) 𝕃 :=
    (hIntSW𝕃.sub (hIntFib𝕃.const_mul (3 * μ))).congr_fun
      (fun u hu => (hslot𝕃 (x := u) hu).symm) h𝕃meas
  -- ### the `I₋` row, integrated
  have hId : c₁ * (∫ u in 𝕀, wbMass v h μ u * nomBoxInner h μ (Φ : X n → ℝ) u)
      = ∫ u in 𝕀, c₁ * (wbMass v h μ u * nomBoxInner h μ (Φ : X n → ℝ) u) :=
    (MeasureTheory.integral_const_mul c₁
      (fun u => wbMass v h μ u * nomBoxInner h μ (Φ : X n → ℝ) u)).symm
  have hI1 : (∫ u in 𝕀, c₁ * (wbMass v h μ u * nomBoxInner h μ (Φ : X n → ℝ) u))
      ≤ ∫ u in 𝕀, (Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)) + PB u := by
    refine MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict 𝕀)
      (f := fun u => c₁ * (wbMass v h μ u * nomBoxInner h μ (Φ : X n → ℝ) u)) ?_ ?_ ?_
    · filter_upwards [MeasureTheory.self_mem_ae_restrict h𝕀meas] with u _
      exact mul_nonneg hc₁.le (mul_nonneg (hmassL' u) (nomBoxInner_nonneg hμ (Φ : X n → ℝ) u))
    · have hsum : Integrable (fun u : E3 =>
          Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) + PB u) (volume.restrict 𝕀) :=
        hIntSW𝕀.add hB1int𝕀
      exact hsum
    · filter_upwards [MeasureTheory.self_mem_ae_restrict h𝕀meas] with u hu
      exact hpt1 u hu
  have hI2 : (∫ u in 𝕀, (Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)) + PB u)
      = (∫ u in 𝕀, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)) + ∫ u in 𝕀, PB u :=
    MeasureTheory.integral_add hIntSW𝕀 hB1int𝕀
  have hI3 : (∫ u in 𝕀, PB u)
      = (∫ u in 𝕀, (PB1 + PB2) u) + ∫ u in 𝕀, PB3 u :=
    MeasureTheory.integral_add (hPB1int𝕀.add hPB2int𝕀) hPB3int𝕀
  have hI4 : (∫ u in 𝕀, (PB1 + PB2) u) = (∫ u in 𝕀, PB1 u) + ∫ u in 𝕀, PB2 u :=
    MeasureTheory.integral_add hPB1int𝕀 hPB2int𝕀
  have hV1 : (∫ u in 𝕀, PB1 u) = ((1 / 2) * μ ^ 2 * normB v μ n (Φ : X n → ℝ)) * 𝒞 := by
    change (∫ u in 𝕀, ((1 / 2) * μ ^ 2 * normB v μ n (Φ : X n → ℝ)) * wbMass v h μ u)
      = ((1 / 2) * μ ^ 2 * normB v μ n (Φ : X n → ℝ)) * 𝒞
    rw [MeasureTheory.integral_const_mul, ← h𝒞def]
  have hV2 : (∫ u in 𝕀, PB2 u)
      = (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
          + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          * normB v μ n (Φ : X n → ℝ))) * 𝒞I := by
    change (∫ u in 𝕀, (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
          + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          * normB v μ n (Φ : X n → ℝ)))
          * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) = _
    rw [MeasureTheory.integral_const_mul, ← h𝒞Idef]
  have hV3 : (∫ u in 𝕀, PB3 u) = C * μ * (a v) * normB v μ n (Φ : X n → ℝ) * VI := by
    change (∫ _ in 𝕀, C * μ * (a v) * normB v μ n (Φ : X n → ℝ)) = _
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def, ← hVIdef]
    ring
  have hIrow0 : c₁ * (∫ u in 𝕀, wbMass v h μ u * nomBoxInner h μ (Φ : X n → ℝ) u)
      ≤ (∫ u in 𝕀, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
        + ((1 / 2) * μ ^ 2 * 𝒞 * normB v μ n (Φ : X n → ℝ)
          + (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
                + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
                * normB v μ n (Φ : X n → ℝ))) * 𝒞I
          + C * μ * (a v) * normB v μ n (Φ : X n → ℝ) * VI) := by
    set_option maxRecDepth 4000 in
    linarith [hId, hI1, hI2, hI3, hI4, hV1, hV2, hV3]
  have hIrow : c₁ * nomRPsi h μ (Φ : X n → ℝ)
      ≤ (∫ u in 𝕀, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
        + ((1 / 2) * μ ^ 2 * 𝒞 * normB v μ n (Φ : X n → ℝ)
          + (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
                + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
                * normB v μ n (Φ : X n → ℝ))) * 𝒞I
          + C * μ * (a v) * normB v μ n (Φ : X n → ℝ) * VI) := by
    rw [nomRPsi]
    exact hIrow0
  -- ### the layer row, integrated
  have hL1 : (∫ u in 𝕃, -(PB u))
      ≤ ∫ u in 𝕃, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) := by
    refine MeasureTheory.integral_mono_ae (μ := volume.restrict 𝕃)
      (f := fun u : E3 => -(PB u))
      (g := fun u : E3 => Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
      hB2int𝕃.neg hIntSW𝕃 ?_
    · filter_upwards [MeasureTheory.self_mem_ae_restrict h𝕃meas] with u hu
      exact hpt2 u (by rw [h𝕃def] at hu; exact hu)
  have hL2 : (∫ u in 𝕃, -(PB u)) = -(∫ u in 𝕃, PB u) :=
    MeasureTheory.integral_neg (f := PB) (μ := volume.restrict 𝕃)
  have hJ3 : (∫ u in 𝕃, PB u)
      = (∫ u in 𝕃, (PB1 + PB2) u) + ∫ u in 𝕃, PB3 u :=
    MeasureTheory.integral_add (hPB1int𝕃.add hPB2int𝕃) hPB3int𝕃
  have hJ4 : (∫ u in 𝕃, (PB1 + PB2) u) = (∫ u in 𝕃, PB1 u) + ∫ u in 𝕃, PB2 u :=
    MeasureTheory.integral_add hPB1int𝕃 hPB2int𝕃
  have hW1 : (∫ u in 𝕃, PB1 u) = ((1 / 2) * μ ^ 2 * normB v μ n (Φ : X n → ℝ)) * 𝒞L := by
    change (∫ u in 𝕃, ((1 / 2) * μ ^ 2 * normB v μ n (Φ : X n → ℝ)) * wbMass v h μ u)
      = ((1 / 2) * μ ^ 2 * normB v μ n (Φ : X n → ℝ)) * 𝒞L
    rw [MeasureTheory.integral_const_mul, ← h𝒞Ldef]
  have hW2 : (∫ u in 𝕃, PB2 u)
      = (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
          + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          * normB v μ n (Φ : X n → ℝ))) * 𝒞Lc := by
    change (∫ u in 𝕃, (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
          + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          * normB v μ n (Φ : X n → ℝ)))
          * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) = _
    rw [MeasureTheory.integral_const_mul, ← h𝒞Lcdef]
  have hW3 : (∫ u in 𝕃, PB3 u) = C * μ * (a v) * normB v μ n (Φ : X n → ℝ) * VL := by
    change (∫ _ in 𝕃, C * μ * (a v) * normB v μ n (Φ : X n → ℝ)) = _
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def, ← hVLdef]
    ring
  have hLrow : -((1 / 2) * μ ^ 2 * 𝒞L * normB v μ n (Φ : X n → ℝ)
          + (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
                + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
                * normB v μ n (Φ : X n → ℝ))) * 𝒞Lc
          + C * μ * (a v) * normB v μ n (Φ : X n → ℝ) * VL)
      ≤ ∫ u in 𝕃, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) := by
    set_option maxRecDepth 4000 in
    linarith [hL1, hL2, hJ3, hJ4, hW1, hW2, hW3]
  -- ### the localisation
  have hwordB_le : wordB v h μ n (Φ : X n → ℝ)
      ≤ -(4 * Real.pi * μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
          * (1 - J * Real.sqrt (μ * (a v) ^ 3))) * normB v μ n (Φ : X n → ℝ) :=
    (Work.BoseFixB1.isLowB_iff hav).mp hlow
  have hwordB_nonpos : wordB v h μ n (Φ : X n → ℝ) ≤ 0 := by
    have hJ1 : J * Real.sqrt (μ * (a v) ^ 3) ≤ 1 := le_trans hJκ hκ'
    have hfac : 0 ≤ 4 * Real.pi * μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
        * (1 - J * Real.sqrt (μ * (a v) ^ 3)) := by
      have h1 : 0 ≤ 4 * Real.pi * μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 := by positivity
      have h2 : 0 ≤ 1 - J * Real.sqrt (μ * (a v) ^ 3) := by linarith
      exact mul_nonneg h1 h2
    nlinarith [hwordB_le, hfac, hNnn]
  have hCSpos : 0 < CS := lt_of_lt_of_le one_pos hCS1
  have hGbound : (∫ u in 𝔾, sbWordSlot v h (if u ∈ 𝕀 then μ else 4 * μ) μ u (Φ : X n → ℝ))
      ≤ CS * wordB v h μ n (Φ : X n → ℝ) := by
    have hSG := hSfun μ hAdmS n Φ
    rw [h𝔾def, h𝕀def]
    have h2 : (1 / CS) * (∫ u in goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
          sbWordSlot v h (if u ∈ interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ then μ else 4 * μ)
            μ u (Φ : X n → ℝ))
        ≤ wordB v h μ n (Φ : X n → ℝ)
          - ((paramsAt μ (a v)).b / (2 * (sideAt μ (a v)) ^ 2))
              * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) := by
      linarith [hSG]
    have h3 := mul_le_mul_of_nonneg_left h2 (le_of_lt hCSpos)
    have h4 : CS * ((1 / CS) * (∫ u in 𝔾, sbWordSlot v h (if u ∈ 𝕀 then μ else 4 * μ) μ u
        (Φ : X n → ℝ)))
        = ∫ u in 𝔾, sbWordSlot v h (if u ∈ 𝕀 then μ else 4 * μ) μ u (Φ : X n → ℝ) := by
      rw [← mul_assoc, mul_one_div_cancel (ne_of_gt hCSpos), one_mul]
    have h5 : 0 ≤ ((paramsAt μ (a v)).b / (2 * (sideAt μ (a v)) ^ 2))
        * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) := by
      refine mul_nonneg (div_nonneg ?_ (by positivity)) hcPnn
      have := Work.BoseFixB1.paramsAt_b_pos μ (a v)
      linarith [this]
    have h6 : CS * (wordB v h μ n (Φ : X n → ℝ)
          - ((paramsAt μ (a v)).b / (2 * (sideAt μ (a v)) ^ 2)) * cnPlus (sideAt μ (a v))
              (Φ : X n → ℝ))
        ≤ CS * wordB v h μ n (Φ : X n → ℝ) := by
      nlinarith [h5, hCSpos]
    linarith [h3, h4, h6]
  -- ### the splitting
  have hunion : 𝕀 ∪ 𝕃 = 𝔾 := by
    rw [h𝕀def, h𝕃def, h𝔾def]
    exact Set.union_sdiff_cancel
      (fun u hu => Work.SmallBoxSliding.interiorSet_subset_goodSet hμ hu)
  have hdisj : Disjoint 𝕀 𝕃 := by
    rw [h𝕀def, h𝕃def, Set.disjoint_left]
    intro u hu h2
    exact h2.2 hu
  have hsplitSW : (∫ u in 𝔾, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
      = (∫ u in 𝕀, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
        + ∫ u in 𝕃, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) := by
    rw [← hunion]
    exact MeasureTheory.setIntegral_union hdisj h𝕃meas hIntSW𝕀 hIntSW𝕃
  have hIsws : (∫ u in 𝕀, sbWordSlot v h (if u ∈ 𝕀 then μ else 4 * μ) μ u (Φ : X n → ℝ))
      = (∫ u in 𝕀, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)) :=
    MeasureTheory.setIntegral_congr_fun h𝕀meas (fun u hu => hslot𝕀 (x := u) hu)
  have hLsws : (∫ u in 𝕃, sbWordSlot v h (if u ∈ 𝕀 then μ else 4 * μ) μ u (Φ : X n → ℝ))
      = (∫ u in 𝕃, (Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)
          - 3 * μ * Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u (Φ : X n → ℝ))) :=
    MeasureTheory.setIntegral_congr_fun h𝕃meas (fun u hu => hslot𝕃 (x := u) hu)
  have hLsubI : (∫ u in 𝕃, (Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)
          - 3 * μ * Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u (Φ : X n → ℝ)))
      = (∫ u in 𝕃, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)) - 3 * μ * Fb := by
    rw [MeasureTheory.integral_sub hIntSW𝕃 (hIntFib𝕃.const_mul (3 * μ)),
      MeasureTheory.integral_const_mul, hFbdef]
  have hsplitSWS' : (∫ u in 𝔾, sbWordSlot v h (if u ∈ 𝕀 then μ else 4 * μ) μ u (Φ : X n → ℝ))
      = (∫ u in 𝕀, sbWordSlot v h (if u ∈ 𝕀 then μ else 4 * μ) μ u (Φ : X n → ℝ))
        + ∫ u in 𝕃, sbWordSlot v h (if u ∈ 𝕀 then μ else 4 * μ) μ u (Φ : X n → ℝ) := by
    rw [← hunion]
    exact MeasureTheory.setIntegral_union hdisj h𝕃meas hIntSWS𝕀 hIntSWS𝕃
  have hsplitSWS : (∫ u in 𝔾, sbWordSlot v h (if u ∈ 𝕀 then μ else 4 * μ) μ u (Φ : X n → ℝ))
      = (∫ u in 𝔾, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)) - 3 * μ * Fb := by
    rw [hsplitSWS', hIsws, hLsws, hLsubI, hsplitSW]
    ring
  -- ### the numeric bounds
  have hκnn : 0 ≤ (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) := by
    refine mul_nonneg (pow_nonneg (le_of_lt (Work.BoseFixB1.paramsAt_KB_pos hAdm)) 3) ?_
    exact Real.rpow_nonneg (le_of_lt (mul_pos hμ (pow_pos hav 3))) _
  have h𝒞_le : 𝒞 ≤ 8 * Real.pi * (a v) * (sideAt μ (a v)) ^ 3
      * (1 + CW * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) := by
    rw [h𝒞def]
    exact hWup μ hAdmW
  have h𝒞L_le : 𝒞L ≤ Cm * (a v) * 𝒞Lc := by
    have h1 : (∫ u in 𝕃, wbMass v h μ u) ≤ ∫ u in 𝕃, Cm * (a v)
        * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u :=
      MeasureTheory.integral_mono hIntW𝕃 (hIntCh𝕃.const_mul (Cm * (a v)))
        (fun u => hmassm μ hAdmm u)
    rw [MeasureTheory.integral_const_mul] at h1
    exact h1
  have h𝒞I_le : 𝒞I ≤ (sideAt μ (a v)) ^ 3 := by
    have h1 : (∫ u in 𝕀, chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)
        ≤ ∫ u : E3, chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u := by
      have h2 := MeasureTheory.setIntegral_mono_set (s := 𝕀) (t := Set.univ)
        hIntChvol.integrableOn
        (by filter_upwards with u; exact Work.SmallBoxSliding.chiMass_nonneg _ _ _ _)
        (by filter_upwards with u _; exact Set.mem_univ u)
      simpa using h2
    have h3 : (∫ u : E3, chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)
        = (sideAt μ (a v)) ^ 3 := Work.SmallBoxSliding.integral_chiMass_eq hM1 hℓ hd
    rw [h𝒞Idef]
    rw [h3] at h1
    exact h1
  have hK2eq : (2 : ℝ) ^ (2 * (paramsAt μ (a v)).M) = (2 : ℝ) ^ 96 := by
    rw [Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  have h𝒞Lc_le : 𝒞Lc ≤ (2 : ℝ) ^ 96 * Kb
      * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) * (sideAt μ (a v)) ^ 3 := by
    have hθd : εθ ≤ (1 / 4 : ℝ) ^ (969 / 166 : ℝ) := by
      rw [hεθdef]; exact min_le_left _ _
    have hAδ : 0 ≤ (1 / 2) * (sideAt μ (a v)) * (1 + (paramsAt μ (a v)).d) - 2 * μ ^ (-1 / 3 : ℝ) := by
      simpa only [neg_div] using
        (Work.BoseFixB1.ell_residual_nonneg_fb hav hμ
          (le_trans (Work.BoseFixB1.adm_dilute hAdmθ) hθd))
    have hpE' : (2 * μ ^ (-1 / 3 : ℝ) / sideAt μ (a v)) ^ (2 * (paramsAt μ (a v)).M)
        * μ ^ (-1 / 3 : ℝ) * (sideAt μ (a v)) ^ 2
        ≤ (2 : ℝ) ^ 96 * (μ * (a v) ^ 3) ^ (((paramsAt μ (a v)).M : ℕ) / 3 : ℝ)
          * (sideAt μ (a v)) ^ 3 := by
      rw [← hK2eq]
      simpa only [neg_div] using hpE
    have hlaw := Work.BoseFixB1.WB.interior_compl_mass_le
      (M := (paramsAt μ (a v)).M) (ℓ := sideAt μ (a v)) (d := (paramsAt μ (a v)).d) (μ := μ)
      (a := a v) (C₁ := (2 : ℝ) ^ 96)
      hM1 hℓ hd hμ hav.le (by norm_num) hAδ hpE'
    have hb := hbsharp μ hμ (Work.BoseFixB1.adm_dilute hAdmb)
    have hmono : 𝒞Lc ≤ ∫ u in (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ,
        chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u := by
      rw [h𝒞Lcdef]
      exact setIntegral_mono_of_subset hLsub h𝕃meas h𝕀meas.compl hIntChvol
        (fun u => Work.SmallBoxSliding.chiMass_nonneg _ _ _ _)
    calc 𝒞Lc ≤ ∫ u in (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ,
            chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u := hmono
      _ ≤ 12 * (1 + (paramsAt μ (a v)).d) ^ 2
            * Submission.BoseGases.chiSmallBandDecay (paramsAt μ (a v)).M (paramsAt μ (a v)).d
            * (2 : ℝ) ^ 96
            * (μ * (a v) ^ 3) ^ (((paramsAt μ (a v)).M : ℕ) / 3 : ℝ)
            * (sideAt μ (a v)) ^ 3 := hlaw
      _ = (12 * (1 + (paramsAt μ (a v)).d) ^ 2
            * Submission.BoseGases.chiSmallBandDecay (paramsAt μ (a v)).M (paramsAt μ (a v)).d
            * (μ * (a v) ^ 3) ^ (((paramsAt μ (a v)).M : ℕ) / 3 : ℝ))
            * (2 : ℝ) ^ 96 * (sideAt μ (a v)) ^ 3 := by ring
      _ ≤ (Kb * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
            * (2 : ℝ) ^ 96 * (sideAt μ (a v)) ^ 3 := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb ?_) ?_
          · positivity
          · positivity
      _ = (2 : ℝ) ^ 96 * Kb * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
            * (sideAt μ (a v)) ^ 3 := by ring
  have hVI_le : VI ≤ 8 * (μ * (sideAt μ (a v)) ^ 3
      * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))) := by
    rw [hVIdef]
    exact le_trans (Work.BoseB1Cube.volume_interiorSet_bandSet_le hℓ hμ hd hd1).1 hpV
  have hVL_le : VL ≤ 8 * (μ * (sideAt μ (a v)) ^ 3
      * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))) := by
    rw [hVLdef]
    refine le_trans (ENNReal.toReal_mono (ne_of_lt (bandSet_volume_lt_top hℓ hd))
      (measure_mono hLband)) ?_
    exact (Work.BoseB1Cube.volume_interiorSet_bandSet_le hℓ hμ hd hd1).2.trans hpV
  have hFb_le : Fb ≤ CrudePlan.bandErr v h μ * (n : ℝ) * normB v μ n (Φ : X n → ℝ) := by
    have hpt : ∀ u ∈ 𝕃, Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u (Φ : X n → ℝ)
        ≤ Work.BoseFixB1.bandK v h (paramsAt μ (a v)).M
            * Work.BoseFixB1.bandS (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d μ ^ 2 * (n : ℝ) * normB v μ n (Φ : X n → ℝ) :=
      fun u hu => fibSum_le_bandS_sq_atParams h hv hvrad hR hv_supp hμ hav hM1 hℓ hd hRd hRχ
        (hLband hu) Φ
    have hint : IntegrableOn (fun u : E3 => Work.BoseFixB1.bandK v h (paramsAt μ (a v)).M
        * Work.BoseFixB1.bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2
        * (n : ℝ) * normB v μ n (Φ : X n → ℝ)) 𝕃 := MeasureTheory.integrableOn_const
    have hmain := MeasureTheory.integral_mono_ae hIntFib𝕃 hint
      (by
        filter_upwards [MeasureTheory.self_mem_ae_restrict h𝕃meas] with u hu
        exact hpt u hu)
    rw [MeasureTheory.setIntegral_const, smul_eq_mul] at hmain
    have hVL' : VL ≤ (volume (Work.SmallBoxSliding.bandSet (sideAt μ (a v))
        (paramsAt μ (a v)).d μ)).toReal := by
      rw [hVLdef]
      exact ENNReal.toReal_mono (ne_of_lt (bandSet_volume_lt_top hℓ hd)) (measure_mono hLband)
    have hbandnn : 0 ≤ Work.BoseFixB1.bandK v h (paramsAt μ (a v)).M
        * Work.BoseFixB1.bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2
        * (n : ℝ) * normB v μ n (Φ : X n → ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (Work.BoseFixB1.bandK_nonneg _) (sq_nonneg _))
        (Nat.cast_nonneg n)) hNnn
    rw [hFbdef]
    refine le_trans hmain ?_
    have hVL'' : volume.real 𝕃 ≤ (volume (Work.SmallBoxSliding.bandSet (sideAt μ (a v))
        (paramsAt μ (a v)).d μ)).toReal := by
      rw [MeasureTheory.measureReal_def]
      exact hVL'
    have hgoal : volume.real 𝕃 * (Work.BoseFixB1.bandK v h (paramsAt μ (a v)).M
          * Work.BoseFixB1.bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2
          * (n : ℝ) * normB v μ n (Φ : X n → ℝ))
        ≤ CrudePlan.bandErr v h μ * (n : ℝ) * normB v μ n (Φ : X n → ℝ) := by
      have hj1 : volume.real 𝕃 * (Work.BoseFixB1.bandK v h (paramsAt μ (a v)).M
            * Work.BoseFixB1.bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2
            * (n : ℝ) * normB v μ n (Φ : X n → ℝ))
          ≤ (volume (Work.SmallBoxSliding.bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)).toReal
            * (Work.BoseFixB1.bandK v h (paramsAt μ (a v)).M
            * Work.BoseFixB1.bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2
            * (n : ℝ) * normB v μ n (Φ : X n → ℝ)) :=
        mul_le_mul_of_nonneg_right hVL'' hbandnn
      have hj2 : (volume (Work.SmallBoxSliding.bandSet (sideAt μ (a v))
              (paramsAt μ (a v)).d μ)).toReal
            * (Work.BoseFixB1.bandK v h (paramsAt μ (a v)).M
            * Work.BoseFixB1.bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2
            * (n : ℝ) * normB v μ n (Φ : X n → ℝ))
          = CrudePlan.bandErr v h μ * (n : ℝ) * normB v μ n (Φ : X n → ℝ) := by
        rw [CrudePlan.bandErr]; ring
      linarith [hj1, hj2]
    exact hgoal
  have hFb_pay : 3 * μ * Fb ≤ E * (μ * (a v)
      * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))) * (n : ℝ)
      * normB v μ n (Φ : X n → ℝ) := by
    have hk := (hKerr μ hAdmK).1
    have h3 : 3 * CrudePlan.bandErr v h μ
        ≤ E * ((a v) * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))) := by
      have hkE := mul_le_mul_of_nonneg_left hk hE.le
      have he : E * (3 / E * CrudePlan.bandErr v h μ) = 3 * CrudePlan.bandErr v h μ := by
        field_simp
      linarith [hkE, he.symm.le, he.le]
    have hnn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have h1 : 3 * CrudePlan.bandErr v h μ * (μ * (n : ℝ) * normB v μ n (Φ : X n → ℝ))
        ≤ (E * ((a v) * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))))
          * (μ * (n : ℝ) * normB v μ n (Φ : X n → ℝ)) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    have h2 : 3 * μ * Fb ≤ 3 * CrudePlan.bandErr v h μ
        * (μ * (n : ℝ) * normB v μ n (Φ : X n → ℝ)) := by
      have h := mul_le_mul_of_nonneg_left hFb_le (by positivity : (0 : ℝ) ≤ 3 * μ)
      nlinarith [h]
    nlinarith [h1, h2]
  have hΓ_le : (R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
      + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)
      ≤ 2 * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) := by
    nlinarith [hpR, hκnn, sq_nonneg (R / (sideAt μ (a v) * (paramsAt μ (a v)).d))]
  have hΓnn : 0 ≤ (R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
      + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) := by
    nlinarith [hκnn, sq_nonneg (R / (sideAt μ (a v) * (paramsAt μ (a v)).d))]
  -- ### nonnegativity of the auxiliary integrals
  have h𝒞nn : 0 ≤ 𝒞 := by
    rw [h𝒞def]
    exact integral_nonneg fun u => hmassL' u
  have h𝒞Inn : 0 ≤ 𝒞I := by
    rw [h𝒞Idef]
    exact integral_nonneg fun u => Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hVInn : 0 ≤ VI := by rw [hVIdef]; exact ENNReal.toReal_nonneg
  have h𝒞Lnn : 0 ≤ 𝒞L := by
    rw [h𝒞Ldef]
    exact integral_nonneg fun u => hmassL' u
  have h𝒞Lcnn : 0 ≤ 𝒞Lc := by
    rw [h𝒞Lcdef]
    exact integral_nonneg fun u => Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hVLnn : 0 ≤ VL := by rw [hVLdef]; exact ENNReal.toReal_nonneg
  have hFbnn : 0 ≤ Fb := by
    rw [hFbdef]
    exact integral_nonneg fun u => fibSum_nonneg (v := v) h hv hvrad hR hv_supp
      (M := (paramsAt μ (a v)).M) hM1 (ℓ := sideAt μ (a v)) (d := (paramsAt μ (a v)).d)
      (μ := μ) hℓ hd u (Φ : X n → ℝ)
  -- ### the assembly
  have key1 : (∫ u in 𝕀, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
      ≤ CS * wordB v h μ n (Φ : X n → ℝ) + 3 * μ * Fb
        + ((1 / 2) * μ ^ 2 * 𝒞L * normB v μ n (Φ : X n → ℝ)
          + (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
                + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
                * normB v μ n (Φ : X n → ℝ))) * 𝒞Lc
          + C * μ * (a v) * normB v μ n (Φ : X n → ℝ) * VL) := by
    have h2 : (∫ u in 𝕀, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
        = (∫ u in 𝔾, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
          - ∫ u in 𝕃, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) := by
      linarith [hsplitSW]
    have h3 : (∫ u in 𝔾, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
        = (∫ u in 𝔾, sbWordSlot v h (if u ∈ 𝕀 then μ else 4 * μ) μ u (Φ : X n → ℝ))
          + 3 * μ * Fb := by
      linarith [hsplitSWS]
    set_option maxRecDepth 4000 in
    linarith [h2, h3, hGbound, hLrow]
  -- ### the cancellation of the `A`-scale background against the low-state energy
  have hcancel : -(4 * Real.pi * μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
            * (1 - J * Real.sqrt (μ * (a v) ^ 3))) * normB v μ n (Φ : X n → ℝ)
          + (1 / 2) * μ ^ 2 * 𝒞 * normB v μ n (Φ : X n → ℝ)
        ≤ 4 * Real.pi * (1 + CW)
            * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
                * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
            * normB v μ n (Φ : X n → ℝ) := by
    have h𝔇'nn : (0 : ℝ) ≤ 4 * Real.pi * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3)
        * normB v μ n (Φ : X n → ℝ) := by positivity
    have h1 : (1 / 2) * μ ^ 2 * 𝒞 * normB v μ n (Φ : X n → ℝ)
        ≤ 4 * Real.pi * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3)
            * normB v μ n (Φ : X n → ℝ)
            * (1 + CW * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))) := by
      calc (1 / 2) * μ ^ 2 * 𝒞 * normB v μ n (Φ : X n → ℝ)
          = ((1 / 2) * μ ^ 2 * normB v μ n (Φ : X n → ℝ)) * 𝒞 := by ring
        _ ≤ ((1 / 2) * μ ^ 2 * normB v μ n (Φ : X n → ℝ))
              * (8 * Real.pi * (a v) * (sideAt μ (a v)) ^ 3
                * (1 + CW * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left h𝒞_le
              (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg μ)) hNnn)
        _ = 4 * Real.pi * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3)
              * normB v μ n (Φ : X n → ℝ)
              * (1 + CW * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))) := by ring
    have h2 : -(4 * Real.pi * μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
              * (1 - J * Real.sqrt (μ * (a v) ^ 3))) * normB v μ n (Φ : X n → ℝ)
            + 4 * Real.pi * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3)
              * normB v μ n (Φ : X n → ℝ)
              * (1 + CW * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
          ≤ 4 * Real.pi * (1 + CW)
              * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
                  * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
              * normB v μ n (Φ : X n → ℝ) := by
      have hkey : J * Real.sqrt (μ * (a v) ^ 3)
            + CW * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          ≤ (1 + CW) * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) := by
        linarith [hJκ]
      calc -(4 * Real.pi * μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
              * (1 - J * Real.sqrt (μ * (a v) ^ 3))) * normB v μ n (Φ : X n → ℝ)
            + 4 * Real.pi * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3)
              * normB v μ n (Φ : X n → ℝ)
              * (1 + CW * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
          = (4 * Real.pi * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3)
                * normB v μ n (Φ : X n → ℝ))
              * (J * Real.sqrt (μ * (a v) ^ 3)
                + CW * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))) := by ring
        _ ≤ (4 * Real.pi * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3)
                * normB v μ n (Φ : X n → ℝ))
              * ((1 + CW) * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hkey h𝔇'nn
        _ = 4 * Real.pi * (1 + CW)
              * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
                  * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
              * normB v μ n (Φ : X n → ℝ) := by ring
    linarith [h1, h2]
  have hBnn : 0 ≤ ((1 / 2) * μ ^ 2 * 𝒞 * normB v μ n (Φ : X n → ℝ)
        + (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
              + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
              * normB v μ n (Φ : X n → ℝ))) * 𝒞I
        + C * μ * (a v) * normB v μ n (Φ : X n → ℝ) * VI)
      + ((1 / 2) * μ ^ 2 * 𝒞L * normB v μ n (Φ : X n → ℝ)
        + (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
              + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
              * normB v μ n (Φ : X n → ℝ))) * 𝒞Lc
        + C * μ * (a v) * normB v μ n (Φ : X n → ℝ) * VL)
      + 3 * μ * Fb := by
    have h1 : 0 ≤ (1 / 2) * μ ^ 2 * 𝒞 * normB v μ n (Φ : X n → ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg μ)) h𝒞nn) hNnn
    have hG : 0 ≤ C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
            + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
            * normB v μ n (Φ : X n → ℝ)) :=
      mul_nonneg hC (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav.le) hΓnn) hNnn)
    have h2 : 0 ≤ (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
              + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
              * normB v μ n (Φ : X n → ℝ))) * 𝒞I :=
      mul_nonneg hG h𝒞Inn
    have h3 : 0 ≤ C * μ * (a v) * normB v μ n (Φ : X n → ℝ) * VI :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hμ.le) hav.le) hNnn) hVInn
    have h4 : 0 ≤ (1 / 2) * μ ^ 2 * 𝒞L * normB v μ n (Φ : X n → ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg μ)) h𝒞Lnn) hNnn
    have h5 : 0 ≤ (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
              + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
              * normB v μ n (Φ : X n → ℝ))) * 𝒞Lc :=
      mul_nonneg hG h𝒞Lcnn
    have h6 : 0 ≤ C * μ * (a v) * normB v μ n (Φ : X n → ℝ) * VL :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hμ.le) hav.le) hNnn) hVLnn
    have h7 : 0 ≤ 3 * μ * Fb := mul_nonneg (mul_nonneg (by norm_num) hμ.le) hFbnn
    set_option maxRecDepth 4000 in
    linarith [h1, h2, h3, h4, h5, h6, h7]
  have hCSw : CS * wordB v h μ n (Φ : X n → ℝ) ≤ wordB v h μ n (Φ : X n → ℝ) := by
    have hmul := mul_nonpos_of_nonneg_of_nonpos
      (by linarith [hCS1] : (0 : ℝ) ≤ CS - 1) hwordB_nonpos
    have he : (CS - 1) * wordB v h μ n (Φ : X n → ℝ)
        = CS * wordB v h μ n (Φ : X n → ℝ) - wordB v h μ n (Φ : X n → ℝ) := by ring
    linarith [hmul, he]
  -- ### the remaining pieces of `B1` and `B2`
  have hI2b : (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
          + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          * normB v μ n (Φ : X n → ℝ))) * 𝒞I
      ≤ 2 * C * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
              * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
          * normB v μ n (Φ : X n → ℝ) := by
    have hCD : (0 : ℝ) ≤ C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
        + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
        * normB v μ n (Φ : X n → ℝ)) := by positivity
    calc (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
          + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          * normB v μ n (Φ : X n → ℝ))) * 𝒞I
        ≤ (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
              + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
              * normB v μ n (Φ : X n → ℝ))) * (sideAt μ (a v)) ^ 3 :=
          mul_le_mul_of_nonneg_left h𝒞I_le hCD
      _ = C * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
              * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
                + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
            * normB v μ n (Φ : X n → ℝ) := by ring
      _ ≤ C * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
              * (2 * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))))
            * normB v μ n (Φ : X n → ℝ) := by
          have hfac : (0 : ℝ) ≤ μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 := by positivity
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΓ_le hfac) hC) hNnn
      _ = 2 * C * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
              * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
            * normB v μ n (Φ : X n → ℝ) := by ring
  have hI3b : C * μ * (a v) * normB v μ n (Φ : X n → ℝ) * VI
      ≤ 8 * C * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
              * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
          * normB v μ n (Φ : X n → ℝ) := by
    calc C * μ * (a v) * normB v μ n (Φ : X n → ℝ) * VI
        ≤ C * μ * (a v) * normB v μ n (Φ : X n → ℝ)
            * (8 * (μ * (sideAt μ (a v)) ^ 3
              * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))) :=
          have hfac : (0 : ℝ) ≤ C * μ * (a v) * normB v μ n (Φ : X n → ℝ) :=
            mul_nonneg (mul_nonneg (mul_nonneg hC hμ.le) hav.le) hNnn
          mul_le_mul_of_nonneg_left hVI_le hfac
      _ = 8 * C * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
              * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
            * normB v μ n (Φ : X n → ℝ) := by ring
  have hL1b : (1 / 2) * μ ^ 2 * 𝒞L * normB v μ n (Φ : X n → ℝ)
      ≤ (1 / 2) * Cm * (2 : ℝ) ^ 96 * Kb
          * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
              * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
          * normB v μ n (Φ : X n → ℝ) := by
    have hAB : (0 : ℝ) ≤ (1 / 2) * μ ^ 2 * normB v μ n (Φ : X n → ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg μ)) hNnn
    have hCB : (0 : ℝ) ≤ Cm * (a v) := mul_nonneg hCm hav.le
    calc (1 / 2) * μ ^ 2 * 𝒞L * normB v μ n (Φ : X n → ℝ)
        = ((1 / 2) * μ ^ 2 * normB v μ n (Φ : X n → ℝ)) * 𝒞L := by ring
      _ ≤ ((1 / 2) * μ ^ 2 * normB v μ n (Φ : X n → ℝ)) * (Cm * (a v) * 𝒞Lc) :=
          mul_le_mul_of_nonneg_left h𝒞L_le hAB
      _ ≤ ((1 / 2) * μ ^ 2 * normB v μ n (Φ : X n → ℝ))
            * (Cm * (a v) * ((2 : ℝ) ^ 96 * Kb
              * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
              * (sideAt μ (a v)) ^ 3)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h𝒞Lc_le hCB) hAB
      _ = (1 / 2) * Cm * (2 : ℝ) ^ 96 * Kb
            * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
              * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
            * normB v μ n (Φ : X n → ℝ) := by ring
  have hL2b : (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
          + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          * normB v μ n (Φ : X n → ℝ))) * 𝒞Lc
      ≤ 2 * C * (2 : ℝ) ^ 96 * Kb
          * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
              * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
          * normB v μ n (Φ : X n → ℝ) := by
    have hCD : (0 : ℝ) ≤ C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
        + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
        * normB v μ n (Φ : X n → ℝ)) := by positivity
    have hCK : (0 : ℝ) ≤ (2 : ℝ) ^ 96 * Kb
        * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) :=
      mul_nonneg (mul_nonneg (by norm_num) hKb) hκnn
    calc (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
          + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          * normB v μ n (Φ : X n → ℝ))) * 𝒞Lc
        ≤ (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
              + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
              * normB v μ n (Φ : X n → ℝ)))
            * ((2 : ℝ) ^ 96 * Kb * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
              * (sideAt μ (a v)) ^ 3) :=
          mul_le_mul_of_nonneg_left h𝒞Lc_le hCD
      _ = C * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
              * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
                + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
            * ((2 : ℝ) ^ 96 * Kb * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
            * normB v μ n (Φ : X n → ℝ) := by ring
      _ ≤ C * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
              * (2 * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))))
            * ((2 : ℝ) ^ 96 * Kb * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
            * normB v μ n (Φ : X n → ℝ) := by
          have hfac : (0 : ℝ) ≤ μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 := by positivity
          set_option maxRecDepth 4000 in
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΓ_le hfac) hC) hCK) hNnn
      _ ≤ 2 * C * (2 : ℝ) ^ 96 * Kb
            * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
              * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
            * normB v μ n (Φ : X n → ℝ) := by
          have hsq : ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
              * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
              ≤ ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) := by
            have h := mul_le_mul_of_nonneg_left hκ' hκnn
            linarith [h]
          calc C * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
                * (2 * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))))
              * ((2 : ℝ) ^ 96 * Kb
                * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
              * normB v μ n (Φ : X n → ℝ)
            = ((C * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3) * (2 : ℝ) ^ 96 * Kb
                * normB v μ n (Φ : X n → ℝ)) * 2)
              * (((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
                * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))) := by ring
            _ ≤ ((C * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3) * (2 : ℝ) ^ 96 * Kb
                * normB v μ n (Φ : X n → ℝ)) * 2)
              * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_left hsq (by positivity)
            _ = 2 * C * (2 : ℝ) ^ 96 * Kb
                * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
                  * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
                * normB v μ n (Φ : X n → ℝ) := by ring
  have hL3b : C * μ * (a v) * normB v μ n (Φ : X n → ℝ) * VL
      ≤ 8 * C * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
              * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
          * normB v μ n (Φ : X n → ℝ) := by
    calc C * μ * (a v) * normB v μ n (Φ : X n → ℝ) * VL
        ≤ C * μ * (a v) * normB v μ n (Φ : X n → ℝ)
            * (8 * (μ * (sideAt μ (a v)) ^ 3
              * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))) :=
          have hfac : (0 : ℝ) ≤ C * μ * (a v) * normB v μ n (Φ : X n → ℝ) :=
            mul_nonneg (mul_nonneg (mul_nonneg hC hμ.le) hav.le) hNnn
          mul_le_mul_of_nonneg_left hVL_le hfac
      _ = 8 * C * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
              * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
            * normB v μ n (Φ : X n → ℝ) := by ring
  have hmain1 : c₁ * nomRPsi h μ (Φ : X n → ℝ)
      ≤ (4 * Real.pi * (1 + CW) + 18 * C + (1 / 2) * Cm * (2 : ℝ) ^ 96 * Kb
            + 2 * C * (2 : ℝ) ^ 96 * Kb)
          * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
              * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
          * normB v μ n (Φ : X n → ℝ)
        + E * (μ * (a v) * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
            * (n : ℝ) * normB v μ n (Φ : X n → ℝ) := by
    set_option maxRecDepth 4000 in
    linarith [hIrow, key1, hCSw, hwordB_le, hFb_pay, hcancel, hI2b, hI3b, hL1b, hL2b, hL3b]
  have hmain2 : ((paramsAt μ (a v)).b / (2 * (sideAt μ (a v)) ^ 2))
        * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
      ≤ (4 * Real.pi * (1 + CW) + 18 * C + (1 / 2) * Cm * (2 : ℝ) ^ 96 * Kb
            + 2 * C * (2 : ℝ) ^ 96 * Kb)
          * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3
              * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
          * normB v μ n (Φ : X n → ℝ)
        + E * (μ * (a v) * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
            * (n : ℝ) * normB v μ n (Φ : X n → ℝ) := by
    have hS1 := hSfun μ hAdmS n Φ
    have hsws_ge : -(((1 / 2) * μ ^ 2 * 𝒞 * normB v μ n (Φ : X n → ℝ)
          + (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
                + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
                * normB v μ n (Φ : X n → ℝ))) * 𝒞I
          + C * μ * (a v) * normB v μ n (Φ : X n → ℝ) * VI)
        + ((1 / 2) * μ ^ 2 * 𝒞L * normB v μ n (Φ : X n → ℝ)
          + (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
                + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
                * normB v μ n (Φ : X n → ℝ))) * 𝒞Lc
          + C * μ * (a v) * normB v μ n (Φ : X n → ℝ) * VL)
        + 3 * μ * Fb)
        ≤ ∫ u in 𝔾, sbWordSlot v h (if u ∈ 𝕀 then μ else 4 * μ) μ u (Φ : X n → ℝ) := by
      have h2 : (∫ u in 𝔾, sbWordSlot v h (if u ∈ 𝕀 then μ else 4 * μ) μ u (Φ : X n → ℝ))
          = (∫ u in 𝕀, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
            + (∫ u in 𝕃, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)) - 3 * μ * Fb := by
        linarith [hsplitSW, hsplitSWS]
      have h3 : -(∫ u in 𝕀, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
          ≤ ((1 / 2) * μ ^ 2 * 𝒞 * normB v μ n (Φ : X n → ℝ)
            + (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
                  + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
                  * normB v μ n (Φ : X n → ℝ))) * 𝒞I
            + C * μ * (a v) * normB v μ n (Φ : X n → ℝ) * VI) := by
        have hc : 0 ≤ c₁ * nomRPsi h μ (Φ : X n → ℝ) :=
          mul_nonneg hc₁.le (by
            rw [nomRPsi]
            exact integral_nonneg fun u =>
              mul_nonneg (hmassL' u) (nomBoxInner_nonneg hμ (Φ : X n → ℝ) u))
        linarith [hIrow, hc]
      have h4 : -(∫ u in 𝕃, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
          ≤ ((1 / 2) * μ ^ 2 * 𝒞L * normB v μ n (Φ : X n → ℝ)
            + (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
                  + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
                  * normB v μ n (Φ : X n → ℝ))) * 𝒞Lc
            + C * μ * (a v) * normB v μ n (Φ : X n → ℝ) * VL) := by linarith [hLrow]
      linarith [h2, h3, h4]
    have hstep1 : ((paramsAt μ (a v)).b / (2 * (sideAt μ (a v)) ^ 2))
          * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        ≤ wordB v h μ n (Φ : X n → ℝ)
          - (1 / CS) * (∫ u in 𝔾, sbWordSlot v h (if u ∈ 𝕀 then μ else 4 * μ) μ u
            (Φ : X n → ℝ)) := by
      linarith [hS1]
    have hstep2 : -(1 / CS) * (∫ u in 𝔾, sbWordSlot v h (if u ∈ 𝕀 then μ else 4 * μ) μ u
          (Φ : X n → ℝ))
        ≤ ((1 / 2) * μ ^ 2 * 𝒞 * normB v μ n (Φ : X n → ℝ)
          + (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
                + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
                * normB v μ n (Φ : X n → ℝ))) * 𝒞I
          + C * μ * (a v) * normB v μ n (Φ : X n → ℝ) * VI)
        + ((1 / 2) * μ ^ 2 * 𝒞L * normB v μ n (Φ : X n → ℝ)
          + (C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
                + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
                * normB v μ n (Φ : X n → ℝ))) * 𝒞Lc
          + C * μ * (a v) * normB v μ n (Φ : X n → ℝ) * VL)
        + 3 * μ * Fb := by
      have h5 : -(1 / CS) * (∫ u in 𝔾, sbWordSlot v h (if u ∈ 𝕀 then μ else 4 * μ) μ u
            (Φ : X n → ℝ))
          = (1 / CS) * (-(∫ u in 𝔾, sbWordSlot v h (if u ∈ 𝕀 then μ else 4 * μ) μ u
            (Φ : X n → ℝ))) := by ring
      have h6 := mul_le_mul_of_nonneg_left hsws_ge (by positivity : (0 : ℝ) ≤ 1 / CS)
      have h7 : 1 / CS ≤ 1 := by
        rw [div_le_one hCSpos]; exact hCS1
      have h8 := mul_le_mul_of_nonneg_right h7 hBnn
      linarith [h5, h6, h8]
    set_option maxRecDepth 4000 in
    linarith [hstep1, hstep2, hwordB_le, hFb_pay, hcancel, hI2b, hI3b, hL1b, hL2b, hL3b]
  exact ⟨hmain1, hmain2⟩

end Work.BoseB1Cube
