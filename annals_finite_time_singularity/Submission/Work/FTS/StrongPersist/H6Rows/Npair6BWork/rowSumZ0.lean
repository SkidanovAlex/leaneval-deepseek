import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Basic
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.Base
import Submission.Work.FTS.TransportS.T2Sup.smainBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-- `√(a · b²) = √a · |b|` for `a ≥ 0`. -/
private theorem sqrt_mul_sq_eq {a b : ℝ} (ha : 0 ≤ a) :
    Real.sqrt (a * b ^ 2) = Real.sqrt a * |b| := by
  rw [Real.sqrt_mul ha, Real.sqrt_sq_eq_abs]

/-- **The pointwise integral engine (absolute-value form).**  A pointwise domination of `|F|`
by `M · HkIntegrand α 6 g` on the open quadrant gives integrability of `F` against the product
measure and the bound `|∫ F| ≤ M · HkSq α 6 g`. -/
private theorem abs_integral_le_pointwise {α M : ℝ} {F g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmemg : Work.Spaces.HkMem α 6 g) (hM : 0 ≤ M)
    (haesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2) PM)
    (hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F z θ| ≤ M * Work.Spaces.HkIntegrand α 6 g z θ) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => F p.1 p.2) PM ∧
      |∫ p, F p.1 p.2 ∂PM| ≤ M * Work.Spaces.HkSq α 6 g := by
  obtain ⟨hint, hle⟩ :=
    Work.FTS.StrongPersist.N6Trans.SixAux.integrable_of_pointwise hg hmemg hM haesm hpt
  obtain ⟨-, hle2⟩ :=
    Work.FTS.StrongPersist.N6Trans.SixAux.integrable_of_pointwise hg hmemg hM haesm.neg
      (fun z θ hz hθ hθ2 => by rw [abs_neg]; exact hpt z θ hz hθ hθ2)
  rw [MeasureTheory.integral_neg] at hle2
  exact ⟨hint, abs_le.mpr ⟨by linarith, hle⟩⟩

/-- **The sup-and-pair engine, with the pointwise domination discharged.**  If the middle
factor `Y` is bounded by `KY` and the two outer factors `X`, `Z` carry the common weight `ρv`
(`≥ 0`) with weighted energies bounded by `AX`, `AZ`, then the triple pairing is integrable
and bounded by `KY · (√AX · √AZ)`. -/
private theorem rowCS {α KY AX AZ : ℝ} {X Y Z ρv : ℝ → ℝ → ℝ}
    (hKY0 : 0 ≤ KY) (hAX0 : 0 ≤ AX) (hAZ0 : 0 ≤ AZ)
    (hρnn : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ ρv z θ)
    (hI1 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρv p.1 p.2 * (X p.1 p.2) ^ 2) PM)
    (hv1 : ∫ p, ρv p.1 p.2 * (X p.1 p.2) ^ 2 ∂PM ≤ AX)
    (hI2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρv p.1 p.2 * (Z p.1 p.2) ^ 2) PM)
    (hv2 : ∫ p, ρv p.1 p.2 * (Z p.1 p.2) ^ 2 ∂PM ≤ AZ)
    (hm1 : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.sqrt (ρv p.1 p.2 * (X p.1 p.2) ^ 2)) PM)
    (hm2 : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.sqrt (ρv p.1 p.2 * (Z p.1 p.2) ^ 2)) PM)
    (hρm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => ρv p.1 p.2) PM)
    (hXm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => X p.1 p.2) PM)
    (hYm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Y p.1 p.2) PM)
    (hZm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Z p.1 p.2) PM)
    (hYb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Y z θ| ≤ KY) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        ρv p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2) PM ∧
      |∫ p, ρv p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2 ∂PM|
        ≤ KY * (Real.sqrt AX * Real.sqrt AZ) := by
  have hρae : ∀ᵐ p ∂PM, 0 ≤ ρv p.1 p.2 :=
    ae_of_forall_Qd (fun z θ hz hθ hθ2 => hρnn z θ hz hθ hθ2)
  refine rowSummand_core (α := α) (f := fun _ _ => (0 : ℝ)) hKY0 hAX0 hAZ0 hρnn
    hI1 hI2 hv1 hv2 hρae hρae hm1 hm2 hρm hXm hYm hZm ?_
  intro z θ hz hθ hθ2
  have hρg := hρnn z θ hz hθ hθ2
  have hY := hYb z θ hz hθ hθ2
  have hs1 : Real.sqrt (ρv z θ * X z θ ^ 2) = Real.sqrt (ρv z θ) * |X z θ| :=
    sqrt_mul_sq_eq hρg
  have hs2 : Real.sqrt (ρv z θ * Z z θ ^ 2) = Real.sqrt (ρv z θ) * |Z z θ| :=
    sqrt_mul_sq_eq hρg
  have hρsq : Real.sqrt (ρv z θ) * Real.sqrt (ρv z θ) = ρv z θ := Real.mul_self_sqrt hρg
  have hXnn : 0 ≤ |X z θ| := abs_nonneg _
  have hZnn : 0 ≤ |Z z θ| := abs_nonneg _
  calc |ρv z θ * X z θ * Y z θ * Z z θ|
      = ρv z θ * |X z θ| * |Y z θ| * |Z z θ| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hρg]
    _ ≤ KY * (ρv z θ * |X z θ| * |Z z θ|) := by
        have hkey : ρv z θ * |X z θ| * |Y z θ| * |Z z θ|
            = |Y z θ| * (ρv z θ * |X z θ| * |Z z θ|) := by ring
        rw [hkey]
        exact mul_le_mul_of_nonneg_right hY
          (mul_nonneg (mul_nonneg hρg hXnn) hZnn)
    _ = KY * (Real.sqrt (ρv z θ * X z θ ^ 2) * Real.sqrt (ρv z θ * Z z θ ^ 2)) := by
        rw [hs1, hs2]
        have hkey : (Real.sqrt (ρv z θ) * |X z θ|) * (Real.sqrt (ρv z θ) * |Z z θ|)
            = ρv z θ * |X z θ| * |Z z θ| := by
          rw [show (Real.sqrt (ρv z θ) * |X z θ|) * (Real.sqrt (ρv z θ) * |Z z θ|)
              = (Real.sqrt (ρv z θ) * Real.sqrt (ρv z θ)) * (|X z θ| * |Z z θ|) from by ring,
            hρsq]
          ring
        rw [hkey]

/-- **Leibniz summand with `a = a₁ = 0` (all three factors pure in `θ`), non-flux.**

`X := D_z^{b₁}A`, `Y := D_z^{b+1-b₁} f`, `Z := D_z^b f`, and `ρ ≤ canonW η` (a pure slot: `IsLeafW α 0 ρ`
only allows `leafEta`/`leafOne`).

* `b₁ ≤ 2`: `|D_z^{b₁}A| ≤ Cα^{-1/2}(K0+K4)` (`CoefData.val` for `b₁ = 0`, `sup_dz_le_hk` for `b₁ = 1,2`) and
  `∫ρ|Y||Z| ≤ HkSq α 6 f` (Cauchy–Schwarz at the `η`-weight; `ord Y = b+1-b₁ ≤ 6` and `ord Z = b ≤ 6` by
  the non-flux hypothesis `¬(b₁ = 0 ∧ b = 6)`).
* `3 ≤ b₁ ≤ 4`: `|D_z^b₁A| ≤ C₃α^{-1/2}K6` (`supSix` with `(b,a) = (b₁,0)`, honestly `HkMem α 6 A`), then
  `∫ρ|X||Z| ≤ K4·HkNorm α 6 f` (using `∫ρX² ≤ HkSq α 4 A ≤ K4²` for `b₁ ≤ 4` and `∫ρZ² ≤ HkSq α 6 f`), and
  `|Y| ≤ C₃α^{-1/2}HkNorm α 6 f` (`ord Y = b+1-b₁ ≤ 4`); overall `Cα^{-1/2}K4·HkSq α 6 f`.
* `5 ≤ b₁ ≤ 6`: `∫ρX² ≤ HkSq α 6 A ≤ K6²`, `∫ρZ² ≤ HkSq α 6 f` and `|Y| ≤ C/√(γ-1)·M` pointwise
  (`ord Y = b+1-b₁ ≤ 2`, a pure slot, `DatData.bdd`), giving `Cα^{-1/2}M·K6·HkNorm α 6 f`.

Assemble with `Npair6BWork.rowSummand_core`/`val_le_HkSq`, `canonW_mul_z_le_of_le`, `canonW_le_of_le`,
`leafW_le_canonW_eta`, `leafW_nonneg`, `aesm_mixed`, `aesm_canonW`. -/
theorem rowSumZ0 : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 K1 M : ℝ) (b b₁ : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.VocabO.CoefThMem 1 A → Work.FTS.VocabO.CoefTh 1 A ≤ K1 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      b ≤ 6 → Work.FTS.TransportS.IsLeafW α 0 ρ → b₁ ≤ b →
      ¬ (b₁ = 0 ∧ b = 6) →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
          * Work.Spaces.DzIter b₁ A p.1 p.2
          * Work.Spaces.DzIter (b + 1 - b₁) f p.1 p.2
          * Work.Spaces.DzIter b f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, ρ p.1 p.2 * Work.Spaces.DzIter b₁ A p.1 p.2
            * Work.Spaces.DzIter (b + 1 - b₁) f p.1 p.2
            * Work.Spaces.DzIter b f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * α ^ (-(1 / 2 : ℝ))
            * ((K0 + K4) * Work.Spaces.HkSq α 6 f
               + M * K6 * Work.Spaces.HkNorm α 6 f) := by
  obtain ⟨Csup, hCsup0, hsup⟩ := Work.FTS.TransportS.sup_dz_le_hk
  obtain ⟨C6, hC60, h6sup⟩ := Work.FTS.StrongPersist.N6Trans.T1SixAux.supSix
  refine ⟨max (max (Csup * Real.sqrt 10) 1) C6, ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) (le_max_left _ _))
  intro α hα A f K0 K4 K6 K1 M b b₁ ρ hcoef hctmem hctle hdat hb hleaf hb1 hnf
  obtain ⟨hα0, hα1⟩ := hα
  -- ## the hypotheses' consequences
  have hK0 : 0 ≤ K0 := by
    have h := hcoef.val 1 (Real.pi / 4) one_pos (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
    linarith [abs_nonneg (A 1 (Real.pi / 4))]
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hcoef.n4
  have hK6 : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hcoef.n6
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hHk6 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hHkn6 : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hαinv0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := (Real.rpow_pos_of_pos hα0 _).le
  have hαinv1 : 1 ≤ α ^ (-(1 / 2 : ℝ)) :=
    Work.FTS.StrongPersist.N6Trans.SixAux.one_le_alpha_rpow_neg_half hα0 hα1
  have hlam' : (Real.sqrt (Work.Spaces.gam α - 1))⁻¹ = Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) := by
    simpa only [one_div] using
      Work.FTS.StrongPersist.N6Trans.SixAux.one_div_sqrt_gam_sub_one hα0
  -- ## the leaf weight
  have hρnn : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ ρ z θ :=
    leafW_nonneg hleaf
  have hρη : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ ≤ Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ :=
    leafW_le_canonW_eta hleaf
  have hρm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => ρ p.1 p.2) PM :=
    aesm_leafW hleaf
  have hηgam : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
  -- ## the index bounds
  have hY6 : b + 1 - b₁ ≤ 6 := by
    rcases Nat.eq_zero_or_pos b₁ with h0 | hpos
    · subst h0
      have hb6 : b ≠ 6 := fun h6 => hnf ⟨rfl, h6⟩
      omega
    · omega
  -- ## the constant comparisons
  have hCsupCX : Csup * Real.sqrt 10 ≤ max (Csup * Real.sqrt 10) 1 := le_max_left _ _
  have hone : (1 : ℝ) ≤ max (max (Csup * Real.sqrt 10) 1) C6 :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hC0 : (0 : ℝ) ≤ max (max (Csup * Real.sqrt 10) 1) C6 :=
    le_trans (by norm_num) hone
  have hCX1 : (1 : ℝ) ≤ max (Csup * Real.sqrt 10) 1 := le_max_right _ _
  have hCsup10nn : 0 ≤ Csup * Real.sqrt 10 := mul_nonneg hCsup0.le (Real.sqrt_nonneg 10)
  rcases lt_or_ge b₁ 3 with hb13 | hb13
  · -- ## Case 1: `b₁ ≤ 2`
    have hb12 : b₁ ≤ 2 := by omega
    have hXb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.DzIter b₁ A z θ|
          ≤ max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) := by
      intro z θ hz hθ hθ2
      rcases Nat.eq_zero_or_pos b₁ with h0 | hpos
      · subst h0
        have h1 : |Work.Spaces.DzIter 0 A z θ| ≤ K0 := by
          simpa only [Work.Spaces.DzIter_zero] using hcoef.val z θ hz hθ hθ2
        have h2 : K0 + K4 ≤ max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) := by
          have h3 : (1 : ℝ) ≤ max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ)) := by
            calc (1 : ℝ) = 1 * 1 := by ring
              _ ≤ max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ)) :=
                  mul_le_mul hCX1 hαinv1 (by norm_num)
                    (le_trans (by norm_num) hCX1)
          calc K0 + K4 = 1 * (K0 + K4) := by ring
            _ ≤ max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) :=
                mul_le_mul_of_nonneg_right h3 (by linarith)
        exact le_trans h1 (le_trans (le_add_of_nonneg_right hK4) h2)
      · have hsupb := hsup α A hα0 hα1 hcoef.sm hcoef.h4 b₁ hb12 z θ hz hθ hθ2
        calc |Work.Spaces.DzIter b₁ A z θ|
            ≤ Csup / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α A := hsupb
          _ = Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α A := by
              rw [div_eq_mul_inv, hlam']; ring
          _ ≤ Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * K4 :=
              mul_le_mul_of_nonneg_left hcoef.n4 (mul_nonneg hCsup10nn hαinv0)
          _ ≤ Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) :=
              mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hK0)
                (mul_nonneg hCsup10nn hαinv0)
          _ ≤ max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCsupCX hαinv0)
                (by linarith)
    have hFm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.DzIter b₁ A p.1 p.2
        * Work.Spaces.DzIter (b + 1 - b₁) f p.1 p.2
        * Work.Spaces.DzIter b f p.1 p.2) PM :=
      (((hρm.mul (aesm_of_smoothOpen (hcoef.sm.DzIter b₁))).mul
        (aesm_of_smoothOpen (hdat.sm.DzIter (b + 1 - b₁)))).mul
        (aesm_of_smoothOpen (hdat.sm.DzIter b)))
    have hMY0 : 0 ≤ max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) :=
      mul_nonneg (mul_nonneg (le_trans (by norm_num) hCX1) hαinv0) (by linarith)
    have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |ρ z θ * Work.Spaces.DzIter b₁ A z θ
          * Work.Spaces.DzIter (b + 1 - b₁) f z θ * Work.Spaces.DzIter b f z θ|
          ≤ (max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4))
            * Work.Spaces.HkIntegrand α 6 f z θ := by
      intro z θ hz hθ hθ2
      have hX := hXb z θ hz hθ hθ2
      have hρ0 := hρnn z θ hz hθ hθ2
      have hzI : z ∈ Work.Spaces.Iz := hz.le
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
      have hpair := Work.FTS.StrongPersist.N6Trans.canonW_pair_le6 (α := α) (g := f)
        (q := Work.Spaces.eta) (j := b + 1 - b₁) (i := 0) (b := b) (a := 0)
        Work.Spaces.eta_pos hηgam (fun _ => le_rfl) (fun _ => le_rfl)
        (by omega) (by omega) hzI hθI
      have hpair' : ρ z θ * |Work.Spaces.DzIter (b + 1 - b₁) f z θ|
            * |Work.Spaces.DzIter b f z θ| ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
        refine le_trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hρη z θ hz hθ hθ2) (abs_nonneg _))
          (abs_nonneg _)) ?_
        simpa only [Work.Spaces.mixed_zero_right] using hpair
      calc |ρ z θ * Work.Spaces.DzIter b₁ A z θ
            * Work.Spaces.DzIter (b + 1 - b₁) f z θ * Work.Spaces.DzIter b f z θ|
          = |Work.Spaces.DzIter b₁ A z θ| * (ρ z θ
              * |Work.Spaces.DzIter (b + 1 - b₁) f z θ|
              * |Work.Spaces.DzIter b f z θ|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hρ0]; ring
        _ ≤ (max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4))
              * (ρ z θ * |Work.Spaces.DzIter (b + 1 - b₁) f z θ|
                * |Work.Spaces.DzIter b f z θ|) :=
            mul_le_mul_of_nonneg_right hX
              (mul_nonneg (mul_nonneg hρ0 (abs_nonneg _)) (abs_nonneg _))
        _ ≤ (max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4))
              * Work.Spaces.HkIntegrand α 6 f z θ :=
            mul_le_mul_of_nonneg_left hpair' hMY0
    obtain ⟨hint, hbd⟩ := abs_integral_le_pointwise hdat.sm hdat.h6 hMY0 hFm hpt
    refine ⟨hint, ?_⟩
    calc |∫ p, ρ p.1 p.2 * Work.Spaces.DzIter b₁ A p.1 p.2
            * Work.Spaces.DzIter (b + 1 - b₁) f p.1 p.2
            * Work.Spaces.DzIter b f p.1 p.2 ∂PM|
        ≤ (max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4))
            * Work.Spaces.HkSq α 6 f := hbd
      _ = max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ))
            * ((K0 + K4) * Work.Spaces.HkSq α 6 f) := by ring
      _ ≤ max (max (Csup * Real.sqrt 10) 1) C6 * α ^ (-(1 / 2 : ℝ))
            * ((K0 + K4) * Work.Spaces.HkSq α 6 f) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hαinv0) ?_
          · exact le_max_left _ _
          · exact mul_nonneg (by linarith) hHk6
      _ ≤ max (max (Csup * Real.sqrt 10) 1) C6 * α ^ (-(1 / 2 : ℝ))
            * ((K0 + K4) * Work.Spaces.HkSq α 6 f
              + M * K6 * Work.Spaces.HkNorm α 6 f) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right
            (mul_nonneg (mul_nonneg hM0 hK6) hHkn6)) (mul_nonneg hC0 hαinv0)
  · rcases lt_or_ge b₁ 5 with hb15 | hb15
    · -- ## Case 2: `3 ≤ b₁ ≤ 4`
      have hb14 : b₁ ≤ 4 := by omega
      have hj4 : b + 1 - b₁ ≤ 4 := by omega
      have hYb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.DzIter (b + 1 - b₁) f z θ|
            ≤ C6 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f := by
        intro z θ hz hθ hθ2
        have h := h6sup α f hα0 hα1 hdat.sm hdat.h6 (b + 1 - b₁) 0 (by omega) z θ hz hθ hθ2
        simpa only [Work.Spaces.mixed_zero_right] using h
      have hKY0 : 0 ≤ C6 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f :=
        mul_nonneg (mul_nonneg hC60.le hαinv0) hHkn6
      have hdom1 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          ρ z θ * (Work.Spaces.DzIter b₁ A z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 A z θ := by
        intro z θ hz hθ hθ2
        refine le_trans (mul_le_mul_of_nonneg_right (hρη z θ hz hθ hθ2) (sq_nonneg _)) ?_
        exact Work.FTS.TransportS.T2Sup.canonW_mul_z_le_of_le (α := α) (q := Work.Spaces.eta)
          (g := A) (z := z) (θ := θ) 4 le_rfl hθ hθ2 hb14
      have hmeas1 : MeasureTheory.AEStronglyMeasurable
          (fun p : ℝ × ℝ => ρ p.1 p.2 * (Work.Spaces.DzIter b₁ A p.1 p.2) ^ 2) PM :=
        hρm.mul ((aesm_of_smoothOpen (hcoef.sm.DzIter b₁)).pow 2)
      have hdom2 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          ρ z θ * (Work.Spaces.DzIter b f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
        intro z θ hz hθ hθ2
        refine le_trans (mul_le_mul_of_nonneg_right (hρη z θ hz hθ hθ2) (sq_nonneg _)) ?_
        exact Work.FTS.TransportS.T2Sup.canonW_mul_z_le_of_le (α := α) (q := Work.Spaces.eta)
          (g := f) (z := z) (θ := θ) 6 le_rfl hθ hθ2 hb
      have hmeas2 : MeasureTheory.AEStronglyMeasurable
          (fun p : ℝ × ℝ => ρ p.1 p.2 * (Work.Spaces.DzIter b f p.1 p.2) ^ 2) PM :=
        hρm.mul ((aesm_of_smoothOpen (hdat.sm.DzIter b)).pow 2)
      obtain ⟨hI1, hv1⟩ := val_le_HkSq (α := α) (k := 4) (f := A) (ρv := ρ)
        (X := fun z θ => Work.Spaces.DzIter b₁ A z θ) hcoef.sm hcoef.h4 hρnn hdom1 hmeas1
      obtain ⟨hI2, hv2⟩ := val_le_HkSq (α := α) (k := 6) (f := f) (ρv := ρ)
        (X := fun z θ => Work.Spaces.DzIter b f z θ) hdat.sm hdat.h6 hρnn hdom2 hmeas2
      obtain ⟨hint, hbd⟩ := rowCS (α := α) (KY := C6 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f)
        (AX := Work.Spaces.HkSq α 4 A) (AZ := Work.Spaces.HkSq α 6 f)
        (X := fun z θ => Work.Spaces.DzIter b₁ A z θ)
        (Y := fun z θ => Work.Spaces.DzIter (b + 1 - b₁) f z θ)
        (Z := fun z θ => Work.Spaces.DzIter b f z θ) (ρv := ρ)
        hKY0 (Work.Spaces.HkSq_nonneg α 4 A) hHk6 hρnn hI1 hv1 hI2 hv2
        (Real.continuous_sqrt.comp_aestronglyMeasurable hmeas1)
        (Real.continuous_sqrt.comp_aestronglyMeasurable hmeas2)
        hρm (aesm_of_smoothOpen (hcoef.sm.DzIter b₁))
        (aesm_of_smoothOpen (hdat.sm.DzIter (b + 1 - b₁)))
        (aesm_of_smoothOpen (hdat.sm.DzIter b)) hYb
      refine ⟨hint, ?_⟩
      have hN4 : Real.sqrt (Work.Spaces.HkSq α 4 A) ≤ K4 := hcoef.n4
      have hAZsq : Real.sqrt (Work.Spaces.HkSq α 6 f) * Real.sqrt (Work.Spaces.HkSq α 6 f)
          = Work.Spaces.HkSq α 6 f := Real.mul_self_sqrt hHk6
      calc |∫ p, ρ p.1 p.2 * Work.Spaces.DzIter b₁ A p.1 p.2
              * Work.Spaces.DzIter (b + 1 - b₁) f p.1 p.2
              * Work.Spaces.DzIter b f p.1 p.2 ∂PM|
          ≤ (C6 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f)
              * (Real.sqrt (Work.Spaces.HkSq α 4 A) * Real.sqrt (Work.Spaces.HkSq α 6 f)) := hbd
        _ ≤ (C6 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f)
              * (K4 * Real.sqrt (Work.Spaces.HkSq α 6 f)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hN4 (Real.sqrt_nonneg _)) hKY0
        _ = C6 * α ^ (-(1 / 2 : ℝ)) * K4
              * (Real.sqrt (Work.Spaces.HkSq α 6 f) * Real.sqrt (Work.Spaces.HkSq α 6 f)) := by
            rw [Work.Spaces.HkNorm]; ring
        _ = C6 * α ^ (-(1 / 2 : ℝ)) * K4 * Work.Spaces.HkSq α 6 f := by rw [hAZsq]
        _ ≤ max (max (Csup * Real.sqrt 10) 1) C6 * α ^ (-(1 / 2 : ℝ))
              * ((K0 + K4) * Work.Spaces.HkSq α 6 f) := by
            rw [show C6 * α ^ (-(1 / 2 : ℝ)) * K4 * Work.Spaces.HkSq α 6 f
                = C6 * α ^ (-(1 / 2 : ℝ)) * (K4 * Work.Spaces.HkSq α 6 f) by ring]
            refine mul_le_mul (mul_le_mul_of_nonneg_right (le_max_right _ _) hαinv0)
              (mul_le_mul_of_nonneg_right (by linarith) hHk6)
              (mul_nonneg hK4 hHk6) (mul_nonneg hC0 hαinv0)
        _ ≤ max (max (Csup * Real.sqrt 10) 1) C6 * α ^ (-(1 / 2 : ℝ))
              * ((K0 + K4) * Work.Spaces.HkSq α 6 f
                + M * K6 * Work.Spaces.HkNorm α 6 f) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right
              (mul_nonneg (mul_nonneg hM0 hK6) hHkn6)) (mul_nonneg hC0 hαinv0)
    · -- ## Case 3: `5 ≤ b₁`
      have hj2 : b + 1 - b₁ ≤ 2 := by omega
      have hb16 : b₁ ≤ 6 := by omega
      have hYb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.DzIter (b + 1 - b₁) f z θ|
            ≤ Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * M := by
        intro z θ hz hθ hθ2
        have h := hsup α f hα0 hα1 hdat.sm
          (HkMem_mono_le hdat.sm (by norm_num) hdat.h6) (b + 1 - b₁) hj2 z θ hz hθ hθ2
        have hcnn : 0 ≤ Csup / Real.sqrt (Work.Spaces.gam α - 1) :=
          div_nonneg hCsup0.le (Real.sqrt_nonneg _)
        calc |Work.Spaces.DzIter (b + 1 - b₁) f z θ|
            ≤ Csup / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f := h
          _ ≤ Csup / Real.sqrt (Work.Spaces.gam α - 1) * M :=
              mul_le_mul_of_nonneg_left hdat.bdd hcnn
          _ = Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * M := by
              rw [div_eq_mul_inv, hlam']; ring
      have hKY0 : 0 ≤ Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * M :=
        mul_nonneg (mul_nonneg hCsup10nn hαinv0) hM0
      have hdom1 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          ρ z θ * (Work.Spaces.DzIter b₁ A z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 A z θ := by
        intro z θ hz hθ hθ2
        refine le_trans (mul_le_mul_of_nonneg_right (hρη z θ hz hθ hθ2) (sq_nonneg _)) ?_
        exact Work.FTS.TransportS.T2Sup.canonW_mul_z_le_of_le (α := α) (q := Work.Spaces.eta)
          (g := A) (z := z) (θ := θ) 6 le_rfl hθ hθ2 hb16
      have hmeas1 : MeasureTheory.AEStronglyMeasurable
          (fun p : ℝ × ℝ => ρ p.1 p.2 * (Work.Spaces.DzIter b₁ A p.1 p.2) ^ 2) PM :=
        hρm.mul ((aesm_of_smoothOpen (hcoef.sm.DzIter b₁)).pow 2)
      have hdom2 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          ρ z θ * (Work.Spaces.DzIter b f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
        intro z θ hz hθ hθ2
        refine le_trans (mul_le_mul_of_nonneg_right (hρη z θ hz hθ hθ2) (sq_nonneg _)) ?_
        exact Work.FTS.TransportS.T2Sup.canonW_mul_z_le_of_le (α := α) (q := Work.Spaces.eta)
          (g := f) (z := z) (θ := θ) 6 le_rfl hθ hθ2 hb
      have hmeas2 : MeasureTheory.AEStronglyMeasurable
          (fun p : ℝ × ℝ => ρ p.1 p.2 * (Work.Spaces.DzIter b f p.1 p.2) ^ 2) PM :=
        hρm.mul ((aesm_of_smoothOpen (hdat.sm.DzIter b)).pow 2)
      obtain ⟨hI1, hv1⟩ := val_le_HkSq (α := α) (k := 6) (f := A) (ρv := ρ)
        (X := fun z θ => Work.Spaces.DzIter b₁ A z θ) hcoef.sm hcoef.h6 hρnn hdom1 hmeas1
      obtain ⟨hI2, hv2⟩ := val_le_HkSq (α := α) (k := 6) (f := f) (ρv := ρ)
        (X := fun z θ => Work.Spaces.DzIter b f z θ) hdat.sm hdat.h6 hρnn hdom2 hmeas2
      obtain ⟨hint, hbd⟩ := rowCS (α := α) (KY := Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * M)
        (AX := Work.Spaces.HkSq α 6 A) (AZ := Work.Spaces.HkSq α 6 f)
        (X := fun z θ => Work.Spaces.DzIter b₁ A z θ)
        (Y := fun z θ => Work.Spaces.DzIter (b + 1 - b₁) f z θ)
        (Z := fun z θ => Work.Spaces.DzIter b f z θ) (ρv := ρ)
        hKY0 (Work.Spaces.HkSq_nonneg α 6 A) hHk6 hρnn hI1 hv1 hI2 hv2
        (Real.continuous_sqrt.comp_aestronglyMeasurable hmeas1)
        (Real.continuous_sqrt.comp_aestronglyMeasurable hmeas2)
        hρm (aesm_of_smoothOpen (hcoef.sm.DzIter b₁))
        (aesm_of_smoothOpen (hdat.sm.DzIter (b + 1 - b₁)))
        (aesm_of_smoothOpen (hdat.sm.DzIter b)) hYb
      refine ⟨hint, ?_⟩
      have hN6 : Real.sqrt (Work.Spaces.HkSq α 6 A) ≤ K6 := hcoef.n6
      calc |∫ p, ρ p.1 p.2 * Work.Spaces.DzIter b₁ A p.1 p.2
              * Work.Spaces.DzIter (b + 1 - b₁) f p.1 p.2
              * Work.Spaces.DzIter b f p.1 p.2 ∂PM|
          ≤ (Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * M)
              * (Real.sqrt (Work.Spaces.HkSq α 6 A) * Real.sqrt (Work.Spaces.HkSq α 6 f)) := hbd
        _ ≤ (Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * M)
              * (K6 * Real.sqrt (Work.Spaces.HkSq α 6 f)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hN6 (Real.sqrt_nonneg _)) hKY0
        _ = Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ))
              * (M * K6 * Real.sqrt (Work.Spaces.HkSq α 6 f)) := by
            show Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * M
                * (K6 * Real.sqrt (Work.Spaces.HkSq α 6 f)) = _
            ring
        _ ≤ max (max (Csup * Real.sqrt 10) 1) C6 * α ^ (-(1 / 2 : ℝ))
              * (M * K6 * Work.Spaces.HkNorm α 6 f) := by
            have hle : Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ))
                ≤ max (max (Csup * Real.sqrt 10) 1) C6 * α ^ (-(1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right
                (le_trans hCsupCX (le_max_left _ _)) hαinv0
            exact mul_le_mul_of_nonneg_right hle
              (mul_nonneg (mul_nonneg hM0 hK6) hHkn6)
        _ ≤ max (max (Csup * Real.sqrt 10) 1) C6 * α ^ (-(1 / 2 : ℝ))
              * ((K0 + K4) * Work.Spaces.HkSq α 6 f
                + M * K6 * Work.Spaces.HkNorm α 6 f) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0 hαinv0)
            exact le_add_of_nonneg_left (mul_nonneg (by linarith) hHk6)

end

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
