import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseB1Cube.wbUSharp_facts
import Submission.Work.BoseFixB1.WB.pq_split_meas
import Submission.Work.BoseFixB1S.sig_sharp_wbUSharp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.nomSplitRow`

FS `thm:aprioriHLambda` step 4, the **`P/Q`-split of the nominal remainder** (the row that
converts the one-body potential energy `⟨Σᵢ U(xᵢ)⟩ = ‖Φ‖²·nomSig` into the condensed-particle
count `n‖Φ‖² − n₊` plus a payment for the excited count `n₊`).

The nominal remainder (`Work.BoseB1Cube.nomSig`) is the `u`-average of the local density against
the localised one-body mass,

    nomSig = ∫_{I₋} ∬w_{1,B(u)} · t(u) du ,     t(u) = (∫_{abox} Φ²·n(u)) / (‖Φ‖²·|B(u)|) ,

with the *sharp* (indicator) box count `n(u) = Σᵢ 1_{B(u)}(xᵢ)` and the *sharp* box volume
`|B(u)| = boxMass ℓ d u`.  Two `ingredients` turn it into the split row proved here:

* `sig_sharp_wbUSharp` (the exact configuration-level identity)

      ‖Φ‖²·nomSig = ∫_{abox} Φ²·Σᵢ U(xᵢ) ,     U = wbUSharp h μ = ∫_{I₋}(∬w_{1,B(u)}/|B(u)|)·1_{B(u)} du ,

  valid because the `u`-integrable weight `∬w_{1,B(u)}/|B(u)|` is *both* the normaliser of the
  density and the density of `U`;
* the `P/Q`-split `Work.BoseFixB1.WB.pq_split_meas` at `ε = 1/2` applied to the potential
  `U`: with `∫_Λ U = wbW` (the defining property of `U`) and the pointwise bound
  `U(z) ≤ KU := C₁(χ_∞χ_s(M))²(a v)` (from the caller's hypothesis `hmassU` together with
  `chiMass ≤ (χ_∞χ_s(M))²·boxMass`),

      (1/2)(wbW/ℓ³)·(n‖Φ‖² − n₊) − 3·KU·n₊ ≤ ∫_{abox} Φ²·Σᵢ U(xᵢ) = ‖Φ‖²·nomSig ,

  which is exactly the requested row.  The sector identity
  `n₊ + S₁ = n‖Φ‖²` (`Submission.BoseGases.cnPlus_add_cS1`) identifies the condensed count
  `Σᵢ‖PᵢΦ‖²` with `n‖Φ‖² − n₊`.

The `ε = 1/2` split is FS's: the cross term of `Φ = PᵢΦ + QᵢΦ` costs `2√((W/ℓ³)S₁·KU·n₊)`, and
`ε` is chosen so that the coefficients `1 − ε = 1/2` and `1 + ε⁻¹ = 3` are exactly the ones
appearing in the row.
-/

namespace Work.BoseB1Cube

theorem nomSplitRow {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR : 0 < R)
    {μ : ℝ} (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v)
    (hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hmassU : ∀ u : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1.wbMass v h μ u
      ≤ C₁ * _root_.BoseGases.a v
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    (hN : 0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) :
    (1 / 2) * (Work.BoseFixB1.wbW v h μ / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3)
        * ((n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            - Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Φ : Submission.BoseGases.X n → ℝ))
      - 3 * (C₁ * (Submission.BoseGases.chiSupAbs
              * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue) ^ 2
            * (_root_.BoseGases.a v))
          * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Φ : Submission.BoseGases.X n → ℝ)
      ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          * Work.BoseB1Cube.nomSig h μ (Φ : Submission.BoseGases.X n → ℝ) := by
  have hM1 : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := hM
  have ha0 : 0 ≤ _root_.BoseGases.a v := hav.le
  -- The constant of the row: `KU = C₁(χ_∞χ_s(M))²(a v)`, the pointwise bound on `U`.
  let KU : ℝ := C₁ * (Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) ^ 2
      * (_root_.BoseGases.a v)
  have hKU0 : 0 ≤ KU := by
    exact mul_nonneg (mul_nonneg hC₁.le (sq_nonneg _)) ha0
  -- ### the four facts about the sharp sliding potential `U = wbUSharp h μ`
  have hfact := Work.BoseB1Cube.wbUSharp_facts (v := v) h hv hvrad hR hv_supp hμ hav hM hℓ hd
    (C := C₁ * (Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay (Work.BoseBox.paramsAt μ (BoseGases.a v)).M) ^ 2)
    (by positivity) (by
      -- the caller's `chiMass`-form bound, pushed to the `boxMass`-form with constant `C`
      intro u
      have h1 := hmassU u
      rw [Work.BoseFixB1.wbMass] at h1
      have h2 := Work.BoseFixB1S.chiMass_le_const_mul_boxMass
        (M := (Work.BoseBox.paramsAt μ (BoseGases.a v)).M) hM hℓ hd u
      have h3 : 0 ≤ C₁ * _root_.BoseGases.a v := mul_nonneg hC₁.le ha0
      calc Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (BoseGases.a v)) (Work.BoseBox.paramsAt μ (BoseGases.a v)).d u
          ≤ C₁ * _root_.BoseGases.a v * Work.SmallBoxSliding.chiMass
              (Work.BoseBox.paramsAt μ (BoseGases.a v)).M (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Work.BoseBox.paramsAt μ (BoseGases.a v)).d u := h1
        _ ≤ C₁ * _root_.BoseGases.a v * ((Submission.BoseGases.chiSupAbs
              * Submission.BoseGases.chiSmallDecay (Work.BoseBox.paramsAt μ (BoseGases.a v)).M) ^ 2
              * Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (BoseGases.a v)).d u) :=
            mul_le_mul_of_nonneg_left h2 h3
        _ = (C₁ * (Submission.BoseGases.chiSupAbs
              * Submission.BoseGases.chiSmallDecay (Work.BoseBox.paramsAt μ (BoseGases.a v)).M) ^ 2)
              * _root_.BoseGases.a v
              * Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (BoseGases.a v)).d u := by ring)
  -- ### `∫_Λ U = W` (the defining property of `U`)
  have hIntW : (∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (BoseGases.a v)),
      Work.BoseFixB1S.wbUSharp h μ z) = Work.BoseFixB1.wbW v h μ :=
    Work.BoseFixB1S.integral_wbUSharp (v := v) (h := h) (R0 := R) hv hvrad hv_supp hR hμ hav
      hM hℓ hd hC₁.le hmassU
  -- ### the `P/Q`-split at `ε = 1/2`, lower half
  have hpq := (Work.BoseFixB1.WB.pq_split_meas (N := n)
      (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v)) hℓ
      (Φ := (Φ : Submission.BoseGases.X n → ℝ)) Φ.contDiff.continuous
      (g := Work.BoseFixB1S.wbUSharp h μ) (Tvol := Work.BoseFixB1.wbW v h μ) (KU := KU)
      (ε := (1/2 : ℝ)) (by norm_num) hfact.2.1 hfact.2.2.1 hfact.1 hIntW hfact.2.2.2).2
  have he1 : (1 : ℝ) - 1/2 = 1/2 := by norm_num
  have he2 : (1 : ℝ) + (1/2 : ℝ)⁻¹ = 3 := by norm_num
  rw [he1, he2] at hpq
  -- ### the configuration-level identity `‖Φ‖²·nomSig = ∫ Φ²·Σᵢ U(xᵢ)`
  have hSigEq : Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        * Work.BoseB1Cube.nomSig h μ (Φ : Submission.BoseGases.X n → ℝ)
      = ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (BoseGases.a v)),
          (Φ : Submission.BoseGases.X n → ℝ) x ^ 2
            * ∑ i : Fin n, Work.BoseFixB1S.wbUSharp h μ (x i) := by
    have hsig := Work.BoseFixB1S.sig_sharp_wbUSharp (v := v) (h := h) (R0 := R) hv hvrad hv_supp
      hR hμ hav hM hℓ hd hC₁.le hmassU Φ
    rw [hsig, Work.BoseB1Cube.nomSig]
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun (Work.SmallBoxSliding.measurableSet_interiorSet _ _ _)
      (fun u hu => ?_)
    rw [Work.BoseB1Cube.nomDens]
    -- the sharp count is the `boxCount` of the sliding box
    have hcnt : (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (BoseGases.a v)),
          (Φ : Submission.BoseGases.X n → ℝ) x ^ 2
            * Work.BoseB1Cube.nomCnt (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Work.BoseBox.paramsAt μ (BoseGases.a v)).d u x)
        = ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (BoseGases.a v)),
          (Φ : Submission.BoseGases.X n → ℝ) x ^ 2 * Work.FockBridge.boxCount
            (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Work.BoseBox.paramsAt μ (BoseGases.a v)).d u) x := by
      refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n _)
        (fun x hx => ?_)
      rw [Work.FockBridge.boxCount_eq_sum_indicator]
      simp only [Work.BoseB1Cube.nomCnt, Work.SmallBoxSliding.boxInd]
    rw [hcnt]
    rw [Work.BoseFixB1.wbMass]
    rw [← mul_div_assoc, ← mul_div_assoc, mul_div_mul_left _ _ (ne_of_gt hN), div_mul_eq_mul_div]
  -- ### the sector identity `Σᵢ‖PᵢΦ‖² = n‖Φ‖² − n₊`
  have hcs : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (BoseGases.a v)),
        (Submission.BoseGases.aP (Work.BoseBox.sideAt μ (BoseGases.a v)) i
            (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)
      = (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        - ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (BoseGases.a v)),
            (Submission.BoseGases.aQ (Work.BoseBox.sideAt μ (BoseGases.a v)) i
                (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 := by
    have h0 := Submission.BoseGases.cnPlus_add_cS1 (N := n) hℓ
      (Φ := (Φ : Submission.BoseGases.X n → ℝ)) Φ.contDiff.continuous
    simp only [Submission.BoseGases.cnPlus, Submission.BoseGases.cS1] at h0
    have hnorm : (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (BoseGases.a v)),
        (Φ : Submission.BoseGases.X n → ℝ) x ^ 2)
        = Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := rfl
    rw [hnorm] at h0
    linarith
  -- ### assembly
  simp only [Submission.BoseGases.cnPlus] at hpq ⊢
  rw [← hcs, hSigEq]
  exact hpq

end Work.BoseB1Cube
