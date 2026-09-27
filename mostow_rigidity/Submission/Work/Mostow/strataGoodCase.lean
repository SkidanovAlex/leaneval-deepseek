import Mathlib
import Submission.Work.Mostow.geeGoodTube
import Submission.Work.Mostow.geeCardK
import Submission.Work.Mostow.covolLB_uncond
import Submission.Work.Mostow.poAction_ge1
import Submission.Work.Mostow.hypIsometry_ge1

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
/-! ## The "fixed-free stratum" case of the covolume gap (CHAPTER PIECE, revised after review)

Setting: `j + m` is the ambient dimension, `2 ≤ j` (stratum dimension), `1 ≤ m` (normal
dimension), `Λ ≤ PO (j+m) 1` discrete with fundamental domain `D`, `b = blk j m 1 R ∈ Λ` with `R`
*fixed-free* (`∀ w, R w = w → w = 0`), every non-identity element of
`Λ ∩ centralizer {b} ∩ ker (resStd j m)` has `rotN (nrmStd j m ·) ≥ rotN R` (the "separation"
hypothesis), and `rotN R ≤ 2 * θ` with `θ ∈ (0,1]`.  Conclusion: `volH (j+m) D ≥ c * θ^(-α)`
for constants `c, α > 0` depending only on `j, m`.

Note (review): this is *unconditional* in `R` — there is no hidden threshold hypothesis.  The
proof splits on the threshold `κ₁` of `geeGoodTube`; the case `κ₁ < rotN R` is handled by
`covolLB_uncond` with the minimum of the two constants.

Pieces already PROVED in the workspace (import them):
* `Work.Mostow.geeGoodTube j m` : for every `CK > 0` there are `c₁ α₁ κ₁ > 0` with `κ₁ ≤ 1` such
  that for all `Λ, D, R` as above with `0 < rotN R ≤ κ₁` and the kernel bound
  `|{c ∈ Λ ∩ centralizer {blk j m 1 R} | resStd j m c = 1}| ≤ ofReal (CK * (rotN R)^(-m/2))`,
  one has `ofReal (c₁ * (rotN R)^(-α₁)) ≤ volH (j+m) D`.  Its hypotheses
  `POActionProp j, HypIsometryProp j, POActionProp (j+m), HypIsometryProp (j+m), CovolLB j` come
  from `Work.Mostow.poAction_ge1`, `Work.Mostow.hypIsometry_ge1`, `Work.Mostow.covolLB_uncond`.
* `Work.Mostow.geeCardK j m` : there is `CK > 0` such that for every `θ > 0` with `θ ≤ rotN R` and
  the separation hypothesis at scale `θ`, the kernel bound of the previous bullet holds with this
  `CK` and exponent `θ^(-m/2)`.  Apply it with `θ := rotN R`.
* `Work.Mostow.covolLB_uncond (N) (hN : 2 ≤ N) : CovolLB N`, giving `v > 0` with
  `ofReal v ≤ volH (j+m) D`.

Assembly.  Case `rotN R ≤ κ₁`: combine the first two bullets to get
`ofReal (c₁ * (rotN R)^(-α₁)) ≤ volH (j+m) D`; from `rotN R ≤ 2θ`, `0 < θ` and `θ ≤ 1` derive
`2^(-α₁) * θ^(-α₁) ≤ (rotN R)^(-α₁)` (`Real.mul_rpow`, `Real.rpow_le_rpow_of_nonpos`).  Hence
`c := c₁ * 2^(-α₁)`, `α := α₁` works in this case.
Case `κ₁ < rotN R`: then `θ ≥ rotN R / 2 > κ₁ / 2 > 0`, so `θ^(-α₁) ≤ (κ₁/2)^(-α₁)`; taking
`c ≤ v * (κ₁/2)^(α₁)` gives `ofReal (c * θ^(-α₁)) ≤ ofReal v ≤ volH (j+m) D`.
So `c := min (c₁ * 2^(-α₁)) (v * (κ₁/2)^(α₁))` and `α := α₁` work in both cases. -/

theorem strataGoodCase (j m : ℕ) (hj : 2 ≤ j) (hm : 1 ≤ m) :
    ∃ c α : ℝ, 0 < c ∧ 0 < α ∧
      ∀ (Λ : Subgroup (PO (j + m) 1)) (D : Set (E (j + m))) (R : E m ≃ₗᵢ[ℝ] E m) (θ : ℝ),
        IsDiscrete (Λ : Set (PO (j + m) 1)) → IsFundamentalDomain Λ D (volH (j + m)) →
        blk j m 1 R ∈ Λ → (∀ w : E m, R w = w → w = 0) → 0 < rotN R →
        rotN R ≤ 2 * θ → 0 < θ → θ ≤ 1 →
        (∀ c : PO (j + m) 1, c ∈ Λ → c ∈ Subgroup.centralizer {blk j m 1 R} →
          resStd j m c = 1 → c ≠ 1 → rotN R ≤ rotN (nrmStd j m c)) →
        ENNReal.ofReal (c * θ ^ (-α)) ≤ volH (j + m) D := by
  have hj1 : 1 ≤ j := by omega
  have hjm1 : 1 ≤ j + m := by omega
  have hAj : POActionProp j := poAction_ge1 j hj1
  have hIj : HypIsometryProp j := hypIsometry_ge1 j hj1 hAj
  have hA : POActionProp (j + m) := poAction_ge1 (j + m) hjm1
  have hI : HypIsometryProp (j + m) := hypIsometry_ge1 (j + m) hjm1 hA
  have hCovj : CovolLB j := covolLB_uncond j hj
  have hCovN : CovolLB (j + m) := covolLB_uncond (j + m) (by omega)
  obtain ⟨v, hvpos, hv⟩ := hCovN
  obtain ⟨CK, hCKpos, hCK⟩ := geeCardK j m hAj hIj hA hI
  obtain ⟨c₁, α₁, κ₁, hc₁, hα₁, hκ₁, hκ₁le1, htube⟩ :=
    geeGoodTube j m hAj hIj hA hI hCovj hj hm CK hCKpos
  refine ⟨min (c₁ * 2 ^ (-α₁)) (v * (κ₁ / 2) ^ α₁), α₁, ?_, hα₁, ?_⟩
  · exact lt_min (mul_pos hc₁ (Real.rpow_pos_of_pos (by norm_num) _))
      (mul_pos hvpos (Real.rpow_pos_of_pos (by linarith) _))
  · intro Λ D R θ hdisc hD hb hRfree hrotpos hrotθ hθpos hθle1 hsep
    have hκhalf_pos : 0 < κ₁ / 2 := by linarith
    have hrpowpos : 0 < θ ^ (-α₁) := Real.rpow_pos_of_pos hθpos _
    by_cases hcase : rotN R ≤ κ₁
    · -- ### good case: `rotN R ≤ κ₁`, use `geeGoodTube`
      have hK := hCK Λ R (rotN R) hdisc hb hRfree hrotpos le_rfl hsep
      have htube' := htube Λ D R hdisc hD hb hRfree hrotpos hcase hK
      have h2rpow : 2 ^ (-α₁) * θ ^ (-α₁) ≤ (rotN R) ^ (-α₁) := by
        rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hθpos.le]
        exact Real.rpow_le_rpow_of_nonpos hrotpos hrotθ (by linarith)
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) htube'
      calc min (c₁ * 2 ^ (-α₁)) (v * (κ₁ / 2) ^ α₁) * θ ^ (-α₁)
          ≤ (c₁ * 2 ^ (-α₁)) * θ ^ (-α₁) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hrpowpos.le
        _ = c₁ * (2 ^ (-α₁) * θ ^ (-α₁)) := by ring
        _ ≤ c₁ * (rotN R) ^ (-α₁) := mul_le_mul_of_nonneg_left h2rpow hc₁.le
    · -- ### bad case: `κ₁ < rotN R`, use the Kazhdan–Margulis bound
      have hcase' : κ₁ < rotN R := not_le.mp hcase
      have hvD : ENNReal.ofReal v ≤ volH (j + m) D := hv Λ hdisc D hD
      have hθκ : κ₁ / 2 ≤ θ := by linarith
      have hratio : (κ₁ / 2) ^ α₁ * θ ^ (-α₁) ≤ 1 := by
        have h1 : (κ₁ / 2) ^ α₁ ≤ θ ^ α₁ := Real.rpow_le_rpow hκhalf_pos.le hθκ hα₁.le
        have h2 : θ ^ (-α₁) = (θ ^ α₁)⁻¹ := Real.rpow_neg hθpos.le α₁
        rw [h2]
        have h3 : 0 < θ ^ α₁ := Real.rpow_pos_of_pos hθpos α₁
        calc (κ₁ / 2) ^ α₁ * (θ ^ α₁)⁻¹ ≤ θ ^ α₁ * (θ ^ α₁)⁻¹ :=
              mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr h3.le)
          _ = 1 := mul_inv_cancel₀ (ne_of_gt h3)
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hvD
      calc min (c₁ * 2 ^ (-α₁)) (v * (κ₁ / 2) ^ α₁) * θ ^ (-α₁)
          ≤ (v * (κ₁ / 2) ^ α₁) * θ ^ (-α₁) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hrpowpos.le
        _ = v * ((κ₁ / 2) ^ α₁ * θ ^ (-α₁)) := by ring
        _ ≤ v * 1 := mul_le_mul_of_nonneg_left hratio hvpos.le
        _ = v := mul_one v

end Work.Mostow
