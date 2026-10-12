import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.K1lim_sub_chiChiImages
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairRowS3Split` — entering step (S3): the three parts of `K1lim`

`FINDING_PotPairRows_exists.md` §SESSION 12 records the (S3) plan.  After the (S2) step the
block-`I/II` part of the `Q₂` row is carried by the **honest limit kernel**

    K1lim ℓ W (w,z) = (ℓ³)⁻¹ [ χ(w)χ(z)·ℓ³Σ_m W(w−z+ℓ•latVec m)
                              − χ(w)θ(z)·pinQBl ℓ W w
                              − θ(w)χ(z)·pinQCl ℓ W z
                              + θ(w)θ(z)·pinQDl ℓ W ] ,

the `L¹`-weighted limit of the truncated `qVec`-kernel `K1exp`.  Its three rows are exactly the
three terms of the projector `Q = 1 − ℓ⁻³|θ⟩⟨θ|` conjoined with the periodisation of `W`:

* the **`χχ`-part** `chiChiPart`: the honest localised kernel `wLoc ℓ (wScaled ℓ h) 0`, which is
  *literally* the word's kernel (`q2word` is stated with `w2 = wLoc ℓ (g₂ v h) 0` and
  `w1 = wLoc ℓ (g₀ v h) 0`), together with its **images** `chiChiImages` (already bounded in the
  row by the PROVED `chiChiImages_pairing_coul`, T7, via `rowPairSubC_chiChiImages`);
* the **`θ`-part** `thetaPart`: the three `χ̂`-rows.  This is where the `aP`-structure of the word's
  `q2word` (the averages `aP ℓ i Φ = ℓ⁻³∫_{acube}Φ(x[i↦y])dy`) enters the row: in the row's
  shapes (see `pairRowS2Row`)

      rowShape13 Θ A A K p = ∫_x∫_y∫_u star(Θ x)·A(x p.1)·K(x p.2, y)·star(A u)·Θ(x[p.1↦y][p.2↦u])

  the `∫_u` against `star(A u)` (`A = pinCond = c·θ_Λ`) *is* the average `aP ℓ p.2`, while every
  `θ`-factor of `K` turns the `∫_y` into the average `aP ℓ p.1`.

The identities here are the pointwise decompositions; they are two-line combinations of the PROVED
`K1lim_sub_chiChiImages` and `chiChi_latPer3_eq_wLoc_add`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-- The `χχ`-part of `K1lim ℓ W`: the honest localised kernel `χ(w)·W(w−y)·χ(y)`, written with the
three scalar factors separately coerced so that the algebra below is a `ring` computation. -/
noncomputable def chiChiPart (ℓ : ℝ) (W : E3 → ℝ) (w y : E3) : ℂ :=
  (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ) * ((W (w - y) : ℝ) : ℂ)
    * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)

/-- The `θ`-part of `K1lim ℓ W`: the three `χ̂`/`θ` rows, the ones that generate the averages
`aP` of the word `q2word`. -/
noncomputable def thetaPart (ℓ : ℝ) (W : E3 → ℝ) (w y : E3) : ℂ :=
  (((ℓ ^ 3 : ℝ)) : ℂ)⁻¹ *
    ( - (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun ℓ y * pinQBl ℓ W w
      - Work.BoseK15.corpusBox.thetaFun ℓ w
          * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * pinQCl ℓ W y
      + Work.BoseK15.corpusBox.thetaFun ℓ w
          * Work.BoseK15.corpusBox.thetaFun ℓ y * pinQDl ℓ W)

/-- The `χχ`-part as a single coercion of the real product. -/
theorem chiChiPart_eq_real (ℓ : ℝ) (W : E3 → ℝ) (w y : E3) :
    chiChiPart ℓ W w y
      = (((Submission.BoseGases.chiScale ℓ w * W (w - y)
            * Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) := by
  rw [chiChiPart]
  simp only [← Complex.ofReal_mul]

/-- **The three-part decomposition of `K1lim`.**  For a weight `W` vanishing outside the ball of
radius `R`, the limit kernel is the sum of its `χχ`-part, its lattice images and its `θ`-part. -/
theorem K1lim_eq_parts {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hW : ∀ z : E3, R < ‖z‖ → W z = 0) (w y : E3) :
    K1lim ℓ W w y
      = chiChiPart ℓ W w y + chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y
        + thetaPart ℓ W w y := by
  have hmain := K1lim_sub_chiChiImages (ℓ := ℓ) (R := R) hℓ hW w y
  rw [sub_eq_iff_eq_add] at hmain
  rw [hmain, chiChiPart, thetaPart]
  -- name the atoms of the bracket so that the algebra below is a `ring` computation
  set Thw : ℂ := Work.BoseK15.corpusBox.thetaFun ℓ w with hThw
  set Thy : ℂ := Work.BoseK15.corpusBox.thetaFun ℓ y with hThy
  set Chw : ℂ := (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ) with hChw
  set Chy : ℂ := (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) with hChy
  set Wv : ℂ := ((W (w - y) : ℝ) : ℂ) with hWv
  set PB : ℂ := pinQBl ℓ W w with hPB
  set PC : ℂ := pinQCl ℓ W y with hPC
  set PD : ℂ := pinQDl ℓ W with hPD
  set L3 : ℂ := (((ℓ ^ 3 : ℝ)) : ℂ) with hL3
  have hne3 : L3 ≠ 0 := by
    rw [hL3]
    exact Complex.ofReal_ne_zero.mpr (pow_ne_zero 3 (ne_of_gt hℓ))
  have hcancel : ∀ z : ℂ, L3⁻¹ * (L3 * z) = z := fun z => by
    rw [← mul_assoc, inv_mul_cancel₀ hne3, one_mul]
  have hchi : chiChiPart ℓ W w y = Chw * Wv * Chy := by
    rw [chiChiPart, hChw, hChy, hWv]
  have hstep : L3⁻¹ *
        (L3 * Chw * Wv * Chy - Chw * Thy * PB - Thw * Chy * PC + Thw * Thy * PD)
      = Chw * Wv * Chy
        + L3⁻¹ * (-(Chw * Thy * PB) - (Thw * Chy * PC) + Thw * Thy * PD) := by
    rw [← hcancel (Chw * Wv * Chy)]
    ring
  rw [hstep]
  ring

/-- The `χχ`-part at the honest weight `wScaled ℓ h` is the corpus's `wLoc ℓ h 0` kernel. -/
theorem chiChiPart_wScaled (ℓ : ℝ) (h : E3 → ℝ) (w y : E3) :
    chiChiPart ℓ (Submission.BoseGases.wScaled ℓ h) w y
      = ((Submission.BoseGases.wLoc ℓ h 0 w y : ℝ) : ℂ) := by
  have h1 : Submission.BoseGases.chiU ℓ 0 w = Submission.BoseGases.chiScale ℓ w := by
    simp [Submission.BoseGases.chiU, Submission.BoseGases.chiScale]
  have h2 : Submission.BoseGases.chiU ℓ 0 y = Submission.BoseGases.chiScale ℓ y := by
    simp [Submission.BoseGases.chiU, Submission.BoseGases.chiScale]
  rw [chiChiPart_eq_real, Submission.BoseGases.wLoc, h1, h2]

/-- **The `wLoc` form of the decomposition**: at the honest weight the `χχ`-part of `K1lim` is
exactly the word's localised kernel `wLoc ℓ h 0`. -/
theorem K1lim_eq_wLoc_add {ℓ R : ℝ} (hℓ : 0 < ℓ) {h : E3 → ℝ}
    (hW : ∀ z : E3, R < ‖z‖ → Submission.BoseGases.wScaled ℓ h z = 0) (w y : E3) :
    K1lim ℓ (Submission.BoseGases.wScaled ℓ h) w y
      = ((Submission.BoseGases.wLoc ℓ h 0 w y : ℝ) : ℂ)
        + chiChiImages ℓ (fun z => ((Submission.BoseGases.wScaled ℓ h z : ℝ) : ℂ)) w y
        + thetaPart ℓ (Submission.BoseGases.wScaled ℓ h) w y := by
  rw [← chiChiPart_wScaled ℓ h w y]
  exact K1lim_eq_parts (ℓ := ℓ) (R := R) hℓ hW w y

end Work.BoseBoxFock
