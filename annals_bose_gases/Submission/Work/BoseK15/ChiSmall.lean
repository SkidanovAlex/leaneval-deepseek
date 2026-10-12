import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseK15.Derive
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseK15.ChiSmall` — `hatChi_small` and `ccrX_small` (K2)

FS `eq:DecayPH`: on the quarter region `P_H^q = {‖q‖ ≥ ¼K_H^{-1}a^{-1}}` the
θ/χ overlap is of order `η = (K_ℓ^{-2}𝓁)^{M̃}`:

    `|χ̂(ℓq)| ≤ Cχ·(ℓ‖q‖)^{-2s} ≤ Cχ·4^{2s}·n^{2s} ≤ K₀·η`

with `s = decayOrder = 26`, `n = aK_H/ℓ` and the arithmetic `n^{2s} ≤ η`
(`Work.BoseK15.arith_KH_a_div_ell_pow_le_eta`: `aK_H/ℓ = X^{103/4}` and
`(K_ℓ^{-2}𝓁)^{M̃} = X^{1236}`, while `2s·103/4 = 1339 ≥ 1236`).

`ccrX_small` is the same statement for the cross commutator
`ccrX s q = χ̂(ℓ(kmom q − kmom s))`: `s ∈ supp f_L ⊆ P_L` contributes at most
`K_L√(μa)` and `‖kmom q‖ ≥ 1/(4K_Ha)`, so the difference is at least `1/(8K_Ha)`
(`con:KLKH`, S1 of the design's smallness list), and the decay gives
`Cχ·8^{2s}·n^{2s} ≤ K₀·η`.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

set_option maxRecDepth 4000

namespace Work.BoseK15

open Work.BoseB7 Work.BoseB7A

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}

namespace K15Input

/-- The generic decay step: `((1+‖p‖²)^s)⁻¹ ≤ ((y²)^s)⁻¹` for `0 < y ≤ ‖p‖`. -/
lemma inv_pow_le_of_le {p : ℝ³} {y : ℝ} (hy : 0 < y) (h : y ≤ ‖p‖) :
    (((1 : ℝ) + ‖p‖ ^ 2) ^ decayOrder)⁻¹ ≤ ((y ^ 2) ^ decayOrder)⁻¹ := by
  have h1 : y ^ 2 ≤ 1 + ‖p‖ ^ 2 := by nlinarith [norm_nonneg p]
  have h2 : 0 < (y ^ 2) ^ decayOrder := by positivity
  have h3 : 0 < ((1 : ℝ) + ‖p‖ ^ 2) ^ decayOrder := by positivity
  exact (inv_le_inv₀ h3 h2).mpr
    (pow_le_pow_left₀ (show (0:ℝ) ≤ y ^ 2 by positivity) h1 decayOrder)

/-- `(((4n)^{-1})²)^s` inverted is `4^{2s}·n^{2s}`. -/
lemma pow_inv_four (n : ℝ) :
    (((((4 * n)⁻¹ : ℝ)) ^ 2) ^ decayOrder)⁻¹
      = 4 ^ (2 * decayOrder) * n ^ (2 * decayOrder) := by
  rw [← pow_mul, inv_pow, inv_inv, mul_pow]

/-- `(((8n)^{-1})²)^s` inverted is `8^{2s}·n^{2s}`. -/
lemma pow_inv_eight (n : ℝ) :
    (((((8 * n)⁻¹ : ℝ)) ^ 2) ^ decayOrder)⁻¹
      = 8 ^ (2 * decayOrder) * n ^ (2 * decayOrder) := by
  rw [← pow_mul, inv_pow, inv_inv, mul_pow]

/-- `ℓ/(4K_Ha) = (4·(aK_H/ℓ))⁻¹`. -/
lemma ell_div_KHa (h : K15Input K₀ F T E) :
    E.ell / (4 * E.KH * E.aScat) = (4 * (E.aScat * E.KH / E.ell))⁻¹ := by
  have hell : E.ell ≠ 0 := ne_of_gt h.ell_pos_E
  have ha : E.aScat ≠ 0 := ne_of_gt h.aScat_pos
  have hKH : E.KH ≠ 0 := ne_of_gt h.KH_pos
  first | (field_simp; ring) | field_simp

/-- `ℓ/(8K_Ha) = (8·(aK_H/ℓ))⁻¹`. -/
lemma ell_div_KHa_eight (h : K15Input K₀ F T E) :
    E.ell / (8 * E.KH * E.aScat) = (8 * (E.aScat * E.KH / E.ell))⁻¹ := by
  have hell : E.ell ≠ 0 := ne_of_gt h.ell_pos_E
  have ha : E.aScat ≠ 0 := ne_of_gt h.aScat_pos
  have hKH : E.KH ≠ 0 := ne_of_gt h.KH_pos
  first | (field_simp; ring) | field_simp

/-- **`hatChi_small` (FS `eq:DecayPH`).** -/
theorem hatChi_small_holds (h : K15Input K₀ F T E)
    (heta : (E.aScat * E.KH / E.ell) ^ (2 * decayOrder) ≤ eta E)
    (q : Mode) (hq : F.PHq E.KH E.aScat q) : |E.hatChi q| ≤ K₀ * eta E := by
  have ha : 0 < E.aScat := h.aScat_pos
  have hKH : 0 < E.KH := h.KH_pos
  have hell : 0 < E.ell := h.ell_pos_E
  have hn : 0 < E.aScat * E.KH / E.ell := by positivity
  have hnorm : 1 / (4 * E.KH * E.aScat) ≤ ‖h.kmom q‖ := by
    have h' := hq
    rw [Work.BoseB7.FockData.PHq, h.kmom_eq q] at h'
    exact h'
  have hy : E.ell / (4 * E.KH * E.aScat) ≤ ‖E.ell • h.kmom q‖ := by
    rw [norm_smul, Real.norm_of_nonneg hell.le]
    have he : E.ell / (4 * E.KH * E.aScat) = E.ell * (1 / (4 * E.KH * E.aScat)) := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hnorm hell.le
  have hstep := inv_pow_le_of_le (p := E.ell • h.kmom q) (by positivity) hy
  rw [h.hatChi_eq q]
  calc |corpusBox.hatChi (E.ell • h.kmom q)|
      ≤ h.Cchi * (((1 : ℝ) + ‖E.ell • h.kmom q‖ ^ 2) ^ decayOrder)⁻¹ :=
        h.hatChi_abs_le _
    _ ≤ h.Cchi * (((E.ell / (4 * E.KH * E.aScat)) ^ 2) ^ decayOrder)⁻¹ :=
        mul_le_mul_of_nonneg_left hstep h.Cchi_nonneg
    _ = h.Cchi * 4 ^ (2 * decayOrder) * (E.aScat * E.KH / E.ell) ^ (2 * decayOrder) := by
        rw [h.ell_div_KHa, pow_inv_four]; ring
    _ ≤ h.Cchi * 4 ^ (2 * decayOrder) * eta E :=
        mul_le_mul_of_nonneg_left heta (mul_nonneg h.Cchi_nonneg (by positivity))
    _ ≤ K₀ * eta E := by
        have h4 : (4 : ℝ) ^ (2 * decayOrder) ≤ 8 ^ (2 * decayOrder) :=
          pow_le_pow_left₀ (by norm_num) (by norm_num) _
        have hC : h.Cchi * 4 ^ (2 * decayOrder) ≤ K₀ :=
          le_trans (mul_le_mul_of_nonneg_left h4 h.Cchi_nonneg) h.K₀_chi
        have heta0 : 0 ≤ eta E := h.eta_nonneg
        calc h.Cchi * 4 ^ (2 * decayOrder) * eta E
            = (h.Cchi * 4 ^ (2 * decayOrder)) * eta E := by ring
          _ ≤ K₀ * eta E := mul_le_mul_of_nonneg_right hC heta0

/-- **`ccrX_small`.** -/
theorem ccrX_small_holds (h : K15Input K₀ F T E)
    (heta : (E.aScat * E.KH / E.ell) ^ (2 * decayOrder) ≤ eta E)
    (hsmall : E.KL * Real.sqrt (E.mu * E.aScat) * (E.KH * E.aScat) ≤ 1 / 16) :
    ∀ s q : Mode, E.fL s ≠ 0 → F.PHq E.KH E.aScat q → |T.ccrX s q| ≤ K₀ * eta E := by
  intro s q hs hq
  have ha : 0 < E.aScat := h.aScat_pos
  have hKH : 0 < E.KH := h.KH_pos
  have hell : 0 < E.ell := h.ell_pos_E
  have hX : 0 < E.KH * E.aScat := mul_pos hKH ha
  have hn : 0 < E.aScat * E.KH / E.ell := by positivity
  have hnorm : 1 / (4 * E.KH * E.aScat) ≤ ‖h.kmom q‖ := by
    have h' := hq
    rw [Work.BoseB7.FockData.PHq, h.kmom_eq q] at h'
    exact h'
  have hsle : ‖h.kmom s‖ ≤ E.KL * Real.sqrt (E.mu * E.aScat) :=
    h.fL_supp _ (by rwa [h.fL_eq s] at hs)
  have hsle16 : ‖h.kmom s‖ ≤ 1 / (16 * E.KH * E.aScat) := by
    have h16 : 0 < 16 * E.KH * E.aScat := by positivity
    have h2 : E.KL * Real.sqrt (E.mu * E.aScat) ≤ 1 / (16 * E.KH * E.aScat) := by
      rw [le_div_iff₀ h16]
      nlinarith [hsmall]
    exact le_trans hsle h2
  have hdiff : 1 / (8 * E.KH * E.aScat) ≤ ‖h.kmom q - h.kmom s‖ := by
    have h4 : |‖h.kmom q‖ - ‖h.kmom s‖| ≤ ‖h.kmom q - h.kmom s‖ :=
      abs_norm_sub_norm_le _ _
    have heq : 1 / (4 * E.KH * E.aScat) - 1 / (16 * E.KH * E.aScat)
        = 3 / (16 * E.KH * E.aScat) := by
      have h1 : (4 * E.KH * E.aScat) ≠ 0 := by positivity
      have h2 : (16 * E.KH * E.aScat) ≠ 0 := by positivity
      field_simp
      ring
    have h3 : 1 / (8 * E.KH * E.aScat) ≤ 3 / (16 * E.KH * E.aScat) := by
      have h2 : (1:ℝ) / (8 * E.KH * E.aScat) = 2 / (16 * E.KH * E.aScat) := by
        have h1 : (8 * E.KH * E.aScat) ≠ 0 := by positivity
        have h4 : (16 * E.KH * E.aScat) ≠ 0 := by positivity
        field_simp
        ring
      rw [h2]
      exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
    have h5 : 1 / (8 * E.KH * E.aScat) ≤ ‖h.kmom q‖ - ‖h.kmom s‖ := by
      have h6 : 1 / (4 * E.KH * E.aScat) - 1 / (16 * E.KH * E.aScat)
          ≤ ‖h.kmom q‖ - ‖h.kmom s‖ := by linarith
      linarith [h3, h6, heq]
    calc 1 / (8 * E.KH * E.aScat) ≤ ‖h.kmom q‖ - ‖h.kmom s‖ := h5
      _ ≤ |‖h.kmom q‖ - ‖h.kmom s‖| := le_abs_self _
      _ ≤ ‖h.kmom q - h.kmom s‖ := h4
  have hy : E.ell / (8 * E.KH * E.aScat) ≤ ‖E.ell • (h.kmom q - h.kmom s)‖ := by
    rw [norm_smul, Real.norm_of_nonneg hell.le]
    have he : E.ell / (8 * E.KH * E.aScat) = E.ell * (1 / (8 * E.KH * E.aScat)) := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hdiff hell.le
  have hstep := inv_pow_le_of_le (p := E.ell • (h.kmom q - h.kmom s)) (by positivity) hy
  rw [h.ccrX_eq s q]
  calc |corpusBox.hatChi (E.ell • (h.kmom q - h.kmom s))|
      ≤ h.Cchi * (((1 : ℝ) + ‖E.ell • (h.kmom q - h.kmom s)‖ ^ 2) ^ decayOrder)⁻¹ :=
        h.hatChi_abs_le _
    _ ≤ h.Cchi * (((E.ell / (8 * E.KH * E.aScat)) ^ 2) ^ decayOrder)⁻¹ :=
        mul_le_mul_of_nonneg_left hstep h.Cchi_nonneg
    _ = h.Cchi * 8 ^ (2 * decayOrder) * (E.aScat * E.KH / E.ell) ^ (2 * decayOrder) := by
        rw [h.ell_div_KHa_eight, pow_inv_eight]; ring
    _ ≤ h.Cchi * 8 ^ (2 * decayOrder) * eta E :=
        mul_le_mul_of_nonneg_left heta (mul_nonneg h.Cchi_nonneg (by positivity))
    _ ≤ K₀ * eta E := by
        have heta0 : 0 ≤ eta E := h.eta_nonneg
        calc h.Cchi * 8 ^ (2 * decayOrder) * eta E
            = (h.Cchi * 8 ^ (2 * decayOrder)) * eta E := by ring
          _ ≤ K₀ * eta E := mul_le_mul_of_nonneg_right h.K₀_chi heta0

end K15Input

end Work.BoseK15
