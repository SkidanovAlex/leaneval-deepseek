import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseK15.Derive
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseK15.chi_small_of_decay` — FS `eq:DecayPH` on `P_H^q`

FS `lem:DecaychiHat` in the two mode-indexed forms the `Q3Kernel` interface needs:

* `hatChi_small : |χ̂(ℓ q)| ≤ K₀ η` for every `q ∈ P_H^q = {‖q‖ ≥ ¼K_H⁻¹a⁻¹}`;
* `ccrX_small : |χ̂(ℓ(kmom q − kmom s))| ≤ K₀ η` for every `s ∈ supp f_L`, `q ∈ P_H^q`,

with `η = (K_ℓ⁻²𝓁)^{M̃}` (`Work.BoseB7A.eta`) and `K₀` the single absolute constant of
`Work.BoseK15.K15Input`.

## The arithmetic

Put `X = aK_H/ℓ`, `s = decayOrder = 26`; the hypothesis `heta` is `X^{2s} ≤ η`.

* `hatChi_small`: `q ∈ P_H^q` gives `‖ℓ q‖ ≥ ℓ/(4K_Ha) = (4X)⁻¹`, so with the decay
  `|χ̂(p)| ≤ Cchi (1+‖p‖²)^{-s}`,
  `|χ̂(ℓq)| ≤ Cchi ((4X)⁻¹)^{-2s} = Cchi·4^{2s}·X^{2s} ≤ K₀η`
  (`K₀_chi` bounds `Cchi·8^{2s} ≤ K₀`, hence `Cchi·4^{2s} ≤ K₀`).
* `ccrX_small`: `s ∈ supp f_L` gives `‖kmom s‖ ≤ K_L√(μa) ≤ (16K_Ha)⁻¹` (`hsmall`:
  the design's `con:KLKH`), while `‖kmom q‖ ≥ (4K_Ha)⁻¹`; hence
  `‖kmom q − kmom s‖ ≥ 3/(16K_Ha) ≥ (8K_Ha)⁻¹` and, scaling by `ℓ`,
  `‖ℓ(kmom q − kmom s)‖ ≥ ℓ/(8K_Ha) = (8X)⁻¹`.  The decay then gives
  `|ccrX s q| ≤ Cchi·8^{2s}·X^{2s} ≤ K₀η` — the factor `8^{2s}` being exactly the
  `8^{2·decayOrder}` of `K₀_chi` (`aScat_pos`, `KH_pos`, `ell_pos_E` are bundle
  fields, so the explicit `ha`/`hKH` of the request are redundant but harmless).

## Contents

* `two_mul_decayOrder`, `inv_pow_le_of_le`, `decay_absorb` — the arithmetic core
  (`decay_absorb`: the decay at a threshold `(cX)⁻¹`, with `C·c^{2s} ≤ K₀` and
  `X^{2s} ≤ η`, is at most `K₀η`).
* `chi_small_of_decay` — the requested lemma.
-/

noncomputable section

-- the request's explicit positivity hypotheses `ha`/`hKH` are redundant (the bundle
-- `K15Input` carries `aScat_pos`/`KH_pos` as fields), but the statement is kept verbatim.
set_option linter.unusedVariables false
set_option linter.unusedTactic false

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseK15

open Work.BoseB7 Work.BoseB7A

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}

/-- The chapter's decay order is `26`, so `2 · decayOrder = 52`. -/
lemma two_mul_decayOrder : 2 * decayOrder = 52 := rfl

/-- The elementary decay step: `((1+‖p‖²)^s)⁻¹ ≤ ((y²)^s)⁻¹` for `0 < y ≤ ‖p‖`. -/
lemma inv_pow_le_of_le {p : ℝ³} {y : ℝ} (hy : 0 < y) (h : y ≤ ‖p‖) :
    (((1 : ℝ) + ‖p‖ ^ 2) ^ decayOrder)⁻¹ ≤ ((y ^ 2) ^ decayOrder)⁻¹ := by
  have h1 : y ^ 2 ≤ 1 + ‖p‖ ^ 2 := by nlinarith [norm_nonneg p]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h1 decayOrder)

/-- **The absorption core.**  If `C ≥ 0`, `C·c^{2s} ≤ K₀`, `X > 0`, `X^{2s} ≤ η` and
`(cX)⁻¹ ≤ y`, then `C·((1+y²)^s)⁻¹ ≤ K₀η` with `s = decayOrder`.

(So a momentum threshold `(cX)⁻¹` for `ℓ·(momentum)` is absorbed by the constant
`c^{2·decayOrder}` of `K₀_chi`; for `hatChi_small` the threshold is `(4X)⁻¹` with
`4^{2s} ≤ 8^{2s}`, for `ccrX_small` it is `(8X)⁻¹`, matching `K₀_chi` exactly.) -/
lemma decay_absorb {C K₀ X η y c : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hK : C * c ^ (2 * decayOrder) ≤ K₀) (hX : 0 < X) (hXη : X ^ (2 * decayOrder) ≤ η)
    (hy : 1 / (c * X) ≤ y) :
    C * ((1 + y ^ 2) ^ decayOrder)⁻¹ ≤ K₀ * η := by
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  have hK0 : 0 ≤ K₀ := le_trans (by positivity) hK
  -- `(1+y²)^s ≥ y^{2s}`
  have h52 : y ^ (2 * decayOrder) ≤ (1 + y ^ 2) ^ decayOrder := by
    have h : (y ^ 2) ^ decayOrder ≤ (1 + y ^ 2) ^ decayOrder :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) decayOrder
    rwa [← pow_mul] at h
  have h1 : ((1 + y ^ 2) ^ decayOrder)⁻¹ ≤ (y ^ (2 * decayOrder))⁻¹ :=
    inv_anti₀ (by positivity) h52
  have h2 : (y ^ (2 * decayOrder))⁻¹ ≤ (c * X) ^ (2 * decayOrder) := by
    have h3 : (1 / (c * X)) ^ (2 * decayOrder) ≤ y ^ (2 * decayOrder) :=
      pow_le_pow_left₀ (by positivity) hy (2 * decayOrder)
    have h4 : (y ^ (2 * decayOrder))⁻¹ ≤ ((1 / (c * X)) ^ (2 * decayOrder))⁻¹ :=
      inv_anti₀ (by positivity) h3
    have h5 : ((1 / (c * X)) ^ (2 * decayOrder))⁻¹ = (c * X) ^ (2 * decayOrder) := by
      rw [← inv_pow, inv_div]
      simp
    rwa [h5] at h4
  calc C * ((1 + y ^ 2) ^ decayOrder)⁻¹ ≤ C * (c * X) ^ (2 * decayOrder) :=
        mul_le_mul_of_nonneg_left (le_trans h1 h2) hC
    _ = (C * c ^ (2 * decayOrder)) * X ^ (2 * decayOrder) := by rw [mul_pow]; ring
    _ ≤ K₀ * X ^ (2 * decayOrder) := mul_le_mul_of_nonneg_right hK (by positivity)
    _ ≤ K₀ * η := mul_le_mul_of_nonneg_left hXη hK0

theorem chi_small_of_decay {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : Work.BoseB7.FockData Mode} {T : Work.BoseB7A.TildeData F} {E : Work.BoseB7.Q3Env Mode}
    {K₀ : ℝ} (h : Work.BoseK15.K15Input K₀ F T E)
    (ha : 0 < E.aScat) (hKH : 0 < E.KH)
    (heta : (E.aScat * E.KH / E.ell) ^ (2 * Work.BoseK15.decayOrder) ≤ Work.BoseB7A.eta E)
    (hsmall : E.KL * Real.sqrt (E.mu * E.aScat) * (E.KH * E.aScat) ≤ 1 / 16) :
    (∀ q : Mode, F.PHq E.KH E.aScat q → |E.hatChi q| ≤ K₀ * Work.BoseB7A.eta E) ∧
    (∀ s q : Mode, E.fL s ≠ 0 → F.PHq E.KH E.aScat q → |T.ccrX s q| ≤ K₀ * Work.BoseB7A.eta E) := by
  have hell : 0 < E.ell := h.ell_pos_E
  have hX : 0 < E.aScat * E.KH / E.ell := by positivity
  refine ⟨?_, ?_⟩
  · -- `hatChi_small`: threshold `1/(4X)`, constant `4^{2s} ≤ 8^{2s}` from `K₀_chi`
    intro q hq
    have hnorm : 1 / (4 * E.KH * E.aScat) ≤ ‖h.kmom q‖ := by
      have h' := hq
      rw [Work.BoseB7.FockData.PHq, h.kmom_eq q] at h'
      exact h'
    have hy : 1 / (4 * (E.aScat * E.KH / E.ell)) ≤ ‖E.ell • h.kmom q‖ := by
      rw [norm_smul, Real.norm_of_nonneg hell.le]
      have he : 1 / (4 * (E.aScat * E.KH / E.ell)) = E.ell * (1 / (4 * E.KH * E.aScat)) := by
        first | (field_simp; ring) | field_simp
      rw [he]
      exact mul_le_mul_of_nonneg_left hnorm hell.le
    have hK4 : h.Cchi * 4 ^ (2 * decayOrder) ≤ K₀ := by
      have h48 : (4 : ℝ) ^ (2 * decayOrder) ≤ 8 ^ (2 * decayOrder) :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) _
      exact le_trans (mul_le_mul_of_nonneg_left h48 h.Cchi_nonneg) h.K₀_chi
    have hcore := decay_absorb (C := h.Cchi) (K₀ := K₀) (X := E.aScat * E.KH / E.ell)
      (η := eta E) (y := ‖E.ell • h.kmom q‖) (c := 4) (by norm_num)
      h.Cchi_nonneg hK4 hX heta hy
    rw [h.hatChi_eq q]
    exact le_trans (h.hatChi_abs_le (E.ell • h.kmom q)) hcore
  · -- `ccrX_small`: threshold `1/(8X)`, matching `K₀_chi` exactly
    intro s q hs hq
    have hnorm : 1 / (4 * E.KH * E.aScat) ≤ ‖h.kmom q‖ := by
      have h' := hq
      rw [Work.BoseB7.FockData.PHq, h.kmom_eq q] at h'
      exact h'
    have hsle : ‖h.kmom s‖ ≤ E.KL * Real.sqrt (E.mu * E.aScat) :=
      h.fL_supp (h.kmom s) (by rwa [h.fL_eq s] at hs)
    have hsle16 : ‖h.kmom s‖ ≤ 1 / (16 * E.KH * E.aScat) := by
      have h16 : 0 < 16 * E.KH * E.aScat := by positivity
      have h2 : E.KL * Real.sqrt (E.mu * E.aScat) ≤ 1 / (16 * E.KH * E.aScat) := by
        rw [le_div_iff₀ h16]
        nlinarith [hsmall]
      exact le_trans hsle h2
    have hdiff : 1 / (8 * E.KH * E.aScat) ≤ ‖h.kmom q - h.kmom s‖ := by
      have h4 : |‖h.kmom q‖ - ‖h.kmom s‖| ≤ ‖h.kmom q - h.kmom s‖ :=
        abs_norm_sub_norm_le _ _
      have h3 : 1 / (8 * E.KH * E.aScat) ≤ ‖h.kmom q‖ - ‖h.kmom s‖ := by
        have hA : 1 / (4 * E.KH * E.aScat) - 1 / (16 * E.KH * E.aScat)
            ≤ ‖h.kmom q‖ - ‖h.kmom s‖ := by linarith
        have hB : 1 / (8 * E.KH * E.aScat)
            ≤ 1 / (4 * E.KH * E.aScat) - 1 / (16 * E.KH * E.aScat) := by
          field_simp
          norm_num
        linarith
      linarith [h3, le_abs_self (‖h.kmom q‖ - ‖h.kmom s‖), h4]
    have hy : 1 / (8 * (E.aScat * E.KH / E.ell)) ≤ ‖E.ell • (h.kmom q - h.kmom s)‖ := by
      rw [norm_smul, Real.norm_of_nonneg hell.le]
      have he : 1 / (8 * (E.aScat * E.KH / E.ell))
          = E.ell * (1 / (8 * E.KH * E.aScat)) := by
        first | (field_simp; ring) | field_simp
      rw [he]
      exact mul_le_mul_of_nonneg_left hdiff hell.le
    have hcore := decay_absorb (C := h.Cchi) (K₀ := K₀) (X := E.aScat * E.KH / E.ell)
      (η := eta E) (y := ‖E.ell • (h.kmom q - h.kmom s)‖) (c := 8) (by norm_num)
      h.Cchi_nonneg h.K₀_chi hX heta hy
    rw [h.ccrX_eq s q]
    exact le_trans (h.hatChi_abs_le (E.ell • (h.kmom q - h.kmom s))) hcore

end Work.BoseK15
