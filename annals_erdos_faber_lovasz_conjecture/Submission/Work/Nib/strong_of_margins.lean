import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Submission.Work.Nib.Vocab

/-!
# `Work.Nib.strong_of_margins`

The seeded margin bundle `ErdosFaberLovaszConjecture.NibbleMargins` records the
paper's asymptotic hierarchy `1/n, 1/r, ξ, β^{1/2} ≪ γ ≪ ρ, ε`, but the proof of
`lem:nibble2` (and hence the §7 assembly, see
`Submission/Work/Nib/assemblyParams_exists.lean`) needs the *`γρε`-relative*
hierarchy `1/r, ξ, β^{1/2} ≪ γρε` of
`ErdosFaberLovaszConjecture.NibbleMarginsStrong`.  This file bridges the two:
from the seeded bundle (applied at `2β, 2γ`) plus the numeric side conditions
that the §12 layer supplies, we obtain the corrected bundle.

The two numerical inputs doing the work are

* `hγρabs : 1000 * (3γ/2) ≤ ρ_abs * ε`, i.e. `1500γ ≤ ρ_abs ε`, which turns the
  `≪ γ` fields into `≪ γρε` fields — note `hβ4` (`β ≤ γ⁴/10^12`) and
  `hγρabs` together give `β ≪ (γρε)²`, while the `hβr1`-bounds on `r₁` convert
  `β ≪ γ⁴` into `r₁ ≫ 1/β ≫ γ^{-4}`, which is what makes `γρε r₁ ≫ 1`;
* `hγρs : 10^6 * (2γ) ≤ ρ_abs`, used only through `hγρabs` on the `hγρε` field.
-/

set_option maxHeartbeats 1000000

namespace Work.Nib

theorem strong_of_margins {n : ℕ} {D β γ ε ρ ρ_abs ξ : ℝ} {r₁ : ℕ}
    (h : ErdosFaberLovaszConjecture.NibbleMargins n D r₁ (2 * β) (2 * γ) ε ρ_abs ξ)
    (hDlin : (n : ℝ) / 2 ≤ D) (hDgap : D ≤ (1 - ρ_abs) * (n : ℝ))
    (hβ4 : β ≤ γ ^ 4 / 10 ^ 12)
    (hγρs : 10 ^ 6 * (2 * γ) ≤ ρ_abs)
    (hξε1 : 10 ^ 12 * ξ ≤ 2 * γ * ρ_abs * ε)
    (hξε2 : ξ ≤ (2 * γ) ^ 2 / 10 ^ 8)
    (hn100 : 10 ^ 100 ≤ 2 * γ * ρ_abs * ε * (n : ℝ))
    (hnbig : 10 ^ 400 * ((ρ_abs⁻¹) ^ 6 + ((2 * γ)⁻¹) ^ 16 + (2 * γ * ρ_abs * ε)⁻¹
        + ((2 * γ * ρ_abs * ε)⁻¹) ^ 2 + (r₁ : ℝ)) ≤ (n : ℝ))
    (hβr1 : 16 ≤ (β / 2) * (r₁ : ℝ))
    (hγρabs : 1000 * (3 * γ / 2) ≤ ρ_abs * ε)
    (hεsmall : 4000 * ε ≤ 1) (hγ1 : γ ≤ 1) :
    ErdosFaberLovaszConjecture.NibbleMarginsStrong n D r₁ (2 * β) (2 * γ) ε ρ_abs ξ := by
  -- ## Toolbox: positivity of the parameters, and the rearranged inputs
  have hβ0 : (0:ℝ) < β := by linarith only [h.hβ0]
  have hγ0 : (0:ℝ) < γ := by linarith only [h.hγ0]
  have hε0 : (0:ℝ) < ε := h.hε0
  have hρ0 : (0:ℝ) < ρ_abs := h.hρ0
  have hβnn : (0:ℝ) ≤ β := le_of_lt hβ0
  have hγnn : (0:ℝ) ≤ γ := le_of_lt hγ0
  have hρnn : (0:ℝ) ≤ ρ_abs := le_of_lt hρ0
  have hεnn : (0:ℝ) ≤ ε := le_of_lt hε0
  have hγ2le1 : γ^2 ≤ 1 := by nlinarith only [hγ1, hγnn]
  have hγ3leγ : γ^3 ≤ γ := by nlinarith only [hγ2le1, hγnn]
  have hγ4nn : (0:ℝ) ≤ γ^4 := by positivity
  -- the `γρε`-relative form of `γ ≪ ρε`
  have hγρabs' : (1500:ℝ) * γ ≤ ρ_abs * ε := by nlinarith only [hγρabs]
  -- `β ≤ γ⁴/10^{12}` as a product bound
  have hγ4β : 10^12 * β ≤ γ^4 := by
    have hh := hβ4
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 10^12)] at hh
    linarith only [hh]
  -- `r₁ ≫ 1/β`
  have hβr1' : (32:ℝ) ≤ β * (r₁:ℝ) := by nlinarith only [hβr1]
  -- so `γ⁴ r₁ ≫ 1`, the engine behind the two `r₁`-fields
  have hA : (32:ℝ) * 10^12 ≤ γ^4 * (r₁:ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hγ4β (Nat.cast_nonneg r₁)
    have h2 := mul_le_mul_of_nonneg_left hβr1' (by positivity : (0:ℝ) ≤ 10^12)
    nlinarith only [h1, h2]
  -- `γ³ ≤ 64 ρ ε`, used to cancel the `γ³` in the `10^{12} ≤ γρε r₁` field
  have hB : γ^3 ≤ 64 * ρ_abs * ε := by
    nlinarith only [hγρabs', hγ3leγ, hγnn, hρnn, hεnn]
  -- ## The fields of `NibbleMarginsStrong`
  -- `β ≪ (γρε)²`: from `10^{12}β ≤ γ⁴` and `γ ≤ ρε/1500`
  have fβ : 10^12 * (2*β) ≤ ((2*γ) * ρ_abs * ε)^2 := by
    have hXnn : (0:ℝ) ≤ (2*γ) * ρ_abs * ε := by positivity
    have hXge : (3000:ℝ)*γ^2 ≤ (2*γ) * ρ_abs * ε := by
      have h1 : (2*γ) * (1500*γ) ≤ (2*γ) * (ρ_abs*ε) :=
        mul_le_mul_of_nonneg_left hγρabs' (by positivity)
      nlinarith only [h1]
    have hsqnn : (0:ℝ) ≤ (3000:ℝ)*γ^2 := by positivity
    have hsq : ((3000:ℝ)*γ^2)^2 ≤ ((2*γ) * ρ_abs * ε)^2 := by
      nlinarith only [hXge, hXnn, hsqnn]
    have he : ((3000:ℝ)*γ^2)^2 = 9000000 * γ^4 := by ring
    have hA2 : 10^12 * (2*β) ≤ 9000000 * γ^4 := by nlinarith only [hγ4β, hγ4nn]
    linarith only [hsq, he, hA2]
  -- `2β ≤ (2γ)⁴/10^{12}`, immediate from `β ≤ γ⁴/10^{12}`
  have fβ4 : (2*β) ≤ (2*γ)^4 / 10^12 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 10^12)]
    have h2 : (2*γ)^4 = 16 * γ^4 := by ring
    rw [h2]
    nlinarith only [hγ4β, hγ4nn]
  -- `10^{12} ≤ γρε r₁`: `r₁ ≥ 32/β ≥ 32·10^{12}/γ⁴`, and `γ³ ≤ 64ρε`
  have fhr : 10^12 ≤ (2*γ) * ρ_abs * ε * (r₁:ℝ) := by
    have h2ρε : (0:ℝ) ≤ 2*(ρ_abs*ε) := by positivity
    have h3 : (32 * (10:ℝ)^12) * (2*(ρ_abs*ε)) ≤ (γ^4 * (r₁:ℝ)) * (2*(ρ_abs*ε)) :=
      mul_le_mul_of_nonneg_right hA h2ρε
    have h4 : 10^12 * γ^3 ≤ 32 * 10^12 * (2*(ρ_abs*ε)) := by
      have hh := mul_le_mul_of_nonneg_left hB (by positivity : (0:ℝ) ≤ 10^12)
      nlinarith only [hh]
    have hγ3pos : (0:ℝ) < γ^3 := by positivity
    have hkey : 10^12 * γ^3 ≤ ((2*γ) * ρ_abs * ε * (r₁:ℝ)) * γ^3 := by
      nlinarith only [h3, h4]
    exact (mul_le_mul_iff_of_pos_right hγ3pos).mp hkey
  -- `10^8 ≤ (2γ)² r₁`, from `γ⁴ r₁ ≥ 32·10^{12}` and `γ ≤ 1`
  have fhr2 : 10^8 ≤ (2*γ)^2 * (r₁:ℝ) := by
    have h10 : (10:ℝ)^8 ≤ 128 * 10^12 := by norm_num
    have h10nn : (0:ℝ) ≤ 10^8 := by positivity
    have h1 : (128:ℝ)*10^12 ≤ 4 * (γ^4 * (r₁:ℝ)) := by nlinarith only [hA]
    have h2 : 10^8 * γ^2 ≤ 128 * 10^12 := by nlinarith only [h10, hγ2le1, h10nn]
    have hγ2pos : (0:ℝ) < γ^2 := by positivity
    have hkey : 10^8 * γ^2 ≤ ((2*γ)^2 * (r₁:ℝ)) * γ^2 := by nlinarith only [h1, h2]
    exact (mul_le_mul_iff_of_pos_right hγ2pos).mp hkey
  -- `10 γ ≤ ρ ε`
  have fγρε : 10 * (2*γ) ≤ ρ_abs * ε := by nlinarith only [hγρabs', hγnn]
  -- `8(2β)D ≤ 2γρε n`: reduce to `16β ≤ 2γρε` via `D ≤ n`, then `β ≪ γ⁴`
  have fβD : 8 * (2*β) * D ≤ (2*γ) * ρ_abs * ε * (n:ℝ) := by
    have hDhigh : D ≤ (n:ℝ) := h.hDhigh
    have h1 : 8 * (2*β) * D ≤ 8 * (2*β) * (n:ℝ) := by nlinarith only [hDhigh, hβnn]
    have hnum : (16:ℝ) ≤ 3000 * 10^12 := by norm_num
    have hC : (16:ℝ) * γ^4 ≤ 10^12 * (2*γ*ρ_abs*ε) := by
      nlinarith only [hγρabs', hγ2le1, hnum, hγnn, hρnn, hεnn]
    have hβle : 16*β ≤ 2*γ*ρ_abs*ε := by
      have h3 : 16 * (10^12*β) ≤ 16 * γ^4 := mul_le_mul_of_nonneg_left hγ4β (by norm_num)
      have h4 : 16 * (10^12*β) ≤ 10^12 * (2*γ*ρ_abs*ε) := le_trans h3 hC
      have h5 : (16*β) * 10^12 ≤ (2*γ*ρ_abs*ε) * 10^12 := by nlinarith only [h4]
      exact (mul_le_mul_iff_of_pos_right (by norm_num : (0:ℝ) < 10^12)).mp h5
    have h6 : 8 * (2*β) * (n:ℝ) ≤ (2*γ) * ρ_abs * ε * (n:ℝ) := by
      have hnn : (0:ℝ) ≤ (n:ℝ) := by positivity
      nlinarith only [hβle, hnn]
    linarith only [h1, h6]
  exact
    { base := h
      hβ := fβ
      hβ4 := fβ4
      hξ := hξε1
      hξ2 := hξε2
      hr := fhr
      hr2 := fhr2
      hγρ := hγρs
      hγρε := fγρε
      hβD := fβD
      hn := hn100
      hε := hεsmall
      hDgap := hDgap
      hDlin := hDlin
      hnbig := hnbig }

end Work.Nib
