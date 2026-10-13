import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.Decomp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

/-! ## Elementary facts about `λ_m = 2m(2m+5)`, about `s2 θ = sin 2θ`, and the
comparison core of the summability estimate. -/

private lemma flam_pos {m : ℕ} (hm : 1 ≤ m) : 0 < Gegenbauer.lam m := by
  have h1 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  simp only [Gegenbauer.lam]
  nlinarith

private lemma flam_ge_one {m : ℕ} (hm : 1 ≤ m) : 1 ≤ Gegenbauer.lam m := by
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  simp only [Gegenbauer.lam]
  nlinarith

private lemma flam_ge_four_sq (m : ℕ) : 4 * (m : ℝ) ^ 2 ≤ Gegenbauer.lam m := by
  have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  simp only [Gegenbauer.lam]
  nlinarith

/-- The comparison core: `(2m+1)·m² ≤ λ_m²` for `m ≥ 1`.  (`λ_m = 4m² + 10m`, so
`λ_m² ≥ (4m²)² = 16m⁴ ≥ 3m³ = (2m+1)m²` once `m ≥ 1`.) -/
private lemma flam_sq_bound {m : ℕ} (hm : 1 ≤ m) :
    (2 * (m : ℝ) + 1) * (m : ℝ) ^ 2 ≤ (Gegenbauer.lam m) ^ 2 := by
  have hx1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  simp only [Gegenbauer.lam]
  nlinarith [hx1, sq_nonneg ((m : ℝ)), sq_nonneg (2 * (m : ℝ) + 5)]

private lemma fs2_pos_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Construction.s2 θ := by
  rw [Construction.s2_eq, Real.sin_two_mul]
  exact mul_pos
    (mul_pos two_pos (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])))
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)

/-- **Summability of `Σ_m b_m λ_m^{-j} G_m Q_m(θ)`.**

The `m`-th summand is bounded by
`C/(λ_m √(2m+1)) · λ_m^{-j} · Cg/λ_m · (C (2m+1)/sin 2θ) ≤ (Cb Cg C/sin 2θ) · (2m+1)/λ_m²`
(since `λ_m ≥ 1` and `j ≥ 0`), and `(2m+1)/λ_m² ≤ m^{-2}` for `m ≥ 1`; the `m = 0` term
vanishes because `b_0 = 0`. -/
theorem summable_bmode_lam_inv_pow_G_Qm (ψ : ℝ → ℝ) (θ : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ'| ≤ C * (2 * (m : ℝ) + 1))
    (Cg : ℝ) (hCg : 0 < Cg) (G : ℕ → ℝ)
    (hG : ∀ m : ℕ, 1 ≤ m → |G m| ≤ Cg / Work.FTS.PhiStar.Gegenbauer.lam m) :
    Summable (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ
      * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ j * G m * Work.FTS.PhiStar.FlatWAux.Qm m θ) := by
  obtain ⟨Cb, hCb, hdec⟩ := hdec
  obtain ⟨Cr, hCr, hgr⟩ := hgr
  have hs2pos : 0 < Construction.s2 θ := fs2_pos_of_mem hθ
  have hs2nonneg : (0 : ℝ) ≤ Construction.s2 θ := le_of_lt hs2pos
  have hθI : θ ∈ Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  set K : ℝ := Cb * Cg * Cr / Construction.s2 θ with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    exact div_pos (mul_pos (mul_pos hCb hCg) hCr) hs2pos
  refine Summable.of_norm_bounded (g := fun m : ℕ => K * (m : ℝ) ^ (-(2 : ℝ))) ?_ ?_
  · exact ((Real.summable_nat_rpow (p := (-(2 : ℝ)))).mpr (by norm_num)).mul_left K
  · intro m
    by_cases hm : m = 0
    · subst hm
      simp only [hb0, zero_mul, norm_zero]
      rw [Nat.cast_zero, Real.zero_rpow (by norm_num : (-(2 : ℝ)) ≠ 0), mul_zero]
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hx1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hxpos : (0 : ℝ) < (m : ℝ) := by linarith
      have hLpos : 0 < Gegenbauer.lam m := flam_pos hm1
      have hL1 : 1 ≤ Gegenbauer.lam m := flam_ge_one hm1
      have hLsqpos : 0 < (Gegenbauer.lam m) ^ 2 := pow_pos hLpos 2
      have hx2pos : 0 < (m : ℝ) ^ 2 := pow_pos hxpos 2
      have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (2 * (m : ℝ) + 1) := by
        rw [Real.one_le_sqrt]; linarith
      have hu1 : (0 : ℝ) ≤ 2 * (m : ℝ) + 1 := by linarith
      have hn1 : (0 : ℝ) ≤ Cb / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) :=
        div_nonneg (le_of_lt hCb) (mul_nonneg (le_of_lt hLpos) (Real.sqrt_nonneg _))
      have hn3 : (0 : ℝ) ≤ Cg / Gegenbauer.lam m :=
        div_nonneg (le_of_lt hCg) (le_of_lt hLpos)
      have hn4 : (0 : ℝ) ≤ Cr * (2 * (m : ℝ) + 1) / Construction.s2 θ :=
        div_nonneg (mul_nonneg (le_of_lt hCr) hu1) hs2nonneg
      have hQm : |Qm m θ| ≤ Cr * (2 * (m : ℝ) + 1) / Construction.s2 θ := by
        simp only [Qm]
        rw [abs_div, abs_of_pos hs2pos]
        exact div_le_div_of_nonneg_right (hgr m θ hθI) hs2nonneg
      have hA2 : ((Gegenbauer.lam m)⁻¹) ^ j ≤ 1 :=
        pow_le_one₀ (inv_nonneg.mpr (le_of_lt hLpos)) (inv_le_one_of_one_le₀ hL1)
      have hpow_nonneg : (0 : ℝ) ≤ ((Gegenbauer.lam m)⁻¹) ^ j :=
        pow_nonneg (inv_nonneg.mpr (le_of_lt hLpos)) j
      -- the four factors, bounded one by one
      have hprod1 : |Series.bmode m ψ| * ((Gegenbauer.lam m)⁻¹) ^ j * |G m| * |Qm m θ|
          ≤ (Cb / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) * 1
              * (Cg / Gegenbauer.lam m) * (Cr * (2 * (m : ℝ) + 1) / Construction.s2 θ) :=
        mul_le_mul
          (mul_le_mul (mul_le_mul (hdec m hm1) hA2 hpow_nonneg hn1) (hG m hm1)
            (abs_nonneg _) (mul_nonneg hn1 zero_le_one))
          hQm (abs_nonneg _) (mul_nonneg (mul_nonneg hn1 zero_le_one) hn3)
      -- drop the `√(2m+1)`
      have hprod2 : (Cb / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) * 1
              * (Cg / Gegenbauer.lam m) * (Cr * (2 * (m : ℝ) + 1) / Construction.s2 θ)
          ≤ (Cb / Gegenbauer.lam m) * (Cg / Gegenbauer.lam m)
              * (Cr * (2 * (m : ℝ) + 1) / Construction.s2 θ) := by
        have hcd : Cb / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
            ≤ Cb / Gegenbauer.lam m :=
          div_le_div_of_nonneg_left (le_of_lt hCb) hLpos (by nlinarith [hsqrt1, hLpos])
        calc (Cb / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) * 1
                * (Cg / Gegenbauer.lam m) * (Cr * (2 * (m : ℝ) + 1) / Construction.s2 θ)
            = (Cb / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
                * ((Cg / Gegenbauer.lam m)
                    * (Cr * (2 * (m : ℝ) + 1) / Construction.s2 θ)) := by ring
          _ ≤ (Cb / Gegenbauer.lam m)
                * ((Cg / Gegenbauer.lam m)
                    * (Cr * (2 * (m : ℝ) + 1) / Construction.s2 θ)) :=
              mul_le_mul_of_nonneg_right hcd (mul_nonneg hn3 hn4)
          _ = (Cb / Gegenbauer.lam m) * (Cg / Gegenbauer.lam m)
                * (Cr * (2 * (m : ℝ) + 1) / Construction.s2 θ) := by ring
      -- the `m`-decay of the remaining factor
      have hkey : (2 * (m : ℝ) + 1) / (Gegenbauer.lam m) ^ 2 ≤ (1 : ℝ) / (m : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ hLsqpos hx2pos]
        nlinarith [flam_sq_bound hm1]
      have hprod3 : (Cb / Gegenbauer.lam m) * (Cg / Gegenbauer.lam m)
              * (Cr * (2 * (m : ℝ) + 1) / Construction.s2 θ) ≤ K * (m : ℝ) ^ (-(2 : ℝ)) := by
        have hfac : (Cb / Gegenbauer.lam m) * (Cg / Gegenbauer.lam m)
              * (Cr * (2 * (m : ℝ) + 1) / Construction.s2 θ)
            = K * ((2 * (m : ℝ) + 1) / (Gegenbauer.lam m) ^ 2) := by
          rw [hKdef]
          simp only [div_eq_mul_inv]
          rw [← inv_pow]
          ring
        rw [hfac]
        calc K * ((2 * (m : ℝ) + 1) / (Gegenbauer.lam m) ^ 2)
            ≤ K * ((1 : ℝ) / (m : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_left hkey (le_of_lt hKpos)
          _ = K * (m : ℝ) ^ (-(2 : ℝ)) := by
              rw [one_div, show (-(2 : ℝ)) = -(((2 : ℕ) : ℝ)) by norm_num,
                  Real.rpow_neg (le_of_lt hxpos), Real.rpow_natCast]
      have hmain : |Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ j * G m * Qm m θ|
          ≤ K * (m : ℝ) ^ (-(2 : ℝ)) := by
        rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_inv, abs_of_pos hLpos]
        exact le_trans hprod1 (le_trans hprod2 hprod3)
      simpa only [Real.norm_eq_abs] using hmain

end Work.FTS.PhiStar.FlatWAux
