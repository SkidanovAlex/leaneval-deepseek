import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.Expansion
import Submission.Work.FTS.PhiStar.FlatWAux.ModeExpansion
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.Series.CmodeDecay

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

/-!
# `Work.FTS.PhiStar.FlatWAux.Decomp` — the decomposition of `psiSeries α (RemSource α ψ)/sin 2θ`

The source `RemSource α ψ = α²·phiA α·ψ` is separable, so the mode series of the solution is
`psiSeries α (RemSource α ψ) z θ = α² Σ_m b_m · radGreen α m (phiA α) z · eFam m θ`
(`ModeExpansion.psiSeries_remSource_eq_tsum`, `RemSetup.acoeff_RemSource`).  Dividing by
`sin 2θ = s2 θ` turns `eFam m θ` into the divided angular mode `Qm m θ`, and the `J`-fold
`1/λ_m`-expansion of the radial Green function (`hexp`) then separates the `m`-dependence into
the resummed angular profiles `Wt ψ j = Σ_m b_m λ_m^{-j} Qm m` plus one remainder series:

`psiSeries α (RemSource α ψ) z θ / s2 θ
   = α² ( Σ_{j<J} α^j (𝒜^j phiA α) z · Wt ψ (j+1) θ
          + α^J Σ_m b_m λ_m^{-J} radGreen α m (𝒜^J (phiA α)) z · Qm m θ )`.

The `m = 0` term drops out because `bmode 0 ψ = 0`, so the expansion hypothesis is only needed
for `m ≥ 1`.  Summability of the finitely many angular series and of the remainder (which is what
makes the rearrangement of the double sum legitimate) follows from the three decay hypotheses
`hdec`, `hQ0`, `hrem` by comparison with `Σ_m m^{-2}`.

## Pieces

* `fts_lam_pos`, `fts_lam_ge_one`, `fts_sq_le_nine`, `fts_m_sq_inv_lam_sq` — the elementary
  estimates for `λ_m = 2m(2m+5)` used in the summability comparisons;
* `summable_bm_lam_Qm`, `summable_bm_G_Qm` — the two summability criteria;
* `decomp_algebra` — the purely algebraic core of the reindexing;
* `tsum_term`, `tsum_tail` — the evaluation of the two `tsum`s after `tsum_finsetSum`;
* `decomp_pointwise` — the pointwise (in `m`) decomposition;
* `decomp_core` — the `tsum`-level statement, and `Decomp` its `psiSeries` form.
-/

/-! ## Elementary facts about `λ_m = 2m(2m+5)` -/

private lemma fts_lam_pos {m : ℕ} (hm : 1 ≤ m) : 0 < Gegenbauer.lam m := by
  have h1 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  simp only [Gegenbauer.lam]; nlinarith

private lemma fts_lam_ge_one {m : ℕ} (hm : 1 ≤ m) : 1 ≤ Gegenbauer.lam m := by
  have h1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  simp only [Gegenbauer.lam]; nlinarith

private lemma fts_sq_le_nine {m : ℕ} (hm : 1 ≤ m) : (2*(m:ℝ)+1)^2 ≤ 9*(m:ℝ)^2 := by
  have h1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  nlinarith

/-- `m² · λ_m^{-2} ≤ 4 m^{-2}` — the decay transfer from `λ_m ≥ 4m²`. -/
private lemma fts_m_sq_inv_lam_sq {m : ℕ} (hm : 1 ≤ m) :
    (m:ℝ)^2 * ((Gegenbauer.lam m)⁻¹)^2 ≤ 4 * (m:ℝ)^(-(2:ℝ)) := by
  have h1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hxpos : (0:ℝ) < (m:ℝ) := by linarith
  have hLpos : 0 < Gegenbauer.lam m := fts_lam_pos hm
  have hlamge : 4*(m:ℝ)^2 ≤ Gegenbauer.lam m := by
    have h0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    simp only [Gegenbauer.lam]; nlinarith
  have hp4 : (m:ℝ)^4 ≤ 4 * (Gegenbauer.lam m)^2 := by
    nlinarith [sq_nonneg (Gegenbauer.lam m)]
  rw [inv_pow, show (-(2:ℝ)) = -(((2:ℕ)):ℝ) by norm_num, Real.rpow_neg (le_of_lt hxpos),
    Real.rpow_natCast]
  field_simp
  nlinarith

private lemma tsum_div_tsum (f : ℕ → ℝ) (c : ℝ) : (∑' m : ℕ, f m) / c = ∑' m : ℕ, f m / c := by
  rw [div_eq_mul_inv]
  exact (tsum_mul_right (f := f) (a := c⁻¹)).symm

/-! ## Summability of the resummed angular series -/

/-- **Summability of the `j`-th resummed angular series.**  `|b_m| ≤ Cb/(λ_m √(2m+1))` and
`|Qm m θ| ≤ Cq (2m+1)²` give, using `λ_m ≥ 4m²` and `(2m+1)² ≤ 9m²`, the bound
`Cb Cq λ_m^{-(j+2)} (2m+1)² ≤ 36 Cb Cq m^{-2}`, and `Σ_m m^{-2}` converges. -/
private lemma summable_bm_lam_Qm (ψ : ℝ → ℝ) (θ : ℝ) (Cb Cq : ℝ)
    (hCb : 0 < Cb) (hCq : 0 < Cq) (hb0 : Series.bmode 0 ψ = 0)
    (hdec : ∀ m : ℕ, 1 ≤ m → |Series.bmode m ψ|
      ≤ Cb / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hQ0 : ∀ m : ℕ, 1 ≤ m → |Qm m θ| ≤ Cq * (2 * (m : ℝ) + 1) ^ 2)
    (j : ℕ) :
    Summable (fun m : ℕ => Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (j+1) * Qm m θ) := by
  refine Summable.of_norm_bounded (g := fun m : ℕ => (36 * Cb * Cq) * (m:ℝ)^(-(2:ℝ))) ?_ ?_
  · exact ((Real.summable_nat_rpow (p := (-(2:ℝ)))).mpr (by norm_num)).mul_left _
  · intro m
    by_cases hm : m = 0
    · subst hm
      simp only [hb0, zero_mul, norm_zero]
      rw [Nat.cast_zero, Real.zero_rpow (by norm_num : (-2:ℝ) ≠ 0), mul_zero]
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hx1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
      have hxpos : (0:ℝ) < (m:ℝ) := by linarith
      have hLpos : 0 < Gegenbauer.lam m := fts_lam_pos hm1
      have hL1 : 1 ≤ Gegenbauer.lam m := fts_lam_ge_one hm1
      have hs1 : 1 ≤ Real.sqrt (2*(m:ℝ)+1) := by rw [Real.one_le_sqrt]; linarith
      have hu2 : (2*(m:ℝ)+1)^2 ≤ 9*(m:ℝ)^2 := fts_sq_le_nine hm1
      have hkey := fts_m_sq_inv_lam_sq hm1
      have hCbdiv : Cb / (Gegenbauer.lam m * Real.sqrt (2*(m:ℝ)+1)) ≤ Cb / Gegenbauer.lam m :=
        div_le_div_of_nonneg_left (le_of_lt hCb) hLpos (by nlinarith [hs1, hLpos])
      have hpow2 : (Gegenbauer.lam m)⁻¹ ^ (j+2) ≤ (Gegenbauer.lam m)⁻¹ ^ 2 :=
        pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hL1) (Nat.le_add_left 2 j)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_inv, abs_of_pos hLpos]
      calc |Series.bmode m ψ| * (Gegenbauer.lam m)⁻¹ ^ (j+1) * |Qm m θ|
          ≤ (Cb / (Gegenbauer.lam m * Real.sqrt (2*(m:ℝ)+1)))
              * (Gegenbauer.lam m)⁻¹ ^ (j+1) * (Cq * (2*(m:ℝ)+1)^2) :=
            mul_le_mul (mul_le_mul (hdec m hm1) le_rfl (by positivity)
                (div_nonneg (le_of_lt hCb) (mul_nonneg (le_of_lt hLpos) (Real.sqrt_nonneg _))))
              (hQ0 m hm1) (abs_nonneg _) (by positivity)
        _ ≤ (Cb * (Gegenbauer.lam m)⁻¹ ^ 2) * (Cq * (9*(m:ℝ)^2)) := by
            refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
            · calc (Cb / (Gegenbauer.lam m * Real.sqrt (2*(m:ℝ)+1)))
                    * (Gegenbauer.lam m)⁻¹ ^ (j+1)
                  ≤ (Cb / Gegenbauer.lam m) * (Gegenbauer.lam m)⁻¹ ^ (j+1) :=
                    mul_le_mul_of_nonneg_right hCbdiv (by positivity)
                _ = Cb * (Gegenbauer.lam m)⁻¹ ^ (j+2) := by
                    rw [div_eq_mul_inv, pow_succ]; ring
                _ ≤ Cb * (Gegenbauer.lam m)⁻¹ ^ 2 :=
                    mul_le_mul_of_nonneg_left hpow2 (le_of_lt hCb)
            · exact mul_le_mul_of_nonneg_left hu2 (le_of_lt hCq)
        _ = 9*Cb*Cq * ((m:ℝ)^2 * ((Gegenbauer.lam m)⁻¹)^2) := by ring
        _ ≤ 9*Cb*Cq * (4 * (m:ℝ)^(-(2:ℝ))) := mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = 36*Cb*Cq * (m:ℝ)^(-(2:ℝ)) := by ring

/-- **Summability with an extra `λ_m^{-1}`-decaying radial factor.**  With
`|G m| ≤ Cg/λ_m` the summand is bounded by `Cb Cg Cq λ_m^{-2}(2m+1)² ≤ 36 Cb Cg Cq m^{-2}`. -/
private lemma summable_bm_G_Qm (ψ : ℝ → ℝ) (θ : ℝ) (Cb Cq Cg : ℝ)
    (hCb : 0 < Cb) (hCq : 0 < Cq) (hCg : 0 < Cg) (hb0 : Series.bmode 0 ψ = 0)
    (hdec : ∀ m : ℕ, 1 ≤ m → |Series.bmode m ψ|
      ≤ Cb / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hQ0 : ∀ m : ℕ, 1 ≤ m → |Qm m θ| ≤ Cq * (2 * (m : ℝ) + 1) ^ 2)
    (G : ℕ → ℝ)
    (hg : ∀ m : ℕ, 1 ≤ m → |G m| ≤ Cg / Gegenbauer.lam m) (k : ℕ) :
    Summable (fun m : ℕ => Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ k * G m * Qm m θ) := by
  refine Summable.of_norm_bounded (g := fun m : ℕ => (36 * Cb * Cg * Cq) * (m:ℝ)^(-(2:ℝ))) ?_ ?_
  · exact ((Real.summable_nat_rpow (p := (-(2:ℝ)))).mpr (by norm_num)).mul_left _
  · intro m
    by_cases hm : m = 0
    · subst hm
      simp only [hb0, zero_mul, norm_zero]
      rw [Nat.cast_zero, Real.zero_rpow (by norm_num : (-2:ℝ) ≠ 0), mul_zero]
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hx1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
      have hxpos : (0:ℝ) < (m:ℝ) := by linarith
      have hLpos : 0 < Gegenbauer.lam m := fts_lam_pos hm1
      have hL1 : 1 ≤ Gegenbauer.lam m := fts_lam_ge_one hm1
      have hs1 : 1 ≤ Real.sqrt (2*(m:ℝ)+1) := by rw [Real.one_le_sqrt]; linarith
      have hu2 : (2*(m:ℝ)+1)^2 ≤ 9*(m:ℝ)^2 := fts_sq_le_nine hm1
      have hkey := fts_m_sq_inv_lam_sq hm1
      have hCbdiv : Cb / (Gegenbauer.lam m * Real.sqrt (2*(m:ℝ)+1)) ≤ Cb / Gegenbauer.lam m :=
        div_le_div_of_nonneg_left (le_of_lt hCb) hLpos (by nlinarith [hs1, hLpos])
      have hpowk : (Gegenbauer.lam m)⁻¹ ^ k ≤ 1 :=
        pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hL1)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow, abs_inv, abs_of_pos hLpos]
      calc |Series.bmode m ψ| * (Gegenbauer.lam m)⁻¹ ^ k * |G m| * |Qm m θ|
          ≤ (Cb / (Gegenbauer.lam m * Real.sqrt (2*(m:ℝ)+1)))
              * (Gegenbauer.lam m)⁻¹ ^ k * (Cg / Gegenbauer.lam m)
              * (Cq * (2*(m:ℝ)+1)^2) :=
            mul_le_mul (mul_le_mul (mul_le_mul (hdec m hm1) le_rfl (by positivity)
                (div_nonneg (le_of_lt hCb) (mul_nonneg (le_of_lt hLpos) (Real.sqrt_nonneg _))))
              (hg m hm1) (by positivity) (by positivity))
              (hQ0 m hm1) (abs_nonneg _) (by positivity)
        _ ≤ (Cb * (Gegenbauer.lam m)⁻¹ * (Cg * (Gegenbauer.lam m)⁻¹))
              * (Cq * (9*(m:ℝ)^2)) := by
            refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
            · rw [div_eq_mul_inv]
              refine mul_le_mul ?_ le_rfl (by positivity) (by positivity)
              · calc (Cb / (Gegenbauer.lam m * Real.sqrt (2*(m:ℝ)+1)))
                    * (Gegenbauer.lam m)⁻¹ ^ k
                  ≤ (Cb / Gegenbauer.lam m) * 1 :=
                    mul_le_mul hCbdiv hpowk (by positivity) (by positivity)
                _ = Cb * (Gegenbauer.lam m)⁻¹ := by rw [mul_one, div_eq_mul_inv]
            · exact mul_le_mul_of_nonneg_left hu2 (le_of_lt hCq)
        _ = 9*Cb*Cg*Cq * ((m:ℝ)^2 * ((Gegenbauer.lam m)⁻¹)^2) := by ring
        _ ≤ 9*Cb*Cg*Cq * (4 * (m:ℝ)^(-(2:ℝ))) := mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = 36*Cb*Cg*Cq * (m:ℝ)^(-(2:ℝ)) := by ring

/-! ## The algebraic core of the reindexing -/

/-- The purely algebraic identity underlying the decomposition: expanding
`Σ_j (α^j/λ^{j+1}) A_j + (α^J/λ^J) GJ` against `B` and `Q`. -/
private lemma decomp_algebra (m : ℕ) (α B Q GJ : ℝ) (A : ℕ → ℝ) :
    α^2 * (B * ((∑ j ∈ Finset.range J, (α^j / (Radial.lamR m)^(j+1)) * A j)
        + (α^J / (Radial.lamR m)^J) * GJ) * Q)
    = (∑ j ∈ Finset.range J,
          (α^j * A j) * (α^2 * (B * ((Gegenbauer.lam m)⁻¹)^(j+1) * Q)))
      + α^2 * (α^J * (B * ((Gegenbauer.lam m)⁻¹)^J * GJ * Q)) := by
  rw [lamR_eq_lam]
  rw [show (∑ j ∈ Finset.range J, (α^j * A j) * (α^2 * (B * ((Gegenbauer.lam m)⁻¹)^(j+1) * Q)))
      = ∑ j ∈ Finset.range J, ((α^j / (Gegenbauer.lam m)^(j+1)) * A j) * (α^2 * B * Q) from
        Finset.sum_congr rfl (fun j _ => by rw [div_eq_mul_inv, inv_pow]; ring)]
  rw [← Finset.sum_mul]
  rw [show α^2 * (α^J * (B * ((Gegenbauer.lam m)⁻¹)^J * GJ * Q))
      = ((α^J / (Gegenbauer.lam m)^J) * GJ) * (α^2 * B * Q) from by
        rw [div_eq_mul_inv, inv_pow]; ring]
  ring

/-! ## Evaluation of the two `tsum`s -/

private lemma tsum_term (α : ℝ) (ψ : ℝ → ℝ) (θ z : ℝ) (j : ℕ) :
    (∑' m : ℕ, (α^j * Ajit α j (VocabO.phiA α) z)
        * (α^2 * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^(j+1) * Qm m θ)))
      = α^2 * (α^j * Ajit α j (VocabO.phiA α) z * Wt ψ (j+1) θ) := by
  have h1 : (∑' m : ℕ, (α^j * Ajit α j (VocabO.phiA α) z)
        * (α^2 * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^(j+1) * Qm m θ)))
      = (α^j * Ajit α j (VocabO.phiA α) z)
        * (∑' m : ℕ, α^2 * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^(j+1) * Qm m θ)) := by
    rw [tsum_mul_left]
  have h2 : (∑' m : ℕ, α^2 * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^(j+1) * Qm m θ))
      = α^2 * (∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^(j+1) * Qm m θ) := by
    rw [tsum_mul_left]
  have hWt : Wt ψ (j+1) θ
      = ∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^(j+1) * Qm m θ := rfl
  rw [h1]
  rw [h2]
  rw [hWt]
  ring

private lemma tsum_tail (α : ℝ) (ψ : ℝ → ℝ) (θ z : ℝ) :
    (∑' m : ℕ, α^2 * (α^J * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^J
        * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ)))
      = α^2 * (α^J * (∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^J
          * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ)) := by
  have h1 : (∑' m : ℕ, α^2 * (α^J * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^J
        * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ)))
      = α^2 * (∑' m : ℕ, α^J * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^J
        * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ)) := by
    rw [tsum_mul_left]
  have h2 : (∑' m : ℕ, α^J * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^J
        * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ))
      = α^J * (∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^J
        * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ) := by
    rw [tsum_mul_left]
  rw [h1, h2]

/-! ## The pointwise decomposition -/

/-- The decomposition term by term in `m`.  For `m = 0` both sides vanish (`bmode 0 ψ = 0`); for
`m ≥ 1` it is `hexp` followed by `decomp_algebra`. -/
private lemma decomp_pointwise (α : ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) (m : ℕ)
    (hz : 0 < z) (hb0 : Series.bmode 0 ψ = 0)
    (hexp : ∀ m : ℕ, 1 ≤ m → ∀ z' : ℝ, 0 < z' →
      Radial.radGreen α m (VocabO.phiA α) z'
        = (∑ j ∈ Finset.range J, (α^j / (Radial.lamR m)^(j+1)) * Ajit α j (VocabO.phiA α) z')
          + (α^J / (Radial.lamR m)^J)
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z') :
    α^2 * (Series.bmode m ψ * Radial.radGreen α m (VocabO.phiA α) z * Qm m θ)
      = (∑ j ∈ Finset.range J, (α^j * Ajit α j (VocabO.phiA α) z)
            * (α^2 * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^(j+1) * Qm m θ)))
        + α^2 * (α^J * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹)^J
            * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ)) := by
  by_cases hm : m = 0
  · subst hm
    rw [hb0]
    simp only [zero_mul, mul_zero, Finset.sum_const_zero, zero_add]
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    rw [hexp m hm1 z hz]
    exact decomp_algebra m α (Series.bmode m ψ) (Qm m θ)
      (Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z) (fun j => Ajit α j (VocabO.phiA α) z)

/-! ## The `tsum`-level decomposition -/

private theorem decomp_core (α : ℝ) (ψ : ℝ → ℝ) (z θ : ℝ)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hz : 0 < z)
    (hb0 : Series.bmode 0 ψ = 0)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Series.bmode m ψ| ≤ C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hQ0 : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ θ' : ℝ, θ' ∈ Set.Ioo 0 (Real.pi / 2) →
      |Qm m θ'| ≤ C * (2 * (m : ℝ) + 1) ^ 2)
    (hrem : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) / z' * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'|
        ≤ C / Gegenbauer.lam m)
    (hexp : ∀ m : ℕ, 1 ≤ m → ∀ z' : ℝ, 0 < z' →
      Radial.radGreen α m (VocabO.phiA α) z'
        = (∑ j ∈ Finset.range J, (α ^ j / (Radial.lamR m) ^ (j + 1))
              * Ajit α j (VocabO.phiA α) z')
          + (α ^ J / (Radial.lamR m) ^ J)
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z') :
    (∑' m : ℕ, α ^ 2 * (Series.bmode m ψ * Radial.radGreen α m (VocabO.phiA α) z * Qm m θ))
      = α ^ 2 * ((∑ j ∈ Finset.range J, α ^ j * Ajit α j (VocabO.phiA α) z * Wt ψ (j + 1) θ)
          + α ^ J * (∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ)) := by
  obtain ⟨Cb, hCb, hdec⟩ := hdec
  obtain ⟨Cq, hCq, hQ0⟩ := hQ0
  obtain ⟨Cr, hCr, hrem⟩ := hrem
  -- the `λ_m^{-1}` bound for the remainder radial factor, from `hrem`
  have hGbd : ∀ m : ℕ, 1 ≤ m →
      |Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z| ≤ Cr / Gegenbauer.lam m := by
    intro m hm
    have h := hrem m hm z hz
    have hsplit : Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z
        = (z/(z+1)) * ((z+1)/z * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z) := by
      field_simp
    rw [hsplit, abs_mul, abs_of_nonneg (le_of_lt (div_pos hz (by linarith)))]
    have hle1 : z/(z+1) ≤ 1 := by
      rw [div_le_one (by linarith : (0:ℝ) < z + 1)]
      linarith
    calc (z/(z+1)) * |(z+1)/z * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z|
        ≤ 1 * (Cr / Gegenbauer.lam m) := mul_le_mul hle1 h (abs_nonneg _) (by positivity)
      _ = Cr / Gegenbauer.lam m := one_mul _
  have hsumTail : Summable (fun m : ℕ => Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
      * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ) :=
    summable_bm_G_Qm ψ θ Cb Cq Cr hCb hCq hCr hb0 (fun m hm => hdec m hm)
      (fun m hm => hQ0 m hm θ hθ) (fun m => Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z)
      hGbd J
  have hsumF : ∀ j ∈ Finset.range J, Summable (fun m : ℕ =>
      (α ^ j * Ajit α j (VocabO.phiA α) z)
        * (α ^ 2 * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (j + 1) * Qm m θ))) := by
    intro j _
    have h := summable_bm_lam_Qm ψ θ Cb Cq hCb hCq hb0 (fun m hm => hdec m hm)
      (fun m hm => hQ0 m hm θ hθ) j
    exact (h.mul_left (α^2)).mul_left (α^j * Ajit α j (VocabO.phiA α) z)
  calc (∑' m : ℕ, α ^ 2 * (Series.bmode m ψ * Radial.radGreen α m (VocabO.phiA α) z * Qm m θ))
      = ∑' m : ℕ, ((∑ j ∈ Finset.range J, (α ^ j * Ajit α j (VocabO.phiA α) z)
            * (α ^ 2 * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (j + 1) * Qm m θ)))
          + α ^ 2 * (α ^ J * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ))) :=
        tsum_congr (fun m => decomp_pointwise α ψ z θ m hz hb0 hexp)
    _ = (∑' m : ℕ, ∑ j ∈ Finset.range J, (α ^ j * Ajit α j (VocabO.phiA α) z)
            * (α ^ 2 * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (j + 1) * Qm m θ)))
          + ∑' m : ℕ, α ^ 2 * (α ^ J * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ)) :=
        (summable_sum hsumF).tsum_add ((hsumTail.mul_left (α^J)).mul_left (α^2))
    _ = (∑ j ∈ Finset.range J, ∑' m : ℕ, (α ^ j * Ajit α j (VocabO.phiA α) z)
            * (α ^ 2 * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (j + 1) * Qm m θ)))
          + ∑' m : ℕ, α ^ 2 * (α ^ J * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ)) := by
        rw [Summable.tsum_finsetSum hsumF]
    _ = (∑ j ∈ Finset.range J, α ^ 2 * (α ^ j * Ajit α j (VocabO.phiA α) z * Wt ψ (j+1) θ))
          + ∑' m : ℕ, α ^ 2 * (α ^ J * (Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ)) := by
        rw [Finset.sum_congr rfl (fun j _ => tsum_term α ψ θ z j)]
    _ = α ^ 2 * ((∑ j ∈ Finset.range J, α ^ j * Ajit α j (VocabO.phiA α) z * Wt ψ (j + 1) θ)
          + α ^ J * (∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z * Qm m θ)) := by
        rw [← Finset.mul_sum]
        rw [tsum_tail α ψ θ z]
        ring

/-- The mode expansion of `psiSeries α (RemSource α ψ)` with the `α²` inside the `tsum`, and the
division by `s2 θ = sin 2θ` turned into the divided angular modes `Qm m θ`. -/
private lemma psiSeries_div_eq_tsum (α : ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) :
    Series.psiSeries α (RemSource α ψ) z θ / Work.Construction.s2 θ
      = ∑' m : ℕ, α^2 * (Series.bmode m ψ * (Radial.radGreen α m (VocabO.phiA α) z)
          * Qm m θ) := by
  have h1 : Series.psiSeries α (RemSource α ψ) z θ
      = ∑' m : ℕ, (α^2 * Series.bmode m ψ) * Radial.radGreen α m (VocabO.phiA α) z
          * Gegenbauer.eFam m θ := by
    rw [Series.psiSeries]
    exact tsum_congr (fun m => by rw [Series.acoeff_RemSource])
  have hdiv : (∑' m : ℕ, (α^2 * Series.bmode m ψ) * Radial.radGreen α m (VocabO.phiA α) z
        * Gegenbauer.eFam m θ) / Work.Construction.s2 θ
      = ∑' m : ℕ, ((α^2 * Series.bmode m ψ) * Radial.radGreen α m (VocabO.phiA α) z
        * Gegenbauer.eFam m θ) / Work.Construction.s2 θ := tsum_div_tsum _ _
  rw [h1]
  rw [hdiv]
  refine tsum_congr (fun m => ?_)
  simp only [Qm]
  ring

theorem Decomp (α : ℝ) (ψ : ℝ → ℝ) (z θ : ℝ)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hz : 0 < z)
    (hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hQ0 : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ θ' : ℝ, θ' ∈ Set.Ioo 0 (Real.pi / 2) →
      |Work.FTS.PhiStar.FlatWAux.Qm m θ'| ≤ C * (2 * (m : ℝ) + 1) ^ 2)
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ'| ≤ C * (2 * (m : ℝ) + 1))
    (hsrc : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) / z' * Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z'|
        ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m)
    (hrem : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) / z' * Work.FTS.PhiStar.Radial.radGreen α m
          (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
            (Work.FTS.VocabO.phiA α)) z'|
        ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m)
    (hexp : ∀ m : ℕ, 1 ≤ m → ∀ z' : ℝ, 0 < z' →
      Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z'
        = (∑ j ∈ Finset.range Work.FTS.PhiStar.FlatWAux.J,
            (α ^ j / (Work.FTS.PhiStar.Radial.lamR m) ^ (j + 1))
              * Work.FTS.PhiStar.FlatWAux.Ajit α j (Work.FTS.VocabO.phiA α) z')
          + (α ^ Work.FTS.PhiStar.FlatWAux.J
              / (Work.FTS.PhiStar.Radial.lamR m) ^ Work.FTS.PhiStar.FlatWAux.J)
              * Work.FTS.PhiStar.Radial.radGreen α m
                  (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                    (Work.FTS.VocabO.phiA α)) z') :
    Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ
        / Work.Construction.s2 θ
      = α ^ 2 * ((∑ j ∈ Finset.range Work.FTS.PhiStar.FlatWAux.J,
            α ^ j * Work.FTS.PhiStar.FlatWAux.Ajit α j (Work.FTS.VocabO.phiA α) z
              * Work.FTS.PhiStar.FlatWAux.Wt ψ (j + 1) θ)
          + α ^ Work.FTS.PhiStar.FlatWAux.J * (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ Work.FTS.PhiStar.FlatWAux.J
              * Work.FTS.PhiStar.Radial.radGreen α m
                  (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                    (Work.FTS.VocabO.phiA α)) z
              * Work.FTS.PhiStar.FlatWAux.Qm m θ)) := by
  rw [psiSeries_div_eq_tsum α ψ z θ]
  exact decomp_core α ψ z θ hθ hz hb0 hdec hQ0 hrem hexp

end Work.FTS.PhiStar.FlatWAux
