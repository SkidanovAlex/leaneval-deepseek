/-
# `Work.FTS.PhiStar.Series.DecayRem` — conjunct 4 of the target: decay as `z → ∞`

For the remainder source `F = RemSource α ψ` the mode series is absolutely summable (§1 of
`NOTES_psiSeries_solves_rem.md`), and the large-`z` half of the radial bound
(`|radGreen α m (phiA α) z| ≤ C/(z(m+1))` for `z ≥ 1`) together with the coefficient decay
`|bmode m ψ| ≤ C(m+1)^{-5/2}` and the growth `|eFam m θ| ≤ C(m+1)^{3/2}` gives the termwise bound

  `‖acoeff α m F z · eFam m θ‖ ≤ (K/z)·(m+1)^{-2}`   (`z ≥ 1`),

so `‖psiSeries α F z θ‖ ≤ (K/z)·∑'_m (m+1)^{-2} → 0`.  This is exactly the fourth conjunct of
`Work.FTS.PhiStar.Series.psiSeries_solves_rem`, stated here with the three crux estimates and the
summability as explicit hypotheses (they are proved separately, so this lemma is independent of
them).
-/
import Mathlib.Analysis.PSeries
import Submission.Work.FTS.PhiStar.Series.SummableModes
import Submission.Work.FTS.PhiStar.Series.ResolventSetup

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

/-- **Conjunct 4 of the target** (conditionally on the crux estimates): for every `θ ∈ Iθ` the
`tsum` defining `psiSeries` of the remainder source tends to `0` as `z → ∞`. -/
theorem psiSeries_tendsto_zero_RemSource (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α)
    (hψ : Work.FTS.PhiStar.AngModel α ψ)
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)))
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |bmode m ψ| ≤ C * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)))
    (hbig : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), 1 ≤ m → ∀ z : ℝ, 1 ≤ z →
      |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
        ≤ C / (z * ((m : ℝ) + 1)))
    (hsum : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Summable (fun m : ℕ => ‖acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ‖)) :
    ∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun z => psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ)
        Filter.atTop (nhds 0) := by
  obtain ⟨Cg, hCg, hgr⟩ := hgr
  obtain ⟨Cd, hCd, hdec⟩ := hdec
  obtain ⟨Cb, hCb, hbig⟩ := hbig
  have hzero : bmode 0 ψ = 0 := bmode_zero ψ hψ.moment
  intro θ hθ
  set K : ℝ := α ^ 2 * Cd * Cb * Cg with hK
  have hmaj : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-(2 : ℝ))) := by
    have h : Summable (fun n : ℕ => ((n : ℝ)) ^ (-(2 : ℝ))) :=
      (Real.summable_nat_rpow (p := (-(2 : ℝ)))).mpr (by norm_num)
    have h' := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ)) ^ (-(2 : ℝ))) 1).mpr h
    simpa only [Nat.cast_add, Nat.cast_one] using h'
  have hterm : ∀ z : ℝ, 1 ≤ z → ∀ m : ℕ,
      ‖acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ‖
        ≤ (K / z) * ((m : ℝ) + 1) ^ (-(2 : ℝ)) := by
    intro z hz m
    by_cases hm : m = 0
    · subst hm
      have h0 : acoeff α 0 (Work.FTS.PhiStar.RemSource α ψ) z *
          Work.FTS.PhiStar.Gegenbauer.eFam 0 θ = 0 := by
        rw [acoeff_RemSource, hzero]
        simp
      rw [h0, norm_zero]
      have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
      have : 0 < K / z := by
        rw [hK]
        have h1 : 0 < 1 / z := one_div_pos.mpr hz0
        positivity
      exact mul_nonneg (le_of_lt this) (by positivity)
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      rw [Real.norm_eq_abs, acoeff_RemSource]
      calc |α ^ 2 * bmode m ψ
              * Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
          = |α ^ 2| * |bmode m ψ|
              * |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
              * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| := by rw [abs_mul, abs_mul, abs_mul]
        _ = α ^ 2 * |bmode m ψ|
              * |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
              * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| := by
            rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ α ^ 2)]
        _ ≤ (α ^ 2 * (Cd * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))))
              * (Cb / (z * ((m : ℝ) + 1)))
              * (Cg * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ))) := by
            have hb := hdec m hm1
            have hr := hbig m hm1 z hz
            have he := hgr m θ hθ
            gcongr
        _ = (K / z) * ((m : ℝ) + 1) ^ (-(2 : ℝ)) := by
            have hp : ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) * ((m : ℝ) + 1) ^ (-(1 : ℝ))
                * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)) = ((m : ℝ) + 1) ^ (-(2 : ℝ)) := by
              rw [← Real.rpow_add (by positivity), ← Real.rpow_add (by positivity)]
              norm_num
            have hinv : Cb / (z * ((m : ℝ) + 1))
                = (Cb / z) * ((m : ℝ) + 1) ^ (-(1 : ℝ)) := by
              rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1), Real.rpow_one,
                div_eq_mul_inv]
              field_simp
            rw [hinv, ← hp, hK]
            ring
  have hbound : ∀ z : ℝ, 1 ≤ z →
      ‖psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ‖
        ≤ (K * (∑' m : ℕ, ((m : ℝ) + 1) ^ (-(2 : ℝ)))) / z := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
    have hs := hsum z hz0 θ hθ
    calc ‖psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ‖
        = ‖∑' m : ℕ, acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z *
            Work.FTS.PhiStar.Gegenbauer.eFam m θ‖ := rfl
      _ ≤ ∑' m : ℕ, ‖acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z *
            Work.FTS.PhiStar.Gegenbauer.eFam m θ‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' m : ℕ, (K / z) * ((m : ℝ) + 1) ^ (-(2 : ℝ)) :=
          Summable.tsum_le_tsum (fun m => hterm z hz m) hs (hmaj.mul_left (K / z))
      _ = (K * (∑' m : ℕ, ((m : ℝ) + 1) ^ (-(2 : ℝ)))) / z := by
          rw [Summable.tsum_mul_left _ hmaj]
          ring
  have hlim : Filter.Tendsto
      (fun z : ℝ => (K * (∑' m : ℕ, ((m : ℝ) + 1) ^ (-(2 : ℝ)))) / z)
      Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hnorm : Filter.Tendsto
      (fun z : ℝ => ‖psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ‖)
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Filter.Eventually.of_forall (fun z => norm_nonneg _))
      (eventually_atTop.mpr ⟨1, fun z hz => hbound z hz⟩)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

end Work.FTS.PhiStar.Series
