import Mathlib
import Submission.Work.OddCurve.LowSlope.Datum
import Submission.Work.OddRadon.contDiffOn_radonProfile

/-!
# Smoothness of the first Radon datum on a closed interval `[0,b]`, `b < 1`

`Work.OddCurve.LowSlope.radonPhi n ρ` is the spherical-Radon datum
`𝓡 (w₁² ρ(w)^{2n+2})` of a body of revolution with radial function `ρ`.  On the *open*
interval `(0,1)` its smoothness is `Work.OddCurve.LowSlope.contDiffOn_radonPhi`, but that
statement has a continuity hypothesis on the profile at the endpoints `±1` and, being on an
open set, says nothing at the lower endpoint `c = 0`.

Here we prove the datum is `C^∞` on the *closed* interval `[0,b]` for every `b < 1`, from
nothing but `ρ ∈ C^∞(-1,1)`.  The reason the endpoint `c = 0` is harmless is the factor
`u²` of the profile: the defining integral

  `radonPhi n ρ c = |S^{2n-2}| ∫_{-π/2}^{π/2} cos^{2n-2} θ · (c sin θ)² ρ(c sin θ)^{2n+2} dθ`

only ever evaluates `ρ` at the points `c sin θ`, which for `|c| < 1` stay strictly inside
`(-1,1)`.  So on a neighbourhood `(-R,R)` of `[0,b]` with `R < 1` we may replace `ρ` by any
globally smooth function agreeing with it on `[-R,R]` (`Commons.Analysis.Calculus.taylorExtend`)
and differentiate under the integral sign
(`Work.Analysis.Calculus.contDiff_intervalIntegral_fixed`).

The identity in trigonometric form `radonProfile_eq_cos_any` below is the unconditional
version of `Work.OddRadon.radonProfile_eq_cos_integral` (which is stated there for `c > 0`)
combined with the unconditional power conversion `radonProfile_eq_natpow_any`; both hold for
every real `c`.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- **The one-variable Radon transform in natural powers, for every `c`.**
(Unconditional form of `radonProfile_eq_natpow`: the hypothesis `0 < c` is not needed, since the
rewrite is purely a rewriting of the real exponent `(2n+1)/2 - 2 = n - 3/2` in powers.) -/
lemma radonProfile_eq_natpow_any (n : ℕ) (hn : 1 ≤ n) (γ : ℝ → ℝ) (c : ℝ) :
    Work.OddRadon.radonProfile (2 * n + 1) γ c
      = Work.OddRadon.sphereArea (2 * n - 2) *
        (∫ ν in (-1 : ℝ)..1, (1 - ν ^ 2) ^ (n - 1) * γ (c * ν) / Real.sqrt (1 - ν ^ 2)) := by
  rw [Work.OddRadon.radonProfile]
  have hidx : 2 * n + 1 - 3 = 2 * n - 2 := by omega
  rw [hidx]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) (1 : ℝ),
    Measure.ae_ne (volume : Measure ℝ) (-1 : ℝ)] with ν hne1 _ hin
  rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hin
  have hpos : 0 < 1 - ν ^ 2 := by
    have h1 : ν < 1 := lt_of_le_of_ne hin.2 hne1
    nlinarith [hin.1, h1, sq_nonneg ν]
  have hexp : (((2 * n + 1 : ℕ) : ℝ) / 2 - 2) = ((n : ℝ) - 1) + (-(1 / 2)) := by
    push_cast; ring
  have hcast : (((n : ℝ) - 1)) = ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn]; push_cast; ring
  rw [hexp, Real.rpow_add hpos, hcast, Real.rpow_natCast (1 - ν ^ 2) (n - 1),
    Real.rpow_neg hpos.le ((1 : ℝ) / 2), Real.sqrt_eq_rpow, div_eq_mul_inv]
  ring

/-- **The trigonometric form of the Radon profile, for every `c`**: the substitution
`ν = sin θ` removes the endpoint singularity of the defining integral, so that no hypothesis on
`c` (nor any continuity of `γ` at `±1`) is needed. -/
lemma radonProfile_eq_cos_any (n : ℕ) (hn : 1 ≤ n) (γ : ℝ → ℝ) (c : ℝ) :
    Work.OddRadon.radonProfile (2 * n + 1) γ c
      = Work.OddRadon.sphereArea (2 * n - 2) *
        (∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
          Real.cos θ ^ (2 * n - 2) * γ (c * Real.sin θ)) := by
  rw [radonProfile_eq_natpow_any n hn γ c, Work.OddRadon.integral_one_sub_sq_eq_cos n hn γ c]

/-- **The first Radon datum as a trigonometric integral**, for every `c`. -/
lemma radonPhi_eq_cos (n : ℕ) (hn : 1 ≤ n) (ρ : ℝ → ℝ) (c : ℝ) :
    radonPhi n ρ c
      = Work.OddRadon.sphereArea (2 * n - 2) *
        (∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
          Real.cos θ ^ (2 * n - 2) *
            ((c * Real.sin θ) ^ 2 * ρ (c * Real.sin θ) ^ (2 * n + 2))) := by
  rw [radonPhi,
    radonProfile_eq_cos_any n hn (fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2)) c]

/-- **The first Radon datum is `C^∞` on the closed interval `[0,b]`** for every `b < 1`, from
`ρ ∈ C^∞(-1,1)` alone. -/
theorem contDiffOn_radonPhi_Icc (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ} {b : ℝ}
    (hb : b < 1) (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun c : ℝ => Work.OddCurve.LowSlope.radonPhi n ρ c) (Set.Icc 0 b) := by
  rw [contDiffOn_infty]
  intro N
  -- at each point `x ∈ [0,b]` we work on an open neighbourhood `(-R,R)` with `|x| < R < 1`
  refine contDiffOn_of_locally_contDiffOn (fun x hx => ?_)
  obtain ⟨hx0, hxb⟩ := hx
  have hx1 : x < 1 := lt_of_le_of_lt hxb hb
  set R : ℝ := (x + 1) / 2 with hR
  have hxR : x < R := by rw [hR]; linarith
  have hR1 : R < 1 := by rw [hR]; linarith
  refine ⟨Set.Ioo (-R) R, isOpen_Ioo, ⟨by linarith, hxR⟩, ?_⟩
  have hsub : Set.Icc (-R) R ⊆ Set.Ioo (-1 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.1, hR1], by linarith [ht.2, hR1]⟩
  have hγ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2)) (Set.Ioo (-1 : ℝ) 1) :=
    (contDiffOn_id.pow 2).mul (hρ.pow (2 * n + 2))
  have hγR : ContDiffOn ℝ ((N : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2)) (Set.Icc (-R) R) :=
    (hγ.mono hsub).of_le (by exact_mod_cast (le_top : (N : ℕ∞) ≤ (⊤ : ℕ∞)))
  -- a globally `C^N` function agreeing with the profile on `[-R,R]`
  obtain ⟨G, hGsm, hGeq⟩ : ∃ G : ℝ → ℝ, ContDiff ℝ ((N : ℕ∞) : WithTop ℕ∞) G ∧
      Set.EqOn G (fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2)) (Set.Icc (-R) R) :=
    ⟨Commons.Analysis.Calculus.taylorExtend (fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2)) N (-R) R,
      Commons.Analysis.Calculus.contDiff_taylorExtend N (by linarith) hγR,
      Commons.Analysis.Calculus.taylorExtend_eqOn_Icc⟩
  set F : ℝ → ℝ → ℝ := fun c θ => Real.cos θ ^ (2 * n - 2) * G (c * Real.sin θ) with hF
  have hFsm : ContDiff ℝ ((N : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => F p.1 p.2) := by
    rw [hF]
    exact ((Real.contDiff_cos.comp contDiff_snd).pow (2 * n - 2)).mul
      (hGsm.comp (contDiff_fst.mul (Real.contDiff_sin.comp contDiff_snd)))
  have hK : ContDiff ℝ ((N : ℕ∞) : WithTop ℕ∞)
      (fun c : ℝ => ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), F c θ) :=
    Work.Analysis.Calculus.contDiff_intervalIntegral_fixed N hFsm
  -- the smooth integral coincides with the datum on `[0,b] ∩ (-R,R)`
  refine ((hK.const_smul (Work.OddRadon.sphereArea (2 * n - 2))).contDiffOn).congr
    (fun c hc => ?_)
  obtain ⟨hc1, hc2⟩ := hc
  have hc0 : 0 ≤ c := hc1.1
  have hcR : c < R := hc2.2
  rw [radonPhi_eq_cos n hn ρ c]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  rw [hF]
  simp only
  have hsin : |Real.sin θ| ≤ 1 := by
    rw [abs_le]; exact ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have hle : |c * Real.sin θ| ≤ R := by
    rw [abs_mul, abs_of_nonneg hc0]
    calc c * |Real.sin θ| ≤ c * 1 := mul_le_mul_of_nonneg_left hsin hc0
      _ = c := by ring
      _ ≤ R := hcR.le
  have hmem : c * Real.sin θ ∈ Set.Icc (-R) R :=
    ⟨le_trans (neg_le_neg hle) (neg_abs_le _), le_trans (le_abs_self _) hle⟩
  rw [hGeq hmem]

end

end Work.OddCurve.LowSlope
