import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.FatouCoord.Setup
import Submission.Work.Parab.Setup
import Submission.Work.Parab.germ
import Submission.Work.Parab.chartEstimate.chart_estimate
import Submission.Work.Parab.leftCoord.wMap_large_estimates
import Submission.Work.Parab.coordData.region_large
import Submission.Work.Parab.coordData.log_asymp_bound_gen
import Submission.Work.Parab.coordData.log_le_frac8

/-!
# The seed of the ζ-plane left coordinate is defined, large and `L`-valued

`Work.Parab.coordData.tau_seed_gen` discharges the seed hypotheses of the maximal-domain
construction of `Work.Parab.CoordData` in the *general* form, where the second-order coefficient
`c` of `ParabolicBounds f h c r A A'` (which only enters the `O(1/ζ)` chart estimate
`Work.Parab.leftCoord.wMap_large_estimates`) is allowed to differ from the coefficient `a` of the
asymptotic expansion `τ u = u + a log (-u) + b + o(1)`: for a large enough sector `QLeft ξ₀`
(containing the one on which `τ` is asymptotic) the seed `τ` is bounded below by `1 / ρ`, takes
its values in the domain `L` of the left coordinate, and stays there after one step `wMap f`.

The proof is a three-line estimate once the geometry is isolated:
* `τ u` and `wMap f (τ u)` are both within `‖u‖ / 4 + 4` of `u`, because
  `‖τ u - u‖ ≤ 1 + ‖a log (-u) + b‖ ≤ 1 + ‖u‖ / 8` and `‖wMap f ζ - (ζ + 1)‖ ≤ K / ‖ζ‖`;
* `Work.Parab.coordData.region_large` says that any point that close to a point of a far enough
  sector lies in `{Re < -M₀} ∪ {M₁ < |Im|, Re < 3 |Im|} ⊆ L` (by `hL`, `hLim`);
* `Work.Parab.QLeft_subset_norm` converts "far enough sector" into the modulus lower bound that
  makes `1 / ρ ≤ ‖τ u‖`.

It rests only on the three imported lemmas plus Mathlib.
-/

namespace Work.Parab.coordData

open Complex Set Metric Filter
open scoped Topology

noncomputable section

namespace TauSeed

/-- `QLeft` is antitone in the vertex parameter: enlarging `ξ` moves the sector's vertex further
left, so the set of admissible `w` shrinks. -/
theorem QLeft_anti {ξ ξ' : ℝ} (h : ξ ≤ ξ') : MandelDim.QLeft ξ' ⊆ MandelDim.QLeft ξ := by
  intro w hw
  rw [Work.Parab.QLeft_iff] at hw ⊢
  have hδ : (0 : ℝ) ≤ ξ' - ξ := by linarith
  have hsplit : w + (ξ : ℂ) = (w + (ξ' : ℂ)) - ((ξ' - ξ : ℝ) : ℂ) := by push_cast; ring
  rw [hsplit]
  have hre : ((w + (ξ' : ℂ)) - ((ξ' - ξ : ℝ) : ℂ)).re = (w + (ξ' : ℂ)).re - (ξ' - ξ) := by simp
  have hnorm : ‖w + (ξ' : ℂ)‖ ≤ ‖(w + (ξ' : ℂ)) - ((ξ' - ξ : ℝ) : ℂ)‖ + (ξ' - ξ) := by
    have h2 : ‖(((ξ' - ξ : ℝ)) : ℂ)‖ = ξ' - ξ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hδ]
    have h3 : w + (ξ' : ℂ) = ((w + (ξ' : ℂ)) - ((ξ' - ξ : ℝ) : ℂ)) + ((ξ' - ξ : ℝ) : ℂ) := by
      ring
    calc ‖w + (ξ' : ℂ)‖
        = ‖((w + (ξ' : ℂ)) - ((ξ' - ξ : ℝ) : ℂ)) + ((ξ' - ξ : ℝ) : ℂ)‖ := congrArg norm h3
      _ ≤ ‖(w + (ξ' : ℂ)) - ((ξ' - ξ : ℝ) : ℂ)‖ + ‖(((ξ' - ξ : ℝ)) : ℂ)‖ := norm_add_le _ _
      _ = ‖(w + (ξ' : ℂ)) - ((ξ' - ξ : ℝ) : ℂ)‖ + (ξ' - ξ) := by rw [h2]
  rw [hre]
  linarith

end TauSeed

open TauSeed in
/-- **The seed of the left coordinate.**  Suppose
* `f z = z + z ^ 2 h z` on `ball 0 r` with `h z = 1 + c z + O(z^2)` (`ParabolicBounds f h c r A A'`),
* `L` contains the far left half-plane `{Re < -M₀}` and the two-sided wedge
  `{M₁ < |Im|, Re < 3 |Im|}` (`hL`, `hLim`),
* `τ u = u + a log (-u) + b + o(1)` on the sector `QLeft ξ₁` (`hτasym`).

Then for some `ξ₀ ≥ ξ₁`, on the whole sector `QLeft ξ₀` the seed `τ` is bounded below by `1 / ρ`,
takes its values in `L`, and one chart step `wMap f` keeps them in `L`. -/
theorem tau_seed_gen {f : ℂ → ℂ} {h : ℂ → ℂ} {c a : ℂ} {r A A' M₀ M₁ ξ₁ ρ : ℝ} {b : ℂ}
    {L : Set ℂ} {τ : ℂ → ℂ}
    (hb : Work.FatouCoord.ParabolicBounds f h c r A A')
    (hρ : 0 < ρ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (hξ₁ : 0 < ξ₁)
    (hL : ∀ ζ : ℂ, ζ.re < -M₀ → ζ ∈ L)
    (hLim : ∀ ζ : ℂ, M₁ < |ζ.im| → ζ.re < 3 * |ζ.im| → ζ ∈ L)
    (hτasym : ∀ ε > 0, ∃ R : ℝ, ∀ u ∈ MandelDim.QLeft ξ₁, R < ‖u‖ →
      ‖τ u - (u + a * Complex.log (-u) + b)‖ < ε) :
    ∃ ξ₀ : ℝ, ξ₁ ≤ ξ₀ ∧ 0 < ξ₀ ∧ ∀ u ∈ MandelDim.QLeft ξ₀,
      1 / ρ ≤ ‖τ u‖ ∧ τ u ∈ L ∧ Work.FatouCoord.wMap f (τ u) ∈ L := by
  -- the geometry: a point close to a far sector point lies in the two regions covered by `L`
  obtain ⟨ξs, hξs₁, hξspos, hreg⟩ := region_large hM₀ hM₁ hξ₁
  -- the chart estimate `wMap f ζ = ζ + 1 + O(1 / ‖ζ‖)` (coefficient `c` only enters the error)
  obtain ⟨Rw, Kw, hRw, -, hKw, hwe⟩ := Work.Parab.leftCoord.wMap_large_estimates hb
  -- `‖a log (-u) + b‖ = O(log ‖u‖)` and `log ‖u‖ ≤ ‖u‖ / 8` far out
  obtain ⟨cl, hcl, hlog⟩ := log_asymp_bound_gen a b
  obtain ⟨Ml, hMl1, hMlf⟩ := log_le_frac8 cl
  -- the asymptotic expansion of `τ`, with error `< 1`
  obtain ⟨Rt, hRt⟩ := hτasym 1 one_pos
  -- the modulus threshold: `‖u‖ > R₀` for `u ∈ QLeft ξ` as soon as `ξ ≥ 3 R₀`
  set R₀ : ℝ := Ml + max (Rt + 1) 0 + 8 * (Rw + 1) + 8 * (Kw + 1) + 8 * (1 / ρ + 1) + 8
    with hR₀def
  set ξ : ℝ := max ξs (max (3 * R₀) 1) with hξdef
  have hξsξ : ξs ≤ ξ := le_max_left _ _
  have h3R₀ : 3 * R₀ ≤ ξ := le_trans (le_max_left _ _) (le_max_right _ _)
  have h1ξ : (1 : ℝ) ≤ ξ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hξpos : 0 < ξ := lt_of_lt_of_le one_pos h1ξ
  have hmax0 : (0 : ℝ) ≤ max (Rt + 1) 0 := le_max_right _ _
  have hRw1 : (0 : ℝ) ≤ Rw + 1 := by linarith
  have hKw1 : (0 : ℝ) ≤ Kw + 1 := by linarith
  have hρ1 : (0 : ℝ) ≤ 1 / ρ + 1 := by have := one_div_pos.mpr hρ; linarith
  have hMlR₀ : Ml ≤ R₀ := by rw [hR₀def]; linarith
  have hRtR₀ : Rt + 1 ≤ R₀ := by rw [hR₀def]; linarith [le_max_left (Rt + 1) 0]
  have hRwR₀ : (8 / 7) * (Rw + 1) ≤ R₀ := by rw [hR₀def]; linarith
  have hKwR₀ : (8 / 7) * (Kw / 2 + 1) ≤ R₀ := by rw [hR₀def]; linarith
  have hρR₀ : (8 / 7) * (1 / ρ + 1) ≤ R₀ := by rw [hR₀def]; linarith
  have h1R₀ : (1 : ℝ) ≤ R₀ := by rw [hR₀def]; linarith
  have hR₀ξ : R₀ ≤ ξ / 3 := by linarith
  refine ⟨ξ, ?_, hξpos, ?_⟩
  · linarith
  · intro u hu
    have huQ₀ : u ∈ MandelDim.QLeft ξs := TauSeed.QLeft_anti hξsξ hu
    have huQ₁ : u ∈ MandelDim.QLeft ξ₁ := TauSeed.QLeft_anti hξs₁ huQ₀
    have hunorm : R₀ < ‖u‖ := lt_of_le_of_lt hR₀ξ (Work.Parab.QLeft_subset_norm hξpos hu)
    have hu1 : (1 : ℝ) ≤ ‖u‖ := le_trans h1R₀ (le_of_lt hunorm)
    have huMl : Ml ≤ ‖u‖ := le_trans hMlR₀ (le_of_lt hunorm)
    have huRt : Rt < ‖u‖ := lt_of_lt_of_le (by linarith) (le_of_lt hunorm)
    have hlogu : ‖a * Complex.log (-u) + b‖ ≤ ‖u‖ / 8 := by
      have h1 := hlog u hu1
      have h2 := hMlf ‖u‖ huMl
      linarith
    have hτp : ‖τ u - (u + a * Complex.log (-u) + b)‖ < 1 := hRt u huQ₁ huRt
    have hdu_split : ‖τ u - u‖ ≤
        ‖τ u - (u + a * Complex.log (-u) + b)‖ + ‖a * Complex.log (-u) + b‖ := by
      have hp : τ u - u
          = (τ u - (u + a * Complex.log (-u) + b)) + (a * Complex.log (-u) + b) := by ring
      rw [hp]
      exact norm_add_le _ _
    have hdu_small : ‖τ u - u‖ < 1 + ‖u‖ / 8 := lt_of_le_of_lt hdu_split (by linarith)
    have hdu : ‖τ u - u‖ ≤ ‖u‖ / 4 + 4 := by linarith [hdu_small, norm_nonneg u]
    have hτunorm : 7 * ‖u‖ / 8 - 1 < ‖τ u‖ := by
      have h1 : ‖u‖ ≤ ‖τ u‖ + ‖τ u - u‖ := by
        have hsub := norm_sub_le (τ u) (τ u - u)
        have he : τ u - (τ u - u) = u := by ring
        rwa [he] at hsub
      linarith
    have hRw_bound : Rw ≤ 7 * R₀ / 8 - 1 := by linarith
    have hKw_bound : Kw / 2 ≤ 7 * R₀ / 8 - 1 := by linarith
    have hρ_bound : 1 / ρ ≤ 7 * R₀ / 8 - 1 := by linarith
    have hτu_Rw : Rw < ‖τ u‖ := by linarith
    have hτu_pos : 0 < ‖τ u‖ := lt_trans hRw hτu_Rw
    have hτu_Kw : Kw / 2 < ‖τ u‖ := by linarith
    have hτu_ρ : 1 / ρ ≤ ‖τ u‖ := by linarith
    have hwτ : ‖Work.FatouCoord.wMap f (τ u) - (τ u + 1)‖ ≤ Kw / ‖τ u‖ :=
      (hwe (τ u) hτu_Rw).1
    have hKwdiv : Kw / ‖τ u‖ ≤ 2 := by
      rw [div_le_iff₀ hτu_pos]
      linarith
    have hdwu : ‖Work.FatouCoord.wMap f (τ u) - u‖ ≤ ‖u‖ / 4 + 4 := by
      have hsplit : Work.FatouCoord.wMap f (τ u) - u
          = (Work.FatouCoord.wMap f (τ u) - (τ u + 1)) + ((τ u + 1) - u) := by ring
      have h2 : ‖(τ u + 1) - u‖ ≤ ‖τ u - u‖ + 1 := by
        have h3 : (τ u + 1) - u = (τ u - u) + 1 := by ring
        rw [h3]
        simpa using norm_add_le (τ u - u) 1
      calc ‖Work.FatouCoord.wMap f (τ u) - u‖
          = ‖(Work.FatouCoord.wMap f (τ u) - (τ u + 1)) + ((τ u + 1) - u)‖ := by rw [hsplit]
        _ ≤ ‖Work.FatouCoord.wMap f (τ u) - (τ u + 1)‖ + ‖(τ u + 1) - u‖ := norm_add_le _ _
        _ ≤ Kw / ‖τ u‖ + (‖τ u - u‖ + 1) := by linarith
        _ ≤ 2 + (1 + ‖u‖ / 8) + 1 := by linarith
        _ ≤ ‖u‖ / 4 + 4 := by linarith [norm_nonneg u]
    refine ⟨hτu_ρ, ?_, ?_⟩
    · rcases hreg u (τ u) huQ₀ hdu with h' | ⟨h1, h2⟩
      · exact hL _ h'
      · exact hLim _ h1 h2
    · rcases hreg u (Work.FatouCoord.wMap f (τ u)) huQ₀ hdwu with h' | ⟨h1, h2⟩
      · exact hL _ h'
      · exact hLim _ h1 h2

end

end Work.Parab.coordData
