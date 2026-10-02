import Mathlib
import Submission.Work.LandLeaves.gronwallDefs
import Submission.Work.LandLeaves.koebeDerivAux.psiDefs
import Submission.Work.LandLeaves.koebeDerivAux.psiCoeffSummableW
import Submission.Work.Koebe.gwDefs
import Submission.Work.Koebe.gwNonpos
import Submission.Work.Koebe.gwSignedAreaPartial

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves.koebeDerivAux

/-- The Taylor coefficients at `0` of the extension `Fext ψ = ψ (·)⁻¹ - (·)⁻¹` are the Laurent
coefficients `bco ψ n` of `ψ` at infinity. -/
lemma gco_Fext_eq_bco (ψ : ℂ → ℂ) (n : ℕ) : Work.Koebe.gco (Fext ψ) n = bco ψ n := by
  rw [Work.Koebe.gco, bco, div_eq_mul_inv, mul_comm]

/-- Numerical final step of the area theorem: if for every `0 < r < 1` and every truncation length
`N` the partial weighted coefficient sum satisfies
`π * (∑_{n<N} n ‖bco ψ n‖² r^{2n} - r⁻²) ≤ 0`, then `‖bco ψ 1‖ ≤ 1`.

Indeed the instance `N = 2` reads `‖bco ψ 1‖² r² ≤ r⁻²`, i.e. `‖bco ψ 1‖ ≤ r⁻²`; taking
`r = (1 + δ)^{-1/2} ↑ 1` gives `‖bco ψ 1‖ ≤ 1 + δ` for every `δ > 0`. -/
lemma bco_one_of_area (ψ : ℂ → ℂ)
    (harea : ∀ r : ℝ, 0 < r → r < 1 → ∀ N : ℕ,
      Real.pi * ((∑ n ∈ Finset.range N, (n : ℝ) * ‖bco ψ n‖ ^ 2 * r ^ (2 * n)) - r ^ (-2 : ℤ)) ≤ 0) :
    ‖bco ψ 1‖ ≤ 1 := by
  rw [le_iff_forall_pos_le_add]
  intro δ hδ
  have hpos : (0 : ℝ) < 1 + δ := by linarith
  set r : ℝ := (1 + δ) ^ (-(1 / 2) : ℝ) with hrdef
  have hr0 : 0 < r := Real.rpow_pos_of_pos hpos _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
  have hr2 : r ^ 2 = (1 + δ)⁻¹ := by
    rw [hrdef, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hpos),
      ← Real.rpow_neg_one (1 + δ)]
    congr 1
    norm_num
  have h := harea r hr0 hr1 2
  have hsum : (∑ n ∈ Finset.range 2, (n : ℝ) * ‖bco ψ n‖ ^ 2 * r ^ (2 * n))
      = ‖bco ψ 1‖ ^ 2 * r ^ 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  rw [hsum] at h
  have hrpow : r ^ (-2 : ℤ) = 1 + δ := by
    rw [zpow_neg, zpow_ofNat, hr2, inv_inv]
  rw [hrpow] at h
  have hb0 : ‖bco ψ 1‖ ^ 2 * r ^ 2 - (1 + δ) ≤ 0 := by nlinarith [h, Real.pi_pos]
  have hb : ‖bco ψ 1‖ ^ 2 * r ^ 2 ≤ 1 + δ := by linarith
  have hr2pos : (0 : ℝ) < r ^ 2 := pow_pos hr0 2
  have h1 : ‖bco ψ 1‖ ^ 2 ≤ (1 + δ) / r ^ 2 := (le_div_iff₀ hr2pos).mpr hb
  rw [hr2, div_eq_mul_inv, inv_inv] at h1
  have hsq : ‖bco ψ 1‖ ^ 2 ≤ (1 + δ) ^ 2 := by
    calc ‖bco ψ 1‖ ^ 2 ≤ (1 + δ) * (1 + δ) := h1
      _ = (1 + δ) ^ 2 := by rw [pow_two]
  have hs := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + δ)] at hs

/-- The exterior area coefficient bound: for `ψ` holomorphic and injective on `‖w‖ > 1` with `ψ w - w` bounded on `‖w‖ ≥ W` (`W > 1`), the `w⁻¹` Laurent coefficient satisfies `‖bco ψ 1‖ ≤ 1`.

This is the elementary form of Grönwall's area theorem. Suggested route:

1. `Fext ψ ζ = ψ ζ⁻¹ - ζ⁻¹` is holomorphic on the unit disc: it is holomorphic on `0 < ‖ζ‖ < 1` by `hd`, and bounded by `C` on `0 < ‖ζ‖ ≤ 1/W` by `hb` (there `‖ζ⁻¹‖ ≥ W`), so `0` is a removable singularity. Hence `Fext ψ` has honest Taylor coefficients and `ψ w = w + bco ψ 0 + ∑_{n≥1} bco ψ n · w^{-n}` holds on `1 < ‖w‖` (the last step is the localization of `Work.LandLeaves.hasSum_expansion`).
2. `Work.LandLeaves.bco_one_eq` (its argument only needs the expansion of `Fext ψ` near `0`, so it localizes) gives `∮_{‖w‖ = 2} ψ w dw = 2π i · bco ψ 1`.
3. Area identity for every `r > 1`: with `psiK`, `psiW`, `psiAnnulusAreaW`, `psiLevelW` (one large `R₀`) and `psiCurveNull`, the disjoint decomposition `psiK ψ r = psiK ψ R₀ ⊔ ψ '' {r < ‖w‖ < R₀} ⊔ ψ '' {‖w‖ = R₀}` (for `1 < r < R₀`, using injectivity) and `Work.LandLeaves.psiCoeffSummableW` give `(volume (psiK ψ r)).toReal = psiW ψ r`.
4. Non-negativity of the volume gives `psiW ψ r ≥ 0`, i.e. `∑ₙ n‖bco ψ n‖² r^{-2n} ≤ r²`, so in particular `‖bco ψ 1‖² r^{-2} ≤ r²`; as `r ↓ 1` this gives `‖bco ψ 1‖ ≤ 1`.

Sharper alternative for step 3-4 (if the area identity is inconvenient): `Work.LandLeaves.gwSetup`'s `lintegral_norm_sq_eq_volume_image` with the region `{w | ‖ψ w‖ < M}` gives `∫⁻_{‖ψ w‖<M} ‖deriv ψ‖² = volume (ψ '' {‖ψ w‖ < M}) ≤ π M²` (the image lies in the disc of radius `M`), and the polar-coordinate lower bound for this integral also yields `∑ n‖bco ψ n‖²M^{-2n} ≤ M²`.

Proof actually formalised here (the "pole form" route, which is entirely contained in the
workspace): put `F z := ψ z⁻¹` and `H := Fext ψ`, so that `H` is holomorphic on the unit disc
(`differentiableOn_Fext_of_weakBound`), `F z = 1/z + H z` for `0 < ‖z‖ < 1` (`Fext_eq`) and `F` is
injective on the punctured disc (`hinj`).

* `Work.Koebe.sArea_nonpos` gives `(sArea F r).re ≤ 0` for `0 < r < 1`, where
  `sArea F r = (2i)⁻¹ ∮_{|z|=r} conj (F z) · F' z dz` is the signed area enclosed by the curve
  `θ ↦ F (r e^{iθ})` (a purely geometric statement).
* `Work.Koebe.gwSignedAreaPartial` gives, for every truncation length `N`,
  `π (∑_{n<N} n ‖gco H n‖² r^{2n} - r⁻²) ≤ (sArea F r).re` (the Parseval/residue computation).
  Since `Work.Koebe.gco (Fext ψ) n = bco ψ n` (`gco_Fext_eq_bco`), the `N = 2` instance reads
  `π (‖bco ψ 1‖² r² - r⁻²) ≤ 0`, i.e. `‖bco ψ 1‖ ≤ r⁻²`, and letting `r ↑ 1` gives the claim
  (`bco_one_of_area`). -/
lemma bco_one_le_one (ψ : ℂ → ℂ) (W C : ℝ) (hW : 1 < W)
    (hd : DifferentiableOn ℂ ψ {w : ℂ | 1 < ‖w‖})
    (hinj : Set.InjOn ψ {w : ℂ | 1 < ‖w‖})
    (hb : ∀ w, W ≤ ‖w‖ → ‖ψ w - w‖ ≤ C) :
    ‖bco ψ 1‖ ≤ 1 := by
  refine bco_one_of_area ψ ?_
  intro r hr hr1 N
  have hH : DifferentiableOn ℂ (Fext ψ) (Metric.ball 0 1) :=
    differentiableOn_Fext_of_weakBound ψ W C hW hd hb
  have hF : Set.InjOn (fun z : ℂ => ψ z⁻¹) (Metric.ball 0 1 \ {0}) := by
    intro z hz z' hz' hzz'
    have hz0 : z ≠ 0 := by simpa using hz.2
    have hz'0 : z' ≠ 0 := by simpa using hz'.2
    have hz1 : 1 < ‖z⁻¹‖ := by
      rw [norm_inv, one_lt_inv₀ (norm_pos_iff.mpr hz0)]
      have hzin := hz.1
      rwa [Metric.mem_ball, dist_zero_right] at hzin
    have hz1' : 1 < ‖z'⁻¹‖ := by
      rw [norm_inv, one_lt_inv₀ (norm_pos_iff.mpr hz'0)]
      have hzin := hz'.1
      rwa [Metric.mem_ball, dist_zero_right] at hzin
    exact inv_injective (hinj hz1 hz1' hzz')
  have hexp : ∀ z ∈ Metric.ball 0 1 \ {0}, ψ z⁻¹ = 1 / z + Fext ψ z := by
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz.2
    rw [Fext_eq ψ hz0, one_div]
    ring
  have hlow := Work.Koebe.gwSignedAreaPartial (fun z : ℂ => ψ z⁻¹) (Fext ψ) hH hF hexp hr hr1 N
  have hup := Work.Koebe.sArea_nonpos (fun z : ℂ => ψ z⁻¹) (Fext ψ) hH hF hexp hr hr1
  have hsum_eq : (∑ n ∈ Finset.range N, (n : ℝ) * ‖Work.Koebe.gco (Fext ψ) n‖ ^ 2 * r ^ (2 * n))
      = ∑ n ∈ Finset.range N, (n : ℝ) * ‖bco ψ n‖ ^ 2 * r ^ (2 * n) :=
    Finset.sum_congr rfl (fun n _ => by rw [gco_Fext_eq_bco ψ n])
  rw [hsum_eq] at hlow
  exact le_trans hlow hup

end Work.LandLeaves.koebeDerivAux
