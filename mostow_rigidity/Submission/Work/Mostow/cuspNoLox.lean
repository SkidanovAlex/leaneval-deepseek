import Mathlib
import Submission.Work.Mostow.cuspNoLoxRoute
import Submission.Work.Mostow.normalForm
import Submission.Work.Mostow.parabolic_not_commute_levelScaling
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.geomFiniteStabHorosphere

/-!
# A discrete subgroup cannot contain a level-scaling element fixing a parabolic cusp

`Work.Mostow.cuspNoLox`: let `Γ ≤ PO(n,1)` be discrete, let `q ∈ Γ` be parabolic with
`bd q ξ = ξ` for `ξ ∈ Sph n`, and let `g ∈ Γ` satisfy `bd g ξ = ξ`.  Then
`busemann ξ (g • 0) = 0`, i.e. `g` does not shift the horospheres based at the cusp `ξ` of `q`
(the Busemann cocycle `bCocy g ξ` vanishes).

## Two regimes

* `2 ≤ n`.  This is the discreteness argument already carried out in
  `Work.Mostow.geomFiniteStabHorosphere`: a parabolic element fixing `ξ` preserves the horospheres
  of `ξ`, an element with `bCocy g ξ ≠ 0` strictly scales them, and the conjugates
  `g ^ k * q * (g ^ k)⁻¹` would be pairwise distinct elements of `Γ` of uniformly bounded
  displacement from `0`, contradicting `finite_nearStab` (step 6 of the route file).  Here we
  simply call `gfsh_stab_cocycle_zero`, replacing `g` by `g⁻¹` when `bCocy g ξ < 0` — the sign of
  the level scaling is irrelevant (step 1 of the route file).

* `n ≤ 1`.  Then `ξ^⊥ = 0`, so the horospheres of `ξ` are single points: the flat coordinate
  `yc ξ u` vanishes identically (`cuspNoLox_yc_eq_zero_of_le_one`, from `finrank ℝ (E n) = n ≤ 1`)
  and `u` is determined by its level `lev ξ u`.  A parabolic element fixing `ξ` preserves the
  levels (`bCocy_parabolic`), hence fixes every point of `ℍⁿ` — contradicting parabolicity.  So in
  this regime the hypotheses are inconsistent and the claim holds vacuously.

Note that no small-dimension argument can be extracted from `gfsh_stab_cocycle_zero`, which
carries the hypothesis `2 ≤ n` (needed because for `n = 1` commuting parabolic elements do not
exist, so the final contradiction of the discreteness argument is only reached through the
triviality of `ξ^⊥`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-! ## The case `n ≤ 1`: the flat space `ξ^⊥` is trivial -/

/-- For `n ≤ 1` the unit sphere spans `E n`: every normalised flat coordinate vanishes. -/
lemma cuspNoLox_yc_eq_zero_of_le_one {n : ℕ} (hn : n ≤ 1) {ξ : E n} (hξ : ξ ∈ Sph n)
    (u : E n) : yc ξ u = 0 := by
  have hξξ : inner ℝ ξ ξ = (1 : ℝ) := hptOf_level_aux_inner_self hξ
  -- `E n` has dimension `≤ 1`, so it is spanned by the single vector `ξ`
  have hu : u = inner ℝ u ξ • ξ := by
    have hfr : Module.finrank ℝ (E n) ≤ 1 := by
      rw [finrank_euclideanSpace, Fintype.card_fin]
      exact hn
    obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hfr
    obtain ⟨c, hc⟩ := hv u
    obtain ⟨d, hd⟩ := hv ξ
    have h2 : d * d * inner ℝ v v = 1 := by
      rw [← hξξ, ← hd]
      simp only [real_inner_smul_left, real_inner_smul_right]
      ring
    have h3 : inner ℝ u ξ = c * d * inner ℝ v v := by
      rw [← hc, ← hd]
      simp only [real_inner_smul_left, real_inner_smul_right]
      ring
    have h4 : (c * d * inner ℝ v v) * d = c := by
      calc (c * d * inner ℝ v v) * d = c * (d * d * inner ℝ v v) := by ring
        _ = c := by rw [h2, mul_one]
    rw [h3, ← hd, ← hc, smul_smul, h4]
  have hinner : inner ℝ (inner ℝ u ξ • ξ) ξ = inner ℝ u ξ := by
    rw [real_inner_smul_left, hξξ, mul_one]
  have hwc : wc ξ u = 0 := by
    rw [wc, hu, hinner, sub_self]
  rw [yc, hwc, smul_zero]

/-- In dimension `≤ 1` there is no parabolic isometry with a boundary fixed point. -/
lemma cuspNoLox_no_parabolic_of_le_one {n : ℕ} (hn : n ≤ 1) (hA : POActionProp n)
    (hI : HypIsometryProp n) (q : PO n 1) (hq : IsParabolic q) (ξ : E n) (hξ : ξ ∈ Sph n)
    (hqξ : bd q ξ = ξ) : False := by
  -- a parabolic element fixing `ξ` preserves the Busemann function at `ξ` ...
  have hβ : busemann ξ (q • (0 : E n)) = 0 := by
    have h := bCocy_parabolic hA hI q hq ξ hξ hqξ
    rwa [bCocy, hqξ] at h
  -- ... hence every horosphere level at `ξ`
  have hlev : ∀ u : E n, lev ξ (q • u) = lev ξ u := by
    intro u
    rw [lev_smul_self (HypIsoData.ofProp hI) (POBasic.ofProp hA) ξ hξ q u hqξ]
    have h1 : lev ξ (q • (0 : E n)) = 1 := by
      rw [lev_eq_exp hξ, hβ, Real.exp_zero]
    rw [h1, mul_one]
  -- the level determines the point, so `q` fixes every point of `ℍⁿ`
  have hfix : ∀ u : E n, q • u = u := by
    intro u
    have hD : 0 < lev ξ u := lev_pos ξ hξ u
    have h1 : u = hptOf ξ (0 : E n) (lev ξ u) := by
      calc u = hptOf ξ (yc ξ u) (lev ξ u) := (hptOf_yc ξ hξ (lev ξ u) hD u rfl).symm
        _ = hptOf ξ 0 (lev ξ u) := by rw [cuspNoLox_yc_eq_zero_of_le_one hn hξ u]
    have h2 : q • u = hptOf ξ (0 : E n) (lev ξ u) := by
      calc q • u = hptOf ξ (yc ξ (q • u)) (lev ξ (q • u)) :=
            (hptOf_yc ξ hξ (lev ξ (q • u)) (lev_pos ξ hξ _) (q • u) rfl).symm
        _ = hptOf ξ 0 (lev ξ (q • u)) :=
            by rw [cuspNoLox_yc_eq_zero_of_le_one hn hξ (q • u)]
        _ = hptOf ξ 0 (lev ξ u) := by rw [hlev u]
    rw [h2, ← h1]
  exact hq.1 0 (hfix 0)

/-! ## The theorem -/

theorem cuspNoLox (n : ℕ) (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ))
    (q : LeanEval.Geometry.MostowRigidity.PO n 1) (hqmem : q ∈ Γ) (hq : Submission.Mostow.IsParabolic q)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n) (hqξ : Submission.Mostow.bd q ξ = ξ)
    (g : LeanEval.Geometry.MostowRigidity.PO n 1) (hgmem : g ∈ Γ) (hgξ : Submission.Mostow.bd g ξ = ξ) :
    Submission.Mostow.busemann ξ (g • (0 : Submission.Mostow.E n)) = 0 := by
  have hb : bCocy g ξ = 0 := by
    by_cases hn : 2 ≤ n
    · -- the discreteness argument of `geomFiniteStabHorosphere`
      rcases lt_trichotomy (bCocy g ξ) 0 with hlt | heq | hgt
      · -- `bCocy g ξ < 0`: apply it to `g⁻¹`, whose level scaling is positive
        have hbdi : bd g⁻¹ ξ = ξ := gfsh_bd_inv hA hξ hgξ
        have hci : 0 < bCocy g⁻¹ ξ := by
          rw [gfsh_bCocy_inv hA hI g hξ hgξ]
          linarith
        exact (gfsh_stab_cocycle_zero hA hI hn Γ hdisc q g⁻¹ hqmem (Γ.inv_mem hgmem)
          hq ξ hξ hqξ hbdi hci).elim
      · exact heq
      · exact (gfsh_stab_cocycle_zero hA hI hn Γ hdisc q g hqmem hgmem
          hq ξ hξ hqξ hgξ hgt).elim
    · -- `n ≤ 1`: parabolic elements fixing `ξ` do not exist
      exact (cuspNoLox_no_parabolic_of_le_one (by omega) hA hI q hq ξ hξ hqξ).elim
  rwa [bCocy, hgξ] at hb

end

end Work.Mostow
