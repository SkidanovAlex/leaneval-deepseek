import Mathlib
import Submission.Work.Mostow.horSpec
import Submission.Work.Mostow.levYcFormula

/-!
# The flat action of a stabiliser that acts properly on a horosphere

Let `ξ ∈ Sph n` be a boundary point, `D > 0`, and `G ≤ PO n 1` a subgroup all of whose elements
preserve the level function `lev ξ`.  On the horosphere of level `D` at `ξ`, an element `g ∈ G`
acts in the flat coordinates `yc ξ ·` of `ξ^⊥`; the hypothesis

`hprop : ∀ u₀, lev ξ u₀ = D → ∀ K compact, {g : G | g • u₀ ∈ K}.Finite`

says that this action is *proper*: for a base point on the level-`D` horosphere, only finitely many
group elements map it into a given compact set.

The lemma `flatActProper` transfers properness of the action on the horosphere (as tested against
points of `ℍⁿ`) to properness of the *flat* action on a compact piece `K ⊆ ξ^⊥` of the flat
coordinate space: the set of `g ∈ G` which map some point of the compact set
`{hptOf ξ y D | y ∈ K}` (level `D`, flat coordinate in `K`) back into it is finite.

## Proof

If `K = ∅` there is nothing to show.  Otherwise fix `y₀ ∈ K`.  Since `K` is compact it is bounded,
say `‖z‖ ≤ C` for `z ∈ K`; put `M = C + ‖y₀‖`, so that `‖z - y₀‖ ≤ M` for every `z ∈ K`.

For `g` counted in the conclusion pick `y, y' ∈ K` with `yc ξ (g • hptOf ξ y D) = y'`.  Because `g`
preserves the level and `g • hptOf ξ y D` has level `D`, the identity `hptOf_yc` gives
`g • hptOf ξ y D = hptOf ξ y' D`.  Hence, using the isometry property of the action, the triangle
inequality and the flat distance formula `hptOf_hdist`,

`hdist (g • u₀) u₀ ≤ hdist (g • u₀) (g • hptOf ξ y D) + hdist (g • hptOf ξ y D) u₀`
`  = hdist u₀ (hptOf ξ y D) + hdist (hptOf ξ y' D) u₀`
`  ≤ 2 * R`,  where `u₀ = hptOf ξ y₀ D` and `R = arcosh (1 + (D M)²/2)`.

So the counted set is contained in `{g : G | g • u₀ ∈ {v | hdist u₀ v ≤ 2 R}}`, which is finite by
`hprop` applied to the compact `hdist`-ball of `HypIsometryProp`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

theorem flatActProper (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n) (D : ℝ) (hD : 0 < D)
    (G : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    (hlev : ∀ g ∈ G, ∀ u : Submission.Mostow.E n,
      Work.Mostow.lev ξ ((g : LeanEval.Geometry.MostowRigidity.PO n 1) • u) = Work.Mostow.lev ξ u)
    (hprop : ∀ u₀ : Submission.Mostow.E n, Work.Mostow.lev ξ u₀ = D →
      ∀ K : Set (Submission.Mostow.E n), IsCompact K →
      {g : G | (g : LeanEval.Geometry.MostowRigidity.PO n 1) • u₀ ∈ K}.Finite)
    (K : Set (Submission.Mostow.E n)) (hK : IsCompact K)
    (hKW : ∀ y ∈ K, inner ℝ y ξ = 0) :
    {g : G | ∃ y ∈ K, ∃ y' ∈ K,
      Work.Mostow.yc ξ ((g : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.hptOf ξ y D) = y'}.Finite := by
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  by_cases hne : K.Nonempty
  · obtain ⟨y₀, hy₀⟩ := hne
    have hy₀W : inner ℝ y₀ ξ = 0 := hKW y₀ hy₀
    have hlev₀ : lev ξ (hptOf ξ y₀ D) = D := (hptOf_level ξ hξ D hD y₀ hy₀W).1
    -- `K` is bounded, so the flat coordinate of any point of `K` is within `M` of `y₀`.
    obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
    have hC0 : 0 ≤ C := le_trans (norm_nonneg y₀) (hC y₀ hy₀)
    set M : ℝ := C + ‖y₀‖ with hMdef
    have hMnn : 0 ≤ M := by rw [hMdef]; positivity
    have hM : ∀ z ∈ K, ‖z - y₀‖ ≤ M := by
      intro z hz
      have h1 : ‖z - y₀‖ ≤ ‖z‖ + ‖y₀‖ := norm_sub_le _ _
      have h2 : ‖z‖ ≤ C := hC z hz
      rw [hMdef]; linarith
    set R : ℝ := Real.arcosh (1 + (D * M) ^ 2 / 2) with hRdef
    -- properness of the hyperbolic action, tested on the compact `hdist`-ball of radius `2 R`
    have hfin : {g : G | (g : PO n 1) • hptOf ξ y₀ D ∈
        {v : E n | hdist (hptOf ξ y₀ D) v ≤ 2 * R}}.Finite :=
      hprop (hptOf ξ y₀ D) hlev₀ _ (hI'.ball_compact _ _)
    refine hfin.subset ?_
    rintro g ⟨y, hyK, y', hy'K, hyc⟩
    have hyW : inner ℝ y ξ = 0 := hKW y hyK
    have hy'W : inner ℝ y' ξ = 0 := hKW y' hy'K
    -- `g` preserves the level, hence `g • hptOf ξ y D` is the point of level `D` with flat
    -- coordinate `yc ξ (g • hptOf ξ y D) = y'`, i.e. it is `hptOf ξ y' D`.
    have hglevel : lev ξ ((g : PO n 1) • hptOf ξ y D) = D := by
      rw [hlev (g : PO n 1) g.2 (hptOf ξ y D)]
      exact (hptOf_level ξ hξ D hD y hyW).1
    have hgpt : (g : PO n 1) • hptOf ξ y D = hptOf ξ y' D := by
      have h := hptOf_yc ξ hξ D hD ((g : PO n 1) • hptOf ξ y D) hglevel
      rw [hyc] at h
      exact h.symm
    have hA : hdist (hptOf ξ y₀ D) (hptOf ξ y D)
        = Real.arcosh (1 + (D * ‖y₀ - y‖) ^ 2 / 2) :=
      hptOf_hdist ξ hξ D hD y₀ y hy₀W hyW
    have hB : hdist (hptOf ξ y' D) (hptOf ξ y₀ D)
        = Real.arcosh (1 + (D * ‖y' - y₀‖) ^ 2 / 2) :=
      hptOf_hdist ξ hξ D hD y' y₀ hy'W hy₀W
    have hle1 : Real.arcosh (1 + (D * ‖y₀ - y‖) ^ 2 / 2) ≤ R := by
      rw [hRdef]
      refine (Real.arcosh_le_arcosh (by positivity) (by positivity)).mpr ?_
      have h1 : ‖y₀ - y‖ ≤ M := by rw [norm_sub_rev]; exact hM y hyK
      have h2 : D * ‖y₀ - y‖ ≤ D * M := mul_le_mul_of_nonneg_left h1 (le_of_lt hD)
      have h3 : 0 ≤ D * ‖y₀ - y‖ := mul_nonneg (le_of_lt hD) (norm_nonneg _)
      have h4 : (D * ‖y₀ - y‖) ^ 2 ≤ (D * M) ^ 2 := pow_le_pow_left₀ h3 h2 2
      linarith [div_le_div_of_nonneg_right h4 (by norm_num : (0:ℝ) ≤ 2)]
    have hle2 : Real.arcosh (1 + (D * ‖y' - y₀‖) ^ 2 / 2) ≤ R := by
      rw [hRdef]
      refine (Real.arcosh_le_arcosh (by positivity) (by positivity)).mpr ?_
      have h1 : ‖y' - y₀‖ ≤ M := hM y' hy'K
      have h2 : D * ‖y' - y₀‖ ≤ D * M := mul_le_mul_of_nonneg_left h1 (le_of_lt hD)
      have h3 : 0 ≤ D * ‖y' - y₀‖ := mul_nonneg (le_of_lt hD) (norm_nonneg _)
      have h4 : (D * ‖y' - y₀‖) ^ 2 ≤ (D * M) ^ 2 := pow_le_pow_left₀ h3 h2 2
      linarith [div_le_div_of_nonneg_right h4 (by norm_num : (0:ℝ) ≤ 2)]
    -- the triangle inequality, together with `isom_smul`, gives the uniform bound
    have htri := hI'.triangle ((g : PO n 1) • hptOf ξ y₀ D)
      ((g : PO n 1) • hptOf ξ y D) (hptOf ξ y₀ D)
    rw [hI'.isom_smul (g : PO n 1) (hptOf ξ y₀ D) (hptOf ξ y D), hgpt, hA, hB] at htri
    show hdist (hptOf ξ y₀ D) ((g : PO n 1) • hptOf ξ y₀ D) ≤ 2 * R
    rw [hI'.symm]
    linarith
  · have hKe : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hKe]
    simp

end Work.Mostow
