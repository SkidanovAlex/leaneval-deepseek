import Mathlib
import Submission.Work.ELNest.Setup
import Submission.Work.ELNest.Side
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.isOpen_pairSide

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The inverse branch `g` of `F` agrees with the local inverse at the parabolic point

Let `S : NestData c` be the nest data at the parabolic point `z₁ = S.d.z₁`, and let
`g = S.g` be the inverse branch of `F c` on the level-`0` region `Q̂₀ = S.Q 0`: `g` maps
`Q̂₀` into `Q̂₁ = S.Q 1` and `F c (g z) = z` there (`g_mem`, `g_left`).  Since `F c` is a
bijection `Q̂₁ → Q̂₀` (`pbQ 0`), `g` is the inverse of that bijection.

The lemma says that any *continuous* right inverse `h` of `F c` at `z₁` fixing `z₁` agrees
with `g` on a neighbourhood of `z₁` inside `Q̂₀`.  The proof is the local uniqueness of the
inverse branch at the parabolic point: `h` is a right inverse near `z₁`, so on a small
neighbourhood `h z` lies in `Q̂₁`; indeed `h z` is near `z₁` (`hcont`, `hfix`), hence

* `h z` lies on the near side of the `α`-pair: the Leau--Fatou flower `cover` places it
  either in the attracting petal `Pa` (impossible, `F` maps `Pa` into `Pa ⊆ pairSide P₀`
  while `z = F (h z) ∈ Q̂₀` lies on the *near* side, and the two sides are disjoint) or in
  `Ψ (H_R)` with `R` the level of `SP`; then `Ψ u ∈ pairSide P₀` implies
  `z = Ψ (u+1) ∈ pairSide P₀` (`SP`), and `Ψ u ∈ pairCurve P₀` implies
  `z = F (Ψ u) ∈ F '' pairCurve P₀ = pairCurve P₀` (`curveF`); both are impossible because
  `z` lies on the near side, so `Ψ u` lies on the near side by the side decomposition
  `sides_P0.union_eq`;
* `h z` lies on the near side of `Qp 1` because `pairSideNear (Qp 1)` is open and contains
  `z₁` (`z1_near_Q`, `isOpen_pairSide`);
* `pot (h z) = pot z / 1024` (`pot_F`), so the potential of `h z` is below the level of `Q̂₁`.

Hence `h z ∈ Q̂₁`, and since `F c` is injective on `Q̂₁` (`pbQ 0`), `g z = h z`.
-/

open Filter Set Topology Function
open scoped Topology ComplexConjugate

noncomputable section

namespace Work.ELNest

open Work.EL

variable {c : ℂ}

/-- A side of a co-landing pair is contained in the complement of its pair curve. -/
theorem pairSideNear_subset_compl {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} (P : CoPair hN) :
    pairSideNear P ⊆ (pairCurve P)ᶜ := by
  intro w hw
  exact connectedComponentIn_subset _ _ hw

/-- **The inverse branch `g` is the local inverse of `F c` at `z₁`.**  A continuous right
inverse `h` of `F c` fixing `z₁` agrees with `S.g` on a neighbourhood of `z₁` intersected with
the level-`0` region `S.Q 0` of the nest. -/
theorem g_eq_localInverse {c : ℂ} (S : Work.ELNest.NestData c) (h : ℂ → ℂ)
    (hright : {z : ℂ | Work.ELNest.F c (h z) = z} ∈ nhds S.d.z₁)
    (hcont : ContinuousAt h S.d.z₁) (hfix : h S.d.z₁ = S.d.z₁) :
    ∃ ρ > 0, ∀ z ∈ S.Q 0 ∩ Metric.ball S.d.z₁ ρ, S.g z = h z := by
  -- `F` fixes the parabolic point
  have hFz₁ : F c S.d.z₁ = S.d.z₁ := by
    rw [F_eq_tantibar, show (10 : ℕ) = 5 + 5 from rfl, Function.iterate_add_apply,
      S.d.per_half, S.d.per_half]
  -- `hright` as an eventually statement
  have hev_right : ∀ᶠ z in 𝓝 S.d.z₁, F c (h z) = z := hright
  obtain ⟨ρ_h, hρ_h, hh_right⟩ := Metric.mem_nhds_iff.mp hev_right
  -- the `SP` level of the flower, and the cover radius
  obtain ⟨R, hR⟩ := S.SP
  obtain ⟨r, hr_pos, hcover⟩ := S.fl.cover R
  -- the near side of `Qp 1` is an open neighbourhood of `z₁`
  obtain ⟨δ, hδ_pos, hδ_sub⟩ :=
    Metric.isOpen_iff.mp (Work.ELTop.isOpen_pairSide S.d.hN (S.Qp 1)).2 S.d.z₁ (S.z1_near_Q 1)
  -- the continuity radius of `h` at `z₁`
  obtain ⟨ρ_c, hρ_c, hh_cont⟩ :=
    Metric.continuousAt_iff.mp hcont (min r δ) (lt_min hr_pos hδ_pos)
  refine ⟨min ρ_h ρ_c, lt_min hρ_h hρ_c, ?_⟩
  intro z hz
  obtain ⟨hzQ, hzball⟩ := hz
  rw [Metric.mem_ball] at hzball
  have hzρh : dist z S.d.z₁ < ρ_h := lt_of_lt_of_le hzball (min_le_left _ _)
  have hzρc : dist z S.d.z₁ < ρ_c := lt_of_lt_of_le hzball (min_le_right _ _)
  have hFhz : F c (h z) = z := hh_right hzρh
  have hh_ball : dist (h z) S.d.z₁ < min r δ := by
    simpa [hfix] using hh_cont hzρc
  have hh_r : ‖h z - S.d.z₁‖ < r := by
    rw [← dist_eq_norm]
    exact lt_of_lt_of_le hh_ball (min_le_left _ _)
  have hh_δ : dist (h z) S.d.z₁ < δ := lt_of_lt_of_le hh_ball (min_le_right _ _)
  -- `z` lies on the near side of the `α`-pair, with small potential
  have hz_near : z ∈ pairSideNear S.P0 := by
    have hh : z ∈ polyRegion [S.P0, S.Qp 0] (Qlev S.L 0) := hzQ
    rw [S.Qmem 0] at hh
    exact hh.1.1
  have hpot_z : pot S.d.hN z < Real.log (Qlev S.L 0) := by
    have hh : z ∈ polyRegion [S.P0, S.Qp 0] (Qlev S.L 0) := hzQ
    rw [S.Qmem 0] at hh
    exact hh.2
  -- `z ≠ z₁` because `z₁` lies on the pair curve
  have hz_ne : z ≠ S.d.z₁ := by
    intro hzz
    have h1 : S.d.z₁ ∈ pairSideNear S.P0 := hzz ▸ hz_near
    have h2 : S.d.z₁ ∈ pairCurve S.P0 := by
      rw [← S.P0y]
      exact (mem_pairCurve_iff S.P0 S.P0.y).mpr (Or.inr (Or.inl rfl))
    exact pairSideNear_subset_compl S.P0 h1 h2
  -- `h z ≠ z₁`: otherwise `z = F (h z) = F z₁ = z₁`
  have hhz_ne : h z ≠ S.d.z₁ := by
    intro hhz
    exact hz_ne (by rw [← hFhz, hhz, hFz₁])
  have hhz_pos : 0 < ‖h z - S.d.z₁‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hhz_ne
  -- `z` is not on the far side of the `α`-pair
  have hz_notfar : z ∉ pairSide S.P0 :=
    fun h => Set.disjoint_left.mp S.side_disj h hz_near
  -- the flower places `h z` on the near side of the `α`-pair
  have hhz_near : h z ∈ pairSideNear S.P0 := by
    rcases hcover (h z) hhz_pos hh_r with hPa | ⟨w, hw, hwz⟩
    · have hzpa : z ∈ S.fl.Pa := by rw [← hFhz]; exact S.fl.mapsTo_Pa hPa
      exact absurd (S.Pa_far hzpa) hz_notfar
    · rw [← hwz]
      have hfar : S.fl.Ψ w ∉ pairSide S.P0 := by
        intro hc
        refine hz_notfar ?_
        rw [← hFhz, ← hwz, ← S.fl.Ψ_shift w]
        exact (hR w hw).mp hc
      have hcurve : S.fl.Ψ w ∉ pairCurve S.P0 := by
        intro hc
        refine pairSideNear_subset_compl S.P0 hz_near ?_
        rw [← hFhz, ← hwz, ← S.curveF]
        exact ⟨S.fl.Ψ w, hc, rfl⟩
      have h1 : S.fl.Ψ w ∈ pairSide S.P0 ∪ pairSideNear S.P0 := by
        rw [S.sides_P0.union_eq]
        exact hcurve
      rcases h1 with h1 | h1
      · exact absurd h1 hfar
      · exact h1
  -- `h z` lies on the near side of `Qp 1`, being near `z₁`
  have hhz_nearQ1 : h z ∈ pairSideNear (S.Qp 1) :=
    hδ_sub (Metric.mem_ball.mpr hh_δ)
  -- the potential computation
  have hlog0 : Real.log (Qlev S.L 0) = Real.log S.L := by simp [Qlev]
  have hlog1 : Real.log (Qlev S.L 1) = Real.log S.L / 1024 := by
    have h1 : Qlev S.L 1 = S.L ^ ((1 : ℝ) / 1024) := by simp [Qlev]
    rw [h1, Real.log_rpow (by linarith [S.hL])]
    ring
  have hpot_hz : pot S.d.hN (h z) = pot S.d.hN z / 1024 := by
    have hh := S.pot_F (h z)
    rw [hFhz] at hh
    linarith
  have hpot_hz_lt : pot S.d.hN (h z) < Real.log (Qlev S.L 1) := by
    rw [hpot_hz, hlog1]
    have h0 : pot S.d.hN z < Real.log S.L := by rwa [hlog0] at hpot_z
    linarith
  -- `h z` and `g z` both lie in the level-`1` region, where `F` is injective
  have hhz_mem : h z ∈ S.Q 1 := by
    show h z ∈ polyRegion [S.P0, S.Qp 1] (Qlev S.L 1)
    rw [S.Qmem 1]
    exact ⟨⟨hhz_near, hhz_nearQ1⟩, hpot_hz_lt⟩
  have hgz_mem : S.g z ∈ S.Q 1 := by
    show S.g z ∈ polyRegion [S.P0, S.Qp 1] (Qlev S.L 1)
    exact S.g_mem z hzQ
  have hg_left : F c (S.g z) = z := S.g_left z hzQ
  exact (S.pbQ 0).injOn hgz_mem hhz_mem (by rw [hg_left, hFhz])

end Work.ELNest
