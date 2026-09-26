import Mathlib
import Submission.Work.Drive.Mono.WindowCase.CupDefs
import Submission.Work.Drive.Mono.CylRegionDefs
import Submission.Work.CoreTopology.Disk

/-!
# The range of the collapse-aware parametrisation of the cup

This file computes the range of `Work.Drive.Mono.WindowCase.cupE e g`, the collapse-aware
parametrisation of the *cup*

`E = {(x, 0) | x ∈ K} ∪ {(x, y) | x ∈ frontier K, 0 ≤ y ≤ g x}`

over a plane disc `K = range e` (parametrised by the closed unit disc `𝔻 ⊆ ℂ`) with `g ≥ 0` on `K`:

`cupE_range`:  `range (cupE e g) = {(x,0) | x ∈ K} ∪ {(x,y) | x ∈ frontier K, 0 ≤ y ≤ g x}`.

## Route

`cupE` sends `z` to the bottom point `e (z / max (G z) ‖z‖)` at height `0` when `‖z‖ ≤ G z`, and to
the wall point `e (z/‖z‖)` at the height `g (e (z/‖z‖)) · (‖z‖ - G z)/(1 - G z)` otherwise, where
`G z = 1/2 + 1/(2 (1 + g (e (z/‖z‖)))) ∈ (1/2, 1]` is the direction dependent threshold.

* The bottom branch lands in `K × {0}`; the wall branch lands over `frontier K` (the radial
  projection of a wall point has norm `1`, and every point of the unit circle is some
  `circlePoint θ`), with height in `[0, g]` because `G z < ‖z‖ ≤ 1` forces `1 - G z > 0` and
  `0 ≤ (‖z‖ - G z)/(1 - G z) ≤ 1`.
* Conversely, a point `(e w, 0)` of the bottom disc is hit by `z = G w • w` (the threshold is
  constant along a ray, and `G w ≤ 1`, so this point lies in `𝔻` and satisfies `‖z‖ ≤ G z`);
  a wall point `(e u, c)` with `c > 0` is hit by `z = t • u` with `‖u‖ = 1` and
  `t = G u + c (1 - G u)/g (e u) ∈ (G u, 1]`, which lands in the wall branch at height exactly `c`;
  wall points with `c = 0` lie over `frontier K ⊆ K` and are already in the bottom branch.
-/

namespace Work.Drive.Mono.WindowCase

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

set_option linter.unusedVariables false

local notation "𝔻" => Metric.closedBall (0 : ℂ) 1

/-! ## Elementary facts about the model disc -/

theorem cupE_coe_norm_le_one (z : 𝔻) : ‖(z : ℂ)‖ ≤ 1 := by
  have h := z.2
  rwa [Metric.mem_closedBall, dist_zero_right] at h

/-- The core parametrisation of the unit circle hits every point of the boundary sphere. -/
theorem cupE_exists_circlePoint_eq (z : 𝔻) (hz : ‖(z : ℂ)‖ = 1) :
    ∃ θ : ℝ, Work.CoreTopology.circlePoint θ = z := by
  refine ⟨Complex.arg (z : ℂ), Subtype.ext ?_⟩
  rw [Work.CoreTopology.circlePoint_coe]
  have hz' : ((‖(z : ℂ)‖ : ℝ) : ℂ) = 1 := by rw [hz]; norm_num
  have h := Complex.norm_mul_exp_arg_mul_I (z : ℂ)
  rw [hz', one_mul] at h
  exact h

theorem cupE_norm_circlePoint (θ : ℝ) : ‖(Work.CoreTopology.circlePoint θ : ℂ)‖ = 1 := by
  rw [Work.CoreTopology.circlePoint_coe]
  exact Complex.norm_exp_ofReal_mul_I θ

/-- `cupDir` only depends on the ray through the origin of the disc. -/
theorem cupE_cupDir_eq_of_coe_eq_mul {z w : 𝔻} {c : ℝ} (hc : 0 < c)
    (h : (z : ℂ) = (c : ℂ) * (w : ℂ)) : cupDir z = cupDir w := by
  refine Subtype.ext ?_
  rw [cupDir_coe, cupDir_coe, h, norm_mul, Complex.norm_of_nonneg (le_of_lt hc)]
  rw [show ((c * ‖(w : ℂ)‖ : ℝ) : ℂ) = (c : ℂ) * ((‖(w : ℂ)‖ : ℝ) : ℂ) by push_cast; ring]
  exact mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hc))

/-- The threshold `cupG` only depends on the direction. -/
theorem cupE_cupG_congr {e : C(𝔻, EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} {z w : 𝔻} (h : cupDir z = cupDir w) :
    cupG e g z = cupG e g w := by
  simp only [cupG, h]

/-! ## The bottom branch reaches the whole base disc -/

theorem cupE_exists_eq_bottom (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → ℝ) (hgK : ∀ x ∈ Set.range e, 0 ≤ g x) (w : 𝔻) :
    ∃ z : 𝔻, cupE e g z = cmk (e w) 0 := by
  have hm : 0 ≤ g (e (cupDir w)) := hgK _ (Set.mem_range_self _)
  have hGpos : 0 < cupG e g w := cupG_pos hm
  have hGle : cupG e g w ≤ 1 := cupG_le_one hm
  have hw1 : ‖(w : ℂ)‖ ≤ 1 := cupE_coe_norm_le_one w
  have hmem : (cupG e g w : ℂ) * (w : ℂ) ∈ 𝔻 := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_of_nonneg (le_of_lt hGpos)]
    calc cupG e g w * ‖(w : ℂ)‖ ≤ cupG e g w * 1 :=
          mul_le_mul_of_nonneg_left hw1 (le_of_lt hGpos)
      _ = cupG e g w := mul_one _
      _ ≤ 1 := hGle
  refine ⟨⟨(cupG e g w : ℂ) * (w : ℂ), hmem⟩, ?_⟩
  have hcoe : ((⟨(cupG e g w : ℂ) * (w : ℂ), hmem⟩ : 𝔻) : ℂ)
      = (cupG e g w : ℂ) * (w : ℂ) := rfl
  have hdir : cupDir ⟨(cupG e g w : ℂ) * (w : ℂ), hmem⟩ = cupDir w :=
    cupE_cupDir_eq_of_coe_eq_mul hGpos rfl
  have hG : cupG e g ⟨(cupG e g w : ℂ) * (w : ℂ), hmem⟩ = cupG e g w := cupE_cupG_congr hdir
  have hnorm : ‖((⟨(cupG e g w : ℂ) * (w : ℂ), hmem⟩ : 𝔻) : ℂ)‖ = cupG e g w * ‖(w : ℂ)‖ := by
    rw [hcoe, norm_mul, Complex.norm_of_nonneg (le_of_lt hGpos)]
  have hbot : ‖((⟨(cupG e g w : ℂ) * (w : ℂ), hmem⟩ : 𝔻) : ℂ)‖
      ≤ cupG e g ⟨(cupG e g w : ℂ) * (w : ℂ), hmem⟩ := by
    rw [hnorm, hG]
    exact mul_le_of_le_one_right (le_of_lt hGpos) hw1
  rw [cupE_eq_cmk_bottom hbot]
  have hscaled : cupScaled e g ⟨(cupG e g w : ℂ) * (w : ℂ), hmem⟩ = w := by
    refine Subtype.ext ?_
    rw [cupScaled_coe, hcoe, hG, hnorm]
    rw [max_eq_left (mul_le_of_le_one_right (le_of_lt hGpos) hw1)]
    exact mul_div_cancel_left₀ ((w : ℂ)) (Complex.ofReal_ne_zero.mpr (ne_of_gt hGpos))
  rw [hscaled]

/-! ## The wall branch reaches the whole wall over a boundary direction -/

theorem cupE_exists_eq_wall (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → ℝ) {u : 𝔻} (hu : ‖(u : ℂ)‖ = 1) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c ≤ g (e u)) : ∃ z : 𝔻, cupE e g z = cmk (e u) c := by
  have hgu : 0 < g (e u) := lt_of_lt_of_le hc0 hc1
  have hmu : 0 ≤ g (e (cupDir u)) := by rw [cupDir_eq_self hu]; exact le_of_lt hgu
  set G : ℝ := cupG e g u with hGdef
  have hGpos : 0 < G := by rw [hGdef]; exact cupG_pos hmu
  have hGle : G ≤ 1 := by rw [hGdef]; exact cupG_le_one hmu
  have hGne : G ≠ 1 := by
    rw [hGdef]
    intro h
    have h0 : g (e (cupDir u)) = 0 := (cupG_eq_one_iff hmu).mp h
    rw [cupDir_eq_self hu] at h0
    linarith
  have hGlt : G < 1 := lt_of_le_of_ne hGle hGne
  have h1G : 0 < 1 - G := by linarith
  set t : ℝ := G + c * (1 - G) / g (e u) with htdef
  have hpos : 0 < c * (1 - G) / g (e u) := div_pos (mul_pos hc0 h1G) hgu
  have htpos : 0 < t := by rw [htdef]; linarith
  have htle : t ≤ 1 := by
    have h : c * (1 - G) / g (e u) ≤ (1 - G) := by
      rw [div_le_iff₀ hgu]
      calc c * (1 - G) ≤ g (e u) * (1 - G) :=
            mul_le_mul_of_nonneg_right hc1 (le_of_lt h1G)
        _ = (1 - G) * g (e u) := mul_comm _ _
    rw [htdef]; linarith
  have hmem : (t : ℂ) * (u : ℂ) ∈ 𝔻 := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul,
      Complex.norm_of_nonneg (le_of_lt htpos), hu, mul_one]
    exact htle
  refine ⟨⟨(t : ℂ) * (u : ℂ), hmem⟩, ?_⟩
  have hcoe : ((⟨(t : ℂ) * (u : ℂ), hmem⟩ : 𝔻) : ℂ) = (t : ℂ) * (u : ℂ) := rfl
  have hdir : cupDir ⟨(t : ℂ) * (u : ℂ), hmem⟩ = u := by
    have h := cupE_cupDir_eq_of_coe_eq_mul (z := ⟨(t : ℂ) * (u : ℂ), hmem⟩) (w := u) htpos
      (by rw [hcoe])
    rwa [cupDir_eq_self hu] at h
  have hdiru : cupDir ⟨(t : ℂ) * (u : ℂ), hmem⟩ = cupDir u := by rw [hdir, cupDir_eq_self hu]
  have hG : cupG e g ⟨(t : ℂ) * (u : ℂ), hmem⟩ = G := by rw [cupE_cupG_congr hdiru, ← hGdef]
  have hnorm : ‖((⟨(t : ℂ) * (u : ℂ), hmem⟩ : 𝔻) : ℂ)‖ = t := by
    rw [hcoe, norm_mul, Complex.norm_of_nonneg (le_of_lt htpos), hu, mul_one]
  have hwall : cupG e g ⟨(t : ℂ) * (u : ℂ), hmem⟩ < ‖((⟨(t : ℂ) * (u : ℂ), hmem⟩ : 𝔻) : ℂ)‖ := by
    rw [hG, hnorm]; exact lt_add_of_pos_right _ hpos
  rw [cupE_eq_cmk_wall hwall, hdir, hG, hnorm]
  rw [cmk_eq_cmk_iff]
  refine ⟨rfl, ?_⟩
  rw [htdef]
  have hgnz : g (e u) ≠ 0 := ne_of_gt hgu
  have h1nz : (1 : ℝ) - G ≠ 0 := ne_of_gt h1G
  field_simp
  ring

/-! ## The range -/

theorem cupE_range
    {K : Set (EuclideanSpace ℝ (Fin 2))} {g : EuclideanSpace ℝ (Fin 2) → ℝ}
    (e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2)))
    (he_inj : Function.Injective e) (he_range : Set.range e = K)
    (he_bdry : Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier K)
    (hgc : ContinuousOn g K) (hg0 : ∀ x ∈ K, 0 ≤ g x) :
    Set.range (Work.Drive.Mono.WindowCase.cupE e g) =
      {P : EuclideanSpace ℝ (Fin 3) | Work.Drive.Mono.cproj P ∈ K ∧
        Work.Drive.Mono.clast P = 0} ∪
      {P : EuclideanSpace ℝ (Fin 3) | Work.Drive.Mono.cproj P ∈ frontier K ∧
        0 ≤ Work.Drive.Mono.clast P ∧ Work.Drive.Mono.clast P ≤ g (Work.Drive.Mono.cproj P)} := by
  have hgK : ∀ x ∈ Set.range e, 0 ≤ g x := fun x hx => hg0 x (he_range ▸ hx)
  -- the bottom part of the range, in terms of the parametrisation
  have hbot_mem : ∀ {P : EuclideanSpace ℝ (Fin 3)}, cproj P ∈ Set.range e → clast P = 0 →
      P ∈ Set.range (cupE e g) := by
    intro P h1 h2
    obtain ⟨w, hw⟩ := h1
    obtain ⟨z, hz⟩ := cupE_exists_eq_bottom e g hgK w
    refine ⟨z, ?_⟩
    rw [hz, ← cmk_cproj_clast P, ← hw, h2]
  refine Set.Subset.antisymm ?_ ?_
  · -- every point of the cup is in the range
    rintro P ⟨z, rfl⟩
    by_cases h : ‖(z : ℂ)‖ ≤ cupG e g z
    · left
      rw [cupE_of_le h]
      exact ⟨by rw [cproj_cupBottom]; exact he_range ▸ Set.mem_range_self _,
        clast_cupBottom e g z⟩
    · right
      rw [cupE_of_gt (lt_of_not_ge h)]
      have hlt : cupG e g z < ‖(z : ℂ)‖ := lt_of_not_ge h
      have hznz : (z : ℂ) ≠ 0 := by
        intro h0
        have hp : 0 < cupG e g z := cupG_pos (hgK _ (Set.mem_range_self _))
        rw [h0, norm_zero] at hlt
        linarith
      have hnorm1 : ‖(cupDir z : ℂ)‖ = 1 := norm_cupDir_of_ne_zero hznz
      obtain ⟨θ, hθ⟩ := cupE_exists_circlePoint_eq (cupDir z) hnorm1
      have hgu : 0 ≤ g (e (cupDir z)) := hgK _ (Set.mem_range_self _)
      have hGlt1 : cupG e g z < 1 := lt_of_lt_of_le hlt (cupE_coe_norm_le_one z)
      have hden : 0 < 1 - cupG e g z := by linarith
      have hnum : 0 ≤ ‖(z : ℂ)‖ - cupG e g z := by linarith
      refine ⟨?_, ?_, ?_⟩
      · rw [cproj_cupWall, ← he_bdry]
        exact ⟨θ, by show e (Work.CoreTopology.circlePoint θ) = e (cupDir z); rw [hθ]⟩
      · rw [clast_cupWall]
        exact mul_nonneg hgu (div_nonneg hnum (le_of_lt hden))
      · rw [clast_cupWall, cproj_cupWall]
        refine mul_le_of_le_one_right hgu ?_
        rw [div_le_one hden]
        linarith [cupE_coe_norm_le_one z]
  · -- every point of the target set is in the range
    intro P hP
    rcases hP with ⟨hP1, hP2⟩ | ⟨hP1, hP2, hP3⟩
    · rw [← he_range] at hP1
      exact hbot_mem hP1 hP2
    · rw [← he_bdry] at hP1
      obtain ⟨θ, hθ⟩ := hP1
      have hθ' : e (Work.CoreTopology.circlePoint θ) = cproj P := hθ
      have hu : ‖(Work.CoreTopology.circlePoint θ : ℂ)‖ = 1 := cupE_norm_circlePoint θ
      by_cases hc : clast P = 0
      · exact hbot_mem (by rw [← hθ']; exact Set.mem_range_self _) hc
      · have hcpos : 0 < clast P := lt_of_le_of_ne hP2 (Ne.symm hc)
        obtain ⟨z, hz⟩ := cupE_exists_eq_wall e g hu hcpos (by rw [hθ']; exact hP3)
        refine ⟨z, ?_⟩
        calc cupE e g z = cmk (e (Work.CoreTopology.circlePoint θ)) (clast P) := hz
          _ = cmk (cproj P) (clast P) := by rw [← hθ']
          _ = P := cmk_cproj_clast P

end

end Work.Drive.Mono.WindowCase
