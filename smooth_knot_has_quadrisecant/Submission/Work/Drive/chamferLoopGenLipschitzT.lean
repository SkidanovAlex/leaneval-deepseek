import Mathlib
import Submission.Work.Drive.chamferLoopGenLipAux

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-! ## Auxiliary estimates for `chamferLoopGenLipschitzT`

This file proves `Work.Drive.chamferLoopGenLipschitzT`, the Lipschitz continuity of the *scheduled*
generalised chamfer loop in the loop parameter `t`, with a constant uniform in the sweep parameter.

The route is:

* `Work.Drive.profLipConst` — the explicit Lipschitz constant for the *profile* of the loop;
* `Work.Drive.lipGlue` — gluing two `K`-Lipschitz functions that agree at a junction;
* `Work.Drive.chamferProf_lip` — the profile `u ↦ chamferLoopProf r D lay (α σ) (β σ) σ u` is
  `profLipConst`-Lipschitz, uniformly in `σ`;
* `Work.Drive.chamferProf_zero_eq_one` (in `chamferLoopGenLipAux`) — the profile loop is closed;
* `Work.Drive.sweepParam_lipschitz_of_closed` (in `chamferLoopGenLipAux`) — a closed `K`-Lipschitz
  profile composed with the sawtooth `sweepParam` is `K / period`-Lipschitz.
-/

/-- The explicit Lipschitz constant of the profile of the scheduled chamfer loop.  With
`Dz = max (lay * period) |ρ|` (the bound on the cut depth) and
`Bz = lay * Mr * period + |cQ| * Dz` (the bound on `β σ • (r (tbR σ) - r (taR σ))`), the three
branch constants are `2 * Mr * (period + 2 * Dz)` (arc), `(2 / lay) * (Mr * Dz + Bz)` (chamfers)
and `(Mr * period + 2 * Bz) / (1 / 2 - lay)` (chord). -/
def profLipConst (Mr lay ρ cQ : ℝ) : ℝ :=
  max (2 * Mr * (period + 2 * max (lay * period) |ρ|))
    (max ((2 / lay) * (Mr * max (lay * period) |ρ|
            + (lay * Mr * period + |cQ| * max (lay * period) |ρ|)))
      ((Mr * period + 2 * (lay * Mr * period + |cQ| * max (lay * period) |ρ|)) / (1 / 2 - lay)))

/-- **Gluing of two Lipschitz functions agreeing at a junction.** -/
lemma lipGlue {f g : ℝ → Space} {K c : ℝ}
    (hf : ∀ x y : ℝ, ‖f x - f y‖ ≤ K * |x - y|)
    (hg : ∀ x y : ℝ, ‖g x - g y‖ ≤ K * |x - y|)
    (hfg : f c = g c) :
    ∀ x y : ℝ, ‖(if x ≤ c then f x else g x) - (if y ≤ c then f y else g y)‖ ≤ K * |x - y| := by
  have key : ∀ x y : ℝ, x ≤ y →
      ‖(if x ≤ c then f x else g x) - (if y ≤ c then f y else g y)‖ ≤ K * (y - x) := by
    intro x y hxy
    by_cases hyc : y ≤ c
    · have hxc : x ≤ c := le_trans hxy hyc
      rw [if_pos hxc, if_pos hyc]
      have h := hf x y
      rwa [abs_of_nonpos (by linarith : x - y ≤ 0), neg_sub] at h
    · by_cases hxc : x ≤ c
      · rw [if_pos hxc, if_neg hyc]
        have he : f x - g y = (f x - f c) + (g c - g y) := by rw [hfg]; abel
        rw [he]
        refine (norm_add_le _ _).trans ?_
        have h1 : ‖f x - f c‖ ≤ K * (c - x) := by
          have h := hf x c
          rwa [abs_of_nonpos (by linarith : x - c ≤ 0), neg_sub] at h
        have h2 : ‖g c - g y‖ ≤ K * (y - c) := by
          have h := hg c y
          rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - c)] at h
          exact h
        calc ‖f x - f c‖ + ‖g c - g y‖ ≤ K * (c - x) + K * (y - c) := add_le_add h1 h2
          _ = K * (y - x) := by ring
      · rw [if_neg hxc, if_neg hyc]
        have h := hg x y
        rwa [abs_of_nonpos (by linarith : x - y ≤ 0), neg_sub] at h
  intro x y
  rcases le_total x y with hxy | hxy
  · rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - x)]
    exact key x y hxy
  · rw [norm_sub_rev, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - y)]
    exact key y x hxy


/-- **The profile of the scheduled chamfer loop is Lipschitz in the profile variable**, with the
explicit constant `profLipConst`, uniformly in the sweep parameter `σ`. -/
lemma chamferProf_lip {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {Mr lay ρ δs cQ : ℝ} (hMrlip : ∀ x y : ℝ, ‖r x - r y‖ ≤ Mr * |x - y|)
    (hMr : 0 ≤ Mr) (hlay : 0 < lay) (hlay1 : lay < 1 / 2) (hδs : 0 < δs) (σ : ℝ) :
    ∀ u v : ℝ,
      ‖chamferLoopProf r D lay (schedAlpha lay ρ δs D σ) (schedBeta r lay ρ δs cQ D σ) σ u
        - chamferLoopProf r D lay (schedAlpha lay ρ δs D σ) (schedBeta r lay ρ δs cQ D σ) σ v‖
      ≤ profLipConst Mr lay ρ cQ * |u - v| := by
  set α : ℝ := schedAlpha lay ρ δs D σ with hαdef
  set β : ℝ := schedBeta r lay ρ δs cQ D σ with hβdef
  set W : ℝ := sweepW' D σ with hWdef
  set dep : ℝ := schedDep lay ρ δs D σ with hdepdef
  set Dz : ℝ := max (lay * period) |ρ| with hDzdef
  set Bz : ℝ := lay * Mr * period + |cQ| * Dz with hBzdef
  have hWb : 0 ≤ W ∧ W ≤ period := sweepW'_bounds D σ
  have hW0 : 0 ≤ W := hWb.1
  have hWP : W ≤ period := hWb.2
  have hDz0 : 0 ≤ Dz := by
    rw [hDzdef]; exact le_trans (abs_nonneg ρ) (le_max_right _ _)
  have hdep0 : 0 ≤ dep := schedDep_nonneg D hlay σ
  have hdeple : dep ≤ Dz := schedDep_le D hlay σ
  have haW : α * W = dep := schedAlpha_mul_sweepW' D hlay hδs σ
  have hBs : ‖β • (r (tbR D σ) - r (taR D σ))‖ ≤ Bz :=
    schedBeta_smul_bound D hMr hMrlip hlay hδs σ
  have htb : tbR D σ = taR D σ + W := by rw [hWdef, sweepW']; ring
  have hKarc : 2 * Mr * (period + 2 * Dz) ≤ profLipConst Mr lay ρ cQ := by
    rw [profLipConst]; exact le_max_left _ _
  have hKcham : (2 / lay) * (Mr * Dz + Bz) ≤ profLipConst Mr lay ρ cQ := by
    rw [profLipConst]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hKchord : (Mr * period + 2 * Bz) / (1 / 2 - lay) ≤ profLipConst Mr lay ρ cQ := by
    rw [profLipConst]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hVb : ‖r (tbR D σ) - r (taR D σ)‖ ≤ Mr * period := by
    have h := hMrlip (tbR D σ) (taR D σ)
    have hW' : (0 : ℝ) ≤ tbR D σ - taR D σ := hW0
    rw [abs_of_nonneg hW'] at h
    exact h.trans (mul_le_mul_of_nonneg_left hWP hMr)
  -- the two point differences appearing in the chamfer/chord branches
  have hCA : ‖sweepChord' r D σ (1 - β) - sweepArc' r D σ (1 - α)‖ ≤ Mr * Dz + Bz := by
    have hC1 : sweepChord' r D σ (1 - β)
        = β • r (taR D σ) + (1 - β) • r (tbR D σ) := by
      rw [sweepChord', show (1 : ℝ) - (1 - β) = β by ring]
    have hA1 : sweepArc' r D σ (1 - α) = r (tbR D σ - dep) := by
      rw [sweepArc']
      congr 1
      have h1 : (1 - α) * W = W - dep := by rw [sub_mul, one_mul, haW]
      rw [htb, h1]; ring
    rw [hC1, hA1]
    have e : β • r (taR D σ) + (1 - β) • r (tbR D σ) - r (tbR D σ - dep)
        = (r (tbR D σ) - r (tbR D σ - dep)) + β • (r (taR D σ) - r (tbR D σ)) := by
      module
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖r (tbR D σ) - r (tbR D σ - dep)‖ ≤ Mr * Dz := by
      have h := hMrlip (tbR D σ) (tbR D σ - dep)
      rw [show tbR D σ - (tbR D σ - dep) = dep by ring, abs_of_nonneg hdep0] at h
      exact h.trans (mul_le_mul_of_nonneg_left hdeple hMr)
    have h2 : ‖β • (r (taR D σ) - r (tbR D σ))‖ ≤ Bz := by
      rw [show r (taR D σ) - r (tbR D σ) = -(r (tbR D σ) - r (taR D σ)) by abel,
        smul_neg, norm_neg]
      exact hBs
    linarith [h1, h2]
  have hAC : ‖sweepArc' r D σ α - sweepChord' r D σ β‖ ≤ Mr * Dz + Bz := by
    have hA2 : sweepArc' r D σ α = r (taR D σ + dep) := by
      rw [sweepArc']; congr 1; rw [haW]
    have hC2 : sweepChord' r D σ β = (1 - β) • r (taR D σ) + β • r (tbR D σ) := rfl
    rw [hA2, hC2]
    have e : r (taR D σ + dep) - ((1 - β) • r (taR D σ) + β • r (tbR D σ))
        = (r (taR D σ + dep) - r (taR D σ)) + β • (r (taR D σ) - r (tbR D σ)) := by
      module
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖r (taR D σ + dep) - r (taR D σ)‖ ≤ Mr * Dz := by
      have h := hMrlip (taR D σ + dep) (taR D σ)
      rw [show taR D σ + dep - taR D σ = dep by ring, abs_of_nonneg hdep0] at h
      exact h.trans (mul_le_mul_of_nonneg_left hdeple hMr)
    have h2 : ‖β • (r (taR D σ) - r (tbR D σ))‖ ≤ Bz := by
      rw [show r (taR D σ) - r (tbR D σ) = -(r (tbR D σ) - r (taR D σ)) by abel,
        smul_neg, norm_neg]
      exact hBs
    linarith [h1, h2]
  -- the four branches
  have hg1 : ∀ u v : ℝ,
      ‖sweepArc' r D σ (α + (1 - 2 * α) * (2 * u))
        - sweepArc' r D σ (α + (1 - 2 * α) * (2 * v))‖
      ≤ profLipConst Mr lay ρ cQ * |u - v| := by
    intro u v
    have harg : (taR D σ + (α + (1 - 2 * α) * (2 * u)) * W)
        - (taR D σ + (α + (1 - 2 * α) * (2 * v)) * W) = (W - 2 * dep) * (2 * (u - v)) := by
      have h1 : (α + (1 - 2 * α) * (2 * u)) * W = dep + (1 - 2 * α) * W * (2 * u) := by
        rw [add_mul, haW]; ring
      have h2 : (α + (1 - 2 * α) * (2 * v)) * W = dep + (1 - 2 * α) * W * (2 * v) := by
        rw [add_mul, haW]; ring
      have hc : (1 - 2 * α) * W = W - 2 * dep := by
        have h3 : (1 - 2 * α) * W = 1 * W - 2 * (α * W) := by ring
        rw [h3, haW]; ring
      rw [h1, h2, hc]; ring
    have hb := hMrlip (taR D σ + (α + (1 - 2 * α) * (2 * u)) * W)
      (taR D σ + (α + (1 - 2 * α) * (2 * v)) * W)
    rw [harg] at hb
    have hW2 : |W - 2 * dep| ≤ period + 2 * Dz := by
      refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
    have habs : |(W - 2 * dep) * (2 * (u - v))| ≤ (period + 2 * Dz) * (2 * |u - v|) := by
      rw [abs_mul, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
      exact mul_le_mul_of_nonneg_right hW2 (by positivity)
    have e1 : ‖sweepArc' r D σ (α + (1 - 2 * α) * (2 * u))
          - sweepArc' r D σ (α + (1 - 2 * α) * (2 * v))‖
        ≤ Mr * |(W - 2 * dep) * (2 * (u - v))| := hb
    have e2 : Mr * |(W - 2 * dep) * (2 * (u - v))|
        ≤ Mr * ((period + 2 * Dz) * (2 * |u - v|)) := mul_le_mul_of_nonneg_left habs hMr
    have e3 : Mr * ((period + 2 * Dz) * (2 * |u - v|)) = (2 * Mr * (period + 2 * Dz)) * |u - v| := by
      ring
    have e4 : (2 * Mr * (period + 2 * Dz)) * |u - v|
        ≤ profLipConst Mr lay ρ cQ * |u - v| := mul_le_mul_of_nonneg_right hKarc (abs_nonneg _)
    linarith [e1, e2, e3, e4]
  have hg2 : ∀ u v : ℝ,
      ‖((1 - (2 * u - 1) / lay) • sweepArc' r D σ (1 - α)
          + ((2 * u - 1) / lay) • sweepChord' r D σ (1 - β))
        - ((1 - (2 * v - 1) / lay) • sweepArc' r D σ (1 - α)
          + ((2 * v - 1) / lay) • sweepChord' r D σ (1 - β))‖
      ≤ profLipConst Mr lay ρ cQ * |u - v| := by
    intro u v
    have hdiff : ((1 - (2 * u - 1) / lay) • sweepArc' r D σ (1 - α)
          + ((2 * u - 1) / lay) • sweepChord' r D σ (1 - β))
        - ((1 - (2 * v - 1) / lay) • sweepArc' r D σ (1 - α)
          + ((2 * v - 1) / lay) • sweepChord' r D σ (1 - β))
        = ((2 * (u - v)) / lay) • (sweepChord' r D σ (1 - β) - sweepArc' r D σ (1 - α)) := by
      module
    rw [hdiff, norm_smul, Real.norm_eq_abs]
    have habs : |(2 * (u - v)) / lay| = (2 / lay) * |u - v| := by
      rw [abs_div, abs_mul, abs_of_pos hlay, show |(2 : ℝ)| = 2 by norm_num]
      ring
    rw [habs]
    have e1 : (2 / lay) * |u - v| * ‖sweepChord' r D σ (1 - β) - sweepArc' r D σ (1 - α)‖
        ≤ (2 / lay) * |u - v| * (Mr * Dz + Bz) :=
          mul_le_mul_of_nonneg_left hCA (by positivity)
    have e2 : (2 / lay) * |u - v| * (Mr * Dz + Bz)
        = ((2 / lay) * (Mr * Dz + Bz)) * |u - v| := by ring
    have e3 : ((2 / lay) * (Mr * Dz + Bz)) * |u - v|
        ≤ profLipConst Mr lay ρ cQ * |u - v| := mul_le_mul_of_nonneg_right hKcham (abs_nonneg _)
    linarith [e1, e2, e3]
  have hg3 : ∀ u v : ℝ,
      ‖sweepChord' r D σ ((1 - β) - ((u - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * β))
        - sweepChord' r D σ ((1 - β) - ((v - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * β))‖
      ≤ profLipConst Mr lay ρ cQ * |u - v| := by
    intro u v
    have hdenpos : (0 : ℝ) < 1 / 2 - lay := by linarith
    have hgen : ∀ x y : ℝ, sweepChord' r D σ x - sweepChord' r D σ y
        = (x - y) • (r (tbR D σ) - r (taR D σ)) := by
      intro x y
      rw [sweepChord', sweepChord']
      module
    have hxi : ((1 - β) - ((u - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * β))
        - ((1 - β) - ((v - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * β))
        = -(((u - v) / (1 / 2 - lay)) * (1 - 2 * β)) := by ring
    rw [hgen, hxi, norm_smul, Real.norm_eq_abs]
    have habs : |(-(((u - v) / (1 / 2 - lay)) * (1 - 2 * β)))|
        = (|u - v| / (1 / 2 - lay)) * |1 - 2 * β| := by
      rw [abs_neg, abs_mul, abs_div, abs_of_pos hdenpos]
    rw [habs]
    have h12b : |1 - 2 * β| * ‖r (tbR D σ) - r (taR D σ)‖ ≤ Mr * period + 2 * Bz := by
      have e : (1 - 2 * β) • (r (tbR D σ) - r (taR D σ))
          = (r (tbR D σ) - r (taR D σ)) - (2 : ℝ) • (β • (r (tbR D σ) - r (taR D σ))) := by
        module
      have hsum : ‖(1 - 2 * β) • (r (tbR D σ) - r (taR D σ))‖ ≤ Mr * period + 2 * Bz := by
        rw [e]
        refine (norm_sub_le _ _).trans ?_
        have h2 : ‖(2 : ℝ) • (β • (r (tbR D σ) - r (taR D σ)))‖ ≤ 2 * Bz := by
          rw [norm_smul, Real.norm_eq_abs, show |(2 : ℝ)| = 2 by norm_num]
          linarith [hBs]
        linarith
      simpa only [norm_smul, Real.norm_eq_abs] using hsum
    have e0 : |u - v| / (1 / 2 - lay) * |1 - 2 * β| * ‖r (tbR D σ) - r (taR D σ)‖
        = |u - v| / (1 / 2 - lay) * (|1 - 2 * β| * ‖r (tbR D σ) - r (taR D σ)‖) := by ring
    have e1 : |u - v| / (1 / 2 - lay) * (|1 - 2 * β| * ‖r (tbR D σ) - r (taR D σ)‖)
        ≤ |u - v| / (1 / 2 - lay) * (Mr * period + 2 * Bz) :=
          mul_le_mul_of_nonneg_left h12b (by positivity)
    have e2 : |u - v| / (1 / 2 - lay) * (Mr * period + 2 * Bz)
        = ((Mr * period + 2 * Bz) / (1 / 2 - lay)) * |u - v| := by ring
    have e3 : ((Mr * period + 2 * Bz) / (1 / 2 - lay)) * |u - v|
        ≤ profLipConst Mr lay ρ cQ * |u - v| := mul_le_mul_of_nonneg_right hKchord (abs_nonneg _)
    linarith [e0, e1, e2, e3]
  have hg4 : ∀ u v : ℝ,
      ‖((1 - (u - (1 - lay / 2)) / (lay / 2)) • sweepChord' r D σ β
          + ((u - (1 - lay / 2)) / (lay / 2)) • sweepArc' r D σ α)
        - ((1 - (v - (1 - lay / 2)) / (lay / 2)) • sweepChord' r D σ β
          + ((v - (1 - lay / 2)) / (lay / 2)) • sweepArc' r D σ α)‖
      ≤ profLipConst Mr lay ρ cQ * |u - v| := by
    intro u v
    have hdiff : ((1 - (u - (1 - lay / 2)) / (lay / 2)) • sweepChord' r D σ β
          + ((u - (1 - lay / 2)) / (lay / 2)) • sweepArc' r D σ α)
        - ((1 - (v - (1 - lay / 2)) / (lay / 2)) • sweepChord' r D σ β
          + ((v - (1 - lay / 2)) / (lay / 2)) • sweepArc' r D σ α)
        = (((u - v) / (lay / 2))) • (sweepArc' r D σ α - sweepChord' r D σ β) := by
      module
    rw [hdiff, norm_smul, Real.norm_eq_abs]
    have habs : |(u - v) / (lay / 2)| = (2 / lay) * |u - v| := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < lay / 2), div_mul_eq_mul_div,
        div_eq_div_iff (by positivity : (lay / 2 : ℝ) ≠ 0) (by positivity : lay ≠ 0)]
      ring
    rw [habs]
    have e1 : (2 / lay) * |u - v| * ‖sweepArc' r D σ α - sweepChord' r D σ β‖
        ≤ (2 / lay) * |u - v| * (Mr * Dz + Bz) :=
          mul_le_mul_of_nonneg_left hAC (by positivity)
    have e2 : (2 / lay) * |u - v| * (Mr * Dz + Bz)
        = ((2 / lay) * (Mr * Dz + Bz)) * |u - v| := by ring
    have e3 : ((2 / lay) * (Mr * Dz + Bz)) * |u - v|
        ≤ profLipConst Mr lay ρ cQ * |u - v| := mul_le_mul_of_nonneg_right hKcham (abs_nonneg _)
    linarith [e1, e2, e3]
  -- the gluing
  let g1 : ℝ → Space := fun u => sweepArc' r D σ (α + (1 - 2 * α) * (2 * u))
  let g2 : ℝ → Space := fun u => (1 - (2 * u - 1) / lay) • sweepArc' r D σ (1 - α)
      + ((2 * u - 1) / lay) • sweepChord' r D σ (1 - β)
  let g3 : ℝ → Space := fun u =>
      sweepChord' r D σ ((1 - β) - ((u - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * β))
  let g4 : ℝ → Space := fun u => (1 - (u - (1 - lay / 2)) / (lay / 2)) • sweepChord' r D σ β
      + ((u - (1 - lay / 2)) / (lay / 2)) • sweepArc' r D σ α
  let G3 : ℝ → Space := fun u => if u ≤ 1 - lay / 2 then g3 u else g4 u
  let G2 : ℝ → Space := fun u => if u ≤ 1 / 2 + lay / 2 then g2 u else G3 u
  let G1 : ℝ → Space := fun u => if u ≤ 1 / 2 then g1 u else G2 u
  have h34 : g3 (1 - lay / 2) = g4 (1 - lay / 2) := by
    have hc1 : (1 - lay / 2 - (1 / 2 + lay / 2)) / (1 / 2 - lay) = 1 := by
      rw [show (1 : ℝ) - lay / 2 - (1 / 2 + lay / 2) = 1 / 2 - lay by ring]
      exact div_self (by linarith : (1 : ℝ) / 2 - lay ≠ 0)
    have hc2 : (1 - lay / 2 - (1 - lay / 2)) / (lay / 2) = 0 := by
      rw [sub_self, zero_div]
    have hb2 : (1 - β) - 1 * (1 - 2 * β) = β := by ring
    dsimp only [g3, g4]
    rw [hc1, hc2, hb2]
    simp
  have h23 : g2 (1 / 2 + lay / 2) = G3 (1 / 2 + lay / 2) := by
    have hG : G3 (1 / 2 + lay / 2) = g3 (1 / 2 + lay / 2) := by
      dsimp only [G3]
      exact if_pos (by linarith : (1 : ℝ) / 2 + lay / 2 ≤ 1 - lay / 2)
    have hc1 : (2 * (1 / 2 + lay / 2) - 1) / lay = 1 := by
      rw [show 2 * (1 / 2 + lay / 2) - 1 = lay by ring]
      exact div_self (ne_of_gt hlay)
    have hc2 : ((1 / 2 + lay / 2) - (1 / 2 + lay / 2)) / (1 / 2 - lay) = 0 := by
      rw [sub_self, zero_div]
    rw [hG]
    dsimp only [g2, g3]
    rw [hc1, hc2]
    simp
  have h12 : g1 (1 / 2) = G2 (1 / 2) := by
    have hG : G2 (1 / 2) = g2 (1 / 2) := by
      dsimp only [G2]
      exact if_pos (by linarith : (1 : ℝ) / 2 ≤ 1 / 2 + lay / 2)
    have hcoef : (2 * ((1 : ℝ) / 2) - 1) / lay = 0 := by
      rw [show 2 * ((1 : ℝ) / 2) - 1 = 0 by norm_num, zero_div]
    have harg : α + (1 - 2 * α) * (2 * ((1 : ℝ) / 2)) = 1 - α := by ring
    rw [hG]
    dsimp only [g1, g2]
    rw [hcoef, harg]
    simp
  have hG3 : ∀ x y : ℝ, ‖G3 x - G3 y‖ ≤ profLipConst Mr lay ρ cQ * |x - y| := by
    intro x y
    exact lipGlue hg3 hg4 h34 x y
  have hG2 : ∀ x y : ℝ, ‖G2 x - G2 y‖ ≤ profLipConst Mr lay ρ cQ * |x - y| := by
    intro x y
    exact lipGlue hg2 hG3 h23 x y
  show ∀ u v : ℝ, ‖G1 u - G1 v‖ ≤ profLipConst Mr lay ρ cQ * |u - v|
  exact lipGlue hg1 hG2 h12

/-- The explicit profile constant is non-negative. -/
lemma profLipConst_nonneg {Mr lay ρ cQ : ℝ} (hMr : 0 ≤ Mr) (hlay : 0 < lay)
    (hlay1 : lay < 1 / 2) : 0 ≤ profLipConst Mr lay ρ cQ := by
  have hDz : 0 ≤ max (lay * period) |ρ| := le_trans (abs_nonneg ρ) (le_max_right _ _)
  have h1 : 0 ≤ 2 * Mr * (period + 2 * max (lay * period) |ρ|) :=
    mul_nonneg (mul_nonneg (by norm_num) hMr)
      (add_nonneg period_pos.le (mul_nonneg (by norm_num) hDz))
  exact le_trans h1 (le_max_left _ _)

theorem chamferLoopGenLipschitzT {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {lay ρ₀ δs cQ : ℝ} (hlay : 0 < lay) (hlay1 : lay < 1 / 2) (hδs : 0 < δs) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ t₁ t₂ : ℝ,
      ‖Work.Drive.chamferLoopGen r D lay (Work.Drive.schedAlpha lay ρ₀ δs D)
          (Work.Drive.schedBeta r lay ρ₀ δs cQ D) σ t₁
        - Work.Drive.chamferLoopGen r D lay (Work.Drive.schedAlpha lay ρ₀ δs D)
          (Work.Drive.schedBeta r lay ρ₀ δs cQ D) σ t₂‖ ≤ M * |t₂ - t₁| := by
  obtain ⟨Mr, hMrpos, hMrlip⟩ := exists_knot_lipschitz hr
  have hK0 : 0 ≤ profLipConst Mr lay ρ₀ cQ := profLipConst_nonneg hMrpos.le hlay hlay1
  refine ⟨profLipConst Mr lay ρ₀ cQ / period, div_nonneg hK0 period_pos.le, ?_⟩
  intro σ t₁ t₂
  have h := sweepParam_lipschitz_of_closed
    (Φ := fun u : ℝ => chamferLoopProf r D lay (schedAlpha lay ρ₀ δs D σ)
      (schedBeta r lay ρ₀ δs cQ D σ) σ u) hK0
    (chamferProf_lip D hMrlip hMrpos.le hlay hlay1 hδs σ)
    (chamferProf_zero_eq_one D hlay hlay1 σ) t₁ t₂
  rw [chamferLoopGen_eq_prof' r D lay (schedAlpha lay ρ₀ δs D) (schedBeta r lay ρ₀ δs cQ D) σ t₁,
    chamferLoopGen_eq_prof' r D lay (schedAlpha lay ρ₀ δs D) (schedBeta r lay ρ₀ δs cQ D) σ t₂,
    abs_sub_comm]
  exact h

end Work.Drive
