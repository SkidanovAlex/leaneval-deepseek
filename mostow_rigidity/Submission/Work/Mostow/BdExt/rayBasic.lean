import Mathlib
import Submission.Work.Mostow.BdExt.bdMap
import Submission.Work.Mostow.BdExt.bdMapClose
import Submission.Work.Mostow.BdExt.rayDist

/-!
# Elementary facts about the ray `ray ξ ·`, the level function and `dirv`

Small shared lemmas for the boundary-extension development:

* `dirv_ray` : for `ξ ∈ Sph n` and `t > 0` the direction of `ray ξ t` is `ξ`;
* `tendsto_lvl_ray` : along a ray the level escapes to `+∞`;
* `tendsto_lvl_of_close_ray` : a sequence at bounded distance from a ray also escapes to `+∞`
  in level;
* `tendsto_dirv_ray` : the directions along a ray converge to `ξ` (the sequence form of `dirv_ray`).

These are the "sequence bookkeeping" facts used when applying `closeSeq`.
-/

namespace Work.Mostow.BdExt

open Submission.Mostow Filter

noncomputable section

variable {n : ℕ}

/-- For `ξ ∈ Sph n` and `t > 0`, the direction of the ray point `ray ξ t` is `ξ`. -/
lemma dirv_ray (ξ : E n) (hξ : ξ ∈ Sph n) {t : ℝ} (ht : 0 < t) : dirv (ray ξ t) = ξ := by
  have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
  have hs : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  have hnorm : ‖Real.sinh t • ξ‖ = Real.sinh t := by
    rw [norm_smul, hξn, mul_one, Real.norm_of_nonneg (le_of_lt hs)]
  rw [dirv, ray, hnorm, smul_smul, inv_mul_cancel₀ (ne_of_gt hs), one_smul]

/-- Along the ray to `ξ ∈ Sph n` the level escapes to `+∞`. -/
lemma tendsto_lvl_ray (ξ : E n) (hξ : ξ ∈ Sph n) :
    Tendsto (fun k : ℕ => lvl (ray ξ (k : ℝ))) atTop atTop := by
  have h : (fun k : ℕ => lvl (ray ξ (k : ℝ))) = fun k : ℕ => (k : ℝ) := by
    funext k
    rw [lvl, hdist_zero_ray ξ hξ (k : ℝ) (Nat.cast_nonneg k)]
  rw [h]
  exact tendsto_natCast_atTop_atTop

/-- A sequence at bounded distance from the ray to `ξ ∈ Sph n` escapes to `+∞` in level. -/
lemma tendsto_lvl_of_close_ray (hI : HypIsometryProp n) (ξ : E n) (hξ : ξ ∈ Sph n)
    (u : ℕ → E n) (D : ℝ) (h : ∀ k, hdist (u k) (ray ξ (k : ℝ)) ≤ D) :
    Tendsto (fun k : ℕ => lvl (u k)) atTop atTop := by
  have hf : Tendsto (fun k : ℕ => (k : ℝ) - D) atTop atTop := by
    refine (tendsto_atTop_add_const_right atTop (-D) tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards with k
    ring
  refine tendsto_atTop_mono (f := fun k : ℕ => (k : ℝ) - D) ?_ hf
  intro k
  have h0 : hdist 0 (ray ξ (k : ℝ)) = (k : ℝ) :=
    hdist_zero_ray ξ hξ (k : ℝ) (Nat.cast_nonneg k)
  have h1 : (k : ℝ) ≤ hdist 0 (u k) + hdist (u k) (ray ξ (k : ℝ)) :=
    calc (k : ℝ) = hdist 0 (ray ξ (k : ℝ)) := h0.symm
      _ ≤ hdist 0 (u k) + hdist (u k) (ray ξ (k : ℝ)) :=
          hI.2.2.2.1 0 (u k) (ray ξ (k : ℝ))
  rw [lvl]
  linarith [h k]

/-- The directions along the ray to `ξ ∈ Sph n` converge to `ξ`: the sequence form of `dirv_ray`. -/
lemma tendsto_dirv_ray (hI : HypIsometryProp n) (ξ : E n) (hξ : ξ ∈ Sph n) :
    Tendsto (fun k : ℕ => dirv (ray ξ (k : ℝ))) atTop (nhds ξ) := by
  have hclose : ∀ k : ℕ, hdist (ray ξ (((k + 1 : ℕ) : ℝ))) (ray ξ (k : ℝ)) ≤ 1 := by
    intro k
    rw [hdist_ray_ray ξ hξ]
    have h1 : (((k + 1 : ℕ) : ℝ)) - (k : ℝ) = 1 := by push_cast; ring
    rw [h1, abs_one]
  have hu : Tendsto (fun k : ℕ => lvl (ray ξ (((k + 1 : ℕ) : ℝ)))) atTop atTop := by
    have h : (fun k : ℕ => lvl (ray ξ (((k + 1 : ℕ) : ℝ)))) =
        fun k : ℕ => (((k + 1 : ℕ)) : ℝ) := by
      funext k
      rw [lvl, hdist_zero_ray ξ hξ _ (Nat.cast_nonneg _)]
    rw [h]
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hdir : Tendsto (fun k : ℕ => dirv (ray ξ (((k + 1 : ℕ) : ℝ)))) atTop (nhds ξ) := by
    have h : (fun k : ℕ => dirv (ray ξ (((k + 1 : ℕ) : ℝ)))) = fun _ : ℕ => ξ := by
      funext k
      exact dirv_ray ξ hξ (by exact_mod_cast Nat.succ_pos k)
    rw [h]
    exact tendsto_const_nhds
  exact closeSeq n hI (fun k : ℕ => ray ξ (((k + 1 : ℕ) : ℝ))) (fun k : ℕ => ray ξ (k : ℝ))
    1 zero_le_one hclose hu (tendsto_lvl_ray ξ hξ) ξ hdir

end

end Work.Mostow.BdExt
