import Mathlib
import Submission.Work.Mostow.parabGeoPt
import Submission.Work.Mostow.parabLevelUniq
import Submission.Work.Mostow.periodicOrbitFix
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.geomFiniteStabHorosphere
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.BaryBase

/-!
# `parabolicCommuteFix`

Two parabolic isometries of `ℍⁿ` with commuting non-trivial powers fix the same boundary point.
The proof rests on the two classification facts for a parabolic element `G`:

* `parabolic_pow` : every positive power of a parabolic element is parabolic;
* `parabolic_fixed_unique` : a parabolic element fixes at most one point of the boundary sphere.

This file develops the elementary parts (iteration of the action, Busemann invariance on
horospheres of a parabolic element, the displacement estimate for powers) and assembles the final
statement from the three delegated technical lemmas `parabGeoPt`, `parabLevelUniq`,
`periodicOrbitFix`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

variable {n : ℕ}

/-! ## Iterates of the action -/

/-- The `m`-th power of `g` acts as the `m`-fold iterate of the action of `g`. -/
theorem pcf_pow_smul_iterate (hA : POActionProp n) (g : PO n 1) (m : ℕ) :
    ∀ u : E n, (g ^ m) • u = (fun x : E n => g • x)^[m] u := by
  induction m with
  | zero => intro u; rw [pow_zero, hA.2.2.2.1]; rfl
  | succ m ih =>
      intro u
      rw [pow_succ, hA.2.2.2.2.1 (g ^ m) g u, ih (g • u), Function.iterate_succ_apply]

/-- Iterates of a distance-preserving map preserve distances. -/
theorem pcf_hdist_iterate_eq (f : E n → E n)
    (hf : ∀ u v : E n, hdist (f u) (f v) = hdist u v) (j : ℕ) (a b : E n) :
    hdist (f^[j] a) (f^[j] b) = hdist a b := by
  induction j generalizing a b with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih (f a) (f b), hf a b]

/-- Consecutive points of an orbit under a distance-preserving map are at constant distance. -/
theorem pcf_hdist_iterate_step (f : E n → E n)
    (hf : ∀ u v : E n, hdist (f u) (f v) = hdist u v) (u : E n) (j : ℕ) :
    hdist (f^[j] u) (f^[j] (f u)) = hdist u (f u) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      calc hdist (f^[j+1] u) (f^[j+1] (f u))
          = hdist (f^[j] (f u)) (f^[j] (f (f u))) := by
              rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
        _ = hdist (f u) (f (f u)) := pcf_hdist_iterate_eq f hf j (f u) (f (f u))
        _ = hdist u (f u) := hf u (f u)

/-- Triangle-inequality bound for the displacement of a power of a distance-preserving map. -/
theorem pcf_hdist_iterate_le (hI : HypIsometryProp n) (f : E n → E n)
    (hf : ∀ u v : E n, hdist (f u) (f v) = hdist u v) (u : E n) (m : ℕ) :
    hdist u (f^[m] u) ≤ (m : ℝ) * hdist u (f u) := by
  induction m with
  | zero => simp [hdist_self]
  | succ m ih =>
      calc hdist u (f^[m+1] u)
          = hdist u (f^[m] (f u)) := by rw [Function.iterate_succ_apply]
        _ ≤ hdist u (f^[m] u) + hdist (f^[m] u) (f^[m] (f u)) :=
              hI.2.2.2.1 u (f^[m] u) (f^[m] (f u))
        _ = hdist u (f^[m] u) + hdist u (f u) := by
              rw [pcf_hdist_iterate_step f hf u m]
        _ ≤ (m : ℝ) * hdist u (f u) + hdist u (f u) := by linarith
        _ = ((m + 1 : ℕ) : ℝ) * hdist u (f u) := by push_cast; ring

/-- The displacement of the `m`-th power is at most `m` times the displacement of `g`. -/
theorem pcf_hdist_pow_le (hA : POActionProp n) (hI : HypIsometryProp n) (g : PO n 1) (u : E n)
    (m : ℕ) : hdist u ((g ^ m) • u) ≤ (m : ℝ) * hdist u (g • u) := by
  rw [pcf_pow_smul_iterate hA g m u]
  exact pcf_hdist_iterate_le hI (fun x : E n => g • x) (fun a b => hI.2.2.2.2.2.2.1 g a b) u m

/-! ## Iterates of the boundary action -/

/-- A boundary point fixed by `g` is fixed by every power of `g`. -/
theorem pcf_bd_pow_fixed (hA : POActionProp n) (g : PO n 1) (ξ : E n) (hξ : ξ ∈ Sph n)
    (hgξ : bd g ξ = ξ) (m : ℕ) : bd (g ^ m) ξ = ξ := by
  induction m with
  | zero => rw [pow_zero]; exact hA.2.2.2.2.2.2.2.2.1 ξ hξ
  | succ m ih =>
      rw [pow_succ, hA.2.2.2.2.2.2.2.2.2.1 (g ^ m) g ξ hξ, hgξ]; exact ih

/-! ## Busemann invariance at a parabolic fixed point -/

/-- A parabolic isometry with boundary fixed point `ξ` preserves every horosphere at `ξ`: the
Busemann cocycle of `g` at `ξ` vanishes. -/
theorem pcf_busemann_smul_of_parabolic (hA : POActionProp n) (hI : HypIsometryProp n) (g : PO n 1)
    (hg : IsParabolic g) (ξ : E n) (hξ : ξ ∈ Sph n) (hgξ : bd g ξ = ξ) :
    ∀ u : E n, busemann ξ (g • u) = busemann ξ u := by
  intro u
  have hc : busemann ξ (g • (0 : E n)) = 0 := by
    simpa [bCocy, hgξ] using bCocy_parabolic hA hI g hg ξ hξ hgξ
  have hbus := hI.2.2.2.2.2.2.2.2.2.2.2.2 g ξ u hξ
  rw [hgξ, hc, add_zero] at hbus
  exact hbus

/-! ## Powers of parabolic isometries -/

/-- The infimal displacement of a positive power of a parabolic element is still `0`. -/
theorem pcf_parabolic_pow_infdisp (hA : POActionProp n) (hI : HypIsometryProp n) (g : PO n 1)
    (hg : IsParabolic g) (m : ℕ) (hm : 0 < m) :
    ∀ ε > 0, ∃ u : E n, hdist u ((g ^ m) • u) < ε := by
  intro ε hε
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  obtain ⟨u, hu⟩ := hg.2 (ε / m) (by positivity)
  refine ⟨u, ?_⟩
  have h1 := pcf_hdist_pow_le hA hI g u m
  have h2 : (m : ℝ) * hdist u (g • u) < ε := by
    have hmul : (m : ℝ) * (ε / m) = ε := by field_simp
    calc (m : ℝ) * hdist u (g • u) < (m : ℝ) * (ε / m) :=
          mul_lt_mul_of_pos_left hu hmR
      _ = ε := hmul
  linarith

/-- A positive power of a parabolic isometry is parabolic. -/
theorem pcf_parabolic_pow (hA : POActionProp n) (hI : HypIsometryProp n) (g : PO n 1)
    (hg : IsParabolic g) (m : ℕ) (hm : 0 < m) : IsParabolic (g ^ m) := by
  constructor
  · intro u hu
    obtain ⟨b, hb⟩ := periodicOrbitFix n hA g m hm u hu
    exact hg.1 b hb
  · exact pcf_parabolic_pow_infdisp hA hI g hg m hm


/-! ## A parabolic isometry fixes at most one boundary point -/

/-- **Uniqueness of the boundary fixed point of a parabolic isometry.**  A parabolic isometry
preserves the horospheres at each of its boundary fixed points, and the common level set of the
two Busemann functions of two distinct boundary points at complementary levels is a single point;
hence the explicit geodesic point between the two fixed points would be fixed by `g`. -/
theorem pcf_parabolic_fixed_unique (hA : POActionProp n) (hI : HypIsometryProp n) (g : PO n 1)
    (hg : IsParabolic g) (ξ ψ : E n) (hξ : ξ ∈ Sph n) (hψ : ψ ∈ Sph n)
    (hgξ : bd g ξ = ξ) (hgψ : bd g ψ = ψ) : ξ = ψ := by
  by_contra hne
  have hbi : ∀ u : E n, busemann ξ (g • u) = busemann ξ u :=
    pcf_busemann_smul_of_parabolic hA hI g hg ξ hξ hgξ
  have hbj : ∀ u : E n, busemann ψ (g • u) = busemann ψ u :=
    pcf_busemann_smul_of_parabolic hA hI g hg ψ hψ hgψ
  have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
  have hψn : ‖ψ‖ = 1 := (mem_Sph_iff ψ).mp hψ
  have hlt : inner ℝ ξ ψ < 1 := by
    rcases lt_or_eq_of_le (by simpa [hξn, hψn] using real_inner_le_norm ξ ψ) with h | h
    · exact h
    · exfalso
      have h2 : ‖ξ - ψ‖ ^ 2 = 0 := by
        rw [norm_sub_sq_real, h, hξn, hψn]; ring
      have h3 : ‖ξ - ψ‖ = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h2
      exact hne (sub_eq_zero.mp (norm_eq_zero.mp h3))
  have hqpos : 0 < Real.sqrt ((1 - inner ℝ ξ ψ) / 2) := Real.sqrt_pos.2 (by linarith)
  set q : ℝ := Real.sqrt ((1 - inner ℝ ξ ψ) / 2) with hq
  have hu : (2 * q)⁻¹ • (Real.exp 0 • ξ + Real.exp (-0) • ψ) = (2 * q)⁻¹ • (ξ + ψ) := by
    simp [Real.exp_zero]
  obtain ⟨-, hb1, hb2⟩ := parabGeoPt n ξ ψ hξ hψ hne 0
  rw [← hq, hu] at hb1 hb2
  have hb1' : busemann ξ ((2 * q)⁻¹ • (ξ + ψ)) = Real.log q := by rw [hb1]; ring
  have hb2' : busemann ψ ((2 * q)⁻¹ • (ξ + ψ)) = Real.log q := by rw [hb2]; ring
  have hx1 : busemann ξ (g • ((2 * q)⁻¹ • (ξ + ψ))) = Real.log (Real.sqrt ((1 - inner ℝ ξ ψ) / 2)) - 0 := by
    rw [hbi, hb1', hq]; ring
  have hx2 : busemann ψ (g • ((2 * q)⁻¹ • (ξ + ψ))) = Real.log (Real.sqrt ((1 - inner ℝ ξ ψ) / 2)) + 0 := by
    rw [hbj, hb2', hq]; ring
  have huniq := parabLevelUniq n ξ ψ (g • ((2 * q)⁻¹ • (ξ + ψ))) hξ hψ hne 0 hx1 hx2
  have hfix : g • ((2 * q)⁻¹ • (ξ + ψ)) = (2 * q)⁻¹ • (ξ + ψ) := by
    rw [huniq, ← hq, hu]
  exact hg.1 _ hfix

/-- Two parabolic isometries of `ℍⁿ` with commuting non-trivial powers fix the same boundary
point. -/
theorem parabolicCommuteFix (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (g h : LeanEval.Geometry.MostowRigidity.PO n 1)
    (hg : Submission.Mostow.IsParabolic g) (hh : Submission.Mostow.IsParabolic h)
    (ξ η : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n) (hη : η ∈ Submission.Mostow.Sph n)
    (hgξ : Submission.Mostow.bd g ξ = ξ) (hhη : Submission.Mostow.bd h η = η)
    (m k : ℕ) (hm : 0 < m) (hk : 0 < k) (hcomm : g ^ m * h ^ k = h ^ k * g ^ m) : ξ = η := by
  have hgm : IsParabolic (g ^ m) := pcf_parabolic_pow hA hI g hg m hm
  have hhk : IsParabolic (h ^ k) := pcf_parabolic_pow hA hI h hh k hk
  have hbdgm : bd (g ^ m) ξ = ξ := pcf_bd_pow_fixed hA g ξ hξ hgξ m
  have hbdhk : bd (h ^ k) η = η := pcf_bd_pow_fixed hA h η hη hhη k
  -- the conjugate boundary point `bd (h^k) ξ` is fixed by `bd (g^m)`
  have hψ : bd (g ^ m) (bd (h ^ k) ξ) = bd (h ^ k) ξ := by
    have h1 : bd (g ^ m * h ^ k) ξ = bd (h ^ k * g ^ m) ξ := by rw [hcomm]
    rw [hA.2.2.2.2.2.2.2.2.2.1 (g ^ m) (h ^ k) ξ hξ,
      hA.2.2.2.2.2.2.2.2.2.1 (h ^ k) (g ^ m) ξ hξ, hbdgm] at h1
    exact h1
  have hψSph : bd (h ^ k) ξ ∈ Sph n := hA.2.2.2.2.2.2.2.1 (h ^ k) ξ hξ
  have h1 : ξ = bd (h ^ k) ξ :=
    pcf_parabolic_fixed_unique hA hI (g ^ m) hgm ξ (bd (h ^ k) ξ) hξ hψSph hbdgm hψ
  exact pcf_parabolic_fixed_unique hA hI (h ^ k) hhk ξ η hξ hη h1.symm hbdhk

end

end Work.Mostow
