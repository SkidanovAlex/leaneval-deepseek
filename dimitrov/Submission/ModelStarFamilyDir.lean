import Mathlib
import Submission.ModelStarFamily
import Submission.ModelStarDirection
import Submission.ModelStarBoundary4

/-!
# ModelStarFamilyDir -- the arc-direction dictionary for the general-s family

For `s ≥ 1`, a weight vector `r` (`0 < r k`, `Σ r k = 1`) and a gap vector `g`
(`0 < g k`, `Σ g k = 1`) of the general-s model-star family
(`Submission.ModelStarFamily`), this module proves

  * `arcLo g` is strictly increasing on `[0, 2π)`,
  * the sweep factor does not vanish on an open arc (`rhoG_ne_zero_of_Ioo`),
  * **`arcGood_direction`**: the `ArcGood` direction of arc `j` (the unit complex
    `u` with `modelF z₀ r (eAngle t) = ρ(t)·u` on the arc) is
        `eAngle (Σ_k r k·φ k + π·(2·Σ_{k≤j} r k − 1))`,
    i.e. `eAngle (A + 2π R j)` with `A := Σ_k r k φ k − π` and `R j := Σ_{k≤j} r k`.

Consequently the model star's spike directions are `A + 2π R j`, so consecutive
directions differ by `2π r j`: comparing with any prescribed direction pattern
`θ` having the same gaps, the two patterns differ by ONE rotation
(the rotation invariance of the Fekete root limsup absorbs it,
`Submission.Step3Decomp.rootLimsup_rotation`).
-/

noncomputable section

open scoped Real BigOperators Topology
open Set Filter

namespace Submission.ModelStarFamilyDir

open Submission.ModelStarFamily
open Submission.ModelStarBoundary2 (eAngle dirSign)
open Submission.ModelStarBoundary3 (rho)

variable {s : ℕ}

/-! ## The junction angles are strictly increasing on `[0, 2π)` -/

lemma arcLo_zero (g : Fin s → ℝ) (hs : 0 < s) : arcLo g ⟨0, hs⟩ = 0 := junc_zero g hs

lemma arcLo_mono {g : Fin s → ℝ} (hg : ∀ k, 0 ≤ g k) : Monotone (arcLo g) :=
  junc_mono hg

lemma arcLo_lt_two_pi {g : Fin s → ℝ} (hg : ∀ k, 0 < g k) (hsum : (∑ k, g k) = 1)
    (j : Fin s) : arcLo g j < 2 * Real.pi := by
  have hS : (∑ k : Fin s, (if k.val < j.val then g k else 0 : ℝ)) ≤ 1 - g j := by
    rw [← Finset.sum_filter]
    have hsplit : (∑ k ∈ Finset.univ.filter (fun k : Fin s => k.val < j.val), g k)
        + (∑ k ∈ Finset.univ.filter (fun k : Fin s => ¬ k.val < j.val), g k) = 1 := by
      rw [Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin s => k.val < j.val) g,
        hsum]
    have hge : g j ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin s => ¬ k.val < j.val), g k :=
      Finset.single_le_sum (fun k _ => (hg k).le) (by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact lt_irrefl _)
    linarith
  unfold arcLo junc
  nlinarith [Real.pi_pos, hg j]

lemma arcLo_strict {g : Fin s → ℝ} (hg : ∀ k, 0 < g k) : StrictMono (arcLo g) := by
  intro i j hij
  have hij' : i.val < j.val := hij
  have hdiff : 0 < (∑ k : Fin s, (if k.val < j.val then g k else 0 : ℝ))
      - (∑ k : Fin s, (if k.val < i.val then g k else 0 : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_pos' (fun k _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
    · by_cases h1 : k.val < j.val
      · have e1 : (if k.val < j.val then g k else 0 : ℝ) = g k := if_pos h1
        rw [e1]
        by_cases h2 : k.val < i.val
        · have e2 : (if k.val < i.val then g k else 0 : ℝ) = g k := if_pos h2
          rw [e2]; linarith [hg k]
        · have e2 : (if k.val < i.val then g k else 0 : ℝ) = 0 := if_neg h2
          rw [e2]; linarith [hg k]
      · have e1 : (if k.val < j.val then g k else 0 : ℝ) = 0 := if_neg h1
        rw [e1]
        by_cases h2 : k.val < i.val
        · exact absurd (lt_trans h2 hij') h1
        · have e2 : (if k.val < i.val then g k else 0 : ℝ) = 0 := if_neg h2
          rw [e2]; norm_num
    · rw [if_pos hij', if_neg (lt_irrefl i.val)]
      simpa using hg i
  unfold arcLo junc
  nlinarith [Real.pi_pos]

lemma arcLo_injective {g : Fin s → ℝ} (hg : ∀ k, 0 < g k) :
    Function.Injective (arcLo g) :=
  (arcLo_strict hg).injective

lemma arcHi_le_two_pi {g : Fin s → ℝ} (hg : ∀ k, 0 ≤ g k) (hsum : (∑ k, g k) = 1)
    (j : Fin s) : arcHi g j ≤ 2 * Real.pi := by
  have h := cum_le_one hg hsum j
  unfold arcHi
  nlinarith [Real.pi_pos]

/-! ## Nonvanishing of the sweep factor on an open arc -/

lemma rhoG_ne_zero_of_Ioo {r g : Fin s → ℝ} (hr : ∀ k, 0 < r k) (hg : ∀ k, 0 < g k)
    (hsumg : (∑ k, g k) = 1) {j : Fin s} {t : ℝ}
    (ht : t ∈ Ioo (arcLo g j) (arcHi g j)) : rhoG r g t ≠ 0 := by
  have ht0 : 0 < t := lt_of_le_of_lt (junc_nonneg (fun k => (hg k).le) j) ht.1
  have ht2 : t < 2 * Real.pi :=
    lt_of_lt_of_le ht.2 (arcHi_le_two_pi (fun k => (hg k).le) hsumg j)
  have hlt : arcLo g j < arcHi g j := lt_trans ht.1 ht.2
  unfold rhoG
  refine Finset.prod_ne_zero_iff.mpr (fun k _ => ?_)
  intro hzero
  have h1 : ‖1 - eAngle (junc g k - t)‖ = 0 := by
    by_contra hne
    exact (ne_of_gt (Real.rpow_pos_of_pos
      (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)) _)) hzero
  have h2 : eAngle (junc g k - t) = 1 :=
    (sub_eq_zero.mp (norm_eq_zero.mp h1)).symm
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h2
  -- `junc g k - t = 2π n`
  have h4 : junc g k - t = 2 * Real.pi * n := by
    have hI : ((junc g k - t : ℝ) : ℂ) * Complex.I * (-Complex.I)
        = ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (-Complex.I) := by rw [hn]
    have h3 : ((junc g k - t : ℝ) : ℂ) = (n : ℂ) * (2 * (Real.pi : ℂ)) := by
      simpa [mul_assoc, Complex.I_mul_I, Complex.neg_re, Complex.neg_im] using hI
    have hre := congrArg Complex.re h3
    have : junc g k - t = (n : ℝ) * (2 * Real.pi) := by simpa using hre
    rw [this]; ring
  -- the value `junc g k` lies in `[0, 2π)`, and `t` lies in `(0, 2π)`, so `n = 0`
  have hjk : junc g k ∈ Set.Ico 0 (2 * Real.pi) :=
    ⟨junc_nonneg (fun k => (hg k).le) k, arcLo_lt_two_pi hg hsumg k⟩
  have hn0 : n = 0 := by
    rcases lt_trichotomy n 0 with h | h | h
    · have hn1 : (n : ℝ) ≤ -1 := by
        have : n ≤ -1 := by omega
        exact_mod_cast this
      nlinarith [Real.pi_pos, ht2, hjk.1, h4]
    · exact h
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        have : (1 : ℤ) ≤ n := by omega
        exact_mod_cast this
      nlinarith [Real.pi_pos, ht0, hjk.2, h4]
  -- hence `junc g k = t`, contradicting the arc bounds
  have h5 : junc g k = t := by
    have h := h4
    simp only [hn0, Int.cast_zero, mul_zero, sub_eq_zero] at h
    exact h
  rcases lt_trichotomy k.val j.val with h | h | h
  · have := arcLo_strict hg (Fin.lt_def.mpr h)
    rw [show arcLo g k = junc g k from rfl, h5] at this
    exact absurd this (not_lt.mpr ht.1.le)
  · rw [show arcLo g j = junc g j from rfl, ← Fin.ext h, h5] at ht
    exact absurd ht.1 (lt_irrefl _)
  · have hkj : j.val + 1 ≤ k.val := h
    have hlt2 : j.val + 1 < s := lt_of_le_of_lt hkj k.isLt
    have h1 : arcLo g ⟨j.val + 1, hlt2⟩ ≤ arcLo g k :=
      arcLo_mono (g := g) (fun i => (hg i).le) (Fin.le_def.mpr hkj)
    have h2 : arcLo g ⟨j.val + 1, hlt2⟩ = arcHi g j := by
      show junc g ⟨j.val + 1, hlt2⟩ = arcHi g j
      rw [junc_succ g hlt2, arcHi_eq_arcLo_add]
      rfl
    rw [show arcLo g k = junc g k from rfl, h5] at h1
    linarith [ht.2, h1, h2]

/-! ## The direction angle of an arc and the rotation match -/

/-- The direction angle of the arc following the junctions with index `≤ j`. -/
def Theta (r g : Fin s → ℝ) (j : Fin s) : ℝ :=
  (∑ k : Fin s, r k * arcLo g k)
    + Real.pi * (2 * (∑ k ∈ Finset.univ.filter (fun k : Fin s => k.val ≤ j.val), r k) - 1)

/-- The direction angles of consecutive arcs differ by `2π r (j+1)`. -/
lemma Theta_succ (r g : Fin s → ℝ) {j : Fin s} (hj : j.val + 1 < s) :
    Theta r g ⟨j.val + 1, hj⟩ = Theta r g j + 2 * Real.pi * r ⟨j.val + 1, hj⟩ := by
  have hgs : r ⟨j.val + 1, hj⟩
      = ∑ k : Fin s, (if k = ⟨j.val + 1, hj⟩ then r k else 0 : ℝ) := by
    rw [Finset.sum_ite_eq' Finset.univ _ (fun k => r k), if_pos (Finset.mem_univ _)]
  have hsum : (∑ k : Fin s, (if k.val ≤ j.val + 1 then r k else 0 : ℝ))
      = (∑ k : Fin s, (if k.val ≤ j.val then r k else 0 : ℝ)) + r ⟨j.val + 1, hj⟩ := by
    rw [hgs, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h1 : k.val ≤ j.val
    · have h2 : k.val ≤ j.val + 1 := by omega
      rw [if_pos h2, if_pos h1]
      have hne : k ≠ ⟨j.val + 1, hj⟩ := by
        intro hk
        rw [hk] at h1
        simp only [Fin.val_mk] at h1
        omega
      rw [if_neg hne, add_zero]
    · by_cases h2 : k.val ≤ j.val + 1
      · have h3 : k = ⟨j.val + 1, hj⟩ := by
          apply Fin.ext
          simp only [Fin.val_mk]
          omega
        rw [if_pos h2, if_neg h1, if_pos h3, zero_add]
      · have hne : k ≠ ⟨j.val + 1, hj⟩ := by
          intro hk
          rw [hk] at h2
          simp only [Fin.val_mk] at h2
          omega
        rw [if_neg h2, if_neg h1, if_neg hne, add_zero]
  have hsum' : (∑ k ∈ Finset.univ.filter (fun k : Fin s => k.val ≤ j.val + 1), r k)
      = (∑ k ∈ Finset.univ.filter (fun k : Fin s => k.val ≤ j.val), r k) + r ⟨j.val + 1, hj⟩ := by
    rw [Finset.sum_filter, Finset.sum_filter]
    exact hsum
  unfold Theta
  rw [hsum']
  ring


/-! ## The arc-direction dictionary -/

/-- **The arc direction** from any `ArcGood` datum. -/
theorem arcGood_direction_of (hs : 0 < s) (r g : Fin s → ℝ)
    (hr : ∀ k, 0 < r k) (hg : ∀ k, 0 < g k) (hsumr : (∑ k, r k) = 1)
    (hsumg : (∑ k, g k) = 1) (j : Fin s) {u : ℂ} {m : ℝ}
    (hAG : Submission.ModelStarImageSeg.ArcGood (fun k => eAngle (arcLo g k)) r
      (arcLo g) hs j u m) :
    u = eAngle (Theta r g j) := by
  have hlt : arcLo g j < arcHi g j := by
    rw [arcHi_eq_arcLo_add]
    have := hg j
    nlinarith [Real.pi_pos]
  set t : ℝ := (arcLo g j + arcHi g j) / 2 with htdef
  have ht : t ∈ Ioo (arcLo g j) (arcHi g j) :=
    ⟨by rw [htdef]; linarith, by rw [htdef]; linarith⟩
  have ht0 : 0 < t := lt_of_le_of_lt (junc_nonneg (fun k => (hg k).le) j) ht.1
  have ht2 : t < 2 * Real.pi :=
    lt_of_lt_of_le ht.2 (arcHi_le_two_pi (fun k => (hg k).le) hsumg j)
  have htne : ∀ k : Fin s, arcLo g k ≠ t := by
    intro k hk
    rcases lt_trichotomy k.val j.val with h | h | h
    · have h1 : arcLo g k < arcLo g j := arcLo_strict hg (Fin.lt_def.mpr h)
      rw [hk] at h1
      exact absurd h1 (not_lt.mpr ht.1.le)
    · have h2 : k = j := Fin.ext h
      have h3 : arcLo g k = arcLo g j := by rw [h2]
      rw [h3] at hk
      exact absurd hk (ne_of_lt ht.1)
    · have hlt2 : j.val + 1 < s := lt_of_le_of_lt h k.isLt
      have h1 : arcLo g ⟨j.val + 1, hlt2⟩ ≤ arcLo g k :=
        arcLo_mono (fun i => (hg i).le) (Fin.le_def.mpr h)
      have h2 : arcLo g ⟨j.val + 1, hlt2⟩ = arcHi g j := by
        show junc g ⟨j.val + 1, hlt2⟩ = arcHi g j
        rw [junc_succ g hlt2, arcHi_eq_arcLo_add]
        rfl
      rw [hk] at h1
      linarith [ht.2, h1, h2]
  have hray := Submission.ModelStarBoundary2.modelF_boundary_ray
    (z₀ := fun k => eAngle (arcLo g k)) (r := r) (φ := arcLo g)
    (fun k => rfl) (fun k => junc_nonneg (fun i => (hg i).le) k)
    (fun k => arcLo_lt_two_pi hg hsumg k)
    hsumr ht0 ht2 htne
  have ht' : t ∈ Ioo (arcLo g j)
      (Submission.ModelStarImageSeg.nextJunction (arcLo g) hs j) := by
    rw [show Submission.ModelStarImageSeg.nextJunction (arcLo g) hs j
        = Submission.ModelStarImageSeg.nextJunction (junc g) hs j from rfl,
      ← arcHi_eq_nextJunction (g := g) hs hsumg j]
    exact ht
  have hAGt : Submission.ModelStarMap.modelF (fun k => eAngle (arcLo g k)) r (eAngle t)
      = (rhoG r g t : ℂ) * u := by
    have h := hAG.2.2.1 t ht'
    simpa only [rhoG, Submission.ModelStarBoundary3.rho, arcLo, junc,
      Submission.ModelStarBoundary2.eAngle] using h
  have hrayG : Submission.ModelStarMap.modelF (fun k => eAngle (arcLo g k)) r (eAngle t)
      = (rhoG r g t : ℂ) *
        eAngle (∑ k : Fin s, r k * (arcLo g k + Real.pi * dirSign (arcLo g) t k)) := by
    have h := hray
    simpa only [rhoG, Submission.ModelStarBoundary3.rho, arcLo, junc,
      Submission.ModelStarBoundary2.eAngle] using h
  have hrho : (rhoG r g t : ℂ) ≠ 0 := by
    have h := rhoG_ne_zero_of_Ioo hr hg hsumg ht
    exact_mod_cast h
  have hcancel : u = eAngle (∑ k : Fin s, r k * (arcLo g k + Real.pi * dirSign (arcLo g) t k)) :=
    mul_left_cancel₀ hrho (hAGt.symm.trans hrayG)
  rw [hcancel]
  have harc : ∀ k : Fin s, (arcLo g k < t ↔ k.val ≤ j.val) := by
    intro k
    constructor
    · intro hk
      by_contra hnot
      push Not at hnot
      have hlt2 : j.val + 1 < s := lt_of_le_of_lt hnot k.isLt
      have h2 : arcLo g ⟨j.val + 1, hlt2⟩ ≤ arcLo g k :=
        arcLo_mono (fun i => (hg i).le) (Fin.le_def.mpr hnot)
      have h3 : arcLo g ⟨j.val + 1, hlt2⟩ = arcHi g j := by
        show junc g ⟨j.val + 1, hlt2⟩ = arcHi g j
        rw [junc_succ g hlt2, arcHi_eq_arcLo_add]
        rfl
      linarith [ht.2, h2, h3, hk]
    · intro hk
      have h2 : arcLo g k ≤ arcLo g j :=
        arcLo_mono (fun i => (hg i).le) (Fin.le_def.mpr hk)
      linarith [ht.1]
  rw [Submission.ModelStarDirection.theta_on_arc (arcLo g) r harc]
  simp only [Theta]
  rw [hsumr]

/-- **The arc direction**: the `ArcGood` direction of arc `j` is
`eAngle (A + 2π R j)`. -/
theorem arcGood_direction (hs : 0 < s) (r g : Fin s → ℝ) (hr : ∀ k, 0 < r k)
    (hg : ∀ k, 0 < g k) (hsumr : (∑ k, r k) = 1) (hsumg : (∑ k, g k) = 1)
    (j : Fin s) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ u = eAngle (Theta r g j) := by
  obtain ⟨u, m, hAG⟩ := Submission.ModelStarImageSeg.exists_arcGood (s := s) hs
    (z₀ := fun k => eAngle (arcLo g k)) (r := r) (φ := arcLo g)
    (fun k => rfl) (fun k => junc_nonneg (fun i => (hg i).le) k)
    (fun k => arcLo_lt_two_pi hg hsumg k)
    hsumr (arcLo_mono (fun k => (hg k).le)) (arcLo_injective hg) hr j
  exact ⟨u, hAG.1, arcGood_direction_of hs r g hr hg hsumr hsumg j hAG⟩


/-! ## The direction angle of an arc and the rotation match -/

/-- The direction angles of the arcs of the family, in order, form the SAME
cyclic pattern as the prescribed enumeration `θ`, up to the single rotation
`eAngle (θ 0 − Θ 0)`. -/
theorem direction_rotation (r g : Fin s → ℝ) (hs : 0 < s) (θ : Fin s → ℝ)
    (hgap : ∀ (k : Fin s) (hk : k.val + 1 < s),
      θ ⟨k.val + 1, hk⟩ - θ k = 2 * Real.pi * r ⟨k.val + 1, hk⟩) :
    ∀ j : Fin s, eAngle (θ j)
      = eAngle (θ ⟨0, hs⟩ - Theta r g ⟨0, hs⟩) * eAngle (Theta r g j) := by
  have key : ∀ n, ∀ (hn : n < s), eAngle (θ ⟨n, hn⟩)
      = eAngle (θ ⟨0, hs⟩ - Theta r g ⟨0, hs⟩) * eAngle (Theta r g ⟨n, hn⟩) := by
    intro n
    induction n with
    | zero =>
      intro hn
      have h0 : (⟨0, hn⟩ : Fin s) = ⟨0, hs⟩ := Fin.ext rfl
      rw [h0]
      have hsplit : θ ⟨0, hs⟩
          = (θ ⟨0, hs⟩ - Theta r g ⟨0, hs⟩) + Theta r g ⟨0, hs⟩ := by ring
      conv_lhs => rw [hsplit]
      rw [Submission.ModelStarDirection.eAngle_add]
    | succ m ih =>
      intro hm
      have hm' : m < s := by omega
      have hstep := hgap ⟨m, hm'⟩ hm
      have hΘ := Theta_succ r g (j := ⟨m, hm'⟩) hm
      rw [show θ ⟨m + 1, hm⟩ = θ ⟨m, hm'⟩ + (θ ⟨m + 1, hm⟩ - θ ⟨m, hm'⟩) from by ring,
        Submission.ModelStarDirection.eAngle_add, ih hm', hstep,
        ← Submission.ModelStarDirection.eAngle_add, hΘ]
      rw [← Submission.ModelStarDirection.eAngle_add,
        ← Submission.ModelStarDirection.eAngle_add]
      ring
  exact fun j => key j.val j.isLt

end Submission.ModelStarFamilyDir

