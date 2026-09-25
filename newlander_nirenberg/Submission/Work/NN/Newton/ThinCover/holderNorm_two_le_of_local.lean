import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc

namespace Work.NN.Newton.ThinCover

open scoped NNReal ENNReal
open Set

/-- The elementary coefficient identity `(6 + 6/s)·ℓ = 6·ℓ + 3·(2ℓ/s)` at the level of
`ℝ≥0∞`-valued `ofReal`s. -/
private lemma coeff_eq (ℓ s : ℝ) (hs : 0 < s) (hℓ : 0 ≤ ℓ) :
    ENNReal.ofReal (6 + 6 / s) * ENNReal.ofReal ℓ
      = 6 * ENNReal.ofReal ℓ + 3 * ENNReal.ofReal (2 * ℓ / s) := by
  have h6s : 0 ≤ 6 + 6 / s := by positivity
  have h6 : (6 : ℝ≥0∞) * ENNReal.ofReal ℓ = ENNReal.ofReal (6 * ℓ) := by
    rw [← ENNReal.ofReal_ofNat 6, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 6)]
  have h3 : (3 : ℝ≥0∞) * ENNReal.ofReal (2 * ℓ / s) = ENNReal.ofReal (6 * ℓ / s) := by
    rw [← ENNReal.ofReal_ofNat 3,
      ← ENNReal.ofReal_mul (p := (3:ℝ)) (q := 2 * ℓ / s) (by norm_num : (0:ℝ) ≤ 3)]
    congr 1
    field_simp
    ring
  rw [← ENNReal.ofReal_mul h6s]
  rw [h6, h3]
  rw [← ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ 6*ℓ) (by positivity : (0:ℝ) ≤ 6*ℓ/s)]
  congr 1
  field_simp

/-- **From a uniform local level-2 bound to a global one.**

If every point `c` of an open set `P` carries a local bound `holderNorm 2 α u (polydisc c (2s)) ≤ L`
for a common `L` (with `0 < s ≤ 1`), then `holderNorm 2 α u P ≤ (6 + 6/s) L`: the derivatives at a
point are bounded by the local bound at that point, pairs at distance `≤ s` lie in a common
polydisc of radius `2s`, and pairs at distance `> s` are estimated by `2·sup/s^α ≤ 2·sup/s`
(as `α < 1`, `s ≤ 1`).  No finiteness of `L` is needed (`L = ⊤` makes the claim trivial). -/
theorem holderNorm_two_le_of_local {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {u : Work.NN.Core.Cn n → ℂ} {P : Set (Work.NN.Core.Cn n)} (hP : IsOpen P)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {L : ℝ≥0∞}
    (hloc : ∀ c : Work.NN.Core.Cn n, c ∈ P → Work.CR.Flat.holderNorm 2 α u
        (Work.CR.Flat.polydisc c (fun _ => 2 * s)) ≤ L) :
    Work.CR.Flat.holderNorm 2 α u P ≤ ENNReal.ofReal (6 + 6 / s) * L := by
  rcases eq_or_ne L ⊤ with hL | hL
  · -- `L = ⊤`: the right-hand side is `⊤` because the coefficient is non-zero.
    have hne : ENNReal.ofReal (6 + 6 / s) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    rw [hL, ENNReal.mul_top hne]
    exact le_top
  · -- `L = ofReal L.toReal` is finite.
    have hℓnn : (0 : ℝ) ≤ L.toReal := ENNReal.toReal_nonneg
    have hLℓ : L = ENNReal.ofReal L.toReal := (ENNReal.ofReal_toReal hL).symm
    have hmem_self : ∀ x : Work.NN.Core.Cn n, x ∈ Work.CR.Flat.polydisc x (fun _ => 2 * s) := by
      intro x j
      simp only [sub_self, norm_zero]
      linarith
    -- (A) The iterated derivatives at a point are bounded by the local bound at that point.
    have hA : ∀ i ≤ 2, Work.CR.Flat.iterDerivNorm i u P ≤ L := by
      intro i hi
      refine iSup₂_le fun x hx => ?_
      have hopen : IsOpen (Work.CR.Flat.polydisc x (fun _ : Fin n => 2 * s)) :=
        Work.CR.Flat.isOpen_polydisc x _
      calc ENNReal.ofReal ‖iteratedFDerivWithin ℝ i u P x‖
          = ENNReal.ofReal
              ‖iteratedFDerivWithin ℝ i u (Work.CR.Flat.polydisc x (fun _ => 2 * s)) x‖ := by
            rw [iteratedFDerivWithin_of_isOpen i hP hx,
              ← iteratedFDerivWithin_of_isOpen i hopen (hmem_self x)]
        _ ≤ Work.CR.Flat.iterDerivNorm i u (Work.CR.Flat.polydisc x (fun _ => 2 * s)) :=
            Work.CR.Flat.le_iterDerivNorm i u _ (hmem_self x)
        _ ≤ Work.CR.Flat.holderNorm 2 α u (Work.CR.Flat.polydisc x (fun _ => 2 * s)) :=
            Work.CR.Flat.iterDerivNorm_le_holderNorm 2 α u _ hi
        _ ≤ L := hloc x hx
    -- (B) The Hölder seminorms: near pairs go into the polydisc of radius `2s` about `x`,
    -- far pairs are estimated by `2 L.toReal / s`.
    have hB : ∀ i ≤ 2, Work.CR.Flat.holderSeminorm i α u P
        ≤ L + ENNReal.ofReal (2 * L.toReal / s) := by
      intro i hi
      refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
      have hopen : IsOpen (Work.CR.Flat.polydisc x (fun _ : Fin n => 2 * s)) :=
        Work.CR.Flat.isOpen_polydisc x _
      by_cases hnear : ‖x - y‖ ≤ s
      · -- near pair: both points lie in the polydisc of radius `2s` about `x`
        have hymem : y ∈ Work.CR.Flat.polydisc x (fun _ => 2 * s) := by
          intro j
          have h1 : ‖y j - x j‖ ≤ ‖x - y‖ := by
            calc ‖y j - x j‖ ≤ ‖y - x‖ := norm_le_pi_norm (y - x) j
              _ = ‖x - y‖ := norm_sub_rev y x
          linarith
        have ex : iteratedFDerivWithin ℝ i u P x
            = iteratedFDerivWithin ℝ i u (Work.CR.Flat.polydisc x (fun _ => 2 * s)) x := by
          rw [iteratedFDerivWithin_of_isOpen i hP hx,
            iteratedFDerivWithin_of_isOpen i hopen (hmem_self x)]
        have ey : iteratedFDerivWithin ℝ i u P y
            = iteratedFDerivWithin ℝ i u (Work.CR.Flat.polydisc x (fun _ => 2 * s)) y := by
          rw [iteratedFDerivWithin_of_isOpen i hP hy,
            iteratedFDerivWithin_of_isOpen i hopen hymem]
        calc ENNReal.ofReal (‖iteratedFDerivWithin ℝ i u P x -
                iteratedFDerivWithin ℝ i u P y‖ / ‖x - y‖ ^ α)
            = ENNReal.ofReal (‖iteratedFDerivWithin ℝ i u
                  (Work.CR.Flat.polydisc x (fun _ => 2 * s)) x -
                iteratedFDerivWithin ℝ i u
                  (Work.CR.Flat.polydisc x (fun _ => 2 * s)) y‖ / ‖x - y‖ ^ α) := by
              rw [ex, ey]
          _ ≤ Work.CR.Flat.holderSeminorm i α u (Work.CR.Flat.polydisc x (fun _ => 2 * s)) :=
              Work.CR.Flat.le_holderSeminorm i α u _ (hmem_self x) hymem hxy
          _ ≤ Work.CR.Flat.holderNorm 2 α u (Work.CR.Flat.polydisc x (fun _ => 2 * s)) :=
              Work.CR.Flat.holderSeminorm_le_holderNorm 2 α u _ hi
          _ ≤ L := hloc x hx
          _ ≤ L + ENNReal.ofReal (2 * L.toReal / s) := le_add_right le_rfl
      · -- far pair: `‖x - y‖ > s`
        rw [not_le] at hnear
        have hxℓ : ‖iteratedFDerivWithin ℝ i u P x‖ ≤ L.toReal :=
          (ENNReal.ofReal_le_iff_le_toReal hL).mp
            (le_trans (Work.CR.Flat.le_iterDerivNorm i u P hx) (hA i hi))
        have hyℓ : ‖iteratedFDerivWithin ℝ i u P y‖ ≤ L.toReal :=
          (ENNReal.ofReal_le_iff_le_toReal hL).mp
            (le_trans (Work.CR.Flat.le_iterDerivNorm i u P hy) (hA i hi))
        have hnorm : ‖iteratedFDerivWithin ℝ i u P x - iteratedFDerivWithin ℝ i u P y‖
            ≤ 2 * L.toReal := by
          calc ‖iteratedFDerivWithin ℝ i u P x - iteratedFDerivWithin ℝ i u P y‖
              ≤ ‖iteratedFDerivWithin ℝ i u P x‖ + ‖iteratedFDerivWithin ℝ i u P y‖ :=
                norm_sub_le _ _
            _ ≤ L.toReal + L.toReal := add_le_add hxℓ hyℓ
            _ = 2 * L.toReal := by ring
        have hss : s ≤ s ^ α := by
          have h := Real.rpow_le_rpow_of_exponent_ge hs hs1 hα1.le
          rwa [Real.rpow_one] at h
        have hsα : s ^ α ≤ ‖x - y‖ ^ α := Real.rpow_le_rpow hs.le hnear.le hα0.le
        have hsαpos : 0 < s ^ α := Real.rpow_pos_of_pos hs α
        have hmain : ‖iteratedFDerivWithin ℝ i u P x - iteratedFDerivWithin ℝ i u P y‖
            / ‖x - y‖ ^ α ≤ 2 * L.toReal / s :=
          calc ‖iteratedFDerivWithin ℝ i u P x - iteratedFDerivWithin ℝ i u P y‖ / ‖x - y‖ ^ α
              ≤ (2 * L.toReal) / s ^ α :=
                div_le_div₀ (by positivity : (0:ℝ) ≤ 2 * L.toReal) hnorm hsαpos hsα
            _ ≤ (2 * L.toReal) / s := div_le_div_of_nonneg_left (by positivity) hs hss
        calc ENNReal.ofReal (‖iteratedFDerivWithin ℝ i u P x -
                iteratedFDerivWithin ℝ i u P y‖ / ‖x - y‖ ^ α)
            ≤ ENNReal.ofReal (2 * L.toReal / s) := ENNReal.ofReal_le_ofReal hmain
          _ ≤ L + ENNReal.ofReal (2 * L.toReal / s) := le_add_left le_rfl
    -- (C) Assemble the six terms.
    have hsum : Work.CR.Flat.holderNorm 2 α u P
        = (Work.CR.Flat.iterDerivNorm 0 u P + Work.CR.Flat.holderSeminorm 0 α u P)
        + (Work.CR.Flat.iterDerivNorm 1 u P + Work.CR.Flat.holderSeminorm 1 α u P)
        + (Work.CR.Flat.iterDerivNorm 2 u P + Work.CR.Flat.holderSeminorm 2 α u P) := by
      simp [Work.CR.Flat.holderNorm, Finset.sum_range_succ]
    have hcoef : ENNReal.ofReal (6 + 6 / s) * L
        = 6 * L + 3 * ENNReal.ofReal (2 * L.toReal / s) := by
      rw [hLℓ, ENNReal.toReal_ofReal hℓnn]
      exact coeff_eq L.toReal s hs hℓnn
    rw [hcoef, hsum]
    have t0 := add_le_add (hA 0 (by norm_num)) (hB 0 (by norm_num))
    have t1 := add_le_add (hA 1 (by norm_num)) (hB 1 (by norm_num))
    have t2 := add_le_add (hA 2 le_rfl) (hB 2 le_rfl)
    refine le_trans (add_le_add (add_le_add t0 t1) t2) (le_of_eq ?_)
    ring

end Work.NN.Newton.ThinCover
