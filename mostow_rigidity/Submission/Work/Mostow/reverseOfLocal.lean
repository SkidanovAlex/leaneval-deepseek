import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.geoSpec

namespace Work.Mostow

open Submission.Mostow
open LeanEval.Geometry.MostowRigidity

/-!
# `reverseOfLocal` — a local reverse bound upgrades to a global reverse quasi-isometry bound

If `Φ : ℍⁿ → ℍⁿ` is `Cs`-coarsely surjective and `M`-locally `a`-expanding
(`hdist (Φ u) (Φ v) ≤ M → hdist u v ≤ a`), with `2 Cs + 1 ≤ M`, then

  `hdist u v ≤ max a 1 * hdist (Φ u) (Φ v) + 2 a`  for all `u, v`.

The proof subdivides the geodesic from `Φ u` to `Φ v` (via the explicit chart geodesic `geo`)
into `⌈d⌉` arcs of length `≤ 1`; each arc lifts, through coarse surjectivity, to a pair of
preimages whose `Φ`-images are within `Cs + 1 + Cs ≤ M`, hence at distance `≤ a`.  Summing the
`⌈d⌉` links bounds `hdist u v` by `⌈d⌉ * a ≤ max a 1 * d + 2 a`.
-/

variable {n : ℕ}

/-- The distance along a finite chain is bounded by the sum of the increments. -/
private theorem hdist_chain_le {n : ℕ} (hI : HypIsoData n) (f : ℕ → E n) (k : ℕ) :
    hdist (f 0) (f k) ≤ ∑ i ∈ Finset.range k, hdist (f i) (f (i + 1)) := by
  induction k with
  | zero => simp [hdist_self]
  | succ k ih =>
    have h1 : hdist (f 0) (f (k+1)) ≤ hdist (f 0) (f k) + hdist (f k) (f (k+1)) :=
      hI.triangle (f 0) (f k) (f (k+1))
    rw [Finset.sum_range_succ]
    linarith

theorem reverseOfLocal {n : ℕ} (hI : Work.Mostow.HypIsoData n)
    {Φ : Submission.Mostow.E n → Submission.Mostow.E n} {a Cs M : ℝ}
    (ha : 0 ≤ a) (hCs : 0 ≤ Cs)
    (hsurj : ∀ w : Submission.Mostow.E n, ∃ u : Submission.Mostow.E n,
      Submission.Mostow.hdist (Φ u) w ≤ Cs)
    (hrevloc : ∀ u v : Submission.Mostow.E n,
      Submission.Mostow.hdist (Φ u) (Φ v) ≤ M → Submission.Mostow.hdist u v ≤ a)
    (hM : 2 * Cs + 1 ≤ M) :
    ∀ u v : Submission.Mostow.E n,
      Submission.Mostow.hdist u v ≤ max a 1 * Submission.Mostow.hdist (Φ u) (Φ v) + 2 * a := by
  intro u v
  have hM1 : 1 ≤ M := by linarith
  have hΦ : 0 ≤ hdist (Φ u) (Φ v) := hI.nonneg _ _
  rcases le_or_gt (hdist (Φ u) (Φ v)) 1 with hd1 | hd1
  · -- small case: the local hypothesis applies directly
    have hM' : hdist (Φ u) (Φ v) ≤ M := by linarith
    have huv := hrevloc u v hM'
    have hnn : 0 ≤ max a 1 * hdist (Φ u) (Φ v) :=
      mul_nonneg (le_max_of_le_right zero_le_one) (hI.nonneg _ _)
    linarith
  · -- large case: subdivide the geodesic from `Φ u` to `Φ v`
    set d : ℝ := hdist (Φ u) (Φ v) with hd
    have hd0 : 0 < d := by rw [hd]; linarith
    set k : ℕ := Nat.ceil d with hk
    have hkpos : 0 < k := by rw [hk]; exact Nat.ceil_pos.mpr hd0
    have hkr : (0:ℝ) < (k:ℝ) := by exact_mod_cast hkpos
    have hdle : d ≤ (k : ℝ) := by rw [hk]; exact Nat.le_ceil d
    have hklt : (k : ℝ) < d + 1 := by rw [hk]; exact Nat.ceil_lt_add_one (le_of_lt hd0)
    -- the subdivision points on the geodesic
    set w : ℕ → E n := (fun i => geo (Φ u) (Φ v) ((i:ℝ)/(k:ℝ))) with hw
    have hw0 : w 0 = Φ u := by
      rw [hw]; dsimp only
      rw [show ((0:ℕ):ℝ) = 0 by norm_num, zero_div]
      exact (geoSpec (Φ u) (Φ v) 0 0 ⟨le_refl 0, zero_le_one⟩ ⟨le_refl 0, zero_le_one⟩).1
    have hwk : w k = Φ v := by
      rw [hw]; dsimp only
      rw [div_self (ne_of_gt hkr)]
      exact (geoSpec (Φ u) (Φ v) 1 1 ⟨zero_le_one, le_refl 1⟩ ⟨zero_le_one, le_refl 1⟩).2.1
    -- consecutive subdivision points are at distance at most 1
    have hstep : ∀ i : ℕ, i < k → hdist (w i) (w (i+1)) ≤ 1 := by
      intro i hi
      have hwi : w i = geo (Φ u) (Φ v) ((i:ℝ)/(k:ℝ)) := by simp only [hw]
      have hwj : w (i+1) = geo (Φ u) (Φ v) (((i+1:ℕ):ℝ)/(k:ℝ)) := by simp only [hw]
      have hik : i ≤ k := le_of_lt hi
      have hi1 : i + 1 ≤ k := hi
      have hs : ((i:ℝ)/(k:ℝ)) ∈ Set.Icc (0:ℝ) 1 := by
        refine ⟨div_nonneg (Nat.cast_nonneg i) (le_of_lt hkr), ?_⟩
        rw [div_le_one hkr]; exact_mod_cast hik
      have ht : (((i+1:ℕ):ℝ)/(k:ℝ)) ∈ Set.Icc (0:ℝ) 1 := by
        refine ⟨div_nonneg (Nat.cast_nonneg (i+1)) (le_of_lt hkr), ?_⟩
        rw [div_le_one hkr]; exact_mod_cast hi1
      have hg := (geoSpec (Φ u) (Φ v) ((i:ℝ)/(k:ℝ)) (((i+1:ℕ):ℝ)/(k:ℝ)) hs ht).2.2
      rw [hwi, hwj, hg]
      have harg : |((i:ℝ)/(k:ℝ)) - (((i+1:ℕ):ℝ)/(k:ℝ))| = 1/(k:ℝ) := by
        rw [← sub_div, abs_div, abs_of_pos hkr]
        have hnum : (i:ℝ) - ((i+1:ℕ):ℝ) = -1 := by push_cast; ring
        rw [hnum, abs_neg, abs_one]
      rw [harg, ← hd]
      have hkd : (1/(k:ℝ)) * d ≤ 1 := by
        have heq : (1/(k:ℝ)) * d = d / (k:ℝ) := by ring
        rw [heq, div_le_one hkr]; exact hdle
      exact hkd
    -- a chain of preimages, with the correct endpoints
    set p : ℕ → E n :=
      (fun i => if i = 0 then u else if i = k then v else (hsurj (w i)).choose) with hp
    have hp0 : p 0 = u := by simp only [hp]; simp
    have hpk : p k = v := by
      simp only [hp]
      rw [if_neg (show ¬ (k = 0) from ne_of_gt hkpos)]
      simp
    -- every `p i` is a `Cs`-preimage of `w i`
    have hpCs : ∀ i, hdist (Φ (p i)) (w i) ≤ Cs := by
      intro i
      by_cases h0 : i = 0
      · subst h0
        rw [hp0, hw0, hdist_self]; exact hCs
      · by_cases hk' : i = k
        · subst hk'
          rw [hpk, hwk, hdist_self]; exact hCs
        · have hpi : p i = (hsurj (w i)).choose := by
            simp only [hp]
            rw [if_neg h0, if_neg hk']
          rw [hpi]; exact (hsurj (w i)).choose_spec
    -- each link is `a`-short
    have hlink : ∀ i, i < k → hdist (p i) (p (i+1)) ≤ a := by
      intro i hi
      apply hrevloc
      have t1 : hdist (Φ (p i)) (Φ (p (i+1)))
          ≤ hdist (Φ (p i)) (w i) + hdist (w i) (Φ (p (i+1))) := hI.triangle _ _ _
      have t2 : hdist (w i) (Φ (p (i+1)))
          ≤ hdist (w i) (w (i+1)) + hdist (w (i+1)) (Φ (p (i+1))) := hI.triangle _ _ _
      have t3 : hdist (w (i+1)) (Φ (p (i+1))) = hdist (Φ (p (i+1))) (w (i+1)) := hI.symm _ _
      rw [t3] at t2
      linarith [t1, t2, hpCs i, hpCs (i+1), hstep i hi, hM]
    have hchain := hdist_chain_le hI p k
    rw [hp0, hpk] at hchain
    have hsum : ∑ i ∈ Finset.range k, hdist (p i) (p (i+1)) ≤ (k:ℝ) * a := by
      calc ∑ i ∈ Finset.range k, hdist (p i) (p (i+1))
          ≤ ∑ i ∈ Finset.range k, a := by
            apply Finset.sum_le_sum
            intro i hi
            exact hlink i (Finset.mem_range.mp hi)
        _ = (k:ℝ) * a := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hka : (k:ℝ) * a ≤ max a 1 * d + 2 * a := by
      have h1 : (k:ℝ) * a ≤ (d + 1) * a :=
        mul_le_mul_of_nonneg_right (by linarith [hklt]) ha
      have h3 : a * d ≤ max a 1 * d :=
        mul_le_mul_of_nonneg_right (le_max_left a 1) hΦ
      nlinarith [h1, h3, ha]
    linarith [hchain, hsum, hka]

end Work.Mostow
