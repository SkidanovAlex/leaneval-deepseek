import Mathlib
import Submission.Work.Mostow.localIsomDefs
import Submission.Work.Mostow.betweenTrans

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- **Gluing of a locally geodesic parametrisation.**

Let `γ : ℝ → ℍⁿ` be a curve which is a local isometry on the interval `[0,d]` at scale `δ`
(`hloc`), where `hdist` is the hyperbolic distance with the triangle inequality `htri` and
positive-definiteness `hzero`.  Then `hdist (γ 0) (γ d) = d`: a locally arclength-parametrised
curve is globally geodesic, because hyperbolic space is a Hadamard space and has no closed
geodesics that could produce a shortcut.

The proof bootstraps from the local information using transitivity of betweenness
(`betweenTrans`): if `γ` is known to be radially geodesic from `γ 0` on `[0,t]`, and
`h' < δ - (u - t)`, then the four points `γ 0`, `γ (t-h')`, `γ t`, `γ u` are arranged so that
two triangle equalities hold, whence `hdist (γ 0) (γ u) = u`.  Iterating (Archimedes) reaches `d`. -/
theorem gluing {n : ℕ} (γ : ℝ → E n) (d δ : ℝ) (hd : 0 ≤ d) (hδ : 0 < δ)
    (htri : ∀ x y z : E n, hdist x z ≤ hdist x y + hdist y z)
    (hzero : ∀ x y : E n, hdist x y = 0 ↔ x = y)
    (hloc : ∀ s s' : ℝ, s ∈ Set.Icc 0 d → s' ∈ Set.Icc 0 d → |s - s'| < δ →
      hdist (γ s) (γ s') = |s - s'|) :
    hdist (γ 0) (γ d) = d := by
  have h2δ : 0 < δ / 2 := by linarith
  -- the "good" predicate: `γ` is radially geodesic from `γ 0` on `[0,t]`
  let Good : ℝ → Prop := fun t => ∀ u, 0 ≤ u → u ≤ t → hdist (γ 0) (γ u) = u
  have hGood0 : Good 0 := by
    intro u hu0 hu0'
    have hu : u = 0 := le_antisymm hu0' hu0
    subst hu
    exact (hzero (γ 0) (γ 0)).2 rfl
  have hGood_mono : ∀ {t t' : ℝ}, Good t → t' ≤ t → Good t' := by
    intro t t' ht htt' u hu0 hut'
    exact ht u hu0 (le_trans hut' htt')
  -- the extension step
  have hstep : ∀ t : ℝ, Good t → 0 ≤ t → t < d → Good (min (t + δ/2) d) := by
    intro t ht ht0 htd
    intro u hu0 hu_le
    have hutδ : u ≤ t + δ / 2 := le_trans hu_le (min_le_left _ _)
    have hud : u ≤ d := le_trans hu_le (min_le_right _ _)
    have huI : u ∈ Set.Icc 0 d := ⟨hu0, hud⟩
    rcases lt_or_ge t u with htu | hut
    · -- t < u
      have hℓ0 : 0 < u - t := sub_pos.mpr htu
      have hℓle : u - t ≤ δ / 2 := by linarith
      rcases eq_or_lt_of_le ht0 with hteq | htpos
      · -- t = 0
        have huδ : u < δ := by rw [← hteq] at hutδ; linarith
        have h0I : (0 : ℝ) ∈ Set.Icc 0 d := ⟨le_refl 0, hd⟩
        have h := hloc 0 u h0I huI (by rw [zero_sub, abs_neg, abs_of_nonneg hu0]; exact huδ)
        rwa [zero_sub, abs_neg, abs_of_nonneg hu0] at h
      · -- 0 < t
        set h' : ℝ := min (t / 2) ((δ - (u - t)) / 2) with hh'
        have h'pos : 0 < h' := by rw [hh']; exact lt_min (by linarith) (by linarith)
        have h'le_t : h' ≤ t := by
          rw [hh']; exact le_trans (min_le_left _ _) (by linarith)
        have h'lt_dl : h' < δ - (u - t) := by
          rw [hh']; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
        have h'lt_δ : h' < δ := by linarith
        have htm0 : 0 ≤ t - h' := by linarith
        have htmle : t - h' ≤ d := by linarith
        have htI : t ∈ Set.Icc 0 d := ⟨ht0, le_of_lt htd⟩
        have htmI : t - h' ∈ Set.Icc 0 d := ⟨htm0, htmle⟩
        have hBt : hdist (γ 0) (γ t) = t := ht t ht0 le_rfl
        have hBtm : hdist (γ 0) (γ (t - h')) = t - h' := ht (t - h') htm0 (by linarith)
        have hloc_tu : hdist (γ t) (γ u) = u - t := by
          have hgap : |t - u| < δ := by
            rw [abs_of_neg (by linarith : t - u < 0)]; linarith
          have h := hloc t u htI huI hgap
          rw [abs_of_neg (by linarith : t - u < 0)] at h
          linarith
        have hloc_mt : hdist (γ (t - h')) (γ t) = h' := by
          have hgap : |(t - h') - t| < δ := by
            rw [show (t - h') - t = -h' from by ring, abs_neg, abs_of_pos h'pos]; exact h'lt_δ
          have h := hloc (t - h') t htmI htI hgap
          rwa [show (t - h') - t = -h' from by ring, abs_neg, abs_of_pos h'pos] at h
        have hloc_mu : hdist (γ (t - h')) (γ u) = u - (t - h') := by
          have hgap : |(t - h') - u| < δ := by
            rw [abs_of_neg (by linarith : (t - h') - u < 0)]; linarith
          have h := hloc (t - h') u htmI huI hgap
          rw [abs_of_neg (by linarith : (t - h') - u < 0)] at h
          linarith
        have hyz : γ (t - h') ≠ γ t := by
          intro heq
          have hz : hdist (γ (t - h')) (γ t) = 0 := (hzero _ _).2 heq
          linarith [hloc_mt, h'pos]
        have h1 : hdist (γ 0) (γ t)
            = hdist (γ 0) (γ (t - h')) + hdist (γ (t - h')) (γ t) := by
          rw [hBt, hBtm, hloc_mt]; ring
        have h2 : hdist (γ (t - h')) (γ u)
            = hdist (γ (t - h')) (γ t) + hdist (γ t) (γ u) := by
          rw [hloc_mu, hloc_mt, hloc_tu]; ring
        have hconcl := betweenTrans (γ 0) (γ (t - h')) (γ t) (γ u) hyz h1 h2
        rw [hBtm, hloc_mu] at hconcl
        linarith [hconcl]
    · exact ht u hu0 hut
  -- Archimedean induction
  have hind : ∀ k : ℕ, Good (min ((k : ℝ) * (δ / 2)) d) := by
    intro k
    induction k with
    | zero =>
        have hz : min (((0 : ℕ) : ℝ) * (δ / 2)) d = 0 := by
          rw [Nat.cast_zero, zero_mul, min_eq_left hd]
        rw [hz]; exact hGood0
    | succ k ih =>
        have hcast : (((k + 1 : ℕ)) : ℝ) * (δ / 2) = (k : ℝ) * (δ / 2) + δ / 2 := by
          push_cast; ring
        by_cases hkd : (k : ℝ) * (δ / 2) ≤ d
        · have ih' : Good ((k : ℝ) * (δ / 2)) := by rwa [min_eq_left hkd] at ih
          by_cases hklt : (k : ℝ) * (δ / 2) < d
          · have hstep' := hstep ((k : ℝ) * (δ / 2)) ih'
              (mul_nonneg (Nat.cast_nonneg k) (le_of_lt h2δ)) hklt
            rw [hcast]; exact hstep'
          · have hklt' : d ≤ (k : ℝ) * (δ / 2) := not_lt.mp hklt
            have hkk : min ((((k + 1 : ℕ)) : ℝ) * (δ / 2)) d = d := by
              exact min_eq_right (by rw [hcast]; linarith)
            rw [hkk]
            rw [show d = (k : ℝ) * (δ / 2) from le_antisymm hklt' hkd]
            exact ih'
        · have hkd' : d < (k : ℝ) * (δ / 2) := not_le.mp hkd
          have ihd : Good d := by rwa [min_eq_right (le_of_lt hkd')] at ih
          have hkk : min ((((k + 1 : ℕ)) : ℝ) * (δ / 2)) d = d := by
            exact min_eq_right (by rw [hcast]; linarith)
          rw [hkk]; exact ihd
  obtain ⟨k, hk⟩ := exists_nat_ge (d / (δ / 2))
  have hk' : d ≤ (k : ℝ) * (δ / 2) := by
    have h3 := mul_le_mul_of_nonneg_right hk (le_of_lt h2δ)
    rwa [div_mul_cancel₀ d (ne_of_gt h2δ)] at h3
  have hGd : Good d := by
    have := hind k
    rwa [min_eq_right hk'] at this
  exact hGd d hd le_rfl

end Work.Mostow
