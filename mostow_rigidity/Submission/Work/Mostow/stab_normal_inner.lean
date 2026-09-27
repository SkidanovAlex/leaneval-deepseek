import Mathlib
import Submission.Work.Mostow.cosh_hdist_fermi
import Submission.Work.Mostow.fermi_inv

namespace Work.Mostow

/-! For an isometry `g'` of `ℍ^{k+m}` fixing the standard stratum pointwise, the induced map on the
normal fibre, `R w := (fermiInv k m (g' • fermi k m 0 w)).2`, preserves the Euclidean inner product
and is surjective (together with `Work.Mostow.linear_isometry_of_inner` this makes `R` an element of
`O(m)`; `‖R w‖ = ‖w‖` follows from `inner ℝ (R w) (R w) = inner ℝ w w`).

Guidance.  (a) Norm/foot: by the foot facts (stated separately as `Work.Mostow.stab_fermi_foot`,
reprove them privately if needed) `g' • fermi k m 0 w = fermi k m 0 (R w)` and `‖R w‖ = ‖w‖`.
The isometry clause of `HypIsometryProp (k+m)` gives
`hdist (fermi k m 0 (R w)) (fermi k m 0 (R w')) = hdist (fermi k m 0 w) (fermi k m 0 w')`;
take `cosh`, expand with `Work.Mostow.cosh_hdist_fermi` at `v = v' = 0`
(`hdist 0 0 = 0`, `Real.cosh 0 = 1`, `inner ℝ 0 _ = 0`), cancel the common
`cosh ‖w‖ * cosh ‖w'‖` using `‖R w‖ = ‖w‖`, and divide by the positive `sinhc ‖w‖ * sinhc ‖w'‖`
(the degenerate cases `w = 0` or `w' = 0` are immediate since then `R w = 0`).
(b) Surjectivity: `g'⁻¹` also fixes the stratum pointwise (from `hg'`, the multiplication law and
`inv_mul_cancel` in `POActionProp (k + m)`, together with `(g⁻¹ * g) • u = u`), so the same foot
computation applies to `g'⁻¹`; given `y : E m`, the point `g'⁻¹ • fermi k m 0 y` equals
`fermi k m 0 y'` with `y' := (fermiInv k m (g'⁻¹ • fermi k m 0 y)).2`, and applying `g'`
(and the formula for `g'` at `v = 0`) yields `R y' = y`. -/

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-! ### Private preliminaries about the Fermi chart -/

/-- Helper re-proof of `sinhc` positivity (`sinhc s = sinh s / s` for `s ≠ 0`, `sinhc 0 = 1`). -/
private lemma sinhc_pos_loc (s : ℝ) : 0 < sinhc s := by
  rw [sinhc]
  by_cases h : s = 0
  · simp [h]
  · simp only [h, ↓reduceIte]
    rcases lt_trichotomy s 0 with hs | hs | hs
    · exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr hs) hs
    · exact absurd hs h
    · exact div_pos (Real.sinh_pos_iff.mpr hs) hs

private lemma fermi_zero_eq_coordEmb_loc (k m : ℕ) (v : E k) :
    fermi k m v (0 : E m) = coordEmb k m v := by
  simp only [fermi, coordEmb, sinhc, norm_zero, Real.cosh_zero, one_mul]
  norm_num

/-- `tanC` of an embedded point of the stratum. -/
private lemma tanC_coordEmb_loc (k m : ℕ) (v : E k) : tanC k m (coordEmb k m v) = v := by
  ext i; simp [tanC, coordEmb]

/-- `coordEmb k m` is an isometry for `hdist`. -/
private lemma hdist_coordEmb_loc (k m : ℕ) (a b : E k) :
    hdist (coordEmb k m a) (coordEmb k m b) = hdist a b := by
  have h1 : ∀ x : E k, tpart (coordEmb k m x) = tpart x := fun x => by
    rw [← fermi_zero_eq_coordEmb_loc k m x, Work.Mostow.tpart_fermi]; simp
  have h2 : inner ℝ (coordEmb k m a) (coordEmb k m b) = inner ℝ a b := by
    rw [← fermi_zero_eq_coordEmb_loc k m a, ← fermi_zero_eq_coordEmb_loc k m b,
      Work.Mostow.inner_fermi]
    simp only [norm_zero, Real.cosh_zero, sinhc, one_mul, inner_zero_right, mul_zero, add_zero]
  rw [hdist, hdist, h1 a, h1 b, h2]

/-- `coordEmb k m` is injective. -/
private lemma coordEmb_injective_loc (k m : ℕ) : Function.Injective (coordEmb k m) := by
  intro a b h
  have h2 := congrArg (tanC k m) h
  rwa [tanC_coordEmb_loc, tanC_coordEmb_loc] at h2

/-- The foot facts: an isometry of `ℍ^{k+m}` fixing the standard stratum pointwise preserves the
foot coordinate and the norm of the normal coordinate. -/
private lemma stab_fermi_foot_loc {k m : ℕ} (hI : HypIsometryProp (k + m))
    (h : PO (k + m) 1) (hh : ∀ v : E k, h • coordEmb k m v = coordEmb k m v)
    (v : E k) (w : E m) :
    (fermiInv k m (h • fermi k m v w)).1 = v ∧
      ‖(fermiInv k m (h • fermi k m v w)).2‖ = ‖w‖ := by
  have hiso := hI.2.2.2.2.2.2.1
  have hzero := hI.2.2.1
  have hpos := hI.1
  have hsym := hI.2.1
  set W : E k := (fermiInv k m (h • fermi k m v w)).1 with hW
  set Ŵ : E m := (fermiInv k m (h • fermi k m v w)).2 with hŴ
  have hpoint : fermi k m W Ŵ = h • fermi k m v w := (Work.Mostow.fermi_inv k m).2.1 _
  have key : ∀ v' : E k, Real.cosh ‖Ŵ‖ * Real.cosh (hdist W v')
      = Real.cosh ‖w‖ * Real.cosh (hdist v v') := by
    intro v'
    have h1 : hdist (h • fermi k m v w) (h • coordEmb k m v')
        = hdist (fermi k m v w) (coordEmb k m v') := hiso h _ _
    rw [hh v'] at h1
    rw [← hpoint, ← fermi_zero_eq_coordEmb_loc k m v'] at h1
    have h2 := congrArg Real.cosh h1
    rw [Work.Mostow.cosh_hdist_fermi, Work.Mostow.cosh_hdist_fermi] at h2
    have hs0 : sinhc (0 : ℝ) = 1 := by rw [sinhc]; norm_num
    simp only [norm_zero, Real.cosh_zero, hs0, inner_zero_right, mul_one, mul_zero,
      sub_zero] at h2
    exact h2
  have hv0 : hdist v v = 0 := by
    have h1 : hdist (coordEmb k m v) (coordEmb k m v) = 0 := (hzero _ _).mpr rfl
    rwa [hdist_coordEmb_loc] at h1
  have hW0 : hdist W W = 0 := by
    have h1 : hdist (coordEmb k m W) (coordEmb k m W) = 0 := (hzero _ _).mpr rfl
    rwa [hdist_coordEmb_loc] at h1
  have hsymk : hdist W v = hdist v W := by
    have h1 := hsym (coordEmb k m W) (coordEmb k m v)
    rwa [hdist_coordEmb_loc, hdist_coordEmb_loc] at h1
  have hWw : Real.cosh ‖Ŵ‖ = Real.cosh ‖w‖ * Real.cosh (hdist v W) := by
    have h := key W
    rw [hW0, Real.cosh_zero, mul_one] at h
    exact h
  have hWv : Real.cosh ‖Ŵ‖ * Real.cosh (hdist v W) = Real.cosh ‖w‖ := by
    have h := key v
    rw [hv0, Real.cosh_zero, mul_one, hsymk] at h
    exact h
  have hb2 : Real.cosh (hdist v W) * Real.cosh (hdist v W) = 1 := by
    have ha : Real.cosh ‖w‖ ≠ 0 := (Real.cosh_pos ‖w‖).ne'
    refine mul_left_cancel₀ ha ?_
    show Real.cosh ‖w‖ * (Real.cosh (hdist v W) * Real.cosh (hdist v W))
      = Real.cosh ‖w‖ * 1
    rw [mul_one, ← mul_assoc]
    rw [← hWw, hWv]
  have hb : Real.cosh (hdist v W) = 1 := by
    have hb1 : 1 ≤ Real.cosh (hdist v W) := Real.one_le_cosh _
    nlinarith [hb2, hb1]
  have hnonneg : 0 ≤ hdist v W := by
    have h1 := hpos (coordEmb k m v) (coordEmb k m W)
    rwa [hdist_coordEmb_loc] at h1
  have h0 : hdist v W = 0 :=
    Real.cosh_injOn hnonneg (Set.mem_Ici.mpr le_rfl) (by rw [hb, Real.cosh_zero])
  have hWv' : W = v := by
    have h1 : hdist (coordEmb k m v) (coordEmb k m W) = 0 := by rwa [hdist_coordEmb_loc]
    exact (coordEmb_injective_loc k m ((hzero _ _).mp h1)).symm
  refine ⟨hWv', ?_⟩
  have hc : Real.cosh ‖Ŵ‖ = Real.cosh ‖w‖ := by rw [hWw, hb, mul_one]
  exact Real.cosh_injOn (Set.mem_Ici.mpr (norm_nonneg Ŵ)) (Set.mem_Ici.mpr (norm_nonneg w)) hc

theorem stab_normal_inner (k m : ℕ) (hA : Submission.Mostow.POActionProp (k + m))
    (hI : Submission.Mostow.HypIsometryProp (k + m))
    (g' : LeanEval.Geometry.MostowRigidity.PO (k + m) 1)
    (hg' : ∀ v : Submission.Mostow.E k,
      g' • Submission.Mostow.coordEmb k m v = Submission.Mostow.coordEmb k m v) :
    (∀ w w' : Submission.Mostow.E m,
        inner ℝ (Submission.Mostow.fermiInv k m (g' • Submission.Mostow.fermi k m 0 w)).2
          (Submission.Mostow.fermiInv k m (g' • Submission.Mostow.fermi k m 0 w')).2
        = inner ℝ w w') ∧
      Function.Surjective (fun w : Submission.Mostow.E m =>
        (Submission.Mostow.fermiInv k m (g' • Submission.Mostow.fermi k m 0 w)).2) := by
  have hiso := hI.2.2.2.2.2.2.1
  have hone := hA.2.2.2.1
  have hmul := hA.2.2.2.2.1
  have h0k : hdist (0 : E k) (0 : E k) = 0 := by
    rw [← hdist_coordEmb_loc k m (0 : E k) (0 : E k)]
    exact (hI.2.2.1 (coordEmb k m (0 : E k)) (coordEmb k m (0 : E k))).mpr rfl
  constructor
  · intro w w'
    have hw := stab_fermi_foot_loc hI g' hg' (0 : E k) w
    have hw' := stab_fermi_foot_loc hI g' hg' (0 : E k) w'
    have e1 : fermi k m 0 (fermiInv k m (g' • fermi k m 0 w)).2 = g' • fermi k m 0 w := by
      have h := (Work.Mostow.fermi_inv k m).2.1 (g' • fermi k m 0 w)
      rw [hw.1] at h
      exact h
    have e2 : fermi k m 0 (fermiInv k m (g' • fermi k m 0 w')).2 = g' • fermi k m 0 w' := by
      have h := (Work.Mostow.fermi_inv k m).2.1 (g' • fermi k m 0 w')
      rw [hw'.1] at h
      exact h
    have hdis : hdist (fermi k m 0 (fermiInv k m (g' • fermi k m 0 w)).2)
        (fermi k m 0 (fermiInv k m (g' • fermi k m 0 w')).2)
        = hdist (fermi k m 0 w) (fermi k m 0 w') := by
      have hbase := hiso g' (fermi k m 0 w) (fermi k m 0 w')
      rw [← e1, ← e2] at hbase
      exact hbase
    have hcosh := congrArg Real.cosh hdis
    rw [Work.Mostow.cosh_hdist_fermi, Work.Mostow.cosh_hdist_fermi] at hcosh
    rw [h0k, Real.cosh_zero, mul_one, hw.2, hw'.2] at hcosh
    have hkey : sinhc ‖w‖ * sinhc ‖w'‖ *
        inner ℝ (fermiInv k m (g' • fermi k m 0 w)).2
          (fermiInv k m (g' • fermi k m 0 w')).2
        = sinhc ‖w‖ * sinhc ‖w'‖ * inner ℝ w w' := by
      linarith [hcosh]
    exact mul_left_cancel₀ (mul_ne_zero (sinhc_pos_loc _).ne' (sinhc_pos_loc _).ne') hkey
  · intro y
    have hleft : ∀ u : E (k + m), g'⁻¹ • (g' • u) = u := by
      intro u
      have h := hmul g'⁻¹ g' u
      rw [inv_mul_cancel, hone u] at h
      exact h.symm
    have hright : ∀ u : E (k + m), g' • (g'⁻¹ • u) = u := by
      intro u
      have h := hmul g' g'⁻¹ u
      rw [mul_inv_cancel, hone u] at h
      exact h.symm
    have hg'' : ∀ v : E k, g'⁻¹ • coordEmb k m v = coordEmb k m v := by
      intro v
      have h := hleft (coordEmb k m v)
      rw [hg' v] at h
      exact h
    have hfy := stab_fermi_foot_loc hI g'⁻¹ hg'' (0 : E k) y
    refine ⟨(fermiInv k m (g'⁻¹ • fermi k m 0 y)).2, ?_⟩
    have hpt : fermi k m 0 (fermiInv k m (g'⁻¹ • fermi k m 0 y)).2
        = g'⁻¹ • fermi k m 0 y := by
      have h := (Work.Mostow.fermi_inv k m).2.1 (g'⁻¹ • fermi k m 0 y)
      rw [hfy.1] at h
      exact h
    have hkey : g' • fermi k m 0 (fermiInv k m (g'⁻¹ • fermi k m 0 y)).2
        = fermi k m 0 y := by
      rw [hpt]
      exact hright (fermi k m 0 y)
    change (fermiInv k m (g' • fermi k m 0 (fermiInv k m (g'⁻¹ • fermi k m 0 y)).2)).2 = y
    rw [hkey]
    exact congrArg Prod.snd ((Work.Mostow.fermi_inv k m).1 (0 : E k) y)

end Work.Mostow
