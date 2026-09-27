import Mathlib
import Submission.Work.Mostow.cosh_hdist_fermi
import Submission.Work.Mostow.fermi_inv

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-! ### Elementary hyperbolic facts on `E k`

`hI : HypIsometryProp (k + m)` only gives these for the ambient space `E (k+m)`; the foot of a
Fermi chart lives in `E k`, so we record the two or three facts we need there. -/

private lemma tpart_sq_k (k : ℕ) (u : E k) : tpart u ^ 2 = 1 + ‖u‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

private lemma hdist_self_k (k : ℕ) (u : E k) : hdist u u = 0 := by
  rw [hdist]
  have h : tpart u * tpart u - inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq]
    have := tpart_sq_k k u
    linarith
  rw [h, Real.arcosh_zero]

private lemma hdist_comm_k (k : ℕ) (u v : E k) : hdist u v = hdist v u := by
  rw [hdist, hdist]
  congr 1
  rw [real_inner_comm, mul_comm (tpart u) (tpart v)]

private lemma one_le_cc_k (k : ℕ) (u v : E k) : 1 ≤ tpart u * tpart v - inner ℝ u v := by
  have h1 : inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
  have h2 : 1 + ‖u‖ * ‖v‖ ≤ tpart u * tpart v := by
    have ha : tpart u * tpart v = Real.sqrt ((1 + ‖u‖ ^ 2) * (1 + ‖v‖ ^ 2)) := by
      rw [tpart, tpart, Real.sqrt_mul (by nlinarith [sq_nonneg ‖u‖])]
    rw [ha]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  linarith

private lemma cosh_hdist_k (k : ℕ) (u v : E k) :
    Real.cosh (hdist u v) = tpart u * tpart v - inner ℝ u v := by
  rw [hdist]
  exact Real.cosh_arcosh (one_le_cc_k k u v)

/-- `tpart p * tpart q - ⟪p,q⟫ = 1` forces `p = q` (equality case of Cauchy–Schwarz). -/
private lemma cc_eq_one_imp_eq (k : ℕ) (p q : E k)
    (h : tpart p * tpart q - inner ℝ p q = 1) : p = q := by
  have hsq : (tpart p * tpart q) ^ 2 = (1 + inner ℝ p q) ^ 2 := by
    have h1 : tpart p * tpart q = 1 + inner ℝ p q := by linarith
    rw [h1]
  have hp := tpart_sq_k k p
  have hq := tpart_sq_k k q
  have hcs : (inner ℝ p q) ^ 2 ≤ (‖p‖ * ‖q‖) ^ 2 := by
    have h0 : |inner ℝ p q| ≤ ‖p‖ * ‖q‖ := abs_real_inner_le_norm p q
    have h0' : |inner ℝ p q| ^ 2 ≤ (‖p‖ * ‖q‖) ^ 2 := by
      have := mul_self_le_mul_self (abs_nonneg _) h0
      simpa [sq] using this
    rwa [sq_abs] at h0'
  have hns : ‖p - q‖ ^ 2 = ‖p‖ ^ 2 - 2 * inner ℝ p q + ‖q‖ ^ 2 := norm_sub_sq_real p q
  have hkey : ‖p - q‖ ^ 2 ≤ 0 := by
    rw [hns]
    nlinarith [hsq, hp, hq, hcs]
  have hzero : ‖p - q‖ ^ 2 = 0 := le_antisymm hkey (sq_nonneg _)
  have hnorm : ‖p - q‖ = 0 := by nlinarith [hzero, norm_nonneg (p - q)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- `coordEmb k m v` is the Fermi chart point with foot `v` and zero normal vector. -/
private lemma coordEmb_eq_fermi_zero (k m : ℕ) (v : E k) :
    coordEmb k m v = fermi k m v 0 := by
  simp [coordEmb, fermi, sinhc]

/-! A hyperbolic isometry `g'` of `ℍ^{k+m}` which fixes the standard totally geodesic stratum
`stdTG k m = range (coordEmb k m)` **pointwise** preserves Fermi coordinates on the foot: the first
component of `fermiInv (g' • fermi k m v w)` is `v` (the projection to the stratum), and the normal
vector has the same norm (the distance to the stratum is preserved).

Guidance.  Put `u := fermi k m v w`, `y := g' • u`, `(p, ŵ) := fermiInv k m y`, so `y = fermi k m p ŵ`
(`Work.Mostow.fermi_inv`).  For every `v' : E k`,
  `hdist y (coordEmb k m v') = hdist (g' • u) (g' • coordEmb k m v')`   (as `hg' v'`)
   `= hdist u (coordEmb k m v')`   (isometry clause of `HypIsometryProp (k+m)`).
Take `cosh` of both sides and evaluate with `Work.Mostow.cosh_hdist_fermi` at `w' = 0`
(`coordEmb k m v' = fermi k m v' 0`, `sinhc 0 = 1`, `inner _ 0 = 0`, `Real.cosh 0 = 1`):
  `cosh (hdist y (coordEmb k m v')) = cosh ‖ŵ‖ * cosh (hdist p v')`
  `cosh (hdist u (coordEmb k m v')) = cosh ‖w‖ * cosh (hdist v v')`.
Specialise at `v' = p` and at `v' = v`, put `a := Real.cosh ‖w‖ > 0` and
`b := Real.cosh (hdist v p) ≥ 1`; symmetry of `hdist` gives `cosh ‖ŵ‖ = a * b` and
`cosh ‖ŵ‖ * b = a`, hence `a * b ^ 2 = a`, `b = 1`, `hdist v p = 0`, and `p = v` by clause 3 of
`HypIsometryProp (k+m)`.  Then `cosh ‖ŵ‖ = cosh ‖w‖` and `Real.cosh_injOn` (clause 1 gives
`0 ≤ ‖ŵ‖` and `0 ≤ ‖w‖` — note `Real.norm_nonneg`) give `‖ŵ‖ = ‖w‖`. -/
theorem stab_fermi_foot (k m : ℕ) (hA : Submission.Mostow.POActionProp (k + m))
    (hI : Submission.Mostow.HypIsometryProp (k + m))
    (g' : LeanEval.Geometry.MostowRigidity.PO (k + m) 1)
    (hg' : ∀ v : Submission.Mostow.E k,
      g' • Submission.Mostow.coordEmb k m v = Submission.Mostow.coordEmb k m v)
    (v : Submission.Mostow.E k) (w : Submission.Mostow.E m) :
    (Submission.Mostow.fermiInv k m (g' • Submission.Mostow.fermi k m v w)).1 = v ∧
      ‖(Submission.Mostow.fermiInv k m (g' • Submission.Mostow.fermi k m v w)).2‖ = ‖w‖ := by
  set y := g' • fermi k m v w with hy
  set p := (fermiInv k m y).1 with hp
  set W := (fermiInv k m y).2 with hW
  have hyf : fermi k m p W = y := by
    rw [hp, hW, hy]
    exact (fermi_inv k m).2.1 _
  -- The two `cosh`-expansions of `cosh (hdist (g'•u) (coordEmb v'))`.
  have hstep : ∀ v' : E k,
      Real.cosh (hdist y (coordEmb k m v')) =
        Real.cosh (hdist (fermi k m v w) (coordEmb k m v')) := by
    intro v'
    refine congrArg Real.cosh ?_
    have hy1 : hdist y (coordEmb k m v')
        = hdist (g' • fermi k m v w) (coordEmb k m v') := by rw [hy]
    have hy2 : hdist (g' • fermi k m v w) (coordEmb k m v')
        = hdist (g' • fermi k m v w) (g' • coordEmb k m v') :=
      congrArg (fun z => hdist (g' • fermi k m v w) z) (hg' v').symm
    have hiso : hdist (g' • fermi k m v w) (g' • coordEmb k m v')
        = hdist (fermi k m v w) (coordEmb k m v') :=
      hI.2.2.2.2.2.2.1 g' (fermi k m v w) (coordEmb k m v')
    exact hy1.trans (hy2.trans hiso)
  have hsl : ∀ v' : E k,
      Real.cosh (hdist (fermi k m v w) (coordEmb k m v')) =
        Real.cosh ‖w‖ * Real.cosh (hdist v v') := by
    intro v'
    rw [coordEmb_eq_fermi_zero]
    rw [cosh_hdist_fermi]
    simp [Real.cosh_zero, sinhc, inner_zero_right]
  have hsr : ∀ v' : E k,
      Real.cosh (hdist y (coordEmb k m v')) =
        Real.cosh ‖W‖ * Real.cosh (hdist p v') := by
    intro v'
    rw [← hyf]
    rw [coordEmb_eq_fermi_zero]
    rw [cosh_hdist_fermi]
    simp [Real.cosh_zero, sinhc, inner_zero_right]
  have hkey : ∀ v' : E k,
      Real.cosh ‖W‖ * Real.cosh (hdist p v') =
        Real.cosh ‖w‖ * Real.cosh (hdist v v') := by
    intro v'
    rw [← hsr v', hstep v', hsl v']
  have hpp : hdist p p = 0 := hdist_self_k k p
  have hvv : hdist v v = 0 := hdist_self_k k v
  have hpv : hdist p v = hdist v p := hdist_comm_k k p v
  have h1 : Real.cosh ‖W‖ = Real.cosh ‖w‖ * Real.cosh (hdist v p) := by
    have h := hkey p
    rw [hpp, Real.cosh_zero, mul_one] at h
    exact h
  have h2 : Real.cosh ‖W‖ * Real.cosh (hdist v p) = Real.cosh ‖w‖ := by
    have h := hkey v
    rw [hvv, Real.cosh_zero, mul_one, hpv] at h
    exact h
  have hb2 : Real.cosh (hdist v p) ^ 2 = 1 := by
    have ha : 0 < Real.cosh ‖w‖ := Real.cosh_pos _
    have step : Real.cosh ‖w‖ * Real.cosh (hdist v p) ^ 2 = Real.cosh ‖w‖ * 1 := by
      calc Real.cosh ‖w‖ * Real.cosh (hdist v p) ^ 2
          = (Real.cosh ‖w‖ * Real.cosh (hdist v p)) * Real.cosh (hdist v p) := by ring
        _ = Real.cosh ‖W‖ * Real.cosh (hdist v p) := by rw [← h1]
        _ = Real.cosh ‖w‖ := h2
        _ = Real.cosh ‖w‖ * 1 := by ring
    exact mul_left_cancel₀ ha.ne' step
  have hbge : 1 ≤ Real.cosh (hdist v p) := Real.one_le_cosh _
  have hb : Real.cosh (hdist v p) = 1 := by
    rcases sq_eq_one_iff.mp hb2 with h | h
    · exact h
    · rw [h] at hbge
      norm_num at hbge
  have hcc : tpart v * tpart p - inner ℝ v p = 1 := by
    have h := cosh_hdist_k k v p
    rw [hb] at h
    exact h.symm
  have hpv_eq : p = v := (cc_eq_one_imp_eq k v p hcc).symm
  have hnorm : ‖W‖ = ‖w‖ := by
    have hc : Real.cosh ‖W‖ = Real.cosh ‖w‖ := by rw [h1, hb, mul_one]
    exact Real.cosh_injOn (norm_nonneg W) (norm_nonneg w) hc
  exact ⟨hpv_eq, hnorm⟩

end Work.Mostow
