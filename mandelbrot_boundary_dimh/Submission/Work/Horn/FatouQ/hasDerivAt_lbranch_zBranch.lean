import Mathlib
import Submission.Work.Horn.fatouQ_defs
import Submission.Work.Horn.FatouQ.zBranch_contDiff
import Submission.Work.Horn.FatouQ.chartdict

namespace Work.Horn.FatouQ

open Work.Horn.Flower Filter
open scoped Topology

/-!
# Differentiability of the branch of the logarithm along the inverse chart

On the half plane `{Re w > M}` the inverse chart `zBranch q a j` is a genuine inverse of `chartQ`,
so that `(zBranch q a j w') ^ q / cc q a = (w')⁻¹` there.  Hence

  `Lbranch q a (zBranch q a j w') = (log ((w')⁻¹) + log (cc q a)) / q`,

an explicit elementary function of `w'` whose derivative is `-1/(q * w)`.
-/

/-- Pointwise form of the chart identity: for `Re w > M` the inverse chart lies on the `j`-th
petal and `(zBranch q a j w)^q / cc q a = w⁻¹`. -/
theorem zBranch_pow_div_cc_eq_inv {q : ℕ} {a : ℂ} {M : ℝ} (hgeo : PetalFacts q a M)
    (hM : 0 < M)
    (j : Fin q) (hpetal : ∀ w : ℂ, M < w.re → zBranch q a j w ∈ petal q a M j)
    (hchart : ∀ w : ℂ, M < w.re → chartQ q a (zBranch q a j w) = w)
    {w : ℂ} (hw : M < w.re) :
    (zBranch q a j w) ^ q / cc q a = w⁻¹ := by
  have hcc : cc q a ≠ 0 := hgeo.cc_ne_zero
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw; linarith
  have hzmem : zBranch q a j w ∈ petal q a M j := hpetal w hw
  have hzpos : 0 < ‖zBranch q a j w‖ := ((hgeo.mem_petal_iff j _).mp hzmem).1
  have hz0 : zBranch q a j w ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hzpos)
  have hzq0 : (zBranch q a j w) ^ q ≠ 0 := pow_ne_zero q hz0
  have hchart' : cc q a / (zBranch q a j w) ^ q = w := hchart w hw
  have h1 : cc q a = w * (zBranch q a j w) ^ q := (div_eq_iff hzq0).mp hchart'
  have h2 : (zBranch q a j w) ^ q = cc q a / w :=
    (eq_div_iff hw0).mpr (by rw [mul_comm]; exact h1.symm)
  rw [h2]
  field_simp

/-- **The derivative of `Lbranch` along the inverse chart.**  Since on the half plane `{Re w > M}`
the composite is the elementary function `w' ↦ (log (w'⁻¹) + log (cc q a)) / q`, its derivative
at `w` is `-1/(q * w)`. -/
theorem hasDerivAt_lbranch_zBranch {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hd : Work.Horn.FatouQ.PetalDatum f D q a ρ M) (j : Fin q)
    (hpetal : ∀ w : ℂ, M < w.re → Work.Horn.FatouQ.zBranch q a j w ∈ Work.Horn.Flower.petal q a M j)
    (hchart : ∀ w : ℂ, M < w.re → Work.Horn.Flower.chartQ q a (Work.Horn.FatouQ.zBranch q a j w) = w)
    {w : ℂ} (hw : M < w.re) :
    HasDerivAt (fun w' : ℂ => Work.Horn.FatouQ.Lbranch q a (Work.Horn.FatouQ.zBranch q a j w'))
      (-1 / ((q : ℂ) * w)) w := by
  have hM : 0 < M := hd.hM
  have hwpos : 0 < w.re := lt_trans hM hw
  have hw0 : w ≠ 0 := fun h => by rw [h] at hwpos; simp at hwpos
  -- the composite function is, near `w`, an explicit elementary function
  have heq : (fun w' : ℂ => Lbranch q a (zBranch q a j w')) =ᶠ[𝓝 w]
      (fun w' : ℂ => (Complex.log (w'⁻¹) + Complex.log (cc q a)) / (q : ℂ)) := by
    have hS : IsOpen {w' : ℂ | M < w'.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hS.mem_nhds hw] with w' hw'
    simp only [Lbranch]
    rw [zBranch_pow_div_cc_eq_inv hd.hgeo hM j hpetal hchart hw']
  -- derivative of the elementary function
  have hre : 0 < (w⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hwpos (Complex.normSq_pos.mpr hw0)
  have hslit : w⁻¹ ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hre)
  have hinv : HasDerivAt (fun w' : ℂ => (w')⁻¹) (-(w ^ 2)⁻¹) w := hasDerivAt_inv hw0
  have hlog : HasDerivAt (fun w' : ℂ => Complex.log (w'⁻¹)) ((-(w ^ 2)⁻¹) / w⁻¹) w :=
    hinv.clog hslit
  have hlog' : HasDerivAt (fun w' : ℂ => Complex.log (w'⁻¹)) (-w⁻¹) w := by
    convert hlog using 1
    field_simp
  have hderiv : HasDerivAt (fun w' : ℂ => (Complex.log (w'⁻¹) + Complex.log (cc q a)) / (q : ℂ))
      (-1 / ((q : ℂ) * w)) w := by
    have h2 := hlog'.add_const (Complex.log (cc q a))
    have h3 := h2.div_const ((q : ℂ))
    convert h3 using 1
    field_simp
  exact hderiv.congr_of_eventuallyEq heq

end Work.Horn.FatouQ
