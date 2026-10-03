import Mathlib
import Submission.Work.Horn.flower_defs

/-!
# Invariance of the Leau–Fatou petals (`Flower` vocabulary)

The chart `w = c / z ^ q` (`c = cc q a = -1/(q a)`) conjugates the parabolic germ
`f z = z + a z^{q+1} + o(z^{q+1})` to the translation `w ↦ w + 1 + o(1)`; the `j`-th attracting
petal `petal q a M j` is the `j`-th branch of the `q`-th root of the disc
`DM q a M = {s | M * ‖s‖² < Re (c * conj s)} = {Re (c/s) > M}`.

`petal_mapsTo` is the invariance of the petals: if `f` maps its chart coordinate forward by at
least `3/4` in real part (`Bounds.hchart`) and the petal scale `M` is large enough that
`‖cc‖/M < ρ ^ q` (so that the petals sit in the disc where the quantitative bounds hold), then
`f` maps each petal into itself, up to the fixed point `0`.

The one analytic input is the principal-branch identity `log (u^q) = q log u` for
`|arg u| * q < π`, which is a hypothesis of the statement (`hlogpow`), exactly as requested.
-/

namespace Work.Horn

open scoped Topology

noncomputable section

/-- `s ∈ DM q a M ↔ M < Re (cc q a / s)` for `s ≠ 0`: the root disc is the set where the chart
value has real part bigger than `M`. -/
theorem mem_DM_iff {q : ℕ} {a : ℂ} {M : ℝ} {s : ℂ} (hs : s ≠ 0) :
    s ∈ Flower.DM q a M ↔ M < (Flower.cc q a / s).re := by
  have hns : (0 : ℝ) < Complex.normSq s := Complex.normSq_pos.mpr hs
  have hdiv : (Flower.cc q a / s).re * Complex.normSq s = (Flower.cc q a * star s).re := by
    rw [Complex.div_re, Complex.mul_re]
    simp only [Complex.star_def, Complex.conj_re, Complex.conj_im]
    field_simp
    ring
  have hmem : (s ∈ Flower.DM q a M) ↔
      M * Complex.normSq s < (Flower.cc q a * star s).re := Iff.rfl
  rw [hmem, ← hdiv, mul_comm M (Complex.normSq s),
    mul_comm ((Flower.cc q a / s).re) (Complex.normSq s)]
  exact mul_lt_mul_iff_right₀ hns

theorem petal_mapsTo {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hb : Work.Horn.Flower.Bounds f D q a ρ) (hM : 0 < M)
    (hRM : ‖Work.Horn.Flower.cc q a‖ / M < ρ ^ q)
    (hgeo : Work.Horn.Flower.PetalFacts q a M)
    (hlogpow : ∀ u : ℂ, u ≠ 0 → |u.arg| * (q : ℝ) < Real.pi →
      Complex.log (u ^ q) = (q : ℂ) * Complex.log u) :
    ∀ j : Fin q, Set.MapsTo f (Work.Horn.Flower.petal q a M j)
      (Work.Horn.Flower.petal q a M j ∪ {0}) := by
  intro j z hz
  obtain ⟨hzpos, hzqDM, hroot⟩ := (hgeo.mem_petal_iff j z).mp hz
  have hq : 1 ≤ q := hb.hq
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcc : Flower.cc q a ≠ 0 := hgeo.cc_ne_zero
  have hznorm := hgeo.petal_norm_pow_lt j z hz
  have hzlt : ‖z‖ < ρ :=
    lt_of_pow_lt_pow_left₀ q (le_of_lt hb.hρ) (lt_trans hznorm hRM)
  have hzball : z ∈ Metric.ball (0 : ℂ) ρ := by
    simp only [Metric.mem_ball, dist_zero_right]; exact hzlt
  have hzq_ne : z ^ q ≠ 0 := pow_ne_zero q (norm_pos_iff.mp hzpos)
  set u : ℂ := 1 + z ^ q * Flower.Hfun f q a z with hu
  have hune : u ≠ 0 := by rw [hu]; exact hb.hunit_ne z hzball
  have hure : 0 < (u ^ q).re := by rw [hu]; exact hb.hunit_re z hzball
  have huarg : |u.arg| * (q : ℝ) < Real.pi := by rw [hu]; exact hb.hunit_arg z hzball
  have hfz : f z = z * u := by rw [hu]; exact hb.hf_eq z
  have hz_ne : z ≠ 0 := norm_pos_iff.mp hzpos
  have hfz_ne : f z ≠ 0 := by rw [hfz]; exact mul_ne_zero hz_ne hune
  have hfzq_ne : (f z) ^ q ≠ 0 := pow_ne_zero q hfz_ne
  have hpos_fz : 0 < ‖f z‖ := norm_pos_iff.mpr hfz_ne
  have hchartQ_ne : Flower.chartQ q a z ≠ 0 := by
    rw [Flower.chartQ]; exact div_ne_zero hcc hzq_ne
  have hwre : M < (Flower.chartQ q a z).re := by
    have h := (mem_DM_iff (q := q) (a := a) (M := M) (s := z ^ q) hzq_ne).mp hzqDM
    simpa [Flower.chartQ] using h
  have hchart := hb.hchart z hzpos hzlt
  have hw're : M < (Flower.chartQ q a (f z)).re := by
    have h1 : |(Flower.chartQ q a (f z) - Flower.chartQ q a z - 1).re| ≤ 1 / 4 :=
      le_trans (Complex.abs_re_le_norm _) hchart
    have h2 : -1 / 4 ≤ (Flower.chartQ q a (f z)).re - (Flower.chartQ q a z).re - 1 := by
      have h3 := (abs_le.mp h1).1
      simp only [Complex.sub_re, Complex.one_re] at h3
      linarith
    linarith
  have hfzqDM : (f z) ^ q ∈ Flower.DM q a M := by
    refine (mem_DM_iff (q := q) (a := a) (M := M) (s := (f z) ^ q) hfzq_ne).mpr ?_
    simpa [Flower.chartQ] using hw're
  have hxy : (f z) ^ q / Flower.cc q a = (z ^ q / Flower.cc q a) * u ^ q := by
    rw [hfz, mul_pow, div_mul_eq_mul_div]
  have hx_ne : z ^ q / Flower.cc q a ≠ 0 := div_ne_zero hzq_ne hcc
  have hy_ne : u ^ q ≠ 0 := pow_ne_zero q hune
  have hxre : 0 < (z ^ q / Flower.cc q a).re := by
    have heq : z ^ q / Flower.cc q a = (Flower.chartQ q a z)⁻¹ := by
      rw [Flower.chartQ, inv_div]
    rw [heq, Complex.inv_re]
    exact div_pos (lt_trans hM hwre) (Complex.normSq_pos.mpr hchartQ_ne)
  have hargIoc : (z ^ q / Flower.cc q a).arg + (u ^ q).arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    have hx := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hxre))
    have hy := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hure))
    constructor <;> linarith [Real.pi_pos, hx.1, hx.2, hy.1, hy.2]
  have hlogmul := Complex.log_mul hx_ne hy_ne hargIoc
  have hkey : Complex.exp (Complex.log ((f z) ^ q / Flower.cc q a) / (q : ℂ))
      = Complex.exp (Complex.log (z ^ q / Flower.cc q a) / (q : ℂ)) * u := by
    have hlogy : Complex.log (u ^ q) = (q : ℂ) * Complex.log u := hlogpow u hune huarg
    rw [hxy, hlogmul, hlogy, add_div, mul_div_cancel_left₀ _ hq0]
    rw [Complex.exp_add, Complex.exp_log hune]
  have hroot_unf : Flower.zeta q a j
      * Complex.exp (Complex.log (z ^ q / Flower.cc q a) / (q : ℂ)) = z := by
    simpa [Flower.rootFun] using hroot
  have hfinal : Flower.rootFun q a j ((f z) ^ q) = f z := by
    rw [Flower.rootFun, hkey, ← mul_assoc, hroot_unf, hfz]
  exact Or.inl ((hgeo.mem_petal_iff j (f z)).mpr ⟨hpos_fz, hfzqDM, hfinal⟩)

end

end Work.Horn
