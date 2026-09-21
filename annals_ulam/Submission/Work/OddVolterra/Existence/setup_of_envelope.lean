import Mathlib
import Submission.Work.OddVolterra.RowIdentity.Basic
import Submission.Work.OddEnvelope.Main
import Submission.Work.OddCurve.const_eq_refConst_of_smallSlope
import Submission.Work.OddVolterra.Existence.Qy_Qx_pos_of_envelope
import Submission.Work.OddVolterra.Existence.envelopeProfile_eq_semicircle_Icc_profileX1

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff
open Commons.Geometry.Ulam (profileX semicircle)

noncomputable section

/-
GUIDE (context for the prover, not part of the claim).

`Work.OddVolterra.RowIdentity.Setup` (see `Submission/Work/OddVolterra/RowIdentity/Basic.lean`)
collects the hypotheses under which the two row identities `odd_rowF` / `odd_rowH` were proved.
The content here: the *envelope* chapter (`Work.OddEnvelope`) plus the `1/100`-closeness of
`(x,y)` to `profileX` supply all of them, with `a = c = s` (so that `Icc a c = {s}`).

Hints (all the needed material is sorry-free in this workspace):
* `f := envelopeProfile h x y`; the smoothness field is `Work.OddEnvelope.contDiffOn_envelopeProfile`
  (or the corresponding field of `Work.OddEnvelope.envelopeProfile_spec`), the root conditions are
  `Work.OddEnvelope.envelopeProfile_root_right` / `_root_left`, and `hfb` (profile = semicircle on
  `Icc (-profileX 1) (profileX 1)`) follows from
  `Work.OddCurve.envelopeProfile_eq_semicircle_Icc_tStar` with `a = profileX 1 ≤ tStar`.
* `hxdec`/`hydec` are immediate from `H.x_deriv_neg`/`H.y_deriv_neg`; `hxb`/`hyb` from
  `H.x_tail`/`H.y_tail` (`1 - tau ≤ 1`); `hord` is `le_of_lt` of `profileX 1 > 0`.
* Fields ranging over `Icc a 1` (namely `hxle`, `hyle`, `hint`, `hmid`) must be proved on the whole
  of `[s,1]`, not just at `s`: use that `x`, `y` are strictly decreasing on `(0,∞)` (this follows
  from `H.x_deriv_neg`/`H.y_deriv_neg`), together with `x_tail`/`y_tail` at `σ = 1`.
* For `hKden` use `Work.OddEnvelope.envelopeProfile_sub_sq_pos` (with
  `Work.OddEnvelope.concaveOn_envelopeProfile`) on the section of slope `s`, applied at `y σ`
  respectively `-(x σ)` for `σ ∈ [s,1]` (these points lie in `(-(x s), y s)` since `x`, `y` are
  strictly decreasing), plus `Work.OddVolterra.sub_mul_hquot` to factor `psi` into
  `(σ-u)·(t+hquot)·(line σ t + line u t)`; at the diagonal `σ = u` use
  `Work.OddVolterra.hquot_self` and `H.mono_y`.
* For `hmid` the middle interval already sits inside the section of slope `s`, so
  `envelopeProfile_sub_sq_pos` again applies (the profile is the semicircle on
  `Icc (-profileX 1) (profileX 1)`, see `hfb`), or alternatively `1 - t^2 - (s t + h s)^2` is
  concave in `t` with value `> 0` at `t = ±profileX 1`.
* For `hint` (`y σ < 1` and `x σ < 1` on `[s,1]`): if `y σ ≥ 1` then `envelopeProfile h x y (y σ)=0`
  (it is `0` outside `(-1,1)`), so the root condition gives `h σ = -σ · y σ ≤ -σ`; since `h = 0`
  off `[1-2τ, 1-τ] = [0.8, 0.9]` and `|h|` is bounded by `≈ 0.05` there (integrate `mono_y` and
  `mono_x` across the window, using `hclose` and `h = 0` at the right end `9/10`), this is a
  contradiction.  Similarly for `x σ ≥ 1`.
-/
set_option linter.unusedVariables false in
theorem setup_of_envelope (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hclose : ∀ s : ℝ, 0 < s →
      |x s - Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv x s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv x) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 100 ∧
      |y s - Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv y s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv y) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 100)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ S : Work.OddVolterra.RowIdentity.Setup,
      S.n = n ∧ S.a = s ∧ S.c = s ∧ S.h = h ∧ S.x = x ∧ S.y = y ∧
      S.f = Work.OddEnvelope.envelopeProfile h x y := by
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have hxA : AntitoneOn x (Set.Ioi 0) := H.toChordCurve_x.strictAntiOn.antitoneOn
  have hyA : AntitoneOn y (Set.Ioi 0) := H.toChordCurve_y.strictAntiOn.antitoneOn
  have hxlt : x s < 1 := H.toChordCurve_x.lt_one hs
  have hylt : y s < 1 := H.toChordCurve_y.lt_one hs
  have hone : (1 : ℝ) ∈ Set.Ioi 0 := by norm_num
  have hx1 : x 1 = profileX 1 := H.x_tail 1 (by norm_num [Work.OddEnvelope.tau])
  have hy1 : y 1 = profileX 1 := H.y_tail 1 (by norm_num [Work.OddEnvelope.tau])
  have hpx : 0 < profileX 1 := Commons.Geometry.Ulam.profileX_pos 1 (by norm_num)
  have hfb : ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
      Work.OddEnvelope.envelopeProfile h x y t = semicircle t :=
    envelopeProfile_eq_semicircle_Icc_profileX1 H
  have hK : ∀ a b : ℝ, s ≤ a → a ≤ b → b ≤ 1 →
      0 < Work.OddVolterra.RowIdentity.Qy h y a b ∧
      0 < Work.OddVolterra.RowIdentity.Qx h x a b :=
    fun a b ha hab _ =>
      Qy_Qx_pos_of_envelope hh1 H a b (lt_of_lt_of_le hs ha) hab
  let S : Work.OddVolterra.RowIdentity.Setup :=
      { n := n, hn := hn, a := s, c := s, ha := hs, hac := le_rfl, hc1 := hs1,
        h := h, x := x, y := y, f := Work.OddEnvelope.envelopeProfile h x y,
        hh := hh, hx := H.smooth_x, hy := H.smooth_y,
        hf := Work.OddEnvelope.envelopeProfile_contDiffOn H,
        hxy := fun u hu => ⟨Work.OddEnvelope.envelopeProfile_root_right H hu.1,
          Work.OddEnvelope.envelopeProfile_root_left H hu.1⟩,
        hxdec := fun σ hσ => le_of_lt (H.x_deriv_neg σ (lt_trans hs hσ.1)),
        hydec := fun σ hσ => le_of_lt (H.y_deriv_neg σ (lt_trans hs hσ.1)),
        hxb := hx1, hyb := hy1, hfb := hfb,
        hxle := fun u hu => hxA (lt_of_lt_of_le hs hu.1) hone hu.2,
        hyle := fun u hu => hyA (lt_of_lt_of_le hs hu.1) hone hu.2,
        hord := by rw [hx1, hy1]; linarith,
        hint := by
          intro u hu
          have hu0 : 0 < u := lt_of_lt_of_le hs hu.1
          have h1 : x 1 ≤ x u := hxA hu0 hone hu.2
          have h2 : x u ≤ x s := hxA hs hu0 hu.1
          have h3 : y 1 ≤ y u := hyA hu0 hone hu.2
          have h4 : y u ≤ y s := hyA hs hu0 hu.1
          rw [hx1] at h1
          rw [hy1] at h3
          exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩,
        hKden := hK,
        hmid := by
          intro u hu t ht
          have hu0 : 0 < u := lt_of_lt_of_le hs hu.1
          have h1 : x 1 ≤ x u := hxA hu0 hone hu.2
          have h3 : y 1 ≤ y u := hyA hu0 hone hu.2
          rw [hx1] at h1
          rw [hy1] at h3
          have ht1 : -(x u) < t := by linarith [ht.1]
          have ht2 : t < y u := by linarith [ht.2]
          have hpos := Work.OddEnvelope.envelopeProfile_sub_sq_pos H
            (Work.OddEnvelope.concaveOn_envelopeProfile H) hu0 t ⟨ht1, ht2⟩
          have hfs : Work.OddEnvelope.envelopeProfile h x y t = semicircle t :=
            hfb t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
          have hgoal : Work.OddVolterra.psi h semicircle u t
              = (Work.OddEnvelope.envelopeProfile h x y t) ^ 2 - (u * t + h u) ^ 2 := by
            rw [Work.OddVolterra.psi, Work.OddVolterra.line, ← hfs]
          rw [hgoal]
          exact hpos }
  exact ⟨S, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end


end Work.OddVolterra.Existence
