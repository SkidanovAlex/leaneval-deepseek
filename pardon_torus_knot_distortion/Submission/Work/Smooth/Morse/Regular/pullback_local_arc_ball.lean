import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.Morse.Regular.arc_data_snd
import Submission.Work.Smooth.Morse.Regular.strictMonoOn_or_strictAntiOn_of_deriv_ne_zero
import Submission.Work.Smooth.Morse.Regular.abs_sub_le_of_deriv_eq_zero

/-!
# A local arc of a regular level set, contained in a ball

At a regular point `p` of a `C¹` function `f : ℝ × ℝ → ℝ` the level set `{f = t}` is locally an
arc, and for a small enough radius `ε` the *whole* portion of the level set inside the ball
`Metric.ball p ε` is the image of a continuous injective parametrisation on `(-1,1)`; moreover the
parametrisation itself stays inside that ball.

This is the "ball" refinement of `Work.Smooth.Morse.Regular.pullback_local_arc`.  The point of the
extra condition is that the arc is parametrised *by the slice of the ball*: the set
`A = {x | |x - p.1| < ε ∧ |ψ x - p.2| < ε}` (where `x ↦ (x, ψ x)` parametrises the level curve,
`ψ` being the implicit function) is exactly the set of parameters whose point lies in the ball, and
it is an interval because the level curve, near a regular point, meets every ball in at most one
point on each side of `p`.  That interval is then reparametrised to `(-1,1)`.

## Main results

* `isInvertible_of_ne_zero` -- a nonzero continuous linear functional `ℝ →L[ℝ] ℝ` is invertible;
* `abs_sub_le_abs_sub_of_between` -- a point between `a` and `z` is at least as close to `a` as `z`;
* `starShaped_of_arc_data` -- for small `ε`, `{x | |x - a| < ε ∧ |ψ x - b| < ε}` is star shaped
  around `a` (the analytic heart: `ψ` is either strictly monotone near `a` or 1-Lipschitz there);
* `eq_Ioo_csInf_csSup` -- an open star shaped set is the open interval between its infimum and
  supremum;
* `ArcReparam` and its properties -- an explicit increasing homeomorphism from `(-1,1)` onto an
  interval `(lo, hi)` containing `a`, sending `0` to `a`;
* `local_arc_ball_snd`, `local_arc_ball_of_fderiv_ne_zero` -- the statement for an abstract `C¹`
  function, in the two cases (second partial invertible / total derivative nonzero);
* `pullback_local_arc_ball` -- the statement for the pull-back through the parametrised torus.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped Topology

namespace Work.Smooth.Morse.Regular

/-- A nonzero continuous linear functional `ℝ →L[ℝ] ℝ` is invertible: it is multiplication by the
nonzero real number `g 1`. -/
private theorem isInvertible_of_ne_zero {g : ℝ →L[ℝ] ℝ} (hg : g ≠ 0) : g.IsInvertible := by
  have hg_apply : ∀ x : ℝ, g x = x * g 1 := fun x => by
    simpa [smul_eq_mul] using map_smul g x (1 : ℝ)
  have hg1 : g 1 ≠ 0 := by
    intro h
    apply hg
    apply ContinuousLinearMap.ext
    intro x
    rw [hg_apply x, h, mul_zero]
    simp
  refine ContinuousLinearMap.IsInvertible.of_inverse (f := g)
    (g := ContinuousLinearMap.toSpanSingleton ℝ (g 1)⁻¹) ?_ ?_
  · apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    rw [hg_apply, mul_assoc, inv_mul_cancel₀ hg1, mul_one]
  · apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    rw [hg_apply, mul_assoc, mul_inv_cancel₀ hg1, mul_one]

/-- A point of `[min a z, max a z]` is at least as close to `a` as `z` is. -/
private theorem abs_sub_le_abs_sub_of_between {a z w : ℝ} (h1 : min a z ≤ w)
    (h2 : w ≤ max a z) : |w - a| ≤ |z - a| := by
  rcases le_total a z with h | h
  · rw [min_eq_left h] at h1
    rw [max_eq_right h] at h2
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · rw [min_eq_right h] at h1
    rw [max_eq_left h] at h2
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

/-- **The slice of a small ball around a regular level arc is star shaped.**  If `ψ` is `C¹` near
`a` (with derivative `deriv ψ`) and `ψ a = b`, then for all small enough `ε` the set
`{x | |x - a| < ε ∧ |ψ x - b| < ε}` is star shaped around `a`: a point between `a` and a point `z`
of the set is again in the set.

Indeed, if `deriv ψ a ≠ 0` then `ψ` is strictly monotone on a neighbourhood of `a` (continuity of
the derivative gives a neighbourhood on which the derivative has constant sign), while if
`deriv ψ a = 0` then `|ψ x - b| ≤ |x - a|` near `a`. -/
private theorem starShaped_of_arc_data {ψ : ℝ → ℝ} {a b ρ : ℝ} (hρ : 0 < ρ) (hψa : ψ a = b)
    (hd : ∀ x ∈ Ioo (a - ρ) (a + ρ), HasDerivAt ψ (deriv ψ x) x)
    (hdc : ContinuousOn (deriv ψ) (Ioo (a - ρ) (a + ρ))) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ z : ℝ,
      |z - a| < ε → |ψ z - b| < ε → ∀ w : ℝ, min a z ≤ w → w ≤ max a z →
        |ψ w - b| < ε := by
  have hmemAux : ∀ {d x : ℝ}, |x - a| < d → x ∈ Ioo (a - d) (a + d) := by
    intro d x hx
    obtain ⟨h1, h2⟩ := abs_lt.mp hx
    rw [mem_Ioo]
    exact ⟨by linarith, by linarith⟩
  by_cases h0 : deriv ψ a = 0
  · obtain ⟨δ, hδ0, hδρ, hbnd⟩ := abs_sub_le_of_deriv_eq_zero hρ hψa hd hdc h0
    refine ⟨δ, hδ0, hδρ, fun ε hε hεδ z hz hψz w hw1 hw2 => ?_⟩
    have hwa : |w - a| ≤ |z - a| := abs_sub_le_abs_sub_of_between hw1 hw2
    have hwδ : |w - a| < δ := lt_of_le_of_lt hwa (lt_of_lt_of_le hz hεδ)
    exact lt_of_le_of_lt (hbnd w (hmemAux hwδ)) (lt_of_le_of_lt hwa hz)
  · obtain ⟨δ, hδ0, hδρ, hmono⟩ :=
      strictMonoOn_or_strictAntiOn_of_deriv_ne_zero hρ hd hdc h0
    refine ⟨δ, hδ0, hδρ, fun ε hε hεδ z hz hψz w hw1 hw2 => ?_⟩
    have hzδ : z ∈ Ioo (a - δ) (a + δ) := hmemAux (lt_of_lt_of_le hz hεδ)
    have hwδ : w ∈ Ioo (a - δ) (a + δ) :=
      hmemAux (lt_of_le_of_lt (abs_sub_le_abs_sub_of_between hw1 hw2) (lt_of_lt_of_le hz hεδ))
    have haδ : a ∈ Ioo (a - δ) (a + δ) := hmemAux (by simpa using hδ0)
    rcases le_total a z with h | h
    · -- `a ≤ z`, so `w ∈ [a, z]`
      rw [min_eq_left h] at hw1
      rw [max_eq_right h] at hw2
      rcases hmono with hm | ha
      · have h1 : b ≤ ψ w := by simpa [hψa] using hm.monotoneOn haδ hwδ hw1
        have h2 : ψ w ≤ ψ z := hm.monotoneOn hwδ hzδ hw2
        have hwb : 0 ≤ ψ w - b := by linarith
        have hzb : 0 ≤ ψ z - b := by linarith
        rw [abs_of_nonneg hwb]
        have hz' : ψ z - b < ε := by simpa [abs_of_nonneg hzb] using hψz
        linarith
      · have h1 : ψ w ≤ b := by simpa [hψa] using ha.antitoneOn haδ hwδ hw1
        have h2 : ψ z ≤ ψ w := ha.antitoneOn hwδ hzδ hw2
        have hwb : ψ w - b ≤ 0 := by linarith
        have hzb : ψ z - b ≤ 0 := by linarith
        rw [abs_of_nonpos hwb]
        have hz' : -(ψ z - b) < ε := by simpa [abs_of_nonpos hzb] using hψz
        linarith
    · -- `z ≤ a`, so `w ∈ [z, a]`
      rw [min_eq_right h] at hw1
      rw [max_eq_left h] at hw2
      rcases hmono with hm | ha
      · have h1 : ψ w ≤ b := by simpa [hψa] using hm.monotoneOn hwδ haδ hw2
        have h2 : ψ z ≤ ψ w := hm.monotoneOn hzδ hwδ hw1
        have hwb : ψ w - b ≤ 0 := by linarith
        have hzb : ψ z - b ≤ 0 := by linarith
        rw [abs_of_nonpos hwb]
        have hz' : -(ψ z - b) < ε := by simpa [abs_of_nonpos hzb] using hψz
        linarith
      · have h1 : b ≤ ψ w := by simpa [hψa] using ha.antitoneOn hwδ haδ hw2
        have h2 : ψ w ≤ ψ z := ha.antitoneOn hzδ hwδ hw1
        have hwb : 0 ≤ ψ w - b := by linarith
        have hzb : 0 ≤ ψ z - b := by linarith
        rw [abs_of_nonneg hwb]
        have hz' : ψ z - b < ε := by simpa [abs_of_nonneg hzb] using hψz
        linarith

/-- An open set containing `a`, star shaped around `a` and contained in `Ioo (a - ε) (a + ε)` is
the open interval between its infimum and its supremum. -/
private theorem eq_Ioo_csInf_csSup {A : Set ℝ} {a ε : ℝ} (hAopen : IsOpen A) (ha : a ∈ A)
    (hsub : A ⊆ Ioo (a - ε) (a + ε))
    (hstar : ∀ z ∈ A, ∀ w : ℝ, min a z ≤ w → w ≤ max a z → w ∈ A) :
    A = Ioo (sInf A) (sSup A) := by
  have hne : A.Nonempty := ⟨a, ha⟩
  have hbdd_below : BddBelow A := ⟨a - ε, fun y hy => (hsub hy).1.le⟩
  have hbdd_above : BddAbove A := ⟨a + ε, fun y hy => (hsub hy).2.le⟩
  ext x
  constructor
  · intro hx
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hAopen.mem_nhds hx)
    have hlt : sInf A < x := by
      have hmem : x - r / 2 ∈ A := hball (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith)
      have := csInf_le hbdd_below hmem
      linarith
    have hgt : x < sSup A := by
      have hmem : x + r / 2 ∈ A := hball (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith)
      have := le_csSup hbdd_above hmem
      linarith
    exact ⟨hlt, hgt⟩
  · intro hx
    obtain ⟨z, hzA, hzx⟩ := exists_lt_of_csInf_lt hne hx.1
    obtain ⟨y, hyA, hxy⟩ := exists_lt_of_lt_csSup hne hx.2
    rcases le_total a x with h | h
    · have hay : a ≤ y := by
        by_contra hc
        rw [not_le] at hc
        linarith
      exact hstar y hyA x (by rw [min_eq_left hay]; exact h)
        (by rw [max_eq_right hay]; exact le_of_lt hxy)
    · have hza : z ≤ a := by
        by_contra hc
        rw [not_le] at hc
        linarith
      exact hstar z hzA x (by rw [min_eq_right hza]; exact le_of_lt hzx)
        (by rw [max_eq_left hza]; exact h)

/-- An explicit increasing homeomorphism from `(-1,1)` onto the open interval `(lo, hi)`, with
`0 ↦ a` (where `lo < a < hi`).  It is affine on each side of `0`. -/
private def ArcReparam (a lo hi s : ℝ) : ℝ :=
  a + (a - lo) * s + (hi + lo - 2 * a) * max s 0

private theorem ArcReparam_continuous (a lo hi : ℝ) : Continuous (ArcReparam a lo hi) := by
  rw [show ArcReparam a lo hi = fun s : ℝ => a + (a - lo) * s + (hi + lo - 2 * a) * max s 0
    from rfl]
  fun_prop

private theorem ArcReparam_mem {a lo hi s : ℝ} (h1 : lo < a) (h2 : a < hi)
    (hs : s ∈ Ioo (-1 : ℝ) 1) : ArcReparam a lo hi s ∈ Ioo lo hi := by
  rw [mem_Ioo]
  rcases le_or_gt 0 s with h | h
  · have hmax : max s 0 = s := max_eq_left h
    rw [ArcReparam, hmax]
    refine ⟨by nlinarith [h, h1, hs.1], by nlinarith [hs.2, h2]⟩
  · have hmax : max s 0 = 0 := max_eq_right (le_of_lt h)
    rw [ArcReparam, hmax]
    refine ⟨by nlinarith [hs.1, h1], by nlinarith [h, h1]⟩

private theorem ArcReparam_injOn {a lo hi : ℝ} (h1 : lo < a) (h2 : a < hi) :
    InjOn (ArcReparam a lo hi) (Ioo (-1 : ℝ) 1) := by
  have ha1 : 0 < a - lo := by linarith
  have ha2 : 0 < hi - a := by linarith
  intro s _ s' _ heq
  rcases le_or_gt 0 s with h | h <;> rcases le_or_gt 0 s' with h' | h'
  · rw [ArcReparam, max_eq_left h, ArcReparam, max_eq_left h'] at heq
    have hfac : (hi - a) * s = (hi - a) * s' := by
      ring_nf at heq ⊢
      linarith
    exact mul_left_cancel₀ (ne_of_gt ha2) hfac
  · rw [ArcReparam, max_eq_left h, ArcReparam, max_eq_right (le_of_lt h')] at heq
    nlinarith [ha1, ha2, h, h']
  · rw [ArcReparam, max_eq_right (le_of_lt h), ArcReparam, max_eq_left h'] at heq
    nlinarith [ha1, ha2, h, h']
  · rw [ArcReparam, max_eq_right (le_of_lt h), ArcReparam, max_eq_right (le_of_lt h')] at heq
    have hfac : (a - lo) * s = (a - lo) * s' := by
      ring_nf at heq ⊢
      linarith
    exact mul_left_cancel₀ (ne_of_gt ha1) hfac

private theorem ArcReparam_surjOn {a lo hi : ℝ} (h1 : lo < a) (h2 : a < hi) :
    ∀ x ∈ Ioo lo hi, ∃ s ∈ Ioo (-1 : ℝ) 1, ArcReparam a lo hi s = x := by
  have ha1 : 0 < a - lo := by linarith
  have ha2 : 0 < hi - a := by linarith
  intro x hx
  rcases le_or_gt a x with h | h
  · have hs0 : 0 ≤ (x - a) / (hi - a) := div_nonneg (by linarith) (le_of_lt ha2)
    refine ⟨(x - a) / (hi - a), ⟨?_, ?_⟩, ?_⟩
    · linarith
    · rw [div_lt_one ha2]; linarith [hx.2]
    · rw [ArcReparam, max_eq_left hs0]
      field_simp
      ring
  · have hs0 : (x - a) / (a - lo) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt ha1)
    refine ⟨(x - a) / (a - lo), ⟨?_, ?_⟩, ?_⟩
    · rw [lt_div_iff₀ ha1]; linarith [hx.1]
    · linarith
    · rw [ArcReparam, max_eq_right hs0]
      field_simp
      ring

/-- **The local arc of a regular level set, inside a ball** (case where the partial derivative in
the second variable is invertible).

The level curve is the graph `x ↦ (x, ψ x)` of the implicit function.  The set `A` of parameters
whose graph point lies in the ball `Metric.ball p ε` is, for small `ε`, an interval `(lo, hi)`
containing `p.1`; reparametrising it to `(-1,1)` gives the required arc, and the construction
guarantees that the arc stays in the ball and exhausts the level set there. -/
private theorem local_arc_ball_snd {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {t : ℝ} (hf : ContDiff ℝ 1 f)
    (hp : f p = t) (hinv : (fderiv ℝ f p ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ σ : ℝ → ℝ × ℝ, σ 0 = p ∧
      ContinuousOn σ (Ioo (-1 : ℝ) 1) ∧ InjOn σ (Ioo (-1 : ℝ) 1) ∧
      (∀ s ∈ Ioo (-1 : ℝ) 1, f (σ s) = t) ∧
      (∀ s ∈ Ioo (-1 : ℝ) 1, σ s ∈ Metric.ball p ε) ∧
      (∀ q : ℝ × ℝ, f q = t → ‖q - p‖ < ε → ∃ s ∈ Ioo (-1 : ℝ) 1, σ s = q) := by
  obtain ⟨ψ, ρ, U, hρ, hUopen, hpU, hψa, -, hder, hdcder, hψcont, hlevel, huniq⟩ :=
    arc_data_snd hf.contDiffAt hp hinv
  obtain ⟨δ, hδ0, hδρ, hstar⟩ := starShaped_of_arc_data hρ hψa hder hdcder
  obtain ⟨ε₁, hε₁, hballU⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hpU)
  have hδcont : ContinuousOn ψ (Ioo (p.1 - δ) (p.1 + δ)) :=
    hψcont.mono fun x hx => ⟨by linarith [hx.1, hδρ], by linarith [hx.2, hδρ]⟩
  set ε : ℝ := min δ ε₁ / 2 with hεdef
  have hε0 : 0 < ε := by rw [hεdef]; positivity
  have hεδ : ε ≤ δ := by
    rw [hεdef]; have := min_le_left δ ε₁; linarith
  have hεε₁ : ε < ε₁ := by
    rw [hεdef]; have := min_le_right δ ε₁; linarith
  set A : Set ℝ := {x : ℝ | |x - p.1| < ε ∧ |ψ x - p.2| < ε} with hAdef
  have hAmem_iff : ∀ x : ℝ, x ∈ A ↔ |x - p.1| < ε ∧ |ψ x - p.2| < ε := by
    intro x; simp only [hAdef, Set.mem_setOf_eq]
  have hminlt : ∀ {u v y : ℝ}, |u - v| < y → v - y < u ∧ u < v + y := by
    intro u v y hx
    obtain ⟨h1, h2⟩ := abs_lt.mp hx
    exact ⟨by linarith, by linarith⟩
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨hx1, hx2⟩ := (hAmem_iff x).mp hx
    have hxρ : x ∈ Ioo (p.1 - ρ) (p.1 + ρ) :=
      hminlt (lt_of_lt_of_le (lt_of_lt_of_le hx1 hεδ) hδρ)
    have hcontx : ContinuousAt ψ x := ((hder x hxρ).differentiableAt).continuousAt
    have hψmem : ψ x ∈ Ioo (p.2 - ε) (p.2 + ε) := hminlt hx2
    have hxmem : x ∈ Ioo (p.1 - ε) (p.1 + ε) := hminlt hx1
    filter_upwards [isOpen_Ioo.mem_nhds hxmem,
      hcontx.preimage_mem_nhds (isOpen_Ioo.mem_nhds hψmem)] with y hy1 hy2
    obtain ⟨b1, b2⟩ := hy1
    obtain ⟨c1, c2⟩ := hy2
    exact (hAmem_iff y).mpr
      ⟨by rw [abs_lt]; exact ⟨by linarith, by linarith⟩,
       by rw [abs_lt]; exact ⟨by linarith, by linarith⟩⟩
  have hAmem : p.1 ∈ A := (hAmem_iff p.1).mpr ⟨by simpa using hε0, by
    rw [hψa, sub_self, abs_zero]; exact hε0⟩
  have hAsub : A ⊆ Ioo (p.1 - ε) (p.1 + ε) := fun x hx => hminlt ((hAmem_iff x).mp hx).1
  have hAstar : ∀ z ∈ A, ∀ w : ℝ, min p.1 z ≤ w → w ≤ max p.1 z → w ∈ A := by
    rintro z hz w hw1 hw2
    obtain ⟨hz1, hz2⟩ := (hAmem_iff z).mp hz
    have hwm : |w - p.1| ≤ |z - p.1| := abs_sub_le_abs_sub_of_between hw1 hw2
    exact (hAmem_iff w).mpr ⟨lt_of_le_of_lt hwm hz1, hstar ε hε0 hεδ z hz1 hz2 w hw1 hw2⟩
  have hAeq : A = Ioo (sInf A) (sSup A) :=
    eq_Ioo_csInf_csSup hAopen hAmem hAsub hAstar
  set lo : ℝ := sInf A with hloadef
  set hi : ℝ := sSup A with hhidef
  have hAeq_mem : ∀ x : ℝ, x ∈ A ↔ x ∈ Ioo lo hi := by
    intro x; rw [hAeq]
  have hmemIoo : p.1 ∈ Ioo lo hi := (hAeq_mem p.1).mp hAmem
  have hlo : lo < p.1 := hmemIoo.1
  have hhi : p.1 < hi := hmemIoo.2
  have hAsub' : A ⊆ Ioo (p.1 - δ) (p.1 + δ) := fun x hx =>
    hminlt (lt_of_lt_of_le ((hAmem_iff x).mp hx).1 hεδ)
  refine ⟨ε, hε0, fun s => (ArcReparam p.1 lo hi s, ψ (ArcReparam p.1 lo hi s)),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (ArcReparam p.1 lo hi 0, ψ (ArcReparam p.1 lo hi 0)) = p
    rw [show ArcReparam p.1 lo hi 0 = p.1 from by simp [ArcReparam], hψa]
  · have hcont : ContinuousOn (ArcReparam p.1 lo hi) (Ioo (-1 : ℝ) 1) :=
      (ArcReparam_continuous _ _ _).continuousOn
    have hmap : MapsTo (ArcReparam p.1 lo hi) (Ioo (-1 : ℝ) 1) (Ioo (p.1 - δ) (p.1 + δ)) :=
      fun s hs => hAsub' ((hAeq_mem _).mpr (ArcReparam_mem hlo hhi hs))
    exact hcont.prodMk (hδcont.comp hcont hmap)
  · intro s hs s' hs' heq
    exact ArcReparam_injOn hlo hhi hs hs' (congrArg Prod.fst heq)
  · intro s hs
    have hsA : ArcReparam p.1 lo hi s ∈ A :=
      (hAeq_mem _).mpr (ArcReparam_mem hlo hhi hs)
    obtain ⟨h1, -⟩ := (hAmem_iff _).mp hsA
    exact hlevel _ (hminlt (lt_of_lt_of_le h1 (le_trans hεδ hδρ)))
  · intro s hs
    have hsA : ArcReparam p.1 lo hi s ∈ A :=
      (hAeq_mem _).mpr (ArcReparam_mem hlo hhi hs)
    obtain ⟨h1, h2⟩ := (hAmem_iff _).mp hsA
    rw [Metric.mem_ball, dist_eq_norm]
    show ‖(ArcReparam p.1 lo hi s, ψ (ArcReparam p.1 lo hi s)) - p‖ < ε
    rw [show (ArcReparam p.1 lo hi s, ψ (ArcReparam p.1 lo hi s)) - p
        = (ArcReparam p.1 lo hi s - p.1, ψ (ArcReparam p.1 lo hi s) - p.2) from rfl]
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_lt h1 h2
  · rintro q hfq hqn
    have hqU : q ∈ U := hballU (by rw [Metric.mem_ball, dist_eq_norm]; exact lt_trans hqn hεε₁)
    have hq2 : q.2 = ψ q.1 := huniq q hqU hfq
    have hqnorm : ‖q - p‖ = max |q.1 - p.1| |q.2 - p.2| := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, Prod.fst_sub, Prod.snd_sub]
    have hq1 : |q.1 - p.1| < ε := lt_of_le_of_lt (le_max_left _ _) (hqnorm ▸ hqn)
    have hq2' : |q.2 - p.2| < ε := lt_of_le_of_lt (le_max_right _ _) (hqnorm ▸ hqn)
    have hqA : q.1 ∈ A := (hAmem_iff q.1).mpr ⟨hq1, by rw [← hq2]; exact hq2'⟩
    obtain ⟨s, hs, hsw⟩ := ArcReparam_surjOn hlo hhi q.1 ((hAeq_mem q.1).mp hqA)
    refine ⟨s, hs, ?_⟩
    show (ArcReparam p.1 lo hi s, ψ (ArcReparam p.1 lo hi s)) = q
    rw [hsw, ← hq2]

/-- The same statement for an abstract `C¹` function whose total derivative at `p` does not
vanish.  If the partial derivative in the second variable is invertible this is
`local_arc_ball_snd`; otherwise the first partial is nonzero and we apply `local_arc_ball_snd` to
`f ∘ L`, where `L` is the swap of the two coordinates (a linear isometry), and transport the arc
back through `L`. -/
private theorem local_arc_ball_of_fderiv_ne_zero {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {p : ℝ × ℝ} {t : ℝ} (hp : f p = t) (hd : fderiv ℝ f p ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ σ : ℝ → ℝ × ℝ, σ 0 = p ∧
      ContinuousOn σ (Ioo (-1 : ℝ) 1) ∧ InjOn σ (Ioo (-1 : ℝ) 1) ∧
      (∀ s ∈ Ioo (-1 : ℝ) 1, f (σ s) = t) ∧
      (∀ s ∈ Ioo (-1 : ℝ) 1, σ s ∈ Metric.ball p ε) ∧
      (∀ q : ℝ × ℝ, f q = t → ‖q - p‖ < ε → ∃ s ∈ Ioo (-1 : ℝ) 1, σ s = q) := by
  set f' : ℝ × ℝ →L[ℝ] ℝ := fderiv ℝ f p with hf'_def
  by_cases h2 : f' ∘L ContinuousLinearMap.inr ℝ ℝ ℝ = 0
  · -- the second partial vanishes, hence the first one does not
    have h1 : f' ∘L ContinuousLinearMap.inl ℝ ℝ ℝ ≠ 0 := by
      intro h1
      apply hd
      apply ContinuousLinearMap.ext
      intro v
      have hv := ContinuousLinearMap.comp_inl_add_comp_inr f' v
      rw [← hv, h1, h2]
      simp
    let L : ℝ × ℝ →L[ℝ] ℝ × ℝ := (LinearIsometryEquiv.prodComm ℝ ℝ ℝ : ℝ × ℝ →L[ℝ] ℝ × ℝ)
    have hLL : ∀ x : ℝ × ℝ, L (L x) = x := fun x => by simp [L]
    have hLinj : Function.Injective L := fun x y hxy => by rw [← hLL x, ← hLL y, hxy]
    have hLnorm : ∀ x : ℝ × ℝ, ‖L x‖ = ‖x‖ := fun x =>
      LinearIsometryEquiv.norm_map (LinearIsometryEquiv.prodComm ℝ ℝ ℝ) x
    have hLir : (L ∘L ContinuousLinearMap.inr ℝ ℝ ℝ) = ContinuousLinearMap.inl ℝ ℝ ℝ := by
      apply ContinuousLinearMap.ext
      intro x
      simp [L]
    have hFderiv : fderiv ℝ (fun v => f (L v)) (L p) = f' ∘L L := by
      have hcomp : fderiv ℝ (fun v => f (L v)) (L p)
          = fderiv ℝ f (L (L p)) ∘L fderiv ℝ (fun v => L v) (L p) :=
        fderiv_comp (L p) (hf.differentiable (by norm_num)).differentiableAt
          (ContinuousLinearMap.differentiableAt L)
      rw [hcomp, hLL, ContinuousLinearMap.fderiv, ← hf'_def]
    have hLcd : ContDiff ℝ 1 (fun v : ℝ × ℝ => L v) := ContinuousLinearMap.contDiff L
    have hFct : ContDiff ℝ 1 (fun v => f (L v)) := hf.comp hLcd
    have hFt : (fun v => f (L v)) (L p) = t := by
      show f (L (L p)) = t
      rw [hLL, hp]
    have hInv : (fderiv ℝ (fun v => f (L v)) (L p) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
      rw [hFderiv, ContinuousLinearMap.comp_assoc, hLir]
      exact isInvertible_of_ne_zero h1
    obtain ⟨ε, hε, σ, hσ0, hcont, hinj, hlev, hball, hcov⟩ := local_arc_ball_snd hFct hFt hInv
    refine ⟨ε, hε, fun s => L (σ s), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show L (σ 0) = p
      rw [hσ0, hLL]
    · exact (ContinuousLinearMap.continuous L).continuousOn.comp hcont (mapsTo_univ _ _)
    · intro a ha b hb hab
      exact hinj ha hb (hLinj hab)
    · intro s hs
      show f (L (σ s)) = t
      exact hlev s hs
    · intro s hs
      have hs' := hball s hs
      rw [Metric.mem_ball, dist_eq_norm] at hs' ⊢
      have hsub : L (σ s) - p = L (σ s - L p) := by rw [map_sub, hLL]
      rw [hsub, hLnorm]
      exact hs'
    · intro q hq hdist
      have hq' : (fun v => f (L v)) (L q) = t := by
        show f (L (L q)) = t
        rw [hLL]
        exact hq
      have hdist' : ‖L q - L p‖ < ε := by
        rw [← map_sub, hLnorm]
        exact hdist
      obtain ⟨s, hs, hsq⟩ := hcov (L q) hq' hdist'
      exact ⟨s, hs, by show L (σ s) = q; rw [hsq, hLL]⟩
  · exact local_arc_ball_snd hf hp (by simpa [hf'_def] using isInvertible_of_ne_zero h2)

theorem pullback_local_arc_ball (ψ : Submission.Diffeo) {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ} (hg : ContDiff ℝ 1 g) (t : ℝ) (p : ℝ × ℝ) (hp : Work.Smooth.Morse.pullback ψ g p = t) (hd : fderiv ℝ (Work.Smooth.Morse.pullback ψ g) p ≠ 0) : ∃ ε : ℝ, 0 < ε ∧ ∃ σ : ℝ → ℝ × ℝ, σ 0 = p ∧ ContinuousOn σ (Set.Ioo (-1 : ℝ) 1) ∧ Set.InjOn σ (Set.Ioo (-1 : ℝ) 1) ∧ (∀ s ∈ Set.Ioo (-1 : ℝ) 1, Work.Smooth.Morse.pullback ψ g (σ s) = t) ∧ (∀ s ∈ Set.Ioo (-1 : ℝ) 1, σ s ∈ Metric.ball p ε) ∧ (∀ q : ℝ × ℝ, Work.Smooth.Morse.pullback ψ g q = t → ‖q - p‖ < ε → ∃ s ∈ Set.Ioo (-1 : ℝ) 1, σ s = q) := by
  have hf : ContDiff ℝ 1 (Work.Smooth.Morse.pullback ψ g) :=
    Work.Smooth.Morse.pullback_contDiff_one ψ hg
  exact local_arc_ball_of_fderiv_ne_zero hf hp hd

end Work.Smooth.Morse.Regular
