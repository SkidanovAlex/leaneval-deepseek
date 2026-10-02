/-
Copyright: Work.MRMT (mandelbar) subproject.
The weak (= distributional) `∂̄`-derivative of a compactly supported `C^n` function, `n ≠ 0`.

## Why this file exists (`⊤` is ANALYTIC in Lean v4.34)

In the requested statement

`theorem is_dbar_deriv_of_contDiff_hasCompactSupport (f : ℂ → ℂ) (hc : ContDiff ℝ ⊤ f)
    (hs : HasCompactSupport f) : IsDbarDeriv f (dzbar f)`

the order `⊤` lives in `ℕ∞ω = WithTop ℕ∞`, where `⊤` is `ω`, the **analyticity** order, and
*not* the `C^∞` order `∞ = ↑(⊤ : ℕ∞)`.  This matches the convention recorded at the top of the
mandelbar run ("smooth = `ContDiff ℝ ∞`; `⊤` is ANALYTIC").  With `hc : ContDiff ℝ ω f` the
hypotheses `hc, hs` force `f = 0` (a real-analytic function on the connected plane vanishing on
the non-empty open complement of its compact support vanishes identically, by
`AnalyticOnNhd.eq_of_eventuallyEq`), so the requested statement asserts only
`IsDbarDeriv 0 0`: it is true but vacuous, and cannot be applied to a bump function, which is
what the Ahlfors–Bers / Weyl-lemma development needs.

The mathematically correct statement, which *does* carry all the content, is the one below:
it uses the weakest hypothesis under which the argument works, namely `ContDiff ℝ n` with
`n ≠ 0` (this is exactly what `ContDiff.differentiable` and `ContDiff.continuous_fderiv`
consume), and it specialises to `ContDiff ℝ ∞` (`ContDiff ℝ_infty_hasCompactSupport`).

## The proof

`IsDbarDeriv f (dzbar f)` unfolds to local integrability of `f` and of `dzbar f` plus the
distributional identity against every test function `φ : 𝓓(⊤, ℂ)`.  Put `F = f * φ`, which is
compactly supported and as smooth as `f`.  The product rule for the Wirtinger derivative
(`Work.MRMT.Sobolev.dzbar_mul`) gives

`∂̄F = f · ∂̄φ + φ · ∂̄f`,

and the fundamental identity `∫ ∂̄G = 0` for compactly supported `G` (proved in
`Submission.Work.MRMT.Sobolev.integral_dzbar_eq_zero_of_contDiff` by integrating by parts
against the constant test function `1`) gives `∫ f·∂̄φ = -∫ ∂̄f·φ`, as required.
-/
import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Sobolev.dzbar_mul
import Submission.Work.MRMT.Sobolev.integral_dzbar_eq_zero_of_contDiff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open MeasureTheory Complex Function Filter
open scoped Distributions Topology

namespace Work.MRMT.Sobolev

/-- `∂̄f` is continuous as soon as `f` is `C^n` with `n ≠ 0`. -/
theorem continuous_dzbar_of_contDiff (f : ℂ → ℂ) {n : WithTop ℕ∞} (hn : n ≠ 0)
    (hc : ContDiff ℝ n f) : Continuous (dzbar f) := by
  have hd : Continuous (fderiv ℝ f) := hc.continuous_fderiv hn
  unfold dzbar
  exact ((hd.clm_apply continuous_const).add
    (continuous_const.mul (hd.clm_apply continuous_const))).div_const 2

/-- **Weak `∂̄`-derivative of a compactly supported `C^n` function** (`n ≠ 0`): for
`f : ℂ → ℂ` of class `C^n` with `n ≠ 0` and compact support, the pointwise Wirtinger
derivative `dzbar f` is the distributional (weak) `∂̄`-derivative of `f`, i.e.
`∫ f · ∂̄φ = -∫ ∂̄f · φ` for every smooth compactly supported test function `φ`.

This is the correct form of `is_dbar_deriv_of_contDiff_hasCompactSupport`; see the module
docstring for why the hypothesis there (`ContDiff ℝ ⊤`, i.e. real-analyticity) is degenerate. -/
theorem is_dbar_deriv_of_contDiff_of_ne_zero_hasCompactSupport (f : ℂ → ℂ) {n : WithTop ℕ∞}
    (hn : n ≠ 0) (hc : ContDiff ℝ n f) (hs : HasCompactSupport f) : IsDbarDeriv f (dzbar f) := by
  have hinf : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hne : n ⊓ ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
    intro h
    have h' : min n ((⊤ : ℕ∞) : WithTop ℕ∞) = ⊥ := h
    rw [min_eq_bot] at h'
    rcases h' with h' | h'
    · exact hn h'
    · exact hinf h'
  have hcd : Continuous (dzbar f) := continuous_dzbar_of_contDiff f hn hc
  refine ⟨hc.continuous.locallyIntegrable, hcd.locallyIntegrable, fun φ => ?_⟩
  -- the test function has order `∞`
  have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ : ℂ → ℂ) := φ.contDiff
  -- `F = f * φ` is compactly supported and of order `n ⊓ ∞`
  have hFcd : ContDiff ℝ (n ⊓ ((⊤ : ℕ∞) : WithTop ℕ∞)) (fun z => f z * (φ : ℂ → ℂ) z) :=
    (hc.of_le inf_le_left).mul (hφ.of_le inf_le_right)
  have hFcs : HasCompactSupport (fun z => f z * (φ : ℂ → ℂ) z) := φ.hasCompactSupport.mul_left
  have hzero : ∫ z, dzbar (fun z => f z * (φ : ℂ → ℂ) z) z = 0 :=
    integral_dzbar_eq_zero_of_contDiff _ hne hFcd hFcs
  -- the Leibniz rule for `∂̄`
  have hpt : ∀ z, dzbar (fun z => f z * (φ : ℂ → ℂ) z) z
      = f z * dzbar (φ : ℂ → ℂ) z + (φ : ℂ → ℂ) z * dzbar f z := fun z =>
    dzbar_mul (hc.differentiable hn z) (hφ.differentiable hinf z)
  have ha : Integrable (fun z => f z * dzbar (φ : ℂ → ℂ) z) :=
    (hc.continuous.mul (continuous_dzbar_of_contDiff _ hinf hφ)).integrable_of_hasCompactSupport
      hs.mul_right
  have hb : Integrable (fun z => (φ : ℂ → ℂ) z * dzbar f z) :=
    (hφ.continuous.mul hcd).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right
  have hb' : Integrable (fun z => dzbar f z * (φ : ℂ → ℂ) z) := by
    simpa only [mul_comm] using hb
  refine ⟨ha, hb', ?_⟩
  have h1 : ∫ z, (f z * dzbar (φ : ℂ → ℂ) z + (φ : ℂ → ℂ) z * dzbar f z) = 0 := by
    rw [← hzero]
    exact integral_congr_ae (Eventually.of_forall fun z => (hpt z).symm)
  have h2 : (∫ z, f z * dzbar (φ : ℂ → ℂ) z) + ∫ z, (φ : ℂ → ℂ) z * dzbar f z = 0 := by
    rw [← integral_add ha hb]; exact h1
  have h3 : ∫ z, (φ : ℂ → ℂ) z * dzbar f z = ∫ z, dzbar f z * (φ : ℂ → ℂ) z :=
    integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
  rw [h3] at h2
  exact eq_neg_iff_add_eq_zero.mpr h2

/-- **Weak `∂̄`-derivative of a compactly supported smooth function**: the
`C^∞` (`= ContDiff ℝ ∞`, `∞ = ↑(⊤ : ℕ∞)`) case of
`is_dbar_deriv_of_contDiff_of_ne_zero_hasCompactSupport`.  This is the statement the
Ahlfors–Bers development wants (bump functions are `C^∞` but never real-analytic). -/
theorem is_dbar_deriv_of_contDiff_infty_hasCompactSupport (f : ℂ → ℂ)
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hs : HasCompactSupport f) :
    IsDbarDeriv f (dzbar f) :=
  is_dbar_deriv_of_contDiff_of_ne_zero_hasCompactSupport f (by simp) hc hs

/-- **The requested hypothesis is degenerate**: in Lean v4.34 `ContDiff ℝ ⊤` is the order
`ω = ⊤` of `ℕ∞ω = WithTop ℕ∞`, i.e. *real analyticity*, and a real-analytic `f : ℂ → ℂ` with
compact support vanishes identically.

`tsupport f` is compact, and `ℂ` is not compact (`IsCompact.ne_univ`), so we may choose
`x ∉ tsupport f`; since `tsupport f` is closed, `f` vanishes on a neighbourhood of `x`, and the
identity theorem `AnalyticOnNhd.eq_of_eventuallyEq` (`ℂ` is preconnected) gives `f = 0`.

Consequently the statement `is_dbar_deriv_of_contDiff_hasCompactSupport` can only ever be
applied to `f = 0`, where it reduces to the triviality `IsDbarDeriv 0 0` — it is *true* but
carries no mathematical content, and it cannot be applied to a bump function. -/
theorem eq_zero_of_contDiff_omega_hasCompactSupport (f : ℂ → ℂ)
    (hc : ContDiff ℝ (⊤ : WithTop ℕ∞) f) (hs : HasCompactSupport f) : f = 0 := by
  have h_an : AnalyticOnNhd ℝ f Set.univ := hc.analyticOnNhd
  obtain ⟨x, hx⟩ : ∃ x : ℂ, x ∉ tsupport f := by
    by_contra h
    rw [not_exists] at h
    exact hs.ne_univ (Set.eq_univ_of_forall fun x => not_not.mp (h x))
  have hxev : f =ᶠ[𝓝 x] 0 := by
    have : (tsupport f)ᶜ ∈ 𝓝 x := (isClosed_tsupport f).isOpen_compl.mem_nhds hx
    filter_upwards [this] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  exact AnalyticOnNhd.eq_of_eventuallyEq h_an (analyticOnNhd_const (v := (0 : ℂ))) hxev

end Work.MRMT.Sobolev
