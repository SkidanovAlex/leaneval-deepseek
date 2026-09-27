import Mathlib
import Submission.Work.Drive.hasDerivAt_localArg

namespace Work.Surf

/-- **A continuous lift of `t ↦ arg (γ t) / (2π)` is differentiable wherever the curve is.**
If `γ : ℝ → ℂ` is differentiable at `t₀` with non-vanishing values and `G : ℝ → ℝ` is a continuous
lift of the honest argument of `γ` (i.e. `(G t : ℝ/ℤ) = arg (γ t) / (2π)` for all `t`), then `G` is
differentiable at `t₀` with derivative `Im (γ' t₀ / γ t₀) / (2π)`.  Route: the local argument lift
`L t = (arg (γ t₀) + Im (log (γ t / γ t₀))) / (2π)` is differentiable at `t₀` by
`Work.Drive.hasDerivAt_localArg` (halved), it is a lift of the honest argument near `t₀`, and any two
continuous lifts differ locally by a constant integer. -/
theorem hasDerivAt_of_lift_arg {γ : ℝ → ℂ} {t₀ : ℝ} (hγ : HasDerivAt γ (deriv γ t₀) t₀)
    (hne : ∀ t, γ t ≠ 0) {G : ℝ → ℝ} (hG : Continuous G)
    (hlift : ∀ t : ℝ, (G t : UnitAddCircle) = ((γ t).arg / (2 * Real.pi) : ℝ)) :
    HasDerivAt G ((deriv γ t₀ / γ t₀).im / (2 * Real.pi)) t₀ := by
  -- The local argument lift built from the principal logarithm.
  set L : ℝ → ℝ :=
    fun s => (Complex.arg (γ t₀) + (Complex.log (γ s / γ t₀)).im) / (2 * Real.pi) with hL
  have hmem : γ t₀ / γ t₀ ∈ Complex.slitPlane := by
    rw [div_self (hne t₀)]
    exact Complex.one_mem_slitPlane
  -- `L` is differentiable at `t₀` with the expected derivative.
  have hLdiff : HasDerivAt L ((deriv γ t₀ / γ t₀).im / (2 * Real.pi)) t₀ := by
    rw [hL]
    have h := (Work.Drive.hasDerivAt_localArg (z := γ) (t₀ := t₀) (t := t₀) hγ hmem).div_const 2
    have hfun :
        (fun s : ℝ => ((Complex.arg (γ t₀) + (Complex.log (γ s / γ t₀)).im) / Real.pi) / 2)
          = fun s : ℝ => (Complex.arg (γ t₀) + (Complex.log (γ s / γ t₀)).im) / (2 * Real.pi) := by
      funext s
      rw [div_div]
      ring_nf
    have hder :
        (((deriv γ t₀ / γ t₀).im / Real.pi) / 2) = (deriv γ t₀ / γ t₀).im / (2 * Real.pi) := by
      rw [div_div]
      ring_nf
    rw [hfun, hder] at h
    exact h
  -- `L` is a lift of the honest argument: it differs from `arg (γ s) / (2π)` by an integer.
  have hrel : ∀ s : ℝ, (L s : UnitAddCircle) = ((γ s).arg / (2 * Real.pi) : ℝ) := by
    intro s
    rw [hL]
    have hangle : (((Complex.arg (γ t₀) + (Complex.log (γ s / γ t₀)).im : ℝ) : Real.Angle)
        = ((Complex.arg (γ s) : ℝ) : Real.Angle)) := by
      rw [Complex.log_im, Real.Angle.coe_add, Complex.arg_div_coe_angle (hne s) (hne t₀)]
      abel
    have h2 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have h'' : (((Complex.arg (γ t₀) + (Complex.log (γ s / γ t₀)).im : ℝ) : AddCircle (2 * Real.pi))
        = ((Complex.arg (γ s) : ℝ) : AddCircle (2 * Real.pi))) := hangle
    have h' := congrArg (AddCircle.equivAddCircle (2 * Real.pi) 1 h2 one_ne_zero) h''
    rw [AddCircle.equivAddCircle_apply_mk, AddCircle.equivAddCircle_apply_mk] at h'
    simpa [div_eq_mul_inv, mul_comm, mul_assoc] using h'
  -- Hence `G - L` is integer valued everywhere.
  have hdiff : ∀ s : ℝ, ∃ n : ℤ, (n : ℝ) = G s - L s := by
    intro s
    have hEq : (G s : UnitAddCircle) = (L s : UnitAddCircle) := by rw [hlift s, ← hrel s]
    have h0 : ((G s - L s : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, hEq, sub_self]
    have hmem2 : (G s - L s) - 0 ∈ AddSubgroup.zmultiples (1 : ℝ) := by
      rw [← QuotientAddGroup.eq_iff_sub_mem (N := AddSubgroup.zmultiples (1 : ℝ))]
      rw [h0, QuotientAddGroup.mk_zero]
    have hmem3 : G s - L s ∈ AddSubgroup.zmultiples (1 : ℝ) := by simpa using hmem2
    obtain ⟨k, hk⟩ :=
      (AddSubgroup.mem_zmultiples_iff.mp hmem3 : ∃ k : ℤ, k • (1 : ℝ) = G s - L s)
    exact ⟨k, by rw [← hk, zsmul_one]⟩
  -- `G - L` is continuous at `t₀` and integer valued, hence constant near `t₀`.
  have hHcont : ContinuousAt (fun s : ℝ => G s - L s) t₀ :=
    hG.continuousAt.sub hLdiff.continuousAt
  have hev : (fun s : ℝ => G s - L s) =ᶠ[nhds t₀] fun _ => G t₀ - L t₀ := by
    have hmemI : G t₀ - L t₀ ∈ Set.Ioo (G t₀ - L t₀ - 1 / 2) (G t₀ - L t₀ + 1 / 2) := by
      constructor <;> norm_num
    have hb := hHcont.eventually (isOpen_Ioo.mem_nhds hmemI)
    filter_upwards [hb] with s hs
    obtain ⟨m, hm⟩ := hdiff s
    obtain ⟨n, hn⟩ := hdiff t₀
    have h1 : |((m - n : ℤ) : ℝ)| < 1 := by
      rw [Int.cast_sub, hm, hn, abs_lt]
      constructor <;> linarith [hs.1, hs.2]
    have h2 : |m - n| < 1 := by
      have : ((|m - n| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; exact h1
      exact_mod_cast this
    have h3 : m = n := by
      have h4 : m - n = 0 := Int.abs_lt_one_iff.mp h2
      omega
    rw [← hm, ← hn, h3]
  -- Therefore `G` agrees near `t₀` with the differentiable function `L` plus a constant.
  have hGeq : G =ᶠ[nhds t₀] fun s => (G t₀ - L t₀) + L s := by
    filter_upwards [hev] with s hs
    linarith
  have hderiv : HasDerivAt (fun s : ℝ => (G t₀ - L t₀) + L s)
      (0 + ((deriv γ t₀ / γ t₀).im / (2 * Real.pi))) t₀ :=
    (hasDerivAt_const t₀ (G t₀ - L t₀)).add hLdiff
  simpa using hderiv.congr_of_eventuallyEq hGeq

end Work.Surf
