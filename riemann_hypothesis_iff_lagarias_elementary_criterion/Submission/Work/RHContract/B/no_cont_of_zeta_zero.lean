import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.B.Phi_secondDeriv
import Submission.Work.RHContract.B.h2Minus_unbounded

/-!
# `Work.RHContract.B.no_cont_of_zeta_zero`

`Φ(s) = ∫_2^∞ (ψ t − t) k(t) t^{−s} dt` is holomorphic on the right half plane `Re s > 0`
(`B.Phi_analyticOn`) and its second derivative there is the closed form `h₂ − h₂′`
(`B.Phi_secondDeriv`), whose double pole at `ρ − 1` makes it unbounded near that point
(`B.h2Minus_unbounded`, ROUTE_LEAD §3.3 step B6).

The present lemma is the corresponding *rigidity* statement (ROUTE_LEAD §3.3, B7): for a zero `ρ`
of `ζ₁` in the critical strip, `Φ` admits **no** analytic continuation to any right half plane
`{s | c < Re s}` with `c < Re ρ − 1`.  Indeed, if `H` were such a continuation, then on
`{Re s > 0}` we have `H = Φ`, so `H″ = Φ″ = h₂ − h₂′`; by the identity theorem for meromorphic
functions — applied on the half plane `{Re s > c}`, where both `H″` (holomorphic) and
`h₂ − h₂′` (meromorphic) live and where the two agree on the non empty open subset
`{Re s > 0}` — the meromorphic orders of `H″` and of `h₂ − h₂′` at `ρ − 1` coincide.  But
`H″` is holomorphic at `ρ − 1`, hence has non negative order, whereas `h₂ − h₂′` has the double
pole, i.e. order `−2`.  Contradiction.

The three ingredients are therefore

* the meromorphy of the closed form `h₂` (`h₂ = −(logDeriv ζ)(s+1)/(s+1) − 2^{−s}/s` off
  `s = 0, −1`), and hence of `h₂ − h₂′` — globally, so in particular on any half plane;
* the identity theorem for meromorphic functions on a preconnected open set, proved here from
  `isOpen_setOfPred_eventually_nhdsWithin` and the principles of isolated zeros
  (`MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero`,
  `MeromorphicAt.frequently_zero_iff_eventuallyEq_zero`), so that no discreteness or
  connectedness statement about half planes minus a discrete set is needed;
* the order computation `meromorphicOrderAt h2Minus (ρ − 1) = −2` (the case `h2Closed_order` of
  `B.h2Minus_unbounded`, combined with `meromorphicOrderAt_deriv_eq_sub_one`).
-/

open MeasureTheory Filter
open scoped Topology

namespace Work.RHContract.B

noncomputable section

/-! ## Meromorphy of the closed form `h₂` and of `h₂ − h₂′` -/

/-- The Riemann zeta function is meromorphic on `ℂ` (holomorphic away from `1`, simple pole at
`1`). -/
private lemma meromorphic_riemannZeta : Meromorphic riemannZeta := by
  intro x
  by_cases hx : x = 1
  · subst hx
    refine MeromorphicAt.congr (f := fun s : ℂ => (s - 1)⁻¹ * riemannZeta₁ s) ?_ ?_
    · exact (MeromorphicAt.inv (analyticAt_id.sub analyticAt_const).meromorphicAt).mul
        (differentiable_riemannZeta₁.analyticAt 1).meromorphicAt
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact (riemannZeta_eq_inv_sub_mul (by simpa using hs)).symm
  · exact (analyticOn_riemannZeta x (by simpa using hx)).meromorphicAt

/-- The closed form of `h₂` is the manifestly meromorphic expression
`−(logDeriv ζ)(s+1)/(s+1) − 2^{−s}/s`, off the two points `s = 0` and `s = −1`. -/
private lemma h2Closed_eq (s : ℂ) (hs0 : s ≠ 0) (hs1 : s + 1 ≠ 0) :
    Work.RHContract.Landau.h2Closed s =
      -(logDeriv riemannZeta (s + 1)) / (s + 1) - (2 : ℂ) ^ (-s) / s := by
  unfold Work.RHContract.Landau.h2Closed logDeriv
  simp only [Pi.div_apply]
  field_simp
  ring

/-- A point different from `y` is eventually different from `y` in the punctured neighbourhood
filter. -/
private lemma eventually_ne_singleton (x y : ℂ) : ∀ᶠ s in 𝓝[≠] x, s ≠ y := by
  rcases eq_or_ne x y with rfl | hxy
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simpa using hs
  · exact nhdsWithin_le_nhds (compl_singleton_mem_nhds hxy)

/-- The closed form `h₂` is meromorphic on `ℂ`. -/
lemma meromorphic_h2Closed : Meromorphic Work.RHContract.Landau.h2Closed := by
  intro x
  have hlog : Meromorphic (logDeriv riemannZeta) :=
    meromorphic_riemannZeta.deriv.div meromorphic_riemannZeta
  refine MeromorphicAt.congr
    (f := fun s : ℂ => -(logDeriv riemannZeta (s + 1)) / (s + 1) - (2:ℂ)^(-s) / s) ?_ ?_
  · have h1 : MeromorphicAt (fun s : ℂ => logDeriv riemannZeta (s + 1)) x :=
      (hlog (x + 1)).comp_analyticAt (g := fun s : ℂ => s + 1) (by fun_prop)
    have h2 : MeromorphicAt (fun s : ℂ => -(logDeriv riemannZeta (s + 1))) x := h1.neg
    have h3 : MeromorphicAt (fun s : ℂ => (s + 1 : ℂ)) x :=
      (analyticAt_id.add analyticAt_const).meromorphicAt
    have h4 : MeromorphicAt (fun s : ℂ => (2:ℂ)^(-s)) x :=
      (AnalyticAt.cpow analyticAt_const analyticAt_id.neg
        (by norm_num [Complex.mem_slitPlane_iff])).meromorphicAt
    have h5 : MeromorphicAt (fun s : ℂ => (s : ℂ)) x := analyticAt_id.meromorphicAt
    exact (h2.div h3).sub (h4.div h5)
  · filter_upwards [eventually_ne_singleton x 0, eventually_ne_singleton x (-1)]
      with s hs0 hsm1
    exact (h2Closed_eq s hs0 (by intro h; exact hsm1 (by linear_combination h))).symm

/-- `h₂ − h₂′` is meromorphic on `ℂ`. -/
lemma meromorphic_h2Minus : Meromorphic Work.RHContract.Landau.h2Minus :=
  meromorphic_h2Closed.sub meromorphic_h2Closed.deriv

/-! ## The identity theorem for meromorphic functions -/

/-- **Identity theorem for meromorphic functions.**  If `f` and `g` are meromorphic on an open
preconnected set `U` and agree on a non empty open subset `V ⊆ U`, then they have the same germ at
every point of `U`.

The set `Z` where the two germs agree is open, and its complement (within `U`) is open as well:
at a point where the germs do not agree the difference is, by the principle of isolated zeros,
non vanishing in a punctured neighbourhood.  A preconnected set with a non empty clopen subset is
contained in it. -/
lemma meromorphic_germ_eq_of_eqOn_open {f g : ℂ → ℂ} {U V : Set ℂ}
    (hUo : IsOpen U) (hU : IsPreconnected U) (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (hV : IsOpen V) (hVU : V ⊆ U) (hVne : V.Nonempty) (hfg : Set.EqOn f g V) :
    U ⊆ {z : ℂ | f =ᶠ[𝓝[≠] z] g} := by
  set h : ℂ → ℂ := f - g with hh
  have hZ : IsOpen {z : ℂ | h =ᶠ[𝓝[≠] z] 0} := isOpen_setOfPred_eventually_nhdsWithin
  have hZ' : IsOpen {z : ℂ | ∀ᶠ w in 𝓝[≠] z, h w ≠ 0} := isOpen_setOfPred_eventually_nhdsWithin
  have hmain : U ⊆ {z : ℂ | h =ᶠ[𝓝[≠] z] 0} := by
    refine IsPreconnected.subset_left_of_subset_union hZ (hUo.inter hZ') ?_ ?_ ?_ hU
    · rw [Set.disjoint_left]
      intro z hz hz'
      obtain ⟨hzU, hz'⟩ := hz'
      have hm : MeromorphicAt h z := (hf z hzU).sub (hg z hzU)
      have hfreq : ∃ᶠ w in 𝓝[≠] z, h w = 0 := hm.frequently_zero_iff_eventuallyEq_zero.mpr hz
      obtain ⟨w, hw⟩ := (hfreq.and_eventually hz').exists
      exact hw.2 hw.1
    · intro z hzU
      have hm : MeromorphicAt h z := (hf z hzU).sub (hg z hzU)
      rcases hm.eventually_eq_zero_or_eventually_ne_zero with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨hzU, h0⟩
    · obtain ⟨v, hv⟩ := hVne
      refine ⟨v, hVU hv, ?_⟩
      have hVmem : ∀ᶠ w in 𝓝 v, w ∈ V := by
        filter_upwards [IsOpen.mem_nhds hV hv] with w hw; exact hw
      filter_upwards [hVmem.filter_mono nhdsWithin_le_nhds] with w hw
      simp [hh, hfg hw]
  intro z hz
  have hz' : h =ᶠ[𝓝[≠] z] 0 := hmain hz
  have h2 := hz'.add (Filter.EventuallyEq.refl (𝓝[≠] z) g)
  simpa [hh, Pi.sub_apply] using h2

/-! ## The double pole of `h₂ − h₂′` at `ρ − 1` -/

/-- At a zero `ρ` of `ζ₁` in the critical strip the closed form `h₂` has a simple pole and its
derivative a double pole at `ρ − 1`, while the two orders differ; hence the difference `h₂ − h₂′`
has a double pole there: its meromorphic order at `ρ − 1` is `−2`. -/
lemma h2Minus_order (ρ : ℂ) (hρ : riemannZeta₁ ρ = 0)
    (hb1 : (1 / 2 : ℝ) < ρ.re) (hb2 : ρ.re < 1) :
    meromorphicOrderAt Work.RHContract.Landau.h2Minus (ρ - 1) = -2 := by
  have h2ord : meromorphicOrderAt Work.RHContract.Landau.h2Closed (ρ - 1) = -1 :=
    h2Closed_order ρ hρ hb1 hb2
  have hderiv : meromorphicOrderAt (deriv Work.RHContract.Landau.h2Closed) (ρ - 1) = -2 := by
    have h := meromorphicOrderAt_deriv_eq_sub_one (f := Work.RHContract.Landau.h2Closed)
      (x := ρ - 1) (n := -1) (by norm_num) h2ord
    simpa using h
  have hneg : meromorphicOrderAt (fun s => -(deriv Work.RHContract.Landau.h2Closed s)) (ρ - 1)
      = -2 := by
    rw [← meromorphicOrderAt_fun_neg (f := deriv Work.RHContract.Landau.h2Closed) (x := ρ - 1)]
    exact hderiv
  have hEq : Work.RHContract.Landau.h2Minus =
      ((fun s => -(deriv Work.RHContract.Landau.h2Closed s)) +
        Work.RHContract.Landau.h2Closed) := by
    ext s; simp [Work.RHContract.Landau.h2Minus, sub_eq_add_neg, add_comm]
  rw [hEq]
  have hmem : MeromorphicAt Work.RHContract.Landau.h2Closed (ρ - 1) :=
    meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [h2ord]; norm_num)
  have hlt : meromorphicOrderAt (fun s => -(deriv Work.RHContract.Landau.h2Closed s)) (ρ - 1)
      < meromorphicOrderAt Work.RHContract.Landau.h2Closed (ρ - 1) := by
    rw [hneg, h2ord]; decide
  rw [meromorphicOrderAt_add_eq_left_of_lt hmem hlt, hneg]

/-! ## The target -/

/-- **`Φ` cannot be continued analytically to the left of `Re s = Re ρ − 1`** for a zero `ρ` of
`ζ₁` with `1/2 < Re ρ < 1`. -/
theorem no_cont_of_zeta_zero (ρ : ℂ) (hρ : riemannZeta₁ ρ = 0)
    (hb1 : (1/2 : ℝ) < ρ.re) (hb2 : ρ.re < 1) :
    ¬ ∃ (H : ℂ → ℂ) (c : ℝ), c < ρ.re - 1 ∧ AnalyticOn ℂ H {s : ℂ | c < s.re} ∧
        (∀ s : ℂ, 0 < s.re → H s = Work.RHContract.Landau.Phi s) := by
  rintro ⟨H, c, hc, hHan, hHΦ⟩
  have hUopen : IsOpen {s : ℂ | c < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected {s : ℂ | c < s.re} := (convex_halfSpace_re_gt c).isPreconnected
  have hUρ : ρ - 1 ∈ {s : ℂ | c < s.re} := by
    simp only [Set.mem_ofPred_eq, Complex.sub_re, Complex.one_re]
    linarith
  have hFdiff : DifferentiableOn ℂ (fun s => deriv (deriv H) s) {s : ℂ | c < s.re} :=
    (hHan.differentiableOn.deriv hUopen).deriv hUopen
  have hFmer : MeromorphicOn (fun s => deriv (deriv H) s) {s : ℂ | c < s.re} :=
    fun x hx => (hFdiff.analyticAt (hUopen.mem_nhds hx)).meromorphicAt
  have hgmer : MeromorphicOn Work.RHContract.Landau.h2Minus {s : ℂ | c < s.re} :=
    meromorphic_h2Minus.meromorphicOn
  have hVopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hVU : {s : ℂ | 0 < s.re} ⊆ {s : ℂ | c < s.re} := by
    intro s hs
    simp only [Set.mem_ofPred_eq] at *
    linarith
  have hVne : ({s : ℂ | 0 < s.re} : Set ℂ).Nonempty := ⟨1, by norm_num⟩
  -- `H″ = Φ″ = h₂ − h₂′` on the right half plane
  have hVeq : Set.EqOn (fun s => deriv (deriv H) s) Work.RHContract.Landau.h2Minus
      {s : ℂ | 0 < s.re} := by
    intro s hs
    change deriv (deriv H) s = Work.RHContract.Landau.h2Minus s
    have hVs : {s : ℂ | 0 < s.re} ∈ 𝓝 s := hVopen.mem_nhds hs
    have hev : H =ᶠ[𝓝 s] Work.RHContract.Landau.Phi := by
      filter_upwards [hVs] with w hw
      exact hHΦ w hw
    have h1 : deriv (deriv H) s = deriv (deriv Work.RHContract.Landau.Phi) s :=
      (hev.deriv.deriv).eq_of_nhds
    rw [h1, Phi_secondDeriv s hs]
  have hgerm : (fun s => deriv (deriv H) s) =ᶠ[𝓝[≠] (ρ - 1)] Work.RHContract.Landau.h2Minus :=
    meromorphic_germ_eq_of_eqOn_open hUopen hUconn hFmer hgmer hVopen hVU hVne hVeq hUρ
  -- `H″` is holomorphic at `ρ − 1`, so its order there is `≥ 0`, but that order equals `−2`
  have horder : 0 ≤ meromorphicOrderAt Work.RHContract.Landau.h2Minus (ρ - 1) := by
    rw [← meromorphicOrderAt_congr hgerm]
    exact AnalyticAt.meromorphicOrderAt_nonneg (hFdiff.analyticAt (hUopen.mem_nhds hUρ))
  rw [h2Minus_order ρ hρ hb1 hb2] at horder
  exact absurd horder (by decide)

end

end Work.RHContract.B
