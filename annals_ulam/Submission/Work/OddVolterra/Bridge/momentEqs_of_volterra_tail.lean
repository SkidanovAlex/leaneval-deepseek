import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Assembly
import Submission.Work.OddVolterra.Ball
import Submission.Work.OddVolterra.Abel.abel_form_of_volterra_form
import Submission.Commons.Analysis.Calculus.eq_zero_of_iteratedDerivWithin_eq_zero_of_eventuallyEq_zero
import Submission.Work.OddVolterra.Bridge.moment_identities_on_tail

/-!
# The odd Volterra bridge, with the missing hypothesis made explicit

The requested bridge `Work.OddVolterra.Bridge.momentEqs_of_volterra` (in
`Submission/Work/OddVolterra/Bridge/momentEqs_of_volterra.lean`) is **not derivable** from its
hypotheses: the passage from the differentiated identities to the two moment equations requires
the perturbed data to coincide with the base (ball) data on a neighbourhood of an anchor point
(Ryabogin, Annals 195 (2022), W3.tex: "Since `h(s)=0`, `x(s)=x_o(s)`, `y(s)=y_o(s)` on `[1-τ,1]`,
`F` and `H` vanish on `[1-τ,1]` and, therefore, identically"), and `CurveData` records
`x s = y s = profileX s` for `s ≥ 1 - tau` but nothing about `h` there beyond the bounds
`|h|, |h'|, |h''| ≤ 1/100`.  This file contains the *provable* versions of the bridge:

* `Work.OddVolterra.Bridge.momentEqs_of_volterra_of_tail` — with the hypothesis
  `∀ s, 1 - tau ≤ s → h s = 0`;
* `Work.OddVolterra.Bridge.momentEqs_of_volterra_of_support` — with the hypothesis
  `Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)` supplied by the existence construction
  `Work.OddVolterra.Existence.curve_data`; this is the form actually needed by the odd case.

Nothing in this file uses `sorry`.

## Contents

* `eq_zero_of_iteratedDeriv_eq_zero_of_eventuallyEq_zero` — the "constant of integration" tool
  (Taylor with Lagrange remainder): `C^∞` on `(0,1)`, vanishing `(n+1)`-st derivative on `(0,1)`
  and vanishing near an interior point ⟹ identically zero;
* `momentEqs_of_moment_derivs` — the moment equations from the two differentiated identities plus
  the *values* on the tail `[1 - tau, 1]`;
* `contDiffAt_momentRHS`, `iteratedDeriv_momentF_sub_eq_zero_of_harik_hrow`,
  `iteratedDeriv_momentH_eq_zero_of_harik_hrowH` — the differentiated identities obtained from
  the Abel inversion `harik` (paper `(arik)`) together with the row identities `hrow`, `hrowH`
  (paper `(ass+)`/`(t1)`, `(t2)`);
* `momentEqs_of_volterra_of_tail`, `momentEqs_of_volterra_of_support` — the bridge itself.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.Bridge

open Commons.Geometry.Ulam

noncomputable section

/-- **The constant-of-integration tool.**  If `F` is `C^∞` on `(0,1)`, its `(n+1)`-st derivative
vanishes on `(0,1)`, and `F` vanishes on a neighbourhood of an interior point `c`, then `F`
vanishes on `(0,1)`.  (Taylor's formula with Lagrange remainder at `c`, applied on an interval
`[a,b] ⊂ (0,1)` chosen to contain both `s` and `c`.) -/
theorem eq_zero_of_iteratedDeriv_eq_zero_of_eventuallyEq_zero (n : ℕ) {F : ℝ → ℝ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (Set.Ioo 0 1))
    (hd : ∀ s ∈ Set.Ioo 0 1, iteratedDeriv (n + 1) F s = 0)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hz : F =ᶠ[𝓝 c] 0) :
    ∀ s ∈ Set.Ioo 0 1, F s = 0 := by
  intro s hs
  have hlo0 : 0 < min s c := lt_min hs.1 hc.1
  have hhi1 : max s c < 1 := max_lt hs.2 hc.2
  have hab : min s c / 2 < (1 + max s c) / 2 := by
    linarith [min_le_max (a := s) (b := c)]
  have hgt : min s c / 2 < c := by
    have := min_le_right s c; linarith
  have hlt : c < (1 + max s c) / 2 := by
    have := le_max_right s c; linarith
  have hsub : Set.Icc (min s c / 2) ((1 + max s c) / 2) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hF' : ContDiffOn ℝ ((n : ℕ) + 1) F (Set.Icc (min s c / 2) ((1 + max s c) / 2)) := by
    apply (hF.mono hsub).of_le
    rw [← Nat.cast_add_one]
    exact WithTop.coe_le_coe.mpr le_top
  have hd' : ∀ x ∈ Set.Ioo (min s c / 2) ((1 + max s c) / 2),
      iteratedDerivWithin ((n : ℕ) + 1) F (Set.Icc (min s c / 2) ((1 + max s c) / 2)) x = 0 := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := hsub ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have huniq : UniqueDiffOn ℝ (Set.Icc (min s c / 2) ((1 + max s c) / 2)) := uniqueDiffOn_Icc hab
    have hcont : ContDiffAt ℝ ((n : ℕ) + 1) F x := by
      apply (hF.contDiffAt (isOpen_Ioo.mem_nhds hx')).of_le
      rw [← Nat.cast_add_one]
      exact WithTop.coe_le_coe.mpr le_top
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq hcont ⟨le_of_lt hx.1, le_of_lt hx.2⟩]
    exact hd x hx'
  have hzv : ∀ y ∈ Set.Icc (min s c / 2) ((1 + max s c) / 2), F y = 0 :=
    Commons.Analysis.Calculus.eq_zero_of_iteratedDerivWithin_eq_zero_of_eventuallyEq_zero
      n hgt hlt hF' hd' hz
  exact hzv s ⟨by linarith [min_le_left s c], by linarith [le_max_left s c]⟩

/-- **The moment equations from the differentiated identities plus the tail values.**

This is the "constant of integration" step of the paper's passage from the differentiated
equations to the moment equations.  The hypotheses are exactly the differentiated identities
(`hderF`, `hderH`) together with the *values* of the two moment integrals on the unperturbed
tail `[1 - tau, 1]` (`hvalF`, `hvalH`); the values are what the requested statement
`momentEqs_of_volterra` is missing. -/
theorem momentEqs_of_moment_derivs (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hcontF : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u : ℝ => momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) u - momentRHS n u)
      (Set.Ioo 0 1))
    (hcontH : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u : ℝ => momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) u)
      (Set.Ioo 0 1))
    (hderF : ∀ s ∈ Set.Ioo 0 1,
      iteratedDeriv (n + 1)
        (fun u : ℝ => momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) u
          - momentRHS n u) s = 0)
    (hderH : ∀ s ∈ Set.Ioo 0 1,
      iteratedDeriv n
        (fun u : ℝ => momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) u) s = 0)
    (hvalF : ∀ s ∈ Set.Icc (1 - tau) 1,
      momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) s = momentRHS n s)
    (hvalH : ∀ s ∈ Set.Icc (1 - tau) 1,
      momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0) :
    MomentEqsOn n (oddSemicircleMomentConstant n) h x y
      (Work.OddEnvelope.envelopeProfile h x y) (Set.Ioc 0 1) := by
  have htau : tau = 1 / 10 := rfl
  have hcIoo : (1 - tau / 2) ∈ Set.Ioo (0 : ℝ) 1 := by rw [htau]; norm_num
  have hc1 : 1 - tau < 1 - tau / 2 := by rw [htau]; norm_num
  have hc2 : 1 - tau / 2 < 1 := by rw [htau]; norm_num
  have hnbhd : Set.Icc (1 - tau) 1 ∈ 𝓝 (1 - tau / 2) := Icc_mem_nhds hc1 hc2
  have hzF : (fun u : ℝ => momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) u
      - momentRHS n u) =ᶠ[𝓝 (1 - tau / 2)] 0 := by
    filter_upwards [hnbhd] with u hu
    exact sub_eq_zero.mpr (hvalF u hu)
  have hzH : (fun u : ℝ => momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) u)
      =ᶠ[𝓝 (1 - tau / 2)] 0 := by
    filter_upwards [hnbhd] with u hu
    exact hvalH u hu
  have hF0 : ∀ s ∈ Set.Ioo 0 1,
      momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) s - momentRHS n s = 0 :=
    eq_zero_of_iteratedDeriv_eq_zero_of_eventuallyEq_zero n hcontF hderF hcIoo hzF
  have hH0 : ∀ s ∈ Set.Ioo 0 1,
      momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0 := by
    have hder' : ∀ s ∈ Set.Ioo 0 1,
        iteratedDeriv ((n - 1) + 1)
          (fun u : ℝ => momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) u) s = 0 := by
      intro s hs; rw [Nat.sub_add_cancel hn]; exact hderH s hs
    exact eq_zero_of_iteratedDeriv_eq_zero_of_eventuallyEq_zero (n - 1) hcontH hder' hcIoo hzH
  constructor
  · intro s hs
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · have h := hF0 s ⟨hs.1, hlt⟩
      rw [sub_eq_zero] at h
      rw [h]
      rfl
    · subst heq
      exact hvalF 1 ⟨by rw [htau]; norm_num, le_rfl⟩
  · intro s hs
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · exact hH0 s ⟨hs.1, hlt⟩
    · subst heq
      exact hvalH 1 ⟨by rw [htau]; norm_num, le_rfl⟩


/-- `momentRHS` is smooth. -/
theorem contDiffAt_momentRHS (n : ℕ) (s : ℝ) :
    ContDiffAt ℝ ((n : ℕ) + 1) (momentRHS n) s := by
  unfold momentRHS
  have hsqrt : ContDiffAt ℝ ((n : ℕ) + 1) (fun u : ℝ => Real.sqrt (1 + u ^ 2)) s :=
    (Real.contDiffAt_sqrt (by positivity : (1 + s ^ 2) ≠ 0)).comp s (by fun_prop)
  exact (contDiffAt_const (c := (Commons.Geometry.Ulam.oddSemicircleMomentConstant n))).div
    hsqrt (by positivity)

/-- **The differentiated first moment identity.**  Combining the row identity `hrow` (the paper's
`(ass+)`, which rewrites `(d/ds)^{n+1} momentF` as `E₁` plus the Abel integral) with the Abel
inversion `harik` (the paper's `(arik)`, which computes that same Abel integral) gives that
`momentF - momentRHS` has vanishing `(n+1)`-st derivative on `(0,1)`. -/
theorem iteratedDeriv_momentF_sub_eq_zero_of_harik_hrow (n : ℕ) {h x y : ℝ → ℝ}
    (harik : ∀ a c : ℝ, 0 < a → a ≤ c → c < 1 → ∀ s ∈ Set.Icc a c,
      (∫ σ in s..1,
          (Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0 /
            Real.sqrt (σ - s)) = (Q n h s) 0 ∧
      (∫ σ in s..1,
          (Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1 /
            Real.sqrt (σ - s)) = (Q n h s) 1)
    (hrow : ∀ a c : ℝ, 0 < a → a ≤ c → c < 1 → ∀ s ∈ Set.Icc a c,
      iteratedDeriv (n + 1)
          (fun u : ℝ => momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) u) s =
        E1 n h s + ∫ σ in s..1,
          (Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0 /
            Real.sqrt (σ - s))
    (hcontF : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u : ℝ => momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) u
        - momentRHS n u) (Set.Ioo 0 1)) :
    ∀ s ∈ Set.Ioo 0 1,
      iteratedDeriv (n + 1)
        (fun u : ℝ => momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) u
          - momentRHS n u) s = 0 := by
  intro s hs
  have ha : 0 < s / 2 := by linarith [hs.1]
  have hac : s / 2 ≤ (1 + s) / 2 := by linarith
  have hc1 : (1 + s) / 2 < 1 := by linarith [hs.2]
  have hsIcc : s ∈ Set.Icc (s / 2) ((1 + s) / 2) := ⟨by linarith, by linarith⟩
  have hrow_s := hrow (s / 2) ((1 + s) / 2) ha hac hc1 s hsIcc
  have harik_s := (harik (s / 2) ((1 + s) / 2) ha hac hc1 s hsIcc).1
  have hQ : (Q n h s) 0 = - E1 n h s + iteratedDeriv (n + 1) (momentRHS n) s := by simp [Q]
  have hkey : iteratedDeriv (n + 1)
        (fun u : ℝ => momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) u) s
      = iteratedDeriv (n + 1) (momentRHS n) s := by
    rw [hrow_s, harik_s, hQ]; ring
  have hR : ContDiffAt ℝ (n + 1) (momentRHS n) s := contDiffAt_momentRHS n s
  have hG : ContDiffAt ℝ (n + 1)
      (fun u : ℝ => momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) u) s := by
    have h1 : ContDiffAt ℝ (n + 1)
        (fun u : ℝ => momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) u
          - momentRHS n u) s := by
      apply (hcontF.contDiffAt (isOpen_Ioo.mem_nhds hs)).of_le
      rw [← Nat.cast_add_one]
      exact WithTop.coe_le_coe.mpr le_top
    have h2 := h1.add hR
    simpa using h2
  have hsub := iteratedDeriv_sub (f := fun u : ℝ =>
      momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) u) (g := momentRHS n) hG hR
  change iteratedDeriv (n + 1)
    ((fun u : ℝ => momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) u) - momentRHS n) s = 0
  rw [hsub, hkey, sub_self]

/-- **The differentiated second (centroid) moment identity.**  Combining the row identity
`hrowH` (the paper's `(t2)`) with the Abel inversion `harik` gives that `momentH` has vanishing
`n`-th derivative on `(0,1)`. -/
theorem iteratedDeriv_momentH_eq_zero_of_harik_hrowH (n : ℕ) {h x y : ℝ → ℝ}
    (harik : ∀ a c : ℝ, 0 < a → a ≤ c → c < 1 → ∀ s ∈ Set.Icc a c,
      (∫ σ in s..1,
          (Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0 /
            Real.sqrt (σ - s)) = (Q n h s) 0 ∧
      (∫ σ in s..1,
          (Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1 /
            Real.sqrt (σ - s)) = (Q n h s) 1)
    (hrowH : ∀ a c : ℝ, 0 < a → a ≤ c → c < 1 → ∀ s ∈ Set.Icc a c,
      iteratedDeriv n
          (fun u : ℝ => momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) u) s =
        E2 n h s + ∫ σ in s..1,
          (Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1 /
            Real.sqrt (σ - s)) :
    ∀ s ∈ Set.Ioo 0 1,
      iteratedDeriv n
        (fun u : ℝ => momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) u) s = 0 := by
  intro s hs
  have ha : 0 < s / 2 := by linarith [hs.1]
  have hac : s / 2 ≤ (1 + s) / 2 := by linarith
  have hc1 : (1 + s) / 2 < 1 := by linarith [hs.2]
  have hsIcc : s ∈ Set.Icc (s / 2) ((1 + s) / 2) := ⟨by linarith, by linarith⟩
  have hrowH_s := hrowH (s / 2) ((1 + s) / 2) ha hac hc1 s hsIcc
  have harik_s := (harik (s / 2) ((1 + s) / 2) ha hac hc1 s hsIcc).2
  have hQ : (Q n h s) 1 = - E2 n h s := by simp [Q]
  rw [hrowH_s, harik_s, hQ]; ring


/-- **The provable version of the bridge.**  This is the requested statement with the missing
hypothesis `htail : ∀ s, 1 - tau ≤ s → h s = 0` (equivalently `Function.support h ⊆ Set.Iic
(1 - tau)`).  That hypothesis is exactly what the existence theorem produces: its input requires
`Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)`, hence `h` vanishes on `[1 - tau, 1]`.

With `htail` the perturbed data coincide with the ball data on the unperturbed tail
`[1 - tau, 1]` (`moment_identities_on_tail`), so `momentF - momentRHS` and `momentH` vanish
there; their `(n+1)`-st resp. `n`-th derivatives vanish on `(0,1)` by `harik` together with the
row identities `hrow`, `hrowH`; hence they vanish identically by
`Work.OddVolterra.Bridge.momentEqs_of_moment_derivs`. -/
theorem momentEqs_of_volterra_of_tail (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hdata : Work.OddVolterra.CurveData n h x y)
    (htail : ∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s → h s = 0)
    (harik : ∀ a c : ℝ, 0 < a → a ≤ c → c < 1 → ∀ s ∈ Set.Icc a c,
      (∫ σ in s..1,
          (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0 /
            Real.sqrt (σ - s)) = (Work.OddVolterra.Q n h s) 0 ∧
      (∫ σ in s..1,
          (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1 /
            Real.sqrt (σ - s)) = (Work.OddVolterra.Q n h s) 1)
    (hrow : ∀ a c : ℝ, 0 < a → a ≤ c → c < 1 → ∀ s ∈ Set.Icc a c,
      iteratedDeriv (n + 1)
          (fun u : ℝ => Work.OddVolterra.momentF n h x y
            (Work.OddEnvelope.envelopeProfile h x y) u) s =
        Work.OddVolterra.E1 n h s + ∫ σ in s..1,
          (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0 /
            Real.sqrt (σ - s))
    (hrowH : ∀ a c : ℝ, 0 < a → a ≤ c → c < 1 → ∀ s ∈ Set.Icc a c,
      iteratedDeriv n
          (fun u : ℝ => Work.OddVolterra.momentH n h x y
            (Work.OddEnvelope.envelopeProfile h x y) u) s =
        Work.OddVolterra.E2 n h s + ∫ σ in s..1,
          (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1 /
            Real.sqrt (σ - s))
    (hcontF : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u : ℝ => Work.OddVolterra.momentF n h x y
        (Work.OddEnvelope.envelopeProfile h x y) u - Work.OddVolterra.momentRHS n u)
      (Set.Ioo 0 1))
    (hcontH : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u : ℝ => Work.OddVolterra.momentH n h x y
        (Work.OddEnvelope.envelopeProfile h x y) u) (Set.Ioo 0 1)) :
    Work.OddVolterra.MomentEqsOn n (Commons.Geometry.Ulam.oddSemicircleMomentConstant n) h x y
      (Work.OddEnvelope.envelopeProfile h x y) (Set.Ioc 0 1) := by
  have hanchor := Work.OddVolterra.Bridge.moment_identities_on_tail n hn hh hdata htail
  exact momentEqs_of_moment_derivs n hn hcontF hcontH
    (iteratedDeriv_momentF_sub_eq_zero_of_harik_hrow n harik hrow hcontF)
    (iteratedDeriv_momentH_eq_zero_of_harik_hrowH n harik hrowH)
    (fun s hs => (hanchor s hs).1) (fun s hs => (hanchor s hs).2)


/-- **The provable bridge in the form supplied by the existence theorem.**  The existence
construction `Work.OddVolterra.Existence.curve_data` takes as input a smooth `h` with
`Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)`; with that hypothesis the tail vanishing
`htail = ∀ s, 1 - tau ≤ s → h s = 0` is automatic (`h` vanishes on `(1 - tau, ∞)` by the support
condition and at `1 - tau` by continuity), so this is a direct consequence of
`momentEqs_of_volterra_of_tail`. -/
theorem momentEqs_of_volterra_of_support (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hdata : Work.OddVolterra.CurveData n h x y)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (harik : ∀ a c : ℝ, 0 < a → a ≤ c → c < 1 → ∀ s ∈ Set.Icc a c,
      (∫ σ in s..1,
          (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0 /
            Real.sqrt (σ - s)) = (Work.OddVolterra.Q n h s) 0 ∧
      (∫ σ in s..1,
          (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1 /
            Real.sqrt (σ - s)) = (Work.OddVolterra.Q n h s) 1)
    (hrow : ∀ a c : ℝ, 0 < a → a ≤ c → c < 1 → ∀ s ∈ Set.Icc a c,
      iteratedDeriv (n + 1)
          (fun u : ℝ => Work.OddVolterra.momentF n h x y
            (Work.OddEnvelope.envelopeProfile h x y) u) s =
        Work.OddVolterra.E1 n h s + ∫ σ in s..1,
          (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0 /
            Real.sqrt (σ - s))
    (hrowH : ∀ a c : ℝ, 0 < a → a ≤ c → c < 1 → ∀ s ∈ Set.Icc a c,
      iteratedDeriv n
          (fun u : ℝ => Work.OddVolterra.momentH n h x y
            (Work.OddEnvelope.envelopeProfile h x y) u) s =
        Work.OddVolterra.E2 n h s + ∫ σ in s..1,
          (Work.OddVolterra.Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1 /
            Real.sqrt (σ - s))
    (hcontF : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u : ℝ => Work.OddVolterra.momentF n h x y
        (Work.OddEnvelope.envelopeProfile h x y) u - Work.OddVolterra.momentRHS n u)
      (Set.Ioo 0 1))
    (hcontH : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u : ℝ => Work.OddVolterra.momentH n h x y
        (Work.OddEnvelope.envelopeProfile h x y) u) (Set.Ioo 0 1)) :
    Work.OddVolterra.MomentEqsOn n (Commons.Geometry.Ulam.oddSemicircleMomentConstant n) h x y
      (Work.OddEnvelope.envelopeProfile h x y) (Set.Ioc 0 1) := by
  refine momentEqs_of_volterra_of_tail n hn hh hdata (fun s hs => ?_) harik hrow hrowH hcontF hcontH
  have htau : 0 < Work.OddVolterra.tau := by norm_num [Work.OddVolterra.tau]
  have hcont : ContinuousAt h s := hh.continuous.continuousAt
  have hright : Filter.Tendsto h (𝓝[Set.Ioi s] s) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hnotmem : t ∉ Function.support h := by
      intro hmem
      have hmem' := hsupp (Function.mem_support.mpr hmem)
      have ht' : s < t := ht
      exact absurd hmem'.2 (by linarith)
    exact (Function.notMem_support.mp hnotmem).symm
  exact tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds) hright



end

end Work.OddVolterra.Bridge
