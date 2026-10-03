/-
# `Submission.Work.FIArea6.S16.HeartIface` — the `Z`-continuation interface of the §16 heart

The §16 heart (`Work.FIArea6.S16TsumHeart`, *FI* (16.38)) is the contour-shift bound for the
Möbius-twisted Hecke sum

  `Tsum Pa χ m p = Σ_{(n,Π)=1} λ_m(n)μ(n)γ(n;C)p(n)`.

Exactly as for its `(5.9)`-restricted sibling `Submission.Work.FIArea6Road.TauIface`, the proof
splits into two independent halves:

* the **existence** of a continuation `Zc` of the Dirichlet series
  `Zsfun s = Σ_n c(n)n^{-s}` (`c(n) = 1_{(n,Π)=1}λ_m(n)μ(n)γ(n;C)`) into the strip
  `1/2 < re s < 1`, together with the bound (16.35) that the contour shift consumes (`ZcHyp`); and
* the **contour shift** itself: the Mellin representation (16.28) of `p`, Cauchy's theorem on the
  rectangle `[1-δ, 1+1/log N] × [-T,T]` (`T = heightT Pa`, `δ = deltaC`), and the estimates on the
  shifted line, the two horizontal segments and the far piece `|t| > T`.

The interface below is the *verbatim* analogue of `Work.FIArea6Road.ZcHypTau` with
`ZsfunTau ↦ Zsfun` and the restricted sum `tsumTau ↦ Tsum`, so that the two halves are
interchangeable between the two hearts.

**The shape of the log-power.**  The two Euler-product factors of the regrouping are bounded with
absolute constants only as `P(s) ≪ (log Pz)^{O(1)}` (16.33) and `Q(s) ≪ C^{1-σ}log C` (16.34); a
factor `(log Pz)^{O(1)}` grows with `x` and cannot be absorbed into a *uniform* `C_z`, so the shape
with `log N` inside the log-power (`log Pz ≤ log N`, `Pa.hPhi`) is the correct, uniformly
satisfiable one.  The contour shift loses only a constant, since `log(|m|+|t|+3) ≥ √log N/2` on the
rectangle `|t| ≤ heightT Pa` for large `x`.
-/
import Mathlib
import Submission.Work.FIArea6.S16TsumHeartDefs
import Submission.Work.FIArea6.TauPieces.TsumHeartDefs
import Submission.Work.FIArea6Hecke.S16CleanDefs
import Submission.Work.FITop4.Bridge.area5_6_defs

set_option autoImplicit false

namespace Work.FIArea6.S16

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The `Z`-continuation interface** (*FI* (16.31)–(16.35)).  `ZcHyp Pa χ m d ε c_h C_z Zc`
bundles the properties of the continuation `Zc` of `Zsfun` that the §16 contour shift needs:

1. `Zc` agrees with the Dirichlet series `Zsfun` on the half-plane `re s > 1`;
2. `Zc` is analytic in the region `re s > 1/2 ∧ 1 - c_h/(2 d^ε log(|m|+|Im s|+3)) < re s`;
3. `‖Zc s‖ ≤ C_z·d·C^{1-σ}·L(s)^6` for `1/2 < σ ≤ 1` (the shifted line, where the saving
   `C^{1-σ}` is used);
4. `‖Zc s‖ ≤ C_z·d·L(s)^6` for `1 < σ ≤ 1 + 1/log N` (the two horizontal segments on the part
   `σ > 1`, where the `C^{1-σ}` saving is unavailable but unnecessary),

with `σ = re s` and `L(s) = log N + log(|m| + |Im s| + 3) + 2`.

**Why the split.**  `Zc(2) = Zsfun 2 = 1 + O((log C)³/C)` (the summand `n = 1` is `1`, and the
ones with `1 < n ≤ C` and `(n,Π)=1` vanish), so a *single* bound of the shape
`C_z·d·C^{1-re s}·log^6` on the whole strip `re s ≤ 2` forces `C_z ≳ C/(d log^6 N)`, which is not
uniform in the datum; and a single bound without the `C^{1-re s}` factor loses the saving
`C^{1-σ}` on the shifted line (`C ≤ N^{1-η}`, so `C^{1-σ₀} = C^{δ}` is exactly what discharges
`N^{-δ}` against `E1 + E2`).  Splitting at `σ = 1` gives both: the factor where it is available
(`σ ≤ 1`), and its absence where it is not needed (`σ > 1`). -/
def ZcHyp (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (d : ℕ) (ε c_h C_z : ℝ)
    (Zc : ℂ → ℂ) : Prop :=
  0 < C_z ∧
  (∀ s : ℂ, 1 < s.re → Zc s = Work.FIArea6.TauPieces.Zsfun Pa chi m s) ∧
  AnalyticOn ℂ Zc {s : ℂ | 1 / 2 < s.re ∧
    1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re} ∧
  (∀ s : ℂ, 1 / 2 < s.re →
    1 - 1 / Real.log (Pa.Pz : ℝ) ≤ s.re →
    1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re → s.re ≤ 1 →
    ‖Zc s‖ ≤ C_z * (d : ℝ) * Pa.C ^ (1 - s.re)
      * (Real.log (Pa.N) + Real.log (|(m : ℝ)| + |s.im| + 3) + 2) ^ (6 : ℕ)) ∧
  (∀ s : ℂ, 1 < s.re → s.re ≤ 1 + 1 / Real.log Pa.N → s.re ≤ 2 →
    ‖Zc s‖ ≤ C_z * (d : ℝ)
      * (Real.log (Pa.N) + Real.log (|(m : ℝ)| + |s.im| + 3) + 2) ^ (6 : ℕ))

/-- The first exponential slot `exp(-η c (4d)^{-ε}√log N)` of *FI* (16.38). -/
abbrev S16E1 (Pa : Work.FITop.Params) (c : ℝ) (d : ℕ) (ε : ℝ) : ℝ :=
  Real.exp (-(Pa.η * c * (((4 * d : ℕ) : ℝ)) ^ (-ε) * Real.sqrt (Real.log Pa.N)))

/-- The second exponential slot `exp(-η log N/log Pz)` of *FI* (16.38). -/
abbrev S16E2 (Pa : Work.FITop.Params) : ℝ :=
  Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))

/-- The right-hand side of *FI* (16.38) with explicit `c` and prefactor `C`. -/
abbrev S16RH (Pa : Work.FITop.Params) (c C : ℝ) (d : ℕ) (ε : ℝ) : ℝ :=
  C * (S16E1 Pa c d ε + S16E2 Pa) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)

/-- The common hypotheses on the datum `(Pa, ν, d, m, χ, p)` of the §16 heart. -/
def HeartHyp (Pa : Work.FITop.Params) (ν : ℝ) (d : ℕ) (m : ℤ) (chi : GaussianInt → ℂ)
    (p : ℝ → ℝ) (ε : ℝ) : Prop :=
  0 < ν ∧ ν < 1 / (2 * ε) ∧ 1 ≤ d ∧ (d : ℝ) ≤ 2 * (Real.log Pa.N) ^ ν ∧
  |(m : ℝ)| ≤ 4 * Real.exp (Real.sqrt (Real.log Pa.N)) ∧
  Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi ∧
  ContDiff ℝ 2 p ∧ (∀ u, 0 ≤ p u) ∧ (∀ u, p u ≤ 1) ∧
  (∀ u, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N) ∧
  (∀ k : ℕ, k ≤ 2 → ∀ u : ℝ,
    |iteratedDeriv k p u| ≤ Work.FITop4.cMoll k * (Pa.θ * Pa.N) ^ (-(k : ℝ)))

/-- The §16 heart's conclusion at an explicit exponent constant `c` and prefactor `C`. -/
def HeartBound (Pa : Work.FITop.Params) (c C : ℝ) (d : ℕ) (ε : ℝ) (m : ℤ)
    (chi : GaussianInt → ℂ) (p : ℝ → ℝ) : Prop :=
  ‖Work.FIArea6Hecke.Tsum Pa chi m p‖ ≤ S16RH Pa c C d ε

/-- **`ZcHyp` is monotone in the region depth `c_h`**: a smaller `c_h` shrinks both the
analyticity region and the region on which the bound is required, so the interface is easier. -/
lemma ZcHyp_mono {Pa : Work.FITop.Params} {chi : GaussianInt → ℂ} {m : ℤ} {d : ℕ} {ε : ℝ}
    {C_z : ℝ} {Zc : ℂ → ℂ} {c_h c_h' : ℝ} (hd : 1 ≤ d) (h : c_h ≤ c_h')
    (H : ZcHyp Pa chi m d ε c_h' C_z Zc) : ZcHyp Pa chi m d ε c_h C_z Zc := by
  obtain ⟨hC, heq, han, h4, h5⟩ := H
  have key : ∀ s : ℂ, 1 - c_h' / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3))
      ≤ 1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) := by
    intro s
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hde : (0 : ℝ) < (d : ℝ) ^ ε := Real.rpow_pos_of_pos hd0 _
    have hlog : (0 : ℝ) < Real.log (|(m : ℝ)| + |s.im| + 3) := by
      apply Real.log_pos
      have h1 := abs_nonneg (m : ℝ)
      have h2 := abs_nonneg s.im
      linarith
    have hpos : (0 : ℝ) < 2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3) := by positivity
    have hdiv : c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3))
        ≤ c_h' / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) :=
      div_le_div_of_nonneg_right h hpos.le
    linarith
  refine ⟨hC, heq, han.mono ?_, ?_, h5⟩
  · intro s hs
    exact ⟨hs.1, lt_of_le_of_lt (key s) hs.2⟩
  · intro s h1 h2 h3 h4'
    exact h4 s h1 h2 (lt_of_le_of_lt (key s) h3) h4'

/-- Restatement of `S16TsumHeart` in terms of `HeartHyp`/`HeartBound` (definitional), for use by
the assembly and by the delegated pieces. -/
theorem s16TsumHeart_iff :
    Work.FIArea6.S16TsumHeart ↔
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
        ∃ c C x0 : ℝ, 0 < c ∧ 0 < C ∧ 0 < x0 ∧
          ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
          ∀ (ν : ℝ) (d : ℕ) (m : ℤ) (chi : GaussianInt → ℂ) (p : ℝ → ℝ),
            HeartHyp Pa ν d m chi p ε → HeartBound Pa c C d ε m chi p := by
  constructor
  · intro h ε hε hε4
    obtain ⟨c, C, x0, hc, hC, hx0, H⟩ := h ε hε hε4
    refine ⟨c, C, x0, hc, hC, hx0, ?_⟩
    intro Pa hPa ν d m chi p hh
    obtain ⟨hν0, hν1, hd1, hdN, hm, hchi, hpC, hp0, hp1, hpsupp, hpd⟩ := hh
    exact H Pa hPa ν d m chi p hν0 hν1 hd1 hdN hm hchi hpC hp0 hp1 hpsupp hpd
  · intro h ε hε hε4
    obtain ⟨c, C, x0, hc, hC, hx0, H⟩ := h ε hε hε4
    refine ⟨c, C, x0, hc, hC, hx0, ?_⟩
    intro Pa hPa ν d m chi p hν0 hν1 hd1 hdN hm hchi hpC hp0 hp1 hpsupp hpd
    exact H Pa hPa ν d m chi p ⟨hν0, hν1, hd1, hdN, hm, hchi, hpC, hp0, hp1, hpsupp, hpd⟩

end

end Work.FIArea6.S16
