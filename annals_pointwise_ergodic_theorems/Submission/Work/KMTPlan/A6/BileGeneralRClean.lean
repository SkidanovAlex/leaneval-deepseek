/-
# Theorem `bile` for `r > 1` in the finite cyclic model — the interpolation, clean

Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals 195 (2022), Theorem `bile`: for `1 ≤ r < 2d/(d-1)`, `d = deg P`, the arithmetic
bilinear average `A(f,g) = polyBilinearAverageZMod X P Q f g` obeys

  `‖A(f,g)‖_{L^r(ℤ/Qℤ)} ≲ 2^{-c_r l} ‖f‖_{L²} ‖g‖_{L²}`

whenever one of `f, g` satisfies the Ionescu--Wainger minor-arc condition at height `2^l`, with a
constant uniform in the modulus `Q` and the height `l`.

This file proves the **log-convex interpolation step** that turns

* the `r = 1` base estimate with gain (`Work.KMTPlan.A6.MdlBileR1OfImprov`, proved from
  `ImprovKMT`; the paper's Proposition `bile-2`) and
* the **unconditional** `L^q` endpoint (the paper's (avg-1): `‖A(f,g)‖_{L^q} ≲ ‖f‖₂‖g‖₂` for
  `q < 2d/(d-1)`, uniformly in `Q`, which needs the Appendix C concentration estimates)

into Theorem `bile` at every `r ∈ [2, 2d/(d-1))`, with the (weaker but sufficient) gain
`2^{-(c₁θ)l}` where `1/r = θ/1 + (1-θ)/q`.

## What is clean here and what is named

Everything in this file is axiom-clean (`#print axioms`).  The unconditional endpoint is *not*
proved here: it enters as the explicit predicate `LqEndpointUniform P q` (a statement about
`BilinearAverageLq`, i.e. only about `LpNormZMod`/`polyBilinearAverageZMod` — no stubs), so that
`MdlBileGeneralR_of_LqEndpoint` is the exact statement of the area's target `BileGeneralR`
conditional on the (avg-1) chapter.  The other files attempting this
(`KMTPlan/A6/MdlBileOfR1.lean`, `KMTPlan/A6/BileGeneralR.lean`) are respectively non-compiling and
a `sorry` stub; `bileInterpIw.lean` duplicates the interpolation with the same minor-arc
hypothesis but does not compile.

## The ingredients used (all proved and axiom-clean)

* `Work.Analysis.Paraproduct.LpNormZMod_logconvex` — log-convexity of the normalized `L^p` norms
  on `ℤ/Qℤ` (Hölder);
* `Work.KMTPlan.A6.MdlBileR1OfImprov` — the `r = 1` estimate with gain, under the *Ionescu--Wainger*
  minor-arc hypothesis `MdlIwMinorArc` (this is why the interpolation below is stated with
  `MdlIwMinorArc` and not with the naive `MinorArcSupport`: the latter is a *weaker* hypothesis, so
  the `r = 1` estimate that is available — the one under `MdlIwMinorArc` — cannot be used for it);
* the exponent arithmetic `exists_interp_theta_clean`, proved here by hand (the existing
  `Work.KMTPlan.A6.exists_interp_theta` is a `sorry` stub).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlBileR1OfImprov
import Submission.Work.Analysis.Paraproduct.LpNormZMod_logconvex

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

/-! ## Two elementary helpers for the interpolation -/

/-- The normalized `L^p` norm on `ℤ/Qℤ` is nonnegative (reproduced to keep the closure small). -/
private lemma lpNormZMod_nonneg' (Q : ℕ) [NeZero Q] (p : ℝ) (f : ZMod Q → ℂ) :
    0 ≤ Work.Analysis.Concentration.LpNormZMod Q p f := by
  unfold Work.Analysis.Concentration.LpNormZMod
  exact Real.rpow_nonneg (mul_nonneg (by positivity)
    (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) p)) _

/-- The arithmetic core of the interpolation (no division needed, so it is valid at `A * B = 0`):
`(ε * (A * B))^θ * (C * (A * B))^{1-θ} ≤ ε^θ * C^{1-θ} * A * B` for `ε, C, A, B ≥ 0`. -/
private lemma rpow_interp_arith' {ε C θ A B : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (ε * (A * B)) ^ θ * (C * (A * B)) ^ (1 - θ) ≤ ε ^ θ * C ^ (1 - θ) * A * B := by
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have hABeq : (A * B) ^ θ * (A * B) ^ (1 - θ) = A * B := by
    rw [← Real.rpow_add' hAB (by norm_num : θ + (1 - θ) ≠ 0),
      show θ + (1 - θ) = 1 by ring, Real.rpow_one]
  rw [Real.mul_rpow hε hAB, Real.mul_rpow hC hAB]
  rw [show ε ^ θ * (A * B) ^ θ * (C ^ (1 - θ) * (A * B) ^ (1 - θ))
      = (ε ^ θ * C ^ (1 - θ)) * ((A * B) ^ θ * (A * B) ^ (1 - θ)) by ring]
  rw [hABeq]
  exact le_of_eq (by ring)

/-! ## The exponent arithmetic -/

/-- **Exponent arithmetic for the interpolation of Theorem `bile`.**  For `d ≥ 2` and
`2 ≤ r < 2d/(d-1)` there are an intermediate exponent `q` and a weight `θ` with
`r < q < 2d/(d-1)`, `1 < q`, `0 < θ ≤ 1` and `1/r = θ/1 + (1-θ)/q` (so that log-convexity of the
`L^p` norms interpolates between `L^1` and `L^q`, and the gain at `L^1` survives with exponent
`θ > 0`). -/
theorem exists_interp_theta_clean {d r : ℝ} (hd : 2 ≤ d) (hr : 2 ≤ r)
    (hrd : r < 2 * d / (d - 1)) :
    ∃ q θ : ℝ, r < q ∧ q < 2 * d / (d - 1) ∧ 1 < q ∧ 0 < θ ∧ θ ≤ 1 ∧
      1 / r = θ / 1 + (1 - θ) / q := by
  set q : ℝ := (r + 2 * d / (d - 1)) / 2 with hq
  have hd1 : 1 < d := by linarith
  have hMgt : r < 2 * d / (d - 1) := hrd
  have hrpos : 0 < r := by linarith
  have hqgt : r < q := by
    simp only [hq]
    linarith
  have hqlt : q < 2 * d / (d - 1) := by
    simp only [hq]
    linarith
  have hq1 : 1 < q := by
    simp only [hq]
    linarith
  have hqpos : 0 < q := by linarith
  have h1q : (1 : ℝ) / q < 1 / r := by
    rw [div_lt_div_iff₀ hqpos hrpos]
    linarith
  have h1q1 : (1 : ℝ) / q < 1 := by
    rw [div_lt_one hqpos]
    linarith
  have h1r1 : (1 : ℝ) / r ≤ 1 := by
    rw [div_le_one hrpos]
    linarith
  refine ⟨q, (1 / r - 1 / q) / (1 - 1 / q), hqgt, hqlt, hq1, ?_, ?_, ?_⟩
  · exact div_pos (by linarith) (by linarith)
  · rw [div_le_one (by linarith : (0 : ℝ) < 1 - 1 / q)]
    linarith
  · have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqpos
    have hq1' : (q : ℝ) - 1 ≠ 0 := by linarith
    have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hrpos
    rw [div_one]
    have h1 : (1 : ℝ) - 1 / q = (q - 1) / q := by field_simp
    rw [h1]
    field_simp
    ring

/-! ## The interpolation with the Ionescu--Wainger minor-arc hypothesis -/

/-- **`L^r` interpolation of the arithmetic bilinear estimate** (Krause--Mirek--Tao, §10), with the
minor-arc hypothesis in its *Ionescu--Wainger* form `MdlIwMinorArc`: if
`A(f,g) = polyBilinearAverageZMod X P Q f g` is bounded on `L^1` by `ε ‖f‖₂‖g‖₂` on
minor-arc data and on `L^q` by `C ‖f‖₂‖g‖₂` unconditionally (`1 < q`), then it is bounded on `L^r`
by `ε^θ C^{1-θ} ‖f‖₂‖g‖₂` for `1/r = θ/1 + (1-θ)/q`, `0 ≤ θ ≤ 1`. -/
theorem bileInterpIwClean (P : Polynomial ℤ) (Q : ℕ) [NeZero Q] {ρ : ℝ} {l : ℕ}
    {q r θ ε C : ℝ} (hq : 1 < q) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hrel : 1 / r = θ / 1 + (1 - θ) / q) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (h1 : ∀ f g : ZMod Q → ℂ, (MdlIwMinorArc ρ l Q f ∨ MdlIwMinorArc ρ l Q g) →
      Work.Analysis.Concentration.LpNormZMod Q 1
          (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f g)
        ≤ ε * Work.Analysis.Concentration.LpNormZMod Q 2 f *
            Work.Analysis.Concentration.LpNormZMod Q 2 g)
    (h2 : ∀ f g : ZMod Q → ℂ,
      Work.Analysis.Concentration.LpNormZMod Q q
          (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f g)
        ≤ C * Work.Analysis.Concentration.LpNormZMod Q 2 f *
            Work.Analysis.Concentration.LpNormZMod Q 2 g) :
    ∀ f g : ZMod Q → ℂ, (MdlIwMinorArc ρ l Q f ∨ MdlIwMinorArc ρ l Q g) →
      Work.Analysis.Concentration.LpNormZMod Q r
          (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f g)
        ≤ ε ^ θ * C ^ (1 - θ) * Work.Analysis.Concentration.LpNormZMod Q 2 f *
            Work.Analysis.Concentration.LpNormZMod Q 2 g := by
  intro f g hsup
  have hLf : 0 ≤ Work.Analysis.Concentration.LpNormZMod Q 2 f := lpNormZMod_nonneg' Q 2 f
  have hLg : 0 ≤ Work.Analysis.Concentration.LpNormZMod Q 2 g := lpNormZMod_nonneg' Q 2 g
  have hX : 0 ≤ Work.Analysis.Concentration.LpNormZMod Q 2 f *
      Work.Analysis.Concentration.LpNormZMod Q 2 g := mul_nonneg hLf hLg
  have hn1 : Work.Analysis.Concentration.LpNormZMod Q 1
      (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f g)
      ≤ ε * (Work.Analysis.Concentration.LpNormZMod Q 2 f *
          Work.Analysis.Concentration.LpNormZMod Q 2 g) := by
    have h := h1 f g hsup
    rwa [mul_assoc] at h
  have hn2 : Work.Analysis.Concentration.LpNormZMod Q q
      (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f g)
      ≤ C * (Work.Analysis.Concentration.LpNormZMod Q 2 f *
          Work.Analysis.Concentration.LpNormZMod Q 2 g) := by
    have h := h2 f g
    rwa [mul_assoc] at h
  have hnT1 : 0 ≤ Work.Analysis.Concentration.LpNormZMod Q 1
      (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f g) :=
    lpNormZMod_nonneg' Q 1 _
  have hnTq : 0 ≤ Work.Analysis.Concentration.LpNormZMod Q q
      (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f g) :=
    lpNormZMod_nonneg' Q q _
  have hlog := Work.Analysis.Paraproduct.LpNormZMod_logconvex (Q := Q) (q := q) (r := r)
    (θ := θ) hq hθ0 hθ1 hrel
    (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f g)
  calc Work.Analysis.Concentration.LpNormZMod Q r
        (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f g)
      ≤ (Work.Analysis.Concentration.LpNormZMod Q 1
            (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f g)) ^ θ *
          (Work.Analysis.Concentration.LpNormZMod Q q
            (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f g)) ^ (1 - θ) :=
        hlog
    _ ≤ (ε * (Work.Analysis.Concentration.LpNormZMod Q 2 f *
            Work.Analysis.Concentration.LpNormZMod Q 2 g)) ^ θ *
          (C * (Work.Analysis.Concentration.LpNormZMod Q 2 f *
            Work.Analysis.Concentration.LpNormZMod Q 2 g)) ^ (1 - θ) :=
        mul_le_mul (Real.rpow_le_rpow hnT1 hn1 hθ0)
          (Real.rpow_le_rpow hnTq hn2 (sub_nonneg.mpr hθ1))
          (Real.rpow_nonneg hnTq _) (Real.rpow_nonneg (mul_nonneg hε hX) _)
    _ ≤ ε ^ θ * C ^ (1 - θ) * Work.Analysis.Concentration.LpNormZMod Q 2 f *
          Work.Analysis.Concentration.LpNormZMod Q 2 g :=
        rpow_interp_arith' hε hC hLf hLg

/-! ## The unconditional `L^q` endpoint, as a named predicate -/

/-- **The unconditional `L^q` endpoint of Theorem `bile`** (the paper's (avg-1)) for a fixed
exponent `q`: the bilinear arithmetic average maps `L² × L²` into `L^q` with a constant *uniform in
the modulus* `Q`.  This is the only ingredient of Theorem `bile` for `r > 1` that is not available
in the library yet: it is proved in the paper from the Appendix C concentration estimates on the
fibres of `P`, via the CRT (`Work.Analysis.Concentration.fiberLpBound_prime_pow`,
`fiberLpBound_mul_of_coprime`, `Work.Analysis.Paraproduct.bilinearAverageLq_of_fiber`), and the
in-flight files `KMTPlan/A6/BilinearAverageLqUniform.lean` /
`Analysis/Paraproduct/BilinearAverageLq_allQ_of_primePow.lean` are attempts at it. -/
def LqEndpointUniform (P : Polynomial ℤ) (q : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℕ) [NeZero Q],
    Work.Analysis.Concentration.BilinearAverageLq P Q q C

/-! ## Theorem `bile` for `2 ≤ r < 2d/(d-1)` -/

/-- **Theorem `bile` for `2 ≤ r < 2d/(d-1)`, modulo the unconditional `L^q` endpoint.**  Given the
`r = 1` base estimate with gain (from `ImprovKMT`, via `MdlBileR1OfImprov`) and the endpoint
`LqEndpointUniform` at some `q` with `Hmm`, this is exactly the statement of the area's target
`Work.KMTPlan.A6.BileGeneralR`: the arithmetic bilinear estimate at the exponent `r` under the
Ionescu--Wainger minor-arc hypothesis, with gain `2^{-(c₁θ)l}` and constant uniform in `Q` and
`l`. -/
theorem MdlBileGeneralR_of_LqEndpoint (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hEnd : ∀ q : ℝ, 1 ≤ q →
      q < 2 * (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1) → LqEndpointUniform P q)
    (hI : Work.KMTContract.ImprovKMT P) (r : ℝ) (hr : 2 ≤ r)
    (hrd : r < 2 * (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1)) :
    ∃ c : ℝ, 0 < c ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, 0 < C ∧
      ∀ (Q : ℕ) [NeZero Q] (l : ℕ) (f g : ZMod Q → ℂ),
        (MdlIwMinorArc ρ l Q f ∨ MdlIwMinorArc ρ l Q g) →
        Work.Analysis.Concentration.LpNormZMod Q r
            (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f g)
          ≤ C * (2 : ℝ) ^ (-(c * (l : ℝ))) *
              Work.Analysis.Concentration.LpNormZMod Q 2 f *
              Work.Analysis.Concentration.LpNormZMod Q 2 g := by
  obtain ⟨c₁, hc₁, hbile1⟩ := MdlBileR1OfImprov P hd hI
  have hdR : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
  obtain ⟨q₀, θ, _hrq, hqM, hq1, hθpos, hθle, hrel⟩ :=
    exists_interp_theta_clean (d := (P.natDegree : ℝ)) hdR hr hrd
  refine ⟨c₁ * θ, mul_pos hc₁ hθpos, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨C₁, hC₁pos, hC₁⟩ := hbile1 ρ hρ hρ1
  obtain ⟨C₂, hC₂pos, hC₂⟩ := hEnd q₀ hq1.le hqM
  refine ⟨C₁ ^ θ * C₂ ^ (1 - θ),
    mul_pos (Real.rpow_pos_of_pos hC₁pos θ) (Real.rpow_pos_of_pos hC₂pos (1 - θ)), ?_⟩
  intro Q hNZ l f g hm
  have h1 : ∀ f' g' : ZMod Q → ℂ, (MdlIwMinorArc ρ l Q f' ∨ MdlIwMinorArc ρ l Q g') →
      Work.Analysis.Concentration.LpNormZMod Q 1
          (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f' g')
        ≤ (C₁ * (2 : ℝ) ^ (-(c₁ * (l : ℝ)))) *
            Work.Analysis.Concentration.LpNormZMod Q 2 f' *
            Work.Analysis.Concentration.LpNormZMod Q 2 g' :=
    fun f' g' h => hC₁ Q l f' g' h
  have h2 : ∀ f' g' : ZMod Q → ℂ,
      Work.Analysis.Concentration.LpNormZMod Q q₀
          (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f' g')
        ≤ C₂ * Work.Analysis.Concentration.LpNormZMod Q 2 f' *
            Work.Analysis.Concentration.LpNormZMod Q 2 g' :=
    fun f' g' => hC₂ Q f' g'
  have hεpos : (0 : ℝ) ≤ C₁ * (2 : ℝ) ^ (-(c₁ * (l : ℝ))) :=
    mul_nonneg (le_of_lt hC₁pos)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(c₁ * (l : ℝ))))
  have hmain := bileInterpIwClean (P := P) (Q := Q) (ρ := ρ) (l := l) (q := q₀) (r := r)
    (θ := θ) (ε := C₁ * (2 : ℝ) ^ (-(c₁ * (l : ℝ)))) (C := C₂)
    hq1 hθpos.le hθle hrel hεpos hC₂pos.le h1 h2 f g hm
  have hεθ : (C₁ * (2 : ℝ) ^ (-(c₁ * (l : ℝ)))) ^ θ
      = C₁ ^ θ * (2 : ℝ) ^ (-((c₁ * θ) * (l : ℝ))) := by
    rw [Real.mul_rpow (le_of_lt hC₁pos)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(c₁ * (l : ℝ)))),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      show -(c₁ * (l : ℝ)) * θ = -((c₁ * θ) * (l : ℝ)) from by ring]
  calc Work.Analysis.Concentration.LpNormZMod Q r
        (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f g)
      ≤ (C₁ * (2 : ℝ) ^ (-(c₁ * (l : ℝ)))) ^ θ * C₂ ^ (1 - θ) *
          (Work.Analysis.Concentration.LpNormZMod Q 2 f *
            Work.Analysis.Concentration.LpNormZMod Q 2 g) := by
        simpa only [mul_assoc] using hmain
    _ = (C₁ ^ θ * C₂ ^ (1 - θ)) * (2 : ℝ) ^ (-((c₁ * θ) * (l : ℝ))) *
          (Work.Analysis.Concentration.LpNormZMod Q 2 f *
            Work.Analysis.Concentration.LpNormZMod Q 2 g) := by
        rw [hεθ]; ac_rfl
    _ = (C₁ ^ θ * C₂ ^ (1 - θ)) * (2 : ℝ) ^ (-((c₁ * θ) * (l : ℝ))) *
          Work.Analysis.Concentration.LpNormZMod Q 2 f *
          Work.Analysis.Concentration.LpNormZMod Q 2 g := by ac_rfl

end

end Work.KMTPlan.A6
