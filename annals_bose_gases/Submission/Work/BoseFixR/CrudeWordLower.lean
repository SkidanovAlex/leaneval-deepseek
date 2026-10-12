import ChallengeDeps
import Submission.Work.BoseFixR.Defs
import Submission.Work.BoseFixR.WordBridgeId
import Submission.Work.BoseKinLoc.Word.kinFormB_nonneg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/CrudeWordLower` — SKELETON: the requested crude word bound

**Requested statement** (kept verbatim at the end of this file, `sorry`):

`∃ C ≥ 0, ∀ n, ∀ μ > 0, ∀ Ψ : X n → ℝ` smooth,
`-(C·μ·(a v)·n)·normB v μ n Ψ ≤ wordB v h μ n Ψ`,  `ℓ = sideAt μ (a v)`.

## VERDICT: the statement is FALSE (it is missing the dilute régime `R ≤ ℓ·chiR0`)

The *intended* proof of this bound is the one every kernel bound of this corpus uses: split
`wordB = kinFormB + ∫_{abox} Ψ²·potWordU` (definitional, `BoseKinLoc.boxFormB`), drop the
non-negative pair term (`wLoc_zero_nonneg` below), keep `kinFormB ≥ 0`, and bound the
chemical (one-body) kernel by the fibre bound (`fibre_wLoc_g0_abs_le` below — the régime
hypothesis in action):

`|K(z)| := |∫_y wLoc ℓ (g₀) 0 z y dy| ≤ chiSup²·2·∫|g₀| = chiSup²·2·8π(a v) =: C_a`.

With that, `wordB ≥ -μ·n·C_a·normB`, i.e. the statement holds with `C = chiSup²·2·8π`.  The
hypothesis `R ≤ ℓ·chiR0` is used *only* through the fibre bound: it is what gives
`(χ⋆χ)((x−y)/ℓ) ≥ 1/2` on the support of `g₀`, hence `|wScaled ℓ g₀| ≤ 2|g₀|`.

**Without it the bound is false.**  Write `ℓ = sideAt μ (a v)`, `g := g₀ = v(1−ω) ≥ 0` a.e.
with `∫g = 8π(a v)`, and let `χ` be the corpus bump (`CubicChi.chi`: radial, smooth,
support the closed ball of radius `1/2`, `χ(0) > 0`).  The chemical kernel is

`K(x) = χ(x/ℓ)·∫_z g(z)·χ((x−z)/ℓ)/(χ⋆χ)(z/ℓ) dz`.

The mechanism is that `χ⋆χ` vanishes at the *boundary of its support* faster than `χ²`: the
overlap of two balls of radius `1/2` at centre distance `1−s` is a lens of volume `≍ s²` on
which the integrand is `≍ s^{2p}` (`p` = vanishing order of `χ` at `‖x‖ = 1/2`), so

`(χ⋆χ)(1−s) ≍ c·s^{2p+2}`,   while   `χ(w/2)² ≍ s^{2p}`   (`‖w‖ = 1−s`),

i.e. the ratio `χ(u)χ(u−w)/(χ⋆χ)(w)` is unbounded (`≍ s^{-2}`).  Hence for potentials whose
`g₀` is concentrated in the *outer* part of the support the kernel is not bounded by a
multiple of `a v` once the box side is comparable with the support radius:

* take `v` non-negative, radial, `L¹`, `ScatSol`, with `g₀` supported in a thin shell
  `{R−η ≤ ‖z‖ ≤ R}` (the constructive pair `v = g̃/(1−w₀)`, `w₀` the Newton potential of a
  shell bump `g̃` with small `sup g̃`, realises this with no appeal to the existence of
  scattering solutions — `FINDING_low_particle_bound.md` §3);
* choose `μ` with `ℓ = sideAt μ (a v) = R + ε`, `s₀ := 1 − R/ℓ = ε/(R+ε)`, and a shell of
  width `≈ ε` so that its `s = 1 − ‖w‖`-range is `[s₀, 2s₀]`;
* then at `x* = ℓ(1/2 − δ)ê`, `δ = s₀/(p+2)` (an interior point of the box `abox 1 ℓ`),

`K(x*)/(8π a v) ≍ const_p/s₀ → ∞`  (`s₀ → 0`),   `const_p = p^p (p+1)^{p+1}/(p+2)^{2p+1}`.

The computation is elementary and order-independent.  With `w = v/κ`, `u := x/ℓ`, `s := 1 − ‖w‖`
and `G(1−s) := g₀(ℓ·(1−s)ê)` (radial), the `θ`-integral is exact,

`∫_0^π sinθ·χ(|u−v(θ)|)dθ = (F(‖u‖+‖v‖) − F(|‖u‖−‖v‖|))/(‖u‖‖v‖)`,   `F′ = t χ(t)`,

and it contributes `(s−δ)^{p+1}/(p+1)` near the tangency `|u−v| = 1/2`; the angular
Jacobian contributes the geometrical factor and `(χ⋆χ)(1−s) ≍ c s^{2p+2}` the denominator, so
`K(x*) ≈ χ(u)·ℓ³·2π/u·∫ G(s)(s−δ)^{p+1}/((p+1) c s^{2p+2}) ds`, maximised over `δ ∈ (0,s₀)` at
`δ = s₀/(p+2)` with value `≍ 8π(a v)·const_p/s₀`.  Numerically (with `χ(r) = (1/2−r)₊`,
`p = 1`, and the analytic `(χ⋆χ)(1−s) = πs⁴/48`, which reproduces the exact convolution at
`s = 10⁻¹` to 6%): `K(x*)/(8π a v) = 53.8, 5379, 53779` at `s₀ = 10⁻³, 10⁻⁴, 10⁻⁵`, with the
maximiser at `δ ≈ 0.33 s₀ = s₀/(p+2)` — as predicted.  (For the corpus's own bump the
vanishing order `p` is finite but different, which only changes `const_p`: the divergence is
`1/s₀` for every `p`, and also for super-flat bumps, where the two exponentials cancel and the
lens-volume factor `s²` alone produces the divergence.)

Hence, with `n = 1` and a smooth `Ψ` of `L²`-mass one concentrated at `x*`
(`normB = 1`, no pair term for `n = 1`),

`wordB ≈ kinFormB(Ψ) − μ·K(x*)`,

and `-(C μ (a v))·1 ≤ wordB` fails for every fixed `C` once `s₀ < const_p·8π/C`: the
chemical term is `≫ μ·C·(a v)` while `kinFormB(Ψ)` is bounded (fix `Ψ` of width `≈ ℓ`; the
kinetic symbols stay bounded as `ε → 0`).  (All integrands occurring in this configuration are
integrable on their compact supports — the singularity of `1/(χ⋆χ)` at `‖z‖ = ℓ` lies
strictly outside the support of `g₀` when `ℓ > R` — so this is a genuine failure of the
Lean statement, not an artefact of the `∫ = 0` convention for non-integrable functions.)

**The failure window is exactly the régime-violating one.**  Since `ℓ = a v·(μ (a v)³)^{−163/323}`
(`Work.BoseBox.boxSide`, `mu_ell_cube_fsParams`), the box side takes *every* positive value
as `μ` ranges over `(0,∞)`, and the counterexample uses `R < ℓ < R/chiR0`, i.e.

`(a v·chiR0/R)^{323/163} < μ (a v)³ < (a v/R)^{323/163}`

(this interval is non-empty because `chiR0 < 1` — `χ⋆χ` vanishes outside `ball 0 1` — and
`a v ≤ R`, `av_bounds_weak`).  On that window the fibre bound's hypothesis fails
(`(χ⋆χ)(z/ℓ) ≥ 1/2` on the support of `g₀` needs `ℓ ≥ R/chiR0`), the kernel is finite but
unbounded (`≍ 1/s₀ = ℓ/(ℓ−R)`), and the requested inequality fails.  Note that no purely
"small-`μ`" restriction of the form `μ (a v)³ ≤ ε₀` excludes the window: choosing
`ε₀ < (a v/R)^{323/163}` does, and that is precisely the rôle of the régime hypothesis.

The same defect (no relation between `R` and `ℓ = sideAt μ (a v)` in the hypothesis list)
was already found and machine-checked for the sibling statement
`Work.BoseFixR.low_particle_bound` (`FINDING_low_particle_bound.md`), whose §4 recommends
exactly this repair.  Every kernel bound in the corpus carries the same hypothesis:
`KernelFibreBound.fibre_integral_abs_le`, `fibre_acube_abs_le`, `wScaled_abs_le_two`,
`LocPotential.locPotential_*`, `SmallBoxA0.pot_sharp_summary`, `q0word_sharp`, …

## The repair

`∃ C ≥ 0, ∀ n μ > 0, Adm v 1 μ → R ≤ sideAt μ (a v)·chiR0 → ∀ Ψ smooth,
  -(C·μ·(a v)·n)·normB ≤ wordB`

is true and is proved by the route above (`Adm` supplies the parameter facts
`0 < a v, 0 < d, 0 < s, 0 ≤ ε_T ≤ 1, 0 ≤ b` — `BoseBox.paramsAt_facts` — so that the
kinetic bound applies; the two file-local lemmas below give the other two ingredients).
Both corrected forms are **proved** (sorry-free, axiom-clean) and consume the two helper
lemmas of this file:

* `Submission/Work/BoseFixR/CrudeWordLowerRegime.lean`
  (`Work.BoseFixR.CrudeWordLowerRegime`): `Adm v 1 μ` (`0 < μ`, `μ (a v)³ ≤ 1`,
  `ParamsOK`) together with the régime, constant `C = chiSup²·2·8π`;
* `Submission/Work/BoseFixR/CrudeWordLowerRegimeOnly.lean`
  (`Work.BoseFixR.CrudeWordLowerRegimeOnly`): the régime hypothesis *alone* — the minimal
  repair of the statement below.

Note that adding *diluteness* alone (`μ (a v)³ ≤ ε₀` for a fixed `ε₀`, e.g. `ε₀ = 1`) does
**not** repair the statement: the counterexample of §"failure window" lives at
`μ (a v)³ ∈ ((a v·chiR0/R)^{323/163}, (a v/R)^{323/163})`, i.e. inside any diluteness
régime with `ε₀ ≥ (a v/R)^{323/163}`; the smallness threshold must depend on `a v/R` (the
régime hypothesis is the clean way of saying this).

## Status of this file

`SKELETON` — the requested `CrudeWordLower` is kept verbatim with `sorry`; everything else
in this file is `sorry`-free.  It is imported only by the two corrected files
(`CrudeWordLowerRegime`, `CrudeWordLowerRegimeOnly`), which re-use its two helper lemmas.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false


/-! ## 1. The two true ingredients of the intended (régime-restricted) proof -/

/-- **The localised two-body kernel is pointwise non-negative** for a non-negative
potential.  This is what lets the pair term `Σ_{i<j}wLoc ℓ v 0 (xᵢ,xⱼ)` be dropped from the
lower bound for `wordB`.  (No `.chiR0`-régime is needed: `χ ≥ 0`, `χ⋆χ ≥ 0`, `v ≥ 0` and
Lean's `x/0 = 0`.) -/
lemma wLoc_zero_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v) (ℓ : ℝ) (a b : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ wLoc ℓ v 0 a b := by
  have h1 : 0 ≤ chiU ℓ 0 a := by
    simpa [chiU] using chi_nonneg ((ℓ⁻¹) • a - 0)
  have h2 : 0 ≤ chiU ℓ 0 b := by
    simpa [chiU] using chi_nonneg ((ℓ⁻¹) • b - 0)
  have h3 : 0 ≤ convScale ℓ (a - b) := by
    simpa [convScale] using conv3chi_nonneg ((ℓ⁻¹) • (a - b))
  have h4 : 0 ≤ wScaled ℓ v (a - b) := by
    rw [wScaled]
    exact div_nonneg (hv (a - b)) h3
  rw [wLoc]
  exact mul_nonneg (mul_nonneg h1 h4) h2

/-- **The one-body (fibre) bound in the dilute régime** (the whole-space integral of the
localised kernel): for any integrable `g` vanishing outside `ball 0 R` and any
`R ≤ ℓ·chiR0`,

`|∫_y wLoc ℓ g 0 z y dy| ≤ chiSup²·2·∫|g|`.

This is `KernelFibreBound.fibre_integral_abs_le` transported from `wPair` to `wLoc` at
`u = 0` (they are the same kernel: `chiU ℓ 0 = chiScale ℓ`). -/
lemma fibre_wLoc_zero_abs_le {R ℓ : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * chiR0) {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : MeasureTheory.Integrable g)
    (hgsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → g z = 0) (z : EuclideanSpace ℝ (Fin 3)) :
    |∫ y : EuclideanSpace ℝ (Fin 3), wLoc ℓ g 0 z y| ≤ chiSup ^ 2 * 2 * ∫ y : EuclideanSpace ℝ (Fin 3), |g y| := by
  have h := fibre_integral_abs_le (ℓ := ℓ) (R := R) hℓ hR hRℓ hg hgsupp z
  have heq : (fun y : EuclideanSpace ℝ (Fin 3) => wLoc ℓ g 0 z y) = fun y : EuclideanSpace ℝ (Fin 3) => wPair ℓ g z y := by
    funext y
    simp [wLoc, wPair, chiU, chiScale, sub_zero]
  rw [heq]
  exact h

/-- The fibre bound at the chosen numerator `g₀ = v(1−ω)`, in the form in which it enters
the crude bound: `|∫_y wLoc ℓ (g₀) 0 z y dy| ≤ chiSup²·2·8π(a v) =: C_a` — the constant
the requested statement's `C = chiSup²·2·8π` comes from. -/
lemma fibre_wLoc_g0_abs_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ} (h : Work.UBB.ScatSol v)
    (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hℓ : 0 < ℓ)
    (hRℓ : R ≤ ℓ * chiR0) (z : EuclideanSpace ℝ (Fin 3)) :
    |∫ y : EuclideanSpace ℝ (Fin 3), wLoc ℓ (g0 v h) 0 z y| ≤ chiSup ^ 2 * 2 * (8 * π * a v) := by
  have hbound := fibre_wLoc_zero_abs_le (R := R) (ℓ := ℓ) hℓ hR.le hRℓ
    (g0_integrable (v := v) hR hv_supp h)
    (fun z hz => g0_zero_of_norm_ge (v := v) hv_supp hz h) z
  have hnn : ∀ᵐ z : EuclideanSpace ℝ (Fin 3), 0 ≤ g0 v h z := g0_nonneg_ae hR hv hvrad hv_supp h
  have hEq : (∫ z : EuclideanSpace ℝ (Fin 3), |g0 v h z|) = ∫ z : EuclideanSpace ℝ (Fin 3), g0 v h z := by
    apply integral_congr_ae
    filter_upwards [hnn] with z hz
    exact abs_of_nonneg hz
  rw [hEq, g0_integral (v := v) hR hv_supp h] at hbound
  exact hbound

/-! ## 2. The requested statement (FALSE as written; see the module docstring) -/

theorem CrudeWordLower {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ} {μ : ℝ}, 0 < μ →
      ∀ {Ψ : Submission.BoseGases.X n → ℝ}, ContDiff ℝ (⊤ : ℕ∞) Ψ →
      -(C * μ * _root_.BoseGases.a v * (n : ℝ)) * Work.BoseBoxFix.normB v μ n Ψ
        ≤ Work.BoseBoxFix.wordB v h μ n Ψ := by sorry

end Work.BoseFixR
