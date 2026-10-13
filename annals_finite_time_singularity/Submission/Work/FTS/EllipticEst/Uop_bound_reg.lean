/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Uop_bound_reg` — the `U`-shape of the residual in the interior class `EllHypQ`

This module proves

  `Work.FTS.EllipticEst.Uop_bound_reg`:

there is a universal `C > 0` with, for every `0 < α ≤ 1/4` and every datum `(F,Ψ)` of the
interior class `EllHypQ α 4` whose *straightened* solution `Ψ + Gsing α F · sin 2θ` is
orthogonal to `sin θ cos²θ`,

  `|Uop α (EllResid α F Ψ) / sin 2θ|_{ℋ⁴} ≤ C |F|_{ℋ⁴}`,

together with the interior smoothness and the honesty (`HkMem`) of the quotient.  This is
Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the incompressible Euler
equations on `ℝ³`*, Annals of Math. **194** (2021), §Modulation tex 1472 (`I^𝒩₂`):

  `|(1/sin 2θ)·U(Φ_g - (1/4α) sin 2θ · L₁₂(g))|_{ℋ⁴} ≤ C |g|_{ℋ⁴}`,

where `U(Ψ) = -3Ψ - α z ∂_zΨ` is the coefficient of `∂_θΩ` in the self-similar vorticity
equation (paper (Relations), tex 1320) and `Φ_g - (1/4α) sin 2θ L₁₂(g)` is the residual
`EllResid` of Theorem `RemovingL12`.

## VERDICT (added after the reduction was built): the statement is FALSE as stated

The first conjunct (`SmoothQuad` of the quotient) fails for data of the class.  The
counterexample is **fully formalised, `sorry`-free and axiom-clean** in
`Submission/Work/FTS/EllipticEst/RegQ/Refute/` (see `CexFinal.lean`, and the negations
`RegQ.EllResid_smoothQuad_reg_orth_is_false`, whose `#print axioms` is
`[propext, Classical.choice, Quot.sound]`):

* `F = cexF`, the *pinch* profile `cexF r θ = ρ(θ·(-r)^{-1/4})` for `r < 0` and `0` for `r ≥ 0`
  (`ρ` a bump), `Ψ = PsiCex z θ = Real.smoothTransition (-z³)·(θ⁻²ψ(θ))`;
* `EllHypQ α 4 cexF PsiCex` holds for every `α` (`ellHypQ_cexF_PsiCex`): everything in the class
  is evaluated on the closed half-plane `z ≥ 0`, where both functions (and all their derivatives)
  vanish identically, and `bslOp α PsiCex = cexF` holds on `z > 0` because both sides vanish
  there;
* `OrthCond (Ψ + Gsing α F · sin 2θ)` holds (`orthCond_cexF_PsiCex`): on `z ≥ 0` both terms
  vanish, and on `z < 0` the slice `θ ↦ PsiCex z θ·sinθcos²θ` is *not* integrable, so by
  Mathlib's totalised-integral convention the whole integrand has Bochner integral `0`;
* but `L12dens cexF r ≤ -(3/8)(-r)^{-1/2}` on `(-1/16,0)` and `= 0` on `(0,∞)`, so
  `L12 cexF z ≤ -(3/4)√(-z)` for `z ∈ (-1/16,0)` and `= 0` for `z ≥ 0`:
  `L12 (cexF)` has a square-root cusp at `0`, `EllResid α cexF PsiCex` is not differentiable at
  `(0,π/4)` (`not_smoothQuad_EllResid_cexF_PsiCex`), and the quotient
  `Uop α (EllResid)/sin 2θ` inherits the cusp
  (`= -3Ψ/sin2θ - αz∂_zΨ/sin2θ + (3/(4α))L12 F + (z/4)(L12 F)′`, and `L12 F′ ≥ (3/8)(-z)^{-1/2}`
  on `(-1/16,0)` while the function vanishes for `z > 0`), so it is not even differentiable at
  `(0,π/4)`.

**Root cause.**  `SmoothQuad` demands `C^∞` across `z = 0` on both sides, but `EllHypQ` ties `F`
to `Ψ` only on the open quadrant `z > 0` (`IsBslSol`), while `HkMem`/`BdryTraces`/`L2Mem` are
evaluated only at `z ∈ [0,∞)`; and `OrthCond` constrains only the *values* of the angular
moments, and can be met by the junk value of a non-integrable Bochner integral.  The intended
data (the canonical solution of N1, whose `F` is `bslOp α Ψ` on a whole neighbourhood of the
closed quadrant) do satisfy the paper's estimate; the statement needs one of:

1. the off-quadrant equation `∀ z ∈ Ioi (-1), ∀ θ ∈ Ioo 0 (π/2), bslOp α Ψ z θ = F z θ`;
2. smoothness of the angular moments, `∀ m, ContDiffOn ℝ m (Fstar F) (Ioi (-1))`;
3. honesty of the orthogonality (an integrable moment on the whole line, not the totalised one).

See `Submission/Work/FTS/EllipticEst/NOTES_Uop_bound_reg.md` for the full analysis (including two
traps in the `Real.rpow` convention at negative bases that invalidate the first two derivations
attempted there).

## The route (the paper's, tex 1472–1481)

Write `W := EllResid α F Ψ` and `g₀ := Uop α W / sin 2θ`.  Then

* **(division by `sin 2θ`)** `|Φ/sin 2θ|_{ℋ⁴} ≤ C|∂_θΦ|_{ℋ⁴}` for any `Φ` vanishing on the two
  angular boundary lines — the paper's Proposition `DivisionBySin` (`Work.Elliptic.DivisionBySin`,
  general `k` in `Work.FTS.EllipticEst.divSin_Hk_gen`).  Here `Φ = Uop α W`, which does vanish
  on the boundary (`VanishTheta_Uop_EllResid`, proved);
* **(transfer estimate)** `|∂_θ(Uop α W)|_{ℋ⁴} ≤ C(|F|_{ℋ⁴} + |∂_θθW|_{ℋ⁴}
  + α²|z²∂_zzΨ|_{ℋ⁴})`: split `∂_θ(U(W)) = -3∂_θW - α z ∂_θ∂_zW`, remove the single `∂_θ` by the
  slicewise angular Poincaré and the mixed term `αD_z∂_θW` by the weighted energy
  interpolation (the paper's §`H2` machinery);
* **(Theorem `RemovingL12`)** the two elliptic *diagonal* quantities on the right are bounded
  by `C|F|_{ℋ⁴}`: `α²|z²∂_zzΨ|_{ℋ⁴} + |∂_θθ(EllResid α F Ψ)|_{ℋ⁴} ≤ C|F|_{ℋ⁴}`.

The four sub-statements are stated below in the *interior* class (open quadrant, no
`Work.Spaces.SmoothNbhd`, i.e. no analyticity), which is the class of the frozen vocabulary
`Work.FTS.Nonlin.RegQ`: they are the `RegQ` restatements of the four lemmas of the `EllHyp`
chain (`ThetaU.pthU_EllResid_le`, `removingL12_fts`, `divSin_Hk_gen` and the smoothness of
`EllResid`).  Only the assembly is proved here; the four statements are the analytic input.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.EllipticEst.RegQ
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 0. Elementary closure facts -/

/-- `Work.FTS.LocData.SmoothQuad` (genuine `C^∞` on `z > -1`, `0 < θ < π/2`) restricts to
`SmoothOpen` (genuine `C^∞` on `z > 0`, `0 < θ < π/2`). -/
theorem smoothOpen_of_smoothQuad {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad f) : SmoothOpen f := by
  refine h.mono ?_
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := mem_Q0.mp (show (p.1, p.2) ∈ Q0 from hp)
  simp only [Work.Spaces.quadU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
  exact ⟨by linarith, hθ0, hθ1⟩

/-- Differences of `SmoothOpen` functions are `SmoothOpen`. -/
theorem smoothOpen_sub' {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) :
    SmoothOpen (fun z θ => f z θ - g z θ) := by
  rw [SmoothOpen] at hf hg ⊢
  have h : (Function.uncurry fun z θ => f z θ - g z θ)
      = (fun p : ℝ × ℝ => Function.uncurry f p) - (fun p : ℝ × ℝ => Function.uncurry g p) := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [h]
  exact ContDiffOn.sub hf hg

/-- Scalar multiples of `SmoothOpen` functions are `SmoothOpen`. -/
theorem smoothOpen_const_mul' (c : ℝ) {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) :
    SmoothOpen (fun z θ => c * f z θ) := by
  rw [SmoothOpen] at hf ⊢
  have h : (Function.uncurry fun z θ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [h]
  exact (contDiffOn_const (c := c) (s := Q0)).mul hf

/-- `Uop α f = -3f - α·D_zf` on the open quadrant, where `D_z = z ∂_z`. -/
theorem Uop_eq_neg_three_sub_Dz (α : ℝ) (f : ℝ → ℝ → ℝ) :
    Uop α f = fun z θ => -3 * f z θ - α * Work.Spaces.Dz f z θ := by
  funext z θ
  simp only [Uop, Work.Spaces.Dz]
  ring

/-- `SmoothOpen` of the `Uop`-expression for a `SmoothOpen` datum. -/
theorem smoothOpen_Uop {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) :
    SmoothOpen (Uop α f) := by
  rw [Uop_eq_neg_three_sub_Dz]
  have h1 : SmoothOpen (fun z θ => -3 * f z θ) := smoothOpen_const_mul' (-3) hf
  have h2 : SmoothOpen (fun z θ => α * Work.Spaces.Dz f z θ) :=
    smoothOpen_const_mul' α hf.Dz
  exact smoothOpen_sub' h1 h2

/-- `SmoothQuad` of the `Uop`-expression. -/
theorem smoothQuad_Uop {α : ℝ} {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad f) : Work.FTS.LocData.SmoothQuad (Uop α f) := by
  rw [Uop_eq_neg_three_sub_Dz]
  refine Work.FTS.LocData.smoothQuad_sub ?_ ?_
  · exact Work.FTS.LocData.smoothQuad_const_mul (-3) h
  · have h1 : Work.FTS.LocData.SmoothQuad (Work.Spaces.Dz f) := by
      simpa using Work.FTS.LocData.SmoothQuad.DzIter h 1
    exact Work.FTS.LocData.smoothQuad_const_mul α h1

/-- Division by `sin(2θ)` preserves `C^∞` on a set on which `sin(2θ) ≠ 0` (here the quadrant
`(-1,∞) × (0,π/2)`, where `2θ ∈ (0,π)`). -/
theorem smoothQuad_div_sinTwo {Φ : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad Φ) :
    Work.FTS.LocData.SmoothQuad (fun z θ => Φ z θ / Real.sin (2 * θ)) := by
  rw [Work.FTS.LocData.SmoothQuad] at h ⊢
  have hfun : (Function.uncurry fun z θ : ℝ => Φ z θ / Real.sin (2 * θ))
      = (fun p : ℝ × ℝ => Φ p.1 p.2)
        / (fun p : ℝ × ℝ => Real.sin (2 * p.2)) := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  refine h.div ?_ ?_
  · have hsin : ContDiff ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.sin (2 * θ)) := by
      fun_prop
    exact (hsin.comp_contDiffOn contDiffOn_snd :
      ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.sin (2 * p.2))
        Work.Spaces.quadU)
  · intro p hp
    simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp
    have h1 : 0 < 2 * p.2 := by linarith [hp.2.1]
    have h2 : 2 * p.2 < Real.pi := by linarith [hp.2.2, Real.pi_pos]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)

/-! ## 1. The four analytic inputs (RegQ restatements of the `EllHyp` chain) -/

/-- **Smoothness of the residual.**  `EllResid α F Ψ = Ψ - (1/4α) sin 2θ L₁₂(F)` is genuinely
`C^∞` on the open quadrant `z > -1`, `0 < θ < π/2` for the data of `EllHypQ` *together with the
orthogonality hypothesis*.

*Design note.*  `SmoothQuad` is `C^∞` on the two-sided strip `z ∈ (-1,0]` (only the angular
endpoints are excluded), so the statement needs `z ↦ L12 F z = 3∫_{(z,∞)} F⋆(F)(r)/r dr` to be
`C^∞` on `(-1,∞)`, whereas the class constrains `F` on `z < 0` only through `SmoothQuad F`
(`IsBslSol` speaks about the open quadrant `z > 0`, and `HkMem`/`BdryTraces`/`L2Mem` evaluate only
at `z ∈ [0,∞)`).

* **Without `OrthCond` the statement is false**: `RegQ/NOTES_EllResid_smoothQuad_reg_FALSE.md`
  exhibits `F(r,θ) = ρ(θ·(-r)^{-1/4})` for `r < 0`, `Ψ = 0` — `SmoothQuad` with every
  `HkMem`/`BdryTraces`/`L2Mem` field trivial (they live at `z ≥ 0`, where `F ≡ 0`) — yet
  `L12dens F r ≈ -c(-r)^{-1/2}` and `L12 F z ≈ -c'(-z)^{1/2}` has a square-root cusp at `0`.
* With `OrthCond` the two sides of the strip are coupled by an identity relating the tail integral
  of `F⋆(F)` to `F⋆(Ψ)` and to the "bar" integral of `F⋆(F)`; see
  `Submission/Work/FTS/EllipticEst/NOTES_Uop_bound_reg.md` §3 for the exact relation (and for the
  refutation of the *naive* reading that it forces a sign flip of `L12 F` across `z = 0`: Lean's
  `Real.rpow` is not multiplicative at negative bases, `Real.rpow_def_of_neg`).  Whether that
  coupling rules out the cusp is **open**; the statement is delegated as
  `RegQ.EllResid_smoothQuad_reg_orth`, and it is decidable from the data class alone, without the
  elliptic core.
-/
abbrev EllResidSmoothQuadStmt : Prop := ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 / 4 → EllHypQ α 4 F Ψ →
    Work.Elliptic.OrthCond (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) →
    Work.FTS.LocData.SmoothQuad (Work.Elliptic.EllResid α F Ψ)

/-- **The division by `sin 2θ` for the `U`-shape of the residual** (Elgindi's Proposition
`DivisionBySin`, tex 1293, applied as in tex 1478): for the data of `EllHypQ` (whose class
carries the angular boundary traces `BdryTraces`, so that the slices of the residual and of
`Uop α W` do tend to `0` at `θ = 0, π/2`), the quotient `Uop α W / sin 2θ` is honestly in `ℋ^k`
and its norm is bounded by the norm of `∂_θ(Uop α W)`.

*Design note.*  This step is stated for the residual's `U`-shape and **not** as the general
statement "`|Φ/sin 2θ|_{ℋ^k} ≤ C|∂_θΦ|_{ℋ^k}` for `Φ` smooth on the open quadrant with
`VanishTheta Φ`", which is **false**: a function that is a fixed smooth `z`-profile in `θ` on
the open quadrant and `0` on the two boundary lines satisfies `SmoothOpen`, `VanishTheta` and
`∂_θΦ = 0`, yet `Φ/sin 2θ` is not in `ℋ^k` (the same refutation as the one recorded for
`Work.FTS.EllipticEst.HkNorm_le_pth2_open` in
`Submission/Work/FTS/EllipticEst/HkNorm_le_pth2_open_counter.lean`).  The extra information the
argument needs is the *trace* of the angular slices at the endpoints, which `BdryTraces`
supplies (`sin(2θ)^{1-γ}` times the square of each mixed derivative of `Ψ`, `∂_θΨ`, `∂_θθΨ`,
`z²∂_zzΨ`, `Ψ/cos θ` and `F` tends to `0` at `θ → 0, π/2`). -/
abbrev DivSinUopStmt : Prop := ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 → EllHypQ α k F Ψ →
      Work.Elliptic.OrthCond
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) →
      Work.Spaces.HkMem α k (fun z θ =>
          Uop α (Work.Elliptic.EllResid α F Ψ) z θ / Real.sin (2 * θ)) ∧
        Work.Spaces.HkNorm α k (fun z θ =>
            Uop α (Work.Elliptic.EllResid α F Ψ) z θ / Real.sin (2 * θ))
          ≤ C * Work.Spaces.HkNorm α k
              (Work.Spaces.pth (Uop α (Work.Elliptic.EllResid α F Ψ)))

/-- **The transfer estimate for the `U`-shape of the residual** (§Modulation, tex 1471--1481):
the `ℋ^k`-norm of `∂_θ(Uop α (EllResid α F Ψ))` is bounded by the source and the two elliptic
diagonal quantities, and the quantity is honestly in `ℋ^k`. -/
abbrev PthUStmt : Prop := ∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 → EllHypQ α k F Ψ →
      Work.Elliptic.OrthCond (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) →
      Work.Spaces.HkMem α k
        (Work.Spaces.pth (Uop α (Work.Elliptic.EllResid α F Ψ))) ∧
        Work.Spaces.HkNorm α k (Work.Spaces.pth (Uop α (Work.Elliptic.EllResid α F Ψ)))
          ≤ C * (Work.Spaces.HkNorm α k F
              + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
              + α ^ 2 * Work.Spaces.HkNorm α k
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))

/-- **Theorem `RemovingL12`** (tex 1034) in the interior class: the elliptic a-priori estimate
on the two diagonal quantities of the residual. -/
abbrev RemovingL12Stmt : Prop := ∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 → EllHypQ α k F Ψ →
      Work.Elliptic.OrthCond (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) →
      α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ))
        ≤ C * Work.Spaces.HkNorm α k F

/-! ## 2. The assembly -/

/-- **The target shape from the four analytic inputs.**  With `Φ := Uop α (EllResid α F Ψ)`:

* `Φ` is `C^∞` on the open quadrant and vanishes on the two angular boundary lines, so the
  division estimate gives both `Φ/sin 2θ ∈ ℋ⁴` honestly and the bound by `|∂_θΦ|_{ℋ⁴}`;
* the transfer estimate bounds `|∂_θΦ|_{ℋ⁴}` by `|F|_{ℋ⁴} + |∂_θθW|_{ℋ⁴} + α²|z²∂_zzΨ|_{ℋ⁴}`;
* Theorem `RemovingL12` bounds the two diagonal quantities by `|F|_{ℋ⁴}`;
* the smoothness of the residual gives the interior `C^∞`-regularity of the quotient. -/
theorem uop_bound_of_pieces (h1 : EllResidSmoothQuadStmt) (h2 : DivSinUopStmt)
    (h3 : PthUStmt) (h4 : RemovingL12Stmt) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.EllHypQ α 4 F Ψ →
      Work.Elliptic.OrthCond
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) →
      Work.FTS.LocData.SmoothQuad (fun z θ =>
          Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α F Ψ) z θ / Real.sin (2 * θ)) ∧
        Work.Spaces.HkMem α 4 (fun z θ =>
          Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α F Ψ) z θ / Real.sin (2 * θ)) ∧
        Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α F Ψ) z θ / Real.sin (2 * θ))
          ≤ C * Work.FTS.Nonlin.Xn α F := by
  obtain ⟨C2, hC2pos, h2'⟩ := h2 4 (by norm_num)
  obtain ⟨C3, hC3pos, h3'⟩ := h3 4 (by norm_num)
  obtain ⟨C4, hC4pos, h4'⟩ := h4 4 (by norm_num)
  refine ⟨C2 * C3 * (1 + C4), by positivity, ?_⟩
  intro α F Ψ hα hα4 hHyp hOrth
  set W : ℝ → ℝ → ℝ := Work.Elliptic.EllResid α F Ψ with hW
  set Φ : ℝ → ℝ → ℝ := Uop α W with hΦ
  -- ### the smoothness of the residual
  have hWsq : Work.FTS.LocData.SmoothQuad W := h1 α F Ψ hα hα4 hHyp hOrth
  -- ### the division estimate: honesty of the quotient and the bound by `∂_θΦ`
  obtain ⟨hmemG, hleG⟩ := h2' α F Ψ hα hα4 hHyp hOrth
  -- ### the transfer estimate: honesty of `∂_θΦ` and the bound
  obtain ⟨hmemP, hleP⟩ := h3' α F Ψ hα hα4 hHyp hOrth
  -- ### Theorem RemovingL12 on the two diagonal quantities
  have hdiag := h4' α F Ψ hα hα4 hHyp hOrth
  -- ### the arithmetic
  have hFnn : 0 ≤ Work.Spaces.HkNorm α 4 F := Work.Spaces.HkNorm_nonneg α 4 F
  have hP2nn : 0 ≤ Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 W) :=
    Work.Spaces.HkNorm_nonneg α 4 _
  have hP3nn : 0 ≤ α ^ 2 * Work.Spaces.HkNorm α 4
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    mul_nonneg (sq_nonneg α) (Work.Spaces.HkNorm_nonneg α 4 _)
  have hsum : Work.Spaces.HkNorm α 4 F + Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 W)
      + α ^ 2 * Work.Spaces.HkNorm α 4 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      ≤ (1 + C4) * Work.Spaces.HkNorm α 4 F := by
    have h1' : Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 W)
        + α ^ 2 * Work.Spaces.HkNorm α 4 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        ≤ C4 * Work.Spaces.HkNorm α 4 F := by
      rw [add_comm]; exact hdiag
    linarith
  refine ⟨?_, hmemG, ?_⟩
  · -- smoothness of the quotient on the open quadrant
    have hΦsq : Work.FTS.LocData.SmoothQuad Φ := hΦ ▸ smoothQuad_Uop hWsq
    exact smoothQuad_div_sinTwo hΦsq
  · -- the norm bound
    calc Work.FTS.Nonlin.Xn α (fun z θ => Uop α W z θ / Real.sin (2 * θ))
        = Work.Spaces.HkNorm α 4 (fun z θ => Φ z θ / Real.sin (2 * θ)) := rfl
      _ ≤ C2 * Work.Spaces.HkNorm α 4 (Work.Spaces.pth Φ) := hleG
      _ ≤ C2 * (C3 * (Work.Spaces.HkNorm α 4 F + Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 W)
            + α ^ 2 * Work.Spaces.HkNorm α 4 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))) :=
          mul_le_mul_of_nonneg_left hleP (le_of_lt hC2pos)
      _ ≤ C2 * (C3 * ((1 + C4) * Work.Spaces.HkNorm α 4 F)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (le_of_lt hC3pos))
            (le_of_lt hC2pos)
      _ = C2 * C3 * (1 + C4) * Work.Spaces.HkNorm α 4 F := by ring

/-! ## 3. The four analytic inputs, and the target -/

theorem EllResid_smoothQuad_reg : EllResidSmoothQuadStmt := by
  intro α F Ψ hα hα4 hHyp hOrth
  sorry

theorem divSin_Uop_reg : DivSinUopStmt := by
  intro k hk
  sorry

theorem pthU_EllResid_reg : PthUStmt := by
  intro k hk
  sorry

theorem removingL12_reg : RemovingL12Stmt := by
  intro k hk
  sorry

theorem Uop_bound_reg : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.EllHypQ α 4 F Ψ →
    Work.Elliptic.OrthCond (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) →
    Work.FTS.LocData.SmoothQuad (fun z θ =>
        Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α F Ψ) z θ / Real.sin (2 * θ)) ∧
      Work.Spaces.HkMem α 4 (fun z θ =>
        Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α F Ψ) z θ / Real.sin (2 * θ)) ∧
      Work.FTS.Nonlin.Xn α (fun z θ =>
        Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α F Ψ) z θ / Real.sin (2 * θ))
        ≤ C * Work.FTS.Nonlin.Xn α F :=
  uop_bound_of_pieces EllResid_smoothQuad_reg divSin_Uop_reg pthU_EllResid_reg removingL12_reg

end Work.FTS.EllipticEst
