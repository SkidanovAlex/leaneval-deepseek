/-
Copyright: work module for the Elgindi finite-time singularity project.

# `bslOp α Ψ` is `C^∞` on the open quadrant for `Ψ` smooth near the quadrant

The certificate

  `Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp`:
`Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ)` for every
`Ψ` with `Work.Spaces.SmoothNbhd Ψ`.

This is needed because the source `F` of the elliptic problem is defined as `bslOp α Ψ`
on the open quadrant, while the estimates of §'Elliptic Regularity Estimates' of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021)

are stated for data in the *open-quadrant* class `SmoothOpen`
(`Submission/Work/FTS/EllipticEst/OpenQDefs.lean`).  Note that `bslOp α Ψ` is *not*
`SmoothNbhd`: the operator contains `Real.tan θ`, whose pole at `θ = π/2` lies inside the
neighbourhood `(-1,∞) × (-1, π/2+1)` of `SmoothNbhd`, and Lean's `Real.tan` is totalised
(`Real.tan (π/2) = 0`), so `θ ↦ bslOp α Ψ z θ` genuinely jumps at `θ = π/2`.  On the open
quadrant, however, `tan` is analytic, and all operations defining `Lzero`/`bslOp` preserve
`C^∞` there.

The proof is a purely algebraic bookkeeping argument:

* `smoothNbhd_smoothOpen_bsl` : `SmoothNbhd Ψ → SmoothOpen Ψ` (analyticity on the
  neighbourhood `(-1,∞) × (-1, π/2+1)` of `SmoothNbhd` restricts to `C^∞` on the open
  quadrant `Q0`; this is the `SmoothOpen`-analogue of the delivered
  `Work.FTS.EllipticEst.SmoothNbhd_smoothOpen`);
* `smoothOpen_{add,sub,neg,const_mul,mul,congr}_bsl` : the elementary closure properties of
  `SmoothOpen` (proved here directly from `ContDiffOn.add`, `.sub`, `.neg`, `.mul`, ...);
* `smoothOpen_{z,zsq,tan}_bsl` : the three concrete `SmoothOpen` factors `z`, `z²`, `tan θ`
  occurring in `bslOp` (`tan` needs `Real.cos θ ≠ 0` on `Q0`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.OpenQAux
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false

/-! ## Elementary closure properties of `SmoothOpen`

These are stated for the (uncurried) `SmoothOpen` of `OpenQDefs`, i.e. `C^∞` on the open
quadrant `Q0 = (0,∞) × (0,π/2)`.  They are the open-quadrant analogues of
`smoothQuad_mul`, `SmoothQuad.DzIter`, ... of `Work.FTS.LocData.SmoothChain`, and of
`Work.FTS.EllipticEst.smoothOpen_add` / `SmoothOpen.const_mul'` / `smoothOpen_sub`
(delivered in `EllHyp_certificates`).  They are proved here directly, so that this module
depends only on `sorry`-free modules. -/

/-- `SmoothOpen` is closed under pointwise addition. -/
theorem smoothOpen_add_bsl {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => f z θ + g z θ)) Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2 + g p.1 p.2)
    Work.FTS.EllipticEst.Q0
  exact hf.add hg

/-- `SmoothOpen` is closed under pointwise subtraction. -/
theorem smoothOpen_sub_bsl {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ - g z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => f z θ - g z θ)) Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2 - g p.1 p.2)
    Work.FTS.EllipticEst.Q0
  exact hf.sub hg

/-- `SmoothOpen` is closed under pointwise negation. -/
theorem smoothOpen_neg_bsl {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -f z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => -f z θ)) Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => -f p.1 p.2)
    Work.FTS.EllipticEst.Q0
  exact hf.neg

/-- `SmoothOpen` is closed under multiplication by a constant. -/
theorem smoothOpen_const_mul_bsl (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => c * f z θ)) Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => c * f p.1 p.2)
    Work.FTS.EllipticEst.Q0
  exact (contDiffOn_const (c := c) (s := Work.FTS.EllipticEst.Q0)).mul hf

/-- `SmoothOpen` is closed under pointwise multiplication. -/
theorem smoothOpen_mul_bsl {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => f z θ * g z θ)) Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2 * g p.1 p.2)
    Work.FTS.EllipticEst.Q0
  exact hf.mul hg

/-- The iterated plain derivative `∂_θ^i` preserves `SmoothOpen`.  (`OpenQDefs` provides the
analogues for `∂_z`, `D_z`, `D_θ` — `SmoothOpen.pzIter`, `SmoothOpen.DzIter`,
`SmoothOpen.DthIter` — but not for `∂_θ`; `Lzero` needs `∂_θ²`.) -/
theorem smoothOpen_pthIter_bsl {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (i : ℕ) : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i f) := by
  induction i with
  | zero => simpa using hf
  | succ n ih => rw [Work.Spaces.pthIter_succ]; exact Work.FTS.EllipticEst.SmoothOpen.pth ih

/-- Congruence for `SmoothOpen`: a function agreeing with a `SmoothOpen` function on the
open quadrant is `SmoothOpen`. -/
theorem smoothOpen_congr_bsl {f g : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen f)
    (h' : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    Work.FTS.EllipticEst.SmoothOpen g := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Work.FTS.EllipticEst.Q0
  refine ContDiffOn.congr h ?_
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact (h' p.1 p.2 hz hθ0 hθ1).symm

/-! ## The concrete factors `z`, `z²` and `tan θ` -/

/-- The coordinate `z` is `C^∞` on the open quadrant. -/
theorem smoothOpen_z_bsl : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (fun z _ : ℝ => z))
    Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1) Work.FTS.EllipticEst.Q0
  exact contDiffOn_fst

/-- The factor `z²` of the second-order term of `bslOp` is `C^∞` on the open quadrant. -/
theorem smoothOpen_zsq_bsl : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z ^ 2) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (fun z _ : ℝ => z ^ 2))
    Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 ^ 2)
    Work.FTS.EllipticEst.Q0
  exact (contDiffOn_fst (𝕜 := ℝ) (s := Work.FTS.EllipticEst.Q0)).pow 2

/-- **`tan θ` is `C^∞` on the open quadrant**, i.e. as a function of `(z,θ)` on `Q0`.  It is
`sin/cos` with `cos θ ≠ 0` for `0 < θ < π/2`. -/
theorem smoothOpen_tan_bsl : Work.FTS.EllipticEst.SmoothOpen (fun _ : ℝ => Real.tan) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (fun _ : ℝ => Real.tan))
    Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.tan p.2)
    Work.FTS.EllipticEst.Q0
  have hfun : (fun p : ℝ × ℝ => Real.tan p.2)
      = fun p : ℝ × ℝ => Real.sin p.2 / Real.cos p.2 := by
    funext p; exact Real.tan_eq_sin_div_cos p.2
  rw [hfun]
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.sin p.2)
      Work.FTS.EllipticEst.Q0 := by
    change ContDiffOn ℝ Work.Stability.smoothOrder (Real.sin ∘ Prod.snd)
      Work.FTS.EllipticEst.Q0
    exact (Real.contDiff_sin (n := Work.Stability.smoothOrder)).comp_contDiffOn contDiffOn_snd
  have hcos : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.cos p.2)
      Work.FTS.EllipticEst.Q0 := by
    change ContDiffOn ℝ Work.Stability.smoothOrder (Real.cos ∘ Prod.snd)
      Work.FTS.EllipticEst.Q0
    exact (Real.contDiff_cos (n := Work.Stability.smoothOrder)).comp_contDiffOn contDiffOn_snd
  refine ContDiffOn.div hsin hcos ?_
  intro p hp
  obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)

/-! ## `SmoothNbhd` implies `SmoothOpen` -/

/-- A function which is analytic on the neighbourhood `(-1,∞) × (-1, π/2+1)` of the closed
quadrant (`Work.Spaces.SmoothNbhd`) is `C^∞` on the open quadrant `Q0`, which is contained
in that neighbourhood. -/
theorem smoothNbhd_smoothOpen_bsl {Ψ : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd Ψ) :
    Work.FTS.EllipticEst.SmoothOpen Ψ := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry Ψ)
    Work.FTS.EllipticEst.Q0
  have hsub : Work.FTS.EllipticEst.Q0 ⊆ Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1) (π / 2 + 1) := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    refine ⟨?_, ?_, ?_⟩
    · show (-1 : ℝ) < p.1; linarith
    · show (-1 : ℝ) < p.2; linarith
    · show p.2 < π / 2 + 1; linarith [Real.pi_pos]
  exact (h.mono hsub).of_le le_top

/-- **`SmoothInt` is `SmoothOpen`.**  `SmoothInt Ψ` is `C^∞` on the open strip
`(-1,∞) × (0,π/2)` (together with the `z`-slices down to `z = 0`); restricting the first
conjunct to the open quadrant `Q0` and dropping the order from the analytic `⊤` to the honest
`C^∞` gives the `SmoothOpen` of `OpenQDefs`.  This is the bridge used by every consumer that
used to pass `SmoothNbhd` and now only has `EllHyp.smooth : SmoothInt`. -/
theorem smoothInt_smoothOpen_bsl {Ψ : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothInt Ψ) :
    Work.FTS.EllipticEst.SmoothOpen Ψ := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry Ψ)
    Work.FTS.EllipticEst.Q0
  have hsub : Work.FTS.EllipticEst.Q0 ⊆ Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo 0 (π / 2) := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ⟨lt_trans (by norm_num) hz, hθ0, hθ1⟩
  exact (h.1.mono hsub).of_le le_top

/-! ## The certificate -/

/-- **`bslOp α Ψ` is `C^∞` on the open quadrant** for every `Ψ` which is smooth on a
neighbourhood of the closed quadrant.  Indeed

  `bslOp α Ψ = -α²z²·∂_z²Ψ - α(5+α)z·∂_zΨ + Lzero Ψ` with
  `Lzero Ψ = -∂_θ²Ψ + ∂_θ(tan θ·Ψ) - 6Ψ`,

and each summand is built from `Ψ`, its partials `∂_z²Ψ`, `∂_zΨ`, `∂_θ²Ψ`, `∂_θ(tan θ·Ψ)`
(which are `SmoothOpen` by `SmoothOpen.pzIter`, `SmoothOpen.pz` and `SmoothOpen.pth` of
`OpenQDefs`, resp. by `smoothOpen_pthIter_bsl` below) and the `C^∞` factors `z²`, `z`,
`tan θ`, using the closure properties above. -/
theorem SmoothOpen_bslOp (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ := smoothNbhd_smoothOpen_bsl hΨ
  have hzsq : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z ^ 2) := smoothOpen_zsq_bsl
  have hz : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z) := smoothOpen_z_bsl
  have htan : Work.FTS.EllipticEst.SmoothOpen (fun _ : ℝ => Real.tan) := smoothOpen_tan_bsl
  -- the second-order term `-α²z²·∂_z²Ψ`
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ) :=
    smoothOpen_congr_bsl
      (smoothOpen_const_mul_bsl (-(α ^ 2))
        (smoothOpen_mul_bsl hzsq (Work.FTS.EllipticEst.SmoothOpen.pzIter hΨso 2)))
      (fun z θ _ _ _ => by ring)
  -- the first-order term `-α(5+α)z·∂_zΨ`
  have hB : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ) :=
    smoothOpen_congr_bsl
      (smoothOpen_const_mul_bsl (α * (5 + α))
        (smoothOpen_mul_bsl hz (Work.FTS.EllipticEst.SmoothOpen.pz hΨso)))
      (fun z θ _ _ _ => by ring)
  -- the angular operator `Lzero Ψ = -∂_θ²Ψ + ∂_θ(tan θ·Ψ) - 6Ψ`
  have htΨ : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) :=
    smoothOpen_mul_bsl htan hΨso
  have hC : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.Lzero Ψ) :=
    smoothOpen_congr_bsl
      (smoothOpen_sub_bsl
        (smoothOpen_add_bsl
          (smoothOpen_neg_bsl (smoothOpen_pthIter_bsl hΨso 2))
          (Work.FTS.EllipticEst.SmoothOpen.pth htΨ))
        (smoothOpen_const_mul_bsl 6 hΨso))
      (fun z θ _ _ _ => by simp only [Work.Elliptic.Lzero])
  -- assembly
  exact smoothOpen_congr_bsl (smoothOpen_add_bsl (smoothOpen_sub_bsl hA hB) hC)
    (fun z θ _ _ _ => by simp only [Work.Elliptic.bslOp_apply])

/-- **The `SmoothInt` form of the certificate**: `bslOp α Ψ` is `C^∞` on the open quadrant for
every `Ψ` with `Work.Spaces.SmoothInt Ψ` (the smoothness carried by `EllHyp.smooth` after the
2026 re-scope).  Verbatim copy of the proof of `SmoothOpen_bslOp`, with the hypothesis weakened
through `smoothInt_smoothOpen_bsl`. -/
theorem SmoothOpen_bslOp_int (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothInt Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ := smoothInt_smoothOpen_bsl hΨ
  have hzsq : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z ^ 2) := smoothOpen_zsq_bsl
  have hz : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z) := smoothOpen_z_bsl
  have htan : Work.FTS.EllipticEst.SmoothOpen (fun _ : ℝ => Real.tan) := smoothOpen_tan_bsl
  -- the second-order term `-α²z²·∂_z²Ψ`
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ) :=
    smoothOpen_congr_bsl
      (smoothOpen_const_mul_bsl (-(α ^ 2))
        (smoothOpen_mul_bsl hzsq (Work.FTS.EllipticEst.SmoothOpen.pzIter hΨso 2)))
      (fun z θ _ _ _ => by ring)
  -- the first-order term `-α(5+α)z·∂_zΨ`
  have hB : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ) :=
    smoothOpen_congr_bsl
      (smoothOpen_const_mul_bsl (α * (5 + α))
        (smoothOpen_mul_bsl hz (Work.FTS.EllipticEst.SmoothOpen.pz hΨso)))
      (fun z θ _ _ _ => by ring)
  -- the angular operator `Lzero Ψ = -∂_θ²Ψ + ∂_θ(tan θ·Ψ) - 6Ψ`
  have htΨ : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) :=
    smoothOpen_mul_bsl htan hΨso
  have hC : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.Lzero Ψ) :=
    smoothOpen_congr_bsl
      (smoothOpen_sub_bsl
        (smoothOpen_add_bsl
          (smoothOpen_neg_bsl (smoothOpen_pthIter_bsl hΨso 2))
          (Work.FTS.EllipticEst.SmoothOpen.pth htΨ))
        (smoothOpen_const_mul_bsl 6 hΨso))
      (fun z θ _ _ _ => by simp only [Work.Elliptic.Lzero])
  -- assembly
  exact smoothOpen_congr_bsl (smoothOpen_add_bsl (smoothOpen_sub_bsl hA hB) hC)
    (fun z θ _ _ _ => by simp only [Work.Elliptic.bslOp_apply])

end Work.FTS.EllipticEst.Cert
