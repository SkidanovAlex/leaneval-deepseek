/-
# `Submission/Work/FTS_MuLamOK/Conversion.lean` — from the row envelopes to the zero modes

The three row lemmas (`Rows/Rl0Open`, `Rows/Rl1Open`, `Rows/Rl2Open`) bound the `L₁₂`-zero-modes
by the paper's envelopes

  `K · (α² + √α·X + α^{-3/2}·X²)`   (`N₀`, `N`)   and   `K · X`   (transport),   `X = Xn α f`,

whereas the μ-bound of `Defs.lean` needs the *scaled* forms `≤ K' α²` on profiles of
`ℋ⁴`-size `≤ C₀α²`.  This file performs that conversion:

* `√α·X ≤ C₀α²` and `α^{-3/2}·X² ≤ C₀²α²` for `X ≤ C₀α²`, `0 < α ≤ 1` (so the whole envelope is
  at most `K(1 + C₀ + C₀²)α²`);
* `ZeroMode0_of_row`, `ZeroMode1_of_row`, `ZeroMode2_of_row` — the three scaled zero modes from
  the three row envelopes;
* `ZeroMode0.mono` / `ZeroMode1.mono` / `ZeroMode2.mono` — enlargement of the constant, so that
  the three can be combined under a single `K`.

The hypotheses of the row lemmas used here are `SmoothOpen f` and `HkMem α 4 f`, both of which
`ClassC α f` supplies (`ClassC.reg`, `ClassC.hkMem_seven` + `HkMem`-monotonicity).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_MuLamOK.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.StrongPersist.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLamOK

open Work.FTS.Galerkin (Fn Fam slice muDyn lamDyn)

set_option autoImplicit false

/-! ## The scale conversion -/

/-- **The envelope converts.**  For `0 < α ≤ 1`, `0 ≤ X ≤ C₀α²` and `0 ≤ K`,
`K(α² + √α·X + α^{-3/2}X²) ≤ K(1 + C₀ + C₀²)α²`. -/
theorem envelope_le {α C₀ K X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hK0 : 0 ≤ K)
    (hX0 : 0 ≤ X) (hX : X ≤ C₀ * α ^ 2) :
    K * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2)
      ≤ K * (1 + C₀ + C₀ ^ 2) * α ^ 2 := by
  have hC₀α2 : (0 : ℝ) ≤ C₀ * α ^ 2 := le_trans hX0 hX
  have hX2 : X ^ 2 ≤ C₀ ^ 2 * α ^ 4 := by
    have h := mul_self_le_mul_self hX0 hX
    nlinarith [h, hC₀α2]
  have h1 : Real.sqrt α * X ≤ C₀ * α ^ 2 := by
    have hsq : Real.sqrt α ≤ 1 := Real.sqrt_le_one.mpr hα1
    have h := mul_le_mul hsq hX hX0 (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  have h2 : α ^ (-(3 / 2 : ℝ)) * X ^ 2 ≤ C₀ ^ 2 * α ^ 2 := by
    have hle : α ^ (-(3 / 2 : ℝ)) ≤ α ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num)
    have hid : α ^ (-(2 : ℝ)) * α ^ 4 = α ^ 2 := by
      rw [← Real.rpow_natCast α 4, ← Real.rpow_add hα]
      norm_num
    calc α ^ (-(3 / 2 : ℝ)) * X ^ 2 ≤ α ^ (-(2 : ℝ)) * X ^ 2 :=
          mul_le_mul_of_nonneg_right hle (sq_nonneg X)
      _ ≤ α ^ (-(2 : ℝ)) * (C₀ ^ 2 * α ^ 4) :=
          mul_le_mul_of_nonneg_left hX2 (Real.rpow_nonneg hα.le _)
      _ = C₀ ^ 2 * α ^ 2 := by
        rw [show α ^ (-(2 : ℝ)) * (C₀ ^ 2 * α ^ 4) = C₀ ^ 2 * (α ^ (-(2 : ℝ)) * α ^ 4) by ring,
          hid]
  have hsum : α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2
      ≤ (1 + C₀ + C₀ ^ 2) * α ^ 2 := by linarith
  calc K * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2)
      ≤ K * ((1 + C₀ + C₀ ^ 2) * α ^ 2) := mul_le_mul_of_nonneg_left hsum hK0
    _ = K * (1 + C₀ + C₀ ^ 2) * α ^ 2 := by ring

/-- The transport envelope converts: `K X ≤ (K C₀) α²` for `X ≤ C₀α²`. -/
theorem envelope_transport_le {α C₀ K X : ℝ} (hK0 : 0 ≤ K) (hX : X ≤ C₀ * α ^ 2) :
    K * X ≤ K * C₀ * α ^ 2 := by
  calc K * X ≤ K * (C₀ * α ^ 2) := mul_le_mul_of_nonneg_left hX hK0
    _ = K * C₀ * α ^ 2 := by ring

/-! ## The three scaled zero modes from the three row envelopes -/

/-- **`ZeroMode0` from the `N₀`-row envelope.** -/
theorem ZeroMode0_of_row {α C₀ K : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K)
    (hrow : ∀ f : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0|
        ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α f
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f ^ 2)) :
    ZeroMode0 α C₀ (K * (1 + C₀ + C₀ ^ 2)) := by
  intro f hf hX
  have hso : Work.FTS.EllipticEst.SmoothOpen f := hf.reg
  have hmem : Work.Spaces.HkMem α 4 f :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hso hf.mem
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  exact le_trans (hrow f hso hmem) (envelope_le hα hα1 hK hX0 hX)

/-- **`ZeroMode1` from the `N`-row envelope.** -/
theorem ZeroMode1_of_row {α C₀ K : ℝ} {Φs : Fn} {E : Fn → Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hK : 0 ≤ K)
    (hrow : ∀ f : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
          (fun z θ => Φs z θ + E f z θ)) 0|
        ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α f
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f ^ 2)) :
    ZeroMode1 α C₀ (K * (1 + C₀ + C₀ ^ 2)) Φs E := by
  intro f hf hX
  have hso : Work.FTS.EllipticEst.SmoothOpen f := hf.reg
  have hmem : Work.Spaces.HkMem α 4 f :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hso hf.mem
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  exact le_trans (hrow f hso hmem) (envelope_le hα hα1 hK hX0 hX)

/-- **`ZeroMode2` from the transport-row envelope.** -/
theorem ZeroMode2_of_row {α C₀ K : ℝ} (hK : 0 ≤ K)
    (hrow : ∀ f : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0|
        ≤ K * Work.FTS.Nonlin.Xn α f) :
    ZeroMode2 α C₀ (K * C₀) := by
  intro f hf hX
  have hso : Work.FTS.EllipticEst.SmoothOpen f := hf.reg
  have hmem : Work.Spaces.HkMem α 4 f :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hso hf.mem
  exact le_trans (hrow f hso hmem) (envelope_transport_le hK hX)

/-! ## The same three conversions, for rows quantified over the class `ClassC` only

The `N`-row needs the elliptic package `EllPkgGo α Ce f (E f)` as a hypothesis, and that package
is only available on the class `ClassC`; so the interface form of the three rows
(`RowReduction.MuLamOK_of_rowEnvelopes`) takes them quantified over `ClassC α f`.  These three
variants are the ones matching that interface. -/

/-- **`ZeroMode0` from the `N₀`-row envelope, `ClassC`-quantified row.** -/
theorem ZeroMode0_of_row_classC {α C₀ K : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K)
    (hrow : ∀ f : Fn, Work.FTS.ClassC.ClassC α f →
      |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0|
        ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α f
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f ^ 2)) :
    ZeroMode0 α C₀ (K * (1 + C₀ + C₀ ^ 2)) := by
  intro f hf hX
  exact le_trans (hrow f hf) (envelope_le hα hα1 hK (Work.Spaces.HkNorm_nonneg α 4 f) hX)

/-- **`ZeroMode1` from the `N`-row envelope, `ClassC`-quantified row.** -/
theorem ZeroMode1_of_row_classC {α C₀ K : ℝ} {Φs : Fn} {E : Fn → Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hK : 0 ≤ K)
    (hrow : ∀ f : Fn, Work.FTS.ClassC.ClassC α f →
      |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
          (fun z θ => Φs z θ + E f z θ)) 0|
        ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α f
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f ^ 2)) :
    ZeroMode1 α C₀ (K * (1 + C₀ + C₀ ^ 2)) Φs E := by
  intro f hf hX
  exact le_trans (hrow f hf) (envelope_le hα hα1 hK (Work.Spaces.HkNorm_nonneg α 4 f) hX)

/-- **`ZeroMode2` from the transport-row envelope, `ClassC`-quantified row.** -/
theorem ZeroMode2_of_row_classC {α C₀ K : ℝ} (hK : 0 ≤ K)
    (hrow : ∀ f : Fn, Work.FTS.ClassC.ClassC α f →
      |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0|
        ≤ K * Work.FTS.Nonlin.Xn α f) :
    ZeroMode2 α C₀ (K * C₀) := by
  intro f hf hX
  exact le_trans (hrow f hf) (envelope_transport_le hK hX)

/-! ## Monotonicity in the constant -/

theorem ZeroMode0.mono {α C₀ K K' : ℝ} (h : ZeroMode0 α C₀ K) (hKK : K ≤ K') :
    ZeroMode0 α C₀ K' := fun f hf hX => le_trans (h f hf hX) (mul_le_mul_of_nonneg_right hKK
  (sq_nonneg α))

theorem ZeroMode1.mono {α C₀ K K' : ℝ} {Φs : Fn} {E : Fn → Fn} (h : ZeroMode1 α C₀ K Φs E)
    (hKK : K ≤ K') : ZeroMode1 α C₀ K' Φs E := fun f hf hX =>
  le_trans (h f hf hX) (mul_le_mul_of_nonneg_right hKK (sq_nonneg α))

theorem ZeroMode2.mono {α C₀ K K' : ℝ} (h : ZeroMode2 α C₀ K) (hKK : K ≤ K') :
    ZeroMode2 α C₀ K' := fun f hf hX => le_trans (h f hf hX) (mul_le_mul_of_nonneg_right hKK
  (sq_nonneg α))

end Work.FTS_MuLamOK
