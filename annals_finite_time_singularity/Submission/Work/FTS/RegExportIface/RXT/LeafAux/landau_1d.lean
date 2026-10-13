import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! # `Work.FTS.RegExportIface.RXT.landau_1d` — leaf port (module `LeafAux.landau_1d`)

The leaf statement of `Submission/Work/FTS/RegExportIface/RXT/Leaves.lean`, **proved**.
Proof ported verbatim from the `Work.FTS_RegExport` mirror area; this module deliberately
does **not** import `Leaves` (which imports it), so the cycle is broken.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.RegExportIface.RXT

set_option autoImplicit false


/-- `|p - q| ≤ |p| + |q|`, the form of the triangle inequality used below. -/
private theorem landau_abs_sub_le (p q : ℝ) : |p - q| ≤ |p| + |q| := by
  rw [abs_sub_le_iff]
  constructor <;> linarith [le_abs_self p, neg_le_abs p, le_abs_self q, neg_le_abs q]

/-- **Second-order Taylor bound, upper sign.**  If `f` is differentiable with derivative `f'`
on `[a, b]`, `f'` is differentiable with derivative `f''` there, `a ≤ b` and `f'' ≤ A` on
`[a, b]`, then the Taylor remainder at the left endpoint is bounded above:
`f b - f a - f' a * (b - a) ≤ A * (b - a)^2 / 2`.

Only pointwise `HasDerivAt` hypotheses are used; no continuity of `f''` is needed. -/
theorem landau_taylor2_upper {f f' f'' : ℝ → ℝ} {a b A : ℝ} (hab : a ≤ b)
    (hf : ∀ y ∈ Set.Icc a b, HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc a b, HasDerivAt f' (f'' y) y)
    (hA : ∀ y ∈ Set.Icc a b, f'' y ≤ A) :
    f b - f a - f' a * (b - a) ≤ A * (b - a) ^ 2 / 2 := by
  have haI : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hfc : ContinuousOn f (Set.Icc a b) := fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hf'c : ContinuousOn f' (Set.Icc a b) := fun t ht => (hf' t ht).continuousAt.continuousWithinAt
  -- the auxiliary function `G` is continuous on `[a,b]`
  have hGcont : ContinuousOn (fun s : ℝ => f b - f s - f' s * (b - s) - A / 2 * (b - s) ^ 2)
      (Set.Icc a b) := by
    have h1 : ContinuousOn (fun s : ℝ => f b - f s) (Set.Icc a b) :=
      (continuousOn_const (s := Set.Icc a b) (c := f b)).sub hfc
    have h2 : ContinuousOn (fun s : ℝ => f' s * (b - s)) (Set.Icc a b) :=
      hf'c.mul ((continuousOn_const (s := Set.Icc a b) (c := b)).sub continuousOn_id)
    have h3 : ContinuousOn (fun s : ℝ => A / 2 * (b - s) ^ 2) (Set.Icc a b) :=
      (continuousOn_const (s := Set.Icc a b) (c := A / 2)).mul
        (((continuousOn_const (s := Set.Icc a b) (c := b)).sub continuousOn_id).pow 2)
    exact (h1.sub h2).sub h3
  -- its derivative on the interior is `(b - t) * (A - f'' t)`
  have hderiv : ∀ t ∈ interior (Set.Icc a b),
      HasDerivWithinAt (fun s : ℝ => f b - f s - f' s * (b - s) - A / 2 * (b - s) ^ 2)
        ((b - t) * (A - f'' t)) (interior (Set.Icc a b)) t := by
    intro t ht
    rw [interior_Icc] at ht
    have htI : t ∈ Set.Icc a b := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hb : HasDerivAt (fun s : ℝ => b - s) (0 - 1) t :=
      (hasDerivAt_const t b).sub (hasDerivAt_id t)
    have h1 : HasDerivAt (fun s : ℝ => f b - f s) (0 - f' t) t :=
      (hasDerivAt_const t (f b)).sub (hf t htI)
    have h2 : HasDerivAt (fun s : ℝ => f' s * (b - s)) (f'' t * (b - t) + f' t * (0 - 1)) t :=
      (hf' t htI).mul hb
    have h3 : HasDerivAt (fun s : ℝ => A / 2 * (b - s) ^ 2)
        (A / 2 * (2 * (b - t) ^ (2 - 1) * (0 - 1))) t :=
      (hb.pow 2).const_mul (A / 2)
    have h4 : HasDerivAt (fun s : ℝ => f b - f s - f' s * (b - s) - A / 2 * (b - s) ^ 2)
        ((0 - f' t) - (f'' t * (b - t) + f' t * (0 - 1))
          - A / 2 * (2 * (b - t) ^ (2 - 1) * (0 - 1))) t :=
      (h1.sub h2).sub h3
    convert h4.hasDerivWithinAt using 1
    norm_num
    ring
  -- and that derivative is nonnegative on `(a,b)`
  have hnonneg : ∀ t ∈ interior (Set.Icc a b), 0 ≤ (b - t) * (A - f'' t) := by
    intro t ht
    rw [interior_Icc] at ht
    have htI : t ∈ Set.Icc a b := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h1 : 0 ≤ b - t := by linarith [ht.2]
    have h2 : 0 ≤ A - f'' t := by linarith [hA t htI]
    exact mul_nonneg h1 h2
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hGcont hderiv hnonneg
  have h := hmono haI hbI hab
  have hG0 : (fun s : ℝ => f b - f s - f' s * (b - s) - A / 2 * (b - s) ^ 2) b = 0 := by
    simp only [sub_self, mul_zero, zero_pow (show (2:ℕ) ≠ 0 by norm_num)]
  rw [hG0] at h
  linarith [h]

/-- **Second-order Taylor bound, lower sign.**  Same as `landau_taylor2_upper` with `f'' ≥ -A`:
the Taylor remainder at the left endpoint is bounded below by `-A * (b - a)^2 / 2`. -/
theorem landau_taylor2_lower {f f' f'' : ℝ → ℝ} {a b A : ℝ} (hab : a ≤ b)
    (hf : ∀ y ∈ Set.Icc a b, HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc a b, HasDerivAt f' (f'' y) y)
    (hA : ∀ y ∈ Set.Icc a b, -A ≤ f'' y) :
    -(A * (b - a) ^ 2 / 2) ≤ f b - f a - f' a * (b - a) := by
  have h := landau_taylor2_upper (f := fun y => -f y) (f' := fun y => -f' y)
    (f'' := fun y => -f'' y) (a := a) (b := b) (A := A) hab
    (fun y hy => (hf y hy).neg) (fun y hy => (hf' y hy).neg)
    (fun y hy => by have := hA y hy; linarith)
  linarith [h]

/-- **Second-order Taylor bound with the Lagrange remainder** for a function whose first two
derivatives are only known to exist pointwise on `[a, b]`: if `|f''| ≤ A` there, then
`|f b - f a - f' a * (b - a)| ≤ A * (b - a)^2 / 2`. -/
theorem landau_taylor2_remainder {f f' f'' : ℝ → ℝ} {a b A : ℝ} (hab : a ≤ b)
    (hf : ∀ y ∈ Set.Icc a b, HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc a b, HasDerivAt f' (f'' y) y)
    (hA : ∀ y ∈ Set.Icc a b, |f'' y| ≤ A) :
    |f b - f a - f' a * (b - a)| ≤ A * (b - a) ^ 2 / 2 := by
  have h1 := landau_taylor2_upper (f := f) (f' := f') (f'' := f'') (A := A) hab hf hf'
    (fun y hy => (abs_le.mp (hA y hy)).2)
  have h2 := landau_taylor2_lower (f := f) (f' := f') (f'' := f'') (A := A) hab hf hf'
    (fun y hy => (abs_le.mp (hA y hy)).1)
  rw [abs_le]
  exact ⟨h2, h1⟩

theorem landau_1d {h : ℝ → ℝ} {x δ M₀ M₂ : ℝ} (hδ : 0 < δ)
    (hd : ∀ y ∈ Set.Icc x (x + δ), HasDerivAt h (deriv h y) y)
    (hd2 : ∀ y ∈ Set.Icc x (x + δ), HasDerivAt (deriv h) (deriv (deriv h) y) y)
    (h0 : ∀ y ∈ Set.Icc x (x + δ), |h y| ≤ M₀)
    (h2 : ∀ y ∈ Set.Icc x (x + δ), |deriv (deriv h) y| ≤ M₂) :
    |deriv h x| ≤ 2 * M₀ / δ + M₂ * δ / 2 := by
  have hxδ : x ≤ x + δ := by linarith
  -- the Lagrange remainder of the second-order Taylor expansion at `x`, evaluated at `x + δ`
  have hrem := landau_taylor2_remainder (f := h) (f' := deriv h) (f'' := deriv (deriv h))
    (a := x) (b := x + δ) (A := M₂) hxδ hd hd2 h2
  have hsub : x + δ - x = δ := by ring
  rw [hsub] at hrem
  have hmemx : x ∈ Set.Icc x (x + δ) := ⟨le_rfl, hxδ⟩
  have hmemδ : x + δ ∈ Set.Icc x (x + δ) := ⟨hxδ, le_rfl⟩
  -- `|h (x+δ) - h x| ≤ 2 M₀`
  have hb : |h (x + δ) - h x| ≤ 2 * M₀ := by
    have h1 : |h (x + δ) - h x| ≤ |h (x + δ)| + |h x| := landau_abs_sub_le _ _
    have h2' : |h (x + δ)| + |h x| ≤ M₀ + M₀ := add_le_add (h0 (x + δ) hmemδ) (h0 x hmemx)
    linarith [h1, h2']
  have key : |deriv h x| * δ ≤ 2 * M₀ + M₂ * δ ^ 2 / 2 := by
    have h1 : |deriv h x| * δ = |deriv h x * δ| := by rw [abs_mul, abs_of_pos hδ]
    rw [h1]
    -- `deriv h x * δ = (h (x+δ) - h x) - R`
    have htri : |deriv h x * δ| ≤ |h (x + δ) - h x| + |h (x + δ) - h x - deriv h x * δ| := by
      have he : deriv h x * δ = (h (x + δ) - h x) - (h (x + δ) - h x - deriv h x * δ) := by ring
      calc |deriv h x * δ|
          = |(h (x + δ) - h x) - (h (x + δ) - h x - deriv h x * δ)| := congrArg abs he
        _ ≤ |h (x + δ) - h x| + |h (x + δ) - h x - deriv h x * δ| := landau_abs_sub_le _ _
    linarith [htri, hb, hrem]
  have hdone : |deriv h x| ≤ (2 * M₀ + M₂ * δ ^ 2 / 2) / δ := (le_div_iff₀ hδ).mpr key
  have harith : (2 * M₀ + M₂ * δ ^ 2 / 2) / δ = 2 * M₀ / δ + M₂ * δ / 2 := by
    field_simp
  rw [harith] at hdone
  exact hdone


end Work.FTS.RegExportIface.RXT
