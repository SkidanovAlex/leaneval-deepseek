import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.H2.prodW_interior_bound
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

set_option autoImplicit false

/- Open-quadrant port of `Work.FTS.H2.sqm_pz_DthIter_mul_le_4` (`SmoothQuad` → `SmoothOpen`),
with the domain restricted to `z > 0` (the only points where `SmoothOpen` supplies the slices'
differentiability: `SmoothQuad`-style smoothness at `z = 0` is *not* available, and both the
Leibniz identity and the bound are stated at interior `z` only).  Needed by the primed rows
10/11/15/19 (`Submission/Work/FTS/NonlinRows/`) to pass the pointwise `𝒲`-type bounds of the two
factors of `2ℛ(Φ̃_*)F_*` to their product.  The `SmoothQuad` hypothesis of the source is used only
through the `z`-slices (`SmoothOpen.curry_z`), so the port is a verbatim re-run; `257` is the
constant of `Work.Spaces.one_add_choose_double_sum_le`. -/

/-! ## The mixed Leibniz calculus of `∂_z^k D_θ^j` in the open quadrant

The `SmoothOpen` (`C^∞` on the open quadrant `z > 0`, `0 < θ < π/2`) counterpart of the
`SmoothQuad` block of `Submission/Work/FTS/H2/prodW_interior_bound.lean`.  The only difference is
that no smoothness at `z = 0` is available, so every statement is made at `z > 0`; the proofs are
verbatim re-runs, with `SmoothOpen.curry_z`/`SmoothOpen.curry_θ` and
`Work.FTS.LocData.DthIter_mul_smoothQuad` in place of their `SmoothQuad` counterparts. -/

/-- The `z`-slices of the `D_θ`-iterates of a `SmoothOpen` function are `C^∞` at every `z > 0`,
for `θ ∈ (0,π/2)`. -/
theorem sqo_dthIter_zslice_contDiffAt {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2))
    {z : ℝ} (hz : 0 < z) (a : ℕ) :
    ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => Work.Spaces.DthIter a f z' θ) z :=
  ((hf.DthIter a).curry_z hθ).contDiffAt (isOpen_Ioi.mem_nhds hz)

/-- At a fixed angle `θ ∈ (0,π/2)` the `D_θ`-Leibniz expansion of a product agrees with
`D_θ^j (f g)` on a neighbourhood of every `z > 0`. -/
theorem sqo_DthIter_mul_zslice_eventuallyEq (j : ℕ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (fun z' => Work.Spaces.DthIter j (fun z θ => f z θ * g z θ) z' θ)
      =ᶠ[𝓝 z] (fun z' => ∑ a ∈ Finset.range (j + 1),
        (j.choose a : ℝ)
          * (Work.Spaces.DthIter a f z' θ * Work.Spaces.DthIter (j - a) g z' θ)) := by
  filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
  exact Work.FTS.LocData.DthIter_mul_smoothQuad j f g hθ (hf.curry_θ hz') (hg.curry_θ hz')

/-- **The mixed Leibniz identity in the open class**: for `SmoothOpen` functions `f, g`, every
`z > 0` and `θ ∈ (0,π/2)`,
`∂_z^k D_θ^j (f g) = ∑_{a≤j} ∑_{c≤k} C(j,a) C(k,c) ∂_z^c D_θ^a f · ∂_z^{k-c} D_θ^{j-a} g`. -/
theorem sqo_pz_DthIter_mul_eq (k j : ℕ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ
        = ∑ a ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (k + 1),
            ((j.choose a : ℝ) * (k.choose c : ℝ))
              * (Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ
                  * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ) := by
  intro z hz θ hθ
  have hslice : ∀ (h : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen h → ∀ a : ℕ,
      ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => Work.Spaces.DthIter a h z' θ) z :=
    fun h hh a => sqo_dthIter_zslice_contDiffAt hh hθ hz a
  have hleib := sqo_DthIter_mul_zslice_eventuallyEq j f g hf hg hz hθ
  rw [Work.Spaces.pzIter_eq_iteratedDeriv k _ z θ, Filter.EventuallyEq.iteratedDeriv_eq k hleib]
  have hsum := Work.Spaces.iteratedDeriv_sum_const_mul (s := Finset.range (j + 1))
    (c := fun a => (j.choose a : ℝ))
    (F := fun a z' => Work.Spaces.DthIter a f z' θ * Work.Spaces.DthIter (j - a) g z' θ) k z
    (fun a _ => ((hslice f hf a).mul (hslice g hg (j - a))).of_le
      (by rw [Work.Stability.smoothOrder]; simp))
  rw [hsum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hfun : (fun z' => Work.Spaces.DthIter a f z' θ * Work.Spaces.DthIter (j - a) g z' θ)
      = (fun z' => Work.Spaces.DthIter a f z' θ)
        * (fun z' => Work.Spaces.DthIter (j - a) g z' θ) := by
    funext z'; rfl
  rw [hfun]
  have hmul := iteratedDeriv_mul (f := fun z' => Work.Spaces.DthIter a f z' θ)
    (g := fun z' => Work.Spaces.DthIter (j - a) g z' θ) (x := z) (n := k)
    ((hslice f hf a).of_le (by rw [Work.Stability.smoothOrder]; simp))
    ((hslice g hg (j - a)).of_le (by rw [Work.Stability.smoothOrder]; simp))
  rw [hmul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Work.Spaces.pzIter_eq_iteratedDeriv c (Work.Spaces.DthIter a f) z θ,
    ← Work.Spaces.pzIter_eq_iteratedDeriv (k - c) (Work.Spaces.DthIter (j - a) g) z θ]
  ring

/-- **The Leibniz bound in the open class**, with the explicit constant `257` of
`Work.Spaces.one_add_choose_double_sum_le` (the `SmoothOpen` counterpart of
`Work.FTS.H2.sqm_pz_DthIter_mul_le_4`): for `SmoothOpen` functions `f, g`, every `z > 0`, every
`θ ∈ (0,π/2)` and `k, j ≤ 4`,
`|∂_z^k D_θ^j (f g)| ≤ 257 ∑_{c≤k} ∑_{a≤j} |∂_z^c D_θ^a f| · |∂_z^{k-c} D_θ^{j-a} g|`. -/
theorem sqm_pz_DthIter_mul_le_4_open (k j : ℕ) (hk : k ≤ 4) (hj : j ≤ 4) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ| ≤
        (257 : ℝ) * ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
          |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ| *
            |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ| := by
  intro z hz θ hθ
  rw [sqo_pz_DthIter_mul_eq k j f g hf hg z hz θ hθ]
  have h1 := Work.Spaces.abs_binom_double_sum_le k j
    (fun a c => Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ)
    (fun a c => Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ)
  have hT : (0 : ℝ) ≤ ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
      |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ| *
        |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ| :=
    Finset.sum_nonneg fun c _ =>
      Finset.sum_nonneg fun a _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  exact h1.trans (mul_le_mul_of_nonneg_right
    (Work.Spaces.one_add_choose_double_sum_le k j hk hj) hT)

end Work.FTS.NonlinRows
