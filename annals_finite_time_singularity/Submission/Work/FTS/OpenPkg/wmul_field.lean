import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.OpenPkg.WDp_le_of_pointwise
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.FTS.Nonlinear.N4Fields.wmul_field

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.OpenPkg.wmul_field` — the `D`-sup product rule of the open-quadrant vocabulary

This file proves the `wmul` clause of `Work.FTS.OpenPkg.N4Norm'`: on the open quadrant
`(0,∞) × (0,π/2)`, for two `C^∞` functions whose mixed derivatives `D_z^b D_θ^j`
(`D_z = z ∂_z`, `D_θ = sin(2θ) ∂_θ`) are bounded up to order `4` (`VocabO.WDMem`), the product
again has bounded mixed derivatives and

`WDp 4 (f·g) ≤ C · WDp 4 f · WDp 4 g`

with a **universal** constant `C` (here `160000`), independent of `α`, `f` and `g`.

The `open scoped Real` below is what makes the `π` of the statement denote `Real.pi`: without it,
under this project's `autoImplicit = false`, the bare `π` is an unknown identifier.

Note that `VocabO.WDp`/`WDMem` are built from `Work.FTS.H2.supAbsO`, whose supremum is taken
over the **open** quadrant only (no boundary line, no `(z+1)^k` weight, no angular weight).
Consequently the boundary-vanishing hypothesis on the `z`-derivatives of `g`'s slices — which is
essential for the frozen `WlInf`-form of the same statement
(`Submission/Work/FTS/Nonlinear/N4Fields/wmul_field.lean`) — is *not* needed here: it is kept in
the statement only for interface compatibility, and the proof never uses it.

The mathematical content is the two-operator Leibniz rule
`D_z^b D_θ^j (f·g) = ∑_{a≤j} ∑_{c≤b} C(j,a) C(b,c) (D_z^c D_θ^a f)(D_z^{b-c} D_θ^{j-a} g)`
on the open quadrant, which is already available as
`Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed`.  Every term of the right-hand side pairs a mixed
derivative of `f` of order `c + a ≤ b + j ≤ 4` with one of `g` of order
`(b - c) + (j - a) ≤ 4`; the hypotheses bound each of them, and the `WDp`-norm of a factor
dominates the supremum of each of its mixed derivatives (`supAbsO_mixed_le_WDp`).
-/

noncomputable section
open scoped Real Topology

namespace Work.FTS.OpenPkg

open Work.FTS.VocabO

/-! ## Two elementary consequences of the hypotheses -/

/-- **Each mixed-derivative supremum of a `WDMem`-function is dominated by its `WDp`-norm.**
`WDp 4 f` is the sum of the `supAbsO (mixed b j f)` over the pairs `b + j ≤ 4`, so one such
supremum is `≤` the whole sum (all summands are nonnegative, `supAbsO_nonneg`). -/
theorem supAbsO_mixed_le_WDp {f : ℝ → ℝ → ℝ} (hfm : WDMem 4 f) {b j : ℕ} (hbj : b + j ≤ 4) :
    Work.FTS.H2.supAbsO (Work.Spaces.mixed b j f) ≤ WDp 4 f :=
  Work.FTS.H2.supAbsO_le (fun z θ hz hθ hθ' =>
    WDMem_of_WDp_le hfm le_rfl b j hbj z θ hz hθ hθ')

/-- **The pointwise Leibniz bound for the product.**  For `SmoothOpen` functions `f, g` whose
mixed derivatives are bounded up to order `4` (`WDMem 4`), and for `b + j ≤ 4`, every mixed
derivative `D_z^b D_θ^j (f·g)` is bounded on the open quadrant by `6400 · WDp 4 f · WDp 4 g`.

The constant is deliberately loose: the Leibniz expansion has `(b+1)(j+1) ≤ 25` summands, each of
which is a product of a binomial coefficient `≤ 16` (`Nat.choose_le_two_pow`), one mixed
derivative of `f` (bounded by `WDp 4 f` via `le_supAbsO` and `supAbsO_mixed_le_WDp`) and one of
`g` (bounded by `WDp 4 g`); hence `25 · 16 · 16 = 6400`. -/
theorem mixed_mul_abs_le {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hfm : WDMem 4 f) (hgm : WDMem 4 g)
    {b j : ℕ} (hbj : b + j ≤ 4) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b j (fun z θ => f z θ * g z θ) z θ|
        ≤ 6400 * (WDp 4 f * WDp 4 g) := by
  intro z θ hz hθ0 hθ1
  have hWf : 0 ≤ WDp 4 f := WDp_nonneg 4 f
  have hWg : 0 ≤ WDp 4 g := WDp_nonneg 4 g
  have hWfg : 0 ≤ WDp 4 f * WDp 4 g := mul_nonneg hWf hWg
  -- each individual mixed derivative of `f`, resp. `g`, is bounded by the corresponding `WDp`
  have hX : ∀ c a : ℕ, c + a ≤ 4 → |Work.Spaces.mixed c a f z θ| ≤ WDp 4 f := by
    intro c a hca
    exact le_trans
      (Work.FTS.H2.le_supAbsO hz hθ0 hθ1 (fun z' θ' hz' hθ' hθ'' =>
        WDMem_of_WDp_le hfm le_rfl c a hca z' θ' hz' hθ' hθ''))
      (supAbsO_mixed_le_WDp hfm hca)
  have hY : ∀ c a : ℕ, c + a ≤ 4 → |Work.Spaces.mixed c a g z θ| ≤ WDp 4 g := by
    intro c a hca
    exact le_trans
      (Work.FTS.H2.le_supAbsO hz hθ0 hθ1 (fun z' θ' hz' hθ' hθ'' =>
        WDMem_of_WDp_le hgm le_rfl c a hca z' θ' hz' hθ' hθ''))
      (supAbsO_mixed_le_WDp hgm hca)
  -- the binomial coefficients occurring in the expansion
  have hcoef : ∀ n k : ℕ, n ≤ 4 → (n.choose k : ℝ) ≤ 16 := by
    intro n k hn
    have h1 : n.choose k ≤ 2 ^ n := Nat.choose_le_two_pow n k
    have h2 : 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hn
    have h3 : n.choose k ≤ 16 := by simpa using le_trans h1 h2
    exact_mod_cast h3
  rw [ProdOpen.leibniz_open_mixed b j f g hf hg z θ hz hθ0 hθ1]
  calc |∑ a ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (b + 1),
          ((j.choose a : ℝ) * (b.choose c : ℝ))
            * (Work.Spaces.mixed c a f z θ * Work.Spaces.mixed (b - c) (j - a) g z θ)|
      ≤ ∑ a ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (b + 1),
          |((j.choose a : ℝ) * (b.choose c : ℝ))
            * (Work.Spaces.mixed c a f z θ * Work.Spaces.mixed (b - c) (j - a) g z θ)| := by
        refine le_trans (Finset.abs_sum_le_sum_abs
          (fun a => ∑ c ∈ Finset.range (b + 1),
            ((j.choose a : ℝ) * (b.choose c : ℝ))
              * (Work.Spaces.mixed c a f z θ * Work.Spaces.mixed (b - c) (j - a) g z θ))
          (Finset.range (j + 1))) ?_
        exact Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (b + 1),
          (256 * (WDp 4 f * WDp 4 g)) := by
        refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun c hc => ?_
        have haj : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        have hcb : c ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
        have hb4 : b ≤ 4 := by omega
        have hj4 : j ≤ 4 := by omega
        have hca : c + a ≤ 4 := by omega
        have hca' : (b - c) + (j - a) ≤ 4 := by omega
        rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
          abs_mul]
        have h1 : (j.choose a : ℝ) * (b.choose c : ℝ) ≤ 16 * 16 :=
          mul_le_mul (hcoef j a hj4) (hcoef b c hb4) (Nat.cast_nonneg _) (by norm_num)
        have h2 : |Work.Spaces.mixed c a f z θ| * |Work.Spaces.mixed (b - c) (j - a) g z θ|
            ≤ WDp 4 f * WDp 4 g :=
          mul_le_mul (hX c a hca) (hY (b - c) (j - a) hca') (abs_nonneg _) hWf
        calc (j.choose a : ℝ) * (b.choose c : ℝ)
              * (|Work.Spaces.mixed c a f z θ| * |Work.Spaces.mixed (b - c) (j - a) g z θ|)
            ≤ (16 * 16) * (WDp 4 f * WDp 4 g) :=
              mul_le_mul h1 h2 (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
          _ = 256 * (WDp 4 f * WDp 4 g) := by norm_num
    _ = ((j + 1) * (b + 1) : ℝ) * (256 * (WDp 4 f * WDp 4 g)) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
          Nat.cast_one]
        ring
    _ ≤ 25 * (256 * (WDp 4 f * WDp 4 g)) := by
        have h1 : ((j + 1) * (b + 1) : ℕ) ≤ 25 := by
          have hb : b + 1 ≤ 5 := by omega
          have hj : j + 1 ≤ 5 := by omega
          calc (j + 1) * (b + 1) ≤ 5 * 5 := Nat.mul_le_mul hj hb
            _ = 25 := by norm_num
        have h1' : ((j + 1) * (b + 1) : ℝ) ≤ 25 := by exact_mod_cast h1
        exact mul_le_mul_of_nonneg_right h1' (mul_nonneg (by norm_num) hWfg)
    _ = 6400 * (WDp 4 f * WDp 4 g) := by ring

/-! ## The product rule -/

theorem wmul_field :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f g : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
      Work.FTS.VocabO.WDMem 4 f → Work.FTS.VocabO.WDMem 4 g →
      (∀ k : ℕ, k ≤ 4 → ∀ z : ℝ,
        Work.Spaces.pzIter k g z 0 = 0 ∧ Work.Spaces.pzIter k g z (π / 2) = 0) →
      Work.FTS.VocabO.WDMem 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.VocabO.WDp 4 (fun z θ => f z θ * g z θ)
        ≤ C * Work.FTS.VocabO.WDp 4 f * Work.FTS.VocabO.WDp 4 g := by
  refine ⟨160000, by norm_num, ?_⟩
  intro α _hα _hα1 f g hf hg hfm hgm _hbdy
  have hpoint : ∀ b j : ℕ, b + j ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b j (fun z θ => f z θ * g z θ) z θ|
        ≤ 6400 * (WDp 4 f * WDp 4 g) :=
    fun b j hbj => mixed_mul_abs_le hf hg hfm hgm hbj
  have hMnn : 0 ≤ 6400 * (WDp 4 f * WDp 4 g) :=
    mul_nonneg (by norm_num) (mul_nonneg (WDp_nonneg 4 f) (WDp_nonneg 4 g))
  refine ⟨fun b j hbj => ⟨6400 * (WDp 4 f * WDp 4 g), hpoint b j hbj⟩, ?_⟩
  calc WDp 4 (fun z θ => f z θ * g z θ)
      ≤ 25 * (6400 * (WDp 4 f * WDp 4 g)) :=
        WDp_le_of_pointwise (α := 0) hMnn hpoint
    _ = 160000 * WDp 4 f * WDp 4 g := by ring

end Work.FTS.OpenPkg
