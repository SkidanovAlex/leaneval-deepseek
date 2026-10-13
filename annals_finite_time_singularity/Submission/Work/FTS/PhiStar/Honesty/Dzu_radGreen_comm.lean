/-
# `Work.FTS.PhiStar.Honesty.Dzu_radGreen_comm`

The univariate operator `Dzu i = (z ∂_z)^i` (`Work.FTS.EllExist.Honesty.Dzu`) commutes with the
mode-`m` radial Green operator:

  `Dzu l (radGreen α m c) = radGreen α m (Dzu l c)`   on `(0, ∞)`,

for a source `c` that is `C^{l+1}` on `(0,∞)` and *compactly supported away from `0`*
(`c` vanishes off `[a,b]` with `0 < a ≤ b`).

Math.  `radGreen α m c` is the decaying-at-`∞` solution of the mode-`m` radial Euler equation
`R a = c`, `R = -(α²(z∂_z)² + α(5+α)(z∂_z)) + λ_m`; since `R` is a polynomial in `D = z∂_z` it
commutes with `D`, so `R (D a) = D c`, and the solution of the same problem with source `D c` is
`radGreen α m (D c)` — the content of the statement.  Formally we avoid any uniqueness argument
and use the *explicit* Green function: the single-step commutation

  `z ∂_z (radGreen α m f) z = radGreen α m (z ∂_z f) z`

is `Work.FTS.ClassCHon.Zpz.radGreen_Dz`, whose proof is the pair of integration-by-parts
identities for the two primitives of the Green function; it asks for `f` differentiable on
`(0,∞)` (so that `deriv f` is honest there) and for the four weighted integrals
`∫_{0}^{1} f t^{q-1}`, `∫_{1}^{∞} f t^{-p-1}`, and the same two with `f` replaced by `t ∂_t f`
(`q = (2m+5)/α`, `p = 2m/α`).  Under compact support all four are immediate, and we do not even
need the `L²`-weighted hypotheses that the other consumer of `radGreen_Dz` uses: continuity +
support in `[a,b] ⊆ (0,∞)` already gives global integrability of every weighted integrand
(`integrable_mul_rpow_of_support`).

The statement is then proved by induction on `l` (`dzu_radGreen_comm_aux`); the induction step
needs, for the source `Dzu n c`,

* `C^1` on `(0,∞)` — from `ContDiffOn.honesty.contDiffOn_Dzu` (the `n`-th `Dzu`-iterate of a
  `C^{n+1}` function is `C^1`);
* the *same* for `t ↦ t ∂_t (Dzu n c) t`, which is `Dzu (n+1) c` definitionally;
* support in `[a,b]` — `deriv` of a function vanishing on the (open) complement of `[a,b]`
  vanishes there too (`deriv_eq_zero_of_notMem_Icc`), which propagates
  (`Dzu_eq_zero_of_support`).

Everything below is complete; the only axioms used are `propext`, `Classical.choice`,
`Quot.sound`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.ClassCHon.Zpz.radGreen_Dz
import Submission.Work.FTS.EllExist.Honesty.RadGreenDzuDefs
import Submission.Work.FTS.EllExist.Honesty.dzu_differentiableAt
import Submission.Work.FTS.PhiStar.Radial.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

/-- If `f` vanishes off the closed interval `[a,b]`, then so does `deriv f`: the complement of
`[a,b]` is open, so `f` is *eventually* `0` near every point of it. -/
theorem deriv_eq_zero_of_notMem_Icc {f : ℝ → ℝ} {a b : ℝ}
    (hsupp : ∀ t : ℝ, t ∉ Set.Icc a b → f t = 0) :
    ∀ t : ℝ, t ∉ Set.Icc a b → deriv f t = 0 := by
  intro t ht
  have hcompl : t ∈ (Set.Icc a b)ᶜ := ht
  have hev : f =ᶠ[𝓝 t] 0 := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hcompl] with s hs
    exact hsupp s hs
  rw [hev.deriv_eq]
  simp

/-- A function continuous on `(0,∞)` and supported in `[a,b]` with `0 < a` gives an integrable
function after multiplication with any real power `t^s`: the product is continuous on the
compact set `[a,b] ⊆ (0,∞)` and vanishes outside it. -/
theorem integrable_mul_rpow_of_support {f : ℝ → ℝ} {a b s : ℝ} (ha : 0 < a)
    (hf : ContinuousOn f (Set.Ioi 0))
    (hsupp : ∀ t : ℝ, t ∉ Set.Icc a b → f t = 0) :
    Integrable (fun t : ℝ => f t * t ^ s) := by
  have hg : ContinuousOn (fun t : ℝ => f t * t ^ s) (Set.Icc a b) := by
    have h1 : ContinuousOn f (Set.Icc a b) := hf.mono (fun t ht => lt_of_lt_of_le ha ht.1)
    have h2 : ContinuousOn (fun t : ℝ => t ^ s) (Set.Icc a b) :=
      continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le ha ht.1)))
    exact h1.mul h2
  have hI : IntegrableOn (fun t : ℝ => f t * t ^ s) (Set.Icc a b) :=
    hg.integrableOn_compact isCompact_Icc
  have hind : (Set.Icc a b).indicator (fun t : ℝ => f t * t ^ s) = fun t => f t * t ^ s := by
    funext t
    by_cases ht : t ∈ Set.Icc a b
    · simp [Set.indicator_of_mem ht]
    · simp [Set.indicator_of_notMem ht, hsupp t ht]
  rw [← hind]
  exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).2 hI

/-- The compact support of `c` propagates to every iterated `Dzu`-derivative: `Dzu n c` vanishes
off `[a,b]` as well. -/
theorem Dzu_eq_zero_of_support {c : ℝ → ℝ} {a b : ℝ}
    (hsupp : ∀ t : ℝ, t ∉ Set.Icc a b → c t = 0) :
    ∀ (n : ℕ) (t : ℝ), t ∉ Set.Icc a b → Work.FTS.EllExist.Honesty.Dzu n c t = 0 := by
  intro n
  induction n with
  | zero => intro t ht; exact hsupp t ht
  | succ k ih =>
      intro t ht
      simp only [Work.FTS.EllExist.Honesty.Dzu_succ]
      rw [deriv_eq_zero_of_notMem_Icc (f := Work.FTS.EllExist.Honesty.Dzu k c) ih t ht, mul_zero]

/-- **`radGreen_Dz` with the four integrability hypotheses discharged from compact support.**
For `f` of class `C^1` on `(0,∞)`, with `t ↦ t ∂_t f t` also `C^1` there, and `f` supported in
`[a,b]` (`0 < a`),

  `z ∂_z (radGreen α m f) z = radGreen α m (z ∂_z f) z`   for `z > 0`. -/
theorem radGreen_Dz_support {α : ℝ} (hα : 0 < α) (m : ℕ) {a b : ℝ} (ha : 0 < a)
    {f : ℝ → ℝ} (hf1 : ContDiffOn ℝ 1 f (Set.Ioi 0))
    (hf2 : ContDiffOn ℝ 1 (fun t : ℝ => t * deriv f t) (Set.Ioi 0))
    (hsupp : ∀ t : ℝ, t ∉ Set.Icc a b → f t = 0) :
    ∀ z : ℝ, 0 < z →
      z * deriv (Work.FTS.PhiStar.Radial.radGreen α m f) z
        = Work.FTS.PhiStar.Radial.radGreen α m (fun t => t * deriv f t) z := by
  have hd0 := deriv_eq_zero_of_notMem_Icc hsupp
  have hsupp' : ∀ t : ℝ, t ∉ Set.Icc a b → t * deriv f t = 0 := by
    intro t ht
    rw [hd0 t ht, mul_zero]
  have hcont : ContinuousOn (fun t : ℝ => t * deriv f t) (Set.Ioi 0) := hf2.continuousOn
  have hcd : ∀ t : ℝ, 0 < t → HasDerivAt f (deriv f t) t := by
    intro t ht
    have hd : DifferentiableAt ℝ f t :=
      (hf1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds ht)
    exact hd.hasDerivAt
  have h0 : IntegrableOn (fun t : ℝ => f t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1) :=
    (integrable_mul_rpow_of_support (a := a) (b := b) ha hf1.continuousOn hsupp).integrableOn
  have hinf : IntegrableOn (fun t : ℝ => f t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1) :=
    (integrable_mul_rpow_of_support (a := a) (b := b) ha hf1.continuousOn hsupp).integrableOn
  have hd0' : IntegrableOn
      (fun t : ℝ => t * deriv f t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1) :=
    (integrable_mul_rpow_of_support (a := a) (b := b) ha hcont hsupp').integrableOn
  have hdinf : IntegrableOn
      (fun t : ℝ => t * deriv f t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1) :=
    (integrable_mul_rpow_of_support (a := a) (b := b) ha hcont hsupp').integrableOn
  exact Work.FTS.ClassCHon.Zpz.radGreen_Dz hα m hcd h0 hinf hd0' hdinf

/-- The induction behind `Dzu_radGreen_comm`, stated with the smoothness order `M` of `c` as a
free parameter (so that the induction hypothesis can be applied at the lower order `M`, which is
all the step for `n` needs). -/
theorem dzu_radGreen_comm_aux {α : ℝ} (hα : 0 < α) (m : ℕ) {a b : ℝ} (ha : 0 < a)
    {c : ℝ → ℝ} (hsupp : ∀ t : ℝ, t ∉ Set.Icc a b → c t = 0) :
    ∀ (n : ℕ) (M : WithTop ℕ∞), ((n + 1 : ℕ) : WithTop ℕ∞) ≤ M →
      ContDiffOn ℝ M c (Set.Ioi 0) →
      ∀ z : ℝ, 0 < z →
        Work.FTS.EllExist.Honesty.Dzu n (Work.FTS.PhiStar.Radial.radGreen α m c) z
          = Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.EllExist.Honesty.Dzu n c) z := by
  intro n
  induction n with
  | zero =>
      intro M _ _ z _
      simp [Work.FTS.EllExist.Honesty.Dzu_zero]
  | succ n ih =>
      intro M hM hc z hz
      have hM' : ((n + 1 : ℕ) : WithTop ℕ∞) ≤ M := by
        refine le_trans ?_ hM
        exact_mod_cast (by omega : n + 1 ≤ n + 2)
      have hrec : ∀ w : ℝ, 0 < w →
          Work.FTS.EllExist.Honesty.Dzu n (Work.FTS.PhiStar.Radial.radGreen α m c) w
            = Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.EllExist.Honesty.Dzu n c) w :=
        ih M hM' hc
      -- `Dzu n c` is `C^1` on `(0,∞)` (the iterate of a `C^{n+2}` function)
      have hf1 : ContDiffOn ℝ 1 (Work.FTS.EllExist.Honesty.Dzu n c) (Set.Ioi 0) := by
        refine Work.FTS.EllExist.Honesty.contDiffOn_Dzu c n 1 ?_
        refine hc.of_le ?_
        have hcast : ((1 : WithTop ℕ∞) + (n : WithTop ℕ∞)) = ((n + 1 : ℕ) : WithTop ℕ∞) := by
          push_cast
          ring
        rw [hcast]
        exact hM'
      -- and so is `t ↦ t ∂_t (Dzu n c) t = Dzu (n+1) c t`
      have hf2 : ContDiffOn ℝ 1 (fun t : ℝ => t * deriv (Work.FTS.EllExist.Honesty.Dzu n c) t)
          (Set.Ioi 0) := by
        rw [← Work.FTS.EllExist.Honesty.Dzu_succ n c]
        refine Work.FTS.EllExist.Honesty.contDiffOn_Dzu c (n + 1) 1 ?_
        refine hc.of_le ?_
        have hcast : ((1 : WithTop ℕ∞) + ((n + 1 : ℕ) : WithTop ℕ∞))
            = ((n + 2 : ℕ) : WithTop ℕ∞) := by
          push_cast
          ring
        rw [hcast]
        exact hM
      have hsupn := Dzu_eq_zero_of_support hsupp n
      have hstep := radGreen_Dz_support (a := a) (b := b) hα m ha hf1 hf2 hsupn z hz
      -- the induction hypothesis identifies the two functions on the neighbourhood `(0,∞)`
      have hderiv : deriv (Work.FTS.EllExist.Honesty.Dzu n
            (Work.FTS.PhiStar.Radial.radGreen α m c)) z
          = deriv (Work.FTS.PhiStar.Radial.radGreen α m
            (Work.FTS.EllExist.Honesty.Dzu n c)) z := by
        refine Filter.EventuallyEq.deriv_eq ?_
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact hrec w hw
      calc Work.FTS.EllExist.Honesty.Dzu (n + 1)
              (Work.FTS.PhiStar.Radial.radGreen α m c) z
          = z * deriv (Work.FTS.PhiStar.Radial.radGreen α m
              (Work.FTS.EllExist.Honesty.Dzu n c)) z := by
            simp only [Work.FTS.EllExist.Honesty.Dzu_succ, hderiv]
        _ = Work.FTS.PhiStar.Radial.radGreen α m
              (fun t => t * deriv (Work.FTS.EllExist.Honesty.Dzu n c) t) z := hstep
        _ = Work.FTS.PhiStar.Radial.radGreen α m
              (Work.FTS.EllExist.Honesty.Dzu (n + 1) c) z := by
            rw [Work.FTS.EllExist.Honesty.Dzu_succ]

theorem Dzu_radGreen_comm {α : ℝ} (hα : 0 < α) (m l : ℕ) {c : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hc : ContDiffOn ℝ (l + 1 : ℕ) c (Set.Ioi 0))
    (hsupp : ∀ t : ℝ, t ∉ Set.Icc a b → c t = 0) :
    ∀ z : ℝ, 0 < z →
      Work.FTS.EllExist.Honesty.Dzu l (Work.FTS.PhiStar.Radial.radGreen α m c) z
        = Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.EllExist.Honesty.Dzu l c) z :=
  dzu_radGreen_comm_aux hα m ha hsupp l ((l + 1 : ℕ) : WithTop ℕ∞) le_rfl hc

end Work.FTS.PhiStar.Honesty
