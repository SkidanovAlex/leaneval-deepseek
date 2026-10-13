import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.DzIter_mul_smoothQuad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.E2Bound

open scoped Real Topology
open Set Filter

set_option autoImplicit false

/-! ### Auxiliary lemmas

The two private lemmas below are the route (i)–(iii) of the docstring of `mixed_zmul`:
the unconditional scalar linearity of `deriv`, and the commutation of `D_θ^i` with
multiplication by a factor depending only on `z`. -/

/-- `deriv` is scalar homogeneous **unconditionally**, unlike Mathlib's `deriv_const_mul`,
which needs differentiability: if `f` is not differentiable at `x` then neither is `c * f`
for `c ≠ 0`, so both sides are `0`. -/
private theorem deriv_const_mul_uncond (c x : ℝ) (f : ℝ → ℝ) :
    deriv (fun y => c * f y) x = c * deriv f x := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ f x) with hf | hf
    · exact deriv_const_mul c hf
    · have h2 : ¬ DifferentiableAt ℝ (fun y => c * f y) x := by
        intro hh
        apply hf
        have he : f = fun y => c⁻¹ * (c * f y) := by
          funext y; rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
        rw [he]
        exact hh.const_mul c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf,
        deriv_zero_of_not_differentiableAt h2, mul_zero]

/-- `D_θ^i` commutes with multiplication by a factor depending only on `z`.  No smoothness
is needed: the only ingredient is the unconditional scalar linearity of `deriv`. -/
private theorem DthIter_zmul (i : ℕ) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => a z * f z θ)
      = fun z θ => a z * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp only [Work.Spaces.DthIter_succ] at ih ⊢
      rw [ih]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [deriv_const_mul_uncond]
      ring

/-- Leibniz expansion of `D_z^j D_θ^i (a · f)` when `a` depends only on `z`.

`D_θ` commutes with multiplication by a `z`-only factor, so after applying `D_θ^i` the
problem is `D_z^j (a · (D_θ^i f))`, which is the binomial expansion for the one-variable
operator `Zop = z ∂_z` acting on `a`:
`D_z^j(a·g) = ∑_{b≤j} (j.choose b) · (Zop^b a) · D_z^{j-b} g`.

ROUTE.
* (i) prove locally (private) `DthIter_zmul : DthIter i (fun z θ => a z * f z θ)
  = fun z θ => a z * DthIter i f z θ` by induction on `i`; the step is the *unconditional*
  scalar linearity of `deriv`, `deriv (fun y => c * g y) x = c * deriv g x` (if `c ≠ 0` and
  `g` is not differentiable at `x` then neither is `c * g`, and both sides are `0`) — see
  `deriv_const_mul_uncond` in `Submission/Work/FTS/LocData/HkIntegrand_const_mul.lean` for the
  exact 12-line argument.  No smoothness is needed for this identity.
* (ii) Apply the general one-operator Leibniz rule
  `Work.Spaces.DerivLike.iterate_mul Work.FTS.LocData.Zop_DerivLike_smoothZd
   Work.FTS.LocData.SmoothZsm_FunClass j haSlice hgSlice hz` with base set `Set.Ioi (-1)`
  (note `hz : z ∈ Set.Ioi (-1)`; do NOT try to use `DzIter_mul_smoothQuad`, whose hypothesis is
  the weaker-set `z ∈ Iz = Ici 0`), where `haSlice := ha.curry_z hθ` is the `C^∞`-smoothness of
  `fun z => a z` and `hgSlice := (hf.DthIter i).curry_z hθ` that of
  `fun z => DthIter i f z θ`.  Combine it with step (i) to express
  `mixed j i (fun z θ => a z * f z θ) z θ = DzIter j (fun z θ => a z * DthIter i f z θ) z θ`.
* (iii) rewrite `DzIter b (fun z θ => a z) z θ = Zop^[b] a z` by
  `congrFun (Work.FTS.LocData.Zop_iterate_slice b (fun z θ => a z) θ) z` and
  `DzIter (j - b) (DthIter i f) = mixed (j - b) i f` by `rfl`.

The imports are listed in `depends_on`.  Nothing of the requester's own machinery is needed and
the file must be self-contained (do not import the requester's files). -/
theorem mixed_zmul (j i : ℕ) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : z ∈ Set.Ioi (-1)) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (ha : Work.FTS.LocData.SmoothQuad (fun z θ : ℝ => a z))
    (hf : Work.FTS.LocData.SmoothQuad f) :
    Work.Spaces.mixed j i (fun z θ => a z * f z θ) z θ
      = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
          (Work.Spaces.Zop^[b] a z * Work.Spaces.mixed (j - b) i f z θ) := by
  -- the two `z`-slices at `θ`, which are `C^∞` on `(-1,∞)`
  have haS := ha.curry_z hθ
  have hfS := (hf.DthIter i).curry_z hθ
  -- the one-operator Leibniz rule for `Zop = z ∂_z` at `z`
  have key := (Work.Spaces.DerivLike.iterate_mul Work.FTS.LocData.Zop_DerivLike_smoothZd
    Work.FTS.LocData.SmoothZsm_FunClass j haS hfS) hz
  -- step (i): `D_θ^i` commutes with the `z`-only factor `a`
  have hL : Work.Spaces.mixed j i (fun z θ => a z * f z θ) z θ
      = Work.Spaces.Zop^[j] ((fun z : ℝ => a z)
          * (fun z : ℝ => Work.Spaces.DthIter i f z θ)) z := by
    rw [Work.Spaces.mixed, DthIter_zmul i a f]
    exact congrFun (Work.FTS.LocData.Zop_iterate_slice j
      (fun z θ => a z * Work.Spaces.DthIter i f z θ) θ) z
  rw [hL, key]
  -- step (iii): identify the two factors of each summand
  apply Finset.sum_congr rfl
  intro b hb
  have h1 : Work.Spaces.Zop^[b] (fun z : ℝ => a z) z = Work.Spaces.Zop^[b] a z := rfl
  have h2 : Work.Spaces.Zop^[j - b] (fun z : ℝ => Work.Spaces.DthIter i f z θ) z
      = Work.Spaces.mixed (j - b) i f z θ := by
    rw [Work.Spaces.mixed]
    exact (congrFun (Work.FTS.LocData.Zop_iterate_slice (j - b)
      (Work.Spaces.DthIter i f) θ) z).symm
  rw [h1, h2]

end Work.FTS.CoercivityFix.E2Bound
