import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS_RegExport.RXT.Slots.v2_paramC2
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.EllipticEst.Blocks.LopIter_sin_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

set_option autoImplicit false

/-! ## Auxiliary facts: the iterates of `sin(2θ)²` are multiples of `sin(2θ)²`

For use outside the `private` scope of `Blocks.slice_f_bound` we reproduce the three
elementary facts underlying the proof:

* `deriv_sin_two`: `(sin 2θ)' = 2 cos 2θ`;
* `Lop_sin_sq`: `L (sin²θ) = sin(2θ)²` for `L = sin(2θ) ∂_θ`;
* `LopIter_sin_sq_factor`: `L^a (sin(2θ)²) = sin(2θ)² · gfun a`;
* `exists_bound_gfun`: the finitely many coefficients `gfun i`, `i ≤ k`, are bounded on the
  compact interval `Iθ = [0, π/2]` by a strictly positive constant (each `gfun i` is `C^∞`). -/

/-- `deriv (fun t => sin (2t)) θ = 2 cos (2θ)`. -/
private lemma deriv_sin_two (θ : ℝ) :
    deriv (fun t : ℝ => Real.sin (2 * t)) θ = 2 * Real.cos (2 * θ) := by
  have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul (2 : ℝ))
  simpa [Function.comp_def, mul_comm] using h.deriv

/-- The operator `L = sin(2θ) ∂_θ` maps the function `sin²θ` to `sin(2θ)²`. -/
private lemma Lop_sin_sq :
    Work.Spaces.Lop (fun θ : ℝ => Real.sin θ ^ 2)
      = fun θ : ℝ => (Real.sin (2 * θ)) ^ 2 := by
  funext θ
  have hd : deriv (fun t : ℝ => Real.sin t ^ 2) θ = 2 * Real.sin θ * Real.cos θ := by
    have h := (Real.hasDerivAt_sin θ).pow 2
    simpa using h.deriv
  simp only [Work.Spaces.Lop, hd]
  rw [Real.sin_two_mul]
  ring

/-- The coefficient factorisation `L^a (sin(2θ)²) = sin(2θ)² · gfun a`. -/
private lemma LopIter_sin_sq_factor (a : ℕ) :
    LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2)
      = fun θ : ℝ => (Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.gfun a θ := by
  induction a with
  | zero => funext θ; simp
  | succ n ih =>
      rw [LopIter_succ, ih, Work.FTS.EllipticEst.gfun_succ]
      funext θ
      have hsin : DifferentiableAt ℝ (fun t : ℝ => Real.sin (2 * t)) θ := by fun_prop
      have hg : DifferentiableAt ℝ (Work.FTS.EllipticEst.gfun n) θ :=
        ((GfunContDiff n).differentiable (by simp)).differentiableAt
      have hh : DifferentiableAt ℝ
          (fun t : ℝ => Real.sin (2 * t) * Work.FTS.EllipticEst.gfun n t) θ := hsin.mul hg
      have h1 : (fun t : ℝ => (Real.sin (2 * t)) ^ 2 * Work.FTS.EllipticEst.gfun n t)
          = fun t : ℝ => Real.sin (2 * t)
              * (Real.sin (2 * t) * Work.FTS.EllipticEst.gfun n t) := by
        funext t; ring
      rw [h1, Lop_sin_mul _ θ hh]
      have hderiv : deriv (fun t : ℝ => Real.sin (2 * t) * Work.FTS.EllipticEst.gfun n t) θ
          = 2 * Real.cos (2 * θ) * Work.FTS.EllipticEst.gfun n θ
            + Real.sin (2 * θ) * deriv (Work.FTS.EllipticEst.gfun n) θ := by
        have hfun : (fun t : ℝ => Real.sin (2 * t) * Work.FTS.EllipticEst.gfun n t)
            = (fun t : ℝ => Real.sin (2 * t)) * Work.FTS.EllipticEst.gfun n := rfl
        rw [hfun, deriv_mul hsin hg, deriv_sin_two θ]
      rw [hderiv]
      ring

/-- The finitely many coefficients `gfun i`, `i ≤ K`, are bounded on the compact `Iθ` by a
strictly positive constant. -/
private theorem exists_bound_gfun (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i ≤ K, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.EllipticEst.gfun i θ| ≤ C := by
  induction K with
  | zero =>
      refine ⟨1, one_pos, ?_⟩
      intro i hi θ _
      have hi0 : i = 0 := Nat.le_zero.mp hi
      subst hi0
      simp
  | succ K ih =>
      obtain ⟨C, hCpos, hC⟩ := ih
      obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (f := Work.FTS.EllipticEst.gfun (K + 1))
        ((GfunContDiff (K + 1)).continuous.continuousOn)
      refine ⟨max C (D + 1), lt_max_of_lt_left hCpos, ?_⟩
      intro i hi θ hθ
      rcases Nat.lt_or_eq_of_le hi with hlt | heq
      · exact le_trans (hC i (Nat.lt_succ_iff.mp hlt) θ hθ) (le_max_left _ _)
      · subst heq
        have hDθ := hD θ hθ
        rw [Real.norm_eq_abs] at hDθ
        exact le_trans hDθ (le_trans (le_add_of_nonneg_right zero_le_one) (le_max_right _ _))

/-- **Divisibility of `D_θ^m (sin²θ)`, `m ≥ 1`, by `sin(2θ)`.**
PLACEMENT: file `Submission/Work/FTS/EllipticEst/Blocks/LopIter_sin_sq_le.lean`, namespace
`Work.FTS.EllipticEst.Blocks`, so the fully qualified name is
`Work.FTS.EllipticEst.Blocks.LopIter_sin_sq_le`.
There is a constant `K ≥ 0` (depending on `k`) such that for every `m ≤ k` and every
`θ ∈ (0,π/2)`,
`(LopIter (m+1) (fun θ => sin θ ^ 2) θ)² ≤ K · sin(2θ)²`,
where `LopIter` is the iterate of `L = sin(2θ)∂_θ` (`Work.FTS.EllipticEst.LopIter`,
`Submission/Work/FTS/EllipticEst/ThetaPoincareDefs.lean`).
RECOMMENDED ROUTE (all ingredients are already in the workspace and sorry-free):
* `Lop (fun θ => sin θ ^ 2) = fun θ => (sin (2θ))^2` (compute the derivative, using
  `Real.sin_two_mul`), hence `LopIter (m+1) (fun θ => sin θ ^ 2)
  = LopIter m (fun θ => (Real.sin (2 * θ))^2)` by `LopIter_succ`;
* `LopIter a (fun θ => (sin (2θ))^2) = fun θ => (sin (2θ))^2 * gfun a θ`
  (`gfun` is in `Submission/Work/FTS/EllipticEst/LopIterSinSqDefs.lean`; prove this exactly as the
  private `sfb_LopIter_sin_sq_factor` in `Submission/Work/FTS/EllipticEst/Blocks/slice_f_bound.lean`,
  using `Work.FTS.EllipticEst.Lop_sin_mul`, `Submission/Work/FTS/EllipticEst/Lop_sin_mul.lean`);
* `GfunContDiff` (`Submission/Work/FTS/EllipticEst/GfunContDiff.lean`) says each `gfun i` is
  `C^∞`, so the finitely many `|gfun i|`, `i ≤ k`, are bounded on the compact `Iθ` by some
  `C ≥ 0` (mirror the private `sfb_exists_bound_gfun` in `Blocks/slice_f_bound.lean`);
* then `(LopIter (m+1) sin² θ)² = sin(2θ)^4 · gfun m θ ^2 ≤ (sin(2θ))^2 · C^2`,
  using `0 ≤ sin(2θ) ≤ 1`; take `K := C^2`.
Do NOT use the sorry-containing `Work.FTS.EllipticEst.Lop_iter_sin_sq_bound` or
`Work.FTS.EllipticEst.Slice9.LopIterSqSin2Bound`. -/
theorem LopIter_sin_sq_le (k : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, m ≤ k →
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
    (Work.FTS.EllipticEst.LopIter (m + 1) (fun θ => Real.sin θ ^ 2) θ) ^ 2
      ≤ K * (Real.sin (2 * θ)) ^ 2 := by
  obtain ⟨C, _hCpos, hC⟩ := exists_bound_gfun k
  refine ⟨C ^ 2, sq_nonneg C, ?_⟩
  intro m hm θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθI
  have hs1 : Real.sin (2 * θ) ≤ 1 := sin_two_le_one θ
  have hstep : Work.FTS.EllipticEst.LopIter (m + 1) (fun θ : ℝ => Real.sin θ ^ 2)
      = Work.FTS.EllipticEst.LopIter m
          (Work.Spaces.Lop (fun θ : ℝ => Real.sin θ ^ 2)) := by
    simp only [LopIter]
    exact Function.iterate_succ_apply Work.Spaces.Lop m (fun θ : ℝ => Real.sin θ ^ 2)
  rw [hstep, Lop_sin_sq, LopIter_sin_sq_factor m]
  have hg : |Work.FTS.EllipticEst.gfun m θ| ≤ C := hC m hm θ hθI
  have hg2 : (Work.FTS.EllipticEst.gfun m θ) ^ 2 ≤ C ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hg 2
  have hs2 : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by nlinarith [hs0, hs1]
  have hs4 : (Real.sin (2 * θ)) ^ 4 ≤ (Real.sin (2 * θ)) ^ 2 := by
    have h2 : (0 : ℝ) ≤ (Real.sin (2 * θ)) ^ 2 := sq_nonneg _
    have h := mul_le_mul_of_nonneg_right hs2 h2
    nlinarith [h]
  calc ((Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.gfun m θ) ^ 2
      = (Real.sin (2 * θ)) ^ 4 * (Work.FTS.EllipticEst.gfun m θ) ^ 2 := by ring
    _ ≤ (Real.sin (2 * θ)) ^ 4 * C ^ 2 :=
        mul_le_mul_of_nonneg_left hg2 (by positivity)
    _ = C ^ 2 * (Real.sin (2 * θ)) ^ 4 := by ring
    _ ≤ C ^ 2 * (Real.sin (2 * θ)) ^ 2 := mul_le_mul_of_nonneg_left hs4 (sq_nonneg C)

end Work.FTS.EllipticEst.Blocks
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Blocks.slice_data_integrable_of_HkIntegrand =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

/-! ## The two scaling identities that strip the radial weight

The `j`-th summand of `HkIntegrand α k G z ·` carrying the *radial* `D_z`-weight is
`(D_z^j G z θ · w z / sin(2θ)^{η/2})²`.  By the weight identifications `w_div_sin_sq`
and `Wt_sq` of `Work.FTS.EllipticEst.SliceAux` this is

`(D_z^j G z θ)² · (w z)² · sin(2θ)^{-η}`  resp.  `(D_z^j D_θ^m G z θ)² · (w z)² · sin(2θ)^{-γ}`,

so multiplying by the *constant* `((w z)²)^{-1}` removes the factor `(w z)²` and leaves
exactly the slice integrands `(·)² · thEta θ` resp. `(·)² · thGam α θ` of the slice
estimates.  These two algebraic lemmas isolate that manipulation (which is the only place
where the hypothesis `z > 0` is used, through `w z ≠ 0`). -/

/-- For `z > 0` the radial weight `w z = (1+z)²/z²` is nonzero. -/
private lemma w_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : Work.Spaces.w z ≠ 0 := by
  have h1 : (1 + z) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith)
  have h2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
  rw [Work.Spaces.w]
  exact div_ne_zero h1 h2




end Work.FTS.EllipticEst.Blocks
end
-- ===== merged: Submission.Work.FTS.EllipticEst.ThetaSliceIdent =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## Locality of the iterated angular operator on one-variable functions -/

/-- If two functions of one variable agree near `θ`, then each of them is equal to the other
on a neighbourhood of every point of a neighbourhood of `θ`. -/
lemma eventuallyEq_nhds_mono {u v : ℝ → ℝ} {θ : ℝ} (h : u =ᶠ[𝓝 θ] v) :
    ∀ᶠ θ' in 𝓝 θ, u =ᶠ[𝓝 θ'] v := by
  obtain ⟨t, hts, htopen, hθt⟩ := mem_nhds_iff.mp h
  filter_upwards [htopen.mem_nhds hθt] with θ' hθ'
  exact eventually_of_mem (htopen.mem_nhds hθ') hts

/-- `Lop = L` only sees the germ of its argument. -/
lemma Lop_eventuallyEq {u v : ℝ → ℝ} {θ : ℝ} (h : u =ᶠ[𝓝 θ] v) :
    ∀ᶠ θ' in 𝓝 θ, Work.Spaces.Lop u θ' = Work.Spaces.Lop v θ' := by
  filter_upwards [eventuallyEq_nhds_mono h] with θ' hθ'
  simp only [Work.Spaces.Lop]
  rw [hθ'.deriv_eq]

/-- All the iterates of `Lop = L` only see the germ of their argument. -/
lemma LopIter_eventuallyEq {u v : ℝ → ℝ} {θ : ℝ} (h : u =ᶠ[𝓝 θ] v) (m : ℕ) :
    ∀ᶠ θ' in 𝓝 θ, LopIter m u θ' = LopIter m v θ' := by
  induction m with
  | zero => exact h
  | succ m ih =>
      have h' : LopIter m u =ᶠ[𝓝 θ] LopIter m v := ih
      simpa only [LopIter_succ] using Lop_eventuallyEq h'

/-- The iterates of `Lop = L` take the same value at `θ` on functions that agree near `θ`. -/
lemma LopIter_congr_nhds {u v : ℝ → ℝ} {θ : ℝ} (h : u =ᶠ[𝓝 θ] v) (m : ℕ) :
    LopIter m u θ = LopIter m v θ :=
  (LopIter_eventuallyEq h m).self_of_nhds

/-! ## The slices of `D_z^j f` on the open neighbourhood `nbhU` -/




/-! ## The two slice identities -/



end Work.FTS.EllipticEst
end
end
