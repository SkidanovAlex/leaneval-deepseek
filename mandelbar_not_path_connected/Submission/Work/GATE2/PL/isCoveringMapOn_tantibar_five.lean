/-
# `(Tantibar c)^[5]` is a covering map off its critical values

`Tantibar c z = z̄² + c` is the antiholomorphic quadratic of the tricorn family, and
`Tsq c = Tantibar c ∘ Tantibar c` (i.e. `Tsq c z = (z² + c̄)² + c`) is its holomorphic second
iterate.  This file proves that the fifth iterate `(Tantibar c)^[5]`, restricted over the
complement of its critical values `{T_c^j c : 0 ≤ j ≤ 4} = {T_c^k 0 : 1 ≤ k ≤ 5}`, is a
covering map.

The proof conjugates the antiholomorphic iterate into a *polynomial* and then appeals to
Mathlib's `Polynomial.isCoveringMapOn_eval` (a polynomial is a covering map off its critical
values), transporting along the isometry `star : ℂ ≃ₜ ℂ`:

* `Tantibar c = star ∘ (·² + c̄)`, so `(Tantibar c)^[5] = Tantibar c ∘ (Tsq c)^[2] = star ∘ p`
  where `p = (X² + c̄) ∘ (Tsq c)^[2]` is the polynomial `tantibar5Poly c`.
* The critical values of `p` are the image under `star` of points of the critical orbit of
  `Tantibar c`: a critical point of `p` is either a preimage of `0` under `(Tsq c)^[2]`
  (`p`-value `c̄`), or a critical point of `(Tsq c)^[2] = (Tantibar c)^[4]`, whose critical
  values lie on the critical orbit by `Work.ELPull.critValues_tsqIterate`.
* Hence `(star '' S)ᶜ` consists of regular values of `p`, and `IsCoveringMapOn.homeomorph_comp`
  transports the covering statement across `star`, whose involutivity turns `(star '' S)ᶜ` back
  into `Sᶜ`.
-/
import Mathlib
import Submission.Work.ELPull.isCoveringMapOn_tsqIterate
import Submission.Work.ELPull.critValues_tsqIterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Function Polynomial
open LeanEval.ComplexAnalysis (Tantibar)

namespace Work.GATE2.PL

/-! ## Complex conjugation as a homeomorphism -/

/-- Complex conjugation, as a homeomorphism of `ℂ`. -/
def conjHomeo : ℂ ≃ₜ ℂ where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  continuous_toFun := continuous_star
  continuous_invFun := continuous_star

@[simp] theorem conjHomeo_apply (z : ℂ) : conjHomeo z = star z := rfl

@[simp] theorem conjHomeo_symm_apply (z : ℂ) : conjHomeo.symm z = star z := rfl

theorem coe_conjHomeo_symm : ⇑conjHomeo.symm = (star : ℂ → ℂ) := rfl

/-! ## Conjugation of the `Tantibar` iterates -/

/-- `star` intertwines `Tantibar c` and `Tantibar c̄` (up to the order of the arguments). -/
theorem star_Tantibar (c z : ℂ) : star (Tantibar c z) = Tantibar (star c) (star z) := by
  simp [Tantibar, star_add, star_pow]

/-- `star` intertwines the iterates of `Tantibar c` and `Tantibar c̄`. -/
theorem star_Tantibar_iterate (c z : ℂ) (n : ℕ) :
    star ((Tantibar c)^[n] z) = (Tantibar (star c))^[n] (star z) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', star_Tantibar, ih]

/-! ## The polynomial conjugate to `(Tantibar c)^[5]` -/

/-- The polynomial `(Tsq c)^[2] = (Tantibar c)^[4]`, i.e. the holomorphic fourth iterate of the
tricorn map. -/
def TsqIter2Poly (c : ℂ) : ℂ[X] := Work.ELPull.polyIter (Work.ELPull.tsqPoly c) 2

/-- Evaluation of `TsqIter2Poly c` is the iterate `(Tsq c)^[2]`. -/
theorem TsqIter2Poly_eval (c z : ℂ) :
    (TsqIter2Poly c).eval z = (Work.Landing.Tsq c)^[2] z :=
  (congrFun (Work.ELPull.tsqIterate_eq_polyIter_eval c 2) z).symm

/-- The polynomial `p` whose `star`-conjugate is `(Tantibar c)^[5]`:
`p = (X² + c̄) ∘ (Tsq c)^[2]`. -/
def tantibar5Poly (c : ℂ) : ℂ[X] := (X ^ 2 + C (star c)).comp (TsqIter2Poly c)

theorem tantibar5Poly_eval (c z : ℂ) :
    (tantibar5Poly c).eval z = ((Work.Landing.Tsq c)^[2] z) ^ 2 + star c := by
  rw [tantibar5Poly, eval_comp, TsqIter2Poly_eval]
  simp

/-- `star` of the polynomial `tantibar5Poly c` is the fifth iterate of `Tantibar c`. -/
theorem star_tantibar5Poly_eval (c z : ℂ) :
    star ((tantibar5Poly c).eval z) = (Tantibar c)^[5] z := by
  have h4 : (Tantibar c)^[4] = (Work.Landing.Tsq c)^[2] := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, Function.iterate_mul,
      ← Work.ELRig.Tsq_eq_Tantibar_iterate_two]
  have h5 : (Tantibar c)^[5] z = Tantibar c ((Work.Landing.Tsq c)^[2] z) := by
    rw [Function.iterate_succ_apply', h4]
  rw [tantibar5Poly_eval, h5]
  simp [Tantibar, star_add, star_pow]

/-! ## The derivative of `tantibar5Poly` and its critical values -/

theorem eval_derivative_TsqIter2Poly (c z : ℂ) :
    eval z (derivative (TsqIter2Poly c)) = deriv ((Work.Landing.Tsq c)^[2]) z := by
  rw [← Polynomial.deriv (TsqIter2Poly c) (x := z)]
  congr 1
  funext w
  exact TsqIter2Poly_eval c w

/-- The chain rule for `tantibar5Poly c = (X² + c̄) ∘ (Tsq c)^[2]`: the multiplier factorizes
through the critical point condition of `(Tsq c)^[2]` and the vanishing of the inner iterate. -/
theorem eval_derivative_tantibar5Poly (c z : ℂ) :
    eval z (derivative (tantibar5Poly c))
      = (2 * (Work.Landing.Tsq c)^[2] z) * deriv ((Work.Landing.Tsq c)^[2]) z := by
  rw [tantibar5Poly, derivative_comp, eval_mul, eval_comp, TsqIter2Poly_eval,
    eval_derivative_TsqIter2Poly]
  have hd : eval ((Work.Landing.Tsq c)^[2] z) (derivative (X ^ 2 + C (star c) : ℂ[X]))
      = 2 * (Work.Landing.Tsq c)^[2] z := by
    rw [derivative_add, derivative_C, add_zero, derivative_X_pow]
    norm_num
  rw [hd]
  ring

/-- If `z` is a critical point of `(Tsq c)^[2] = (Tantibar c)^[4]`, then `(Tantibar c)^[5] z`
lies on the critical orbit of `Tantibar c`: it is `(Tantibar c)^[j] c` for some `j ≤ 4`. -/
theorem tantibar5_iterate_mem_of_deriv_eq_zero (c z : ℂ)
    (hz : deriv ((Work.Landing.Tsq c)^[2]) z = 0) :
    ∃ j : ℕ, j ≤ 4 ∧ (Tantibar c)^[5] z = (Tantibar c)^[j] c := by
  obtain ⟨k, hk, hkz⟩ := Work.ELPull.critValues_tsqIterate (c := c) 2 z hz
  rw [Finset.mem_Icc] at hk
  have h5 : (Tantibar c)^[5] z = Tantibar c ((Work.Landing.Tsq c)^[2] z) := by
    have h4 : (Tantibar c)^[4] = (Work.Landing.Tsq c)^[2] := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, Function.iterate_mul,
        ← Work.ELRig.Tsq_eq_Tantibar_iterate_two]
    rw [Function.iterate_succ_apply', h4]
  have hTc : Tantibar c 0 = c := by simp [Tantibar]
  have hstep : Tantibar c ((Tantibar c)^[k] 0) = (Tantibar c)^[k] c := by
    rw [(Function.iterate_succ_apply' (Tantibar c) k 0).symm, Function.iterate_succ_apply, hTc]
  exact ⟨k, hk.2, by rw [h5, hkz, hstep]⟩

/-- Every critical value of `tantibar5Poly c`, conjugated by `star`, lies on the critical orbit
of `Tantibar c`.  Equivalently: the critical values of `(Tantibar c)^[5]` lie in
`{T_c^j c : 0 ≤ j ≤ 4}`. -/
theorem critValue_star_mem (c z : ℂ)
    (hz : eval z (derivative (tantibar5Poly c)) = 0) :
    ∃ j : ℕ, j ≤ 4 ∧ star ((tantibar5Poly c).eval z) = (Tantibar c)^[j] c := by
  rw [eval_derivative_tantibar5Poly] at hz
  rcases mul_eq_zero.mp hz with h0 | hd
  · have hz0 : (Work.Landing.Tsq c)^[2] z = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h (by norm_num)
      · exact h
    refine ⟨0, by norm_num, ?_⟩
    have : star ((tantibar5Poly c).eval z) = c := by
      rw [tantibar5Poly_eval, hz0]
      simp
    rw [this]
    rfl
  · obtain ⟨j, hj, hjval⟩ := tantibar5_iterate_mem_of_deriv_eq_zero c z hd
    exact ⟨j, hj, by rw [star_tantibar5Poly_eval]; exact hjval⟩

/-- `tantibar5Poly c` is a covering map off the `star`-conjugate of the critical orbit of
`Tantibar c`. -/
theorem isCoveringMapOn_tantibar5Poly (c : ℂ) :
    IsCoveringMapOn (tantibar5Poly c).eval
      (star '' {z : ℂ | ∃ j : ℕ, j ≤ 4 ∧ z = (Tantibar c)^[j] c})ᶜ := by
  refine (Polynomial.isCoveringMapOn_eval (tantibar5Poly c)).mono ?_
  intro y hy
  simp only [Set.mem_compl_iff, Set.mem_image, Set.mem_ofPred_eq] at hy ⊢
  rintro ⟨z, hz, hzy⟩
  obtain ⟨j, hj, hjval⟩ := critValue_star_mem c z hz
  exact hy ⟨star ((tantibar5Poly c).eval z), ⟨j, hj, hjval⟩, by rw [star_star, hzy]⟩

/-! ## The covering map -/

/-- `(T_c)^[5]`, the antiholomorphic fifth iterate of the tricorn map `T_c`, is a covering map
off its critical values `{T_c^[j] c : 0 ≤ j ≤ 4}` (equivalently `{T_c^[k] 0 : 1 ≤ k ≤ 5}`). -/
theorem isCoveringMapOn_tantibar_five (c : ℂ) :
    IsCoveringMapOn ((LeanEval.ComplexAnalysis.Tantibar c)^[5])
      ({z : ℂ | ∃ j : ℕ, j ≤ 4 ∧ z = (LeanEval.ComplexAnalysis.Tantibar c)^[j] c})ᶜ := by
  have h2 := (isCoveringMapOn_tantibar5Poly c).homeomorph_comp conjHomeo
  have hset : ⇑conjHomeo.symm ⁻¹'
      (star '' {z : ℂ | ∃ j : ℕ, j ≤ 4 ∧ z = (Tantibar c)^[j] c})ᶜ
      = ({z : ℂ | ∃ j : ℕ, j ≤ 4 ∧ z = (Tantibar c)^[j] c})ᶜ := by
    rw [coe_conjHomeo_symm, Set.preimage_compl, Set.preimage_image_eq _ star_injective]
  rw [hset] at h2
  have hfun : (⇑conjHomeo ∘ fun x => Polynomial.eval x (tantibar5Poly c))
      = (Tantibar c)^[5] := by
    funext z
    simpa only [Function.comp_apply, conjHomeo_apply] using star_tantibar5Poly_eval c z
  rw [hfun] at h2
  exact h2

/-- The covering property may be restricted to any subset of the regular values. -/
theorem isCoveringMapOn_tantibar_five_mono (c : ℂ) {s : Set ℂ}
    (hs : s ⊆
      ({z : ℂ | ∃ j : ℕ, j ≤ 4 ∧ z = (LeanEval.ComplexAnalysis.Tantibar c)^[j] c})ᶜ) :
    IsCoveringMapOn ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) s :=
  (isCoveringMapOn_tantibar_five c).mono hs

/-- The iterate `(T_c)^[5]` is a local homeomorphism off the preimage of its critical values. -/
theorem isLocalHomeomorphOn_tantibar_five (c : ℂ) :
    IsLocalHomeomorphOn ((LeanEval.ComplexAnalysis.Tantibar c)^[5])
      (((LeanEval.ComplexAnalysis.Tantibar c)^[5]) ⁻¹'
        ({z : ℂ | ∃ j : ℕ, j ≤ 4 ∧ z = (LeanEval.ComplexAnalysis.Tantibar c)^[j] c})ᶜ) :=
  (isCoveringMapOn_tantibar_five c).isLocalHomeomorphOn

end Work.GATE2.PL
