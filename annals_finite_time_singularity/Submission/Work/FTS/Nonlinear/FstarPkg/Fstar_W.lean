/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `F_*`-package, `𝒲^{4,∞}`-part: `Fstar_W`

This proves the design statement `Fstar_W` of `FTS/N45_DESIGN_LEAD.md` §3.2 (row 1 of the
table of `Submission/Work/FTS/Nonlinear/NOTES_N4.md`, §"F_* package"):

  `𝒲^{4,∞}(F_*) ≤ C α`, with `C` universal, for every `0 < α ≤ 1`,

where `F_*(z,θ) = α (Γ(θ)/c) · 2z/(1+z)²` is the profile of `Work.Construction.Fstar`
(paper tex 1334), `Γ(θ) = (sin θ cos²θ)^{α/3}` and `c = ∫_{Iθ} Γ K`.

## Mathematics

Everything is a consequence of the *separation of variables*
`F_* = a · (Γ ⊗ h)`, with `h(z) = z/(1+z)²` and `a = 2α/c`, together with the two
elementary estimates of the paper's `ΓRegularity`:

* `|Γ(θ)| ≤ 1` on `Iθ` (`Gam_bounds`);
* `α · Γ(θ) · sin(2θ)^{-α/5}/(α + sin 2θ) ≤ 1` on `Iθ` (`Gam_mul_weight_le`);
* `|(1+z)^k h^{(k)}(z)| ≤ k! (k+1)` for `z ≥ 0` (`pzIter_hKer_bound`);
* `|D_θ^m Γ(θ)| ≤ α · tBound (m-1) 0 · Γ(θ)` for `m ≥ 1` (`dthU_Gam_le`);
* `1/10 ≤ c(α)` (`c_bounds`), so that `|a| ≤ 20 α`.

Since both `D_z`- and `D_θ`-iterates of `F_*` are again products `(θ-factor) · (z-factor)`,
the `𝒲^{4,∞}`-summands factorize, and the `z`-part is bounded by the universal constant
`k! (k+1)` while the `θ`-part carries exactly one factor `α` — the `Γ`-factor is consumed
by the weight `sin(2θ)^{-α/5}/(α+sin 2θ)`.  This yields, with an explicit universal
constant `KB`,

  `𝒲^{4,∞}(F_*) ≤ 20 α · KB`,

and `WlInfMem` holds with the same pointwise bounds (each summand is bounded by the very
same explicit constant, so every `SupFinite` predicate is witnessed by it).

The function `pzIter k (F_*)` is the `k`-fold iterated `z`-derivative, `DthIter j` the
`j`-fold iterated `D_θ = sin(2θ)∂_θ`; the helpers `pzIter_Fstar_eq` /
`pzIter_DthIter_Fstar_eq` record the factorization, and `Fstar_z_bound` /
`Fstar_mixed_bound` the two pointwise estimates.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Spaces.c_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.FstarPkg

set_option autoImplicit false

/-! ## The factorization `F_* = a · (Γ ⊗ h)` and its iterated derivatives -/

/-- `F_*(z,θ) = a · Γ(θ) · h(z)` with `a = 2α/c` and `h(z) = z/(1+z)²`: the profile of the
paper is the product of the angular factor `Γ` and the radial factor `h`. -/
lemma Fstar_eq_factored (α : ℝ) :
    Work.Construction.Fstar α
      = fun z θ => ((2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ) * Work.Spaces.hKer z := by
  funext z θ
  simp only [Work.Construction.Fstar, Work.FM.Fstar, Work.Spaces.hKer]
  ring

/-- The `z`-iterates of `F_*` factor through the `z`-iterates of `h = z/(1+z)²`. -/
lemma pzIter_Fstar_eq (α : ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (Work.Construction.Fstar α) z θ
      = ((2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ) * deriv^[k] Work.Spaces.hKer z := by
  rw [Fstar_eq_factored α, Work.Spaces.pzIter_decomp]

/-- `D_θ^j F_* = a · (D_θ^j Γ) ⊗ h`: the angular operator `D_θ = sin(2θ)∂_θ` acts only on
`Γ`. -/
lemma DthIter_Fstar_eq (α : ℝ) (j : ℕ) :
    Work.Spaces.DthIter j (Work.Construction.Fstar α)
      = fun z θ => ((2 * α / Work.Spaces.c α)
          * (Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t)) θ) * Work.Spaces.hKer z := by
  funext z θ
  rw [Fstar_eq_factored α, Work.Spaces.DthIter_decomp]
  simp only [Work.Spaces.dthU_iter_const_mul]

/-- The mixed iterates of `F_*`: `∂_z^k D_θ^j F_* = a · (D_θ^j Γ) ⊗ h^{(k)}`. -/
lemma pzIter_DthIter_Fstar_eq (α : ℝ) (j k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (Work.Spaces.DthIter j (Work.Construction.Fstar α)) z θ
      = ((2 * α / Work.Spaces.c α)
          * (Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t)) θ)
          * deriv^[k] Work.Spaces.hKer z := by
  rw [DthIter_Fstar_eq α j, Work.Spaces.pzIter_decomp]

/-! ## The two pointwise estimates -/

/-- The prefactor `a = 2α/c` is bounded by `20 α`, since `c(α) ≥ 1/10`. -/
lemma Fstar_coef_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    |2 * α / Work.Spaces.c α| ≤ 20 * α := by
  have hc := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hnum : 0 ≤ 2 * α := by linarith
  rw [abs_of_nonneg (div_nonneg hnum (le_of_lt hcpos))]
  rw [div_le_iff₀ hcpos]
  nlinarith

/-- The radial `𝒲^{4,∞}`-summands of `F_*` are bounded by `20 α · k!(k+1)`. -/
lemma Fstar_z_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (z θ : ℝ)
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Construction.Fstar α) z θ| ≤
      20 * α * ((k.factorial : ℝ) * (k + 1)) := by
  have hcoef := Fstar_coef_le α hα hα1
  have hGam := Work.Spaces.Gam_bounds α θ hα hθ
  have hker : |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z| ≤ (k.factorial : ℝ) * (k + 1) :=
    Work.Spaces.pzIter_hKer_bound k z hz
  rw [pzIter_Fstar_eq]
  rw [show (z + 1) ^ k * (((2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ)
        * deriv^[k] Work.Spaces.hKer z)
      = ((2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ)
        * ((z + 1) ^ k * deriv^[k] Work.Spaces.hKer z) by ring]
  rw [abs_mul]
  have h1 : |(2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ| ≤ 20 * α := by
    rw [abs_mul, abs_of_nonneg hGam.1]
    calc |2 * α / Work.Spaces.c α| * Work.Spaces.Gam α θ ≤ (20 * α) * 1 :=
          mul_le_mul hcoef hGam.2 hGam.1 (by linarith)
      _ = 20 * α := by ring
  calc |(2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ|
        * |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z|
      ≤ (20 * α) * ((k.factorial : ℝ) * (k + 1)) :=
        mul_le_mul h1 hker (abs_nonneg _) (by positivity)
    _ = 20 * α * ((k.factorial : ℝ) * (k + 1)) := by ring

/-- The angular `𝒲^{4,∞}`-summands of `F_*` are bounded by `20 α · tBound (j-1) 0 · k!(k+1)`:
each `D_θ` costs one factor `α` (`dthU_Gam_le`), and the resulting `α Γ` is absorbed by the
weight (`Gam_mul_weight_le`). -/
lemma Fstar_mixed_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (j k : ℕ) (hj : 1 ≤ j)
    (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (Work.Construction.Fstar α)) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤
      20 * α * (Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1))) := by
  have hT0 : 0 ≤ Work.Spaces.tBound (j - 1) 0 := Work.Spaces.tBound_nonneg _ _
  have hK0 : 0 ≤ (k.factorial : ℝ) * (k + 1) := by positivity
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hw0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
    Work.Spaces.gamma_weight_nonneg α θ hα hθ
  have hdth := Work.Spaces.dthU_Gam_le j hj α hα hα1 θ hθ
  have hgamw : α * Work.Spaces.Gam α θ
      * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ 1 := by
    rw [← mul_div_assoc]
    exact Work.Spaces.Gam_mul_weight_le α θ hα hθ
  have hcoef : |2 * α / Work.Spaces.c α| ≤ 20 * α := Fstar_coef_le α hα hα1
  have hker : |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z|
      ≤ (k.factorial : ℝ) * (k + 1) := Work.Spaces.pzIter_hKer_bound k z hz
  rw [pzIter_DthIter_Fstar_eq]
  rw [show (z + 1) ^ k * (2 * α / Work.Spaces.c α
          * (Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t)) θ
          * deriv^[k] Work.Spaces.hKer z)
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
      = (2 * α / Work.Spaces.c α) * (Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t)) θ
        * ((z + 1) ^ k * deriv^[k] Work.Spaces.hKer z)
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) from by ring]
  rw [abs_mul, abs_mul, abs_of_nonneg hw0]
  have hstep1 : |(2 * α / Work.Spaces.c α)
        * (Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t)) θ|
      ≤ |2 * α / Work.Spaces.c α| * (α * Work.Spaces.tBound (j - 1) 0 * Work.Spaces.Gam α θ) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hdth (abs_nonneg _)
  have hTK0 : 0 ≤ |2 * α / Work.Spaces.c α| * Work.Spaces.tBound (j - 1) 0
      * ((k.factorial : ℝ) * (k + 1)) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) hT0) hK0
  have hstep2 : |(2 * α / Work.Spaces.c α)
        * (Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t)) θ|
        * |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ (|2 * α / Work.Spaces.c α| * (α * Work.Spaces.tBound (j - 1) 0 * Work.Spaces.Gam α θ))
        * ((k.factorial : ℝ) * (k + 1))
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
    apply mul_le_mul_of_nonneg_right _ hw0
    exact mul_le_mul hstep1 hker (abs_nonneg _)
      (mul_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg (le_of_lt hα) hT0) hG0))
  refine le_trans hstep2 ?_
  rw [show (|2 * α / Work.Spaces.c α| * (α * Work.Spaces.tBound (j - 1) 0 * Work.Spaces.Gam α θ))
        * ((k.factorial : ℝ) * (k + 1))
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      = (|2 * α / Work.Spaces.c α| * Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1)))
        * (α * Work.Spaces.Gam α θ
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) from by ring]
  calc (|2 * α / Work.Spaces.c α| * Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1)))
        * (α * Work.Spaces.Gam α θ
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
      ≤ (|2 * α / Work.Spaces.c α| * Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1))) * 1 :=
        mul_le_mul_of_nonneg_left hgamw hTK0
    _ = |2 * α / Work.Spaces.c α| * (Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1))) := by ring
    _ ≤ (20 * α) * (Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1))) :=
        mul_le_mul_of_nonneg_right hcoef (mul_nonneg hT0 hK0)
    _ = 20 * α * (Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1))) := by ring

/-! ## Assembly -/

/-- The universal constant `KB` multiplying `20 α`: the sum of all the (α-independent)
pointwise bounds of the summands of `𝒲^{4,∞}(F_*)`. -/
noncomputable def KB : ℝ :=
  (∑ k ∈ Finset.range 5, (k.factorial : ℝ) * (k + 1))
    + ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
        (if 1 ≤ j ∧ k + j ≤ 4 then
          Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1)) else 0)

lemma KB_nonneg : 0 ≤ KB := by
  rw [KB]
  refine add_nonneg (Finset.sum_nonneg fun k _ => by positivity) ?_
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_
  split_ifs with h
  · exact mul_nonneg (Work.Spaces.tBound_nonneg _ _) (by positivity)
  · norm_num

/-- The `𝒲^{4,∞}`-norm of `F_*` is at most `20 α · KB`. -/
lemma WlInf_Fstar_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInf α 4 (Work.Construction.Fstar α) ≤ 20 * α * KB := by
  have hKB : 20 * α * KB =
      (∑ k ∈ Finset.range 5, 20 * α * ((k.factorial : ℝ) * (k + 1)))
        + ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
            (20 * α * (if 1 ≤ j ∧ k + j ≤ 4 then
              Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1)) else 0)) := by
    rw [KB, mul_add]
    congr 1
    · rw [Finset.mul_sum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
  rw [Work.Spaces.WlInf, hKB]
  apply add_le_add
  · exact Finset.sum_le_sum fun k hk =>
      Work.Spaces.supAbs_le fun z hz θ hθ => Fstar_z_bound α hα hα1 k z θ hz hθ
  · apply Finset.sum_le_sum
    intro j hj
    apply Finset.sum_le_sum
    intro k hk
    split_ifs with hcond
    · exact Work.Spaces.supAbs_le fun z hz θ hθ =>
        Fstar_mixed_bound α hα hα1 j k hcond.1 z θ hz hθ
    · simp

/-- `F_* ∈ 𝒲^{4,∞}` for `0 < α ≤ 1`.  Every `SupFinite` predicate is witnessed by the
explicit bound of `Fstar_z_bound` / `Fstar_mixed_bound`. -/
lemma WlInfMem_Fstar (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInfMem α 4 (Work.Construction.Fstar α) := by
  constructor
  · intro k hk
    refine ⟨20 * α * ((k.factorial : ℝ) * (k + 1)), fun y hy => ?_⟩
    rcases hy with ⟨z, hz, θ, hθ, rfl⟩
    exact Fstar_z_bound α hα hα1 k z θ hz hθ
  · intro j hj k hk hj1 hjk
    refine ⟨20 * α * (Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1))),
      fun y hy => ?_⟩
    rcases hy with ⟨z, hz, θ, hθ, rfl⟩
    exact Fstar_mixed_bound α hα hα1 j k hj1 z θ hz hθ

theorem Fstar_W :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.WlInfMem α 4 (Work.Construction.Fstar α) ∧
      Work.Spaces.WlInf α 4 (Work.Construction.Fstar α) ≤ C * α := by
  refine ⟨20 * KB + 1, by linarith [KB_nonneg], fun α hα hα1 =>
    ⟨WlInfMem_Fstar α hα hα1, ?_⟩⟩
  refine le_trans (WlInf_Fstar_le α hα hα1) ?_
  nlinarith [KB_nonneg, hα]

end Work.FTS.Nonlinear.FstarPkg
