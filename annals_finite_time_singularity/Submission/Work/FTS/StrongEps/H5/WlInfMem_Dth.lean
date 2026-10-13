import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.FTS.StrongEps.H5.WlInfDthAux.sum_shift_identity

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary facts about `D_θ` and the angular weight

The level shift `WlInfMem α (l+1) f → WlInfMem α l (D_θ f)` hinges on two elementary
observations, recorded here before the main theorem:

* `DthIter j (D_θ f) = DthIter (j+1) f`, so every angular slot of the level-`l` norm of
  `D_θ f` is *literally* a slot of the level-`(l+1)` norm of `f`;
* the angular weight of the level-`(l+1)` norm, `sin(2θ)^{-α/5}/(α + sin 2θ)`, dominates
  `1/(α+1)` on `Iθ`, because `sin(2θ)^{α/5}(α + sin 2θ) ≤ α + 1` there.  Since the plain
  `z`-slots of the level-`l` norm of `D_θ f` are the *unweighted* versions of the `j = 1`
  slots of `f`, this is exactly the constant `(α+1)` of the statement.
-/

/-- `D_θ^j (D_θ f) = D_θ^{j+1} f`. -/
theorem DthIter_Dth (f : ℝ → ℝ → ℝ) :
    ∀ j : ℕ, Work.Spaces.DthIter j (Work.Spaces.Dth f) = Work.Spaces.DthIter (j + 1) f
  | 0 => rfl
  | j + 1 => by
      show Work.Spaces.Dth (Work.Spaces.DthIter j (Work.Spaces.Dth f))
        = Work.Spaces.DthIter (j + 1 + 1) f
      rw [DthIter_Dth f j]
      rfl

/-- `sin(2θ) ≥ 0` on the angular interval `[0, π/2]`. -/
theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  refine Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_
  · linarith [hθ.1]
  · linarith [hθ.2, Real.pi_pos]

/-- On `Iθ` the inverse angular weight is at most `α+1`:
`sin(2θ)^{α/5} (α + sin 2θ) ≤ α + 1`. -/
theorem weight_mul_le {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.sin (2 * θ) ^ (α / 5) * (α + Real.sin (2 * θ)) ≤ α + 1 := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h1 : Real.sin (2 * θ) ^ (α / 5) ≤ 1 := Real.rpow_le_one hs0 hs1 (by linarith)
  calc Real.sin (2 * θ) ^ (α / 5) * (α + Real.sin (2 * θ))
      ≤ 1 * (α + 1) := mul_le_mul h1 (by linarith) (by linarith) (by norm_num)
    _ = α + 1 := one_mul _

/-- The inverse of the angular weight at `θ`, when `sin(2θ) > 0`. -/
theorem weight_key {α θ : ℝ} (hα : 0 < α) (_hθ : θ ∈ Work.Spaces.Iθ)
    (hs : 0 < Real.sin (2 * θ)) :
    ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      * ((Real.sin (2 * θ)) ^ (α / 5) * (α + Real.sin (2 * θ))) = 1 := by
  have hαs : α + Real.sin (2 * θ) ≠ 0 := by linarith
  rw [div_eq_mul_inv]
  rw [show (Real.sin (2 * θ)) ^ (-(α / 5)) * (α + Real.sin (2 * θ))⁻¹
        * ((Real.sin (2 * θ)) ^ (α / 5) * (α + Real.sin (2 * θ)))
      = ((Real.sin (2 * θ)) ^ (-(α / 5)) * (Real.sin (2 * θ)) ^ (α / 5))
        * ((α + Real.sin (2 * θ))⁻¹ * (α + Real.sin (2 * θ))) from by ring]
  rw [← Real.rpow_add hs, inv_mul_cancel₀ hαs, mul_one]
  have hexp : -(α / 5) + α / 5 = 0 := by ring
  rw [hexp, Real.rpow_zero]

/-- **Pointwise form of the weight bound.**  If `g` vanishes wherever `sin(2θ) = 0`, then on
`Iθ` the plain value `g z θ` is at most `(α+1)` times its weighted version
`g z θ · sin(2θ)^{-α/5}/(α + sin 2θ)`.  Indeed on `Iθ` the weight is `≥ 1/(α+1)`. -/
theorem abs_le_mul_abs_weight {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hzero : ∀ z θ, Real.sin (2 * θ) = 0 → g z θ = 0)
    {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |g z θ| ≤ (α + 1) * |g z θ * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  rcases eq_or_lt_of_le hs0 with hs | hs
  · rw [← hs, hzero z θ hs.symm]; simp
  · have hαs : 0 < α + Real.sin (2 * θ) := by linarith
    have hkey := weight_key hα hθ hs
    have hc : g z θ = (g z θ * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        * ((Real.sin (2 * θ)) ^ (α / 5) * (α + Real.sin (2 * θ))) := by
      rw [show g z θ * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
          = g z θ * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) from by ring]
      rw [mul_assoc, hkey, mul_one]
    have hc2 : |g z θ| = |g z θ * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
        * ((Real.sin (2 * θ)) ^ (α / 5) * (α + Real.sin (2 * θ))) := by
      conv_lhs => rw [hc]
      rw [abs_mul, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hs0 _) (le_of_lt hαs))]
    rw [hc2]
    calc |g z θ * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
          * ((Real.sin (2 * θ)) ^ (α / 5) * (α + Real.sin (2 * θ)))
        ≤ |g z θ * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| * (α + 1) :=
          mul_le_mul_of_nonneg_left (weight_mul_le hα hθ) (abs_nonneg _)
      _ = (α + 1) * |g z θ * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| := by ring

/-- One `D_θ`-derivative costs one level of the `𝒲`-norm, with the explicit constant `(α+1)`.

For `0 < α ≤ 1` and `WlInfMem α (l+1) f`, both `WlInfMem α l (Dth f)` and
`WlInf α l (Dth f) ≤ (α + 1) · WlInf α (l+1) f` hold.  Indeed `DthIter j (Dth f) = DthIter (j+1) f`
definitionally, so every angular slot of `WlInf α l (Dth f)` is literally a slot of
`WlInf α (l+1) f`; the only difference is that the level-`l` norm lists the *unweighted*
suprema `(z+1)^k ∂_z^k (Dth f)`, while the level-`(l+1)` norm prices `Dth f` only through the
weighted slot with weight `sin(2θ)^{-α/5}/(α+sin 2θ)`.  The inverse weight
`sin(2θ)^{α/5}(α+sin 2θ)` is bounded by `α+1` on `Iθ` (`sin 2θ ≤ 1`, and `sin(2θ) = 0` implies
`DthIter j f z θ = 0`, so the endpoints are harmless). -/
theorem WlInfMem_Dth {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {l : ℕ} {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.WlInfMem α (l + 1) f) :
    Work.Spaces.WlInfMem α l (Work.Spaces.Dth f) ∧
      Work.Spaces.WlInf α l (Work.Spaces.Dth f)
        ≤ (α + 1) * Work.Spaces.WlInf α (l + 1) f := by
  have hzeroD : ∀ (k : ℕ) (z θ : ℝ), Real.sin (2 * θ) = 0 →
      (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ = 0 := by
    intro k z θ hθ
    have h1 : Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ = 0 :=
      Work.Spaces.pzIter_DthIter_eq_zero_of_sin_eq_zero f 0 hθ k z
    rw [h1, mul_zero]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- the plain `z`-slots of the level-`l` norm of `D_θ f`
    intro k hk
    refine ⟨(α + 1) * Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
        * Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))), ?_⟩
    rintro y ⟨z, hz, θ, hθ, rfl⟩
    have hfin : Work.Spaces.SupFinite (fun z θ => (z + 1) ^ k
        * Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
      h.2 1 (by omega) k (by omega) (le_refl 1) (by omega)
    have h2 : |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
        ≤ Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
          * Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
      Work.Spaces.abs_le_supAbs hz hθ hfin
    refine le_trans (abs_le_mul_abs_weight hα
      (g := fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ)
      (fun z θ hs => hzeroD k z θ hs) hθ) ?_
    exact mul_le_mul_of_nonneg_left h2 (by linarith)
  · -- the weighted angular slots of `D_θ f` are the `j = 1` slots of `f`
    intro j hj k hk hj1 hjk
    simp only [DthIter_Dth f]
    exact h.2 (j + 1) (by omega) k (by omega) (by omega) (by omega)
  · -- the norm inequality
    change ((∑ k ∈ Finset.range (l + 1), Work.Spaces.supAbs (fun z θ =>
            (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ))
          + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
              (if 1 ≤ j ∧ k + j ≤ l then Work.Spaces.supAbs (fun z θ =>
                (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (Work.Spaces.Dth f)) z θ
                * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0))
        ≤ (α + 1) * ((∑ k ∈ Finset.range (l + 2), Work.Spaces.supAbs (fun z θ =>
            (z + 1) ^ k * Work.Spaces.pzIter k f z θ))
          + ∑ j ∈ Finset.range (l + 2), ∑ k ∈ Finset.range (l + 2),
              (if 1 ≤ j ∧ k + j ≤ l + 1 then Work.Spaces.supAbs (fun z θ =>
                (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
                * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0))
    -- replace `D_θ^j (D_θ f)` by `D_θ^{j+1} f` in the angular sum
    simp only [DthIter_Dth f]
    set SD := (∑ k ∈ Finset.range (l + 1), Work.Spaces.supAbs (fun z θ =>
      (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ)) with hSDdef
    set TD := (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
      (if 1 ≤ j ∧ k + j ≤ l then Work.Spaces.supAbs (fun z θ =>
        (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter (j + 1) f) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0)) with hTDdef
    set SF := (∑ k ∈ Finset.range (l + 2), Work.Spaces.supAbs (fun z θ =>
      (z + 1) ^ k * Work.Spaces.pzIter k f z θ)) with hSFdef
    set TF := (∑ j ∈ Finset.range (l + 2), ∑ k ∈ Finset.range (l + 2),
      (if 1 ≤ j ∧ k + j ≤ l + 1 then Work.Spaces.supAbs (fun z θ =>
        (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0)) with hTFdef
    -- each plain `z`-slot of `D_θ f` is dominated by the `j = 1` weighted slot of `f`
    have hslot : ∀ k ≤ l, Work.Spaces.supAbs (fun z θ =>
        (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ)
        ≤ (α + 1) * Work.Spaces.supAbs (fun z θ =>
          (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter 1 f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
      intro k hk
      refine Work.Spaces.supAbs_le (fun z hz θ hθ => ?_)
      have hfin : Work.Spaces.SupFinite (fun z θ => (z + 1) ^ k
          * Work.Spaces.pzIter k (Work.Spaces.DthIter 1 f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
        h.2 1 (by omega) k (by omega) (le_refl 1) (by omega)
      have h2 : |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
          ≤ Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (Work.Spaces.DthIter 1 f) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
        Work.Spaces.abs_le_supAbs hz hθ hfin
      refine le_trans (abs_le_mul_abs_weight hα
        (g := fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ)
        (fun z θ hs => hzeroD k z θ hs) hθ) ?_
      exact mul_le_mul_of_nonneg_left h2 (by linarith)
    have hSD : SD ≤ (α + 1) * (∑ k ∈ Finset.range (l + 1), Work.Spaces.supAbs
        (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter 1 f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by
      rw [hSDdef, Finset.mul_sum]
      exact Finset.sum_le_sum fun k hk => hslot k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    have hSFnn : 0 ≤ SF := by
      rw [hSFdef]
      exact Finset.sum_nonneg fun k hk =>
        Work.Spaces.supAbs_nonneg (h.1 k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
    have hTDnn : 0 ≤ TD := by
      rw [hTDdef]
      refine Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun k hk => ?_
      have hj' : j < l + 1 := Finset.mem_range.mp hj
      have hk' : k < l + 1 := Finset.mem_range.mp hk
      by_cases hc : 1 ≤ j ∧ k + j ≤ l
      · rw [ite_eq_left hc]
        exact Work.Spaces.supAbs_nonneg
          (h.2 (j + 1) (by omega) k (by omega) (by omega) (by omega))
      · rw [ite_eq_right hc]
    -- the `j = 1` slots of `f` together with the shifted slots form the angular part of `f`
    have hid' : (∑ k ∈ Finset.range (l + 1), Work.Spaces.supAbs
        (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter 1 f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) + TD = TF := by
      rw [hTDdef, hTFdef]
      exact WlInfDthAux.sum_shift_identity (fun j k => Work.Spaces.supAbs (fun z θ =>
        (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) l
    rw [← hid']
    set E := (∑ k ∈ Finset.range (l + 1), Work.Spaces.supAbs
        (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter 1 f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) with hEdef
    have hSD' : SD ≤ (α + 1) * E := by rw [hEdef]; exact hSD
    have hgrow : TD ≤ (α + 1) * TD := le_mul_of_one_le_left hTDnn (by linarith)
    calc SD + TD
        ≤ (α + 1) * E + TD := by linarith [hSD']
      _ ≤ (α + 1) * E + (α + 1) * TD := by linarith [hgrow]
      _ = (α + 1) * (E + TD) := by rw [mul_add]
      _ ≤ (α + 1) * (SF + (E + TD)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hSFnn) (by linarith)

end Work.FTS.StrongEps.H5
