import Mathlib
import Submission.Work.Diff.STE.flat.energy_apriori

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

/-- **Faà di Bruno bound for the DeTurck nonlinearity**: the composition with the pair map
`y ↦ (y, V y)` (the first coordinate is the identity, i.e. the explicit `x`-dependence of the
nonlinearity).

If `Ψ : E × F → ℝ` and `V : E → F` are `C^∞` at `(p, V p)` resp. `p`, if the derivatives of `Ψ`
at `(p, V p)` up to order `k` are bounded by `M`, and if the derivatives of `V` at `p` up to order
`k` are bounded by `D ^ i` for some `D ≥ 0`, then
`‖D^k (fun y => Ψ (y, V y)) p‖ ≤ k! * M * (1 + D) ^ k`.

The factor `(1 + D)` is forced by the identity coordinate (both reviewers checked this, and the
statement with `D ^ k` is *false* at `k = 1`): with `W := fun y => (y, V y)` one has
`iteratedFDeriv ℝ i W p = (iteratedFDeriv ℝ i (fun y => y) p).prod (iteratedFDeriv ℝ i V p)`
(`iteratedFDeriv_prodMk`) and `‖(a, b)‖ = max ‖a‖ ‖b‖` (`Prod.norm_mk`), so
`‖D^i W p‖ = max ([i = 1], ‖D^i V p‖) ≤ (1 + D)^i` for `1 ≤ i ≤ k` (using `hD0` at `i = 1` and
`D^i ≤ (1 + D)^i` for `i ≥ 2`, the latter from `0 ≤ D`).

Available ingredient: `Work.Diff.STE.flat.norm_iteratedFDeriv_comp_le_of_contDiffAt_ste`
(proved sorry-free in `Diff/STE/flat/energy_apriori`), the `ContDiffAt` Faà di Bruno bound
`‖D^k (g ∘ f) x‖ ≤ k! * C * D^k`, to be applied with `g := Ψ`, `f := W`, `C := M`,
`D := 1 + D`. -/
theorem norm_iteratedFDeriv_comp_prod_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : E × F → ℝ) (V : E → F) (p : E) (k : ℕ) (M D : ℝ)
    (hΨ : ContDiffAt ℝ (⊤ : ℕ∞) Ψ (p, V p)) (hV : ContDiffAt ℝ (⊤ : ℕ∞) V p)
    (hM : ∀ i ≤ k, ‖iteratedFDeriv ℝ i Ψ (p, V p)‖ ≤ M)
    (hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i V p‖ ≤ D ^ i) (hD0 : 0 ≤ D) :
    ‖iteratedFDeriv ℝ k (fun y : E => Ψ (y, V y)) p‖
      ≤ (Nat.factorial k : ℝ) * M * (1 + D) ^ k := by
  -- the pair map `W y = (y, V y)` is smooth at `p`
  have hWdiff : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E => (y, V y)) p :=
    (contDiffAt_id (x := p)).prodMk hV
  -- the identity coordinate contributes at most `1` to the `i`-th derivative, `i ≥ 1`
  have hid_le : ∀ i : ℕ, 1 ≤ i → ‖iteratedFDeriv ℝ i (fun y : E => y) p‖ ≤ 1 := by
    intro i hi
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    rw [iteratedFDeriv_succ_eq_comp_right (𝕜 := ℝ) (f := fun y : E => y) (x := p)]
    rw [Function.comp_apply, LinearIsometryEquiv.norm_map]
    have hfd : (fun y : E => fderiv ℝ (fun y : E => y) y) =
        fun _ : E => (ContinuousLinearMap.id ℝ E) :=
      funext (fun y => fderiv_id)
    rw [hfd]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      -- order `1`: the derivative is the identity, of norm at most `1`
      rw [norm_iteratedFDeriv_zero]
      exact ContinuousLinearMap.norm_id_le
    · -- order `≥ 2`: the constant map has vanishing iterated derivative
      rw [iteratedFDeriv_const_of_ne (𝕜 := ℝ) (by omega : n ≠ 0) (ContinuousLinearMap.id ℝ E)]
      simp
  -- the geometric bound for the pair map, with constant `1 + D`
  have hD' : ∀ i, 1 ≤ i → i ≤ k →
      ‖iteratedFDeriv ℝ i (fun y : E => (y, V y)) p‖ ≤ (1 + D) ^ i := by
    intro i hi1 hi2
    have hprod : iteratedFDeriv ℝ i (fun y : E => (y, V y)) p =
        (iteratedFDeriv ℝ i (fun y : E => y) p).prod (iteratedFDeriv ℝ i V p) :=
      iteratedFDeriv_prodMk (contDiffAt_id (x := p)) hV
        (WithTop.coe_le_coe.mpr le_top)
    rw [hprod, ContinuousMultilinearMap.opNorm_prod]
    refine max_le ?_ ?_
    · refine (hid_le i hi1).trans ?_
      exact one_le_pow₀ (by linarith) (n := i)
    · exact (hD i hi1 hi2).trans (pow_le_pow_left₀ hD0 (by linarith) i)
  -- Faà di Bruno for `Ψ ∘ W`
  exact norm_iteratedFDeriv_comp_le_of_contDiffAt_ste Ψ (fun y : E => (y, V y)) p k M (1 + D)
    hΨ hWdiff hM hD'

end Work.Diff.STE.flat
