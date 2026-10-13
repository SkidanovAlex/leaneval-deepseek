import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.ClassC.VanishFamilyDefs
import Submission.Work.FTS.ClassC.VanishWeightDom
import Submission.Work.FTS.ClassC.HkMem_seven_slots_of_plain_family

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

/-- (local helper) The vanishing integrand `hVint` is nonnegative on the angular interval. -/
theorem vigDz_hVint_nonneg (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (t l : ℕ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ hVint α Ψ t l z θ := by
  rw [hVint]
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ' hθ) _)

/-- (local helper) A single vanishing slot of the grid majorant `vanGrid` is dominated by the
whole majorant, because all the remaining summands are non-negative on `Iθ`. -/
theorem vigDz_hVint_le_vanGrid (α : ℝ) (Ψ : ℝ → ℝ → ℝ) {t l : ℕ}
    (ht : t ∈ Finset.Icc 3 9) (hl : l ∈ Finset.range 10) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : hVint α Ψ t l z θ ≤ vanGrid α Ψ z θ := by
  rw [vanGrid]
  have hterm : hVint α Ψ t l z θ
      ≤ ∑ t' ∈ Finset.Icc 3 9, ∑ l' ∈ Finset.range 10, hVint α Ψ t' l' z θ := by
    refine le_trans (Finset.single_le_sum (f := fun l' => hVint α Ψ t l' z θ) ?_ hl) ?_
    · intro l' _
      exact vigDz_hVint_nonneg α Ψ t l' hθ
    · exact Finset.single_le_sum
        (f := fun t' => ∑ l' ∈ Finset.range 10, hVint α Ψ t' l' z θ)
        (fun t' _ => Finset.sum_nonneg fun l' _ => vigDz_hVint_nonneg α Ψ t' l' hθ) ht
  have hHk : 0 ≤ ∑ l' ∈ Finset.range 10, ∑ m ∈ Finset.range 3,
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l' (Work.Spaces.pthIter m Ψ)) z θ :=
    Finset.sum_nonneg fun l' _ => Finset.sum_nonneg fun _ _ =>
      Work.Spaces.HkIntegrand_nonneg α 0 _ z θ
  linarith

/-- (local helper) The grid majorant dominates its own quadruple. -/
theorem vigDz_vanGrid_le_four_mul (α : ℝ) (Ψ : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : vanGrid α Ψ z θ ≤ 4 * vanGrid α Ψ z θ := by
  have := vanGrid_nonneg α Ψ z hθ
  linarith

/-- **The vanishing slot of `z ∂_z ∂_θ²Ψ` is dominated by the grid majorant.**

For `1 ≤ r`, `r + j ≤ 7` the vanishing integrand of the profile `z ∂_z∂_θ²Ψ = D_z∂_θ²Ψ` is

`vig α (z ∂_z∂_θ²Ψ) r j z θ = (D_z^j ∂_θ^r(D_z∂_θ²Ψ) · w)² · sin(2θ)^{2r-γ}
   = (D_z^{j+1} ∂_θ^{r+2}Ψ · w)² · sin(2θ)^{2r-γ}   = hVint α Ψ (r+2) (j+1) z θ`,

i.e. *exactly* the `(t,l) = (r+2, j+1)` summand of `vanGrid` (the exponents agree because
`2(r+2) - 4 - γ = 2r - γ`).  Hence the domination `≤ 4 · vanGrid` is the membership of that
summand in the (non-negative) grid sum.  The pointwise identification
`∂_θ^r(D_z∂_θ²Ψ) = D_z ∂_θ^{r+2}Ψ` on the open quadrant is Clairaut plus locality of the
`D_z`-iterates. -/
theorem vig_Dz_pthIter_two_le {α : ℝ} (hγ : Work.Spaces.gam α ≤ 3 / 2)
    {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ j r : ℕ, 1 ≤ r → r + j ≤ 7 → ∀ z : ℝ, 0 < z →
      ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.FTS.ClassC.vig α (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) r j z θ
        ≤ 4 * Work.FTS.ClassC.vanGrid α Ψ z θ := by
  intro j r hr hrj z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- `∂_θ^r (z ∂_z∂_θ²Ψ) = D_z ∂_θ^{r+2}Ψ` on the open quadrant.
  have hcongr : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pthIter r (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) z θ
        = Work.Spaces.DzIter 1 (Work.Spaces.pthIter (r + 2) Ψ) z θ := by
    intro z' θ' hz' hθ' hπ'
    have h0 := seven_pthIter_DzIter_eqOn_Q0 (f := Work.Spaces.pthIter 2 Ψ)
      (SmoothOpen_pthIter_classC hΨ 2) r 1 z' θ' hz' hθ' hπ'
    rw [← seven_pthIter_add r 2 Ψ] at h0
    exact h0
  have hD : Work.Spaces.DzIter j
      (Work.Spaces.pthIter r (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)) z θ
      = Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter (r + 2) Ψ) z θ := by
    have h2 := Work.FTS.EllipticEst.SmoothOpen.DzIter_congr
      (F := Work.Spaces.pthIter r
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ))
      (G := Work.Spaces.DzIter 1 (Work.Spaces.pthIter (r + 2) Ψ)) hcongr j z θ hz hθ.1 hθ.2
    rw [h2, seven_DzIter_add j 1 (Work.Spaces.pthIter (r + 2) Ψ)]
  have heq : Work.FTS.ClassC.vig α
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) r j z θ
      = Work.FTS.ClassC.hVint α Ψ (r + 2) (j + 1) z θ := by
    simp only [vig, hVint]
    rw [hD]
    have hexp : 2 * ((r + 2 : ℕ) : ℝ) - 4 - Work.Spaces.gam α
        = 2 * (r : ℝ) - Work.Spaces.gam α := by
      push_cast
      ring
    rw [hexp]
  rw [heq]
  refine le_trans (vigDz_hVint_le_vanGrid α Ψ ?_ ?_ hθI) (vigDz_vanGrid_le_four_mul α Ψ hθI)
  · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · exact Finset.mem_range.mpr (by omega)

end Work.FTS.ClassC
