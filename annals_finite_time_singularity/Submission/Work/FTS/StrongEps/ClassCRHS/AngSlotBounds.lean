import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.ClassCRHS.StarAux
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row23
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le
import Submission.Work.Spaces.GammaW_Prelim
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Spaces.c_bounds
import Submission.Work.FTS.Nonlinear.Pieces.RNP.dthU_pow_Gam_sharp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.ClassCRHS

/-!
# Angular slot bounds for the two `F_*`-angular profiles

`SA0 α = αΓ/c` and `SA1 α = α D_θΓ/c` are the two angular profiles of the scaled
`F_*`-atoms (`StarAux`).  We prove that, uniformly for `α ∈ (0,1]`, both are bounded by a
constant `B0`, and that all their `D_θ`-iterates of order `1 ≤ i ≤ 4` are bounded by
`B1 · SGmj α θ = B1 · Γ(θ)(α + sin 2θ)`.

The only input is the sharp angular jet bound `RNP.dthU_pow_Gam_sharp`
(`|D_θ^m Γ| ≤ C α Γ (α + sin 2θ)` for `2 ≤ m ≤ 5`) together with the first-order bound
`RNP.dthIter_one_Gam_le`, plus `1/10 ≤ c ≤ 10` (`Spaces.c_bounds`) and `0 ≤ Γ ≤ 1` on `Iθ`
(`Spaces.Gam_bounds`).
-/

/-- `sin (2θ) ≥ 0` on `Iθ = [0, π/2]`. -/
lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  refine Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], ?_⟩
  linarith [hθ.2]

/-- The `D_θ`-iterates of the `θ`-only function `SA0 α` are `(α/c)` times those of `Γ`. -/
lemma DthIter_SA0_repr (α : ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun _ (θ' : ℝ) => SA0 α θ') z θ
      = (α / Work.Spaces.c α) * Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ := by
  have hfun : (fun t : ℝ => SA0 α t)
      = (fun t : ℝ => (α / Work.Spaces.c α) * (fun s => Work.Spaces.Gam α s) t) := by
    funext t
    show α * (fun s => Work.Spaces.Gam α s) t / Work.Spaces.c α
        = (α / Work.Spaces.c α) * (fun s => Work.Spaces.Gam α s) t
    ring
  rw [Work.FTS.LocData.DthIter_rad_eq i (fun θ' => SA0 α θ') z θ, hfun,
    Work.Spaces.dthU_iter_const_mul i (α / Work.Spaces.c α) (fun s => Work.Spaces.Gam α s)]

/-- The `D_θ`-iterates of `SA1 α = (α/c) D_θΓ` are `(α/c)` times those of `Γ`, shifted by one. -/
lemma DthIter_SA1_repr (α : ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun _ (θ' : ℝ) => SA1 α θ') z θ
      = (α / Work.Spaces.c α) * Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ := by
  have hfun : (fun t : ℝ => SA1 α t)
      = (fun t : ℝ => (α / Work.Spaces.c α)
          * Work.Spaces.dthU (fun s => Work.Spaces.Gam α s) t) := by
    funext t
    show α * Work.Spaces.dthU (fun s => Work.Spaces.Gam α s) t / Work.Spaces.c α
        = (α / Work.Spaces.c α) * Work.Spaces.dthU (fun s => Work.Spaces.Gam α s) t
    ring
  rw [Work.FTS.LocData.DthIter_rad_eq i (fun θ' => SA1 α θ') z θ, hfun,
    Work.Spaces.dthU_iter_const_mul i (α / Work.Spaces.c α)
      (Work.Spaces.dthU (fun s => Work.Spaces.Gam α s)),
    Work.Spaces.dthU_iter_comp i (fun s => Work.Spaces.Gam α s)]

/-- **The arithmetic core.**  `(α/c)·D_θ^iΓ` is bounded by `B1·Γ(α + sin 2θ)` uniformly in
`α ∈ (0,1]` and `1 ≤ i ≤ 5`, with `B1 = 10C + 40/3 + 1`.

For `i = 1` we use `|D_θΓ| ≤ (4/3)αΓ` and `α² ≤ α + sin 2θ`; for `i ≥ 2` the sharp bound
`|D_θ^iΓ| ≤ C α Γ (α + sin 2θ)` and `α² ≤ 1`. -/
lemma jet_cmul_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ θ ∈ Work.Spaces.Iθ, ∀ m : ℕ, 2 ≤ m → m ≤ 5 →
      |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
        ≤ C * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (i : ℕ) (hi1 : 1 ≤ i) (hi5 : i ≤ 5) :
    |(α / Work.Spaces.c α) * Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
      ≤ (10 * C + 40 / 3 + 1)
        * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by
  have hc := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith [hc.1]
  have hdc : 0 ≤ α / Work.Spaces.c α := div_nonneg hα.le hcpos.le
  have hdiv : α / Work.Spaces.c α ≤ 10 * α := by
    rw [div_le_iff₀ hcpos]
    nlinarith [hc.1, hα]
  have hG := Work.Spaces.Gam_bounds α θ hα hθ
  have hsin := sin_two_nonneg_Iθ hθ
  have hα2 : α ^ 2 ≤ α + Real.sin (2 * θ) := by nlinarith [hα.le, hα1, hsin]
  have hα2' : α ^ 2 ≤ 1 := by nlinarith [hα.le, hα1]
  have hX : 0 ≤ Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) :=
    mul_nonneg hG.1 (by linarith [hα.le, hsin])
  rw [abs_mul, abs_of_nonneg hdc]
  rcases eq_or_lt_of_le hi1 with hone | hgt
  · subst hone
    rw [Function.iterate_one]
    have hb : |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        ≤ (4 / 3) * α * Work.Spaces.Gam α θ := by
      have hrepr : Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
          = Work.Spaces.DthIter 1 (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ := by
        rw [Work.FTS.LocData.DthIter_rad_eq 1 (fun t => Work.Spaces.Gam α t) 0 θ,
          Function.iterate_one]
      rw [hrepr]
      exact Work.FTS.Nonlinear.Pieces.RNP.dthIter_one_Gam_le hα hα1 θ hθ
    have h4nn : 0 ≤ (4 / 3) * α * Work.Spaces.Gam α θ :=
      mul_nonneg (mul_nonneg (by norm_num) hα.le) hG.1
    calc (α / Work.Spaces.c α) * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        ≤ (α / Work.Spaces.c α) * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
          mul_le_mul_of_nonneg_left hb hdc
      _ ≤ (10 * α) * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
          mul_le_mul_of_nonneg_right hdiv h4nn
      _ = (40 / 3) * (α ^ 2 * Work.Spaces.Gam α θ) := by ring
      _ ≤ (40 / 3) * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          calc α ^ 2 * Work.Spaces.Gam α θ
              ≤ (α + Real.sin (2 * θ)) * Work.Spaces.Gam α θ :=
                mul_le_mul_of_nonneg_right hα2 hG.1
            _ = Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) := by ring
      _ ≤ (10 * C + 40 / 3 + 1)
            * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
          mul_le_mul_of_nonneg_right (by linarith) hX
  · have hb := hC θ hθ i (by omega) hi5
    have hCnn : 0 ≤ C * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) :=
      mul_nonneg (mul_nonneg (mul_nonneg hCpos.le hα.le) hG.1) (by linarith [hα.le, hsin])
    calc (α / Work.Spaces.c α) * |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
        ≤ (α / Work.Spaces.c α)
            * (C * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
          mul_le_mul_of_nonneg_left hb hdc
      _ ≤ (10 * α) * (C * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
          mul_le_mul_of_nonneg_right hdiv hCnn
      _ = (10 * C) * (α ^ 2 * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))) := by ring
      _ ≤ (10 * C) * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith [hCpos])
          calc α ^ 2 * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
              ≤ 1 * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
                mul_le_mul_of_nonneg_right hα2' hX
            _ = Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) := one_mul _
      _ ≤ (10 * C + 40 / 3 + 1)
            * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
          mul_le_mul_of_nonneg_right (by linarith) hX

theorem AngSlotBounds :
    ∃ B0 B1 : ℝ, 0 < B0 ∧ 0 < B1 ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
      (∀ θ ∈ Work.Spaces.Iθ,
          |Work.FTS.StrongEps.ClassCRHS.SA0 α θ| ≤ B0) ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
          |Work.Spaces.DthIter i (fun _ (θ' : ℝ) =>
              Work.FTS.StrongEps.ClassCRHS.SA0 α θ') 0 θ|
            ≤ B1 * Work.FTS.StrongEps.ClassCRHS.SGmj α θ) ∧
      (∀ θ ∈ Work.Spaces.Iθ,
          |Work.FTS.StrongEps.ClassCRHS.SA1 α θ| ≤ B0) ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
          |Work.Spaces.DthIter i (fun _ (θ' : ℝ) =>
              Work.FTS.StrongEps.ClassCRHS.SA1 α θ') 0 θ|
            ≤ B1 * Work.FTS.StrongEps.ClassCRHS.SGmj α θ) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.Nonlinear.Pieces.RNP.dthU_pow_Gam_sharp
  refine ⟨10 ^ 6, 10 * C + 40 / 3 + 1, by norm_num, by linarith, ?_⟩
  intro α hαmem
  obtain ⟨hα, hα1⟩ := hαmem
  have hc := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith [hc.1]
  have hdc : 0 ≤ α / Work.Spaces.c α := div_nonneg hα.le hcpos.le
  have hdiv : α / Work.Spaces.c α ≤ 10 * α := by
    rw [div_le_iff₀ hcpos]
    nlinarith [hc.1, hα]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- clause 1: `|SA0| ≤ 10⁶`
    intro θ hθ
    have hG := Work.Spaces.Gam_bounds α θ hα hθ
    have h1 : |SA0 α θ| = α * Work.Spaces.Gam α θ / Work.Spaces.c α := by
      show |α * Work.Spaces.Gam α θ / Work.Spaces.c α|
          = α * Work.Spaces.Gam α θ / Work.Spaces.c α
      exact abs_of_nonneg (div_nonneg (mul_nonneg hα.le hG.1) hcpos.le)
    rw [h1, div_le_iff₀ hcpos]
    have h2 : α * Work.Spaces.Gam α θ ≤ 1 := by
      have h := mul_le_mul hα1 hG.2 hG.1 (by norm_num : (0 : ℝ) ≤ 1)
      simpa using h
    have h3 : 1 ≤ 10 ^ 6 * Work.Spaces.c α := by nlinarith [hc.1]
    linarith
  · -- clause 2: the `SA0`-slots
    intro i hi1 hi4 θ hθ
    rw [DthIter_SA0_repr α i 0 θ]
    show |(α / Work.Spaces.c α) * Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
        ≤ (10 * C + 40 / 3 + 1)
          * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
    exact jet_cmul_le hα hα1 hCpos (hC α hα hα1) hθ i hi1 (by omega)
  · -- clause 3: `|SA1| ≤ 10⁶`
    intro θ hθ
    have hG := Work.Spaces.Gam_bounds α θ hα hθ
    have hsa1 : SA1 α θ = (α / Work.Spaces.c α)
        * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ := by
      show α * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ / Work.Spaces.c α
          = (α / Work.Spaces.c α) * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
      ring
    have hb : |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        ≤ (4 / 3) * α * Work.Spaces.Gam α θ := by
      have hrepr : Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
          = Work.Spaces.DthIter 1 (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ := by
        rw [Work.FTS.LocData.DthIter_rad_eq 1 (fun t => Work.Spaces.Gam α t) 0 θ,
          Function.iterate_one]
      rw [hrepr]
      exact Work.FTS.Nonlinear.Pieces.RNP.dthIter_one_Gam_le hα hα1 θ hθ
    rw [hsa1, abs_mul, abs_of_nonneg hdc]
    have h4nn : 0 ≤ (4 / 3) * α * Work.Spaces.Gam α θ :=
      mul_nonneg (mul_nonneg (by norm_num) hα.le) hG.1
    have hα2' : α ^ 2 ≤ 1 := by nlinarith [hα.le, hα1]
    calc (α / Work.Spaces.c α)
          * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        ≤ (α / Work.Spaces.c α) * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
          mul_le_mul_of_nonneg_left hb hdc
      _ ≤ (10 * α) * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
          mul_le_mul_of_nonneg_right hdiv h4nn
      _ = (40 / 3) * (α ^ 2 * Work.Spaces.Gam α θ) := by ring
      _ ≤ (40 / 3) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact (mul_le_mul hα2' hG.2 hG.1 (by norm_num)).trans_eq (by norm_num)
      _ ≤ 10 ^ 6 := by norm_num
  · -- clause 4: the `SA1`-slots
    intro i hi1 hi4 θ hθ
    rw [DthIter_SA1_repr α i 0 θ]
    show |(α / Work.Spaces.c α) * Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ|
        ≤ (10 * C + 40 / 3 + 1)
          * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
    exact jet_cmul_le hα hα1 hCpos (hC α hα hα1) hθ (i + 1) (by omega) (by omega)

end Work.FTS.StrongEps.ClassCRHS
