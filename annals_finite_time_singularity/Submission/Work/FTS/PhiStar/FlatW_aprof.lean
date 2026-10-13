/-
# `Work.FTS.PhiStar.FlatW_aprof` — the flat radial piece `((z+1)/z)·Aprof α` is `O(α)` in `FlatW 7`

`Aprof α = GzProfile α − ThetaProfile` is the flat radial factor of
`Φ̃_* = Aprof α(z)·sin 2θ + α φ(z) ψ(θ) + R`, and the lead design
(`FTS/STARPKG_T2_LEAD.md` §1.4 (A), node P-A) asks for the *flat* bound

`FlatW 7 (fun z θ => (z+1)/z · Aprof α z) (C·α)`,  `C` universal,

which is the `(A)`-piece of the `StarCore` witness `Ycheck α Φ_*`.

## Route

Everything is *radial*, so the angular half of `FlatW` is trivial (`pth` of a radial
function vanishes, and `pzIter k 0 = 0`), and the `z`-half is the one-variable estimate

`|(1+z)^k ∂_z^k ((z+1)/z · Aprof α z)| ≤ C α`   for `k ≤ 7`, `z > 0`.

* `Aprof_eqOn_negDk` identifies `Aprof α = −Dk (5/α) 0` on `{z > 0}`, and
  `Dk N 0 z = −(1/2)(z·At N 0 z)`, so on `z > 0`

  `(z+1)/z · Aprof α z = (1/2)·(1+z)·At N 0 z`,   `N = 5/α ≥ 5`,

  where `At N 0 z = ∫₀¹ t^N(1+zt)^{-2} dt` (`GbarDefs.lean`).  The factor `1/z` of the
  flat weight cancels exactly against the `z` produced by `Dk`, leaving the harmless
  `(1/2)(1+z)At N 0 z`.

* `At_linear_deriv_bound` (`Submission.Work.FTS.PhiStar.At_linear_deriv_bound`) is the
  one-variable analytic input: for `N ≥ 2`, `z > 0` and `k ≤ 7`,

  `|(1+z)^k ∂_z^k ((1+·)·At N 0)| ≤ C₀/N`.

* The `deriv`-iterates are transported through the *germ* equality (valid on the open set
  `{z > 0}`) with `Filter.EventuallyEq.iteratedDeriv_eq`, and the factor `1/2` is pulled
  out with the unconditional `iteratedDeriv_const_mul_field`.  Since `N = 5/α`,
  `C₀/N = C₀ α/5`, and half of that is `C₀ α/10`.
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.PhiStar.Aprof_wiln
import Submission.Work.FTS.H2.PhiStarE.Gbar_wiln
import Submission.Work.FTS.PhiStar.At_linear_deriv_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option linter.unusedVariables false

/-! ## The angular half: a radial function has no `∂_θ`-derivatives -/

/-- `pth` of a radial function vanishes. -/
private theorem pth_radial (g : ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => g z) = fun _ _ => (0 : ℝ) := by
  funext z θ
  simp [Work.Spaces.pth]

/-- `D_θ^i` of the zero function is zero. -/
private theorem DthIter_zero_fun (i : ℕ) :
    Work.Spaces.DthIter i (fun _ _ => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      simp [Work.Spaces.Dth, Work.Spaces.pth]

/-! ## The identification of the flat radial piece on `z > 0` -/

/-- On `z > 0` the flat radial factor is `(1/2)·z·At N 0 z` with `N = 5/α`: this is
`Aprof α = −Dk N 0` together with `Dk N 0 z = −(1/2)(z·At N 0 z)`. -/
private theorem Aprof_eqOn_half_At {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    EqOn (Aprof α) (fun z => (1 / 2) * (z * Work.FTS.H2.PhiStarE.At (5 / α) 0 z))
      (Set.Ioi 0) := by
  intro z hz
  have h := Aprof_eqOn_negDk hα hα1 hz
  rw [h, Work.FTS.H2.PhiStarE.Dk_zero]
  ring

/-- The germ form of the identification, with the flat weight `(z+1)/z` applied:
on `{z > 0}`, `((z+1)/z)·Aprof α = (1/2)·(1+·)·At N 0`. -/
private theorem Aprof_germ {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {z : ℝ} (hz : 0 < z) :
    (fun z' => (z' + 1) / z' * Aprof α z')
      =ᶠ[𝓝 z] (fun z' => (1 / 2) * ((1 + z') * Work.FTS.H2.PhiStarE.At (5 / α) 0 z')) := by
  filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
  have h := Aprof_eqOn_negDk hα hα1 (show z' ∈ Set.Ioi 0 from hz')
  rw [h, Work.FTS.H2.PhiStarE.Dk_zero]
  have hz'0 : z' ≠ 0 := ne_of_gt hz'
  field_simp
  ring

/-! ## The flat radial estimate -/

/-- **The radial half of `FlatW 7`.**  From the one-variable analytic bound
`At_linear_deriv_bound` for `(1+·)·At N 0`, transported along the germ equality
`Aprof_germ` and scaled by `1/2`. -/
private theorem flat_radial_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ k : ℕ, k ≤ 7 → ∀ z : ℝ, 0 < z →
      |(z + 1) ^ k * (deriv^[k]) (fun z' => (z' + 1) / z' * Aprof α z') z| ≤ C * α := by
  obtain ⟨C₀, hC₀, hbound⟩ := At_linear_deriv_bound
  refine ⟨C₀ / 10 + 1, by positivity, fun α hα hα1 k hk z hz => ?_⟩
  have hgerm := Aprof_germ hα hα1 hz
  have hN : (2 : ℝ) ≤ 5 / α := by
    rw [le_div_iff₀ hα]; linarith
  have h1 : (deriv^[k]) (fun z' => (z' + 1) / z' * Aprof α z') z
      = (deriv^[k]) (fun w => (1 / 2) * ((1 + w) * Work.FTS.H2.PhiStarE.At (5 / α) 0 w)) z := by
    rw [← iteratedDeriv_eq_iterate, ← iteratedDeriv_eq_iterate]
    exact hgerm.iteratedDeriv_eq k
  have h2 : (deriv^[k]) (fun w => (1 / 2) * ((1 + w) * Work.FTS.H2.PhiStarE.At (5 / α) 0 w)) z
      = (1 / 2) * (deriv^[k]) (fun w => (1 + w) * Work.FTS.H2.PhiStarE.At (5 / α) 0 w) z := by
    rw [← iteratedDeriv_eq_iterate, ← iteratedDeriv_eq_iterate]
    exact iteratedDeriv_const_mul_field (1 / 2)
      (fun w => (1 + w) * Work.FTS.H2.PhiStarE.At (5 / α) 0 w)
  have hb := hbound (5 / α) z k hN hz hk
  rw [show (1 : ℝ) + z = z + 1 from by ring] at hb
  have hC₀N : C₀ / (5 / α) = C₀ * α / 5 := by field_simp
  rw [hC₀N] at hb
  have hrw : (z + 1) ^ k * (deriv^[k]) (fun z' => (z' + 1) / z' * Aprof α z') z
      = (1 / 2) * ((z + 1) ^ k * (deriv^[k])
          (fun w => (1 + w) * Work.FTS.H2.PhiStarE.At (5 / α) 0 w) z) := by
    rw [h1, h2]; ring
  rw [hrw, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc (1 / 2) * |(z + 1) ^ k * (deriv^[k])
          (fun w => (1 + w) * Work.FTS.H2.PhiStarE.At (5 / α) 0 w) z|
      ≤ (1 / 2) * (C₀ * α / 5) :=
        mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 1 / 2)
    _ = C₀ * α / 10 := by ring
    _ ≤ (C₀ / 10 + 1) * α := by nlinarith [hα, hC₀]

/-! ## The main statement -/

/-- **The flat radial piece of the `StarCore` witness is `O(α)` in `FlatW 7`.**
The angular slots of `FlatW` vanish because the function is radial, and the radial slots
are `flat_radial_bound`. -/
theorem FlatW_aprof : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    Work.FTS.VocabO2.FlatW 7 (fun z θ => (z + 1) / z * Work.FTS.PhiStar.Aprof α z) (C * α) := by
  obtain ⟨C₁, hC₁, hrad⟩ := flat_radial_bound
  refine ⟨C₁, hC₁, fun α hα hα1 => ?_⟩
  intro z θ hz hθ hθ2
  constructor
  · intro k hk
    rw [show Work.Spaces.pzIter k (fun z θ => (z + 1) / z * Aprof α z) z θ
        = (deriv^[k]) (fun z' => (z' + 1) / z' * Aprof α z') z from
          Work.FTS.H2.PhiStarE.pzIter_radial (fun z' => (z' + 1) / z' * Aprof α z') k z θ]
    exact hrad α hα hα1 k hk z hz
  · intro k i hki
    have hf : Work.Spaces.DthIter i (Work.Spaces.pth (fun z θ => (z + 1) / z * Aprof α z))
        = fun _ _ => (0 : ℝ) := by
      rw [pth_radial (fun z' => (z' + 1) / z' * Aprof α z'), DthIter_zero_fun i]
    rw [hf, Work.FTS.H2.PhiStarE.pzIter_zero_fun]
    simp only [mul_zero, abs_zero]
    exact mul_nonneg (le_of_lt hC₁) (le_of_lt hα)

end Work.FTS.PhiStar
