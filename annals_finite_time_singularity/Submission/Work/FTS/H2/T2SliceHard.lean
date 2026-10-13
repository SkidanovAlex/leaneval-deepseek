import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.T2Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.H2.T2SliceAux
import Submission.Work.FTS.H2.HardSummandZero
import Submission.Work.FTS.H2.HardSummandMixed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.H2

set_option autoImplicit false

/-! ## The five "hard" summands in mixed-derivative form -/

/-- The `k`-th "hard" `g`-derivative is the mixed derivative `D_z^{4-k} D_θ^k g`. -/
theorem Thard_eq (g : ℝ → ℝ → ℝ) (k : Fin 5) :
    Thard g k = Work.Spaces.mixed (4 - k.val) k.val g := by
  funext z θ
  fin_cases k <;> rfl

/-- The angular weight of the `k = 0` term is `sin(2θ)^{-η}` (`η = 99/100 < 1`, so this
weight is integrable on `Iθ`). -/
theorem sghard_apply_zero (α θ : ℝ) :
    sghard α 0 θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := rfl

/-- The angular weight of a term with `k ≠ 0` is `sin(2θ)^{-γ}`, `γ = 1 + α/10`; the term
carries an additional second-order vanishing in `sin(2θ)`, so this weight is harmless. -/
theorem sghard_apply_ne (α : ℝ) (k : Fin 5) (hk : k.val ≠ 0) (θ : ℝ) :
    sghard α k θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  fin_cases k <;> simp_all [sghard]

/-! ## Each of the five summands is integrable in `θ` -/

/-- The `θ`-slice of a single summand of `Hhard` is integrable on `Iθ`: for `k = 0` this is
`HardSummandZero` (the weight `sin(2θ)^{-η}` with `η < 1`), and for `k ≠ 0` the summand is
`HardSummandMixed` with `j = 4 - k`, `i = k ≥ 1` (the two factors `∂_z(mixed j i g)` and
`mixed j i g` each contribute a factor `sin(2θ)`, which tames the weight
`sin(2θ)^{-γ}`). -/
theorem hardSummand_integrable (α : ℝ) (g : ℝ → ℝ → ℝ) (hsmg : Work.Spaces.SmoothNbhd g)
    (hα1 : α ≤ 1) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) (k : Fin 5) :
    MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pz (Thard g k) z θ * Thard g k z θ * (Work.Spaces.w z) ^ 2
        * sghard α k θ) Work.Spaces.Iθ := by
  rcases eq_or_ne k.val 0 with hk0 | hk0
  · -- `k = 0`: only the weight `sin(2θ)^{-η}` is singular.
    have hk : k = 0 := Fin.ext (by simpa using hk0)
    subst hk
    refine (HardSummandZero g hsmg hz).congr_fun ?_ measurableSet_Icc
    intro θ hθ
    simp only [Thard_eq g 0, sghard_apply_zero α θ]
    rfl
  · -- `k ≠ 0`: the two factors each vanish to first order at the endpoints.
    have h := HardSummandMixed α g hsmg hα1 (4 - k.val) k.val
      (Nat.one_le_iff_ne_zero.mpr hk0) hz
    refine h.congr_fun ?_ measurableSet_Icc
    intro θ hθ
    simp only [Thard_eq g k, sghard_apply_ne α k hk0]

/-- Angular slice integrability of the five "hard" terms: for every `z ∈ Iz` the function
`θ ↦ Hhard α f g z θ` is integrable on `Iθ`.

Each of the five summands is (a bounded continuous function of `θ`, since `SmoothNbhd` gives
smoothness of `f`, `g` and of `∂_z Θ_k`, and `|w z|` is a constant in `θ`) times
`Th_k(z,θ)^2 · σ_k(θ)` with `σ_0 = sin(2θ)^{-η}` and `σ_k = sin(2θ)^{-γ}` for `k ≥ 1`.
For `k ≥ 1` the factor `Th_k = mixed j i g` with `i ≥ 1` vanishes at `θ = 0` to first order
(`D_θ = sin(2θ) ∂_θ`, and the factor `sin(2θ)` survives iteration), so
`Th_k² sin(2θ)^{-γ}` behaves like `sin(2θ)^{2-γ}` near `0`, which is integrable because
`2 - γ ≥ 0.9 > -1`; the same first-order vanishing holds for `∂_z Th_k`.  For `k = 0` the
weight is `sin(2θ)^{-η}` with `η < 1`, also integrable. -/
theorem T2SliceHard : ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.Spaces.SmoothNbhd f → Work.Spaces.SmoothNbhd g →
    Work.Spaces.DecayAll 4 f → Work.Spaces.DecayAll 4 g →
    Work.Spaces.HkMem α 4 f → Work.Spaces.HkMem α 4 g →
    ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => Work.FTS.H2.Hhard α f g z θ) Work.Spaces.Iθ := by
  intro α f g _hα hα1 hsmf hsmg _ _ _ _ z hz
  -- Every one of the five summands is integrable in `θ`.
  have hper : ∀ k : Fin 5, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pz (Thard g k) z θ * Thard g k z θ * (Work.Spaces.w z) ^ 2
        * sghard α k θ) Work.Spaces.Iθ :=
    fun k => hardSummand_integrable α g hsmg hα1 hz k
  -- Hence so is their finite sum.
  have hS : Integrable
      (fun θ => ∑ k : Fin 5, Work.Spaces.pz (Thard g k) z θ * Thard g k z θ
        * (Work.Spaces.w z) ^ 2 * sghard α k θ) (volume.restrict Work.Spaces.Iθ) :=
    integrable_finsetSum Finset.univ fun k _ => hper k
  -- The remaining factor `θ ↦ f z θ * z` is bounded on the compact `Iθ`.
  obtain ⟨Cf, _hCf0, hCf⟩ := exists_nonneg_bound_abs (continuousOn_slice hsmf hz)
  have haesm : AEStronglyMeasurable (fun θ => f z θ * z)
      (volume.restrict Work.Spaces.Iθ) :=
    ((continuousOn_slice hsmf hz).mul continuousOn_const).aestronglyMeasurable measurableSet_Icc
  have hbdd : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ‖f z θ * z‖ ≤ Cf * |z| := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hCf θ hθ) (abs_nonneg z)
  have hmain : Integrable
      (fun θ => (∑ k : Fin 5, Work.Spaces.pz (Thard g k) z θ * Thard g k z θ
        * (Work.Spaces.w z) ^ 2 * sghard α k θ) * (f z θ * z))
      (volume.restrict Work.Spaces.Iθ) :=
    hS.mul_bdd haesm hbdd
  -- The product is `Hhard`, up to the order of the factors.
  refine hmain.congr ?_
  filter_upwards with θ
  simp only [Hhard]
  ring

end Work.FTS.H2
