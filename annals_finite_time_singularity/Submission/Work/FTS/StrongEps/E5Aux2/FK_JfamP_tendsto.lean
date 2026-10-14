import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsWPLim.Basic
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary facts about the slices, the weight `F_*` and the angular kernel `K` -/

/-- The `θ`-slice of a function which is smooth on the open quadrant is continuous on
`(0,π/2)`. -/
theorem continuousOn_thSlice_of_smoothOpen {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ : ℝ => f z θ) (Set.Ioo 0 (π/2)) := by
  have hcont : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0 := hf.continuousOn
  have hmap : MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (π/2)) Work.FTS.EllipticEst.Q0 :=
    fun θ hθ => ⟨hz, hθ⟩
  have hcomp := hcont.comp ((continuous_const.prodMk continuous_id).continuousOn) hmap
  convert hcomp using 1
  funext θ
  rfl

/-- `Γ(θ) = (sinθ cos²θ)^{α/3}` is continuous on the open interval `(0,π/2)`, where its base
is positive. -/
theorem continuousOn_Gam_Ioo {α : ℝ} (hα : 0 < α) :
    ContinuousOn (fun θ : ℝ => Work.Spaces.Gam α θ) (Set.Ioo 0 (π/2)) := by
  unfold Work.Spaces.Gam
  apply ContinuousOn.rpow
  · exact Real.continuous_sin.continuousOn.mul (Real.continuous_cos.continuousOn.pow 2)
  · exact continuousOn_const
  · intro θ hθ
    right
    exact div_pos hα (by norm_num)

/-- The reference profile `F_*(z,·)` is continuous on `(0,π/2)` (it is
`α·(Γ(θ)/c(α))·F_{*,rad}(z)`). -/
theorem continuousOn_Fstar_Ioo {α z : ℝ} (hα : 0 < α) :
    ContinuousOn (fun θ : ℝ => Work.Construction.Fstar α z θ) (Set.Ioo 0 (π/2)) := by
  have hGam := continuousOn_Gam_Ioo (α := α) hα
  have h1 : ContinuousOn
      (fun θ : ℝ => (α * Work.FM.Fstar z / Work.Spaces.c α) * Work.Spaces.Gam α θ)
      (Set.Ioo 0 (π/2)) := continuousOn_const.mul hGam
  refine h1.congr ?_
  intro θ hθ
  unfold Work.Construction.Fstar
  ring

/-- The radial factor `2z/(1+z)²` of the reference profile is bounded by `2` for `z > 0`. -/
theorem abs_FM_Fstar_le_two {z : ℝ} (hz : 0 < z) : |Work.FM.Fstar z| ≤ 2 := by
  rw [Work.FM.Fstar, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (1 + z), sq_nonneg z]

/-- **Pointwise bound of the reference profile**: `|F_*(z,θ)| ≤ 20` for `θ ∈ Iθ`, `0 < α ≤ 1`. -/
theorem abs_Fstar_le_twenty {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) : |Work.Construction.Fstar α z θ| ≤ 20 := by
  have hG := Work.Spaces.Gam_bounds α θ hα hθ
  have hc := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith [hc.1]
  have hdiv : |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 := by
    rw [abs_of_nonneg (div_nonneg hG.1 hcpos.le), div_le_iff₀ hcpos]
    nlinarith [hG.2, hc.1]
  have hrad : |Work.FM.Fstar z| ≤ 2 := abs_FM_Fstar_le_two hz
  rw [Work.Construction.Fstar, abs_mul, abs_mul]
  have ha : |α| ≤ 1 := by rw [abs_of_pos hα]; exact hα1
  calc |α| * |Work.Spaces.Gam α θ / Work.Spaces.c α| * |Work.FM.Fstar z|
      ≤ 1 * 10 * 2 :=
        mul_le_mul (mul_le_mul ha hdiv (abs_nonneg _) (by norm_num)) hrad (abs_nonneg _)
          (by norm_num)
    _ = 20 := by norm_num

/-- The angular kernel `K(θ) = 3 sinθ cos²θ` is bounded by `3` everywhere. -/
theorem abs_K_le_three (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  rw [Work.Spaces.K, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3), abs_pow]
  have h1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have h2 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  nlinarith [abs_nonneg (Real.cos θ), abs_nonneg (Real.sin θ)]

/-- Almost every `θ ∈ Iθ` is an *interior* point of `Iθ` (the two endpoints form a null set). -/
theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π/2) := by
  refine MeasureTheory.ae_iff.mpr ?_
  have hcomp : MeasurableSet {θ : ℝ | ¬ θ ∈ Set.Ioo 0 (π/2)} := measurableSet_Ioo.compl
  rw [MeasureTheory.Measure.restrict_apply hcomp]
  refine measure_mono_null (t := ({0, π/2} : Set ℝ)) ?_ ?_
  · intro θ hθ
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ioo, Work.Spaces.Iθ, Set.mem_Icc]
      at hθ
    obtain ⟨h2, h0, h1⟩ := hθ
    by_cases h3 : θ = 0
    · exact Or.inl h3
    · refine Or.inr (le_antisymm h1 ?_)
      by_contra hlt
      exact h2 ⟨lt_of_le_of_ne h0 (Ne.symm h3), lt_of_not_ge hlt⟩
  · have h : ({0, π/2} : Set ℝ) = {0} ∪ {Real.pi / 2} := rfl
    rw [h]
    exact MeasureTheory.measure_union_null (measure_singleton 0) (measure_singleton _)

/-! ## The dominated-convergence step -/

/-- **Dominated convergence for the angular moment.**  If the `θ`-integrands `F n z · * K`
are a.e. strongly measurable, dominated by the constant `C` and converge a.e. to
`G z · * K`, then `𝔽K (F n) z → 𝔽K G z`. -/
theorem FK_tendsto_of_dominated {C : ℝ} {F : ℕ → ℝ → ℝ → ℝ} {G : ℝ → ℝ → ℝ} {z : ℝ}
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun θ => F n z θ * Work.Spaces.K θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hbdd : ∀ n : ℕ, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖F n z θ * Work.Spaces.K θ‖ ≤ C)
    (hCint : Integrable (fun _ : ℝ => C) (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hlim : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Tendsto (fun n => F n z θ * Work.Spaces.K θ) atTop (nhds (G z θ * Work.Spaces.K θ))) :
    Tendsto (fun n => Work.Construction.FK (F n) z) atTop (nhds (Work.Construction.FK G z)) := by
  have h := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (F := fun (n : ℕ) (θ : ℝ) => F n z θ * Work.Spaces.K θ)
    (f := fun θ : ℝ => G z θ * Work.Spaces.K θ)
    (bound := fun _ : ℝ => C) hmeas hCint hbdd hlim
  simpa only [Work.Construction.FK] using h

/-! ## The target -/

theorem FK_JfamP_tendsto {α B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam} {s : ℝ} {Maj : ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1) (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hsm : ∀ n : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (Work.FTS.Galerkin.slice (G n) s)) Work.FTS.StrongEps.Quad)
    (hconv : Work.FTS.StrongEps.ConvLocUnifH6 α B (fun n => Work.FTS.Galerkin.slice (G n) s)
      (Work.FTS.Galerkin.slice g s))
    (hC : ∀ n : ℕ, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (hMajint : MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0))
    (hDec : ∀ n : ℕ, Work.FTS.StrongEps.EpsDecay α ρ Φs E (ε n) s (G n) Maj)
    (hl12 : Filter.Tendsto (fun n : ℕ => Work.Construction.L12
      (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) s)) 0)
      Filter.atTop (nhds 0)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), Filter.Tendsto (fun n : ℕ => Work.Construction.FK
      (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z) Filter.atTop
      (nhds (Work.Construction.FK (Work.Construction.Ftau α g s) z)) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- the angular-regularity hypothesis in the shape demanded by `mixed_JfamP_tendsto`
  have hsm' : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ k
      (Function.uncurry (Work.FTS.Galerkin.slice (G n) s))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun n k => by simpa only [Work.FTS.StrongEps.Quad] using hsm n k
  intro z hz
  refine FK_tendsto_of_dominated (C := (63 : ℝ))
    (F := fun n => Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
    (G := Work.Construction.Ftau α g s) ?_ ?_ ?_ ?_
  -- the two measures `volume.restrict (0,π/2)` and `volume.restrict Iθ` agree (the endpoints are
  -- null), which is what turns the open-quadrant regularity into a.e. measurability on `Iθ`
  have hrestrIoo : MeasureTheory.volume.restrict (Set.Ioo 0 (π/2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact Measure.restrict_congr_set Ioo_ae_eq_Icc
  · -- measurable a.e.: open-quadrant smoothness of the projected slices
    intro n
    have hJc : ContinuousOn (fun θ : ℝ =>
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ)
        (Set.Ioo 0 (π/2)) := continuousOn_thSlice_of_smoothOpen (hC n).reg hz
    have hFc : ContinuousOn (fun θ : ℝ => Work.Construction.Fstar α z θ)
        (Set.Ioo 0 (π/2)) := continuousOn_Fstar_Ioo hα0
    have hKc : ContinuousOn (fun θ : ℝ => Work.Spaces.K θ) (Set.Ioo 0 (π/2)) := by
      unfold Work.Spaces.K
      fun_prop
    show AEStronglyMeasurable (fun θ : ℝ => (Work.Construction.Fstar α z θ
      + (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ)
      * Work.Spaces.K θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ)
    rw [← hrestrIoo]
    exact ((hFc.add hJc).mul hKc).aestronglyMeasurable measurableSet_Ioo
  · -- the constant majorant `63`
    intro n
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hFb : |Work.Construction.Fstar α z θ| ≤ 20 :=
      abs_Fstar_le_twenty hα0 hα1 hz hθI
    have hJb : |Work.FTS.StrongEps.JfamP ρ (ε n) (G n) z θ s| ≤ 1 := by
      have h := (hDec n).2.2.2.1 z hz θ 0 0 (by norm_num)
      have hM : Maj z ≤ 1 := (hDec n).2.1 z
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
        Work.Spaces.DthIter, Work.Spaces.DzIter, Work.FTS.Galerkin.slice] using
        le_trans h hM
    have hKb : |Work.Spaces.K θ| ≤ 3 := abs_K_le_three θ
    show ‖(Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ
      * Work.Spaces.K θ‖ ≤ (63 : ℝ)
    show |(Work.Construction.Fstar α z θ + Work.FTS.StrongEps.JfamP ρ (ε n) (G n) z θ s)
      * Work.Spaces.K θ| ≤ (63 : ℝ)
    calc |(Work.Construction.Fstar α z θ + Work.FTS.StrongEps.JfamP ρ (ε n) (G n) z θ s)
          * Work.Spaces.K θ|
        ≤ (20 + 1) * 3 := by
          rw [abs_mul]
          refine mul_le_mul ?_ hKb (abs_nonneg _) (by norm_num)
          calc |Work.Construction.Fstar α z θ
                + Work.FTS.StrongEps.JfamP ρ (ε n) (G n) z θ s|
              ≤ |Work.Construction.Fstar α z θ|
                + |Work.FTS.StrongEps.JfamP ρ (ε n) (G n) z θ s| := abs_add_le _ _
            _ ≤ 20 + 1 := add_le_add hFb hJb
      _ = 63 := by norm_num
  · -- integrability of the constant majorant
    have hvol : MeasureTheory.volume Work.Spaces.Iθ ≠ ⊤ := by
      rw [Work.Spaces.Iθ, Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    have hb : ‖(63 : ℝ)‖ₑ ≠ ⊤ := by simp
    exact integrableOn_const (C := (63 : ℝ)) (μ := MeasureTheory.volume)
      (s := Work.Spaces.Iθ) hvol hb
  · -- the a.e. pointwise convergence of the slices
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    have hp : (z, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := ⟨hz, hθ⟩
    have hJ := Work.FTS.StrongEps.mixed_JfamP_tendsto (τ := s) hρ hsm' hconv
      (fun n => (hε n).1) hε0 hl12 hp (j := 0) (i := 0) (by norm_num)
    have hJ' : Tendsto (fun n : ℕ => Work.FTS.StrongEps.JfamP ρ (ε n) (G n) z θ s)
        atTop (nhds (g z θ s)) := by
      simpa only [Work.FTS.Galerkin.slice, Work.Spaces.mixed_zero_left,
        Work.Spaces.mixed_zero_right, Work.Spaces.DthIter, Work.Spaces.DzIter] using hJ
    have hsum : Tendsto (fun n : ℕ => Work.Construction.Fstar α z θ
          + Work.FTS.StrongEps.JfamP ρ (ε n) (G n) z θ s) atTop
        (nhds (Work.Construction.Fstar α z θ + g z θ s)) :=
      tendsto_const_nhds.add hJ'
    have hprod : Tendsto (fun n : ℕ => (Work.Construction.Fstar α z θ
          + Work.FTS.StrongEps.JfamP ρ (ε n) (G n) z θ s) * Work.Spaces.K θ) atTop
        (nhds ((Work.Construction.Fstar α z θ + g z θ s) * Work.Spaces.K θ)) :=
      hsum.mul_const _
    simpa only [Work.Construction.Ftau] using hprod

end Work.FTS.StrongEps.E5Aux2
