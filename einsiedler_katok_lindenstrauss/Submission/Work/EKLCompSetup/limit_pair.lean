import Mathlib
import Submission.Work.EKLComp.C8Defs
import Submission.Work.EKLC8Core.All
import Submission.Work.EKLCompSetup.step7_set
import Submission.Work.EKLCompSetup.limit_step
import Submission.Work.EKLCompSetup.exists_return
import Submission.Work.EKLNonExc.MatrixFacts
import Submission.Work.EKLCompSetup.kappa_lt_of_mem_V

/-!
# The limit pair of the low-entropy argument (EKL §4.2–4.5, Steps 6–11)

Given the data `C8Setup μ` produced by Steps 1–5 of the low-entropy argument and the
non-exceptional returns `NonExceptional μ h01 2`, this file produces the pair `y, y' ∈ X₁`
with `y' = h • y` for some `h ∈ U_(01)`, `h ≠ 1`, and `ν_y = ν_{y'}`.

The proof runs the per-`δ` construction of EKL §4.4–4.5 (Steps 6–11 of `ROUTE_LEAD.md` §5):

* Step 6 (`exists_return`): a compact `K ⊆ X₃` of positive measure with non-exceptional
  returns, giving `z, z' ∈ K` and `g ∈ V δ ∖ L_{01}` with `z' = g • z = α'_2(s) • z`;
* Step 7 (`step7_set`): the flow-density lemma EKL 4.5, for each of the eight
  `(η, θ)`-configurations used below;
* Step 8 (this file): the pigeonhole over the eight sets, the time `τ`, the bound
  `κ(x,x') ≤ κ(z,z')^{3/4}` and the choice of the scale `R = κ(x,x')⁻¹`;
* Steps 9–10 (`step9_10`): the shear parameter `r`, the points in `X₁` and the H-property
  bounds;
* Step 11 (`limit_step`): `δ → 0` and the limit pair.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Matrix
open Work.EKLContract Work.EKLComp

set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLCompSetup

/-! ## Arithmetic of the exponentials of the flow times -/

/-- `e^{4·Tscale κ} = κ⁻¹` for `0 < κ < 1`. -/
theorem exp_four_Tscale {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    Real.exp (4 * Work.EKLC8Core.Tscale κ) = κ⁻¹ := by
  have hlog : Real.log κ < 0 := Real.log_neg hκ0 hκ1
  have h : (4 : ℝ) * Work.EKLC8Core.Tscale κ = -Real.log κ := by
    rw [Work.EKLC8Core.Tscale, abs_of_neg hlog]; ring
  rw [h, Real.exp_neg, Real.exp_log hκ0]

/-- `e^{5|log ρ|} = (ρ⁻¹)^5` for `0 < ρ < 1`. -/
theorem exp_five_log_abs {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Real.exp (5 * |Real.log ρ|) = (ρ⁻¹) ^ 5 := by
  have hlog : Real.log ρ < 0 := Real.log_neg hρ0 hρ1
  have h : (5 : ℝ) * |Real.log ρ| = -(((5 : ℕ) : ℝ) * Real.log ρ) := by
    rw [abs_of_neg hlog]; ring
  rw [h, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hρ0, inv_pow]

/-- `e^{-log x - t} = (e^t x)⁻¹` for `x > 0`. -/
theorem exp_neg_log_sub (x t : ℝ) (hx : 0 < x) :
    Real.exp (-Real.log x - t) = (Real.exp t * x)⁻¹ := by
  rw [Real.exp_sub, Real.exp_neg, Real.exp_log hx, div_eq_mul_inv, ← mul_inv, mul_comm]

/-- `e^{-log x + 5|log ρ| - t} = (ρ⁻¹)^5 * (e^t x)⁻¹` for `x, ρ > 0`, `ρ < 1`. -/
theorem exp_log_shift (x ρ t : ℝ) (hx : 0 < x) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Real.exp (-Real.log x + 5 * |Real.log ρ| - t) = (ρ⁻¹) ^ 5 * (Real.exp t * x)⁻¹ := by
  have h : -Real.log x + 5 * |Real.log ρ| - t = 5 * |Real.log ρ| + (-Real.log x - t) := by
    ring
  rw [h, Real.exp_add, exp_five_log_abs hρ0 hρ1, exp_neg_log_sub x t hx]

/-- The scale bound on `κ(x,x')` at the found time. -/
noncomputable def kappaBnd (δ : ℝ) : ℝ := (2 * δ ^ (1 / 2 : ℝ)) ^ (3 / 4 : ℝ)

/-- The uniform bound on the six "small" entries of the limit displacement. -/
noncomputable def cBnd (ρ δ : ℝ) : ℝ := δ + (ρ⁻¹) ^ 5 * kappaBnd δ + kappaBnd δ

/-- The displacement after time `τ` of the contracting flow: `φ_τ g φ_τ⁻¹`. -/
noncomputable def flowConj (g : Work.EKLContract.SL3) (τ : ℝ) : Work.EKLContract.SL3 :=
  Work.EKLComp.phi τ * g * (Work.EKLComp.phi τ)⁻¹

/-- EKL's `κ(x,x')` for the pair `(φ_τ z, φ_τ z')` with displacement `g`. -/
noncomputable def kappaFlow (g : Work.EKLContract.SL3) (τ : ℝ) : ℝ :=
  Work.EKLC8Core.kappa ((flowConj g τ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)

theorem kappaFlow_eq (g : Work.EKLContract.SL3) (τ : ℝ) :
    kappaFlow g τ = max (Work.EKLC8Core.kappaA ((g : Work.EKLContract.SL3) :
        Matrix (Fin 3) (Fin 3) ℝ))
      (Real.exp τ * Work.EKLC8Core.kappaU ((g : Work.EKLContract.SL3) :
        Matrix (Fin 3) (Fin 3) ℝ)) := by
  rw [kappaFlow, flowConj]
  exact (Work.EKLC8Core.kappa_conj τ g).2.2

theorem flowExp_zero : Work.EKLC8Core.flowExp 0 = (-1 : ℝ) := by
  simp [Work.EKLC8Core.flowExp]

theorem flowExp_one : Work.EKLC8Core.flowExp 1 = (1 : ℝ) := by
  simp [Work.EKLC8Core.flowExp]

theorem flowExp_two : Work.EKLC8Core.flowExp 2 = (0 : ℝ) := by
  simp [Work.EKLC8Core.flowExp]

/-- The characterisation of the centraliser `L_{01}` of `U_{01}` in terms of `κ`: for
`g ∈ SL₃(ℝ)`, `κ(g) = 0` exactly when `g` commutes with `u_{01}(1)` (EKL §4.4, `g ∉ L_{12}`).
This is the entry-level computation `g (1 + E₀₁) = (1 + E₀₁) g`. -/
theorem kappa_eq_zero_iff_mem_Lset' (g : Work.EKLContract.SL3) :
    Work.EKLC8Core.kappa ((g : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) = 0 ↔
      g ∈ Work.EKLContract.Lset Work.EKLComp.h01 := by
  have hmax0 : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (max a b = 0 ↔ (a = 0 ∧ b = 0)) := by
    intro a b ha hb
    constructor
    · intro h
      exact ⟨le_antisymm (le_trans (le_max_left _ _) (le_of_eq h)) ha,
        le_antisymm (le_trans (le_max_right _ _) (le_of_eq h)) hb⟩
    · rintro ⟨rfl, rfl⟩; simp
  have hAnn : ∀ G : Matrix (Fin 3) (Fin 3) ℝ, 0 ≤ Work.EKLC8Core.kappaA G :=
    fun G => abs_nonneg _
  have hUnn : ∀ G : Matrix (Fin 3) (Fin 3) ℝ, 0 ≤ Work.EKLC8Core.kappaU G := by
    intro G
    rw [Work.EKLC8Core.kappaU]
    exact le_trans (Real.sqrt_nonneg _) (le_max_left _ _)
  have hA : ∀ G : Matrix (Fin 3) (Fin 3) ℝ,
      Work.EKLC8Core.kappaA G = 0 ↔ G 1 1 = G 0 0 := by
    intro G
    rw [Work.EKLC8Core.kappaA, abs_eq_zero]
    constructor <;> intro h <;> linarith
  have hU : ∀ G : Matrix (Fin 3) (Fin 3) ℝ,
      Work.EKLC8Core.kappaU G = 0 ↔ (G 1 0 = 0 ∧ G 2 0 = 0 ∧ G 1 2 = 0) := by
    intro G
    rw [Work.EKLC8Core.kappaU]
    constructor
    · intro h
      have h1 : Real.sqrt |G 1 0| ≤ 0 := le_trans (le_max_left _ _) (le_of_eq h)
      have h2 : max |G 2 0| |G 1 2| ≤ 0 := le_trans (le_max_right _ _) (le_of_eq h)
      have h10 : G 1 0 = 0 := by
        have hs : Real.sqrt |G 1 0| = 0 := le_antisymm h1 (Real.sqrt_nonneg _)
        have hle : |G 1 0| ≤ 0 := Real.sqrt_eq_zero'.mp hs
        exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
      have h20 : G 2 0 = 0 :=
        abs_eq_zero.mp (le_antisymm (le_trans (le_max_left _ _) h2) (abs_nonneg _))
      have h12 : G 1 2 = 0 :=
        abs_eq_zero.mp (le_antisymm (le_trans (le_max_right _ _) h2) (abs_nonneg _))
      exact ⟨h10, h20, h12⟩
    · rintro ⟨h10, h20, h12⟩
      rw [h10, h20, h12]
      norm_num
  have hκ : Work.EKLC8Core.kappa ((g : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) = 0 ↔
      (Work.EKLC8Core.kappaA ((g : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) = 0 ∧
       Work.EKLC8Core.kappaU ((g : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) = 0) := by
    rw [Work.EKLC8Core.kappa]
    exact hmax0 _ _ (hAnn _) (hUnn _)
  rw [hκ, hA, hU, Work.EKLNonExc.mem_Lset_iff Work.EKLComp.h01 g]
  constructor
  · rintro ⟨h00, h10, h20, h12⟩
    refine ⟨h00.symm, ?_, ?_⟩
    · intro i hi
      fin_cases i
      · exact (hi rfl).elim
      · exact h10
      · exact h20
    · intro j hj
      fin_cases j
      · exact h10
      · exact (hj rfl).elim
      · exact h12
  · rintro ⟨h00, h1, h2⟩
    exact ⟨h00.symm, h1 1 (by decide), h1 2 (by decide), h2 2 (by decide)⟩


/-! ## Steps 9–10 (EKL §4.5): the shear parameter `r` and the H-property bounds -/

/-- **Bridge between the leafwise measure and its `ℝ`-valued push-forward.** If `ν` is carried
by `U_{01}`, then for a measurable `C ⊆ SL₃(ℝ)`
`nuR ν {r | u(r) ∈ C} = ν C` — one recovers `ν` from `nuR ν` because `par` inverts `r ↦ u(r)`
on `U_{01}`. -/
theorem nuR_preimage_u {ν : MeasureTheory.Measure Work.EKLContract.SL3}
    (hcar : ν (Work.EKLContract.Uij Work.EKLComp.h01 : Set Work.EKLContract.SL3)ᶜ = 0)
    {C : Set Work.EKLContract.SL3} (hC : MeasurableSet C) :
    Work.EKLComp.nuR ν {r : ℝ | Work.EKLC8Core.u r ∈ C} = ν C := by
  have hcont : Continuous fun r : ℝ => Work.EKLC8Core.u r :=
    Work.EKLContract.Lemmas.horoUij_cont Work.EKLComp.h01
  have hS : MeasurableSet {r : ℝ | Work.EKLC8Core.u r ∈ C} := hC.preimage hcont.measurable
  have hmem : ∀ g ∈ (Work.EKLContract.Uij Work.EKLComp.h01 : Set Work.EKLContract.SL3),
      Work.EKLC8Core.u (Work.EKLComp.par g) = g := by
    intro g hg
    obtain ⟨t, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff Work.EKLComp.h01 g).mp hg
    rw [Work.EKLComp.par_uij_h01]
    rfl
  have hset : Work.EKLComp.par ⁻¹' {r : ℝ | Work.EKLC8Core.u r ∈ C}
      ∩ (Work.EKLContract.Uij Work.EKLComp.h01 : Set Work.EKLContract.SL3)
      = C ∩ (Work.EKLContract.Uij Work.EKLComp.h01 : Set Work.EKLContract.SL3) := by
    ext g
    constructor
    · rintro ⟨hg, hgU⟩
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hg
      rw [hmem g hgU] at hg
      exact ⟨hg, hgU⟩
    · rintro ⟨hgC, hgU⟩
      refine ⟨?_, hgU⟩
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      rw [hmem g hgU]
      exact hgC
  have hdiff : ν (C \ (Work.EKLContract.Uij Work.EKLComp.h01 : Set Work.EKLContract.SL3)) = 0 :=
    measure_mono_null (fun g hg => hg.2) hcar
  have hdecomp := MeasureTheory.measure_inter_add_sdiff (μ := ν) C
    (Work.EKLComp.closed_Uij.measurableSet)
  rw [hdiff, add_zero] at hdecomp
  have h1 : Work.EKLComp.nuR ν {r : ℝ | Work.EKLC8Core.u r ∈ C}
      = ν (C ∩ (Work.EKLContract.Uij Work.EKLComp.h01 : Set Work.EKLContract.SL3)) := by
    rw [Work.EKLComp.nuR, Measure.map_apply Work.EKLComp.measurable_par hS,
      Measure.restrict_apply (Work.EKLComp.measurable_par hS), hset]
  rw [h1]
  exact hdecomp

/-- Two measures carried by `U_{01}` with the same `nuR` are equal. -/
theorem eq_of_nuR_eq {ν₁ ν₂ : MeasureTheory.Measure Work.EKLContract.SL3}
    (h₁ : ν₁ (Work.EKLContract.Uij Work.EKLComp.h01 : Set Work.EKLContract.SL3)ᶜ = 0)
    (h₂ : ν₂ (Work.EKLContract.Uij Work.EKLComp.h01 : Set Work.EKLContract.SL3)ᶜ = 0)
    (h : Work.EKLComp.nuR ν₁ = Work.EKLComp.nuR ν₂) : ν₁ = ν₂ := by
  refine MeasureTheory.Measure.ext fun C hC => ?_
  rw [← nuR_preimage_u h₁ hC, ← nuR_preimage_u h₂ hC, h]

/-- **`leafMass` as a measure of a set.** On a point `x`, the mass of the plaque that lies in
`S` is the `ν_x`-measure of the part of the plaque whose `g`-translate lies in `S`. -/
theorem leafMass_eq_measure {ν : X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {x : X3} {S : Set X3} (hS : MeasurableSet S) (hcont : Continuous fun g : Work.EKLContract.SL3 => g • x)
    (R : ℝ) :
    Work.EKLComp.leafMass ν S R x
      = ν x (Work.EKLContract.ballU Work.EKLComp.h01 R ∩ {g : Work.EKLContract.SL3 | g • x ∈ S}) := by
  have hA : MeasurableSet {g : Work.EKLContract.SL3 | g • x ∈ S} :=
    hS.preimage hcont.measurable
  have hB : MeasurableSet (Work.EKLContract.ballU Work.EKLComp.h01 R) :=
    (Work.EKLComp.isCompact_ballU R).isClosed.measurableSet
  rw [Work.EKLComp.leafMass, ← MeasureTheory.lintegral_indicator hB]
  have hfun : ∀ g : Work.EKLContract.SL3,
      (Work.EKLContract.ballU Work.EKLComp.h01 R).indicator
          (fun g => Set.indicator S (fun _ => (1 : ℝ≥0∞)) (g • x)) g
        = (Work.EKLContract.ballU Work.EKLComp.h01 R ∩ {g : Work.EKLContract.SL3 | g • x ∈ S}).indicator
            (fun _ => (1 : ℝ≥0∞)) g := by
    intro g
    by_cases hg : g ∈ Work.EKLContract.ballU Work.EKLComp.h01 R
    · rw [Set.indicator_of_mem hg]
      by_cases hx : g • x ∈ S
      · have hmem : g ∈ Work.EKLContract.ballU Work.EKLComp.h01 R
            ∩ {g : Work.EKLContract.SL3 | g • x ∈ S} := ⟨hg, hx⟩
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx h.2)]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg h.1)]
  rw [MeasureTheory.lintegral_congr (fun g => hfun g),
    MeasureTheory.lintegral_indicator (hB.inter hA)]
  simp

/-- The set of shear parameters `r` for which `u(r) • x` lies in `X₁`. -/
theorem measurableSet_shift (x : X3) :
    MeasurableSet {r : ℝ | Work.EKLC8Core.u r • x ∈ (Set.univ : Set X3)} := by
  simp

/-- **The mass bound of Step 9**: for `x ∈ X₂` the set of `r ∈ [-R,R]` with `u(r) • x ∈ X₁`
carries all but an `ε²`-fraction of the `nuR`-mass of `[-R,R]`. -/
theorem mass_bound {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ]
    [PolishSpace X3] (D : Work.EKLComp.C8Setup μ) {x : X3} (hx : x ∈ D.X₂) (R : ℝ) (hR : 0 < R) :
    MeasurableSet {r : ℝ | Work.EKLC8Core.u r • x ∈ D.X₁} ∧
      (1 - D.ε ^ 2) * (Work.EKLComp.nuR (D.ν x)).real (Set.Icc (-R) R)
        ≤ (Work.EKLComp.nuR (D.ν x)).real
            ({r : ℝ | Work.EKLC8Core.u r • x ∈ D.X₁} ∩ Set.Icc (-R) R) := by
  have hx'' : x ∈ D.X'' := (D.X₂_def x).mp hx |>.1
  have hx' : x ∈ D.X' := D.X''_sub hx''
  have hcar : D.ν x (Work.EKLContract.Uij Work.EKLComp.h01 :
      Set Work.EKLContract.SL3)ᶜ = 0 := D.lw.carried x hx'
  have hcont : Continuous fun g : Work.EKLContract.SL3 => g • x :=
    continuous_smul.comp (continuous_id.prodMk continuous_const)
  have hA : MeasurableSet {g : Work.EKLContract.SL3 | g • x ∈ D.X₁} :=
    D.X₁_compact.isClosed.measurableSet.preimage hcont.measurable
  have hcontu : Continuous fun r : ℝ => Work.EKLC8Core.u r :=
    Work.EKLContract.Lemmas.horoUij_cont Work.EKLComp.h01
  have hpar_u : ∀ r : ℝ, Work.EKLComp.par (Work.EKLC8Core.u r) = r := by
    intro r
    show (((Work.EKLC8Core.u r : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 0 1 = r
    exact Work.EKLContract.Lemmas.uij_apply_self Work.EKLComp.h01 r
  have hball : ∀ r : ℝ, Work.EKLC8Core.u r ∈ Work.EKLContract.ballU Work.EKLComp.h01 R ↔
      r ∈ Set.Icc (-R) R := by
    intro r
    rw [Work.EKLContract.ballU, Set.mem_image]
    constructor
    · rintro ⟨s, hs, hsr⟩
      have h1 : s = r := by
        have h2 := congrArg Work.EKLComp.par hsr
        simpa only [Work.EKLComp.par_uij_h01, hpar_u] using h2
      rwa [h1] at hs
    · intro hr
      exact Set.mem_image_of_mem (fun s : ℝ => Work.EKLContract.uij Work.EKLComp.h01 s) hr
  have hset : {r : ℝ | Work.EKLC8Core.u r • x ∈ D.X₁} ∩ Set.Icc (-R) R
      = {r : ℝ | Work.EKLC8Core.u r ∈ (Work.EKLContract.ballU Work.EKLComp.h01 R
          ∩ {g : Work.EKLContract.SL3 | g • x ∈ D.X₁})} := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [hball r]
    tauto
  refine ⟨hA.preimage hcontu.measurable, ?_⟩
  have hmass : Work.EKLComp.nuR (D.ν x)
        ({r : ℝ | Work.EKLC8Core.u r • x ∈ D.X₁} ∩ Set.Icc (-R) R)
      = D.ν x (Work.EKLContract.ballU Work.EKLComp.h01 R
          ∩ {g : Work.EKLContract.SL3 | g • x ∈ D.X₁}) := by
    rw [hset]
    exact nuR_preimage_u hcar ((Work.EKLComp.isCompact_ballU R).isClosed.measurableSet.inter hA)
  have hX₂ := (D.X₂_def x).mp hx |>.2 R hR
  have h1 : (Work.EKLComp.nuR (D.ν x)).real (Set.Icc (-R) R)
      = (D.ν x (Work.EKLContract.ballU Work.EKLComp.h01 R)).toReal := by
    rw [MeasureTheory.Measure.real, Work.EKLComp.nuR_Icc]
  have h2 : (Work.EKLComp.leafMass D.ν D.X₁ R x).toReal
      = (Work.EKLComp.nuR (D.ν x)).real
          ({r : ℝ | Work.EKLC8Core.u r • x ∈ D.X₁} ∩ Set.Icc (-R) R) := by
    rw [leafMass_eq_measure D.X₁_compact.isClosed.measurableSet hcont R,
      MeasureTheory.Measure.real, hmass]
  rw [← h1, h2] at hX₂
  exact hX₂

/-- **Steps 9–10** (EKL §4.5): the shear parameter `r`, the two points in `X₁` and the
H-property bounds. -/
theorem step9_10'
    {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ] [PolishSpace X3]
    (D : Work.EKLComp.C8Setup μ)
    {x x' : X3} {G : Work.EKLContract.SL3} {κ δ : ℝ}
    (hx : x ∈ D.X₂) (hx' : x' ∈ D.X₂) (hd : x' = G • x)
    (hκ : Work.EKLC8Core.kappa (((G : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) = κ)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hδ0 : 0 < δ) (hδ : δ ≤ D.ρ ^ 4 / 4)
    (h00 : |(((G : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 0 0 - 1| ≤ δ)
    (h11 : |(((G : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 1 1 - 1| ≤ δ)
    (h22 : |(((G : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 2 2 - 1| ≤ δ)
    (h01 : |(((G : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 0 1| ≤ δ)
    (h02 : |(((G : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 0 2| ≤ δ)
    (h21 : |(((G : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 2 1| ≤ δ)
    (heqν : D.ν x = D.ν x')
    (hbad1 : Work.EKLC8Core.BadAt (Work.EKLComp.nuR (D.ν x)) D.ρ κ⁻¹)
    (hbad2 : Work.EKLC8Core.BadAt (Work.EKLComp.nuR (D.ν x')) D.ρ κ⁻¹)
    (hbad3 : Work.EKLC8Core.BadAt (Work.EKLComp.nuR (D.ν x)) D.ρ (D.ρ⁻¹ ^ 5 * κ⁻¹))
    (hbad4 : Work.EKLC8Core.BadAt (Work.EKLComp.nuR (D.ν x')) D.ρ (D.ρ⁻¹ ^ 5 * κ⁻¹)) :
    ∃ r : ℝ, ∃ y y' : X3,
      y ∈ D.X₁ ∧ y' ∈ D.X₁ ∧
      y = Work.EKLC8Core.u r • x ∧ y' = Work.EKLC8Core.u r • x' ∧
      D.ν y = D.ν y' ∧
      y' = Work.EKLC8Core.shear G r • y ∧
      D.ρ ^ 2 / 2 ≤ Work.EKLC8Core.u12max
        (((Work.EKLC8Core.shear G r : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) ∧
      Work.EKLC8Core.u12max
          (((Work.EKLC8Core.shear G r : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ))
        ≤ 2 * (D.ρ⁻¹) ^ 10 + 1 ∧
      |(((Work.EKLC8Core.shear G r : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 1 0| ≤ κ ^ 2 ∧
      |(((Work.EKLC8Core.shear G r : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 1 2| ≤ κ ∧
      |(((Work.EKLC8Core.shear G r : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 2 0| ≤ κ ∧
      |(((Work.EKLC8Core.shear G r : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 0 0 - 1|
        ≤ δ + D.ρ⁻¹ ^ 5 * κ ∧
      |(((Work.EKLC8Core.shear G r : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 1 1 - 1|
        ≤ δ + D.ρ⁻¹ ^ 5 * κ ∧
      |(((Work.EKLC8Core.shear G r : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 2 2 - 1| ≤ δ := by
  have hρ0 : 0 < D.ρ := D.ρ_pos
  have hρ1 : D.ρ ≤ 1 := le_trans D.ρ_small (by norm_num)
  have hρhalf : D.ρ ≤ 1 / 2 := D.ρ_small
  have hε2 : 2 * D.ε ^ 2 < 1 / 2 := by nlinarith [D.ε_small, D.ε_pos]
  have hR1 : 1 ≤ κ⁻¹ := (one_le_inv₀ hκ0).mpr hκ1
  have hρinv5 : (1 : ℝ) ≤ D.ρ⁻¹ ^ 5 := one_le_pow₀ ((one_le_inv₀ hρ0).mpr hρ1)
  have hR2 : 1 ≤ D.ρ⁻¹ ^ 5 * κ⁻¹ := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ D.ρ⁻¹ ^ 5 * κ⁻¹ := mul_le_mul hρinv5 hR1 (by norm_num) (by positivity)
  -- finiteness of the `nuR`-masses of the intervals
  have hfin : ∀ (z : X3) (S : ℝ), 0 < S →
      Work.EKLComp.nuR (D.ν z) (Set.Icc (-S) S) ≠ ⊤ := by
    intro z S _
    rw [Work.EKLComp.nuR_Icc]
    exact ((D.radon z).lt_top_of_isCompact (Work.EKLComp.isCompact_ballU _)).ne
  -- the two candidate shear parameters
  obtain ⟨r₁, hr₁mem, hr₁low, hr₁high⟩ := Work.EKLC8Core.step9_exists_r
    (ν := Work.EKLComp.nuR (D.ν x)) (ε := D.ε) (ρ := D.ρ) (R := κ⁻¹)
    (P := {r : ℝ | Work.EKLC8Core.u r • x ∈ D.X₁} ∩ Set.Icc (-(κ⁻¹)) (κ⁻¹))
    (P' := {r : ℝ | Work.EKLC8Core.u r • x' ∈ D.X₁} ∩ Set.Icc (-(κ⁻¹)) (κ⁻¹))
    D.ε_pos hε2 hρ0 hρ1 hR1 (D.norm x) (hfin x κ⁻¹ (by positivity))
    ((mass_bound D hx κ⁻¹ (by positivity)).1.inter measurableSet_Icc)
    ((mass_bound D hx' κ⁻¹ (by positivity)).1.inter measurableSet_Icc)
    Set.inter_subset_right Set.inter_subset_right
    (mass_bound D hx κ⁻¹ (by positivity)).2
    (by
      have h := (mass_bound D hx' κ⁻¹ (by positivity)).2
      rwa [← heqν] at h)
    hbad1
  obtain ⟨r₂, hr₂mem, hr₂low, hr₂high⟩ := Work.EKLC8Core.step9_exists_r
    (ν := Work.EKLComp.nuR (D.ν x)) (ε := D.ε) (ρ := D.ρ) (R := D.ρ⁻¹ ^ 5 * κ⁻¹)
    (P := {r : ℝ | Work.EKLC8Core.u r • x ∈ D.X₁} ∩
      Set.Icc (-(D.ρ⁻¹ ^ 5 * κ⁻¹)) (D.ρ⁻¹ ^ 5 * κ⁻¹))
    (P' := {r : ℝ | Work.EKLC8Core.u r • x' ∈ D.X₁} ∩
      Set.Icc (-(D.ρ⁻¹ ^ 5 * κ⁻¹)) (D.ρ⁻¹ ^ 5 * κ⁻¹))
    D.ε_pos hε2 hρ0 hρ1 hR2 (D.norm x) (hfin x (D.ρ⁻¹ ^ 5 * κ⁻¹) (by positivity))
    ((mass_bound D hx (D.ρ⁻¹ ^ 5 * κ⁻¹) (by positivity)).1.inter measurableSet_Icc)
    ((mass_bound D hx' (D.ρ⁻¹ ^ 5 * κ⁻¹) (by positivity)).1.inter measurableSet_Icc)
    Set.inter_subset_right Set.inter_subset_right
    (mass_bound D hx (D.ρ⁻¹ ^ 5 * κ⁻¹) (by positivity)).2
    (by
      have h := (mass_bound D hx' (D.ρ⁻¹ ^ 5 * κ⁻¹) (by positivity)).2
      rwa [← heqν] at h)
    hbad3
  have hr₂low' : (D.ρ⁻¹) ^ 4 * κ⁻¹ < |r₂| := by
    have h : D.ρ * (D.ρ⁻¹ ^ 5 * κ⁻¹) < |r₂| := hr₂low
    have heq : D.ρ * (D.ρ⁻¹ ^ 5 * κ⁻¹) = (D.ρ⁻¹) ^ 4 * κ⁻¹ := by
      rw [inv_pow]; field_simp; try ring
    rwa [heq] at h
  -- the drift dichotomy of Step 10
  have htwo := Work.EKLC8Core.step10_two_choice (ρ := D.ρ) (κ := κ) (r₁ := r₁) (r₂ := r₂)
    (G := ((G : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ))
    hρ0 hρhalf hκ0 hκ hr₁low hr₁high hr₂low' hr₂high
  -- the common conclusion for a shear parameter satisfying the two drift bounds
  have key : ∀ r : ℝ, (Work.EKLC8Core.u r • x ∈ D.X₁) → (Work.EKLC8Core.u r • x' ∈ D.X₁) →
      D.ρ ^ 2 ≤ Work.EKLC8Core.drift (((G : Work.EKLContract.SL3) :
        Matrix (Fin 3) (Fin 3) ℝ)) r →
      Work.EKLC8Core.drift (((G : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) r
        ≤ 2 * (D.ρ⁻¹) ^ 10 →
      |r| * κ ≤ (D.ρ⁻¹) ^ 5 →
      ∃ y y' : X3, y ∈ D.X₁ ∧ y' ∈ D.X₁ ∧
        y = Work.EKLC8Core.u r • x ∧ y' = Work.EKLC8Core.u r • x' ∧
        D.ν y = D.ν y' ∧
        y' = Work.EKLC8Core.shear G r • y ∧
        D.ρ ^ 2 / 2 ≤ Work.EKLC8Core.u12max
          (((Work.EKLC8Core.shear G r : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) ∧
        Work.EKLC8Core.u12max
            (((Work.EKLC8Core.shear G r : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ))
          ≤ 2 * (D.ρ⁻¹) ^ 10 + 1 ∧
        |(((Work.EKLC8Core.shear G r : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 1 0| ≤ κ ^ 2 ∧
        |(((Work.EKLC8Core.shear G r : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 1 2| ≤ κ ∧
        |(((Work.EKLC8Core.shear G r : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 2 0| ≤ κ ∧
        |(((Work.EKLC8Core.shear G r : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 0 0 - 1|
          ≤ δ + D.ρ⁻¹ ^ 5 * κ ∧
        |(((Work.EKLC8Core.shear G r : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 1 1 - 1|
          ≤ δ + D.ρ⁻¹ ^ 5 * κ ∧
        |(((Work.EKLC8Core.shear G r : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) 2 2 - 1|
          ≤ δ := by
    intro r hx₁ hx₁' hlo hhi hrκ
    have hupper := Work.EKLC8Core.step10_upper hρ0 hρ1 hκ0 hκ hrκ
    obtain ⟨hu12lo, hu12hi⟩ := Work.EKLC8Core.step10_u12_entries hρ0 hρhalf hδ0 hδ hκ0 hκ
      h01 h02 h21 hlo hhi hrκ
    obtain ⟨ho10, ho12, ho20, hd0, hd1, hd2⟩ := Work.EKLC8Core.step10_other_entries
      hρ0 hκ0 hκ h00 h11 h22 hupper.2
    have hx'' : x ∈ D.X'' := (D.X₂_def x).mp hx |>.1
    have hx''' : x' ∈ D.X'' := (D.X₂_def x').mp hx' |>.1
    have hy'' : Work.EKLC8Core.u r • x ∈ D.X'' := (D.X₁_sub hx₁).1
    have hy''' : Work.EKLC8Core.u r • x' ∈ D.X'' := (D.X₁_sub hx₁').1
    -- equality of the leafwise measures
    have hnuR : Work.EKLComp.nuR (D.ν (Work.EKLC8Core.u r • x))
        = Work.EKLComp.nuR (D.ν (Work.EKLC8Core.u r • x')) :=
      D.transfer x hx'' x' hx''' r hy'' hy''' (by rw [heqν])
    have hcar₁ : D.ν (Work.EKLC8Core.u r • x)
        (Work.EKLContract.Uij Work.EKLComp.h01 : Set Work.EKLContract.SL3)ᶜ = 0 :=
      D.lw.carried _ (D.X''_sub (D.X₁_sub hx₁).1)
    have hcar₂ : D.ν (Work.EKLC8Core.u r • x')
        (Work.EKLContract.Uij Work.EKLComp.h01 : Set Work.EKLContract.SL3)ᶜ = 0 :=
      D.lw.carried _ (D.X''_sub (D.X₁_sub hx₁').1)
    have hνeq : D.ν (Work.EKLC8Core.u r • x) = D.ν (Work.EKLC8Core.u r • x') :=
      eq_of_nuR_eq hcar₁ hcar₂ hnuR
    -- the displacement identity `u(r)x' = shear G r • (u(r)x)`
    have hu1 : Work.EKLC8Core.u (-r) * Work.EKLC8Core.u r = 1 := by
      have h2 : Work.EKLC8Core.u (-r) * Work.EKLC8Core.u r = Work.EKLC8Core.u (-r + r) :=
        (Work.EKLC8Core.uij_api (-r) r Work.EKLComp.h01).2.1
      have h0 : Work.EKLC8Core.u 0 = 1 := (Work.EKLC8Core.uij_api (-r) r Work.EKLComp.h01).1
      rw [h2, neg_add_cancel]
      exact h0
    have hscal : Work.EKLC8Core.u r * G = Work.EKLC8Core.shear G r * Work.EKLC8Core.u r := by
      rw [Work.EKLC8Core.shear, mul_assoc, hu1, mul_one]
    have hshear : Work.EKLC8Core.u r • x'
        = Work.EKLC8Core.shear G r • (Work.EKLC8Core.u r • x) := by
      rw [hd, ← mul_smul, ← mul_smul, hscal]
    refine ⟨Work.EKLC8Core.u r • x, Work.EKLC8Core.u r • x', hx₁, hx₁', rfl, rfl, hνeq, hshear,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [Work.EKLC8Core.shear_coe] using hu12lo
    · simpa only [Work.EKLC8Core.shear_coe] using hu12hi
    · simpa only [Work.EKLC8Core.shear_coe] using ho10
    · simpa only [Work.EKLC8Core.shear_coe] using ho12
    · simpa only [Work.EKLC8Core.shear_coe] using ho20
    · simpa only [Work.EKLC8Core.shear_coe] using hd0
    · simpa only [Work.EKLC8Core.shear_coe] using hd1
    · simpa only [Work.EKLC8Core.shear_coe] using hd2
  rcases htwo with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · have hrκ : |r₁| * κ ≤ (D.ρ⁻¹) ^ 5 := by
      calc |r₁| * κ ≤ κ⁻¹ * κ := mul_le_mul_of_nonneg_right hr₁high hκ0.le
        _ = 1 := inv_mul_cancel₀ hκ0.ne'
        _ ≤ (D.ρ⁻¹) ^ 5 := hρinv5
    exact ⟨r₁, key r₁ hr₁mem.1.1 hr₁mem.2.1 hlo hhi hrκ⟩
  · have hrκ : |r₂| * κ ≤ (D.ρ⁻¹) ^ 5 := by
      calc |r₂| * κ ≤ (D.ρ⁻¹ ^ 5 * κ⁻¹) * κ := mul_le_mul_of_nonneg_right hr₂high hκ0.le
        _ = (D.ρ⁻¹) ^ 5 := by rw [mul_assoc, inv_mul_cancel₀ hκ0.ne', mul_one]
    exact ⟨r₂, key r₂ hr₂mem.1.1 hr₂mem.2.1 hlo hhi hrκ⟩

/-! ## The per-`δ` construction (Steps 6–10) -/

theorem exists_pair_of_delta
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    [PolishSpace Work.EKLContract.X3]
    (D : Work.EKLComp.C8Setup μ) (hNE : Work.EKLContract.NonExceptional μ Work.EKLComp.h01 2)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ16 : δ < 1 / 16)
    (hδ40 : δ < D.ρ ^ 40 / 4) (hδρ : δ < D.ρ ^ 4 / 4) :
    ∃ (y y' : Work.EKLContract.X3) (H : Work.EKLContract.SL3),
      y ∈ D.X₁ ∧ y' ∈ D.X₁ ∧ y' = H • y ∧ D.ν y = D.ν y' ∧
      (∀ i j, |((H : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤
          2 * (D.ρ⁻¹) ^ 10 + (D.ρ⁻¹) ^ 5 + 3) ∧
      |((H : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 0 0 - 1| ≤ cBnd D.ρ δ ∧
      |((H : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 1 1 - 1| ≤ cBnd D.ρ δ ∧
      |((H : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 2 2 - 1| ≤ cBnd D.ρ δ ∧
      |((H : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 1 0| ≤ cBnd D.ρ δ ∧
      |((H : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 1 2| ≤ cBnd D.ρ δ ∧
      |((H : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 2 0| ≤ cBnd D.ρ δ ∧
      D.ρ ^ 2 / 2 ≤ Work.EKLC8Core.u12max
        ((H : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) := by
  obtain ⟨K, _hKc, hKX, _hKμ, hret⟩ := exists_return D hNE
  obtain ⟨z, hzK, s, g, hgV, hz'K, hz'eq, hgL⟩ := hret δ hδ0
  have hz₃ : z ∈ D.X₃ := hKX hzK
  have hz'₃ : Work.EKLContract.aPrime 2 s • z ∈ D.X₃ := hKX hz'K
  set z' : Work.EKLContract.X3 := Work.EKLContract.aPrime 2 s • z with hz'def
  set κa : ℝ := Work.EKLC8Core.kappaA ((g : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)
    with hκadef
  set κu : ℝ := Work.EKLC8Core.kappaU ((g : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)
    with hκudef
  set κ₀ : ℝ := Work.EKLC8Core.kappa ((g : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)
    with hκ₀def
  set T : ℝ := Work.EKLC8Core.Tscale κ₀ with hTdef
  -- basic bounds on `κa, κu, κ₀`
  have hκ₀max : κ₀ = max κa κu := by rw [hκ₀def, hκadef, hκudef, Work.EKLC8Core.kappa]
  have hκAnn : 0 ≤ κa := by rw [hκadef, Work.EKLC8Core.kappaA]; positivity
  have hκUnn : 0 ≤ κu := by rw [hκudef, Work.EKLC8Core.kappaU]; positivity
  have hκ₀nn : 0 ≤ κ₀ := by rw [hκ₀max]; exact le_trans hκAnn (le_max_left _ _)
  have hκ₀pos : 0 < κ₀ := by
    by_contra h
    have h0 : κ₀ = 0 := le_antisymm (not_lt.mp h) hκ₀nn
    rw [hκ₀def] at h0
    exact hgL ((kappa_eq_zero_iff_mem_Lset' g).mp h0)
  have hκ₀lt : κ₀ < 2 * δ ^ (1 / 2 : ℝ) := by
    rw [hκ₀def]; exact kappa_lt_of_mem_V hδ0 (by linarith) hgV
  have hδhalf : δ ^ (1 / 2 : ℝ) < 1 / 2 := by
    rw [← Real.sqrt_eq_rpow]
    have h : Real.sqrt δ < Real.sqrt (1 / 4) :=
      Real.sqrt_lt_sqrt (le_of_lt hδ0) (by linarith)
    rwa [show (1 / 4 : ℝ) = ((1 : ℝ) / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
  have hκ₀one : κ₀ < 1 := by linarith [hκ₀lt, hδhalf]
  have hρlt1 : D.ρ < 1 := lt_of_le_of_lt D.ρ_small (by norm_num)
  have hlogκ : Real.log κ₀ < 0 := Real.log_neg hκ₀pos hκ₀one
  have hT0 : 0 < T := by
    rw [hTdef, Work.EKLC8Core.Tscale, abs_of_neg hlogκ]; linarith
  have hT5 : 5 * |Real.log D.ρ| ≤ T := by
    rw [hTdef]
    exact Work.EKLC8Core.step5_T_ge D.ρ_pos hρlt1 hδ0 hδ40 hκ₀pos hκ₀lt rfl
  have hexp4T : Real.exp (4 * T) = κ₀⁻¹ := by
    rw [hTdef]; exact exp_four_Tscale hκ₀pos hκ₀one
  have hexp5 : Real.exp (5 * |Real.log D.ρ|) = (D.ρ⁻¹) ^ 5 :=
    exp_five_log_abs D.ρ_pos hρlt1
  -- `φ_τ` and `α'` commute, so `Φ_τ z' = α'_2(s) • Φ_τ z`
  have hPhi_a : ∀ τ : ℝ, Work.EKLComp.Phi τ (Work.EKLContract.aPrime 2 s • z)
      = Work.EKLContract.aPrime 2 s • Work.EKLComp.Phi τ z := by
    intro τ
    have hcomm : Work.EKLComp.phi τ * Work.EKLContract.aPrime 2 s
        = Work.EKLContract.aPrime 2 s * Work.EKLComp.phi τ :=
      Work.EKLC8Core.phi_comm_aPrime τ s 2
    show Work.EKLComp.phi τ • (Work.EKLContract.aPrime 2 s • z)
      = Work.EKLContract.aPrime 2 s • (Work.EKLComp.phi τ • z)
    rw [← mul_smul, hcomm, mul_smul]
  have h72 : 72 * D.ε < 1 := by linarith [D.ε_small]
  -- the `a`-family of Step 7 (available unconditionally)
  obtain ⟨Az, hAzm, hAzd, hAzp⟩ := step7_set D z hz₃ (T := T) (θ := 4 * T) (η := 0)
    hT0 (le_refl _) (by linarith) (le_refl 0) (by norm_num)
  obtain ⟨Az', hAz'm, hAz'd, hAz'p⟩ := step7_set D z' hz'₃ (T := T) (θ := 4 * T) (η := 0)
    hT0 (le_refl _) (by linarith) (le_refl 0) (by norm_num)
  obtain ⟨Az5, hAz5m, hAz5d, hAz5p⟩ := step7_set D z hz₃ (T := T)
    (θ := 4 * T + 5 * |Real.log D.ρ|) (η := 0)
    hT0 (by linarith [abs_nonneg (Real.log D.ρ)]) (by linarith) (le_refl 0) (by norm_num)
  obtain ⟨Az'5, hAz'5m, hAz'5d, hAz'5p⟩ := step7_set D z' hz'₃ (T := T)
    (θ := 4 * T + 5 * |Real.log D.ρ|) (η := 0)
    hT0 (by linarith [abs_nonneg (Real.log D.ρ)]) (by linarith) (le_refl 0) (by norm_num)
  -- the ν-equality at a time `τ` where both flow points lie in `X₂`
  have hνeq_of (τ : ℝ) (hx₂ : Work.EKLComp.Phi τ z ∈ D.X₂)
      (hx'₂ : Work.EKLComp.Phi τ z' ∈ D.X₂) :
      D.ν (Work.EKLComp.Phi τ z) = D.ν (Work.EKLComp.Phi τ z') := by
    have hx'' : Work.EKLComp.Phi τ z ∈ D.X'' := (D.X₂_def _).mp hx₂ |>.1
    have hx''' : Work.EKLContract.aPrime 2 s • Work.EKLComp.Phi τ z ∈ D.X'' := by
      rw [← hPhi_a τ, ← hz'def]
      exact (D.X₂_def _).mp hx'₂ |>.1
    have hcen := D.central (Work.EKLComp.Phi τ z) hx'' s hx'''
    rw [← hPhi_a τ, ← hz'def] at hcen
    exact hcen.symm
  -- The heart of Step 8: choose the time `τ` and get the badness at scale `κ(x,x')⁻¹`.
  have hkey : ∃ τ ∈ Set.Icc 0 T,
      Work.EKLComp.Phi τ z ∈ D.X₂ ∧ Work.EKLComp.Phi τ z' ∈ D.X₂ ∧
      D.ν (Work.EKLComp.Phi τ z) = D.ν (Work.EKLComp.Phi τ z') ∧
      Work.EKLC8Core.BadAt (Work.EKLComp.nuR (D.ν (Work.EKLComp.Phi τ z))) D.ρ
        (kappaFlow g τ)⁻¹ ∧
      Work.EKLC8Core.BadAt (Work.EKLComp.nuR (D.ν (Work.EKLComp.Phi τ z'))) D.ρ
        (kappaFlow g τ)⁻¹ ∧
      Work.EKLC8Core.BadAt (Work.EKLComp.nuR (D.ν (Work.EKLComp.Phi τ z))) D.ρ
        ((D.ρ⁻¹) ^ 5 * (kappaFlow g τ)⁻¹) ∧
      Work.EKLC8Core.BadAt (Work.EKLComp.nuR (D.ν (Work.EKLComp.Phi τ z'))) D.ρ
        ((D.ρ⁻¹) ^ 5 * (kappaFlow g τ)⁻¹) := by
    by_cases hU : ∀ τ ∈ Set.Icc 0 T, Real.exp τ * κu < κa
    · -- Case A: `κ(z,z') = κa`, so `κ(x,x') = κa` throughout and the `a`-family applies.
      have h0mem : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_refl 0, le_of_lt hT0⟩
      have hκult : κu < κa := by simpa using hU 0 h0mem
      have hκ₀eq : κ₀ = κa := by rw [hκ₀max]; exact max_eq_left (le_of_lt hκult)
      let P : Fin 8 → Set ℝ := ![Az, Az', Az5, Az'5, Az, Az', Az5, Az'5]
      have hPm : ∀ i, MeasurableSet (P i) := by
        intro i; fin_cases i <;> simp [P, hAzm, hAz'm, hAz5m, hAz'5m]
      have hPd : ∀ i, (1 - 9 * D.ε) * T ≤
          Work.EKLC8Core.vol (P i ∩ Set.Icc 0 T) := by
        intro i; fin_cases i <;> simp [P, hAzd, hAz'd, hAz5d, hAz'5d]
      obtain ⟨τ, hτIcc, hτall⟩ := Work.EKLC8Core.step8_nonempty hT0 D.ε_pos h72 hPm hPd
      have hτAz : τ ∈ Az := by simpa [P] using hτall 0
      have hτAz' : τ ∈ Az' := by simpa [P] using hτall 1
      have hτAz5 : τ ∈ Az5 := by simpa [P] using hτall 2
      have hτAz'5 : τ ∈ Az'5 := by simpa [P] using hτall 3
      obtain ⟨hx₂, hbad1⟩ := hAzp τ hτAz
      obtain ⟨hx'₂, hbad2⟩ := hAz'p τ hτAz'
      obtain ⟨-, hbad3⟩ := hAz5p τ hτAz5
      obtain ⟨-, hbad4⟩ := hAz'5p τ hτAz'5
      have hκτ : kappaFlow g τ = κa := by
        rw [kappaFlow_eq g τ, ← hκadef, ← hκudef]
        exact max_eq_left (le_of_lt (hU τ hτIcc))
      have hs1 : Real.exp (4 * T - 0 * τ) = (kappaFlow g τ)⁻¹ := by
        rw [hκτ, zero_mul, sub_zero, hexp4T, hκ₀eq]
      have hs2 : Real.exp (4 * T + 5 * |Real.log D.ρ| - 0 * τ)
          = (D.ρ⁻¹) ^ 5 * (kappaFlow g τ)⁻¹ := by
        rw [hκτ, zero_mul, sub_zero, Real.exp_add, hexp5, hexp4T, hκ₀eq]
        ring
      refine ⟨τ, hτIcc, hx₂, hx'₂, hνeq_of τ hx₂ hx'₂, ?_, ?_, ?_, ?_⟩
      · rwa [hs1] at hbad1
      · rwa [hs1] at hbad2
      · rwa [hs2] at hbad3
      · rwa [hs2] at hbad4
    · -- Case B: `κ(z,z') = κa` may fail; the `α'`-family of Step 7 is available.
      push_neg at hU
      obtain ⟨τ₀, hτ₀Icc, hτ₀le⟩ := hU
      have hκu0 : 0 < κu := by
        by_contra hcon
        have h : κu ≤ 0 := not_lt.mp hcon
        have hz0 : κa ≤ 0 := by
          have hexp := Real.exp_pos τ₀
          nlinarith
        have hmax0 : max κa κu ≤ 0 := max_le hz0 h
        have hzero : κ₀ = 0 := le_antisymm (by rw [hκ₀max]; exact hmax0) hκ₀nn
        linarith [hκ₀pos]
      have hex : ∃ τ ∈ Set.Icc 0 T, κ₀ ≤ Real.exp τ * κu := by
        refine ⟨τ₀, hτ₀Icc, ?_⟩
        have h1 : κu ≤ Real.exp τ₀ * κu := by
          have h2 : 1 ≤ Real.exp τ₀ := Real.one_le_exp hτ₀Icc.1
          nlinarith
        rw [hκ₀max]
        exact max_le hτ₀le h1
      obtain ⟨-, -, h4T, h5T⟩ := Work.EKLC8Core.step8_kappaU_range hκ₀pos hκ₀one hκu0
        (by rw [hκ₀max]; exact le_max_right _ _) hTdef hex
      obtain ⟨Uz, hUzm, hUzd, hUzp⟩ := step7_set D z hz₃ (T := T)
        (θ := -Real.log κu) (η := 1) hT0 h4T (by linarith) (by norm_num) (le_refl 1)
      obtain ⟨Uz', hUz'm, hUz'd, hUz'p⟩ := step7_set D z' hz'₃ (T := T)
        (θ := -Real.log κu) (η := 1) hT0 h4T (by linarith) (by norm_num) (le_refl 1)
      obtain ⟨Uz5, hUz5m, hUz5d, hUz5p⟩ := step7_set D z hz₃ (T := T)
        (θ := -Real.log κu + 5 * |Real.log D.ρ|) (η := 1)
        hT0 (by linarith [abs_nonneg (Real.log D.ρ)]) (by linarith [h5T, hT5])
        (by norm_num) (le_refl 1)
      obtain ⟨Uz'5, hUz'5m, hUz'5d, hUz'5p⟩ := step7_set D z' hz'₃ (T := T)
        (θ := -Real.log κu + 5 * |Real.log D.ρ|) (η := 1)
        hT0 (by linarith [abs_nonneg (Real.log D.ρ)]) (by linarith [h5T, hT5])
        (by norm_num) (le_refl 1)
      let P : Fin 8 → Set ℝ := ![Az, Az', Az5, Az'5, Uz, Uz', Uz5, Uz'5]
      have hPm : ∀ i, MeasurableSet (P i) := by
        intro i; fin_cases i <;>
          simp [P, hAzm, hAz'm, hAz5m, hAz'5m, hUzm, hUz'm, hUz5m, hUz'5m]
      have hPd : ∀ i, (1 - 9 * D.ε) * T ≤
          Work.EKLC8Core.vol (P i ∩ Set.Icc 0 T) := by
        intro i; fin_cases i <;>
          simp [P, hAzd, hAz'd, hAz5d, hAz'5d, hUzd, hUz'd, hUz5d, hUz'5d]
      obtain ⟨τ, hτIcc, hτall⟩ := Work.EKLC8Core.step8_nonempty hT0 D.ε_pos h72 hPm hPd
      have hτAz : τ ∈ Az := by simpa [P] using hτall 0
      have hτAz' : τ ∈ Az' := by simpa [P] using hτall 1
      have hτAz5 : τ ∈ Az5 := by simpa [P] using hτall 2
      have hτAz'5 : τ ∈ Az'5 := by simpa [P] using hτall 3
      have hτUz : τ ∈ Uz := by simpa [P] using hτall 4
      have hτUz' : τ ∈ Uz' := by simpa [P] using hτall 5
      have hτUz5 : τ ∈ Uz5 := by simpa [P] using hτall 6
      have hτUz'5 : τ ∈ Uz'5 := by simpa [P] using hτall 7
      obtain ⟨hx₂, -⟩ := hAzp τ hτAz
      obtain ⟨hx'₂, -⟩ := hAz'p τ hτAz'
      have hνeq := hνeq_of τ hx₂ hx'₂
      rcases lt_or_ge κa (Real.exp τ * κu) with hlt | hle
      · -- sub-case `κ(x,x') = e^τ κu`
        have hκτ : kappaFlow g τ = Real.exp τ * κu := by
          rw [kappaFlow_eq g τ, ← hκadef, ← hκudef]
          exact max_eq_right (le_of_lt hlt)
        obtain ⟨-, hbad1⟩ := hUzp τ hτUz
        obtain ⟨-, hbad2⟩ := hUz'p τ hτUz'
        obtain ⟨-, hbad3⟩ := hUz5p τ hτUz5
        obtain ⟨-, hbad4⟩ := hUz'5p τ hτUz'5
        have hs1 : Real.exp (-Real.log κu - 1 * τ) = (kappaFlow g τ)⁻¹ := by
          rw [hκτ, one_mul, exp_neg_log_sub κu τ hκu0]
        have hs2 : Real.exp ((-Real.log κu + 5 * |Real.log D.ρ|) - 1 * τ)
            = (D.ρ⁻¹) ^ 5 * (kappaFlow g τ)⁻¹ := by
          rw [hκτ, one_mul, exp_log_shift κu D.ρ τ hκu0 D.ρ_pos hρlt1]
        refine ⟨τ, hτIcc, hx₂, hx'₂, hνeq, ?_, ?_, ?_, ?_⟩
        · rwa [hs1] at hbad1
        · rwa [hs1] at hbad2
        · rwa [hs2] at hbad3
        · rwa [hs2] at hbad4
      · -- sub-case `κ(x,x') = κa`
        have hκu_le : κu ≤ κa := by
          have h2 : 1 ≤ Real.exp τ := Real.one_le_exp hτIcc.1
          nlinarith
        have hκ₀eq : κ₀ = κa := by rw [hκ₀max]; exact max_eq_left hκu_le
        have hκτ : kappaFlow g τ = κa := by
          rw [kappaFlow_eq g τ, ← hκadef, ← hκudef]
          exact max_eq_left hle
        obtain ⟨-, hbad1⟩ := hAzp τ hτAz
        obtain ⟨-, hbad2⟩ := hAz'p τ hτAz'
        obtain ⟨-, hbad3⟩ := hAz5p τ hτAz5
        obtain ⟨-, hbad4⟩ := hAz'5p τ hτAz'5
        have hs1 : Real.exp (4 * T - 0 * τ) = (kappaFlow g τ)⁻¹ := by
          rw [hκτ, zero_mul, sub_zero, hexp4T, hκ₀eq]
        have hs2 : Real.exp (4 * T + 5 * |Real.log D.ρ| - 0 * τ)
            = (D.ρ⁻¹) ^ 5 * (kappaFlow g τ)⁻¹ := by
          rw [hκτ, zero_mul, sub_zero, Real.exp_add, hexp5, hexp4T, hκ₀eq]
          ring
        refine ⟨τ, hτIcc, hx₂, hx'₂, hνeq, ?_, ?_, ?_, ?_⟩
        · rwa [hs1] at hbad1
        · rwa [hs1] at hbad2
        · rwa [hs2] at hbad3
        · rwa [hs2] at hbad4
  -- ## Steps 9–10 at the found time
  obtain ⟨τ, hτIcc, hx₂, hx'₂, hνeq, hbad1, hbad2, hbad3, hbad4⟩ := hkey
  set G : Work.EKLContract.SL3 := Work.EKLComp.phi τ * g * (Work.EKLComp.phi τ)⁻¹ with hGdef
  have hκG : Work.EKLC8Core.kappa ((G : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)
      = kappaFlow g τ := rfl
  have hx'eq : Work.EKLComp.Phi τ z' = G • Work.EKLComp.Phi τ z := by
    have h1 : Work.EKLContract.aPrime 2 s • z = g • z := by rw [← hz'def, hz'eq]
    have hscal : (Work.EKLComp.phi τ * g * (Work.EKLComp.phi τ)⁻¹) * Work.EKLComp.phi τ
        = Work.EKLComp.phi τ * g := by group
    calc Work.EKLComp.Phi τ z' = Work.EKLComp.Phi τ (g • z) := by
          show Work.EKLComp.Phi τ (Work.EKLContract.aPrime 2 s • z) = Work.EKLComp.Phi τ (g • z)
          rw [h1]
      _ = (Work.EKLComp.phi τ * g) • z := by
          show Work.EKLComp.phi τ • (g • z) = (Work.EKLComp.phi τ * g) • z
          rw [mul_smul]
      _ = G • Work.EKLComp.Phi τ z := by
          rw [hGdef]
          show (Work.EKLComp.phi τ * g) • z
            = (Work.EKLComp.phi τ * g * (Work.EKLComp.phi τ)⁻¹) • (Work.EKLComp.phi τ • z)
          rw [← mul_smul, hscal]
  -- the entries of `G = φ_τ g φ_τ⁻¹`
  have hmat : ∀ i j : Fin 3, ((G : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
      = Real.exp ((Work.EKLC8Core.flowExp i - Work.EKLC8Core.flowExp j) * τ)
        * ((g : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j := by
    intro i j
    rw [hGdef]
    exact Work.EKLC8Core.phi_conj_matrix τ g i j
  have hτnonneg : 0 ≤ τ := hτIcc.1
  have hG00 : |((G : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 0 0 - 1| ≤ δ := by
    have h := hgV 0 0
    rw [hmat 0 0] at *
    have hf : Work.EKLC8Core.flowExp 0 - Work.EKLC8Core.flowExp 0 = 0 := by ring
    rw [hf, zero_mul, Real.exp_zero, one_mul] at *
    simpa using le_of_lt h
  have hG11 : |((G : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 1 1 - 1| ≤ δ := by
    have h := hgV 1 1
    rw [hmat 1 1] at *
    have hf : Work.EKLC8Core.flowExp 1 - Work.EKLC8Core.flowExp 1 = 0 := by ring
    rw [hf, zero_mul, Real.exp_zero, one_mul] at *
    simpa using le_of_lt h
  have hG22 : |((G : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 2 2 - 1| ≤ δ := by
    have h := hgV 2 2
    rw [hmat 2 2] at *
    have hf : Work.EKLC8Core.flowExp 2 - Work.EKLC8Core.flowExp 2 = 0 := by ring
    rw [hf, zero_mul, Real.exp_zero, one_mul] at *
    simpa using le_of_lt h
  have hG01 : |((G : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 0 1| ≤ δ := by
    have h := hgV 0 1
    rw [hmat 0 1] at *
    have hf : Work.EKLC8Core.flowExp 0 - Work.EKLC8Core.flowExp 1 = -2 := by
      rw [flowExp_zero, flowExp_one]; norm_num
    rw [hf] at *
    simp only [Matrix.one_apply_ne (by decide : (0 : Fin 3) ≠ 1), sub_zero] at h
    have hexp : Real.exp (-2 * τ) ≤ 1 := by
      calc Real.exp (-2 * τ) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
        _ = 1 := Real.exp_zero
    calc |Real.exp (-2 * τ) * ((g : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 0 1|
        = Real.exp (-2 * τ) *
            |((g : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 0 1| := by
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ 1 * |((g : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 0 1| :=
          mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
      _ = |((g : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 0 1| := one_mul _
      _ ≤ δ := le_of_lt h
  have hG02 : |((G : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 0 2| ≤ δ := by
    have h := hgV 0 2
    rw [hmat 0 2] at *
    have hf : Work.EKLC8Core.flowExp 0 - Work.EKLC8Core.flowExp 2 = -1 := by
      rw [flowExp_zero, flowExp_two]; norm_num
    rw [hf] at *
    simp only [Matrix.one_apply_ne (by decide : (0 : Fin 3) ≠ 2), sub_zero] at h
    have hexp : Real.exp (-1 * τ) ≤ 1 := by
      calc Real.exp (-1 * τ) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
        _ = 1 := Real.exp_zero
    calc |Real.exp (-1 * τ) * ((g : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 0 2|
        = Real.exp (-1 * τ) *
            |((g : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 0 2| := by
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ 1 * |((g : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 0 2| :=
          mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
      _ = |((g : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 0 2| := one_mul _
      _ ≤ δ := le_of_lt h
  have hG21 : |((G : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 2 1| ≤ δ := by
    have h := hgV 2 1
    rw [hmat 2 1] at *
    have hf : Work.EKLC8Core.flowExp 2 - Work.EKLC8Core.flowExp 1 = -1 := by
      rw [flowExp_two, flowExp_one]; norm_num
    rw [hf] at *
    simp only [Matrix.one_apply_ne (by decide : (2 : Fin 3) ≠ 1), sub_zero] at h
    have hexp : Real.exp (-1 * τ) ≤ 1 := by
      calc Real.exp (-1 * τ) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
        _ = 1 := Real.exp_zero
    calc |Real.exp (-1 * τ) * ((g : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 2 1|
        = Real.exp (-1 * τ) *
            |((g : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 2 1| := by
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ 1 * |((g : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 2 1| :=
          mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
      _ = |((g : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 2 1| := one_mul _
      _ ≤ δ := le_of_lt h
  -- `0 < κ(x,x')` and `κ(x,x') ≤ 1`
  have hκ₁ : max κa κu ≤ kappaFlow g τ := by
    rw [kappaFlow_eq g τ, ← hκadef, ← hκudef]
    refine max_le_max_left _ ?_
    have h2 : 1 ≤ Real.exp τ := Real.one_le_exp hτnonneg
    nlinarith
  have hκτ0 : 0 < kappaFlow g τ := by
    have h := hκ₀pos
    rw [hκ₀max] at h
    linarith
  have hκτ_le : kappaFlow g τ ≤ kappaBnd δ := by
    have hb := (Work.EKLC8Core.step8_kappa_bound hκ₀pos hκ₀one hκAnn hκUnn
      (by rw [hκ₀max]; exact le_max_left _ _)
      (by rw [hκ₀max]; exact le_max_right _ _) hτnonneg hτIcc.2 hTdef).1
    rw [kappaFlow_eq g τ, ← hκadef, ← hκudef]
    refine le_trans hb ?_
    exact le_of_lt (Real.rpow_lt_rpow hκ₀nn hκ₀lt (by norm_num))
  have hκτ1 : kappaFlow g τ ≤ 1 := by
    refine le_trans hκτ_le ?_
    have h2 : 2 * δ ^ (1 / 2 : ℝ) ≤ 1 := by linarith
    calc (2 * δ ^ (1 / 2 : ℝ)) ^ (3 / 4 : ℝ) ≤ 1 ^ (3 / 4 : ℝ) := by
          refine Real.rpow_le_rpow ?_ h2 (by norm_num)
          have h3 := Real.rpow_nonneg hδ0.le (1 / 2 : ℝ)
          linarith
      _ = 1 := Real.one_rpow _
  -- Steps 9–10
  obtain ⟨r, y, y', hy, hy', hyx, hy'x, hνyy', hshear, hlow, hu12hi, h10, h12, h20, hd0, hd1, hd2⟩ :=
    step9_10' D hx₂ hx'₂ hx'eq hκG hκτ0 hκτ1 hδ0 (le_of_lt hδρ)
      hG00 hG11 hG22 hG01 hG02 hG21 hνeq hbad1 hbad2 hbad3 hbad4
  set Hm : Matrix (Fin 3) (Fin 3) ℝ :=
    ((Work.EKLC8Core.shear G r : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)
    with hHmdef
  -- the global entry bound
  have hρ5 : 0 ≤ (D.ρ⁻¹) ^ 5 := pow_nonneg (inv_nonneg.mpr D.ρ_pos.le) 5
  have hρ10 : 0 ≤ (D.ρ⁻¹) ^ 10 := pow_nonneg (inv_nonneg.mpr D.ρ_pos.le) 10
  have hBnd1 : (1 : ℝ) ≤ 2 * (D.ρ⁻¹) ^ 10 + (D.ρ⁻¹) ^ 5 + 3 := by linarith
  have hBnd2 : 2 * (D.ρ⁻¹) ^ 10 + 1 ≤ 2 * (D.ρ⁻¹) ^ 10 + (D.ρ⁻¹) ^ 5 + 3 := by linarith
  have hδ1 : δ ≤ 1 := by linarith
  have hBnd3 : δ + (D.ρ⁻¹) ^ 5 * kappaFlow g τ + 1
      ≤ 2 * (D.ρ⁻¹) ^ 10 + (D.ρ⁻¹) ^ 5 + 3 := by
    nlinarith [hρ5, hρ10, hδ1, hκτ1]
  have hglob : ∀ i j : Fin 3, |Hm i j| ≤ 2 * (D.ρ⁻¹) ^ 10 + (D.ρ⁻¹) ^ 5 + 3 := by
    intro i j
    have h01' : |Hm 0 1| ≤ 2 * (D.ρ⁻¹) ^ 10 + 1 :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu12hi
    have h02' : |Hm 0 2| ≤ 2 * (D.ρ⁻¹) ^ 10 + 1 :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu12hi
    have h21' : |Hm 2 1| ≤ 2 * (D.ρ⁻¹) ^ 10 + 1 :=
      le_trans (le_max_right _ _) hu12hi
    have h00' : |Hm 0 0| ≤ 2 * (D.ρ⁻¹) ^ 10 + (D.ρ⁻¹) ^ 5 + 3 := by
      have h : |Hm 0 0| ≤ |Hm 0 0 - 1| + 1 := by
        calc |Hm 0 0| = |(Hm 0 0 - 1) + 1| := by ring_nf
          _ ≤ |Hm 0 0 - 1| + 1 := by simpa using abs_add_le (Hm 0 0 - 1) (1 : ℝ)
      linarith [hd0, hBnd3]
    have h11' : |Hm 1 1| ≤ 2 * (D.ρ⁻¹) ^ 10 + (D.ρ⁻¹) ^ 5 + 3 := by
      have h : |Hm 1 1| ≤ |Hm 1 1 - 1| + 1 := by
        calc |Hm 1 1| = |(Hm 1 1 - 1) + 1| := by ring_nf
          _ ≤ |Hm 1 1 - 1| + 1 := by simpa using abs_add_le (Hm 1 1 - 1) (1 : ℝ)
      linarith [hd1, hBnd3]
    have h22' : |Hm 2 2| ≤ 2 * (D.ρ⁻¹) ^ 10 + (D.ρ⁻¹) ^ 5 + 3 := by
      have h : |Hm 2 2| ≤ |Hm 2 2 - 1| + 1 := by
        calc |Hm 2 2| = |(Hm 2 2 - 1) + 1| := by ring_nf
          _ ≤ |Hm 2 2 - 1| + 1 := by simpa using abs_add_le (Hm 2 2 - 1) (1 : ℝ)
      have hδ1 : δ ≤ 1 := by linarith
      have h5 : 0 ≤ (D.ρ⁻¹) ^ 5 := by positivity
      have h10' : 0 ≤ 2 * (D.ρ⁻¹) ^ 10 := by positivity
      linarith [hd2, hδ1, h5, h10']
    have h10' : |Hm 1 0| ≤ 2 * (D.ρ⁻¹) ^ 10 + (D.ρ⁻¹) ^ 5 + 3 := by
      have hsq : kappaFlow g τ ^ 2 ≤ 1 := by nlinarith [hκτ0, hκτ1]
      linarith [h10, hsq, hBnd1]
    have h12' : |Hm 1 2| ≤ 2 * (D.ρ⁻¹) ^ 10 + (D.ρ⁻¹) ^ 5 + 3 := by
      linarith [h12, hκτ1, hBnd1]
    have h20' : |Hm 2 0| ≤ 2 * (D.ρ⁻¹) ^ 10 + (D.ρ⁻¹) ^ 5 + 3 := by
      linarith [h20, hκτ1, hBnd1]
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;>
      first
        | exact h00' | exact h11' | exact h22'
        | exact (le_trans h01' hBnd2) | exact (le_trans h02' hBnd2)
        | exact (le_trans h21' hBnd2)
        | exact h10' | exact h12' | exact h20'
  -- the small-entry bounds
  have hkbnn : 0 ≤ kappaBnd δ := by
    rw [kappaBnd]; positivity
  have hc1 : δ + (D.ρ⁻¹) ^ 5 * kappaFlow g τ
      ≤ δ + (D.ρ⁻¹) ^ 5 * kappaBnd δ + kappaBnd δ := by
    have h : (D.ρ⁻¹) ^ 5 * kappaFlow g τ ≤ (D.ρ⁻¹) ^ 5 * kappaBnd δ :=
      mul_le_mul_of_nonneg_left hκτ_le hρ5
    linarith
  have hc2 : kappaFlow g τ ≤ δ + (D.ρ⁻¹) ^ 5 * kappaBnd δ + kappaBnd δ := by
    have h5 : 0 ≤ (D.ρ⁻¹) ^ 5 * kappaBnd δ := mul_nonneg hρ5 hkbnn
    linarith [hkbnn, hκτ_le, h5]
  have hc3 : δ ≤ δ + (D.ρ⁻¹) ^ 5 * kappaBnd δ + kappaBnd δ := by
    have h5 : 0 ≤ (D.ρ⁻¹) ^ 5 * kappaBnd δ := mul_nonneg hρ5 hkbnn
    linarith [h5, hkbnn]
  refine ⟨y, y', Work.EKLC8Core.shear G r, hy, hy', hshear, hνyy', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hHmdef]; exact hglob
  · rw [← hHmdef, cBnd]; exact le_trans hd0 hc1
  · rw [← hHmdef, cBnd]; exact le_trans hd1 hc1
  · rw [← hHmdef, cBnd]; exact le_trans hd2 hc3
  · rw [← hHmdef, cBnd]
    refine le_trans h10 (le_trans ?_ hc2)
    nlinarith [hκτ0, hκτ1]
  · rw [← hHmdef, cBnd]; exact le_trans h12 hc2
  · rw [← hHmdef, cBnd]; exact le_trans h20 hc2
  · rw [← hHmdef]; exact hlow

/-! ## The limit `δ → 0` (Step 11) -/

theorem limit_pair [PolishSpace Work.EKLContract.X3]
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    (D : Work.EKLComp.C8Setup μ)
    (hNE : Work.EKLContract.NonExceptional μ Work.EKLComp.h01 2) :
    ∃ (y y' : Work.EKLContract.X3) (h : Work.EKLContract.SL3),
      y ∈ D.X₁ ∧ y' ∈ D.X₁ ∧
      h ∈ (Work.EKLContract.Upar Work.EKLComp.h01 Work.EKLComp.h02 Work.EKLComp.h21 :
        Set Work.EKLContract.SL3) ∧
      h ≠ 1 ∧ y' = h • y ∧ D.ν y = D.ν y' := by
  -- the threshold `δ₀` of Step 5
  obtain ⟨δ₀, hδ₀0, hδ₀16, hδ₀40, hδ₀ρ⟩ :
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 16 ∧ δ₀ < D.ρ ^ 40 / 4 ∧ δ₀ < D.ρ ^ 4 / 4 := by
    have h40 : 0 < D.ρ ^ 40 := pow_pos D.ρ_pos 40
    have h44 : 0 < D.ρ ^ 4 := pow_pos D.ρ_pos 4
    have h40' : 0 < D.ρ ^ 40 / 8 := by linarith
    have h44' : 0 < D.ρ ^ 4 / 8 := by linarith
    refine ⟨min (1 / 32) (min (D.ρ ^ 40 / 8) (D.ρ ^ 4 / 8)), ?_, ?_, ?_, ?_⟩
    · exact lt_min (by norm_num) (lt_min h40' h44')
    · exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    · have h := min_le_right (1 / 32 : ℝ) (min (D.ρ ^ 40 / 8) (D.ρ ^ 4 / 8))
      have h' := min_le_left (D.ρ ^ 40 / 8) (D.ρ ^ 4 / 8)
      linarith
    · have h := min_le_right (1 / 32 : ℝ) (min (D.ρ ^ 40 / 8) (D.ρ ^ 4 / 8))
      have h' := min_le_right (D.ρ ^ 40 / 8) (D.ρ ^ 4 / 8)
      linarith
  set δseq : ℕ → ℝ := fun n => δ₀ / ((n : ℝ) + 2) with hδseqdef
  have hδseq_lt : ∀ n, δseq n < δ₀ := by
    intro n
    have h2 : (1 : ℝ) < (n : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    rw [hδseqdef]
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) + 2)]
    nlinarith [hδ₀0, h2]
  have hδseq_pos : ∀ n, 0 < δseq n := by
    intro n
    rw [hδseqdef]
    have : (0 : ℝ) < (n : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    positivity
  have hchoose : ∀ n : ℕ, ∃ (y y' : Work.EKLContract.X3) (H : Work.EKLContract.SL3),
      y ∈ D.X₁ ∧ y' ∈ D.X₁ ∧ y' = H • y ∧ D.ν y = D.ν y' ∧
      (∀ i j, |((H : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤
          2 * (D.ρ⁻¹) ^ 10 + (D.ρ⁻¹) ^ 5 + 3) ∧
      |((H : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 0 0 - 1| ≤ cBnd D.ρ (δseq n) ∧
      |((H : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 1 1 - 1| ≤ cBnd D.ρ (δseq n) ∧
      |((H : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 2 2 - 1| ≤ cBnd D.ρ (δseq n) ∧
      |((H : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 1 0| ≤ cBnd D.ρ (δseq n) ∧
      |((H : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 1 2| ≤ cBnd D.ρ (δseq n) ∧
      |((H : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) 2 0| ≤ cBnd D.ρ (δseq n) ∧
      D.ρ ^ 2 / 2 ≤ Work.EKLC8Core.u12max
        ((H : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) := by
    intro n
    exact exists_pair_of_delta D hNE (hδseq_pos n) (by linarith [hδseq_lt n, hδ₀16])
      (by linarith [hδseq_lt n, hδ₀40]) (by linarith [hδseq_lt n, hδ₀ρ])
  choose ys ys' Hs hys hys' hsmul heq hB h00 h11 h22 h10 h12 h20 hlow using hchoose
  -- the uniform error sequence
  have hδtend : Tendsto δseq atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => δ₀ / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) := by
        refine tendsto_inv_atTop_zero.comp ?_
        have h3 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
        exact h3.atTop_add tendsto_const_nhds
      simpa [div_eq_mul_inv] using tendsto_const_nhds.mul h2
    exact h1.congr (fun n => by rw [hδseqdef])
  have hc : Tendsto (fun n => cBnd D.ρ (δseq n)) atTop (𝓝 0) := by
    have hkb : Tendsto (fun n => kappaBnd (δseq n)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => δseq n ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
        Filter.Tendsto.rpow_const_nhds_zero hδtend (by norm_num)
      have h2 : Tendsto (fun n => 2 * δseq n ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
        simpa using tendsto_const_nhds.mul h1
      have h3 : Tendsto (fun n => (2 * δseq n ^ (1 / 2 : ℝ)) ^ (3 / 4 : ℝ)) atTop (𝓝 0) :=
        Filter.Tendsto.rpow_const_nhds_zero h2 (by norm_num)
      exact h3.congr (fun n => by rw [kappaBnd])
    have h4 : Tendsto (fun n => (D.ρ⁻¹) ^ 5 * kappaBnd (δseq n) + kappaBnd (δseq n))
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hkb).add hkb
    have h6 : Tendsto (fun n =>
        δseq n + ((D.ρ⁻¹) ^ 5 * kappaBnd (δseq n) + kappaBnd (δseq n))) atTop (𝓝 0) := by
      simpa using hδtend.add h4
    have h5 : Tendsto (fun n =>
        δseq n + D.ρ⁻¹ ^ 5 * kappaBnd (δseq n) + kappaBnd (δseq n)) atTop (𝓝 0) :=
      h6.congr (fun n => by ring)
    exact h5.congr (fun n => by rw [cBnd])
  have hc0 : ∀ n, 0 ≤ cBnd D.ρ (δseq n) := by
    intro n
    rw [cBnd]
    have hn : 0 < δseq n := hδseq_pos n
    have h1 : 0 ≤ (D.ρ⁻¹) ^ 5 := pow_nonneg (inv_nonneg.mpr D.ρ_pos.le) 5
    have h2 : 0 ≤ kappaBnd (δseq n) := by
      rw [kappaBnd]
      refine Real.rpow_nonneg ?_ _
      have h3 := Real.rpow_nonneg hn.le (1 / 2 : ℝ)
      linarith
    have h4 : 0 ≤ (D.ρ⁻¹) ^ 5 * kappaBnd (δseq n) := mul_nonneg h1 h2
    linarith
  exact limit_step D D.ρ_pos hys hys' heq hsmul hc hc0 hB h00 h11 h22 h10 h12 h20 hlow

end Work.EKLCompSetup
