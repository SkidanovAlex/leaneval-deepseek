import Mathlib
import Submission.Work.EKLComp.C8Defs
import Submission.Work.EKLC8Core.All

/-!
# Step 7 (EKL Lemma 4.5) at a single point `w ∈ X₃`

EKL Lemma 4.5, in the *set-valued* form needed by the later assembly: from the two
flow-density hypotheses `X₃_avg₁`, `X₃_avg₂` of the `C8Setup` at the point `w` we produce a
measurable set `P ⊆ [0,T]` of density `≥ (1-9ε)T` such that **every** `τ ∈ P` satisfies

* `Φ_τ w ∈ X₂` (the maximal-inequality set), and
* `BadAt (ν^ℝ_{Φ_τ w}) ρ (e^{θ-ητ})`, i.e. `ν([-ρS,ρS]) < ½ ν([-S,S])` with `S = e^{θ-ητ}`
  (EKL (e:introduceS)).

The set `P` is the set of times `τ ∈ [0,T]` with `Φ_τ w ∈ X₂` and `Φ_{v(τ)} w ∈ 𝒳(ρ)`,
`v(τ) = (θ + (2-η)τ)/2`; its density `≥ (1-9ε)T` is `step7_measure`.  The pointwise statement
is the scaling transfer of `step7_transfer_nopos`: the intermediate time `(θ-ητ)/2 ≥ 0` has
`τ + (θ-ητ)/2 = v(τ)`, so `y := Φ_{(θ-ητ)/2} (Φ_τ w) = Φ_{v(τ)} w ∈ 𝒳(ρ)` (flow law
`phi_add`), `Φ_τ w ∈ X₂ ⊆ X''` and `y ∈ 𝒳(ρ) ⊆ X''` put both points in the domain of the
covariance clause `D.scale` of (U7), and `nuR` transfers the badness from `y` to `Φ_τ w` at
scale `S = e^{θ-ητ} = e^{2(θ-ητ)/2}` (arithmetic of `step7_arith`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal Matrix

noncomputable section

namespace Work.EKLCompSetup

/-! ## Auxiliary lemmas -/

/-- `t ↦ aDiag t` is continuous (entrywise continuity of the diagonal matrix). -/
theorem continuous_aDiag' : Continuous fun t : Fin 3 → ℝ => Work.EKLC8Core.aDiag t := by
  refine Continuous.subtype_mk (p := fun M : Matrix (Fin 3) (Fin 3) ℝ => M.det = 1)
    (f := fun t : Fin 3 → ℝ => Matrix.diagonal (fun i => Real.exp (t i - (∑ j, t j) / 3)))
    ?_ (fun t => (Work.EKLC8Core.aDiag t).2)
  apply continuous_matrix
  intro k l
  simp only [Matrix.diagonal_apply]
  by_cases hkl : k = l
  · simp only [hkl, if_true]
    fun_prop
  · simp only [hkl, if_false]
    exact continuous_const

/-- The contracting flow `τ ↦ φ_τ = diag(e^{-τ},e^{τ},1)` is continuous. -/
theorem continuous_phi' : Continuous fun τ : ℝ => Work.EKLComp.phi τ := by
  have hkey : (fun τ : ℝ => Work.EKLComp.phi τ)
      = fun τ => Work.EKLC8Core.aDiag (τ • Work.EKLC8Core.flowExp) := rfl
  rw [hkey]
  exact continuous_aDiag'.comp (by fun_prop)

/-- The orbit `τ ↦ Φ_τ x = φ_τ • x` of the flow through a fixed point is continuous. -/
theorem continuous_Phi (x : Work.EKLContract.X3) :
    Continuous fun τ : ℝ => Work.EKLComp.Phi τ x := by
  have h2 : Continuous fun τ : ℝ => Work.EKLComp.phi τ • x :=
    continuous_smul.comp (continuous_phi'.prodMk continuous_const)
  simpa [Work.EKLComp.Phi] using h2

/-- The flow law for `Phi`, in the form needed for the Step 7 arithmetic. -/
theorem Phi_add (a b : ℝ) (x : Work.EKLContract.X3) :
    Work.EKLComp.Phi a (Work.EKLComp.Phi b x) = Work.EKLComp.Phi (a + b) x := by
  have hphi : Work.EKLComp.phi (a + b) = Work.EKLComp.phi a * Work.EKLComp.phi b :=
    Work.EKLC8Core.phi_add a b
  show Work.EKLComp.phi a • (Work.EKLComp.phi b • x) = Work.EKLComp.phi (a + b) • x
  rw [← mul_smul, hphi]

/-- The time integral of the indicator of a preimage `{τ | f τ ∈ S}` over `[a,b]` is the
Lebesgue measure of `{τ | f τ ∈ S} ∩ (a,b]`.  This is the bridge between the "flow average"
hypotheses of the `C8Setup` (`∫ τ in 0..T, 1_S (Φ_τ x)`) and the density bookkeeping of
`step7_measure` (`vol ({τ | Φ_τ x ∈ S} ∩ [0,T])`). -/
theorem integral_indicator_comp_eq_vol {Ω : Type*} [MeasurableSpace Ω]
    {S : Set Ω} (hS : MeasurableSet S) {f : ℝ → Ω} (hf : Measurable f) {a b : ℝ}
    (hab : a ≤ b) :
    (∫ τ in a..b, Set.indicator S (fun _ => (1 : ℝ)) (f τ))
      = volume.real ({τ : ℝ | f τ ∈ S} ∩ Set.Ioc a b) := by
  set S' : Set ℝ := {τ : ℝ | f τ ∈ S} with hS'def
  have hS'm : MeasurableSet S' := by
    rw [hS'def]
    exact hS.preimage hf
  -- on `(a,b]` the integrand is the indicator of `S' ∩ (a,b]`
  have hpt : (Set.Ioc a b).indicator (fun τ : ℝ => Set.indicator S (fun _ => (1 : ℝ)) (f τ))
      = (S' ∩ Set.Ioc a b).indicator (fun _ => (1 : ℝ)) := by
    funext τ
    by_cases h2 : τ ∈ Set.Ioc a b
    · rw [Set.indicator_of_mem h2]
      by_cases h1 : f τ ∈ S
      · rw [Set.indicator_of_mem h1,
            Set.indicator_of_mem (show τ ∈ S' ∩ Set.Ioc a b from ⟨h1, h2⟩)]
      · rw [Set.indicator_of_notMem h1,
            Set.indicator_of_notMem (fun h : τ ∈ S' ∩ Set.Ioc a b => h1 h.1)]
    · rw [Set.indicator_of_notMem h2,
          Set.indicator_of_notMem (fun h : τ ∈ S' ∩ Set.Ioc a b => h2 h.2)]
  rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_indicator measurableSet_Ioc,
    hpt]
  exact MeasureTheory.integral_indicator_one (hS'm.inter measurableSet_Ioc)

/-- A lower bound for an interval integral of an indicator gives the same lower bound for the
`vol` of the corresponding set of times (the integral is the `vol` of the *half-open*
intersection, which is contained in the closed one). -/
theorem vol_ge_of_integral_indicator {Ω : Type*} [MeasurableSpace Ω]
    {S : Set Ω} (hS : MeasurableSet S) {f : ℝ → Ω} (hf : Measurable f)
    {a b c : ℝ} (hab : a ≤ b)
    (h : c ≤ ∫ τ in a..b, Set.indicator S (fun _ => (1 : ℝ)) (f τ)) :
    c ≤ Work.EKLC8Core.vol ({τ : ℝ | f τ ∈ S} ∩ Set.Icc a b) := by
  set S' : Set ℝ := {τ : ℝ | f τ ∈ S} with hS'def
  have hEq : (∫ τ in a..b, Set.indicator S (fun _ => (1 : ℝ)) (f τ))
      = volume.real (S' ∩ Set.Ioc a b) := integral_indicator_comp_eq_vol hS hf hab
  rw [hEq] at h
  have hsub : S' ∩ Set.Ioc a b ⊆ S' ∩ Set.Icc a b :=
    Set.inter_subset_inter_right _ (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  have hmono : volume.real (S' ∩ Set.Ioc a b) ≤ volume.real (S' ∩ Set.Icc a b) :=
    measureReal_mono hsub
      (Work.EKLC8Core.volume_ne_top_of_subset_Icc (Set.inter_subset_right))
  have hvol : Work.EKLC8Core.vol (S' ∩ Set.Icc a b) = volume.real (S' ∩ Set.Icc a b) := rfl
  rw [hvol]
  linarith [h, hmono]

/-! ## Step 7 -/

theorem step7_set
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    (D : Work.EKLComp.C8Setup μ) (w : Work.EKLContract.X3) (hw : w ∈ D.X₃)
    {T θ η : ℝ} (hT : 0 < T) (hθ : 4 * T ≤ θ) (hθ' : θ ≤ 6 * T)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    ∃ P : Set ℝ, MeasurableSet P ∧ (1 - 9 * D.ε) * T ≤ Work.EKLC8Core.vol (P ∩ Set.Icc 0 T) ∧
      ∀ τ ∈ P, Work.EKLComp.Phi τ w ∈ D.X₂ ∧
        Work.EKLC8Core.BadAt (Work.EKLComp.nuR (D.ν (Work.EKLComp.Phi τ w))) D.ρ
          (Real.exp (θ - η * τ)) := by
  -- The two density sets of Step 7.
  set Q₁ : Set ℝ := {τ : ℝ | Work.EKLComp.Phi τ w ∈ D.X₂} with hQ₁def
  set Q₂ : Set ℝ := {v : ℝ | Work.EKLComp.Phi v w ∈ D.Xrho} with hQ₂def
  have hΦm : Measurable fun τ : ℝ => Work.EKLComp.Phi τ w := (continuous_Phi w).measurable
  have hQ₁m : MeasurableSet Q₁ := D.X₂_meas_set.preimage hΦm
  have hQ₂m : MeasurableSet Q₂ := D.Xrho_meas_set.preimage hΦm
  -- Their densities, from the flow-averaging clause of `C8Setup` at `w ∈ X₃`.
  have hvol₁ : (1 - D.ε) * T ≤ Work.EKLC8Core.vol (Q₁ ∩ Set.Icc 0 T) :=
    vol_ge_of_integral_indicator D.X₂_meas_set hΦm hT.le (D.X₃_avg₁ w hw T hT)
  have hvol₂ : (1 - D.ε) * (4 * T) ≤ Work.EKLC8Core.vol (Q₂ ∩ Set.Icc 0 (4 * T)) :=
    vol_ge_of_integral_indicator D.Xrho_meas_set hΦm (by linarith)
      (D.X₃_avg₂ w hw (4 * T) (by linarith))
  refine ⟨{τ : ℝ | τ ∈ Q₁ ∧ (θ + (2 - η) * τ) / 2 ∈ Q₂} ∩ Set.Icc 0 T, ?_, ?_, ?_⟩
  · exact (hQ₁m.inter (hQ₂m.preimage (by fun_prop))).inter measurableSet_Icc
  · have h0 := Work.EKLC8Core.step7_measure (Q₁ := Q₁) (Q₂ := Q₂) hT hθ hθ'
      D.ε_pos D.ε_small hη0 hη1 hQ₁m hQ₂m hvol₁ hvol₂
    simpa only [Set.inter_assoc, Set.inter_self] using h0
  · intro τ hτ
    obtain ⟨hτA, hτIcc⟩ := hτ
    have hX₂ : Work.EKLComp.Phi τ w ∈ D.X₂ := hτA.1
    have hXrho : Work.EKLComp.Phi ((θ + (2 - η) * τ) / 2) w ∈ D.Xrho := hτA.2
    have hτ0 : 0 ≤ τ := hτIcc.1
    have hτ1 : τ ≤ T := hτIcc.2
    -- Arithmetic of the intermediate time `(θ - ητ)/2`.
    obtain ⟨hw0, hsum, hexp, -⟩ := Work.EKLC8Core.step7_arith hT hθ hθ' hτ0 hτ1 hη0 hη1
    refine ⟨hX₂, ?_⟩
    -- Membership in the conull covariance set `X''`.
    have hx'' : Work.EKLComp.Phi τ w ∈ D.X'' := (D.X₂_def _).mp hX₂ |>.1
    have hpoint : Work.EKLComp.Phi ((θ - η * τ) / 2) (Work.EKLComp.Phi τ w)
        = Work.EKLComp.Phi ((θ + (2 - η) * τ) / 2) w := by
      rw [Phi_add]
      congr 1
      linarith [hsum]
    have hy'' : Work.EKLComp.Phi ((θ - η * τ) / 2) (Work.EKLComp.Phi τ w) ∈ D.X'' := by
      rw [hpoint]
      exact (D.Xrho_def _).mp hXrho |>.1
    -- The (F1) scaling relation at `x = Φ_τ w` and `φ_{(θ-ητ)/2} x`, i.e. the covariance
    -- clause (U7) at the time `(θ-ητ)/2`, rewritten with `e^{2·(θ-ητ)/2} = e^{θ-ητ}`.
    have hscale : ∀ σ : ℝ,
        (Work.EKLComp.nuR (D.ν (Work.EKLComp.Phi ((θ - η * τ) / 2)
            (Work.EKLComp.Phi τ w)))).real (Set.Icc (-σ) σ)
          * (Work.EKLComp.nuR (D.ν (Work.EKLComp.Phi τ w))).real
              (Set.Icc (-(Real.exp (θ - η * τ))) (Real.exp (θ - η * τ)))
        = (Work.EKLComp.nuR (D.ν (Work.EKLComp.Phi τ w))).real
              (Set.Icc (-(σ * Real.exp (θ - η * τ))) (σ * Real.exp (θ - η * τ)))
          * (Work.EKLComp.nuR (D.ν (Work.EKLComp.Phi ((θ - η * τ) / 2)
              (Work.EKLComp.Phi τ w)))).real (Set.Icc (-1) 1) := by
      intro σ
      have h := D.scale (Work.EKLComp.Phi τ w) hx'' ((θ - η * τ) / 2) σ hy''
      rw [hexp] at h
      exact h
    -- `S = e^{θ-ητ} ≥ 1`.
    have hS1 : 1 ≤ Real.exp (θ - η * τ) := Real.one_le_exp (by linarith)
    -- Finiteness of `ν[-S,S]` (the plaque `ballU` is compact).
    have hfin : Work.EKLComp.nuR (D.ν (Work.EKLComp.Phi τ w))
        (Set.Icc (-(Real.exp (θ - η * τ))) (Real.exp (θ - η * τ))) ≠ ⊤ := by
      rw [Work.EKLComp.nuR_Icc]
      exact ((D.radon (Work.EKLComp.Phi τ w)).lt_top_of_isCompact
        (Work.EKLComp.isCompact_ballU _)).ne
    -- Badness of the intermediate point, from `Φ_{v(τ)} w ∈ 𝒳(ρ)`.
    have hbad1 : Work.EKLC8Core.BadAt (Work.EKLComp.nuR
        (D.ν (Work.EKLComp.Phi ((θ - η * τ) / 2) (Work.EKLComp.Phi τ w)))) D.ρ 1 := by
      rw [hpoint]
      have h := (D.Xrho_def _).mp hXrho
      rw [Work.EKLC8Core.BadAt, D.norm]
      simp only [mul_one]
      exact h.2
    exact Work.EKLC8Core.step7_transfer_nopos
      (ν₀ := Work.EKLComp.nuR (D.ν (Work.EKLComp.Phi τ w)))
      (ν₁ := Work.EKLComp.nuR (D.ν (Work.EKLComp.Phi ((θ - η * τ) / 2)
        (Work.EKLComp.Phi τ w))))
      (ρ := D.ρ) (S := Real.exp (θ - η * τ)) hS1 (D.norm _) (D.norm _) hfin hscale hbad1

end Work.EKLCompSetup
