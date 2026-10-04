import Mathlib
import Submission.Work.Diff.STE.Lead.jetTower_jointContinuous
import Submission.Work.Diff.STE.B3.mat_jet_bound_of_energy

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The homogeneous jet bound for the B3 chart matrices

`Work.Diff.STE.B3.mat_jet_bound_of_energy` bounds the `m`-th flat jet of the chart matrix
`D.mat i h c d` of a section `h` with smooth chart data by `C (1 + √(D.ENormB k₀ h))`, uniformly in
`h` and in the point `z` of the `2σ i`-ball.  The additive constant `1` is spurious: the jet tower
`h ↦ ∂^β (D.mat i h c d)` is *linear* in the section, while `ENormB k₀` is *homogeneous of degree
`2`*, so applying the bound to `r • h` and letting `r → ∞` removes it.

This file supplies the two homogeneity inputs (`ChartData_smul`/`pdVec_ofReal_const_mul` for the
linearity of the tower, `ENormB_smul_local` for the degree-`2` homogeneity of the energy, both
established here for a general section, in contrast with the version
`Work.Diff.STE.Lead.matJet_energy_hom` where the energy homogeneity is an explicit hypothesis) and
then performs the rescaling argument.  The result

  `‖∂^β (D.mat i h c d) z‖ ≤ C √(D.ENormB k₀ h)`

is the form consumed by the joint-continuity argument of
`Submission/Work/Diff/STE/Lead/jetTower_jointContinuous.lean` (see its private
`matJet_energy_hom_local`), made public here.
-/

namespace Work.Diff.STE.Lead.GfJoint

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## Scaling of the B3 vocabulary -/

/-- The chart-smoothness hypothesis is stable under multiplication of the section by a constant. -/
private lemma ChartData_smul (r : ℝ) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) :
    Work.Diff.STE.D.ChartData (I := I) (M := M) (r • h) := by
  intro x₀
  have h1 := hh x₀
  refine (ContDiffOn.const_smul r h1).congr ?_
  intro y hy
  rfl

/-- The chart matrix is homogeneous in the section. -/
private lemma mat_smul (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) (r : ℝ)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E))
    (z : Fin (Module.finrank ℝ E) → ℝ) :
    D.mat i (r • h) a b z = r * D.mat i h a b z := rfl

/-- The localised component is homogeneous in the section (pointwise). -/
private lemma R_smul_local (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) (r : ℝ)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)) :
    D.R i (r • h) a b = r • D.R i h a b := by
  funext z
  simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat, Pi.smul_apply, smul_apply,
    smul_eq_mul]
  ring

/-- The periodised localised component is homogeneous in the section. -/
private lemma Rper_smul_local (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (r : ℝ) (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)) :
    D.Rper i (r • h) a b = r • D.Rper i h a b := by
  funext z
  simp only [Work.Diff.STE.B3Data.Rper]
  have hpt : ∀ m : Fin (Module.finrank ℝ E) → ℤ,
      ((D.R i (r • h) a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ)
        = (r : ℂ) * ((D.R i h a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ) := by
    intro m
    rw [R_smul_local, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  rw [tsum_congr hpt, tsum_mul_left]
  rfl

/-- `pdVec` is homogeneous in the function, for globally smooth complex-valued functions. -/
private lemma pdVec_smul_local {n k : ℕ} (l : Fin k → Fin n) (a : ℂ) {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Work.Diff.STE.pdVec k l (a • f) = a • Work.Diff.STE.pdVec k l f := by
  funext x
  rw [Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv k (a • f) (hf.const_smul a) x l]
  simp only [Pi.smul_apply]
  rw [Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv k f hf x l]
  rw [iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (a := a)
    (hf.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))]
  simp only [smul_apply, smul_eq_mul]

/-- The physical `Hᵏ` energy `ENormSq` is homogeneous of degree `2`. -/
private lemma ENormSq_smul_local {n k : ℕ} (a : ℂ) {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Work.Diff.STE.ENormSq k (a • f) = ‖a‖ ^ 2 * Work.Diff.STE.ENormSq k f := by
  have key : ∀ (l : Fin k → Fin n),
      Work.Diff.STE.pdVec k l (a • f) = a • Work.Diff.STE.pdVec k l f := fun l =>
    pdVec_smul_local l a hf
  simp only [Work.Diff.STE.ENormSq]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [key l]
  have h2 : ∀ x, ‖(a • Work.Diff.STE.pdVec k l f) x‖ ^ 2
      = ‖a‖ ^ 2 * ‖Work.Diff.STE.pdVec k l f x‖ ^ 2 := by
    intro x
    rw [Pi.smul_apply, norm_smul, mul_pow]
  simp only [h2]
  exact MeasureTheory.integral_const_mul _ _

/-- The composite physical energy `ENormB` is homogeneous of degree `2` in the section. -/
private theorem ENormB_smul_local (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (r : ℝ) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) :
    D.ENormB k (r • h) = r ^ 2 * D.ENormB k h := by
  have hsm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i h a b) := fun i a b =>
    (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i h a b
      (Work.Diff.STE.B3.R_contDiff_of_chartData D h hh i a b)).1
  have hnorm : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
  have hsmul_eq : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      D.Rper i (r • h) a b = (((r : ℝ) : ℂ)) • D.Rper i h a b := by
    intro i a b
    rw [Rper_smul_local]
    funext z
    rw [Pi.smul_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  simp only [Work.Diff.STE.B3Data.ENormB]
  calc ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Work.Diff.STE.ENormSq k (D.Rper i (r • h) a b)
      = ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Work.Diff.STE.ENormSq k (((r : ℝ) : ℂ) • D.Rper i h a b) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        rw [hsmul_eq i a b]
    _ = ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ‖((r : ℝ) : ℂ)‖ ^ 2 * Work.Diff.STE.ENormSq k (D.Rper i h a b) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        rw [ENormSq_smul_local _ (hsm i a b)]
    _ = ‖((r : ℝ) : ℂ)‖ ^ 2 * ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E), Work.Diff.STE.ENormSq k (D.Rper i h a b) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
    _ = r ^ 2 * D.ENormB k h := by rw [hnorm]; rfl

/-! ## Linearity of the jet tower in the section -/

/-- The `m`-th jet of a constant multiple of a real-valued function. -/
private lemma pdVec_ofReal_const_mul {n m : ℕ} (f : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) (r : ℝ)
    (β : Fin m → Fin n) (hf : ContDiffAt ℝ (⊤ : ℕ∞) f z) :
    Work.Diff.STE.pdVec m β (fun y => (((r * f y : ℝ)) : ℂ)) z
      = (r : ℂ) * Work.Diff.STE.pdVec m β (fun y => ((f y : ℝ) : ℂ)) z := by
  have hf2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => r * f y) z :=
    (contDiffAt_const (c := r)).mul hf
  have h4 : (fun y => r * f y) = r • f := by funext y; rw [Pi.smul_apply, smul_eq_mul]
  have h3 : iteratedFDeriv ℝ m (fun y => r * f y) z = r • iteratedFDeriv ℝ m f z := by
    rw [h4]
    exact iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (a := r)
      (hf.of_le (WithTop.coe_le_coe.mpr le_top))
  rw [Work.Diff.STE.B3.pdVec_ofReal_eq hf2 m β,
    Work.Diff.STE.B3.pdVec_ofReal_eq hf m β, h3]
  simp only [smul_apply, smul_eq_mul, Complex.ofReal_mul]

end Helpers

/-- **The jet bound for the B3 chart matrices, homogeneous in the physical energy.**  For the Layer
B3 data `D` and `2 m + n < 2 k₀` (`n = finrank ℝ E`), the `m`-th flat jet of the chart matrix
`D.mat i h c d` of a section `h` with smooth chart data is bounded by `C √(D.ENormB k₀ h)`,
uniformly in the section `h` and in the point `z` of the `2σ i`-ball.

(`mat_jet_bound_of_energy` gives `C (1 + √(D.ENormB k₀ h))`; applying it to `r • h`, dividing by
`r` and letting `r → ∞` removes the additive constant, because the jet tower is linear and the
energy is homogeneous of degree `2` in the section.) -/
theorem matJet_hom
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k₀ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hs : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
      (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (m : ℕ)
      (hm : 2 * m + Module.finrank ℝ E < 2 * k₀)
      (β : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ 2 * D.σ i →
      ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ C * Real.sqrt (D.ENormB k₀ h) := by
  classical
  obtain ⟨C, hC, hCb⟩ := Work.Diff.STE.B3.mat_jet_bound_of_energy (I := I) (M := M) D k₀
  have key : ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (_hs : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
      (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (m : ℕ)
      (_hm : 2 * m + Module.finrank ℝ E < 2 * k₀)
      (β : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ)
      (_hz : ‖z‖ ≤ 2 * D.σ i),
      ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ C * Real.sqrt (D.ENormB k₀ h) := by
    intro h hh i c d m hm β z hz
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hstep : ∀ r : ℝ, 0 < r →
        ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((D.mat i h c d y : ℝ) : ℂ)) z‖
          ≤ C / r + C * Real.sqrt (D.ENormB k₀ h) := by
      intro r hr
      have hsmr : Work.Diff.STE.D.ChartData (I := I) (M := M) (r • h) := ChartData_smul r h hh
      have hmat : (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((D.mat i (r • h) c d y : ℝ) : ℂ))
          = fun y : Fin (Module.finrank ℝ E) → ℝ => ((r * D.mat i h c d y : ℝ) : ℂ) := by
        funext y
        rw [mat_smul]
      have hlin : Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((D.mat i (r • h) c d y : ℝ) : ℂ)) z
          = (r : ℂ) * Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((D.mat i h c d y : ℝ) : ℂ)) z := by
        rw [hmat]
        exact pdVec_ofReal_const_mul (f := D.mat i h c d) z r β
          (Work.Diff.STE.B3.mat_contDiffAt_of_chartData D h hh i c d z (D.htarget i z hz))
      have hbound := hCb (r • h) hsmr i c d m hm β z hz
      have hnr : ‖((r : ℝ) : ℂ)‖ = |r| := by simpa using Complex.ofRealLI.norm_map r
      rw [hlin, norm_mul, hnr, abs_of_pos hr] at hbound
      have hE : Real.sqrt (D.ENormB k₀ (r • h)) = r * Real.sqrt (D.ENormB k₀ h) := by
        rw [ENormB_smul_local D k₀ r h hh, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]
      rw [hE] at hbound
      have h5 : ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((D.mat i h c d y : ℝ) : ℂ)) z‖
          ≤ (C * (1 + r * Real.sqrt (D.ENormB k₀ h))) / r :=
        (le_div_iff₀ hr).mpr (by linarith [hbound])
      calc ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((D.mat i h c d y : ℝ) : ℂ)) z‖
          ≤ (C * (1 + r * Real.sqrt (D.ENormB k₀ h))) / r := h5
        _ = C / r + C * Real.sqrt (D.ENormB k₀ h) := by
            field_simp
    obtain ⟨r, hrpos, hrlt⟩ : ∃ r : ℝ, 0 < r ∧ C / r < ε := by
      rcases eq_or_lt_of_le hC with hC0 | hCpos
      · exact ⟨1, one_pos, by rw [← hC0]; simpa using hε⟩
      · refine ⟨C / ε + 1, by positivity, ?_⟩
        have h1 : ε * (C / ε) = C := by
          rw [mul_comm, div_mul_cancel₀ _ hε.ne']
        rw [div_lt_iff₀ (by positivity)]
        have h2 : ε * (C / ε + 1) = C + ε := by rw [mul_add, h1, mul_one]
        rw [h2]
        linarith
    have h := hstep r hrpos
    linarith
  exact ⟨C, hC, fun h hh => key h hh⟩

end Work.Diff.STE.Lead.GfJoint
