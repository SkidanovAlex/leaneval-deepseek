import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.B3.mat_jet_bound_of_energy
import Submission.Work.Diff.STE.B3.BNorm_ENormB_equiv
import Submission.Work.Diff.STE.Lead.mat_jet_uniform_bound
import Submission.Work.Diff.STE.Lead.CoeffRepr

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Joint continuity of the B3 jet tower

Let `D` be the Layer B3 data, `U : ℝ → Bil` a family of sections whose localised chart matrices
are smooth (`ChartData`) with a uniform Fourier-side bound `D.BNorm k (U t) ≤ B k`, and assume
moreover that at every `t ∈ Ico 0 τ` the *difference* sections converge to `0` in every `D.BNorm k`
(`hcont`).  Then for every chart `i`, matrix entry `(c,d)` and multi-index `β` of length `m`, the
jet tower

  `(t, z) ↦ ∂^β (D.mat i (U t) c d) z`

is continuous on `Ico 0 τ × {z | ‖z‖ ≤ D.σ i}`.

The mathematical content is that the `m`-th jet of the chart matrix is *homogeneous* of degree `1`
in the section, with a bound in terms of the physical `Hᵏ` energy `D.ENormB k`, and that the
physical energy is controlled by the Fourier-side norm `D.BNorm k`.  The already proved
`Work.Diff.STE.B3.mat_jet_bound_of_energy` gives the bound with a spurious additive constant
`C (1 + √(ENormB k₀ h))`; rescaling `h ↦ r • h` and letting `r → ∞` removes it.  The resulting
estimate is uniform in the space variable on the `2σ i`-ball, which is what makes the two-variable
`ε`-`δ` argument work.

## Layout

* `ChartData_smul`, `pdVec_smul_local`, `ENormSq_smul_local`, `R_smul_local`, `Rper_smul_local`,
  `ENormB_smul_local` : the homogeneity of the B3 vocabulary under scaling of the section;
* `pdVec_ofReal_const_mul`, `pdVec_ofReal_sub` : linearity of the jet tower in the section;
* `matJet_energy_hom_local` : the homogeneous jet bound (the additive constant removed);
* `ENormB_le_BNorm_uniform_local` : `D.ENormB k h ≤ C * D.BNorm k h` with `C` independent of `h`;
* `contDiffAt_pdVec`, `continuousAt_pdVec_of_contDiffAt` : smoothness of the jet tower in the
  space variable for a single `t`;
* `jetTower_jointContinuous` : the target.
-/

namespace Work.Diff.STE.Lead

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

/-- The `m`-th jet of the difference of two real-valued functions. -/
private lemma pdVec_ofReal_sub {n m : ℕ} (f g : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ)
    (β : Fin m → Fin n) (hf : ContDiffAt ℝ (⊤ : ℕ∞) f z) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g z) :
    Work.Diff.STE.pdVec m β (fun y => (((f y - g y : ℝ)) : ℂ)) z
      = Work.Diff.STE.pdVec m β (fun y => ((f y : ℝ) : ℂ)) z
        - Work.Diff.STE.pdVec m β (fun y => ((g y : ℝ) : ℂ)) z := by
  have hfg : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => f y - g y) z := hf.sub hg
  have h4 : (fun y => f y - g y) = f - g := rfl
  have h3 : iteratedFDeriv ℝ m (fun y => f y - g y) z
      = iteratedFDeriv ℝ m f z - iteratedFDeriv ℝ m g z := by
    rw [h4]
    exact iteratedFDeriv_sub_apply (𝕜 := ℝ)
      (hf.of_le (WithTop.coe_le_coe.mpr le_top))
      (hg.of_le (WithTop.coe_le_coe.mpr le_top))
  rw [Work.Diff.STE.B3.pdVec_ofReal_eq hfg m β,
    Work.Diff.STE.B3.pdVec_ofReal_eq hf m β,
    Work.Diff.STE.B3.pdVec_ofReal_eq hg m β, h3]
  simp only [sub_apply, Complex.ofReal_sub]

/-! ## Smoothness of the jet tower in the flat coordinate -/

/-- A partial derivative of a function smooth at a point is smooth at that point. -/
private lemma contDiffAt_pd {n : ℕ} {f : (Fin n → ℝ) → ℂ} {z : Fin n → ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f z) (j : Fin n) :
    ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.STE.pd j f) z := by
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) z :=
    hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Fin n → ℝ => (fderiv ℝ f x) (Pi.single j (1 : ℝ))) z := by fun_prop
  exact h2

/-- Iterated partial derivatives of a function smooth at a point are smooth at that point. -/
private lemma contDiffAt_pdList {n : ℕ} {f : (Fin n → ℝ) → ℂ} {z : Fin n → ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f z) (L : List (Fin n)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.STE.pdList L f) z := by
  induction L with
  | nil => simpa only [Work.Diff.STE.pdList, List.foldr_nil] using hf
  | cons a L ih =>
    have h : Work.Diff.STE.pdList (a :: L) f = Work.Diff.STE.pd a (Work.Diff.STE.pdList L f) := by
      simp only [Work.Diff.STE.pdList, List.foldr_cons]
    rw [h]
    exact contDiffAt_pd ih a

/-- The `m`-th jet tower of a function smooth at a point is smooth at that point. -/
private lemma contDiffAt_pdVec {n m : ℕ} {f : (Fin n → ℝ) → ℂ} {z : Fin n → ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f z) (β : Fin m → Fin n) :
    ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.STE.pdVec m β f) z := by
  have h : Work.Diff.STE.pdVec m β f = Work.Diff.STE.pdList (List.ofFn β) f := rfl
  rw [h]
  exact contDiffAt_pdList hf _

/-- Consequently the jet tower is continuous in the flat coordinate. -/
private lemma continuousAt_pdVec_of_contDiffAt {n m : ℕ} {f : (Fin n → ℝ) → ℂ} {z : Fin n → ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f z) (β : Fin m → Fin n) :
    ContinuousAt (fun z' => Work.Diff.STE.pdVec m β f z') z :=
  (contDiffAt_pdVec hf β).continuousAt

/-! ## The homogeneous jet bound -/

/-- **The jet bound of `mat_jet_bound_of_energy` without the additive constant.**  For every
section `h` with smooth chart data and every `z` in the `2σ i`-ball,

  `‖∂^β (D.mat i h c d) z‖ ≤ C √(D.ENormB k₀ h)`

with `C` independent of `h` and of `z`.  (`mat_jet_bound_of_energy` gives `C (1 + √·)`; applying it
to `r • h` and letting `r → ∞` removes the `1`.) -/
private theorem matJet_energy_hom_local (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (k₀ : ℕ) (hsmul : ∀ (r : ℝ) (h : Work.Diff.STE.Bil (I := I) (M := M)),
      Work.Diff.STE.D.ChartData (I := I) (M := M) h →
      D.ENormB k₀ (r • h) = r ^ 2 * D.ENormB k₀ h) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M)),
        Work.Diff.STE.D.ChartData (I := I) (M := M) h →
        ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (m : ℕ)
          (hm : 2 * m + Module.finrank ℝ E < 2 * k₀)
          (β : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
          ‖z‖ ≤ 2 * D.σ i →
          ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((D.mat i h c d y : ℝ) : ℂ)) z‖
            ≤ C * Real.sqrt (D.ENormB k₀ h) := by
  classical
  obtain ⟨C, hC, hCb⟩ := Work.Diff.STE.B3.mat_jet_bound_of_energy (I := I) (M := M) D k₀
  have key : ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (_hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
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
        rw [hsmul r h hh, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]
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

/-- **The physical energy is controlled by the Fourier-side norm, uniformly in the section.** -/
private theorem ENormB_le_BNorm_uniform_local (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Work.Diff.STE.Bil (I := I) (M := M)),
      Work.Diff.STE.D.ChartData (I := I) (M := M) h → D.ENormB k h ≤ C * D.BNorm k h := by
  obtain ⟨C, hC, hmain⟩ :=
    Work.Diff.STE.ENormSq_le_CSq_of_contDiff_periodic (ι := Fin (Module.finrank ℝ E)) k
  refine ⟨C, hC, fun h hh => ?_⟩
  have hRsm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.R i h a b) := fun i a b =>
    Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hh i a b
  have hterm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.ENormSq k (D.Rper i h a b)
        ≤ C * Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b)) := by
    intro i a b
    obtain ⟨hcd, hper⟩ :=
      Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i h a b (hRsm i a b)
    exact hmain (D.Rper i h a b) hcd hper
  calc D.ENormB k h
      = ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          Work.Diff.STE.ENormSq k (D.Rper i h a b) := rfl
    _ ≤ ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          C * Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ =>
          Finset.sum_le_sum fun b _ => hterm i a b
    _ = C * D.BNorm k h := by
        simp only [Work.Diff.STE.B3Data.BNorm, Finset.mul_sum]

end Helpers

theorem jetTower_jointContinuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (τ : ℝ) (hτ : 0 < τ) (U : ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hsmU : ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) τ →
      Work.Diff.STE.D.ChartData (I := I) (M := M) (U t))
    (B : ℕ → ℝ) (hB : ∀ k : ℕ, 0 ≤ B k)
    (hUB : ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ k : ℕ, D.BNorm k (U t) ≤ B k)
    (hcont : ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ k : ℕ,
      Filter.Tendsto (fun σ : ℝ => D.BNorm k (U σ - U t))
        (nhdsWithin t (Set.Ico (0 : ℝ) τ)) (nhds 0))
    (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (m : ℕ)
    (β : Fin m → Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun p : ℝ × (Fin (Module.finrank ℝ E) → ℝ) =>
        Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((D.mat i (U p.1) c d y : ℝ) : ℂ)) p.2)
      (Set.Ico (0 : ℝ) τ ×ˢ {z : Fin (Module.finrank ℝ E) → ℝ | ‖z‖ ≤ D.σ i}) := by
  classical
  set k₀ : ℕ := m + Module.finrank ℝ E + 1 with hk₀
  have hmk : 2 * m + Module.finrank ℝ E < 2 * k₀ := by omega
  obtain ⟨C, hC, hCb⟩ := matJet_energy_hom_local (I := I) (M := M) D k₀
    (fun r h hh => ENormB_smul_local D k₀ r h hh)
  obtain ⟨C₁, hC₁, hC₁b⟩ := ENormB_le_BNorm_uniform_local (I := I) (M := M) D k₀
  set F : ℝ × (Fin (Module.finrank ℝ E) → ℝ) → ℂ := fun p =>
    Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      ((D.mat i (U p.1) c d y : ℝ) : ℂ)) p.2 with hFdef
  -- the two-point estimate, uniform in the space variable on the `2σ i`-ball
  have hkey : ∀ (s t : ℝ), s ∈ Set.Ico (0 : ℝ) τ → t ∈ Set.Ico (0 : ℝ) τ →
      ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ i →
      ‖F (s, z) - F (t, z)‖ ≤ C * Real.sqrt (C₁ * D.BNorm k₀ (U s - U t)) := by
    intro s t hs ht z hz
    have hcd : Work.Diff.STE.D.ChartData (I := I) (M := M) (U s - U t) :=
      ChartData_sub (U s) (U t) (hsmU s hs) (hsmU t ht)
    have hms : ContDiffAt ℝ (⊤ : ℕ∞) (D.mat i (U s) c d) z :=
      Work.Diff.STE.B3.mat_contDiffAt_of_chartData D (U s) (hsmU s hs) i c d z
        (D.htarget i z hz)
    have hmt : ContDiffAt ℝ (⊤ : ℕ∞) (D.mat i (U t) c d) z :=
      Work.Diff.STE.B3.mat_contDiffAt_of_chartData D (U t) (hsmU t ht) i c d z
        (D.htarget i z hz)
    have hfun : (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        ((D.mat i (U s - U t) c d y : ℝ) : ℂ))
        = fun y : Fin (Module.finrank ℝ E) → ℝ =>
            (((D.mat i (U s) c d y - D.mat i (U t) c d y : ℝ)) : ℂ) := by
      funext y
      have h1 : D.mat i (U s - U t) c d y
          = D.mat i (U s) c d y - D.mat i (U t) c d y := by
        simp only [Work.Diff.STE.B3Data.mat, Pi.sub_apply, sub_apply]
      rw [h1]
    have hsub : Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        ((D.mat i (U s - U t) c d y : ℝ) : ℂ)) z = F (s, z) - F (t, z) := by
      rw [hfun]
      show Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((D.mat i (U s) c d y - D.mat i (U t) c d y : ℝ) : ℂ)) z
        = Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((D.mat i (U s) c d y : ℝ) : ℂ)) z
          - Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((D.mat i (U t) c d y : ℝ) : ℂ)) z
      exact pdVec_ofReal_sub _ _ z β hms hmt
    rw [← hsub]
    calc ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((D.mat i (U s - U t) c d y : ℝ) : ℂ)) z‖
        ≤ C * Real.sqrt (D.ENormB k₀ (U s - U t)) :=
          hCb (U s - U t) hcd i c d m hmk β z hz
      _ ≤ C * Real.sqrt (C₁ * D.BNorm k₀ (U s - U t)) := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          exact Real.sqrt_le_sqrt (hC₁b (U s - U t) hcd)
  rw [ContinuousOn]
  intro p₀ hp₀
  obtain ⟨ht₀, hz₀⟩ := hp₀
  simp only [Set.mem_setOf_eq] at hz₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  -- the time direction: uniform in space
  have hlim : Filter.Tendsto (fun σ : ℝ => C * Real.sqrt (C₁ * D.BNorm k₀ (U σ - U p₀.1)))
      (nhdsWithin p₀.1 (Set.Ico (0 : ℝ) τ)) (nhds 0) := by
    have hc : ContinuousAt (fun x : ℝ => Real.sqrt (C₁ * x)) 0 :=
      ContinuousAt.sqrt (continuousAt_const.mul continuousAt_id)
    have h3 := hc.tendsto.comp (hcont p₀.1 ht₀ k₀)
    have h4 := h3.const_mul C
    simpa using h4
  have hev : ∀ᶠ σ in nhdsWithin p₀.1 (Set.Ico (0 : ℝ) τ),
      C * Real.sqrt (C₁ * D.BNorm k₀ (U σ - U p₀.1)) < ε / 2 := by
    have h := (Metric.tendsto_nhds.mp hlim) (ε / 2) (by linarith)
    refine h.mono fun σ hσ => ?_
    rw [Real.dist_eq, sub_zero] at hσ
    exact lt_of_le_of_lt (le_abs_self _) hσ
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hev
  -- the space direction at the fixed time
  have hmatc : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : Fin (Module.finrank ℝ E) → ℝ => ((D.mat i (U p₀.1) c d y : ℝ) : ℂ)) p₀.2 := by
    have hT : Work.Diff.STE.flatToE (I := I) (D.x₀ i) p₀.2 ∈ (extChartAt I (D.x₀ i)).target :=
      D.htarget i p₀.2 (by have h := D.hσ i; linarith [hz₀])
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp p₀.2
      (Work.Diff.STE.B3.mat_contDiffAt_of_chartData D (U p₀.1) (hsmU p₀.1 ht₀) i c d p₀.2 hT)
  have hcz : ContinuousAt (fun z : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        ((D.mat i (U p₀.1) c d y : ℝ) : ℂ)) z) p₀.2 :=
    continuousAt_pdVec_of_contDiffAt hmatc β
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.continuousAt_iff.mp hcz (ε / 2) (by linarith)
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
  intro p hp hdist
  obtain ⟨hp1, hp2⟩ := hp
  simp only [Set.mem_setOf_eq] at hp2
  rw [Prod.dist_eq] at hdist
  have hσlt : dist p.1 p₀.1 < δ₁ :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hdist) (min_le_left _ _)
  have hzlt : dist p.2 p₀.2 < δ₂ :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hdist) (min_le_right _ _)
  have hz2 : ‖p.2‖ ≤ 2 * D.σ i := by have h := D.hσ i; linarith [hp2]
  have h1 : ‖F (p.1, p.2) - F (p₀.1, p.2)‖ < ε / 2 :=
    lt_of_le_of_lt (hkey p.1 p₀.1 hp1 ht₀ p.2 hz2) (hδ₁ hσlt hp1)
  have h2 : ‖F (p₀.1, p.2) - F (p₀.1, p₀.2)‖ < ε / 2 := by
    have h := hδ₂ hzlt
    rw [dist_eq_norm] at h
    simpa only [hFdef] using h
  rw [dist_eq_norm]
  have hsplit : F p - F p₀
      = (F (p.1, p.2) - F (p₀.1, p.2)) + (F (p₀.1, p.2) - F (p₀.1, p₀.2)) := by
    have hp' : p = (p.1, p.2) := rfl
    have hp₀' : p₀ = (p₀.1, p₀.2) := rfl
    rw [hp', hp₀']
    ring
  rw [hsplit]
  calc ‖(F (p.1, p.2) - F (p₀.1, p.2)) + (F (p₀.1, p.2) - F (p₀.1, p₀.2))‖
      ≤ ‖F (p.1, p.2) - F (p₀.1, p.2)‖ + ‖F (p₀.1, p.2) - F (p₀.1, p₀.2)‖ :=
        norm_add_le _ _
    _ < ε := by linarith

end Work.Diff.STE.Lead
