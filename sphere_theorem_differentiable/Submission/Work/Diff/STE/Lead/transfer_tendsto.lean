import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.B3.Pointwise
import Submission.Work.Diff.STE.B3.Recon
import Submission.Work.Diff.STE.B3.Rstar_apply
import Submission.Work.Diff.STE.B3.fourierCoeff_periodization
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.D.ChartData_Rstar
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.CSq_tendsto_zero_of_decay_pointwise

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The transfer of coefficientwise convergence through `R_i ∘ R_j^*`

This file proves `Work.Diff.STE.Lead.transfer_tendsto`: the map sending a family of component
functions `g = (g c d)` on the torus to the localised component `R_i (R_j^* g) a b` commutes with
coefficientwise convergence, *provided* the convergence is accompanied by a uniform rapid decay of
the coefficients (`hdec`) and by the transfer estimate `hTb` on the weighted `ℓ²` norms (`CSq`) of
`transfer_CSq_le`.

## Route

* `Rper_fourierCoeff_eq_integral` writes the Fourier coefficient of the periodised component as an
  integral of the (compactly supported, smooth) chart component against the character; additivity
  in the section follows (`Rper_fourierCoeff_sub`, using `R`-additivity `R_sub_tt`).
* `Rper_Rstar_contDiff_periodic` shows that `Rper_i (R_j^* G) a b` is smooth and `1`-periodic as
  soon as the components of `G` are smooth (`ChartData_Rstar` + `R_contDiff_of_chartData` +
  `periodization_contDiff_periodic`).  Combined with `summable_weighted_fourierCoeff_of_contDiff`
  this gives the *summability* of the weighted coefficient family, which is what makes the term
  bound `⟨μ⟩^{2k}‖ĉ(μ)‖² ≤ CSq k ĉ` available.
* The per-component convergence `CSq k (ĉ (f m - f_lim)) → 0` is the child lemma
  `Work.Diff.STE.CSq_tendsto_zero_of_decay_pointwise` (decay `hdec` + pointwise convergence
  `hconv`), and the transfer estimate `hTb` at the level `k = finrank + 1` converts it into
  `CSq k` of the reconstructed component, whence the single coefficient converges.
-/

namespace Work.Diff.STE.Lead

open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **`R_j^*` is additive in the component family.** -/
lemma Rstar_sub (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (u v : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ) :
    D.Rstar j u - D.Rstar j v = D.Rstar j (fun a b z => u a b z - v a b z) := by
  funext p
  ext X Y
  rw [Pi.sub_apply, sub_apply, sub_apply,
    Work.Diff.STE.B3.Rstar_apply, Work.Diff.STE.B3.Rstar_apply, Work.Diff.STE.B3.Rstar_apply]
  rw [← mul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **`R_j` is additive in the section.** -/
lemma R_sub_tt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (X Y : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    D.R j (X - Y) a b = D.R j X a b - D.R j Y a b := by
  funext z
  simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat, Pi.sub_apply, sub_apply]
  ring

/-- The flat chart component of a section with smooth chart component is integrable on `ℝⁿ`. -/
lemma integrable_R_ofReal (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (Z : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀) (a b : Fin (Module.finrank ℝ E))
    (hZ : ContDiff ℝ (⊤ : ℕ∞) (D.R j Z a b)) :
    MeasureTheory.Integrable (fun z => ((D.R j Z a b z : ℝ) : ℂ)) := by
  refine Continuous.integrable_of_hasCompactSupport
    (Complex.ofRealCLM.continuous.comp hZ.continuous) ?_
  show IsCompact (tsupport (fun z => ((D.R j Z a b z : ℝ) : ℂ)))
  have hsub : tsupport (fun z : Fin (Module.finrank ℝ E) → ℝ =>
      ((D.R j Z a b z : ℝ) : ℂ)) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
    refine (closure_mono ?_).trans
      (closure_minimal (Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self)
        (isClosed_set_pi fun _ _ => isClosed_Icc))
    intro z hz
    have hz' : D.R j Z a b z ≠ 0 := by
      intro h0
      exact hz (by show ((D.R j Z a b z : ℝ) : ℂ) = 0
                   rw [h0, Complex.ofReal_zero])
    exact D.psi_supp j (Function.mem_support.mpr (fun h0 => hz' (by
      show D.R j Z a b z = 0
      simp only [Work.Diff.STE.B3Data.R, h0, zero_mul])))
  exact (isCompact_univ_pi (fun _ : Fin (Module.finrank ℝ E) => isCompact_Icc)).of_isClosed_subset
    (isClosed_tsupport _) hsub

/-- **The Fourier coefficient of a periodised component as an integral over `ℝⁿ`.** -/
lemma Rper_fourierCoeff_eq_integral (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (Z : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀) (a b : Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E) → ℤ) (hZ : ContDiff ℝ (⊤ : ℕ∞) (D.R j Z a b)) :
    Work.Diff.STE.fourierCoeff (D.Rper j Z a b) m
      = ∫ z, Work.Diff.STE.fourierExp (-m) z * ((D.R j Z a b z : ℝ) : ℂ) := by
  rw [show D.Rper j Z a b = (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      ∑' k : Fin (Module.finrank ℝ E) → ℤ, ((D.R j Z a b (y + Work.Diff.STE.iVec k) : ℝ) : ℂ))
      from rfl]
  have hsupp : Function.support (fun z : Fin (Module.finrank ℝ E) → ℝ =>
      ((D.R j Z a b z : ℝ) : ℂ)) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro z hz
    have hz' : D.R j Z a b z ≠ 0 := by
      intro h0
      exact hz (by show ((D.R j Z a b z : ℝ) : ℂ) = 0
                   rw [h0, Complex.ofReal_zero])
    exact D.psi_supp j (Function.mem_support.mpr (fun h0 => hz' (by
      show D.R j Z a b z = 0
      simp only [Work.Diff.STE.B3Data.R, h0, zero_mul])))
  rw [Work.Diff.STE.B3.fourierCoeff_periodization _ m hsupp
    (integrable_R_ofReal D Z j a b hZ)]
  have hzero : ∀ z ∉ (Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) =>
      Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))),
      Work.Diff.STE.fourierExp (-m) z * ((D.R j Z a b z : ℝ) : ℂ) = 0 := by
    intro z hz
    have hz' : D.R j Z a b z = 0 := by
      by_contra h0
      have hmem : ((D.R j Z a b z : ℝ) : ℂ) ≠ 0 := by
        rwa [Complex.ofReal_ne_zero]
      exact hz (Set.pi_mono (fun _ _ => Set.Ioo_subset_Ioc_self)
        (hsupp (Function.mem_support.mpr hmem)))
    rw [hz', Complex.ofReal_zero, mul_zero]
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]

/-- **The Fourier coefficients are additive in the section.** -/
lemma Rper_fourierCoeff_sub (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (X Y : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀) (a b : Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E) → ℤ)
    (hXY : ContDiff ℝ (⊤ : ℕ∞) (D.R j (X - Y) a b))
    (hX : ContDiff ℝ (⊤ : ℕ∞) (D.R j X a b))
    (hY : ContDiff ℝ (⊤ : ℕ∞) (D.R j Y a b)) :
    Work.Diff.STE.fourierCoeff (D.Rper j (X - Y) a b) m
      = Work.Diff.STE.fourierCoeff (D.Rper j X a b) m
        - Work.Diff.STE.fourierCoeff (D.Rper j Y a b) m := by
  rw [Rper_fourierCoeff_eq_integral D (X - Y) j a b m hXY,
    Rper_fourierCoeff_eq_integral D X j a b m hX,
    Rper_fourierCoeff_eq_integral D Y j a b m hY]
  rw [show (fun z => Work.Diff.STE.fourierExp (-m) z * ((D.R j (X - Y) a b z : ℝ) : ℂ))
      = fun z => Work.Diff.STE.fourierExp (-m) z * ((D.R j X a b z : ℝ) : ℂ)
          - Work.Diff.STE.fourierExp (-m) z * ((D.R j Y a b z : ℝ) : ℂ) from by
    funext z
    simp only [R_sub_tt (I := I) (M := M) D X Y j a b, Pi.sub_apply, Complex.ofReal_sub]
    ring]
  exact MeasureTheory.integral_sub
    (Work.Diff.STE.B3.integrable_fourierExp_mul (-m)
      (integrable_R_ofReal D X j a b hX))
    (Work.Diff.STE.B3.integrable_fourierExp_mul (-m)
      (integrable_R_ofReal D Y j a b hY))

/-- **`Rper_j (R_j^* G) a b` is smooth and `1`-periodic for smooth components `G`.** -/
lemma Rper_Rstar_contDiff_periodic (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (i j : ι₀)
    (G : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hG : ∀ a b : Fin (Module.finrank ℝ E), ContDiff ℝ (⊤ : ℕ∞) (G a b))
    (a b : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (D.Rper i (D.Rstar j G) a b) ∧
      Work.Diff.STE.Periodic1 (D.Rper i (D.Rstar j G) a b) := by
  have hCD : Work.Diff.STE.D.ChartData (I := I) (M := M) (D.Rstar j G) :=
    Work.Diff.STE.D.ChartData_Rstar (I := I) (M := M) D j G hG
  have hR : ContDiff ℝ (⊤ : ℕ∞) (D.R i (D.Rstar j G) a b) :=
    Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D _ hCD i a b
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun z => ((D.R i (D.Rstar j G) a b z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hR
  have hFsupp : Function.support (fun z : Fin (Module.finrank ℝ E) → ℝ =>
      ((D.R i (D.Rstar j G) a b z : ℝ) : ℂ)) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro z hz
    have hz' : D.R i (D.Rstar j G) a b z ≠ 0 := by
      intro h0
      exact hz (by show ((D.R i (D.Rstar j G) a b z : ℝ) : ℂ) = 0
                   rw [h0, Complex.ofReal_zero])
    refine D.psi_supp i (Function.mem_support.mpr fun h0 => hz' ?_)
    simp only [Work.Diff.STE.B3Data.R, h0, zero_mul]
  have hper := Work.Diff.STE.periodization_contDiff_periodic
    (fun z => ((D.R i (D.Rstar j G) a b z : ℝ) : ℂ)) hF hFsupp
  refine ⟨?_, ?_⟩
  · change ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin (Module.finrank ℝ E) → ℝ =>
      ∑' m : Fin (Module.finrank ℝ E) → ℤ,
        ((D.R i (D.Rstar j G) a b (x + Work.Diff.STE.iVec m) : ℝ) : ℂ))
    exact hper.1
  · change Work.Diff.STE.Periodic1 (fun x : Fin (Module.finrank ℝ E) → ℝ =>
      ∑' m : Fin (Module.finrank ℝ E) → ℤ,
        ((D.R i (D.Rstar j G) a b (x + Work.Diff.STE.iVec m) : ℝ) : ℂ))
    exact hper.2.1

theorem transfer_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (i j : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ)
    (f : ℕ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (flim : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hsm : ∀ (m : ℕ) (c d : Fin (Module.finrank ℝ E)), ContDiff ℝ (⊤ : ℕ∞) (f m c d))
    (hper : ∀ (m : ℕ) (c d : Fin (Module.finrank ℝ E)), Work.Diff.STE.Periodic1 (f m c d))
    (hsm_l : ∀ c d : Fin (Module.finrank ℝ E), ContDiff ℝ (⊤ : ℕ∞) (flim c d))
    (hper_l : ∀ c d : Fin (Module.finrank ℝ E), Work.Diff.STE.Periodic1 (flim c d))
    (hTb : ∀ k : ℕ, Module.finrank ℝ E < 2 * k → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
          (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
        (hsm : ∀ c d, ContDiff ℝ (⊤ : ℕ∞) (g c d))
        (hper : ∀ c d, Work.Diff.STE.Periodic1 (g c d)),
        Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i (D.Rstar j g) a b))
          ≤ C * ∑ c, ∑ d, Work.Diff.STE.CSq k
              (Work.Diff.STE.fourierCoeff (fun z => ((g c d z : ℝ) : ℂ))))
    (hdec : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (c d : Fin (Module.finrank ℝ E))
      (ν : Fin (Module.finrank ℝ E) → ℤ),
      ‖Work.Diff.STE.fourierCoeff (fun z => ((f m c d z : ℝ) : ℂ)) ν‖ *
          (Work.Diff.STE.wt ν) ^ M ≤ C ∧
      ‖Work.Diff.STE.fourierCoeff (fun z => ((flim c d z : ℝ) : ℂ)) ν‖ *
          (Work.Diff.STE.wt ν) ^ M ≤ C)
    (hconv : ∀ (c d : Fin (Module.finrank ℝ E)) (ν : Fin (Module.finrank ℝ E) → ℤ),
      Filter.Tendsto (fun m : ℕ => Work.Diff.STE.fourierCoeff
          (fun z => ((f m c d z : ℝ) : ℂ)) ν) Filter.atTop
        (nhds (Work.Diff.STE.fourierCoeff (fun z => ((flim c d z : ℝ) : ℂ)) ν))) :
    Filter.Tendsto (fun m : ℕ => Work.Diff.STE.fourierCoeff
        (D.Rper i (D.Rstar j (f m)) a b) μ) Filter.atTop
      (nhds (Work.Diff.STE.fourierCoeff (D.Rper i (D.Rstar j flim) a b) μ)) := by
  classical
  -- the level of the weighted `ℓ²` norm at which the transfer estimate is used
  obtain ⟨C₀, hC₀, hTbnd⟩ := hTb (Module.finrank ℝ E + 1) (by omega)
  -- linearity of the Fourier coefficients in the component family
  have hlin : ∀ (m : ℕ) (c d : Fin (Module.finrank ℝ E)) (ν : Fin (Module.finrank ℝ E) → ℤ),
      Work.Diff.STE.fourierCoeff (fun z => (((f m c d z - flim c d z : ℝ)) : ℂ)) ν
        = Work.Diff.STE.fourierCoeff (fun z => (((f m c d z : ℝ)) : ℂ)) ν
          - Work.Diff.STE.fourierCoeff (fun z => (((flim c d z : ℝ)) : ℂ)) ν := by
    intro m c d ν
    have hfun : (fun z : Fin (Module.finrank ℝ E) → ℝ => (((f m c d z - flim c d z : ℝ)) : ℂ))
        = fun z => (((f m c d z : ℝ)) : ℂ) - (((flim c d z : ℝ)) : ℂ) := by
      funext z
      exact Complex.ofReal_sub _ _
    rw [hfun]
    exact Work.Diff.STE.flat.fourierCoeff_sub_of_continuous _ _
      (Complex.continuous_ofReal.comp (hsm m c d).continuous)
      (Complex.continuous_ofReal.comp (hsm_l c d).continuous) ν
  -- the weighted `ℓ²` norms of the component differences tend to `0`
  have hchild : ∀ c d : Fin (Module.finrank ℝ E),
      Filter.Tendsto (fun m : ℕ => Work.Diff.STE.CSq (Module.finrank ℝ E + 1)
        (fun ν : Fin (Module.finrank ℝ E) → ℤ =>
          Work.Diff.STE.fourierCoeff (fun z => (((f m c d z - flim c d z : ℝ)) : ℂ)) ν))
        Filter.atTop (nhds 0) := by
    intro c d
    refine Work.Diff.STE.CSq_tendsto_zero_of_decay_pointwise _ ?_ ?_ (Module.finrank ℝ E + 1)
    · intro M
      obtain ⟨C, hC, hCM⟩ := hdec M
      refine ⟨2 * C, by positivity, fun m ν => ?_⟩
      rw [hlin m c d ν]
      have h2 := (hCM m c d ν).1
      have h3 := (hCM m c d ν).2
      calc ‖Work.Diff.STE.fourierCoeff (fun z => (((f m c d z : ℝ)) : ℂ)) ν
              - Work.Diff.STE.fourierCoeff (fun z => (((flim c d z : ℝ)) : ℂ)) ν‖
            * (Work.Diff.STE.wt ν) ^ M
          ≤ (‖Work.Diff.STE.fourierCoeff (fun z => (((f m c d z : ℝ)) : ℂ)) ν‖
              + ‖Work.Diff.STE.fourierCoeff (fun z => (((flim c d z : ℝ)) : ℂ)) ν‖)
            * (Work.Diff.STE.wt ν) ^ M :=
            mul_le_mul_of_nonneg_right (norm_sub_le _ _)
              (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos ν)) M)
        _ = ‖Work.Diff.STE.fourierCoeff (fun z => (((f m c d z : ℝ)) : ℂ)) ν‖
              * (Work.Diff.STE.wt ν) ^ M
            + ‖Work.Diff.STE.fourierCoeff (fun z => (((flim c d z : ℝ)) : ℂ)) ν‖
              * (Work.Diff.STE.wt ν) ^ M := by ring
        _ ≤ C + C := add_le_add h2 h3
        _ = 2 * C := by ring
    · intro ν
      have hsub : Filter.Tendsto (fun m : ℕ =>
          Work.Diff.STE.fourierCoeff (fun z => (((f m c d z : ℝ)) : ℂ)) ν
          - Work.Diff.STE.fourierCoeff (fun z => (((flim c d z : ℝ)) : ℂ)) ν)
          Filter.atTop (nhds 0) := by
        have hbase : Filter.Tendsto
            (fun _ : ℕ => Work.Diff.STE.fourierCoeff (fun z => (((flim c d z : ℝ)) : ℂ)) ν)
            Filter.atTop
            (nhds (Work.Diff.STE.fourierCoeff (fun z => (((flim c d z : ℝ)) : ℂ)) ν)) :=
          tendsto_const_nhds
        simpa using (hconv c d ν).sub hbase
      simpa only [hlin] using hsub
  have hsumT : Filter.Tendsto
      (fun m : ℕ => ∑ c, ∑ d, Work.Diff.STE.CSq (Module.finrank ℝ E + 1)
        (fun ν : Fin (Module.finrank ℝ E) → ℤ =>
          Work.Diff.STE.fourierCoeff (fun z => (((f m c d z - flim c d z : ℝ)) : ℂ)) ν))
      Filter.atTop (nhds 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun c _ => tendsto_finsetSum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun d _ => hchild c d))
    simpa using h
  -- the coefficient of the reconstructed difference
  have hcoeff : ∀ m : ℕ,
      Work.Diff.STE.fourierCoeff (D.Rper i (D.Rstar j (f m)) a b) μ
        - Work.Diff.STE.fourierCoeff (D.Rper i (D.Rstar j flim) a b) μ
        = Work.Diff.STE.fourierCoeff
            (D.Rper i (D.Rstar j (fun c d z => f m c d z - flim c d z)) a b) μ := by
    intro m
    have hsub : D.Rstar j (f m) - D.Rstar j flim
        = D.Rstar j (fun c d z => f m c d z - flim c d z) :=
      Rstar_sub (I := I) (M := M) D j (f m) flim
    have hX : ContDiff ℝ (⊤ : ℕ∞) (D.R i (D.Rstar j (f m)) a b) :=
      Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D _
        (Work.Diff.STE.D.ChartData_Rstar (I := I) (M := M) D j (f m)
          (fun a b => hsm m a b)) i a b
    have hY : ContDiff ℝ (⊤ : ℕ∞) (D.R i (D.Rstar j flim) a b) :=
      Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D _
        (Work.Diff.STE.D.ChartData_Rstar (I := I) (M := M) D j flim hsm_l) i a b
    have hG : ContDiff ℝ (⊤ : ℕ∞)
        (D.R i (D.Rstar j (fun c d z => f m c d z - flim c d z)) a b) :=
      Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D _
        (Work.Diff.STE.D.ChartData_Rstar (I := I) (M := M) D j _
          (fun a b => (hsm m a b).sub (hsm_l a b))) i a b
    have hXY : ContDiff ℝ (⊤ : ℕ∞) (D.R i (D.Rstar j (f m) - D.Rstar j flim) a b) := by
      rw [hsub]
      exact hG
    have hkey := Rper_fourierCoeff_sub (I := I) (M := M) D (D.Rstar j (f m))
      (D.Rstar j flim) i a b μ hXY hX hY
    rw [hsub] at hkey
    exact hkey.symm
  -- the level-`k` bound for every `m`
  have hbd : ∀ m : ℕ,
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (D.Rstar j (f m)) a b) μ
          - Work.Diff.STE.fourierCoeff (D.Rper i (D.Rstar j flim) a b) μ‖ ^ 2
        * (Work.Diff.STE.wt μ) ^ (Module.finrank ℝ E + 1)
      ≤ C₀ * ∑ c, ∑ d, Work.Diff.STE.CSq (Module.finrank ℝ E + 1)
          (fun ν => Work.Diff.STE.fourierCoeff
            (fun z => (((f m c d z - flim c d z : ℝ)) : ℂ)) ν) := by
    intro m
    have hsmG : ∀ c d, ContDiff ℝ (⊤ : ℕ∞) (fun z => f m c d z - flim c d z) :=
      fun c d => (hsm m c d).sub (hsm_l c d)
    have hperG : ∀ c d, Work.Diff.STE.Periodic1 (fun z => f m c d z - flim c d z) := by
      intro c d i x
      show f m c d (x + Pi.single i 1) - flim c d (x + Pi.single i 1)
        = f m c d x - flim c d x
      rw [hper m c d i x, hper_l c d i x]
    have hperout := Rper_Rstar_contDiff_periodic (I := I) (M := M) D i j
      (fun c d z => f m c d z - flim c d z) hsmG a b
    have hsumm := Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
      (D.Rper i (D.Rstar j (fun c d z => f m c d z - flim c d z)) a b)
      hperout.1 hperout.2 (Module.finrank ℝ E + 1)
    have hterm : (Work.Diff.STE.wt μ) ^ (Module.finrank ℝ E + 1)
        * ‖Work.Diff.STE.fourierCoeff
            (D.Rper i (D.Rstar j (fun c d z => f m c d z - flim c d z)) a b) μ‖ ^ 2
        ≤ Work.Diff.STE.CSq (Module.finrank ℝ E + 1)
          (Work.Diff.STE.fourierCoeff
            (D.Rper i (D.Rstar j (fun c d z => f m c d z - flim c d z)) a b)) := by
      have h := Summable.sum_le_tsum
        (f := fun ν : Fin (Module.finrank ℝ E) → ℤ =>
          (Work.Diff.STE.wt ν) ^ (Module.finrank ℝ E + 1)
            * ‖Work.Diff.STE.fourierCoeff
                (D.Rper i (D.Rstar j (fun c d z => f m c d z - flim c d z)) a b) ν‖ ^ 2)
        ({μ} : Finset (Fin (Module.finrank ℝ E) → ℤ))
        (fun ν _ => mul_nonneg
          (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos ν)) _) (sq_nonneg _))
        hsumm
      simpa [Work.Diff.STE.CSq] using h
    have hT := hTbnd (fun c d z => f m c d z - flim c d z) hsmG hperG
    calc ‖Work.Diff.STE.fourierCoeff (D.Rper i (D.Rstar j (f m)) a b) μ
            - Work.Diff.STE.fourierCoeff (D.Rper i (D.Rstar j flim) a b) μ‖ ^ 2
          * (Work.Diff.STE.wt μ) ^ (Module.finrank ℝ E + 1)
        = ‖Work.Diff.STE.fourierCoeff
            (D.Rper i (D.Rstar j (fun c d z => f m c d z - flim c d z)) a b) μ‖ ^ 2
          * (Work.Diff.STE.wt μ) ^ (Module.finrank ℝ E + 1) := by rw [hcoeff m]
      _ = (Work.Diff.STE.wt μ) ^ (Module.finrank ℝ E + 1)
          * ‖Work.Diff.STE.fourierCoeff
              (D.Rper i (D.Rstar j (fun c d z => f m c d z - flim c d z)) a b) μ‖ ^ 2 :=
          by ring
      _ ≤ Work.Diff.STE.CSq (Module.finrank ℝ E + 1)
          (Work.Diff.STE.fourierCoeff
            (D.Rper i (D.Rstar j (fun c d z => f m c d z - flim c d z)) a b)) := hterm
      _ ≤ C₀ * ∑ c, ∑ d, Work.Diff.STE.CSq (Module.finrank ℝ E + 1)
          (fun ν => Work.Diff.STE.fourierCoeff
            (fun z => (((f m c d z - flim c d z : ℝ)) : ℂ)) ν) := hT
  -- divide by the weight and squeeze
  have hbd' : ∀ m : ℕ,
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (D.Rstar j (f m)) a b) μ
          - Work.Diff.STE.fourierCoeff (D.Rper i (D.Rstar j flim) a b) μ‖ ^ 2
      ≤ (C₀ * ∑ c, ∑ d, Work.Diff.STE.CSq (Module.finrank ℝ E + 1)
          (fun ν => Work.Diff.STE.fourierCoeff
            (fun z => (((f m c d z - flim c d z : ℝ)) : ℂ)) ν))
        / (Work.Diff.STE.wt μ) ^ (Module.finrank ℝ E + 1) := by
    intro m
    rw [le_div_iff₀ (pow_pos (Work.Diff.STE.wt_pos μ) _)]
    exact hbd m
  have hlim2 : Filter.Tendsto
      (fun m : ℕ => ‖Work.Diff.STE.fourierCoeff (D.Rper i (D.Rstar j (f m)) a b) μ
          - Work.Diff.STE.fourierCoeff (D.Rper i (D.Rstar j flim) a b) μ‖ ^ 2)
      Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun m => sq_nonneg _) (fun m => hbd' m) ?_
    have h1 : Filter.Tendsto
        (fun m : ℕ => C₀ * (∑ c, ∑ d, Work.Diff.STE.CSq (Module.finrank ℝ E + 1)
          (fun ν => Work.Diff.STE.fourierCoeff
            (fun z => (((f m c d z - flim c d z : ℝ)) : ℂ)) ν)))
        Filter.atTop (nhds (C₀ * 0)) := hsumT.const_mul C₀
    rw [mul_zero] at h1
    simpa using h1.div_const ((Work.Diff.STE.wt μ) ^ (Module.finrank ℝ E + 1))
  have hnorm : Filter.Tendsto
      (fun m : ℕ => ‖Work.Diff.STE.fourierCoeff (D.Rper i (D.Rstar j (f m)) a b) μ
          - Work.Diff.STE.fourierCoeff (D.Rper i (D.Rstar j flim) a b) μ‖)
      Filter.atTop (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hlim2
    rw [Real.sqrt_zero] at h
    convert h using 1
    ext m
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  exact (tendsto_iff_norm_sub_tendsto_zero).mpr hnorm

end Work.Diff.STE.Lead
