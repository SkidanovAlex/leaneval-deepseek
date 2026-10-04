import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.B3.BPairDefs
import Submission.Work.Diff.STE.B3.dens_bound_sigma
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.D.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open MeasureTheory Work.Diff.STE
open scoped BigOperators

namespace Work.Diff.STE.Lead

/-- The finite set of multi-indices `{0, -1}^n` over which the periodisation of a localised
component supported in the open centred cube is a *finite* sum on the unit cube `(0,1]ⁿ`. -/
def cubeIdx (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    Finset (Fin (Module.finrank ℝ E) → ℤ) :=
  Fintype.piFinset fun _ : Fin (Module.finrank ℝ E) => Finset.Icc (-1 : ℤ) 0

lemma cubeIdx_card (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    (cubeIdx E).card = 2 ^ Module.finrank ℝ E := by
  rw [cubeIdx, Fintype.card_piFinset]
  simp [Finset.prod_const, Finset.card_univ]

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **The elementary one-dimensional Lipschitz bound.** A matrix coefficient `s ↦ u m s x u v` of a
`Bil`-valued family whose `s`-derivative on `[0,τ]` is bounded by `C √g(u,u) √g(v,v)` is Lipschitz
with that constant (mean value inequality on the convex set `[0,τ]`). -/
lemma abs_sub_le_of_ode
    (C τ : ℝ) (u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hode : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) τ → ∀ (x : M) (u₀ v : TangentSpace I x),
      ∃ R : ℝ, HasDerivWithinAt (fun s : ℝ => u m s x u₀ v) R (Set.Icc (0 : ℝ) τ) t ∧
        |R| ≤ C * Real.sqrt (g₀.inner x u₀ u₀) * Real.sqrt (g₀.inner x v v))
    (m : ℕ) (x : M) (u₀ v : TangentSpace I x) {t t' : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) τ) (ht' : t' ∈ Set.Icc (0 : ℝ) τ) :
    |u m t x u₀ v - u m t' x u₀ v|
      ≤ C * Real.sqrt (g₀.inner x u₀ u₀) * Real.sqrt (g₀.inner x v v) * |t - t'| := by
  set f' : ℝ → ℝ →L[ℝ] ℝ := fun s =>
    if h : s ∈ Set.Icc (0 : ℝ) τ then
      ContinuousLinearMap.toSpanSingleton ℝ (Classical.choose (hode m s h x u₀ v)) else 0 with hf'
  have hderiv : ∀ s ∈ Set.Icc (0 : ℝ) τ,
      HasFDerivWithinAt (fun s : ℝ => u m s x u₀ v) (f' s) (Set.Icc (0 : ℝ) τ) s := by
    intro s hs
    have hspec := (Classical.choose_spec (hode m s hs x u₀ v)).1
    have hval : f' s
        = ContinuousLinearMap.toSpanSingleton ℝ (Classical.choose (hode m s hs x u₀ v)) := by
      rw [hf']; exact dite_eq_left hs
    rw [hval]
    exact hspec.hasFDerivWithinAt
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) τ,
      ‖f' s‖ ≤ C * Real.sqrt (g₀.inner x u₀ u₀) * Real.sqrt (g₀.inner x v v) := by
    intro s hs
    have hspec := (Classical.choose_spec (hode m s hs x u₀ v)).2
    have hval : f' s
        = ContinuousLinearMap.toSpanSingleton ℝ (Classical.choose (hode m s hs x u₀ v)) := by
      rw [hf']; exact dite_eq_left hs
    rw [hval, ContinuousLinearMap.norm_toSpanSingleton, Real.norm_eq_abs]
    exact hspec
  have hmain := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound
    (convex_Icc (0 : ℝ) τ) ht' ht
  simpa only [Real.norm_eq_abs] using hmain

/-- **Pointwise Lipschitz bound for the localised component `R`.**  On the support of `ψ i` the
frame `e i` is `g₀`-orthonormal and `|ψ i z| ≤ 1`, while `√(dens i z) ≤ √Cdens`; off the support
both sides are zero.  The matrix `mat i (u m ·) a b z` is Lipschitz with constant `C` by
`abs_sub_le_of_ode`. -/
lemma abs_R_sub_le
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (C τ : ℝ) (hC : 0 ≤ C) (u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hode : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) τ → ∀ (x : M) (u₀ v : TangentSpace I x),
      ∃ R : ℝ, HasDerivWithinAt (fun s : ℝ => u m s x u₀ v) R (Set.Icc (0 : ℝ) τ) t ∧
        |R| ≤ C * Real.sqrt (g₀.inner x u₀ u₀) * Real.sqrt (g₀.inner x v v))
    (Cdens : ℝ)
    (hdens : ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ D.σ i → D.dens i z ≤ Cdens)
    (m : ℕ) {t t' : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) τ) (ht' : t' ∈ Set.Icc (0 : ℝ) τ)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ) :
    |D.R i (u m t) a b z - D.R i (u m t') a b z| ≤ Real.sqrt Cdens * C * |t - t'| := by
  by_cases hpsi : D.psi i z = 0
  · have hsub : D.R i (u m t) a b z - D.R i (u m t') a b z = 0 := by
      simp only [Work.Diff.STE.B3Data.R, hpsi, zero_mul, sub_self]
    rw [hsub, abs_zero]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hC) (abs_nonneg _)
  · have hON := Work.Diff.STE.B3.isONFrame_of_psi_ne_zero D hpsi
    have hsm : ‖z‖ < D.σ i := Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero D hpsi
    have hψeq : D.psi i z = D.ζ i (D.pt i z) :=
      Work.Diff.STE.B3.psi_eq_zeta_of_psi_ne_zero D hpsi
    have hζle : D.ζ i (D.pt i z) ≤ 1 := by
      have h1 : (D.ζ i (D.pt i z)) ^ 2 ≤ 1 := by
        calc (D.ζ i (D.pt i z)) ^ 2 ≤ ∑ j : ι₀, (D.ζ j (D.pt i z)) ^ 2 :=
              Finset.single_le_sum (f := fun j => (D.ζ j (D.pt i z)) ^ 2)
                (s := Finset.univ) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
          _ = 1 := D.hζsq (D.pt i z)
      nlinarith [D.hζnn i (D.pt i z), sq_nonneg (D.ζ i (D.pt i z))]
    have habsψ : |D.psi i z| ≤ 1 := by
      rw [hψeq, abs_of_nonneg (D.hζnn i (D.pt i z))]
      exact hζle
    have hdensle : Real.sqrt (D.dens i z) ≤ Real.sqrt Cdens :=
      Real.sqrt_le_sqrt (hdens i z (le_of_lt hsm))
    have hsq1 :
        Real.sqrt (g₀.inner (D.pt i z) (D.e i a (D.pt i z)) (D.e i a (D.pt i z))) = 1 := by
      rw [hON a a, if_pos rfl, Real.sqrt_one]
    have hsq2 :
        Real.sqrt (g₀.inner (D.pt i z) (D.e i b (D.pt i z)) (D.e i b (D.pt i z))) = 1 := by
      rw [hON b b, if_pos rfl, Real.sqrt_one]
    have hmat : |D.mat i (u m t) a b z - D.mat i (u m t') a b z| ≤ C * |t - t'| := by
      have h := abs_sub_le_of_ode C τ u hode m (D.pt i z)
        (D.e i a (D.pt i z)) (D.e i b (D.pt i z)) ht ht'
      rw [hsq1, hsq2, mul_one, mul_one] at h
      exact h
    have hfac : |D.psi i z * Real.sqrt (D.dens i z)| ≤ Real.sqrt Cdens := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      have h := mul_le_mul habsψ hdensle (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      rwa [one_mul] at h
    have hdecomp : D.psi i z * Real.sqrt (D.dens i z) * D.mat i (u m t) a b z
        - D.psi i z * Real.sqrt (D.dens i z) * D.mat i (u m t') a b z
        = (D.psi i z * Real.sqrt (D.dens i z))
          * (D.mat i (u m t) a b z - D.mat i (u m t') a b z) := by ring
    have hgoal : D.R i (u m t) a b z - D.R i (u m t') a b z
        = (D.psi i z * Real.sqrt (D.dens i z))
          * (D.mat i (u m t) a b z - D.mat i (u m t') a b z) := by
      simp only [Work.Diff.STE.B3Data.R]
      exact hdecomp
    rw [hgoal, abs_mul]
    calc |D.psi i z * Real.sqrt (D.dens i z)|
          * |D.mat i (u m t) a b z - D.mat i (u m t') a b z|
        ≤ Real.sqrt Cdens * (C * |t - t'|) :=
          mul_le_mul hfac hmat (abs_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt Cdens * C * |t - t'| := by ring

/-- **The periodisation is a finite sum on the unit cube.**  If `x ∈ (0,1]ⁿ` then every multi-index
`m` with `R i (·) a b (x + m) ≠ 0` satisfies `m j ∈ {0,-1}` in every coordinate: the support of
`R` lies in the open centred cube, and `x j + m j ∈ (-1/2,1/2)` with `x j ∈ (0,1]` forces this. -/
lemma Rper_sub_eq_finset_sum
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (m : ℕ) (t t' : ℝ) (i : ι₀) (a b : Fin (Module.finrank ℝ E))
    (x : Fin (Module.finrank ℝ E) → ℝ) (hx : x ∈ unitCube (ι := Fin (Module.finrank ℝ E))) :
    D.Rper i (u m t) a b x - D.Rper i (u m t') a b x
      = ∑ m' ∈ cubeIdx E,
          (((D.R i (u m t) a b (x + iVec m') : ℝ) : ℂ)
            - ((D.R i (u m t') a b (x + iVec m') : ℝ) : ℂ)) := by
  have hzero : ∀ (hh : Work.Diff.STE.Bil (I := I) (M := M))
      (m' : Fin (Module.finrank ℝ E) → ℤ), m' ∉ cubeIdx E →
      ((D.R i hh a b (x + iVec m') : ℝ) : ℂ) = 0 := by
    intro hh m' hm
    by_contra hc
    have hne : D.R i hh a b (x + iVec m') ≠ 0 := fun h0 => hc (by rw [h0, Complex.ofReal_zero])
    have hmem : x + iVec m' ∈ Function.support (D.R i hh a b) := by
      rwa [Function.mem_support]
    have hpi := D.R_support i hh a b hmem
    have hnot : ¬∀ j, m' j ∈ Finset.Icc (-1 : ℤ) 0 :=
      fun hall => hm ((Fintype.mem_piFinset).mpr hall)
    obtain ⟨j, hj⟩ := not_forall.mp hnot
    have hj' : ¬((-1 : ℤ) ≤ m' j ∧ m' j ≤ 0) := fun hh' => hj (Finset.mem_Icc.mpr hh')
    have hbad : m' j ≤ -2 ∨ 1 ≤ m' j := by
      push_neg at hj'
      omega
    have hcoord := Set.mem_pi.mp hpi j (Set.mem_univ j)
    rw [Set.mem_Ioo] at hcoord
    simp only [Pi.add_apply, Work.Diff.STE.iVec_apply] at hcoord
    have hxc : x j ∈ Set.Ioc (0 : ℝ) 1 := Set.mem_pi.mp hx j (Set.mem_univ j)
    rw [Set.mem_Ioc] at hxc
    rcases hbad with hle | hge
    · have hcast : ((m' j : ℤ) : ℝ) ≤ -2 := by exact_mod_cast hle
      linarith [hcoord.1, hxc.2]
    · have hcast : (1 : ℝ) ≤ ((m' j : ℤ) : ℝ) := by exact_mod_cast hge
      linarith [hcoord.2, hxc.1]
  have h1 : D.Rper i (u m t) a b x
      = ∑ m' ∈ cubeIdx E, ((D.R i (u m t) a b (x + iVec m') : ℝ) : ℂ) := by
    rw [Work.Diff.STE.B3Data.Rper]
    exact tsum_eq_sum (s := cubeIdx E) (hzero (u m t))
  have h2 : D.Rper i (u m t') a b x
      = ∑ m' ∈ cubeIdx E, ((D.R i (u m t') a b (x + iVec m') : ℝ) : ℂ) := by
    rw [Work.Diff.STE.B3Data.Rper]
    exact tsum_eq_sum (s := cubeIdx E) (hzero (u m t'))
  rw [h1, h2, Finset.sum_sub_distrib]

/-- **Lipschitz bound for the periodised components on the unit cube.** -/
lemma Rper_norm_sub_le
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (C τ : ℝ) (hC : 0 ≤ C) (u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hode : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) τ → ∀ (x : M) (u₀ v : TangentSpace I x),
      ∃ R : ℝ, HasDerivWithinAt (fun s : ℝ => u m s x u₀ v) R (Set.Icc (0 : ℝ) τ) t ∧
        |R| ≤ C * Real.sqrt (g₀.inner x u₀ u₀) * Real.sqrt (g₀.inner x v v))
    (Cdens : ℝ)
    (hdens : ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ D.σ i → D.dens i z ≤ Cdens)
    (m : ℕ) {t t' : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) τ) (ht' : t' ∈ Set.Icc (0 : ℝ) τ)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E))
    (x : Fin (Module.finrank ℝ E) → ℝ) (hx : x ∈ unitCube (ι := Fin (Module.finrank ℝ E))) :
    ‖D.Rper i (u m t) a b x - D.Rper i (u m t') a b x‖
      ≤ (2 : ℝ) ^ Module.finrank ℝ E * (Real.sqrt Cdens * C) * |t - t'| := by
  have hd : ∀ m' : Fin (Module.finrank ℝ E) → ℤ,
      ‖((D.R i (u m t) a b (x + iVec m') : ℝ) : ℂ)
        - ((D.R i (u m t') a b (x + iVec m') : ℝ) : ℂ)‖
        = |D.R i (u m t) a b (x + iVec m') - D.R i (u m t') a b (x + iVec m')| := by
    intro m'
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hcard : ((cubeIdx E).card : ℝ) ≤ (2 : ℝ) ^ Module.finrank ℝ E := by
    rw [cubeIdx_card E, Nat.cast_pow, Nat.cast_ofNat]
  have hsum := Rper_sub_eq_finset_sum D u m t t' i a b x hx
  calc ‖D.Rper i (u m t) a b x - D.Rper i (u m t') a b x‖
      = ‖∑ m' ∈ cubeIdx E, (((D.R i (u m t) a b (x + iVec m') : ℝ) : ℂ)
            - ((D.R i (u m t') a b (x + iVec m') : ℝ) : ℂ))‖ := by rw [hsum]
    _ ≤ ∑ m' ∈ cubeIdx E, ‖(((D.R i (u m t) a b (x + iVec m') : ℝ) : ℂ)
            - ((D.R i (u m t') a b (x + iVec m') : ℝ) : ℂ))‖ := norm_sum_le _ _
    _ = ∑ m' ∈ cubeIdx E,
          |D.R i (u m t) a b (x + iVec m') - D.R i (u m t') a b (x + iVec m')| :=
        Finset.sum_congr rfl fun m' _ => hd m'
    _ ≤ ∑ _m' ∈ cubeIdx E, (Real.sqrt Cdens * C * |t - t'|) :=
        Finset.sum_le_sum fun m' _ =>
          abs_R_sub_le D C τ hC u hode Cdens hdens m ht ht' i a b (x + iVec m')
    _ = ((cubeIdx E).card : ℝ) * (Real.sqrt Cdens * C * |t - t'|) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ Module.finrank ℝ E * (Real.sqrt Cdens * C * |t - t'|) :=
        mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hC) (abs_nonneg _))
    _ = (2 : ℝ) ^ Module.finrank ℝ E * (Real.sqrt Cdens * C) * |t - t'| := by ring

/-- **A continuous pair which agrees within `Cv` on the unit cube has Fourier coefficients within
`Cv`.**  The characters have modulus one, so the sup-norm bound passes to the integral, and the
volume of `(0,1]ⁿ` is one. -/
lemma norm_fourierCoeff_sub_le_of_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F G : (ι → ℝ) → ℂ} (hF : Continuous F) (hG : Continuous G) {Cv : ℝ}
    (h : ∀ x ∈ unitCube (ι := ι), ‖F x - G x‖ ≤ Cv) (k : ι → ℤ) :
    ‖fourierCoeff F k - fourierCoeff G k‖ ≤ Cv := by
  have iF : Integrable (fun x => fourierExp (-k) x * F x)
      (volume.restrict (unitCube (ι := ι))) :=
    integrableOn_unitCube_of_continuous ((continuous_fourierExp (-k)).mul hF)
  have iG : Integrable (fun x => fourierExp (-k) x * G x)
      (volume.restrict (unitCube (ι := ι))) :=
    integrableOn_unitCube_of_continuous ((continuous_fourierExp (-k)).mul hG)
  have hdiff : fourierCoeff F k - fourierCoeff G k
      = ∫ x in unitCube (ι := ι), fourierExp (-k) x * (F x - G x) := by
    rw [fourierCoeff, fourierCoeff, ← MeasureTheory.integral_sub iF iG]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hμ : (volume : Measure (ι → ℝ)) (unitCube (ι := ι)) < ⊤ := by
    rw [volume_unitCube]; exact ENNReal.one_lt_top
  have hb : ‖∫ x in unitCube (ι := ι), fourierExp (-k) x * (F x - G x)‖
      ≤ Cv * ((volume : Measure (ι → ℝ)) (unitCube (ι := ι))).toReal :=
    MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (f := fun x : ι → ℝ => fourierExp (-k) x * (F x - G x)) hμ
      (fun x hx => by rw [norm_mul, tpd_norm_fourierExp, one_mul]; exact h x hx)
  calc ‖fourierCoeff F k - fourierCoeff G k‖
      = ‖∫ x in unitCube (ι := ι), fourierExp (-k) x * (F x - G x)‖ := by rw [hdiff]
    _ ≤ Cv * ((volume : Measure (ι → ℝ)) (unitCube (ι := ι))).toReal := hb
    _ = Cv := by rw [volume_unitCube, ENNReal.toReal_one, mul_one]

end Helpers

theorem coeffFun_lipschitz_of_ode
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (τ C : ℝ) (hτ : 0 < τ) (hC : 0 ≤ C)
    (u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hCD : ∀ (m : ℕ) (t : ℝ), Work.Diff.STE.D.ChartData (I := I) (M := M) (u m t))
    (hode : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) τ → ∀ (x : M) (u₀ v : TangentSpace I x),
      ∃ R : ℝ, HasDerivWithinAt (fun s : ℝ => u m s x u₀ v) R (Set.Icc (0 : ℝ) τ) t ∧
        |R| ≤ C * Real.sqrt (g₀.inner x u₀ u₀) * Real.sqrt (g₀.inner x v v)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (m : ℕ) (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ), ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ t' ∈ Set.Ico (0 : ℝ) τ,
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ
        - Work.Diff.STE.fourierCoeff (D.Rper i (u m t') a b) μ‖ ≤ L * |t - t'| := by
  classical
  obtain ⟨_c, Cdens, _hc, _hCdens, hdens⟩ := Work.Diff.STE.B3.dens_bound_sigma D
  refine ⟨(2 : ℝ) ^ Module.finrank ℝ E * (Real.sqrt Cdens * C), ?_, ?_⟩
  · exact mul_nonneg (pow_nonneg (by norm_num) _)
      (mul_nonneg (Real.sqrt_nonneg _) hC)
  · intro m i a b μ t ht t' ht'
    have htI : t ∈ Set.Icc (0 : ℝ) τ := ⟨ht.1, le_of_lt ht.2⟩
    have htI' : t' ∈ Set.Icc (0 : ℝ) τ := ⟨ht'.1, le_of_lt ht'.2⟩
    have hct : Continuous (D.Rper i (u m t) a b) :=
      ((Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i (u m t) a b
        (Work.Diff.STE.B3.R_contDiff_of_chartData D (u m t) (hCD m t) i a b)).1).continuous
    have hct' : Continuous (D.Rper i (u m t') a b) :=
      ((Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i (u m t') a b
        (Work.Diff.STE.B3.R_contDiff_of_chartData D (u m t') (hCD m t') i a b)).1).continuous
    exact norm_fourierCoeff_sub_le_of_bound (Cv :=
        (2 : ℝ) ^ Module.finrank ℝ E * (Real.sqrt Cdens * C) * |t - t'|) hct hct'
      (fun x hx => Rper_norm_sub_le D C τ hC u hode Cdens
        (fun i z hz => (hdens i z hz).2) m htI htI' i a b x hx) μ

end Work.Diff.STE.Lead
