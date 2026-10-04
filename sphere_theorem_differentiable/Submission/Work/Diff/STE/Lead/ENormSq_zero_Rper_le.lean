import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.B3.dens_bound_sigma
import Submission.Work.Diff.STE.B3.Pointwise
import Submission.Work.Diff.STE.B3.Periodic1_iVec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `L²` energy of a periodised component is bounded by the pointwise bound of the section

For Layer B3 data `D` (`B3Data ι₀ g₀`) and a section `h : Bil` which is pointwise bounded by `K` in
the `g₀`-sense,

`|h y u v| ≤ K √(g₀.inner y u u) √(g₀.inner y v v)`,

the `L²` energy `ENormSq 0 (D.Rper i h a b) = ∫_{unitCube} ‖D.Rper i h a b z‖² dz` of every
periodised localised component is bounded by `C K²`, with `C` depending only on `D`.

## Route

* On the support of the localised weight `psi i = χ i · ζ i ∘ pt i` the chart `i` is genuine, the
  flat coordinate has norm `< σ i` and the frame `e i` is `g₀`-orthonormal (`B3/BPairDefs.lean`).
  Hence every value of the localised component `D.R i h a b` is bounded by `√C · K`, where `C` is
  the uniform upper bound for the volume density on the `σ`-balls (`B3/dens_bound_sigma.lean`).
* The support of `D.R i h a b` lies in the *open* centred unit cube, so at most one lattice
  translate contributes to the periodisation `D.Rper i h a b = ∑' m, D.R i h a b (· + m)`; on the
  fundamental cube the periodisation is the component itself (`B3/Recon.lean`, `B3Data.Rper_eq_R`),
  and `periodization_periodic`/`Periodic1_iVec` move an arbitrary point into that cube.
* Finally `∫_{unitCube} ‖f‖² ≤ M²` for any `f` with `‖f‖ ≤ M` (the cube has volume `1`): the norm
  bound `norm_setIntegral_le_of_norm_le_const_ae` and nonnegativity of the integrand apply without
  any measurability or integrability hypothesis on `f`.
-/

namespace Work.Diff.STE.Lead

open MeasureTheory
open scoped BigOperators

/-- The norm of a real number seen in `ℂ` is its absolute value. -/
private lemma norm_ofReal_cast' (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by
  have h : ‖((x : ℝ) : ℂ)‖ ^ 2 = x ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  calc ‖((x : ℝ) : ℂ)‖ = Real.sqrt (‖((x : ℝ) : ℂ)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (x ^ 2) := by rw [h]
    _ = |x| := Real.sqrt_sq_eq_abs x

/-- The periodisation `D.Rper i h a b` is `1`-periodic in every coordinate. -/
private lemma lead_periodic_Rper
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.Periodic1 (D.Rper i h a b) :=
  Work.Diff.STE.periodization_periodic (fun z : Fin (Module.finrank ℝ E) → ℝ =>
    ((D.R i h a b z : ℝ) : ℂ))

/-- **The pointwise bound on the localised component.**  If the section `h` is bounded by `K` in the
`g₀`-sense and the volume density of chart `i` is at most `C` on its `σ`-ball, then every value of
the localised component `D.R i h a b` is bounded by `√C · K`. -/
private lemma lead_R_abs_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) {K C : ℝ} (hK : 0 ≤ K)
    (hdens : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ D.σ i → D.dens i z ≤ C)
    (hbound : ∀ (y : M) (u' v' : TangentSpace I y),
      |h y u' v'| ≤ K * Real.sqrt (g₀.inner y u' u') * Real.sqrt (g₀.inner y v' v')) :
    ∀ w : Fin (Module.finrank ℝ E) → ℝ, |D.R i h a b w| ≤ Real.sqrt C * K := by
  intro w
  by_cases hpsi : D.psi i w = 0
  · have hz : D.R i h a b w = 0 := by
      simp only [Work.Diff.STE.B3Data.R, hpsi, zero_mul]
    rw [hz, abs_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) hK
  · have hON : Submission.Diff.IsONFrame g₀ (D.pt i w) (fun a => D.e i a (D.pt i w)) :=
      Work.Diff.STE.B3.isONFrame_of_psi_ne_zero D hpsi
    have hσ : ‖w‖ < D.σ i := Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero D hpsi
    have hpsiz : D.psi i w = D.ζ i (D.pt i w) :=
      Work.Diff.STE.B3.psi_eq_zeta_of_psi_ne_zero D hpsi
    have hζle : D.ζ i (D.pt i w) ≤ 1 := by
      have hsq : (D.ζ i (D.pt i w)) ^ 2 ≤ 1 := by
        have h1 : (D.ζ i (D.pt i w)) ^ 2 ≤ ∑ j : ι₀, (D.ζ j (D.pt i w)) ^ 2 :=
          Finset.single_le_sum (s := Finset.univ)
            (f := fun j : ι₀ => (D.ζ j (D.pt i w)) ^ 2) (a := i)
            (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        rwa [D.hζsq (D.pt i w)] at h1
      nlinarith [hsq, D.hζnn i (D.pt i w), sq_nonneg (D.ζ i (D.pt i w))]
    have hsd : Real.sqrt (D.dens i w) ≤ Real.sqrt C :=
      Real.sqrt_le_sqrt (hdens w (le_of_lt hσ))
    have hmat : |D.mat i h a b w| ≤ K := by
      have h1 := hbound (D.pt i w) (D.e i a (D.pt i w)) (D.e i b (D.pt i w))
      have ha : g₀.inner (D.pt i w) (D.e i a (D.pt i w)) (D.e i a (D.pt i w)) = 1 := by
        simpa using hON a a
      have hb : g₀.inner (D.pt i w) (D.e i b (D.pt i w)) (D.e i b (D.pt i w)) = 1 := by
        simpa using hON b b
      rw [ha, hb] at h1
      simpa only [Work.Diff.STE.B3Data.mat, Real.sqrt_one, mul_one] using h1
    have hpsile : |D.psi i w| ≤ 1 := by
      rw [hpsiz, abs_of_nonneg (D.hζnn i (D.pt i w))]
      exact hζle
    calc |D.R i h a b w|
        = |D.psi i w| * Real.sqrt (D.dens i w) * |D.mat i h a b w| := by
          show |D.psi i w * Real.sqrt (D.dens i w) * D.mat i h a b w| = _
          rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (D.dens i w))]
      _ ≤ 1 * Real.sqrt C * K :=
          mul_le_mul (mul_le_mul hpsile hsd (Real.sqrt_nonneg _) zero_le_one) hmat
            (abs_nonneg _) (mul_nonneg zero_le_one (Real.sqrt_nonneg _))
      _ = Real.sqrt C * K := by ring

/-- **From the component to its periodisation.**  If every value of the localised component is
bounded by `L ≥ 0`, then every value of the periodisation `D.Rper i h a b` is bounded by `L`: the
support of the component lies in the open centred unit cube, so at most one lattice translate
contributes, and the periodisation is invariant under integer translations. -/
private lemma lead_Rper_abs_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) {L : ℝ} (hL : 0 ≤ L)
    (hR : ∀ w : Fin (Module.finrank ℝ E) → ℝ, |D.R i h a b w| ≤ L) :
    ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖D.Rper i h a b z‖ ≤ L := by
  have hper : Work.Diff.STE.Periodic1 (D.Rper i h a b) := lead_periodic_Rper D i h a b
  intro z
  by_cases hcase : ∃ m : Fin (Module.finrank ℝ E) → ℤ,
      ∀ j, (z + Work.Diff.STE.iVec m) j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)
  · obtain ⟨m, hm⟩ := hcase
    have h1 : D.Rper i h a b z = D.Rper i h a b (z + Work.Diff.STE.iVec m) :=
      (Work.Diff.STE.B3.Periodic1_iVec hper m z).symm
    rw [h1, D.Rper_eq_R i h a b hm, norm_ofReal_cast']
    exact hR (z + Work.Diff.STE.iVec m)
  · have hterm : ∀ m : Fin (Module.finrank ℝ E) → ℤ,
        ((D.R i h a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ) = 0 := by
      intro m
      have hR0 : D.R i h a b (z + Work.Diff.STE.iVec m) = 0 := by
        by_contra hne
        exact hcase ⟨m, fun j => D.R_support i h a b
          (Function.mem_support.mpr hne) j (Set.mem_univ j)⟩
      rw [hR0, Complex.ofReal_zero]
    have hz0 : D.Rper i h a b z = 0 := by
      show (∑' m : Fin (Module.finrank ℝ E) → ℤ,
        ((D.R i h a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ)) = 0
      simp only [hterm]
      exact tsum_zero
    rw [hz0, norm_zero]
    exact hL

/-- **The `L²` bound from a pointwise bound.**  If `‖u z‖ ≤ M` for every `z`, then
`ENormSq 0 u = ∫_{unitCube} ‖u z‖² dz ≤ M²` (the unit cube has volume `1`).  No measurability or
integrability hypothesis is needed: the norm estimate `norm_setIntegral_le_of_norm_le_const_ae`
holds without any, and the integrand is nonnegative. -/
private lemma lead_ENormSq_zero_le {n : ℕ} (u : (Fin n → ℝ) → ℂ) {M : ℝ} (_hM : 0 ≤ M)
    (hu : ∀ z, ‖u z‖ ≤ M) : Work.Diff.STE.ENormSq 0 u ≤ M ^ 2 := by
  have hvol : (MeasureTheory.volume : Measure (Fin n → ℝ))
      (Work.Diff.STE.unitCube (ι := Fin n)) = 1 := by
    rw [Work.Diff.STE.unitCube, Real.volume_pi_Ioc]
    simp
  have hreal : MeasureTheory.volume.real (Work.Diff.STE.unitCube (ι := Fin n)) = 1 := by
    rw [MeasureTheory.Measure.real_def, hvol]
    simp
  rw [Work.Diff.STE.ENormSq_zero]
  have habs : |∫ z in Work.Diff.STE.unitCube (ι := Fin n), ‖u z‖ ^ 2| ≤ M ^ 2 := by
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae
      (μ := MeasureTheory.volume) (s := Work.Diff.STE.unitCube (ι := Fin n))
      (f := fun z : Fin n → ℝ => ‖u z‖ ^ 2) (C := M ^ 2)
      (by rw [hvol]; exact ENNReal.one_lt_top)
      (Filter.Eventually.of_forall fun z => by
        have h1 : ‖u z‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hu z) 2
        rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)])
    simpa only [hreal, mul_one, Real.norm_eq_abs] using h
  have hnn : (0 : ℝ) ≤ ∫ z in Work.Diff.STE.unitCube (ι := Fin n), ‖u z‖ ^ 2 :=
    MeasureTheory.setIntegral_nonneg_of_ae (Filter.Eventually.of_forall fun z => by positivity)
  exact (le_abs_self _).trans habs

theorem ENormSq_zero_Rper_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M)) (K : ℝ), 0 ≤ K →
      (∀ (y : M) (u' v' : TangentSpace I y),
        |h y u' v'| ≤ K * Real.sqrt (g₀.inner y u' u') * Real.sqrt (g₀.inner y v' v')) →
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        Work.Diff.STE.ENormSq 0 (D.Rper i h a b) ≤ C * K ^ 2 := by
  obtain ⟨c, C, hc, hCpos, hb⟩ := Work.Diff.STE.B3.dens_bound_sigma D
  refine ⟨C, le_of_lt hCpos, ?_⟩
  intro h K hK hbound i a b
  have hR : ∀ w : Fin (Module.finrank ℝ E) → ℝ, |D.R i h a b w| ≤ Real.sqrt C * K :=
    lead_R_abs_le D h i a b hK (fun z hz => (hb i z hz).2) hbound
  have hRp : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖D.Rper i h a b z‖ ≤ Real.sqrt C * K :=
    lead_Rper_abs_le D h i a b (mul_nonneg (Real.sqrt_nonneg _) hK) hR
  have hfin : Work.Diff.STE.ENormSq 0 (D.Rper i h a b) ≤ (Real.sqrt C * K) ^ 2 :=
    lead_ENormSq_zero_le (D.Rper i h a b) (mul_nonneg (Real.sqrt_nonneg _) hK) hRp
  calc Work.Diff.STE.ENormSq 0 (D.Rper i h a b) ≤ (Real.sqrt C * K) ^ 2 := hfin
    _ = C * K ^ 2 := by rw [mul_pow, Real.sq_sqrt hCpos.le]

end Work.Diff.STE.Lead
