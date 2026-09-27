import Mathlib
import Submission.Work.Whitney.CutPush.projection_family_of_sheet
import Submission.Work.Whitney.CutPush.projection_collapse_clm
import Submission.Work.Whitney.CutPush.section_family
import Submission.Work.Whitney.CutPush.bump_on_compact
import Submission.Work.Whitney.CutPush.compact_between

/-!
# The localised projection family of the sheet (`NOTES_STATE_S59.md` §12.3 item 2)

Steps 7–8 of §7.2 with **no outer piece**: the per-piece projection families `Q i` are averaged with a
partition of unity subordinate to `{O i}` and *renormalised* by `σ t = Σ i, ρ i t`, so that the weights
sum to `1` on the whole open set `W := {χ = 1}` (where `χ` is a bump supported inside `{σ > 0}`).  This
is what makes the average a projection by the collapse, while the cut-off `χ` makes the family globally
smooth.  No idempotence is claimed off `W`: by §12.2 of the notes a globally idempotent family built
from a partition of unity plus one fixed outer projection cannot exist, `ℝ` being connected.
-/

namespace Work.Whitney.CutPush

open scoped Manifold ContDiff
open Topology

/-- **A smooth partition of unity on an arbitrary closed interval.** -/
theorem exists_smooth_partitionOfUnity_Icc {ι : Type*} [Fintype ι] (a b : ℝ)
    (J : ι → Set ℝ) (hJ : ∀ i, IsOpen (J i)) (hcov : Set.Icc a b ⊆ ⋃ i, J i) :
    ∃ ρ : ι → ℝ → ℝ, (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ i)) ∧
      (∀ i t, 0 ≤ ρ i t) ∧
      (∀ i, tsupport (ρ i) ⊆ J i) ∧
      (∀ t ∈ Set.Icc a b, ∑ i, ρ i t = 1) := by
  classical
  obtain ⟨F, hF⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, ℝ)) (s := Set.Icc a b) isClosed_Icc J hJ hcov
  refine ⟨fun i t => F i t, fun i => contMDiff_iff_contDiff.mp (F i).contMDiff,
    fun i t => F.nonneg i t, fun i => hF i, fun t ht => ?_⟩
  have h := F.sum_eq_one ht
  rwa [finsum_eq_sum_of_fintype] at h



/-- **The localised family of projections of the sheet.**  On an open `W ⊇ Icc a b` there is a smooth
family `P` of orthogonal projections with `range (P t) = range (mfderiv F (δ t))`.  It is built from
the per-piece families `Q i` (`exists_local_projections_of_sheet`) by the *renormalised* average
`P t = Σ i, w i t • Q i t`, `w i t = χ t * (ρ i t * (σ t)⁻¹)`, where `σ t = Σ i, ρ i t` and `χ` is a
smooth cut-off equal to `1` on `W` and supported where `σ ≠ 0`.  On `W` the weights sum to `1`, so the
CLM collapse (`sum_smul_projection_eq_of_common_range_clm`) identifies `P t` with the (single active)
correct piece `Q i₀ t`. -/
theorem exists_localised_projection_family {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [LocallyCompactSpace M]
    (F : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hF : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hFinj : ∀ y : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F y))
    {δ : ℝ → M}
    (hδ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) δ)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ (P : ℝ → EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)))
      (W : Set ℝ),
      IsOpen W ∧ Set.Icc a b ⊆ W ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin (2 * n)) => P p.1 p.2) ∧
      (∀ t ∈ W, P t * P t = P t) ∧
      (∀ t ∈ W, ∀ x y : EuclideanSpace ℝ (Fin (2 * n)),
        inner ℝ (P t x) y = inner ℝ x (P t y)) ∧
      (∀ t ∈ W, LinearMap.range (P t : EuclideanSpace ℝ (Fin (2 * n)) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin (2 * n)))
        = LinearMap.range ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F (δ t)
            : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))).toLinearMap)) := by
  classical
  obtain ⟨ι, hιfin, O, Q, hOo, hcov, hQsm, hQidem, hQadj, hQrng⟩ :=
    exists_local_projections_of_sheet F hF hFinj hδ a b hab
  haveI := hιfin
  obtain ⟨ρ, hρc, _hρnn, hρsupp, hρsum⟩ := exists_smooth_partitionOfUnity_Icc a b O hOo hcov
  set σ : ℝ → ℝ := fun t => ∑ i, ρ i t with hσ
  have hσc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ := by
    rw [hσ]
    exact ContDiff.sum (fun i _ => hρc i)
  have hσ1 : ∀ t ∈ Set.Icc a b, σ t = 1 := by
    intro t ht
    rw [hσ]
    exact hρsum t ht
  set W : Set ℝ := {t : ℝ | (1 : ℝ) / 2 < σ t} with hW
  have hWo : IsOpen W := isOpen_lt continuous_const hσc.continuous
  have hWab : Set.Icc a b ⊆ W := fun t ht => by
    rw [hW]
    simp only [Set.mem_setOf_eq]
    rw [hσ1 t ht]
    norm_num
  set χ : ℝ → ℝ := fun t => Real.smoothTransition (4 * (σ t - 1 / 4)) with hχ
  have hχc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := by
    rw [hχ]
    exact Real.smoothTransition.contDiff.comp
      (contDiff_const.mul (hσc.sub contDiff_const))
  have hχ1 : ∀ t ∈ W, χ t = 1 := by
    intro t ht
    have h1 : 1 ≤ 4 * (σ t - 1 / 4) := by
      rw [hW] at ht
      simp only [Set.mem_setOf_eq] at ht
      linarith
    rw [hχ]
    exact Real.smoothTransition.one_of_one_le h1
  have hχsupp : tsupport χ ⊆ {t : ℝ | σ t ≠ 0} := by
    have hsub : Function.support χ ⊆ {t : ℝ | (1 : ℝ) / 4 < σ t} := by
      intro t ht
      simp only [Function.mem_support] at ht
      by_contra h
      have hle : 4 * (σ t - 1 / 4) ≤ 0 := by
        have h4 : σ t ≤ 1 / 4 := le_of_not_gt h
        linarith
      exact ht (by rw [hχ]; exact Real.smoothTransition.zero_of_nonpos hle)
    have hclosed : IsClosed {t : ℝ | (1 : ℝ) / 4 ≤ σ t} :=
      isClosed_le continuous_const hσc.continuous
    calc tsupport χ = closure (Function.support χ) := rfl
      _ ⊆ closure {t : ℝ | (1 : ℝ) / 4 < σ t} := closure_mono hsub
      _ ⊆ {t : ℝ | (1 : ℝ) / 4 ≤ σ t} :=
          closure_minimal (fun t ht => by simp only [Set.mem_setOf_eq] at ht ⊢; linarith) hclosed
      _ ⊆ {t : ℝ | σ t ≠ 0} := fun t ht => by
          simp only [Set.mem_setOf_eq] at ht ⊢
          linarith
  have hUo : IsOpen {t : ℝ | σ t ≠ 0} :=
    (isClosed_singleton.preimage hσc.continuous).isOpen_compl
  set w : ι → ℝ → ℝ := fun i t => χ t * (ρ i t * (σ t)⁻¹) with hw
  have hwc : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (w i) := by
    intro i
    have hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => ρ i t * (σ t)⁻¹) {t : ℝ | σ t ≠ 0} :=
      (hρc i).contDiffOn.mul (hσc.contDiffOn.inv (fun t ht => ht))
    have h := contDiff_bump_mul_contDiffOn hUo hf hχc hχsupp
    simpa only [hw, smul_eq_mul] using h
  have hwsupp : ∀ i, tsupport (w i) ⊆ O i := by
    intro i
    have h1 : Function.support (w i) ⊆ Function.support (ρ i) := by
      intro t ht
      simp only [Function.mem_support] at ht ⊢
      intro h0
      exact ht (by simp only [hw]; rw [h0]; ring)
    calc tsupport (w i) = closure (Function.support (w i)) := rfl
      _ ⊆ closure (Function.support (ρ i)) := closure_mono h1
      _ = tsupport (ρ i) := rfl
      _ ⊆ O i := hρsupp i
  have htermsm : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => w i t • Q i t) := fun i =>
    contDiff_bump_mul_contDiffOn (hOo i) (hQsm i) (hwc i) (hwsupp i)
  set P : ℝ → EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
    fun t => ∑ i, w i t • Q i t with hP
  have hPcur : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P := by
    rw [hP]
    exact ContDiff.sum (fun i _ => htermsm i)
  have hPun : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin (2 * n)) => P p.1 p.2) :=
    (hPcur.comp contDiff_fst).clm_apply contDiff_snd
  have hkey : ∀ t ∈ W, ∃ i₀ : ι, (∑ i, w i t • Q i t) = Q i₀ t ∧ t ∈ O i₀ := by
    intro t ht
    have hχt : χ t = 1 := hχ1 t ht
    have hσne : σ t ≠ 0 :=
      hχsupp (subset_closure (Function.mem_support.mpr (by rw [hχt]; exact one_ne_zero)))
    have hsum : ∑ i, w i t = 1 := by
      have h1 : ∀ i, w i t = (χ t * (σ t)⁻¹) * ρ i t := by
        intro i
        simp only [hw]
        ring
      calc ∑ i, w i t = ∑ i, (χ t * (σ t)⁻¹) * ρ i t :=
            Finset.sum_congr rfl (fun i _ => h1 i)
        _ = (χ t * (σ t)⁻¹) * ∑ i, ρ i t := (Finset.mul_sum _ _ _).symm
        _ = (χ t * (σ t)⁻¹) * σ t := by rw [hσ]
        _ = 1 := by rw [hχt]; field_simp
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ : ι, w i₀ t ≠ 0 := by
      by_contra h
      push_neg at h
      have h0 : ∑ i, w i t = 0 := Finset.sum_eq_zero (fun i _ => h i)
      rw [hsum] at h0
      exact one_ne_zero h0
    have hact : ∀ i, w i t ≠ 0 → t ∈ O i := fun i hi =>
      hwsupp i (subset_closure (Function.mem_support.mpr hi))
    refine ⟨i₀, ?_, hact i₀ hi₀⟩
    exact sum_smul_projection_eq_of_common_range_clm (fun i => Q i t) (fun i => w i t) hsum i₀ hi₀
      (fun i hi => by
        refine ContinuousLinearMap.ext (fun x => ?_)
        rw [ContinuousLinearMap.comp_apply]
        exact congrArg (fun f : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
          EuclideanSpace ℝ (Fin (2 * n)) => f x) (hQidem i t (hact i hi)))
      (fun i hi => hQadj i t (hact i hi))
      (fun i hi => (hQrng i t (hact i hi)).trans (hQrng i₀ t (hact i₀ hi₀)).symm)
  refine ⟨P, W, hWo, hWab, hPun, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨i₀, heq, hmem⟩ := hkey t ht
    rw [hP]
    simp only []
    rw [heq]
    exact hQidem i₀ t hmem
  · intro t ht x y
    obtain ⟨i₀, heq, hmem⟩ := hkey t ht
    rw [hP]
    simp only []
    rw [heq]
    exact hQadj i₀ t hmem x y
  · intro t ht
    obtain ⟨i₀, heq, hmem⟩ := hkey t ht
    rw [hP]
    simp only []
    rw [heq]
    exact hQrng i₀ t hmem

end Work.Whitney.CutPush
