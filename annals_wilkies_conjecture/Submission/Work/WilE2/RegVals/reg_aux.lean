import Mathlib
import Submission.Work.WilE2.RegVals.Basic

open MeasureTheory
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Work.WilE2.RegVals

/-! ## 1. Auxiliary lemmas -/

/-- **Fubini**, with a real first factor. -/
theorem volume_eq_zero_of_slices_null_real {s : ℕ} {K : Set (ℝ × (Fin s → ℝ))}
    (hK : MeasurableSet K) (h : ∀ a : ℝ, volume {b | (a, b) ∈ K} = 0) : volume K = 0 := by
  have h' : ∀ a : ℝ, volume (Prod.mk a ⁻¹' K) = 0 := fun a => h a
  rw [Measure.volume_eq_prod ℝ (Fin s → ℝ), Measure.prod_apply hK]
  simp [h']

/-- `Fin.insertNth` reassembles a function from the value at `p` and the values off `p`. -/
theorem insertNth_self {n : ℕ} {α : Type*} (p : Fin (n+1)) (y : Fin (n+1) → α) :
    Fin.insertNth (α := fun _ => α) p (y p) (fun l => y (p.succAbove l)) = y := by
  funext m
  by_cases hm : m = p
  · subst hm; rw [Fin.insertNth_apply_same]
  · obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hm
    rw [← hz, Fin.insertNth_apply_succAbove]

/-- `Fin.insertNth` is injective in both arguments. -/
theorem insertNth_inj {n : ℕ} (p : Fin (n+1)) (a b : ℝ) (u v : Fin n → ℝ)
    (h : Fin.insertNth (α := fun _ => ℝ) p a u = Fin.insertNth (α := fun _ => ℝ) p b v) :
    a = b ∧ u = v := by
  constructor
  · have hh := congrFun h p
    simpa [Fin.insertNth_apply_same] using hh
  · funext l
    have hh := congrFun h (p.succAbove l)
    simpa [Fin.insertNth_apply_succAbove] using hh

/-- If `T : E × ℝ → F` is linear then `p ↦ (T p, p.2)` is surjective exactly when
`T ∘ inl` is. -/
theorem surjective_prod_snd_iff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E × ℝ →L[ℝ] F) :
    Function.Surjective (fun p : E × ℝ => (T p, p.2)) ↔
      Function.Surjective (T.comp (ContinuousLinearMap.inl ℝ E ℝ)) := by
  constructor
  · intro h y
    obtain ⟨p, hp⟩ := h (y, 0)
    have h1 : p.2 = 0 := congrArg Prod.snd hp
    have h2 : T p = y := congrArg Prod.fst hp
    refine ⟨p.1, ?_⟩
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    rw [show (p.1, (0:ℝ)) = p from Prod.ext rfl h1.symm]
    exact h2
  · intro h y
    obtain ⟨p1, p2⟩ := y
    obtain ⟨e, he⟩ := h (p1 - T (0, p2))
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] at he
    refine ⟨(e, p2), ?_⟩
    have hsum : T (e, p2) = T (e, 0) + T (0, p2) := by
      rw [show ((e, p2) : E × ℝ) = (e, 0) + (0, p2) from by ext <;> simp]
      rw [map_add]
    change (T (e, p2), p2) = (p1, p2)
    rw [hsum, he]
    simp

/-- The derivative of a slice is the derivative composed with the inclusion. -/
theorem fderiv_slice {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (φ : E × ℝ → F) (u : E) (c : ℝ)
    (h : DifferentiableAt ℝ φ (u, c)) :
    fderiv ℝ (fun u' => φ (u', c)) u
      = (fderiv ℝ φ (u, c)).comp (ContinuousLinearMap.inl ℝ E ℝ) := by
  have h1 : HasFDerivAt (fun u' : E => ((u', c) : E × ℝ)) (ContinuousLinearMap.inl ℝ E ℝ) u := by
    have hfun : (fun u' : E => ((u', c) : E × ℝ))
        = fun u' : E => ((u', (0:ℝ)) : E × ℝ) + ((0:E), c) := by
      funext u'; ext <;> simp
    rw [hfun]
    have h2 := HasFDerivAt.add ((ContinuousLinearMap.inl ℝ E ℝ).hasFDerivAt)
      (hasFDerivAt_const ((0:E), c) u)
    rw [show ((ContinuousLinearMap.inl ℝ E ℝ) + 0 : E →L[ℝ] E × ℝ)
        = ContinuousLinearMap.inl ℝ E ℝ from add_zero _] at h2
    exact h2
  have h2 : (fun u' : E => φ (u', c)) = φ ∘ (fun u' : E => ((u', c) : E × ℝ)) := rfl
  rw [h2, fderiv_comp u h h1.differentiableAt, h1.fderiv]

/-- An open set between a compact set and an open set containing it. -/
theorem exists_open_between {E : Type*} [PseudoMetricSpace E] {K W : Set E} (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W) : ∃ V, IsOpen V ∧ K ⊆ V ∧ closure V ⊆ W := by
  obtain ⟨d, hd0, hd⟩ := hK.exists_cthickening_subset_open hW hKW
  refine ⟨Metric.thickening (d/2) K, Metric.isOpen_thickening, ?_, ?_⟩
  · intro x hx
    exact Metric.mem_thickening_iff.mpr ⟨x, hx, by rw [dist_self]; linarith⟩
  · refine (Metric.closure_thickening_subset_cthickening (d/2) K).trans ?_
    exact (Metric.cthickening_mono (by linarith) K).trans hd

/-- A smooth cutoff function equal to `1` near `K` whose (topological) support lies in `W`. -/
theorem exists_smooth_cutoff_supp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [T2Space E] [NormalSpace E] [SigmaCompactSpace E]
    {K W : Set E} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ χ : E → ℝ, ContDiff ℝ 2 χ ∧ (∀ x ∈ K, χ =ᶠ[𝓝 x] 1) ∧ tsupport χ ⊆ W := by
  obtain ⟨V, hVo, hKV, hVW⟩ := exists_open_between hK hW hKW
  have hKV' : K ⊆ interior V := by rwa [hVo.interior_eq]
  obtain ⟨f, hf1, hf0, _⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (modelWithCornersSelf ℝ E)
      (n := (⊤ : ℕ∞)) hK.isClosed hKV'
  refine ⟨f, ?_, ?_, ?_⟩
  · have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f : E → ℝ) :=
      contMDiff_iff_contDiff.mp f.contMDiff
    exact hf.of_le (WithTop.coe_le_coe.mpr le_top)
  · intro x hx
    have hle : 𝓝 x ≤ 𝓝ˢ K := by
      have h2 := nhdsSet_le_iff.mpr (Set.singleton_subset_iff.mpr hx)
      rwa [nhdsSet_singleton] at h2
    exact Filter.Eventually.filter_mono hle hf1
  · refine (closure_mono ?_).trans hVW
    intro x hx
    by_contra hxV
    exact hx (hf0 x hxV)

/-- From `T ≠ 0` extract coordinates on which `T` does not vanish. -/
theorem exists_coord {n : ℕ} (T : (Fin n → ℝ) →L[ℝ] (Fin (n-1) → ℝ)) (hT : T ≠ 0) :
    ∃ (i : Fin (n-1)) (j : Fin n), T (Pi.single j (1:ℝ)) i ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hT
  ext v m
  change T v m = 0
  have hv : (∑ l : Fin n, v l • (Pi.single l (1:ℝ) : Fin n → ℝ)) = v := by
    funext m
    rw [Finset.sum_apply, Finset.sum_eq_single m]
    · simp
    · intro l _ hl
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hl), smul_zero]
    · intro hm; exact absurd (Finset.mem_univ m) hm
  have hstep : T v m = (T (∑ l : Fin n, v l • (Pi.single l (1:ℝ) : Fin n → ℝ))) m := by
    rw [hv]
  rw [hstep, map_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [map_smul, Pi.smul_apply, h m l, smul_zero]


end Work.WilE2.RegVals
