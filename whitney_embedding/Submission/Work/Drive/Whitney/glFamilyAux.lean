import Mathlib
import Submission.Work.Drive.PushDisc.exists_contDiff_path_to_one
import Submission.Work.Embedding.smooth_implicit_function_nhd

/-!
# Auxiliary infrastructure for a global `GL`-valued family with prescribed action

This file provides the analytic foundations for `Work.Drive.Whitney.glFamilyOfVelocity`:

* a scalar bump equal to `1` on `[0,1]` and vanishing off `(-ε, 1+ε)`;
* `IsUnit` of an endomorphism with nonzero determinant;
* invertibility of a smooth family persists on a neighbourhood of `[0,1]`;
* the *base family* `K (s,t) = Γ s * A 0⁻¹ * A (s*t)`: globally smooth, equal to `1` at `s = 0`
  and to `A` at `s = 1`, invertible near the square, with a globally smooth two-sided inverse
  `Kinv` (obtained by cutting `Ring.inverse ∘ K` off along the square).
-/

namespace Work.Drive.Whitney

open scoped ContDiff Topology
open Set Filter

variable {m : ℕ}

/-- A scalar bump equal to `1` on `[0,1]` and vanishing off `(-ε, 1+ε)`. -/
noncomputable def sBump (ε : ℝ) (x : ℝ) : ℝ :=
  Real.smoothTransition ((x + ε) / ε) * Real.smoothTransition ((1 + ε - x) / ε)

lemma sBump_contDiff (ε : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sBump ε) :=
  (Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const ε)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const ε))

lemma sBump_eq_one {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : sBump ε x = 1 := by
  have h1 : 1 ≤ (x + ε) / ε := by rw [le_div_iff₀ hε]; linarith [hx.1]
  have h2 : 1 ≤ (1 + ε - x) / ε := by rw [le_div_iff₀ hε]; linarith [hx.2]
  simp [sBump, Real.smoothTransition.eq_one_iff_one_le.mpr h1,
    Real.smoothTransition.eq_one_iff_one_le.mpr h2]

lemma sBump_eq_zero_of_le {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : x ≤ -ε) : sBump ε x = 0 := by
  have h : (x + ε) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hε)
  simp [sBump, Real.smoothTransition.zero_of_nonpos h]

lemma sBump_eq_zero_of_ge {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 1 + ε ≤ x) : sBump ε x = 0 := by
  have h : (1 + ε - x) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hε)
  simp [sBump, Real.smoothTransition.zero_of_nonpos h]

/-- An endomorphism of `ℝᵐ` with nonzero determinant is a unit. -/
lemma isUnit_of_det_ne_zero {T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (h : LinearMap.det T.toLinearMap ≠ 0) : IsUnit T := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  have hker : T.toLinearMap.ker = ⊥ := by
    by_contra hc
    exact h ((LinearMap.det_eq_zero_iff_ker_ne_bot).mpr hc)
  have hinj : Function.Injective
      (T.toLinearMap : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) := by
    rwa [← LinearMap.ker_eq_bot]
  have hsurj : Function.Surjective
      (T.toLinearMap : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ)
      (V := EuclideanSpace ℝ (Fin m)) (V₂ := EuclideanSpace ℝ (Fin m)) rfl).mp hinj
  exact ⟨fun a b hab => hinj hab, fun b => hsurj b⟩

/-- Invertibility of a smooth family of endomorphisms on `[0,1]` persists on an interval around
`[0,1]`. -/
lemma exists_delta_isUnit (A : ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hdet : ∀ t ∈ Icc (0 : ℝ) 1, 0 < LinearMap.det ((A t).toLinearMap)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ Icc (-δ) (1 + δ), IsUnit (A u) := by
  have hU : IsOpen {S : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) | IsUnit S} := by
    rw [show {S : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) | IsUnit S} =
        {S | S.IsInvertible} from
      Set.ext fun S => (Work.Embedding.isInvertible_iff_isUnit_end S).symm]
    exact Work.Embedding.isOpen_isInvertible_end
  have hopen : IsOpen {u : ℝ | IsUnit (A u)} := hA.continuous.isOpen_preimage _ hU
  have hsub : Icc (0:ℝ) 1 ⊆ {u : ℝ | IsUnit (A u)} := fun u hu =>
    isUnit_of_det_ne_zero (ne_of_gt (hdet u hu))
  obtain ⟨δ, hδpos, hδ⟩ := isCompact_Icc.exists_thickening_subset_open hopen hsub
  refine ⟨δ/2, by linarith, ?_⟩
  intro u hu
  apply hδ
  rw [Metric.mem_thickening_iff]
  by_cases h : 0 ≤ u
  · by_cases h1 : u ≤ 1
    · exact ⟨u, ⟨h, h1⟩, by rw [dist_self]; exact hδpos⟩
    · push Not at h1
      exact ⟨1, ⟨zero_le_one, le_refl 1⟩,
        by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith [hu.2, hδpos]⟩
  · push Not at h
    exact ⟨0, ⟨le_refl 0, zero_le_one⟩,
      by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; linarith [hu.1, hδpos]⟩

set_option synthInstance.maxHeartbeats 200000 in
/-- **The base family.**  A globally smooth family of endomorphisms equal to `1` at `s = 0` and to
`A t` at `s = 1`, invertible near the square, together with a globally smooth two-sided inverse
family. -/
theorem exists_baseFamily (A : ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hdet : ∀ t ∈ Icc (0 : ℝ) 1, 0 < LinearMap.det ((A t).toLinearMap)) :
    ∃ K : ℝ × ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m),
    ∃ Kinv : ℝ × ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Kinv ∧
      (∀ t ∈ Icc (0:ℝ) 1, K (0, t) = 1) ∧
      (∀ t ∈ Icc (0:ℝ) 1, K (1, t) = A t) ∧
      (∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, K (s, t) * Kinv (s, t) = 1) ∧
      (∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, Kinv (s, t) * K (s, t) = 1) := by
  have hA0det : LinearMap.det ((A 0).toLinearMap) ≠ 0 := ne_of_gt (hdet 0 (by norm_num))
  have hA0 : IsUnit (A 0) := isUnit_of_det_ne_zero hA0det
  have hbij : Function.Bijective (A 0) := (ContinuousLinearMap.isUnit_iff_bijective).mp hA0
  let A0e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
    ContinuousLinearEquiv.ofBijective (A 0)
      (by rw [LinearMap.ker_eq_bot]; exact hbij.1)
      (by rw [LinearMap.range_eq_top]; exact hbij.2)
  have hA0e : (A0e : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) = A 0 :=
    ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hpos : 0 < LinearMap.det (A0e : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
    have h : (A0e : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) =
        (A 0).toLinearMap := by rw [← hA0e]; rfl
    rw [h]; exact hdet 0 (by norm_num)
  obtain ⟨Γ, hΓsm, hΓ0, hΓ1⟩ := Work.Drive.PushDisc.exists_contDiff_path_to_one A0e hpos
  have hΓc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun s : ℝ => (Γ s : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) := by
    rw [contDiff_clm_apply_iff]
    intro y
    exact hΓsm.comp (contDiff_id.prodMk contDiff_const)
  let K : ℝ × ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    fun p => (Γ p.1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) *
      (A0e.symm : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) * A (p.1 * p.2)
  have hKsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => (Γ p.1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) :=
      hΓc.comp contDiff_fst
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1 * p.2)) :=
      hA.comp (contDiff_fst.mul contDiff_snd)
    exact (h1.mul contDiff_const).mul h2
  have hK0 : ∀ t : ℝ, K (0, t) = 1 := by
    intro t
    have h : (Γ 0 : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)) = 1 := hΓ0
    have hcoe : (Γ 0 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) = 1 := by
      rw [h]; rfl
    have h2 : (A0e.symm : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) *
        (A 0) = 1 := by
      have hgrp : A0e.symm * A0e = 1 := inv_mul_cancel A0e
      have := congrArg (fun e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m) =>
        (e : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) hgrp
      simpa [hA0e] using this
    show (Γ 0 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) *
      (A0e.symm : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) * A (0 * t) = 1
    rw [zero_mul, hcoe, one_mul]
    exact h2
  have hK1 : ∀ t : ℝ, K (1, t) = A t := by
    intro t
    have hcoe : (Γ 1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) = A 0 := by
      rw [hΓ1]; exact hA0e
    have h2 : (A0e : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) *
        (A0e.symm : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) = 1 := by
      have hgrp : A0e * A0e.symm = 1 := mul_inv_cancel A0e
      have := congrArg (fun e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m) =>
        (e : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) hgrp
      exact this
    show (Γ 1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) *
      (A0e.symm : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) * A (1 * t) = A t
    rw [one_mul, hcoe, ← hA0e, h2, one_mul]
  obtain ⟨δ, hδpos, hδ⟩ := exists_delta_isUnit A hA hdet
  obtain ⟨η, hηpos, hη1, hη2⟩ : ∃ η : ℝ, 0 < η ∧ (1 + η) ^ 2 ≤ 1 + δ ∧ η * (1 + η) ≤ δ := by
    have hposmin : (0:ℝ) < min (δ/4) (1/2) := lt_min (by linarith) (by norm_num)
    refine ⟨min (δ/4) (1/2), hposmin, ?_, ?_⟩
    · have hle1 : min (δ/4) (1/2) ≤ δ/4 := min_le_left _ _
      have hle2 : min (δ/4) (1/2) ≤ 1/2 := min_le_right _ _
      nlinarith [hδpos, hposmin, hle1, hle2]
    · have hle1 : min (δ/4) (1/2) ≤ δ/4 := min_le_left _ _
      have hle2 : min (δ/4) (1/2) ≤ 1/2 := min_le_right _ _
      nlinarith [hδpos, hposmin, hle1, hle2]
  let χ : ℝ × ℝ → ℝ := fun p => sBump η p.1 * sBump η p.2
  have hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ :=
    ((sBump_contDiff η).comp contDiff_fst).mul ((sBump_contDiff η).comp contDiff_snd)
  have hχ1 : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, χ (s,t) = 1 := fun s hs t ht => by
    simp [χ, sBump_eq_one hηpos hs, sBump_eq_one hηpos ht]
  -- the closed box is contained in the unit locus
  have hbox_unit : ∀ p : ℝ × ℝ, p.1 ∈ Icc (-η) (1 + η) → p.2 ∈ Icc (-η) (1 + η) → IsUnit (K p) := by
    intro p hs ht
    have hst : p.1 * p.2 ∈ Icc (-δ) (1 + δ) := by
      refine ⟨?_, ?_⟩
      · rcases le_total 0 p.1 with h1 | h1
        · rcases le_total 0 p.2 with h2 | h2
          · nlinarith [hδpos]
          · nlinarith [hs.2, ht.1, h1, h2, hη2]
        · rcases le_total 0 p.2 with h2 | h2
          · nlinarith [hs.1, ht.2, h1, h2, hη2]
          · nlinarith [hδpos]
      · rcases le_total 0 p.1 with h1 | h1
        · rcases le_total 0 p.2 with h2 | h2
          · nlinarith [hs.2, ht.2, h1, h2, hη1]
          · nlinarith [hδpos]
        · rcases le_total 0 p.2 with h2 | h2
          · nlinarith [hδpos]
          · nlinarith [hs.1, ht.1, h1, h2, hη1]
    have huA : IsUnit (A (p.1 * p.2)) := hδ _ hst
    have huΓ : IsUnit (Γ p.1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) := by
      refine isUnit_iff_exists.mpr ⟨(Γ p.1).symm, ?_, ?_⟩
      · have hgrp : Γ p.1 * (Γ p.1).symm = 1 := mul_inv_cancel _
        simpa using congrArg (fun e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m) =>
          (e : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) hgrp
      · have hgrp : (Γ p.1).symm * Γ p.1 = 1 := inv_mul_cancel _
        simpa using congrArg (fun e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m) =>
          (e : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) hgrp
    have huA0 : IsUnit (A0e.symm : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) := by
      refine isUnit_iff_exists.mpr ⟨A0e, ?_, ?_⟩
      · have hgrp : A0e.symm * A0e = 1 := inv_mul_cancel _
        simpa using congrArg (fun e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m) =>
          (e : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) hgrp
      · have hgrp : A0e * A0e.symm = 1 := mul_inv_cancel _
        simpa using congrArg (fun e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m) =>
          (e : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) hgrp
    exact huΓ.mul (huA0.mul huA)
  -- the nonzero set of χ sits in the closed box
  have hχne_box : ∀ p : ℝ × ℝ, χ p ≠ 0 → p.1 ∈ Icc (-η) (1 + η) ∧ p.2 ∈ Icc (-η) (1 + η) := by
    intro p hp
    constructor
    · constructor
      · by_contra hc
        push Not at hc
        exact hp (by simp [χ, sBump_eq_zero_of_le hηpos (le_of_lt hc)])
      · by_contra hc
        push Not at hc
        exact hp (by simp [χ, sBump_eq_zero_of_ge hηpos (le_of_lt hc)])
    · constructor
      · by_contra hc
        push Not at hc
        exact hp (by simp [χ, sBump_eq_zero_of_le hηpos (le_of_lt hc)])
      · by_contra hc
        push Not at hc
        exact hp (by simp [χ, sBump_eq_zero_of_ge hηpos (le_of_lt hc)])
  have hbox_closed : IsClosed (Icc (-η) (1 + η) ×ˢ Icc (-η) (1 + η) :
      Set (ℝ × ℝ)) := isClosed_Icc.prod isClosed_Icc
  have hχsupp_closed : ∀ p : ℝ × ℝ, p ∈ tsupport χ → IsUnit (K p) := by
    intro p hp
    have hsub : {q : ℝ × ℝ | χ q ≠ 0} ⊆ Icc (-η) (1 + η) ×ˢ Icc (-η) (1 + η) := by
      intro q hq
      exact ⟨(hχne_box q hq).1, (hχne_box q hq).2⟩
    have hcl : tsupport χ ⊆ Icc (-η) (1 + η) ×ˢ Icc (-η) (1 + η) :=
      closure_minimal hsub hbox_closed
    exact hbox_unit p (hcl hp).1 (hcl hp).2
  -- the patched inverse
  let Kinv : ℝ × ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    fun p => χ p • Ring.inverse (K p)
  have hχsm_at : ∀ p : ℝ × ℝ, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ p :=
    fun p => hχsm.contDiffAt
  have hKinvsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Kinv := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p ∈ tsupport χ
    · have hu : IsUnit (K p) := hχsupp_closed p hp
      have hrinv : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : ℝ × ℝ => Ring.inverse (K q)) p := by
        have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ring.inverse (K p) := by
          have h := contDiffAt_ringInverse (𝕜 := ℝ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) hu.unit
          rwa [IsUnit.unit_spec hu] at h
        exact h1.comp p hKsm.contDiffAt
      exact (hχsm_at p).smul hrinv
    · have hop : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
      have hmem : (tsupport χ)ᶜ ∈ 𝓝 p := hop.mem_nhds hp
      have hzero : Kinv =ᶠ[𝓝 p] (fun _ : ℝ × ℝ =>
          (0 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) := by
        filter_upwards [hmem] with q hq
        have hχq : χ q = 0 := image_eq_zero_of_notMem_tsupport hq
        show χ q • Ring.inverse (K q) = (0 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
        rw [hχq]
        ext x
        simp
      exact (contDiffAt_const (c := (0 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)))).congr_of_eventuallyEq hzero
  refine ⟨K, Kinv, hKsm, hKinvsm, fun t _ => hK0 t, fun t _ => hK1 t, ?_, ?_⟩
  · intro s hs t ht
    have h1 : χ (s, t) = 1 := hχ1 s hs t ht
    have hu : IsUnit (K (s,t)) :=
      hχsupp_closed (s,t) (subset_tsupport χ (Function.mem_support.mpr (by rw [h1]; exact one_ne_zero)))
    show K (s,t) * (χ (s,t) • Ring.inverse (K (s,t))) = 1
    rw [h1, one_smul, Ring.mul_inverse_cancel _ hu]
  · intro s hs t ht
    have h1 : χ (s, t) = 1 := hχ1 s hs t ht
    have hu : IsUnit (K (s,t)) :=
      hχsupp_closed (s,t) (subset_tsupport χ (Function.mem_support.mpr (by rw [h1]; exact one_ne_zero)))
    show (χ (s,t) • Ring.inverse (K (s,t))) * K (s,t) = 1
    rw [h1, one_smul, Ring.inverse_mul_cancel _ hu]

end Work.Drive.Whitney
