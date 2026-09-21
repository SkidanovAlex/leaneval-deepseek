import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Submission.Commons.Geometry.Convex.eq_of_volume_halfspace_eq_of_convex
import Submission.Commons.Geometry.Ulam.strictConvex_body_of_revolution
import Submission.Commons.Geometry.Ulam.interior_nonempty_body_of_revolution

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped BigOperators ContDiff Pointwise RealInnerProductSpace

set_option autoImplicit false
set_option linter.unusedVariables false

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-! ### Invariance of averages under linear isometries -/

lemma setAverage_linearIsometryEquiv_invariant {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (L : E ≃ₗᵢ[ℝ] E) (s : Set E) (hs : L '' s = s) :
    L (⨍ x in s, x) = ⨍ x in s, x := by
  have hcomm : L (∫ x in s, x) = ∫ x in s, L x := by
    have h := L.toLinearIsometry.integral_comp_comm (μ := volume.restrict s) (fun x : E => x)
    simpa using h.symm
  have himage : ∫ x in s, L x = ∫ x in s, x := by
    have hmp := L.measurePreserving
    have h := hmp.setIntegral_image_emb L.toMeasurableEquiv.measurableEmbedding (fun x : E => x) s
    calc
      ∫ x in s, L x = ∫ y in ⇑L '' s, y := h.symm
      _ = ∫ x in s, x := by rw [hs]
  simp only [MeasureTheory.setAverage_eq]
  rw [map_smul, hcomm, himage]

lemma average_image_linearIsometryEquiv {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (L : E ≃ₗᵢ[ℝ] E) (s : Set E) :
    L (⨍ x in s, x) = ⨍ y in (L '' s), y := by
  have hcomm : L (∫ x in s, x) = ∫ x in s, L x := by
    have h := L.toLinearIsometry.integral_comp_comm (μ := volume.restrict s) (fun x : E => x)
    simpa using h.symm
  have himage : ∫ x in s, L x = ∫ y in (L '' s), y := by
    have hmp := L.measurePreserving
    exact (hmp.setIntegral_image_emb L.toMeasurableEquiv.measurableEmbedding (fun x : E => x) s).symm
  have hvol : volume.real s = volume.real (L '' s) := by
    have hpre := L.measurePreserving.measure_preimage_emb L.toMeasurableEquiv.measurableEmbedding (L '' s)
    have hpre' : L ⁻¹' (L '' s) = s := Set.preimage_image_eq s L.injective
    rw [hpre'] at hpre
    exact congrArg ENNReal.toReal hpre
  simp only [MeasureTheory.setAverage_eq]
  rw [map_smul, hcomm, himage, hvol]

lemma mem_span_smul_of_linearIsometryEquiv {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : E ≃ₗᵢ[ℝ] E) {v ξ : E} (h : L v ∈ ℝ ∙ (L ξ)) : v ∈ ℝ ∙ ξ := by
  rw [Submodule.mem_span_singleton] at h ⊢
  rcases h with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  have hL : L (c • ξ) = L v := by
    rw [map_smul, hc]
  exact L.injective hL

/-! ### Coordinate and body-invariance lemmas -/

lemma coord0_eq_inner_single [NeZero d] (x : ℝᵈ) :
    x 0 = ⟪x, EuclideanSpace.single (0 : Fin d) (1:ℝ)⟫ := by
  rw [EuclideanSpace.inner_single_right]
  simp

lemma coord0_of_linearIsometryEquiv_fixes_single [NeZero d]
    (R : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ)
    (hR0 : R (EuclideanSpace.single (0 : Fin d) (1:ℝ)) = EuclideanSpace.single (0 : Fin d) (1:ℝ))
    (x : ℝᵈ) :
    (R x) 0 = x 0 := by
  rw [coord0_eq_inner_single (R x), coord0_eq_inner_single x]
  rw [← LinearIsometryEquiv.inner_map_map R x (EuclideanSpace.single (0 : Fin d) (1:ℝ))]
  rw [hR0]

lemma sum_split_coord0 [NeZero d] (x : ℝᵈ) :
    (∑ i : Fin d, (x i)^2) = (x 0)^2 + ∑ i ∈ Finset.Ioi (0 : Fin d), (x i)^2 := by
  classical
  have hins : Finset.univ = insert (0 : Fin d) (Finset.Ioi (0 : Fin d)) := by
    ext i
    simp [Fin.pos_iff_ne_zero]
  rw [hins, Finset.sum_insert]
  simp [Fin.pos_iff_ne_zero]

lemma radialSumSq_linearIsometryEquiv_fixes_single [NeZero d]
    (R : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ)
    (hR0 : R (EuclideanSpace.single (0 : Fin d) (1:ℝ)) = EuclideanSpace.single (0 : Fin d) (1:ℝ))
    (x : ℝᵈ) :
    (∑ i ∈ Finset.Ioi (0 : Fin d), (R x i)^2) = ∑ i ∈ Finset.Ioi (0 : Fin d), (x i)^2 := by
  have hcoord := coord0_of_linearIsometryEquiv_fixes_single R hR0 x
  calc
    (∑ i ∈ Finset.Ioi (0 : Fin d), (R x i)^2)
        = (∑ i : Fin d, (R x i)^2) - (R x 0)^2 := by
          rw [sum_split_coord0 (R x)]
          ring
    _ = ‖R x‖^2 - (x 0)^2 := by
          rw [EuclideanSpace.real_norm_sq_eq, hcoord]
    _ = ‖x‖^2 - (x 0)^2 := by rw [R.norm_map]
    _ = ∑ i ∈ Finset.Ioi (0 : Fin d), (x i)^2 := by
          rw [EuclideanSpace.real_norm_sq_eq x]
          rw [sum_split_coord0 x]
          ring

lemma body_of_revolution_tail_linearIsometryEquiv_image [NeZero d]
    {R₁ R₂ : ℝ} {f : ℝ → ℝ}
    (R : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ)
    (hR0 : R (EuclideanSpace.single (0 : Fin d) (1:ℝ)) = EuclideanSpace.single (0 : Fin d) (1:ℝ)) :
    R '' {x : ℝᵈ | x 0 ∈ Set.Icc (-R₁) R₂ ∧
        ∑ i ∈ Finset.Ioi (0 : Fin d), (x i)^2 ≤ f (x 0)^2} =
      {x : ℝᵈ | x 0 ∈ Set.Icc (-R₁) R₂ ∧
        ∑ i ∈ Finset.Ioi (0 : Fin d), (x i)^2 ≤ f (x 0)^2} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · rw [coord0_of_linearIsometryEquiv_fixes_single R hR0 x]
      exact hx.1
    · rw [radialSumSq_linearIsometryEquiv_fixes_single R hR0 x]
      rw [coord0_of_linearIsometryEquiv_fixes_single R hR0 x]
      exact hx.2
  · intro hy
    let x := R.symm y
    refine ⟨x, ?_, ?_⟩
    · constructor
      · have hsymm0 : R.symm (EuclideanSpace.single (0 : Fin d) (1:ℝ)) = EuclideanSpace.single (0 : Fin d) (1:ℝ) := by
          have h := LinearIsometryEquiv.symm_apply_apply R (EuclideanSpace.single (0 : Fin d) (1:ℝ))
          rwa [hR0] at h
        rw [coord0_of_linearIsometryEquiv_fixes_single R.symm hsymm0 y]
        exact hy.1
      · have hsymm0 : R.symm (EuclideanSpace.single (0 : Fin d) (1:ℝ)) = EuclideanSpace.single (0 : Fin d) (1:ℝ) := by
          have h := LinearIsometryEquiv.symm_apply_apply R (EuclideanSpace.single (0 : Fin d) (1:ℝ))
          rwa [hR0] at h
        rw [radialSumSq_linearIsometryEquiv_fixes_single R.symm hsymm0 y]
        rw [coord0_of_linearIsometryEquiv_fixes_single R.symm hsymm0 y]
        exact hy.2
    · dsimp [x]
      simp

lemma halfspace_image_linearIsometryEquiv {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R : E ≃ₗᵢ[ℝ] E) (ξ : E) (t : ℝ) :
    R '' {x | ⟪x, ξ⟫ ≤ t} = {y | ⟪y, R ξ⟫ ≤ t} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [LinearIsometryEquiv.inner_map_map] using hx
  · intro hy
    refine ⟨R.symm y, ?_, ?_⟩
    · have h := LinearIsometryEquiv.inner_map_map R (R.symm y) ξ
      rw [LinearIsometryEquiv.apply_symm_apply] at h
      change ⟪R.symm y, ξ⟫ ≤ t
      rw [← h]
      exact hy
    · simp

lemma exists_tail_linearIsometryEquiv_map_to_last
    [NeZero d] (hd : 2 ≤ d) (ξ : ℝᵈ) :
    ∃ R : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ,
      R (EuclideanSpace.single 0 (1:ℝ)) = EuclideanSpace.single 0 (1:ℝ) ∧
      ∃ a b : ℝ, 0 ≤ b ∧
        R ξ = a • EuclideanSpace.single 0 (1:ℝ) +
          b • EuclideanSpace.single (⟨d - 1, by omega⟩ : Fin d) (1:ℝ) := by
  classical
  let e0 : ℝᵈ := EuclideanSpace.single 0 (1:ℝ)
  let last : Fin d := ⟨d - 1, by omega⟩
  let elast : ℝᵈ := EuclideanSpace.single last (1:ℝ)
  let vtail : ℝᵈ := ξ - (ξ 0) • e0
  by_cases hv : vtail = 0
  · refine ⟨LinearIsometryEquiv.refl ℝ ℝᵈ, ?_⟩
    change LinearIsometryEquiv.refl ℝ ℝᵈ e0 = e0 ∧
        ∃ a b : ℝ, 0 ≤ b ∧ ξ = a • e0 + b • elast
    constructor
    · rfl
    · refine ⟨ξ 0, 0, by norm_num, ?_⟩
      have hξeq : ξ = (ξ 0) • e0 := by
        simpa [e0, vtail] using sub_eq_zero.mp hv
      rw [hξeq]
      ext i
      simp [e0, elast]
  · let r : ℝ := ‖vtail‖
    have hr_pos : 0 < r := norm_pos_iff.mpr hv
    let w : ℝᵈ := r⁻¹ • vtail
    have hw_norm : ‖w‖ = 1 := by
      dsimp [w, r]
      rw [norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (ne_of_gt hr_pos)
    have hvtail0 : vtail 0 = 0 := by
      simp [vtail, e0]
    have hw0 : w 0 = 0 := by
      dsimp [w]
      simp [hvtail0]
    have hw_ortho : ⟪e0, w⟫ = 0 := by
      dsimp [w, e0, vtail]
      rw [inner_smul_right]
      have h1 : ⟪EuclideanSpace.single (0 : Fin d) (1:ℝ), ξ⟫ = ξ 0 := by
        rw [EuclideanSpace.inner_single_left]
        simp
      have h2 : ⟪EuclideanSpace.single (0 : Fin d) (1:ℝ),
          (ξ 0) • EuclideanSpace.single (0 : Fin d) (1:ℝ)⟫ = ξ 0 := by
        rw [inner_smul_right, EuclideanSpace.inner_single_left]
        simp
      rw [inner_sub_right, h1, h2]
      simp
    let s : Set (Fin d) := {0, last}
    let v : Fin d → ℝᵈ := fun i =>
      if i = 0 then e0 else if i = last then w else e0
    have hfinrank : Module.finrank ℝ ℝᵈ = Fintype.card (Fin d) := by
      simpa using (finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin d))
    have hlast_ne : last ≠ 0 := by
      dsimp [last]
      apply Fin.ne_of_val_ne
      simp
      omega
    have hv_ortho : Orthonormal ℝ (s.domRestrict v) := by
      refine ⟨?_, ?_⟩
      · rintro ⟨i, hi⟩
        have hi' : i = 0 ∨ i = last := by
          simpa [s] using hi
        rcases hi' with rfl | rfl
        · simp [v, e0]
        · simp [v, w, hw_norm, hlast_ne]
      · intro i j hij
        rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
        have hi' : i = 0 ∨ i = last := by simpa [s] using hi
        have hj' : j = 0 ∨ j = last := by simpa [s] using hj
        have hij' : i ≠ j := by
          intro h
          apply hij
          cases i; cases j; congr
        rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
        · exact (hij' rfl).elim
        · simp [v, e0, w, hw_ortho, hlast_ne]
        · rw [real_inner_comm]
          simp [v, e0, w, hw_ortho, hlast_ne]
        · exact (hij' rfl).elim
    obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℝ) (E := ℝᵈ) (ι := Fin d) hfinrank
      (v := v) (s := s) hv_ortho
    let R : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ := b.repr
    refine ⟨R, ?_⟩
    change R e0 = e0 ∧ ∃ a b : ℝ, 0 ≤ b ∧ R ξ = a • e0 + b • elast
    constructor
    · have hb0 := hb 0 (by simp [s])
      have hb0' : b 0 = e0 := by
        simpa [v] using hb0
      calc
        R e0 = b.repr e0 := rfl
        _ = b.repr (b 0) := by rw [hb0']
        _ = EuclideanSpace.single 0 (1:ℝ) := by rw [OrthonormalBasis.repr_self]
    · refine ⟨ξ 0, r, norm_nonneg _, ?_⟩
      have hr_ne : r ≠ 0 := ne_of_gt hr_pos
      have hsmul : r • (r⁻¹ • vtail) = vtail := by
        rw [smul_smul, mul_inv_cancel₀ hr_ne, one_smul]
      have hξdecomp : ξ = (ξ 0) • e0 + r • w := by
        calc
          ξ = (ξ 0) • e0 + (ξ - (ξ 0) • e0) := by abel
          _ = (ξ 0) • e0 + r • (r⁻¹ • vtail) := by rw [hsmul]
          _ = (ξ 0) • e0 + r • w := by rfl
      rw [hξdecomp]
      rw [map_add, map_smul, map_smul]
      have hb0' : b 0 = e0 := by
        have hb0 := hb 0 (by simp [s])
        simpa [v] using hb0
      have hblast : b last = w := by
        have hb_last := hb last (by simp [s])
        simpa [v, hlast_ne] using hb_last
      have hR0 : R e0 = e0 := by
        calc
          R e0 = b.repr (b 0) := by rw [hb0']
          _ = EuclideanSpace.single 0 (1:ℝ) := by rw [OrthonormalBasis.repr_self]
      have hRw : R w = elast := by
        calc
          R w = b.repr (b last) := by rw [hblast]
          _ = EuclideanSpace.single last (1:ℝ) := by rw [OrthonormalBasis.repr_self]
      rw [hR0, hRw]
      ext i
      simp [e0, elast, hw0]

/-! ### Hyperplanes have zero volume -/

lemma volume_hyperplane_eq_zero [NeZero d] {ξ : ℝᵈ} (hξ : ξ ≠ 0) (t : ℝ) :
    volume {x : ℝᵈ | ⟪x, ξ⟫ = t} = 0 := by
  classical
  let L : ℝᵈ →L[ℝ] ℝ :=
    { toFun := fun x => ⟪x, ξ⟫
      map_add' := by intro x y; simp [inner_add_left]
      map_smul' := by intro c x; simp [inner_smul_left] }
  have hL0 : L ≠ 0 := by
    intro h
    have h1 := congrArg (fun f : ℝᵈ →L[ℝ] ℝ => f ξ) h
    simp [L] at h1
    have hnorm : ‖ξ‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq]
      simpa using h1
    have hnorm0 : ‖ξ‖ = 0 := by
      exact (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp hnorm
    exact hξ (norm_eq_zero.mp hnorm0)
  let p : ℝᵈ := (t / ‖ξ‖ ^ 2) • ξ
  have hξnorm_ne : ‖ξ‖ ^ 2 ≠ 0 := by
    have hnorm_ne : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
    exact pow_ne_zero 2 hnorm_ne
  have hp_inner : ⟪p, ξ⟫ = t := by
    dsimp [p]
    simp [inner_smul_left, real_inner_self_eq_norm_sq, div_mul_cancel₀ _ hξnorm_ne]
  have hp : L p = t := by
    simpa [L] using hp_inner
  let s : AffineSubspace ℝ ℝᵈ :=
    AffineSubspace.mk' p (LinearMap.ker (L : ℝᵈ →ₗ[ℝ] ℝ))
  have hs_ne : s ≠ ⊤ := by
    intro h
    have hdir : s.direction = ⊤ := by
      simpa using congrArg AffineSubspace.direction h
    have hker : LinearMap.ker (L : ℝᵈ →ₗ[ℝ] ℝ) = ⊤ := by
      simpa [s] using hdir
    have hL_eq_lin : (L : ℝᵈ →ₗ[ℝ] ℝ) = 0 := by
      exact (LinearMap.ker_eq_top).mp hker
    have hL_apply_zero : ∀ x : ℝᵈ, L x = 0 := by
      intro x
      have hx := congrArg (fun f : ℝᵈ →ₗ[ℝ] ℝ => f x) hL_eq_lin
      simpa using hx
    have hL_eq : L = 0 := by
      exact ContinuousLinearMap.ext hL_apply_zero
    exact hL0 hL_eq
  have hset : {x : ℝᵈ | ⟪x, ξ⟫ = t} = (s : Set ℝᵈ) := by
    ext x
    rw [AffineSubspace.mem_coe, AffineSubspace.mem_mk']
    change (⟪x, ξ⟫ = t) ↔ (L : ℝᵈ →ₗ[ℝ] ℝ) (x -ᵥ p) = 0
    have hsub : ⟪x - p, ξ⟫ = 0 ↔ ⟪x, ξ⟫ = t := by
      rw [inner_sub_left, hp_inner, sub_eq_zero]
    have hLsub : (L : ℝᵈ →ₗ[ℝ] ℝ) (x -ᵥ p) = 0 ↔ ⟪x - p, ξ⟫ = 0 := by
      simp [L]
    rw [← hsub, ← hLsub]
  rw [hset]
  exact MeasureTheory.Measure.addHaar_affineSubspace (μ := volume) (E := ℝᵈ) s hs_ne

lemma volume_real_hyperplane_eq_zero [NeZero d] {ξ : ℝᵈ} (hξ : ξ ≠ 0) (t : ℝ) :
    volume.real {x : ℝᵈ | ⟪x, ξ⟫ = t} = 0 := by
  rw [Measure.real, volume_hyperplane_eq_zero hξ t]
  simp

/-! ### Body of revolution properties -/

lemma concaveOn_Icc_zero_endpoints_nonneg {a b : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hf : ConcaveOn ℝ (Set.Icc a b) f)
    (hfa : f a = 0) (hfb : f b = 0) :
    ∀ t ∈ Set.Icc a b, 0 ≤ f t := by
  intro t ht
  have ha_mem : a ∈ Set.Icc a b := by
    rw [Set.mem_Icc]; exact ⟨le_rfl, hab⟩
  have hb_mem : b ∈ Set.Icc a b := by
    rw [Set.mem_Icc]; exact ⟨hab, le_rfl⟩
  have hmin := hf.min_le_of_mem_Icc (x := a) (y := b) (z := t) ha_mem hb_mem ht
  rw [hfa, hfb] at hmin
  simpa using hmin

lemma concaveOn_Icc_zero_endpoints_bounded {a b : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hf : ConcaveOn ℝ (Set.Icc a b) f)
    (hfa : f a = 0) (hfb : f b = 0) :
    Bornology.IsBounded (f '' Set.Icc a b) := by
  classical
  by_cases heq : a = b
  · subst b
    rw [isBounded_iff_forall_norm_le]
    refine ⟨|f a| + 1, ?_⟩
    rintro y ⟨t, ht, rfl⟩
    have ht_eq : t = a := by simpa [Set.mem_Icc] using ht
    subst t
    norm_num [Real.norm_eq_abs]
  · have hab_lt : a < b := lt_of_le_of_ne hab heq
    have hnonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t :=
      concaveOn_Icc_zero_endpoints_nonneg hab hf hfa hfb
    let c : ℝ := (a + b) / 2
    have hac : a < c := by dsimp [c]; linarith
    have hcb : c < b := by dsimp [c]; linarith
    have hc_mem : c ∈ Set.Icc a b := by dsimp [c]; constructor <;> linarith
    have hfc_nonneg : 0 ≤ f c := hnonneg c hc_mem
    have h_le_two : ∀ t ∈ Set.Icc a b, f t ≤ 2 * f c := by
      intro t ht
      by_cases htc : t ≤ c
      · have hbt : b - t > 0 := by linarith [ht.2, htc]
        have hbc : b - c > 0 := by linarith
        have hct : c - t ≥ 0 := by linarith
        let α : ℝ := (b - c) / (b - t)
        let β : ℝ := (c - t) / (b - t)
        have hα_nonneg : 0 ≤ α := by dsimp [α]; positivity
        have hβ_nonneg : 0 ≤ β := by dsimp [β]; positivity
        have hsum : α + β = 1 := by
          dsimp [α, β]
          field_simp [ne_of_gt hbt]
          ring
        have hc_eq : c = α * t + β * b := by
          dsimp [α, β]
          field_simp [ne_of_gt hbt]
          ring
        have hb_mem : b ∈ Set.Icc a b := by
          rw [Set.mem_Icc]; exact ⟨hab_lt.le, le_rfl⟩
        have hconc := hf.2 ht hb_mem hα_nonneg hβ_nonneg hsum
        have hconc' : α * f t + β * f b ≤ f c := by
          simpa [hc_eq, smul_eq_mul] using hconc
        have hft_le_α : α * f t ≤ f c := by
          simpa [hfb] using hconc'
        have hα_ge_half : 1 / 2 ≤ α := by
          dsimp [α]
          have hbc_eq : b - c = (b - a) / 2 := by dsimp [c]; ring
          rw [hbc_eq]
          have hbt_le : b - t ≤ b - a := by linarith [ht.1]
          have hden : 0 < b - t := hbt
          rw [le_div_iff₀ hden]
          nlinarith [hbt_le]
        have hft_nonneg : 0 ≤ f t := hnonneg t ht
        have hhalf : (1 / 2 : ℝ) * f t ≤ α * f t :=
          mul_le_mul_of_nonneg_right hα_ge_half hft_nonneg
        have hft_le_half : (1 / 2 : ℝ) * f t ≤ f c := le_trans hhalf hft_le_α
        nlinarith
      · have hct_lt : c < t := lt_of_not_ge htc
        have hta : t - a > 0 := by linarith [ht.1, hct_lt]
        have hca : c - a > 0 := by linarith
        have htc_nonneg : t - c ≥ 0 := by linarith
        let α : ℝ := (t - c) / (t - a)
        let β : ℝ := (c - a) / (t - a)
        have hα_nonneg : 0 ≤ α := by dsimp [α]; positivity
        have hβ_nonneg : 0 ≤ β := by dsimp [β]; positivity
        have hsum : α + β = 1 := by
          dsimp [α, β]
          field_simp [ne_of_gt hta]
          ring
        have hc_eq : c = α * a + β * t := by
          dsimp [α, β]
          field_simp [ne_of_gt hta]
          ring
        have ha_mem : a ∈ Set.Icc a b := by
          rw [Set.mem_Icc]; exact ⟨le_rfl, hab_lt.le⟩
        have hconc := hf.2 ha_mem ht hα_nonneg hβ_nonneg hsum
        have hconc' : α * f a + β * f t ≤ f c := by
          simpa [hc_eq, smul_eq_mul] using hconc
        have hft_le_β : β * f t ≤ f c := by
          simpa [hfa] using hconc'
        have hβ_ge_half : 1 / 2 ≤ β := by
          dsimp [β]
          have hca_eq : c - a = (b - a) / 2 := by dsimp [c]; ring
          rw [hca_eq]
          have hta_le : t - a ≤ b - a := by linarith [ht.2]
          have hden : 0 < t - a := hta
          rw [le_div_iff₀ hden]
          nlinarith [hta_le]
        have hft_nonneg : 0 ≤ f t := hnonneg t ht
        have hhalf : (1 / 2 : ℝ) * f t ≤ β * f t :=
          mul_le_mul_of_nonneg_right hβ_ge_half hft_nonneg
        have hft_le_half : (1 / 2 : ℝ) * f t ≤ f c := le_trans hhalf hft_le_β
        nlinarith
    have h_abs_le : ∀ t ∈ Set.Icc a b, |f t| ≤ 2 * f c := by
      intro t ht
      rw [abs_of_nonneg (hnonneg t ht)]
      exact h_le_two t ht
    rw [isBounded_iff_forall_norm_le]
    refine ⟨2 * f c + 1, ?_⟩
    rintro y ⟨t, ht, rfl⟩
    have hle := h_abs_le t ht
    norm_num [Real.norm_eq_abs]
    nlinarith [hfc_nonneg]

lemma body_of_revolution_bounded [NeZero d] {R₁ R₂ : ℝ} {f : ℝ → ℝ}
    (hf_conc : ConcaveOn ℝ (Set.Icc (-R₁) R₂) f)
    (hf_left : f (-R₁) = 0) (hf_right : f R₂ = 0) :
    Bornology.IsBounded {x : ℝᵈ | x 0 ∈ Set.Icc (-R₁) R₂ ∧
      ∑ i > 0, (x i)^2 ≤ (f (x 0))^2} := by
  classical
  by_cases hR : -R₁ ≤ R₂
  · have hf_bdd : Bornology.IsBounded (f '' Set.Icc (-R₁) R₂) :=
      concaveOn_Icc_zero_endpoints_bounded hR hf_conc hf_left hf_right
    obtain ⟨B, hB⟩ := hf_bdd.subset_closedBall (0 : ℝ)
    let C : ℝ := max B 0
    have hC_nonneg : 0 ≤ C := by dsimp [C]; exact le_max_right B 0
    have hf_abs_le : ∀ t ∈ Set.Icc (-R₁) R₂, |f t| ≤ C := by
      intro t ht
      have hmem : f t ∈ f '' Set.Icc (-R₁) R₂ := ⟨t, ht, rfl⟩
      have hdist : dist (f t) 0 ≤ B := hB hmem
      have hle : |f t| ≤ B := by simpa [Real.dist_eq] using hdist
      exact hle.trans (le_max_left B 0)
    let A0 : ℝ := max |R₁| |R₂|
    have hA0_nonneg : 0 ≤ A0 := by dsimp [A0]; positivity
    let r : ℝ := √(A0 ^ 2 + C ^ 2)
    refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : ℝᵈ)) (r := r)) ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hx0Icc : x 0 ∈ Set.Icc (-R₁) R₂ := hx.1
    have htail : ∑ i > 0, (x i)^2 ≤ (f (x 0))^2 := hx.2
    have hx0_abs : |x 0| ≤ A0 := by
      dsimp [A0]
      simpa [abs_neg] using (abs_le_max_abs_abs (a := -R₁) (b := x 0) (c := R₂) hx0Icc.1 hx0Icc.2)
    have hx0_sq : (x 0)^2 ≤ A0 ^ 2 := by
      exact sq_le_sq.mpr (by simpa [abs_of_nonneg hA0_nonneg] using hx0_abs)
    have hf_abs_le_C : |f (x 0)| ≤ C := hf_abs_le (x 0) hx0Icc
    have hf_sq_le : (f (x 0))^2 ≤ C ^ 2 := by
      exact sq_le_sq.mpr (by simpa [abs_of_nonneg hC_nonneg] using hf_abs_le_C)
    have htail_le : ∑ i > 0, (x i)^2 ≤ C ^ 2 := htail.trans hf_sq_le
    have hnorm_sq : ‖x‖ ^ 2 ≤ A0 ^ 2 + C ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc
        (∑ i : Fin d, (x i)^2) = (x 0)^2 + ∑ i > 0, (x i)^2 := by
          rw [sum_split_coord0]
        _ ≤ A0 ^ 2 + C ^ 2 := add_le_add hx0_sq htail_le
    have hnorm_le : ‖x‖ ≤ r := Real.le_sqrt_of_sq_le hnorm_sq
    simpa using hnorm_le
  · have hlt : R₂ < -R₁ := lt_of_not_ge hR
    have hempty : {x : ℝᵈ | x 0 ∈ Set.Icc (-R₁) R₂ ∧
        ∑ i > 0, (x i)^2 ≤ (f (x 0))^2} = ∅ := by
      ext x
      rw [Set.mem_empty_iff_false, iff_false]
      intro hx
      have hx0 : x 0 ∈ Set.Icc (-R₁) R₂ := hx.1
      have hIcc_empty : Set.Icc (-R₁) R₂ = ∅ := Set.Icc_eq_empty_of_lt hlt
      exact (by simpa [hIcc_empty] using hx0)
    rw [hempty]
    exact Bornology.isBounded_empty

lemma measurable_of_support_subset_Icc_of_contDiffOn {a b : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hf_support : f.support ⊆ Set.Icc a b)
    (hf_cont : ContDiffOn ℝ ∞ f (Set.Ioo a b))
    (hfa : f a = 0) (hfb : f b = 0) :
    Measurable f := by
  classical
  let s : Set ℝ := Set.Ioo a b
  let g : ℝ → ℝ := s.piecewise f (fun _ => 0)
  have hcont_f : ContinuousOn f s := hf_cont.continuousOn
  have hcont_zero : ContinuousOn (fun _ : ℝ => (0 : ℝ)) sᶜ := continuous_const.continuousOn
  have hg_meas : Measurable g := by
    dsimp [g, s]
    exact ContinuousOn.measurable_piecewise hcont_f hcont_zero measurableSet_Ioo
  have hfg : f = g := by
    ext t
    by_cases ht : t ∈ s
    · simp [g, s, ht]
    · have hzero : f t = 0 := by
        by_cases htc : t ∈ Set.Icc a b
        · have ht1 : a ≤ t := htc.1
          have ht2 : t ≤ b := htc.2
          have hnot : ¬ (a < t ∧ t < b) := by simpa [s] using ht
          have hle_or : t = a ∨ t = b := by
            by_cases hlt : a < t
            · right
              have hnotlt : ¬ t < b := by
                intro h; exact hnot ⟨hlt, h⟩
              linarith
            · left
              linarith
          rcases hle_or with rfl | rfl <;> simp [hfa, hfb]
        · by_contra hz
          have hmem : t ∈ Function.support f := by
            simpa [Function.mem_support] using hz
          exact htc (hf_support hmem)
      simp [g, ht, hzero]
  rw [hfg]
  exact hg_meas

lemma body_of_revolution_measurable [NeZero d] {R₁ R₂ : ℝ} {f : ℝ → ℝ}
    (hf_support : f.support ⊆ Set.Icc (-R₁) R₂)
    (hf_smooth : ContDiffOn ℝ ∞ f (Set.Ioo (-R₁) R₂))
    (hf_left : f (-R₁) = 0) (hf_right : f R₂ = 0) :
    MeasurableSet {x : ℝᵈ | x 0 ∈ Set.Icc (-R₁) R₂ ∧
      ∑ i > 0, (x i)^2 ≤ (f (x 0))^2} := by
  classical
  by_cases hR : -R₁ ≤ R₂
  · have hf_meas : Measurable f := by
      exact measurable_of_support_subset_Icc_of_contDiffOn hR hf_support hf_smooth hf_left hf_right
    let A : Set ℝᵈ := {x | x 0 ∈ Set.Icc (-R₁) R₂}
    let g : ℝᵈ → ℝ := fun x => (∑ i > 0, (x i)^2) - (f (x 0))^2
    have hA_meas : MeasurableSet A := by
      exact (isClosed_Icc.preimage (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) (i := 0))).measurableSet
    have hsum_meas : Measurable (fun x : ℝᵈ => ∑ i > 0, (x i)^2) := by
      refine (continuous_finsetSum (Finset.Ioi (0 : Fin d)) ?_).measurable
      intro i hi
      fun_prop
    have hf_comp_meas : Measurable (fun x : ℝᵈ => f (x 0)) :=
      hf_meas.comp (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) (i := 0)).measurable
    have hf2_meas : Measurable (fun x : ℝᵈ => (f (x 0))^2) := hf_comp_meas.pow_const (2 : ℕ)
    have hg_meas : Measurable g := hsum_meas.sub hf2_meas
    have hpre : MeasurableSet (A ∩ g ⁻¹' Set.Iic 0) := by
      exact hA_meas.inter (hg_meas isClosed_Iic.measurableSet)
    convert hpre using 1
    ext x
    simp [A, g]
  · have hlt : R₂ < -R₁ := lt_of_not_ge hR
    have hempty : {x : ℝᵈ | x 0 ∈ Set.Icc (-R₁) R₂ ∧
        ∑ i > 0, (x i)^2 ≤ (f (x 0))^2} = ∅ := by
      ext x
      rw [Set.mem_empty_iff_false, iff_false]
      intro hx
      have hx0 : x 0 ∈ Set.Icc (-R₁) R₂ := hx.1
      have hIcc_empty : Set.Icc (-R₁) R₂ = ∅ := Set.Icc_eq_empty_of_lt hlt
      exact (by simpa [hIcc_empty] using hx0)
    rw [hempty]
    exact MeasurableSet.empty

lemma body_of_revolution_convex [NeZero d] {R₁ R₂ : ℝ} {f : ℝ → ℝ}
    (hf_conc : ConcaveOn ℝ (Set.Icc (-R₁) R₂) f)
    (hf_left : f (-R₁) = 0) (hf_right : f R₂ = 0) :
    Convex ℝ {x : ℝᵈ | x 0 ∈ Set.Icc (-R₁) R₂ ∧
      ∑ i > 0, (x i)^2 ≤ (f (x 0))^2} := by
  classical
  by_cases hR : -R₁ ≤ R₂
  · have hf_nonneg : ∀ t ∈ Set.Icc (-R₁) R₂, 0 ≤ f t :=
      concaveOn_Icc_zero_endpoints_nonneg hR hf_conc hf_left hf_right
    intro x hx y hy a b ha hb hab
    let z : ℝᵈ := a • x + b • y
    have hz0_mem : z 0 ∈ Set.Icc (-R₁) R₂ := by
      dsimp [z]
      exact convex_Icc (-R₁) R₂ hx.1 hy.1 ha hb hab
    have hx_norm_le : ‖strictConvexBodyOfRevolution.radialPart x‖ ≤ f (x 0) := by
      have hsq : ‖strictConvexBodyOfRevolution.radialPart x‖^2 ≤ (f (x 0))^2 := by
        rw [← strictConvexBodyOfRevolution.radialSumSq_eq_norm_sq x]
        exact hx.2
      exact (sq_le_sq₀ (norm_nonneg _) (hf_nonneg (x 0) hx.1)).1 hsq
    have hy_norm_le : ‖strictConvexBodyOfRevolution.radialPart y‖ ≤ f (y 0) := by
      have hsq : ‖strictConvexBodyOfRevolution.radialPart y‖^2 ≤ (f (y 0))^2 := by
        rw [← strictConvexBodyOfRevolution.radialSumSq_eq_norm_sq y]
        exact hy.2
      exact (sq_le_sq₀ (norm_nonneg _) (hf_nonneg (y 0) hy.1)).1 hsq
    have hz_norm_le : ‖strictConvexBodyOfRevolution.radialPart z‖ ≤
        a * f (x 0) + b * f (y 0) := by
      have hrad : strictConvexBodyOfRevolution.radialPart z =
          a • strictConvexBodyOfRevolution.radialPart x +
          b • strictConvexBodyOfRevolution.radialPart y := by
        simpa [z] using strictConvexBodyOfRevolution.radialPart_smul_add x y a b
      calc
        ‖strictConvexBodyOfRevolution.radialPart z‖
            = ‖a • strictConvexBodyOfRevolution.radialPart x +
                b • strictConvexBodyOfRevolution.radialPart y‖ := by rw [hrad]
        _ ≤ ‖a • strictConvexBodyOfRevolution.radialPart x‖ +
            ‖b • strictConvexBodyOfRevolution.radialPart y‖ := norm_add_le _ _
        _ = a * ‖strictConvexBodyOfRevolution.radialPart x‖ +
            b * ‖strictConvexBodyOfRevolution.radialPart y‖ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
        _ ≤ a * f (x 0) + b * f (y 0) :=
              add_le_add (mul_le_mul_of_nonneg_left hx_norm_le ha)
                (mul_le_mul_of_nonneg_left hy_norm_le hb)
    have hf_combo : a * f (x 0) + b * f (y 0) ≤ f (z 0) := by
      have hconc := hf_conc.2 hx.1 hy.1 ha hb hab
      have hz0 : z 0 = a * x 0 + b * y 0 := by simp [z, smul_eq_mul]
      simpa [hz0, smul_eq_mul] using hconc
    have hnonneg_combo : 0 ≤ a * f (x 0) + b * f (y 0) := by
      exact add_nonneg (mul_nonneg ha (hf_nonneg (x 0) hx.1))
        (mul_nonneg hb (hf_nonneg (y 0) hy.1))
    have hfz_nonneg : 0 ≤ f (z 0) := hf_nonneg (z 0) hz0_mem
    have hz_sq : ‖strictConvexBodyOfRevolution.radialPart z‖^2 ≤ (f (z 0))^2 := by
      have h1 : ‖strictConvexBodyOfRevolution.radialPart z‖^2 ≤
          (a * f (x 0) + b * f (y 0))^2 :=
        (sq_le_sq₀ (norm_nonneg _) hnonneg_combo).2 hz_norm_le
      have h2 : (a * f (x 0) + b * f (y 0))^2 ≤ (f (z 0))^2 :=
        (sq_le_sq₀ hnonneg_combo hfz_nonneg).2 hf_combo
      exact h1.trans h2
    have hz_tail_sq_le : (∑ i > 0, (z i)^2) ≤ (f (z 0))^2 := by
      have hz_tail_eq : (∑ i > 0, (z i)^2) = ‖strictConvexBodyOfRevolution.radialPart z‖^2 := by
        simpa [strictConvexBodyOfRevolution.radialSumSq] using
          (strictConvexBodyOfRevolution.radialSumSq_eq_norm_sq z)
      rw [hz_tail_eq]
      exact hz_sq
    exact ⟨hz0_mem, hz_tail_sq_le⟩
  · have hlt : R₂ < -R₁ := lt_of_not_ge hR
    have hempty : {x : ℝᵈ | x 0 ∈ Set.Icc (-R₁) R₂ ∧
        ∑ i > 0, (x i)^2 ≤ (f (x 0))^2} = ∅ := by
      ext x
      rw [Set.mem_empty_iff_false, iff_false]
      intro hx
      have hx0 : x 0 ∈ Set.Icc (-R₁) R₂ := hx.1
      have hIcc_empty : Set.Icc (-R₁) R₂ = ∅ := Set.Icc_eq_empty_of_lt hlt
      exact (by simpa [hIcc_empty] using hx0)
    rw [hempty]
    exact convex_empty

lemma body_of_revolution_measure_zero_of_not_lt [NeZero d] {R₁ R₂ : ℝ} {f : ℝ → ℝ}
    (hf_left : f (-R₁) = 0) (hf_right : f R₂ = 0)
    (hnot : ¬ -R₁ < R₂) :
    volume.real {x : ℝᵈ | x 0 ∈ Set.Icc (-R₁) R₂ ∧
      ∑ i > 0, (x i)^2 ≤ (f (x 0))^2} = 0 := by
  classical
  have hle : R₂ ≤ -R₁ := le_of_not_gt hnot
  by_cases hlt : R₂ < -R₁
  · have hIcc_empty : Set.Icc (-R₁) R₂ = ∅ := Set.Icc_eq_empty_of_lt hlt
    have hempty : {x : ℝᵈ | x 0 ∈ Set.Icc (-R₁) R₂ ∧
        ∑ i > 0, (x i)^2 ≤ (f (x 0))^2} = ∅ := by
      ext x
      rw [Set.mem_empty_iff_false, iff_false]
      intro hx
      exact (by simpa [hIcc_empty] using hx.1)
    rw [hempty]
    simp
  · have heq : R₂ = -R₁ := le_antisymm hle (le_of_not_gt hlt)
    let v : ℝᵈ := EuclideanSpace.single (0 : Fin d) (-R₁)
    have hsub : {x : ℝᵈ | x 0 ∈ Set.Icc (-R₁) R₂ ∧
        ∑ i > 0, (x i)^2 ≤ (f (x 0))^2} ⊆ ({v} : Set ℝᵈ) := by
      intro x hx
      have hx0 : x 0 ∈ Set.Icc (-R₁) R₂ := hx.1
      have hx0eq : x 0 = -R₁ := by
        have hIcc : Set.Icc (-R₁) R₂ = {-R₁} := by
          rw [heq]
          simp [Set.Icc_self]
        simpa [hIcc] using hx0
      have htail_le : ∑ i > 0, (x i)^2 ≤ 0 := by
        have h := hx.2
        rw [hx0eq] at h
        have hf_right' : f (-R₁) = 0 := by simpa [heq] using hf_right
        rw [hf_right'] at h
        simpa using h
      have htail_nonneg : 0 ≤ ∑ i > 0, (x i)^2 := by
        exact Finset.sum_nonneg (by intro i hi; exact sq_nonneg _)
      have htail_zero : ∑ i > 0, (x i)^2 = 0 := le_antisymm htail_le htail_nonneg
      have htail_ind : ∀ i : Fin d, 0 < i → x i = 0 := by
        intro i hi
        have hsum := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.Ioi (0 : Fin d))
          (f := fun i : Fin d => (x i)^2) (by intro j hj; exact sq_nonneg _)).1
          (by simpa using htail_zero)
        exact sq_eq_zero_iff.mp (hsum i (by simpa [Finset.mem_Ioi] using hi))
      ext i
      by_cases hi : 0 < i
      · rw [htail_ind i hi]
        dsimp [v]
        simp [hi.ne']
      · have hle_i : i ≤ 0 := not_lt.mp hi
        have hi0 : i = 0 := (nonpos_iff_eq_zero).mp hle_i
        rw [hi0, hx0eq]
        dsimp [v]
        simp
    have hmeas := measure_mono (μ := volume) hsub
    have hsing : volume.real ({v} : Set ℝᵈ) = 0 := by
      rw [Measure.real, measure_singleton]
      simp
    have hsing_fin : volume ({v} : Set ℝᵈ) ≠ ⊤ := by
      rw [measure_singleton]
      simp
    have hmeas_real : volume.real {x : ℝᵈ | x 0 ∈ Set.Icc (-R₁) R₂ ∧
        ∑ i > 0, (x i)^2 ≤ (f (x 0))^2} ≤ volume.real ({v} : Set ℝᵈ) := by
      simpa [Measure.real] using ENNReal.toReal_mono hsing_fin hmeas
    rw [hsing] at hmeas_real
    exact le_antisymm hmeas_real (by positivity)


/-! ### Integrability on bounded measurable sets -/

lemma integrableOn_id_bounded_measurable [NeZero d] {s : Set ℝᵈ}
    (hs_meas : MeasurableSet s) (hs_bdd : Bornology.IsBounded s) :
    IntegrableOn (fun x : ℝᵈ => x) s volume := by
  let Kset : Set ℝᵈ := closure s
  have hK_compact : IsCompact Kset := Metric.isCompact_of_isClosed_isBounded isClosed_closure hs_bdd.closure
  exact continuous_id.continuousOn.integrableOn_of_subset_isCompact hK_compact hs_meas subset_closure
    (by simpa [Kset] using hs_bdd.measure_lt_top.ne)

/-! ### Complementary halfspaces of a bounded set -/

lemma measureReal_union_halfspaces [NeZero d] {K : Set ℝᵈ} (hK_meas : MeasurableSet K)
    (hK_finite : volume K < ⊤) {η : ℝᵈ} (hη : η ≠ 0) {c : ℝ} :
    volume.real (K ∩ {x : ℝᵈ | ⟪x, η⟫ ≤ c}) + volume.real (K ∩ {x : ℝᵈ | c ≤ ⟪x, η⟫}) =
      volume.real K := by
  let A : Set ℝᵈ := K ∩ {x : ℝᵈ | ⟪x, η⟫ ≤ c}
  let B : Set ℝᵈ := K ∩ {x : ℝᵈ | c ≤ ⟪x, η⟫}
  have hu_meas : Measurable (fun x : ℝᵈ => ⟪x, η⟫) := by
    exact (continuous_id.inner continuous_const).measurable
  have hA_meas : MeasurableSet A := hK_meas.inter (measurableSet_le hu_meas measurable_const)
  have hB_meas : MeasurableSet B := hK_meas.inter (measurableSet_le measurable_const hu_meas)
  have hAB_sub : A ∩ B ⊆ {x : ℝᵈ | ⟪x, η⟫ = c} := by
    intro x hx
    rcases hx with ⟨⟨hxK, hxle⟩, hxK', hxge⟩
    exact le_antisymm hxle hxge
  have hAB_zero : volume (A ∩ B) = 0 := by
    apply le_antisymm ?_ bot_le
    calc
      volume (A ∩ B) ≤ volume {x : ℝᵈ | ⟪x, η⟫ = c} := measure_mono (μ := volume) hAB_sub
      _ = 0 := volume_hyperplane_eq_zero hη c
  have hAB_disj : AEDisjoint volume A B := by
    rw [AEDisjoint]
    exact hAB_zero
  have hAB_union : A ∪ B = K := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx <;> exact hx.1
    · intro hxK
      by_cases hle : ⟪x, η⟫ ≤ c
      · exact Or.inl ⟨hxK, hle⟩
      · exact Or.inr ⟨hxK, le_of_lt (lt_of_not_ge hle)⟩
  have hA_fin : volume A < ⊤ := lt_of_le_of_lt (measure_mono (μ := volume) (fun x hx => hx.1)) hK_finite
  have hB_fin : volume B < ⊤ := lt_of_le_of_lt (measure_mono (μ := volume) (fun x hx => hx.1)) hK_finite
  have hmeasure : volume (A ∪ B) = volume A + volume B := by
    exact measure_union₀ hB_meas.nullMeasurableSet hAB_disj
  rw [hAB_union] at hmeasure
  have hreal : volume.real K = volume.real A + volume.real B := by
    rw [Measure.real, hmeasure, ENNReal.toReal_add hA_fin.ne hB_fin.ne]
    rfl
  rw [hreal]

lemma setAverage_sub_eq_neg_sub_of_measure_eq_union [NeZero d]
    {K A B : Set ℝᵈ} (hK_meas : MeasurableSet K) (hK_bdd : Bornology.IsBounded K)
    (hA_meas : MeasurableSet A) (hB_meas : MeasurableSet B)
    (hAB_disj : AEDisjoint volume A B) (hAB_union : A ∪ B = K)
    (hA_fin : volume A < ⊤) (hB_fin : volume B < ⊤)
    (hK_vol_pos : 0 < volume.real K)
    (hA_vol : volume.real A = volume.real K / 2)
    (hB_vol : volume.real B = volume.real K / 2) :
    (⨍ x in K, x) - (⨍ x in A, x) = -((⨍ x in K, x) - (⨍ x in B, x)) := by
  have hA_bdd : Bornology.IsBounded A := hK_bdd.subset (by intro x hx; exact (by
    have hxK : x ∈ K := by
      rw [← hAB_union]
      exact Or.inl hx
    exact hxK))
  have hB_bdd : Bornology.IsBounded B := hK_bdd.subset (by intro x hx; exact (by
    have hxK : x ∈ K := by
      rw [← hAB_union]
      exact Or.inr hx
    exact hxK))
  have hA_int : IntegrableOn (fun x : ℝᵈ => x) A volume :=
    integrableOn_id_bounded_measurable hA_meas hA_bdd
  have hB_int : IntegrableOn (fun x : ℝᵈ => x) B volume :=
    integrableOn_id_bounded_measurable hB_meas hB_bdd
  have hK_int : IntegrableOn (fun x : ℝᵈ => x) K volume :=
    integrableOn_id_bounded_measurable hK_meas hK_bdd
  have hav := MeasureTheory.average_union (μ := volume) (f := fun x : ℝᵈ => x)
    hAB_disj hB_meas.nullMeasurableSet hA_fin.ne hB_fin.ne hA_int hB_int
  have hcoeffA : volume.real A / (volume.real A + volume.real B) = (1 / 2 : ℝ) := by
    rw [hA_vol, hB_vol]
    field_simp [ne_of_gt hK_vol_pos]
    ring
  have hcoeffB : volume.real B / (volume.real A + volume.real B) = (1 / 2 : ℝ) := by
    rw [hA_vol, hB_vol]
    field_simp [ne_of_gt hK_vol_pos]
    ring
  have hav' : ⨍ x in K, x = (1 / 2 : ℝ) • (⨍ x in A, x) + (1 / 2 : ℝ) • (⨍ x in B, x) := by
    simpa [hAB_union, hcoeffA, hcoeffB] using hav
  have h2 : (2 : ℝ) • (⨍ x in K, x) = (⨍ x in A, x) + (⨍ x in B, x) := by
    rw [hav', ← smul_add]
    simp
  have h2' : (⨍ x in K, x) + (⨍ x in K, x) = (⨍ x in A, x) + (⨍ x in B, x) := by
    simpa [two_smul ℝ] using h2
  have hzero : ((⨍ x in K, x) - (⨍ x in A, x)) + ((⨍ x in K, x) - (⨍ x in B, x)) = 0 := by
    calc
      ((⨍ x in K, x) - (⨍ x in A, x)) + ((⨍ x in K, x) - (⨍ x in B, x))
          = ((⨍ x in K, x) + (⨍ x in K, x)) - ((⨍ x in A, x) + (⨍ x in B, x)) := by abel
      _ = 0 := by rw [h2']; abel
  rw [eq_neg_iff_add_eq_zero]
  exact hzero

/-! ### Halfspace in the `e0-last` plane -/

lemma halfspace_plane_last_le_slope_intercept [NeZero d] (hd : 2 ≤ d)
    {a b s c t : ℝ} (hb : 0 < b) (hs : s = -a / b) (hc : c = t / b) :
    let last : Fin d := ⟨d - 1, by omega⟩
    let e0 : ℝᵈ := EuclideanSpace.single (0 : Fin d) (1 : ℝ)
    let elast : ℝᵈ := EuclideanSpace.single last (1 : ℝ)
    {x : ℝᵈ | ⟪x, a • e0 + b • elast⟫ ≤ t} = {x : ℝᵈ | x last ≤ s * x 0 + c} := by
  intro last e0 elast
  ext x
  constructor
  · intro hx
    have hx' : a * x 0 + b * x last ≤ t := by
      simpa [e0, elast, inner_add_right, inner_smul_right, EuclideanSpace.inner_single_right] using hx
    have hle : b * x last ≤ t - a * x 0 := by linarith
    have hdiv : x last ≤ (t - a * x 0) / b := by
      rw [le_div_iff₀ hb]
      nlinarith
    rw [hs, hc]
    have hcalc : (t - a * x 0) / b = -a / b * x 0 + t / b := by
      field_simp [ne_of_gt hb]
      ring
    rw [hcalc] at hdiv
    change x.ofLp last ≤ -a / b * x.ofLp 0 + t / b
    exact hdiv
  · intro hx
    have hx' : x last ≤ -a / b * x 0 + t / b := by simpa [hs, hc] using hx
    have hle : b * x last ≤ b * (-a / b * x 0 + t / b) :=
      mul_le_mul_of_nonneg_left hx' (le_of_lt hb)
    have hcalc : b * (-a / b * x 0 + t / b) = -a * x 0 + t := by
      field_simp [ne_of_gt hb]
    have hsum : a * x 0 + b * x last ≤ t := by linarith
    simpa [e0, elast, inner_add_right, inner_smul_right, EuclideanSpace.inner_single_right] using hsum

lemma halfspace_last_le_slope_intercept_eq_inner_single [NeZero d] (hd : 2 ≤ d) {s c : ℝ} :
    let last : Fin d := ⟨d - 1, by omega⟩
    let n_s : ℝᵈ := EuclideanSpace.single (0 : Fin d) (-s) + EuclideanSpace.single last (1 : ℝ)
    {x : ℝᵈ | x last ≤ s * x 0 + c} = {x : ℝᵈ | ⟪x, n_s⟫ ≤ c} := by
  intro last n_s
  ext x
  constructor
  · intro hx
    have hx' : x.ofLp last ≤ s * x.ofLp 0 + c := by simpa using hx
    change ⟪x, n_s⟫ ≤ c
    have hinner : ⟪x, n_s⟫ = -s * x.ofLp 0 + x.ofLp last := by
      simp [n_s, inner_add_right, EuclideanSpace.inner_single_right]
    rw [hinner]
    nlinarith
  · intro hx
    have hinner : ⟪x, n_s⟫ = -s * x.ofLp 0 + x.ofLp last := by
      simp [n_s, inner_add_right, EuclideanSpace.inner_single_right]
    have hx' : -s * x.ofLp 0 + x.ofLp last ≤ c := by
      simpa [hinner] using hx
    change x.ofLp last ≤ s * x.ofLp 0 + c
    nlinarith

lemma reflection_hyperplane_single_fixes_of_inner_eq_zero [NeZero d] {j : Fin d} {w : ℝᵈ}
    (hw : ⟪w, EuclideanSpace.single j (1 : ℝ)⟫ = 0) :
    Submodule.reflection ((ℝ ∙ EuclideanSpace.single j (1 : ℝ))ᗮ) w = w := by
  apply Submodule.reflection_mem_subspace_eq_self
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
  exact hw

lemma coord_eq_zero_of_reflection_hyperplane_fix [NeZero d] {j : Fin d} {v : ℝᵈ}
    (h : (Submodule.reflection ((ℝ ∙ EuclideanSpace.single j (1 : ℝ))ᗮ)) v = v) :
    v j = 0 := by
  let L : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ := Submodule.reflection ((ℝ ∙ EuclideanSpace.single j (1 : ℝ))ᗮ)
  have hL_single : L (EuclideanSpace.single j (1 : ℝ)) = -EuclideanSpace.single j (1 : ℝ) := by
    simpa using Submodule.reflection_orthogonalComplement_singleton_eq_neg (EuclideanSpace.single j (1 : ℝ))
  have hLv : (L v) j = - v j := by
    calc
      (L v) j = ⟪L v, EuclideanSpace.single j (1 : ℝ)⟫ := by
        rw [EuclideanSpace.inner_single_right]
        simp
      _ = ⟪v, L (EuclideanSpace.single j (1 : ℝ))⟫ := by
        have hinner := LinearIsometryEquiv.inner_map_map L v (L.symm (EuclideanSpace.single j (1 : ℝ)))
        simpa [L] using hinner
      _ = ⟪v, -EuclideanSpace.single j (1 : ℝ)⟫ := by rw [hL_single]
      _ = - v j := by
        simp [inner_neg_right, EuclideanSpace.inner_single_right]
  have hcoord : (L v) j = v j := by
    rw [h]
  linarith

/-! ### The main reduction -/

lemma odd_floating_of_family [NeZero d] {R₁ R₂ : ℝ} {f h : ℝ → ℝ}
    (n : ℕ) (hdn : d = 2 * n + 1) (hn : 1 ≤ n)
    (hf_support : f.support ⊆ Set.Icc (-R₁) R₂)
    (hf_smooth : ContDiffOn ℝ ∞ f (Set.Ioo (-R₁) R₂))
    (hf_conc : ConcaveOn ℝ (Set.Icc (-R₁) R₂) f)
    (hf_left : f (-R₁) = 0) (hf_right : f R₂ = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-R₁) R₂, 0 < f t)
    (hh_smooth : ContDiff ℝ ∞ h)
    (h0 : h 0 = 0)
    (hfamily_volume : ∀ s > 0,
      let K : Set (EuclideanSpace ℝ (Fin d)) := {x | x 0 ∈ Set.Icc (-R₁) R₂ ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
      volume.real (K ∩ {x | x ⟨d-1, by exact Nat.sub_lt (Nat.pos_of_neZero d) (by decide : 0 < 1)⟩ ≤ s * x 0 + h s}) =
        volume.real K / 2)
    (hfamily_centroid : ∀ s > 0,
      let K : Set (EuclideanSpace ℝ (Fin d)) := {x | x 0 ∈ Set.Icc (-R₁) R₂ ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
      let nvec : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single (0 : Fin d) (-s) +
        EuclideanSpace.single (⟨d-1, by exact Nat.sub_lt (Nat.pos_of_neZero d) (by decide : 0 < 1)⟩ : Fin d) 1
      (⨍ x in K, x) - (⨍ x in (K ∩ {x | x ⟨d-1, by exact Nat.sub_lt (Nat.pos_of_neZero d) (by decide : 0 < 1)⟩ ≤ s * x 0 + h s}), x) ∈
        ℝ ∙ nvec) :
    let K : Set (EuclideanSpace ℝ (Fin d)) := {x | x 0 ∈ Set.Icc (-R₁) R₂ ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
    ∀ ξ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1, ∀ t : ℝ,
      volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ t}) = volume.real K / 2 →
      (⨍ x in K, x) - (⨍ x in (K ∩ {x | ⟪x, ξ⟫ ≤ t}), x) ∈ ℝ ∙ (ξ : EuclideanSpace ℝ (Fin d)) := by
  classical
  let last : Fin d := ⟨d - 1, by omega⟩
  let e0 : ℝᵈ := EuclideanSpace.single (0 : Fin d) (1 : ℝ)
  let elast : ℝᵈ := EuclideanSpace.single last (1 : ℝ)
  let K : Set ℝᵈ := {x | x 0 ∈ Set.Icc (-R₁) R₂ ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
  have hd2 : 2 ≤ d := by omega
  change ∀ ξ : Metric.sphere (0 : ℝᵈ) 1, ∀ t : ℝ,
      volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ t}) = volume.real K / 2 →
      (⨍ x in K, x) - (⨍ x in (K ∩ {x | ⟪x, ξ⟫ ≤ t}), x) ∈ ℝ ∙ (ξ : ℝᵈ)
  by_cases hK0 : volume.real K = 0
  · intro ξ t ht
    have hH0 : volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ t}) = 0 := by
      rw [ht, hK0]
      norm_num
    have hKavg : (⨍ x in K, x) = (0 : ℝᵈ) := by
      simp [MeasureTheory.setAverage_eq, hK0]
    have hHavg : (⨍ x in (K ∩ {x | ⟪x, ξ⟫ ≤ t}), x) = (0 : ℝᵈ) := by
      simp [MeasureTheory.setAverage_eq, hH0]
    rw [hKavg, hHavg, sub_zero]
    exact Submodule.zero_mem _
  · have hRlt : -R₁ < R₂ := by
      by_contra hnot
      have hzero := body_of_revolution_measure_zero_of_not_lt (d := d) (f := f) (R₁ := R₁) (R₂ := R₂) hf_left hf_right hnot
      exact hK0 (by simpa [K] using hzero)
    have hK_meas : MeasurableSet K := by
      exact body_of_revolution_measurable (d := d) (f := f) (R₁ := R₁) (R₂ := R₂) hf_support hf_smooth hf_left hf_right
    have hK_conv : Convex ℝ K := by
      exact body_of_revolution_convex (d := d) (f := f) (R₁ := R₁) (R₂ := R₂) hf_conc hf_left hf_right
    have hK_bdd : Bornology.IsBounded K := by
      exact body_of_revolution_bounded (d := d) (f := f) (R₁ := R₁) (R₂ := R₂) hf_conc hf_left hf_right
    have hK_finite : volume K < ⊤ := by
      exact hK_bdd.measure_lt_top
    have hf_cont : ContinuousOn f (Set.Ioo (-R₁) R₂) := hf_smooth.continuousOn
    have hK_int : (interior K).Nonempty := by
      simpa [K] using interior_nonempty_body_of_revolution (d := d) (R₁ := R₁) (R₂ := R₂) (f := f) hRlt hf_cont hf_pos
    have hK_vol_pos : 0 < volume.real K := by
      have hU_open : IsOpen (interior K) := isOpen_interior
      have hU_pos : 0 < volume (interior K) := hU_open.measure_pos (μ := volume) hK_int
      have hU_le : volume (interior K) ≤ volume K := measure_mono (μ := volume) interior_subset
      have hU_fin : volume (interior K) < ⊤ := lt_of_le_of_lt hU_le hK_finite
      have hU_real_pos : 0 < volume.real (interior K) := by
        rw [Measure.real]
        exact ENNReal.toReal_pos (ne_of_gt hU_pos) hU_fin.ne
      have hmono : volume.real (interior K) ≤ volume.real K := by
        simpa [Measure.real] using ENNReal.toReal_mono hK_finite.ne hU_le
      exact lt_of_lt_of_le hU_real_pos hmono
    have hhalf_pos : 0 < volume.real K / 2 := by nlinarith
    have hhalf_lt : volume.real K / 2 < volume.real K := by nlinarith
    intro ξ t ht
    let ξv : ℝᵈ := ξ
    obtain ⟨R, hR0, a, b, hb_nonneg, hRξ⟩ := exists_tail_linearIsometryEquiv_map_to_last (d := d) hd2 ξv
    let H : Set ℝᵈ := K ∩ {x | ⟪x, ξv⟫ ≤ t}
    have hvolH : volume.real H = volume.real K / 2 := by simpa [H] using ht
    have hRK : R '' K = K := by
      simpa [K] using body_of_revolution_tail_linearIsometryEquiv_image (d := d) (R₁ := R₁) (R₂ := R₂) (f := f) R hR0
    have hRimageH : R '' H = K ∩ {y | ⟪y, R ξv⟫ ≤ t} := by
      calc
        R '' H = R '' K ∩ R '' {x | ⟪x, ξv⟫ ≤ t} := by
          dsimp [H]
          rw [Set.image_inter R.injective]
        _ = K ∩ {y | ⟪y, R ξv⟫ ≤ t} := by
          rw [hRK, halfspace_image_linearIsometryEquiv R ξv t]
    have hvol_image : volume H = volume (R '' H) := by
      have hpre := R.measurePreserving.measure_preimage_emb R.toMeasurableEquiv.measurableEmbedding (R '' H)
      have hpre' : R ⁻¹' (R '' H) = H := Set.preimage_image_eq H R.injective
      rwa [hpre'] at hpre
    have hvolR : volume.real (K ∩ {y | ⟪y, R ξv⟫ ≤ t}) = volume.real K / 2 := by
      have hvol_image_real : volume.real H = volume.real (R '' H) := congrArg ENNReal.toReal hvol_image
      rw [hRimageH] at hvol_image_real
      rw [← hvol_image_real]
      exact hvolH
    have hRavgK : R (⨍ x in K, x) = ⨍ x in K, x := by
      exact setAverage_linearIsometryEquiv_invariant R K hRK
    have hRavgH : R (⨍ x in H, x) = ⨍ y in (K ∩ {y | ⟪y, R ξv⟫ ≤ t}), y := by
      have h1 := average_image_linearIsometryEquiv R H
      simpa [hRimageH] using h1
    have hrot : (⨍ x in K, x) - (⨍ x in (K ∩ {x | ⟪x, R ξv⟫ ≤ t}), x) ∈ ℝ ∙ (R ξv) := by
      let η : ℝᵈ := R ξv
      let Drot : ℝᵈ := (⨍ x in K, x) - (⨍ x in (K ∩ {x | ⟪x, η⟫ ≤ t}), x)
      change Drot ∈ ℝ ∙ η
      have hη : η = a • e0 + b • elast := hRξ
      have hlast_ne : last ≠ 0 := by
        dsimp [last]
        exact Fin.ne_of_val_ne (by simp; omega)
      by_cases hb0 : b = 0
      · have hη_e0 : η = a • e0 := by simpa [hb0] using hη
        have ha_ne : a ≠ 0 := by
          intro ha0
          have hη0 : η = 0 := by simp [hη_e0, ha0]
          have hnormη : ‖η‖ = 0 := by simp [hη0]
          have hnormξ : ‖η‖ = ‖ξv‖ := R.norm_map ξv
          have hξnorm : ‖ξv‖ = 1 := by
            simpa [ξv] using ξ.2
          linarith
        have hsp : ℝ ∙ η = ℝ ∙ e0 := by
          rw [hη_e0, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha_ne) e0]
        let L0 : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ := Submodule.reflection (ℝ ∙ e0)
        have hL0e0 : L0 e0 = e0 := by
          exact Submodule.reflection_mem_subspace_eq_self (Submodule.mem_span_singleton_self e0)
        have hL0K : L0 '' K = K := by
          simpa [K] using body_of_revolution_tail_linearIsometryEquiv_image (d := d) (R₁ := R₁) (R₂ := R₂) (f := f) L0 hL0e0
        have hL0η : L0 η = η := by
          rw [hη_e0, map_smul, hL0e0]
        have hL0half : L0 '' {x : ℝᵈ | ⟪x, η⟫ ≤ t} = {x : ℝᵈ | ⟪x, η⟫ ≤ t} := by
          rw [halfspace_image_linearIsometryEquiv L0 η t, hL0η]
        have hL0H : L0 '' (K ∩ {x : ℝᵈ | ⟪x, η⟫ ≤ t}) = K ∩ {x : ℝᵈ | ⟪x, η⟫ ≤ t} := by
          calc
            L0 '' (K ∩ {x : ℝᵈ | ⟪x, η⟫ ≤ t})
                = L0 '' K ∩ L0 '' {x : ℝᵈ | ⟪x, η⟫ ≤ t} := by rw [Set.image_inter L0.injective]
            _ = K ∩ {x : ℝᵈ | ⟪x, η⟫ ≤ t} := by rw [hL0K, hL0half]
        have hL0avgK : L0 (⨍ x in K, x) = ⨍ x in K, x :=
          setAverage_linearIsometryEquiv_invariant L0 K hL0K
        have hL0avgH : L0 (⨍ x in (K ∩ {x : ℝᵈ | ⟪x, η⟫ ≤ t}), x) =
            ⨍ x in (K ∩ {x : ℝᵈ | ⟪x, η⟫ ≤ t}), x :=
          setAverage_linearIsometryEquiv_invariant L0 (K ∩ {x : ℝᵈ | ⟪x, η⟫ ≤ t}) hL0H
        have hL0D : L0 Drot = Drot := by
          dsimp [Drot]
          rw [map_sub, hL0avgK, hL0avgH]
        have hD_mem_e0 : Drot ∈ ℝ ∙ e0 := by
          exact (Submodule.reflection_eq_self_iff (x := Drot)).1 hL0D
        simpa [hsp] using hD_mem_e0
      · have hbpos : 0 < b := lt_of_le_of_ne hb_nonneg (Ne.symm hb0)
        have hdirect_case : ∀ {a' b' : ℝ}, 0 < b' → a' < 0 → ∀ {t' : ℝ},
            volume.real (K ∩ {x : ℝᵈ | ⟪x, a' • e0 + b' • elast⟫ ≤ t'}) = volume.real K / 2 →
            (⨍ x in K, x) - (⨍ x in (K ∩ {x : ℝᵈ | ⟪x, a' • e0 + b' • elast⟫ ≤ t'}), x) ∈
              ℝ ∙ (a' • e0 + b' • elast) := by
          intro a' b' hb' ha' t' hvol'
          let s : ℝ := -a' / b'
          have hs_pos : 0 < s := by
            dsimp [s]
            exact div_pos (neg_pos.mpr ha') hb'
          let c : ℝ := t' / b'
          let n_s : ℝᵈ := EuclideanSpace.single (0 : Fin d) (-s) + EuclideanSpace.single last (1 : ℝ)
          have hlast_ne : last ≠ 0 := by
            dsimp [last]
            exact Fin.ne_of_val_ne (by simp; omega)
          have hn_s_ne : n_s ≠ 0 := by
            intro h
            have hlast_val : n_s last = 1 := by simp [n_s, hlast_ne]
            have hlast := congrArg (fun v : ℝᵈ => v last) h
            simp [hlast_val] at hlast
          have hset_rot : {x : ℝᵈ | ⟪x, a' • e0 + b' • elast⟫ ≤ t'} = {x : ℝᵈ | x last ≤ s * x 0 + c} := by
            have hset := halfspace_plane_last_le_slope_intercept (d := d) hd2 (a := a') (b := b') (s := s) (c := c) (t := t') hb' (by dsimp [s]) (by dsimp [c])
            simpa using hset
          have hset_ns : {x : ℝᵈ | x last ≤ s * x 0 + c} = {x : ℝᵈ | ⟪x, n_s⟫ ≤ c} := by
            exact halfspace_last_le_slope_intercept_eq_inner_single (d := d) hd2 (s := s) (c := c)
          have hvol_c : volume.real (K ∩ {x : ℝᵈ | ⟪x, n_s⟫ ≤ c}) = volume.real K / 2 := by
            have h1 : K ∩ {x : ℝᵈ | ⟪x, a' • e0 + b' • elast⟫ ≤ t'} = K ∩ {x : ℝᵈ | x last ≤ s * x 0 + c} := by
              rw [hset_rot]
            have h2 : K ∩ {x : ℝᵈ | x last ≤ s * x 0 + c} = K ∩ {x : ℝᵈ | ⟪x, n_s⟫ ≤ c} := by
              rw [hset_ns]
            rwa [h1, h2] at hvol'
          have hvol_hs : volume.real (K ∩ {x : ℝᵈ | ⟪x, n_s⟫ ≤ h s}) = volume.real K / 2 := by
            have hfamvol := hfamily_volume s hs_pos
            have hset := halfspace_last_le_slope_intercept_eq_inner_single (d := d) hd2 (s := s) (c := h s)
            have h1 : K ∩ {x : ℝᵈ | x last ≤ s * x 0 + h s} = K ∩ {x : ℝᵈ | ⟪x, n_s⟫ ≤ h s} := by
              exact congrArg (fun A : Set ℝᵈ => K ∩ A) hset
            simpa [K] using h1 ▸ hfamvol
          have hc_pos : 0 < volume.real (K ∩ {x : ℝᵈ | ⟪x, n_s⟫ ≤ c}) := by
            rw [hvol_c]; exact hhalf_pos
          have hc_lt : volume.real (K ∩ {x : ℝᵈ | ⟪x, n_s⟫ ≤ c}) < volume.real K := by
            rw [hvol_c]; exact hhalf_lt
          have hh_pos : 0 < volume.real (K ∩ {x : ℝᵈ | ⟪x, n_s⟫ ≤ h s}) := by
            rw [hvol_hs]; exact hhalf_pos
          have hh_lt : volume.real (K ∩ {x : ℝᵈ | ⟪x, n_s⟫ ≤ h s}) < volume.real K := by
            rw [hvol_hs]; exact hhalf_lt
          have hc_eq : c = h s := by
            exact Commons.Geometry.Convex.eq_of_volume_halfspace_eq_of_convex
              (hK_meas := hK_meas) (hK_conv := hK_conv) (hK_int := hK_int) (hK_finite := hK_finite)
              (hξ := hn_s_ne) (a := c) (b := h s)
              hc_pos hc_lt hh_pos hh_lt (by rw [hvol_c, hvol_hs])
          have hfam_cent : (⨍ x in K, x) - (⨍ x in (K ∩ {x : ℝᵈ | x last ≤ s * x 0 + h s}), x) ∈ ℝ ∙ n_s := by
            simpa [K, n_s, e0, elast] using hfamily_centroid s hs_pos
          have hH_eq_fam : K ∩ {x : ℝᵈ | x last ≤ s * x 0 + h s} = K ∩ {x : ℝᵈ | ⟪x, a' • e0 + b' • elast⟫ ≤ t'} := by
            have hset_fam := halfspace_last_le_slope_intercept_eq_inner_single (d := d) hd2 (s := s) (c := h s)
            have h1 : K ∩ {x : ℝᵈ | x last ≤ s * x 0 + h s} = K ∩ {x : ℝᵈ | ⟪x, n_s⟫ ≤ h s} := by
              exact congrArg (fun A : Set ℝᵈ => K ∩ A) hset_fam
            have h2 : K ∩ {x : ℝᵈ | ⟪x, n_s⟫ ≤ h s} = K ∩ {x : ℝᵈ | ⟪x, n_s⟫ ≤ c} := by rw [hc_eq]
            have h3 : K ∩ {x : ℝᵈ | ⟪x, n_s⟫ ≤ c} = K ∩ {x : ℝᵈ | ⟪x, a' • e0 + b' • elast⟫ ≤ t'} := by
              rw [← hset_ns, ← hset_rot]
            rw [h1, h2, h3]
          have hD_mem_ns : (⨍ x in K, x) - (⨍ x in (K ∩ {x : ℝᵈ | ⟪x, a' • e0 + b' • elast⟫ ≤ t'}), x) ∈ ℝ ∙ n_s := by
            rw [← hH_eq_fam]
            exact hfam_cent
          have ha_eq : a' = -s * b' := by
            dsimp [s]
            field_simp [ne_of_gt hb']
          have hsp : ℝ ∙ (a' • e0 + b' • elast) = ℝ ∙ n_s := by
            have hn : a' • e0 + b' • elast = b' • n_s := by
              rw [ha_eq]
              ext i
              by_cases hi0 : i = 0
              · subst i
                simp [n_s, e0, elast, hlast_ne]
                ring
              · by_cases hilast : i = last
                · subst i
                  simp [n_s, e0, elast, hlast_ne]
                · simp [n_s, e0, elast, hi0, hilast]
            rw [hn, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (ne_of_gt hb')) n_s]
          simpa [hsp] using hD_mem_ns
        by_cases ha0 : a = 0
        · let c : ℝ := t / b
          let A0 : Set ℝᵈ := K ∩ {x : ℝᵈ | ⟪x, elast⟫ ≤ 0}
          let B0 : Set ℝᵈ := K ∩ {x : ℝᵈ | 0 ≤ ⟪x, elast⟫}
          have helast_ne : elast ≠ 0 := by
            intro h
            have hlast := congrArg (fun v : ℝᵈ => v last) h
            simp [elast] at hlast
          have hη_eq : η = b • elast := by
            rw [hη, ha0]
            simp
          have hset_c : {x : ℝᵈ | ⟪x, η⟫ ≤ t} = {x : ℝᵈ | ⟪x, elast⟫ ≤ c} := by
            ext x
            have hinner : ⟪x, η⟫ = b * ⟪x, elast⟫ := by
              rw [hη_eq]
              rw [inner_smul_right]
            constructor
            · intro hx
              change ⟪x, η⟫ ≤ t at hx
              rw [hinner] at hx
              rw [← le_div_iff₀' hbpos] at hx
              change ⟪x, elast⟫ ≤ c
              simpa [c] using hx
            · intro hx
              change ⟪x, elast⟫ ≤ c at hx
              change ⟪x, η⟫ ≤ t
              rw [hinner]
              rw [← le_div_iff₀' hbpos]
              simpa [c] using hx
          have hvolη : volume.real (K ∩ {x : ℝᵈ | ⟪x, η⟫ ≤ t}) = volume.real K / 2 := by
            simpa [η] using hvolR
          have hvol_c : volume.real (K ∩ {x : ℝᵈ | ⟪x, elast⟫ ≤ c}) = volume.real K / 2 := by
            rw [← hset_c]
            exact hvolη
          let L0 : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ := Submodule.reflection (ℝ ∙ e0)
          have hL0e0 : L0 e0 = e0 := by
            exact Submodule.reflection_mem_subspace_eq_self (Submodule.mem_span_singleton_self e0)
          have hL0K : L0 '' K = K := by
            simpa [K] using body_of_revolution_tail_linearIsometryEquiv_image (d := d) (R₁ := R₁) (R₂ := R₂) (f := f) L0 hL0e0
          have helast_orth : elast ∈ (ℝ ∙ e0)ᗮ := by
            rw [Submodule.mem_orthogonal_singleton_iff_inner_left, EuclideanSpace.inner_single_left]
            simp [elast, e0, hlast_ne]
          have hL0elast : L0 elast = -elast := by
            exact Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg helast_orth
          have hL0_halfA : L0 '' {x : ℝᵈ | ⟪x, elast⟫ ≤ 0} = {x : ℝᵈ | 0 ≤ ⟪x, elast⟫} := by
            rw [halfspace_image_linearIsometryEquiv L0 elast 0, hL0elast]
            ext x
            constructor
            · intro hx
              change ⟪x, -elast⟫ ≤ 0 at hx
              rw [inner_neg_right] at hx
              change 0 ≤ ⟪x, elast⟫
              linarith
            · intro hx
              change 0 ≤ ⟪x, elast⟫ at hx
              change ⟪x, -elast⟫ ≤ 0
              rw [inner_neg_right]
              linarith
          have hL0A0 : L0 '' A0 = B0 := by
            dsimp [A0, B0]
            calc
              L0 '' (K ∩ {x : ℝᵈ | ⟪x, elast⟫ ≤ 0})
                  = L0 '' K ∩ L0 '' {x : ℝᵈ | ⟪x, elast⟫ ≤ 0} := by
                    rw [Set.image_inter L0.injective]
              _ = K ∩ {x : ℝᵈ | 0 ≤ ⟪x, elast⟫} := by rw [hL0K, hL0_halfA]
          have hvol_A0_eq : volume.real A0 = volume.real B0 := by
            have hpre := L0.measurePreserving.measure_preimage_emb L0.toMeasurableEquiv.measurableEmbedding (L0 '' A0)
            have hpre' : L0 ⁻¹' (L0 '' A0) = A0 := Set.preimage_image_eq A0 L0.injective
            have himage : volume A0 = volume (L0 '' A0) := by
              rwa [hpre'] at hpre
            have himage_real := congrArg ENNReal.toReal himage
            rwa [hL0A0] at himage_real
          have hsum0 : volume.real A0 + volume.real B0 = volume.real K := by
            simpa [A0, B0] using measureReal_union_halfspaces (K := K) hK_meas hK_finite (η := elast) helast_ne (c := 0)
          have hvol_0 : volume.real A0 = volume.real K / 2 := by
            rw [hvol_A0_eq] at hsum0
            nlinarith
          have hvol_B0 : volume.real B0 = volume.real K / 2 := by
            rw [← hvol_A0_eq, hvol_0]
          have hc_pos : 0 < volume.real (K ∩ {x : ℝᵈ | ⟪x, elast⟫ ≤ c}) := by
            rw [hvol_c]
            exact hhalf_pos
          have hc_lt : volume.real (K ∩ {x : ℝᵈ | ⟪x, elast⟫ ≤ c}) < volume.real K := by
            rw [hvol_c]
            exact hhalf_lt
          have h0_pos : 0 < volume.real A0 := by
            rw [hvol_0]
            exact hhalf_pos
          have h0_lt : volume.real A0 < volume.real K := by
            rw [hvol_0]
            exact hhalf_lt
          have hvol_eq : volume.real (K ∩ {x : ℝᵈ | ⟪x, elast⟫ ≤ c}) = volume.real A0 := by
            rw [hvol_c, hvol_0]
          have hc_eq0 : c = 0 := by
            exact Commons.Geometry.Convex.eq_of_volume_halfspace_eq_of_convex
              (hK_meas := hK_meas) (hK_conv := hK_conv) (hK_int := hK_int) (hK_finite := hK_finite)
              (hξ := helast_ne) (a := c) (b := 0)
              hc_pos hc_lt h0_pos h0_lt hvol_eq
          have hH_eq_A0 : K ∩ {x : ℝᵈ | ⟪x, η⟫ ≤ t} = A0 := by
            rw [hset_c, hc_eq0]
          have hDrot_eq : Drot = (⨍ x in K, x) - (⨍ x in A0, x) := by
            dsimp [Drot]
            rw [hH_eq_A0]
          have hu_meas : Measurable (fun x : ℝᵈ => ⟪x, elast⟫) := by
            exact (continuous_id.inner continuous_const).measurable
          have hA0_meas : MeasurableSet A0 := hK_meas.inter (measurableSet_le hu_meas measurable_const)
          have hB0_meas : MeasurableSet B0 := hK_meas.inter (measurableSet_le measurable_const hu_meas)
          have hA0B0_sub : A0 ∩ B0 ⊆ {x : ℝᵈ | ⟪x, elast⟫ = 0} := by
            intro x hx
            rcases hx with ⟨⟨hxK, hxle⟩, hxK', hxge⟩
            exact le_antisymm hxle hxge
          have hA0B0_zero : volume (A0 ∩ B0) = 0 := by
            apply le_antisymm ?_ bot_le
            calc
              volume (A0 ∩ B0) ≤ volume {x : ℝᵈ | ⟪x, elast⟫ = 0} := measure_mono (μ := volume) hA0B0_sub
              _ = 0 := volume_hyperplane_eq_zero helast_ne 0
          have hA0B0_disj : AEDisjoint volume A0 B0 := by
            rw [AEDisjoint]
            exact hA0B0_zero
          have hA0B0_union : A0 ∪ B0 = K := by
            ext x
            constructor
            · intro hx
              rcases hx with hx | hx <;> exact hx.1
            · intro hxK
              by_cases hle : ⟪x, elast⟫ ≤ 0
              · exact Or.inl ⟨hxK, hle⟩
              · exact Or.inr ⟨hxK, le_of_lt (lt_of_not_ge hle)⟩
          have hA0_fin : volume A0 < ⊤ := lt_of_le_of_lt (measure_mono (μ := volume) (fun x hx => hx.1)) hK_finite
          have hB0_fin : volume B0 < ⊤ := lt_of_le_of_lt (measure_mono (μ := volume) (fun x hx => hx.1)) hK_finite
          have hrel0 := setAverage_sub_eq_neg_sub_of_measure_eq_union
            (hK_meas := hK_meas) (hK_bdd := hK_bdd)
            (hA_meas := hA0_meas) (hB_meas := hB0_meas)
            (hAB_disj := hA0B0_disj) (hAB_union := hA0B0_union)
            (hA_fin := hA0_fin) (hB_fin := hB0_fin)
            (hK_vol_pos := hK_vol_pos) (hA_vol := hvol_0) (hB_vol := hvol_B0)
          have hL0avgK : L0 (⨍ x in K, x) = ⨍ x in K, x :=
            setAverage_linearIsometryEquiv_invariant L0 K hL0K
          have hL0avgA0 : L0 (⨍ x in A0, x) = ⨍ x in B0, x := by
            have h1 := average_image_linearIsometryEquiv L0 A0
            simpa [hL0A0] using h1
          have hneg0 : (⨍ x in K, x) - (⨍ x in B0, x) = -((⨍ x in K, x) - (⨍ x in A0, x)) := by
            have h := congrArg (fun v : ℝᵈ => -v) hrel0
            simpa using h.symm
          have hL0Drot : L0 Drot = -Drot := by
            rw [hDrot_eq]
            rw [map_sub, hL0avgK, hL0avgA0]
            exact hneg0
          have hDrot0 : Drot 0 = 0 := by
            have h1 : ⟪L0 Drot, e0⟫ = ⟪Drot, e0⟫ := by
              have h := LinearIsometryEquiv.inner_map_map L0 Drot e0
              simpa [hL0e0] using h
            have h := congrArg (fun v : ℝᵈ => ⟪v, e0⟫) hL0Drot
            rw [h1] at h
            rw [inner_neg_left] at h
            have hinner : ⟪Drot, e0⟫ = 0 := by linarith
            have hcoord := coord0_eq_inner_single Drot
            simpa [e0] using hcoord.trans hinner
          have htail_zero : ∀ j : Fin d, j ≠ 0 → j ≠ last → Drot j = 0 := by
            intro j hj0 hjlast
            let Lj : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ := Submodule.reflection ((ℝ ∙ EuclideanSpace.single j (1:ℝ))ᗮ)
            have hLj_e0 : Lj e0 = e0 := by
              apply reflection_hyperplane_single_fixes_of_inner_eq_zero (j := j) (w := e0)
              dsimp [e0]
              rw [EuclideanSpace.inner_single_right]
              simp [hj0]
            have hLj_elast : Lj elast = elast := by
              apply reflection_hyperplane_single_fixes_of_inner_eq_zero (j := j) (w := elast)
              rw [EuclideanSpace.inner_single_right]
              simp [elast, hjlast]
            have hLjK : Lj '' K = K := by
              simpa [K] using body_of_revolution_tail_linearIsometryEquiv_image (d := d) (R₁ := R₁) (R₂ := R₂) (f := f) Lj hLj_e0
            have hLj_half : Lj '' {x : ℝᵈ | ⟪x, elast⟫ ≤ 0} = {x : ℝᵈ | ⟪x, elast⟫ ≤ 0} := by
              rw [halfspace_image_linearIsometryEquiv Lj elast 0, hLj_elast]
            have hLjA0 : Lj '' A0 = A0 := by
              dsimp [A0]
              calc
                Lj '' (K ∩ {x : ℝᵈ | ⟪x, elast⟫ ≤ 0})
                    = Lj '' K ∩ Lj '' {x : ℝᵈ | ⟪x, elast⟫ ≤ 0} := by
                      rw [Set.image_inter Lj.injective]
                _ = K ∩ {x : ℝᵈ | ⟪x, elast⟫ ≤ 0} := by rw [hLjK, hLj_half]
            have hLjavgK : Lj (⨍ x in K, x) = ⨍ x in K, x :=
              setAverage_linearIsometryEquiv_invariant Lj K hLjK
            have hLjavgA0 : Lj (⨍ x in A0, x) = ⨍ x in A0, x :=
              setAverage_linearIsometryEquiv_invariant Lj A0 hLjA0
            have hLjDrot : Lj Drot = Drot := by
              rw [hDrot_eq]
              rw [map_sub, hLjavgK, hLjavgA0]
            exact coord_eq_zero_of_reflection_hyperplane_fix (j := j) (v := Drot) (by simpa [Lj] using hLjDrot)
          have hDrot_eq_elast : Drot = (Drot last) • elast := by
            ext i
            by_cases hilast : i = last
            · subst i
              simp [elast]
            · by_cases hi0 : i = 0
              · subst i
                rw [hDrot0]
                simp [elast, hlast_ne]
              · have hcoord := htail_zero i hi0 hilast
                rw [hcoord]
                simp [elast, hilast]
          have hD_mem_elast : Drot ∈ ℝ ∙ elast := by
            rw [Submodule.mem_span_singleton]
            exact ⟨Drot last, hDrot_eq_elast.symm⟩
          have hsp_η : ℝ ∙ η = ℝ ∙ elast := by
            rw [hη_eq, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (ne_of_gt hbpos)) elast]
          simpa [hsp_η] using hD_mem_elast
        · by_cases haneg : a < 0
          · have hvolη : volume.real (K ∩ {x : ℝᵈ | ⟪x, a • e0 + b • elast⟫ ≤ t}) = volume.real K / 2 := by
              simpa [η, hη] using hvolR
            have hdir := hdirect_case hbpos haneg (t' := t) hvolη
            simpa [Drot, η, hη] using hdir
          · have hapos : 0 < a := lt_of_le_of_ne (le_of_not_gt haneg) (Ne.symm ha0)
            let η' : ℝᵈ := (-a) • e0 + b • elast
            let Hpos : Set ℝᵈ := K ∩ {x : ℝᵈ | ⟪x, η⟫ ≤ t}
            let Hneg : Set ℝᵈ := K ∩ {x : ℝᵈ | t ≤ ⟪x, η⟫}
            let Hneg' : Set ℝᵈ := K ∩ {x : ℝᵈ | ⟪x, η'⟫ ≤ -t}
            have hη_ne : η ≠ 0 := by
              intro hη0
              have hcoord := congrArg (fun v : ℝᵈ => v last) hη0
              have hη_last : η last = b := by
                rw [hη]
                simp [e0, elast, hlast_ne]
              rw [hη_last] at hcoord
              simp at hcoord
              linarith [hbpos]
            have hvolHpos : volume.real Hpos = volume.real K / 2 := by
              dsimp [Hpos]
              simpa [η] using hvolR
            have hsum : volume.real (K ∩ {x : ℝᵈ | ⟪x, η⟫ ≤ t}) + volume.real Hneg = volume.real K := by
              simpa [Hneg] using measureReal_union_halfspaces (K := K) hK_meas hK_finite (η := η) hη_ne (c := t)
            have hvolHpos' : volume.real (K ∩ {x : ℝᵈ | ⟪x, η⟫ ≤ t}) = volume.real K / 2 := by
              simpa [η] using hvolR
            have hvolcomp : volume.real Hneg = volume.real K / 2 := by
              have hsum' := hsum
              rw [hvolHpos'] at hsum'
              nlinarith
            let Lflip : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ := Submodule.reflection ((ℝ ∙ elast)ᗮ)
            have hLflip_e0 : Lflip e0 = e0 := by
              apply reflection_hyperplane_single_fixes_of_inner_eq_zero (j := last) (w := e0)
              dsimp [e0]
              rw [EuclideanSpace.inner_single_right]
              simp [hlast_ne]
            have hLflip_elast : Lflip elast = -elast := by
              dsimp [Lflip]
              simpa [elast] using (Submodule.reflection_orthogonalComplement_singleton_eq_neg (EuclideanSpace.single last (1:ℝ)))
            have hLflip_inv : Function.Involutive Lflip := Submodule.reflection_involutive ((ℝ ∙ elast)ᗮ)
            have hLflipK : Lflip '' K = K := by
              simpa [K] using body_of_revolution_tail_linearIsometryEquiv_image (d := d) (R₁ := R₁) (R₂ := R₂) (f := f) Lflip hLflip_e0
            have hLflip_η' : Lflip η' = -η := by
              dsimp [η']
              rw [map_add, map_smul, map_smul, hLflip_e0, hLflip_elast, hη]
              ext i
              by_cases hi0 : i = 0
              · subst i
                simp [e0, elast, hlast_ne]
              · by_cases hilast : i = last
                · subst i
                  simp [e0, elast, hlast_ne]
                · simp [e0, elast, hi0, hilast]
            have hset_ge : {x : ℝᵈ | t ≤ ⟪x, η⟫} = {x : ℝᵈ | ⟪x, -η⟫ ≤ -t} := by
              ext x
              constructor
              · intro hx
                change t ≤ ⟪x, η⟫ at hx
                change ⟪x, -η⟫ ≤ -t
                rw [inner_neg_right]
                linarith
              · intro hx
                change ⟪x, -η⟫ ≤ -t at hx
                rw [inner_neg_right] at hx
                change t ≤ ⟪x, η⟫
                linarith
            have hLflip_negη : Lflip (-η) = η' := by
              have h' := congrArg (fun v : ℝᵈ => Lflip v) hLflip_η'
              have h'' : Lflip (Lflip η') = η' := hLflip_inv η'
              simpa [h''] using h'.symm
            have hLflip_half_comp : Lflip '' {x : ℝᵈ | t ≤ ⟪x, η⟫} =
                {x : ℝᵈ | ⟪x, η'⟫ ≤ -t} := by
              rw [hset_ge, halfspace_image_linearIsometryEquiv Lflip (-η) (-t)]
              simpa [hLflip_negη]
            have hLflipHneg : Lflip '' Hneg = Hneg' := by
              dsimp [Hneg, Hneg']
              calc
                Lflip '' (K ∩ {x : ℝᵈ | t ≤ ⟪x, η⟫})
                    = Lflip '' K ∩ Lflip '' {x : ℝᵈ | t ≤ ⟪x, η⟫} := by
                      rw [Set.image_inter Lflip.injective]
                _ = K ∩ {x : ℝᵈ | ⟪x, η'⟫ ≤ -t} := by rw [hLflipK, hLflip_half_comp]
            have hvol_image : volume Hneg = volume (Lflip '' Hneg) := by
              have hpre := Lflip.measurePreserving.measure_preimage_emb Lflip.toMeasurableEquiv.measurableEmbedding (Lflip '' Hneg)
              have hpre' : Lflip ⁻¹' (Lflip '' Hneg) = Hneg := Set.preimage_image_eq Hneg Lflip.injective
              rwa [hpre'] at hpre
            have hvol_image_real : volume.real Hneg = volume.real (Lflip '' Hneg) := congrArg ENNReal.toReal hvol_image
            have hvolHneg' : volume.real Hneg' = volume.real K / 2 := by
              rw [← hLflipHneg]
              rw [← hvol_image_real]
              exact hvolcomp
            have hvol' : volume.real (K ∩ {x : ℝᵈ | ⟪x, (-a) • e0 + b • elast⟫ ≤ -t}) = volume.real K / 2 := by
              simpa [Hneg', η'] using hvolHneg'
            have hneg : -a < 0 := by linarith [hapos]
            have hdir := hdirect_case (a' := -a) (b' := b) hbpos hneg (t' := -t) hvol'
            let Dcomp : ℝᵈ := (⨍ x in K, x) - (⨍ x in Hneg', x)
            have hdir_mem : Dcomp ∈ ℝ ∙ η' := by
              simpa [Dcomp, Hneg', η'] using hdir
            have hLflip_avgK : Lflip (⨍ x in K, x) = ⨍ x in K, x :=
              setAverage_linearIsometryEquiv_invariant Lflip K hLflipK
            have hLflip_avgHneg : Lflip (⨍ x in Hneg, x) = ⨍ x in Hneg', x := by
              have h1 := average_image_linearIsometryEquiv Lflip Hneg
              simpa [hLflipHneg] using h1
            let Dneg : ℝᵈ := (⨍ x in K, x) - (⨍ x in Hneg, x)
            have hLflipDneg : Lflip Dneg = Dcomp := by
              dsimp [Dneg, Dcomp]
              rw [map_sub, hLflip_avgK, hLflip_avgHneg]
            have hu_meas : Measurable (fun x : ℝᵈ => ⟪x, η⟫) := by
              exact (continuous_id.inner continuous_const).measurable
            have hHpos_meas : MeasurableSet Hpos := hK_meas.inter (measurableSet_le hu_meas measurable_const)
            have hHneg_meas : MeasurableSet Hneg := hK_meas.inter (measurableSet_le measurable_const hu_meas)
            have hHposHneg_sub : Hpos ∩ Hneg ⊆ {x : ℝᵈ | ⟪x, η⟫ = t} := by
              intro x hx
              rcases hx with ⟨⟨hxK, hxle⟩, hxK', hxge⟩
              exact le_antisymm hxle hxge
            have hHposHneg_zero : volume (Hpos ∩ Hneg) = 0 := by
              apply le_antisymm ?_ bot_le
              calc
                volume (Hpos ∩ Hneg) ≤ volume {x : ℝᵈ | ⟪x, η⟫ = t} := measure_mono (μ := volume) hHposHneg_sub
                _ = 0 := volume_hyperplane_eq_zero hη_ne t
            have hHposHneg_disj : AEDisjoint volume Hpos Hneg := by
              rw [AEDisjoint]
              exact hHposHneg_zero
            have hHposHneg_union : Hpos ∪ Hneg = K := by
              ext x
              constructor
              · intro hx
                rcases hx with hx | hx <;> exact hx.1
              · intro hxK
                by_cases hle : ⟪x, η⟫ ≤ t
                · exact Or.inl ⟨hxK, hle⟩
                · exact Or.inr ⟨hxK, le_of_lt (lt_of_not_ge hle)⟩
            have hHpos_fin : volume Hpos < ⊤ := lt_of_le_of_lt (measure_mono (μ := volume) (fun x hx => hx.1)) hK_finite
            have hHneg_fin : volume Hneg < ⊤ := lt_of_le_of_lt (measure_mono (μ := volume) (fun x hx => hx.1)) hK_finite
            have hDneg_rel := setAverage_sub_eq_neg_sub_of_measure_eq_union
              (hK_meas := hK_meas) (hK_bdd := hK_bdd)
              (hA_meas := hHpos_meas) (hB_meas := hHneg_meas)
              (hAB_disj := hHposHneg_disj) (hAB_union := hHposHneg_union)
              (hA_fin := hHpos_fin) (hB_fin := hHneg_fin)
              (hK_vol_pos := hK_vol_pos) (hA_vol := hvolHpos) (hB_vol := hvolcomp)
            have hDneg_eq : Dneg = Lflip Dcomp := by
              have h' := congrArg (fun v : ℝᵈ => Lflip v) hLflipDneg
              have h'' : Lflip (Lflip Dneg) = Dneg := hLflip_inv Dneg
              simpa [h''] using h'
            have hDneg_eq' : (⨍ x in K, x) - (⨍ x in Hneg, x) = Lflip Dcomp := by
              simpa [Dneg] using hDneg_eq
            have hDrot_eq : Drot = - Lflip Dcomp := by
              dsimp [Drot]
              have hrel := hDneg_rel
              rw [hDneg_eq'] at hrel
              simpa [Hpos] using hrel
            have hLflipDcomp_mem : Lflip Dcomp ∈ ℝ ∙ (-η) := by
              have hdir_flip : Lflip Dcomp ∈ ℝ ∙ (Lflip η') := by
                rw [Submodule.mem_span_singleton] at hdir_mem ⊢
                rcases hdir_mem with ⟨c, hc⟩
                refine ⟨c, ?_⟩
                have h := congrArg (fun v : ℝᵈ => Lflip v) hc
                simpa [map_smul] using h
              simpa [hLflip_η'] using hdir_flip
            have hmem_Drot : Drot ∈ ℝ ∙ η := by
              rw [Submodule.mem_span_singleton] at hLflipDcomp_mem ⊢
              rcases hLflipDcomp_mem with ⟨c, hc⟩
              refine ⟨c, ?_⟩
              have hneg' := congrArg (fun v : ℝᵈ => -v) hc
              calc
                c • η = - (c • (-η)) := by simp
                _ = - Lflip Dcomp := by rw [hneg']
                _ = Drot := by rw [hDrot_eq]
            exact hmem_Drot
    have hRdiff : R ((⨍ x in K, x) - (⨍ x in H, x)) =
        (⨍ x in K, x) - (⨍ x in (K ∩ {x | ⟪x, R ξv⟫ ≤ t}), x) := by
      rw [map_sub, hRavgK, hRavgH]
    have hmain : (⨍ x in K, x) - (⨍ x in H, x) ∈ ℝ ∙ ξv := by
      have hspan := mem_span_smul_of_linearIsometryEquiv R (v := (⨍ x in K, x) - (⨍ x in H, x)) (ξ := ξv) ?_
      · simpa [hRdiff] using hspan
      · simpa [hRdiff] using hrot
    simpa [H] using hmain

end Commons.Geometry.Ulam