import Mathlib
import Submission.Work.HP.MMDefs
import Submission.Work.HP.IcVolAux
import Submission.Work.HP.JcVolDelta
import Submission.Work.HP.IcVolEst.bandVolAsymp

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Work.HP

/-- The vector `z - (⟪w,z⟫/‖w‖²) w`, the orthogonal projection of `z` onto `(ℝw)ᗮ`. -/
def zPerp {ι : Type*} [Fintype ι] (w z : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  z - (inner ℝ w z / ‖w‖ ^ 2) • w

section reduction
variable {ι : Type*} [Fintype ι]

lemma zPerp_mem_ker (w z : EuclideanSpace ℝ ι) (hw : w ≠ 0) :
    zPerp w z ∈ LinearMap.ker (innerLin (ι := ι) w) := by
  rw [LinearMap.mem_ker]
  simp only [innerLin, zPerp, map_sub, LinearMap.coe_mk, AddHom.coe_mk, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  rw [sub_eq_zero]
  field_simp

lemma inner_zPerp_eq (w z : EuclideanSpace ℝ ι) (hw : w ≠ 0) {t : EuclideanSpace ℝ ι}
    (ht : t ∈ LinearMap.ker (innerLin (ι := ι) w)) :
    inner ℝ z t = inner ℝ (zPerp w z) t := by
  have ht0 : inner ℝ w t = 0 := by
    have := ht
    rw [LinearMap.mem_ker] at this
    simpa [innerLin] using this
  calc inner ℝ z t
      = inner ℝ (zPerp w z + (inner ℝ w z / ‖w‖ ^ 2) • w) t := by
        congr 1; rw [zPerp]; abel
    _ = inner ℝ (zPerp w z) t + (inner ℝ w z / ‖w‖ ^ 2) * inner ℝ w t := by
        rw [inner_add_left, inner_smul_left]; simp
    _ = inner ℝ (zPerp w z) t := by rw [ht0, mul_zero, add_zero]

lemma norm_zPerp (w z : EuclideanSpace ℝ ι) (hw : w ≠ 0) :
    ‖zPerp w z‖ = Real.sqrt (deltaV w z) / ‖w‖ := by
  have hwne : (‖w‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hw
  have hδ : 0 ≤ deltaV w z := by
    rw [deltaV]
    nlinarith [abs_real_inner_le_norm w z, abs_nonneg (inner ℝ w z), sq_nonneg (‖w‖ * ‖z‖),
      sq_abs (inner ℝ w z)]
  have hnorm2 : ‖zPerp w z‖ ^ 2 = deltaV w z / ‖w‖ ^ 2 := by
    rw [zPerp, norm_sub_sq_real, real_inner_smul_right, real_inner_comm z w, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs, deltaV]
    field_simp
    rw [real_inner_comm z w]
    ring
  have key : ‖zPerp w z‖ * ‖w‖ = Real.sqrt (deltaV w z) := by
    apply (sq_eq_sq₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, hnorm2, div_mul_cancel₀ _ (by positivity : (‖w‖ : ℝ) ^ 2 ≠ 0),
      Real.sq_sqrt hδ]
  rw [← key, mul_div_cancel_right₀ _ hwne]

lemma finrank_ker_innerLin (w : EuclideanSpace ℝ ι) (hw : w ≠ 0) :
    Module.finrank ℝ ↥(LinearMap.ker (innerLin (ι := ι) w)) = Fintype.card ι - 1 := by
  have hker : LinearMap.ker (innerLin (ι := ι) w) = (Submodule.span ℝ {w})ᗮ := by
    ext t
    rw [LinearMap.mem_ker, Submodule.mem_orthogonal']
    constructor
    · intro h u hu
      obtain ⟨mu, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [real_inner_smul_right]
      have ht0 : inner ℝ w t = 0 := by simpa [innerLin] using h
      rw [real_inner_comm, ht0, mul_zero]
    · intro h
      have := h w (Submodule.mem_span_singleton_self w)
      simpa [innerLin, real_inner_comm] using this
  have h1 : Module.finrank ℝ ↥(Submodule.span ℝ {w}) +
      Module.finrank ℝ ↥((Submodule.span ℝ {w})ᗮ) = Module.finrank ℝ (EuclideanSpace ℝ ι) :=
    Submodule.finrank_add_finrank_orthogonal _
  rw [finrank_span_singleton hw, finrank_euclideanSpace] at h1
  rw [hker]
  omega

end reduction

theorem IcVolAsymp (ι : Type) [Fintype ι] (hN : 3 ≤ Fintype.card ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w z : EuclideanSpace ℝ ι), LinearIndependent ℝ ![w, z] →
      |IcVol w z - 2 * ((Fintype.card ι : ℝ) - 2) / ((Fintype.card ι : ℝ) - 1) *
          ballVol (Fintype.card ι - 2) * ‖w‖ / Real.sqrt (deltaV w z)| ≤
      C * (2 * ((Fintype.card ι : ℝ) - 2) / ((Fintype.card ι : ℝ) - 1) *
          ballVol (Fintype.card ι - 2) * ‖w‖ / Real.sqrt (deltaV w z)) *
        min 1 (‖w‖ ^ 2 / deltaV w z) := by
  have hdim2 : 2 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin (Fintype.card ι - 1))) := by
    rw [finrank_euclideanSpace, Fintype.card_fin]; omega
  obtain ⟨C, hCpos, hC⟩ :=
    IcVolEst.bandVolAsymp (E := EuclideanSpace ℝ (Fin (Fintype.card ι - 1))) hdim2
  refine ⟨C, hCpos, fun w z h => ?_⟩
  have hw0 : w ≠ 0 := by simpa using LinearIndependent.ne_zero (0 : Fin 2) h
  have hdpos : 0 < deltaV w z := JcVolDelta h
  set V : Submodule ℝ (EuclideanSpace ℝ ι) := LinearMap.ker (innerLin (ι := ι) w) with hV
  have hmem : zPerp w z ∈ V := by rw [hV]; exact zPerp_mem_ker w z hw0
  set cV : ↥V := ⟨zPerp w z, hmem⟩ with hcV
  have hdim : Module.finrank ℝ ↥V = Fintype.card ι - 1 := by
    rw [hV]; exact finrank_ker_innerLin w hw0
  have hinner : ∀ t : ↥V, inner ℝ z (t : EuclideanSpace ℝ ι) = inner ℝ (cV : ↥V) t := by
    intro t
    have ht : (t : EuclideanSpace ℝ ι) ∈ LinearMap.ker (innerLin (ι := ι) w) := by
      rw [← hV]; exact t.2
    rw [inner_zPerp_eq w z hw0 ht]
    rfl
  have hnormc : ‖cV‖ = Real.sqrt (deltaV w z) / ‖w‖ := by
    rw [hcV]; exact norm_zPerp w z hw0
  have hcne : cV ≠ 0 := by
    intro hc
    have h1 : Real.sqrt (deltaV w z) = 0 := by
      have h0 : ‖cV‖ = 0 := by rw [hc]; simp
      rw [hnormc] at h0
      field_simp at h0
      simpa using h0
    exact absurd h1 (ne_of_gt (Real.sqrt_pos.mpr hdpos))
  let φ : ↥V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Fintype.card ι - 1)) :=
    (stdOrthonormalBasis ℝ ↥V).repr.trans
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fin.castOrderIso hdim).toEquiv)
  have hIcVol : IcVol w z = (volume {t : ↥V |
      ‖t‖ ≤ 1 ∧ |inner ℝ z (t : EuclideanSpace ℝ ι)| ≤ ‖t‖}).toReal := by
    have hset : {t : ↥V | (t : EuclideanSpace ℝ ι)
          ∈ {s : EuclideanSpace ℝ ι | |inner ℝ z s| ≤ ‖s‖ ∧ ‖s‖ ≤ 1}}
        = {t : ↥V | ‖t‖ ≤ 1 ∧ |inner ℝ z (t : EuclideanSpace ℝ ι)| ≤ ‖t‖} := by
      ext t
      simp only [Set.mem_ofPred_eq]
      exact and_comm
    rw [IcVol, subVol, ← hV, hset]
  have hset1 : {t : ↥V | ‖t‖ ≤ 1 ∧ |inner ℝ z (t : EuclideanSpace ℝ ι)| ≤ ‖t‖}
      = {t : ↥V | ‖t‖ ≤ 1 ∧ |inner ℝ (cV : ↥V) t| ≤ ‖t‖} := by
    ext t
    simp only [Set.mem_ofPred_eq]
    rw [hinner t]
  have himg : φ '' {t : ↥V | ‖t‖ ≤ 1 ∧ |inner ℝ (cV : ↥V) t| ≤ ‖t‖}
      = {u : EuclideanSpace ℝ (Fin (Fintype.card ι - 1)) |
          ‖u‖ ≤ 1 ∧ |inner ℝ (φ cV) u| ≤ ‖u‖} := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      simp only [Set.mem_ofPred_eq] at ht ⊢
      rw [φ.norm_map t]
      exact ⟨ht.1, by simpa only [φ.inner_map_map cV t] using ht.2⟩
    · intro hu
      refine ⟨φ.symm u, ?_, φ.apply_symm_apply u⟩
      simp only [Set.mem_ofPred_eq] at hu ⊢
      rw [φ.symm.norm_map]
      exact ⟨hu.1, by simpa only [← φ.inner_map_map cV (φ.symm u), φ.apply_symm_apply] using hu.2⟩
  have hvol : (volume {t : ↥V | ‖t‖ ≤ 1 ∧ |inner ℝ (cV : ↥V) t| ≤ ‖t‖}).toReal
      = (volume {u : EuclideanSpace ℝ (Fin (Fintype.card ι - 1)) |
          ‖u‖ ≤ 1 ∧ |inner ℝ (φ cV) u| ≤ ‖u‖}).toReal := by
    have hSmeas : NullMeasurableSet {t : ↥V | ‖t‖ ≤ 1 ∧ |inner ℝ (cV : ↥V) t| ≤ ‖t‖} volume :=
      ((isClosed_le continuous_norm continuous_const).inter
        (isClosed_le (continuous_abs.comp (continuous_const.inner continuous_id))
          continuous_norm)).measurableSet.nullMeasurableSet
    have hmap : volume (φ '' {t : ↥V | ‖t‖ ≤ 1 ∧ |inner ℝ (cV : ↥V) t| ≤ ‖t‖})
        = volume {t : ↥V | ‖t‖ ≤ 1 ∧ |inner ℝ (cV : ↥V) t| ≤ ‖t‖} := by
      have himg2 : φ '' {t : ↥V | ‖t‖ ≤ 1 ∧ |inner ℝ (cV : ↥V) t| ≤ ‖t‖}
          = φ.symm ⁻¹' {t : ↥V | ‖t‖ ≤ 1 ∧ |inner ℝ (cV : ↥V) t| ≤ ‖t‖} := by
        ext u
        simp only [Set.mem_image, Set.mem_preimage]
        constructor
        · rintro ⟨t, ht, ht2⟩
          rwa [← ht2, φ.symm_apply_apply]
        · intro h
          exact ⟨φ.symm u, h, φ.apply_symm_apply u⟩
      rw [himg2]
      exact (LinearIsometryEquiv.measurePreserving φ.symm).measure_preimage hSmeas
    rw [← hmap, himg]
  rw [hIcVol, hset1, hvol]
  have hbound := hC (φ cV) (fun h => hcne (φ.injective (by simpa using h)))
  have hnormφ : ‖φ cV‖ = Real.sqrt (deltaV w z) / ‖w‖ := by rw [φ.norm_map, hnormc]
  have hdime : Module.finrank ℝ (EuclideanSpace ℝ (Fin (Fintype.card ι - 1)))
      = Fintype.card ι - 1 := by rw [finrank_euclideanSpace, Fintype.card_fin]
  have hm1 : Module.finrank ℝ (EuclideanSpace ℝ (Fin (Fintype.card ι - 1))) - 1
      = Fintype.card ι - 2 := by rw [hdime]; omega
  have hcast1 : ((Fintype.card ι - 1 : ℕ) : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card ι), Nat.cast_one]
  have hmain : 2 * ((Module.finrank ℝ (EuclideanSpace ℝ (Fin (Fintype.card ι - 1))) : ℝ) - 1) /
        (Module.finrank ℝ (EuclideanSpace ℝ (Fin (Fintype.card ι - 1))) : ℝ) *
        ballVol (Module.finrank ℝ (EuclideanSpace ℝ (Fin (Fintype.card ι - 1))) - 1) / ‖φ cV‖
      = 2 * ((Fintype.card ι : ℝ) - 2) / ((Fintype.card ι : ℝ) - 1) *
          ballVol (Fintype.card ι - 2) * ‖w‖ / Real.sqrt (deltaV w z) := by
    rw [hm1, hdime, hcast1, hnormφ]
    field_simp
    try ring
  have harg : (1 : ℝ) / ‖φ cV‖ ^ 2 = ‖w‖ ^ 2 / deltaV w z := by
    rw [hnormφ, div_pow]
    field_simp
    rw [Real.sq_sqrt (le_of_lt hdpos)]
    try ring
  rw [← hmain, ← harg]
  exact hbound

end Work.HP
