import Mathlib
import Submission.Work.Mostow.geodDeps
import Submission.Work.Mostow.jordanTorus
import Submission.Work.Mostow.torusAngleDefs
import Submission.Work.Mostow.torusRotZarg

namespace Work.Mostow

open Submission.Mostow

noncomputable section

theorem torusData (m : ℕ) (hm : Even m)
    (A : Subgroup (Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)) [Finite A]
    (hgen : A = Subgroup.closure {a | a ∈ A ∧ Submission.Mostow.rotN a ≤ 1 / 4})
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hnofix : ∀ w : Submission.Mostow.E m, (∀ a ∈ A, a w = w) → w = 0)
    (g : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
    (hg : ∀ a ∈ A, g * a = a * g) :
    ∃ (e : OrthonormalBasis (Fin (m / 2) × Fin 2) ℝ (Submission.Mostow.E m))
      (φ : (Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) →
        Fin (m / 2) → AddCircle (2 * Real.pi))
      (Aang : AddSubgroup (Fin (m / 2) → AddCircle (2 * Real.pi))),
      (∀ c ∈ (A ⊔ Subgroup.zpowers g), ∀ (i : Fin (m / 2)) (x y : ℝ), ∃ t : ℝ,
        (t : AddCircle (2 * Real.pi)) = φ c i ∧
          c (x • e (i, Fin.castSucc 0) + y • e (i, 1)) =
            (Real.cos t * x - Real.sin t * y) • e (i, Fin.castSucc 0) +
              (Real.sin t * x + Real.cos t * y) • e (i, 1)) ∧
      (∀ c ∈ (A ⊔ Subgroup.zpowers g), ∀ c' ∈ (A ⊔ Subgroup.zpowers g),
        φ (c * c') = φ c + φ c') ∧
      (∀ f : Fin (m / 2) → AddCircle (2 * Real.pi),
        f ∈ Aang ↔ ∃ c ∈ (A ⊔ Subgroup.zpowers g), φ c = f) := by
  classical
  obtain ⟨e, _φ0, hrot⟩ := jordanTorus m hm A hgen hcomm hnofix g hg
  let H : Subgroup (E m ≃ₗᵢ[ℝ] E m) := A ⊔ Subgroup.zpowers g
  have he0 : ∀ i : Fin (m / 2), ‖e (i, (0 : Fin 2))‖ = 1 := fun i =>
    e.orthonormal.norm_eq_one _
  have he1 : ∀ i : Fin (m / 2), ‖e (i, (1 : Fin 2))‖ = 1 := fun i =>
    e.orthonormal.norm_eq_one _
  have horth : ∀ i : Fin (m / 2), inner ℝ (e (i, 0)) (e (i, 1)) = 0 := fun i =>
    e.orthonormal.inner_eq_zero (by simp)
  have hRZ : ∀ (i : Fin (m / 2)) (c : E m ≃ₗᵢ[ℝ] E m) (t : ℝ),
      c (e (i, 0)) = Real.cos t • e (i, 0) + Real.sin t • e (i, 1) →
      c (e (i, 1)) = -Real.sin t • e (i, 0) + Real.cos t • e (i, 1) →
      (t : AddCircle (2 * Real.pi)) =
        ((Complex.arg (rotZ (e (i, 0)) (e (i, 1)) c) : ℝ) : AddCircle (2 * Real.pi)) := by
    intro i c t h1 h2
    exact (torusRotZarg (he0 i) (he1 i) (horth i) h1 h2).symm
  have hspec : ∀ (c : E m ≃ₗᵢ[ℝ] E m) (hc : c ∈ H) (i : Fin (m / 2)), ∃ t : ℝ,
      (t : AddCircle (2 * Real.pi)) = ((Complex.arg (rotZ (e (i, 0)) (e (i, 1)) c) : ℝ) :
        AddCircle (2 * Real.pi)) ∧
      c (e (i, 0)) = Real.cos t • e (i, 0) + Real.sin t • e (i, 1) ∧
      c (e (i, 1)) = -Real.sin t • e (i, 0) + Real.cos t • e (i, 1) := by
    intro c hc i
    obtain ⟨t, ht, hf⟩ := hrot c hc i 1 0
    obtain ⟨t2, ht2, hf2⟩ := hrot c hc i 0 1
    have hf' : c (e (i, 0)) = Real.cos t • e (i, 0) + Real.sin t • e (i, 1) := by
      simpa using hf
    have hf₂' : c (e (i, 1)) = -Real.sin t2 • e (i, 0) + Real.cos t2 • e (i, 1) := by
      simpa using hf2
    have hcoe : (t2 : Real.Angle) = (t : Real.Angle) := ht2.trans ht.symm
    have hcos : Real.cos t2 = Real.cos t := by
      have h := congrArg Real.Angle.cos hcoe
      rwa [Real.Angle.cos_coe, Real.Angle.cos_coe] at h
    have hsin : Real.sin t2 = Real.sin t := by
      have h := congrArg Real.Angle.sin hcoe
      rwa [Real.Angle.sin_coe, Real.Angle.sin_coe] at h
    have hcv : c (e (i, 1)) = -Real.sin t • e (i, 0) + Real.cos t • e (i, 1) := by
      rw [← hsin, ← hcos]; exact hf₂'
    exact ⟨t, hRZ i c t hf' hcv, hf', hcv⟩
  let φ : (E m ≃ₗᵢ[ℝ] E m) → Fin (m / 2) → AddCircle (2 * Real.pi) :=
    fun c i => ((Complex.arg (rotZ (e (i, 0)) (e (i, 1)) c) : ℝ) : AddCircle (2 * Real.pi))
  have hrotC : ∀ (c : E m ≃ₗᵢ[ℝ] E m) (hc : c ∈ H) (i : Fin (m / 2)) (x y : ℝ), ∃ t : ℝ,
      (t : AddCircle (2 * Real.pi)) = φ c i ∧
      c (x • e (i, 0) + y • e (i, 1)) =
        (Real.cos t * x - Real.sin t * y) • e (i, 0) +
          (Real.sin t * x + Real.cos t * y) • e (i, 1) := by
    intro c hc i x y
    obtain ⟨t, ht, hcu, hcv⟩ := hspec c hc i
    exact ⟨t, ht, by
      calc c (x • e (i, 0) + y • e (i, 1))
          = x • c (e (i, 0)) + y • c (e (i, 1)) := by rw [map_add, map_smul, map_smul]
        _ = x • (Real.cos t • e (i, 0) + Real.sin t • e (i, 1)) +
              y • (-Real.sin t • e (i, 0) + Real.cos t • e (i, 1)) := by rw [hcu, hcv]
        _ = (Real.cos t * x - Real.sin t * y) • e (i, 0) +
              (Real.sin t * x + Real.cos t * y) • e (i, 1) := by module⟩
  have hphi1 : φ (1 : E m ≃ₗᵢ[ℝ] E m) = 0 := by
    funext i
    show ((Complex.arg (rotZ (e (i, 0)) (e (i, 1)) (1 : E m ≃ₗᵢ[ℝ] E m)) : ℝ) :
        AddCircle (2 * Real.pi)) = 0
    have huu : inner ℝ (e (i, 0)) (e (i, 0)) = 1 := by
      rw [real_inner_self_eq_norm_sq, he0 i]; norm_num
    have h : rotZ (e (i, 0)) (e (i, 1)) (1 : E m ≃ₗᵢ[ℝ] E m) = 1 := by
      rw [rotZ, show (1 : E m ≃ₗᵢ[ℝ] E m) (e (i, 0)) = e (i, 0) from by simp, huu, horth i]
      norm_num
    rw [h, Complex.arg_one]
    rfl
  have hφadd : ∀ (c : E m ≃ₗᵢ[ℝ] E m) (hc : c ∈ H) (c' : E m ≃ₗᵢ[ℝ] E m) (hc' : c' ∈ H),
      φ (c * c') = φ c + φ c' := by
    intro c hc c' hc'
    funext i
    obtain ⟨t, ht, hcu, hcv⟩ := hspec c hc i
    obtain ⟨t', ht', hcu', hcv'⟩ := hspec c' hc' i
    have hmul_u : (c * c') (e (i, 0)) =
        Real.cos (t + t') • e (i, 0) + Real.sin (t + t') • e (i, 1) := by
      rw [LinearIsometryEquiv.mul_def, LinearIsometryEquiv.trans_apply, hcu',
          map_add, map_smul, map_smul, hcu, hcv, Real.cos_add, Real.sin_add]
      module
    have hmul_v : (c * c') (e (i, 1)) =
        -Real.sin (t + t') • e (i, 0) + Real.cos (t + t') • e (i, 1) := by
      rw [LinearIsometryEquiv.mul_def, LinearIsometryEquiv.trans_apply, hcv',
          map_add, map_smul, map_smul, hcu, hcv, Real.cos_add, Real.sin_add]
      module
    have harg : ((Complex.arg (rotZ (e (i, 0)) (e (i, 1)) (c * c')) : ℝ) :
        AddCircle (2 * Real.pi)) = ((t + t' : ℝ) : AddCircle (2 * Real.pi)) :=
      (hRZ i (c * c') (t + t') hmul_u hmul_v).symm
    have htc : ((t : AddCircle (2 * Real.pi))) = φ c i := ht
    have htc' : ((t' : AddCircle (2 * Real.pi))) = φ c' i := ht'
    calc φ (c * c') i
        = ((Complex.arg (rotZ (e (i, 0)) (e (i, 1)) (c * c')) : ℝ) :
            AddCircle (2 * Real.pi)) := rfl
      _ = ((t + t' : ℝ) : AddCircle (2 * Real.pi)) := harg
      _ = (t : AddCircle (2 * Real.pi)) + (t' : AddCircle (2 * Real.pi)) := by simp
      _ = φ c i + φ c' i := by rw [htc, htc']
  let Aang : AddSubgroup (Fin (m / 2) → AddCircle (2 * Real.pi)) :=
    { carrier := {f | ∃ c ∈ H, φ c = f}
      zero_mem' := ⟨1, H.one_mem, hphi1⟩
      add_mem' := by
        intro a b ha hb
        obtain ⟨c, hc, hca⟩ := ha
        obtain ⟨c', hc', hc'b⟩ := hb
        exact ⟨c * c', H.mul_mem hc hc', by
          rw [← hca, ← hc'b]; exact hφadd c hc c' hc'⟩
      neg_mem' := by
        intro a ha
        obtain ⟨c, hc, hca⟩ := ha
        refine ⟨c⁻¹, H.inv_mem hc, ?_⟩
        have h1 : φ (c⁻¹ * c) = φ c⁻¹ + φ c := hφadd c⁻¹ (H.inv_mem hc) c hc
        rw [inv_mul_cancel, hphi1] at h1
        rw [← hca]
        exact eq_neg_of_add_eq_zero_left h1.symm }
  refine ⟨e, φ, Aang, ?_, ?_, ?_⟩
  · intro c hc i x y
    obtain ⟨t, ht, hform⟩ := hrotC c hc i x y
    refine ⟨t, ht, ?_⟩
    rw [Fin.castSucc_zero]
    exact hform
  · intro c hc c' hc'
    exact hφadd c hc c' hc'
  · intro f
    simp only [Aang, H]
    exact Iff.rfl

end

end Work.Mostow
