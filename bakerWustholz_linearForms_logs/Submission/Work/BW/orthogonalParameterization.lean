import Mathlib
import Submission.Work.BW.existsOrthonormalComplement
import Submission.Work.BW.measurePreservingOrthogonal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MeasureTheory Matrix

/-- The fixed identification `Fin k ⊕ Fin (n - k) ≃ Fin n` used to split coordinates. -/
noncomputable def orthoParamE1 {n k : ℕ} (hk : k ≤ n) : Fin k ⊕ Fin (n - k) ≃ Fin n :=
  finSumFinEquiv.trans (Fin.castOrderIso (Nat.add_sub_cancel' hk)).toEquiv

/-- The measure-preserving coordinate split `ℝⁿ ≃ ℝᵏ × ℝⁿ⁻ᵏ`. -/
noncomputable def orthoParamV {n k : ℕ} (hk : k ≤ n) :
    (Fin n → ℝ) ≃ᵐ (Fin k → ℝ) × (Fin (n - k) → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) (orthoParamE1 hk)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin (n - k) => ℝ))

lemma orthoParamV_apply {n k : ℕ} (hk : k ≤ n) (u : Fin n → ℝ) :
    orthoParamV hk u =
      (fun i => u (orthoParamE1 hk (Sum.inl i)), fun j => u (orthoParamE1 hk (Sum.inr j))) := by
  have hg : ∀ b, (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) (orthoParamE1 hk)).symm u b
      = u (orthoParamE1 hk b) := by
    intro b
    rw [show (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) (orthoParamE1 hk)).symm u b
        = (Equiv.piCongrLeft (fun _ : Fin n => ℝ) (orthoParamE1 hk)).symm u b from rfl,
      Equiv.piCongrLeft_symm_apply]
  unfold orthoParamV
  simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.coe_sumPiEquivProdPi,
    Equiv.sumPiEquivProdPi_apply, hg]

lemma orthoParamV_measurePreserving {n k : ℕ} (hk : k ≤ n) :
    MeasurePreserving (orthoParamV hk) (volume : Measure (Fin n → ℝ))
      (volume : Measure ((Fin k → ℝ) × (Fin (n - k) → ℝ))) :=
  (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin k ⊕ Fin (n - k) => ℝ)).comp
    (MeasurePreserving.symm _
      (volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) (orthoParamE1 hk)))

/-- The `n × n` orthogonal matrix whose columns are those of `B` and `Bp`, reindexed by
`orthoParamE1`. -/
noncomputable def orthoParamM {n k : ℕ} (hk : k ≤ n) (B : Matrix (Fin n) (Fin k) ℝ)
    (Bp : Matrix (Fin n) (Fin (n - k)) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun p q => Sum.elim (fun i => B p i) (fun j => Bp p j) ((orthoParamE1 hk).symm q)

lemma orthoParamM_mulVec {n k : ℕ} (hk : k ≤ n) (B : Matrix (Fin n) (Fin k) ℝ)
    (Bp : Matrix (Fin n) (Fin (n - k)) ℝ) (u : Fin n → ℝ) :
    (orthoParamM hk B Bp).mulVec u =
      B.mulVec (orthoParamV hk u).1 + Bp.mulVec (orthoParamV hk u).2 := by
  funext p
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply]
  rw [← Equiv.sum_comp (orthoParamE1 hk) (fun q => orthoParamM hk B Bp p q * u q),
    Fintype.sum_sum_type]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by
      simp only [orthoParamM, Sum.elim_inl, Equiv.symm_apply_apply]; rw [orthoParamV_apply])
  · exact Finset.sum_congr rfl (fun j _ => by
      simp only [orthoParamM, Sum.elim_inr, Equiv.symm_apply_apply]; rw [orthoParamV_apply])

lemma orthoParamM_transpose_mul_self {n k : ℕ} (hk : k ≤ n) (B : Matrix (Fin n) (Fin k) ℝ)
    (Bp : Matrix (Fin n) (Fin (n - k)) ℝ)
    (hB : B.transpose * B = 1) (hBp : Bp.transpose * Bp = 1) (hBo : B.transpose * Bp = 0) :
    (orthoParamM hk B Bp).transpose * (orthoParamM hk B Bp) = 1 := by
  ext q q'
  obtain ⟨a, rfl⟩ := (orthoParamE1 hk).surjective q
  obtain ⟨a', rfl⟩ := (orthoParamE1 hk).surjective q'
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, orthoParamM, Equiv.symm_apply_apply]
  rcases a with i | j
  · rcases a' with i' | j'
    · simp only [Sum.elim_inl]
      rw [show (∑ x, B x i * B x i') = (B.transpose * B) i i' by
        rw [Matrix.mul_apply]; simp [Matrix.transpose_apply], hB, Matrix.one_apply,
        Matrix.one_apply]
      by_cases h : i = i'
      · simp [h]
      · have h2 : orthoParamE1 hk (Sum.inl i) ≠ orthoParamE1 hk (Sum.inl i') :=
          fun hc => h (Sum.inl_injective ((orthoParamE1 hk).injective hc))
        simp [h, h2]
    · simp only [Sum.elim_inl, Sum.elim_inr]
      have hsum : (∑ x, B x i * Bp x j') = 0 := by
        have h := congrFun (congrFun hBo i) j'
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply] at h
        rw [← h]
      rw [hsum, Matrix.one_apply]
      have h2 : ¬ (orthoParamE1 hk (Sum.inl i) = orthoParamE1 hk (Sum.inr j')) :=
        fun hc => Sum.inl_ne_inr ((orthoParamE1 hk).injective hc)
      simp [h2]
  · rcases a' with i' | j'
    · simp only [Sum.elim_inl, Sum.elim_inr]
      have hsum : (∑ x, Bp x j * B x i') = 0 := by
        have h := congrFun (congrFun hBo i') j
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply] at h
        rw [← h]
        exact Finset.sum_congr rfl (fun x _ => by ring)
      rw [hsum, Matrix.one_apply]
      have h2 : ¬ (orthoParamE1 hk (Sum.inr j) = orthoParamE1 hk (Sum.inl i')) :=
        fun hc => Sum.inr_ne_inl ((orthoParamE1 hk).injective hc)
      simp [h2]
    · simp only [Sum.elim_inr]
      rw [show (∑ x, Bp x j * Bp x j') = (Bp.transpose * Bp) j j' by
        rw [Matrix.mul_apply]; simp [Matrix.transpose_apply], hBp, Matrix.one_apply,
        Matrix.one_apply]
      by_cases h : j = j'
      · simp [h]
      · have h2 : orthoParamE1 hk (Sum.inr j) ≠ orthoParamE1 hk (Sum.inr j') :=
          fun hc => h (Sum.inr_injective ((orthoParamE1 hk).injective hc))
        simp [h, h2]

theorem orthogonalParameterization {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ) (hk : k ≤ n)
    (hB : B.transpose * B = 1) :
    ∃ Bp : Matrix (Fin n) (Fin (n - k)) ℝ, Bp.transpose * Bp = 1 ∧ B.transpose * Bp = 0 ∧
      (∀ F : (Fin n → ℝ) → ENNReal, Measurable F →
        ∫⁻ u, F u ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) =
          ∫⁻ x : Fin k → ℝ, ∫⁻ y : Fin (n - k) → ℝ,
            F (B.mulVec x + Bp.mulVec y)) := by
  obtain ⟨Bp, hBp, hBo⟩ := existsOrthonormalComplement hk B hB
  refine ⟨Bp, hBp, hBo, fun F hF => ?_⟩
  have hMP : MeasurePreserving (fun u : Fin n → ℝ => (orthoParamM hk B Bp).mulVec u)
      (volume : Measure (Fin n → ℝ)) (volume : Measure (Fin n → ℝ)) :=
    measurePreservingOrthogonal _ (orthoParamM_transpose_mul_self hk B Bp hB hBp hBo)
  have hV := orthoParamV_measurePreserving hk
  have hmul := orthoParamM_mulVec hk B Bp
  have hBc : Continuous (fun x : Fin k → ℝ => B.mulVec x) := by
    rw [show (fun x : Fin k → ℝ => B.mulVec x) =
        (⇑(toLin' B) : (Fin k → ℝ) → (Fin n → ℝ)) from by funext x; rw [toLin'_apply]]
    exact LinearMap.continuous_of_finiteDimensional _
  have hBpc : Continuous (fun y : Fin (n - k) → ℝ => Bp.mulVec y) := by
    rw [show (fun y : Fin (n - k) → ℝ => Bp.mulVec y) =
        (⇑(toLin' Bp) : (Fin (n - k) → ℝ) → (Fin n → ℝ)) from by funext y; rw [toLin'_apply]]
    exact LinearMap.continuous_of_finiteDimensional _
  have hG : Measurable (fun p : (Fin k → ℝ) × (Fin (n - k) → ℝ) =>
      F (B.mulVec p.1 + Bp.mulVec p.2)) :=
    hF.comp ((hBc.comp continuous_fst).add (hBpc.comp continuous_snd)).measurable
  calc ∫⁻ u, F u ∂(volume : Measure (Fin n → ℝ))
      = ∫⁻ u, F ((orthoParamM hk B Bp).mulVec u) ∂(volume : Measure (Fin n → ℝ)) :=
        (hMP.lintegral_comp hF).symm
    _ = ∫⁻ u, F (B.mulVec (orthoParamV hk u).1 + Bp.mulVec (orthoParamV hk u).2)
          ∂(volume : Measure (Fin n → ℝ)) :=
        lintegral_congr (fun u => by rw [hmul u])
    _ = ∫⁻ p : (Fin k → ℝ) × (Fin (n - k) → ℝ),
          F (B.mulVec p.1 + Bp.mulVec p.2)
          ∂(volume : Measure ((Fin k → ℝ) × (Fin (n - k) → ℝ))) :=
        hV.lintegral_comp hG
    _ = ∫⁻ x : Fin k → ℝ, ∫⁻ y : Fin (n - k) → ℝ, F (B.mulVec x + Bp.mulVec y) :=
        (lintegral_lintegral (μ := (volume : Measure (Fin k → ℝ)))
          (ν := (volume : Measure (Fin (n - k) → ℝ)))
          (f := fun x y => F (B.mulVec x + Bp.mulVec y)) hG.aemeasurable).symm

end Work.BW
