/-
  Work.WilE2 — area E2.  Genericity choices for the Khovanskii–Rolle elimination.

  The elimination perturbs the value `y` of the lifted system to a value `y'` which is a regular
  value (so that all roots of the perturbed system are nondegenerate), and then perturbs the
  Rolle determinant level to a value `δ` which avoids the critical values of `M|_C`.  This
  module assembles the first of these two choices from `sard_square` (Sard in the square case)
  and `avoid_null` (a null set is avoided by every ball).
-/
import Submission.Work.WilE2.sard_square
import Submission.Work.WilE2.avoid_null
import Submission.Work.WilE2.slice_null_ae

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open Classical
namespace Work.WilE2

/-- **Regular values are dense (square case).**  For a differentiable map `f : ℝⁿ → ℝⁿ` and any
ball around `y`, there is a point `y'` of the ball whose every preimage has invertible
differential.  This is what makes the perturbed lifted system nondegenerate at all its roots. -/
theorem exists_regularValue_near {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hf' : ∀ x, HasFDerivAt f (f' x) x) (y : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ y', dist y' y < ε ∧ ∀ z, f z = y' → (f' z).det ≠ 0 := by
  have hN : MeasureTheory.volume (f '' {x | (f' x).det = 0}) = 0 := sard_square f f' hf'
  obtain ⟨y', hy', hyN⟩ := avoid_null hN y hε
  refine ⟨y', hy', fun z hz hdet => hyN ⟨z, hdet, hz⟩⟩

/-- **Simultaneous genericity for the elimination.**  Given the old (square) system map `F` and
the lifted square map `Θ` (the lifted equations together with the Rolle determinant), there are
a value `y'` of `F` near `y₀` and a small `δ > 0` such that

* every preimage of `y'` under `F` has invertible differential (so the roots of the perturbed
  old system are nondegenerate), and
* every preimage of `(y', δ)` under `Θ` has invertible differential (so every solution of the
  new system `(V - y', M - δ)` is a regular solution, which is what the induction hypothesis
  needs).

The two conditions are ultimately the same statement — "a value not in the image of the critical
set" — for `F` and for `Θ`; they are combined with the Fubini slice lemma (`slice_null_ae`),
because `Θ`'s critical values live in `ℝⁿ⁺¹` whereas only an `ℝⁿ`-parameter family of them is
available. -/
theorem exists_generic_pair {n : ℕ} (F : (Fin n → ℝ) → (Fin n → ℝ))
    (F' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hF : ∀ x, HasFDerivAt F (F' x) x)
    (Θ : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
    (Θ' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))
    (hΘ : ∀ z, HasFDerivAt Θ (Θ' z) z)
    (y₀ : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) {δm : ℝ} (hδm : 0 < δm) :
    ∃ (y' : Fin n → ℝ) (δ : ℝ), dist y' y₀ < ε ∧ 0 < δ ∧ δ < δm ∧
      (∀ x, F x = y' → (F' x).det ≠ 0) ∧
      (∀ z, Θ z = Fin.snoc y' δ → (Θ' z).det ≠ 0) := by
  classical
  set N₁ : Set (Fin n → ℝ) := F '' {x | (F' x).det = 0} with hN₁
  set N₂ : Set (Fin (n + 1) → ℝ) := Θ '' {z | (Θ' z).det = 0} with hN₂
  have hN₁0 : MeasureTheory.volume N₁ = 0 := sard_square F F' hF
  have hN₂0 : MeasureTheory.volume N₂ = 0 := sard_square Θ Θ' hΘ
  set B : Set (Fin n → ℝ) :=
    {y | MeasureTheory.volume {t : ℝ | Fin.snoc y t ∈ N₂} ≠ 0} with hB
  have hB0 : MeasureTheory.volume B = 0 := slice_null_ae hN₂0
  have hunion : MeasureTheory.volume (N₁ ∪ B) = 0 :=
    MeasureTheory.measure_union_null hN₁0 hB0
  obtain ⟨y', hy'd, hy'⟩ := avoid_null hunion y₀ hε
  have hy'N₁ : y' ∉ N₁ := fun h => hy' (Or.inl h)
  have hy'B : y' ∉ B := fun h => hy' (Or.inr h)
  have hslice : MeasureTheory.volume {t : ℝ | Fin.snoc y' t ∈ N₂} = 0 := by
    by_contra h
    exact hy'B h
  -- choose `δ` in `(0, δm)` outside the (null) critical slice
  have hδexists : ∃ δ : ℝ, 0 < δ ∧ δ < δm ∧ Fin.snoc y' δ ∉ N₂ := by
    by_contra h
    push Not at h
    have hsub : Set.Ioo (0 : ℝ) δm ⊆ {t : ℝ | Fin.snoc y' t ∈ N₂} :=
      fun t ht => h t ht.1 ht.2
    have hle : MeasureTheory.volume (Set.Ioo (0 : ℝ) δm)
        ≤ MeasureTheory.volume {t : ℝ | Fin.snoc y' t ∈ N₂} :=
      MeasureTheory.measure_mono hsub
    rw [hslice, Real.volume_Ioo] at hle
    simp only [sub_zero] at hle
    have hz : ENNReal.ofReal δm = 0 :=
      le_antisymm hle (by simp : (0 : ENNReal) ≤ ENNReal.ofReal δm)
    have : δm ≤ 0 := by
      by_contra hpos
      push Not at hpos
      exact (ENNReal.ofReal_ne_zero_iff.mpr hpos) hz
    linarith
  obtain ⟨δ, hδpos, hδlt, hδS⟩ := hδexists
  refine ⟨y', δ, hy'd, hδpos, hδlt, fun x hx hdet => hy'N₁ ⟨x, hdet, hx⟩, ?_⟩
  intro z hz hdet
  exact hδS ⟨z, hdet, hz⟩

end Work.WilE2
