import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

namespace Commons.Algebra.MvPolynomial

open scoped BigOperators

section Weight

variable {σ : Type*} [Fintype σ]

/-- The weighted value `∑ i, m i / r i` of a multi-index `m`. -/
noncomputable def indexWt (r : σ → ℕ) (m : σ →₀ ℕ) : ℝ := ∑ i, (m i : ℝ) / (r i : ℝ)

lemma indexWt_nonneg {r : σ → ℕ} (m : σ →₀ ℕ) : 0 ≤ indexWt r m := by
  rw [indexWt]
  exact Finset.sum_nonneg fun i _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma indexWt_zero (r : σ → ℕ) : indexWt r (0 : σ →₀ ℕ) = 0 := by simp [indexWt]

lemma indexWt_eq_zero_iff {r : σ → ℕ} (hr : ∀ i, 0 < r i) (m : σ →₀ ℕ) :
    indexWt r m = 0 ↔ m = 0 := by
  constructor
  · intro h
    rw [indexWt] at h
    have h' := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (f := fun i => (m i : ℝ) / (r i : ℝ))
      (fun i _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).mp h
    ext i
    have hi := h' i (Finset.mem_univ i)
    rw [div_eq_zero_iff] at hi
    rcases hi with hi | hi
    · exact Nat.cast_eq_zero.mp hi
    · exact absurd hi (ne_of_gt (Nat.cast_pos.mpr (hr i)))
  · rintro rfl
    exact indexWt_zero r

/-- For a nonempty finite set of nonnegative reals, `sInf = 0` iff `0` is in the set. -/
lemma csInf_eq_zero_iff_mem {T : Finset ℝ} (hne : T.Nonempty) (hnn : ∀ x ∈ T, 0 ≤ x) :
    sInf (T : Set ℝ) = 0 ↔ (0 : ℝ) ∈ T := by
  constructor
  · intro h
    have hmem := hne.csInf_mem
    rwa [h] at hmem
  · intro h0
    exact le_antisymm (csInf_le ⟨0, fun x hx => hnn x hx⟩ h0)
      (le_csInf hne.to_set hnn)

lemma mem_image_indexWt_zero_iff {r : σ → ℕ} (hr : ∀ i, 0 < r i) (s : Finset (σ →₀ ℕ)) :
    (0 : ℝ) ∈ s.image (indexWt r) ↔ (0 : σ →₀ ℕ) ∈ s := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨m, hm, h0⟩
    rw [indexWt_eq_zero_iff hr m] at h0
    exact h0 ▸ hm
  · intro h0
    exact ⟨0, h0, indexWt_zero r⟩

end Weight

section Shift

variable {σ : Type*}

/-- The Taylor shift `X i ↦ X i + α i`. -/
noncomputable def indexTay {K : Type*} [CommSemiring K] (α : σ → K)
    (P : MvPolynomial σ K) : MvPolynomial σ K :=
  MvPolynomial.aeval (fun i => MvPolynomial.C (α i) + MvPolynomial.X i) P

end Shift

section SetDef

variable {σ : Type*} [Fintype σ]

/-- The index set of `P` at `α` w.r.t. `r`. -/
noncomputable def indexSet {K : Type*} [CommSemiring K] (α : σ → K) (r : σ → ℕ)
    (P : MvPolynomial σ K) : Set ℝ :=
  {t : ℝ | ∃ m ∈ (indexTay α P).support, t = indexWt r m}

lemma indexSet_eq_image {K : Type*} [CommSemiring K] (α : σ → K) (r : σ → ℕ)
    (P : MvPolynomial σ K) :
    indexSet α r P = ((indexTay α P).support.image (indexWt r) : Set ℝ) := by
  ext t
  simp only [indexSet, Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_image]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, rfl⟩

end SetDef

section ShiftLemmas

variable {σ : Type*}

lemma indexTay_injective {K : Type*} [CommRing K] (α : σ → K) :
    Function.Injective fun P : MvPolynomial σ K => indexTay α P := by
  have hinv : ∀ P, (MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (α i)))
      (indexTay α P) = P := by
    intro P
    rw [indexTay, MvPolynomial.comp_aeval_apply]
    have : (fun i => (MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (α i)))
          (MvPolynomial.C (α i) + MvPolynomial.X i)) = (fun i => MvPolynomial.X i) := by
      funext i
      simp
    rw [this, MvPolynomial.aeval_X_left_apply]
  intro P Q h
  have hc := congrArg (MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (α i))) h
  rwa [hinv P, hinv Q] at hc

lemma constantCoeff_indexTay {K : Type*} [CommSemiring K] (α : σ → K) (P : MvPolynomial σ K) :
    MvPolynomial.constantCoeff (indexTay α P) = MvPolynomial.eval α P := by
  rw [indexTay, MvPolynomial.map_aeval]
  simp only [MvPolynomial.constantCoeff_C, map_add, MvPolynomial.constantCoeff_X, add_zero]
  rw [MvPolynomial.constantCoeff_comp_algebraMap]
  rfl

end ShiftLemmas

/-- The nonnegativity, vanishing and "index = 0 iff value nonzero" parts of the index for
Schmidt's subspace theorem, for **positive** weights `r` (this hypothesis is necessary:
with `r i = 0` Lean's `ℝ`-division by zero makes the statement false). -/
theorem index_properties_pos_vanishing {K : Type*} [Field K] [CharZero K] {σ : Type*} [Fintype σ]
    (α : σ → K) (r : σ → ℕ) (hr : ∀ i, 0 < r i) :
    let taylor := fun (P : MvPolynomial σ K) =>
      MvPolynomial.aeval (fun i => MvPolynomial.C (α i) + MvPolynomial.X i) P
    let ind := fun (P : MvPolynomial σ K) =>
      sInf {t : ℝ | ∃ m ∈ (taylor P).support, t = ∑ i, (m i : ℝ) / (r i : ℝ)}
    (∀ P : MvPolynomial σ K, 0 ≤ ind P) ∧
    (∀ P : MvPolynomial σ K, P = 0 → ind P = 0) ∧
    (∀ P : MvPolynomial σ K, P ≠ 0 → (ind P = 0 ↔ MvPolynomial.eval α P ≠ 0)) := by
  have h1 : ∀ P : MvPolynomial σ K, 0 ≤ sInf (indexSet α r P) := by
    intro P
    rw [indexSet_eq_image]
    rcases (indexTay α P).support.image (indexWt r) |>.eq_empty_or_nonempty with hT | hT
    · rw [hT, Finset.coe_empty, Real.sInf_empty]
    · exact le_csInf hT.to_set fun x hx => by
        rcases Finset.mem_image.mp hx with ⟨m, _, rfl⟩
        exact indexWt_nonneg m
  have h2 : ∀ P : MvPolynomial σ K, P = 0 → sInf (indexSet α r P) = 0 := by
    intro P hP
    rw [hP, indexSet_eq_image]
    have hzero : (indexTay α (0 : MvPolynomial σ K)).support.image (indexWt r) = ∅ := by
      rw [indexTay]
      simp
    rw [hzero, Finset.coe_empty, Real.sInf_empty]
  have h3 : ∀ P : MvPolynomial σ K, P ≠ 0 →
      (sInf (indexSet α r P) = 0 ↔ MvPolynomial.eval α P ≠ 0) := by
    intro P hP
    rw [indexSet_eq_image]
    have hTne : ((indexTay α P).support.image (indexWt r)).Nonempty :=
      (MvPolynomial.support_nonempty.mpr ((indexTay_injective α).ne hP)).image (indexWt r)
    rw [csInf_eq_zero_iff_mem hTne (fun x hx => by
      rcases Finset.mem_image.mp hx with ⟨m, _, rfl⟩
      exact indexWt_nonneg m)]
    rw [mem_image_indexWt_zero_iff hr]
    rw [MvPolynomial.mem_support_iff, ← MvPolynomial.constantCoeff_eq, constantCoeff_indexTay]
  exact ⟨h1, h2, h3⟩

end Commons.Algebra.MvPolynomial