import Mathlib
import Submission.Work.SG.SGsepDefs

namespace Work.SGsep

open Work.SG

/-! ## Auxiliary computations, proved locally

`vA_conj` is meant to stand on its own: the sibling deliverables `SGsep/NZ_conj.lean` and
`SGsep/NZ_annihilates.lean` must not be imported here.  The two matrix facts it needs are
therefore established below, in the private namespace `VApriv`, so that importing this module
together with those deliverables cannot produce a name clash.

* `NZ_conj_loc` : `N_{U A U⁻¹} = U N_A U⁻¹` (via `mOrd_conj_loc` and the conjugation
  endomorphism of the matrix monoid);
* `NZ_mul_self` : `N_A · A = N_A`, the statement that `N_A` kills `A - 1` on the right. -/

namespace VApriv

/-- Conjugation by a unimodular integer matrix (`invMat U` being the inverse of `U`) is an
endomorphism of the multiplicative monoid of integer matrices, hence commutes with powers. -/
theorem conjEndo_pow {U : IMat} (hU : IsUnit U.det) (A : IMat) (n : ℕ) :
    (U * A * invMat U) ^ n = U * A ^ n * invMat U := by
  let φ : IMat →* IMat :=
    { toFun := fun B => U * B * invMat U
      map_one' := by simp [mul_invMat hU]
      map_mul' := by
        intro x y
        simp only [mul_assoc]
        rw [← mul_assoc (invMat U) U (y * invMat U), invMat_mul hU, one_mul] }
  have h : φ A = U * A * invMat U := rfl
  have := map_pow φ A n
  rw [h] at this
  exact this.symm

/-- Conjugation by a unimodular integer matrix preserves the multiplicative order of a matrix. -/
theorem mOrd_conj_loc {U : IMat} (hU : IsUnit U.det) (A : IMat) :
    mOrd (U * A * invMat U) = mOrd A := by
  have hpow := conjEndo_pow hU A
  have hiff : ∀ m, 1 ≤ m → (A ^ m = 1 ↔ (U * A * invMat U) ^ m = 1) := by
    intro m _hm
    constructor
    · intro h
      rw [hpow m, h]
      simp [mul_invMat hU]
    · intro h
      have key : invMat U * (U * A * invMat U) ^ m * U = A ^ m := by
        rw [hpow m]
        simp only [mul_assoc, invMat_mul hU, mul_one]
        rw [← mul_assoc, invMat_mul hU, one_mul]
      rw [← key, h]
      simp [invMat_mul hU]
  by_cases hA : ∃ m, 1 ≤ m ∧ A ^ m = 1
  · obtain ⟨h1, h2⟩ := mOrd_spec hA
    have hB : ∃ m, 1 ≤ m ∧ (U * A * invMat U) ^ m = 1 :=
      ⟨mOrd A, h1, (hiff (mOrd A) h1).mp h2⟩
    obtain ⟨g1, g2⟩ := mOrd_spec hB
    exact le_antisymm (mOrd_min hB h1 ((hiff _ h1).mp h2))
      (mOrd_min hA g1 ((hiff _ g1).mpr g2))
  · have hB : ¬ ∃ m, 1 ≤ m ∧ (U * A * invMat U) ^ m = 1 := by
      rintro ⟨m, hm, hBm⟩
      exact hA ⟨m, hm, (hiff m hm).mpr hBm⟩
    rw [mOrd, mOrd, dite_eq_right hA, dite_eq_right hB]

/-- `N_{U A U⁻¹} = U · N_A · U⁻¹` for a unimodular integer matrix `U`. -/
theorem NZ_conj_loc {U : IMat} (hU : IsUnit U.det) (A : IMat) :
    NZ (U * A * invMat U) = U * NZ A * invMat U := by
  rw [NZ, NZ, mOrd_conj_loc hU A]
  unfold Nsum
  have hsum : ∑ i ∈ Finset.range (mOrd A), (U * A * invMat U) ^ i
      = ∑ i ∈ Finset.range (mOrd A), U * A ^ i * invMat U := by
    apply Finset.sum_congr rfl
    intro i _
    rw [conjEndo_pow hU A i]
  rw [hsum, ← Finset.sum_mul, ← Finset.mul_sum]

/-- `N_A · A = N_A` for every integer matrix `A`: for finite order `m = mOrd A` this is the
telescoping identity `(∑_{i<m} A^i)(A-1) = A^m - 1 = 0`, and for infinite order both sides
vanish because `mOrd A = 0` makes `N_A` the empty sum. -/
theorem NZ_mul_self (A : IMat) : NZ A * A = NZ A := by
  by_cases h : ∃ m, 1 ≤ m ∧ A ^ m = 1
  · have hspec : A ^ mOrd A = 1 := (mOrd_spec h).2
    have hg : NZ A * (A - 1) = 0 := by
      rw [NZ, Nsum, geom_sum_mul, hspec, sub_self]
    have h2 : NZ A * A - NZ A = 0 := by
      have h3 : NZ A * A - NZ A * 1 = 0 := by rw [← mul_sub]; exact hg
      simpa using h3
    exact sub_eq_zero.mp h2
  · have h0 : mOrd A = 0 := by rw [mOrd, dite_eq_right h]
    rw [NZ, h0, Nsum]
    simp

end VApriv

/-- Naturality of the intrinsic translation `v_A = N_A τ(A)`: under conjugation by `x ↦ U x + s`
(with `U` unimodular), `v_{U A U⁻¹} = U v_A + m` with `m ∈ N_{U A U⁻¹} ℤ³`, given the cocycle
equation `τ'(U A U⁻¹) = U τ(A) + s - (U A U⁻¹) s + n`.  The terms in `s` cancel because
`N_{UAU⁻¹} (U A U⁻¹) = N_{UAU⁻¹}` (prove `NZ_conj`/`NZ_annihilates` here if needed; they are
separate deliverables, do not import them). -/
theorem vA_conj {U : IMat} (hU : IsUnit U.det) (τ τ' : IMat → Fin 3 → ℝ) (s : Fin 3 → ℝ) (A : IMat)
    (h : ∃ n : IVec, τ' (U * A * invMat U) =
        (toRMat U).mulVec (τ A) + s - (toRMat (U * A * invMat U)).mulVec s + toRVec n) :
    ∃ m ∈ latImg (U * NZ A * invMat U), vA τ' (U * A * invMat U) = (toRMat U).mulVec (vA τ A) + m := by
  obtain ⟨n, hn⟩ := h
  -- Write `B` for the conjugate and `M` for the conjugated sum of powers.
  set B : IMat := U * A * invMat U with hB
  set M : IMat := U * NZ A * invMat U with hM
  have hNZB : NZ B = M := by rw [hB, VApriv.NZ_conj_loc hU A, hM]
  -- The natural candidate: `m = N_B n = M n ∈ M ℤ³`.
  refine ⟨toRVec (M.mulVec n), ?_, ?_⟩
  · rw [mem_latImg]
    exact ⟨n, mulVec_toRVec M n⟩
  · -- `N_B τ'(B) = N_B (U τ(A) + s - B s + n) = U (N_A τ(A)) + (N_B s - N_B B s) + N_B n`,
    -- and the `s`-terms cancel since `N_B B = N_B`.
    show (toRMat (NZ B)).mulVec (τ' B) = (toRMat U).mulVec (vA τ A) + toRVec (M.mulVec n)
    have hBR : toRMat (NZ B) * toRMat B = toRMat (NZ B) := by
      rw [← toRMat_mul, VApriv.NZ_mul_self B]
    have hBU : toRMat (NZ B) * toRMat U = toRMat U * toRMat (NZ A) := by
      rw [← toRMat_mul, hNZB, hM, Matrix.mul_assoc (U * NZ A) (invMat U) U, invMat_mul hU,
        mul_one, toRMat_mul]
    have hZ : (toRMat (NZ B)).mulVec (toRVec n) = toRVec (M.mulVec n) := by
      rw [hNZB, mulVec_toRVec]
    rw [hn]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    rw [hBU, hBR, hZ, ← Matrix.mulVec_mulVec, add_sub_cancel_right]
    rfl

end Work.SGsep
