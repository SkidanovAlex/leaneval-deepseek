import Mathlib
import Submission.NK.CFTLib.Arl.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.CFTLib.Arl

open NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The real value of `x : K` at the real infinite place `w`, read through the completion. -/
private lemma ringEquivReal_algebraMap_eq (w : InfinitePlace K) (hw : w.IsReal) (y : K) :
    (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (algebraMap K w.Completion y)
      = (mixedEmbedding K y).1 ⟨w, hw⟩ := by
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
  simp [mixedEmbedding.mixedEmbedding_apply_isReal]

/-- The image of a `ℤ`-linear combination of the integral basis in the mixed space. -/
private lemma mixedEmbedding_coe_sum (z : Module.Free.ChooseBasisIndex ℤ (𝓞 K) → ℤ)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (mixedEmbedding K (((∑ i, z i • RingOfIntegers.basis K i : 𝓞 K) : K))).1 w
      = ∑ i, (z i : ℝ) * ((mixedEmbedding.latticeBasis K) i).1 w := by
  simp only [map_sum, Prod.fst_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [zsmul_eq_mul, integralBasis_apply]

/-- **Sign adjustment by an algebraic integer.**  For a number field `K`, a positive integer `m`
and a nowhere-vanishing function `r` on the real infinite places, there is `u ∈ 𝓞 K` such that
`1 + m u` has the sign of `r w` at every real place `w` (read in the completion `K_w ≅ ℝ`). -/
theorem exists_integral_sign_adjust (K : Type*) [Field K] [NumberField K]
    (m : ℕ) (hm : 0 < m) (r : NumberField.InfinitePlace K → ℝ)
    (hr : ∀ (w : NumberField.InfinitePlace K), w.IsReal → r w ≠ 0) :
    ∃ u : NumberField.RingOfIntegers K, ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      0 < r w * (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        (algebraMap K w.Completion ((1 : K) + m * ((u : NumberField.RingOfIntegers K) : K))) := by
  classical
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hiR : (0 : ℝ) < ((m : ℝ))⁻¹ := inv_pos.mpr hmR
  -- the target value at the real places
  set T : ℝ := 1 + ((m : ℝ))⁻¹ with hT
  -- the sign function on the real places
  set s : {w : InfinitePlace K // w.IsReal} → ℝ :=
    fun w => if 0 < r w.1 then (1 : ℝ) else -1 with hs
  -- the target point of the mixed space
  set t : mixedEmbedding.mixedSpace K := (fun w => s w * T, fun _ => 0) with ht
  -- its coordinates in the lattice basis
  set c : Module.Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ :=
    fun i => (mixedEmbedding.latticeBasis K).repr t i with hc
  -- the size of the basis vectors at the real places
  set C : {w : InfinitePlace K // w.IsReal} → ℝ :=
    fun w => ∑ i, |((mixedEmbedding.latticeBasis K) i).1 w| with hC
  have hCnn : ∀ w, 0 ≤ C w := by
    intro w; rw [hC]; exact Finset.sum_nonneg fun i _ => abs_nonneg _
  -- choose `N` large enough
  set S : ℝ := ((m : ℝ))⁻¹ + ∑ w, C w with hS
  set N : ℕ := Nat.ceil S + 1 with hN
  have hNr : (N : ℝ) = (Nat.ceil S : ℝ) + 1 := by rw [hN]; push_cast; ring
  have hNbig : ∀ w : {w : InfinitePlace K // w.IsReal}, ((m : ℝ))⁻¹ + C w < (N : ℝ) := by
    intro w
    have h1 : S ≤ (Nat.ceil S : ℝ) := Nat.le_ceil S
    have h2 : C w ≤ ∑ w, C w :=
      Finset.single_le_sum (fun i _ => hCnn i) (Finset.mem_univ w)
    have h3 : ((m : ℝ))⁻¹ + C w ≤ S := by rw [hS]; linarith
    rw [hNr]; linarith
  -- the integral element
  set u : 𝓞 K := ∑ i, ⌊(N : ℝ) * c i⌋ • RingOfIntegers.basis K i with hu
  refine ⟨u, ?_⟩
  intro w hw
  -- the value of `u` at the place `w`
  have hcoordu : (mixedEmbedding K ((u : 𝓞 K) : K)).1 ⟨w, hw⟩
      = ∑ i, ((⌊(N : ℝ) * c i⌋ : ℤ) : ℝ) * ((mixedEmbedding.latticeBasis K) i).1 ⟨w, hw⟩ := by
    rw [hu]; exact mixedEmbedding_coe_sum _ _
  -- the target coordinates
  have hsumt : ∑ i, c i • (mixedEmbedding.latticeBasis K) i = t := by
    rw [hc]; exact Module.Basis.sum_repr _ _
  have hcoordt : ∑ i, c i * ((mixedEmbedding.latticeBasis K) i).1 ⟨w, hw⟩ = s ⟨w, hw⟩ * T := by
    have h := congrArg (fun x : mixedEmbedding.mixedSpace K => x.1 ⟨w, hw⟩) hsumt
    simpa [Finset.sum_apply, Prod.fst_sum, Pi.smul_apply, smul_eq_mul, ht] using h
  -- the rounding error
  have hzi : ∀ i, |((⌊(N : ℝ) * c i⌋ : ℤ) : ℝ) - (N : ℝ) * c i| < 1 := by
    intro i
    have h1 : ((⌊(N : ℝ) * c i⌋ : ℤ) : ℝ) ≤ (N : ℝ) * c i := Int.floor_le _
    have h2 : (N : ℝ) * c i < ((⌊(N : ℝ) * c i⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    rw [abs_lt]; constructor <;> linarith
  -- the error bound
  have herror : |(∑ i, ((⌊(N : ℝ) * c i⌋ : ℤ) : ℝ) * ((mixedEmbedding.latticeBasis K) i).1 ⟨w, hw⟩)
        - (N : ℝ) * (s ⟨w, hw⟩ * T)| ≤ C ⟨w, hw⟩ := by
    have hsplit : (∑ i, ((⌊(N : ℝ) * c i⌋ : ℤ) : ℝ) * ((mixedEmbedding.latticeBasis K) i).1 ⟨w, hw⟩)
          - (N : ℝ) * (s ⟨w, hw⟩ * T)
        = ∑ i, (((⌊(N : ℝ) * c i⌋ : ℤ) : ℝ) - (N : ℝ) * c i)
            * ((mixedEmbedding.latticeBasis K) i).1 ⟨w, hw⟩ := by
      rw [← hcoordt, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit]
    calc |∑ i, (((⌊(N : ℝ) * c i⌋ : ℤ) : ℝ) - (N : ℝ) * c i)
            * ((mixedEmbedding.latticeBasis K) i).1 ⟨w, hw⟩|
        ≤ ∑ i, |(((⌊(N : ℝ) * c i⌋ : ℤ) : ℝ) - (N : ℝ) * c i)
            * ((mixedEmbedding.latticeBasis K) i).1 ⟨w, hw⟩| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |((⌊(N : ℝ) * c i⌋ : ℤ) : ℝ) - (N : ℝ) * c i|
            * |((mixedEmbedding.latticeBasis K) i).1 ⟨w, hw⟩| := by
          exact Finset.sum_congr rfl fun i _ => abs_mul _ _
      _ ≤ ∑ i, 1 * |((mixedEmbedding.latticeBasis K) i).1 ⟨w, hw⟩| :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (le_of_lt (hzi i)) (abs_nonneg _)
      _ = C ⟨w, hw⟩ := by rw [hC]; simp
  -- the key inequality: `s w * (mixed embedding of u at w) > 1/m`
  have hsabs : |s ⟨w, hw⟩| = 1 := by
    rw [hs]; simp only; split_ifs <;> norm_num
  have hs2 : s ⟨w, hw⟩ * s ⟨w, hw⟩ = 1 := by
    rw [hs]; simp only; split_ifs <;> norm_num
  have hsNT : s ⟨w, hw⟩ * ((N : ℝ) * (s ⟨w, hw⟩ * T)) = (N : ℝ) * T := by
    calc s ⟨w, hw⟩ * ((N : ℝ) * (s ⟨w, hw⟩ * T))
        = (s ⟨w, hw⟩ * s ⟨w, hw⟩) * ((N : ℝ) * T) := by ring
      _ = (N : ℝ) * T := by rw [hs2, one_mul]
  have hkey : ((m : ℝ))⁻¹ < s ⟨w, hw⟩ * (mixedEmbedding K ((u : 𝓞 K) : K)).1 ⟨w, hw⟩ := by
    have hmain : s ⟨w, hw⟩ * (mixedEmbedding K ((u : 𝓞 K) : K)).1 ⟨w, hw⟩
        ≥ (N : ℝ) * T - C ⟨w, hw⟩ := by
      have hX : s ⟨w, hw⟩ * (mixedEmbedding K ((u : 𝓞 K) : K)).1 ⟨w, hw⟩
          = (N : ℝ) * T + s ⟨w, hw⟩ * ((mixedEmbedding K ((u : 𝓞 K) : K)).1 ⟨w, hw⟩
              - (N : ℝ) * (s ⟨w, hw⟩ * T)) := by
        rw [mul_sub, hsNT]; ring
      rw [hX, hcoordu]
      have h2 : -(C ⟨w, hw⟩) ≤ s ⟨w, hw⟩ * ((∑ i, ((⌊(N : ℝ) * c i⌋ : ℤ) : ℝ)
            * ((mixedEmbedding.latticeBasis K) i).1 ⟨w, hw⟩) - (N : ℝ) * (s ⟨w, hw⟩ * T)) := by
        have h3 := neg_abs_le (s ⟨w, hw⟩ * ((∑ i, ((⌊(N : ℝ) * c i⌋ : ℤ) : ℝ)
            * ((mixedEmbedding.latticeBasis K) i).1 ⟨w, hw⟩) - (N : ℝ) * (s ⟨w, hw⟩ * T)))
        rw [abs_mul, hsabs, one_mul] at h3
        linarith [neg_le_neg herror]
      linarith
    have hNT : ((m : ℝ))⁻¹ < (N : ℝ) * T - C ⟨w, hw⟩ := by
      have hNN : (0 : ℝ) ≤ (N : ℝ) * ((m : ℝ))⁻¹ :=
        mul_nonneg (Nat.cast_nonneg _) (le_of_lt hiR)
      nlinarith [hNbig ⟨w, hw⟩, hT, hNN]
    linarith
  -- compute the image of `1 + m * u` under the completion
  have hval : (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        (algebraMap K w.Completion ((1 : K) + m * ((u : 𝓞 K) : K)))
      = 1 + (m : ℝ) * (mixedEmbedding K ((u : 𝓞 K) : K)).1 ⟨w, hw⟩ := by
    have h1 : algebraMap K w.Completion ((1 : K) + m * ((u : 𝓞 K) : K))
        = 1 + ((m : ℕ) : w.Completion) * algebraMap K w.Completion ((u : 𝓞 K) : K) := by
      rw [map_add, map_mul, map_one, map_natCast]
    rw [h1, map_add, map_mul, map_one, map_natCast, ringEquivReal_algebraMap_eq]
  rw [hval]
  -- the final sign discussion
  by_cases hpos : 0 < r w
  · have hs1 : s ⟨w, hw⟩ = 1 := by rw [hs]; simp only; exact if_pos hpos
    rw [hs1, one_mul] at hkey
    have : 1 < (m : ℝ) * (mixedEmbedding K ((u : 𝓞 K) : K)).1 ⟨w, hw⟩ := by
      have := mul_lt_mul_of_pos_left hkey hmR
      rwa [mul_inv_cancel₀ (ne_of_gt hmR)] at this
    nlinarith
  · have hneg : r w < 0 := by
      rcases lt_trichotomy (r w) 0 with h | h | h
      · exact h
      · exact absurd h (hr w hw)
      · exact absurd h hpos
    have hs1 : s ⟨w, hw⟩ = -1 := by rw [hs]; simp only; exact if_neg hpos
    rw [hs1, neg_one_mul] at hkey
    have : (m : ℝ) * (mixedEmbedding K ((u : 𝓞 K) : K)).1 ⟨w, hw⟩ < -1 := by
      have := mul_lt_mul_of_pos_left hkey hmR
      rw [mul_inv_cancel₀ (ne_of_gt hmR)] at this
      linarith
    nlinarith

end NK.CFTLib.Arl
