import Mathlib
import Submission.NK.NUV2.RouteB.CongCountDefs

namespace NK.NUV2.RouteB.CongCount

open NumberField NumberField.mixedEmbedding

/-- The set of points of the fundamental cone whose `mixedEmbedding.norm` is `≤ X` is
bounded in the mixed space. -/
theorem isBounded_fundamentalCone_norm_le (K : Type*) [Field K] [NumberField K] (X : ℝ) :
    Bornology.IsBounded {x : mixedSpace K |
      x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ X} := by
  classical
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    (fundamentalCone.isBounded_normLeOne K)
  refine isBounded_iff_forall_norm_le.mpr ⟨max 1 X * max C 0, fun x hx => ?_⟩
  obtain ⟨hxcone, hxnorm⟩ := hx
  have hpos : 0 < mixedEmbedding.norm x := fundamentalCone.norm_pos_of_mem hxcone
  set n : ℕ := Module.finrank ℚ K with hn
  have hnpos : 1 ≤ n := by
    have : 0 < Module.finrank ℚ K := Module.finrank_pos
    omega
  set s : ℝ := (mixedEmbedding.norm x) ^ ((n : ℝ))⁻¹ with hs
  have hs_pos : 0 < s := Real.rpow_pos_of_pos hpos _
  have hs_ne : s ≠ 0 := hs_pos.ne'
  have hs_rpow : s ^ (n : ℝ) = mixedEmbedding.norm x := by
    rw [hs]
    rw [← Real.rpow_mul hpos.le]
    have hnne : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le Nat.zero_lt_one hnpos))
    rw [inv_mul_cancel₀ hnne, Real.rpow_one]
  have hs_natpow : s ^ n = mixedEmbedding.norm x := by
    rw [← Real.rpow_natCast s n]
    exact hs_rpow
  have hycone : s⁻¹ • x ∈ fundamentalCone K :=
    fundamentalCone.smul_mem_of_mem hxcone (inv_ne_zero hs_ne)
  have hynorm : mixedEmbedding.norm (s⁻¹ • x) = 1 := by
    rw [NumberField.mixedEmbedding.norm_smul, abs_of_pos (inv_pos.mpr hs_pos), inv_pow, hs_natpow,
      inv_mul_cancel₀ hpos.ne']
  have hymem : s⁻¹ • x ∈ fundamentalCone.normLeOne K :=
    fundamentalCone.mem_normLeOne.mpr ⟨hycone, le_of_eq hynorm⟩
  have hyC : ‖s⁻¹ • x‖ ≤ C := hC _ hymem
  have hx_eq : s • (s⁻¹ • x) = x := by
    rw [smul_smul, mul_inv_cancel₀ hs_ne, one_smul]
  have hnx : ‖x‖ = s * ‖s⁻¹ • x‖ := by
    have h1 : ‖x‖ = ‖s • (s⁻¹ • x)‖ := by rw [hx_eq]
    rw [h1, _root_.norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos]
  have hs_le : s ≤ max 1 X := by
    rcases lt_or_ge s 1 with h | h
    · exact le_trans h.le (le_max_left _ _)
    · have h1 : s ≤ s ^ n := by
        calc s = s ^ 1 := (pow_one s).symm
          _ ≤ s ^ n := pow_le_pow_right₀ h hnpos
      calc s ≤ s ^ n := h1
        _ = mixedEmbedding.norm x := hs_natpow
        _ ≤ X := hxnorm
        _ ≤ max 1 X := le_max_right _ _
  calc ‖x‖ = s * ‖s⁻¹ • x‖ := hnx
    _ ≤ max 1 X * max C 0 := by
        refine mul_le_mul hs_le (le_trans hyC (le_max_left _ _)) (norm_nonneg _) ?_
        exact le_trans zero_le_one (le_max_left _ _)

/-- The set of algebraic integers mapping into the fundamental cone with norm `≤ X` is
finite. -/
theorem finite_mixedEmbedding_cone_norm_le (K : Type*) [Field K] [NumberField K] (X : ℝ) :
    {α : 𝓞 K | mixedEmbedding K α ∈ fundamentalCone K ∧
      mixedEmbedding.norm (mixedEmbedding K α) ≤ X}.Finite := by
  classical
  let B : Set (mixedSpace K) :=
    {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ X}
  have hB : Bornology.IsBounded B := isBounded_fundamentalCone_norm_le K X
  have hLclosed : IsClosed ((mixedEmbedding.integerLattice K : Set (mixedSpace K))) := by
    change IsClosed ((mixedEmbedding.integerLattice K).toAddSubgroup : Set (mixedSpace K))
    have : DiscreteTopology (mixedEmbedding.integerLattice K).toAddSubgroup :=
      (inferInstance : DiscreteTopology (mixedEmbedding.integerLattice K))
    exact AddSubgroup.isClosed_of_discrete
  have hLdisc : IsDiscrete ((mixedEmbedding.integerLattice K : Set (mixedSpace K))) := by
    have : DiscreteTopology (mixedEmbedding.integerLattice K) := inferInstance
    exact DiscreteTopology.isDiscrete
  have hfin : (B ∩ (mixedEmbedding.integerLattice K : Set (mixedSpace K))).Finite :=
    Metric.finite_isBounded_inter_isClosed hLdisc hB hLclosed
  let f : 𝓞 K → mixedSpace K := fun α => mixedEmbedding K α
  have hinj : Function.Injective f := by
    intro a b hab
    exact RingOfIntegers.ext (mixedEmbedding_injective K hab)
  have hpre : (f ⁻¹' (B ∩ (mixedEmbedding.integerLattice K : Set (mixedSpace K)))).Finite :=
    Set.Finite.preimage hinj.injOn hfin
  refine hpre.subset ?_
  intro α hα
  obtain ⟨hcone, hnorm⟩ := hα
  have hmem : f α ∈ mixedEmbedding.integerLattice K :=
    LinearMap.mem_range.mpr ⟨α, rfl⟩
  exact ⟨⟨hcone, hnorm⟩, hmem⟩

theorem finite_cosetConeSet (K : Type*) [Field K] [NumberField K]
    (𝔪 : Ideal (NumberField.RingOfIntegers K))
    (c : NumberField.RingOfIntegers K) (X : ℝ) :
    {α : NumberField.RingOfIntegers K | α - c ∈ 𝔪 ∧
      NumberField.mixedEmbedding K α ∈
        NumberField.mixedEmbedding.fundamentalCone K ∧
      NumberField.mixedEmbedding.norm (NumberField.mixedEmbedding K α) ≤ X}.Finite := by
  refine (finite_mixedEmbedding_cone_norm_le K X).subset ?_
  intro α hα
  exact ⟨hα.2.1, hα.2.2⟩

end NK.NUV2.RouteB.CongCount
