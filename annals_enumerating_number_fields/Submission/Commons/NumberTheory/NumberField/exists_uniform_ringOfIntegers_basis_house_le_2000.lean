import Mathlib
import Submission.Commons.NumberTheory.NumberField.exists_uniform_ringOfIntegers_basis_house_le

/-!
# A uniform `ℤ`-basis of the ring of integers with house at most `n ^ 2000 · Δ ^ 2000`

This is the explicit-constant specialisation (`c = 2000`) of
`Commons.NumberTheory.NumberField.exists_uniform_ringOfIntegers_basis_house_le`:
for every number field `K` of degree `n` and root discriminant `Δ`, the ring of
integers `𝓞 K` admits a `ℤ`-basis all of whose elements have house at most
`n ^ 2000 · Δ ^ 2000`.

The proof is the same construction as in the general uniform bound: Minkowski's
second theorem together with the bounded-basis theorem produce a basis of the
Euclidean lattice whose elements have norm at most
`(2 n + 1) · (√n · (16 Δ)^2)`, and a final numerical inequality dominates this
by `n ^ 2000 · Δ ^ 2000`.
-/

noncomputable section

open scoped NumberField BigOperators NNReal ENNReal Classical
open NumberField NumberField.mixedEmbedding MeasureTheory Set Filter Metric Submodule

namespace Commons.NumberTheory.NumberField

/-- For a number field `K`, the ring of integers admits a `ℤ`-basis whose elements
all have house at most `(finrank ℚ K) ^ 2000 * rootDiscr K ^ 2000`. -/
theorem exists_uniform_ringOfIntegers_basis_house_le_2000 (K : Type*) [Field K] [NumberField K] :
    ∃ b : Module.Basis (Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)) ℤ
        (NumberField.RingOfIntegers K),
      ∀ i, NumberField.house ((b i : NumberField.RingOfIntegers K) : K) ≤
        (Module.finrank ℚ K : ℝ) ^ (2000 : ℝ) * NumberField.rootDiscr K ^ (2000 : ℝ) := by
  classical
  by_cases hdeg1 : Module.finrank ℚ K = 1
  · -- degree one: the ring of integers is `ℤ`, so `{±1}` is a basis of house `1`
    obtain ⟨b, hb⟩ :=
      Commons.NumberTheory.NumberField.basis_house_le_one_of_finrank_eq_one K hdeg1
    refine ⟨b, ?_⟩
    intro i
    have hpow : ((Module.finrank ℚ K : ℝ)) ^ (2000 : ℝ) = 1 := by
      rw [hdeg1]
      simp
    have hΔc : (1 : ℝ) ≤ NumberField.rootDiscr K ^ (2000 : ℝ) := by
      have := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) (one_le_rootDiscr K)
        (by norm_num : (0 : ℝ) ≤ 2000)
      simpa using this
    calc NumberField.house ((b i : NumberField.RingOfIntegers K) : K) ≤ 1 := hb i
      _ ≤ (Module.finrank ℚ K : ℝ) ^ (2000 : ℝ) * NumberField.rootDiscr K ^ (2000 : ℝ) := by
          rw [hpow, one_mul]; exact hΔc
  · have hdeg2 : 2 ≤ SmallBasis.deg K := by
      have h1 : 1 ≤ SmallBasis.deg K := by
        dsimp [SmallBasis.deg]
        exact Nat.succ_le_of_lt (Module.finrank_pos (R := ℚ) (M := K))
      have hne : SmallBasis.deg K ≠ 1 := fun h => hdeg1 h
      omega
    obtain ⟨b0, hb0⟩ := SmallBasis.exists_euc_basis_bounded K
    obtain ⟨B, hB⟩ := SmallBasis.basis_of_euc_basis K b0
    set R : ℝ := (2 * (SmallBasis.deg K : ℝ) + 1) *
        (Real.sqrt (SmallBasis.deg K) * (16 * NumberField.rootDiscr K) ^ 2) with hRdef
    have hR0 : 0 ≤ R := by
      rw [hRdef]; positivity
    have hBval : ∀ i : Fin (SmallBasis.deg K), B i = SmallBasis.ofEuc K (b0 i) :=
      fun i => Subtype.ext (hB i)
    have hEuc : ∀ i : Fin (SmallBasis.deg K), SmallBasis.eucOf K (B i) = b0 i := by
      intro i
      rw [hBval i, SmallBasis.eucOf_ofEuc]
    have hBsup : ∀ i : Fin (SmallBasis.deg K),
        ‖(euclidean.toMixed K) ((SmallBasis.eucOf K (B i)) : euclidean.mixedSpace K)‖ ≤ R := by
      intro i
      rw [hEuc i]
      calc ‖(euclidean.toMixed K) ((b0 i : SmallBasis.EucLattice K) : euclidean.mixedSpace K)‖
          ≤ ‖((b0 i : SmallBasis.EucLattice K) : euclidean.mixedSpace K)‖ :=
            SmallBasis.sup_norm_le_euc_norm K _
        _ ≤ R := by rw [hRdef]; exact hb0 i
    have hhouse : ∀ i : Fin (SmallBasis.deg K),
        NumberField.house ((B i : 𝓞 K) : K) ≤ R :=
      SmallBasis.house_basis_le K B hR0 hBsup
    have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = SmallBasis.deg K := by
      dsimp [SmallBasis.deg]
      rw [← Module.finrank_eq_card_chooseBasisIndex ℤ (𝓞 K)]
      exact NumberField.RingOfIntegers.rank K
    let eqv : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin (SmallBasis.deg K) :=
      Fintype.equivFinOfCardEq hcard
    refine ⟨B.reindex eqv.symm, ?_⟩
    intro i
    have hval : (B.reindex eqv.symm) i = B (eqv i) := by
      rw [Module.Basis.reindex_apply]
      simp
    rw [hval]
    refine (hhouse (eqv i)).trans ?_
    have hn2R : (2 : ℝ) ≤ (SmallBasis.deg K : ℝ) := by exact_mod_cast hdeg2
    have hfin := SmallBasis.basis_house_final_ineq (SmallBasis.deg K : ℝ) (NumberField.rootDiscr K)
      hn2R (one_le_rootDiscr K)
    simpa [SmallBasis.deg, hRdef] using hfin

end Commons.NumberTheory.NumberField
