import Mathlib
import Submission.Commons.RingTheory.Valuation.exists_pow_eq_algebraMap_of_isAlgebraic
import Submission.Commons.RingTheory.Valuation.exists_separator_of_pairwise_independent

namespace Commons.RingTheory.Valuation

/-- **Coinitiality of the value group of a Henselian valuation subring.**
If `V` is a proper valuation subring of `F` and `W` is a valuation subring of an algebraic
extension `L` restricting to `V` (i.e. `W.comap (algebraMap F L) = V`), then every positive
value `η` in the value group of `W` dominates the valuation of some nonzero element of `F`.

The proof uses the classical fact that for algebraic extensions the value group extension is
torsion: for `x : L` the lemma `exists_pow_eq_algebraMap_of_isAlgebraic` provides `n > 0` and
`y : F` with `(W.valuation x) ^ n = W.valuation (algebraMap F L y)`.  Writing `η = W.valuation x`,
we then distinguish the two cases `η ≥ 1` and `η < 1`. -/
theorem exists_algebraMap_valuation_lt_of_ne_top {F L : Type*} [Field F] [Field L] [Algebra F L]
    (V : ValuationSubring F) [HenselianLocalRing V] (hV : V ≠ ⊤) (W : ValuationSubring L)
    (hW : W.comap (algebraMap F L) = V) (halg : Algebra.IsAlgebraic F L) {η : W.ValueGroup}
    (hη : 0 < η) : ∃ c : F, c ≠ 0 ∧ W.valuation (algebraMap F L c) < η := by
  classical
  -- Realize `η` as the value of a nonzero `x : L`.
  obtain ⟨x, hx⟩ := W.valuation_surjective η
  have hx0 : x ≠ 0 :=
    (Valuation.ne_zero_iff W.valuation).mp (by rw [hx]; exact ne_of_gt hη)
  -- Torsion of the value-group extension `Γ_L / Γ_F`.
  obtain ⟨n, hn, y, hy0, hy⟩ :=
    exists_pow_eq_algebraMap_of_isAlgebraic W.valuation
      (@Algebra.IsAlgebraic.isAlgebraic F L _ _ _ halg x) hx0
  -- hy : (W.valuation x) ^ n = W.valuation (algebraMap F L y)
  have hy' : W.valuation (algebraMap F L y) = η ^ n := by rw [← hy, hx]
  rcases le_or_gt 1 η with hge | hlt
  · -- Case `η ≥ 1`: use a non-unit `x₀` of `V`, whose image has value `> 1`.
    obtain ⟨x₀, hx₀⟩ := exists_valuation_gt_one V hV
    have hx₀_notmem : x₀ ∉ V := by
      rw [← ValuationSubring.valuation_le_one_iff V x₀]
      exact not_le.mpr hx₀
    have hx₀_notmemW : algebraMap F L x₀ ∉ W :=
      fun hmem => hx₀_notmem (by rw [← hW]; exact hmem)
    have hval_gt : 1 < W.valuation (algebraMap F L x₀) := by
      have h := (ValuationSubring.valuation_le_one_iff W (algebraMap F L x₀)).mp
      exact lt_of_not_ge (fun hle => hx₀_notmemW (h hle))
    have hx₀_ne : x₀ ≠ 0 :=
      (Valuation.ne_zero_iff V.valuation).mp (ne_of_gt (lt_trans zero_lt_one hx₀))
    refine ⟨x₀⁻¹, inv_ne_zero hx₀_ne, ?_⟩
    rw [map_inv₀ (algebraMap F L) x₀, Valuation.map_inv]
    exact lt_of_lt_of_le (inv_lt_one_of_one_lt₀ hval_gt) hge
  · -- Case `η < 1`: square `y`; this lowers the value from `η ^ n` to `η ^ (2n) < η`.
    refine ⟨y * y, mul_ne_zero hy0 hy0, ?_⟩
    have hval : W.valuation (algebraMap F L (y * y)) = η ^ (2 * n) := by
      rw [map_mul (algebraMap F L), Valuation.map_mul, hy', ← pow_add, two_mul]
    rw [hval]
    have h2n : 2 ≤ 2 * n := by omega
    have hle : η ^ (2 * n) ≤ η ^ 2 := pow_le_pow_of_le_one hη.le hlt.le h2n
    have hsq : η ^ 2 < η := by
      rw [pow_two]
      exact mul_lt_of_lt_one_right hη hlt
    exact lt_of_le_of_lt hle hsq

end Commons.RingTheory.Valuation
