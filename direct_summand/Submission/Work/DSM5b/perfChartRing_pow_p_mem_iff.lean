import Mathlib
import Submission.Work.DSMap.Mix2
import Submission.Work.DSM5b.Basic

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
universe a

section Helpers

variable (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p] {ι : Type a}
  [DecidableEq ι] (t : ι → R) (S : Finset ι)

/-- In any localisation of a ring of characteristic `p`, the natural number `p` is `0`.  (No
`CharP` instance is available for the localisation itself: it need not be of characteristic `p`
when the localised element is nilpotent; but `(p : S) = 0` always holds and is all we need.) -/
lemma natCast_p_eq_zero_localization :
    (p : Localization.Away (tS t S)) = 0 := by
  rw [← map_natCast (algebraMap R (Localization.Away (tS t S)))]
  simp

/-- Freshman's dream for the `p`-th power map in the localisation, available since `(p : S) = 0`. -/
lemma add_pow_p_localization (x y : Localization.Away (tS t S)) (n : ℕ) :
    (x + y) ^ (p ^ n) = x ^ (p ^ n) + y ^ (p ^ n) := by
  obtain ⟨r, hr⟩ :=
    exists_add_pow_prime_pow_eq (p := p) (R := Localization.Away (tS t S)) Fact.out x y n
  rw [hr, natCast_p_eq_zero_localization p t S]
  ring

/-- `perfChartGens` is closed under addition: a `CharP`-free version of `perfChartGens_add`. -/
lemma perfChartGens_add' {x y : Localization.Away (tS t S)} {e₁ e₂ : ℕ}
    (hx : x ^ (p ^ e₁) ∈ chartRing t S) (hy : y ^ (p ^ e₂) ∈ chartRing t S) :
    (x + y) ^ (p ^ max e₁ e₂) ∈ chartRing t S := by
  rw [add_pow_p_localization p t S x y]
  exact Subalgebra.add_mem _
    (perfChartGens_mono p t S (le_max_left e₁ e₂) hx)
    (perfChartGens_mono p t S (le_max_right e₁ e₂) hy)

/-- The set `perfChartGens p t S` of elements some `p`-power of which lies in the honest chart
ring is closed under all the algebra operations, hence is the underlying set of an
`R`-subalgebra — which is then the perfected chart ring. -/
def perfChartSubalgebra : Subalgebra R (Localization.Away (tS t S)) where
  carrier := perfChartGens p t S
  mul_mem' := by
    rintro x y ⟨e₁, hx⟩ ⟨e₂, hy⟩
    exact ⟨max e₁ e₂, perfChartGens_mul p t S hx hy⟩
  one_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨e₁, hx⟩ ⟨e₂, hy⟩
    exact ⟨max e₁ e₂, perfChartGens_add' p t S hx hy⟩
  zero_mem' := ⟨0, by simp⟩
  algebraMap_mem' := by
    intro r
    exact ⟨0, by simp⟩

lemma perfChartRing_eq_perfChartSubalgebra :
    perfChartRing p t S = perfChartSubalgebra p t S := by
  refine le_antisymm ?_ ?_
  · rw [perfChartRing_eq_adjoin p t S]
    exact (Algebra.adjoin_le_iff).mpr fun _ hx => hx
  · intro x hx
    rw [perfChartRing_eq_adjoin p t S]
    exact Algebra.subset_adjoin hx

/-- Membership characterisation of the perfected chart ring. -/
lemma mem_perfChartRing_iff {y : Localization.Away (tS t S)} :
    y ∈ perfChartRing p t S ↔ ∃ e : ℕ, y ^ (p ^ e) ∈ chartRing t S := by
  rw [perfChartRing_eq_perfChartSubalgebra p t S]
  exact Iff.rfl

end Helpers

/-- The perfected chart ring `perfChartRing p t S ⊆ Localization.Away (tS t S)` (the perfection of
the honest blowup chart `chartRing t S = R[J/t_S]`, `J = (t_i)`) is closed under `p`-th roots: for
every element `x` of the localisation, `x ^ p` lies in the perfected chart iff `x` does.  With `R`
perfect (so the localisation is reduced) this says that the `p`-th power map is a bijection of the
perfected chart ring onto itself — the structural fact behind the M5b Frobenius upgrade.

Route: `perfChartRing p t S = Algebra.adjoin R G` with `G = {x | ∃ e, x ^ (p^e) ∈ chartRing t S}`.
The set `G` is an `R`-subalgebra: it is closed under `+` (`(x+y)^(p^n) = x^(p^n) + y^(p^n)`,
`add_pow_char_pow`; the localisation has characteristic `p`) and under `*`
(`Subalgebra.mul_mem` with the exponents maximised), and contains the image of `R` (take `e = 0`).
Hence `perfChartRing p t S = ↑G` as a set, and the equivalence is
`x^(p^(e+1)) = (x^p)^(p^e) ∈ chartRing t S`.  The helper `perfChartGens_add`/`perfChartGens_mul`
of `Submission.Work.DSM5b.Basic` already gives the closure steps (they carry the required
`CharP (Localization.Away (tS t S)) p` instance). -/
theorem perfChartRing_pow_p_mem_iff (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R]
    [CharP R p] [PerfectRing R p] {ι : Type a} [DecidableEq ι] (t : ι → R) (S : Finset ι)
    (x : Localization.Away (tS t S)) :
    x ^ p ∈ perfChartRing p t S ↔ x ∈ perfChartRing p t S := by
  rw [mem_perfChartRing_iff p t S (y := x ^ p), mem_perfChartRing_iff p t S (y := x)]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e + 1, ?_⟩
    rwa [pow_succ', pow_mul]
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    rw [show (x ^ p) ^ (p ^ f) = (x ^ (p ^ f)) ^ p from by
      rw [← pow_mul, ← pow_mul, mul_comm p (p ^ f)]]
    exact Subalgebra.pow_mem _ hf p

end Work.DSM5b
