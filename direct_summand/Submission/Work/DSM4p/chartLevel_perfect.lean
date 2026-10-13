import Mathlib
import Submission.Work.DSM4p.Chart
import Submission.Work.DSM4p.chartLevel_frobenius_surj
import Submission.Work.DSM4p.exists_eq_algebraMap_of_pow_pow

/-!
# DSM4p — permission of the chart levels

`Work.DSM4p.chartRing hG T N` is the `N`-th level `R[T_k^N / G_k] ⊆ R[1/G_0]` of the chart
model of the Riemann extension tower (`Submission/Work/DSM4p/Chart.lean`).  This file proves
that each level is a *perfect ring* — Bhatt, arXiv:1608.08882, §3, where perfectoidness is
verified on the chart presentations:

`PerfectRing (chartRing hG T N) p`, i.e. the absolute Frobenius `x ↦ x ^ p` is bijective.

## The two halves

* **Injectivity.** `chartRing hG T N` is a subring of the ambient `R[1/G_0]`, which is reduced
  because `R` is (`isReduced_of_perfect`, a perfect ring of prime characteristic has no
  nilpotents) and reducedness is preserved by localization.  Since `(p : R[1/G_0]) = 0`, the
  freshman's dream `(u - v) ^ p = u ^ p - v ^ p` holds (`sub_pow_pow_of_natCast_eq_zero`), and
  `u ^ p = v ^ p` forces `u - v = 0` by reducedness.

* **Surjectivity.** The level is generated as an `R`-algebra by the chart generators
  `x_k = T_k^N / G_k`, and each generator is a `p`-th power *inside the level*:
  `x_k = x_{k+1} ^ p` (`chartGenIn_pow`, the root relation for `G` together with the
  compatibility `T_{k+1}^p = T_k`).  In characteristic `p` the set of `p`-th powers is closed
  under sums and products, and contains the image of `R` because `R` is perfect; hence it is
  the whole level.  Formally this is the `Algebra.adjoin_induction` on
  `adjoin_chartGenIn_eq_top`.
-/

namespace Work.DSM4p

universe a

/-- **Freshman's dream for `(p : S) = 0`.**  In a commutative ring in which `p` vanishes, the
`p`-th power map is additive, `(x + y) ^ p = x ^ p + y ^ p`, for `p` prime.  This needs only
`(p : S) = 0`, not `CharP S p`, and therefore also covers the zero ring. -/
lemma add_pow_prime_of_natCast_eq_zero {S : Type*} [CommRing S] {p : ℕ} (hp : p.Prime)
    (hS : (p : S) = 0) (x y : S) : (x + y) ^ p = x ^ p + y ^ p := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (R := S) (p := p) hp x y
  rw [hr, hS]; ring

/-- **The chart levels are perfect.**  For a perfect ring `R` of prime characteristic `p`, any
compatible system `G` of `p`-power roots, and the chart level `chartRing hG T N` built from it,
the absolute Frobenius is bijective. -/
theorem chartLevel_perfect {p : ℕ} [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p]
    [PerfectRing R p] {G T : ℕ → R} (hG : Work.DSM4p.IsRootSystem p G)
    (hT : Work.DSM4p.IsRootSystem p T) (N : ℕ) :
    PerfectRing (Work.DSM4p.chartRing hG T N) p := by
  have hp : p.Prime := Fact.out
  refine ⟨⟨?_, ?_⟩⟩
  · -- **Injectivity** of the Frobenius map on the level.
    have hRred : IsReduced R := isReduced_of_perfect
    have hCred : IsReduced (ChartAmbient G) :=
      isReduced_localizationPreserves (Submonoid.powers (G 0)) _ hRred
    have hCp : (p : ChartAmbient G) = 0 := by
      rw [← map_natCast (algebraMap R (ChartAmbient G)) p, CharP.cast_eq_zero, map_zero]
    intro x y hxy
    -- Compare the two elements inside the reduced ambient localization.
    have hloc : ((x : ChartAmbient G)) ^ p = ((y : ChartAmbient G)) ^ p := by
      have h := congrArg (fun z : chartRing hG T N => (z : ChartAmbient G)) hxy
      simpa using h
    have hzero : ((x : ChartAmbient G) - (y : ChartAmbient G)) ^ p = 0 := by
      have h1 := sub_pow_pow_of_natCast_eq_zero hp hCp 1
        (x : ChartAmbient G) (y : ChartAmbient G)
      simp only [pow_one] at h1
      rw [h1, hloc, sub_self]
    have hsub : (x : ChartAmbient G) - (y : ChartAmbient G) = 0 :=
      eq_zero_of_pow_eq_zero hzero
    exact Subtype.ext (sub_eq_zero.mp hsub)
  · -- **Surjectivity** of the Frobenius map on the level.
    have hAp : (p : chartRing hG T N) = 0 := by
      rw [← map_natCast (algebraMap R (chartRing hG T N)) p, CharP.cast_eq_zero, map_zero]
    -- Every element of the adjoin of the chart generators is a `p`-th power.
    have hP : ∀ x ∈ Algebra.adjoin R (Set.range (chartGenIn hG T N)), ∃ y, y ^ p = x := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem a ha =>
          -- the root relation `x_k = x_{k+1} ^ p`
          obtain ⟨k, rfl⟩ := ha
          exact ⟨chartGenIn hG T N (k + 1), (chartGenIn_pow hG T hT N k).symm⟩
      | algebraMap r =>
          -- `R` is perfect, so its image consists of `p`-th powers
          obtain ⟨r', hr'⟩ := (PerfectRing.bijective_frobenius (R := R) (p := p)).2 r
          exact ⟨algebraMap R (chartRing hG T N) r', by
            rw [← map_pow]; exact congrArg (algebraMap R (chartRing hG T N)) hr'⟩
      | add a b ha hb iha ihb =>
          obtain ⟨ya, hya⟩ := iha
          obtain ⟨yb, hyb⟩ := ihb
          exact ⟨ya + yb, by rw [add_pow_prime_of_natCast_eq_zero hp hAp ya yb, hya, hyb]⟩
      | mul a b ha hb iha ihb =>
          obtain ⟨ya, hya⟩ := iha
          obtain ⟨yb, hyb⟩ := ihb
          exact ⟨ya * yb, by rw [mul_pow, hya, hyb]⟩
    intro x
    exact hP x (by rw [adjoin_chartGenIn_eq_top hG T N]; trivial)

end Work.DSM4p
