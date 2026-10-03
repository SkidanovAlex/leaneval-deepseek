import Mathlib
import Submission.Work.KMTPlan.A6.BilinearAverageLqUniform

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6

open Work.Analysis.Concentration

/-- **(avg-1) in the form used by the CRT assembly.**  From Appendix C, Corollary `cor:1`
(`Corollary1 P P.natDegree`: the fibre counting function of `P` modulo every prime power has a
bounded `L^s` norm for `s < d/(d-1)`, uniformly in the prime power) we obtain, for every
`2 ≤ q < 2d/(d-1)`, a constant `K` with `‖A_{ℤ/p^jℤ}(f,g)‖_{L^q} ≤ K‖f‖_{L²}‖g‖_{L²}` for all
primes `p` and all `j ≥ 1`.

Indeed `s = q/2 < d/(d-1)`, and Cauchy–Schwarz in the summation index together with Young's
inequality (`Work.Analysis.Paraproduct.bilinAverage_lq_fiber`) turn the `L^s` concentration
bound `‖h‖_{L^s} ≤ C` into the `L² × L² → L^{2s}` bound with constant `√C`. -/
theorem avg1_of_corollary1 (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hConc : Corollary1 P P.natDegree) :
    ∀ q : ℝ, 2 ≤ q → q < 2 * (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1) →
      ∃ K : ℝ, 0 < K ∧ ∀ (p j : ℕ) [Fact p.Prime], 1 ≤ j →
        BilinearAverageLq P (p ^ j) q K := by
  intro q hq2 hqT
  have hdR : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
  have hden : (0 : ℝ) < (P.natDegree : ℝ) - 1 := by linarith
  have hs0 : 0 < q / 2 := by linarith
  have hsd : q / 2 < (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1) := by
    have hden' : ((P.natDegree : ℝ) - 1) ≠ 0 := ne_of_gt hden
    have hbridge : (2 * (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1)) / 2
        = (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1) := by
      field_simp
    have hL : q / 2 < (2 * (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1)) / 2 := by linarith
    rwa [hbridge] at hL
  obtain ⟨C, hCpos, hCb⟩ := hConc (q / 2) hs0 hsd
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hCpos, fun p j _ hj => ?_⟩
  have hFL : LpNormZMod (p ^ j) (q / 2)
      (fun m => (polyFiberCard P (p ^ j) m : ℂ)) ≤ C :=
    Work.Analysis.Paraproduct.lpNorm_fiberCard_le_of_fiberLpBound P (p ^ j) hs0 hCpos.le
      (hCb p j hj)
  have h1 : 1 ≤ q / 2 := by linarith
  intro f g
  have h := Work.Analysis.Paraproduct.bilinAverage_lq_fiber P (p ^ j) (s := q / 2) (C := C)
    h1 hFL f g
  rwa [show 2 * (q / 2) = q by ring] at h

/-- **The paper's `(Avg-prof)` of §10 on the finite cyclic groups, from the single-scale
minor-arc estimate `improv`.**  Krause--Mirek--Tao, *Pointwise ergodic theorems for
non-conventional bilinear polynomial averages*, Annals 195 (2022), §10: for a polynomial
`P ∈ ℤ[X]` of degree `d ≥ 2` and every `1 ≤ q < 2d/(d-1)` there is `C = C(P,q) > 0` such that
for *every* modulus `Q ≠ 0`

`‖A(f,g)‖_{L^q(ℤ/Qℤ)} ≤ C ‖f‖_{L²}‖g‖_{L²}`,  `A(f,g)(x) = Q⁻¹ ∑_y f(x-y) g(x-P(y))`.

The proof follows §10 in three steps:

* **(avg-1)**: the uniform-in-`(p,j)` prime-power bound from Appendix C's concentration
  estimate, supplied here through `Corollary1WeakType`/`Corollary1` (see
  `avg1_of_corollary1`);
* **(avg-2)**: the large-prime improvement to constant `1` (`bilinAvgLq_largePrime_avg2`),
  whose proof uses the single-scale minor-arc estimate `improv` (the hypothesis `hI`, via
  Proposition `bile-2` = `MdlBileR1OfImprov`) for the mean-zero `L¹` gain
  (`meanZero_l1_gain_largePrime_of_improv`), interpolation with (avg-1) and a Taylor expansion;
* **CRT/tensor factorisation**: `BilinearAverageLq_crt` iterated over the prime powers
  dividing `Q`, together with the fact that only the finitely many primes below the threshold
  of (avg-2) contribute a constant `> 1`
  (`BilinearAverageLqUniform_of_primePower`). -/
theorem BilinearAverageLqUniformImprov (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hI : Work.KMTContract.ImprovKMT P) :
    ∀ q : ℝ, 1 ≤ q → q < 2 * (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1) →
      ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℕ) [NeZero Q] (f g : ZMod Q → ℂ),
        Work.Analysis.Concentration.LpNormZMod Q q
            (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f g)
          ≤ C * Work.Analysis.Concentration.LpNormZMod Q 2 f *
              Work.Analysis.Concentration.LpNormZMod Q 2 g := by
  intro q hq hqT
  have hd1 : 1 < P.natDegree := by omega
  -- Appendix C: the concentration estimate for the fibres of `P` modulo prime powers,
  -- uniformly in the prime and the exponent.
  have hConc : Corollary1 P P.natDegree :=
    Work.Analysis.Concentration.corollary1_of_weakType hd1
      (Work.KMTPlan.A6.ConcAux2.fibreWeakType_of_cover P hd)
  -- (avg-1): the uniform prime-power bound.
  have hUniform := avg1_of_corollary1 P hd hConc
  -- (avg-2): the large-prime improvement; at `q = 2` the elementary `L²` bound already has
  -- constant `1`.
  have hLarge : ∀ q : ℝ, 2 ≤ q → q < 2 * (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1) →
      ∃ p₀ : ℕ, ∀ (p j : ℕ) [Fact p.Prime], p₀ ≤ p → 1 ≤ j →
        BilinearAverageLq P (p ^ j) q 1 := by
    intro q' hq2 hqT'
    rcases eq_or_lt_of_le hq2 with h | h
    · subst h
      refine ⟨0, ?_⟩
      intro p j _ hp0 hj f g
      exact bilinearAverageLq_le_two P (by norm_num) le_rfl (p ^ j) f g
    · obtain ⟨p₀, hp₀⟩ := bilinAvgLq_largePrime_avg2 P hd hI hConc q' h hqT'
      exact ⟨p₀, fun p j _ hp hj => hp₀ p j hp hj⟩
  -- The CRT/tensor assembly over the primes dividing `Q`.
  obtain ⟨C, hCpos, hCb⟩ :=
    BilinearAverageLqUniform_of_primePower P hd hUniform hLarge q hq hqT
  exact ⟨C, hCpos, fun Q _ f g => hCb Q f g⟩

end Work.KMTPlan.A6
