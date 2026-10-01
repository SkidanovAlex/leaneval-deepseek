import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.burgess_moment_prime
import Submission.Commons.NumberTheory.DirichletCharacter.burgess_moment_squarefree_r2
import Submission.Commons.NumberTheory.DirichletCharacter.burgess_moment_r3_singleton_cubefree_sum
import Submission.Commons.Combinatorics.Counting.card_functions_fin_six_small_range
import Submission.Work.LinnikBurgess.DdBits
import Submission.Work.LinnikBurgess.nosingleton_sum_bound
import Submission.Work.ZeroFreeTables.P9F.Chain.ssa

/-!
# The `r = 3` sixth-moment bound modulo a modulus divisible by a cube

Target (`Work.LinnikBurgess.burgess_r3_noncubefree`): for every `ε > 0` there is `C` such that for
every `q` divisible by a cube, every primitive non-trivial `χ` modulo `q` and every `H` with
`H^6 ≤ q`,

`∑_{m < q} ‖∑_{h ∈ (m, m+H]} χ h‖^6 ≤ C q^ε (q H^3 + H^6 √q)`.

This is Burgess 1986, Theorem B (Heath-Brown, *Burgess's bounds for character sums*, Lemma 2 (iii)).

## The route

* `moment_eq_pairSum`: `∑_m ‖S_m‖^6 = ‖∑_{f,g} corr6 q χ f g‖` (the exact sixth-moment
  expansion, `sum_norm_eq_norm_sum` + `Z_eq'` + `corr6_eq_Tgq`).
* `pairSum_split`: split the pair sum into *singleton* pairs (some shift occurs exactly once) and
  the rest.
* The non-singleton part is `≤ 729 q H^3` (`nosingleton_sum_bound`).
* The singleton part is the analytic core: `singleton_sum_nonCubefree`.

## The analytic core

`corr6 q χ f g = ∏_{p^e ‖ q} S_{p^e}(f,g)` by CRT (`split_sum6`), and each local sum `S_{p^e}` is
controlled by `charCorrelation6_primePow_local` *except* on the pairs carrying a **doubly
degenerate** critical class: a class `r : ZMod p` at which all six shifts are units, the two
triples of inverses agree to first *and* second order mod `p`, and `p^2` divides the `p`-adic
criticality defect `D_1(r) = ∑_l (r+a_l)^{-1} - ∑_l (r+b_l)^{-1}`.

WARNING (established by a delegated attempt, `dd_levelSum_exact`, which was found **FALSE and
deleted**): the level sum at a doubly degenerate class is **not** governed by the single valuation
`v_p(D_1(r))` alone.  Counterexample (p = 7, e = 10, j = 2): take `A`, `C` the roots mod `7^10` of
`x³ − 147x² − 21x − 1` and `t³ + 147t² + 21t + 1`; then `∑A − ∑C ≡ 0 (mod 7²)` but `≢ 0 (mod 7³)`,
`∑A ≡ ∑C` and `∑A² ≡ ∑C² (mod 7)`, `r = 0`, `a_l = A_l^{-1}`, `b_l = C_l^{-1}` — all hypotheses of
the naive graded bound `|level sum| ≤ 2 p^{((e-2)+j)/2}` hold, but the level sum exceeds it.  The
`p`-adic stationary-phase expansion needs the valuations of the *whole* family
`D_k(r) = ∑_l (r+a_l)^{-k} - ∑_l (r+b_l)^{-k}`, `k = 1, 2, 3, …`, not only `k = 1`; the level sum
is large exactly when the first several `D_k` are all highly divisible by `p`, and such pairs are
correspondingly rare.  A correct local statement must be graded by that full data, and the
counting of the pairs must be graded the same way.

The companion counting `dd_incidence_count` (singleton pairs carrying a doubly degenerate class
modulo `p^j` are `≤ C · p^ε · (H^6/p^j + H^3)`) is independent of this defect and stands on its own;
an earlier version with `p^{j+1}` in place of `p^j` was also refuted by its prover (`p^j` is the
correct exponent, the `H^3` is the exact-degeneracy term).
-/

open Finset
open scoped BigOperators

namespace Work.P9Chain

open Work.LinnikBurgess

open Commons.NumberTheory.DirichletCharacter (Tgq Z_eq' sum_norm_eq_norm_sum bmr3sc_Tgq_three_eq_corr)

/-- For a primitive non-trivial `χ` the correlation sum `corr6` is `Tgq H 3 χ f g`. -/
lemma corr6_eq_Tgq {q : ℕ} [NeZero q] {H : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (f g : Fin 3 → Fin H) : corr6 q χ f g = Tgq H 3 χ f g := by
  have hm : 2 ≤ orderOf χ := by
    have h1 : orderOf χ ≠ 1 := fun h => hχ (orderOf_eq_one_iff.mp h)
    have h2 : 1 ≤ orderOf χ := orderOf_pos χ
    omega
  rw [bmr3sc_Tgq_three_eq_corr (q := q) H χ hm f g]
  rfl

/-- The exact sixth-moment expansion: the mean sixth power of the interval sums is the norm of the
sum of the cubic correlations over all pairs of triples of shifts. -/
theorem moment_eq_pairSum {q : ℕ} [NeZero q] {H : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) :
    (∑ m ∈ Finset.range q, ‖∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod q)‖ ^ 6)
      = ‖∑ f : Fin 3 → Fin H, ∑ g : Fin 3 → Fin H, corr6 q χ f g‖ := by
  rw [show (6 : ℕ) = 2 * 3 from rfl,
    sum_norm_eq_norm_sum (p := q)
      (S := fun m => ∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod q)) 3]
  rw [Z_eq' (q := q) H 3 χ hχ]
  congr 1
  exact Finset.sum_congr rfl (fun f _ =>
    Finset.sum_congr rfl (fun g _ => (corr6_eq_Tgq χ hχ f g).symm))

/-- Splitting the pair sum into the singleton and the non-singleton part. -/
lemma pairSum_split {q : ℕ} [NeZero q] {H : ℕ} (χ : DirichletCharacter ℂ q) :
    (∑ f : Fin 3 → Fin H, ∑ g : Fin 3 → Fin H, corr6 q χ f g)
      = (∑ f : Fin 3 → Fin H, ∑ g : Fin 3 → Fin H,
            (if IsSingleton6 (f, g) then corr6 q χ f g else 0))
        + (∑ f : Fin 3 → Fin H, ∑ g : Fin 3 → Fin H,
            (if IsSingleton6 (f, g) then 0 else corr6 q χ f g)) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  by_cases h : IsSingleton6 (f, g) <;> simp [h]

/-- The singleton part as a sum of norms. -/
lemma singleton_sum_norm {q : ℕ} [NeZero q] {H : ℕ} (χ : DirichletCharacter ℂ q) :
    ‖∑ f : Fin 3 → Fin H, ∑ g : Fin 3 → Fin H,
        (if IsSingleton6 (f, g) then corr6 q χ f g else 0)‖
      ≤ ∑ f : Fin 3 → Fin H, ∑ g : Fin 3 → Fin H,
          (if IsSingleton6 (f, g) then ‖corr6 q χ f g‖ else 0) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun f _ => ?_))
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun g _ => ?_))
  by_cases h : IsSingleton6 (f, g)
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, norm_zero]

/-- **The reduction.**  Given the singleton-pair bound, the sixth-moment bound for moduli divisible
by a cube follows by splitting the pair sum. -/
theorem burgess_r3_noncubefree_of_singleton {ε : ℝ} (hε : 0 < ε)
    (hsing : ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q], (∃ p : ℕ, p.Prime ∧ p ^ 3 ∣ q) →
      ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ H : ℕ, H ^ 6 ≤ q →
        ∑ f : Fin 3 → Fin H, ∑ g : Fin 3 → Fin H,
          (if IsSingleton6 (f, g) then ‖corr6 q χ f g‖ else 0)
        ≤ C * (q : ℝ) ^ ε * ((q : ℝ) * (H : ℝ) ^ 3 + (H : ℝ) ^ 6 * Real.sqrt (q : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q], (∃ p : ℕ, p.Prime ∧ p ^ 3 ∣ q) →
      ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ H : ℕ, H ^ 6 ≤ q →
        ∑ m ∈ Finset.range q, ‖∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod q)‖ ^ 6
          ≤ C * (q : ℝ) ^ ε * ((q : ℝ) * (H : ℝ) ^ 3 + (H : ℝ) ^ 6 * Real.sqrt (q : ℝ)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := hsing
  refine ⟨C₁ + 729 + 1, by positivity, ?_⟩
  intro q _ hcube χ hprim hne H hH
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqe : (1 : ℝ) ≤ (q : ℝ) ^ ε := Real.one_le_rpow hqR hε.le
  have hqe0 : (0 : ℝ) ≤ (q : ℝ) ^ ε := Real.rpow_nonneg (by positivity) _
  set X : ℝ := (q : ℝ) * (H : ℝ) ^ 3 + (H : ℝ) ^ 6 * Real.sqrt (q : ℝ) with hX
  have hX0 : (0 : ℝ) ≤ X := by rw [hX]; positivity
  have hH3 : (0 : ℝ) ≤ (H : ℝ) ^ 3 := by positivity
  rw [moment_eq_pairSum χ hne, pairSum_split χ]
  refine (norm_add_le _ _).trans ?_
  have hA : ‖∑ f : Fin 3 → Fin H, ∑ g : Fin 3 → Fin H,
        (if IsSingleton6 (f, g) then corr6 q χ f g else 0)‖
      ≤ ∑ f : Fin 3 → Fin H, ∑ g : Fin 3 → Fin H,
          (if IsSingleton6 (f, g) then ‖corr6 q χ f g‖ else 0) := singleton_sum_norm χ
  have hB := nosingleton_sum_bound (q := q) H χ
  have hB' : 729 * ((H : ℝ) ^ 3 * (q : ℝ)) ≤ 729 * ((q : ℝ) ^ ε * X) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    calc (H : ℝ) ^ 3 * (q : ℝ) = (q : ℝ) * (H : ℝ) ^ 3 := by ring
      _ ≤ (q : ℝ) ^ ε * ((q : ℝ) * (H : ℝ) ^ 3) := le_mul_of_one_le_left (by positivity) hqe
      _ ≤ (q : ℝ) ^ ε * X := by
          refine mul_le_mul_of_nonneg_left ?_ hqe0
          rw [hX]; linarith [show (0 : ℝ) ≤ (H : ℝ) ^ 6 * Real.sqrt (q : ℝ) by positivity]
  have hfin := add_le_add (hA.trans (hC₁ hcube χ hprim hne H hH)) (hB.trans hB')
  refine hfin.trans ?_
  have hY0 : (0 : ℝ) ≤ (q : ℝ) ^ ε * X := mul_nonneg hqe0 hX0
  calc (C₁ * (q : ℝ) ^ ε) * X + 729 * ((q : ℝ) ^ ε * X)
      = (C₁ + 729) * ((q : ℝ) ^ ε * X) := by ring
    _ ≤ (C₁ + 729 + 1) * ((q : ℝ) ^ ε * X) := by nlinarith [hY0]
    _ = (C₁ + 729 + 1) * (q : ℝ) ^ ε * X := by ring

/-- **The `r = 3` sixth moment bound for moduli divisible by a cube** (Burgess 1986, Theorem B;
Heath-Brown, *Burgess's bounds for character sums*, Lemma 2 (iii), and Lemma 1 (iii) of the
Burgess 1986 paper). -/
theorem burgess_r3_noncubefree {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q], (∃ p : ℕ, p.Prime ∧ p ^ 3 ∣ q) →
      ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ H : ℕ, H ^ 6 ≤ q →
        ∑ m ∈ Finset.range q, ‖∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod q)‖ ^ 6
          ≤ C * (q : ℝ) ^ ε * ((q : ℝ) * (H : ℝ) ^ 3 + (H : ℝ) ^ 6 * Real.sqrt (q : ℝ)) := by
  obtain ⟨C, hC, hall⟩ := Work.P9Chain.singleton_sum_all hε
  exact burgess_r3_noncubefree_of_singleton hε
    ⟨C, hC, fun _ χ hχ h1 H _ => hall χ hχ h1 H⟩

end Work.P9Chain
