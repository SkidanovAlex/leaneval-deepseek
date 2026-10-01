import Mathlib
import Submission.Work.ZeroDensity.LogFree.logFreeNPInstances
import Submission.Work.LinnikAreas.DhRepel.nearSumLeZeroCountIn
import Submission.Work.LinnikAreas.DhRepel.logLogLogDivThreeLeLogDivFive
import Submission.Work.ZeroFreeTables.t23ArithFour

namespace Work.ZeroFreeTables

/-- Near-line log-free zero count for a single character: for every non-principal `χ` mod `q` and every `t` with `0 ≤ t ≤ (1/3) log log log q`, the multiplicity-weighted number of zeros `u` of `L(s,χ)` with `λ(u) = (1-Re u) log q ≤ t` and `|Im u| ≤ 10 log q` is `O((log q)^A)` for some `A < 1`, uniformly in `q` and `χ`.

ROUTE (all ingredients are axiom-clean and already available): take the *unconditional* log-free family estimate `Work.ZeroDensity.LogFree.logFreeNP_3979_5000_four : logFreeNP (3979/5000) 4`, i.e. `∃ C > 0, ∀ q ≥ 2, σ ∈ [3979/5000, 1], T ≥ 1, famCountNP q σ T ≤ C * ((q:ℝ)*T)^(4*(1-σ))` where `famCountNP q σ T = ∑ χ ∈ Finset.univ.erase 1, zeroCountIn χ σ T` (`Work.ZeroDensity.LogFree.Defs`, using `Work.ZeroDensity.zCount = Work.LinnikAreas.zeroCountIn` definitionally).  Set `σ := 1 - t/log q`, `T := 10 * log q`.  Then: (1) `Work.LinnikAreas.DhRepel.nearSumLeZeroCountIn` rewrites the `∑ᶠ` on the left as `≤ zeroCountIn χ σ T`; (2) `Finset.single_le_sum` over `Finset.univ.erase 1` (with `χ ≠ 1` and `Work.ZeroDensity.zCount_nonneg`) bounds it by `famCountNP q σ T`; (3) `(q*T)^(4t/log q) ≤ exp (8 * t) ≤ exp (8 * (log log log q)/3) = (log log q)^(8/3)`, which is `≤ (log q)^(1/2)` for large `q`.  Hence `C := C₀`, `A := 1/2` work.  Thresholds: `σ ≥ 3979/5000` follows from `t/log q ≤ (log log log q)/(3 log q) → 0`, and `T = 10 log q ≥ 1`. -/
theorem t23NearLineCountLogFree :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ A < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ t : ℝ, 0 ≤ t →
        t ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
        (∑ᶠ u : ℂ, if Work.LinnikContract.zeroMult χ u ≠ 0 ∧
            |u.im| ≤ 10 * Real.log (q : ℝ) ∧ Work.LinnikContract.lamOf q u ≤ t
          then (Work.LinnikContract.zeroMult χ u : ℝ) else 0)
          ≤ C * (Real.log (q : ℝ)) ^ A := by
  -- the unconditional log-free family estimate `logFreeNP (3979/5000) 4`
  obtain ⟨C₀, hC₀, hfam⟩ := Work.ZeroDensity.LogFree.logFreeNP_3979_5000_four
  -- the pure arithmetic input with exponent `4t/log q`
  obtain ⟨qArith, hArith⟩ :=
    Work.ZeroFreeTables.t23ArithFour C₀ (1 / 2) hC₀ (by norm_num)
  -- the threshold at which `(1/3) log log log q ≤ (1/5) log q`
  obtain ⟨X, hX⟩ := Work.LinnikAreas.DhRepel.logLogLogDivThreeLeLogDivFive
  refine ⟨1, 1 / 2, one_pos, by norm_num, by norm_num,
    max (max qArith (Nat.ceil X)) 2, ?_⟩
  intro q hq _inst χ hχ t ht0 htle
  have hqArith : qArith ≤ q :=
    le_trans (le_trans (le_max_left qArith (Nat.ceil X))
      (le_max_left (max qArith (Nat.ceil X)) 2)) hq
  have hqX : Nat.ceil X ≤ q :=
    le_trans (le_trans (le_max_right qArith (Nat.ceil X))
      (le_max_left (max qArith (Nat.ceil X)) 2)) hq
  have hq2 : 2 ≤ q := le_trans (le_max_right (max qArith (Nat.ceil X)) 2) hq
  have hXq : X ≤ (q : ℝ) := le_trans (Nat.le_ceil X) (by exact_mod_cast hqX)
  have hlogpos : 0 < Real.log (q : ℝ) := by
    have h1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
    exact Real.log_pos h1
  -- `T = 10 log q ≥ 1`
  have hT1 : 1 ≤ 10 * Real.log (q : ℝ) := by
    have hlog2 : (1 / 10 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlog2q : Real.log 2 ≤ Real.log (q : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hq2)
    linarith
  -- the exponent threshold `t ≤ log log log q / 3 ≤ log q / 5`, and `1/5 ≤ 1021/5000`
  have hσ0 : (3979 / 5000 : ℝ) ≤ 1 - t / Real.log (q : ℝ) := by
    have hb : Real.log (Real.log (Real.log (q : ℝ))) / 3 ≤ Real.log (q : ℝ) / 5 := hX _ hXq
    have h5 : t ≤ Real.log (q : ℝ) / 5 := le_trans htle hb
    have h : t / Real.log (q : ℝ) ≤ 1021 / 5000 := by
      rw [div_le_iff₀ hlogpos]; linarith
    linarith
  have hσ1 : 1 - t / Real.log (q : ℝ) ≤ 1 := by
    have : 0 ≤ t / Real.log (q : ℝ) := div_nonneg ht0 hlogpos.le
    linarith
  -- near sum ⟶ rectangle count ⟶ family count ⟶ `(qT)^{4(1-σ)}` ⟶ `(log q)^{1/2}`
  calc (∑ᶠ u : ℂ, if Work.LinnikContract.zeroMult χ u ≠ 0 ∧
          |u.im| ≤ 10 * Real.log (q : ℝ) ∧ Work.LinnikContract.lamOf q u ≤ t
        then (Work.LinnikContract.zeroMult χ u : ℝ) else 0)
      ≤ Work.LinnikAreas.zeroCountIn χ (1 - t / Real.log (q : ℝ)) (10 * Real.log (q : ℝ)) :=
        Work.LinnikAreas.DhRepel.nearSumLeZeroCountIn hq2 χ t
    _ ≤ Work.ZeroDensity.LogFree.famCountNP q (1 - t / Real.log (q : ℝ))
          (10 * Real.log (q : ℝ)) := by
        have h := Finset.single_le_sum
          (f := fun χ' : DirichletCharacter ℂ q =>
            Work.ZeroDensity.zCount χ' (1 - t / Real.log (q : ℝ)) (10 * Real.log (q : ℝ)))
          (fun i _ => Work.ZeroDensity.zCount_nonneg i _ _)
          (Finset.mem_erase.mpr ⟨hχ, Finset.mem_univ χ⟩)
        simpa only [Work.ZeroDensity.LogFree.famCountNP, Work.ZeroDensity.zCount] using h
    _ ≤ C₀ * ((q : ℝ) * (10 * Real.log (q : ℝ))) ^
          (4 * (1 - (1 - t / Real.log (q : ℝ)))) :=
        hfam q hq2 (1 - t / Real.log (q : ℝ)) (10 * Real.log (q : ℝ)) hσ0 hσ1 hT1
    _ = C₀ * ((q : ℝ) * (10 * Real.log (q : ℝ))) ^ (4 * t / Real.log (q : ℝ)) := by
        have hexp : 4 * (1 - (1 - t / Real.log (q : ℝ))) = 4 * t / Real.log (q : ℝ) := by
          have h1 : 1 - (1 - t / Real.log (q : ℝ)) = t / Real.log (q : ℝ) := by ring
          rw [h1, mul_div_assoc]
        rw [hexp]
    _ ≤ (Real.log (q : ℝ)) ^ (1 / 2 : ℝ) := hArith q hqArith t ht0 htle
    _ = 1 * (Real.log (q : ℝ)) ^ (1 / 2 : ℝ) := (one_mul _).symm

end Work.ZeroFreeTables
