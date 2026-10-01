import Mathlib
import Submission.Work.LinnikAreas.frame_count_own
import Submission.Work.ZeroFreeTables.P9F.Chain.ssa
import Submission.Work.ZeroFreeTables.P9F.Chain.burg
import Submission.Work.LinnikAreas.u8own.localFactor_bound_small
import Submission.Work.LinnikBurgess.local_prime_powOne_bound
import Submission.Work.LinnikBurgess.localFactor_bound_ge5
import Submission.Work.LinnikBurgess.corr6_norm_le_prod_local
import Submission.Work.LinnikBurgess.sqrtGcdW_prod_le_sqfreePart
import Submission.Work.LinnikBurgess.sqrt_prod_factorization
import Submission.Work.LinnikBurgess.divisors_card_pow_le
import Submission.Work.LinnikBurgess.sqfreePart_frame_hyp
import Submission.Work.LinnikBurgess.divisor_bounds_high
import Submission.Work.LinnikBurgess.sqrt_mul_sum_le

/-!
# The `r = 3` sixth-moment bound, assembled with MY frame count

The parametric assembly `Work.P9Chain.singleton_sum_all_aux` is instantiated here with

* the nine sorry-free `Work.LinnikBurgess` inputs,
* my own `Work.LinnikAreas.frame_count_own` (Theorem F) for the frame count, so that this chain
  does **not** depend on the sibling `Work.LinnikBurgess.sumI_le` / `frame_count`,
* **my own** `Work.LinnikAreas.u8own.localFactor_bound_small` (U8, `p ≤ 3`) in place of the
  sibling's still-`sorry`ed `Work.LinnikBurgess.localFactor_bound_small`.
-/

open scoped BigOperators
open Work.LinnikBurgess

namespace Work.LinnikAreas

/-- **The singleton-pair sixth-moment bound**, with my frame count. -/
theorem singleton_sum_all_own2 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q], ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      χ ≠ 1 → ∀ H : ℕ,
        ∑ f : Fin 3 → Fin H, ∑ g : Fin 3 → Fin H,
          (if IsSingleton6 (f, g) then ‖corr6 q χ f g‖ else 0)
        ≤ C * (q : ℝ) ^ ε * ((q : ℝ) * (H : ℝ) ^ 3 + (H : ℝ) ^ 6 * Real.sqrt (q : ℝ)) :=
  Work.P9Chain.singleton_sum_all_aux
    (fun p _ χ hχ a b i => local_prime_powOne_bound χ hχ a b i)
    (fun {p e} _ hp5 he χ hχ a b i hi => localFactor_bound_ge5 hp5 he χ hχ a b i hi)
    (fun {p e} _ hp3 he χ hχ a b i hi =>
      Work.LinnikAreas.u8own.localFactor_bound_small hp3 he χ hχ a b i hi)
    (fun {H} i {m d g} hm hmd hmg hd hg => frame_count_own i hm hmd hmg hd hg)
    (fun q i v => sqrtGcdW_prod_le_sqfreePart q i v)
    (fun {q} hq => sqrt_prod_factorization hq)
    (fun {q d g} hq h => divisors_card_pow_le hq h)
    (fun {q} hq σ hσ => sqfreePart_frame_hyp hq σ hσ)
    (fun {q} hq {d} hd => divisor_bounds_high hq hd)
    (fun {q H} => sqrt_mul_sum_le (q := q) (H := H))
    hε

/-- **Burgess's `r = 3` sixth-moment bound for moduli divisible by a cube.** -/
theorem burgess_r3_noncubefree_own2 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q], (∃ p : ℕ, p.Prime ∧ p ^ 3 ∣ q) →
      ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ H : ℕ, H ^ 6 ≤ q →
        ∑ m ∈ Finset.range q, ‖∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod q)‖ ^ 6
          ≤ C * (q : ℝ) ^ ε * ((q : ℝ) * (H : ℝ) ^ 3 + (H : ℝ) ^ 6 * Real.sqrt (q : ℝ)) := by
  obtain ⟨C, hC, hall⟩ := singleton_sum_all_own2 hε
  exact Work.P9Chain.burgess_r3_noncubefree_of_singleton hε
    ⟨C, hC, fun _ χ hχ h1 H _ => hall χ hχ h1 H⟩

end Work.LinnikAreas
