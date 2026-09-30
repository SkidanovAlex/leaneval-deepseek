import Mathlib
import Submission.Work.BMF.mr_direct.ep2R_defs
import Submission.Work.BMF.mr_direct.ep2_integral_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open Finset

/-- The fibre of `freq` over `n` inside `pSetER P Q A B` injects into the primes of
`primeSet P Q` dividing `n` (by sending `(p, m)` to `p`): if `p = p'` and `m·p = m'·p'`
then `m = m'`.  Hence the fibre has cardinality at most `ω(n;P,Q)`. -/
lemma ep2R_fiber_card_le (P Q A B : ℝ) (hA : 1 ≤ A) (n : ℕ) :
    ((Work.BMF.mr_direct.pSetER P Q A B).filter
        (fun x => Work.BMF.mr_direct.freq x = n)).card
      ≤ Work.BMF.mrDirect.omegaCount P Q n := by
  by_cases hne : ((Work.BMF.mr_direct.pSetER P Q A B).filter
      (fun x => Work.BMF.mr_direct.freq x = n)).Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    have hx0' : x0 ∈ Work.BMF.mr_direct.pSetER P Q A B := (Finset.mem_filter.mp hx0).1
    have hf0 : Work.BMF.mr_direct.freq x0 = n := (Finset.mem_filter.mp hx0).2
    have hn1 : 1 ≤ n := by
      have h2 : 1 ≤ x0.2 := one_le_sndR hA hx0'
      have h1 : 1 ≤ x0.1 := (primeSet_bounds (mem_pSetER_fst hx0')).1.one_le
      have : 0 < x0.2 * x0.1 := Nat.mul_pos (by omega) (by omega)
      rw [← hf0, Work.BMF.mr_direct.freq]
      omega
    have hmap : ∀ x ∈ (Work.BMF.mr_direct.pSetER P Q A B).filter
        (fun x => Work.BMF.mr_direct.freq x = n),
        x.1 ∈ (Work.BMF.mrDirect.primeSet P Q).filter (fun p => p ∣ n) := by
      intro x hx
      rw [Finset.mem_filter]
      refine ⟨mem_pSetER_fst (Finset.mem_filter.mp hx).1, ?_⟩
      have hdvd : x.1 ∣ x.2 := mem_pSetER_dvd (Finset.mem_filter.mp hx).1
      have hfx : Work.BMF.mr_direct.freq x = n := (Finset.mem_filter.mp hx).2
      have : x.1 ∣ x.2 * x.1 := dvd_mul_of_dvd_left hdvd x.1
      rwa [← hfx, Work.BMF.mr_direct.freq]
    have hinj : Set.InjOn (fun x : Σ _ : ℕ, ℕ => x.1)
        ↑((Work.BMF.mr_direct.pSetER P Q A B).filter
          (fun x => Work.BMF.mr_direct.freq x = n)) := by
      intro x hx y hy hxy
      change x.1 = y.1 at hxy
      have hx' := Finset.mem_filter.mp hx
      have hy' := Finset.mem_filter.mp hy
      have hy1 : 0 < y.1 := (primeSet_bounds (mem_pSetER_fst hy'.1)).1.pos
      have hfreq : x.2 * x.1 = y.2 * y.1 := by
        have : Work.BMF.mr_direct.freq x = Work.BMF.mr_direct.freq y := by
          rw [hx'.2, hy'.2]
        simpa only [Work.BMF.mr_direct.freq] using this
      have hthis : x.2 = y.2 := by
        rw [hxy] at hfreq
        exact Nat.mul_right_cancel hy1 hfreq
      exact Sigma.ext hxy (heq_of_eq hthis)
    have hcard := Finset.card_le_card_of_injOn (fun x : Σ _ : ℕ, ℕ => x.1) hmap hinj
    rw [Work.BMF.mr_direct.card_primeSet_filter_dvd hn1] at hcard
    exact hcard
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le _

end Work.BMF.mr_direct
