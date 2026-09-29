import Mathlib
import Submission.CDT.Lcm2Bound
import Submission.CDT.IntegratedLcm
import Submission.Work.Holonomy3.defs
import Submission.Work.Holonomy3.log_lcm_cap_le

/-!
# Definitions for the τ♯ (denominator surplus) estimate

The extras that the `n^{e_i}` factors of the denominator types `(den type int)` add to the
denominators of a coefficient of the auxiliary series are cleared position by position by the
window lcm `[n_j - D, n_j]` (the `Q`-monomials have partial degrees `< D`, so the coefficient
index `n_j - k_j` lies in that window).  This module isolates the two arithmetic ingredients:

* `winLcm n D` — the lcm of the window `[n-D, n]`, with `0` removed;
* `ppFac l n` — the extra contribution of the *proper* prime powers `p^j`, `j ≥ 2`, below `n`
  and above the threshold `l`;
* `winLcm_dvd_split` — the window lcm divides `[1,…,l] · L^{≥l} · ppFac`, where `L^{≥l}` is the
  paper's product of the primes `p > l` having a multiple in the window (Lemma `lcm-2`).
-/

namespace Work.Holonomy3

open Submission.CDTPlan
open scoped BigOperators

/-- The lcm of the window `[n-D, n]` of integers, with `0` removed (so that it is positive). -/
noncomputable def winLcm (n D : ℕ) : ℕ := ((Finset.Icc (n - D) n).erase 0).lcm (fun m => m)

/-- The product of the proper prime powers `p^j` (`j ≥ 2`, `p` prime) with `l < p^j ≤ n`: the
part of the "prime power" denominators that the product `[1,…,l]·L^{≥l}` of Lemma `lcm-2` misses. -/
noncomputable def ppFac (l n : ℕ) : ℕ :=
  ∏ j ∈ Finset.Icc 2 n,
    ∏ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ l < p ^ j ∧ p ^ j ≤ n), p

lemma winLcm_pos (n D : ℕ) : 0 < winLcm n D :=
  Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun _ hm => (Finset.mem_erase.mp hm).1))

lemma ppFac_pos (l n : ℕ) : 0 < ppFac l n := by
  refine Finset.prod_pos (fun j _ => Finset.prod_pos (fun p hp => ?_))
  exact (Finset.mem_filter.mp hp).2.1.pos

lemma winLcm_mono (n D D' : ℕ) (h : D ≤ D') : winLcm n D ≤ winLcm n D' := by
  rw [winLcm, winLcm]
  refine Nat.le_of_dvd (Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr
    (fun _ hm => (Finset.mem_erase.mp hm).1))) (Finset.lcm_mono ?_)
  intro m hm
  rw [Finset.mem_erase] at hm ⊢
  refine ⟨hm.1, ?_⟩
  rw [Finset.mem_Icc] at hm ⊢
  exact ⟨le_trans (Nat.sub_le_sub_left h n) hm.2.1, hm.2.2⟩

end Work.Holonomy3
