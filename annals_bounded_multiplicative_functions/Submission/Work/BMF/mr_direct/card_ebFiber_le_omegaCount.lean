import Mathlib
import Submission.Work.BMF.mr_direct.ebound_defs
import Submission.Work.BMF.mr_direct.buchstab_aux
import Submission.Work.BMF.mr_direct.card_primeSet_filter_dvd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open Finset

/-- The fibre of `ebnn` over `n` injects into the primes of `primeSet P Q` dividing `n`
(by sending `(p, m)` to `p`), hence has cardinality at most `ω(n;P,Q)`. -/
theorem card_ebFiber_le_omegaCount (K P Q X : ℝ) (hX : 1 ≤ X) (n : ℕ) :
    (Work.BMF.mr_direct.ebFiber K P Q X n).card ≤ Work.BMF.mrDirect.omegaCount P Q n := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    have hempty : Work.BMF.mr_direct.ebFiber K P Q X 0 = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro i hi
      rw [Work.BMF.mr_direct.ebFiber, Finset.mem_filter] at hi
      obtain ⟨hiB, hie⟩ := hi
      rw [Work.BMF.mrDirect.pSetB, Finset.mem_sigma] at hiB
      obtain ⟨hprimemem, hi2⟩ := hiB
      rw [Work.BMF.mrDirect.primeSet, Finset.mem_filter] at hprimemem
      have hprime : i.1.Prime := hprimemem.2
      have hi2win : i.2 ∈ Work.BMF.mrDirect.winIdx K X (Work.BMF.mrDirect.jdex K i.1) :=
        (Finset.mem_filter.mp hi2).1
      rw [Work.BMF.mr_direct.ebnn] at hie
      have hm0 : i.2 = 0 := by
        rcases Nat.mul_eq_zero.mp hie with h | h
        · exact absurd h hprime.ne_zero
        · exact h
      rw [Work.BMF.mrDirect.winIdx, Work.BMF.natIcc, Finset.mem_Icc] at hi2win
      have ha_pos : 0 < X * Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K) :=
        mul_pos (by linarith) (Real.exp_pos _)
      have hceil : 1 ≤ ⌈X * Real.exp (-(((Work.BMF.mrDirect.jdex K i.1 : ℕ) : ℝ) + 1) / K)⌉₊ :=
        Nat.one_le_ceil_iff.mpr ha_pos
      omega
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    rw [← card_primeSet_filter_dvd (P := P) (Q := Q) hn1]
    have hinj : Set.InjOn (fun i : Sigma (fun _ : ℕ => ℕ) => i.1)
        ↑(Work.BMF.mr_direct.ebFiber K P Q X n) := by
      intro i hi j hj hij
      simp only [Finset.mem_coe, Work.BMF.mr_direct.ebFiber, Finset.mem_filter] at hi hj
      obtain ⟨hiB, hie⟩ := hi
      obtain ⟨hjB, hje⟩ := hj
      have hp : i.1 ∈ Work.BMF.mrDirect.primeSet P Q := (Finset.mem_sigma.mp hiB).1
      have hpprime : i.1.Prime := by
        rw [Work.BMF.mrDirect.primeSet, Finset.mem_filter] at hp
        exact hp.2
      have hp0 : 0 < i.1 := hpprime.pos
      rw [Work.BMF.mr_direct.ebnn] at hie hje
      rcases i with ⟨p, m⟩
      rcases j with ⟨p', m'⟩
      simp only at hij hie hje hpprime hp0
      subst hij
      have hmm : m = m' := Nat.mul_left_cancel hp0 (by rw [hie, hje])
      subst hmm
      rfl
    have hsub : (Work.BMF.mr_direct.ebFiber K P Q X n).image (fun i : Sigma (fun _ : ℕ => ℕ) => i.1)
        ⊆ (Work.BMF.mrDirect.primeSet P Q).filter (fun p => p ∣ n) := by
      intro p hp
      rw [Finset.mem_image] at hp
      obtain ⟨i, hi, rfl⟩ := hp
      rw [Work.BMF.mr_direct.ebFiber, Finset.mem_filter] at hi
      obtain ⟨hiB, hie⟩ := hi
      rw [Finset.mem_filter]
      refine ⟨(Finset.mem_sigma.mp hiB).1, ?_⟩
      rw [Work.BMF.mr_direct.ebnn] at hie
      rw [← hie]
      exact dvd_mul_right i.1 i.2
    calc (Work.BMF.mr_direct.ebFiber K P Q X n).card
        = ((Work.BMF.mr_direct.ebFiber K P Q X n).image
            (fun i : Sigma (fun _ : ℕ => ℕ) => i.1)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ ((Work.BMF.mrDirect.primeSet P Q).filter (fun p => p ∣ n)).card :=
          Finset.card_le_card hsub

end Work.BMF.mr_direct
