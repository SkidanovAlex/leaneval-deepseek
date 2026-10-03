import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_sieve_remainder_le
import Submission.Commons.NumberTheory.ZMod.card_Icc_filter_modEq_le_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

open Finset

/-- For each fixed `c ≥ 1` and modulus `d ≥ 1`, the number of `a ∈ ℤ` with `|a| ≤ A` and
`d ∣ a ^ 2 + c ^ 4` is at most `(2 * (A / d) + 2)` times `ρ(c², d)`, the number of roots of
`ν ^ 2 + c ^ 4 = 0` modulo `d` (each root is one residue class, which occurs at most
`2 * (A / d) + 2` times in `[-A, A]`). -/
theorem card_filter_dvd_sq_add_pow_four_le {A d c : ℕ} (hd : 0 < d) :
    ((Finset.Icc (-(A : ℤ)) (A : ℤ)).filter
        (fun a : ℤ => (d : ℤ) ∣ a ^ 2 + (c : ℤ) ^ 4)).card
      ≤ (2 * (A / d) + 2) * Submission.rho (c ^ 2) d := by
  classical
  have hne : NeZero d := ⟨hd.ne'⟩
  set S : Finset ℤ := (Finset.Icc (-(A : ℤ)) (A : ℤ)).filter
      (fun a : ℤ => (d : ℤ) ∣ a ^ 2 + (c : ℤ) ^ 4) with hS
  -- the set of roots of `ν ^ 2 + c ^ 4 = 0` in `ZMod d`
  set R : Finset (ZMod d) :=
    Finset.univ.filter (fun α : ZMod d => α ^ 2 + ((c ^ 2 : ℕ) : ZMod d) ^ 2 = 0) with hR
  have hRcard : R.card = Submission.rho (c ^ 2) d := by
    rw [hR]
    unfold Submission.rho
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  have key : S.card ≤ (2 * (A / d) + 2) * R.card := by
    refine Finset.card_le_mul_card_image_of_maps_to
      (f := fun a : ℤ => (a : ZMod d)) ?hf (2 * (A / d) + 2) ?hn
    · -- every `a ∈ S` reduces modulo `d` to a root
      intro a ha
      rw [hS, Finset.mem_filter] at ha
      obtain ⟨-, hdvd⟩ := ha
      rw [hR, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have h := (Commons.NumberTheory.ZMod.int_dvd_pow4_iff_zmod d c a).mp hdvd
      have hc : ((c ^ 2 : ℕ) : ZMod d) ^ 2 = (c : ZMod d) ^ 4 := by push_cast; ring
      rw [hc]; exact h
    · -- each residue class in `[-A, A]` has at most `2 * (A / d) + 2` elements
      intro b _
      have hsub : S.filter (fun a : ℤ => (a : ZMod d) = b)
          ⊆ (Finset.Icc (-(A : ℤ)) (A : ℤ)).filter
              (fun a : ℤ => a ≡ (b.val : ℤ) [ZMOD d]) := by
        intro a ha
        rw [Finset.mem_filter] at ha ⊢
        obtain ⟨haS, hab⟩ := ha
        rw [hS, Finset.mem_filter] at haS
        refine ⟨haS.1, ?_⟩
        have hbval : (((b.val : ℤ)) : ZMod d) = b := by
          push_cast
          exact ZMod.natCast_zmod_val b
        have heq : (a : ZMod d) = (((b.val : ℤ)) : ZMod d) := by rw [hab, hbval]
        rw [Int.modEq_iff_dvd]
        exact (ZMod.intCast_eq_intCast_iff_dvd_sub a (b.val : ℤ) d).mp heq
      calc (S.filter (fun a : ℤ => (a : ZMod d) = b)).card
          ≤ ((Finset.Icc (-(A : ℤ)) (A : ℤ)).filter
              (fun a : ℤ => a ≡ (b.val : ℤ) [ZMOD d])).card :=
            Finset.card_le_card hsub
        _ ≤ 2 * (A / d) + 2 :=
            Commons.NumberTheory.ZMod.card_Icc_filter_modEq_le_bound hd A (b.val : ℤ)
  rw [hRcard] at key
  exact key

end Commons.NumberTheory.FriedlanderIwaniec
