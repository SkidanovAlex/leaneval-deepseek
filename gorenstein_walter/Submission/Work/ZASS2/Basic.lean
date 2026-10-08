/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area ZASS2: the two easy leaves of step Z6

Both leaf `Prop`s below are proved from the already delivered area `ZASS`:

* `Work.ZASS2.zassCyclicOfComm : Work.GW2.ZassCyclicOfCommProp` -- an abelian two-point
  stabilizer is cyclic.  From `Z2`/`Z3` (`Work.ZASS.exists_unipotent_structure`) the
  two-point stabilizer `H = G_{ab}` is the Frobenius complement of `U`, so
  `Work.ZASS.isCyclic_of_isMulCommutative_of_free` (Isaacs Cor 6.17) applies.

* `Work.ZASS2.zassGoodSwap : Work.GW2.ZassGoodSwapProp` -- the choice of the involution `s`
  interchanging `∞` and `0`: `Work.ZASS.zassInvolutionSwapProp` (HB 1.7b/c) always gives
  one, and `Work.ZASS.exists_swap_two_fixed` (HB 1.8b) gives one with exactly two fixed
  points when `d = (q-1)/2` is even.
-/
import Mathlib
import Submission.Work.ZASS.Leaf9
import Submission.Work.ZASS.Z5
import Submission.Work.ZASS.Frobenius
import Submission.Work.ZASS.zassInvolutionSwapProp
import Submission.Work.ZASS.exists_swap_two_fixed

namespace Work.ZASS2

open Work.GW2
open Work.Zassenhaus (borel pairStab)

/-- **`ZassCyclicOfCommProp`.**  An abelian two-point stabilizer `G_{ab}` is cyclic: it is an
abelian Frobenius complement (`U ⋊ G_{ab}`, Z2/Z3), and abelian Frobenius complements are
cyclic (`Work.ZASS.isCyclic_of_isMulCommutative_of_free`, Isaacs Cor 6.17). -/
theorem zassCyclicOfComm : ZassCyclicOfCommProp := by
  intro G X _ _ _ _ p k _ hp hq h a b hab hcomm
  obtain ⟨U, hUB, hcardU, hN, _hdec, hfree, _hequiv, _hcommU, _hexp⟩ :=
    Work.ZASS.exists_unipotent_structure (p := p) (k := k) hp hq h (inf := a) (zero := b) hab
  have hnt : Nontrivial U := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcardU]
    have := hq
    omega
  have hcommH : IsMulCommutative ↥(pairStab G a b) := by
    rw [Work.GW2.pairStab_eq_inf_stabilizer]
    exact hcomm
  have hcyc := Work.ZASS.isCyclic_of_isMulCommutative_of_free (U := U) (inf := a) (zero := b)
    hUB hN hfree hcommH hnt
  rw [← Work.GW2.pairStab_eq_inf_stabilizer]
  exact hcyc

/-- **`ZassGoodSwapProp`.**  There is an involution interchanging two distinct points `∞ ≠ 0`,
and if `d = (q-1)/2` is even one with (at least) one fixed point.  The first part is HB 1.7b/c
(`Work.ZASS.zassInvolutionSwapProp`), the refinement HB 1.8b
(`Work.ZASS.exists_swap_two_fixed`). -/
theorem zassGoodSwap : ZassGoodSwapProp := by
  intro G X _ _ _ _ p k _ hp hq h inf zero hne
  have hoddq : Odd (p ^ k) := hp.pow
  rcases Nat.even_or_odd ((p ^ k - 1) / 2) with hd | hd
  · obtain ⟨s, hs2, hsi, hsz, hfix⟩ :=
      Work.ZASS.exists_swap_two_fixed (q := p ^ k) h hoddq hd hne
    refine ⟨s, hs2, hsi, hsz, fun _ => ?_⟩
    obtain ⟨x, y, _hxy, hset⟩ := Set.ncard_eq_two.mp hfix
    refine ⟨x, ?_⟩
    have hx : x ∈ ({x : X | s • x = x} : Set X) := by rw [hset]; simp
    exact hx
  · obtain ⟨s, hs2, hsi, hsz⟩ :=
      Work.ZASS.zassInvolutionSwap_aux G X (p ^ k) hoddq h inf zero hne
    exact ⟨s, hs2, hsi, hsz, fun hc => absurd hc (Nat.not_even_iff_odd.mpr hd)⟩

end Work.ZASS2
