/-
# `Work.FIArea1.boxZ_dvd_count_le`

The lattice count behind *FI* §5: for the integer box `boxZ n = [-n,n]²`, the number of
points `z` of the box with `d ∣ |z|²` is at most `Nsol d` times the square of the number of
integers of `[-n,n]` in a fixed residue class mod `d`.

The proof is the elementary one: the reduction map `z ↦ (z.1, z.2) : (ZMod d)²` sends the box
into the `Nsol d` residue classes solving `r² + s² = 0`, and each fibre is contained in a
product of two one-dimensional residue classes, each of which meets `[-n,n]` in at most
`2n/d + 2` points.
-/
import Mathlib
import Submission.Work.FIArea1.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea1

open Finset

/-- One-dimensional residue-class count: an interval `[0,N]` meets a fixed class mod `d`
in at most `N/d + 1` points. -/
lemma nat_card_mod_le (N d t : ℕ) (hd : 0 < d) :
    ((Finset.Icc 0 N).filter (fun y => y % d = t)).card ≤ N / d + 1 := by
  have hinj : Set.InjOn (fun y : ℕ => y / d)
      ↑((Finset.Icc 0 N).filter (fun y => y % d = t)) := by
    intro y1 hy1 y2 hy2 h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hy1 hy2
    change y1 / d = y2 / d at h
    have e1 : d * (y2 / d) + t = y1 := by
      calc d * (y2 / d) + t = d * (y1 / d) + y1 % d := by rw [h, hy1.2]
        _ = y1 := Nat.div_add_mod y1 d
    have e2 : d * (y2 / d) + t = y2 := by
      calc d * (y2 / d) + t = d * (y2 / d) + y2 % d := by rw [hy2.2]
        _ = y2 := Nat.div_add_mod y2 d
    exact e1.symm.trans e2
  calc ((Finset.Icc 0 N).filter (fun y => y % d = t)).card
      ≤ (Finset.Icc 0 (N / d)).card :=
        Finset.card_le_card_of_injOn (fun y => y / d)
          (fun y hy => by
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hy ⊢
            exact ⟨Nat.zero_le _, Nat.div_le_div_right hy.1.2⟩)
          hinj
    _ = N / d + 1 := by simp

/-- Residue-class count in a symmetric interval: for `c : ZMod d` the interval
`[-n,n] ⊆ ℤ` meets the class `c` in at most `2n/d + 2` points.  (The shift `x ↦ x + n`
transports this to the one-dimensional count `nat_card_mod_le`.) -/
lemma int_card_mod_le (n d : ℕ) (hd : 0 < d) (c : ZMod d) :
    ((Finset.Icc (-(n:ℤ)) (n:ℤ)).filter (fun x : ℤ => (x : ZMod d) = c)).card
      ≤ 2 * n / d + 2 := by
  set t : ℕ := (c + (n : ZMod d)).val with ht
  have hmain : ((Finset.Icc (-(n:ℤ)) (n:ℤ)).filter (fun x : ℤ => (x : ZMod d) = c)).card
      ≤ ((Finset.Icc 0 (2*n)).filter (fun y => y % d = t)).card := by
    apply Finset.card_le_card_of_injOn (fun x : ℤ => (x + (n:ℤ)).toNat)
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hx ⊢
      obtain ⟨⟨hlo, hhi⟩, hc⟩ := hx
      have h0 : (0:ℤ) ≤ x + (n:ℤ) := by omega
      have hcast : (((x + (n:ℤ)).toNat : ℕ) : ℤ) = x + (n:ℤ) := Int.toNat_of_nonneg h0
      have htop : (((x + (n:ℤ)).toNat : ℕ) : ℤ) ≤ ((2*n : ℕ) : ℤ) := by
        rw [hcast]; push_cast; omega
      refine ⟨⟨Nat.zero_le _, by exact_mod_cast htop⟩, ?_⟩
      have hzm : (((x + (n:ℤ)).toNat : ℕ) : ZMod d) = c + (n : ZMod d) := by
        rw [show ((((x + (n:ℤ)).toNat : ℕ)) : ZMod d) = ((x + (n:ℤ) : ℤ) : ZMod d) from by
              rw [← Int.toNat_of_nonneg h0]; norm_cast]
        push_cast [hc]; ring
      rw [ht, ← ZMod.val_natCast d ((x + (n:ℤ)).toNat)]
      exact congrArg ZMod.val hzm
    · intro x1 hx1 x2 hx2 h
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hx1 hx2
      change (x1 + (n:ℤ)).toNat = (x2 + (n:ℤ)).toNat at h
      have h0a : (0:ℤ) ≤ x1 + (n:ℤ) := by omega
      have h0b : (0:ℤ) ≤ x2 + (n:ℤ) := by omega
      have e1 : ((x1 + (n:ℤ)).toNat : ℤ) = x1 + (n:ℤ) := Int.toNat_of_nonneg h0a
      have e2 : ((x2 + (n:ℤ)).toNat : ℤ) = x2 + (n:ℤ) := Int.toNat_of_nonneg h0b
      have hh : ((x1 + (n:ℤ)).toNat : ℤ) = ((x2 + (n:ℤ)).toNat : ℤ) := by rw [h]
      omega
  refine hmain.trans ?_
  have hbd := nat_card_mod_le (2*n) d t hd
  omega

theorem boxZ_dvd_count_le (n d : ℕ) (hd : 0 < d) :
    ((Work.FIArea1.boxZ n).filter (fun p : ℤ × ℤ => (d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 2)).card
      ≤ Work.FIArea1.Nsol d * (2 * n / d + 2) ^ 2 := by
  classical
  haveI : NeZero d := ⟨Nat.pos_iff_ne_zero.mp hd⟩
  set B : ℕ := 2 * n / d + 2 with hB
  set S : Finset (ℤ × ℤ) :=
    (Work.FIArea1.boxZ n).filter (fun p : ℤ × ℤ => (d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 2) with hS
  set T : Finset (ZMod d × ZMod d) :=
    Finset.univ.filter (fun z : ZMod d × ZMod d => z.1 ^ 2 + z.2 ^ 2 = 0) with hT
  set f : ℤ × ℤ → ZMod d × ZMod d := fun p => ((p.1 : ZMod d), (p.2 : ZMod d)) with hf
  have hNsol : Work.FIArea1.Nsol d = T.card := by
    rw [Work.FIArea1.Nsol, Set.ncard_eq_toFinset_card, hT]
    congr 1
    ext z
    simp
  have hfiber : ∀ b : ZMod d × ZMod d, (S.filter (fun a => f a = b)).card ≤ B ^ 2 := by
    intro b
    have hsub : S.filter (fun a => f a = b) ⊆
        ((Finset.Icc (-(n:ℤ)) (n:ℤ)).filter (fun x : ℤ => (x : ZMod d) = b.1)) ×ˢ
        ((Finset.Icc (-(n:ℤ)) (n:ℤ)).filter (fun x : ℤ => (x : ZMod d) = b.2)) := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, hS, hf,
        Work.FIArea1.boxZ, Finset.product_eq_sprod, Prod.ext_iff] at ha ⊢
      exact ⟨⟨ha.1.1.1, ha.2.1⟩, ⟨ha.1.1.2, ha.2.2⟩⟩
    calc (S.filter (fun a => f a = b)).card
        ≤ (((Finset.Icc (-(n:ℤ)) (n:ℤ)).filter (fun x : ℤ => (x : ZMod d) = b.1)) ×ˢ
        ((Finset.Icc (-(n:ℤ)) (n:ℤ)).filter (fun x : ℤ => (x : ZMod d) = b.2))).card :=
          Finset.card_le_card hsub
      _ = _ * _ := Finset.card_product _ _
      _ ≤ B * B := Nat.mul_le_mul (by simpa [hB] using int_card_mod_le n d hd b.1)
                                   (by simpa [hB] using int_card_mod_le n d hd b.2)
      _ = B ^ 2 := by ring
  have himage : (S.image f).card ≤ Work.FIArea1.Nsol d := by
    rw [hNsol]
    apply Finset.card_le_card
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [Finset.mem_filter, hS, Work.FIArea1.boxZ, Finset.product_eq_sprod,
      Finset.mem_product] at ha
    obtain ⟨_, hdvd⟩ := ha
    have hthis : ((a.1 ^ 2 + a.2 ^ 2 : ℤ) : ZMod d) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mpr hdvd
    push_cast at hthis
    simpa [hf] using hthis
  calc S.card = ∑ b ∈ S.image f, (S.filter (fun a => f a = b)).card :=
        Finset.card_eq_sum_card_image f S
    _ ≤ ∑ b ∈ S.image f, B ^ 2 := Finset.sum_le_sum (fun b _ => hfiber b)
    _ = (S.image f).card * B ^ 2 := by
        rw [Finset.sum_const_nat]; intro x hx; rfl
    _ ≤ Work.FIArea1.Nsol d * B ^ 2 := Nat.mul_le_mul_right _ himage

end Work.FIArea1
