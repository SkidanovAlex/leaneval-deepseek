import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.NA.Setup
import Submission.Work.HP.NA.SmoothDefs
import Submission.Work.HP.NA.Smooth.card_ker_of_surj

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HP.NA

open Finset

theorem card_smooth_cond (d n p e : ℕ) (hp : p.Prime) (x : Fin (n + 1) → ZMod (p ^ e))
    (j0 : Fin (n + 1)) (hx : IsUnit (x j0)) :
    Nat.card {a : Work.HP.Mon d n → ZMod (p ^ e) // Work.HP.NA.fev d n a x = 0 ∧ ∀ i, i ≠ j0 → Work.HP.NA.dfev d n a x i = 0}
      = (p ^ e) ^ (Work.HP.NN d n - (n + 1)) := by
  have hcard : Nat.card {a : Mon d n → ZMod (p ^ e) //
        fev d n a x = 0 ∧ ∀ i, i ≠ j0 → dfev d n a x i = 0}
      = Nat.card (LinearMap.ker (smoothMap d n x j0)) := by
    refine Nat.card_congr
      ⟨fun a => ⟨a.1, LinearMap.mem_ker.mpr ((smoothMap_zero_iff d n x j0 a.1).mpr a.2)⟩,
       fun b => ⟨b.1, (smoothMap_zero_iff d n x j0 b.1).mp (LinearMap.mem_ker.mp b.2)⟩,
       fun a => Subtype.ext rfl, fun b => Subtype.ext rfl⟩
  rw [hcard]
  cases d with
  | zero =>
    let z0 : Mon 0 n := ⟨fun _ => (0 : Fin (0 + 1)), by simp⟩
    have hz : ∀ m : Mon 0 n, m = z0 := by
      intro m
      refine Subtype.ext (funext fun i => ?_)
      exact Fin.eq_zero (m.1 i)
    have key : ∀ a : Mon 0 n → ZMod (p ^ e), fev 0 n a x = 0 → a = 0 := by
      intro a ha
      have hv : veronese 0 n x z0 = 1 := by
        rw [veronese]
        apply Finset.prod_eq_one
        intro i _
        rw [show ((z0.1 i : ℕ)) = 0 from by simp [z0]]
        simp
      have hsum : fev 0 n a x = a z0 * veronese 0 n x z0 := by
        rw [fev, Finset.sum_eq_single z0 (fun b _ hb => absurd (hz b) hb)
          (fun h => absurd (Finset.mem_univ z0) h)]
      have hz0val : a z0 = 0 := by
        have h1 : a z0 * veronese 0 n x z0 = 0 := by rw [← hsum]; exact ha
        rwa [hv, mul_one] at h1
      funext m
      simp [hz m, hz0val]
    have hker : Nat.card (LinearMap.ker (smoothMap 0 n x j0)) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => ?_⟩, ⟨⟨0, ?_⟩⟩⟩
      · refine Subtype.ext ?_
        rw [key a.1 ((smoothMap_zero_iff 0 n x j0 a.1).mp (LinearMap.mem_ker.mp a.2)).1,
            key b.1 ((smoothMap_zero_iff 0 n x j0 b.1).mp (LinearMap.mem_ker.mp b.2)).1]
      · exact LinearMap.mem_ker.mpr (map_zero (smoothMap 0 n x j0))
    have hNN : NN 0 n = 1 := by
      show Fintype.card (Mon 0 n) = 1
      rw [← Nat.card_eq_fintype_card, Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => by rw [hz a, hz b]⟩, ⟨z0⟩⟩
    rw [hker, hNN, show (1 : ℕ) - (n + 1) = 0 from by omega, pow_zero]
  | succ d' =>
    obtain ⟨u, hu⟩ := hx
    let yi : ZMod (p ^ e) := ↑u⁻¹
    have hyi : yi * x j0 = 1 := by
      have h1 : (↑u⁻¹ : ZMod (p ^ e)) * (↑u : ZMod (p ^ e)) = 1 := Units.inv_mul u
      rw [hu] at h1
      exact h1
    have hs : ∀ j : Fin (n + 1),
        smoothMap (d' + 1) n x j0 (svFun d' n x j0 yi j) = Pi.single j 1 := by
      intro j
      by_cases hj : j = j0
      · rw [svFun, dif_pos hj, map_smul, smoothMap_single_pM0]
        rw [show (yi ^ (d' + 1)) • Pi.single j0 (x j0 ^ (d' + 1))
              = Pi.single j0 ((yi ^ (d' + 1)) * x j0 ^ (d' + 1)) from by
            funext i
            simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
            split_ifs <;> ring]
        rw [← mul_pow, hyi, one_pow, hj]
      · rw [svFun, dif_neg hj, map_add, map_smul, map_smul, smoothMap_single_pMk,
          smoothMap_single_pM0]
        have h1 : yi ^ d' * x j0 ^ d' = 1 := by rw [← mul_pow, hyi, one_pow]
        have h2 : yi ^ (d' + 1) * x j0 ^ (d' + 1) = 1 := by rw [← mul_pow, hyi, one_pow]
        rw [show (yi ^ d') • ((Pi.single j0 (x j0 ^ d' * x j) : Fin (n + 1) → ZMod (p ^ e))
                + (Pi.single j (x j0 ^ d') : Fin (n + 1) → ZMod (p ^ e)))
              = Pi.single j0 (yi ^ d' * (x j0 ^ d' * x j))
                + Pi.single j (yi ^ d' * x j0 ^ d') from by
            funext i
            simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.single_apply]
            split_ifs <;> ring,
            show (-(x j * yi ^ (d' + 1))) •
                (Pi.single j0 (x j0 ^ (d' + 1)) : Fin (n + 1) → ZMod (p ^ e))
              = Pi.single j0 ((-(x j * yi ^ (d' + 1))) * x j0 ^ (d' + 1)) from by
            funext i
            simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
            split_ifs <;> ring]
        rw [show yi ^ d' * (x j0 ^ d' * x j) = x j from by
              rw [← mul_assoc, h1, one_mul],
            h1,
            show (-(x j * yi ^ (d' + 1))) * x j0 ^ (d' + 1) = -x j from by
              rw [neg_mul, mul_assoc, h2, mul_one]]
        rw [show ((Pi.single j0 (x j) : Fin (n + 1) → ZMod (p ^ e))
                  + Pi.single j (1 : ZMod (p ^ e))) + Pi.single j0 (-x j)
              = Pi.single j (1 : ZMod (p ^ e))
                + (Pi.single j0 (x j) + Pi.single j0 (-x j)) from by abel,
            show (Pi.single j0 (x j) : Fin (n + 1) → ZMod (p ^ e)) + Pi.single j0 (-x j) = 0 from by
              funext i
              simp only [Pi.add_apply, Pi.single_apply]
              split_ifs <;> simp,
            add_zero]
    have hsurj : Function.Surjective (smoothMap (d' + 1) n x j0) := by
      intro y
      refine ⟨∑ j, y j • svFun d' n x j0 yi j, ?_⟩
      have h1 : smoothMap (d' + 1) n x j0 (∑ j, y j • svFun d' n x j0 yi j)
          = ∑ j, y j • smoothMap (d' + 1) n x j0 (svFun d' n x j0 yi j) := by
        rw [map_sum]
        exact Finset.sum_congr rfl (fun j _ => by rw [map_smul])
      rw [h1]
      ext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hterm : ∀ j : Fin (n + 1),
          y j * (smoothMap (d' + 1) n x j0 (svFun d' n x j0 yi j) i)
            = if i = j then y j else 0 := by
        intro j
        rw [hs j, Pi.single_apply]
        by_cases h : i = j <;> simp [h]
      rw [Finset.sum_congr rfl (fun j _ => hterm j)]
      simpa using Finset.sum_ite_eq Finset.univ i (fun j : Fin (n + 1) => y j)
    have hle : Fintype.card (Fin (n + 1)) ≤ Fintype.card (Mon (d' + 1) n) := by
      let f : Fin (n + 1) → Mon (d' + 1) n := fun i =>
        ⟨fun l => if l = i then ⟨d' + 1, Nat.lt_succ_self (d' + 1)⟩ else 0, by
          have h : (∑ l, ((if l = i then (⟨d' + 1, Nat.lt_succ_self (d' + 1)⟩ :
              Fin (d' + 1 + 1)) else 0 : Fin (d' + 1 + 1)) : ℕ))
              = ∑ l, (if l = i then d' + 1 else 0) := by
            apply Finset.sum_congr rfl; intro l _; by_cases h : l = i <;> simp [h]
          rw [h]; simp⟩
      apply Fintype.card_le_of_injective f
      intro i i' hii
      by_contra hne
      have hc := congrArg (fun m : Mon (d' + 1) n => ((m.1 i : ℕ))) hii
      have h1 : ((f i).1 i : ℕ) = d' + 1 := by simp [f]
      have h2 : ((f i').1 i : ℕ) = 0 := by simp [f, hne]
      rw [h1, h2] at hc
      omega
    haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
    have hmain := Smooth.card_ker_of_surj (T := smoothMap (d' + 1) n x j0) hsurj hle
    rw [hmain, ZMod.card, Fintype.card_fin]

end Work.HP.NA
