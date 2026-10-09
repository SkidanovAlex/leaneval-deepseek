import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option linter.style.haveILetI false

namespace Work.SSGRoute.HSTwoRow

theorem exists_zmodN_cocycle (p d N : ℕ) [Fact p.Prime] (hN : N = p * d) (hN2 : 1 < N)
    (G' : Type) [Group G'] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G' M] (s : G') (hs : s ^ d = 1) (v : M) :
    ∃ coc : ZMod N → M, coc 0 = 0 ∧ coc 1 = v ∧
      (∀ x : ZMod N, coc x = (Finset.range x.val).sum (fun i => (s ^ i) • v)) ∧
      ∀ x y : ZMod N, coc (x + y) = coc x + (s ^ x.val) • coc y := by
  haveI hNe : NeZero N := ⟨by omega⟩
  let f : ℕ → M := fun k => (Finset.range k).sum (fun i => (s ^ i) • v)
  have hf0 : f 0 = 0 := Finset.sum_range_zero _
  -- one-step recurrence
  have hstep : ∀ k, f (k + 1) = f k + (s ^ k) • v := by
    intro k
    show (Finset.range (k + 1)).sum (fun i => (s ^ i) • v)
        = (Finset.range k).sum (fun i => (s ^ i) • v) + (s ^ k) • v
    rw [Finset.sum_range_succ]
  -- crossed-homomorphism identity
  have hcross : ∀ a b : ℕ, f (a + b) = f a + (s ^ a) • f b := by
    intro a b
    induction b with
    | zero =>
        show f (a + 0) = f a + (s ^ a) • f 0
        rw [Nat.add_zero, hf0, smul_zero, add_zero]
    | succ b ih =>
        have h1 : f (a + (b + 1)) = f (a + b) + (s ^ (a + b)) • v := by
          rw [show a + (b + 1) = (a + b) + 1 by omega]
          exact hstep (a + b)
        rw [h1, ih, hstep b, smul_add, smul_smul, ← pow_add, add_assoc]
  -- the values at multiples of `d`
  have hmuld : ∀ k : ℕ, f (k * d) = k • f d := by
    intro k
    induction k with
    | zero =>
        show f (0 * d) = 0 • f d
        rw [Nat.zero_mul, zero_smul]
        exact hf0
    | succ k ih =>
        have h1 : f (Nat.succ k * d) = f (k * d + d) := by rw [Nat.succ_mul]
        rw [h1, hcross (k * d) d, ih]
        have hp : s ^ (k * d) = 1 := by rw [pow_mul' s k d, hs, one_pow]
        rw [hp, succ_nsmul, one_smul]
  -- the sum over a full period `N = p * d` vanishes
  have hfN : f N = 0 := by
    rw [hN, hmuld p, ← Nat.cast_smul_eq_nsmul (ZMod p) p (f d), ZMod.natCast_self, zero_smul]
  -- periodicity
  have hper : ∀ k : ℕ, f (k + N) = f k := by
    intro k
    rw [hcross k N, hfN, smul_zero, add_zero]
  refine ⟨fun x => f x.val, ?_, ?_, ?_, ?_⟩
  · show f (0 : ZMod N).val = 0
    rw [ZMod.val_zero]
    exact hf0
  · haveI : Fact (1 < N) := ⟨hN2⟩
    show f (1 : ZMod N).val = v
    rw [ZMod.val_one N]
    show (Finset.range 1).sum (fun i => (s ^ i) • v) = v
    rw [Finset.sum_range_one, pow_zero, one_smul]
  · intro x
    rfl
  · intro x y
    show f (x + y).val = f x.val + (s ^ x.val) • f y.val
    rw [ZMod.val_add x y, ← hcross x.val y.val]
    by_cases ha : x.val + y.val < N
    · rw [Nat.mod_eq_of_lt ha]
    · have h1 : x.val + y.val = (x.val + y.val - N) + N := by
        have := ZMod.val_lt (n := N) x
        have := ZMod.val_lt (n := N) y
        omega
      have h2 : (x.val + y.val) % N = x.val + y.val - N := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt]
        have := ZMod.val_lt (n := N) x
        have := ZMod.val_lt (n := N) y
        omega
      have h3 : f (x.val + y.val) = f (x.val + y.val - N) := by
        conv_lhs => rw [h1]
        rw [hper]
      rw [h2, h3]

end Work.SSGRoute.HSTwoRow
