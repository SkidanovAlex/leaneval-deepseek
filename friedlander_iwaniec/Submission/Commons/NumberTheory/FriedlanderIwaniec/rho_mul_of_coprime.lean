import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_sieve_remainder_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- The root count `ρ(b; d) = #{α : ZMod d | α ^ 2 + b ^ 2 = 0}` is multiplicative
in `d`: for coprime `m`, `n`, `ρ(b; mn) = ρ(b; m) · ρ(b; n)`. -/
theorem rho_mul_of_coprime (b m n : ℕ) (h : Nat.Coprime m n) :
    Submission.rho b (m * n) = Submission.rho b m * Submission.rho b n := by
  let e : ZMod (m * n) ≃+* ZMod m × ZMod n := ZMod.chineseRemainder h
  let S : Set (ZMod (m * n)) := {α | α ^ 2 + (b : ZMod (m * n)) ^ 2 = 0}
  let Bm : Set (ZMod m) := {x | x ^ 2 + (b : ZMod m) ^ 2 = 0}
  let Bn : Set (ZMod n) := {y | y ^ 2 + (b : ZMod n) ^ 2 = 0}
  have hcast : e (b : ZMod (m * n)) = ((b : ZMod m), (b : ZMod n)) := by
    apply Prod.ext <;> simp [e, ZMod.chineseRemainder]
  have himg : e '' S = Bm ×ˢ Bn := by
    ext q
    constructor
    · rintro ⟨α, hα, rfl⟩
      have hα' : α ^ 2 + (b : ZMod (m * n)) ^ 2 = 0 := hα
      have hmap : e α ^ 2 + ((b : ZMod m), (b : ZMod n)) ^ 2 = 0 := by
        have h0 : e (α ^ 2 + (b : ZMod (m * n)) ^ 2) = e 0 := by rw [hα']
        rw [map_add, map_pow, map_pow, hcast, map_zero] at h0
        exact h0
      rw [Set.mem_prod]
      constructor
      · have := congrArg Prod.fst hmap
        simpa [Bm] using this
      · have := congrArg Prod.snd hmap
        simpa [Bn] using this
    · rintro hq
      have hq' : q.1 ^ 2 + (b : ZMod m) ^ 2 = 0 ∧ q.2 ^ 2 + (b : ZMod n) ^ 2 = 0 := by
        simpa only [Set.mem_prod, Bm, Bn, Set.mem_ofPred_eq] using hq
      refine ⟨e.symm q, ?_, e.apply_symm_apply q⟩
      show (e.symm q) ^ 2 + (b : ZMod (m * n)) ^ 2 = 0
      apply e.injective
      rw [map_add, map_pow, map_pow, hcast, map_zero, e.apply_symm_apply]
      refine Prod.ext ?_ ?_
      · simpa using hq'.1
      · simpa using hq'.2
  have hcard : S.ncard = Bm.ncard * Bn.ncard := by
    calc S.ncard = (e '' S).ncard := (Set.ncard_image_of_injective S e.injective).symm
      _ = (Bm ×ˢ Bn).ncard := by rw [himg]
      _ = Bm.ncard * Bn.ncard := Set.ncard_prod
  simpa only [Submission.rho, S, Bm, Bn] using hcard

end Commons.NumberTheory.FriedlanderIwaniec
