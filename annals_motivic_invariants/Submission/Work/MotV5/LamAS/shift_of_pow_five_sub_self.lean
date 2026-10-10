import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Galois shift of a root of `X⁵ - X - g`

Let `L` be a field of characteristic `5` together with an `F`-algebra structure for a field `F` of
characteristic `5`, let `W ∈ L` satisfy the Artin–Schreier equation `W⁵ - W = g` for a `g` in the
image of `F`, and let `γ` be an `F`-algebra automorphism of `L`.

Then `γ W` is another root of the same equation, so `γ W - W` is a root of the additive polynomial
`X⁵ - X = ℘(X)`, whose roots are exactly the elements of the prime field `𝔽₅`.  Consequently
`γ W = W + k` for some `k ∈ {0,1,2,3,4}`, the `k`-th integer in `L`.

The formal proof is short:

* `γ` fixes the constants (it is `F`-linear), so `γ (W⁵ - W) = W⁵ - W`; together with
  `(γ W)⁵ - γ W = γ (W⁵ - W)` this gives `℘(γ W) = ℘(W)`.
* In characteristic `5` the Frobenius is additive (freshman's dream `sub_pow_char`), so
  `(γ W - W)⁵ = (γ W)⁵ - W⁵` and hence `℘(γ W - W) = 0`, i.e. `(γ W - W)⁵ = γ W - W`.
* `Subfield.mem_bot_iff_pow_eq_self` then places `γ W - W` in the prime subfield, and
  `mem_bot_iff_intCast` exhibits it as the image of an integer, which we reduce modulo `5` to an
  index `k : Fin 5`.
-/

namespace Work.MotV5.LamAS

theorem shift_of_pow_five_sub_self {F L : Type*} [Field F] [CharP F 5] [Field L]
    [Algebra F L] {W : L} {g' : F} (hW : W ^ 5 - W = algebraMap F L g')
    (γ : L ≃ₐ[F] L) :
    ∃ k : Fin 5, γ W = W + algebraMap ℤ L ((k : Fin 5) : ℤ) := by
  have h5p : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hL : CharP L 5 := CharP.of_ringHom_of_ne_zero (algebraMap F L) 5 (by norm_num)
  -- `γ` fixes the constants
  have hfix : γ (algebraMap F L g') = algebraMap F L g' := AlgEquiv.commutes γ g'
  -- `γ W` is a root of the same Artin–Schreier equation
  have hgm : (γ W) ^ 5 - γ W = W ^ 5 - W := by
    have hγ : γ (W ^ 5 - W) = (γ W) ^ 5 - γ W := by rw [map_sub, map_pow]
    rw [← hγ, hW, hfix]
  -- hence `x = γ W - W` satisfies `x⁵ = x`
  have hx : (γ W - W) ^ 5 = γ W - W := by
    have h1 : (γ W - W) ^ 5 = (γ W) ^ 5 - W ^ 5 := sub_pow_char (γ W) W
    rw [h1]
    have h2 : (γ W) ^ 5 - W ^ 5 = ((γ W) ^ 5 - γ W) - (W ^ 5 - W) + (γ W - W) := by ring
    rw [h2, hgm]
    first | refl_ring1 | ring
  -- so `x` lies in the prime field
  have hxmem : γ W - W ∈ (⊥ : Subfield L) :=
    (Subfield.mem_bot_iff_pow_eq_self L 5).mpr hx
  obtain ⟨n, hn⟩ := (mem_bot_iff_intCast 5 L).mp hxmem
  -- reduce the integer representative `n` modulo `5`
  let k : Fin 5 := ⟨n.natMod 5, Int.natMod_lt (m := n) (by norm_num)⟩
  refine ⟨k, ?_⟩
  have hk : ((k : Fin 5) : ℤ) = n % (5 : ℤ) := by
    simp only [k]
    rw [Int.natMod, Int.toNat_of_nonneg (Int.emod_nonneg n (by norm_num))]
  have hcast : algebraMap ℤ L ((k : Fin 5) : ℤ) = (n : L) := by
    rw [hk]
    exact (CharP.intCast_eq_intCast_mod L 5 (a := n)).symm
  refine eq_add_of_sub_eq' ?_
  rw [hcast, ← hn]

end Work.MotV5.LamAS
