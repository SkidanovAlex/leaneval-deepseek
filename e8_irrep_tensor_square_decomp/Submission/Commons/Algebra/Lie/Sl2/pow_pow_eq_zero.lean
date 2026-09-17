import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Order.Lattice.Nat

namespace Commons.Algebra.Lie.Sl2

open Finset

/-- If `e` and `f` are locally nilpotent endomorphisms of a `K`-module `V`, then for every
vector `v` the family `{e^b v : b}` (which is finite, since `e` is locally nilpotent on `v`)
admits a uniform nilpotency bound for `f`, and moreover `e^b v` itself vanishes for large `b`.
Hence there is `N` such that `f^a (e^b v) = 0` whenever `N ≤ a` or `N ≤ b`. -/
theorem pow_pow_eq_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {e f : Module.End K V}
    (he : ∀ v : V, ∃ n : ℕ, (e ^ n) v = 0) (hf : ∀ v : V, ∃ n : ℕ, (f ^ n) v = 0)
    (v : V) : ∃ N : ℕ, ∀ a b : ℕ, N ≤ a ∨ N ≤ b → (f ^ a) ((e ^ b) v) = 0 := by
  classical
  -- `n` is a nilpotency index of `e` at `v`.
  obtain ⟨n, hn⟩ := he v
  -- Choose, for each `b`, a bound `g b` with `f^(g b) (e^b v) = 0`.
  let g : ℕ → ℕ := fun b => Classical.choose (hf ((e ^ b) v))
  have hg : ∀ b : ℕ, (f ^ g b) ((e ^ b) v) = 0 :=
    fun b => Classical.choose_spec (hf ((e ^ b) v))
  -- The uniform bound, taken as the max over the finitely many nonzero `e^b v`, `b < n`.
  let M : ℕ := (Finset.range n).sup g
  have hMle : ∀ b : ℕ, b < n → g b ≤ M :=
    fun b hb => Finset.le_sup (Finset.mem_range.mpr hb)
  -- `f^M` kills every `e^b v`.
  have hMbound : ∀ b : ℕ, (f ^ M) ((e ^ b) v) = 0 := by
    intro b
    by_cases hb : b < n
    · have hgb : g b ≤ M := hMle b hb
      rw [← Nat.sub_add_cancel hgb, pow_add, Module.End.mul_apply, hg b, map_zero]
    · have hnb : n ≤ b := Nat.le_of_not_lt hb
      have hzb : (e ^ b) v = 0 := by
        rw [← Nat.sub_add_cancel hnb, pow_add, Module.End.mul_apply, hn, map_zero]
      rw [hzb, map_zero]
  refine ⟨max M n, ?_⟩
  intro a b hab
  rcases hab with ha | hb
  · -- `M ≤ N ≤ a`: peel off an `f^M`, which kills `e^b v`.
    have hMa : M ≤ a := le_trans (le_max_left M n) ha
    rw [← Nat.sub_add_cancel hMa, pow_add, Module.End.mul_apply, hMbound b, map_zero]
  · -- `n ≤ N ≤ b`: then `e^b v = 0`.
    have hnb : n ≤ b := le_trans (le_max_right M n) hb
    have hzb : (e ^ b) v = 0 := by
      rw [← Nat.sub_add_cancel hnb, pow_add, Module.End.mul_apply, hn, map_zero]
    rw [hzb, map_zero]

end Commons.Algebra.Lie.Sl2