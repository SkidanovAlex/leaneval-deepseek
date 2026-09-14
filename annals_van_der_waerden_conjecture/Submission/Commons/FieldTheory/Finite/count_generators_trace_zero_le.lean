import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Trace.Defs

namespace Commons.FieldTheory.Finite

/-- In a finite field `F` of characteristic `p` and degree `n = [F : 𝔽_p]` over its
prime field, if the trace `F → 𝔽_p` is not identically zero, then at most
`p ^ (n - 1) - 1` elements of `Fˣ` of maximal order (i.e. generators of the cyclic
group `Fˣ`) have trace `0`.

This is the trivial count: the trace is a nonzero `𝔽_p`-linear functional, hence onto,
so the trace-zero hyperplane has `p ^ (n - 1)` elements, exactly one of which is `0`. -/
theorem count_generators_trace_zero_le {F : Type*} [Field F] [Fintype F] (p : ℕ)
    [Fact (Nat.Prime p)] [Algebra (ZMod p) F] [CharP F p]
    (hT : Algebra.trace (ZMod p) F ≠ 0) :
    Nat.card {x : Fˣ // orderOf x = Fintype.card F - 1 ∧
      Algebra.trace (ZMod p) F (x : F) = 0}
      ≤ p ^ (Module.finrank (ZMod p) F - 1) - 1 := by
  classical
  let T : F →ₗ[ZMod p] ZMod p := Algebra.trace (ZMod p) F
  have hTne : T ≠ 0 := hT
  -- A nonzero linear functional into the one-dimensional space `𝔽_p` is surjective.
  have hsurj : T.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    obtain ⟨y, hy⟩ : ∃ y, T y ≠ 0 := by
      by_contra h
      apply hTne
      ext w
      simpa using not_exists.mp h w
    intro z
    refine ⟨(z * (T y)⁻¹) • y, ?_⟩
    rw [map_smul, smul_eq_mul]
    rw [mul_assoc, inv_mul_cancel₀ hy, mul_one]
  have hfr : Module.finrank (ZMod p) T.range = 1 := by
    rw [hsurj, finrank_top (ZMod p) (ZMod p), Module.finrank_self]
  have hrn := LinearMap.finrank_range_add_finrank_ker T
  rw [hfr] at hrn
  -- Rank-nullity: the kernel (the trace-zero hyperplane) has dimension `n - 1`.
  have hkerdim : Module.finrank (ZMod p) T.ker = Module.finrank (ZMod p) F - 1 := by
    omega
  have hkercard : Fintype.card T.ker = p ^ (Module.finrank (ZMod p) F - 1) := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := T.ker), hkerdim, ZMod.card]
  -- The generators of trace zero form a subset of the nonzero trace-zero elements.
  let S := {x : Fˣ // orderOf x = Fintype.card F - 1 ∧ T (x : F) = 0}
  have hmap : Nat.card S ≤ Nat.card {y : T.ker // y ≠ 0} := by
    apply Nat.card_le_card_of_injective
      (f := fun x : S =>
        (⟨⟨(x.1 : F), by rw [LinearMap.mem_ker]; exact x.2.2⟩,
          by
            intro h
            exact Units.ne_zero x.1 (by simpa using congrArg (fun w : T.ker => (w : F)) h)⟩
          : {y : T.ker // y ≠ 0}))
    intro a b hab
    apply Subtype.ext
    have hv : (a.1 : F) = (b.1 : F) := by
      have := congrArg (fun w : {y : T.ker // y ≠ 0} => ((w.1 : T.ker) : F)) hab
      simpa using this
    exact Units.ext hv
  have hnonzerocard : Nat.card {y : T.ker // y ≠ 0} = Fintype.card T.ker - 1 := by
    rw [Nat.card_eq_fintype_card]
    exact Set.card_ne_eq (0 : T.ker)
  calc Nat.card S ≤ Nat.card {y : T.ker // y ≠ 0} := hmap
    _ = Fintype.card T.ker - 1 := hnonzerocard
    _ = p ^ (Module.finrank (ZMod p) F - 1) - 1 := by rw [hkercard]

end Commons.FieldTheory.Finite