import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A finite `p`-group acting `𝔽_p`-linearly on a nonzero module has a nonzero fixed vector

Let `P` be a finite `p`-group acting `𝔽_p`-linearly on a nonzero module `M` over `ZMod p`
(the `P`-action commutes with the scalar action, `SMulCommClass P (ZMod p) M`).  Then `M`
contains a nonzero vector fixed by all of `P`.

The argument is the standard one.  Pick `x ≠ 0` and let `V` be the `P`-stable
`𝔽_p`-submodule spanned by the `P`-orbit of `x`; it is nonzero and finite dimensional, hence
finite.  A finite `p`-group acting on a finite set has a number of fixed points congruent to
the cardinality of the set modulo `p` (`IsPGroup.card_modEq_card_fixedPoints`).  Since `V` is a
nonzero finite dimensional `𝔽_p`-vector space, `p ∣ Nat.card V`, so `p ∣ Nat.card V^P`; as `0`
is a fixed point this produces a *second* fixed point `b ≠ 0`, whose image in `M` is fixed by
`P` and nonzero.
-/

namespace Work.SSGRoute.PTembedding

set_option linter.style.haveILetI false

theorem pgroup_fixed_vector {p : ℕ} [Fact p.Prime] {P M : Type} [Group P] [Finite P]
    (hP : IsPGroup p P) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction P M]
    [SMulCommClass P (ZMod p) M] (hM : Nontrivial M) :
    ∃ m : M, m ≠ 0 ∧ ∀ g : P, g • m = m := by
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  -- the `P`-orbit of `x` and the submodule it spans
  set T : Set M := Set.range (fun g : P => g • x) with hT
  set V : Submodule (ZMod p) M := Submodule.span (ZMod p) T with hV
  have hxT : x ∈ T := by rw [hT]; exact ⟨1, one_smul P x⟩
  have hxV : x ∈ V := by rw [hV]; exact Submodule.subset_span hxT
  -- `V` is stable under the action of `P`
  have hstable : ∀ (g : P) {v : M}, v ∈ V → g • v ∈ V := by
    intro g v hv
    rw [hV] at hv ⊢
    refine Submodule.span_induction (s := T)
      (p := fun v _ => g • v ∈ Submodule.span (ZMod p) T) ?_ ?_ ?_ ?_ hv
    · intro y hy
      rw [hT] at hy
      obtain ⟨h, hh⟩ := hy
      rw [← hh]
      exact Submodule.subset_span (by rw [hT]; exact ⟨g * h, mul_smul g h x⟩)
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro y z _ _ hy hz
      rw [smul_add]; exact Submodule.add_mem _ hy hz
    · intro a y _ hy
      rw [smul_comm]; exact Submodule.smul_mem _ a hy
  -- the induced action of `P` on the subtype `V`
  letI hA : MulAction P V :=
    { toSMul := ⟨fun g v => ⟨g • (v : M), hstable g v.2⟩⟩
      one_smul := fun v => Subtype.ext (one_smul P (v : M))
      mul_smul := fun a b v => Subtype.ext (mul_smul a b (v : M)) }
  haveI hfin : Module.Finite (ZMod p) V := by
    rw [hV]
    exact Module.Finite.span_of_finite (ZMod p) (Set.finite_range _)
  haveI : Nontrivial V := by
    refine ⟨⟨x, hxV⟩, 0, ?_⟩
    intro h
    exact hx (by simpa using congrArg Subtype.val h)
  -- `V` is a nonzero finite dimensional `𝔽_p`-vector space
  have hcard : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := V), Nat.card_zmod]
  haveI : Finite V := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact pow_ne_zero _ (Fact.out (p := p.Prime)).ne_zero)
  have hpdvd : p ∣ Nat.card V := by
    rw [hcard]
    exact dvd_pow_self p (Module.finrank_pos (R := ZMod p) (M := V)).ne'
  -- `0` is a fixed point of the action on `V`
  have hzero : (0 : V) ∈ MulAction.fixedPoints P V := by
    rw [MulAction.mem_fixedPoints]
    intro g
    exact Subtype.ext (smul_zero g)
  -- so there is a second, nonzero, fixed point
  obtain ⟨b, hbmem, hbne⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hpdvd (a := (0 : V)) hzero
  refine ⟨(b : M), ?_, ?_⟩
  · intro h
    exact hbne (Subtype.ext h).symm
  · intro g
    exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp hbmem g)

end Work.SSGRoute.PTembedding
