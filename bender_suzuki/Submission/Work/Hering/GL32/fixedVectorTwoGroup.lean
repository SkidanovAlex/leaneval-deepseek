import Mathlib
import Submission.Work.Hering.GL32.pgroup_fixed_ne_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.Hering.GL32

/-- **A finite `2`-group acting linearly on a nonzero finite module over `𝔽₂` fixes a nonzero
vector.**

This is the special case `p = 2` of `pgroup_fixed_ne_bot`; the proof here repeats the orbit-counting
argument directly on the subspace spanned by the `P`-orbit of a chosen nonzero vector, which lets us
work with the `MulAction` of `P` alone (no `SMulCommClass` hypothesis is needed). -/
theorem fixedVectorTwoGroup {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (hne : ∃ m : M, m ≠ 0) {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (φ : P →* (M ≃ₗ[ZMod 2] M)) : ∃ m : M, m ≠ 0 ∧ ∀ g : P, φ g m = m := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m₀, hm₀⟩ := hne
  -- The `𝔽₂`-subspace of `M` spanned by the `P`-orbit of `m₀`.
  let v : P → M := fun g => φ g m₀
  let V : Submodule (ZMod 2) M := Submodule.span (ZMod 2) (Set.range v)
  have hm₀V : m₀ ∈ V := Submodule.subset_span (Set.mem_range.mpr ⟨1, by simp [v]⟩)
  -- `V` is invariant under `φ`.
  have hVmem : ∀ (g : P) {x : M}, x ∈ V → φ g x ∈ V := by
    intro g x hx
    refine Submodule.span_induction (p := fun y _ => φ g y ∈ V) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨h, rfl⟩
      have key : φ g (v h) = v (g * h) := by simp [v, map_mul]
      rw [key]
      exact Submodule.subset_span (Set.mem_range.mpr ⟨g * h, rfl⟩)
    · rw [map_zero]; exact V.zero_mem
    · intro y z _ _ ihy ihz; rw [map_add]; exact V.add_mem ihy ihz
    · intro a y _ ihy
      rw [LinearEquiv.map_smul]
      exact V.smul_mem a ihy
  -- The induced action of `P` on `V`.
  let actV : P → V → V := fun g x => ⟨φ g (x : M), hVmem g x.2⟩
  letI : MulAction P V :=
    { smul := actV
      one_smul := fun x => Subtype.ext (by show φ 1 (x : M) = (x : M); rw [map_one]; rfl)
      mul_smul := fun g h x => Subtype.ext (by
        show φ (g * h) (x : M) = φ g (φ h (x : M)); rw [map_mul]; rfl) }
  haveI : Finite V :=
    Finite.of_injective (Subtype.val : V → M) Subtype.val_injective
  -- `V` is a nontrivial finite `𝔽₂`-vector space, so `Nat.card V` is a positive power of `2`.
  haveI hntV : Nontrivial V :=
    ⟨⟨⟨m₀, hm₀V⟩, 0, fun h => hm₀ (by simpa using congrArg Subtype.val h)⟩⟩
  haveI : Module.Finite (ZMod 2) V :=
    Module.Finite.span_of_finite (ZMod 2) (Set.finite_range v)
  haveI : Module.Free (ZMod 2) V := Module.Free.of_divisionRing (ZMod 2) V
  have hfin : 0 < Module.finrank (ZMod 2) V :=
    (Module.finrank_pos_iff_of_free (ZMod 2) V).mpr hntV
  have hdvd : 2 ∣ Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Nat.card_zmod]
    exact dvd_pow_self 2 hfin.ne'
  -- `0` is a fixed point and `2 ∣ Nat.card V`, so another (nonzero) fixed point exists.
  have h0fix : (0 : V) ∈ MulAction.fixedPoints P V := by
    rw [MulAction.mem_fixedPoints]
    intro g
    exact Subtype.ext (by show φ g (0 : M) = 0; rw [map_zero])
  obtain ⟨b, hbfix, hbne⟩ :=
    IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point hP V hdvd h0fix
  refine ⟨(b : M), ?_, ?_⟩
  · intro hb
    exact hbne (Subtype.ext (by simpa using hb)).symm
  · intro g
    have h := MulAction.mem_fixedPoints.mp hbfix g
    change actV g b = b at h
    exact congrArg Subtype.val h

end Work.Hering.GL32
