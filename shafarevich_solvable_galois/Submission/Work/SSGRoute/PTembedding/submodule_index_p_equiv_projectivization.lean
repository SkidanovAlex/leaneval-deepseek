import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTembedding

open scoped LinearAlgebra.Projectivization

set_option linter.style.haveILetI false

/-- A nonzero linear functional `φ : V → ZMod p` has kernel of index `p`:
the quotient `V ⧸ ker φ` is isomorphic to the range of `φ`, which is all of `ZMod p`. -/
lemma ker_index_eq (p : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    (φ : Module.Dual (ZMod p) V) (hφ : φ ≠ 0) :
    (φ.ker).toAddSubgroup.index = p := by
  have htop : φ.range = ⊤ := by
    rcases Ideal.eq_bot_or_top φ.range with h | h
    · exact absurd (LinearMap.range_eq_bot.mp h) hφ
    · exact h
  show Nat.card (V ⧸ φ.ker) = p
  rw [Nat.card_congr φ.quotKerEquivRange.toEquiv, htop]
  rw [Nat.card_congr (Submodule.topEquiv (R := ZMod p) (M := ZMod p)).toEquiv, Nat.card_zmod]

/-- Every submodule `K` of a `ZMod p`-module `V` with `K.toAddSubgroup.index = p` is the kernel
of a nonzero linear functional.  Indeed `V ⧸ K` has `p` elements, hence is a one-dimensional
vector space over `ZMod p`, so it is linearly isomorphic to `ZMod p`; composing the inverse
isomorphism with the quotient map yields the desired functional. -/
lemma exists_dual_ker_eq (p : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    (K : Submodule (ZMod p) V) (hK : K.toAddSubgroup.index = p) :
    ∃ φ : Module.Dual (ZMod p) V, φ ≠ 0 ∧ φ.ker = K := by
  have hp := Fact.out (p := p.Prime)
  have hcard : Nat.card (V ⧸ K) = p := by
    have h := AddSubgroup.index_eq_card K.toAddSubgroup
    rw [hK] at h
    exact h.symm
  haveI : Finite (V ⧸ K) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  haveI : Module.Finite (ZMod p) (V ⧸ K) := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod p) (V ⧸ K) = 1 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V ⧸ K)
    rw [hcard, Nat.card_zmod] at h
    exact ((Nat.Prime.pow_eq_iff hp).mp h.symm).2
  let e : (V ⧸ K) ≃ₗ[ZMod p] ZMod p :=
    LinearEquiv.ofFinrankEq (V ⧸ K) (ZMod p) (by rw [hfr, Module.finrank_self])
  refine ⟨e.toLinearMap.comp (Submodule.mkQ K), ?_, ?_⟩
  · intro hzero
    have hsurj : Function.Surjective (e.toLinearMap.comp (Submodule.mkQ K)) :=
      e.surjective.comp (Submodule.mkQ_surjective K)
    obtain ⟨x, hx⟩ := hsurj 1
    rw [hzero, LinearMap.zero_apply] at hx
    exact one_ne_zero hx.symm
  · ext x
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_toLinearMap]
    constructor
    · intro h
      have h0 : (Submodule.Quotient.mk x : V ⧸ K) = 0 := by
        apply e.injective
        rw [h, map_zero]
      rwa [Submodule.Quotient.mk_eq_zero] at h0
    · intro hx
      rw [show (Submodule.Quotient.mk x : V ⧸ K) = 0 from (Submodule.Quotient.mk_eq_zero K).mpr hx,
        map_zero]

/-- Two nonzero linear functionals with the same kernel are proportional.  This is proved
elementarily: if `φ ≠ 0` and `v` satisfies `φ v ≠ 0`, then `ψ = (ψ v / φ v) • φ`. -/
lemma exists_smul_of_ker_eq (p : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    (φ ψ : Module.Dual (ZMod p) V) (hφ : φ ≠ 0) (hk : φ.ker = ψ.ker) :
    ∃ c : ZMod p, c • φ = ψ := by
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hφ
    exact ⟨v, by simpa using hv⟩
  refine ⟨ψ v * (φ v)⁻¹, ?_⟩
  ext w
  have hmem : φ w • v - φ v • w ∈ φ.ker := by
    rw [LinearMap.mem_ker]
    simp only [map_sub, map_smul, smul_eq_mul]
    ring
  rw [hk, LinearMap.mem_ker] at hmem
  rw [LinearMap.smul_apply, smul_eq_mul]
  have h1 : φ w * ψ v = φ v * ψ w := by
    simpa only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] using hmem
  have h2 : ψ w = ψ v * (φ v)⁻¹ * φ w := by
    calc ψ w = (φ v)⁻¹ * (φ v) * ψ w := by rw [inv_mul_cancel₀ hv, one_mul]
      _ = (φ v)⁻¹ * (φ v * ψ w) := by ring
      _ = (φ v)⁻¹ * (φ w * ψ v) := by rw [← h1]
      _ = ψ v * (φ v)⁻¹ * φ w := by ring
  exact h2.symm

/-- The map sending a projectivised nonzero functional to its kernel, as a submodule of index `p`.
It is well defined on scaling classes because multiplying a functional by a nonzero scalar does
not change its kernel. -/
noncomputable def bwd (p : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module (ZMod p) V] :
    Projectivization (ZMod p) (Module.Dual (ZMod p) V) →
      {K : Submodule (ZMod p) V // K.toAddSubgroup.index = p} :=
  Projectivization.lift
    (fun φ => ⟨φ.1.ker, ker_index_eq p V φ.1 φ.2⟩)
    (by
      intro a b t ht
      have ht0 : t ≠ 0 := by
        rintro rfl
        exact a.2 (by rw [ht]; simp)
      have hker : a.1.ker = b.1.ker := by
        rw [ht, LinearMap.ker_smul b.1 t ht0]
      exact Subtype.ext hker)

/-- The map sending a submodule of index `p` to the class of any nonzero functional with that
kernel (chosen classically). -/
noncomputable def fwd (p : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    (K : {K : Submodule (ZMod p) V // K.toAddSubgroup.index = p}) :
    Projectivization (ZMod p) (Module.Dual (ZMod p) V) :=
  Projectivization.mk (ZMod p) (Classical.choose (exists_dual_ker_eq p V K.1 K.2))
    (Classical.choose_spec (exists_dual_ker_eq p V K.1 K.2)).1

/-- The submodules of a `ZMod p`-module of index `p` are in bijection with the projectivization
of the dual: a submodule of index `p` is the kernel of a nonzero linear functional, and two
functionals have the same kernel if and only if they are proportional. -/
theorem submodule_index_p_equiv_projectivization (p : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] :
    Nonempty ({K : Submodule (ZMod p) V // K.toAddSubgroup.index = p} ≃
      Projectivization (ZMod p) (Module.Dual (ZMod p) V)) := by
  refine ⟨Equiv.mk (fwd p V) (bwd p V) ?_ ?_⟩
  · intro K
    apply Subtype.ext
    simp only [fwd, bwd, Projectivization.lift_mk]
    exact (Classical.choose_spec (exists_dual_ker_eq p V K.1 K.2)).2
  · intro w
    induction w using Projectivization.ind with
    | h v hv =>
      have hspec := Classical.choose_spec (exists_dual_ker_eq p V v.ker (ker_index_eq p V v hv))
      simp only [fwd, bwd, Projectivization.lift_mk]
      apply (Projectivization.mk_eq_mk_iff' (ZMod p) _ v hspec.1 hv).mpr
      obtain ⟨c, hc⟩ := exists_smul_of_ker_eq p V v _ hv hspec.2.symm
      exact ⟨c, hc⟩

end Work.SSGRoute.PTembedding
