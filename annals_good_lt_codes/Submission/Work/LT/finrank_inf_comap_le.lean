import Mathlib

namespace Work.LT

/-- For arbitrary linear maps `φ i, ψ i : V → W` and a subspace `T ≤ W`, the intersection of the
`2 |ι|` preimages of `T` has codimension at most `2 |ι| · codim T` (rank-nullity applied to
`v ↦ (φ i v mod T, ψ i v mod T)`). -/
lemma finrank_inf_comap_le {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {ι : Type*} [Fintype ι]
    (φ ψ : ι → V →ₗ[ZMod 2] W) (T : Submodule (ZMod 2) W) :
    Module.finrank (ZMod 2) V ≤
      (Module.finrank (ZMod 2)
        ((⨅ i, T.comap (φ i)) ⊓ (⨅ i, T.comap (ψ i)) : Submodule (ZMod 2) V)) +
      (Fintype.card ι + Fintype.card ι) * Module.finrank (ZMod 2) (W ⧸ T) := by
  let F : V →ₗ[ZMod 2] (ι → W ⧸ T) × (ι → W ⧸ T) :=
    (LinearMap.pi (fun i => T.mkQ.comp (φ i))).prod (LinearMap.pi (fun i => T.mkQ.comp (ψ i)))
  have hker : F.ker = ((⨅ i, T.comap (φ i)) ⊓ (⨅ i, T.comap (ψ i)) : Submodule (ZMod 2) V) := by
    show ((LinearMap.pi (fun i => T.mkQ.comp (φ i))).prod
        (LinearMap.pi (fun i => T.mkQ.comp (ψ i)))).ker
      = ((⨅ i, T.comap (φ i)) ⊓ (⨅ i, T.comap (ψ i)) : Submodule (ZMod 2) V)
    ext v
    simp only [LinearMap.mem_ker, LinearMap.prod_apply, LinearMap.pi_apply, LinearMap.comp_apply,
      Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, Function.prod, Prod.mk_eq_zero,
      funext_iff, Pi.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have h1 : Module.finrank (ZMod 2) (V ⧸ F.ker) ≤
      Module.finrank (ZMod 2) ((ι → W ⧸ T) × (ι → W ⧸ T)) := by
    calc Module.finrank (ZMod 2) (V ⧸ F.ker)
        = Module.finrank (ZMod 2) F.range := (LinearMap.quotKerEquivRange F).finrank_eq
      _ ≤ Module.finrank (ZMod 2) ((ι → W ⧸ T) × (ι → W ⧸ T)) := Submodule.finrank_le F.range
  have h2 : Module.finrank (ZMod 2) ((ι → W ⧸ T) × (ι → W ⧸ T)) =
      (Fintype.card ι + Fintype.card ι) * Module.finrank (ZMod 2) (W ⧸ T) := by
    rw [Module.finrank_prod, Module.finrank_pi_fintype]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    nlinarith
  have hquot : Module.finrank (ZMod 2) V =
      Module.finrank (ZMod 2) (V ⧸ F.ker) + Module.finrank (ZMod 2) F.ker :=
    (Submodule.finrank_quotient_add_finrank F.ker).symm
  calc Module.finrank (ZMod 2) V
      = Module.finrank (ZMod 2) (V ⧸ F.ker) + Module.finrank (ZMod 2) F.ker := hquot
    _ ≤ (Fintype.card ι + Fintype.card ι) * Module.finrank (ZMod 2) (W ⧸ T)
          + Module.finrank (ZMod 2) F.ker :=
        Nat.add_le_add_right (h1.trans (le_of_eq h2)) _
    _ = Module.finrank (ZMod 2) F.ker
          + (Fintype.card ι + Fintype.card ι) * Module.finrank (ZMod 2) (W ⧸ T) :=
        Nat.add_comm _ _
    _ = (Module.finrank (ZMod 2)
          ((⨅ i, T.comap (φ i)) ⊓ (⨅ i, T.comap (ψ i)) : Submodule (ZMod 2) V)) +
        (Fintype.card ι + Fintype.card ι) * Module.finrank (ZMod 2) (W ⧸ T) := by
        rw [hker]

end Work.LT
