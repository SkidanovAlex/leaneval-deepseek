import Mathlib

namespace Work.LT

/-- The preimage under a linear endomorphism `f` of a subspace `W` contained in the range of `f` has cardinality `|ker f| * |W|`. -/
theorem gb_card_preimage_submodule {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (f : V →ₗ[ZMod 2] V) (W : Submodule (ZMod 2) V) (hW : W ≤ f.range) :
    Nat.card {a : V // f a ∈ W} = Nat.card ↥f.ker * Nat.card ↥W := by
  -- The preimage is the submodule `P = f⁻¹(W)`.
  set P : Submodule (ZMod 2) V := Submodule.comap f W with hP
  have hPmem : ∀ v, v ∈ P ↔ f v ∈ W := fun v => Submodule.mem_comap
  have h1 : Nat.card {a : V // f a ∈ W} = Nat.card ↥P := by
    rw [hP]
    rfl
  -- The restriction `g : P → W` of `f`; it is surjective because `W ≤ f.range`
  -- and its kernel is `P ⊓ ker f`.
  set g : ↥P →ₗ[ZMod 2] ↥W :=
    (f.domRestrict P).codRestrict W (fun x => by
      rw [LinearMap.domRestrict_apply]; exact (hPmem x.1).mp x.2) with hg
  have hker_eq : g.ker = Submodule.comap P.subtype f.ker := by
    rw [hg, LinearMap.ker_codRestrict, LinearMap.ker_domRestrict]
  have hrange : g.range = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro w
    obtain ⟨v, hv⟩ := hW w.2
    refine LinearMap.mem_range.mpr ⟨⟨v, ?_⟩, ?_⟩
    · rw [hPmem]; rw [hv]; exact w.2
    · apply Subtype.ext
      rw [hg, LinearMap.codRestrict_apply, LinearMap.domRestrict_apply]
      exact hv
  -- The kernel of `g` has the same cardinality as `ker f`.
  have hkercard : Nat.card ↥(Submodule.comap P.subtype f.ker) = Nat.card ↥f.ker := by
    refine Nat.card_congr ?_
    refine { toFun := fun x => ⟨x.1.1, Submodule.mem_comap.mp x.2⟩,
             invFun := fun y => ⟨⟨y.1, ?_⟩, ?_⟩,
             left_inv := ?_, right_inv := ?_ }
    · rw [hPmem, LinearMap.mem_ker.mp y.2]; exact W.zero_mem
    · exact y.2
    · intro x; rfl
    · intro y; rfl
  -- The quotient `P / ker g` has the cardinality of `W`, since `g` is surjective.
  have hquot : Nat.card (↥P ⧸ g.ker) = Nat.card ↥W := by
    calc Nat.card (↥P ⧸ g.ker) = Nat.card ↥g.range :=
          Nat.card_congr (LinearMap.quotKerEquivRange g).toEquiv
      _ = Nat.card ↥(⊤ : Submodule (ZMod 2) ↥W) := by rw [hrange]
      _ = Nat.card ↥W := Nat.card_congr (Submodule.topEquiv (R := ZMod 2) (M := ↥W)).toEquiv
  -- Assemble: `|P| = |ker g| * |P / ker g|`.
  rw [h1]
  calc Nat.card ↥P
      = Nat.card ↥(Submodule.comap P.subtype f.ker) *
          Nat.card (↥P ⧸ Submodule.comap P.subtype f.ker) :=
        Submodule.card_eq_card_quotient_mul_card _
    _ = Nat.card ↥f.ker * Nat.card (↥P ⧸ Submodule.comap P.subtype f.ker) := by rw [hkercard]
    _ = Nat.card ↥f.ker * Nat.card ↥W := by rw [← hker_eq, hquot]

end Work.LT
