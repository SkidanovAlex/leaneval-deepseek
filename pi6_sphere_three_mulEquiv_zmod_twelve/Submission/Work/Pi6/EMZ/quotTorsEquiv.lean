import Mathlib
import Submission.Work.Pi6.EMZ.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The quotient/torsion dictionary transfers along an isomorphism

Given an additive isomorphism `e : G ≃+ H` of abelian groups, everything that can be expressed in
terms of the `p`-divisibility, the `p`-torsion, the quotient `G ⧸ p·G` and the subgroup `G[p]`
transfers: `G` is `p`-divisible iff `H` is, `G` has no `p`-torsion iff `H` has none, and the
quotient by `p`-multiples is canonically isomorphic — hence of equal cardinality — on both sides.

The isomorphism of quotients is `QuotientAddGroup.congr` applied to `e` once one knows that `e`
carries `pH p G` onto `pH p H`, which is the only computational content here.
-/

namespace Work.Pi6.EMZ

noncomputable section

/-- An additive equivalence carries the subgroup of `p`-multiples onto the subgroup of
`p`-multiples. -/
theorem map_pH {G H : Type} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H) (p : ℕ) :
    AddSubgroup.map (e : G →+ H) (pH p G) = pH p H := by
  ext x
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz⟩ := mem_pH'.mp hy
    exact mem_pH'.mpr ⟨e z, by simpa [hz] using (map_nsmul e p z).symm⟩
  · intro hx
    obtain ⟨y, hy⟩ := mem_pH'.mp hx
    refine ⟨p • e.symm y, mem_pH'.mpr ⟨e.symm y, rfl⟩, ?_⟩
    show (↑e : G →+ H) (p • ⇑e.symm y) = x
    rw [map_nsmul]
    rw [← hy]
    simp

/-- `p`-divisibility transfers along an additive equivalence. -/
theorem div_eq_of_addEquiv {G H : Type} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H) (p : ℕ) :
    (∀ x : G, ∃ y : G, p • y = x) ↔ (∀ x : H, ∃ y : H, p • y = x) := by
  constructor
  · intro h x
    obtain ⟨y, hy⟩ := h (e.symm x)
    exact ⟨e y, ((map_nsmul e p y).symm.trans (congrArg (⇑e) hy)).trans
      (AddEquiv.apply_symm_apply e x)⟩
  · intro h x
    obtain ⟨y, hy⟩ := h (e x)
    exact ⟨e.symm y, ((map_nsmul e.symm p y).symm.trans (congrArg (⇑e.symm) hy)).trans
      (AddEquiv.symm_apply_apply e x)⟩

/-- `p`-torsion-freeness transfers along an additive equivalence. -/
theorem tors_free_eq_of_addEquiv {G H : Type} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H)
    (p : ℕ) : (∀ x : G, p • x = 0 → x = 0) ↔ (∀ x : H, p • x = 0 → x = 0) := by
  constructor
  · intro h x hx
    have h1 : p • e.symm x = 0 :=
      ((map_nsmul e.symm p x).symm.trans (congrArg (⇑e.symm) hx)).trans (map_zero e.symm)
    have h2 : e.symm x = 0 := h (e.symm x) h1
    calc x = (↑e : G →+ H) (⇑e.symm x) := (AddEquiv.apply_symm_apply e x).symm
      _ = (↑e : G →+ H) 0 := by rw [h2]
      _ = 0 := map_zero e
  · intro h x hx
    have h1 : p • e x = 0 :=
      ((map_nsmul e p x).symm.trans (congrArg (⇑e) hx)).trans (map_zero e)
    have h2 : e x = 0 := h (e x) h1
    calc x = (↑e.symm : H →+ G) (⇑e x) := (AddEquiv.symm_apply_apply e x).symm
      _ = (↑e.symm : H →+ G) 0 := by rw [h2]
      _ = 0 := map_zero e.symm

theorem quotTorsEquiv {G H : Type} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H) (p : ℕ) :
    ((∀ x : G, ∃ y : G, p • y = x) ↔ (∀ x : H, ∃ y : H, p • y = x)) ∧
      ((∀ x : G, p • x = 0 → x = 0) ↔ (∀ x : H, p • x = 0 → x = 0)) ∧
      (Subsingleton (G ⧸ Work.Pi6.EMZ.pH p G) ↔ Subsingleton (H ⧸ Work.Pi6.EMZ.pH p H)) ∧
      (Subsingleton (Work.Pi6.EMZ.torsP p G) ↔ Subsingleton (Work.Pi6.EMZ.torsP p H)) ∧
      Nat.card (G ⧸ Work.Pi6.EMZ.pH p G) = Nat.card (H ⧸ Work.Pi6.EMZ.pH p H) := by
  have hdiv := div_eq_of_addEquiv e p
  have htors := tors_free_eq_of_addEquiv e p
  refine ⟨hdiv, htors, ?_, ?_, ?_⟩
  · rw [subsingleton_quot_pH_iff, subsingleton_quot_pH_iff]
    exact hdiv
  · rw [subsingleton_torsP_iff, subsingleton_torsP_iff]
    exact htors
  · exact Nat.card_congr (QuotientAddGroup.congr (pH p G) (pH p H) e (map_pH e p))

end

end Work.Pi6.EMZ
