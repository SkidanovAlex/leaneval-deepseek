import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Reductions

open MulAction

theorem transfer_twoTransitive {G : Type} [Group G] {H L : Subgroup G}
    (h2 : MulAction.IsMultiplyPretransitive ↥L (↥L ⧸ (L ⊓ H).subgroupOf L) 2)
    (htrans : ∀ ω : G ⧸ H, ∃ l : L, (l : G) • (QuotientGroup.mk (1 : G) : G ⧸ H) = ω) :
    ∀ a b c d : G ⧸ H, a ≠ b → c ≠ d →
      ∃ l : L, (l : G) • a = c ∧ (l : G) • b = d := by
  intro a b c d hab hcd
  -- The well-definedness of the map `L/(L ⊓ H) → G/H`, `l(L ⊓ H) ↦ lH`.
  have hwell : ∀ x y : ↥L, QuotientGroup.leftRel ((L ⊓ H).subgroupOf L) x y →
      QuotientGroup.leftRel H (x : G) (y : G) := by
    intro x y hxy
    rw [QuotientGroup.leftRel_apply] at hxy ⊢
    rw [Subgroup.mem_subgroupOf] at hxy
    simpa using hxy.2
  let φ : ↥L ⧸ (L ⊓ H).subgroupOf L → G ⧸ H :=
    Quotient.map' (Subtype.val : ↥L → G) hwell
  have hφ : ∀ x : ↥L, φ (QuotientGroup.mk x) = QuotientGroup.mk (x : G) := by
    intro x
    exact Quotient.map'_mk'' (Subtype.val : ↥L → G) hwell x
  -- `φ` is injective.
  have hinj : Function.Injective φ := by
    intro p q hpq
    revert hpq
    refine Quotient.inductionOn' p (fun x => ?_)
    refine Quotient.inductionOn' q (fun y => ?_)
    intro hpq
    simp only [hφ] at hpq
    rw [QuotientGroup.eq] at hpq
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact ⟨(x⁻¹ * y).2, by simpa using hpq⟩
  -- `φ` is surjective, thanks to the transitivity hypothesis.
  have hsurj : Function.Surjective φ := by
    intro ω
    obtain ⟨l, hl⟩ := htrans ω
    refine ⟨QuotientGroup.mk l, ?_⟩
    rw [hφ l, ← hl]
    simp only [Quotient.smul_mk, smul_eq_mul, mul_one]
  have heq_mk : ∀ (l : ↥L) (y : ↥L),
      (l : G) • φ (QuotientGroup.mk y) = φ (l • QuotientGroup.mk y) := by
    intro l y
    have h1 : (l : ↥L) • QuotientGroup.mk y =
        QuotientGroup.mk (l * y) :=
      Quotient.smul_mk ((L ⊓ H).subgroupOf L) l y
    rw [h1, hφ (l * y), hφ y, Quotient.smul_mk]
    rfl
  have heq : ∀ (l : ↥L) (x : ↥L ⧸ (L ⊓ H).subgroupOf L),
      (l : G) • φ x = φ (l • x) := by
    intro l x
    refine Quotient.inductionOn' x (fun y => ?_)
    exact heq_mk l y
  -- Package `φ` as an equivalence.
  let e : ↥L ⧸ (L ⊓ H).subgroupOf L ≃ G ⧸ H := Equiv.ofBijective φ ⟨hinj, hsurj⟩
  have he : ∀ x, e x = φ x := fun x => Equiv.ofBijective_apply φ _ x
  have hee : ∀ (l : ↥L) (x : ↥L ⧸ (L ⊓ H).subgroupOf L),
      (l : G) • e x = e (l • x) := by
    intro l x
    rw [he x, he (l • x)]
    exact heq l x
  have hne1 : e.symm a ≠ e.symm b := by
    intro h
    exact hab (by rw [← e.apply_symm_apply a, ← e.apply_symm_apply b, h])
  have hne2 : e.symm c ≠ e.symm d := by
    intro h
    exact hcd (by rw [← e.apply_symm_apply c, ← e.apply_symm_apply d, h])
  obtain ⟨l, hl1, hl2⟩ :=
    (MulAction.is_two_pretransitive_iff.mp h2) hne1 hne2
  refine ⟨l, ?_, ?_⟩
  · calc (l : G) • a = (l : G) • e (e.symm a) := by rw [e.apply_symm_apply]
      _ = e (l • e.symm a) := hee l (e.symm a)
      _ = e (e.symm c) := by rw [hl1]
      _ = c := e.apply_symm_apply c
  · calc (l : G) • b = (l : G) • e (e.symm b) := by rw [e.apply_symm_apply]
      _ = e (l • e.symm b) := hee l (e.symm b)
      _ = e (e.symm d) := by rw [hl2]
      _ = d := e.apply_symm_apply d

end Work.Reductions
