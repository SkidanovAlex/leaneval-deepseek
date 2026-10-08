import Mathlib
import Submission.Work.ThmG.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `D = H ∩ Hᵗ ≠ 1` unless `G` is a Zassenhaus group

Peterfalvi II p. 236: for a split rank-one datum `H = Q ⋊ D`, `t ∉ H`, the pointwise stabiliser
of three distinct points of `G ⧸ H` is trivial (i.e. `G` is a Zassenhaus group on `G ⧸ H`)
exactly when `V = C_D(t) = 1`.  Since `V ≤ D = H ∩ Hᵗ`, the implication
`D = 1 → G` Zassenhaus holds, hence its contrapositive:

`¬ IsZassenhaus H → twoPoint H t ≠ ⊥`.

The only structural input needed is the 2-transitivity of `G` on `G ⧸ H` (a field of
`IsSplitRankOne`): if `D = 1` then the pointwise stabiliser of any two distinct points, being
`G`-conjugate to `D`, is trivial, and hence so is that of any three distinct points.
-/

namespace Work.ThmG

/-- The stabiliser in `G` of the point `tH` of `G ⧸ H` is `Hᵗ = H.map (MulAut.conj t)`. -/
lemma stabilizer_quotient_conj {G : Type*} [Group G] (H : Subgroup G) (t : G) :
    MulAction.stabilizer G ((t : G) : G ⧸ H) = Submission.Blueprint.conj t H := by
  rw [Submission.Blueprint.conj]
  ext y
  rw [MulAction.mem_stabilizer_iff, MulAction.Quotient.smul_coe, QuotientGroup.eq]
  constructor
  · intro hh
    rw [Subgroup.mem_map]
    refine ⟨t⁻¹ * y * t, ?_, ?_⟩
    · have h' : (t⁻¹ * y * t)⁻¹ ∈ H := by simpa [mul_assoc] using hh
      simpa using inv_mem h'
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨hh, hhh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using inv_mem hhh

theorem twoPoint_ne_bot_of_not_zassenhaus {G : Type*} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G} (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hz : ¬ Submission.Blueprint.IsZassenhaus H) :
    Submission.Blueprint.twoPoint H t ≠ ⊥ := by
  intro hbot
  apply hz
  intro a b c hab hac hbc g hga hgb hgc
  -- the two points `H` and `tH` of `G ⧸ H`; they are distinct because `t ∉ H`
  set ω : G ⧸ H := ((1 : G) : G ⧸ H) with hωdef
  set τ : G ⧸ H := ((t : G) : G ⧸ H) with hτdef
  have hωτ : ω ≠ τ := by
    intro heq
    refine h.not_mem ?_
    have hh := QuotientGroup.eq.mp heq
    simpa [hωdef, hτdef] using hh
  -- 2-transitivity moves the pair `(a, b)` to `(H, tH)`
  have h2 : ∀ {p q r s : G ⧸ H}, p ≠ q → r ≠ s → ∃ x : G, x • p = r ∧ x • q = s :=
    MulAction.is_two_pretransitive_iff.mp h.twoTransitive
  obtain ⟨x, hx1, hx2⟩ : ∃ x : G, x • a = ω ∧ x • b = τ := h2 hab hωτ
  have hxa : x⁻¹ • ω = a := by rw [← hx1, ← mul_smul, inv_mul_cancel, one_smul]
  have hxb : x⁻¹ • τ = b := by rw [← hx2, ← mul_smul, inv_mul_cancel, one_smul]
  -- `x g x⁻¹` fixes both `H` and `tH`
  have hyω : (x * g * x⁻¹) • ω = ω := by
    rw [mul_smul, mul_smul, hxa, hga, hx1]
  have hyτ : (x * g * x⁻¹) • τ = τ := by
    rw [mul_smul, mul_smul, hxb, hgb, hx2]
  -- hence it lies in the pointwise stabiliser `H ∩ Hᵗ = twoPoint H t`
  have hmem : x * g * x⁻¹ ∈ Submission.Blueprint.twoPoint H t := by
    rw [Submission.Blueprint.twoPoint, Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [← MulAction.stabilizer_quotient H, MulAction.mem_stabilizer_iff]
      exact hyω
    · have hstab : MulAction.stabilizer G τ = Submission.Blueprint.conj t H := by
        rw [hτdef]; exact stabilizer_quotient_conj H t
      rw [← hstab, MulAction.mem_stabilizer_iff]
      exact hyτ
  -- `D = 1` kills it, so `g = 1`
  have hbot' : x * g * x⁻¹ ∈ (⊥ : Subgroup G) := hbot ▸ hmem
  have hg1 : x * g * x⁻¹ = 1 := Subgroup.mem_bot.mp hbot'
  have hkey : x⁻¹ * (x * g * x⁻¹) * x = g := by group
  rw [hg1, mul_one] at hkey
  rw [inv_mul_cancel] at hkey
  exact hkey.symm

end Work.ThmG
