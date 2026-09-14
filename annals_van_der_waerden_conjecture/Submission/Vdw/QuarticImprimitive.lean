import Mathlib
import Submission.Vdw.PrimitiveCase
import Submission.Vdw.QuarticResolvent
import Submission.Commons.GroupTheory.GroupAction.block_pair_of_not_preprimitive_four

open Polynomial

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The `n = 4` imprimitive chapter: a bounded integer root of the cubic resolvent

Bhargava, *Galois groups of random integer polynomials and van der Waerden's
Conjecture* (Annals of Math. **201** (2025)), Theorem 1, final case.

For a monic quartic `f` whose Galois group is a *transitive imprimitive*
subgroup of `S₄` (equivalently, by Kappe–Warren, whose cubic resolvent
`resolventCubic` — see `Submission/Vdw/QuarticResolvent.lean` — has a rational
root), the counting bound `#ImprimitiveBad 4 H = O(H³)` follows from
Chow–Dietmann's enumeration of quartics with a rational resolvent root.

This module formalizes the **algebraic** half: an imprimitive quartic in the box
has an *integer* root of its resolvent, bounded by `4H`.  The classical
argument:

* a transitive imprimitive subgroup of `S₄` stabilizes a partition of the four
  roots into two pairs (`Commons.GroupTheory.GroupAction.block_pair_of_not_preprimitive_four`);
* the two products of the two pairs are then permuted (possibly exchanged) by
  every Galois element, so `β = y₁y₂ + y₃y₄` is fixed by `Gal`;
* hence `β ∈ ℚ`, and `β` is integral over `ℤ` (a sum of products of roots of the
  monic integer polynomial `f`), so `β ∈ ℤ`;
* expanding `f = (X² - A X + p)(X² - B X + q)` along the Galois-stable pairing
  and applying the pairing identity (`resolventCubic_eval_pairing`) shows that
  this integer is a root of the resolvent;
* finally, an integer root `z` of the monic cubic `resolventCubic a b c d` with
  `|a|, |b|, |c|, |d| ≤ H` satisfies `|z| ≤ 4H` (the leading term dominates).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace Submission.Vdw

noncomputable section

/-! ## Generic polynomial lemmas -/

/-- A product of `(X - C (x i))` over a finset of *distinct* roots of `q` divides `q`. -/
theorem prod_X_sub_C_dvd_of_distinct_roots {R : Type*} [CommRing R] [IsDomain R] {ι : Type*}
    (x : ι → R) : ∀ (s : Finset ι) (q : R[X]), (∀ i ∈ s, q.eval (x i) = 0) →
      (∀ i ∈ s, ∀ j ∈ s, x i = x j → i = j) → (∏ i ∈ s, (X - C (x i))) ∣ q := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro q _ _; simp
  | insert a s ha ih =>
    intro q hroot hinj
    rw [Finset.prod_insert ha]
    have hX : (X - C (x a)) ∣ q := by
      rw [dvd_iff_isRoot, Polynomial.IsRoot]
      exact hroot a (Finset.mem_insert_self a s)
    obtain ⟨q', rfl⟩ := hX
    refine mul_dvd_mul_left _ (ih q' ?_ ?_)
    · intro i hi
      have hq : ((X - C (x a)) * q').eval (x i) = 0 := hroot i (Finset.mem_insert_of_mem hi)
      rw [eval_mul, eval_sub, eval_X, eval_C] at hq
      rcases mul_eq_zero.mp hq with h | h
      · exact absurd (hinj i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self a s)
          (sub_eq_zero.mp h) ▸ hi) ha
      · exact h
    · intro i hi j hj hij
      exact hinj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij

/-- Expansion of a product of two monic quadratics. -/
theorem quad_mul_quad {R : Type*} [CommRing R] (A B p q : R) :
    (X ^ 2 - C A * X ^ 1 + C p) * (X ^ 2 - C B * X ^ 1 + C q)
      = X ^ 4 - C (A + B) * X ^ 3 + C (A * B + p + q) * X ^ 2
        - C (p * B + q * A) * X ^ 1 + C (p * q) := by
  simp only [C_add, C_mul]
  ring

/-- Conjugation of permutations is compatible with composition of the
equivalences. -/
theorem permCongrHom_trans {α β γ : Type*} (e : α ≃ β) (f : β ≃ γ) :
    (permCongrHom f).comp (permCongrHom e) = permCongrHom (e.trans f) := by
  ext σ x
  simp [permCongrHom, Equiv.permCongr_apply, Equiv.trans_apply]

/-- Expansion of a product of two factors `X - C u`, `X - C v`. -/
theorem linear_mul_linear {R : Type*} [CommRing R] (u v : R) :
    (X - C u) * (X - C v) = X ^ 2 - C (u + v) * X ^ 1 + C (u * v) := by
  simp only [C_add, C_mul]
  ring

end

end Submission.Vdw

namespace Submission.Vdw

noncomputable section

/-- **Pairing data of an imprimitive quartic.**  For a monic integer quartic `f` of degree `4` that is
irreducible over `ℚ` with imprimitive Galois group, the four roots `x₁ x₂ x₃ x₄` in the splitting
field can be paired so that `f` factors as `(X² - A X + p)(X² - B X + q)` with `A = x₁+x₂`,
`B = x₃+x₄`, `p = x₁x₂`, `q = x₃x₄`, and the resolvent root `β = p + q` is fixed by `Gal`, hence
rational and integral. -/
theorem quartic_pairing_data (f : ℤ[X]) (hirr : Irreducible (f.map φℚ)) (hm : f.Monic)
    (hdeg : f.natDegree = 4) (hnotprim : ¬ galPrimitive f hirr) :
    ∃ A B p q : (f.map φℚ).SplittingField,
      (((f.coeff 3 : ℤ)) : (f.map φℚ).SplittingField) = -(A + B) ∧
      (((f.coeff 2 : ℤ)) : (f.map φℚ).SplittingField) = A * B + p + q ∧
      (((f.coeff 1 : ℤ)) : (f.map φℚ).SplittingField) = -(p * B + q * A) ∧
      (((f.coeff 0 : ℤ)) : (f.map φℚ).SplittingField) = p * q ∧
      IsIntegral ℤ (p + q) ∧ ∃ e : ℚ, algebraMap ℚ (f.map φℚ).SplittingField e = p + q := by
  classical
  haveI : Fact (Irreducible (f.map φℚ)) := ⟨hirr⟩
  have hsep : (f.map φℚ).Separable := separable_of_irreducible_rat hirr
  have hdegP : (f.map φℚ).natDegree = 4 := by
    rw [monic_natDegree_map_rat f hm, hdeg]
  haveI hFact : Fact ((f.map φℚ).map (algebraMap ℚ ((f.map φℚ).SplittingField))).Splits :=
    ⟨Polynomial.SplittingField.splits (f.map φℚ)⟩
  -- the identification of the four roots with `Fin 4`
  let e : (f.map φℚ).rootSet ((f.map φℚ).SplittingField) ≃ Fin ((f.map φℚ).natDegree) :=
    rootFinEquiv (f.map φℚ) hsep
  let par : (f.map φℚ).rootSet ((f.map φℚ).SplittingField) ≃
      (f.map φℚ).rootSet ((f.map φℚ).SplittingField) :=
    Polynomial.Gal.rootsEquivRoots (f.map φℚ) ((f.map φℚ).SplittingField)
  let c : (f.map φℚ).rootSet ((f.map φℚ).SplittingField) ≃ Fin ((f.map φℚ).natDegree) :=
    par.trans e
  -- the immprimitivity hypothesis yields a stable `2 + 2` partition of the index set
  have hcard : Nat.card (Fin ((f.map φℚ).natDegree)) = 4 := by
    rw [Nat.card_fin, hdegP]
  haveI : MulAction.IsPretransitive ((irrGalFinHom f).range) (Fin ((f.map φℚ).natDegree)) :=
    irrGalFinHom_pretransitive f
  obtain ⟨B, C, _hBblk, _hCblk, hBcard, hCcard, hBCdisj, hBCuniv, hsplit⟩ :=
    Commons.GroupTheory.GroupAction.block_pair_of_not_preprimitive_four
      (G := ((irrGalFinHom f).range)) hcard hnotprim
  -- the plain (application) action of `Gal` on the roots
  let Φ : (f.map φℚ).Gal →*
      Equiv.Perm ((f.map φℚ).rootSet ((f.map φℚ).SplittingField)) :=
    @MulAction.toPermHom (f.map φℚ).Gal _ _ (Polynomial.Gal.galActionAux (f.map φℚ))
  have hΦ : ∀ σ, Φ σ = auxRootPerm (f.map φℚ) σ := fun σ => rfl
  -- the canonical action is the plain action conjugated by `c`
  have hkey : ∀ σ : (f.map φℚ).Gal, irrGalFinHom f σ = c.permCongr (Φ σ) := by
    intro σ
    have h2 : galRootPerm (f.map φℚ) σ = par.permCongr (Φ σ) := by
      rw [galRootPerm_eq_conj (f.map φℚ) hFact σ]
      rfl
    have h3 : (permCongrHom e) ((permCongrHom par) (Φ σ)) = (permCongrHom (par.trans e)) (Φ σ) := by
      rw [← MonoidHom.comp_apply, permCongrHom_trans]
    calc irrGalFinHom f σ
        = (permCongrHom e) (galRootPerm (f.map φℚ) σ) := rfl
      _ = (permCongrHom e) (par.permCongr (Φ σ)) := by rw [h2]
      _ = (permCongrHom e) ((permCongrHom par) (Φ σ)) := rfl
      _ = (permCongrHom (par.trans e)) (Φ σ) := h3
      _ = c.permCongr (Φ σ) := rfl
  -- the corresponding Galois-stable pairing of the roots
  let B' : Set ((f.map φℚ).rootSet ((f.map φℚ).SplittingField)) := c ⁻¹' B
  let C' : Set ((f.map φℚ).rootSet ((f.map φℚ).SplittingField)) := c ⁻¹' C
  have hstab : ∀ σ, (∀ y, y ∈ B' ↔ Φ σ y ∈ B') ∨ (∀ y, y ∈ B' ↔ Φ σ y ∈ C') := by
    intro σ
    rcases hsplit ⟨irrGalFinHom f σ, ⟨σ, rfl⟩⟩ with h | h
    · left
      intro y
      have hy := h (c y)
      simp only [MulAction.subgroup_smul_def, Equiv.Perm.smul_def] at hy
      rw [hkey σ] at hy
      have hcy : (c.permCongr (Φ σ)) (c y) = c (Φ σ y) := by
        rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
      rw [hcy] at hy
      constructor
      · intro h1
        show c (Φ σ y) ∈ B
        exact hy.mp (show c y ∈ B from h1)
      · intro h1
        show c y ∈ B
        exact hy.mpr (show c (Φ σ y) ∈ B from h1)
    · right
      intro y
      have hy := h (c y)
      simp only [MulAction.subgroup_smul_def, Equiv.Perm.smul_def] at hy
      rw [hkey σ] at hy
      have hcy : (c.permCongr (Φ σ)) (c y) = c (Φ σ y) := by
        rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
      rw [hcy] at hy
      constructor
      · intro h1
        show c (Φ σ y) ∈ C
        exact hy.mp (show c y ∈ B from h1)
      · intro h1
        show c y ∈ B
        exact hy.mpr (show c (Φ σ y) ∈ C from h1)
  -- the two-element blocks, transported to the roots
  have hB' : B' = c.symm '' B := by
    ext y
    constructor
    · intro hy
      exact ⟨c y, show c y ∈ B from hy, c.symm_apply_apply y⟩
    · rintro ⟨x, hx, rfl⟩
      show c (c.symm x) ∈ B
      rwa [c.apply_symm_apply]
  have hC' : C' = c.symm '' C := by
    ext y
    constructor
    · intro hy
      exact ⟨c y, show c y ∈ C from hy, c.symm_apply_apply y⟩
    · rintro ⟨x, hx, rfl⟩
      show c (c.symm x) ∈ C
      rwa [c.apply_symm_apply]
  have hB'card : B'.ncard = 2 := by
    rw [hB', Set.ncard_image_of_injective _ c.symm.injective, hBcard]
  have hC'card : C'.ncard = 2 := by
    rw [hC', Set.ncard_image_of_injective _ c.symm.injective, hCcard]
  have hB'C'disj : Disjoint B' C' := by
    rw [Set.disjoint_left]
    intro y hyB hyC
    exact Set.disjoint_left.mp hBCdisj (show c y ∈ B from hyB) (show c y ∈ C from hyC)
  have hB'C'univ : B' ∪ C' = Set.univ := by
    show c ⁻¹' B ∪ c ⁻¹' C = Set.univ
    rw [← Set.preimage_union, hBCuniv, Set.preimage_univ]
  obtain ⟨x₁, x₂, hx1, hx2, hx12, hcovB⟩ := set_pair_of_ncard_two B' hB'card
  obtain ⟨x₃, x₄, hx3, hx4, hx34, hcovC⟩ := set_pair_of_ncard_two C' hC'card
  have hx3B : x₃ ∉ B' := fun h => (Set.disjoint_left.mp hB'C'disj h hx3).elim
  have hx4B : x₄ ∉ B' := fun h => (Set.disjoint_left.mp hB'C'disj h hx4).elim
  -- the resolvent root
  set β : (f.map φℚ).SplittingField :=
    ((x₁ : (f.map φℚ).SplittingField)) * ((x₂ : (f.map φℚ).SplittingField))
      + ((x₃ : (f.map φℚ).SplittingField)) * ((x₄ : (f.map φℚ).SplittingField)) with hβdef
  -- the plain action applies the field automorphism to the roots
  have hΦval (σ : (f.map φℚ).Gal)
      (y : (f.map φℚ).rootSet ((f.map φℚ).SplittingField)) :
      ((Φ σ y : (f.map φℚ).rootSet ((f.map φℚ).SplittingField)) :
        (f.map φℚ).SplittingField) = σ ((y : _) : (f.map φℚ).SplittingField) := by
    rw [hΦ]
    exact auxRootPerm_apply_val (f.map φℚ) σ y
  -- the two roots of a block are permuted (or exchanged) by the plain action
  have hpr (σ : (f.map φℚ).Gal) (h : ∀ y, y ∈ B' ↔ Φ σ y ∈ B') :
      ((Φ σ x₁ : (f.map φℚ).rootSet _) : (f.map φℚ).SplittingField)
          * ((Φ σ x₂ : (f.map φℚ).rootSet _) : (f.map φℚ).SplittingField)
        + ((Φ σ x₃ : (f.map φℚ).rootSet _) : (f.map φℚ).SplittingField)
          * ((Φ σ x₄ : (f.map φℚ).rootSet _) : (f.map φℚ).SplittingField)
        = (x₁ : (f.map φℚ).SplittingField) * (x₂ : (f.map φℚ).SplittingField)
          + (x₃ : (f.map φℚ).SplittingField) * (x₄ : (f.map φℚ).SplittingField) := by
    have hx1' : Φ σ x₁ ∈ B' := (h x₁).mp hx1
    have hx2' : Φ σ x₂ ∈ B' := (h x₂).mp hx2
    have hx3' : Φ σ x₃ ∈ C' := by
      have hmem : Φ σ x₃ ∈ B' ∪ C' := by rw [hB'C'univ]; exact Set.mem_univ _
      rw [Set.mem_union] at hmem
      rcases hmem with hb | hc
      · exact absurd ((h x₃).mpr hb) hx3B
      · exact hc
    have hx4' : Φ σ x₄ ∈ C' := by
      have hmem : Φ σ x₄ ∈ B' ∪ C' := by rw [hB'C'univ]; exact Set.mem_univ _
      rw [Set.mem_union] at hmem
      rcases hmem with hb | hc
      · exact absurd ((h x₄).mpr hb) hx4B
      · exact hc
    have hpr12 : ((Φ σ x₁ : (f.map φℚ).rootSet _) : (f.map φℚ).SplittingField)
        * ((Φ σ x₂ : (f.map φℚ).rootSet _) : (f.map φℚ).SplittingField)
        = (x₁ : (f.map φℚ).SplittingField) * (x₂ : (f.map φℚ).SplittingField) := by
      rcases hcovB _ hx1' with h1 | h1 <;> rcases hcovB _ hx2' with h2 | h2
      · exact absurd ((Φ σ).injective (by rw [h1, h2])) hx12
      · rw [h1, h2]
      · rw [h1, h2]; exact mul_comm _ _
      · exact absurd ((Φ σ).injective (by rw [h1, h2])) hx12
    have hpr34 : ((Φ σ x₃ : (f.map φℚ).rootSet _) : (f.map φℚ).SplittingField)
        * ((Φ σ x₄ : (f.map φℚ).rootSet _) : (f.map φℚ).SplittingField)
        = (x₃ : (f.map φℚ).SplittingField) * (x₄ : (f.map φℚ).SplittingField) := by
      rcases hcovC _ hx3' with h1 | h1 <;> rcases hcovC _ hx4' with h2 | h2
      · exact absurd ((Φ σ).injective (by rw [h1, h2])) hx34
      · rw [h1, h2]
      · rw [h1, h2]; exact mul_comm _ _
      · exact absurd ((Φ σ).injective (by rw [h1, h2])) hx34
    rw [hpr12, hpr34]
  have hsw (σ : (f.map φℚ).Gal) (h : ∀ y, y ∈ B' ↔ Φ σ y ∈ C') :
      ((Φ σ x₁ : (f.map φℚ).rootSet _) : (f.map φℚ).SplittingField)
          * ((Φ σ x₂ : (f.map φℚ).rootSet _) : (f.map φℚ).SplittingField)
        + ((Φ σ x₃ : (f.map φℚ).rootSet _) : (f.map φℚ).SplittingField)
          * ((Φ σ x₄ : (f.map φℚ).rootSet _) : (f.map φℚ).SplittingField)
        = (x₁ : (f.map φℚ).SplittingField) * (x₂ : (f.map φℚ).SplittingField)
          + (x₃ : (f.map φℚ).SplittingField) * (x₄ : (f.map φℚ).SplittingField) := by
    have hx1' : Φ σ x₁ ∈ C' := (h x₁).mp hx1
    have hx2' : Φ σ x₂ ∈ C' := (h x₂).mp hx2
    have hx3' : Φ σ x₃ ∈ B' := by
      have hmem : Φ σ x₃ ∈ B' ∪ C' := by rw [hB'C'univ]; exact Set.mem_univ _
      rw [Set.mem_union] at hmem
      rcases hmem with hb | hc
      · exact hb
      · exact absurd ((h x₃).mpr hc) hx3B
    have hx4' : Φ σ x₄ ∈ B' := by
      have hmem : Φ σ x₄ ∈ B' ∪ C' := by rw [hB'C'univ]; exact Set.mem_univ _
      rw [Set.mem_union] at hmem
      rcases hmem with hb | hc
      · exact hb
      · exact absurd ((h x₄).mpr hc) hx4B
    have hpr12 : ((Φ σ x₁ : (f.map φℚ).rootSet _) : (f.map φℚ).SplittingField)
        * ((Φ σ x₂ : (f.map φℚ).rootSet _) : (f.map φℚ).SplittingField)
        = (x₃ : (f.map φℚ).SplittingField) * (x₄ : (f.map φℚ).SplittingField) := by
      rcases hcovC _ hx1' with h1 | h1 <;> rcases hcovC _ hx2' with h2 | h2
      · exact absurd ((Φ σ).injective (by rw [h1, h2])) hx12
      · rw [h1, h2]
      · rw [h1, h2]; exact mul_comm _ _
      · exact absurd ((Φ σ).injective (by rw [h1, h2])) hx12
    have hpr34 : ((Φ σ x₃ : (f.map φℚ).rootSet _) : (f.map φℚ).SplittingField)
        * ((Φ σ x₄ : (f.map φℚ).rootSet _) : (f.map φℚ).SplittingField)
        = (x₁ : (f.map φℚ).SplittingField) * (x₂ : (f.map φℚ).SplittingField) := by
      rcases hcovB _ hx3' with h1 | h1 <;> rcases hcovB _ hx4' with h2 | h2
      · exact absurd ((Φ σ).injective (by rw [h1, h2])) hx34
      · rw [h1, h2]
      · rw [h1, h2]; exact mul_comm _ _
      · exact absurd ((Φ σ).injective (by rw [h1, h2])) hx34
    rw [hpr12, hpr34]; ring
  have hfix : ∀ σ : (f.map φℚ).Gal, σ β = β := by
    intro σ
    have hb : β = (x₁ : (f.map φℚ).SplittingField) * (x₂ : (f.map φℚ).SplittingField)
        + (x₃ : (f.map φℚ).SplittingField) * (x₄ : (f.map φℚ).SplittingField) := hβdef
    rcases hstab σ with h | h
    · rw [hb, map_add, map_mul, map_mul, ← hΦval σ x₁, ← hΦval σ x₂, ← hΦval σ x₃, ← hΦval σ x₄]
      exact hpr σ h
    · rw [hb, map_add, map_mul, map_mul, ← hΦval σ x₁, ← hΦval σ x₂, ← hΦval σ x₃, ← hΦval σ x₄]
      exact hsw σ h
  -- `β` is rational (fixed by the full Galois group)
  haveI hsplit : IsSplittingField ℚ ((f.map φℚ).SplittingField) (f.map φℚ) :=
    IsSplittingField.splittingField (f.map φℚ)
  haveI : IsGalois ℚ ((f.map φℚ).SplittingField) :=
    IsGalois.of_separable_splitting_field (p := f.map φℚ) hsep
  have hβmem : β ∈ (⊥ : IntermediateField ℚ ((f.map φℚ).SplittingField)) :=
    (IsGalois.mem_bot_iff_fixed β).mpr hfix
  have hβrat : ∃ e : ℚ, algebraMap ℚ ((f.map φℚ).SplittingField) e = β := by
    rcases IntermediateField.mem_bot.mp hβmem with ⟨e, he⟩
    exact ⟨e, he⟩
  -- `β` is integral over `ℤ`
  have hint : ∀ y : (f.map φℚ).rootSet ((f.map φℚ).SplittingField),
      IsIntegral ℤ ((y : (f.map φℚ).rootSet _) : (f.map φℚ).SplittingField) := by
    intro y
    refine ⟨f, hm, ?_⟩
    have hy : (aeval (((y : (f.map φℚ).rootSet _)) : (f.map φℚ).SplittingField))
        (f.map (algebraMap ℤ ℚ)) = 0 := by
      simpa only [φℚ] using (Polynomial.mem_rootSet.mp y.2).2
    rw [Polynomial.aeval_map_algebraMap (R := ℤ) (A := ℚ)
      (((y : (f.map φℚ).rootSet _)) : (f.map φℚ).SplittingField) f] at hy
    exact hy
  have hβint : IsIntegral ℤ β := by
    rw [hβdef]
    exact ((hint x₁).mul (hint x₂)).add ((hint x₃).mul (hint x₄))
  -- the four roots are pairwise distinct
  have hx13 : x₁ ≠ x₃ := fun h => hx3B (h ▸ hx1)
  have hx14 : x₁ ≠ x₄ := fun h => hx4B (h ▸ hx1)
  have hx23 : x₂ ≠ x₃ := fun h => hx3B (h ▸ hx2)
  have hx24 : x₂ ≠ x₄ := fun h => hx4B (h ▸ hx2)
  -- the squarefree product of the four linear factors divides `f`
  have hroot : ∀ y : (f.map φℚ).rootSet ((f.map φℚ).SplittingField),
      ((f.map φℚ).map (algebraMap ℚ ((f.map φℚ).SplittingField))).eval
        ((y : (f.map φℚ).rootSet _) : (f.map φℚ).SplittingField) = 0 := by
    intro y
    have hy : (aeval (((y : (f.map φℚ).rootSet _)) : (f.map φℚ).SplittingField))
        (f.map φℚ) = 0 := (Polynomial.mem_rootSet.mp y.2).2
    rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at hy
  have hQdvd : ((X - Polynomial.C ((x₁ : (f.map φℚ).SplittingField)))
        * (X - Polynomial.C ((x₂ : (f.map φℚ).SplittingField)))
        * ((X - Polynomial.C ((x₃ : (f.map φℚ).SplittingField)))
          * (X - Polynomial.C ((x₄ : (f.map φℚ).SplittingField)))))
      ∣ ((f.map φℚ).map (algebraMap ℚ ((f.map φℚ).SplittingField))) := by
    have h := prod_X_sub_C_dvd_of_distinct_roots
      (R := (f.map φℚ).SplittingField)
      (fun y : (f.map φℚ).rootSet ((f.map φℚ).SplittingField) =>
        ((y : (f.map φℚ).rootSet _) : (f.map φℚ).SplittingField))
      ({x₁, x₂, x₃, x₄} : Finset ((f.map φℚ).rootSet ((f.map φℚ).SplittingField)))
      ((f.map φℚ).map (algebraMap ℚ ((f.map φℚ).SplittingField)))
      (fun y _ => hroot y) (fun y _ z _ hyz => Subtype.ext hyz)
    have hsplit4 : ({x₁, x₂, x₃, x₄} : Finset ((f.map φℚ).rootSet _))
        = ({x₁, x₂} : Finset _) ∪ ({x₃, x₄} : Finset _) := by
      ext y
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
      tauto
    have hdisj : Disjoint ({x₁, x₂} : Finset ((f.map φℚ).rootSet _))
        ({x₃, x₄} : Finset _) := by
      rw [Finset.disjoint_left]
      intro y hy hy'
      rw [Finset.mem_insert, Finset.mem_singleton] at hy hy'
      rcases hy with rfl | rfl <;> rcases hy' with h | h
      · exact hx13 h
      · exact hx14 h
      · exact hx23 h
      · exact hx24 h
    rw [hsplit4, Finset.prod_union hdisj, Finset.prod_pair hx12, Finset.prod_pair hx34] at h
    exact h
  -- the two quadratic factors of the Galois-stable pairing
  set A : (f.map φℚ).SplittingField := (x₁ : (f.map φℚ).SplittingField)
    + (x₂ : (f.map φℚ).SplittingField) with hA
  set B : (f.map φℚ).SplittingField := (x₃ : (f.map φℚ).SplittingField)
    + (x₄ : (f.map φℚ).SplittingField) with hB
  set p : (f.map φℚ).SplittingField := (x₁ : (f.map φℚ).SplittingField)
    * (x₂ : (f.map φℚ).SplittingField) with hp
  set q : (f.map φℚ).SplittingField := (x₃ : (f.map φℚ).SplittingField)
    * (x₄ : (f.map φℚ).SplittingField) with hq
  have hQmonic : ((X - Polynomial.C ((x₁ : (f.map φℚ).SplittingField)))
      * (X - Polynomial.C ((x₂ : (f.map φℚ).SplittingField)))
      * ((X - Polynomial.C ((x₃ : (f.map φℚ).SplittingField)))
        * (X - Polynomial.C ((x₄ : (f.map φℚ).SplittingField))))).Monic :=
    Monic.mul (Monic.mul (monic_X_sub_C _) (monic_X_sub_C _))
      (Monic.mul (monic_X_sub_C _) (monic_X_sub_C _))
  have hPmonic : ((f.map φℚ).map (algebraMap ℚ ((f.map φℚ).SplittingField))).Monic :=
    (hm.map φℚ).map (algebraMap ℚ _)
  have hQdeg : ((X - Polynomial.C ((x₁ : (f.map φℚ).SplittingField)))
      * (X - Polynomial.C ((x₂ : (f.map φℚ).SplittingField)))
      * ((X - Polynomial.C ((x₃ : (f.map φℚ).SplittingField)))
        * (X - Polynomial.C ((x₄ : (f.map φℚ).SplittingField))))).natDegree = 4 := by
    rw [Monic.natDegree_mul (Monic.mul (monic_X_sub_C _) (monic_X_sub_C _))
        (Monic.mul (monic_X_sub_C _) (monic_X_sub_C _)),
      Monic.natDegree_mul (monic_X_sub_C _) (monic_X_sub_C _),
      Monic.natDegree_mul (monic_X_sub_C _) (monic_X_sub_C _), natDegree_X_sub_C]
    norm_num
  have hPdeg : ((f.map φℚ).map (algebraMap ℚ ((f.map φℚ).SplittingField))).natDegree = 4 := by
    rw [Polynomial.Monic.natDegree_map (hm.map φℚ), hdegP]
  have hfac : ((f.map φℚ).map (algebraMap ℚ ((f.map φℚ).SplittingField)))
      = (X - Polynomial.C ((x₁ : (f.map φℚ).SplittingField)))
        * (X - Polynomial.C ((x₂ : (f.map φℚ).SplittingField)))
        * ((X - Polynomial.C ((x₃ : (f.map φℚ).SplittingField)))
          * (X - Polynomial.C ((x₄ : (f.map φℚ).SplittingField)))) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le hQmonic hPmonic hQdvd (by rw [hPdeg, hQdeg])
  have hfac2 : ((f.map φℚ).map (algebraMap ℚ ((f.map φℚ).SplittingField)))
      = (X ^ 2 - Polynomial.C A * X ^ 1 + Polynomial.C p)
        * (X ^ 2 - Polynomial.C B * X ^ 1 + Polynomial.C q) := by
    rw [hfac, linear_mul_linear, linear_mul_linear, hA, hB, hp, hq]
  have hcoeff {k : ℕ} : (((f.map φℚ).map (algebraMap ℚ ((f.map φℚ).SplittingField))).coeff k)
      = (((f.coeff k : ℤ)) : (f.map φℚ).SplittingField) := by
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    exact (IsScalarTower.algebraMap_apply ℤ ℚ ((f.map φℚ).SplittingField) (f.coeff k)).symm
  have hc3 : (((f.coeff 3 : ℤ)) : (f.map φℚ).SplittingField) = -(A + B) := by
    rw [← hcoeff, hfac2, quad_mul_quad]
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C]
    norm_num
  have hc2 : (((f.coeff 2 : ℤ)) : (f.map φℚ).SplittingField) = A * B + p + q := by
    rw [← hcoeff, hfac2, quad_mul_quad]
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C]
    norm_num
  have hc1 : (((f.coeff 1 : ℤ)) : (f.map φℚ).SplittingField) = -(p * B + q * A) := by
    rw [← hcoeff, hfac2, quad_mul_quad]
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C]
    norm_num
  have hc0 : (((f.coeff 0 : ℤ)) : (f.map φℚ).SplittingField) = p * q := by
    rw [← hcoeff, hfac2, quad_mul_quad]
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C]
    norm_num
  have hpq : p + q = β := by
    rw [hp, hq]
  refine ⟨A, B, p, q, hc3, hc2, hc1, hc0, ?_, ?_⟩
  · rw [hpq]; exact hβint
  · rcases hβrat with ⟨e, he⟩
    exact ⟨e, by rw [hpq]; exact he⟩

/-- **Root bound for the resolvent.**  A rational root of the cubic resolvent of a monic quartic
whose coefficients are bounded by `H` in absolute value is bounded by `4H`. -/
theorem resolventCubic_root_abs_le (H : ℕ) (a b c d z : ℚ)
    (ha : |a| ≤ (H : ℚ)) (hb : |b| ≤ (H : ℚ)) (hc : |c| ≤ (H : ℚ)) (hd : |d| ≤ (H : ℚ))
    (hz : (resolventCubic a b c d).eval z = 0) : |z| ≤ 4 * (H : ℚ) := by
  by_contra hcon
  push_neg at hcon
  have hHnn : (0 : ℚ) ≤ (H : ℚ) := Nat.cast_nonneg H
  have hz0 : 0 < |z| := by linarith
  have hHlt : (H : ℚ) < |z| / 4 := by linarith
  have hz' : z ^ 3 - b * z ^ 2 + (a * c - 4 * d) * z - (a ^ 2 * d - 4 * b * d + c ^ 2) = 0 := by
    simpa [resolventCubic, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] using hz
  have hkey : z ^ 2 * (z - b) = (a ^ 2 * d - 4 * b * d + c ^ 2) - (a * c - 4 * d) * z := by
    have h : z ^ 3 - b * z ^ 2 = (a ^ 2 * d - 4 * b * d + c ^ 2) - (a * c - 4 * d) * z := by
      linarith [hz']
    rw [show z ^ 2 * (z - b) = z ^ 3 - b * z ^ 2 by ring]
    exact h
  set X : ℚ := |z| with hX
  have hXval : X = |z| := hX
  have hX0 : 0 < X := by rw [hXval]; exact hz0
  have hXnn : (0 : ℚ) ≤ X := le_of_lt hX0
  have hHX : (H : ℚ) < X / 4 := by rw [hXval]; exact hHlt
  -- lower bound
  have htri : |z| ≤ |z - b| + |b| := by
    have := abs_add_le (z - b) b
    rwa [sub_add_cancel] at this
  have hlower : X ^ 2 * (X - (H : ℚ)) ≤ |z ^ 2 * (z - b)| := by
    have h1 : |z| - (H : ℚ) ≤ |z - b| := by linarith [htri, hb]
    rw [show X ^ 2 = |z| ^ 2 by rw [hXval], show X = |z| by rw [hXval]]
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  -- upper bound
  have habs_ac : |a * c - 4 * d| ≤ (H : ℚ) ^ 2 + 4 * (H : ℚ) := by
    have h1 : |a * c| ≤ (H : ℚ) ^ 2 := by
      rw [abs_mul]
      nlinarith [mul_le_mul ha hc (abs_nonneg c) hHnn]
    have h2 : |4 * d| ≤ 4 * (H : ℚ) := by
      rw [abs_mul]
      have h4 : |(4 : ℚ)| = 4 := by norm_num
      rw [h4]
      nlinarith [hd]
    have h3 : |a * c - 4 * d| ≤ |a * c| + |4 * d| := abs_sub _ _
    linarith
  have habs_rest : |a ^ 2 * d - 4 * b * d + c ^ 2| ≤ (H : ℚ) ^ 3 + 5 * (H : ℚ) ^ 2 := by
    have h1 : |a ^ 2 * d| ≤ (H : ℚ) ^ 3 := by
      rw [abs_mul, abs_pow]
      nlinarith [mul_le_mul (pow_le_pow_left₀ (abs_nonneg a) ha 2) hd (abs_nonneg d)
        (by positivity : (0:ℚ) ≤ (H:ℚ) ^ 2)]
    have h2 : |4 * b * d| ≤ 4 * (H : ℚ) ^ 2 := by
      rw [abs_mul, abs_mul]
      have h4 : |(4 : ℚ)| = 4 := by norm_num
      rw [h4]
      nlinarith [mul_le_mul (mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℚ) ≤ 4)) hd
        (abs_nonneg d) (by positivity : (0:ℚ) ≤ 4 * (H:ℚ))]
    have h3 : |c ^ 2| ≤ (H : ℚ) ^ 2 := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg c) hc 2
    have h4 := abs_add_le (a ^ 2 * d - 4 * b * d) (c ^ 2)
    have h5 := abs_sub (a ^ 2 * d) (4 * b * d)
    linarith
  have hupper : |(a ^ 2 * d - 4 * b * d + c ^ 2) - (a * c - 4 * d) * z|
      ≤ ((H : ℚ) ^ 2 + 4 * (H : ℚ)) * X + ((H : ℚ) ^ 3 + 5 * (H : ℚ) ^ 2) := by
    have h1 : |(a * c - 4 * d) * z| ≤ ((H : ℚ) ^ 2 + 4 * (H : ℚ)) * X := by
      rw [abs_mul, show X = |z| by rw [hXval]]
      exact mul_le_mul_of_nonneg_right habs_ac (abs_nonneg z)
    have h2 := abs_sub (a ^ 2 * d - 4 * b * d + c ^ 2) ((a * c - 4 * d) * z)
    linarith
  have hf2 : X ^ 2 * (X - (H : ℚ))
      ≤ ((H : ℚ) ^ 2 + 4 * (H : ℚ)) * X + ((H : ℚ) ^ 3 + 5 * (H : ℚ) ^ 2) := by
    have h : X ^ 2 * (X - (H : ℚ))
        ≤ |(a ^ 2 * d - 4 * b * d + c ^ 2) - (a * c - 4 * d) * z| := by
      rw [← hkey]
      exact hlower
    exact h.trans hupper
  have h1m : (0 : ℚ) ≤ X / 4 - (H : ℚ) := by linarith
  have h2m : (0 : ℚ) ≤ X / 4 + (H : ℚ) := by linarith
  have hH2le : (H : ℚ) ^ 2 ≤ X ^ 2 / 16 := by
    nlinarith [mul_nonneg h1m h2m, hXnn]
  have hb1 : (H : ℚ) ^ 2 * X ≤ X ^ 3 / 16 := by nlinarith [hH2le, hXnn]
  have hb2 : 4 * (H : ℚ) * X ≤ X ^ 2 := by nlinarith [hHX, hXnn]
  have hb3 : (H : ℚ) ^ 3 ≤ X ^ 3 / 64 := by
    have h := mul_le_mul hHX.le hH2le (by positivity : (0:ℚ) ≤ (H:ℚ) ^ 2)
      (by linarith : (0:ℚ) ≤ X / 4)
    nlinarith [h]
  have hb4 : 5 * (H : ℚ) ^ 2 ≤ 5 * X ^ 2 / 16 := by nlinarith [hH2le]
  have hstep : X ^ 3 * (43 / 64) ≤ ((H : ℚ) + 21 / 16) * X ^ 2 := by
    nlinarith [hf2, hb1, hb2, hb3, hb4]
  have hX2 : 0 < X ^ 2 := by positivity
  have hstep2 : X * (43 / 64) ≤ (H : ℚ) + 21 / 16 := by
    by_contra hlt
    push_neg at hlt
    nlinarith [hstep, hlt, hX2]
  have hHsmall : (H : ℚ) < 7 / 9 := by nlinarith [hstep2, hHX]
  have hH0 : (H : ℚ) = 0 := by
    have h1 : (H : ℚ) < 1 := by linarith
    have h2 : H < 1 := by exact_mod_cast h1
    have : H = 0 := by omega
    simp [this]
  rw [hH0] at hf2
  nlinarith [hf2, hX0]

open Classical in
/-- **The `n = 4` imprimitive quartic has a bounded integer root of its resolvent.**

Every member of `ImprimitiveBad 4 H` (a monic degree-`4` box polynomial with `|Gal| < 4!` whose
Galois group is imprimitive) has an integer root `z` of its cubic resolvent with `|z| ≤ 4H`.  This
is the algebraic input to the Chow–Dietmann count `#ImprimitiveBad 4 H ≤ R(4H) = O(H³)`. -/
theorem quartic_imprimitive_resolvent_root (H : ℕ) (f : ℤ[X]) (hf : f ∈ ImprimitiveBad 4 H) :
    ∃ z : ℤ, |z| ≤ 4 * (H : ℤ) ∧
      (resolventCubic (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)).eval z = 0 := by
  classical
  obtain ⟨hbad, hnotprim⟩ := hf
  have hbox : f ∈ Box 4 H := Bad_subset_Box 4 H (irreducibleBad_subset_Bad 4 H hbad)
  have hm : f.Monic := hbox.1
  have hdeg : f.natDegree = 4 := Polynomial.natDegree_eq_of_degree_eq_some hbox.2.1
  have hcoeff : ∀ i < 4, |f.coeff i| ≤ (H : ℤ) := hbox.2.2
  have hirr : Irreducible (f.map φℚ) := irreducibleBad_mem_irreducible_rat (by norm_num) hbad
  have hnp : ¬ galPrimitive f hirr := fun h => hnotprim ⟨hirr, h⟩
  obtain ⟨A, B, p, q, hc3, hc2, hc1, hc0, hβint, hβrat⟩ :=
    quartic_pairing_data f hirr hm hdeg hnp
  have hZinj : Function.Injective (algebraMap ℤ (f.map φℚ).SplittingField) := by
    intro x y h
    have h' : ((x : ℤ) : (f.map φℚ).SplittingField) = ((y : ℤ) : (f.map φℚ).SplittingField) := h
    exact_mod_cast h'
  have hQinj : Function.Injective (algebraMap ℚ (f.map φℚ).SplittingField) :=
    (algebraMap ℚ (f.map φℚ).SplittingField).injective
  -- the resolvent vanishes at `β = p + q`
  have hres : (resolventCubic (((f.coeff 3 : ℤ)) : (f.map φℚ).SplittingField)
      (((f.coeff 2 : ℤ)) : (f.map φℚ).SplittingField) (((f.coeff 1 : ℤ)) : (f.map φℚ).SplittingField)
      (((f.coeff 0 : ℤ)) : (f.map φℚ).SplittingField)).eval (p + q) = 0 := by
    rw [hc3, hc2, hc1, hc0]
    simpa only [mul_comm, add_comm, add_left_comm, add_assoc] using
      resolventCubic_eval_pairing A B p q
  -- `β` is an integer
  rcases hβrat with ⟨e, he⟩
  have heint : IsIntegral ℤ e := by
    obtain ⟨P, hPmon, hPa⟩ := hβint
    refine ⟨P, hPmon, ?_⟩
    have h1 := Polynomial.aeval_algebraMap_apply (R := ℤ) (A := ℚ)
      ((f.map φℚ).SplittingField) e P
    have hPa' : (aeval (p + q)) P = 0 := hPa
    rw [he, hPa'] at h1
    exact (map_eq_zero_iff _ hQinj).mp h1.symm
  obtain ⟨z, hz⟩ := exists_int_of_isIntegral_rat heint
  -- `algebraMap ℤ N z = p + q`
  have hzpq : algebraMap ℤ (f.map φℚ).SplittingField z = p + q := by
    calc algebraMap ℤ (f.map φℚ).SplittingField z
        = algebraMap ℚ (f.map φℚ).SplittingField ((z : ℚ)) :=
          (IsScalarTower.algebraMap_apply ℤ ℚ (f.map φℚ).SplittingField z).symm
      _ = algebraMap ℚ (f.map φℚ).SplittingField e := by rw [hz]
      _ = p + q := he
  -- the resolvent vanishes at the integer `z`
  have hresZ : (resolventCubic (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)).eval z = 0 := by
    have h1 : algebraMap ℤ (f.map φℚ).SplittingField
        ((resolventCubic (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)).eval z) = 0 := by
      rw [← Polynomial.eval_map_apply (f := algebraMap ℤ (f.map φℚ).SplittingField)
        (p := resolventCubic (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)) (x := z),
        resolventCubic_map, hzpq]
      exact hres
    exact (map_eq_zero_iff _ hZinj).mp h1
  refine ⟨z, ?_, hresZ⟩
  -- the root bound
  have hrat : (resolventCubic ((f.coeff 3 : ℤ) : ℚ) ((f.coeff 2 : ℤ) : ℚ)
      ((f.coeff 1 : ℤ) : ℚ) ((f.coeff 0 : ℤ) : ℚ)).eval (z : ℚ) = 0 := by
    rw [eval_resolventCubic_intCast, hresZ]
    norm_num
  have hbd : |(z : ℚ)| ≤ 4 * (H : ℚ) :=
    resolventCubic_root_abs_le H _ _ _ _ _
      (by exact_mod_cast hcoeff 3 (by norm_num))
      (by exact_mod_cast hcoeff 2 (by norm_num))
      (by exact_mod_cast hcoeff 1 (by norm_num))
      (by exact_mod_cast hcoeff 0 (by norm_num)) hrat
  have hcast : ((|z| : ℤ) : ℚ) ≤ ((4 * (H : ℤ) : ℤ) : ℚ) := by
    rw [Int.cast_abs, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    exact hbd
  exact_mod_cast hcast

end

end Submission.Vdw
