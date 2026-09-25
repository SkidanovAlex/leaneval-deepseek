import Mathlib
import Submission.Work.ProPDeficiency.Basic

/-!
# Deficiency of a finite group is `≤ 0`: `card_le_rel_card_of_finite`

**Namespace** `Work.ProPDeficiency`; module `Submission.Work.ProPDeficiency.card_le_rel_card_of_finite`.

A finite group presented on `d` generators by `r` relators needs at least `d` relators
(`Fintype.card α ≤ rel.card`); equivalently, the deficiency of a finite group is `≤ 0`.
No minimality of the generating set `α` is needed, only finiteness of `G`.

The proof abelianises.  Writing `α →₀ ℤ` for the free abelian group on `α` (the exponent vectors
of words in `FreeGroup α`), the presentation `G ≃* FreeGroup α ⧸ normalClosure rel` together with
the pairing

`(v, x) ↦ ∑ a, v a * (exponent of a in x)`

for `v : α → ℚ` and `x` a word gives a `ℚ`-linear map `relMatrix rel : (α → ℚ) →ₗ[ℚ] (rel → ℚ)`.
If `v` is in its kernel then the group homomorphism `W_v : FreeGroup α →* (ℚ,+)` sending
generator `a` to `v a` kills every relator, hence kills the normal closure of `rel`, hence factors
through the finite group `G`; but there is no nontrivial homomorphism from a finite group into
the torsion-free group `ℚ`.  So `W_v = 1` and `v = 0`: `relMatrix rel` is injective, whence

`card α = finrank ℚ (α → ℚ) ≤ finrank ℚ (rel → ℚ) = rel.card`.

## Main results

* `freeAbExp` : the abelianisation `FreeGroup α →* Multiplicative (α →₀ ℤ)` (exponent vectors);
* `ratEval` : the hom `FreeGroup α →* Multiplicative ℚ` attached to `v : α → ℚ`;
* `toAdd_ratEval` : `W_v` evaluated on a word is the pairing of `v` with its exponent vector;
* `pairing_eq_sum`, `expPairing` : the elementary pairing and its `ℚ`-linearity;
* `monoidHom_to_rat_eq_one` : **no nontrivial hom from a finite group to `ℚ`**;
* `relMatrix` and `relMatrix_injective` : the abelianised relation matrix is injective;
* `card_le_rel_card_of_finite` : the target statement.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Classical

namespace Work.ProPDeficiency

noncomputable section

variable {α : Type*} [Fintype α]

/-! ## Exponent vectors and the pairing with `ℚ^α` -/

/-- The abelianisation map `FreeGroup α →* Multiplicative (α →₀ ℤ)`: a word is sent to its vector
of exponent sums.  (The target is an abelian group, so `FreeGroup.lift` kills commutators.) -/
noncomputable def freeAbExp : FreeGroup α →* Multiplicative (α →₀ ℤ) :=
  FreeGroup.lift fun a => Multiplicative.ofAdd (Finsupp.single a (1 : ℤ))

theorem freeAbExp_of (a : α) : freeAbExp (FreeGroup.of a) =
    Multiplicative.ofAdd (Finsupp.single a (1 : ℤ)) := FreeGroup.lift_apply_of

/-- The group homomorphism `FreeGroup α →* Multiplicative ℚ` sending the generator `a` to `v a`.
Its values are the `ℚ`-linear functionals of `v` evaluated on the abelianised relators. -/
noncomputable def ratEval (v : α → ℚ) : FreeGroup α →* Multiplicative ℚ :=
  FreeGroup.lift fun a => Multiplicative.ofAdd (v a)

theorem ratEval_of (v : α → ℚ) (a : α) : ratEval v (FreeGroup.of a) =
    Multiplicative.ofAdd (v a) := FreeGroup.lift_apply_of

/-- The additive hom `ℤ^α → ℚ` given by pairing with `v : α → ℚ`. -/
noncomputable def expPairing (v : α → ℚ) : (α →₀ ℤ) →+ ℚ :=
  (Finsupp.linearCombination ℤ v).toAddMonoidHom

theorem expPairing_apply (v : α → ℚ) (y : α →₀ ℤ) :
    expPairing v y = (Finsupp.linearCombination ℤ v) y := rfl

/-- `ratEval v` is the composite of the abelianisation with the pairing by `v`: on a word, it is
the pairing of `v` with the exponent vector of the word. -/
theorem toAdd_ratEval (v : α → ℚ) (x : FreeGroup α) :
    Multiplicative.toAdd (ratEval v x) =
      (Finsupp.linearCombination ℤ v) (Multiplicative.toAdd (freeAbExp x)) := by
  have h : ((expPairing v).toMultiplicative.comp freeAbExp) = ratEval v := by
    refine MonoidHom.ext fun x => ?_
    exact FreeGroup.lift_unique (f := fun a => Multiplicative.ofAdd (v a)) _ (fun a => by
      rw [MonoidHom.comp_apply, freeAbExp_of, AddMonoidHom.toMultiplicative_apply_apply,
        toAdd_ofAdd, expPairing_apply, Finsupp.linearCombination_single, one_smul])
  rw [← h, MonoidHom.comp_apply, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd]
  rfl

/-- The pairing `∑ a, v a * (y a)`, i.e. the linear combination of `v` with the coefficients `y`,
expanded in coordinates. -/
theorem pairing_eq_sum (v : α → ℚ) (y : α →₀ ℤ) :
    (Finsupp.linearCombination ℤ v) y = ∑ a : α, v a * ((y a : ℤ) : ℚ) := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  rw [Finset.sum_subset (Finset.subset_univ _) ?_]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [zsmul_eq_mul, mul_comm]
  · intro a _ ha
    rw [Finsupp.notMem_support_iff.mp ha]
    simp

/-! ## No nontrivial homomorphism from a finite group to `ℚ` -/

/-- Every group homomorphism from a finite group to the additive group `ℚ` (written
multiplicatively) is trivial: `x ^ n = 1` for `n = Nat.card H` forces `n • f x = 0` in the
torsion-free group `ℚ`. -/
theorem monoidHom_to_rat_eq_one {H : Type*} [Group H] [Finite H] (f : H →* Multiplicative ℚ) :
    f = 1 := by
  haveI : Fintype H := Fintype.ofFinite H
  ext x
  have hx : x ^ Fintype.card H = 1 := pow_card_eq_one
  have h1 : (Fintype.card H) • (Multiplicative.toAdd (f x)) = 0 := by
    have h2 : Multiplicative.toAdd (f (x ^ Fintype.card H)) = 0 := by rw [hx, map_one]; rfl
    rwa [map_pow, toAdd_pow] at h2
  have hc : (Fintype.card H : ℚ) ≠ 0 := by
    have : 0 < Fintype.card H := Fintype.card_pos_iff.mpr ⟨1⟩
    exact_mod_cast this.ne'
  have h3 : (Fintype.card H : ℚ) * Multiplicative.toAdd (f x) = 0 := by
    simpa only [nsmul_eq_mul] using h1
  exact toAdd_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left hc)

/-! ## The abelianised relation matrix -/

/-- The `ℚ`-linear map attached to a relator set `rel`: it pairs `v : α → ℚ` with the exponent
vectors of the relators.  This is the abelianised "relation matrix" of the presentation. -/
noncomputable def relMatrix (rel : Finset (FreeGroup α)) : (α → ℚ) →ₗ[ℚ] (rel → ℚ) where
  toFun v := fun x => ∑ a : α, v a * (((Multiplicative.toAdd (freeAbExp x.val)) a : ℤ) : ℚ)
  map_add' u v := by
    ext x
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    ext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring

theorem relMatrix_apply_eq (rel : Finset (FreeGroup α)) (v : α → ℚ) (x : rel) :
    relMatrix rel v x = Multiplicative.toAdd (ratEval v x.val) := by
  rw [toAdd_ratEval, pairing_eq_sum]
  rfl

/-- **The abelianised relation matrix is injective.**  If `v : α → ℚ` is in its kernel then the
homomorphism `ratEval v` kills every relator, so it kills the normal closure of `rel`; factoring
through the finite group `G` and using `monoidHom_to_rat_eq_one` shows `ratEval v = 1`, so `v = 0`. -/
theorem relMatrix_injective {G : Type} [Group G] [Finite G] (rel : Finset (FreeGroup α))
    (hpres : IsPresentation α rel G) : Function.Injective (relMatrix rel) := by
  have hker : ∀ v : α → ℚ, relMatrix rel v = 0 → v = 0 := by
    intro v hv
    have hkill : ∀ x ∈ (rel : Set (FreeGroup α)), ratEval v x = 1 := by
      intro x hx
      have hx0 : relMatrix rel v ⟨x, hx⟩ = 0 := by rw [hv]; rfl
      have h1 : Multiplicative.toAdd (ratEval v x) = 0 := by
        rw [← relMatrix_apply_eq rel v ⟨x, hx⟩, hx0]
      exact toAdd_eq_zero.mp h1
    have hN : Subgroup.normalClosure (rel : Set (FreeGroup α)) ≤ (ratEval v).ker :=
      Subgroup.normalClosure_le_normal hkill
    obtain ⟨e⟩ := hpres
    haveI : Finite (FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))) :=
      Finite.of_equiv G e.toEquiv
    have hlift : QuotientGroup.lift _ (ratEval v) hN = 1 := monoidHom_to_rat_eq_one _
    have hfac : ratEval v = (QuotientGroup.lift _ (ratEval v) hN).comp
        (QuotientGroup.mk' (Subgroup.normalClosure (rel : Set (FreeGroup α)))) := by
      ext x
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.lift_mk']
    have hrat1 : ratEval v = 1 := by rw [hfac, hlift]; ext x; simp
    funext a
    have h := DFunLike.congr_fun hrat1 (FreeGroup.of a)
    simp only [ratEval_of, MonoidHom.one_apply] at h
    exact ofAdd_eq_one.mp h
  intro u w h
  have h0 : relMatrix rel (u - w) = 0 := by rw [map_sub, h, sub_self]
  have h2 := hker (u - w) h0
  rwa [sub_eq_zero] at h2

/-! ## The target statement -/

-- File: Submission/Work/ProPDeficiency/card_le_rel_card_of_finite.lean, namespace `Work.ProPDeficiency`.
-- "A finite group presented with `d` generators needs at least `d` relators" (deficiency of a
-- finite group is `≤ 0`).  `IsPresentation α rel G` is `Nonempty (G ≃* FreeGroup α ⧸ normalClosure rel)`
-- (defined in `Submission.Work.ProPDeficiency.Basic`).
-- Proof: abelianize.  `G` finite ⟹ `Abelianization G` finite; `Abelianization (F ⧸ N)` is
-- the quotient of `Abelianization F ≅ ℤ^α` (multiplicatively `Multiplicative (α →₀ ℤ)`) by the
-- subgroup generated by the `r` images of the relators.  The pairing `(v, x) ↦ ∑ a, v a * (exponent
-- of a in x)` is a `ℚ`-linear map `(α → ℚ) →ₗ[ℚ] (rel → ℚ)`; it is injective because a `v` in its
-- kernel gives a homomorphism `FreeGroup α → ℚ` killing all relators, hence factoring through the
-- finite group `G`, and any homomorphism from a finite group to the torsion-free `ℚ` is trivial.
-- Thus `Fintype.card α = finrank ℚ (α → ℚ) ≤ finrank ℚ (rel → ℚ) = rel.card`.
-- Note: no minimality of `α` is needed, only finiteness of `G`.
theorem card_le_rel_card_of_finite {α : Type} [Fintype α] {G : Type} [Group G] [Finite G]
    (rel : Finset (FreeGroup α)) (hpres : IsPresentation α rel G) :
    Fintype.card α ≤ rel.card := by
  calc Fintype.card α = Module.finrank ℚ (α → ℚ) := (Module.finrank_fintype_fun_eq_card ℚ).symm
    _ ≤ Module.finrank ℚ (rel → ℚ) :=
        LinearMap.finrank_le_finrank_of_injective (relMatrix_injective rel hpres)
    _ = rel.card := by rw [Module.finrank_fintype_fun_eq_card ℚ, Fintype.card_coe]

end

end Work.ProPDeficiency
