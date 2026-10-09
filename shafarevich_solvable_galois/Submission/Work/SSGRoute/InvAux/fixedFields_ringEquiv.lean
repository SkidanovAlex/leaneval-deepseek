import Mathlib
import Submission.Work.SSGRoute.InvAux
import Submission.Work.SSGRoute.InvAux.exists_orderEmbedding
import Submission.Work.SSGRoute.InvAux.irreducible_natDegree_le_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The fixed fields of the involutions of `ℚ̄` are isomorphic

Let `c₁, c₂` be two non-trivial involutive ring automorphisms of `Ω = ℚ̄` (`c * c = 1`, `c ≠ 1`)
and let `Fᵢ = Ω^{cᵢ}` be their fixed fields (`Work.SSGRoute.InvAux.fixSub`).  We prove that `F₁` and
`F₂` are isomorphic:
`Work.SSGRoute.InvAux.fixedFields_ringEquiv`.

The proof rests on the following description of `F`, valid for **any** non-trivial involution `c`
of `ℚ̄`:

* the norm set `normSet c = {m * c m | m ≠ 0}` makes `F = ℚ̄^c` a linearly ordered field
  (`InvAux.lean`);
* every element of `ℚ̄` is algebraic over `ℚ`, hence bounded by a natural number inside `F`, so the
  order of `F` is Archimedean; an Archimedean linearly ordered field embeds into `ℝ`
  (`InvAux/exists_orderEmbedding.lean`);
* the image `L ⊆ ℝ` is a subfield of `ℝ` that is *real closed in the algebraic sense*: every
  irreducible polynomial over `L` has degree at most two (this is transported from
  `InvAux/irreducible_natDegree_le_two.lean` along the ring isomorphism `F ≃+* L`), and every
  non-negative element of `L` is a square (`cone` consists of norms, and norms are squares of fixed
  elements).

Consequently `L` contains every real algebraic number: if `y ∈ ℝ` is algebraic over `ℚ` then `y` is
algebraic over `L`, its minimal polynomial over `L` has degree at most two, and the quadratic case
is settled by completing the square and using that non-negative elements of `L` are squares.  So
`L` is exactly the field `ℝ^{alg}` of real algebraic numbers, and both `F₁` and `F₂` are isomorphic
to `ℝ^{alg}`.

The four auxiliary lemmas below (`isSquareOfCone`, `irreducibleNatDegreeLeTwoOfRingEquiv`,
`isSquareOfNonnegOfRingEquiv`, `isAlgebraicMemOfSubfield`) are the independent pieces of this
argument; the rest is assembly.
-/

namespace Work.SSGRoute.InvAux

open Polynomial
open TwoTorsion

/-! ## The real algebraic numbers -/

/-- The real algebraic numbers, as a subfield of `ℝ`. -/
def realAlgSubfield : Subfield ℝ where
  carrier := {x | IsAlgebraic ℚ x}
  mul_mem' := fun hx hy => hx.mul hy
  one_mem' := isAlgebraic_one
  add_mem' := fun hx hy => hx.add hy
  zero_mem' := isAlgebraic_zero
  neg_mem' := fun hx => IsAlgebraic.neg hx
  inv_mem' := fun _ hx => IsAlgebraic.inv hx

@[simp] lemma mem_realAlgSubfield {x : ℝ} : x ∈ realAlgSubfield ↔ IsAlgebraic ℚ x := Iff.rfl

/-! ## A piece of "real closedness" of the fixed field: non-negative elements are squares -/

/-- Every element of the fixed field of an involution of an algebraically closed field of
characteristic zero that is non-negative for the order induced by the norm set is a square. -/
theorem isSquareOfCone {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] {c : Ω ≃+* Ω}
    (hc : c * c = 1) {x : ↥(fixSub c)} (hx : cone x) : IsSquare x := by
  rw [cone] at hx
  rcases hx with h | h
  · exact ⟨0, by rw [mul_zero]; exact Subtype.ext h⟩
  · obtain ⟨m, hm, -, hmsq⟩ := exists_fixed_sq_of_mem_normSet hc h
    refine ⟨⟨m, hm⟩, ?_⟩
    apply Subtype.ext
    show (x : Ω) = m * m
    rw [hmsq, pow_two]

/-! ## Transport of the two "real closedness" properties along a ring isomorphism -/

/-- The bound "every irreducible polynomial has degree at most two" is transported along a ring
isomorphism. -/
theorem irreducibleNatDegreeLeTwoOfRingEquiv {R S : Type*} [Field R] [Field S] (e : R ≃+* S)
    (h : ∀ f : Polynomial R, Irreducible f → f.natDegree ≤ 2) (g : Polynomial S)
    (hg : Irreducible g) : g.natDegree ≤ 2 := by
  have hcomp₁ : (e : R →+* S).comp (e.symm : S →+* R) = RingHom.id S := by ext y; simp
  have hcomp₂ : (e.symm : S →+* R).comp (e : R →+* S) = RingHom.id R := by ext y; simp
  have hmap₁ : ∀ p : Polynomial S,
      Polynomial.map (e : R →+* S) (Polynomial.map (e.symm : S →+* R) p) = p := by
    intro p
    rw [Polynomial.map_map, hcomp₁, Polynomial.map_id]
  have hmap₂ : ∀ p : Polynomial R,
      Polynomial.map (e.symm : S →+* R) (Polynomial.map (e : R →+* S) p) = p := by
    intro p
    rw [Polynomial.map_map, hcomp₂, Polynomial.map_id]
  have hdeg : (Polynomial.map (e.symm : S →+* R) g).natDegree = g.natDegree :=
    Polynomial.natDegree_map_eq_of_injective e.symm.injective g
  rw [← hdeg]
  refine h _ ⟨?_, ?_⟩
  · intro hunit
    exact hg.not_isUnit (by
      have h2 : IsUnit (Polynomial.map (e : R →+* S)
          (Polynomial.map (e.symm : S →+* R) g)) := by
        have h3 := hunit.map
          (Polynomial.mapRingHom (e : R →+* S) : Polynomial R →+* Polynomial S)
        simpa using h3
      rwa [hmap₁] at h2)
  · intro a b hab
    have h1 : Polynomial.map (e : R →+* S) a * Polynomial.map (e : R →+* S) b = g := by
      rw [← Polynomial.map_mul (e : R →+* S), ← hab, hmap₁]
    rcases hg.isUnit_or_isUnit h1.symm with h' | h'
    · exact Or.inl (by
        have h2 : IsUnit (Polynomial.map (e.symm : S →+* R)
            (Polynomial.map (e : R →+* S) a)) := by
          have h3 := h'.map
            (Polynomial.mapRingHom (e.symm : S →+* R) : Polynomial S →+* Polynomial R)
          simpa using h3
        rwa [hmap₂] at h2)
    · exact Or.inr (by
        have h2 : IsUnit (Polynomial.map (e.symm : S →+* R)
            (Polynomial.map (e : R →+* S) b)) := by
          have h3 := h'.map
            (Polynomial.mapRingHom (e.symm : S →+* R) : Polynomial S →+* Polynomial R)
          simpa using h3
        rwa [hmap₂] at h2)

/-- The property "every non-negative element is a square" is transported along an order preserving
ring isomorphism. -/
theorem isSquareOfNonnegOfRingEquiv {R S : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Field S] [LinearOrder S] [IsStrictOrderedRing S] (e : R ≃+* S)
    (he : ∀ a b : R, a ≤ b → e a ≤ e b) (h : ∀ x : R, 0 ≤ x → IsSquare x) {y : S}
    (hy : 0 ≤ y) : IsSquare y := by
  have h0 : 0 ≤ e.symm y := by
    by_contra hc
    rw [not_le] at hc
    have hle : e (e.symm y) ≤ e 0 := he _ _ (le_of_lt hc)
    rw [RingEquiv.apply_symm_apply, map_zero] at hle
    have hy0 : y = 0 := le_antisymm hle hy
    rw [hy0, map_zero] at hc
    exact lt_irrefl 0 hc
  obtain ⟨z, hz⟩ := h (e.symm y) h0
  refine ⟨e z, ?_⟩
  calc y = e (e.symm y) := (RingEquiv.apply_symm_apply e y).symm
    _ = e (z * z) := by rw [hz]
    _ = e z * e z := map_mul e z z

/-! ## Real closed subfields of `ℝ` contain all real algebraic numbers -/

/-- A subfield `L ⊆ ℝ` over which every irreducible polynomial has degree at most two and in which
every non-negative element is a square contains every real algebraic number. -/
theorem isAlgebraicMemOfSubfield (L : Subfield ℝ) (hQ : ∀ q : ℚ, (q : ℝ) ∈ L)
    (h2 : ∀ f : Polynomial ↥L, Irreducible f → f.natDegree ≤ 2)
    (hsq : ∀ x : ↥L, 0 ≤ x → IsSquare x) {y : ℝ} (hy : IsAlgebraic ℚ y) : y ∈ L := by
  by_contra hmem
  have hyL : IsAlgebraic ↥L y := IsAlgebraic.tower_top ↥L hy
  set f : Polynomial ↥L := minpoly ↥L y with hf
  have hfmon : f.Monic := minpoly.monic hyL.isIntegral
  have hfirr : Irreducible f := by
    rw [hf]; exact minpoly.irreducible hyL.isIntegral
  have hdeg : f.natDegree ≤ 2 := h2 f hfirr
  -- `f` is neither constant nor linear: otherwise `y ∈ L`.
  have hne0 : f.natDegree ≠ 0 := by
    intro h0
    have hf1 : f = 1 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
      have hc1 : f.coeff 0 = 1 := by
        rw [← h0, Polynomial.coeff_natDegree, hfmon.leadingCoeff]
      rw [hc1, map_one]
    have := minpoly.aeval ↥L y
    rw [← hf, hf1] at this
    simp at this
  have hne1 : f.natDegree ≠ 1 := by
    intro h1
    obtain ⟨a, ha0, b, hfab⟩ := Polynomial.natDegree_eq_one.mp h1
    have hrel : (algebraMap ↥L ℝ) a * y + (algebraMap ↥L ℝ) b = 0 := by
      have h := minpoly.aeval ↥L y
      rw [← hf, ← hfab] at h
      simpa using h
    have hy' : y = -((algebraMap ↥L ℝ) b / (algebraMap ↥L ℝ) a) := by
      have ha0' : (algebraMap ↥L ℝ) a ≠ 0 := fun h0 =>
        ha0 (Subtype.ext (show (a : ℝ) = 0 from h0))
      field_simp
      linarith
    refine hmem ?_
    rw [hy']
    exact L.neg_mem (L.div_mem b.2 a.2)
  have hdeg2 : f.natDegree = 2 := by omega
  -- write `f = X ^ 2 + C b * X + C c` and read off the quadratic relation at `y`
  set b : ↥L := f.coeff 1 with hb
  set c : ↥L := f.coeff 0 with hc
  have hfeq : f = X ^ 2 + C b * X + C c := by
    ext n
    rcases lt_trichotomy n 2 with hlt | heq | hgt
    · interval_cases n
      · simp [hb, hc]
      · simp [hb, hc]
    · subst heq
      have h2' : f.coeff 2 = 1 := by
        rw [← hdeg2, Polynomial.coeff_natDegree, hfmon.leadingCoeff]
      simp [h2']
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_X_pow,
        Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
      simp only [show n ≠ 2 by omega, show n ≠ 1 by omega, show n ≠ 0 by omega,
        if_false, add_zero]
  have hrel : y ^ 2 + (algebraMap ↥L ℝ) b * y + (algebraMap ↥L ℝ) c = 0 := by
    have h := minpoly.aeval ↥L y
    rw [← hf, hfeq] at h
    simpa using h
  -- completing the square
  have hkey : (2 * y + (algebraMap ↥L ℝ) b) ^ 2
      = (algebraMap ↥L ℝ) b ^ 2 - 4 * (algebraMap ↥L ℝ) c := by
    linear_combination 4 * hrel
  have hmemt : (algebraMap ↥L ℝ) b ^ 2 - 4 * (algebraMap ↥L ℝ) c ∈ L := by
    have h4 : (4 : ℝ) ∈ L := by simpa using hQ 4
    exact L.sub_mem (L.pow_mem b.2 2) (L.mul_mem h4 c.2)
  obtain ⟨s, hs⟩ := hsq ⟨_, hmemt⟩ (show (0 : ℝ) ≤
    (algebraMap ↥L ℝ) b ^ 2 - 4 * (algebraMap ↥L ℝ) c by
      rw [← hkey]; exact sq_nonneg _)
  have hs' : (algebraMap ↥L ℝ) b ^ 2 - 4 * (algebraMap ↥L ℝ) c
      = (s : ℝ) * (s : ℝ) := congrArg Subtype.val hs
  have hsq2 : (2 * y + (algebraMap ↥L ℝ) b) ^ 2 = (s : ℝ) ^ 2 := by
    rw [hkey, hs', pow_two]
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq2) with h | h
  · refine hmem ?_
    have hy' : y = ((s : ℝ) - (algebraMap ↥L ℝ) b) / 2 := by linarith
    rw [hy']
    exact L.div_mem (L.sub_mem s.2 b.2) (show (2 : ℝ) ∈ L from by simpa using hQ 2)
  · refine hmem ?_
    have hy' : y = (-(s : ℝ) - (algebraMap ↥L ℝ) b) / 2 := by linarith
    rw [hy']
    exact L.div_mem (L.sub_mem (L.neg_mem s.2) b.2) (show (2 : ℝ) ∈ L from by simpa using hQ 2)

/-! ## The order embedding of the fixed field into `ℝ` and its range -/

section Embedding

variable (c : SSGRoute.QBar ≃+* SSGRoute.QBar) [Fact (c * c = 1)] [Fact (c ≠ 1)]

/-- The (essentially unique) order preserving ring homomorphism from the fixed field of a
non-trivial involution of `ℚ̄` to `ℝ`. -/
noncomputable def fixSubEmbed : ↥(fixSub c) →+*o ℝ :=
  Classical.choose (exists_orderEmbedding (c := c))

lemma fixSubEmbed_injective : Function.Injective (fixSubEmbed c) :=
  (Classical.choose_spec (exists_orderEmbedding (c := c))).1

/-- The positivity cone of the fixed field is exactly the cone of the embedding. -/
lemma fixSubEmbed_nonneg_iff (x : ↥(fixSub c)) : 0 ≤ fixSubEmbed c x ↔ cone x :=
  (Classical.choose_spec (exists_orderEmbedding (c := c))).2 x

/-- The embedding is compatible with the order. -/
lemma fixSubEmbed_mono {x y : ↥(fixSub c)} (h : x ≤ y) : fixSubEmbed c x ≤ fixSubEmbed c y :=
  (fixSubEmbed c).monotone' h

lemma fixSubEmbed_le_iff {x y : ↥(fixSub c)} : fixSubEmbed c x ≤ fixSubEmbed c y ↔ x ≤ y := by
  refine ⟨fun h => ?_, fun h => fixSubEmbed_mono c h⟩
  by_contra hc
  rw [not_le] at hc
  have h1 : fixSubEmbed c y ≤ fixSubEmbed c x := fixSubEmbed_mono c (le_of_lt hc)
  exact absurd (fixSubEmbed_injective c (le_antisymm h h1)) (ne_of_gt hc)

/-- The embedding, as a `ℚ`-algebra homomorphism (every ring homomorphism maps `ℚ` to `ℚ` and so is
`ℚ`-linear). -/
noncomputable def fixSubAlgHom : ↥(fixSub c) →ₐ[ℚ] ℝ where
  toRingHom := (fixSubEmbed c).toRingHom
  commutes' := by
    intro q
    have h : (fixSubEmbed c).toRingHom.comp (algebraMap ℚ ↥(fixSub c)) = (algebraMap ℚ ℝ) :=
      RingHom.ext_rat _ _
    exact congrArg (fun f : ℚ →+* ℝ => f q) h

/-- The image of the fixed field inside `ℝ`. -/
noncomputable def fixSubRange : Subfield ℝ := (fixSubEmbed c).toRingHom.fieldRange

lemma mem_fixSubRange {y : ℝ} : y ∈ fixSubRange c ↔ ∃ x : ↥(fixSub c), fixSubEmbed c x = y :=
  RingHom.mem_fieldRange

/-- The map from the fixed field to its image in `ℝ`. -/
noncomputable def fixSubRangeHom : ↥(fixSub c) →+* ↥(fixSubRange c) where
  toFun x := ⟨fixSubEmbed c x, RingHom.mem_fieldRange.mpr ⟨x, rfl⟩⟩
  map_one' := Subtype.ext (map_one (fixSubEmbed c))
  map_mul' a b := Subtype.ext (map_mul (fixSubEmbed c) a b)
  map_zero' := Subtype.ext (map_zero (fixSubEmbed c))
  map_add' a b := Subtype.ext (map_add (fixSubEmbed c) a b)

@[simp] lemma fixSubRangeHom_coe (x : ↥(fixSub c)) :
    ((fixSubRangeHom c x : ↥(fixSubRange c)) : ℝ) = fixSubEmbed c x := rfl

/-- The fixed field is isomorphic to its image in `ℝ`. -/
noncomputable def fixSubRangeEquiv : ↥(fixSub c) ≃+* ↥(fixSubRange c) :=
  RingEquiv.ofBijective (fixSubRangeHom c)
    ⟨fun a b hab => fixSubEmbed_injective c (by
        have h := congrArg (fun x : ↥(fixSubRange c) => (x : ℝ)) hab
        exact h),
     fun y => by
       obtain ⟨x, hx⟩ := (mem_fixSubRange c).mp y.2
       exact ⟨x, Subtype.ext hx⟩⟩

@[simp] lemma fixSubRangeEquiv_coe (x : ↥(fixSub c)) :
    ((fixSubRangeEquiv c x : ↥(fixSubRange c)) : ℝ) = fixSubEmbed c x := rfl

/-- The image of the fixed field contains all rational numbers (the embedding fixes `ℚ`). -/
lemma rat_mem_fixSubRange (q : ℚ) : (q : ℝ) ∈ fixSubRange c :=
  ⟨(q : ↥(fixSub c)), map_ratCast (fixSubEmbed c) q⟩

/-- Every element of the fixed field is algebraic over `ℚ`. -/
lemma isAlgebraic_fixSub (x : ↥(fixSub c)) : IsAlgebraic ℚ x := by
  haveI : Algebra.IsAlgebraic ℚ SSGRoute.QBar := AlgebraicClosure.isAlgebraic ℚ
  have h : Algebra.IsAlgebraic ℚ ↥(fixSub c) :=
    Algebra.IsAlgebraic.of_injective
      (IsScalarTower.toAlgHom ℚ ↥(fixSub c) SSGRoute.QBar) Subtype.coe_injective
  exact h.isAlgebraic x

/-- The image in `ℝ` consists of algebraic numbers. -/
lemma fixSubRange_le_realAlg {y : ℝ} (hy : y ∈ fixSubRange c) : y ∈ realAlgSubfield := by
  obtain ⟨x, rfl⟩ := (mem_fixSubRange c).mp hy
  exact IsAlgebraic.algHom (fixSubAlgHom c) (isAlgebraic_fixSub c x)

/-- Irreducible polynomials over the image have degree at most two: transported from the fixed
field. -/
lemma fixSubRange_irreducible_natDegree_le_two {f : Polynomial ↥(fixSubRange c)}
    (hf : Irreducible f) : f.natDegree ≤ 2 :=
  irreducibleNatDegreeLeTwoOfRingEquiv (fixSubRangeEquiv c)
    (fun g hg => irreducible_natDegree_le_two (Ω := SSGRoute.QBar) (Fact.out : c * c = 1) hg)
    f hf

/-- In the image, every non-negative element is a square. -/
lemma fixSubRange_isSquare_of_nonneg {y : ↥(fixSubRange c)} (hy : 0 ≤ y) : IsSquare y :=
  isSquareOfNonnegOfRingEquiv (fixSubRangeEquiv c)
    (fun a b hab => by
      have h := fixSubEmbed_mono c hab
      exact h)
    (fun x hx => isSquareOfCone (Ω := SSGRoute.QBar) (Fact.out : c * c = 1)
      ((zero_le_iff_cone x).mp hx)) hy

/-- The image in `ℝ` contains all real algebraic numbers. -/
lemma realAlg_le_fixSubRange {y : ℝ} (hy : y ∈ realAlgSubfield) : y ∈ fixSubRange c :=
  isAlgebraicMemOfSubfield (fixSubRange c) (rat_mem_fixSubRange c)
    (fun f hf => fixSubRange_irreducible_natDegree_le_two c hf)
    (fun x hx => fixSubRange_isSquare_of_nonneg c hx) hy

/-- The image is exactly the real algebraic numbers. -/
lemma fixSubRange_eq_realAlg : fixSubRange c = realAlgSubfield :=
  le_antisymm (fun y hy => fixSubRange_le_realAlg c hy) (fun y hy => realAlg_le_fixSubRange c hy)

/-- The ring homomorphism from the fixed field onto the real algebraic numbers. -/
noncomputable def fixSubToRealAlg : ↥(fixSub c) →+* ↥realAlgSubfield where
  toFun x := ⟨fixSubEmbed c x, fixSubRange_le_realAlg c ⟨x, rfl⟩⟩
  map_one' := Subtype.ext (map_one (fixSubEmbed c))
  map_mul' a b := Subtype.ext (map_mul (fixSubEmbed c) a b)
  map_zero' := Subtype.ext (map_zero (fixSubEmbed c))
  map_add' a b := Subtype.ext (map_add (fixSubEmbed c) a b)

/-- **The fixed field of a non-trivial involution of `ℚ̄` is the field of real algebraic
numbers.** -/
noncomputable def fixSubEquivRealAlg : ↥(fixSub c) ≃+* ↥realAlgSubfield :=
  RingEquiv.ofBijective (fixSubToRealAlg c)
    ⟨fun a b hab => fixSubEmbed_injective c (by
        have h : (fixSubEmbed c a : ℝ) = fixSubEmbed c b :=
          congrArg (fun x : ↥realAlgSubfield => (x : ℝ)) hab
        exact h),
     fun y => by
       obtain ⟨x, hx⟩ := (mem_fixSubRange c).mp (realAlg_le_fixSubRange c y.2)
       exact ⟨x, Subtype.ext hx⟩⟩

end Embedding

/-- The fixed fields of any two non-trivial involutive automorphisms of `ℚ̄` are isomorphic: both are
the field of real algebraic numbers. -/
theorem fixedFields_ringEquiv {c₁ c₂ : SSGRoute.QBar ≃+* SSGRoute.QBar}
    [Fact (c₁ * c₁ = 1)] [Fact (c₁ ≠ 1)] [Fact (c₂ * c₂ = 1)] [Fact (c₂ ≠ 1)] :
    Nonempty (↥(Work.SSGRoute.InvAux.fixSub c₁) ≃+* ↥(Work.SSGRoute.InvAux.fixSub c₂)) :=
  ⟨(fixSubEquivRealAlg c₁).trans (fixSubEquivRealAlg c₂).symm⟩

end Work.SSGRoute.InvAux
