import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.ArchDefs
import Submission.Work.SSGRoute.ZDataTwo.not_isLocalNorm_ofInfinite_iff
import Submission.Work.SSGRoute.ZDataTwo.exists_orderEmbedding_fixSub
import Submission.Work.SSGRoute.ZDataTwo.orderEmbedding_ext
import Submission.Work.SSGRoute.ZDataTwo.orderEmbedding_fixSub_fieldRange
import Submission.Work.SSGRoute.ZDataTwo.exists_conjInv_kummerChar_eq_zero_iff
import Submission.Work.SSGRoute.ZDataTwo.eq_of_isNegAt_iff
import Submission.Work.SSGRoute.InvAux
import Submission.Work.SSGRoute.InvAux.exists_orderEmbedding
import Submission.Work.SSGRoute.InvAux.exists_nat_ge_of_aeval_eq_zero
import Submission.Work.SSGRoute.InvAux.irreducible_natDegree_le_two
import Submission.Work.SSGRoute.InvAux.fixedFields_ringEquiv
import Submission.Work.SSGRoute.InvAux.conjugate_of_ringEquiv
import Submission.Work.SSGRoute.InvAux.eq_of_fixes_fixSub
import Submission.Work.SSGRoute.TwoTorsion.neg_one_notMem_normSet
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Artin–Schreier dictionary between involutions and real places

The main theorem `Work.SSGRoute.ZDataTwo.arch_sum_eq_badRealSum` compares a sum over a transversal
of the conjugacy classes of the involutions of `G_k = Ω ≃ₐ[k] Ω` with the number of real places of
`k` at which `β` fails to be a local norm from `k(√α)`.  This file proves the two dictionary
lemmas that make the comparison possible:

* `exists_realPlace_of_involution` — every non-trivial involution `c` of `G_k` is the complex
  conjugation at a real place `w` of `k`, in the sense that the Kummer character of `a ∈ kˣ` at `c`
  is `1` exactly when `a` is negative at `w` (Artin–Schreier);
* `conjugate_of_same_kummerChar` — conversely two non-trivial involutions with the same Kummer
  character on `kˣ` are conjugate in `G_k` (uniqueness of the real closure of an ordered field, in
  the shape in which the `ℝ`-order embedding of the fixed field pins the real place down),
  together with the involution `conjInv` attached to a real place.

Everything is reduced to the order embedding of the fixed field of an involution (the *positivity
cone* of the workspace file `SSGRoute/InvAux.lean`) and to the norm-set dictionary of
`ArchDefs.lean`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.SSGRoute.ZDataTwo

open NumberField

/-! ## Positivity in the fixed field of an involution -/

section Positivity

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] {c : Ω ≃+* Ω} [Fact (c * c = 1)]
  [Fact (c ≠ 1)]

/-- In the fixed field of a non-trivial involution, an element is in the positivity cone exactly
when it belongs to the norm set. -/
lemma cone_iff_mem_normSet (x : ↥(Work.SSGRoute.InvAux.fixSub c)) (hx : x ≠ 0) :
    Work.SSGRoute.InvAux.cone x ↔ (x : Ω) ∈ Work.SSGRoute.TwoTorsion.normSet c := by
  rw [Work.SSGRoute.InvAux.cone]
  constructor
  · rintro (h | h)
    · exact absurd (Work.SSGRoute.InvAux.coe_eq_zero.mpr h) hx
    · exact h
  · exact Or.inr

/-- The positive elements of the fixed field are exactly the elements of the norm set. -/
lemma pos_iff_mem_normSet (x : ↥(Work.SSGRoute.InvAux.fixSub c)) :
    0 < x ↔ x ≠ 0 ∧ (x : Ω) ∈ Work.SSGRoute.TwoTorsion.normSet c := by
  constructor
  · intro h
    refine ⟨ne_of_gt h, ?_⟩
    have hcone : Work.SSGRoute.InvAux.cone x := by
      have := ((Work.SSGRoute.InvAux.lt_iff_cone (0 : ↥(Work.SSGRoute.InvAux.fixSub c)) x).mp h).1
      simpa using this
    exact (cone_iff_mem_normSet x (ne_of_gt h)).mp hcone
  · rintro ⟨hx, hmem⟩
    have hcone : Work.SSGRoute.InvAux.cone x := (cone_iff_mem_normSet x hx).mpr hmem
    have hneg : ¬ Work.SSGRoute.InvAux.cone (-x) := by
      intro hc
      have hx0 : (-x : ↥(Work.SSGRoute.InvAux.fixSub c)) ≠ 0 := by
        simpa using hx
      have hmem' : ((-x : ↥(Work.SSGRoute.InvAux.fixSub c)) : Ω) ∈
          Work.SSGRoute.TwoTorsion.normSet c := (cone_iff_mem_normSet (-x) hx0).mp hc
      have hneg1 : (-1 : Ω) ∉ Work.SSGRoute.TwoTorsion.normSet c :=
        Work.SSGRoute.TwoTorsion.neg_one_notMem_normSet c Fact.out Fact.out
      exact Work.SSGRoute.InvAux.notMem_normSet_neg (Fact.out : c * c = 1) hneg1 hmem
        (by simpa using hmem')
    exact (Work.SSGRoute.InvAux.lt_iff_cone (0 : ↥(Work.SSGRoute.InvAux.fixSub c)) x).mpr
      ⟨by simpa using hcone, by simpa using hneg⟩

end Positivity

section ToRingEquiv

variable {Ω : Type} [Field Ω] {k : Type} [Field k] [Algebra k Ω]

/-- The underlying ring automorphism of an involutive `k`-algebra automorphism is an involution. -/
lemma toRingEquiv_mul_self {c : Ω ≃ₐ[k] Ω} (hc : c ^ 2 = 1) :
    c.toRingEquiv * c.toRingEquiv = 1 := by
  rw [show c.toRingEquiv = (c : Ω ≃+* Ω) from rfl]
  have h2 : (c * c : Ω ≃ₐ[k] Ω) = 1 := by rw [← pow_two, hc]
  exact_mod_cast congrArg (fun e : Ω ≃ₐ[k] Ω => (e : Ω ≃+* Ω)) h2

/-- The underlying ring automorphism of a non-trivial `k`-algebra automorphism is non-trivial. -/
lemma toRingEquiv_ne_one {c : Ω ≃ₐ[k] Ω} (hc : c ≠ 1) : c.toRingEquiv ≠ 1 := by
  intro h
  apply hc
  ext x
  have := congrArg (fun e : Ω ≃+* Ω => e x) h
  simpa [show c.toRingEquiv = (c : Ω ≃+* Ω) from rfl] using this

end ToRingEquiv

/-! ## The sign of a unit at the real place attached to an order embedding -/

section Sign

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] {k : Type} [Field k] [NumberField k]
  [Algebra k Ω] {c : Ω ≃+* Ω} [Fact (c * c = 1)] [Fact (c ≠ 1)]

/-- If `ρ` is the order embedding of the fixed field of a non-trivial involution `c` and `τ` is the
embedding of `k` into that fixed field, then a unit `a ∈ kˣ` is negative at the corresponding
infinite place exactly when it lies in the norm set of `c` (i.e. exactly when its Kummer character
at `c` vanishes). -/
lemma neg_iff_not_mem_normSet_of_orderEmbedding (ρ : ↥(Work.SSGRoute.InvAux.fixSub c) →+*o ℝ)
    (hρ : ∀ x, 0 ≤ ρ x ↔ Work.SSGRoute.InvAux.cone x)
    (τ : k →+* ↥(Work.SSGRoute.InvAux.fixSub c))
    (hτ : ∀ x : k, ((τ x : ↥(Work.SSGRoute.InvAux.fixSub c)) : Ω) = algebraMap k Ω x)
    (a : kˣ) :
    (ρ.toRingHom.comp τ) (a : k) < 0 ↔
      algebraMap k Ω (a : k) ∉ Work.SSGRoute.TwoTorsion.normSet c := by
  have h0 : τ (a : k) ≠ 0 := by
    intro hzero
    have h1 : ((τ (a : k) : ↥(Work.SSGRoute.InvAux.fixSub c)) : Ω) = 0 := by
      have := congrArg (fun x : ↥(Work.SSGRoute.InvAux.fixSub c) => (x : Ω)) hzero
      simpa using this
    rw [hτ] at h1
    exact a.ne_zero ((algebraMap k Ω).injective (by rw [h1, map_zero]))
  have hcoe : (ρ.toRingHom.comp τ) (a : k) = ρ (τ (a : k)) := rfl
  rw [hcoe, ← not_le, hρ, cone_iff_mem_normSet (τ (a : k)) h0, hτ]

end Sign

/-! ## Every non-trivial involution is a complex conjugation -/

section RealPlace

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

/-- **The Artin–Schreier dictionary (existence half).**  Every non-trivial involution `c` of
`G_k = Ω ≃ₐ[k] Ω` is the complex conjugation at a real place `w` of `k`: the Kummer character of
`a ∈ kˣ` at `c` is `1` exactly when `a` is negative at `w`. -/
theorem exists_realPlace_of_involution (ζ : k) (hζ : IsPrimitiveRoot ζ 2)
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) (hc1 : c ≠ 1) :
    ∃ w : NumberField.InfinitePlace k, ∀ a : kˣ,
      Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a c = 1 ↔ IsNegAt w a := by
  haveI : CharZero Ω :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective k Ω)
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ k Ω
  have hc' : c.toRingEquiv * c.toRingEquiv = 1 := by
    rw [show c.toRingEquiv = (c : Ω ≃+* Ω) from rfl]
    have h2 : (c * c : Ω ≃ₐ[k] Ω) = 1 := by rw [← pow_two, hc]
    exact_mod_cast congrArg (fun e : Ω ≃ₐ[k] Ω => (e : Ω ≃+* Ω)) h2
  have hc1' : c.toRingEquiv ≠ 1 := by
    intro h
    apply hc1
    ext x
    have := congrArg (fun e : Ω ≃+* Ω => e x) h
    simpa [show c.toRingEquiv = (c : Ω ≃+* Ω) from rfl] using this
  haveI : Fact (c.toRingEquiv * c.toRingEquiv = 1) := ⟨hc'⟩
  haveI : Fact (c.toRingEquiv ≠ 1) := ⟨hc1'⟩
  obtain ⟨ρ, hρinj, hρ⟩ := exists_orderEmbedding_fixSub (Ω := Ω) (c := c.toRingEquiv)
  let τ : k →+* ↥(Work.SSGRoute.InvAux.fixSub c.toRingEquiv) :=
    { toFun := fun x => ⟨algebraMap k Ω x, by
        change c.toRingEquiv (algebraMap k Ω x) = algebraMap k Ω x
        rw [show c.toRingEquiv = (c : Ω ≃+* Ω) from rfl]
        exact c.commutes x⟩
      map_one' := Subtype.ext (map_one _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y) }
  have hτ : ∀ x : k, ((τ x : ↥(Work.SSGRoute.InvAux.fixSub c.toRingEquiv)) : Ω) =
      algebraMap k Ω x := fun x => rfl
  let τρ : k →+* ℝ := ρ.toRingHom.comp τ
  let φ : k →+* ℂ := (algebraMap ℝ ℂ).comp τρ
  let w : NumberField.InfinitePlace k := NumberField.InfinitePlace.mk φ
  have hφreal : NumberField.ComplexEmbedding.IsReal φ := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    show (starRingEnd ℂ) (φ x) = φ x
    rw [show φ x = ((τρ x : ℝ) : ℂ) from rfl, starRingEnd_apply]
    exact Complex.conj_ofReal _
  have hw : w.IsReal := ⟨φ, hφreal, rfl⟩
  have hψ : NumberField.InfinitePlace.embedding_of_isReal hw = τρ := by
    ext x
    apply Complex.ofReal_injective
    rw [NumberField.InfinitePlace.embedding_of_isReal_apply,
      NumberField.InfinitePlace.embedding_mk_eq_of_isReal hφreal]
    rfl
  have hsign : ∀ a : kˣ, IsNegAt w a ↔ (ρ.toRingHom.comp τ) (a : k) < 0 := by
    intro a
    rw [isNegAt_iff hw, hψ]
  refine ⟨w, fun a => ?_⟩
  have hzero : Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a c = 0 ↔ ¬ IsNegAt w a := by
    rw [kummerChar_eq_zero_iff_mem_normSet ζ hζ c hc a]
    rw [← not_not (a := algebraMap k Ω (a : k) ∈ Work.SSGRoute.TwoTorsion.normSet c.toRingEquiv)]
    rw [← neg_iff_not_mem_normSet_of_orderEmbedding (c := c.toRingEquiv) ρ hρ τ hτ a]
    exact (not_congr (hsign a)).symm
  exact (zmodTwo_eq_one_iff_ne_zero _).trans (by
    rw [Ne, hzero]
    exact not_not)

end RealPlace


/-! ## Two ring homomorphisms `k → ℝ` with the same signs coincide -/

section Signs

variable {k : Type} [Field k] [NumberField k]

/-- A real place is determined by the signs of the units of `k`: two ring homomorphisms `k → ℝ`
which are negative on the same units are equal. -/
theorem ringHom_ext_of_signs {σ₁ σ₂ : k →+* ℝ}
    (h : ∀ a : kˣ, σ₁ (a : k) < 0 ↔ σ₂ (a : k) < 0) : σ₁ = σ₂ := by
  have key : ∀ (τ₁ τ₂ : k →+* ℝ), (∀ a : kˣ, τ₁ (a : k) < 0 ↔ τ₂ (a : k) < 0) →
      ∀ x : k, τ₁ x < τ₂ x → False := by
    intro τ₁ τ₂ hh x hlt
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have hy : x - (q : k) ≠ 0 := by
      intro hzero
      have h1 : τ₁ (x - (q : k)) = 0 := by rw [hzero, map_zero]
      rw [map_sub, map_ratCast] at h1
      linarith
    have h1 : τ₁ ((x - (q : k) : k)) < 0 := by
      rw [map_sub, map_ratCast]
      linarith
    have h2 : ¬ (τ₂ ((x - (q : k) : k)) < 0) := by
      rw [map_sub, map_ratCast]
      linarith
    exact h2 ((hh (Units.mk0 _ hy)).mp h1)
  ext x
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key σ₁ σ₂ h x hlt
  · exact key σ₂ σ₁ (fun a => (h a).symm) x hlt

end Signs

/-- The ring equivalence from a field onto the image of a ring homomorphism into `ℝ`. -/
noncomputable def fieldRangeEquiv {F : Type} [Field F] (ρ : F →+* ℝ) : F ≃+* ↥(ρ.fieldRange) :=
  RingEquiv.ofBijective
    ({ toFun := fun x => ⟨ρ x, RingHom.mem_fieldRange.mpr ⟨x, rfl⟩⟩
       map_one' := Subtype.ext (map_one ρ)
       map_zero' := Subtype.ext (map_zero ρ)
       map_add' := fun x y => Subtype.ext (map_add ρ x y)
       map_mul' := fun x y => Subtype.ext (map_mul ρ x y) } : F →+* ↥(ρ.fieldRange))
    ⟨fun x y hxy => ρ.injective (congrArg Subtype.val hxy),
      fun y => by
        obtain ⟨x, hx⟩ := RingHom.mem_fieldRange.mp y.2
        exact ⟨x, Subtype.ext hx⟩⟩

@[simp] lemma fieldRangeEquiv_apply_coe {F : Type} [Field F] (ρ : F →+* ℝ) (x : F) :
    ((fieldRangeEquiv ρ x : ↥(ρ.fieldRange)) : ℝ) = ρ x := rfl

/-! ## Conjugacy of involutions with the same Kummer character -/

section Conjugacy

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]

/-- The general form of `Work.SSGRoute.InvAux.conjugate_of_ringEquiv`, keeping track of the
isomorphism of the fixed fields which the conjugating automorphism realises. -/
theorem exists_conjugate_of_fixSubRingEquiv {c₁ c₂ : Ω ≃+* Ω} (hc₁ : c₁ * c₁ = 1)
    (hc₂ : c₂ * c₂ = 1) (hn₁ : c₁ ≠ 1) (hn₂ : c₂ ≠ 1)
    (e : ↥(Work.SSGRoute.InvAux.fixSub c₁) ≃+* ↥(Work.SSGRoute.InvAux.fixSub c₂)) :
    ∃ σ : Ω ≃+* Ω, σ * c₁ * σ⁻¹ = c₂ ∧
      ∀ a : ↥(Work.SSGRoute.InvAux.fixSub c₁), σ (a : Ω) = (e a : Ω) := by
  have h₁ : IsAlgClosure ↥(Work.SSGRoute.InvAux.fixSub c₁) Ω :=
    ⟨inferInstance, Work.SSGRoute.InvAux.algebra_isAlgebraic_over_fixSub hc₁⟩
  have h₂ : IsAlgClosure ↥(Work.SSGRoute.InvAux.fixSub c₂) Ω :=
    ⟨inferInstance, Work.SSGRoute.InvAux.algebra_isAlgebraic_over_fixSub hc₂⟩
  set σ : Ω ≃+* Ω := IsAlgClosure.equivOfEquiv Ω Ω e with hσdef
  have hσa : ∀ a : ↥(Work.SSGRoute.InvAux.fixSub c₁), σ (a : Ω) = (e a : Ω) := by
    intro a
    rw [hσdef]
    exact IsAlgClosure.equivOfEquiv_algebraMap (L := Ω) (M := Ω) e a
  refine ⟨σ, ?_, hσa⟩
  have hd : (σ * c₁ * σ⁻¹) * (σ * c₁ * σ⁻¹) = 1 := by
    rw [show (σ * c₁ * σ⁻¹) * (σ * c₁ * σ⁻¹) = σ * (c₁ * c₁) * σ⁻¹ from by group, hc₁]
    group
  have hd1 : σ * c₁ * σ⁻¹ ≠ 1 := by
    intro h
    apply hn₁
    have h2 : (σ * c₁ * σ⁻¹) * σ = 1 * σ := by rw [h]
    rw [show (σ * c₁ * σ⁻¹) * σ = σ * c₁ from by group, one_mul] at h2
    exact mul_left_cancel h2
  have hfix : ∀ x : Ω, c₂ x = x → (σ * c₁ * σ⁻¹) x = x := by
    intro x hx
    let a : ↥(Work.SSGRoute.InvAux.fixSub c₁) := e.symm ⟨x, hx⟩
    have hσax : σ (a : Ω) = x := by
      rw [hσa]
      simp [a]
    have hax : (a : Ω) = σ.symm x := by
      rw [← hσax, RingEquiv.symm_apply_apply]
    have hca : c₁ (a : Ω) = (a : Ω) := a.2
    simp only [RingAut.mul_apply, RingAut.inv_apply]
    rw [← hax, hca, hσax]
  exact Work.SSGRoute.InvAux.eq_of_fixes_fixSub hc₂ hn₂ hd hd1 hfix

end Conjugacy

section SameKummerChar

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

/-- **The Artin–Schreier dictionary (uniqueness half).**  Two non-trivial involutions of `G_k` with
the same Kummer character on `kˣ` are conjugate. -/
theorem conjugate_of_same_kummerChar (ζ : k) (hζ : IsPrimitiveRoot ζ 2)
    (c₁ c₂ : Ω ≃ₐ[k] Ω) (hc₁ : c₁ ^ 2 = 1) (hn₁ : c₁ ≠ 1) (hc₂ : c₂ ^ 2 = 1) (hn₂ : c₂ ≠ 1)
    (h : ∀ a : kˣ, Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a c₁ = 0 ↔
      Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a c₂ = 0) :
    ∃ σ : Ω ≃ₐ[k] Ω, c₂ = σ * c₁ * σ⁻¹ := by
  haveI : CharZero Ω :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective k Ω)
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ k Ω
  have hc₁' : c₁.toRingEquiv * c₁.toRingEquiv = 1 := by
    rw [show c₁.toRingEquiv = (c₁ : Ω ≃+* Ω) from rfl]
    have h2 : (c₁ * c₁ : Ω ≃ₐ[k] Ω) = 1 := by rw [← pow_two, hc₁]
    exact_mod_cast congrArg (fun e : Ω ≃ₐ[k] Ω => (e : Ω ≃+* Ω)) h2
  have hn₁' : c₁.toRingEquiv ≠ 1 := by
    intro hh
    apply hn₁
    ext x
    have := congrArg (fun e : Ω ≃+* Ω => e x) hh
    simpa [show c₁.toRingEquiv = (c₁ : Ω ≃+* Ω) from rfl] using this
  have hc₂' : c₂.toRingEquiv * c₂.toRingEquiv = 1 := by
    rw [show c₂.toRingEquiv = (c₂ : Ω ≃+* Ω) from rfl]
    have h2 : (c₂ * c₂ : Ω ≃ₐ[k] Ω) = 1 := by rw [← pow_two, hc₂]
    exact_mod_cast congrArg (fun e : Ω ≃ₐ[k] Ω => (e : Ω ≃+* Ω)) h2
  have hn₂' : c₂.toRingEquiv ≠ 1 := by
    intro hh
    apply hn₂
    ext x
    have := congrArg (fun e : Ω ≃+* Ω => e x) hh
    simpa [show c₂.toRingEquiv = (c₂ : Ω ≃+* Ω) from rfl] using this
  haveI : Fact (c₁.toRingEquiv * c₁.toRingEquiv = 1) := ⟨hc₁'⟩
  haveI : Fact (c₁.toRingEquiv ≠ 1) := ⟨hn₁'⟩
  haveI : Fact (c₂.toRingEquiv * c₂.toRingEquiv = 1) := ⟨hc₂'⟩
  haveI : Fact (c₂.toRingEquiv ≠ 1) := ⟨hn₂'⟩
  obtain ⟨ρ₁, hρ₁inj, hρ₁⟩ := exists_orderEmbedding_fixSub (Ω := Ω) (c := c₁.toRingEquiv)
  obtain ⟨ρ₂, hρ₂inj, hρ₂⟩ := exists_orderEmbedding_fixSub (Ω := Ω) (c := c₂.toRingEquiv)
  let τ₁ : k →+* ↥(Work.SSGRoute.InvAux.fixSub c₁.toRingEquiv) :=
    { toFun := fun x => ⟨algebraMap k Ω x, by
        change c₁.toRingEquiv (algebraMap k Ω x) = algebraMap k Ω x
        rw [show c₁.toRingEquiv = (c₁ : Ω ≃+* Ω) from rfl]
        exact c₁.commutes x⟩
      map_one' := Subtype.ext (map_one _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y) }
  let τ₂ : k →+* ↥(Work.SSGRoute.InvAux.fixSub c₂.toRingEquiv) :=
    { toFun := fun x => ⟨algebraMap k Ω x, by
        change c₂.toRingEquiv (algebraMap k Ω x) = algebraMap k Ω x
        rw [show c₂.toRingEquiv = (c₂ : Ω ≃+* Ω) from rfl]
        exact c₂.commutes x⟩
      map_one' := Subtype.ext (map_one _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y) }
  have hτ₁ : ∀ x : k, ((τ₁ x : ↥(Work.SSGRoute.InvAux.fixSub c₁.toRingEquiv)) : Ω) =
      algebraMap k Ω x := fun x => rfl
  have hτ₂ : ∀ x : k, ((τ₂ x : ↥(Work.SSGRoute.InvAux.fixSub c₂.toRingEquiv)) : Ω) =
      algebraMap k Ω x := fun x => rfl
  have hsign : ∀ a : kˣ, (ρ₁.toRingHom.comp τ₁) (a : k) < 0 ↔
      (ρ₂.toRingHom.comp τ₂) (a : k) < 0 := by
    intro a
    rw [neg_iff_not_mem_normSet_of_orderEmbedding (c := c₁.toRingEquiv) ρ₁ hρ₁ τ₁ hτ₁ a,
      neg_iff_not_mem_normSet_of_orderEmbedding (c := c₂.toRingEquiv) ρ₂ hρ₂ τ₂ hτ₂ a]
    have hχ := h a
    rw [kummerChar_eq_zero_iff_mem_normSet ζ hζ c₁ hc₁ a,
      kummerChar_eq_zero_iff_mem_normSet ζ hζ c₂ hc₂ a] at hχ
    exact not_congr hχ
  have hσ : (ρ₁.toRingHom.comp τ₁) = (ρ₂.toRingHom.comp τ₂) := ringHom_ext_of_signs hsign
  have himg : (ρ₁ : ↥(Work.SSGRoute.InvAux.fixSub c₁.toRingEquiv) →+* ℝ).fieldRange =
      (ρ₂ : ↥(Work.SSGRoute.InvAux.fixSub c₂.toRingEquiv) →+* ℝ).fieldRange := by
    rw [orderEmbedding_fixSub_fieldRange ρ₁ hρ₁, orderEmbedding_fixSub_fieldRange ρ₂ hρ₂]
  -- the isomorphism of fixed fields induced by the two order embeddings
  have hex : ∀ x : ↥(Work.SSGRoute.InvAux.fixSub c₁.toRingEquiv),
      ∃ y : ↥(Work.SSGRoute.InvAux.fixSub c₂.toRingEquiv), ρ₂ y = ρ₁ x := by
    intro x
    have hx : ρ₁ x ∈ (ρ₂ : ↥(Work.SSGRoute.InvAux.fixSub c₂.toRingEquiv) →+* ℝ).fieldRange := by
      rw [← himg]
      exact (fieldRangeEquiv (ρ₁ : ↥(Work.SSGRoute.InvAux.fixSub c₁.toRingEquiv) →+* ℝ) x).2
    obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.mp hx
    exact ⟨y, hy⟩
  let efun : ↥(Work.SSGRoute.InvAux.fixSub c₁.toRingEquiv) →
      ↥(Work.SSGRoute.InvAux.fixSub c₂.toRingEquiv) := fun x => Classical.choose (hex x)
  have hefun : ∀ x, ρ₂ (efun x) = ρ₁ x := fun x => Classical.choose_spec (hex x)
  have efun_inj : Function.Injective efun := fun x y hxy =>
    hρ₁inj (by rw [← hefun x, ← hefun y, hxy])
  have efun_surj : Function.Surjective efun := by
    intro y
    have hy : ρ₂ y ∈ (ρ₁ : ↥(Work.SSGRoute.InvAux.fixSub c₁.toRingEquiv) →+* ℝ).fieldRange := by
      rw [himg]
      exact (fieldRangeEquiv (ρ₂ : ↥(Work.SSGRoute.InvAux.fixSub c₂.toRingEquiv) →+* ℝ) y).2
    obtain ⟨x, hx⟩ := RingHom.mem_fieldRange.mp hy
    exact ⟨x, hρ₂inj (by rw [hefun x]; exact hx)⟩
  let e : ↥(Work.SSGRoute.InvAux.fixSub c₁.toRingEquiv) ≃+*
      ↥(Work.SSGRoute.InvAux.fixSub c₂.toRingEquiv) :=
    RingEquiv.ofBijective
      ({ toFun := efun
         map_one' := hρ₂inj (by rw [hefun 1]; simp)
         map_zero' := hρ₂inj (by rw [hefun 0]; simp)
         map_add' := fun x y => hρ₂inj (by rw [hefun (x + y)]; simp [hefun])
         map_mul' := fun x y => hρ₂inj (by rw [hefun (x * y)]; simp [hefun]) }
        : ↥(Work.SSGRoute.InvAux.fixSub c₁.toRingEquiv) →+*
          ↥(Work.SSGRoute.InvAux.fixSub c₂.toRingEquiv))
      ⟨efun_inj, efun_surj⟩
  have he_val : ∀ x, ρ₂ (e x) = ρ₁ x := hefun
  have he : ∀ x : k, e (τ₁ x) = τ₂ x := by
    intro x
    apply hρ₂inj
    rw [he_val]
    show (ρ₁.toRingHom.comp τ₁) x = (ρ₂.toRingHom.comp τ₂) x
    rw [hσ]
  obtain ⟨σ, hconj, hfixk⟩ := exists_conjugate_of_fixSubRingEquiv hc₁' hc₂' hn₁' hn₂' e
  have hk : ∀ x : k, σ (algebraMap k Ω x) = algebraMap k Ω x := by
    intro x
    have h1 := hfixk (τ₁ x)
    rw [show (τ₁ x : Ω) = algebraMap k Ω x from rfl] at h1
    rw [h1, he x]
    rfl
  let σa : Ω ≃ₐ[k] Ω := AlgEquiv.ofRingEquiv (f := σ) (fun x => hk x)
  refine ⟨σa, ?_⟩
  ext x
  have h := congrArg (fun ee : Ω ≃+* Ω => ee x) hconj
  change c₂ x = (σ * c₁.toRingEquiv * σ⁻¹) x
  exact h.symm

end SameKummerChar

/-! ## The complex conjugation at a real place -/

section ConjInv

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

/-- The involution of `G_k` attached to a real place `w`: a complex conjugation at `w`, i.e. an
involution whose fixed field is the real closure of `k` at `w`. -/
noncomputable def conjInv (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (w : NumberField.InfinitePlace k)
    (hw : w.IsReal) : Ω ≃ₐ[k] Ω :=
  Classical.choose (exists_conjInv_kummerChar_eq_zero_iff ζ hζ w hw)

lemma conjInv_sq (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (w : NumberField.InfinitePlace k)
    (hw : w.IsReal) : conjInv (Ω := Ω) ζ hζ w hw ^ 2 = 1 :=
  (Classical.choose_spec (exists_conjInv_kummerChar_eq_zero_iff ζ hζ w hw)).1

lemma conjInv_ne_one (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (w : NumberField.InfinitePlace k)
    (hw : w.IsReal) : conjInv (Ω := Ω) ζ hζ w hw ≠ 1 :=
  (Classical.choose_spec (exists_conjInv_kummerChar_eq_zero_iff ζ hζ w hw)).2.1

lemma conjInv_kummerChar_eq_zero_iff (ζ : k) (hζ : IsPrimitiveRoot ζ 2)
    (w : NumberField.InfinitePlace k) (hw : w.IsReal) (a : kˣ) :
    Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a (conjInv (Ω := Ω) ζ hζ w hw) = 0 ↔
      ¬ IsNegAt w a :=
  (Classical.choose_spec (exists_conjInv_kummerChar_eq_zero_iff ζ hζ w hw)).2.2 a

lemma conjInv_kummerChar_eq_one_iff (ζ : k) (hζ : IsPrimitiveRoot ζ 2)
    (w : NumberField.InfinitePlace k) (hw : w.IsReal) (a : kˣ) :
    Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a (conjInv (Ω := Ω) ζ hζ w hw) = 1 ↔
      IsNegAt w a := by
  rw [zmodTwo_eq_one_iff_ne_zero, Ne, conjInv_kummerChar_eq_zero_iff ζ hζ w hw a, not_not]

end ConjInv

end Work.SSGRoute.ZDataTwo
