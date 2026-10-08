/-
Area A11 (p-stability) of the Feit--Thompson drive: the "quadratic" GL-core.

The odd-order form of Hall--Higman B (`Work.HallHigman.GLCore.glCore`, proved in area A10)
applies only to `p'`-groups `Q` of *odd* order.  For the p-stability statement needed by the
odd order theorem one must allow `Q` of even order, at the price of assuming that every
`2`-subgroup of `Q` is abelian (or `p ≥ 5`); in exchange the hypothesis on `X` is *quadratic*
(`(X - 1) ^ 2 = 0` rather than `(X - 1) ^ (p - 1) = 0`), which is exactly the form in which the
hypothesis arises from a `p`-subgroup all of whose elements act quadratically.

This file contains the hypothesis structure `QuadCore` and its transport lemmas.
-/
import Mathlib
import Submission.Work.HallHigman.GLCore.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u v w

namespace Work.PStable.Quad

open scoped commutatorElement

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

/-- The hypothesis of the quadratic GL-core: `𝒬 ≤ GL(V)` is finite of order prime to `p`, `X`
has order `p`, normalises `𝒬`, does not commute with `𝒬`, and either `p ≥ 5` or every
`2`-subgroup of `𝒬` is abelian. -/
structure QuadCore (p : ℕ) (Q : Subgroup (Module.End K V)ˣ) (X : (Module.End K V)ˣ) : Prop where
  /-- `𝒬` is finite. -/
  finite : Finite Q
  /-- `p ∤ |𝒬|`. -/
  cop : ¬ p ∣ Nat.card Q
  /-- `X` has order `p`. -/
  pow : X ^ p = 1
  /-- `X` normalises `𝒬`. -/
  norm : ∀ a ∈ Q, X * a * X⁻¹ ∈ Q
  /-- `X` does not commute with `𝒬`. -/
  noncomm : ∃ a ∈ Q, a * X ≠ X * a
  /-- Either `p ≥ 5`, or every `2`-subgroup of `𝒬` is abelian. -/
  two : p ≥ 5 ∨ ∀ S : Subgroup ↥Q, IsPGroup 2 ↥S → IsMulCommutative ↥S

/-! ### Elementary consequences -/

/-- A `q`-group with `q ≠ 2` has odd order. -/
lemma odd_card_of_isPGroup {H : Type*} [Group H] {Q : Subgroup H} [Finite Q] {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hQq : IsPGroup q Q) : Odd (Nat.card Q) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQq
  rw [hn]
  exact Odd.pow (hq.odd_iff.mpr hq3)

/-- The odd-order core hypothesis of area A10 follows from the quadratic one when `|𝒬|` is odd. -/
lemma _root_.Work.HallHigman.CoreHyp.ofQuadCore {p : ℕ}
    {Q : Subgroup (Module.End K V)ˣ} {X : (Module.End K V)ˣ} (h : QuadCore p Q X)
    (hodd : Odd (Nat.card Q)) : Work.HallHigman.CoreHyp p Q X :=
  ⟨h.finite, hodd, h.cop, h.pow, h.norm, h.noncomm⟩

/-- If every Sylow `2`-subgroup of a finite group is abelian, so is every `2`-subgroup. -/
lemma isMulCommutative_of_isPGroup_two_of_sylow {H : Type*} [Group H] [Finite H]
    (h : ∀ T : Sylow 2 H, IsMulCommutative ↥(T : Subgroup H)) {S : Subgroup H}
    (hS : IsPGroup 2 ↥S) : IsMulCommutative ↥S := by
  obtain ⟨T, hST⟩ := IsPGroup.exists_le_sylow (p := 2) (P := S) hS
  haveI : IsMulCommutative ↥(T : Subgroup H) := h T
  rw [isMulCommutative_iff] at this ⊢
  intro x y
  have hxy := this ⟨(x : H), hST x.2⟩ ⟨(y : H), hST y.2⟩
  exact Subtype.ext (by simpa using congrArg Subtype.val hxy)

/-- The property "every `2`-subgroup is abelian" is inherited by quotients. -/
lemma isMulCommutative_of_isPGroup_two_of_surjective {A B : Type*} [Group A] [Group B] [Finite A]
    {ψ : A →* B} (hψ : Function.Surjective ψ)
    (h : ∀ S : Subgroup A, IsPGroup 2 ↥S → IsMulCommutative ↥S) {S' : Subgroup B}
    (hS' : IsPGroup 2 ↥S') : IsMulCommutative ↥S' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hS'T⟩ := IsPGroup.exists_le_sylow (p := 2) (P := S') hS'
  obtain ⟨P, hPT⟩ := Sylow.mapSurjective_surjective (p := 2) hψ T
  have hPabel : IsMulCommutative ↥(P : Subgroup A) := h (P : Subgroup A) P.2
  have hTabel : IsMulCommutative ↥(T : Subgroup B) := by
    rw [← hPT, Sylow.coe_mapSurjective]
    exact Subgroup.map_isMulCommutative (P : Subgroup A) ψ
  rw [isMulCommutative_iff] at hTabel ⊢
  intro x y
  have hxy := hTabel ⟨(x : B), hS'T x.2⟩ ⟨(y : B), hS'T y.2⟩
  exact Subtype.ext (by simpa using congrArg Subtype.val hxy)

/-- The property "every `2`-subgroup is abelian" is inherited by subgroups. -/
lemma isMulCommutative_of_isPGroup_two_of_le {A : Type*} [Group A]
    (h : ∀ S : Subgroup A, IsPGroup 2 ↥S → IsMulCommutative ↥S) {R : Subgroup A}
    {S : Subgroup ↥R} (hS : IsPGroup 2 ↥S) : IsMulCommutative ↥S := by
  set S' : Subgroup A := S.map R.subtype with hS'def
  have hS' : IsPGroup 2 ↥S' := hS.map R.subtype
  haveI : IsMulCommutative ↥S' := h S' hS'
  rw [isMulCommutative_iff] at this ⊢
  intro x y
  have hx : (((x : ↥S) : ↥R) : A) ∈ S' := Subgroup.mem_map_of_mem R.subtype x.2
  have hy : (((y : ↥S) : ↥R) : A) ∈ S' := Subgroup.mem_map_of_mem R.subtype y.2
  have hxy := this ⟨(((x : ↥S) : ↥R) : A), hx⟩ ⟨(((y : ↥S) : ↥R) : A), hy⟩
  refine Subtype.ext (Subtype.ext ?_)
  simpa using congrArg Subtype.val hxy

/-- The property "every `2`-subgroup is abelian" is inherited by isomorphic images. -/
lemma isMulCommutative_of_isPGroup_two_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∀ S : Subgroup A, IsPGroup 2 ↥S → IsMulCommutative ↥S) {S' : Subgroup B}
    (hS' : IsPGroup 2 ↥S') : IsMulCommutative ↥S' := by
  have hT : IsPGroup 2 ↥(S'.comap e.toMonoidHom) :=
    hS'.comap_of_injective e.toMonoidHom e.injective
  haveI : IsMulCommutative ↥(S'.comap e.toMonoidHom) := h _ hT
  have hmap : (S'.comap e.toMonoidHom).map e.toMonoidHom = S' := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      simpa [Subgroup.mem_comap] using hx
  rw [← hmap]
  exact Subgroup.map_isMulCommutative _ e.toMonoidHom

/-- The property "every `2`-subgroup is abelian" is inherited by subgroups of the group. -/
lemma two_of_subgroup_le {A : Type*} [Group A] {Q R : Subgroup A} (hRQ : R ≤ Q)
    (h : ∀ S : Subgroup ↥Q, IsPGroup 2 ↥S → IsMulCommutative ↥S) :
    ∀ S : Subgroup ↥R, IsPGroup 2 ↥S → IsMulCommutative ↥S := by
  intro S hS
  have hS' : IsPGroup 2 ↥(S.map (Subgroup.inclusion hRQ)) := hS.map _
  haveI habel : IsMulCommutative ↥(S.map (Subgroup.inclusion hRQ)) := h _ hS'
  rw [isMulCommutative_iff] at habel ⊢
  intro x y
  refine Subtype.ext (Subtype.ext ?_)
  have hx : Subgroup.inclusion hRQ x ∈ S.map (Subgroup.inclusion hRQ) :=
    Subgroup.mem_map_of_mem _ x.2
  have hy : Subgroup.inclusion hRQ y ∈ S.map (Subgroup.inclusion hRQ) :=
    Subgroup.mem_map_of_mem _ y.2
  have h2 := habel ⟨Subgroup.inclusion hRQ x, hx⟩ ⟨Subgroup.inclusion hRQ y, hy⟩
  have h3 := congrArg (fun z : ↥(S.map (Subgroup.inclusion hRQ)) => ((z : ↥Q) : A)) h2
  simpa using h3

/-! ### Transport of the quadratic core hypothesis -/

/-- `QuadCore` is preserved by a surjective homomorphism on the linear part. -/
lemma QuadCore.map_surjective {p : ℕ} {Q : Subgroup (Module.End K V)ˣ}
    {X : (Module.End K V)ˣ} (h : QuadCore p Q X) {W : Type*} [AddCommGroup W] [Module K W]
    {Q' : Subgroup (Module.End K W)ˣ} {X' : (Module.End K W)ˣ} (φ : ↥Q →* ↥Q')
    (hφ : Function.Surjective φ) (hpow : X' ^ p = 1)
    (hnorm : ∀ a ∈ Q', X' * a * X'⁻¹ ∈ Q') (hnc : ∃ a ∈ Q', a * X' ≠ X' * a) :
    QuadCore p Q' X' where
  finite := by
    haveI : Finite ↥Q := h.finite
    exact Finite.of_surjective φ hφ
  cop := fun hd => h.cop (hd.trans (Subgroup.card_dvd_of_surjective (f := φ) hφ))
  pow := hpow
  norm := hnorm
  noncomm := hnc
  two := by
    haveI : Finite ↥Q := h.finite
    rcases h.two with h5 | h2
    · exact Or.inl h5
    · refine Or.inr ?_
      intro S' hS'
      exact isMulCommutative_of_isPGroup_two_of_surjective hφ h2 hS'

/-- `QuadCore` is preserved by an injective ring homomorphism on the linear part (used for the
extension of scalars to an algebraically closed field). -/
lemma QuadCore.unitsMap {p : ℕ} {Q : Subgroup (Module.End K V)ˣ} {X : (Module.End K V)ˣ}
    (h : QuadCore p Q X) {L : Type*} [Field L] {W : Type*} [AddCommGroup W] [Module L W]
    (F : Module.End K V →+* Module.End L W) (hF : Function.Injective F) :
    QuadCore p (Q.map (Units.map F.toMonoidHom)) (Units.map F.toMonoidHom X) where
  finite := by
    haveI : Finite ↥Q := h.finite
    exact Finite.of_equiv ↥Q (Subgroup.equivMapOfInjective Q (Units.map F.toMonoidHom)
      (Units.map_injective hF)).toEquiv
  cop := by
    rw [Subgroup.card_map_of_injective (Units.map_injective hF)]
    exact h.cop
  pow := by
    rw [← map_pow, h.pow, map_one]
  norm := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    have heq : (Units.map F.toMonoidHom) (X * b * X⁻¹)
        = (Units.map F.toMonoidHom) X * (Units.map F.toMonoidHom) b
            * ((Units.map F.toMonoidHom) X)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [← heq]
    exact Subgroup.mem_map_of_mem _ (h.norm b hb)
  noncomm := by
    obtain ⟨a, ha, hne⟩ := h.noncomm
    refine ⟨Units.map F.toMonoidHom a, Subgroup.mem_map_of_mem _ ha, fun hcontra => ?_⟩
    apply hne
    apply Units.map_injective hF
    rw [map_mul, map_mul]
    exact Units.ext (by
      have h1 := congrArg (fun u : (Module.End L W)ˣ => ((u : Module.End L W))) hcontra
      simpa using h1)
  two := by
    rcases h.two with h5 | h2
    · exact Or.inl h5
    · refine Or.inr ?_
      intro S' hS'
      exact isMulCommutative_of_isPGroup_two_of_equiv
        (Subgroup.equivMapOfInjective Q (Units.map F.toMonoidHom)
          (Units.map_injective hF)) h2 hS'

end Work.PStable.Quad
