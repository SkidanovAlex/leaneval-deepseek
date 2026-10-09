/-
Copyright (c) 2025. All rights reserved.

# Every extension comes from a `2`-cocycle

Given a group extension `1 → A → E → Q → 1` of `Q` by an abelian group `A` (with the prescribed
conjugation action of `Q` on `A`), the extension is equivalent to the extension
`Extension.ofCocycle Q A c` constructed from a suitable `2`-cocycle `c ∈ Z²(Q, A)`.

The cocycle is obtained from a set-theoretic section `σ : Q → E` of the projection, normalized so
that `σ 1 = 1`: writing every `e : E` uniquely as `inl (ofAdd (α e)) * σ (rightHom e)` with
`α e ∈ A`, the cocycle is `c q r = α (σ q * σ r)`.  It satisfies `c (q, 1) = 0` for all `q`, so it
agrees with its normalization `normCocycle c`, and the map `e ↦ (α e, rightHom e)` is an
equivalence of extensions onto the twisted product `A × Q` with multiplication
`(a, q) * (b, r) = (a + q • b + c (q, r), q * r)`.
-/
import Mathlib
import Submission.Work.GroupCohomology.Extension
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.GroupCohomology

open Multiplicative

variable {Q : Type u} {A : Type v} [Group Q] [AddCommGroup A] [DistribMulAction Q A]

/-- Every extension of `Q` by `A` is equivalent to `Extension.ofCocycle Q A c` for a `2`-cocycle
`c` which is normalized in the sense that `c (q, 1) = 0` for every `q : Q`. -/
theorem exists_cocycle_equiv_aux (X : Extension Q A) :
    ∃ c : Z2 Q A, (∀ q, (c : Q × Q → A) (q, 1) = 0) ∧
      Nonempty (Extension.Equiv X (Extension.ofCocycle Q A c)) := by
  letI := X.groupE
  -- a set-theoretic section of the projection, normalized so that `σ 1 = 1`
  obtain ⟨σ, hσ, hσ1⟩ : ∃ σ : Q → X.E, (∀ q, X.ext.rightHom (σ q) = q) ∧ σ 1 = 1 := by
    choose s hs using X.ext.rightHom_surjective
    refine ⟨fun q => s q * (s 1)⁻¹, ?_, ?_⟩
    · intro q; rw [map_mul, map_inv, hs q, hs 1, inv_one, mul_one]
    · show s 1 * (s 1)⁻¹ = 1; rw [mul_inv_cancel]
  -- `Multiplicative.ofAdd` turns addition in `A` into multiplication in `Multiplicative A`.
  have hmap_add : ∀ x y : A, X.ext.inl (Multiplicative.ofAdd (x + y))
      = X.ext.inl (Multiplicative.ofAdd x) * X.ext.inl (Multiplicative.ofAdd y) := by
    intro x y
    rw [ofAdd_add, X.ext.inl.map_mul]
  -- the `A`-coordinate `α e` of `e : E`, defined by `inl (ofAdd (α e)) = e * (σ (rightHom e))⁻¹`
  have hex : ∀ e : X.E,
      ∃ a : A, X.ext.inl (Multiplicative.ofAdd a) = e * (σ (X.ext.rightHom e))⁻¹ := by
    intro e
    have hmem : e * (σ (X.ext.rightHom e))⁻¹ ∈ X.ext.inl.range := by
      rw [X.ext.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, hσ, mul_inv_cancel]
    obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp hmem
    exact ⟨Multiplicative.toAdd n, hn⟩
  choose α hα using hex
  have inl_inj : ∀ {a b : A},
      X.ext.inl (Multiplicative.ofAdd a) = X.ext.inl (Multiplicative.ofAdd b) → a = b :=
    fun h => Multiplicative.ofAdd.injective (X.ext.inl_injective h)
  -- the cocycle `c₀ (q, r) = α (σ q * σ r)`
  let c₀ : Q × Q → A := fun p => α (σ p.1 * σ p.2)
  have hc0eq : ∀ q r : Q, σ q * σ r = X.ext.inl (Multiplicative.ofAdd (c₀ (q, r))) * σ (q * r) := by
    intro q r
    have h := hα (σ q * σ r)
    rw [map_mul, hσ q, hσ r] at h
    calc σ q * σ r = (σ q * σ r * (σ (q * r))⁻¹) * σ (q * r) := by group
      _ = X.ext.inl (Multiplicative.ofAdd (c₀ (q, r))) * σ (q * r) := by rw [← h]
  -- the decomposition `e = inl (ofAdd (α e)) * σ (rightHom e)`
  have decomp : ∀ e : X.E, X.ext.inl (Multiplicative.ofAdd (α e)) * σ (X.ext.rightHom e) = e := by
    intro e
    rw [hα e, mul_assoc, inv_mul_cancel, mul_one]
  -- `α` inverts the above decomposition
  have α_action : ∀ (a : A) (q : Q), α (X.ext.inl (Multiplicative.ofAdd a) * σ q) = a := by
    intro a q
    apply inl_inj
    have h : X.ext.rightHom (X.ext.inl (Multiplicative.ofAdd a) * σ q) = q := by
      rw [map_mul, X.ext.rightHom_inl, one_mul, hσ]
    rw [hα (X.ext.inl (Multiplicative.ofAdd a) * σ q), h, mul_assoc, mul_inv_cancel, mul_one]
  -- conjugation by an element of `inl '' A` is trivial, since `A` is abelian
  have conjAct_inl : ∀ n : Multiplicative A, X.ext.conjAct (X.ext.inl n) = 1 := by
    intro n
    apply MulEquiv.ext
    intro m
    rw [MulAut.one_apply]
    apply X.ext.inl_injective
    rw [X.ext.inl_conjAct_comm, ← map_mul, ← map_inv, ← map_mul]
    congr 1
    rw [mul_comm n m, mul_inv_cancel_right]
  -- hence the conjugation action only depends on the image in `Q`
  have conjAct_cast : ∀ (e f : X.E), X.ext.rightHom e = X.ext.rightHom f →
      X.ext.conjAct e = X.ext.conjAct f := by
    intro e f h
    have hker : e⁻¹ * f ∈ X.ext.inl.range := by
      rw [X.ext.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp hker
    have key : X.ext.conjAct f = X.ext.conjAct e := by
      calc X.ext.conjAct f = X.ext.conjAct (e * (e⁻¹ * f)) := by rw [mul_inv_cancel_left]
        _ = X.ext.conjAct e * X.ext.conjAct (e⁻¹ * f) := by rw [map_mul]
        _ = X.ext.conjAct e * 1 := by rw [← hn, conjAct_inl]
        _ = X.ext.conjAct e := mul_one _
    exact key.symm
  -- and realizes the prescribed action of `Q` on `A`
  have conjAct_smul : ∀ (e : X.E) (a : A),
      (X.ext.conjAct e) (Multiplicative.ofAdd a) = Multiplicative.ofAdd (X.ext.rightHom e • a) := by
    intro e a
    obtain ⟨f, hf, hfa⟩ := X.conjAct_eq (X.ext.rightHom e) a
    rw [conjAct_cast e f hf.symm, hfa]
  -- the resulting commutation rule between `σ` and `inl`
  have conj_mul : ∀ (e : X.E) (a : A),
      e * X.ext.inl (Multiplicative.ofAdd a) * e⁻¹
        = X.ext.inl (Multiplicative.ofAdd (X.ext.rightHom e • a)) := by
    intro e a
    rw [← X.ext.inl_conjAct_comm, conjAct_smul]
  have section_mul : ∀ (q : Q) (b : A),
      σ q * X.ext.inl (Multiplicative.ofAdd b)
        = X.ext.inl (Multiplicative.ofAdd (q • b)) * σ q := by
    intro q b
    have h := conj_mul (σ q) b
    rw [hσ q] at h
    calc σ q * X.ext.inl (Multiplicative.ofAdd b)
        = (σ q * X.ext.inl (Multiplicative.ofAdd b) * (σ q)⁻¹) * σ q := by group
      _ = X.ext.inl (Multiplicative.ofAdd (q • b)) * σ q := by rw [h]
  -- the multiplication of `E` in terms of the coordinates `(α, rightHom)`
  have mul_formula : ∀ (a : A) (q : Q) (b : A) (r : Q),
      (X.ext.inl (Multiplicative.ofAdd a) * σ q) * (X.ext.inl (Multiplicative.ofAdd b) * σ r)
        = X.ext.inl (Multiplicative.ofAdd (a + q • b + c₀ (q, r))) * σ (q * r) := by
    intro a q b r
    calc (X.ext.inl (Multiplicative.ofAdd a) * σ q) *
            (X.ext.inl (Multiplicative.ofAdd b) * σ r)
        = X.ext.inl (Multiplicative.ofAdd a) *
            (σ q * X.ext.inl (Multiplicative.ofAdd b)) * σ r := by group
      _ = X.ext.inl (Multiplicative.ofAdd a) *
            (X.ext.inl (Multiplicative.ofAdd (q • b)) * σ q) * σ r := by rw [section_mul q b]
      _ = (X.ext.inl (Multiplicative.ofAdd a) *
            X.ext.inl (Multiplicative.ofAdd (q • b))) * (σ q * σ r) := by group
      _ = X.ext.inl (Multiplicative.ofAdd (a + q • b)) * (σ q * σ r) := by rw [← hmap_add]
      _ = X.ext.inl (Multiplicative.ofAdd (a + q • b)) *
            (X.ext.inl (Multiplicative.ofAdd (c₀ (q, r))) * σ (q * r)) := by rw [hc0eq q r]
      _ = (X.ext.inl (Multiplicative.ofAdd (a + q • b)) *
            X.ext.inl (Multiplicative.ofAdd (c₀ (q, r)))) * σ (q * r) := by group
      _ = X.ext.inl (Multiplicative.ofAdd (a + q • b + c₀ (q, r))) * σ (q * r) := by
            rw [← hmap_add]
  have mul_decomp : ∀ e e' : X.E,
      X.ext.inl (Multiplicative.ofAdd
          (α e + X.ext.rightHom e • α e' + c₀ (X.ext.rightHom e, X.ext.rightHom e')))
        * σ (X.ext.rightHom e * X.ext.rightHom e') = e * e' := by
    intro e e'
    have h2 := mul_formula (α e) (X.ext.rightHom e) (α e') (X.ext.rightHom e')
    have h3 : (X.ext.inl (Multiplicative.ofAdd (α e)) * σ (X.ext.rightHom e)) *
        (X.ext.inl (Multiplicative.ofAdd (α e')) * σ (X.ext.rightHom e')) = e * e' := by
      rw [decomp e, decomp e']
    exact h2.symm.trans h3
  -- the coordinates make `E` a twisted product
  let φ : X.E → A × Q := fun e => (α e, X.ext.rightHom e)
  let ψ : A × Q → X.E := fun x => X.ext.inl (Multiplicative.ofAdd x.1) * σ x.2
  have ψ_φ : ∀ e : X.E, ψ (φ e) = e := by
    intro e
    exact decomp e
  have φ_ψ : ∀ x : A × Q, φ (ψ x) = x := by
    rintro ⟨a, q⟩
    show (α (X.ext.inl (Multiplicative.ofAdd a) * σ q),
      X.ext.rightHom (X.ext.inl (Multiplicative.ofAdd a) * σ q)) = (a, q)
    rw [α_action a q, map_mul, X.ext.rightHom_inl, one_mul, hσ]
  have hφ_mul : ∀ e e' : X.E, φ (e * e') = twMul Q A c₀ (φ e) (φ e') := by
    intro e e'
    rw [← mul_decomp e e']
    simp only [φ, twMul, Prod.mk.injEq]
    constructor
    · rw [α_action]
    · rw [map_mul, X.ext.rightHom_inl, one_mul, hσ]
  have hsurj : Function.Surjective φ := fun x => ⟨ψ x, φ_ψ x⟩
  -- `c₀` is a `2`-cocycle, because the twisted product is associative
  have hc₀ : c₀ ∈ Z2 Q A := by
    rw [mem_Z2_iff]
    intro g h k
    have hassoc : ∀ x y z : A × Q, twMul Q A c₀ (twMul Q A c₀ x y) z
        = twMul Q A c₀ x (twMul Q A c₀ y z) := by
      intro x y z
      obtain ⟨s, hs⟩ := hsurj x
      obtain ⟨t, ht⟩ := hsurj y
      obtain ⟨u, hu⟩ := hsurj z
      rw [← hs, ← ht, ← hu, ← hφ_mul s t, ← hφ_mul (s * t) u, mul_assoc, hφ_mul s (t * u),
        hφ_mul t u]
    have hkey := hassoc (0, g) (0, h) (0, k)
    simp only [twMul, smul_zero, add_zero, zero_add] at hkey
    have h1 := (Prod.ext_iff.mp hkey).1
    rw [add_comm (c₀ (g, h)) (c₀ (g * h, k))] at h1
    exact h1
  -- `c₀` is already normalized
  have hq1 : ∀ q : Q, c₀ (q, 1) = 0 := by
    intro q
    have h1 : c₀ (q, 1) = α (σ q) := by
      show α (σ q * σ 1) = α (σ q)
      rw [hσ1, mul_one]
    rw [h1]
    have h2 : α (σ q) = α (X.ext.inl (Multiplicative.ofAdd (0 : A)) * σ q) := by
      congr 1
      rw [ofAdd_zero, map_one, one_mul]
    rw [h2, α_action]
  have hcc : normCocycle Q A c₀ = c₀ := by
    funext p
    obtain ⟨q, r⟩ := p
    simp only [normCocycle_apply, hq1 q, sub_zero]
  refine ⟨⟨c₀, hc₀⟩, hq1, ?_⟩
  letI := (Extension.ofCocycle Q A (⟨c₀, hc₀⟩ : Z2 Q A)).groupE
  refine ⟨?_⟩
  refine { toMulEquiv := ?_, inl_comm := ?_, rightHom_comm := ?_ }
  · refine { toFun := φ, invFun := ψ, left_inv := ψ_φ, right_inv := φ_ψ, map_mul' := ?_ }
    intro e e'
    show φ (e * e') = twMul Q A (normCocycle Q A c₀) (φ e) (φ e')
    rw [hcc]
    exact hφ_mul e e'
  · funext n
    refine Prod.ext ?_ ?_
    · show α (X.ext.inl n) = Multiplicative.toAdd n
      have h3 : X.ext.inl n = X.ext.inl (Multiplicative.ofAdd (Multiplicative.toAdd n)) * σ 1 := by
        rw [hσ1, mul_one]
        rfl
      rw [h3, α_action]
    · show X.ext.rightHom (X.ext.inl n) = 1
      rw [X.ext.rightHom_inl]
  · funext e
    rfl

theorem exists_cocycle_equiv {Q : Type*} {A : Type*} [Group Q] [AddCommGroup A]
    [DistribMulAction Q A] (X : Work.GroupCohomology.Extension Q A) :
    ∃ c : Work.GroupCohomology.Z2 Q A, Nonempty (Work.GroupCohomology.Extension.Equiv X
      (Work.GroupCohomology.Extension.ofCocycle Q A c)) := by
  obtain ⟨c, _, h⟩ := exists_cocycle_equiv_aux X
  exact ⟨c, h⟩

end Work.GroupCohomology
