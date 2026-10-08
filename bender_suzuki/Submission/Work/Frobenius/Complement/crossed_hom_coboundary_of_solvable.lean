import Mathlib
import Submission.Work.Coprime.schurZassenhaus_conj_of_solvable_quotient

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Vanishing of `H¹` for a coprime action of a solvable group

If a finite solvable group `A` acts on a finite group `M` (multiplicatively, by automorphisms)
with `Nat.card A` coprime to `Nat.card M`, then every crossed homomorphism
(`1`-cocycle) `η : A → M`, i.e. every `η` with `η 1 = 1` and
`η (a * b) = η a * (a • η b)`, is a coboundary: there is `m : M` with
`η a = m * (a • m)⁻¹` for all `a`.

The proof realises `η` as a complement of `M` inside the semidirect product `M ⋊ A`
(the graph of `η`), and applies the conjugacy part of the Schur–Zassenhaus theorem
(in the form `Work.Coprime.schurZassenhaus_conj_of_solvable_quotient`, which uses that
the quotient `A` is solvable) to show that this complement is conjugate to the canonical
one.  Conjugating the graph back gives the required element `m`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Pointwise

namespace Work.Frobenius.Complement

theorem crossed_hom_coboundary_of_solvable {A M : Type*} [Group A] [Group M] [Finite A] [Finite M]
    [MulDistribMulAction A M] (hsol : Group.IsSolvable A)
    (hcop : (Nat.card A).Coprime (Nat.card M))
    (η : A → M) (hη1 : η 1 = 1) (hη : ∀ a b : A, η (a * b) = η a * (a • η b)) :
    ∃ m : M, ∀ a : A, η a = m * (a • m)⁻¹ := by
  let φ : A →* MulAut M := MulDistribMulAction.toMulAut A M
  have hφ : ∀ (a : A) (m : M), φ a m = a • m := by
    intro a m; simp [φ, MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply]
  -- The graph of `η`, as a homomorphism `A →* M ⋊[φ] A`.
  let σ : A →* M ⋊[φ] A :=
    { toFun := fun a => ⟨η a, a⟩
      map_one' := by ext <;> simp [hη1]
      map_mul' := by
        intro a b
        ext
        · exact hη a b
        · rfl }
  have hσ : ∀ a : A, (σ a).left = η a := fun a => rfl
  have hσ2 : ∀ a : A, (σ a).right = a := fun a => rfl
  let N : Subgroup (M ⋊[φ] A) := SemidirectProduct.rightHom.ker
  let K : Subgroup (M ⋊[φ] A) := SemidirectProduct.inr.range
  let H : Subgroup (M ⋊[φ] A) := σ.range
  haveI : Finite (M ⋊[φ] A) := Finite.of_equiv (M × A) (SemidirectProduct.equivProd (φ := φ)).symm
  haveI : N.Normal := MonoidHom.normal_ker _
  have mem_N : ∀ x : M ⋊[φ] A, x ∈ N ↔ x.right = 1 := by
    intro x; rw [show N = SemidirectProduct.rightHom.ker from rfl, MonoidHom.mem_ker]; rfl
  have mem_K : ∀ x : M ⋊[φ] A, x ∈ K ↔ x.left = 1 := by
    intro x
    constructor
    · rintro ⟨a, ha⟩
      rw [← ha]; rfl
    · intro hx
      refine ⟨x.right, ?_⟩
      cases x; simp_all
  have mem_H : ∀ x : M ⋊[φ] A, x ∈ H ↔ ∃ a : A, σ a = x := fun x => MonoidHom.mem_range
  -- `H` and `K` are complements of `N`.
  have hNH : N.IsComplement' H := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff_inf_le]
      rintro x ⟨hxN, hxH⟩
      rw [Subgroup.mem_bot]
      obtain ⟨a, ha⟩ := (mem_H x).mp hxH
      have h1 : a = 1 := by
        have hxr : x.right = 1 := (mem_N x).mp hxN
        have := congrArg SemidirectProduct.right ha
        simpa [hσ2, hxr] using this
      subst h1
      rw [← ha]
      exact σ.map_one
    · rw [Set.eq_univ_iff_forall]
      intro x
      refine Set.mem_mul.mpr ⟨⟨x.left * (η x.right)⁻¹, 1⟩, ?_, σ x.right, ?_, ?_⟩
      · exact (mem_N _).mpr rfl
      · exact (mem_H _).mpr ⟨x.right, rfl⟩
      · ext <;> simp [hσ, hσ2]
  have hNK : N.IsComplement' K := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff_inf_le]
      rintro x hx
      obtain ⟨hxN, hxK⟩ := hx
      rw [Subgroup.mem_bot]
      have hxr : x.right = 1 := (mem_N x).mp hxN
      have hxl : x.left = 1 := (mem_K x).mp hxK
      cases x; simp_all
    · rw [Set.eq_univ_iff_forall]
      intro x
      refine Set.mem_mul.mpr ⟨⟨x.left, 1⟩, ?_, SemidirectProduct.inr x.right, ?_, ?_⟩
      · exact (mem_N _).mpr rfl
      · exact MonoidHom.mem_range.mpr ⟨x.right, rfl⟩
      · ext <;> simp
  -- The quotient `(M ⋊ A) ⧸ N` is isomorphic to the solvable group `A`.
  have hsolq : Group.IsSolvable ((M ⋊[φ] A) ⧸ N) :=
    Group.isSolvable_of_isSolvable_injective
      (f := QuotientGroup.kerLift (SemidirectProduct.rightHom (φ := φ)))
      (QuotientGroup.kerLift_injective _)
  have hR : (SemidirectProduct.rightHom (φ := φ)).range = ⊤ :=
    MonoidHom.range_eq_top.mpr SemidirectProduct.rightHom_surjective
  -- Cardinality bookkeeping: `|N| = |M|` and `[G : N] = |A|`.
  have hcardN : Nat.card N = Nat.card M := by
    refine Nat.card_congr ?_
    refine { toFun := fun x => x.1.left, invFun := fun m => ⟨⟨m, 1⟩, ?_⟩,
             left_inv := ?_, right_inv := ?_ }
    · exact (mem_N _).mpr rfl
    · intro x
      refine Subtype.ext ?_
      ext
      · rfl
      · simp [(mem_N x.1).mp x.2]
    · intro m; rfl
  have hidx : N.index = Nat.card A := by
    rw [Subgroup.index_eq_card]
    calc Nat.card ((M ⋊[φ] A) ⧸ N)
        = Nat.card (SemidirectProduct.rightHom (φ := φ)).range :=
          Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv
      _ = Nat.card (⊤ : Subgroup A) := by rw [hR]
      _ = Nat.card A := Nat.card_congr Subgroup.topEquiv.toEquiv
  have hc : (Nat.card N).Coprime N.index := by rw [hcardN, hidx]; exact hcop.symm
  -- Schur–Zassenhaus: the two complements of `N` are conjugate.
  obtain ⟨g, hg⟩ := Work.Coprime.schurZassenhaus_conj_of_solvable_quotient hc hsolq hNH hNK
  refine ⟨g.right⁻¹ • g.left⁻¹, fun d => ?_⟩
  set a' : A := g.right * d * g.right⁻¹ with ha'
  have hconj : ∀ a : A, (MulAut.conj g⁻¹) (SemidirectProduct.inr a)
      = ⟨(g.right⁻¹ • g.left⁻¹) * ((g.right⁻¹ * a) • g.left), g.right⁻¹ * a * g.right⟩ := by
    intro a
    rw [MulAut.conj_apply, inv_inv]
    ext <;> simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.inv_left, SemidirectProduct.inv_right, SemidirectProduct.left_inr,
      SemidirectProduct.right_inr, hφ, smul_one, mul_one]
  -- Conjugating by `g⁻¹` turns the canonical complement into the graph of `η`.
  have hH_eq : H = K.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [hg, Subgroup.map_map]
    have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom
        = MonoidHom.id (M ⋊[φ] A) := by
      apply MonoidHom.ext
      intro x
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom]
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [hcomp, Subgroup.map_id]
  have hmemK : (SemidirectProduct.inr a' : M ⋊[φ] A) ∈ K := (mem_K _).mpr rfl
  have hyH : (MulAut.conj g⁻¹).toMonoidHom (SemidirectProduct.inr a') ∈ H := by
    rw [hH_eq]
    exact Subgroup.mem_map.mpr ⟨SemidirectProduct.inr a', hmemK, rfl⟩
  obtain ⟨b, hb⟩ := (mem_H _).mp hyH
  have hb' : σ b
      = ⟨(g.right⁻¹ • g.left⁻¹) * ((g.right⁻¹ * a') • g.left), g.right⁻¹ * a' * g.right⟩ := by
    rw [hb]
    exact hconj a'
  have hbd : b = d := by
    have h2 : b = g.right⁻¹ * a' * g.right := by
      have := congrArg SemidirectProduct.right hb'
      simpa [hσ2] using this
    rw [ha'] at h2
    rw [h2]; group
  have hleft : η d = (g.right⁻¹ • g.left⁻¹) * ((g.right⁻¹ * a') • g.left) := by
    have := congrArg SemidirectProduct.left hb'
    simp only [hσ] at this
    rw [← hbd]
    exact this
  rw [hleft, ha']
  rw [show g.right⁻¹ * (g.right * d * g.right⁻¹) = d * g.right⁻¹ from by group]
  congr 1
  rw [← mul_smul, smul_inv', inv_inv]

end Work.Frobenius.Complement
