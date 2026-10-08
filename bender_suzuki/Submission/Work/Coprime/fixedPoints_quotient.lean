import Mathlib
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Basic
import Submission.Work.Coprime.cocycle_is_coboundary
import Submission.Work.Frobenius.Complement.crossed_hom_coboundary_of_solvable
import Submission.Work.Hall.SchurZassenhaus.hall_schurZassenhaus_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `C_{G/N}(A) = C_G(A)N/N` for a coprime action

We prove `Work.Coprime.fixedPoints_quotient`: for a finite group `A` acting by
automorphisms on a finite group `G` with `|A|` coprime to `|G|`, and `N ⊴ G` an
`A`-invariant normal subgroup, the image of `C_G(A)` in `G ⧸ N` is all of
`C_{G/N}(A)`.

The mathematical content is the vanishing of `H¹(A, N)`: a crossed homomorphism
`φ : A → N` (for the restricted action of `A` on `N`) is a coboundary as soon as
`A` or `N` is solvable (Schur–Zassenhaus).  Concretely, if `gN ∈ C_{G/N}(A)`,
then `a ↦ g⁻¹ (a • g)` is a crossed homomorphism `A → N`, and a coboundary
witness `n ∈ N` with `g⁻¹ (a • g) = n (a • n)⁻¹` exhibits `g n ∈ C_G(A)` with
`gnN = gN`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Pointwise

namespace Work.Coprime

/-- **Coprime actions of a solvable group.** If a finite solvable group `A` acts on a finite
group `M` with `Nat.card A` coprime to `Nat.card M`, then every crossed homomorphism
`η : A → M` is a coboundary: there is `m : M` with `η a = m * (a • m)⁻¹` for all `a`.

This is the coefficient-group-solvable partner of
`Work.Frobenius.Complement.crossed_hom_coboundary_of_solvable`; the proof realises `η` as the
graph of a complement of `M` in the semidirect product `M ⋊ A` and uses the conjugacy part of
the Schur–Zassenhaus theorem, here in the form `hall_schurZassenhaus_conj` which only needs the
normal Hall subgroup to be solvable. -/

theorem coboundary_of_solvable_coeff {A M : Type*} [Group A] [Group M] [Finite A] [Finite M]
    [MulDistribMulAction A M] (hsol : Group.IsSolvable M)
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
  have hsolN : Group.IsSolvable ↥N := by
    haveI := hsol
    have heq : N = (SemidirectProduct.inl : M →* (M ⋊[φ] A)).range :=
      SemidirectProduct.range_inl_eq_ker_rightHom.symm
    rw [heq]
    exact Group.isSolvable_of_surjective
      (f := MonoidHom.rangeRestrict (SemidirectProduct.inl : M →* (M ⋊[φ] A)))
      (MonoidHom.rangeRestrict_surjective _)
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
  obtain ⟨g, hg⟩ := Work.Hall.SchurZassenhaus.hall_schurZassenhaus_conj hsolN hc hNH hNK
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

/-- Coboundary form of the vanishing of `H¹` for a coprime action, when either the acting group
or the coefficient group is solvable. -/
theorem cocycle_is_coboundary_aux (A : Type*) {N : Type*} [Group A] [Group N] [Finite A] [Finite N]
    [MulDistribMulAction A N] (hcop : (Nat.card A).Coprime (Nat.card N))
    (hsol : Group.IsSolvable A ∨ Group.IsSolvable N) (φ : A → N)
    (hφ : ∀ a b : A, φ (a * b) = φ a * (a • φ b)) :
    ∃ n : N, ∀ a : A, φ a = n * (a • n)⁻¹ := by
  have hφ1 : φ 1 = 1 := by
    have h := hφ 1 1
    rw [mul_one, one_smul] at h
    have h2 : φ 1 * 1 = φ 1 * φ 1 := by rw [mul_one]; exact h
    exact (mul_left_cancel h2).symm
  rcases hsol with hA | hN
  · exact Work.Frobenius.Complement.crossed_hom_coboundary_of_solvable hA hcop φ hφ1 hφ
  · exact coboundary_of_solvable_coeff hN hcop φ hφ1 hφ

/-- **`C_{G/N}(A) = C_G(A)N/N`.**  For a finite group `A` acting by automorphisms on a finite
group `G` with `|A|` coprime to `|G|`, and an `A`-invariant normal subgroup `N ⊴ G`, the image
of the fixed-point subgroup `C_G(A)` under `G ↠ G ⧸ N` is exactly `C_{G/N}(A)`. -/
theorem fixedPoints_quotient (A : Type*) {G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    [MulDistribMulAction A G] (hcop : (Nat.card A).Coprime (Nat.card G))
    (hsol : Group.IsSolvable A ∨ Group.IsSolvable G)
    (N : Subgroup G) [N.Normal] [FT.IsInvariant A N] :
    (FT.fixedPoints A G).map (QuotientGroup.mk' N) = FT.fixedPoints A (G ⧸ N) := by
  refine le_antisymm (FT.map_fixedPoints_le N) ?_
  intro x hx
  rw [FT.mem_fixedPoints] at hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hxg : ∀ a : A, a • (g : G ⧸ N) = (g : G ⧸ N) := by
    intro a
    have h := hx a
    rwa [QuotientGroup.mk'_apply] at h
  -- The cocycle `a ↦ g⁻¹(a • g)` with values in `N`.
  let Φ : A → ↥N := fun a => ⟨g⁻¹ * (a • g), by
    have h := hxg a
    rw [FT.quotient_smul_mk] at h
    exact QuotientGroup.eq.mp h.symm⟩
  have key : ∀ c : A, ((Φ c : ↥N) : G) = g⁻¹ * (c • g) := fun c => rfl
  have hcross : ∀ a b : A, Φ (a * b) = Φ a * (a • Φ b) := by
    intro a b
    apply Subtype.ext
    simp only [Subgroup.coe_mul, FT.coe_subgroup_smul]
    rw [key (a * b), key a, key b, smul_mul', smul_inv', mul_smul]
    group
  -- Coprimality and solvability descend to `N`.
  have hcN : (Nat.card A).Coprime (Nat.card ↥N) :=
    hcop.coprime_dvd_right ⟨N.index, (Subgroup.card_mul_index N).symm⟩
  have hsolN : Group.IsSolvable A ∨ Group.IsSolvable ↥N := by
    rcases hsol with h | h
    · exact Or.inl h
    · exact Or.inr (by
        haveI := h
        exact Group.isSolvable_of_isSolvable_injective N.subtype_injective)
  obtain ⟨n, hn⟩ := cocycle_is_coboundary_aux A hcN hsolN Φ hcross
  refine Subgroup.mem_map.mpr ⟨g * (n : G), ?_, ?_⟩
  · rw [FT.mem_fixedPoints]
    intro a
    have hn' : ((Φ a : ↥N) : G) = (n : G) * (a • (n : G))⁻¹ := by
      have := congrArg (Subtype.val) (hn a)
      rw [key a] at this
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, FT.coe_subgroup_smul] using this
    have hΦa : a • g = g * ((Φ a : ↥N) : G) := by
      rw [key a]
      group
    rw [smul_mul', hΦa, hn']
    group
  · rw [map_mul]
    have hn1 : (QuotientGroup.mk' N) (n : G) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact n.2
    rw [hn1, mul_one]

end Work.Coprime
