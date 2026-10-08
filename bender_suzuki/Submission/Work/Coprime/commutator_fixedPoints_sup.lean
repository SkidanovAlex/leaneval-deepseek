import Mathlib
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Basic
import Submission.Work.Hall.SchurZassenhaus.hall_schurZassenhaus_conj
import Submission.Work.Coprime.schurZassenhaus_conj_of_solvable_quotient

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Pointwise

namespace Work.Coprime

/-! ## Conjugation formulae in a semidirect product -/

private theorem semidirect_conj_inl_inr {A N : Type*} [Group A] [Group N]
    [MulDistribMulAction A N] (m : N) (a : A) :
    (SemidirectProduct.inl m * SemidirectProduct.inr a * (SemidirectProduct.inl m)⁻¹ :
        N ⋊[MulDistribMulAction.toMulAut A N] A) = ⟨m * (a • m⁻¹), a⟩ := by
  ext <;>
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
      SemidirectProduct.inv_right, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      SemidirectProduct.left_inr, SemidirectProduct.right_inr, one_mul, mul_one,
      map_mul, map_inv, map_one, MulAut.mul_apply, MulAut.one_apply, inv_one, smul_inv']
  rfl

private theorem semidirect_conj_inl_inr_inr {A N : Type*} [Group A] [Group N]
    [MulDistribMulAction A N] (m : N) (b c : A) :
    ((SemidirectProduct.inl m * SemidirectProduct.inr b) * SemidirectProduct.inr c *
      ((SemidirectProduct.inl m * SemidirectProduct.inr b))⁻¹ :
        N ⋊[MulDistribMulAction.toMulAut A N] A) =
      ⟨m * ((b * c * b⁻¹) • m⁻¹), b * c * b⁻¹⟩ := by
  ext <;>
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
      SemidirectProduct.inv_right, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      SemidirectProduct.left_inr, SemidirectProduct.right_inr, one_mul, mul_one,
      map_mul, map_inv, map_one, MulAut.mul_apply, MulAut.one_apply, inv_one, smul_inv', mul_smul]
  rw [← map_inv (MulDistribMulAction.toMulAut A N) b]
  rfl

/-- **Non-abelian `H¹`-vanishing for a coprime action.**  If a finite group `A` acts on a finite
group `N` with `Nat.card A` coprime to `Nat.card N`, and `A` or `N` is solvable, then every
`1`-cocycle `φ : A → N` (i.e. `φ (a * b) = φ a * (a • φ b)`) is a coboundary:
there is `n : N` with `φ a = n⁻¹ * (a • n)` for all `a`.

This is the conjugacy part of the Schur–Zassenhaus theorem applied inside the semidirect
product `N ⋊ A`. -/
theorem cocycle_vanish (A : Type*) {N : Type*} [Group A] [Group N] [Finite A] [Finite N]
    [MulDistribMulAction A N] (hcop : (Nat.card A).Coprime (Nat.card N))
    (hsol : Group.IsSolvable A ∨ Group.IsSolvable N) (φ : A → N)
    (hφ : ∀ a b : A, φ (a * b) = φ a * (a • φ b)) :
    ∃ n : N, ∀ a : A, φ a = n⁻¹ * (a • n) := by
  have hφ1 : φ 1 = 1 := by
    have h0 : φ 1 = φ 1 * φ 1 := by simpa using hφ 1 1
    have h : φ 1 * φ 1 = φ 1 * 1 := by rw [mul_one]; exact h0.symm
    exact mul_left_cancel h
  let ψ : A →* MulAut N := MulDistribMulAction.toMulAut A N
  let s : A →* N ⋊[ψ] A :=
    { toFun := fun a => ⟨φ a, a⟩
      map_one' := by ext <;> simp [hφ1]
      map_mul' := by intro a b; ext <;> simp only [hφ a b] <;> rfl }
  have hs_left : ∀ a : A, (s a).left = φ a := fun a => rfl
  have hs_right : ∀ a : A, (s a).right = a := fun a => rfl
  let Nsub : Subgroup (N ⋊[ψ] A) := (SemidirectProduct.rightHom (φ := ψ)).ker
  let A0 : Subgroup (N ⋊[ψ] A) := (SemidirectProduct.inr (φ := ψ)).range
  let T : Subgroup (N ⋊[ψ] A) := s.range
  haveI : Nsub.Normal := by
    show (SemidirectProduct.rightHom (φ := ψ)).ker.Normal
    infer_instance
  haveI : Finite (N ⋊[ψ] A) :=
    Finite.of_injective (SemidirectProduct.equivProd (φ := ψ))
      (SemidirectProduct.equivProd (φ := ψ)).injective
  have hker : ∀ x : N ⋊[ψ] A, x ∈ Nsub ↔ x.right = 1 := by
    intro x
    show x ∈ (SemidirectProduct.rightHom (φ := ψ)).ker ↔ x.right = 1
    rw [MonoidHom.mem_ker, SemidirectProduct.rightHom_eq_right]
  have hinl : ∀ n : N, SemidirectProduct.inl n ∈ Nsub := by
    intro n; rw [hker]; simp
  have hright1 : ∀ x : N ⋊[ψ] A, x.right = 1 → x = SemidirectProduct.inl x.left := by
    intro x hx
    have h := SemidirectProduct.inl_left_mul_inr_right x
    rw [hx, map_one, mul_one] at h
    exact h.symm
  have hcomp0 : Nsub.IsComplement' A0 := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff_inf_le]
      rintro x ⟨hxN, hxA⟩
      change x ∈ Nsub at hxN
      rw [hker] at hxN
      obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hxA
      rw [Subgroup.mem_bot]
      have hc1 : c = 1 := by
        have h2 : (SemidirectProduct.inr (φ := ψ) c).right = 1 := by rw [hc]; exact hxN
        simpa using h2
      rw [← hc, hc1, map_one]
    · rw [Set.eq_univ_iff_forall]
      intro x
      exact Set.mem_mul.mpr ⟨SemidirectProduct.inl x.left, hinl x.left,
        SemidirectProduct.inr x.right, MonoidHom.mem_range.mpr ⟨x.right, rfl⟩,
        SemidirectProduct.inl_left_mul_inr_right x⟩
  have hcompT : Nsub.IsComplement' T := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff_inf_le]
      rintro x ⟨hxN, hxT⟩
      change x ∈ Nsub at hxN
      rw [hker] at hxN
      obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hxT
      rw [Subgroup.mem_bot]
      have hc1 : c = 1 := by
        have h2 : (s c).right = 1 := by rw [hc]; exact hxN
        rw [hs_right] at h2
        exact h2
      rw [← hc, hc1, map_one]
    · rw [Set.eq_univ_iff_forall]
      intro x
      refine Set.mem_mul.mpr ⟨SemidirectProduct.inl (x.left * (φ x.right)⁻¹), hinl _,
        s x.right, MonoidHom.mem_range.mpr ⟨x.right, rfl⟩, ?_⟩
      ext <;>
        simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
          SemidirectProduct.left_inl, SemidirectProduct.right_inl, one_mul, mul_one,
          map_one, MulAut.one_apply, MulAut.mul_apply, hs_left, hs_right]
      · group
  have hcardN : Nat.card ↥Nsub = Nat.card N := by
    have hNsub_eq : Nsub = Subgroup.map (SemidirectProduct.inl (φ := ψ)) ⊤ := by
      show (SemidirectProduct.rightHom (φ := ψ)).ker = _
      rw [← SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.range_eq_map]
    rw [hNsub_eq, Subgroup.card_map_of_injective SemidirectProduct.inl_injective,
      Subgroup.card_top]
  have hindexN : Nsub.index = Nat.card A := by
    show (SemidirectProduct.rightHom (φ := ψ)).ker.index = Nat.card A
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr SemidirectProduct.rightHom_surjective,
      Subgroup.card_top]
  have hc : (Nat.card ↥Nsub).Coprime Nsub.index := by rw [hcardN, hindexN]; exact hcop.symm
  obtain ⟨x, hx⟩ : ∃ x : N ⋊[ψ] A, T = A0.map (MulAut.conj x).toMonoidHom := by
    rcases hsol with hA | hN
    · haveI : Group.IsSolvable A := hA
      have e : ((N ⋊[ψ] A) ⧸ Nsub) ≃* A :=
        QuotientGroup.quotientKerEquivOfSurjective (SemidirectProduct.rightHom (φ := ψ))
          SemidirectProduct.rightHom_surjective
      have hquot : Group.IsSolvable ((N ⋊[ψ] A) ⧸ Nsub) :=
        Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
      exact schurZassenhaus_conj_of_solvable_quotient hc hquot hcomp0 hcompT
    · haveI : Group.IsSolvable N := hN
      let f : N →* ↥Nsub :=
        { toFun := fun n => ⟨SemidirectProduct.inl n, hinl n⟩
          map_one' := Subtype.ext (map_one _)
          map_mul' := fun a b => Subtype.ext (map_mul _ a b) }
      have hNsub_sol : Group.IsSolvable ↥Nsub :=
        Group.isSolvable_of_surjective (f := f) (fun y =>
          ⟨y.val.left, Subtype.ext (hright1 y.val ((hker y.val).mp y.2)).symm⟩)
      exact Hall.SchurZassenhaus.hall_schurZassenhaus_conj hNsub_sol hc hcomp0 hcompT
  refine ⟨x.left⁻¹, fun a => ?_⟩
  have hsa : s a ∈ A0.map (MulAut.conj x).toMonoidHom := by rw [← hx]; exact ⟨a, rfl⟩
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hsa
  obtain ⟨c, hc0⟩ := MonoidHom.mem_range.mp hy
  have hconj : (MulAut.conj x) (SemidirectProduct.inr c) =
      (⟨x.left * ((x.right * c * x.right⁻¹) • x.left⁻¹), x.right * c * x.right⁻¹⟩ :
        N ⋊[ψ] A) := by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x, MulAut.conj_apply]
    exact semidirect_conj_inl_inr_inr x.left x.right c
  have hkey : (⟨x.left * ((x.right * c * x.right⁻¹) • x.left⁻¹), x.right * c * x.right⁻¹⟩ :
      N ⋊[ψ] A) = s a := by
    rw [← hconj, hc0]
    simpa using hyx
  have hright : x.right * c * x.right⁻¹ = a := by
    have hh := congrArg SemidirectProduct.right hkey
    rw [hs_right] at hh
    simpa using hh
  have hleft : x.left * ((x.right * c * x.right⁻¹) • x.left⁻¹) = φ a := by
    have hh := congrArg SemidirectProduct.left hkey
    rw [hs_left] at hh
    simpa using hh
  rw [inv_inv, ← hleft, hright]

/-- **Coprime action: `G = C_G(A) · [G, A]`.**  If a finite group `A` acts on a finite group `G`
with `Nat.card A` coprime to `Nat.card G`, and `A` or `G` is solvable, then every element of `G`
is a product of a fixed point of `A` and an element of the commutator `[G, A]`. -/
theorem commutator_fixedPoints_sup (A : Type*) {G : Type*} [Group A] [Group G] [Finite A]
    [Finite G] [MulDistribMulAction A G] (hcop : (Nat.card A).Coprime (Nat.card G))
    (hsol : Group.IsSolvable A ∨ Group.IsSolvable G) :
    FT.fixedPoints A G ⊔ FT.commutator A (⊤ : Subgroup G) = ⊤ := by
  set M : Subgroup G := FT.commutator A (⊤ : Subgroup G)
  haveI : FT.IsInvariant A M := inferInstance
  have hcop' : (Nat.card A).Coprime (Nat.card M) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_subgroup_dvd_card M) hcop
  have hsol' : Group.IsSolvable A ∨ Group.IsSolvable M := by
    rcases hsol with h | h
    · exact Or.inl h
    · haveI : Group.IsSolvable G := h
      exact Or.inr inferInstance
  apply top_le_iff.mp
  intro g _
  let φ : A → M := fun a => ⟨g⁻¹ * (a • g), FT.le_commutator a (Subgroup.mem_top g)⟩
  have hφ : ∀ a b : A, φ (a * b) = φ a * (a • φ b) := by
    intro a b
    apply Subtype.ext
    simp only [φ, Subtype.coe_mk, Subgroup.coe_mul, FT.coe_subgroup_smul, mul_smul, smul_inv',
      smul_mul']
    group
  obtain ⟨n, hn⟩ := cocycle_vanish A hcop' hsol' φ hφ
  have hfix : g * (n : G)⁻¹ ∈ FT.fixedPoints A G := by
    rw [FT.mem_fixedPoints]
    intro a
    have h := congrArg Subtype.val (hn a)
    simp only [φ, Subtype.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv, FT.coe_subgroup_smul] at h
    have key : (a • g) = g * (n : G)⁻¹ * (a • (n : G)) := by
      calc (a • g) = g * (g⁻¹ * (a • g)) := by group
        _ = g * ((n : G)⁻¹ * (a • (n : G))) := by rw [h]
        _ = g * (n : G)⁻¹ * (a • (n : G)) := by group
    rw [smul_mul', key, smul_inv']
    group
  have hg : g = (g * (n : G)⁻¹) * (n : G) := by group
  rw [hg]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hfix) (Subgroup.mem_sup_right n.2)

end Work.Coprime
