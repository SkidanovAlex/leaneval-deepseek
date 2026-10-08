/-
# Glauberman's lemma for a coprime action

`A` acts by automorphisms on a finite group `G` (instance `[MulDistribMulAction A G]`) with
`Nat.card A` coprime to `Nat.card G`, and `G` acts transitively on a set `Ω` on which `A` acts
compatibly (`a • (g • ω) = (a • g) • (a • ω)`).  If moreover `A` or `G` is solvable, then

* `A` has a fixed point on `Ω`, and
* the `A`-fixed points of `Ω` form a single orbit under `C_G(A)`.

The second statement is proved by exhibiting, for two `A`-fixed points `ω`, `ω'` and `g` with
`g • ω = ω'`, the crossed homomorphism `a ↦ g⁻¹ * (a • g)` with values in the `A`-invariant
subgroup `Stab_G ω`, and applying the vanishing of `H¹` for coprime actions with one solvable side
(`Work.Coprime.cocycle_is_coboundary`).

The first statement reduces, as in the coprimality reduction of Schur--Zassenhaus, to the existence
of a complement: with `X = G ⋊ A` acting on `Ω` and `K = X_ω` the stabiliser of a point, `K ∩ G`
is a normal Hall subgroup of `K`; a complement of it in `K` (Schur--Zassenhaus existence, available
unconditionally in Mathlib) has order `|A|`, hence is a complement of `G` in `X`, and by the
conjugacy part of Schur--Zassenhaus (`Work.Hall.SchurZassenhaus.hall_schurZassenhaus_conj` in the
solvable-`G` case, `Work.Coprime.schurZassenhaus_conj_of_solvable_quotient` in the solvable-`A`
case) it is conjugate to `A` in `X`; the conjugate lies in `K` and its fixed point is the desired
one.
-/
import Mathlib
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Basic
import Submission.Work.Coprime.cocycle_is_coboundary
import Submission.Work.Coprime.schurZassenhaus_conj_of_solvable_quotient
import Submission.Work.Hall.SchurZassenhaus.hall_schurZassenhaus_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false
set_option linter.unusedSectionVars false

open scoped Pointwise

namespace Work.Coprime

/-! ## The action of the semidirect product on a compatible `G`-set -/

section SemidirectAction

variable {A G Ω : Type*} [Group A] [Group G] [MulDistribMulAction A G]
variable [MulAction G Ω] [MulAction A Ω]

/-- If `A` acts on the `G`-set `Ω` compatibly with the action of `A` on `G`
(`a • (g • ω) = (a • g) • (a • ω)`), then `Ω` is a `G ⋊ A`-set. -/
def semidirectMulAction
    (hcomp : ∀ (a : A) (g : G) (ω : Ω), a • (g • ω) = (a • g) • (a • ω)) :
    MulAction (G ⋊[(MulDistribMulAction.toMulAut A G)] A) Ω where
  smul x ω := x.left • (x.right • ω)
  one_smul ω := by
    show (1 : G ⋊[(MulDistribMulAction.toMulAut A G)] A).left •
      ((1 : G ⋊[(MulDistribMulAction.toMulAut A G)] A).right • ω) = ω
    simp
  mul_smul x y ω := by
    have hkey : (x.right • y.left) • (x.right • (y.right • ω))
        = x.right • (y.left • (y.right • ω)) := (hcomp x.right y.left (y.right • ω)).symm
    have h1 : (x * y).left = x.left * (x.right • y.left) := SemidirectProduct.mul_left x y
    have h2 : (x * y).right = x.right * y.right := SemidirectProduct.mul_right x y
    calc (x * y).left • ((x * y).right • ω)
        = (x.left * (x.right • y.left)) • ((x.right * y.right) • ω) := by rw [h1, h2]
      _ = x.left • ((x.right • y.left) • ((x.right * y.right) • ω)) := by rw [mul_smul]
      _ = x.left • ((x.right • y.left) • (x.right • (y.right • ω))) := by rw [mul_smul]
      _ = x.left • (x.right • (y.left • (y.right • ω))) := by rw [hkey]

end SemidirectAction

/-! ## The conjugacy half of Glauberman's lemma -/

section Conjugacy

variable {A G Ω : Type*} [Group A] [Group G] [Finite A] [Finite G]
variable [MulDistribMulAction A G] [MulAction G Ω] [MulAction A Ω]

theorem fixed_conj_of_fixed
    (hcop : (Nat.card A).Coprime (Nat.card G))
    (hsol : Group.IsSolvable A ∨ Group.IsSolvable G)
    (hcomp : ∀ (a : A) (g : G) (ω : Ω), a • (g • ω) = (a • g) • (a • ω))
    (htrans : ∀ ω ω' : Ω, ∃ g : G, g • ω = ω')
    {ω ω' : Ω} (hω : ∀ a : A, a • ω = ω) (hω' : ∀ a : A, a • ω' = ω') :
    ∃ c : G, c ∈ FT.fixedPoints A G ∧ c • ω = ω' := by
  classical
  obtain ⟨g, hg⟩ := htrans ω ω'
  let V : Subgroup G := MulAction.stabilizer G ω
  have hVmem : ∀ y : G, y ∈ V ↔ y • ω = ω := fun y => MulAction.mem_stabilizer_iff
  have hVinv : FT.IsInvariant A V := ⟨fun a => by
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    show (a⁻¹ • x) • ω = ω ↔ x • ω = ω
    constructor
    · intro h
      have h2 := congrArg (fun z : Ω => a • z) h
      rw [hcomp a (a⁻¹ • x) ω, ← mul_smul, mul_inv_cancel, one_smul] at h2
      simpa [hω a] using h2
    · intro h
      rw [show (a⁻¹ • x) • ω = a⁻¹ • (x • ω) from by
        calc (a⁻¹ • x) • ω = (a⁻¹ • x) • (a⁻¹ • ω) := by rw [hω a⁻¹]
          _ = a⁻¹ • (x • ω) := (hcomp a⁻¹ x ω).symm, h, hω a⁻¹]⟩
  haveI : FT.IsInvariant A V := hVinv
  letI : MulDistribMulAction A ↥V := FT.instSubgroupMulDistribMulAction (A := A) V
  let η : A → ↥V := fun a => ⟨g⁻¹ * (a • g), by
    rw [hVmem]
    have h1 : (a • g) • ω = ω' := by
      rw [show (a • g) • ω = (a • g) • (a • ω) from by rw [hω a],
        ← hcomp a g ω, hg, hω' a]
    rw [mul_smul, h1, ← hg, inv_smul_smul]⟩
  have hη1 : η 1 = 1 := by
    apply Subtype.ext
    show g⁻¹ * ((1 : A) • g) = 1
    rw [one_smul, inv_mul_cancel]
  have hη : ∀ a b : A, η (a * b) = η a * (a • η b) := by
    intro a b
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [FT.coe_subgroup_smul]
    show g⁻¹ * ((a * b) • g) = (g⁻¹ * (a • g)) * (a • (g⁻¹ * (b • g)))
    rw [mul_smul, smul_mul', smul_inv']
    group
  have hcopV : (Nat.card A).Coprime (Nat.card ↥V) :=
    hcop.coprime_dvd_right
      (by simpa [Subgroup.card_top] using Work.Hall.card_dvd_card_of_le (le_top : V ≤ ⊤))
  have hsolV : Group.IsSolvable A ∨ Group.IsSolvable ↥V := by
    rcases hsol with h | h
    · exact Or.inl h
    · haveI : Group.IsSolvable G := h
      exact Or.inr (Group.isSolvable_of_isSolvable_injective (f := V.subtype)
        (Subgroup.subtype_injective V))
  obtain ⟨u, hu⟩ := Work.Coprime.cocycle_is_coboundary A hcopV hsolV η hη
  refine ⟨g * (u : G)⁻¹, ?_, ?_⟩
  · rw [FT.mem_fixedPoints]
    intro a
    show a • (g * (u : G)⁻¹) = g * (u : G)⁻¹
    have hu' : (η a : G) = (u : G)⁻¹ * (a • (u : G)) := by
      have := congrArg Subtype.val (hu a)
      rwa [Subgroup.coe_mul, Subgroup.coe_inv, FT.coe_subgroup_smul] at this
    have hga : a • g = g * (η a : G) := by
      show a • g = g * (g⁻¹ * (a • g))
      group
    rw [smul_mul', smul_inv', hga, hu']
    group
  · show (g * (u : G)⁻¹) • ω = ω'
    have huω : (u : G) • ω = ω := (hVmem (u : G)).mp u.2
    have huω' : ((u : G)⁻¹) • ω = ω := by
      calc ((u : G)⁻¹) • ω = ((u : G)⁻¹) • ((u : G) • ω) := by rw [huω]
        _ = ω := by rw [inv_smul_smul]
    rw [mul_smul, huω', hg]

end Conjugacy

/-! ## The existence half of Glauberman's lemma -/

section Existence

variable {A G Ω : Type*} [Group A] [Group G] [Finite A] [Finite G]
variable [MulDistribMulAction A G] [MulAction G Ω] [MulAction A Ω] [Finite Ω] [Nonempty Ω]

theorem fixed_point_exists
    (hcop : (Nat.card A).Coprime (Nat.card G))
    (hsol : Group.IsSolvable A ∨ Group.IsSolvable G)
    (hcomp : ∀ (a : A) (g : G) (ω : Ω), a • (g • ω) = (a • g) • (a • ω))
    (htrans : ∀ ω ω' : Ω, ∃ g : G, g • ω = ω') :
    ∃ ω : Ω, ∀ a : A, a • ω = ω := by
  classical
  let φ : A →* MulAut G := MulDistribMulAction.toMulAut A G
  letI : MulAction (G ⋊[φ] A) Ω := semidirectMulAction (A := A) (G := G) (Ω := Ω) hcomp
  haveI : Finite (G ⋊[φ] A) :=
    Finite.of_equiv (G × A) (SemidirectProduct.equivProd (φ := φ)).symm
  let ω₀ : Ω := Classical.arbitrary Ω
  let U : Subgroup (G ⋊[φ] A) := MulAction.stabilizer (G ⋊[φ] A) ω₀
  let G₀ : Subgroup (G ⋊[φ] A) := (SemidirectProduct.rightHom (φ := φ)).ker
  let A₀ : Subgroup (G ⋊[φ] A) := SemidirectProduct.inr.range
  have hsmul : ∀ (x : G ⋊[φ] A) (ω : Ω), x • ω = x.left • (x.right • ω) := fun _ _ => rfl
  have hG₀normal : G₀.Normal := MonoidHom.normal_ker _
  haveI : G₀.Normal := hG₀normal
  have hG₀eq : G₀ = SemidirectProduct.inl.range := SemidirectProduct.range_inl_eq_ker_rightHom.symm
  -- `G` is transitive on `Ω`, so `X = G₀ · U`
  have hsup : G₀ ⊔ U = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨g, hg⟩ := htrans ω₀ (x • ω₀)
    have hinl : (SemidirectProduct.inl g : G ⋊[φ] A) • ω₀ = g • ω₀ := by
      rw [hsmul, SemidirectProduct.left_inl, SemidirectProduct.right_inl, one_smul]
    have hxU : (SemidirectProduct.inl g)⁻¹ * x ∈ U := by
      show (SemidirectProduct.inl g)⁻¹ * x ∈ MulAction.stabilizer (G ⋊[φ] A) ω₀
      rw [MulAction.mem_stabilizer_iff, mul_smul, ← hg, ← hinl, inv_smul_smul]
    have hx : x = SemidirectProduct.inl g * ((SemidirectProduct.inl g)⁻¹ * x) := by group
    rw [hx]
    exact Subgroup.mul_mem_sup (MonoidHom.mem_ker.mpr rfl) hxU
  -- cardinalities
  have hcardG₀ : Nat.card ↥G₀ = Nat.card G := by
    have h1 : G₀ = (⊤ : Subgroup G).map (SemidirectProduct.inl : G →* (G ⋊[φ] A)) := by
      rw [hG₀eq, Subgroup.map_top]
    rw [h1, Subgroup.card_map_of_injective SemidirectProduct.inl_injective, Subgroup.card_top]
  have hG₀index : G₀.index = Nat.card A := by
    rw [Subgroup.index_eq_card]
    calc Nat.card ((G ⋊[φ] A) ⧸ (SemidirectProduct.rightHom (φ := φ)).ker)
        = Nat.card ↥(SemidirectProduct.rightHom (φ := φ)).range :=
          Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv
      _ = Nat.card ↥(⊤ : Subgroup A) := by
            rw [MonoidHom.range_eq_top.mpr SemidirectProduct.rightHom_surjective]
      _ = Nat.card A := Subgroup.card_top
  have hcG₀ : (Nat.card ↥G₀).Coprime G₀.index := by
    rw [hcardG₀, hG₀index]; exact hcop.symm
  -- the normal Hall subgroup `V = G₀ ⊓ U ≤ U`
  let V : Subgroup ↥U := G₀.subgroupOf U
  haveI : V.Normal := hG₀normal.subgroupOf U
  have hVcard : Nat.card ↥V ∣ Nat.card G := by
    have h1 : Nat.card ↥V = Nat.card ↥(G₀ ⊓ U) := by
      rw [← Subgroup.card_map_of_injective (f := U.subtype) (Subgroup.subtype_injective U),
        Subgroup.subgroupOf_map_subtype]
    rw [h1]
    exact (Work.Hall.card_dvd_card_of_le (inf_le_left : G₀ ⊓ U ≤ G₀)).trans (hcardG₀ ▸ dvd_rfl)
  have hVindex : V.index = Nat.card A := by
    have h1 : G₀.relIndex U = G₀.index := by
      rw [← Subgroup.relIndex_sup_left U G₀, hsup]
      have h2 := Subgroup.relIndex_mul_index (H := G₀) (K := ⊤) le_top
      rw [Subgroup.index_top, mul_one] at h2
      exact h2
    rw [show V.index = G₀.relIndex U from rfl, h1, hG₀index]
  have hVcoprime : (Nat.card ↥V).Coprime V.index := by
    rw [hVindex]
    exact (hcop.coprime_dvd_right hVcard).symm
  -- Schur--Zassenhaus existence: a complement of `V` in `U`
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime (G := ↥U) (N := V) hVcoprime
  let K' : Subgroup (G ⋊[φ] A) := K.map U.subtype
  have hK'le : K' ≤ U := Subgroup.map_subtype_le K
  have hAcomp : G₀.IsComplement' A₀ := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff_inf_le]
      rintro y ⟨hyG, hyA⟩
      rw [Subgroup.mem_bot]
      have hy1 : y.right = 1 := MonoidHom.mem_ker.mp hyG
      obtain ⟨a, ha⟩ := hyA
      have h1 : a = 1 := by
        have h2 := congrArg SemidirectProduct.right ha
        rw [SemidirectProduct.right_inr, hy1] at h2
        exact h2
      rw [← ha, h1, map_one]
    · rw [Set.eq_univ_iff_forall]
      intro y
      refine Set.mem_mul.mpr ⟨SemidirectProduct.inl y.left, MonoidHom.mem_ker.mpr rfl,
        SemidirectProduct.inr y.right, ⟨y.right, rfl⟩,
        SemidirectProduct.inl_left_mul_inr_right y⟩
  have hK'comp : G₀.IsComplement' K' := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff_inf_le]
      rintro y ⟨hyG, hyK⟩
      rw [Subgroup.mem_bot]
      obtain ⟨k, hkK, hkx⟩ := Subgroup.mem_map.mp hyK
      have hkV : k ∈ V := by
        rw [Subgroup.mem_subgroupOf]
        exact Eq.mpr (congrArg (fun z : G ⋊[φ] A => z ∈ G₀) hkx) hyG
      have h1 : k = 1 := Subgroup.mem_bot.mp (disjoint_iff_inf_le.mp hK.disjoint ⟨hkV, hkK⟩)
      rw [← hkx, h1, map_one]
    · rw [Set.eq_univ_iff_forall]
      intro y
      have hy : y ∈ G₀ ⊔ U := hsup ▸ Subgroup.mem_top y
      obtain ⟨g, hgG, u, huU, hgu⟩ := Subgroup.mem_sup_of_normal_left.mp hy
      have hu : (⟨u, huU⟩ : ↥U) ∈ (V : Set ↥U) * (K : Set ↥U) := by rw [hK.mul_eq]; trivial
      obtain ⟨v, hvV, k, hkK, hvk⟩ := Set.mem_mul.mp hu
      refine Set.mem_mul.mpr ⟨g * (v : G ⋊[φ] A), G₀.mul_mem hgG hvV,
        (k : G ⋊[φ] A), Subgroup.mem_map.mpr ⟨k, hkK, rfl⟩, ?_⟩
      have hvk' : (v : G ⋊[φ] A) * (k : G ⋊[φ] A) = u := by
        rw [← Subgroup.coe_mul, hvk]
      rw [mul_assoc, hvk', hgu]
  -- Schur--Zassenhaus conjugacy
  have hsolG₀ : Group.IsSolvable G → Group.IsSolvable ↥G₀ := by
    intro hG
    haveI : Group.IsSolvable G := hG
    have hf : Function.Injective (fun y : ↥G₀ => (y : G ⋊[φ] A).left) := by
      intro a b hab
      have ha : (a : G ⋊[φ] A).right = 1 := MonoidHom.mem_ker.mp a.2
      have hb : (b : G ⋊[φ] A).right = 1 := MonoidHom.mem_ker.mp b.2
      have h1 : (a : G ⋊[φ] A) = SemidirectProduct.inl ((a : G ⋊[φ] A).left) := by
        calc (a : G ⋊[φ] A)
            = SemidirectProduct.inl ((a : G ⋊[φ] A).left) *
                SemidirectProduct.inr ((a : G ⋊[φ] A).right) :=
              (SemidirectProduct.inl_left_mul_inr_right (a : G ⋊[φ] A)).symm
          _ = SemidirectProduct.inl ((a : G ⋊[φ] A).left) := by rw [ha, map_one, mul_one]
      have h2 : (b : G ⋊[φ] A) = SemidirectProduct.inl ((b : G ⋊[φ] A).left) := by
        calc (b : G ⋊[φ] A)
            = SemidirectProduct.inl ((b : G ⋊[φ] A).left) *
                SemidirectProduct.inr ((b : G ⋊[φ] A).right) :=
              (SemidirectProduct.inl_left_mul_inr_right (b : G ⋊[φ] A)).symm
          _ = SemidirectProduct.inl ((b : G ⋊[φ] A).left) := by rw [hb, map_one, mul_one]
      have hab' : (a : G ⋊[φ] A).left = (b : G ⋊[φ] A).left := hab
      exact Subtype.ext (by rw [h1, h2, hab'])
    let f : ↥G₀ →* G :=
      { toFun := fun y => (y : G ⋊[φ] A).left
        map_one' := rfl
        map_mul' := fun a b => by
          have ha : (a : G ⋊[φ] A).right = 1 := MonoidHom.mem_ker.mp a.2
          show ((a : G ⋊[φ] A) * (b : G ⋊[φ] A)).left
            = (a : G ⋊[φ] A).left * (b : G ⋊[φ] A).left
          rw [SemidirectProduct.mul_left]
          simp [ha] }
    exact Group.isSolvable_of_isSolvable_injective (f := f) hf
  have hsolQuot : Group.IsSolvable A → Group.IsSolvable ((G ⋊[φ] A) ⧸ G₀) := by
    intro hA
    haveI : Group.IsSolvable A := hA
    exact Group.isSolvable_of_isSolvable_injective
      (f := QuotientGroup.kerLift (SemidirectProduct.rightHom (φ := φ)))
      (QuotientGroup.kerLift_injective _)
  obtain ⟨x, hx⟩ : ∃ x : G ⋊[φ] A, K' = A₀.map (MulAut.conj x).toMonoidHom := by
    rcases hsol with hA | hG
    · exact schurZassenhaus_conj_of_solvable_quotient hcG₀ (hsolQuot hA) hAcomp hK'comp
    · exact Work.Hall.SchurZassenhaus.hall_schurZassenhaus_conj (hsolG₀ hG) hcG₀ hAcomp hK'comp
  have hconj_le : A₀.map (MulAut.conj x).toMonoidHom ≤ U := hx ▸ hK'le
  -- the fixed point
  refine ⟨x⁻¹ • ω₀, fun a => ?_⟩
  have hmem : x * (SemidirectProduct.inr a) * x⁻¹ ∈ U := by
    have h1 : (SemidirectProduct.inr a : G ⋊[φ] A) ∈ A₀ := ⟨a, rfl⟩
    have h2 := hconj_le ⟨SemidirectProduct.inr a, h1, rfl⟩
    rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h2
  have h3 : (x * SemidirectProduct.inr a * x⁻¹) • ω₀ = ω₀ :=
    MulAction.mem_stabilizer_iff.mp (show x * SemidirectProduct.inr a * x⁻¹ ∈
      MulAction.stabilizer (G ⋊[φ] A) ω₀ from hmem)
  have hinr : (SemidirectProduct.inr a : G ⋊[φ] A) • (x⁻¹ • ω₀) = a • (x⁻¹ • ω₀) := by
    rw [hsmul, SemidirectProduct.left_inr, SemidirectProduct.right_inr, one_smul]
  have h4 : x • (a • (x⁻¹ • ω₀)) = ω₀ := by
    rw [mul_smul, mul_smul, hinr] at h3
    exact h3
  have h5 : a • (x⁻¹ • ω₀) = x⁻¹ • ω₀ := by
    have h6 := congrArg (fun z : Ω => x⁻¹ • z) h4
    rw [← mul_smul, inv_mul_cancel, one_smul] at h6
    exact h6
  exact h5

end Existence

/-! ## Glauberman's lemma -/

/-- **Glauberman's lemma.** If a finite group `A` acts on a finite group `G` by automorphisms with
`|A|` coprime to `|G|`, if `G` acts transitively on a set `Ω` carrying a compatible `A`-action,
and if `A` or `G` is solvable, then `A` has a fixed point on `Ω`, and any two `A`-fixed points of
`Ω` are conjugate by an element of `C_G(A)`. -/
theorem glauberman_lemma (A : Type*) (G Ω : Type*) [Group A] [Group G] [Finite A] [Finite G]
    [MulDistribMulAction A G] [MulAction G Ω] [MulAction A Ω] [Finite Ω] [Nonempty Ω]
    (hcop : (Nat.card A).Coprime (Nat.card G))
    (hsol : Group.IsSolvable A ∨ Group.IsSolvable G)
    (hcomp : ∀ (a : A) (g : G) (ω : Ω), a • (g • ω) = (a • g) • (a • ω))
    (htrans : ∀ ω ω' : Ω, ∃ g : G, g • ω = ω') :
    (∃ ω : Ω, ∀ a : A, a • ω = ω) ∧
      (∀ ω ω' : Ω, (∀ a : A, a • ω = ω) → (∀ a : A, a • ω' = ω') →
        ∃ c : G, c ∈ FT.fixedPoints A G ∧ c • ω = ω') :=
  ⟨fixed_point_exists hcop hsol hcomp htrans,
    fun _ _ hω hω' => fixed_conj_of_fixed hcop hsol hcomp htrans hω hω'⟩

end Work.Coprime
