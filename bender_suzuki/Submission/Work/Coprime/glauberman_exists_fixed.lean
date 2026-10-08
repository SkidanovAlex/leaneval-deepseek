import Mathlib
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Basic
import Submission.Work.Coprime.cocycle_is_coboundary
import Submission.Work.Hall.SchurZassenhaus.hall_schurZassenhaus_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Glauberman's fixed point lemma (existence)

Let `A` act by automorphisms on a finite group `G`, with `Nat.card A` coprime to `Nat.card G`,
and suppose that `A` or `G` is solvable.  Suppose `A` and `G` both act on a finite nonempty
type `Ω` in a compatible way
(`a • (g • ω) = (a • g) • (a • ω)`) and that `G` acts transitively on `Ω`.
Then `A` fixes a point of `Ω`.

The proof realises `Ω` as a `G ⋊ A`-set, takes `ω₀ ∈ Ω`, `K = (G ⋊ A)_{ω₀}` and
`N = ker (G ⋊ A → A)`; then `N ◁ G ⋊ A` is a normal Hall subgroup, `N ⊔ K = ⊤` and
`K ∩ N` is a normal Hall subgroup of `K`, so Schur–Zassenhaus (existence) produces a
complement `B ≤ K` of `K ∩ N` in `K`.  Having order `|A|` and trivial intersection with `N`,
`B` is a complement of `N` in `G ⋊ A`; Schur–Zassenhaus (conjugacy, in one of the two
available forms) makes it a conjugate of the canonical complement `A`, and a conjugate of `A`
inside `K` is exactly a fixed point.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Pointwise

namespace Work.Coprime

theorem glauberman_exists_fixed (A : Type*) (G Ω : Type*) [Group A] [Group G] [Finite A] [Finite G]
    [MulDistribMulAction A G] [MulAction G Ω] [MulAction A Ω] [Finite Ω] [Nonempty Ω]
    (hcop : (Nat.card A).Coprime (Nat.card G))
    (hsol : Group.IsSolvable A ∨ Group.IsSolvable G)
    (hcomp : ∀ (a : A) (g : G) (ω : Ω), a • (g • ω) = (a • g) • (a • ω))
    (htrans : ∀ ω ω' : Ω, ∃ g : G, g • ω = ω') :
    ∃ ω : Ω, ∀ a : A, a • ω = ω := by
  classical
  let φ : A →* MulAut G := MulDistribMulAction.toMulAut A G
  have hφ : ∀ (a : A) (g : G), φ a g = a • g := by
    intro a g
    simp [φ, MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply]
  let X := G ⋊[φ] A
  haveI : Finite X := Finite.of_equiv (G × A) (SemidirectProduct.equivProd (φ := φ)).symm
  -- The action of `G ⋊ A` on `Ω`: `(g, a) • ω = g • (a • ω)`.
  letI : MulAction X Ω :=
  { smul := fun x ω => x.left • (x.right • ω)
    one_smul := fun ω => by
      show (1 : X).left • ((1 : X).right • ω) = ω
      rw [SemidirectProduct.one_left, SemidirectProduct.one_right, one_smul, one_smul]
    mul_smul := fun x y ω => by
      show (x * y).left • ((x * y).right • ω) = x.left • (x.right • (y.left • (y.right • ω)))
      rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right, hφ, mul_smul, mul_smul, hcomp] }
  have hInl : ∀ (g : G) (ω : Ω), (SemidirectProduct.inl g : X) • ω = g • ω := by
    intro g ω
    show ((SemidirectProduct.inl g : X)).left • (((SemidirectProduct.inl g : X)).right • ω) = g • ω
    rw [SemidirectProduct.left_inl, SemidirectProduct.right_inl, one_smul]
  have hInr : ∀ (a : A) (ω : Ω), (SemidirectProduct.inr a : X) • ω = a • ω := by
    intro a ω
    show ((SemidirectProduct.inr a : X)).left • (((SemidirectProduct.inr a : X)).right • ω) = a • ω
    rw [SemidirectProduct.left_inr, SemidirectProduct.right_inr, one_smul]
  let ω₀ : Ω := Classical.choice ‹Nonempty Ω›
  let K : Subgroup X := MulAction.stabilizer X ω₀
  let N : Subgroup X := SemidirectProduct.rightHom.ker
  haveI : N.Normal := MonoidHom.normal_ker _
  have memN : ∀ x : X, x ∈ N ↔ x.right = 1 := by
    intro x
    rw [show N = SemidirectProduct.rightHom.ker from rfl, MonoidHom.mem_ker]
    rfl
  have hNeq : N = (SemidirectProduct.inl : G →* X).range :=
    (SemidirectProduct.range_inl_eq_ker_rightHom).symm
  have hcardN : Nat.card N = Nat.card G := by
    rw [hNeq, MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective (f := (SemidirectProduct.inl : G →* X))
        SemidirectProduct.inl_injective]
    simp
  have hcardInr : Nat.card (SemidirectProduct.inr : A →* X).range = Nat.card A := by
    rw [MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective (f := (SemidirectProduct.inr : A →* X))
        SemidirectProduct.inr_injective]
    simp
  have hidx : N.index = Nat.card A := by
    rw [Subgroup.index_eq_card]
    calc Nat.card (X ⧸ N)
        = Nat.card (SemidirectProduct.rightHom (φ := φ)).range :=
          Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv
      _ = Nat.card (⊤ : Subgroup A) := by
          rw [MonoidHom.range_eq_top.mpr SemidirectProduct.rightHom_surjective]
      _ = Nat.card A := Nat.card_congr Subgroup.topEquiv.toEquiv
  -- The image of `A` in `X` is a complement of the normal Hall subgroup `N`.
  have hNinr : N.IsComplement' (SemidirectProduct.inr : A →* X).range := by
    rw [Subgroup.isComplement'_iff_card_mul_and_disjoint]
    refine ⟨?_, ?_⟩
    · rw [hcardN, hcardInr, SemidirectProduct.card]
    · rw [disjoint_iff_inf_le]
      rintro z hz
      rw [Subgroup.mem_inf] at hz
      obtain ⟨hzN, hzI⟩ := hz
      obtain ⟨a, ha⟩ := hzI
      rw [Subgroup.mem_bot]
      have hzr : z.right = 1 := (memN z).mp hzN
      have ha1 : a = 1 := by
        have h2 : (SemidirectProduct.inr a : X).right = z.right :=
          congrArg SemidirectProduct.right ha
        rw [hzr] at h2
        simpa using h2
      rw [← ha, ha1]
      rfl
  -- Transitivity of `G` on `Ω` upgrades to `N ⊔ K = ⊤`.
  have hsup : N ⊔ K = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨h, hh⟩ := htrans ω₀ (x • ω₀)
    have hmemK : (SemidirectProduct.inl h⁻¹ : X) * x ∈ K := by
      rw [MulAction.mem_stabilizer_iff]
      show ((SemidirectProduct.inl h⁻¹ : X) * x) • ω₀ = ω₀
      rw [mul_smul, hInl, ← hh, inv_smul_smul]
    have hmul : SemidirectProduct.inl h * (SemidirectProduct.inl h⁻¹ * x) = x := by
      rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    rw [← hmul]
    exact Subgroup.mul_mem (N ⊔ K)
      (Subgroup.mem_sup_left (show SemidirectProduct.inl h ∈ N from by rw [hNeq]; exact ⟨h, rfl⟩))
      (Subgroup.mem_sup_right hmemK)
  -- `K ∩ N` has index `|A|` in `K`.
  have hrel : (N.subgroupOf K).index = Nat.card A := by
    change N.relIndex K = Nat.card A
    rw [← Subgroup.relIndex_sup_left (H := K) (K := N), hsup, Subgroup.relIndex_top_right, hidx]
  have hc : (Nat.card N).Coprime N.index := by rw [hcardN, hidx]; exact hcop.symm
  have hdvd : Nat.card (N.subgroupOf K) ∣ Nat.card G := by
    rw [← hcardN, ← Subgroup.comap_subtype]
    exact Subgroup.card_comap_dvd_of_injective N K.subtype Subtype.coe_injective
  have hKcop : (Nat.card (N.subgroupOf K)).Coprime (N.subgroupOf K).index := by
    rw [hrel]
    exact hcop.symm.coprime_dvd_left hdvd
  -- Schur–Zassenhaus (existence) in `K`: a complement `B'` of `K ∩ N`.
  obtain ⟨B', hB'⟩ := Subgroup.exists_right_complement'_of_coprime (G := ↥K)
    (N := N.subgroupOf K) hKcop
  let B : Subgroup X := B'.map K.subtype
  have hBK : B ≤ K := by
    rintro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact z.2
  have hBN : B ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyB, hyN⟩
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp (show y ∈ B'.map K.subtype from hyB)
    rw [← hzy] at hyN ⊢
    have hzM : z ∈ N.subgroupOf K := by rw [Subgroup.mem_subgroupOf]; exact hyN
    have hzbot : z ∈ (⊥ : Subgroup ↥K) := disjoint_iff_inf_le.mp hB'.disjoint ⟨hzM, hz⟩
    have hz1 : z = 1 := Subgroup.mem_bot.mp hzbot
    rw [hz1]
    rfl
  have hcardB' : Nat.card B' = (N.subgroupOf K).index := (hB'.symm.index_eq_card).symm
  have hcardB : Nat.card B = Nat.card A := by
    change Nat.card (B'.map K.subtype) = Nat.card A
    rw [Subgroup.card_map_of_injective (f := K.subtype) Subtype.coe_injective, hcardB', hrel]
  have hNB : N.IsComplement' B := by
    rw [Subgroup.isComplement'_iff_card_mul_and_disjoint]
    refine ⟨?_, ?_⟩
    · rw [hcardN, hcardB, SemidirectProduct.card]
    · rw [disjoint_iff_inf_le, inf_comm, hBN]
  -- Schur–Zassenhaus (conjugacy): `B` is a conjugate of the canonical complement of `N`.
  obtain ⟨γ, hγ⟩ : ∃ γ : X, B = (SemidirectProduct.inr : A →* X).range.map
      (MulAut.conj γ).toMonoidHom := by
    rcases hsol with hA | hG
    · haveI : Group.IsSolvable A := hA
      refine Work.Coprime.schurZassenhaus_conj_of_solvable_quotient hc ?_ hNinr hNB
      exact Group.isSolvable_of_isSolvable_injective
        (f := QuotientGroup.kerLift (SemidirectProduct.rightHom (φ := φ)))
        (QuotientGroup.kerLift_injective _)
    · haveI : Group.IsSolvable G := hG
      have hsolN : Group.IsSolvable ↥N := by
        let f : ↥N →* G :=
          { toFun := fun x => x.1.left
            map_one' := by simp
            map_mul' := by
              intro x y
              have hx : x.1.right = 1 := (memN x.1).mp x.2
              rw [Subgroup.coe_mul, SemidirectProduct.mul_left, hx, map_one]
              simp }
        refine Group.isSolvable_of_isSolvable_injective (f := f) ?_
        intro x y hxy
        refine Subtype.ext ?_
        ext
        · exact hxy
        · rw [(memN x.1).mp x.2, (memN y.1).mp y.2]
      exact Work.Hall.SchurZassenhaus.hall_schurZassenhaus_conj hsolN hc hNinr hNB
  -- A conjugate of `A` inside `K` gives a fixed point.
  refine ⟨γ⁻¹ • ω₀, fun a => ?_⟩
  have hb_mem : γ * (SemidirectProduct.inr a : X) * γ⁻¹ ∈ B := by
    rw [hγ]
    refine Subgroup.mem_map.mpr ⟨(SemidirectProduct.inr a : X), ?_, ?_⟩
    · exact MonoidHom.mem_range.mpr ⟨a, rfl⟩
    · rw [MulEquiv.coe_toMonoidHom]
      exact MulAut.conj_apply γ (SemidirectProduct.inr a : X)
  have hbK : (γ * (SemidirectProduct.inr a : X) * γ⁻¹) • ω₀ = ω₀ := by
    have h1 : γ * (SemidirectProduct.inr a : X) * γ⁻¹ ∈ MulAction.stabilizer X ω₀ :=
      hBK hb_mem
    exact MulAction.mem_stabilizer_iff.mp h1
  have hbexp : (γ * (SemidirectProduct.inr a : X) * γ⁻¹) • ω₀
      = γ • ((SemidirectProduct.inr a : X) • (γ⁻¹ • ω₀)) := by
    rw [mul_smul, mul_smul]
  rw [hbexp] at hbK
  rw [← hInr a]
  have hfin : (SemidirectProduct.inr a : X) • (γ⁻¹ • ω₀) = γ⁻¹ • ω₀ := by
    have h := congrArg (fun z => γ⁻¹ • z) hbK
    rw [inv_smul_smul] at h
    exact h
  exact hfin

end Work.Coprime
