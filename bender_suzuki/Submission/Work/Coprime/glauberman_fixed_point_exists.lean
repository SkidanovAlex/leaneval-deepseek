import Mathlib
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Basic
import Submission.Work.Coprime.cocycle_is_coboundary
import Submission.Work.Hall.SchurZassenhaus.hall_schurZassenhaus_conj
import Submission.Work.Coprime.schurZassenhaus_conj_of_solvable_quotient
import Submission.Work.Coprime.exists_conj_le_of_isComplement

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.Coprime

/-- **Glauberman's fixed-point lemma (existence), `Ω ≅ G/H` form.**

Let `A` act by automorphisms on a finite group `G`, let `Ω` be a finite nonempty transitive
`G`-set, and suppose the actions of `A` and `G` on `Ω` are compatible
(`a • (g • ω) = (a • g) • (a • ω)`).  If `|A|` and `|G|` are coprime and `A` or `G` is solvable,
then `A` has a fixed point on `Ω`.

The proof forms the semidirect product `X = G ⋊ A` (which acts on `Ω` by `(g,a) • ω = g • a • ω`),
observes that `Ω` is a transitive `X`-set, and applies the group-theoretic core
`exists_conj_le_of_isComplement` to the stabilizer `K = X_ω` of a point: if `Gsub ≤ X` is the
copy of `G` and `Asub ≤ X` the copy of `A`, then `Gsub` is a normal Hall subgroup of `X` with
complement `Asub`, and `Gsub ⊔ K = X`; a conjugate of `K` therefore contains `Asub`, i.e. some
conjugate `x • ω` of `ω` is stabilised by `Asub`, hence fixed by `A`. -/
theorem glauberman_fixed_point_exists (A : Type*) (G Ω : Type*) [Group A] [Group G] [Finite A] [Finite G]
    [MulDistribMulAction A G] [MulAction G Ω] [MulAction A Ω] [Finite Ω] [Nonempty Ω]
    (hcop : (Nat.card A).Coprime (Nat.card G))
    (hsol : Group.IsSolvable A ∨ Group.IsSolvable G)
    (hcomp : ∀ (a : A) (g : G) (ω : Ω), a • (g • ω) = (a • g) • (a • ω))
    (htrans : ∀ ω ω' : Ω, ∃ g : G, g • ω = ω') :
    ∃ ω : Ω, ∀ a : A, a • ω = ω := by
  classical
  let φ : A →* MulAut G := MulDistribMulAction.toMulAut A G
  let xsmul : (G ⋊[φ] A) → Ω → Ω := fun x ω => x.left • (x.right • ω)
  have hφ : ∀ (a : A) (g : G), φ a g = a • g := by
    intro a g
    simp [φ, MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply]
  have xs_one : ∀ ω, xsmul 1 ω = ω := by
    intro ω; simp [xsmul]
  have xs_mul : ∀ x y : G ⋊[φ] A, ∀ ω, xsmul (x * y) ω = xsmul x (xsmul y ω) := by
    intro x y ω
    simp only [xsmul, SemidirectProduct.mul_left, SemidirectProduct.mul_right]
    rw [hφ x.right y.left]
    rw [hcomp x.right y.left (y.right • ω)]
    rw [mul_smul, mul_smul]
  letI : MulAction (G ⋊[φ] A) Ω :=
    { smul := xsmul, one_smul := xs_one, mul_smul := xs_mul }
  haveI : Finite (G ⋊[φ] A) := Finite.of_equiv (G × A) (SemidirectProduct.equivProd (φ := φ)).symm
  obtain ⟨ω0⟩ := (inferInstance : Nonempty Ω)
  let K : Subgroup (G ⋊[φ] A) := MulAction.stabilizer (G ⋊[φ] A) ω0
  let Gsub : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl (φ := φ)).range
  let Asub : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr (φ := φ)).range
  have hGsubEq : Gsub = SemidirectProduct.rightHom.ker :=
    SemidirectProduct.range_inl_eq_ker_rightHom
  haveI : Gsub.Normal := hGsubEq ▸ MonoidHom.normal_ker (SemidirectProduct.rightHom (φ := φ))
  have htransX : ∀ ω ω' : Ω, ∃ x : G ⋊[φ] A, x • ω = ω' := by
    intro ω ω'
    obtain ⟨g, hg⟩ := htrans ω ω'
    refine ⟨(SemidirectProduct.inl g : G ⋊[φ] A), ?_⟩
    have hx' : (SemidirectProduct.inl g : G ⋊[φ] A) • ω = g • ω := by
      show xsmul (SemidirectProduct.inl g) ω = g • ω
      simp [xsmul]
    rw [hx', hg]
  have hcomp' : Gsub.IsComplement' Asub := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff_inf_le]
      rintro x ⟨hx1, hx2⟩
      obtain ⟨g, rfl⟩ := hx1
      obtain ⟨a, ha⟩ := hx2
      have hg1 : g = 1 := by
        have h := congrArg SemidirectProduct.left ha
        simpa using h.symm
      subst hg1
      simp
    · rw [Set.eq_univ_iff_forall]
      intro x
      refine Set.mem_mul.mpr ⟨SemidirectProduct.inl x.left, ⟨x.left, rfl⟩,
        SemidirectProduct.inr x.right, ⟨x.right, rfl⟩, ?_⟩
      have hx : (⟨x.left, x.right⟩ : G ⋊[φ] A) = x := by ext <;> rfl
      rw [← hx]
      exact (SemidirectProduct.mk_eq_inl_mul_inr x.right x.left).symm
  have hsup : Gsub ⊔ K = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨g, hg⟩ := htrans ω0 (x • ω0)
    have h1 : SemidirectProduct.inl g ∈ Gsub := ⟨g, rfl⟩
    have h2 : (SemidirectProduct.inl g)⁻¹ * x ∈ K := by
      rw [MulAction.mem_stabilizer_iff]
      show ((SemidirectProduct.inl g)⁻¹ * x) • ω0 = ω0
      rw [mul_smul]
      have hg' : (SemidirectProduct.inl g : G ⋊[φ] A) • ω0 = x • ω0 := by
        have hx' : (SemidirectProduct.inl g : G ⋊[φ] A) • ω0 = g • ω0 := by
          show xsmul (SemidirectProduct.inl g) ω0 = g • ω0
          simp [xsmul]
        rw [hx', hg]
      rw [← hg', inv_smul_smul]
    have hx' : x = SemidirectProduct.inl g * ((SemidirectProduct.inl g)⁻¹ * x) := by group
    rw [hx']
    exact Subgroup.mul_mem_sup h1 h2
  have hcardGsub : Nat.card Gsub = Nat.card G :=
    (Nat.card_congr (MonoidHom.ofInjective (f := (SemidirectProduct.inl : G →* (G ⋊[φ] A)))
      SemidirectProduct.inl_injective).toEquiv).symm
  have hcardAsub : Nat.card Asub = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective (f := (SemidirectProduct.inr : A →* (G ⋊[φ] A)))
      SemidirectProduct.inr_injective).toEquiv).symm
  have hindexGsub : Gsub.index = Nat.card A := by
    rw [Subgroup.IsComplement'.index_eq_card hcomp'.symm, hcardAsub]
  have hc : (Nat.card Gsub).Coprime Gsub.index := by
    rw [hcardGsub, hindexGsub]; exact hcop.symm
  have hsol' : Group.IsSolvable Gsub ∨ Group.IsSolvable ((G ⋊[φ] A) ⧸ Gsub) := by
    rcases hsol with hA | hG
    · right
      haveI := hA
      have e : (G ⋊[φ] A) ⧸ Gsub ≃* A :=
        (QuotientGroup.quotientMulEquivOfEq hGsubEq).trans
          (QuotientGroup.quotientKerEquivOfSurjective SemidirectProduct.rightHom
            SemidirectProduct.rightHom_surjective)
      exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    · left
      haveI := hG
      have e : G ≃* Gsub := MonoidHom.ofInjective (f := (SemidirectProduct.inl : G →* (G ⋊[φ] A)))
        SemidirectProduct.inl_injective
      exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  obtain ⟨x, hx⟩ := exists_conj_le_of_isComplement (G := Gsub) (A := Asub) (K := K)
    hc hcomp' hsup hsol'
  refine ⟨x • ω0, fun a => ?_⟩
  have hmem : SemidirectProduct.inr a ∈ K.map (MulAut.conj x).toMonoidHom := hx ⟨a, rfl⟩
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj x ω0] at hmem
  have hfix : (SemidirectProduct.inr a) • (x • ω0) = x • ω0 := MulAction.mem_stabilizer_iff.mp hmem
  rwa [show (SemidirectProduct.inr a) • (x • ω0) = a • (x • ω0) from by
    show xsmul (SemidirectProduct.inr a) (xsmul x ω0) = a • (xsmul x ω0)
    simp [xsmul]] at hfix

end Work.Coprime
