import Mathlib
import Submission.Work.Coprime.Defs
import Submission.Work.Hall.SchurZassenhaus.hall_sz_conj_abelian

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.Coprime

universe u

/-- The center is invariant under any action by group automorphisms. -/
private theorem isInvariant_center (A : Type*) {G : Type u} [Group A] [Group G]
    [MulDistribMulAction A G] : FT.IsInvariant A (Subgroup.center G) := by
  refine ⟨fun a => Subgroup.ext fun x => ?_⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_center_iff,
    Subgroup.mem_center_iff]
  constructor
  · intro h g
    have h' := h (a⁻¹ • g)
    have := congrArg (fun t => a • t) h'
    simpa [smul_mul'] using this
  · intro h g
    have h' := h (a • g)
    have := congrArg (fun t => a⁻¹ • t) h'
    simpa [smul_mul'] using this

/-- **Step A.**  If `N ≤ G` is an `A`-invariant *abelian* subgroup with `|A|` coprime to `|N|` and
`x ∈ G` satisfies `x⁻¹ (a • x) ∈ N` for all `a ∈ A`, then `x ∈ C_G(A)·N ⊆ C_G(A) ⊔ N`. -/
private theorem mem_fixedPoints_sup_of_commutator_sub
    (A : Type*) {G : Type u} [Group A] [Group G] [Finite A] [Finite G] [MulDistribMulAction A G]
    {N : Subgroup G} [hNin : FT.IsInvariant A N] (hN : IsMulCommutative N)
    (hcop : (Nat.card A).Coprime (Nat.card N))
    {x : G} (hx : ∀ a : A, x⁻¹ * (a • x) ∈ N) :
    x ∈ FT.fixedPoints A G ⊔ N := by
  classical
  letI : MulDistribMulAction A ↥N :=
    { smul := fun a y => ⟨a • (y : G), hNin.smul_mem a y.2⟩
      one_smul := fun y => Subtype.ext (one_smul A (y : G))
      mul_smul := fun a b y => Subtype.ext (mul_smul a b (y : G))
      smul_one := fun a => Subtype.ext (smul_one a)
      smul_mul := fun a y z => Subtype.ext (smul_mul' a (y : G) (z : G)) }
  have coe_smul : ∀ (a : A) (y : ↥N), ((a • y : ↥N) : G) = a • (y : G) := fun _ _ => rfl
  let φ : A →* MulAut ↥N := MulDistribMulAction.toMulAut A ↥N
  let f : A → ↥N := fun a => ⟨x⁻¹ * (a • x), hx a⟩
  have hf : ∀ a b : A, f (a * b) = f a * (φ a) (f b) := by
    intro a b
    refine Subtype.ext ?_
    show x⁻¹ * ((a * b) • x) = (x⁻¹ * (a • x)) * (a • (x⁻¹ * (b • x)))
    rw [mul_smul, smul_mul', smul_inv']
    group
  obtain ⟨n', hn'⟩ := Work.Hall.SchurZassenhaus.exists_coboundary φ hcop.symm f hf
  have hcomm : ∀ u v : G, u ∈ N → v ∈ N → u * v = v * u := fun u v hu hv =>
    congrArg Subtype.val ((isMulCommutative_iff.mp hN) ⟨u, hu⟩ ⟨v, hv⟩)
  have hzN : ∀ a : A, a • (n' : G) ∈ N := fun a => hNin.smul_mem a n'.2
  have hc : x * (n' : G)⁻¹ ∈ FT.fixedPoints A G := by
    rw [FT.mem_fixedPoints]
    intro a
    have h3 : x⁻¹ * (a • x) = (a • (n' : G)) * (n' : G)⁻¹ := by
      have h := congrArg (Subtype.val) (hn' a)
      simp only [f, φ, Subgroup.coe_mul, Subgroup.coe_inv,
        MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply, coe_smul] at h
      exact h
    have h2 : a • x = x * (a • (n' : G)) * (n' : G)⁻¹ := by
      calc a • x = x * (x⁻¹ * (a • x)) := by group
        _ = x * ((a • (n' : G)) * (n' : G)⁻¹) := by rw [h3]
        _ = x * (a • (n' : G)) * (n' : G)⁻¹ := by group
    have hyz : (a • (n' : G)) * (n' : G)⁻¹ = (n' : G)⁻¹ * (a • (n' : G)) :=
      hcomm _ _ (hzN a) (N.inv_mem n'.2)
    calc a • (x * (n' : G)⁻¹) = (a • x) * (a • (n' : G))⁻¹ := by rw [smul_mul', smul_inv']
      _ = x * (a • (n' : G)) * (n' : G)⁻¹ * (a • (n' : G))⁻¹ := by rw [h2]
      _ = x * ((a • (n' : G)) * (n' : G)⁻¹ * (a • (n' : G))⁻¹) := by group
      _ = x * ((n' : G)⁻¹ * (a • (n' : G)) * (a • (n' : G))⁻¹) := by rw [hyz]
      _ = x * (n' : G)⁻¹ := by group
  rw [show x = (x * (n' : G)⁻¹) * (n' : G) from by group]
  exact Subgroup.mul_mem (FT.fixedPoints A G ⊔ N) (Subgroup.mem_sup_left hc)
    (Subgroup.mem_sup_right n'.2)

/-- The commutator `[G, A]` maps onto `[G/N, A]` for an `A`-invariant normal `N`. -/
private theorem map_commutator_quotient (A : Type*) {G : Type u} [Group A] [Group G]
    [MulDistribMulAction A G] (N : Subgroup G) [N.Normal] [FT.IsInvariant A N] :
    (FT.commutator A (⊤ : Subgroup G)).map (QuotientGroup.mk' N)
      = FT.commutator A (⊤ : Subgroup (G ⧸ N)) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine FT.commutator_le (H := (⊤ : Subgroup G))
      (K := (FT.commutator A (⊤ : Subgroup (G ⧸ N))).comap (QuotientGroup.mk' N)) fun a x _ => ?_
    rw [Subgroup.mem_comap]
    have hkey : (QuotientGroup.mk' N) (x⁻¹ * (a • x))
        = ((QuotientGroup.mk' N) x)⁻¹ * (a • (QuotientGroup.mk' N) x) := by
      rw [map_mul, map_inv]
      rfl
    rw [hkey]
    exact FT.le_commutator a trivial
  · refine FT.commutator_le (H := (⊤ : Subgroup (G ⧸ N)))
      (K := (FT.commutator A (⊤ : Subgroup G)).map (QuotientGroup.mk' N)) fun a x _ => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * (a • g), FT.le_commutator a trivial, ?_⟩
    rw [map_mul, map_inv]
    rfl

/-- **Coprime action on a `p`-group.**  If `A` (finite, coprime to `|G|`) acts on the finite
`p`-group `G`, then `G = C_G(A)·[G, A]`. -/
private theorem cent_sup_commutator_eq_top_of_isPGroup
    (A : Type*) {G : Type u} [Group A] [Group G] [Finite A] [Finite G] [MulDistribMulAction A G]
    (hcop : (Nat.card A).Coprime (Nat.card G))
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G) :
    FT.fixedPoints A G ⊔ FT.commutator A (⊤ : Subgroup G) = ⊤ := by
  classical
  suffices key : ∀ n : ℕ, ∀ (G' : Type u) [Group G'] [Finite G'] [MulDistribMulAction A G'],
      Nat.card G' = n → ∀ (p : ℕ) [Fact p.Prime], IsPGroup p G' →
      (Nat.card A).Coprime (Nat.card G') →
      FT.fixedPoints A G' ⊔ FT.commutator A (⊤ : Subgroup G') = ⊤ by
    exact key (Nat.card G) G rfl p hG hcop
  intro n
  refine Nat.strong_induction_on (p := fun n => ∀ (G : Type u) [Group G] [Finite G]
      [MulDistribMulAction A G], Nat.card G = n → ∀ (p : ℕ) [Fact p.Prime], IsPGroup p G →
      (Nat.card A).Coprime (Nat.card G) →
      FT.fixedPoints A G ⊔ FT.commutator A (⊤ : Subgroup G) = ⊤) n ?_
  intro m ih G _ _ _ hcard p _ hG hcop
  by_cases hcomm : IsMulCommutative G
  · haveI : IsMulCommutative G := hcomm
    haveI hNab : IsMulCommutative ↥(FT.commutator A (⊤ : Subgroup G)) := inferInstance
    have hcopN : (Nat.card A).Coprime (Nat.card ↥(FT.commutator A (⊤ : Subgroup G))) :=
      hcop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card _)
    refine eq_top_iff.mpr fun x _ => ?_
    exact mem_fixedPoints_sup_of_commutator_sub A hNab hcopN (fun a => FT.le_commutator a trivial)
  · haveI : Nontrivial G := by
      rw [isMulCommutative_iff] at hcomm
      push Not at hcomm
      obtain ⟨a, b, hab⟩ := hcomm
      exact ⟨a, b, fun h => hab (by rw [h])⟩
    let Z : Subgroup G := Subgroup.center G
    haveI hZn : Z.Normal := Subgroup.instNormalCenter
    haveI hZi : FT.IsInvariant A Z := isInvariant_center A
    have hZne : Z ≠ ⊤ := fun h => hcomm (Subgroup.center_eq_top_iff.mp h)
    haveI : Nontrivial (G ⧸ Z) := QuotientGroup.nontrivial_iff.mpr hZne
    have hlt : Nat.card (G ⧸ Z) < Nat.card G := by
      have h1 : Nat.card G = Nat.card (G ⧸ Z) * Nat.card Z :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup Z
      have hZnt : Nontrivial ↥Z := show Nontrivial ↥(Subgroup.center G) from
        IsPGroup.center_nontrivial hG
      have h2 : 1 < Nat.card (G ⧸ Z) := Finite.one_lt_card
      have h3 : 1 < Nat.card Z := Finite.one_lt_card
      nlinarith
    have hquot : FT.fixedPoints A (G ⧸ Z) ⊔ FT.commutator A (⊤ : Subgroup (G ⧸ Z)) = ⊤ :=
      ih _ (hcard ▸ hlt) _ rfl p (hG.to_quotient Z)
        (hcop.coprime_dvd_right ⟨Nat.card Z, Subgroup.card_eq_card_quotient_mul_card_subgroup Z⟩)
    have hZle : Z ≤ FT.fixedPoints A G ⊔ FT.commutator A (⊤ : Subgroup G) := by
      intro z hz
      have hNZ : FT.commutator A Z ≤ Z := FT.commutator_le fun a y hy =>
        Z.mul_mem (Z.inv_mem hy)
          (FT.IsInvariant.smul_mem (inferInstance : FT.IsInvariant A Z) a hy)
      have hNsub : FT.commutator A Z ≤ FT.commutator A (⊤ : Subgroup G) := FT.commutator_mono le_top
      haveI hNab : IsMulCommutative ↥(FT.commutator A Z) :=
        IsMulCommutative.of_comm (fun u v => Subtype.ext (by
          have hh := (isMulCommutative_iff.mp (Subgroup.center.isMulCommutative G))
            (⟨(u : G), hNZ u.2⟩ : ↥Z) (⟨(v : G), hNZ v.2⟩ : ↥Z)
          simpa using congrArg Subtype.val hh))
      have hcopN : (Nat.card A).Coprime (Nat.card ↥(FT.commutator A Z)) :=
        hcop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card _)
      exact (sup_le_sup_left hNsub (FT.fixedPoints A G))
        (mem_fixedPoints_sup_of_commutator_sub A hNab hcopN (fun a => FT.le_commutator a hz))
    have hfix : FT.fixedPoints A (G ⧸ Z)
        ≤ (FT.fixedPoints A G ⊔ FT.commutator A (⊤ : Subgroup G)).map (QuotientGroup.mk' Z) := by
      intro cbar hcbar
      obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective Z cbar
      have hcfix : ∀ a : A, c⁻¹ * (a • c) ∈ Z := by
        intro a
        have hsmul : a • (QuotientGroup.mk' Z) c = (QuotientGroup.mk' Z) (a • c) := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, FT.quotient_smul_mk]
        rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker, map_mul, map_inv, ← hsmul, hc,
          FT.smul_eq_self_of_mem_fixedPoints hcbar a, inv_mul_cancel]
      have hcS : c ∈ FT.fixedPoints A G ⊔ FT.commutator A (⊤ : Subgroup G) :=
        (sup_le le_sup_left hZle)
          (mem_fixedPoints_sup_of_commutator_sub A (Subgroup.center.isMulCommutative G)
            (hcop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card Z)) hcfix)
      exact Subgroup.mem_map.mpr ⟨c, hcS, hc⟩
    have hcom : FT.commutator A (⊤ : Subgroup (G ⧸ Z))
        ≤ (FT.fixedPoints A G ⊔ FT.commutator A (⊤ : Subgroup G)).map (QuotientGroup.mk' Z) := by
      rw [← map_commutator_quotient A Z]
      exact Subgroup.map_mono le_sup_right
    have hSm : (FT.fixedPoints A G ⊔ FT.commutator A (⊤ : Subgroup G)).map (QuotientGroup.mk' Z)
        = ⊤ := by
      rw [eq_top_iff, ← hquot]
      exact sup_le hfix hcom
    refine eq_top_iff.mpr fun g _ => ?_
    have hg : (QuotientGroup.mk' Z) g
        ∈ (FT.fixedPoints A G ⊔ FT.commutator A (⊤ : Subgroup G)).map (QuotientGroup.mk' Z) :=
      hSm ▸ Subgroup.mem_top _
    obtain ⟨s, hs, hsg⟩ := Subgroup.mem_map.mp hg
    have hz : s⁻¹ * g ∈ Z := by
      rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker, map_mul, map_inv, hsg, inv_mul_cancel]
    rw [show g = s * (s⁻¹ * g) from by group]
    exact Subgroup.mul_mem (FT.fixedPoints A G ⊔ FT.commutator A (⊤ : Subgroup G)) hs (hZle hz)

theorem trivial_of_trivial_on_frattiniQuotient (A : Type*) {G : Type*} [Group A] [Group G]
    [Finite A] [Finite G] [MulDistribMulAction A G] (hcop : (Nat.card A).Coprime (Nat.card G))
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (h : FT.commutator A (⊤ : Subgroup G) ≤ frattini G) : FT.IsTrivialOn A G := by
  rw [← FT.fixedPoints_eq_top_iff]
  have hsup := cent_sup_commutator_eq_top_of_isPGroup A hcop p hG
  refine frattini_nongenerating (le_antisymm le_top ?_)
  rw [← hsup]
  exact sup_le_sup (le_refl _) h

end Work.Coprime
