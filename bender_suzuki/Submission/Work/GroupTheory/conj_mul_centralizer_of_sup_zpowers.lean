import Mathlib
import Submission.Work.Coprime.schurZassenhaus_conj_of_solvable_quotient

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.GroupTheory

/-- **Wielandt's product lemma** (H. Wielandt, cited as `[28] p. 162` in Feit–Thompson,
"Solvability of groups of odd order", Pacific J. Math. 13 (1963); used in the proof of Lemma 9.1,
p. 805).  Let `A` be a normal Hall subgroup of the finite group `G` and let `b ∈ G` together with
`A` generate a complement: `A ⊔ ⟨b⟩ = ⊤` and `|A|` coprime to the order of `b` (so `A ∩ ⟨b⟩ = 1`
and `G = A⟨b⟩`).  Then every element of `A` can be conjugated into `C_A(b)·b`: for `a ∈ A` there
are `a' ∈ A` commuting with `b` and `g ∈ G` with `g * (a * b) * g⁻¹ = a' * b`.

The classical form ("if `G = AB` with `A` a normal Hall subgroup and `B` a complement, then every
element of `G` is conjugate to an element `ab = ba` with `a ∈ A`, `b ∈ B`") is equivalent:
the conclusion is existential in `g`, and the element `b` may be replaced by the cyclic subgroup it
generates.  The hypotheses are exactly Feit–Thompson's in the application `G = 𝔑_i`, `A = 𝔎_i`,
`⟨b⟩` a cyclic complement (`𝔎_i` is a Hall subgroup of `𝔑_i = N(𝔎_i)` by Definition 9.1(ii)(b)).
For `a = 1` the claim is `b = 1 * b`, and for `b = 1` it is `a = a * 1`.

The statement is FALSE without `[A.Normal]` (e.g. `G = SL(2,3)`, `A` of order 3, `B = Q₈`) and
without coprimality, so both hypotheses are needed.  Suggested route: reduce to `G = A ⋊ ⟨b⟩`
with `⟨b⟩` cyclic, so Schur–Zassenhaus conjugacy of complements applies with the *quotient* `⟨b⟩`
solvable (`Work.Coprime.schurZassenhaus_conj_of_solvable_quotient`), and use the coprime-action
machinery `C_G(b)·[G,b] = ⊤` (`Work.Coprime.commutator_fixedPoints_sup`) together with
`H¹(⟨b⟩, -) = 0` (`Work.Coprime.cocycle_is_coboundary`). -/
theorem conj_mul_centralizer_of_sup_zpowers {G : Type*} [Group G] [Fintype G] {A : Subgroup G}
    [A.Normal] {b : G} (hcop : (Nat.card A).Coprime (orderOf b))
    (htop : A ⊔ Subgroup.zpowers b = ⊤) (a : A) :
    ∃ (a' : A) (g : G), (a' : G) * b = b * (a' : G) ∧ g * ((a : G) * b) * g⁻¹ = (a' : G) * b := by
  classical
  -- ### Step 1: `A` and `⟨b⟩` are complementary in `G`
  have hdisjAB : Disjoint A (Subgroup.zpowers b) := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [Nat.card_zpowers]
    exact hcop
  have hcompAB : A.IsComplement' (Subgroup.zpowers b) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisjAB ?_
    rw [Set.eq_univ_iff_forall]
    intro g
    have hg : g ∈ A ⊔ Subgroup.zpowers b := by rw [htop]; exact Subgroup.mem_top g
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    exact Set.mem_mul.mpr ⟨y, hy, z, hz, hyz⟩
  -- ### Step 2: `A.index = orderOf b`
  have hindexA : A.index = orderOf b := by
    have h1 : Nat.card ↥A * A.index = Nat.card G := Subgroup.card_mul_index A
    have h2 : Nat.card ↥A * Nat.card ↥(Subgroup.zpowers b) = Nat.card G := hcompAB.card_mul_card
    rw [Nat.card_zpowers] at h2
    exact Nat.mul_left_cancel (Nat.card_pos) (h1.trans h2.symm)
  -- ### Step 3: the centralizer `C` of `x = a * b` supplements `A`
  set x : G := (a : G) * b with hx
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hC
  have hxC : x ∈ C := by
    rw [hC]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hbAC : b ∈ A ⊔ C := by
    have hb : b = (a : G)⁻¹ * x := by rw [hx]; group
    rw [hb]
    exact Subgroup.mul_mem_sup (A.inv_mem a.2) hxC
  have hsupAC : A ⊔ C = ⊤ := by
    have hle : A ⊔ Subgroup.zpowers b ≤ A ⊔ C :=
      sup_le le_sup_left (Subgroup.zpowers_le.mpr hbAC)
    rw [htop] at hle
    exact top_le_iff.mp hle
  -- ### Step 4: `A ⊓ C` is a normal Hall subgroup of `C`
  have hrelIndex : ((A ⊓ C).subgroupOf C).index = A.index := by
    show (A ⊓ C).relIndex C = A.index
    rw [Subgroup.inf_relIndex_right (H := A) (K := C)]
    rw [← Subgroup.relIndex_sup_left (H := C) (K := A)]
    rw [hsupAC, Subgroup.relIndex_top_right]
  have hcopC : Nat.Coprime (Nat.card ↥((A ⊓ C).subgroupOf C))
      (((A ⊓ C).subgroupOf C).index) := by
    have hcard2 : Nat.card ↥((A ⊓ C).subgroupOf A) = Nat.card ↥(A ⊓ C) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ C ≤ A)).toEquiv
    have hcard : Nat.card ↥((A ⊓ C).subgroupOf C) = Nat.card ↥(A ⊓ C) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ C ≤ C)).toEquiv
    rw [hcard, hrelIndex, hindexA]
    exact hcop.coprime_dvd_left
      (hcard2 ▸ Subgroup.card_subgroup_dvd_card ((A ⊓ C).subgroupOf A))
  -- ### Step 5: Schur–Zassenhaus, existence, inside `C`
  haveI hN₀ : ((A ⊓ C).subgroupOf C).Normal := by
    rw [Subgroup.inf_subgroupOf_right]
    exact Subgroup.Normal.comap (inferInstance : A.Normal) C.subtype
  obtain ⟨T', hT'⟩ :=
    Subgroup.exists_right_complement'_of_coprime (G := C) (N := (A ⊓ C).subgroupOf C) hcopC
  -- ### Step 6: transport `T'` to a complement `T` of `A` in `G`
  let T : Subgroup G := T'.map C.subtype
  have hTcard' : Nat.card ↥T' = A.index := by
    have h2 : Nat.card ↥((A ⊓ C).subgroupOf C) = Nat.card ↥(A ⊓ C) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ C ≤ C)).toEquiv
    have h1 : Nat.card ↥((A ⊓ C).subgroupOf C) * Nat.card ↥T' = Nat.card ↥C :=
      hT'.card_mul_card
    have h3 : Nat.card ↥((A ⊓ C).subgroupOf C) * A.index = Nat.card ↥C := by
      rw [← hrelIndex]
      exact Subgroup.card_mul_index ((A ⊓ C).subgroupOf C)
    exact Nat.mul_left_cancel (Nat.card_pos) (h1.trans h3.symm)
  have hcardT : Nat.card ↥T = Nat.card ↥T' := Subgroup.card_map_of_injective C.subtype_injective
  have hTle : T ≤ C := by
    intro y hy
    obtain ⟨z, _hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact z.2
  have hdisjTA : Disjoint T A := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hcardT, hTcard', hindexA]
    exact hcop.symm
  have hTinfA : T ⊓ A = ⊥ := disjoint_iff.mp hdisjTA
  have hcardTA : Nat.card ↥T * Nat.card ↥A = Nat.card G := by
    have hTeq : Nat.card ↥T = A.index := by rw [hcardT, hTcard']
    rw [hTeq, Nat.mul_comm A.index (Nat.card ↥A)]
    exact Subgroup.card_mul_index A
  have hTcompA : T.IsComplement' A :=
    Subgroup.isComplement'_of_card_mul_and_disjoint hcardTA hdisjTA
  -- ### Step 7: `G ⧸ A` is cyclic (hence solvable)
  have hgen : Subgroup.zpowers ((QuotientGroup.mk' A) b) = ⊤ := by
    refine le_antisymm le_top ?_
    intro q _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective A q
    have hg : g ∈ A ⊔ Subgroup.zpowers b := by rw [htop]; exact Subgroup.mem_top g
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    show (QuotientGroup.mk' A) g ∈ Subgroup.zpowers ((QuotientGroup.mk' A) b)
    rw [← hyz, map_mul]
    have hy1 : (QuotientGroup.mk' A) y = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hy
    rw [hy1, one_mul, ← hk, map_zpow]
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
  have hcommq : ∀ g₁ g₂ : G, ((QuotientGroup.mk' A) g₁) * ((QuotientGroup.mk' A) g₂) =
      ((QuotientGroup.mk' A) g₂) * ((QuotientGroup.mk' A) g₁) := by
    intro g₁ g₂
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (show (QuotientGroup.mk' A) g₁ ∈ Subgroup.zpowers ((QuotientGroup.mk' A) b) by
        rw [hgen]; exact Subgroup.mem_top _)
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp
      (show (QuotientGroup.mk' A) g₂ ∈ Subgroup.zpowers ((QuotientGroup.mk' A) b) by
        rw [hgen]; exact Subgroup.mem_top _)
    rw [← hk, ← hl]
    exact Commute.zpow_zpow_self ((QuotientGroup.mk' A) b) k l
  have hsolA : Group.IsSolvable (G ⧸ A) := by
    refine Group.isSolvable_of_comm (fun p q => ?_)
    obtain ⟨g₁, rfl⟩ := QuotientGroup.mk'_surjective A p
    obtain ⟨g₂, rfl⟩ := QuotientGroup.mk'_surjective A q
    exact hcommq g₁ g₂
  -- ### Step 8: Schur–Zassenhaus conjugacy in `G`
  obtain ⟨g, hg⟩ := Work.Coprime.schurZassenhaus_conj_of_solvable_quotient (G := G) (N := A)
    (H := T) (K := Subgroup.zpowers b) (by rw [hindexA]; exact hcop) hsolA hTcompA.symm hcompAB
  -- ### Step 9: extract a complement generator commuting with `x`
  have hbTg : b ∈ T.map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact Subgroup.mem_zpowers b
  obtain ⟨t, htT, htg⟩ := Subgroup.mem_map.mp hbTg
  have htg' : g * t * g⁻¹ = b := by
    have h := htg
    rwa [show (MulEquiv.toMonoidHom (MulAut.conj g)) t = MulAut.conj g t from rfl,
      MulAut.conj_apply] at h
  have htC : t ∈ C := hTle htT
  have htx : t * x = x * t := Subgroup.mem_centralizer_singleton_iff.mp htC
  set y : G := g * x * g⁻¹ with hy
  have hkey : (g * x * g⁻¹) * (g * t * g⁻¹) = (g * t * g⁻¹) * (g * x * g⁻¹) := by
    calc (g * x * g⁻¹) * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
      _ = g * (t * x) * g⁻¹ := by rw [htx]
      _ = (g * t * g⁻¹) * (g * x * g⁻¹) := by group
  have hyb : y * b = b * y := by
    calc y * b = (g * x * g⁻¹) * (g * t * g⁻¹) := by rw [hy, ← htg']
      _ = (g * t * g⁻¹) * (g * x * g⁻¹) := hkey
      _ = b * y := by rw [hy, htg']
  -- `y` has the same image in `G ⧸ A` as `b`
  have hyq : (QuotientGroup.mk' A) y = (QuotientGroup.mk' A) b := by
    have ha1 : (QuotientGroup.mk' A) (a : G) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact a.2
    have hcm : (QuotientGroup.mk' A) g * (QuotientGroup.mk' A) b =
        (QuotientGroup.mk' A) b * (QuotientGroup.mk' A) g := hcommq g b
    calc (QuotientGroup.mk' A) y
        = (QuotientGroup.mk' A) g * (QuotientGroup.mk' A) x * ((QuotientGroup.mk' A) g)⁻¹ := by
          rw [hy, map_mul, map_mul, map_inv]
      _ = (QuotientGroup.mk' A) g * (QuotientGroup.mk' A) b * ((QuotientGroup.mk' A) g)⁻¹ := by
          rw [hx, map_mul, ha1, one_mul]
      _ = (QuotientGroup.mk' A) b * (QuotientGroup.mk' A) g * ((QuotientGroup.mk' A) g)⁻¹ := by
          rw [hcm]
      _ = (QuotientGroup.mk' A) b := by group
  have hybA : y * b⁻¹ ∈ A := by
    rw [← QuotientGroup.eq_one_iff (N := A) (x := y * b⁻¹)]
    show (QuotientGroup.mk' A) (y * b⁻¹) = 1
    rw [map_mul, map_inv, hyq, mul_inv_cancel]
  -- ### Conclusion
  refine ⟨⟨y * b⁻¹, hybA⟩, g, ?_, ?_⟩
  · show (y * b⁻¹) * b = b * (y * b⁻¹)
    have hyb' : b * y * b⁻¹ = y := by rw [← hyb]; group
    calc (y * b⁻¹) * b = y := by group
      _ = b * y * b⁻¹ := hyb'.symm
      _ = b * (y * b⁻¹) := by group
  · show g * ((a : G) * b) * g⁻¹ = (y * b⁻¹) * b
    rw [hy, hx]
    group

end Work.GroupTheory
