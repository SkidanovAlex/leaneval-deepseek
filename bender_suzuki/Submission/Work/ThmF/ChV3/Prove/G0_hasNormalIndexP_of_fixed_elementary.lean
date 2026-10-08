import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.Coprime.abelian_split
import Submission.Work.Coprime.Internal
import Submission.Work.Coprime.Basic
import Submission.Work.Coprime.commutator_normal
import Submission.Work.PGroup.exists_isCoatom_notMem_of_normal
import Submission.Work.PGroup.card_sup_mul_card_inf_of_le_normalizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# G0: a fixed vector in an elementary abelian section gives a quotient of order `p`

`X = S C` with `S ◁ X` a `p`-subgroup, `C` a `p'`-subgroup, `N ◁ X` with `N ≤ S` such that
`S/N` is elementary abelian (`[S,S] ≤ N` and `S^p ≤ N`), and some `x ∈ S − N` is fixed by `C`
modulo `N`.  Then `X` has a normal subgroup of index `p` (Peterfalvi II, Ch. V §3, step (12)'s
input G0).

The mathematical content is Maschke/coprime-action theory: in `Q = X/N` the image `V = S/N` is an
elementary abelian normal `p`-subgroup, `Q = V · A` with `A` the image of `C` and `V ∩ A = 1`, and
the image `x̄` of `x` is a nontrivial element of `V` fixed by `A`.  The coprime decomposition
`V = C_V(A) · [V,A]` (`Work.Coprime.abelian_split`) shows that `A` acts trivially on `V/[V,A]` and
that `x̄ ∉ [V,A]`; the preimage in `V` of a subgroup of index `p` of `V/[V,A]` avoiding `x̄` is an
`A`-invariant subgroup `V' ≤ V` of index `p`, and `M = V' · A` is the required normal subgroup of
index `p`.

The statement of the paper's lemma is the theorem `G0_hasNormalIndexP_of_fixed_elementary` at the
end of this file; it is obtained from the abstract coprime-action engine
`exists_normal_index_prime_of_coprime_fixed` by passing to the quotient `X ⧸ N`.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.ThmF.ChV3.Prove

/-- A nontrivial abelian group of exponent `p` has a subgroup of index `p` avoiding any prescribed
non-identity element (the dual statement that a nonzero vector can be separated from `0` by a
linear functional, over the prime field `𝔽_p`). -/
theorem exists_index_prime_not_mem_of_exp_p {V : Type*} [Group V] [Finite V] {p : ℕ}
    (hp : p.Prime) [IsMulCommutative V] (hexp : ∀ v : V, v ^ p = 1) {x : V} (hx : x ≠ 1) :
    ∃ W : Subgroup V, W.index = p ∧ x ∉ W := by
  have hexp' : Monoid.exponent V ∣ p :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hexp
  obtain ⟨g, hgx, hgk⟩ := Work.PGroup.exists_monoidHom_zmod_ker_index (Q := V) hp hexp' hx
  exact ⟨g.ker, hgk, fun h => hgx (MonoidHom.mem_ker.mpr h)⟩

/-- **Coprime-action engine.**  Let `Q` be a finite group, `V ◁ Q` a commutative subgroup of
exponent `p`, `A ≤ Q` of order prime to `p` with `Q = V · A` and `V ∩ A = 1`.  If `x ∈ V` is a
non-identity element fixed by `A`, then `Q` has a normal subgroup of index `p`. -/
theorem exists_normal_index_prime_of_coprime_fixed {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) {V A : Subgroup Q} [hVc : IsMulCommutative ↥V] (hVn : V.Normal)
    (hVe : ∀ v : ↥V, v ^ p = 1) (hAcop : ¬ p ∣ Nat.card A)
    (hsup : V ⊔ A = ⊤) (hinf : V ⊓ A = ⊥)
    {x : Q} (hxV : x ∈ V) (hxf : ∀ a ∈ A, a * x * a⁻¹ = x) (hxne : x ≠ 1) :
    ∃ M : Subgroup Q, M.Normal ∧ M.index = p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hVA : A ≤ Subgroup.normalizer (V : Set Q) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hVn]; exact le_top
  haveI hNVA : FT.Normalizes A V := ⟨hVA⟩
  -- `V` is a `p`-group, so `|V|` is a power of `p`, hence coprime to `|A|`
  have hVp : IsPGroup p ↥V :=
    IsPGroup.of_exponent_dvd_pow (n := 1) (by
      rw [pow_one]; exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hVe)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := ↥V)).mp hVp
  have hcop : (Nat.card A).Coprime (Nat.card ↥V) := by
    rw [hn]
    exact (Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr hAcop)).pow_right n
  -- the coprime decomposition `V = C_V(A) · [V,A]`
  have hcompl : (FT.fixedPoints ↥A ↥V).IsComplement'
      (FT.commutator ↥A (⊤ : Subgroup ↥V)) :=
    Work.Coprime.abelian_split ↥A (G := ↥V) hcop
  set C : Subgroup ↥V := FT.fixedPoints ↥A ↥V with hCdef
  set D : Subgroup ↥V := FT.commutator ↥A (⊤ : Subgroup ↥V) with hDdef
  haveI hDn : D.Normal := Work.Coprime.commutator_normal ↥A
  haveI hDinv : FT.IsInvariant ↥A D := inferInstance
  have hxVfix : (⟨x, hxV⟩ : ↥V) ∈ FT.fixedPoints ↥A ↥V := by
    rw [FT.mem_fixedPoints]
    intro a
    apply Subtype.ext
    show (a : Q) * x * (a : Q)⁻¹ = x
    exact hxf a a.2
  -- `x` is not in the commutator part
  have hxD : (⟨x, hxV⟩ : ↥V) ∉ D := by
    intro hmem
    obtain ⟨_, _, huniq⟩ :=
      (Subgroup.isComplement'_def.mp hcompl).existsUnique (⟨x, hxV⟩ : ↥V)
    have e1 : (((1 : ↥C), (⟨⟨x, hxV⟩, hmem⟩ : ↥D)) : ↥C × ↥D) =
        ((⟨⟨x, hxV⟩, hxVfix⟩ : ↥C), (1 : ↥D)) :=
      (huniq _ (by simp)).trans (huniq _ (by simp)).symm
    have h3 := congrArg (fun y : ↥C × ↥D => ((y.1 : ↥V))) e1
    have hx1 : (⟨x, hxV⟩ : ↥V) = 1 := by simpa using h3.symm
    exact hxne (Subtype.ext_iff.mp hx1)
  -- the action on the quotient `V/[V,A]` is trivial
  have htriv : FT.IsTrivialOn ↥A (↥V ⧸ D) :=
    (FT.isTrivialOn_quotient_iff (A := ↥A) (G := ↥V) D).mpr le_rfl
  have hQcomm : ∀ a b : (↥V ⧸ D), a * b = b * a := by
    intro a b
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective D a
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective D b
    simpa only [map_mul] using
      congrArg (QuotientGroup.mk' D) (IsMulCommutative.is_comm.comm u v)
  haveI : IsMulCommutative (↥V ⧸ D) := ⟨⟨hQcomm⟩⟩
  have hexpQ : ∀ y : (↥V ⧸ D), y ^ p = 1 := by
    intro y
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective D y
    rw [← map_pow, hVe v, map_one]
  have hxbar : (QuotientGroup.mk' D (⟨x, hxV⟩ : ↥V)) ≠ 1 := fun h =>
    hxD ((QuotientGroup.eq_one_iff (⟨x, hxV⟩ : ↥V)).mp (by
      rwa [QuotientGroup.mk'_apply] at h))
  -- a subgroup of index `p` of `V/[V,A]` avoiding the image of `x`
  obtain ⟨Wb, hWbidx, hWbnotmem⟩ :=
    exists_index_prime_not_mem_of_exp_p hp (V := ↥V ⧸ D) hexpQ hxbar
  set W : Subgroup ↥V := Wb.comap (QuotientGroup.mk' D) with hWdef
  have hWidx : W.index = p := by
    rw [hWdef, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective D)]
    exact hWbidx
  have hxW : (⟨x, hxV⟩ : ↥V) ∉ W := fun h => hWbnotmem (by
    rw [hWdef, Subgroup.mem_comap] at h; exact h)
  have hDW : D ≤ W := by
    intro d hd
    rw [hWdef, Subgroup.mem_comap]
    have h1 : (QuotientGroup.mk' D) d = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff d).mpr hd
    rw [h1]; exact Wb.one_mem
  -- `W` is invariant under the action of `A`
  have hWinv : ∀ (a : ↥A), ∀ v ∈ W, a • v ∈ W := by
    intro a v hv
    rw [hWdef, Subgroup.mem_comap] at hv ⊢
    rw [QuotientGroup.mk'_apply] at hv ⊢
    rw [← FT.quotient_smul_mk (A := ↥A) (G := ↥V) (N := D) (a := a) (g := v)]
    rw [htriv a (v : (↥V ⧸ D))]
    exact hv
  -- the subgroup `V' ≤ Q` obtained from `W`
  set V' : Subgroup Q := W.map V.subtype with hV'def
  have hV'leV : V' ≤ V := Subgroup.map_subtype_le W
  have hV'sub : V'.subgroupOf V = W := by
    rw [hV'def]
    ext y
    constructor
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hy
      have hwy' : w = y := Subtype.ext hwy
      rwa [← hwy']
    · intro hy
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
  have hV'idx : (V'.subgroupOf V).index = p := by rw [hV'sub]; exact hWidx
  -- `V'` is invariant under `A`
  have hV'A : ∀ a ∈ A, ∀ y ∈ V', a * y * a⁻¹ ∈ V' := by
    intro a ha y hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨(⟨a, ha⟩ : ↥A) • w, hWinv ⟨a, ha⟩ w hw, ?_⟩
    exact FT.conj_smul_coe A V ⟨a, ha⟩ w
  -- `V` normalizes `V'` (as `V` is commutative)
  have hmul_comm : ∀ v ∈ V, ∀ y ∈ V, v * y = y * v := fun v hv y hy =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨v, hv⟩ : ↥V) (⟨y, hy⟩ : ↥V))
  have hVV' : ∀ v ∈ V, ∀ y ∈ V', v * y * v⁻¹ ∈ V' := by
    intro v hv y hy
    have hvy : v * y = y * v := hmul_comm v hv y (hV'leV hy)
    rw [hvy, mul_assoc, mul_inv_cancel, mul_one]
    exact hy
  have hVN' : V ≤ Subgroup.normalizer (V' : Set Q) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hVV' v hv y
    · intro hy
      have h := hVV' v⁻¹ (V.inv_mem hv) (v * y * v⁻¹) hy
      rwa [show v⁻¹ * (v * y * v⁻¹) * (v⁻¹)⁻¹ = y by group] at h
  have hAN' : A ≤ Subgroup.normalizer (V' : Set Q) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hV'A a ha y
    · intro hy
      have h := hV'A a⁻¹ (A.inv_mem ha) (a * y * a⁻¹) hy
      rwa [show a⁻¹ * (a * y * a⁻¹) * (a⁻¹)⁻¹ = y by group] at h
  have hV'normal : V'.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    refine eq_top_iff.mpr fun q _ => ?_
    have hq : q ∈ V ⊔ A := hsup ▸ Subgroup.mem_top q
    change q ∈ (↑(V ⊔ A) : Set Q) at hq
    rw [Subgroup.normal_mul V A] at hq
    obtain ⟨v, hv, a, ha, rfl⟩ := Set.mem_mul.mp hq
    exact Subgroup.mul_mem _ (hVN' hv) (hAN' ha)
  -- cross commutators `[V,A]` lie in `V'`
  have hcross : ∀ v ∈ V, ∀ c ∈ A, v * c * v⁻¹ * c⁻¹ ∈ V' := by
    intro v hv c hc
    have hx1 : (⟨v⁻¹, V.inv_mem hv⟩ : ↥V)⁻¹ *
        ((⟨c, hc⟩ : ↥A) • (⟨v⁻¹, V.inv_mem hv⟩ : ↥V)) ∈ D :=
      FT.le_commutator (⟨c, hc⟩ : ↥A) (Subgroup.mem_top _)
    refine Subgroup.mem_map.mpr ⟨_, hDW hx1, ?_⟩
    rw [map_mul, map_inv, Subgroup.coe_subtype, FT.conj_smul_coe]
    group
  -- the candidate `M = V' · A` is normal in `Q`
  have hMnormal : (V' ⊔ A).Normal := by
    refine Subgroup.Normal.mk fun n hn g => ?_
    obtain ⟨n1, hn1, n2, hn2, rfl⟩ := by
      change n ∈ (↑(V' ⊔ A) : Set Q) at hn
      rw [Subgroup.normal_mul V' A] at hn
      exact Set.mem_mul.mp hn
    obtain ⟨v, hv, a, ha, rfl⟩ := by
      have hg : g ∈ V ⊔ A := hsup ▸ Subgroup.mem_top g
      change g ∈ (↑(V ⊔ A) : Set Q) at hg
      rw [Subgroup.normal_mul V A] at hg
      exact Set.mem_mul.mp hg
    have hc1 : (a * n1 * a⁻¹) ∈ V' := hV'A a ha n1 hn1
    have hc2 : (a * n2 * a⁻¹) ∈ A := A.mul_mem (A.mul_mem ha hn2) (A.inv_mem ha)
    have hconj : v * (a * n1 * a⁻¹) * v⁻¹ = (a * n1 * a⁻¹) := by
      rw [hmul_comm v hv _ (hV'leV hc1), mul_assoc, mul_inv_cancel, mul_one]
    have hsplit : (v * a) * (n1 * n2) * (v * a)⁻¹ =
        (a * n1 * a⁻¹) * (v * (a * n2 * a⁻¹) * v⁻¹) := by
      calc (v * a) * (n1 * n2) * (v * a)⁻¹
          = v * ((a * n1 * a⁻¹) * (a * n2 * a⁻¹)) * v⁻¹ := by group
        _ = (v * (a * n1 * a⁻¹) * v⁻¹) * (v * (a * n2 * a⁻¹) * v⁻¹) := by group
        _ = (a * n1 * a⁻¹) * (v * (a * n2 * a⁻¹) * v⁻¹) := by rw [hconj]
    rw [hsplit]
    have hc3 : (v * (a * n2 * a⁻¹) * v⁻¹ * (a * n2 * a⁻¹)⁻¹) ∈ V' := hcross v hv _ hc2
    rw [show v * (a * n2 * a⁻¹) * v⁻¹ =
      (v * (a * n2 * a⁻¹) * v⁻¹ * (a * n2 * a⁻¹)⁻¹) * (a * n2 * a⁻¹) from by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc1)
      (Subgroup.mul_mem _ (Subgroup.mem_sup_left hc3) (Subgroup.mem_sup_right hc2))
  -- index computation
  have hcardQ : Nat.card ↥(V ⊔ A) = Nat.card ↥V * Nat.card ↥A := by
    have h := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer (H := V) (K := A) hVA
    rw [hinf, Subgroup.card_bot, mul_one] at h
    exact h
  have hcardM : Nat.card ↥(V' ⊔ A) = Nat.card ↥V' * Nat.card ↥A := by
    have h := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer (H := V') (K := A) hAN'
    have hinf' : V' ⊓ A = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_inf] at hy
      have h1 : y ∈ V ⊓ A := Subgroup.mem_inf.mpr ⟨hV'leV hy.1, hy.2⟩
      rwa [hinf] at h1
    rw [hinf', Subgroup.card_bot, mul_one] at h
    exact h
  have hcardV : Nat.card ↥V = Nat.card ↥V' * p := by
    have h := Subgroup.card_mul_index (V'.subgroupOf V)
    rw [hV'idx] at h
    have hc : Nat.card ↥(V'.subgroupOf V) = Nat.card ↥V' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV'leV).toEquiv
    rw [hc] at h
    exact h.symm
  have hcardQ' : Nat.card Q = Nat.card ↥V * Nat.card ↥A := by
    rw [← hcardQ, hsup]
    exact (Nat.card_congr Subgroup.topEquiv.toEquiv).symm
  refine ⟨V' ⊔ A, hMnormal, ?_⟩
  have hk : Nat.card ↥(V' ⊔ A) * (V' ⊔ A).index = Nat.card Q :=
    Subgroup.card_mul_index (V' ⊔ A)
  have hkp : Nat.card ↥(V' ⊔ A) * p = Nat.card ↥(V' ⊔ A) * (V' ⊔ A).index := by
    rw [hk, hcardQ', hcardM, hcardV]
    ring
  exact (Nat.mul_left_cancel (Nat.card_pos (α := ↥(V' ⊔ A))) hkp).symm

/-- **G0** (Peterfalvi II, Ch. V §3): a fixed vector in an elementary abelian section gives a
quotient of order `p`. -/
theorem G0_hasNormalIndexP_of_fixed_elementary {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X S C N : Subgroup G} (hSX : S ≤ X) (hCX : C ≤ X) (hSC : S ⊔ C = X)
    (hSn : X ≤ Work.ThmF.ChV3.NG S) (hNn : X ≤ Work.ThmF.ChV3.NG N) (hNS : N ≤ S)
    (hS : IsPGroup p S) (hC : ¬ p ∣ Nat.card C)
    (hab : ∀ a ∈ S, ∀ b ∈ S, a * b * a⁻¹ * b⁻¹ ∈ N) (hpow : ∀ a ∈ S, a ^ p ∈ N)
    {x : G} (hxS : x ∈ S) (hxN : x ∉ N)
    (hfix : ∀ y ∈ C, y * x * y⁻¹ * x⁻¹ ∈ N) :
    Work.ThmF.HasNormalIndexP p ↥X := by
  classical
  have hNX : N ≤ X := hNS.trans hSX
  have hNn' : (N.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr hNn
  have hSn' : (S.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSX).mpr hSn
  haveI := hNn'
  set V : Subgroup (↥X ⧸ (N.subgroupOf X)) :=
    (S.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X)) with hV
  set A : Subgroup (↥X ⧸ (N.subgroupOf X)) :=
    (C.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X)) with hA
  -- `V` is normal in the quotient
  have hVn : V.Normal := by
    rw [hV]
    exact Subgroup.Normal.map hSn' (QuotientGroup.mk' (N.subgroupOf X))
      (QuotientGroup.mk'_surjective _)
  -- `V` is commutative
  have hVcomm : ∀ a b : ↥V, a * b = b * a := by
    intro a b
    obtain ⟨u, hu, hua⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨v, hv, hvb⟩ := Subgroup.mem_map.mp b.2
    have huS : (u : G) ∈ S := Subgroup.mem_subgroupOf.mp hu
    have hvS : (v : G) ∈ S := Subgroup.mem_subgroupOf.mp hv
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hua, ← hvb]
    have hmem : (u * v) * (v * u)⁻¹ ∈ N.subgroupOf X := by
      rw [Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      convert hab (u : G) huS (v : G) hvS using 1
      group
    have h3 : (QuotientGroup.mk' (N.subgroupOf X)) (u * v) =
        (QuotientGroup.mk' (N.subgroupOf X)) (v * u) := by
      have h1 : ((u * v) * (v * u)⁻¹ : ↥X ⧸ (N.subgroupOf X)) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hmem
      have h2 : (QuotientGroup.mk' (N.subgroupOf X)) ((u * v) * (v * u)⁻¹) = 1 := by
        rwa [QuotientGroup.mk'_apply]
      have h4 : (QuotientGroup.mk' (N.subgroupOf X)) (u * v) *
          ((QuotientGroup.mk' (N.subgroupOf X)) (v * u))⁻¹ = 1 := by
        rw [← map_inv, ← map_mul]; exact h2
      exact mul_inv_eq_one.mp h4
    simpa only [map_mul] using h3
  haveI : IsMulCommutative ↥V := ⟨⟨hVcomm⟩⟩
  -- `V` has exponent `p`
  have hVe : ∀ v : ↥V, v ^ p = 1 := by
    intro v
    obtain ⟨s, hs, hsv⟩ := Subgroup.mem_map.mp v.2
    have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
    have hmem : s ^ p ∈ N.subgroupOf X := by
      rw [Subgroup.mem_subgroupOf]
      exact hpow (s : G) hsS
    have h1 : (QuotientGroup.mk' (N.subgroupOf X)) (s ^ p) = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff (s ^ p)).mpr hmem
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hsv, ← map_pow]
    exact h1
  -- `V ⊔ A = ⊤`
  have hsup : V ⊔ A = ⊤ := by
    rw [hV, hA, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hSX hCX, hSC,
      Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  -- `¬ p ∣ |A|`
  have hAp : ¬ p ∣ Nat.card A := by
    intro h
    apply hC
    have h1 : Nat.card A ∣ Nat.card (C.subgroupOf X) :=
      Subgroup.card_map_dvd (H := C.subgroupOf X) (QuotientGroup.mk' (N.subgroupOf X))
    have h2 : Nat.card (C.subgroupOf X) = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCX).toEquiv
    rw [h2] at h1
    exact h.trans h1
  -- `V ⊓ A = ⊥` (coprime orders)
  have hVpg : IsPGroup p V := IsPGroup.map hS.comap_subtype (QuotientGroup.mk' (N.subgroupOf X))
  have hinf : V ⊓ A = ⊥ := by
    rw [← disjoint_iff]
    exact IsPGroup.disjoint_of_coprime hVpg IsPGroup.card (hp.coprime_iff_not_dvd.mpr hAp)
  -- the fixed element
  set xq : ↥X ⧸ (N.subgroupOf X) :=
    (QuotientGroup.mk' (N.subgroupOf X)) ⟨x, hSX hxS⟩ with hxq
  have hxqV : xq ∈ V := by
    rw [hV, hxq]
    exact Subgroup.mem_map.mpr ⟨⟨x, hSX hxS⟩, Subgroup.mem_subgroupOf.mpr hxS, rfl⟩
  have hxqne : xq ≠ 1 := by
    intro h
    rw [hxq, QuotientGroup.mk'_apply] at h
    exact hxN (Subgroup.mem_subgroupOf.mp
      ((QuotientGroup.eq_one_iff (⟨x, hSX hxS⟩ : ↥X)).mp h))
  have hxqfix : ∀ a ∈ A, a * xq * a⁻¹ = xq := by
    intro a ha
    obtain ⟨c, hc, hca⟩ := Subgroup.mem_map.mp ha
    have hcC : (c : G) ∈ C := Subgroup.mem_subgroupOf.mp hc
    rw [← hca, hxq]
    have hmem : (c * ⟨x, hSX hxS⟩ * c⁻¹) * (⟨x, hSX hxS⟩)⁻¹ ∈ N.subgroupOf X := by
      rw [Subgroup.mem_subgroupOf]
      simpa using hfix (c : G) hcC
    have h2 : (QuotientGroup.mk' (N.subgroupOf X)) (c * ⟨x, hSX hxS⟩ * c⁻¹) *
        ((QuotientGroup.mk' (N.subgroupOf X)) ⟨x, hSX hxS⟩)⁻¹ = 1 := by
      rw [← map_inv, ← map_mul]
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff _).mpr hmem
    have h3 := mul_inv_eq_one.mp h2
    simpa only [map_mul, map_inv] using h3
  obtain ⟨M, hMn, hMidx⟩ := exists_normal_index_prime_of_coprime_fixed
    (Q := ↥X ⧸ (N.subgroupOf X)) hp hVn hVe hAp hsup hinf hxqV hxqfix hxqne
  exact ⟨M.comap (QuotientGroup.mk' (N.subgroupOf X)), Subgroup.Normal.comap hMn _, by
    rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _), hMidx]⟩

end Work.ThmF.ChV3.Prove
