/-
# Area BG: the sum of a class function over the involutions of `H ∖ H₀`

This file proves `Work.BG.invJ_sum_conjClasses`: for Bender–Glauberman data `D`, a compatible
§2 context `C`, and a class function `ψ` on `H = C.P.H`,

`∑_{x ∈ J} ψ x = |t₁^H| ψ(t₁) + |t₂^H| ψ(t₂)`,

where `J = invJ C` is the set of involutions of `H` outside `H₀ = H₁ D`, `t₁, t₂` are the two
`H`-class representatives of `D` (with `tᵢ` an element of `↥C.P.H` mapping to `D.tᵢ` in `G`),
and `|tᵢ^H| = |H : C_H(tᵢ)| = (C_G(tᵢ)).relIndex D.H`.

The content is the class decomposition `J = t₁^H ⊔ t₂^H` of Bender–Glauberman 1981, Lemma 2.2
(`J` is exactly the set of involutions of `H ∖ H₀`, and these form the two classes `t₁^H`, `t₂^H`),
combined with the two easiest facts about it:

* a class function is constant on a conjugacy class, so a sum over a class is
  `(class size) · ψ(representative)` (`classFun_sum_conjClassF`);
* the class size is the index of the centralizer (`Work.BG.card_conjClassF_subtype`, and the
  already-proven `Work.BG.invJCard` which gives `|J| = k₁ + k₂`).

The class decomposition itself (`mem_invJ_iff_isConj'`) is proved here by a Sylow argument that
avoids the explicit `H = U·S` decomposition of `invJCard`: since `S = D.S` is a Sylow
`2`-subgroup of `G` contained in `H = C_G(t)`, it is also a Sylow `2`-subgroup of `H`; any
involution `x ∈ H` therefore lies in a conjugate `g S g⁻¹` of `S` inside `H`
(`IsPGroup.exists_le_sylow` + Sylow conjugacy), so `g⁻¹ x g ∈ S`; this element is outside `S₀`
(otherwise it would be the unique involution `t ∈ S₀` of the cyclic group `S₀ = ⟨t₁t₂⟩`,
by `Work.BG.eqOfMemZpowersOfSqEqOne`, whence `x = t ∈ H₀`), and
`Work.BG.invS_conj_t1_or_t2` conjugates it to `t₁` or `t₂` inside `S ≤ H`. Conversely every
`H`-conjugate of `tᵢ` is an involution outside the normal subgroup `H₀ ⊴ H`.
-/
import Mathlib
import Submission.Work.BG.invJCard
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.card_conjClassF_subtype

open scoped Pointwise

namespace Work.BG

/-! ## 1. Sums of a class function over a pointwise constant finset -/

/-- A finset whose elements all have the same `ψ`-value: the sum is the cardinality times that
value. -/
lemma sum_eq_card_mul_of_forall {K : Type} (s : Finset K) (ψ : K → ℂ) (c : K)
    (h : ∀ x ∈ s, ψ x = ψ c) : ∑ x ∈ s, ψ x = (s.card : ℂ) * ψ c := by
  rw [show s.sum ψ = s.card • ψ c from by
    rw [Finset.sum_congr rfl h, Finset.sum_const]]
  simp [nsmul_eq_mul]

/-- **A class function is constant on a conjugacy class.** The sum of a conjugation invariant
function `ψ` over the class of `c` is `|c^K| · ψ(c)`. -/
lemma classFun_sum_conjClassF {K : Type} [Group K] [Fintype K]
    (ψ : K → ℂ) (hψ : ∀ g x : K, ψ (g * x * g⁻¹) = ψ x) (c : K) :
    ∑ x ∈ conjClassF K c, ψ x = ((conjClassF K c).card : ℂ) * ψ c := by
  refine sum_eq_card_mul_of_forall _ ψ c ?_
  intro x hx
  obtain ⟨g, hg⟩ := isConj_iff.mp ((mem_conjClassF c x).mp hx)
  exact (hg ▸ hψ g x).symm

/-! ## 2. `invJ C` is the union of the two classes `t₁^H`, `t₂^H` -/

/-- **The involutions of `H ∖ H₀` are exactly the `H`-conjugates of `t₁` and `t₂`.** -/
theorem mem_invJ_iff_isConj' {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Fintype ↥C.P.H]
    (hC : Work.GW2.C16.Compat D C)
    (t1 t2 : ↥C.P.H) (ht1 : (t1 : G) = D.t1) (ht2 : (t2 : G) = D.t2)
    (x : ↥C.P.H) :
    x ∈ Work.GW2.C16.invJ C ↔ IsConj x t1 ∨ IsConj x t2 := by
  classical
  have hH : C.P.H = D.H := hC.H_eq
  have hH0 : C.P.H0 = H1 D := hC.H0_eq
  have hS_le : (D.S : Subgroup G) ≤ C.P.H := by rw [hH]; exact S_le_H D
  have ht1H0 : (t1 : G) ∉ C.P.H0 := by rw [hH0, ht1]; exact t1_notMem_H1 D
  have ht2H0 : (t2 : G) ∉ C.P.H0 := by rw [hH0, ht2]; exact t2_notMem_H1 D
  have hconj : ∀ (c y : ↥C.P.H), y ∈ Work.GW2.C16.invJ C → c * y * c⁻¹ ∈ Work.GW2.C16.invJ C := by
    intro c y hy
    rw [Work.BG.mem_invJ] at hy ⊢
    obtain ⟨hy2, hy1, hyH0⟩ := hy
    refine ⟨?_, ?_, ?_⟩
    · rw [show (c * y * c⁻¹) ^ 2 = c * y ^ 2 * c⁻¹ from by rw [pow_two, pow_two]; group, hy2]
      group
    · intro h
      apply hy1
      have h2 : c⁻¹ * (c * y * c⁻¹) * c = y := by group
      rw [← h2, h]; group
    · intro hmem
      apply hyH0
      have hm' : (c * y * c⁻¹ : ↥C.P.H) ∈ (C.P.H0).subgroupOf C.P.H := by
        rw [Subgroup.mem_subgroupOf]; exact hmem
      have h3 := C.P.H0_normal.conj_mem' _ hm' c
      have h4 : (y : ↥C.P.H) = c⁻¹ * (c * y * c⁻¹) * c := by group
      rw [← h4] at h3
      exact Subgroup.mem_subgroupOf.mp h3
  constructor
  · intro hx
    rw [Work.BG.mem_invJ] at hx
    obtain ⟨hx2, hx1, hxH0⟩ := hx
    -- `x` lies in a conjugate of the Sylow `2`-subgroup `S` of `H`
    obtain ⟨g, hgy⟩ : ∃ g : ↥C.P.H,
        (g⁻¹ * x * g : ↥C.P.H) ∈ ((D.S).subtype hS_le : Subgroup ↥C.P.H) := by
      have hzp : IsPGroup 2 ↥(Subgroup.zpowers x) := by
        have hxord : orderOf x = 2 := (orderOf_eq_prime_iff (p := 2)).mpr ⟨hx2, hx1⟩
        refine IsPGroup.of_card (n := 1) ?_
        rw [Nat.card_zpowers, hxord]; norm_num
      obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (p := 2) (P := Subgroup.zpowers x) hzp
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥C.P.H) ((D.S).subtype hS_le) Q
      refine ⟨g, ?_⟩
      have hxQ : x ∈ ((Q : Sylow 2 ↥C.P.H) : Subgroup ↥C.P.H) := hQ (Subgroup.mem_zpowers x)
      rw [← hg] at hxQ
      exact (show x ∈ ((g • (D.S).subtype hS_le : Sylow 2 ↥C.P.H) : Subgroup ↥C.P.H) ↔
          g⁻¹ * x * g ∈ (((D.S).subtype hS_le) : Subgroup ↥C.P.H) from by
        rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
        show (MulAut.conj g)⁻¹ x ∈ (((D.S).subtype hS_le) : Subgroup ↥C.P.H) ↔
            g⁻¹ * x * g ∈ (((D.S).subtype hS_le) : Subgroup ↥C.P.H)
        rw [MulAut.conj_inv_apply]).mp hxQ
    have hyS : (((g⁻¹ * x * g : ↥C.P.H)) : G) ∈ (D.S : Subgroup G) := by
      rw [Sylow.coe_subtype] at hgy
      exact Subgroup.mem_subgroupOf.mp hgy
    -- and it cannot lie in `S₀`, whose only involution is `t`
    have hyS0 : (((g⁻¹ * x * g : ↥C.P.H)) : G) ∉ D.S0 := by
      intro hmem
      have hy2 : (g⁻¹ * x * g : ↥C.P.H) ^ 2 = 1 := by
        rw [show (g⁻¹ * x * g) ^ 2 = g⁻¹ * x ^ 2 * g from by rw [pow_two, pow_two]; group, hx2]
        group
      have hyG2 : (((g⁻¹ * x * g : ↥C.P.H)) : G) ^ 2 = 1 := by
        simpa [Subgroup.coe_pow] using congrArg (fun z : ↥C.P.H => (z : G)) hy2
      have hy1 : (g⁻¹ * x * g : ↥C.P.H) ≠ 1 := by
        intro h
        apply hx1
        have h3 := congrArg (fun z : ↥C.P.H => g * z * g⁻¹) h
        simpa [mul_assoc] using h3
      have hyG1 : (((g⁻¹ * x * g : ↥C.P.H)) : G) ≠ 1 := by
        intro h
        exact hy1 (Subtype.ext (by simpa using h))
      have hyzp : (((g⁻¹ * x * g : ↥C.P.H)) : G) ∈ Subgroup.zpowers (D.t1 * D.t2) := by
        rw [← D.gen]; exact hmem
      have htzp : D.t ∈ Subgroup.zpowers (D.t1 * D.t2) := by rw [← D.gen]; exact D.t_mem
      have htG2 : D.t ^ 2 = 1 := ((orderOf_eq_prime_iff (p := 2)).mp D.t_order).1
      have htG1 : D.t ≠ 1 := ((orderOf_eq_prime_iff (p := 2)).mp D.t_order).2
      have heq : (((g⁻¹ * x * g : ↥C.P.H)) : G) = D.t :=
        eqOfMemZpowersOfSqEqOne hyzp htzp hyG2 htG2 hyG1 htG1
      apply hxH0
      have hxG : (x : G) = D.t := by
        have h1 : x = g * (g⁻¹ * x * g : ↥C.P.H) * g⁻¹ := by group
        have h2 : (x : G) = (g : G) * (((g⁻¹ * x * g : ↥C.P.H)) : G) * ((g : G))⁻¹ := by
          rw [h1]; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
        rw [h2, heq, ← hC.t_eq, C.t_comm_H (g : G) g.2]
        group
      rw [hxG, ← hC.t_eq]
      exact C.t.2
    rcases invS_conj_t1_or_t2 D hyS hyS0 with ⟨c, hcS, hc⟩ | ⟨c, hcS, hc⟩
    · left
      refine isConj_iff.mpr ⟨⟨c * (g : G)⁻¹, ?_⟩, ?_⟩
      · exact C.P.H.mul_mem (by rw [hH]; exact S_le_H D hcS) (C.P.H.inv_mem g.2)
      · apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        have hxG : (x : G) = (g : G) * (((g⁻¹ * x * g : ↥C.P.H)) : G) * ((g : G))⁻¹ := by
          have h1 : x = g * (g⁻¹ * x * g : ↥C.P.H) * g⁻¹ := by group
          rw [h1]; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
        rw [hxG, ht1, ← hc]
        group
    · right
      refine isConj_iff.mpr ⟨⟨c * (g : G)⁻¹, ?_⟩, ?_⟩
      · exact C.P.H.mul_mem (by rw [hH]; exact S_le_H D hcS) (C.P.H.inv_mem g.2)
      · apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        have hxG : (x : G) = (g : G) * (((g⁻¹ * x * g : ↥C.P.H)) : G) * ((g : G))⁻¹ := by
          have h1 : x = g * (g⁻¹ * x * g : ↥C.P.H) * g⁻¹ := by group
          rw [h1]; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
        rw [hxG, ht2, ← hc]
        group
  · rintro (hconj1 | hconj2)
    · obtain ⟨c, hc⟩ := isConj_iff.mp hconj1
      have hxeq : x = c⁻¹ * t1 * c := by rw [← hc]; group
      rw [Work.BG.mem_invJ]
      refine ⟨?_, ?_, ?_⟩
      · rw [hxeq, show (c⁻¹ * t1 * c) ^ 2 = c⁻¹ * t1 ^ 2 * c from by rw [pow_two, pow_two]; group,
          show t1 ^ 2 = 1 from by
            apply Subtype.ext; simpa [Subgroup.coe_pow, ht1] using t1_sq D]
        group
      · intro h
        apply t1_ne_one D
        rw [← ht1]
        have hh : (t1 : G) = ((c * x * c⁻¹ : ↥C.P.H) : G) := by rw [hc]
        rw [hh, h]; simp
      · intro hmem
        apply ht1H0
        have hxmem' : (x : ↥C.P.H) ∈ (C.P.H0).subgroupOf C.P.H := by
          rw [Subgroup.mem_subgroupOf]; exact hmem
        have hmem2 := C.P.H0_normal.conj_mem _ hxmem' c
        have h2 : ((c * x * c⁻¹ : ↥C.P.H) : G) ∈ C.P.H0 := Subgroup.mem_subgroupOf.mp hmem2
        rwa [hc] at h2
    · obtain ⟨c, hc⟩ := isConj_iff.mp hconj2
      have hxeq : x = c⁻¹ * t2 * c := by rw [← hc]; group
      rw [Work.BG.mem_invJ]
      refine ⟨?_, ?_, ?_⟩
      · rw [hxeq, show (c⁻¹ * t2 * c) ^ 2 = c⁻¹ * t2 ^ 2 * c from by rw [pow_two, pow_two]; group,
          show t2 ^ 2 = 1 from by
            apply Subtype.ext; simpa [Subgroup.coe_pow, ht2] using t2_sq D]
        group
      · intro h
        apply t2_ne_one D
        rw [← ht2]
        have hh : (t2 : G) = ((c * x * c⁻¹ : ↥C.P.H) : G) := by rw [hc]
        rw [hh, h]; simp
      · intro hmem
        apply ht2H0
        have hxmem' : (x : ↥C.P.H) ∈ (C.P.H0).subgroupOf C.P.H := by
          rw [Subgroup.mem_subgroupOf]; exact hmem
        have hmem2 := C.P.H0_normal.conj_mem _ hxmem' c
        have h2 : ((c * x * c⁻¹ : ↥C.P.H) : G) ∈ C.P.H0 := Subgroup.mem_subgroupOf.mp hmem2
        rwa [hc] at h2

/-! ## 3. The sum over `invJ C` -/

theorem invJ_sum_conjClasses {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Fintype ↥C.P.H]
    (hC : Work.GW2.C16.Compat D C)
    (t1 t2 : ↥C.P.H) (ht1 : (t1 : G) = D.t1) (ht2 : (t2 : G) = D.t2)
    (ψ : ↥C.P.H → ℂ) (hψ : ∀ g x : ↥C.P.H, ψ (g * x * g⁻¹) = ψ x) :
    ∑ x ∈ Work.GW2.C16.invJ C, ψ x =
      ((Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H : ℂ) * ψ t1 +
      ((Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H : ℂ) * ψ t2 := by
  classical
  have hH : C.P.H = D.H := hC.H_eq
  -- the class decomposition `J = t₁^H ∪ t₂^H`
  have hUnion : Work.GW2.C16.invJ C =
      Work.BG.conjClassF (↥C.P.H) t1 ∪ Work.BG.conjClassF (↥C.P.H) t2 := by
    ext x
    rw [Finset.mem_union, Work.BG.mem_conjClassF, Work.BG.mem_conjClassF]
    exact mem_invJ_iff_isConj' D C hC t1 t2 ht1 ht2 x
  -- `|J| = k₁ + k₂` (Bender–Glauberman's `|J| = k`, `Work.BG.invJCard`)
  have hJcard : (Work.GW2.C16.invJ C).card =
      (Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H +
      (Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H := by
    have h := Work.BG.invJCard D C hC
    simpa only [Work.GW2.BGData.k] using h
  -- the two classes have `k₁`, `k₂` elements
  have hA : (Work.BG.conjClassF (↥C.P.H) t1).card =
      (Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H := by
    have hx : D.t1 ∈ C.P.H := by rw [hH]; exact S_le_H D D.t1_mem
    have h1 : (⟨D.t1, hx⟩ : ↥C.P.H) = t1 := Subtype.ext (by rw [ht1])
    rw [← h1, Work.BG.card_conjClassF_subtype (H := C.P.H) D.t1 hx, hH]
  have hB : (Work.BG.conjClassF (↥C.P.H) t2).card =
      (Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H := by
    have hx : D.t2 ∈ C.P.H := by rw [hH]; exact S_le_H D D.t2_mem
    have h2 : (⟨D.t2, hx⟩ : ↥C.P.H) = t2 := Subtype.ext (by rw [ht2])
    rw [← h2, Work.BG.card_conjClassF_subtype (H := C.P.H) D.t2 hx, hH]
  -- hence the two classes are disjoint (compare cardinalities with `|J| = k₁ + k₂`)
  have hdisj : Disjoint (Work.BG.conjClassF (↥C.P.H) t1) (Work.BG.conjClassF (↥C.P.H) t2) := by
    have h := Finset.card_union_add_card_inter (Work.BG.conjClassF (↥C.P.H) t1)
      (Work.BG.conjClassF (↥C.P.H) t2)
    rw [← hUnion, hJcard, hA, hB] at h
    have hint : (Work.BG.conjClassF (↥C.P.H) t1 ∩ Work.BG.conjClassF (↥C.P.H) t2).card = 0 := by
      omega
    exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hint)
  rw [hUnion, Finset.sum_union hdisj, classFun_sum_conjClassF ψ hψ t1,
    classFun_sum_conjClassF ψ hψ t2, hA, hB]

end Work.BG
