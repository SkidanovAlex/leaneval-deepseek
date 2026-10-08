import Mathlib
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.P3Sub.Helpers
import Submission.Work.ThreePoints.P3Sub.App2Seven
import Submission.Work.ThreePoints.P3Sub.prop1a_fixes_three
import Submission.Work.ThreePoints.P3Sub.p3F_subgroupOf_normalizer_normal
import Submission.Work.ThreePoints.P3Sub.twoTransitive_of_regular
import Submission.Work.ThreePoints.involutions_conj_of_stronglyEmbedded
import Submission.Work.DoubleTransitivity.App1.app1_1b

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.GroupTheory.Defs
open scoped Pointwise

namespace Work.ThreePoints.P3Sub

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-! ## 1. Appendix I (1): `D ⊓ N_G(X) ≤ F ⊔ (V ⊓ N_G(X))`, and `N_G(X) ≤ N_G(O^{2'}(C_G(X)))` -/

theorem normalizer_le_normalizer_p3F (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer ((p3F X : Subgroup G) : Set G) := by
  haveI := p3F_subgroupOf_normalizer_normal X
  exact Subgroup.le_normalizer_of_normal_subgroupOf (p3F_le_normalizer X)

/-- If `g` normalises both `A` and `B`, then it normalises `A ⊓ B`. -/
theorem mem_normalizer_inf_of {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact ⟨fun h => ⟨(hA x).mp h.1, (hB x).mp h.2⟩,
    fun h => ⟨(hA x).mpr h.1, (hB x).mpr h.2⟩⟩

/-- `t` normalises the two-point stabiliser `twoPoint H t`. -/
theorem mem_normalizer_twoPoint' {H : Subgroup G} {t : G} (ht : orderOf t = 2) :
    t ∈ Subgroup.normalizer ((twoPoint H t : Subgroup G) : Set G) := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  show Submission.Blueprint.conj t (twoPoint H t) = twoPoint H t
  have h1 : Submission.Blueprint.conj t (twoPoint H t) = conj t H ⊓ H := by
    rw [twoPoint_eq, Work.ThreePoints.conj_inf, ← Work.ThreePoints.conj_mul, ht2,
      Work.ThreePoints.conj_one]
  rw [h1, twoPoint_eq]
  exact inf_comm _ _

/-- Peterfalvi I, Appendix I (1)(b): every element of `D ⊓ N_G(X)` is a product of an element of
`V ⊓ N_G(X)` and an element of `K ∩ N_G(X)`. -/
theorem twoPoint_inf_normalizer_le_sup_centD {H X : Subgroup G} {t : G}
    (hH : IsStronglyEmbedded H)
    (ht : orderOf t = 2) (htH : t ∉ H) (hX : X ≤ centD H t)
    (hNK : (invertedBy (twoPoint H t) t ∩
        (Subgroup.normalizer (X : Set G) : Set G)) ⊆ (p3F X : Set G)) :
    (twoPoint H t ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) ≤
      p3F X ⊔ (centD H t ⊓ Subgroup.normalizer (X : Set G)) := by
  classical
  let D : Subgroup G := twoPoint H t
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  let V : Subgroup G := centD H t
  let M : Subgroup G := D ⊓ N
  let F : Subgroup G := p3F X
  let CV : Subgroup G := V ⊓ N
  change M ≤ F ⊔ CV
  intro m hm
  have htC : t ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (mem_centD.mp (hX hx)).2.2
  have htN : t ∈ N := Subgroup.centralizer_le_normalizer (X : Set G) htC
  have htD : t ∈ Subgroup.normalizer (D : Set G) := mem_normalizer_twoPoint' ht
  have htM : t ∈ Subgroup.normalizer (M : Set G) :=
    mem_normalizer_inf_of htD (Subgroup.le_normalizer htN)
  have hoddD : Odd (Nat.card ↥D) := hH.2.2 t htH
  have hMD : M ≤ D := inf_le_left
  have hoddM : Odd (Nat.card ↥M) :=
    Odd.of_dvd_nat hoddD (Subgroup.card_dvd_of_le hMD)
  obtain ⟨p, hp⟩ :=
    (Work.DoubleTransitivity.App1.phiMap_bijective (X := M) (t := t) ht hoddM htM).2 ⟨m, hm⟩
  have hm_eq : (p.1 : G) * (p.2 : G) ^ Work.DoubleTransitivity.App1.expo M = m := by
    have h1 := congrArg (fun z : ↥M => (z : G)) hp
    simpa [Work.DoubleTransitivity.App1.phiMap_apply] using h1
  have hvm : (p.1 : G) ∈ CV := by
    have h1 : (p.1 : G) ∈ Work.DoubleTransitivity.centralizerIn M t := p.1.2
    have h1M : (p.1 : G) ∈ M := (Subgroup.mem_inf.mp h1).1
    have h1c : (p.1 : G) ∈ Subgroup.centralizer ({t} : Set G) := (Subgroup.mem_inf.mp h1).2
    have h1D : (p.1 : G) ∈ D := (Subgroup.mem_inf.mp h1M).1
    have h1N : (p.1 : G) ∈ N := (Subgroup.mem_inf.mp h1M).2
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨h1D, h1c⟩, h1N⟩
  have hyF : (p.2 : G) ∈ F := by
    have h2 : (p.2 : G) ∈ invertedBy M t := p.2.2
    have h2M : (p.2 : G) ∈ M := h2.1
    have h2D : (p.2 : G) ∈ invertedBy (twoPoint H t) t :=
      ⟨(Subgroup.mem_inf.mp h2M).1, h2.2⟩
    have h2N : (p.2 : G) ∈ N := (Subgroup.mem_inf.mp h2M).2
    exact hNK ⟨h2D, h2N⟩
  have hpow : (p.2 : G) ^ Work.DoubleTransitivity.App1.expo M ∈ F :=
    Subgroup.pow_mem F hyF _
  have hsum : (p.1 : G) * (p.2 : G) ^ Work.DoubleTransitivity.App1.expo M ∈ F ⊔ CV :=
    Subgroup.mul_mem (F ⊔ CV) (Subgroup.mem_sup_right hvm) (Subgroup.mem_sup_left hpow)
  rwa [hm_eq] at hsum

theorem sup_twoPoint_eq_sup_centD {H X : Subgroup G} {t : G} (hH : IsStronglyEmbedded H)
    (ht : orderOf t = 2) (htH : t ∉ H) (hX : X ≤ centD H t)
    (hNK : (invertedBy (twoPoint H t) t ∩
        (Subgroup.normalizer (X : Set G) : Set G)) ⊆ (p3F X : Set G)) :
    p3F X ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) =
      p3F X ⊔ (centD H t ⊓ Subgroup.normalizer (X : Set G)) := by
  refine le_antisymm ?_ ?_
  · exact sup_le le_sup_left (twoPoint_inf_normalizer_le_sup_centD hH ht htH hX hNK)
  · refine sup_le le_sup_left ?_
    exact le_sup_of_le_right (le_inf (inf_le_left.trans inf_le_left) inf_le_right)

/-! ## 2. Elementary lemmas (copied from `chIIFourP3Subnormal`, which cannot be imported:
    it imports this module) -/

/-- The points `H` and `H^t` of `Ω = G ⧸ H` are distinct when `t ∉ H`. -/
theorem mk_one_ne_mk_t {H : Subgroup G} {t : G} (htH : t ∉ H) :
    (QuotientGroup.mk (1 : G) : G ⧸ H) ≠ QuotientGroup.mk t := by
  intro hcon
  rw [QuotientGroup.eq] at hcon
  exact htH (by simpa using hcon)

/-- The stabiliser of the point `H` of `Ω`. -/
theorem stabilizer_pt (H : Subgroup G) :
    MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) = H := by
  rw [stabilizer_mk H 1, conj_one]

/-- `N_G(X)` preserves the set of fixed points `Ω_X`. -/
theorem smul_mem_fixedPts_of_mem_normalizer {H X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) {ω : G ⧸ H}
    (hω : ω ∈ fixedPts H X) : g • ω ∈ fixedPts H X := by
  rw [mem_fixedPts] at hω ⊢
  intro x hx
  have hxh : g⁻¹ * x * g ∈ X := by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
  calc x • (g • ω) = (x * g) • ω := by rw [mul_smul]
    _ = (g * (g⁻¹ * x * g)) • ω := by rw [show x * g = g * (g⁻¹ * x * g) from by group]
    _ = g • ((g⁻¹ * x * g) • ω) := by rw [mul_smul]
    _ = g • ω := by rw [hω _ hxh]

/-- Monotonicity of `2`-transitivity in the acting subgroup. -/
theorem twoTransitive_mono {E : Type} [MulAction G E] {A B : Subgroup G} {S : Set E}
    (h : Work.DoubleTransitivity.IsTwoTransitiveOnSub A S) (hAB : A ≤ B) :
    Work.DoubleTransitivity.IsTwoTransitiveOnSub B S :=
  fun c hc d hd hcd c' hc' d' hd' hcd' =>
    let ⟨g, hg, h1, h2⟩ := h c hc d hd hcd c' hc' d' hd' hcd'
    ⟨g, hAB hg, h1, h2⟩

/-- Prop. 3 (a), first step: `2`-transitivity of `F` forces `N_G(X) = F · N_D(X)`. -/
theorem normalizer_eq_sup_twoPoint {H X : Subgroup G} {t : G} (htH : t ∉ H)
    (hX : X ≤ centD H t)
    (h2t : Work.DoubleTransitivity.IsTwoTransitiveOnSub (p3F X) (fixedPts H X)) :
    Subgroup.normalizer (X : Set G) =
      p3F X ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) := by
  refine le_antisymm ?_ (sup_le (p3F_le_normalizer X) inf_le_right)
  intro g hg
  have ha : (QuotientGroup.mk (1 : G) : G ⧸ H) ∈ fixedPts H X :=
    pt_mem_fixedPts_of_le_centD hX
  have hb : (QuotientGroup.mk t : G ⧸ H) ∈ fixedPts H X :=
    mk_t_mem_fixedPts_of_le_centD hX
  have hga := smul_mem_fixedPts_of_mem_normalizer hg ha
  have hgb := smul_mem_fixedPts_of_mem_normalizer hg hb
  have hne : g • (QuotientGroup.mk (1 : G) : G ⧸ H) ≠ g • (QuotientGroup.mk t : G ⧸ H) := by
    intro hcon
    exact mk_one_ne_mk_t htH (smul_left_cancel g hcon)
  obtain ⟨f, hf, hf1, hf2⟩ :=
    h2t _ hga _ hgb hne _ ha _ hb (mk_one_ne_mk_t htH)
  have hfg1 : f * g ∈ MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) := by
    rw [MulAction.mem_stabilizer_iff, mul_smul]
    exact hf1
  have hfg2 : f * g ∈ MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ H) := by
    rw [MulAction.mem_stabilizer_iff, mul_smul]
    exact hf2
  have hfgH : f * g ∈ H := by
    rw [stabilizer_pt] at hfg1
    exact hfg1
  have hfgD : f * g ∈ twoPoint H t := by
    rw [twoPoint_eq, Subgroup.mem_inf]
    exact ⟨hfgH, by rwa [stabilizer_mk] at hfg2⟩
  have hfgN : f * g ∈ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normalizer (X : Set G)).mul_mem (p3F_le_normalizer X hf) hg
  have hg_eq : g = f⁻¹ * (f * g) := by group
  rw [hg_eq]
  exact (p3F X ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G))).mul_mem
    ((p3F X ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G))).inv_mem
      (Subgroup.mem_sup_left hf))
    (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hfgD, hfgN⟩))

/-- Peterfalvi I Ch. II §4, Lemma 1 (the inclusion used below). -/
theorem nk_le_closure {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX : X ≤ centD H t)
    (hev : Even (Nat.card (Subgroup.normalizer (X : Set G) ⊓ H : Subgroup G))) :
    (invertedBy (twoPoint H t) t ∩ (Subgroup.normalizer (X : Set G) : Set G)) ⊆
      (Subgroup.closure (involutions (Subgroup.centralizer (X : Set G) : Set G)) : Set G) := by
  intro k hk
  obtain ⟨hkK, hkN⟩ := hk
  have hkH : k ∈ H := (mem_twoPoint.mp hkK.1).1
  have hkinv : t * k * t⁻¹ = k⁻¹ := hkK.2
  have htC : t ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (p3sub_centralizer_of_le_centD hX hx)
  have htN : t ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.centralizer_le_normalizer _ htC
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htkN : t * k ∈ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normalizer (X : Set G)).mul_mem htN hkN
  have htk2 : (t * k) * (t * k) = 1 := by
    have h1 : t * k * t = k⁻¹ := by simpa [htinv] using hkinv
    calc (t * k) * (t * k) = ((t * k) * t) * k := by group
      _ = k⁻¹ * k := by rw [h1]
      _ = 1 := inv_mul_cancel k
  have htk_ne : t * k ≠ 1 := by
    intro hcon
    apply htH
    have h1 : t = k⁻¹ := by
      have h2 : t * k * k⁻¹ = k⁻¹ := by rw [hcon, one_mul]
      simpa using h2
    rw [h1]
    exact H.inv_mem hkH
  have htk2' : orderOf (t * k) = 2 := by
    have hdvd : orderOf (t * k) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact htk2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) htk_ne
    · exact h1
  have hSE : IsStronglyEmbedded
      ((Subgroup.normalizer (X : Set G) ⊓ H).subgroupOf (Subgroup.normalizer (X : Set G))) := by
    refine IsStronglyEmbedded.subgroupOf_inf hH ?_ hev
    intro hcon
    rw [Subgroup.subgroupOf_eq_top] at hcon
    exact htH (Subgroup.mem_inf.mp (hcon htN)).2
  have hconj : IsConj (⟨t, htN⟩ : ↥(Subgroup.normalizer (X : Set G)))
      (⟨t * k, htkN⟩ : ↥(Subgroup.normalizer (X : Set G))) := by
    refine involutions_conj_of_stronglyEmbedded hSE ?_ ?_
    · have hco : orderOf (⟨t, htN⟩ : ↥(Subgroup.normalizer (X : Set G))) = orderOf t :=
        (Subgroup.orderOf_coe ⟨t, htN⟩).symm
      rw [hco, ht]
    · have hco : orderOf (⟨t * k, htkN⟩ : ↥(Subgroup.normalizer (X : Set G))) =
          orderOf (t * k) :=
        (Subgroup.orderOf_coe ⟨t * k, htkN⟩).symm
      rw [hco, htk2']
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have htkC : t * k ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hcval : (c : G) * t * (c : G)⁻¹ = t * k := congrArg Subtype.val hc
    have hcN : (c : G) ∈ Subgroup.normalizer (X : Set G) := c.2
    have hcinv : (c : G)⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
      (Subgroup.normalizer (X : Set G)).inv_mem hcN
    have hxc : (c : G)⁻¹ * x * (c : G) ∈ X := by
      simpa using ((Subgroup.mem_set_normalizer_iff.mp hcinv) x).mp hx
    have hcom : ((c : G)⁻¹ * x * (c : G)) * t = t * ((c : G)⁻¹ * x * (c : G)) :=
      Subgroup.mem_centralizer_iff.mp htC _ hxc
    rw [← hcval]
    have hx1 : x = (c : G) * ((c : G)⁻¹ * x * (c : G)) * (c : G)⁻¹ := by group
    rw [hx1]
    calc (c : G) * ((c : G)⁻¹ * x * (c : G)) * (c : G)⁻¹ * ((c : G) * t * (c : G)⁻¹)
        = (c : G) * (((c : G)⁻¹ * x * (c : G)) * t) * (c : G)⁻¹ := by group
      _ = (c : G) * (t * ((c : G)⁻¹ * x * (c : G))) * (c : G)⁻¹ := by rw [hcom]
      _ = (c : G) * t * (c : G)⁻¹ * ((c : G) * ((c : G)⁻¹ * x * (c : G)) * (c : G)⁻¹) := by
            group
  have hmem : k ∈ Subgroup.closure
      (involutions (Subgroup.centralizer (X : Set G) : Set G)) := by
    have h1 : k = t * (t * k) := by rw [← mul_assoc, ht2, one_mul]
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨htC, ht⟩)
      (Subgroup.subset_closure ⟨htkC, htk2'⟩)
  exact hmem

/-- If `S ⊔ D = K` with `K ≤ N(S)`, every element of `K` is a product `s * d`, `s ∈ S`, `d ∈ D`. -/
theorem eq_mul_of_mem_sup_of_normal {S D K : Subgroup G} (hSK : S ≤ K) (hDK : D ≤ K)
    (hnorm : K ≤ Subgroup.normalizer (S : Set G)) (hsup : S ⊔ D = K) {g : G} (hg : g ∈ K) :
    ∃ s ∈ S, ∃ d ∈ D, s * d = g := by
  have hSN : (S.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSK).mpr hnorm
  have hsup' : S.subgroupOf K ⊔ D.subgroupOf K = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hSK hDK, hsup, Subgroup.subgroupOf_self]
  haveI := hSN
  have hmem : (⟨g, hg⟩ : ↥K) ∈ (↑(S.subgroupOf K) * ↑(D.subgroupOf K) : Set ↥K) := by
    rw [← Subgroup.normal_mul (S.subgroupOf K) (D.subgroupOf K), hsup']
    trivial
  obtain ⟨s, hs, d, hd, hsd⟩ := hmem
  exact ⟨(s : G), Subgroup.mem_subgroupOf.mp hs, (d : G), Subgroup.mem_subgroupOf.mp hd,
    by simpa using congrArg (Subtype.val) hsd⟩

/-- If a normal subgroup `S` of a finite group `K` has a complement `D` of odd order
(`S ⊔ D = ⊤`, `S ⊓ D = ⊥`), then `[K : S]` is odd. -/
theorem odd_index_of_normal_complement {K : Type} [Group K] [Finite K] {S D : Subgroup K}
    (hS : S.Normal) (hsup : S ⊔ D = ⊤) (hinf : S ⊓ D = ⊥) (hodd : Odd (Nat.card ↥D)) :
    Odd S.index := by
  haveI := hS
  have huniv : (↑D : Set K) * (↑S : Set K) = (Set.univ : Set K) := by
    rw [← Subgroup.mul_normal D S, sup_comm, hsup]
    rfl
  have hcomp : D.IsComplement' S :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf).symm huniv
  rw [hcomp.index_eq_card]
  exact hodd

/-! ## 3. App. II (7) input: `S₀` is sharply transitive from `mk t` onto `Ω_{X₀} ∖ {H}` -/

theorem sharpTrans_of_P3Ab_aux {H X₀ : Subgroup G} {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) (hX₀ : X₀ ≤ centD H t)
    (h2t : Work.DoubleTransitivity.IsTwoTransitiveOnSub
      (Subgroup.normalizer (X₀ : Set G)) (fixedPts H X₀))
    {S₀ : Subgroup G} (hS₀le : S₀ ≤ p3F X₀ ⊓ H)
    (hS₀n : H ⊓ Subgroup.normalizer (X₀ : Set G) ≤ Subgroup.normalizer (S₀ : Set G))
    (hS₀D : S₀ ⊓ twoPoint H t = ⊥)
    (hS₀sup : S₀ ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X₀ : Set G)) =
      H ⊓ Subgroup.normalizer (X₀ : Set G)) :
    ∀ c ∈ fixedPts H X₀, c ≠ (QuotientGroup.mk (1 : G) : G ⧸ H) →
      ∃! q : ↥S₀, (q : G) • (QuotientGroup.mk t : G ⧸ H) = c := by
  intro c hc hca
  have ha : (QuotientGroup.mk (1 : G) : G ⧸ H) ∈ fixedPts H X₀ :=
    pt_mem_fixedPts_of_le_centD hX₀
  have hb : (QuotientGroup.mk t : G ⧸ H) ∈ fixedPts H X₀ :=
    mk_t_mem_fixedPts_of_le_centD hX₀
  have hab : (QuotientGroup.mk (1 : G) : G ⧸ H) ≠ (QuotientGroup.mk t : G ⧸ H) :=
    mk_one_ne_mk_t htH
  have hS₀H : S₀ ≤ H := hS₀le.trans inf_le_right
  have hS₀K : S₀ ≤ H ⊓ Subgroup.normalizer (X₀ : Set G) :=
    le_inf hS₀H ((hS₀le.trans inf_le_left).trans (p3F_le_normalizer X₀))
  have hD'le : twoPoint H t ⊓ Subgroup.normalizer (X₀ : Set G) ≤
      H ⊓ Subgroup.normalizer (X₀ : Set G) :=
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  obtain ⟨g, hg, hga, hgb⟩ := h2t _ ha _ hb hab _ ha _ hc hca.symm
  have hgH : g ∈ H := by
    have hmem : g ∈ MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) :=
      MulAction.mem_stabilizer_iff.mpr hga
    rwa [stabilizer_pt] at hmem
  obtain ⟨s, hs, d, hd, hsd⟩ := eq_mul_of_mem_sup_of_normal hS₀K hD'le hS₀n hS₀sup
    (Subgroup.mem_inf.mpr ⟨hgH, hg⟩)
  have hdD : d ∈ twoPoint H t := (Subgroup.mem_inf.mp hd).1
  have hdb : d • (QuotientGroup.mk t : G ⧸ H) = (QuotientGroup.mk t : G ⧸ H) := by
    have hmem : d ∈ MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ H) := by
      rw [stabilizer_mk H t]; exact hdD.2
    exact MulAction.mem_stabilizer_iff.mp hmem
  have hsv : (s : G) • (QuotientGroup.mk t : G ⧸ H) = c := by
    calc (s : G) • (QuotientGroup.mk t : G ⧸ H)
        = (s * d) • (QuotientGroup.mk t : G ⧸ H) := by rw [mul_smul, hdb]
      _ = g • (QuotientGroup.mk t : G ⧸ H) := by rw [← hsd]
      _ = c := hgb
  refine ⟨⟨s, hs⟩, hsv, ?_⟩
  intro y hy
  apply Subtype.ext
  have hmem : ((s : G)⁻¹ * (y : G)) ∈ S₀ ⊓ twoPoint H t := by
    refine Subgroup.mem_inf.mpr ⟨S₀.mul_mem (S₀.inv_mem hs) y.2, ?_⟩
    refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.inv_mem (hS₀H hs)) (hS₀H y.2), ?_⟩
    have hfix : ((s : G)⁻¹ * (y : G)) • (QuotientGroup.mk t : G ⧸ H) =
        (QuotientGroup.mk t : G ⧸ H) := by
      rw [mul_smul, hy, ← hsv, inv_smul_smul]
    have hmem2 : ((s : G)⁻¹ * (y : G)) ∈
        MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ H) :=
      MulAction.mem_stabilizer_iff.mpr hfix
    rwa [stabilizer_mk H t] at hmem2
  have hbot : ((s : G)⁻¹ * (y : G)) = 1 := by
    have h := hmem
    rw [hS₀D] at h
    simpa using h
  exact (inv_mul_eq_one.mp hbot).symm

/-! ## 4. `S₀ ⊓ F` is a Sylow `2`-subgroup of `F ⊓ H` and normal in `H ⊓ N_G(X)` -/

theorem isSylow_index_and_normal_of_inf_p3F_aux {H X₀ X : Subgroup G} {t : G}
    (hH : IsStronglyEmbedded H) (htH : t ∉ H) (hX₀X : X₀ ≤ X)
    (hNX : X ≤ Subgroup.normalizer (X₀ : Set G))
    {S₀ : Subgroup G} (hS₀p : IsPGroup 2 S₀) (hS₀le : S₀ ≤ p3F X₀ ⊓ H)
    (hS₀n : H ⊓ Subgroup.normalizer (X₀ : Set G) ≤ Subgroup.normalizer (S₀ : Set G))
    (hS₀D : S₀ ⊓ twoPoint H t = ⊥)
    (hS₀sup : S₀ ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X₀ : Set G)) =
      H ⊓ Subgroup.normalizer (X₀ : Set G)) :
    ¬ 2 ∣ ((S₀ ⊓ p3F X).subgroupOf (p3F X ⊓ H)).index ∧
    H ⊓ Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer ((S₀ ⊓ p3F X : Subgroup G) : Set G) := by
  classical
  have hS₀H : S₀ ≤ H := hS₀le.trans inf_le_right
  have hS₀K : S₀ ≤ H ⊓ Subgroup.normalizer (X₀ : Set G) :=
    le_inf hS₀H ((hS₀le.trans inf_le_left).trans (p3F_le_normalizer X₀))
  have hD'le : twoPoint H t ⊓ Subgroup.normalizer (X₀ : Set G) ≤
      H ⊓ Subgroup.normalizer (X₀ : Set G) :=
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hNormK : (S₀.subgroupOf (H ⊓ Subgroup.normalizer (X₀ : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hS₀K).mpr hS₀n
  -- ### the index of `S₀` in `K = H ⊓ N_G(X₀)` is odd
  have hoddIdx : Odd (S₀.subgroupOf (H ⊓ Subgroup.normalizer (X₀ : Set G))).index := by
    have hsup : S₀.subgroupOf (H ⊓ Subgroup.normalizer (X₀ : Set G)) ⊔
        (twoPoint H t ⊓ Subgroup.normalizer (X₀ : Set G)).subgroupOf
          (H ⊓ Subgroup.normalizer (X₀ : Set G)) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hS₀K hD'le, hS₀sup, Subgroup.subgroupOf_self]
    have hinf : S₀.subgroupOf (H ⊓ Subgroup.normalizer (X₀ : Set G)) ⊓
        (twoPoint H t ⊓ Subgroup.normalizer (X₀ : Set G)).subgroupOf
          (H ⊓ Subgroup.normalizer (X₀ : Set G)) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      have hxS : (x : G) ∈ S₀ := Subgroup.mem_subgroupOf.mp hx1
      have hxD : (x : G) ∈ twoPoint H t := (Subgroup.mem_subgroupOf.mp hx2).1
      have hthis : (x : G) ∈ S₀ ⊓ twoPoint H t := ⟨hxS, hxD⟩
      rw [hS₀D] at hthis
      exact Subtype.ext (by simpa using hthis)
    have hoddD' : Odd (Nat.card ↥(twoPoint H t ⊓ Subgroup.normalizer (X₀ : Set G) :
        Subgroup G)) :=
      Odd.of_dvd_nat (hH.2.2 t htH)
        (Subgroup.card_dvd_of_le
          (inf_le_left : twoPoint H t ⊓ Subgroup.normalizer (X₀ : Set G) ≤ twoPoint H t))
    have hoddD : Odd (Nat.card ↥((twoPoint H t ⊓ Subgroup.normalizer (X₀ : Set G)).subgroupOf
        (H ⊓ Subgroup.normalizer (X₀ : Set G)))) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD'le).toEquiv]
      exact hoddD'
    exact odd_index_of_normal_complement hNormK hsup hinf hoddD
  -- ### every element of `F ⊓ H` of `2`-power order lies in `S₀`
  have hmemS₀ : ∀ {y : G}, y ∈ p3F X → y ∈ H → ∀ {k : ℕ}, orderOf y = 2 ^ k → y ∈ S₀ := by
    intro y hyF hyH k hk
    have hyC₀ : y ∈ Subgroup.centralizer (X₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_centralizer_iff.mp (p3F_le_centralizer X hyF) x (hX₀X hx)
    have hyK : y ∈ H ⊓ Subgroup.normalizer (X₀ : Set G) :=
      ⟨hyH, Subgroup.centralizer_le_normalizer _ hyC₀⟩
    have hord : orderOf (⟨y, hyK⟩ : ↥(H ⊓ Subgroup.normalizer (X₀ : Set G))) = 2 ^ k := by
      rw [← Subgroup.orderOf_coe ⟨y, hyK⟩]; exact hk
    have hmem := Work.ThreePoints.mem_of_orderOf_eq_two_pow_of_odd_index hNormK hoddIdx hord
    exact Subgroup.mem_subgroupOf.mp hmem
  -- ### the index of `S₀ ⊓ F` in `F ⊓ H` is odd
  have hp3F_le_N₀ : p3F X ≤ Subgroup.normalizer (X₀ : Set G) := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (X : Set G) := p3F_le_centralizer X hx
    have hxC₀ : x ∈ Subgroup.centralizer (X₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at hxC ⊢
      exact fun y hy => hxC y (hX₀X hy)
    exact Subgroup.centralizer_le_normalizer (X₀ : Set G) hxC₀
  have hA_le_K : p3F X ⊓ H ≤ H ⊓ Subgroup.normalizer (X₀ : Set G) :=
    le_inf inf_le_right (inf_le_left.trans hp3F_le_N₀)
  have hsubEq : (S₀ ⊓ p3F X).subgroupOf (p3F X ⊓ H) = S₀.subgroupOf (p3F X ⊓ H) := by
    have h1 : S₀ ⊓ (p3F X ⊓ H) = S₀ ⊓ p3F X := by
      rw [← inf_assoc, inf_eq_left.mpr (inf_le_left.trans hS₀H)]
    rw [← h1, Subgroup.inf_subgroupOf_right]
  have hdiv : ((S₀ ⊓ p3F X).subgroupOf (p3F X ⊓ H)).index ∣
      (S₀.subgroupOf (H ⊓ Subgroup.normalizer (X₀ : Set G))).index := by
    rw [hsubEq]
    have h1 : (S₀.subgroupOf (H ⊓ Subgroup.normalizer (X₀ : Set G))).relIndex
        ((p3F X ⊓ H).subgroupOf (H ⊓ Subgroup.normalizer (X₀ : Set G))) ∣
        (S₀.subgroupOf (H ⊓ Subgroup.normalizer (X₀ : Set G))).index := by
      haveI := hNormK
      exact Subgroup.relIndex_dvd_index_of_normal _ _
    rwa [Subgroup.relIndex_subgroupOf hA_le_K] at h1
  have hSylow : ¬ 2 ∣ ((S₀ ⊓ p3F X).subgroupOf (p3F X ⊓ H)).index :=
    fun h2 => (Nat.not_even_iff_odd.mpr hoddIdx) (even_iff_two_dvd.mpr (h2.trans hdiv))
  -- ### `S₀ ⊓ F` is the set of `2`-elements of `F ⊓ H`, hence normal in `H ⊓ N_G(X)`
  have hchar : ∀ y : G, y ∈ (S₀ ⊓ p3F X : Subgroup G) ↔
      (y ∈ (p3F X ⊓ H : Subgroup G) ∧ ∃ k : ℕ, orderOf y = 2 ^ k) := by
    intro y
    constructor
    · rintro ⟨hyS₀, hyF⟩
      have hpow : ∃ k : ℕ, orderOf y = 2 ^ k := by
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hS₀p) ⟨y, hyS₀⟩
        exact ⟨k, (Subgroup.orderOf_coe ⟨y, hyS₀⟩).trans hk⟩
      exact ⟨⟨hyF, hS₀H hyS₀⟩, hpow⟩
    · rintro ⟨⟨hyF, hyH⟩, k, hk⟩
      exact ⟨hmemS₀ hyF hyH hk, hyF⟩
  have hNormal : H ⊓ Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer ((S₀ ⊓ p3F X : Subgroup G) : Set G) := by
    intro h hh
    obtain ⟨hhH, hhN⟩ := Subgroup.mem_inf.mp hh
    have hconjF : Submission.Blueprint.conj h (p3F X) = p3F X :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (normalizer_le_normalizer_p3F X hhN)
    have hconjH : Submission.Blueprint.conj h H = H := Work.ThreePoints.conj_eq_self_of_mem hhH
    have hconjA : Submission.Blueprint.conj h (p3F X ⊓ H : Subgroup G) =
        (p3F X ⊓ H : Subgroup G) := by
      rw [Work.ThreePoints.conj_inf, hconjF, hconjH]
    have hmemA : ∀ y : G, (h⁻¹ * y * h ∈ (p3F X ⊓ H : Subgroup G)) ↔
        (y ∈ (p3F X ⊓ H : Subgroup G)) := by
      intro y
      constructor
      · intro hy
        have h1 : y ∈ Submission.Blueprint.conj h (p3F X ⊓ H : Subgroup G) :=
          Subgroup.mem_map.mpr ⟨h⁻¹ * y * h, hy, by
            rw [Work.ThreePoints.mulAut_conj_toMonoidHom_apply]; group⟩
        rwa [hconjA] at h1
      · intro hy
        have h1 : y ∈ Submission.Blueprint.conj h (p3F X ⊓ H : Subgroup G) := by
          rw [hconjA]; exact hy
        exact Work.ThreePoints.mem_conj_iff.mp h1
    have hord : ∀ y : G, orderOf (h⁻¹ * y * h) = orderOf y := by
      intro y
      have h2 := MulEquiv.orderOf_eq (MulAut.conj h⁻¹) y
      rw [Work.ThreePoints.mulAut_conj_apply] at h2
      simpa [inv_inv] using h2
    have hconjS : Submission.Blueprint.conj h (S₀ ⊓ p3F X) = (S₀ ⊓ p3F X) := by
      ext y
      rw [Work.ThreePoints.mem_conj_iff, hchar (h⁻¹ * y * h), hchar y]
      constructor
      · rintro ⟨hyA, k, hk⟩
        exact ⟨(hmemA y).mp hyA, k, by rw [← hord y]; exact hk⟩
      · rintro ⟨hyA, k, hk⟩
        exact ⟨(hmemA y).mpr hyA, k, by rw [hord y]; exact hk⟩
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hconjS
  exact ⟨hSylow, hNormal⟩

/-- `N_H(X)` has even order (Ch. II §4 Prop. 1 (a) at `M = H`). -/
theorem even_card_normalizer_inf_H
    (hFT : FeitThompsonProp) (hC : ThmCProp) (hA : ThmAProp)
    (hBrSz : BrauerSuzukiProp) (hS : Situation G)
    {H X : Subgroup G} (hH : IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2)
    (htH : t ∉ H) (hX : X ≤ centD H t) :
    Even (Nat.card (Subgroup.normalizer (X : Set G) ⊓ H : Subgroup G)) := by
  have hX3 : 3 ≤ (fixedPts H X).ncard := three_le_ncard_fixedPts_of_le_centD hH ht htH hX
  obtain ⟨u, hu, hu2⟩ := exists_orderOf_two_of_even_card
    (prop1a_fixes_three hFT hC hA hBrSz hS hH (X := X) hX3 (M := H) ⟨1, (conj_one H).symm⟩
      (le_of_le_centD hX).1)
  exact even_card_of_mem_involution
    (Subgroup.mem_inf.mpr ⟨Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_inf.mp hu).2, (Subgroup.mem_inf.mp hu).1⟩) hu2

/-! ## 5. The induction step across one normal subgroup -/

theorem p3pkg_step {H X₀ X : Subgroup G} {t : G}
    (hH : IsStronglyEmbedded H) (ht : orderOf t = 2) (htH : t ∉ H)
    (hX₀ : X₀ ≤ centD H t) (hX : X ≤ centD H t) (hX₀X : X₀ ≤ X)
    (hNX : X ≤ Subgroup.normalizer (X₀ : Set G))
    (hinc : (invertedBy (twoPoint H t) t ∩ (Subgroup.normalizer (X : Set G) : Set G)) ⊆
      (p3F X : Set G))
    (hP₀ : P3Pkg H t X₀) : P3Pkg H t X := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  obtain ⟨⟨-, S₀, hS₀p, hS₀le, -, hS₀n, hS₀D, hS₀sup⟩, h2t₀⟩ := hP₀
  have hXH : X ≤ H := (le_of_le_centD hX).1
  have hS₀H : S₀ ≤ H := hS₀le.trans inf_le_right
  have ha_mem : (QuotientGroup.mk (1 : G) : G ⧸ H) ∈ fixedPts H X₀ :=
    pt_mem_fixedPts_of_le_centD hX₀
  have hb_mem : (QuotientGroup.mk t : G ⧸ H) ∈ fixedPts H X₀ :=
    mk_t_mem_fixedPts_of_le_centD hX₀
  have ha_memX : (QuotientGroup.mk (1 : G) : G ⧸ H) ∈ fixedPts H X :=
    pt_mem_fixedPts_of_le_centD hX
  have hb_memX : (QuotientGroup.mk t : G ⧸ H) ∈ fixedPts H X :=
    mk_t_mem_fixedPts_of_le_centD hX
  have hab : (QuotientGroup.mk (1 : G) : G ⧸ H) ≠ (QuotientGroup.mk t : G ⧸ H) :=
    mk_one_ne_mk_t htH
  -- ### Step A: `S₀` is sharply transitive from `mk t` onto `Ω_{X₀} ∖ {mk 1}`
  have hreg : ∀ c ∈ fixedPts H X₀, c ≠ (QuotientGroup.mk (1 : G) : G ⧸ H) →
      ∃! q : ↥S₀, (q : G) • (QuotientGroup.mk t : G ⧸ H) = c :=
    sharpTrans_of_P3Ab_aux ht htH hX₀ h2t₀ hS₀le hS₀n hS₀D hS₀sup
  -- ### Step B: App. II (7)
  have hstab_a : MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) = H := stabilizer_pt H
  have hstab_b : MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ H) = conj t H :=
    stabilizer_mk H t
  have hQa : S₀ ≤ MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) :=
    fun x hx => by rw [hstab_a]; exact hS₀H hx
  have hQn : Subgroup.normalizer (X₀ : Set G) ⊓
      MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) ≤
      Subgroup.normalizer (S₀ : Set G) := by
    rw [hstab_a]
    exact fun x hx => hS₀n ⟨hx.2, hx.1⟩
  have hDstab : twoPoint H t ≤ MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) ⊓
      MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ H) := by
    intro x hx
    rw [twoPoint_eq] at hx
    exact Subgroup.mem_inf.mpr
      ⟨by rw [hstab_a]; exact hx.1, by rw [hstab_b]; exact hx.2⟩
  have hYstab : X ≤ MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) ⊓
      MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ H) :=
    le_inf (fun x hx => by rw [hstab_a]; exact hXH hx)
      (fun x hx => by rw [hstab_b]; exact (le_of_le_centD hX).2 hx)
  have hZreg : Work.DoubleTransitivity.IsRegularOnSub
      (S₀ ⊓ Subgroup.centralizer (X : Set G))
      ((Work.DoubleTransitivity.fixedBySub X) \ ({(QuotientGroup.mk (1 : G) : G ⧸ H)} :
        Set (G ⧸ H))) :=
    app2_7 (E0 := fixedPts H X₀) (a := (QuotientGroup.mk (1 : G) : G ⧸ H))
      (b := (QuotientGroup.mk t : G ⧸ H)) (N := Subgroup.normalizer (X₀ : Set G)) (Q := S₀)
      (D := twoPoint H t) (Y := X)
      ha_mem hb_mem hab hQa hQn (fun c hc => hreg c hc.1 (by simpa using hc.2))
      hDstab hYstab hNX (fixedPts_mono hX₀X)
  have hZleF : S₀ ⊓ Subgroup.centralizer (X : Set G) ≤ p3F X :=
    mem_p3F_of_isPGroup inf_le_right (hS₀p.to_le inf_le_left)
  have hZa : S₀ ⊓ Subgroup.centralizer (X : Set G) ≤
      MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) :=
    fun x hx => by rw [hstab_a]; exact hS₀H (Subgroup.mem_inf.mp hx).1
  have htF : t ∈ p3F X := t_mem_p3F hX ht
  have hFtrans : ∀ x ∈ fixedPts H X, ∃ f ∈ p3F X,
      f • (QuotientGroup.mk (1 : G) : G ⧸ H) = x := by
    intro x hx
    by_cases hxa : x = (QuotientGroup.mk (1 : G) : G ⧸ H)
    · exact ⟨1, (p3F X).one_mem, by rw [hxa, one_smul]⟩
    · obtain ⟨z, hz, hzval⟩ := hZreg.1 (QuotientGroup.mk t : G ⧸ H)
        ⟨hb_memX, by simpa using hab.symm⟩ x ⟨hx, by simpa using hxa⟩
      refine ⟨z * t, (p3F X).mul_mem (hZleF hz) htF, ?_⟩
      show (z * t) • (QuotientGroup.mk (1 : G) : G ⧸ H) = x
      rw [mul_smul, smul_mk H t 1, mul_one]
      exact hzval
  have h2tF : Work.DoubleTransitivity.IsTwoTransitiveOnSub (p3F X) (fixedPts H X) :=
    twoTransitive_of_regular (p3F X) (S₀ ⊓ Subgroup.centralizer (X : Set G)) (fixedPts H X)
      (QuotientGroup.mk (1 : G) : G ⧸ H) ha_memX
      (fun f hf x hx => smul_mem_fixedPts_of_mem_normalizer (p3F_le_normalizer X hf) hx)
      hZleF hZa
      (fun c hc hca d hd hda =>
        hZreg.1 c ⟨hc, by simpa using hca⟩ d ⟨hd, by simpa using hda⟩)
      hFtrans
  have h2tN : Work.DoubleTransitivity.IsTwoTransitiveOnSub
      (Subgroup.normalizer (X : Set G)) (fixedPts H X) :=
    twoTransitive_mono h2tF (p3F_le_normalizer X)
  -- ### (a)
  have ha_eq : Subgroup.normalizer (X : Set G) =
      p3F X ⊔ (centD H t ⊓ Subgroup.normalizer (X : Set G)) :=
    calc Subgroup.normalizer (X : Set G)
        = p3F X ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) :=
          normalizer_eq_sup_twoPoint htH hX h2tF
      _ = p3F X ⊔ (centD H t ⊓ Subgroup.normalizer (X : Set G)) :=
          sup_twoPoint_eq_sup_centD hH ht htH hX hinc
  -- ### (b)
  have hSp : IsPGroup 2 ↥(S₀ ⊓ p3F X) := hS₀p.to_le inf_le_left
  have hSle : S₀ ⊓ p3F X ≤ p3F X ⊓ H := le_inf inf_le_right (inf_le_left.trans hS₀H)
  have hCax := isSylow_index_and_normal_of_inf_p3F_aux hH htH hX₀X hNX hS₀p hS₀le hS₀n hS₀D
    hS₀sup
  have hidx : ¬ 2 ∣ ((S₀ ⊓ p3F X).subgroupOf (p3F X ⊓ H)).index := hCax.1
  have hSnorm : H ⊓ Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer ((S₀ ⊓ p3F X : Subgroup G) : Set G) := hCax.2
  have hSD : S₀ ⊓ p3F X ⊓ twoPoint H t = ⊥ := by
    have h : S₀ ⊓ p3F X ⊓ twoPoint H t ≤ S₀ ⊓ twoPoint H t :=
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
    rw [hS₀D] at h
    exact le_bot_iff.mp h
  have hsup_le : S₀ ⊓ p3F X ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) ≤
      H ⊓ Subgroup.normalizer (X : Set G) :=
    sup_le (le_inf (inf_le_left.trans hS₀H) (inf_le_right.trans (p3F_le_normalizer X)))
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  have hle_sup : H ⊓ Subgroup.normalizer (X : Set G) ≤
      S₀ ⊓ p3F X ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) := by
    intro h hh
    obtain ⟨hhH, hhN⟩ := Subgroup.mem_inf.mp hh
    have hhb : h • (QuotientGroup.mk t : G ⧸ H) ∈ fixedPts H X :=
      smul_mem_fixedPts_of_mem_normalizer hhN hb_memX
    have hha : h • (QuotientGroup.mk (1 : G) : G ⧸ H) =
        (QuotientGroup.mk (1 : G) : G ⧸ H) := by
      have hmem : h ∈ MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) := by
        rw [hstab_a]; exact hhH
      exact MulAction.mem_stabilizer_iff.mp hmem
    have hhba : h • (QuotientGroup.mk t : G ⧸ H) ≠ (QuotientGroup.mk (1 : G) : G ⧸ H) := by
      intro hcon
      refine hab (smul_left_cancel h ?_)
      rw [hha, hcon]
    obtain ⟨z, hz, hzval⟩ := hZreg.1 (QuotientGroup.mk t : G ⧸ H)
      ⟨hb_memX, by simpa using hab.symm⟩ (h • (QuotientGroup.mk t : G ⧸ H))
      ⟨hhb, by simpa using hhba⟩
    have hzS : z ∈ S₀ ⊓ p3F X := ⟨hz.1, hZleF hz⟩
    have hzN : z ∈ Subgroup.normalizer (X : Set G) := p3F_le_normalizer X (hZleF hz)
    have hzh : z⁻¹ * h ∈ twoPoint H t ⊓ Subgroup.normalizer (X : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.inv_mem (hS₀H hz.1)) hhH, ?_⟩
        rw [← hstab_b, MulAction.mem_stabilizer_iff, mul_smul, ← hzval, inv_smul_smul]
      · exact (Subgroup.normalizer (X : Set G)).mul_mem
          ((Subgroup.normalizer (X : Set G)).inv_mem hzN) hhN
    have hh_eq : h = z * (z⁻¹ * h) := by group
    rw [hh_eq]
    exact (S₀ ⊓ p3F X ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G))).mul_mem
      (Subgroup.mem_sup_left hzS) (Subgroup.mem_sup_right hzh)
  refine ⟨⟨ha_eq, S₀ ⊓ p3F X, hSp, hSle, hidx, hSnorm, hSD,
      le_antisymm hsup_le hle_sup⟩, h2tN⟩

/-! ## 6. The main lemma -/

theorem p3pkg_of_subnormal {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hZJ : Submission.Blueprint.GlaubermanZJProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hMod : Submission.Blueprint.ModelFactsProp)
    (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    {t : G} (ht : orderOf t = 2) (htH : t ∉ H)
    {X : Subgroup G} (hX : X ≤ Submission.Blueprint.centD H t)
    (ih : ∀ X₀ : Subgroup G, Nat.card ↥X₀ < Nat.card ↥X →
      X₀ ≤ Submission.Blueprint.centD H t →
      (∃ Y : Subgroup G, Y ≠ ⊥ ∧ Submission.Blueprint.IsSubnormalIn Y X₀ ∧
        Work.ThreePoints.HasNonTrivialNK H t Y) → Work.ThreePoints.P3Pkg H t X₀)
    {Y : Subgroup G} (hYne : Y ≠ ⊥) (hsub : Submission.Blueprint.IsSubnormalIn Y X)
    (hYX : Y ≠ X) (hNK : Work.ThreePoints.HasNonTrivialNK H t Y) :
    Work.ThreePoints.P3Pkg H t X := by
  classical
  obtain ⟨X₀, hYX₀, hX₀X, hX₀norm, hX₀ne, hsub₀⟩ := exists_normal_subgroup_of_subnormal hsub hYX
  have hX₀le : X₀ ≤ centD H t := hX₀X.trans hX
  have hlt : Nat.card ↥X₀ < Nat.card ↥X :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hX₀X hX₀ne)
  have hP₀ : P3Pkg H t X₀ := ih X₀ hlt hX₀le ⟨Y, hYne, hsub₀, hNK⟩
  have hNX : X ≤ Subgroup.normalizer (X₀ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX₀X).mp hX₀norm
  have hinc : (invertedBy (twoPoint H t) t ∩ (Subgroup.normalizer (X : Set G) : Set G)) ⊆
      (p3F X : Set G) := by
    by_cases hnk : HasNonTrivialNK H t X
    · intro k hk
      have hcl := nk_le_closure hH ht htH hX
        (even_card_normalizer_inf_H hFT hC hA hBrSz hS hH ht htH hX) hk
      exact Subgroup.closure_le (p3F X) |>.mpr (fun u hu => mem_p3F_of_involution hu.1 hu.2) hcl
    · intro k hk
      have hk1 : k = 1 := by
        by_contra hne
        exact hnk ⟨k, hk.1, hne, hk.2⟩
      rw [hk1]
      exact (p3F X).one_mem
  exact p3pkg_step hH ht htH hX₀le hX hX₀X hNX hinc hP₀

end Work.ThreePoints.P3Sub
