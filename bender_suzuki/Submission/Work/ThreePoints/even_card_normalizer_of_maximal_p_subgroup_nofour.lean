import Mathlib
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

open scoped Pointwise

/-- The map argument identifying `N_K(Q)` with `N_F(Q) ⊓ K`: the normaliser of `Q.subgroupOf K`
in `K` has the same cardinality as `K ⊓ N_F(Q)`. -/
theorem card_normalizer_subgroupOf_eq_card_inf {F : Type} [Group F] {K Q : Subgroup F}
    (hQK : Q ≤ K) :
    Nat.card ↥(Subgroup.normalizer (Q.subgroupOf K : Set K) : Subgroup K) =
      Nat.card ↥(K ⊓ Subgroup.normalizer (Q : Set F) : Subgroup F) := by
  have hmap : (Subgroup.normalizer (Q.subgroupOf K : Set K)).map K.subtype =
      K ⊓ Subgroup.normalizer (Q : Set F) := by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hy' : (Q.subgroupOf K).map (MulAut.conj y).toMonoidHom = Q.subgroupOf K :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hy
      calc Q.map (MulAut.conj (y : F)).toMonoidHom
          = ((Q.subgroupOf K).map K.subtype).map (MulAut.conj (y : F)).toMonoidHom := by
            conv_lhs => rw [← Subgroup.map_subgroupOf_eq_of_le hQK]
        _ = (Q.subgroupOf K).map ((MulAut.conj (y : F)).toMonoidHom.comp K.subtype) := by
            rw [Subgroup.map_map]
        _ = (Q.subgroupOf K).map (K.subtype.comp (MulAut.conj y).toMonoidHom) := by
            rw [show (MulAut.conj (y : F)).toMonoidHom.comp K.subtype =
              K.subtype.comp (MulAut.conj y).toMonoidHom from by
                ext z
                simp [MulAut.conj_apply]]
        _ = ((Q.subgroupOf K).map (MulAut.conj y).toMonoidHom).map K.subtype := by
            rw [Subgroup.map_map]
        _ = (Q.subgroupOf K).map K.subtype := by rw [hy']
        _ = Q := Subgroup.map_subgroupOf_eq_of_le hQK
    · rintro ⟨hxK, hxN⟩
      refine Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, ?_, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have hyQ : (y : F) ∈ Q := Subgroup.mem_subgroupOf.mp hy
        have h1 : x * (y : F) * x⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp hxN) (y : F) |>.mp hyQ
        rw [Subgroup.mem_subgroupOf]
        simpa using h1
      · intro hy
        have hyQ : x * (y : F) * x⁻¹ ∈ Q := by
          have h := Subgroup.mem_subgroupOf.mp hy
          simpa using h
        have hxi : x⁻¹ ∈ Subgroup.normalizer (Q : Set F) :=
          (Subgroup.normalizer (Q : Set F)).inv_mem hxN
        have h1 : x⁻¹ * (x * (y : F) * x⁻¹) * x⁻¹⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp hxi) (x * (y : F) * x⁻¹) |>.mp hyQ
        have h2 : x⁻¹ * (x * (y : F) * x⁻¹) * x⁻¹⁻¹ = (y : F) := by group
        rw [h2] at h1
        exact Subgroup.mem_subgroupOf.mpr h1
  rw [← hmap]
  exact (Subgroup.card_map_of_injective (f := K.subtype) Subtype.coe_injective).symm

/-- Conjugation carries the fixed-point set of a subgroup to that of its conjugate:
`fixedPts K (conj y R) = y • fixedPts K R`. -/
theorem fixedPts_conj {F : Type} [Group F] (K : Subgroup F) (y : F) (R : Subgroup F) :
    fixedPts K (conj y R) = y • fixedPts K R :=
  Work.DoubleTransitivity.App2.app2_3_fixedBySub_map_conj (X := F) (E := F ⧸ K) R y

/-- **The assembly of Peterfalvi I Ch. I §4 Prop. 2 in the `2`-rank-`1` case**, reduced to the
"no `p`-subgroup has exactly two fixed points" input `hNO2`.

Given `hNO2`, the argument is the source's: (1) `Q` is a `p`-Sylow subgroup of `K ⊓ L` for every
conjugate `L` of `K` containing `Q` (otherwise a strictly larger `p`-subgroup of `K ⊓ L` would
have exactly two fixed points or contradict maximality of `Q` in `K`), so `N_F(Q)` is transitive
on `Ω_Q` (`sec3_lemma1`); (2) transitivity upgrades maximality of `Q` in `K` to maximality in
`F`; (3) `sec3_prop1_transitive` supplies a point stabiliser of `N_F(Q)` of even order, which
transitivity transfers to the point stabiliser `K`; (4) the identification
`N_K(Q) ≅ K ⊓ N_F(Q)` (`card_normalizer_subgroupOf_eq_card_inf`) concludes. -/
theorem even_card_normalizer_nofour_of_no_two_fixed {F : Type} [Group F] [Finite F]
    {K : Subgroup F} (hK : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup F} (hQK : Q ≤ K)
    (hQp : IsPGroup p Q) (hQ3 : 3 ≤ (Submission.Blueprint.fixedPts K Q).ncard)
    (hQmax : ∀ R : Subgroup F, Q ≤ R → R ≤ K → IsPGroup p R →
      3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q)
    (hNO2 : ∀ P : Subgroup F, IsPGroup p P → (Submission.Blueprint.fixedPts K P).ncard ≠ 2)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) :
    Even (Nat.card (Subgroup.normalizer (Q.subgroupOf K : Set K) : Subgroup K)) := by
  classical
  haveI : Fintype (F ⧸ K) := Fintype.ofFinite _
  set M : Subgroup F := Subgroup.normalizer (Q : Set F) with hMdef
  set ω₀ : F ⧸ K := ((1 : F) : F ⧸ K) with hω₀def
  have hstab0 : MulAction.stabilizer F ω₀ = K := by
    rw [hω₀def, Work.ThreePoints.stabilizer_mk, Work.ThreePoints.conj_one]
  have hω₀Q : ω₀ ∈ Submission.Blueprint.fixedPts K Q :=
    Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mpr (by rw [hstab0]; exact hQK)
  -- Step 1: `Q` is a `p`-Sylow subgroup of `K ⊓ L` for every conjugate `L ≠ K` containing `Q`.
  have hsyl : ∀ L : Subgroup F, (∃ g : F, L = conj g K) → Q ≤ L → L ≠ K →
      Work.DoubleTransitivity.IsSylowSubgroupOf p Q (K ⊓ L) := by
    intro L hLconj hQL hLne
    refine ⟨le_inf hQK hQL, hQp, ?_⟩
    intro hdvd
    obtain ⟨Q', hQ'le, hQ'p, hQ'gt⟩ :=
      Work.ThreePoints.exists_pSubgroup_lt_of_dvd_index hp hQp (le_inf hQK hQL) hdvd
    have hQ'K : Q' ≤ K := le_trans hQ'le inf_le_left
    have hQ'L : Q' ≤ L := le_trans hQ'le inf_le_right
    have hωK : ω₀ ∈ Submission.Blueprint.fixedPts K Q' :=
      Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mpr (by rw [hstab0]; exact hQ'K)
    obtain ⟨g, hgL⟩ := hLconj
    have hωL : (g : F ⧸ K) ∈ Submission.Blueprint.fixedPts K Q' := by
      rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer,
        Work.ThreePoints.stabilizer_mk]
      exact hQ'L.trans (le_of_eq hgL)
    have hne : ω₀ ≠ (g : F ⧸ K) := by
      intro h
      apply hLne
      have h2 : MulAction.stabilizer F ω₀ = MulAction.stabilizer F (g : F ⧸ K) := by rw [h]
      rw [hstab0, Work.ThreePoints.stabilizer_mk] at h2
      rw [hgL]
      exact h2.symm
    have h2le : 2 ≤ (Submission.Blueprint.fixedPts K Q').ncard := by
      have h1lt : 1 < (Submission.Blueprint.fixedPts K Q').ncard :=
        (Set.one_lt_ncard (Set.toFinite _)).mpr ⟨ω₀, hωK, (g : F ⧸ K), hωL, hne⟩
      omega
    by_cases h2eq : (Submission.Blueprint.fixedPts K Q').ncard = 2
    · exact hNO2 Q' hQ'p h2eq
    · have h3 : 3 ≤ (Submission.Blueprint.fixedPts K Q').ncard := by omega
      exact (ne_of_lt hQ'gt).symm (hQmax Q' hQ'gt.le hQ'K hQ'p h3)
  -- Step 2: `N_F(Q)` is transitive on `Ω_Q`.
  have hbase : ∀ ω ∈ Submission.Blueprint.fixedPts K Q,
      ∃ y ∈ M, y • ω₀ = ω := by
    intro ω hω
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
    by_cases hgK : g ∈ K
    · refine ⟨1, M.one_mem, ?_⟩
      rw [one_smul, hω₀def]
      rw [Work.DoubleTransitivity.mk_eq_mk_iff]
      simpa using hgK
    · have hLne : conj g K ≠ K := by
        intro h
        apply hgK
        have hgN : g ∈ Subgroup.normalizer (K : Set F) :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
        rw [Work.ThreePoints.IsStronglyEmbedded.normalizer_eq hK] at hgN
        exact hgN
      have hQL : Q ≤ conj g K := by
        rw [← Work.ThreePoints.stabilizer_mk K g]
        exact Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mp hω
      have hne : ω₀ ≠ (g : F ⧸ K) := by
        intro h
        apply hLne
        have h2 : MulAction.stabilizer F ω₀ = MulAction.stabilizer F (g : F ⧸ K) := by rw [h]
        rw [hstab0, Work.ThreePoints.stabilizer_mk] at h2
        exact h2.symm
      have hsylg := hsyl (conj g K) ⟨g, rfl⟩ hQL hLne
      have hsyl' : Work.DoubleTransitivity.IsSylowSubgroupOf p Q
          (MulAction.stabilizer F ω₀ ⊓ MulAction.stabilizer F (g : F ⧸ K)) := by
        rwa [hstab0, Work.ThreePoints.stabilizer_mk]
      obtain ⟨u, -, huQ, huω⟩ := Work.ThreePoints.sec3_lemma1 hK hp hne hsyl'
      exact ⟨u, Subgroup.mem_normalizer_iff_map_conj_eq.mpr huQ, huω⟩
  have htransF : Work.DoubleTransitivity.IsTransitiveOnSub M
      (Submission.Blueprint.fixedPts K Q) := by
    intro c hc d hd
    obtain ⟨yc, hycM, hyc⟩ := hbase c hc
    obtain ⟨yd, hydM, hyd⟩ := hbase d hd
    refine ⟨yd * yc⁻¹, M.mul_mem hydM (M.inv_mem hycM), ?_⟩
    rw [mul_smul]
    have h1 : yc⁻¹ • c = ω₀ := by
      rw [← hyc, ← mul_smul, inv_mul_cancel, one_smul]
    rw [h1, hyd]
  -- Step 3: `Q` is maximal among the `p`-subgroups of `F` with ≥ 3 fixed points.
  have hmaxF : ∀ R : Subgroup F, Q ≤ R → IsPGroup p R →
      3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q := by
    intro R hQR hRp hR3
    have hne : (Submission.Blueprint.fixedPts K R).Nonempty := by
      rw [← Set.ncard_pos]; omega
    obtain ⟨ω, hω⟩ := hne
    have hωQ : ω ∈ Submission.Blueprint.fixedPts K Q :=
      Work.ThreePoints.fixedPts_mono hQR hω
    obtain ⟨y, hyM, hy⟩ := htransF ω₀ hω₀Q ω hωQ
    set R' : Subgroup F := conj y⁻¹ R with hR'def
    have hQR' : Q ≤ R' := by
      have hyQ : conj y⁻¹ Q = Q :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (M.inv_mem hyM)
      rw [hR'def, ← hyQ]
      exact Subgroup.map_mono hQR
    have hωK' : ω₀ ∈ Submission.Blueprint.fixedPts K R' := by
      rw [hR'def, fixedPts_conj]
      exact ⟨y • ω₀, hy ▸ hω, inv_smul_smul y ω₀⟩
    have hR'K : R' ≤ K := by
      have h := (Work.ThreePoints.mem_fixedPts_iff_le_stabilizer (H := K) (X := R')
        (ω := ω₀)).mp hωK'
      rwa [hstab0] at h
    have hR'3 : 3 ≤ (Submission.Blueprint.fixedPts K R').ncard := by
      rw [hR'def, fixedPts_conj, Set.ncard_smul_set]; exact hR3
    have hR'p : IsPGroup p R' := hRp.map (MulAut.conj y⁻¹).toMonoidHom
    have hR'eq : R' = Q := hQmax R' hQR' hR'K hR'p hR'3
    have hyQ : conj y Q = Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hyM
    have : R = conj y Q := by
      rw [← hR'eq, hR'def, Work.DoubleTransitivity.conj_conj_inv]
    rw [this, hyQ]
  -- Step 4: Ch. I §3 Prop. 1 and the transfer to the point stabiliser `K`.
  obtain ⟨ω₁, hω₁, heven⟩ :=
    Work.ThreePoints.sec3_prop1_transitive hK hBrSz hp hp2 hQp hQ3 hmaxF htransF
  obtain ⟨n, hnM, hn⟩ := htransF ω₀ hω₀Q ω₁ hω₁
  have hMconj : conj n M = M := by
    have hstep : ∀ u ∈ M, conj u M ≤ M := by
      intro u hu m hm
      rw [Work.ThreePoints.mem_conj_iff] at hm
      have h := M.mul_mem (M.mul_mem hu hm) (M.inv_mem hu)
      rwa [show u * (u⁻¹ * m * u) * u⁻¹ = m from by group] at h
    refine le_antisymm (hstep n hnM) ?_
    calc M = conj n (conj n⁻¹ M) := by rw [← Work.ThreePoints.conj_mul, mul_inv_cancel,
        Work.ThreePoints.conj_one]
      _ ≤ conj n M := Subgroup.map_mono (hstep n⁻¹ (M.inv_mem hnM))
  have hcard_eq : Nat.card (MulAction.stabilizer F ω₁ ⊓ M : Subgroup F) =
      Nat.card (MulAction.stabilizer F ω₀ ⊓ M : Subgroup F) := by
    have h1 : MulAction.stabilizer F ω₁ = conj n (MulAction.stabilizer F ω₀) := by
      rw [← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj n ω₀, hn]
    have key2 : MulAction.stabilizer F ω₁ ⊓ M =
        conj n (MulAction.stabilizer F ω₀ ⊓ M) := by
      rw [Work.ThreePoints.conj_inf, ← h1, hMconj]
    rw [key2]
    exact Subgroup.card_map_of_injective (MulAut.conj n).injective
  have hevenK : Even (Nat.card (MulAction.stabilizer F ω₀ ⊓ M : Subgroup F)) := by
    rw [← hcard_eq]; exact heven
  rw [card_normalizer_subgroupOf_eq_card_inf hQK, ← hstab0]
  exact hevenK

end Work.ThreePoints
