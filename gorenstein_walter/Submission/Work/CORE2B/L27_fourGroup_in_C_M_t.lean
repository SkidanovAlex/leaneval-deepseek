import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.BenderCtx_sylow_not_cyclic
import Submission.Work.RED.DihedralSubgroup
import Submission.Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic
import Submission.Work.RED.DihOrCycSubgroup
import Submission.Work.Dihedral.Defs
import Submission.Work.CORE2B.L27_dihedral_commuting_involution

/-!
# CORE2B — Bender 1981, Lemma 2.7 (p. 221): the four-group step

Under the hypotheses of Lemma 2.7 (`Work.CORE2B.L27Hyp`) there is a Klein four-group `V ≤ M`
with `t ∈ V` and `V ≤ C_G(t)`.  Equivalently there is an involution `v ∈ M`, `v ≠ t`, commuting
with `t`.

The proof only uses `t ∈ M` and "Sylow 2-subgroups of `M` are not cyclic" from `L27Hyp`:

* `t` is a 2-element of `M`, so some `P : Sylow 2 M` contains it (`IsPGroup.exists_le_sylow`);
* `P` is not cyclic (`L27Hyp.sylow_nc`), and `P` is cyclic or dihedral by heredity of
  `DihOrCycSylow` (`Work.RED.DihOrCycSubgroup` + `Work.RED.DihedralSubgroup`), so
  `e : ↥P ≃* DihedralGroup n` for some `n`;
* `P` is a non-cyclic 2-group, so `n` is even and nonzero
  (`Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic`);
* in `DihedralGroup n` with `n` even, every involution admits a *different* involution
  commuting with it (`Work.CORE2B.L27_dihedral_commuting_involution`); applied to `e t`
  this produces `u ∈ DihedralGroup n`, and `v := e⁻¹ u ∈ P ⊆ M` is an involution of `G`
  commuting with `t` and different from it;
* `V := ⟨t, v⟩` is a Klein four-group (`fourGroup_closure_pair`, proved below in the local
  `Work.GW2` vocabulary), contained in `M` and centralized by `t`.

Note that neither `M ≠ ⊤`, nor `BRel B.Hhat M`, nor `¬ M ≤ B.Hhat`, nor `t ∉ E(M)`, nor the
`size` disjunction is needed.
-/

namespace Work.CORE2B

open Subgroup

/-! ## 0. A Klein four-group from two distinct commuting involutions

The statement of `fourGroup_closure_pair` below is the local (`Submission.Work.CORE2B.Defs`)
copy of `Work.CORE2A.isFourGroup_closure_pair`, which cannot be imported here because
`Submission.Work.CORE2A.Defs` re-declares the `Work.GW2` vocabulary.  The proof uses only
Mathlib. -/

/-- For commuting involutions `u, v` in a group, the subgroup `⟨{u, v}⟩` is exactly
`{1, u, v, uv}`. -/
private theorem mem_closure_pair_of_sq_eq_one {G : Type*} [Group G] {u v x : G}
    (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) (hc : u * v = v * u) :
    x ∈ Subgroup.closure ({u, v} : Set G) ↔ x = 1 ∨ x = u ∨ x = v ∨ x = u * v := by
  have hu2 : u * u = 1 := by simpa [pow_two] using hu
  have hv2 : v * v = 1 := by simpa [pow_two] using hv
  have hcs : v * u = u * v := hc.symm
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have huuv : u * (u * v) = v := by rw [← mul_assoc, hu2, one_mul]
  have huvv : (u * v) * v = u := by rw [mul_assoc, hv2, mul_one]
  have hvuv : v * (u * v) = u := by rw [← mul_assoc, ← hc, huvv]
  have huvu : (u * v) * u = v := by rw [mul_assoc, ← hc, ← mul_assoc, hu2, one_mul]
  have huvuv : (u * v) * (u * v) = 1 := by rw [← mul_assoc, huvu, hv2]
  have huv' : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_right huvuv
  constructor
  · intro hx
    refine Subgroup.closure_induction (k := ({u, v} : Set G))
      (p := fun y (_ : y ∈ Subgroup.closure ({u, v} : Set G)) =>
        y = 1 ∨ y = u ∨ y = v ∨ y = u * v) ?_ ?_ ?_ ?_ hx
    · rintro y hy
      rcases hy with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl rfl
    · rintro x y _ _ hx' hy'
      rcases hx' with rfl | rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl | rfl <;>
        simp [hu2, hv2, hcs, huuv, hvuv, huvu, huvv, huvuv]
    · rintro x _ hx'
      rcases hx' with rfl | rfl | rfl | rfl <;> simp [hu', hv', huv']
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

/-- If `u, v` are commuting involutions whose four products `1, u, v, uv` are pairwise
distinct, then `⟨{u, v}⟩` has exactly four elements. -/
private theorem card_closure_pair_of_sq_eq_one {G : Type*} [Group G] (u v : G) (hu : u ^ 2 = 1)
    (hv : v ^ 2 = 1) (hc : u * v = v * u) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hne : u * v ≠ 1) :
    Nat.card (Subgroup.closure ({u, v} : Set G)) = 4 := by
  have hu2 : u * u = 1 := by simpa [pow_two] using hu
  have hut : u ≠ v := fun h => hne (by rw [← h]; exact hu2)
  have h1t : (1 : G) ≠ u := fun h => hu1 h.symm
  have h1s : (1 : G) ≠ v := fun h => hv1 h.symm
  have h1uv : (1 : G) ≠ u * v := fun h => hne h.symm
  have huuv' : u ≠ u * v := fun h => hv1 ((mul_left_cancel (by rw [mul_one]; exact h)).symm)
  have hvuv' : v ≠ u * v := fun h => hu1 ((mul_right_cancel (by rw [one_mul]; exact h)).symm)
  have h3 : ({v, u * v} : Set G).ncard = 2 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_singleton]
    simpa only [Set.mem_singleton_iff] using hvuv'
  have h2 : ({u, v, u * v} : Set G).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem, h3]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hut, huuv'⟩
  have h4 : ({1, u, v, u * v} : Set G).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, h2]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1t, h1s, h1uv⟩
  have hset : ((Subgroup.closure ({u, v} : Set G)) : Set G) = {1, u, v, u * v} := by
    ext x
    show x ∈ Subgroup.closure ({u, v} : Set G) ↔ x ∈ ({1, u, v, u * v} : Set G)
    rw [mem_closure_pair_of_sq_eq_one hu hv hc]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  change Nat.card ↥((Subgroup.closure ({u, v} : Set G)) : Set G) = 4
  rw [Nat.card_coe_set_eq, hset, h4]

/-- Two distinct, nontrivial, commuting involutions generate a Klein four-group, which is
contained in the centralizer of either of them. -/
theorem fourGroup_closure_pair {G : Type} [Group G] [Finite G] {t v : G}
    (ht : t ^ 2 = 1) (hv : v ^ 2 = 1) (ht1 : t ≠ 1) (hv1 : v ≠ 1) (hne : v ≠ t)
    (hcomm : v * t = t * v) :
    Work.GW2.IsFourGroup (Subgroup.closure ({t, v} : Set G)) ∧
      t ∈ Subgroup.closure ({t, v} : Set G) ∧
      Subgroup.closure ({t, v} : Set G) ≤ Subgroup.centralizer ({t} : Set G) := by
  have hcomm' : t * v = v * t := hcomm.symm
  have ht2 : t * t = 1 := by simpa [pow_two] using ht
  have hne' : t * v ≠ 1 := by
    intro h
    refine hne ?_
    calc v = t * (t * v) := by rw [← mul_assoc, ht2, one_mul]
      _ = t * 1 := by rw [h]
      _ = t := mul_one t
  refine ⟨⟨card_closure_pair_of_sq_eq_one t v ht hv hcomm' ht1 hv1 hne', ?_⟩, ?_, ?_⟩
  · intro x hx
    rw [mem_closure_pair_of_sq_eq_one (u := t) (v := v) ht hv hcomm'] at hx
    rcases hx with hx | hx | hx | hx
    · rw [hx]; exact one_pow 2
    · rw [hx]; exact ht
    · rw [hx]; exact hv
    · rw [hx, Commute.mul_pow hcomm', ht, hv, one_mul]
  · exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        rfl)
    · exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hcomm.symm)

/-! ## 1. The four-group of Lemma 2.7 -/

/-- **Bender 1981, Lemma 2.7 (p. 221), the four-group step.**  Under the hypotheses of Lemma 2.7
there is a Klein four-group `V ≤ M` with `t ∈ V` and `V ≤ C_G(t)`; equivalently there is an
involution `v ∈ M`, `v ≠ t`, commuting with `t`.

Route: `t` is a 2-element of `M`, so there is `P : Sylow 2 M` with `t ∈ P`; extend `P` to a Sylow
`Q` of `G`.  `Q` is dihedral of order `≥ 4` (`BenderCtx.sylow` together with
`Work.CORE2B.BenderCtx_sylow_not_cyclic`, `Work.RED.DihedralSubgroup` and
`Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic`), so the non-cyclic 2-group `P` is
isomorphic to `DihedralGroup m` for some `m ≥ 2`.  Every `DihedralGroup m` with `m ≥ 2` has at
least three involutions, so there is an involution `v ∈ P ⊆ M` with `v ≠ t`; then `V := ⟨t, v⟩`
is a Klein four-group contained in `M` and in `C_G(t)` (`Work.GW2.IsFourGroup`). -/
theorem L27_fourGroup_in_C_M_t :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), Work.CORE2B.L27Hyp B M →
        ∃ V : Subgroup G, V ≤ M ∧ V ≤ Subgroup.centralizer ({B.t} : Set G) ∧
          Work.GW2.IsFourGroup V ∧ B.t ∈ V := by
  intro G _ _ hctx B M hD
  -- `t` as an element of `M`
  let tM : M := ⟨B.t, hD.t_mem⟩
  have htG2 : B.t ^ 2 = 1 := by
    rw [← B.t_order]
    exact pow_orderOf_eq_one B.t
  have htG1 : B.t ≠ 1 := by
    intro h
    have h2 : orderOf B.t = 1 := by rw [h, orderOf_one]
    rw [B.t_order] at h2
    exact absurd h2 (by norm_num)
  have htM_order : orderOf tM = 2 := by
    rw [← Subgroup.orderOf_coe tM]
    exact B.t_order
  have htM_sq : tM ^ 2 = 1 := by
    rw [← htM_order]
    exact pow_orderOf_eq_one tM
  -- a Sylow 2-subgroup of `M` containing `t`
  obtain ⟨P, htP⟩ : ∃ P : Sylow 2 M, tM ∈ (P : Subgroup M) := by
    have hzp : IsPGroup 2 (Subgroup.zpowers tM) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, htM_order]
      norm_num
    obtain ⟨P, hle⟩ := hzp.exists_le_sylow
    exact ⟨P, hle (Subgroup.mem_zpowers tM)⟩
  let tP : ↥(P : Subgroup M) := ⟨tM, htP⟩
  have htP_sq : tP ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact htM_sq
  have hPnc : ¬ IsCyclic ↥(P : Subgroup M) := hD.sylow_nc P
  -- `P` is cyclic or dihedral, and it is not cyclic
  have hdihM : Work.GW2.DihOrCycSylow ↥M :=
    Work.RED.DihOrCycSubgroup (fun n _ H => Work.RED.DihedralSubgroup n H) M hctx.sylow
  obtain ⟨n, ⟨e⟩⟩ : ∃ n : ℕ, Nonempty (↥(P : Subgroup M) ≃* DihedralGroup n) := by
    rcases hdihM P with h | h
    · exact absurd h hPnc
    · exact h
  have hPp : IsPGroup 2 ↥(P : Subgroup M) := P.isPGroup'
  have hpar := Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic e hPp hPnc
  haveI : NeZero n := hpar.2
  -- an involution of `DihedralGroup n` commuting with `e t` and different from it
  have hz2 : (e tP) ^ 2 = 1 := by
    rw [← map_pow, htP_sq, map_one]
  obtain ⟨u, hu2, hu1, huz, huzc⟩ := L27_dihedral_commuting_involution hpar.1 (e tP) hz2
  -- pull `u` back to `P ≤ M`
  let vP : ↥(P : Subgroup M) := e.symm u
  have hevP : e vP = u := e.apply_symm_apply u
  have hvP_sq : vP ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one, hevP, hu2]
  have hvP_ne : vP ≠ tP := by
    intro h
    exact huz (by rw [← hevP, h])
  have hvP1 : vP ≠ 1 := by
    intro h
    exact hu1 (by rw [← hevP, h, map_one])
  have hvP_comm : vP * tP = tP * vP := by
    apply e.injective
    rw [map_mul, map_mul, hevP, huzc]
  -- the image of `vP` in `G`
  let φ : ↥(P : Subgroup M) →* G := M.subtype.comp (P : Subgroup M).subtype
  have hvG_sq : (φ vP) ^ 2 = 1 := by
    rw [← map_pow, hvP_sq, map_one]
  have hvG_ne : φ vP ≠ B.t := by
    intro h
    exact hvP_ne (Subtype.ext (Subtype.ext h))
  have hvG1 : φ vP ≠ 1 := by
    intro h
    exact hvP1 (Subtype.ext (Subtype.ext h))
  have hvG_comm : φ vP * B.t = B.t * φ vP := by
    have h1 : φ tP = B.t := rfl
    calc φ vP * B.t = φ vP * φ tP := by rw [h1]
      _ = φ (vP * tP) := (map_mul φ vP tP).symm
      _ = φ (tP * vP) := by rw [hvP_comm]
      _ = φ tP * φ vP := map_mul φ tP vP
      _ = B.t * φ vP := by rw [h1]
  -- conclude
  have hF := fourGroup_closure_pair (t := B.t) (v := φ vP) htG2 hvG_sq htG1 hvG1 hvG_ne hvG_comm
  refine ⟨Subgroup.closure ({B.t, φ vP} : Set G), ?_, ?_, hF.1, hF.2.1⟩
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hD.t_mem
    · exact (vP : M).2
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        rfl)
    · exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hvG_comm.symm)

end Work.CORE2B
