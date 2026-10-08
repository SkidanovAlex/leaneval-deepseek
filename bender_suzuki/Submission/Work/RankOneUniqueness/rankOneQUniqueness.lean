import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.RankOneUniqueness.Statements
import Submission.Work.RankOneUniqueness.qPt_injective
import Submission.Work.RankOneUniqueness.qPt_surjective
import Submission.Work.RankOneUniqueness.t_smul_qPt
import Submission.Work.RankOneUniqueness.f_exists
import Submission.Work.RankOneUniqueness.mulEquiv_of_intertwining
import Submission.Work.RankOneUniqueness.closure_Q_t_eq_top

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.RankOneUniqueness.rankOneQUniqueness` — recognition from `(Q, f)` (S4)

Proof of `RankOneQUniquenessProp`: two finite simple groups with split rank-one data whose root
groups are isomorphic by an isomorphism carrying the `f`-relation of the first to that of the
second are isomorphic.

* The action on `Ω = G ⧸ H` is faithful because `G` is simple and `H ≠ ⊤` (the kernel of the
  action lies in `H`).
* The bijection `Φ : Ω ≃ Ω'` is `∞ ↦ ∞'`, `qPt H t x ↦ qPt H' t' (ψ x)`; it is a bijection by
  `qPt_injective`/`qPt_surjective` (which do not use `ψ`).
* `Φ` intertwines the action of `Q` (via `x • qPt y = qPt (xy)`) and that of `t`
  (via `t_smul_qPt` together with the `f`-compatibility hypothesis).
* `⟨Q, t⟩ = ⊤` on both sides (`closure_Q_t_eq_top`), so `mulEquiv_of_intertwining` (S3) applies.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.RankOneUniqueness

theorem rankOneQUniqueness : RankOneQUniquenessProp := by
  intro G G' _ _ _ _ H Q t H' Q' t' hsimple hsimple' hS hS' ψ hψf
  classical
  -- #### 0. faithfulness of the actions, from simplicity
  have hfaith : FaithfulCosets H := by
    intro g hg
    have hker_le : (MulAction.toPermHom G (G ⧸ H)).ker ≤ H := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have h1 : x • pt H = pt H := by
        have h2 := congrArg (fun (p : Equiv.Perm (G ⧸ H)) => p (pt H)) hx
        rw [MulAction.toPermHom_apply, MulAction.toPerm_apply] at h2
        rw [h2]
        simp
      exact (smul_pt_iff H x).mp h1
    have hker_ne : (MulAction.toPermHom G (G ⧸ H)).ker ≠ ⊤ := by
      intro htop
      refine hS.stronglyEmbedded.1 ?_
      rw [← top_le_iff, ← htop]
      exact hker_le
    have hbot : (MulAction.toPermHom G (G ⧸ H)).ker = ⊥ :=
      ((MonoidHom.normal_ker _).eq_bot_or_eq_top).resolve_right hker_ne
    have hmem : g ∈ (MulAction.toPermHom G (G ⧸ H)).ker := by
      rw [MonoidHom.mem_ker]
      ext ω
      exact hg ω
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hfaith' : FaithfulCosets H' := by
    intro g hg
    have hker_le : (MulAction.toPermHom G' (G' ⧸ H')).ker ≤ H' := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have h1 : x • pt H' = pt H' := by
        have h2 := congrArg (fun (p : Equiv.Perm (G' ⧸ H')) => p (pt H')) hx
        rw [MulAction.toPermHom_apply, MulAction.toPerm_apply] at h2
        rw [h2]
        simp
      exact (smul_pt_iff H' x).mp h1
    have hker_ne : (MulAction.toPermHom G' (G' ⧸ H')).ker ≠ ⊤ := by
      intro htop
      refine hS'.stronglyEmbedded.1 ?_
      rw [← top_le_iff, ← htop]
      exact hker_le
    have hbot : (MulAction.toPermHom G' (G' ⧸ H')).ker = ⊥ :=
      ((MonoidHom.normal_ker _).eq_bot_or_eq_top).resolve_right hker_ne
    have hmem : g ∈ (MulAction.toPermHom G' (G' ⧸ H')).ker := by
      rw [MonoidHom.mem_ker]
      ext ω
      exact hg ω
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  -- #### 1. the bijection `Φ : Ω ≃ Ω'`
  let invQ : ∀ ω : G ⧸ H, ω ≠ pt H → G := fun ω hω => Classical.choose (qPt_surjective hS hω)
  have invQ_mem : ∀ (ω : G ⧸ H) (hω : ω ≠ pt H), invQ ω hω ∈ Q :=
    fun ω hω => (Classical.choose_spec (qPt_surjective hS hω)).1
  have invQ_spec : ∀ (ω : G ⧸ H) (hω : ω ≠ pt H), qPt H t (invQ ω hω) = ω :=
    fun ω hω => (Classical.choose_spec (qPt_surjective hS hω)).2
  have invQ_eq : ∀ (x : G) (hx : x ∈ Q),
      (⟨invQ (qPt H t x) (qPt_ne_pt hS hx), invQ_mem (qPt H t x) (qPt_ne_pt hS hx)⟩ : Q)
        = ⟨x, hx⟩ := by
    intro x hx
    apply Subtype.ext
    exact qPt_injective hS (invQ_mem (qPt H t x) (qPt_ne_pt hS hx)) hx
      (invQ_spec (qPt H t x) (qPt_ne_pt hS hx))
  let Φfun : (G ⧸ H) → (G' ⧸ H') := fun ω =>
    if hω : ω = pt H then pt H'
    else qPt H' t' (((ψ ⟨invQ ω hω, invQ_mem ω hω⟩ : Q') : G'))
  have Φfun_pt : Φfun (pt H) = pt H' := by
    dsimp only [Φfun]
    rw [dite_eq_left rfl]
  have Φfun_neq : ∀ (ω : G ⧸ H) (hω : ω ≠ pt H),
      Φfun ω = qPt H' t' (((ψ ⟨invQ ω hω, invQ_mem ω hω⟩ : Q') : G')) := by
    intro ω hω
    dsimp only [Φfun]
    rw [dite_eq_right hω]
  have Φfun_qPt : ∀ (x : G) (hx : x ∈ Q),
      Φfun (qPt H t x) = qPt H' t' (((ψ ⟨x, hx⟩ : Q') : G')) := by
    intro x hx
    rw [Φfun_neq _ (qPt_ne_pt hS hx), invQ_eq x hx]
  have hinj : Function.Injective Φfun := by
    intro ω ω' heq
    by_cases hω : ω = pt H
    · subst hω
      by_cases hω' : ω' = pt H
      · rw [hω']
      · exfalso
        have h1 : Φfun ω' ≠ pt H' := by
          rw [Φfun_neq ω' hω']
          exact qPt_ne_pt hS' (ψ ⟨invQ ω' hω', invQ_mem ω' hω'⟩).2
        exact h1 (heq.symm.trans Φfun_pt)
    · by_cases hω' : ω' = pt H
      · exfalso
        have h1 : Φfun ω ≠ pt H' := by
          rw [Φfun_neq ω hω]
          exact qPt_ne_pt hS' (ψ ⟨invQ ω hω, invQ_mem ω hω⟩).2
        exact h1 (by rw [heq, hω', Φfun_pt])
      · rw [← invQ_spec ω hω, ← invQ_spec ω' hω'] at heq
        rw [Φfun_qPt (invQ ω hω) (invQ_mem ω hω),
          Φfun_qPt (invQ ω' hω') (invQ_mem ω' hω')] at heq
        have h3 : (ψ ⟨invQ ω hω, invQ_mem ω hω⟩ : Q')
            = ψ ⟨invQ ω' hω', invQ_mem ω' hω'⟩ :=
          Subtype.ext (qPt_injective hS' (ψ ⟨invQ ω hω, invQ_mem ω hω⟩).2
            (ψ ⟨invQ ω' hω', invQ_mem ω' hω'⟩).2 heq)
        have h4 : invQ ω hω = invQ ω' hω' := congrArg Subtype.val (ψ.injective h3)
        rw [← invQ_spec ω hω, ← invQ_spec ω' hω', h4]
  have hsurj : Function.Surjective Φfun := by
    intro ω'
    by_cases hω' : ω' = pt H'
    · exact ⟨pt H, by rw [Φfun_pt, hω']⟩
    · obtain ⟨x', hx', hx'eq⟩ := qPt_surjective hS' hω'
      refine ⟨qPt H t ((ψ.symm ⟨x', hx'⟩ : Q) : G), ?_⟩
      rw [Φfun_qPt _ (ψ.symm ⟨x', hx'⟩).2]
      have h1 : (⟨((ψ.symm ⟨x', hx'⟩ : Q) : G), (ψ.symm ⟨x', hx'⟩).2⟩ : Q)
          = ψ.symm ⟨x', hx'⟩ := Subtype.ext rfl
      rw [h1, MulEquiv.apply_symm_apply, ← hx'eq]
  let Φ : (G ⧸ H) ≃ (G' ⧸ H') := Equiv.ofBijective Φfun ⟨hinj, hsurj⟩
  have Φ_apply : ∀ ω : G ⧸ H, Φ ω = Φfun ω := fun ω => Equiv.ofBijective_apply Φfun _ ω
  -- #### 2. `Φ` intertwines the action of `Q`
  have ΦQ : ∀ (q : Q) (ω : G ⧸ H), Φ ((q : G) • ω) = ((ψ q : Q') : G') • Φ ω := by
    intro q ω
    by_cases hω : ω = pt H
    · subst hω
      rw [smul_pt_of_mem H (hS.le q.2), Φ_apply, Φfun_pt]
      exact (smul_pt_of_mem H' (hS'.le (ψ q).2)).symm
    · have hx : invQ ω hω ∈ Q := invQ_mem ω hω
      have hsm : (q : G) • qPt H t (invQ ω hω) = qPt H t ((q : G) * invQ ω hω) := by
        rw [qPt_def, qPt_def, smul_mk, mul_assoc]
      have hsm' : ((ψ q : Q') : G') • qPt H' t' (((ψ ⟨invQ ω hω, hx⟩ : Q') : G'))
          = qPt H' t' (((ψ q : Q') : G') * ((ψ ⟨invQ ω hω, hx⟩ : Q') : G')) := by
        rw [qPt_def, smul_mk, qPt_def, mul_assoc]
      rw [← invQ_spec ω hω, hsm, Φ_apply, Φ_apply,
        Φfun_qPt ((q : G) * invQ ω hω) (Q.mul_mem q.2 hx), Φfun_qPt (invQ ω hω) hx, hsm']
      congr 1
      rw [show (⟨(q : G) * invQ ω hω, Q.mul_mem q.2 hx⟩ : Q) = q * ⟨invQ ω hω, hx⟩
            from Subtype.ext (by rw [Subgroup.coe_mul]),
        map_mul, Subgroup.coe_mul]
  -- #### 3. `Φ` intertwines the action of `t`
  have Φt : ∀ ω : G ⧸ H, Φ (t • ω) = t' • Φ ω := by
    intro ω
    by_cases hω : ω = pt H
    · subst hω
      have h0 : t • pt H = qPt H t (1 : G) := by
        rw [qPt_def, smul_pt, one_mul]
      have h1 : (⟨(1 : G), Q.one_mem⟩ : Q) = 1 := Subtype.ext rfl
      rw [h0, Φ_apply, Φfun_qPt (1 : G) Q.one_mem, Φ_apply, Φfun_pt, h1, map_one,
        Subgroup.coe_one, qPt_def, one_mul, pt_def, smul_mk, mul_one]
    · have hx : invQ ω hω ∈ Q := invQ_mem ω hω
      by_cases hx1 : (⟨invQ ω hω, hx⟩ : Q) = 1
      · have hx1G : invQ ω hω = 1 := Subtype.ext_iff.mp hx1
        have h0 : t • qPt H t (invQ ω hω) = pt H := by
          show t • qPt H t (((⟨invQ ω hω, hx⟩ : Q) : G)) = pt H
          rw [hx1, qPt_def, Subgroup.coe_one, smul_mk, one_mul, mul_self_eq_one hS]
          rfl
        have h2 : t' • qPt H' t' ((ψ ⟨invQ ω hω, hx⟩ : Q') : G') = pt H' := by
          rw [hx1, map_one, Subgroup.coe_one]
          rw [show qPt H' t' (1 : G') = ((t' : G') : G' ⧸ H') from by rw [qPt_def, one_mul]]
          rw [smul_mk, mul_self_eq_one hS']
          rfl
        rw [← invQ_spec ω hω, h0, Φ_apply, Φfun_pt, Φ_apply, Φfun_qPt (invQ ω hω) hx, h2]
      · have hx1G : invQ ω hω ≠ 1 := fun h => hx1 (Subtype.ext h)
        have hx1' : (invQ ω hω)⁻¹ ≠ 1 := fun h => hx1G (inv_eq_one.mp h)
        obtain ⟨y, hy, m, hm, hcanon⟩ := f_exists hS (Q.inv_mem hx) hx1'
        have h1 : t • qPt H t (invQ ω hω) = qPt H t (y⁻¹) :=
          t_smul_qPt hS hx hx1G hm hy hcanon
        obtain ⟨m', hm', hcanon'⟩ :=
          hψf ⟨invQ ω hω, hx⟩⁻¹ ⟨y, hy⟩ (by simpa using hx1')
            ⟨m, hm, by simpa using hcanon⟩
        have hc : t' * (((ψ ⟨invQ ω hω, hx⟩ : Q') : G'))⁻¹ * t'
            = m' * t' * (((ψ ⟨y, hy⟩ : Q') : G')) := by
          have h2 := hcanon'
          rw [map_inv, Subgroup.coe_inv] at h2
          exact h2
        have hx'1 : ((ψ ⟨invQ ω hω, hx⟩ : Q') : G') ≠ 1 := by
          intro h
          have h2 : ψ ⟨invQ ω hω, hx⟩ = (1 : Q') :=
            Subtype.ext (by rw [Subgroup.coe_one]; exact h)
          exact hx1 (ψ.injective (by rw [h2, map_one]))
        have h2' : t' • qPt H' t' ((ψ ⟨invQ ω hω, hx⟩ : Q') : G')
            = qPt H' t' (((ψ ⟨y, hy⟩ : Q') : G')⁻¹) :=
          t_smul_qPt hS' (ψ ⟨invQ ω hω, hx⟩).2 hx'1 hm' (ψ ⟨y, hy⟩).2 hc
        have hyinv : (ψ ⟨y⁻¹, Q.inv_mem hy⟩ : Q') = (ψ ⟨y, hy⟩)⁻¹ := by
          have h := MulEquiv.map_inv ψ ⟨y, hy⟩
          rwa [show (⟨y, hy⟩ : Q)⁻¹ = ⟨y⁻¹, Q.inv_mem hy⟩ from
            Subtype.ext (by rw [Subgroup.coe_inv])] at h
        rw [← invQ_spec ω hω, h1, Φ_apply, Φfun_qPt (y⁻¹) (Q.inv_mem hy), Φ_apply,
          Φfun_qPt (invQ ω hω) hx, h2', hyinv, Subgroup.coe_inv]
  -- #### 4. assemble and apply S3
  let S : Set G := (Q : Set G) ∪ {t}
  let S' : Set G' := (Q' : Set G') ∪ {t'}
  have htQ : t ∉ (Q : Set G) := fun hx => hS.not_mem (hS.le hx)
  have htQ' : t' ∉ (Q' : Set G') := fun hx => hS'.not_mem (hS'.le hx)
  let σ₀ : G → G' := fun x =>
    if hx : x ∈ (Q : Set G) then ((ψ ⟨x, hx⟩ : Q') : G') else t'
  have hσ₀_mem : ∀ x ∈ S, σ₀ x ∈ S' := by
    intro x hx
    by_cases hxq : x ∈ (Q : Set G)
    · have h1 : σ₀ x = ((ψ ⟨x, hxq⟩ : Q') : G') := by
        dsimp only [σ₀]
        rw [dite_eq_left hxq]
      rw [h1]
      exact Or.inl (ψ ⟨x, hxq⟩).2
    · have hxt : x = t := by
        rcases hx with h | h
        · exact absurd h hxq
        · exact h
      have h1 : σ₀ t = t' := by
        dsimp only [σ₀]
        rw [dite_eq_right htQ]
      rw [hxt, h1]
      exact Or.inr rfl
  have hσ₀_inj : Set.InjOn σ₀ S := by
    intro x hx y hy hxy
    by_cases hxq : x ∈ (Q : Set G)
    · by_cases hyq : y ∈ (Q : Set G)
      · have hx' : σ₀ x = ((ψ ⟨x, hxq⟩ : Q') : G') := by
          dsimp only [σ₀]
          rw [dite_eq_left hxq]
        have hy' : σ₀ y = ((ψ ⟨y, hyq⟩ : Q') : G') := by
          dsimp only [σ₀]
          rw [dite_eq_left hyq]
        rw [hx', hy'] at hxy
        exact congrArg Subtype.val (ψ.injective (Subtype.ext hxy))
      · have hyt : y = t := by
          rcases hy with h | h
          · exact absurd h hyq
          · exact h
        exfalso
        have h2 : σ₀ y = t' := by
          rw [hyt]
          dsimp only [σ₀]
          rw [dite_eq_right htQ]
        have hx' : σ₀ x = ((ψ ⟨x, hxq⟩ : Q') : G') := by
          dsimp only [σ₀]
          rw [dite_eq_left hxq]
        have h3 : ((ψ ⟨x, hxq⟩ : Q') : G') = t' := by rw [← hx', hxy, h2]
        exact hS'.not_mem (hS'.le (h3 ▸ (ψ ⟨x, hxq⟩).2))
    · have hxt : x = t := by
        rcases hx with h | h
        · exact absurd h hxq
        · exact h
      by_cases hyq : y ∈ (Q : Set G)
      · exfalso
        have h2 : σ₀ x = t' := by
          rw [hxt]
          dsimp only [σ₀]
          rw [dite_eq_right htQ]
        have hy' : σ₀ y = ((ψ ⟨y, hyq⟩ : Q') : G') := by
          dsimp only [σ₀]
          rw [dite_eq_left hyq]
        have h3 : ((ψ ⟨y, hyq⟩ : Q') : G') = t' := by rw [← hy', ← hxy, h2]
        exact hS'.not_mem (hS'.le (h3 ▸ (ψ ⟨y, hyq⟩).2))
      · have hyt : y = t := by
          rcases hy with h | h
          · exact absurd h hyq
          · exact h
        rw [hxt, hyt]
  have hσ₀_image : σ₀ '' S = S' := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro y ⟨x, hx, rfl⟩
      exact hσ₀_mem x hx
    · intro y hy
      rcases hy with hy | hy
      · refine ⟨((ψ.symm ⟨y, hy⟩ : Q) : G), Or.inl (ψ.symm ⟨y, hy⟩).2, ?_⟩
        have h1 : σ₀ (((ψ.symm ⟨y, hy⟩ : Q) : G))
            = ((ψ ⟨((ψ.symm ⟨y, hy⟩ : Q) : G), (ψ.symm ⟨y, hy⟩).2⟩ : Q') : G') := by
          dsimp only [σ₀]
          split_ifs with h
          · exact congrArg (fun z : Q => ((ψ z : Q') : G')) (Subtype.ext rfl)
          · exact absurd (ψ.symm ⟨y, hy⟩).2 h
        rw [h1]
        have h2 : (⟨((ψ.symm ⟨y, hy⟩ : Q) : G), (ψ.symm ⟨y, hy⟩).2⟩ : Q)
            = ψ.symm ⟨y, hy⟩ := Subtype.ext rfl
        rw [h2, MulEquiv.apply_symm_apply]
      · have hyt : y = t' := hy
        have h1 : σ₀ t = t' := by
          dsimp only [σ₀]
          rw [dite_eq_right htQ]
        exact ⟨t, Or.inr rfl, by rw [hyt, h1]⟩
  let σ : S ≃ (σ₀ '' S) := Equiv.Set.imageOfInjOn σ₀ S hσ₀_inj
  have hgen' : Subgroup.closure (σ₀ '' S) = ⊤ := by
    rw [hσ₀_image]
    exact closure_Q_t_eq_top hS'
  have hσ : ∀ (s : S) (ω : G ⧸ H),
      Φ ((s : G) • ω) = (((σ s : σ₀ '' S) : G')) • Φ ω := by
    intro s ω
    rcases s.2 with hs | hs
    · have h1 : ((σ s : σ₀ '' S) : G') = ((ψ ⟨(s : G), hs⟩ : Q') : G') := by
        show σ₀ (s : G) = ((ψ ⟨(s : G), hs⟩ : Q') : G')
        dsimp only [σ₀]
        rw [dite_eq_left hs]
      rw [h1]
      exact ΦQ ⟨(s : G), hs⟩ ω
    · have hst : (s : G) = t := hs
      have h1 : ((σ s : σ₀ '' S) : G') = t' := by
        show σ₀ (s : G) = t'
        rw [hst]
        dsimp only [σ₀]
        rw [dite_eq_right htQ]
      rw [hst, h1]
      exact Φt ω
  exact mulEquiv_of_intertwining Φ S (σ₀ '' S) σ hfaith hfaith' (closure_Q_t_eq_top hS) hgen' hσ

/-- `RankOneQUniquenessProp` in the project's `FeitThompsonProp`-carrying convention (the
hypothesis is inert: the proof is group-theoretic). -/
theorem rankOneQUniquenessFT (_hFT : Submission.Blueprint.FeitThompsonProp) :
    RankOneQUniquenessProp := rankOneQUniqueness

end Work.RankOneUniqueness
