import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.RankOneUniqueness.exists_smul_t_eq
import Submission.Work.RankOneUniqueness.qPt_injective
import Submission.Work.RankOneUniqueness.qPt_surjective
import Submission.Work.RankOneUniqueness.smul_qPt
import Submission.Work.RankOneUniqueness.t_smul_qPt
import Submission.Work.RankOneUniqueness.conj_notMem
import Submission.Work.RankOneUniqueness.canon_unique
import Submission.Work.RankOneUniqueness.canon_exists
import Submission.Work.RankOneUniqueness.f_exists
import Submission.Work.RankOneUniqueness.f_unique
import Submission.Work.RankOneUniqueness.gen_top
import Submission.Work.RankOneUniqueness.mulEquiv_of_permEquiv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.RankOneUniqueness.rankOneUniqueness` — the area theorem

Peterfalvi II, Ch. VII §1 (Lemma p. 268), in the form of
`Submission.Blueprint.RankOneUniquenessProp`: a split rank-one group `G` acting faithfully
on `Ω = G ⧸ H` is determined up to isomorphism by the data of `H = Q ⋊ D` and of the
`f`-map (`t x t = m t y`) on `Q#`.

The isomorphism is built as follows.  Write `Ω = {∞} ⊔ Q` by `x ↦ qPt H t x = x t H` and
likewise for the primed group; the isomorphism `ψ : H ≃* H'` transports `Q` to `Q'`, and
the bijection `Φ : Ω ≃ Ω'` is `∞ ↦ ∞'`, `qPt H t x ↦ qPt H' t' ψ(x)`.  Then `Φ` transports
the `H`-action (via `smul_qPt` and the factorisation `H = Q·D`) and the `t`-action: for
`x ≠ 1` the canonical form of `t x⁻¹ t` is transported by the `f`-compatibility hypothesis,
whence `Φ (t • qPt H t x) = t' • Φ (qPt H t x)`.  Since `G = ⟨H, t⟩` (`gen_top`) and the
actions are faithful, `mulEquiv_of_permEquiv` yields `G ≃* G'`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.RankOneUniqueness

theorem rankOneUniqueness : Submission.Blueprint.RankOneUniquenessProp := by
  intro G G' _ _ _ _ H Q t H' Q' t' hS hS' hfaith hfaith' ψ hψQ hψD hψf
  classical
  -- #### 1. coordinates on `Ω ∖ {∞}` and the map `Φ`
  let invQ : ∀ ω : G ⧸ H, ω ≠ pt H → G := fun ω hω => Classical.choose (qPt_surjective hS hω)
  have invQ_mem : ∀ (ω : G ⧸ H) (hω : ω ≠ pt H), invQ ω hω ∈ Q :=
    fun ω hω => (Classical.choose_spec (qPt_surjective hS hω)).1
  have invQ_spec : ∀ (ω : G ⧸ H) (hω : ω ≠ pt H), qPt H t (invQ ω hω) = ω :=
    fun ω hω => (Classical.choose_spec (qPt_surjective hS hω)).2
  let invQH : ∀ ω : G ⧸ H, ω ≠ pt H → H := fun ω hω => ⟨invQ ω hω, hS.le (invQ_mem ω hω)⟩
  have invQH_eq : ∀ (x : G) (hx : x ∈ Q),
      invQH (qPt H t x) (qPt_ne_pt hS hx) = ⟨x, hS.le hx⟩ := by
    intro x hx
    apply Subtype.ext
    exact qPt_injective hS (invQ_mem (qPt H t x) (qPt_ne_pt hS hx)) hx
      (invQ_spec (qPt H t x) (qPt_ne_pt hS hx))
  let Φfun : (G ⧸ H) → (G' ⧸ H') := fun ω =>
    if hω : ω = pt H then pt H' else qPt H' t' (ψ (invQH ω hω))
  have Φfun_pt : Φfun (pt H) = pt H' := by
    dsimp only [Φfun]
    rw [dite_eq_left rfl]
  have Φfun_neq : ∀ (ω : G ⧸ H) (hω : ω ≠ pt H), Φfun ω = qPt H' t' (ψ (invQH ω hω)) := by
    intro ω hω
    dsimp only [Φfun]
    rw [dite_eq_right hω]
  have Φfun_qPt : ∀ (x : G) (hx : x ∈ Q),
      Φfun (qPt H t x) = qPt H' t' (ψ ⟨x, hS.le hx⟩) := by
    intro x hx
    rw [Φfun_neq _ (qPt_ne_pt hS hx), invQH_eq x hx]
  -- #### 2. `Φ` is a bijection
  have hinj : Function.Injective Φfun := by
    intro ω ω' heq
    by_cases hω : ω = pt H
    · subst hω
      by_cases hω' : ω' = pt H
      · rw [hω']
      · exfalso
        have h1 : Φfun ω' ≠ pt H' := by
          rw [Φfun_neq ω' hω']
          exact qPt_ne_pt hS' ((hψQ (invQH ω' hω')).mp (invQ_mem ω' hω'))
        exact h1 (heq.symm.trans Φfun_pt)
    · by_cases hω' : ω' = pt H
      · exfalso
        have h1 : Φfun ω ≠ pt H' := by
          rw [Φfun_neq ω hω]
          exact qPt_ne_pt hS' ((hψQ (invQH ω hω)).mp (invQ_mem ω hω))
        exact h1 (by rw [heq, hω', Φfun_pt])
      · rw [← invQ_spec ω hω, ← invQ_spec ω' hω'] at heq
        rw [Φfun_qPt (invQ ω hω) (invQ_mem ω hω),
          Φfun_qPt (invQ ω' hω') (invQ_mem ω' hω')] at heq
        have h3 : (ψ (invQH ω hω) : G') = (ψ (invQH ω' hω') : G') :=
          qPt_injective hS' ((hψQ (invQH ω hω)).mp (invQ_mem ω hω))
            ((hψQ (invQH ω' hω')).mp (invQ_mem ω' hω')) heq
        have h4 : invQ ω hω = invQ ω' hω' :=
          congrArg Subtype.val (ψ.injective (Subtype.ext h3))
        rw [← invQ_spec ω hω, ← invQ_spec ω' hω', h4]
  have hsurj : Function.Surjective Φfun := by
    intro ω'
    by_cases hω' : ω' = pt H'
    · exact ⟨pt H, by rw [Φfun_pt, hω']⟩
    · obtain ⟨x', hx', hx'eq⟩ := qPt_surjective hS' hω'
      let xH : H := ψ.symm ⟨x', hS'.le hx'⟩
      have hxHmem : (xH : G) ∈ Q :=
        (hψQ xH).mpr (by rw [MulEquiv.apply_symm_apply]; exact hx')
      refine ⟨qPt H t (xH : G), ?_⟩
      rw [Φfun_qPt (xH : G) hxHmem]
      have hxHeq : (⟨(xH : G), hS.le hxHmem⟩ : H) = xH := Subtype.ext rfl
      rw [hxHeq, MulEquiv.apply_symm_apply, ← hx'eq]
  let Φ : (G ⧸ H) ≃ (G' ⧸ H') := Equiv.ofBijective Φfun ⟨hinj, hsurj⟩
  have Φ_apply : ∀ ω : G ⧸ H, Φ ω = Φfun ω := fun ω => Equiv.ofBijective_apply Φfun _ ω
  -- #### 3. `Φ` transports the action of `H`
  have ΦH : ∀ (a : H) (ω : G ⧸ H), Φ ((a : G) • ω) = (ψ a : G') • Φ ω := by
    intro a ω
    by_cases hω : ω = pt H
    · subst hω
      rw [smul_pt_of_mem H a.2, Φ_apply, Φfun_pt]
      exact (smul_pt_of_mem H' (ψ a).2).symm
    · let xH : H := invQH ω hω
      have hx : invQ ω hω ∈ Q := invQ_mem ω hω
      obtain ⟨z, hz, d, hd, hfac⟩ :=
        fact_exists hS (a := (a : G) * invQ ω hω) (H.mul_mem a.2 (hS.le hx))
      let zH : H := ⟨z, hS.le hz⟩
      let dH : H := ⟨d, (mem_twoPoint_iff.mp hd).1⟩
      have hsmul1 : (a : G) • qPt H t (invQ ω hω) = qPt H t z :=
        smul_qPt hS a.2 hx hz hd hfac
      obtain ⟨z', hz', d', hd', hfac'⟩ :=
        fact_exists hS' (a := (ψ a : G') * (ψ xH : G'))
          (H'.mul_mem (ψ a).2 (hS'.le ((hψQ xH).mp hx)))
      have htrans : (ψ zH : G') * (ψ dH : G') = (ψ a : G') * (ψ xH : G') := by
        have h1 : a * xH = zH * dH := by
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_mul]
          exact hfac
        have h2 : ψ (a * xH) = ψ zH * ψ dH := by rw [h1, map_mul]
        have h3 := congrArg (fun w : H' => (w : G')) h2
        simpa only [Subgroup.coe_mul, map_mul] using h3.symm
      have hdD' : (ψ dH : G') ∈ twoPoint H' t' := (hψD dH).mp hd
      have hzd : z' * d' = (ψ zH : G') * (ψ dH : G') := by rw [← hfac', htrans]
      have hze : z' = (ψ zH : G') :=
        (fact_unique hS' hz' ((hψQ zH).mp hz) hd' hdD' hzd).1
      rw [← invQ_spec ω hω, Φ_apply, Φ_apply, hsmul1, Φfun_qPt z hz,
        Φfun_qPt (invQ ω hω) hx, smul_qPt hS' (ψ a).2 ((hψQ xH).mp hx) hz' hd' hfac',
        ← hze]
  -- #### 4. `Φ` transports the action of `t`
  have Φt : ∀ ω : G ⧸ H, Φ (t • ω) = t' • Φ ω := by
    intro ω
    by_cases hω : ω = pt H
    · subst hω
      have h0 : t • pt H = qPt H t (1 : G) := by
        rw [qPt_def, smul_pt, one_mul]
      have h1 : (⟨(1 : G), hS.le Q.one_mem⟩ : H) = 1 := Subtype.ext rfl
      rw [h0, Φ_apply, Φfun_qPt (1 : G) Q.one_mem, Φ_apply, Φfun_pt, h1, map_one,
        Subgroup.coe_one, qPt_def, one_mul, pt_def, smul_mk, mul_one]
    · let xH : H := invQH ω hω
      have hx : invQ ω hω ∈ Q := invQ_mem ω hω
      by_cases hx1 : (xH : G) = 1
      · have hxH1 : xH = 1 := Subtype.ext hx1
        have h0 : t • qPt H t (xH : G) = pt H := by
          rw [hxH1, qPt_def, Subgroup.coe_one, smul_mk, one_mul, mul_self_eq_one hS]
          rfl
        have hxH1' : (⟨invQ ω hω, hS.le hx⟩ : H) = 1 := by
          apply Subtype.ext
          rw [Subgroup.coe_one]
          exact hx1
        rw [← invQ_spec ω hω, h0, Φ_apply, Φfun_pt, Φ_apply, Φfun_qPt (invQ ω hω) hx,
          hxH1', map_one, Subgroup.coe_one, qPt_def, one_mul, pt_def, smul_mk,
          mul_self_eq_one hS']
      · have hx1' : ((xH : G))⁻¹ ≠ 1 := fun h => hx1 (inv_eq_one.mp h)
        obtain ⟨m, hm, y, hy, hcanon⟩ :=
          canon_exists hS (conj_notMem hS (Q.inv_mem hx) hx1')
        let yH : H := ⟨y, hS.le hy⟩
        have h1 : t • qPt H t (invQ ω hω) = qPt H t (y⁻¹) :=
          t_smul_qPt hS hx hx1 hm hy hcanon
        obtain ⟨m', hm', hcanon'⟩ := hψf (xH⁻¹) yH
          (by simpa using Q.inv_mem hx) (by simpa using hy) (by simpa using hx1')
          ⟨m, hm, by simpa using hcanon⟩
        have hc' : t' * ((ψ xH : G'))⁻¹ * t' = m' * t' * (ψ yH : G') := by
          have h2 := hcanon'
          rw [map_inv, Subgroup.coe_inv] at h2
          exact h2
        have hx'1 : (ψ xH : G') ≠ 1 := by
          intro h
          apply hx1
          have h3 : ψ xH = (1 : H') := by
            apply Subtype.ext
            rw [Subgroup.coe_one]
            exact h
          have h4 := congrArg (fun w : H' => ((ψ.symm w : H) : G)) h3
          simpa using h4
        have h2' : t' • qPt H' t' (ψ xH : G') = qPt H' t' ((ψ yH : G')⁻¹) :=
          t_smul_qPt hS' ((hψQ xH).mp hx) hx'1 hm' ((hψQ yH).mp hy) hc'
        have h5 : (ψ yH : G')⁻¹ = (ψ (yH⁻¹) : G') := by
          rw [map_inv, Subgroup.coe_inv]
        have h6 : (⟨y⁻¹, hS.le (Q.inv_mem hy)⟩ : H) = yH⁻¹ :=
          Subtype.ext (by rw [Subgroup.coe_inv])
        rw [← invQ_spec ω hω, h1, Φ_apply, Φfun_qPt (y⁻¹) (Q.inv_mem hy), Φ_apply,
          Φfun_qPt (invQ ω hω) hx, h2', h5, h6]
  -- #### 5. the isomorphism
  exact mulEquiv_of_permEquiv Φ ψ hfaith hfaith' (gen_top hS) (gen_top hS') ΦH Φt

end Work.RankOneUniqueness
