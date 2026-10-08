import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.ThetaOmegaAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness
open Classical

namespace Work.PSU3.StageB.Omega

open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

theorem fcan_mul_eq_qconj {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (h5 : ∀ {ω : ↥Q}, (ω : G) ∉ fr.Q0 → ∀ {y : ↥Q}, (y : G) ∈ fr.Q0 →
      ∀ {a : ↥(Submission.Blueprint.twoPoint H t)},
      Work.PSU3.StageB.fcan hS.split ω = Work.PSU3.StageB.qconj hS.split a (ω * y) →
        (a : G) ∉ Work.ThmF.Ksub H t)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {x y : ↥Q} (hx : (x : G) ∈ fr.Q0) (hx1 : x ≠ 1)
    (hy : (y : G) ∈ fr.Q0) {a : ↥(Submission.Blueprint.twoPoint H t)}
    (h : Work.PSU3.StageB.fcan hS.split (ω * x) =
      Work.PSU3.StageB.qconj hS.split a (Work.PSU3.StageB.fcan hS.split ω * y)) :
    (a : G) ∉ Work.ThmF.Ksub H t := by
  -- ## Step 1: write `x = zcQF fr u`, `u ∈ F*`
  obtain ⟨v, hv, hvz⟩ := fr.zc_surj (x : G) hx
  have hv0 : v ≠ 0 := by
    intro hc
    refine hx1 (Subtype.ext ?_)
    rw [← hvz, hc, zc_zero fr]
    simp
  set u : ↥(FX n) := mkFX v hv hv0 with hu
  have hxu : zcQF fr u = x := by
    apply Subtype.ext
    show fr.zc (fval u) = (x : G)
    rw [hu, fval_mkFX]
    exact hvz
  -- ## Step 2: side conditions for the recursion §2 (2)
  have hω1 : (ω : G) ≠ 1 := fun hc => hω (by rw [hc]; exact Q0_one_mem fr)
  have hωx1 : ((ω * zcQF fr u : ↥Q) : G) ≠ 1 := by
    rw [hxu]
    intro hc
    have hmem : ((ω * x : ↥Q) : G) ∈ fr.Q0 := by rw [hc]; exact Q0_one_mem fr
    have h2 : (ω : G) = ((ω * x : ↥Q) : G) * (x : G)⁻¹ := by
      rw [Subgroup.coe_mul]; group
    exact hω (by rw [h2]; exact fr.Q0.mul_mem hmem (fr.Q0.inv_mem hx))
  -- ## Step 3: the recursion §2 (2) and the hypothesis, in `G`-form
  have hrec := fcan_mul_zcQF hS fr (x := ω) hω1 u hωx1
  have hhyp : (fcan hS.split (ω * zcQF fr u) : G) =
      (a : G)⁻¹ * (fcan hS.split ω : G) * (y : G) * (a : G) := by
    rw [hxu]
    have hh := congrArg (fun z : ↥Q => (z : G)) h
    simpa only [qconj_coe, Subgroup.coe_mul, mul_assoc] using hh
  -- abbreviations for the group elements occurring in the two relations
  set B : G := t * (hcan hS.split (zcQF fr u) : G) * t with hB
  set F : G := (fcan hS.split ω : G) with hF
  set W : G := (fcan hS.split (fcan hS.split ω * zcQF fr u⁻¹) : G) with hW
  set K : G := (zcQF fr u⁻¹ : G) with hK
  have h1 : B⁻¹ * W * B * K = (a : G)⁻¹ * F * (y : G) * (a : G) := hrec.symm.trans hhyp
  -- solve for `W`: the `f`-value of `ω' = f(ω)·(zc u⁻¹)`
  have key : W = B * (a : G)⁻¹ * F * (y : G) * (a : G) * K⁻¹ * B⁻¹ := by
    have h2 : B⁻¹ * W * B = (a : G)⁻¹ * F * (y : G) * (a : G) * K⁻¹ := by
      rw [← h1]; group
    calc W = B * (B⁻¹ * W * B) * B⁻¹ := by group
      _ = B * ((a : G)⁻¹ * F * (y : G) * (a : G) * K⁻¹) * B⁻¹ := by rw [h2]
      _ = B * (a : G)⁻¹ * F * (y : G) * (a : G) * K⁻¹ * B⁻¹ := by group
  -- ## Step 4: the `K`-bookkeeping: `B = t h(x) t ∈ Ksub`
  have hKmem : K ∈ fr.Q0 := by
    rw [hK]
    show fr.zc (fval u⁻¹) ∈ fr.Q0
    exact fr.zc_mem _ (by rw [fval_inv, map_inv₀, u.2])
  have hhcan : (hcan hS.split (zcQF fr u) : G) ∈ Ksub H t := by
    have hc := (canon_zcQF_coe fr hS u).2.2
    rw [hc]
    exact (Ksub H t).mul_mem (kElF_mem_Ksub fr (tau hS fr u))
      (kElF_mem_Ksub fr (tau hS fr u))
  have hBmem : B ∈ Ksub H t := by
    rw [hB, tconj_eq_inv hS.split fr hhcan]
    exact (Ksub H t).inv_mem hhcan
  have hBD : B ∈ twoPoint H t := fr.KW_le (fr.K_le hBmem)
  have hbD : (a : G) * B⁻¹ ∈ twoPoint H t :=
    (twoPoint H t).mul_mem a.2 ((twoPoint H t).inv_mem hBD)
  -- ## Step 5: the new configuration of type (5)
  set ω' : ↥Q := fcan hS.split ω * zcQF fr u⁻¹ with hω'def
  set y'Q : ↥Q :=
    ⟨K⁻¹ * (y : G) * ((a : G) * K⁻¹ * (a : G)⁻¹), fr.Q0_le (by
      refine fr.Q0.mul_mem (fr.Q0.mul_mem (fr.Q0.inv_mem hKmem) hy) ?_
      exact conj_mem_Q0_of_mem_D hS fr a.2 (fr.Q0.inv_mem hKmem))⟩ with hy'Qdef
  have hω' : (ω' : G) ∉ fr.Q0 := by
    have hFQ : ((fcan hS.split ω : ↥Q) : G) ∉ fr.Q0 :=
      fun hc => hω ((fcan_mem_Q0_iff hS fr ω).mp hc)
    intro hc
    have h2 : ((fcan hS.split ω : ↥Q) : G) = (ω' : G) * K⁻¹ := by
      rw [hω'def, hK]
      simp only [Subgroup.coe_mul]
      group
    exact hFQ (by rw [h2]; exact fr.Q0.mul_mem hc (fr.Q0.inv_mem hKmem))
  have hy'Q : (y'Q : G) ∈ fr.Q0 := by
    rw [hy'Qdef]
    exact fr.Q0.mul_mem (fr.Q0.mul_mem (fr.Q0.inv_mem hKmem) hy)
      (conj_mem_Q0_of_mem_D hS fr a.2 (fr.Q0.inv_mem hKmem))
  have heq : fcan hS.split ω' = qconj hS.split ⟨(a : G) * B⁻¹, hbD⟩ (ω' * y'Q) := by
    apply Subtype.ext
    have hL : (fcan hS.split ω' : G) = W := hW.symm
    rw [hL, key, qconj_coe, Subgroup.coe_mul]
    have h1c : ((⟨(a : G) * B⁻¹, hbD⟩ : ↥(twoPoint H t)) : G) = (a : G) * B⁻¹ := rfl
    have h2c : ((ω' : ↥Q) : G) = F * K := by
      rw [hω'def, hF, hK]
      simp only [Subgroup.coe_mul]
    have h3c : ((y'Q : ↥Q) : G) = K⁻¹ * (y : G) * ((a : G) * K⁻¹ * (a : G)⁻¹) := by
      rw [hy'Qdef]
    rw [h1c, h2c, h3c]
    group
  -- ## Step 6: hypothesis (5) and the conclusion
  have hb : ((⟨(a : G) * B⁻¹, hbD⟩ : ↥(twoPoint H t)) : G) ∉ Ksub H t :=
    h5 hω' hy'Q heq
  intro ha
  exact hb ((Ksub H t).mul_mem ha ((Ksub H t).inv_mem hBmem))

end Work.PSU3.StageB.Omega
