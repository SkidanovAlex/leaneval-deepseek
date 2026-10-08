import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.ChV12.prop3
import Submission.Work.PSU3.StageA.Ksub_eq_Kset_of_Hyp5_of_solvable
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.Q0sub_elementary
import Submission.Work.ZassenhausSuzuki.QSZ_abelian_fpf_isCyclic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageA.Ksub_cyclic_caseB`

In case b) of the Proposition of Peterfalvi II Ch. VI §1 (`Q` non-abelian of order `|Q₀|²`,
`orderOf (s*t) = 5`, `W = C_V(K) = ⊥`), **given** that `K = J(D,t) = Kset H t` is a subgroup
(`hKsub`), the subgroup `Ksub H t` is cyclic.

The only facts needed are:

* the involutions of `H` commute (Ch. V §1 Prop. 1 (c), `Work.ThmF.L5.involutions_commute`),
  so that `Q₀sub H` is elementary abelian with `Q₀sub H ∖ {1} = Inv H`
  (`Work.ThmF.ChV12.Q0sub_elementary`);
* `K = J(D,t)` acts **regularly** (sharply transitively) on the involutions `Inv H` of `H`
  (Ch. I §2, `Work.ThmF.L5.Kset_regular`), hence faithfully and fixed-point-freely;
* `K` is abelian, because `t` inverts it.

So `K` is a finite abelian group acting fixed-point-freely (by conjugation) on the nontrivial
finite group `Q₀sub H`; Burnside's theorem on abelian fixed-point-free groups
(`Work.ZassenhausSuzuki.QSZ_abelian_fpf_isCyclic`) then gives that `K` is cyclic.  Neither
Feit–Thompson nor Appendix X is used.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.PSU3.StageA

theorem Ksub_cyclic_caseB {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (h5 : orderOf (s * t) = 5) (hW : Work.ThmF.W H t = ⊥)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hcard : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 2)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t) :
    IsCyclic ↥(Work.ThmF.Ksub H t) := by
  classical
  have hsplit : Submission.Blueprint.IsSplitRankOne H Q t := hS.split
  have hcomm := Work.ThmF.L5.involutions_commute hS.situation hC4 hsplit
  obtain ⟨hQ0sq, hQ0comm, hQ0norm, hQ0inv⟩ := Work.ThmF.ChV12.Q0sub_elementary H hcomm
  have hreg := Work.ThmF.L5.Kset_regular hsplit
  have htinv : t⁻¹ = t := Work.RankOneUniqueness.inv_eq_self hsplit
  -- `K` lies in `H` and normalises `Q₀sub H`
  have hKleH : Work.ThmF.Ksub H t ≤ H := Work.ThmF.ChV12.Ksub_le_H H t
  have hKnorm : ∀ k ∈ Work.ThmF.Ksub H t,
      k ∈ Subgroup.normalizer (Work.ThmF.Q0sub H : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hQ0norm k (hKleH hk) x hx
    · intro hx
      have h1 := hQ0norm k⁻¹ (H.inv_mem (hKleH hk)) (k * x * k⁻¹) hx
      have h2 : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x := by group
      rwa [h2] at h1
  -- the conjugation action of `K` on `Q₀sub H`
  let inc : ↥(Work.ThmF.Ksub H t) →* ↥(Subgroup.normalizer (Work.ThmF.Q0sub H : Set G)) :=
    { toFun := fun k => ⟨(k : G), hKnorm (k : G) k.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  let ρ : ↥(Work.ThmF.Ksub H t) →* MulAut ↥(Work.ThmF.Q0sub H) :=
    (Subgroup.normalizerMonoidHom (Work.ThmF.Q0sub H)).comp inc
  have hρ_apply : ∀ (k : ↥(Work.ThmF.Ksub H t)) (x : ↥(Work.ThmF.Q0sub H)),
      ((ρ k x : ↥(Work.ThmF.Q0sub H)) : G) = (k : G) * (x : G) * (k : G)⁻¹ := fun _ _ => rfl
  -- `t` inverts `K`
  have hKinv : ∀ x ∈ (Work.ThmF.Ksub H t : Set G), t * x * t = x⁻¹ := by
    intro x hx
    have hxKset : x ∈ Work.ThmF.Kset H t := by rw [← hKsub]; exact hx
    have h := (Work.ThmF.mem_Kset_iff.mp hxKset).2
    rwa [htinv] at h
  -- hence `K` is abelian
  haveI : IsMulCommutative ↥(Work.ThmF.Ksub H t) := by
    refine isMulCommutative_iff.mpr (fun a b => Subtype.ext ?_)
    have hab : (a : G) * (b : G) ∈ (Work.ThmF.Ksub H t : Set G) :=
      (Work.ThmF.Ksub H t).mul_mem a.2 b.2
    have h1 : t * ((a : G) * (b : G)) * t = ((a : G) * (b : G))⁻¹ := hKinv _ hab
    have hconj : ∀ x y : G, t * (x * y) * t = (t * x * t) * (t * y * t) := by
      intro x y
      have hm : t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by
        simpa only [MulAut.conj_apply] using map_mul (MulAut.conj t) x y
      simpa only [htinv] using hm
    have h2 : t * ((a : G) * (b : G)) * t = (a : G)⁻¹ * (b : G)⁻¹ := by
      rw [hconj (a : G) (b : G), hKinv (a : G) a.2, hKinv (b : G) b.2]
    have h3 : ((a : G) * (b : G))⁻¹ = ((b : G) * (a : G))⁻¹ := by
      have h4 : (a : G)⁻¹ * (b : G)⁻¹ = ((b : G) * (a : G))⁻¹ := by rw [mul_inv_rev]
      rw [← h1, h2, h4]
    exact inv_injective h3
  -- the action is fixed-point-free: `K` acts regularly on `Inv H = (Q₀sub H) ∖ {1}`
  have hfp : ∀ k : ↥(Work.ThmF.Ksub H t), k ≠ 1 → ∀ x : ↥(Work.ThmF.Q0sub H),
      ρ k x = x → x = 1 := by
    intro k hk x hx
    by_contra hx1
    have hxG : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hxInv : (x : G) ∈ Submission.Blueprint.involutions (H : Set G) :=
      hQ0inv (x : G) x.2 hxG
    have hkKset : (k : G) ∈ Work.ThmF.Kset H t := by
      have h2 : (k : G) ∈ (Work.ThmF.Ksub H t : Set G) := k.2
      rwa [hKsub] at h2
    have hfix : (k : G) * (x : G) * (k : G)⁻¹ = (x : G) := by
      have h := congrArg (fun z : ↥(Work.ThmF.Q0sub H) => (z : G)) hx
      rwa [hρ_apply] at h
    obtain ⟨m, -, huniq⟩ := hreg (x : G) hxInv (x : G) hxInv
    have e1 : (k : G) = m := huniq (k : G) ⟨hkKset, hfix⟩
    have e2 : (1 : G) = m := huniq 1 ⟨Work.ThmF.one_mem_Kset H t, by group⟩
    have hfin : (k : G) = 1 := by rw [e1, ← e2]
    exact hk (Subtype.ext hfin)
  -- `Q₀sub H` is nontrivial (`s` is a non-identity element)
  have hsInv : s ∈ Submission.Blueprint.involutions (H : Set G) := ⟨hsplit.le hs, hs2⟩
  have hsQ0 : s ∈ Work.ThmF.Q0sub H := Work.ThmF.Q0_le_Q0sub H (Or.inl hsInv)
  have hsne : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  haveI : Nontrivial ↥(Work.ThmF.Q0sub H) :=
    (Subgroup.nontrivial_iff_ne_bot (Work.ThmF.Q0sub H)).mpr
      (fun hbot => hsne (Subgroup.mem_bot.mp (hbot ▸ hsQ0)))
  exact Work.ZassenhausSuzuki.QSZ_abelian_fpf_isCyclic ρ hfp

end Work.PSU3.StageA
