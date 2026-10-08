import Mathlib
import Submission.Work.ZJB.Step1.Defs
import Submission.Work.ZJB2.Step1.claimAProp
import Submission.Work.ZJB2.Step1.zsLeZJProp
import Submission.Work.ZJB2.Step1.dltProp
import Submission.Work.ZJB2.Step1.thompsonJEqOfLeProp
import Submission.Work.ZJB2.Step1.memSupIffOfCommute
import Submission.Work.ZJB2.Step1.ltNormalizerInfOfLt

/-!
# ZJB2, step (I), leaf I.3: `Z(S₁) ≤ D` and an `a ∈ N(D) ∩ S₁` with `Z(S)^a ⊄ Z(J)`

This file proves `Work.ZJB.ExistsAProp p G`, the leaf **I.3** of step (I) of Glauberman's
Theorem 5.1(a) (Glauberman 1968, p. 1118).  In the notation of
`Submission/Work/ZJB/Step1/Defs.lean`:

* `S` is a Sylow `p`-subgroup and `S₁` is a *bad* Sylow `p`-subgroup of maximal `|D|`
  (`Work.ZJB.MaxBad p S S₁`): `Z(S) ≤ S₁` but `Z(S) ⊄ Z(J(S₁))`;
* `D = Dsub S S₁ = N_G(J(S)) ⊓ S₁` and `J = J(S)`.

The statement is the conjunction

* `Z(S₁) ≤ D`, and
* there is `a ∈ N_G(D) ⊓ S₁` with `Z(S)^a ⊄ Z(J(S))`.

Both halves are instances of **Claim A** (I.2, `Work.ZJB2.Step1.claimAProp`), which says that a
subgroup `A` with `D ≤ A ≤ N_G(D) ⊓ S₁` on which `a ↦ pconj (Z(S)) a` stays inside `Z(J(S))`
must equal `D`.

## First half: `Z(S₁) ≤ D`

Take `A = Z(S₁) ⊔ D` (the paper's `Z(S₁)·D`).  Then

* `D ≤ A ≤ N_G(D) ⊓ S₁`: `Z(S₁) ≤ C_G(S₁) ≤ C_G(D) ≤ N_G(D)` because `D ≤ S₁`;
* every element of `A` is of the form `x * y` with `x ∈ Z(S₁)`, `y ∈ D`
  (`Work.ZJB2.Step1.memSupIffOfCommute`, applicable because `Z(S₁) ≤ C_G(S₁)` commutes
  elementwise with `D ≤ S₁`), and then
  `pconj (Z(S)) (x*y) = pconj (pconj (Z(S)) x) y = pconj (Z(S)) y ≤ Z(J(S))`, since `x`
  centralises `Z(S) ≤ S₁` and `y ∈ N_G(J(S))` normalises `Z(J(S))`.

Claim A then gives `A = D`, hence `Z(S₁) ≤ A = D`.

## Second half: an `a ∈ N_G(D) ∩ S₁` with `Z(S)^a ⊄ Z(J)`

`D ≠ S₁` because `S₁ ⊄ N_G(J(S))` (leaf I.1, `Work.ZJB2.Step1.dltProp`), so `D` is a *proper*
subgroup of the `p`-group `S₁`; by the normalizer condition for finite `p`-groups
(`Work.ZJB2.Step1.ltNormalizerInfOfLt`), `D` is a proper subgroup of
`N_G(D) ⊓ S₁ = N_{S₁}(D)`.  If `Z(S)^a ≤ Z(J(S))` held for every `a` in the (larger) subgroup
`N_G(D) ⊓ S₁`, Claim A would force `N_G(D) ⊓ S₁ = D`, a contradiction.

## Auxiliary lemmas

`pconj_mul`, `pconj_eq_self_of_mem_normalizer`, `pconj_eq_self_of_mem_centralizer`,
`pconj_ZJ_le_of_mem_normalizer_thompsonJ` and `pconj_ZS_le_ZJ_of_mem_normalizer` are the
elementary `pconj`-calculus used above; `memSupIffOfCommute` and `ltNormalizerInfOfLt` are the
two general facts, proved in the sibling files of the same directory.
-/

namespace Work.ZJB2.Step1

open Work.ZJB
open Subgroup

variable {G : Type*} [Group G]

/-- `pconj` is an action: `X^(a*b) = (X^a)^b` in the paper's convention `X^g = g⁻¹Xg`. -/
private theorem pconj_mul (X : Subgroup G) (a b : G) : pconj X (a * b) = pconj (pconj X a) b := by
  ext x
  rw [mem_pconj, mem_pconj, mem_pconj]
  constructor <;> intro h <;> (convert h using 1; group)

/-- An element of `N_G(X)` fixes `X` under `pconj`. -/
private theorem pconj_eq_self_of_mem_normalizer {X : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (X : Set G)) : pconj X a = X := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [mem_pconj] at hx
    exact (Subgroup.mem_normalizer_iff.mp ha x).2 hx
  · intro x hx
    rw [mem_pconj]
    exact (Subgroup.mem_normalizer_iff.mp ha x).1 hx

/-- An element centralising `X` fixes `X` under `pconj`. -/
private theorem pconj_eq_self_of_mem_centralizer {X : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.centralizer (X : Set G)) : pconj X a = X :=
  pconj_eq_self_of_mem_normalizer (Subgroup.centralizer_le_normalizer (X : Set G) ha)

/-- `N_G(J(P))` normalises `Z(J(P))`: conjugation by `a ∈ N_G(J(P))` maps `J(P)` to itself,
hence `Z(J(P)) = J(P) ⊓ C_G(J(P))` to itself (`Z(J(-))` is characteristic in `J(-)`). -/
private theorem pconj_ZJ_le_of_mem_normalizer_thompsonJ [Finite G] (P : Subgroup G) {a : G}
    (ha : a ∈ Subgroup.normalizer (Work.GW2.thompsonJ P : Set G)) :
    pconj (Work.GW2.ZJ P) a ≤ Work.GW2.ZJ P := by
  have hJ : (Work.GW2.thompsonJ P).map (MulAut.conj a⁻¹).toMonoidHom =
      Work.GW2.thompsonJ P := by
    have ha' : a⁻¹ ∈ Subgroup.normalizer (Work.GW2.thompsonJ P : Set G) :=
      (Subgroup.normalizer (Work.GW2.thompsonJ P : Set G)).inv_mem ha
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact (Subgroup.mem_normalizer_iff.mp ha' y).1 hy
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨a * x * a⁻¹, (Subgroup.mem_normalizer_iff.mp ha x).1 hx, ?_⟩
      show (MulAut.conj a⁻¹).toMonoidHom (a * x * a⁻¹) = x
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hC : (Subgroup.centralizer (Work.GW2.thompsonJ P : Set G)).map
      (MulAut.conj a⁻¹).toMonoidHom ≤ Subgroup.centralizer (Work.GW2.thompsonJ P : Set G) := by
    have h := Subgroup.map_centralizer_le_centralizer_image
      (s := (Work.GW2.thompsonJ P : Set G)) (f := (MulAut.conj a⁻¹).toMonoidHom)
    rw [← Subgroup.coe_map (f := (MulAut.conj a⁻¹).toMonoidHom)
      (K := Work.GW2.thompsonJ P)] at h
    rw [hJ] at h
    exact h
  show (Work.GW2.ZJ P).map (MulAut.conj a⁻¹).toMonoidHom ≤ Work.GW2.ZJ P
  rw [Work.GW2.ZJ]
  rw [Subgroup.map_inf (Work.GW2.thompsonJ P)
    (Subgroup.centralizer (Work.GW2.thompsonJ P : Set G))
    (MulAut.conj a⁻¹).toMonoidHom (MulAut.conj a⁻¹).injective]
  rw [hJ]
  exact inf_le_inf_left _ hC

/-- `Z(P)^a ≤ Z(J(P))` for `a ∈ N_G(J(P))`: the conjugates of `Z(P)` lie in `Z(J(P))`
(F0 along with `Z(J(P))` being normalised by `N_G(J(P))`). -/
private theorem pconj_ZS_le_ZJ_of_mem_normalizer [Finite G] (P : Subgroup G) {a : G}
    (ha : a ∈ Subgroup.normalizer (Work.GW2.thompsonJ P : Set G)) :
    pconj (ZS P) a ≤ Work.GW2.ZJ P :=
  (pconj_mono (zs_le_zj P) a).trans (pconj_ZJ_le_of_mem_normalizer_thompsonJ P ha)

/-- **I.3.** `Z(S₁) ≤ D = N_G(J(S)) ⊓ S₁`, and some `a ∈ N_G(D) ⊓ S₁` has
`Z(S)^a ⊄ Z(J(S))`. -/
theorem existsAProp {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    Work.ZJB.ExistsAProp p G := by
  intro S S₁ hMB
  obtain ⟨hZ_S₁, hbad, hmax⟩ := hMB
  -- (I.1): `S₁ ⊄ N_G(J(S))`
  have hS₁_not_le_NJ : ¬ (S₁ : Subgroup G) ≤
      Subgroup.normalizer (Work.GW2.thompsonJ (S : Subgroup G) : Set G) :=
    dltProp (p := p) (G := G) S S₁ hZ_S₁ hbad
  -- hence `D ⊊ S₁`
  have hD_ne : Work.ZJB.Dsub S S₁ ≠ (S₁ : Subgroup G) := by
    intro h
    refine hS₁_not_le_NJ ?_
    rw [← h]
    exact inf_le_left
  have hD_le_S₁ : Work.ZJB.Dsub S S₁ ≤ (S₁ : Subgroup G) := inf_le_right
  have hD_lt_S₁ : Work.ZJB.Dsub S S₁ < (S₁ : Subgroup G) :=
    lt_of_le_of_ne hD_le_S₁ hD_ne
  refine ⟨?_, ?_⟩
  · -- **First conjunct**: `Z(S₁) ≤ D`, by Claim A applied to `A = Z(S₁) ⊔ D`.
    -- `Z(S₁)` commutes elementwise with `D ≤ S₁`.
    have hc : ∀ x ∈ Work.ZJB.ZS (S₁ : Subgroup G), ∀ y ∈ Work.ZJB.Dsub S S₁,
        x * y = y * x := by
      intro x hx y hy
      have hxC : x ∈ Subgroup.centralizer (S₁ : Set G) := (Subgroup.mem_inf.mp hx).1
      exact ((Subgroup.mem_centralizer_iff.mp hxC) y (hD_le_S₁ hy)).symm
    -- `D ≤ Z(S₁) ⊔ D ≤ N_G(D) ⊓ S₁`
    have hA_le : Work.ZJB.ZS (S₁ : Subgroup G) ⊔ Work.ZJB.Dsub S S₁ ≤
        Subgroup.normalizer (Work.ZJB.Dsub S S₁ : Set G) ⊓ (S₁ : Subgroup G) := by
      refine le_inf ?_ ?_
      · refine sup_le ?_ Subgroup.le_normalizer
        exact inf_le_left.trans ((Subgroup.centralizer_le inf_le_right).trans
          (Subgroup.centralizer_le_normalizer (Work.ZJB.Dsub S S₁ : Set G)))
      · exact sup_le inf_le_right inf_le_right
    -- `Z(S)^a ≤ Z(J(S))` for every `a ∈ Z(S₁) ⊔ D`
    have hP : ∀ a ∈ Work.ZJB.ZS (S₁ : Subgroup G) ⊔ Work.ZJB.Dsub S S₁,
        pconj (Work.ZJB.ZS (S : Subgroup G)) a ≤ Work.GW2.ZJ (S : Subgroup G) := by
      intro a ha
      obtain ⟨x, hx, y, hy, rfl⟩ := (memSupIffOfCommute hc).mp ha
      have hxcent : x ∈ Subgroup.centralizer (Work.ZJB.ZS (S : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro m hm
        exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).1) m (hZ_S₁ hm)
      rw [pconj_mul, pconj_eq_self_of_mem_centralizer hxcent]
      exact pconj_ZS_le_ZJ_of_mem_normalizer (S : Subgroup G) (Subgroup.mem_inf.mp hy).1
    have hAeq := claimAProp (p := p) (G := G) S S₁ ⟨hZ_S₁, hbad, hmax⟩
      (Work.ZJB.ZS (S₁ : Subgroup G) ⊔ Work.ZJB.Dsub S S₁) le_sup_right hA_le hP
    exact le_sup_left.trans (le_of_eq hAeq)
  · -- **Second conjunct**: `N_G(D) ⊓ S₁` is strictly bigger than `D`, so Claim A with
    -- `A = N_G(D) ⊓ S₁` produces the required `a`.
    have hD_lt_A : Work.ZJB.Dsub S S₁ <
        Subgroup.normalizer (Work.ZJB.Dsub S S₁ : Set G) ⊓ (S₁ : Subgroup G) :=
      ltNormalizerInfOfLt (p := p) (P := (S₁ : Subgroup G)) S₁.isPGroup' hD_lt_S₁
    by_cases hex : ∃ a ∈ Subgroup.normalizer (Work.ZJB.Dsub S S₁ : Set G) ⊓ (S₁ : Subgroup G),
        ¬ pconj (Work.ZJB.ZS (S : Subgroup G)) a ≤ Work.GW2.ZJ (S : Subgroup G)
    · exact hex
    · exfalso
      have hP : ∀ a ∈ Subgroup.normalizer (Work.ZJB.Dsub S S₁ : Set G) ⊓ (S₁ : Subgroup G),
          pconj (Work.ZJB.ZS (S : Subgroup G)) a ≤ Work.GW2.ZJ (S : Subgroup G) := by
        intro a ha
        by_contra hcon
        exact hex ⟨a, ha, hcon⟩
      have heq := claimAProp (p := p) (G := G) S S₁ ⟨hZ_S₁, hbad, hmax⟩
        (Subgroup.normalizer (Work.ZJB.Dsub S S₁ : Set G) ⊓ (S₁ : Subgroup G))
        (le_inf Subgroup.le_normalizer inf_le_right) le_rfl hP
      exact (ne_of_lt hD_lt_A) heq.symm

end Work.ZJB2.Step1
