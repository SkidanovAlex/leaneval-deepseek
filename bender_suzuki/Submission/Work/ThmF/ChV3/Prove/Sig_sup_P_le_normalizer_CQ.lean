import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.Sig_sup_P_le_normalizer_CQ`

Peterfalvi II Ch. V §3: `Σ ⊔ P ≤ N_G(C_Q(P))`, where `Σ = C_W(P) = W ∩ C_G(P)` and
`C_Q(P) = Q ∩ C_G(P)`.

The proof only uses the standing context `CtxF` (no extra chain data).  The join is handled
through the conjugation action:

* `Σ = W ∩ C_G(P) ≤ C_G(P)`, and `Σ ≤ W ≤ V = C_D(t) ≤ D ≤ H`, while `H ≤ N_G(Q)`
  (`IsSplitRankOne.normal`).  So `Σ ≤ C_G(P) ∩ N_G(Q)`.
* `P ≤ V = C_D(t) ≤ D ≤ H ≤ N_G(Q)`, and `P` normalises its own centraliser `C_G(P)`
  (see `normalizer_le_normalizer_centralizer`).  So `P ≤ C_G(P) ∩ N_G(Q)`.

Finally `N_G(A) ∩ N_G(B) ≤ N_G(A ∩ B)`, and `C_Q(P) = Q ∩ C_G(P)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF.ChV3.Prove

/-- If `x` normalises `A` and `y` centralises `A`, then `x * y * x⁻¹` centralises `A`. -/
theorem conj_mem_centralizer {G : Type*} [Group G] {A : Subgroup G} {x y : G}
    (hx : x ∈ Subgroup.normalizer (A : Set G))
    (hy : y ∈ Subgroup.centralizer (A : Set G)) :
    x * y * x⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro a ha
  have hxinv : x⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normalizer (A : Set G)).inv_mem hx
  have hb : x⁻¹ * a * x ∈ A := by
    simpa using (Subgroup.mem_normalizer_iff.mp hxinv a).mp ha
  have hcomm := hy (x⁻¹ * a * x) hb
  calc a * (x * y * x⁻¹)
      = x * ((x⁻¹ * a * x) * y) * x⁻¹ := by group
    _ = x * (y * (x⁻¹ * a * x)) * x⁻¹ := by rw [hcomm]
    _ = (x * y * x⁻¹) * a := by group

/-- `N_G(A) ≤ N_G(C_G(A))`: an element normalising `A` normalises the centraliser of `A`. -/
theorem normalizer_le_normalizer_centralizer {G : Type*} [Group G] {A : Subgroup G} :
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact conj_mem_centralizer hx
  · intro hy
    have hxinv : x⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normalizer (A : Set G)).inv_mem hx
    have h := conj_mem_centralizer hxinv hy
    have h2 : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
    rwa [h2] at h

/-- `N_G(A) ∩ N_G(B) ≤ N_G(A ∩ B)`. -/
theorem inf_normalizer_le_normalizer_inf {G : Type*} [Group G] {A B : Subgroup G} :
    Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (B : Set G) ≤
      Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx y hy
  obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hyA, hyB⟩ := Subgroup.mem_inf.mp hy
  exact Subgroup.mem_inf.mpr
    ⟨(Subgroup.mem_normalizer_iff.mp hxA y).mp hyA,
     (Subgroup.mem_normalizer_iff.mp hxB y).mp hyB⟩

theorem Sig_sup_P_le_normalizer_CQ {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (c : Work.ThmF.ChV3.CtxF H Q t s r P) :
    Work.ThmF.ChV3.Sig H t P ⊔ P ≤ Subgroup.normalizer (Work.ThmF.ChV3.CQ Q P : Set G) := by
  -- `Σ = W ∩ C_G(P)` sits in `W ≤ V ≤ D ≤ H`, and `H ≤ N_G(Q)`.
  have hSig_le_W : Work.ThmF.ChV3.Sig H t P ≤ Work.ThmF.W H t := inf_le_left
  have hSig_le_centD : Work.ThmF.ChV3.Sig H t P ≤ centD H t :=
    hSig_le_W.trans (Work.ThmF.W_le_centD H t)
  have hSig_le_D : Work.ThmF.ChV3.Sig H t P ≤ twoPoint H t :=
    hSig_le_centD.trans (Work.ThmF.centD_le_twoPoint t)
  have hSig_le_H : Work.ThmF.ChV3.Sig H t P ≤ H :=
    hSig_le_D.trans (Work.Models.twoPoint_le_left H t)
  -- `P ≤ V = C_D(t) ≤ D ≤ H`.
  have hP_le_H : P ≤ H :=
    c.P_le.trans ((Work.ThmF.centD_le_twoPoint t).trans (Work.Models.twoPoint_le_left H t))
  -- `Σ ≤ C_G(P)` is the second factor of the defining intersection.
  have hSig_le_C : Work.ThmF.ChV3.Sig H t P ≤ Subgroup.centralizer (P : Set G) := inf_le_right
  -- Both `Σ` and `P` normalise `Q` and `C_G(P)`.
  have hSig_le_NQ : Work.ThmF.ChV3.Sig H t P ≤ Subgroup.normalizer (Q : Set G) :=
    hSig_le_H.trans c.split.normal
  have hSig_le_NC : Work.ThmF.ChV3.Sig H t P ≤
      Subgroup.normalizer (Subgroup.centralizer (P : Set G) : Set G) :=
    hSig_le_C.trans Subgroup.le_normalizer
  have hP_le_NQ : P ≤ Subgroup.normalizer (Q : Set G) := hP_le_H.trans c.split.normal
  have hP_le_NC : P ≤ Subgroup.normalizer (Subgroup.centralizer (P : Set G) : Set G) :=
    Subgroup.le_normalizer.trans normalizer_le_normalizer_centralizer
  -- Assemble: `Σ ⊔ P ≤ N_G(Q) ∩ N_G(C_G(P)) ≤ N_G(Q ∩ C_G(P)) = N_G(C_Q(P))`.
  exact (sup_le (le_inf hSig_le_NQ hSig_le_NC) (le_inf hP_le_NQ hP_le_NC)).trans
    inf_normalizer_le_normalizer_inf

end Work.ThmF.ChV3.Prove
