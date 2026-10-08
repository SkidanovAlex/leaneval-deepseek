/-
# Ch. III §4: the order of `V = centD H t`

We prove, from the intermediate conclusions of §4 Lemma 1 (d) (`Lemma1dConc`), Prop. 1
(`Prop1Conc`) and Prop. 2 (a) (`Prop2aConc`), the dimension count of `V = C_D(t)`:

`|V| = |E' ⊓ V| · p · |C_A(P)|`,

where `E' = Ecomm H t W = ⁅E,E⁆`, `E = Egrp H t W = W ⊓ D`, `D = twoPoint H t`, and
`C_A(P) = A ⊓ C_G(P)`.

The mathematics: by `Setup45A`, `V = A ⋊ P` with `|P| = p`, so `|V| = |A| · p`.  Prop. 1
(step 6) gives that `[A,P]` is a complement of `C_A(P)` in `A`, i.e. `|A| = |[A,P]| · |C_A(P)|`;
Prop. 2 (a) identifies `[A,P]` with `E' ⊓ V`.  Formally the complement statement is recovered
from the two hypotheses

* `IsNormalComplementOf ((⟨K⟩ ⊔ [A,P]) ⊔ P) C_A(P) D` (the last clause of `Prop1Conc`), and
* `E' = ⟨K⟩ ⊔ [A,P]` (a clause of `Prop2aConc`),

as follows.  Write `N = (⟨K⟩ ⊔ [A,P]) ⊔ P = E' ⊔ P` (the last equality is `Prop2aConc`); then
`N = E = Egrp H t W` (`Prop2aConc` again) and `D = N ⊔ C_A(P)` with `N ⊓ C_A(P) = ⊥` and
`N ⊴ D`.  Since `A ⊴ V` (`Setup45A.A_normal`), `A ⊓ P = ⊥` and `A ⊔ P = V`, and since
`A ⊓ N = [A,P]` (an element of `A ⊓ N = A ⊓ (E' ⊔ P)` is `y·q` with `y ∈ E'`, `q ∈ P`; then
`y = x·q⁻¹ ∈ V`, so `y ∈ E' ⊓ V = [A,P]` by `Prop2aConc`, and `q ∈ A ⊓ P = 1`), the modular
identity `A = (A ⊓ N) ⊔ C_A(P) = [A,P] ⊔ C_A(P)` holds, with `[A,P] ⊓ C_A(P) ≤ N ⊓ C_A(P) = ⊥`.
Counting with `card_sup_mul_card_inf` finishes.
-/
import Mathlib
import Submission.Work.NormalComplement.NC4.Defs
import Submission.Work.NormalComplement.appI_one
import Submission.Work.NormalComplement.sec2_one
import Submission.Work.NormalComplement.appI_five_d_corrected
import Submission.Work.NormalComplement.card_sup_mul_card_inf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.NormalComplement.Design

namespace Work.NormalComplement.NC4

theorem card_centD {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G} {W : Subgroup G}
    {p : ℕ} {P A : Subgroup G}
    (h : Work.NormalComplement.Design.Setup45A G H t W p P A)
    (h1d : Work.NormalComplement.NC4.Lemma1dConc H t W p P A)
    (hP1 : Work.NormalComplement.NC4.Prop1Conc H t W p P A)
    (h2a : Work.NormalComplement.NC4.Prop2aConc H t W p P A) :
    Nat.card ↥(Submission.Blueprint.centD H t) =
      Nat.card ↥(Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t) * p *
        Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) := by
  -- local abbreviations (`let`, so that all the statements below are definitionally equal
  -- to the goal and to the hypotheses)
  let V : Subgroup G := Submission.Blueprint.centD H t
  let E' : Subgroup G := Work.NormalComplement.Design.Ecomm H t W
  let C : Subgroup G := A ⊓ Subgroup.centralizer (P : Set G)
  let M : Subgroup G := Work.NormalComplement.Design.commSub A P
  let N : Subgroup G := (Work.NormalComplement.Kgrp (twoPoint H t) t ⊔
    Work.NormalComplement.Design.commSub A P) ⊔ P
  -- ## elementary consequences of the hypotheses
  have hA_le_V : A ≤ V := h.A_le
  have hP_le_V : P ≤ V := h.P_le.trans inf_le_right
  have hV_le_D : V ≤ twoPoint H t := inf_le_left
  have hP_norm_A : P ≤ Subgroup.normalizer (A : Set G) := hP_le_V.trans h.A_normal
  have hAsup : A ⊔ P = V := h.A_sup
  have hAinf : A ⊓ P = ⊥ := h.A_inf
  have hPcard : Nat.card ↥P = p := h.P_card
  have hE'supP : E' ⊔ P = Egrp H t W := h1d.2.2
  have hE'infP : E' ⊓ P = ⊥ := h1d.2.1
  have hE'eq : E' = Work.NormalComplement.Kgrp (twoPoint H t) t ⊔
      Work.NormalComplement.Design.commSub A P := h2a.2.1
  have hE'V : E' ⊓ V = M := h2a.2.2
  have hNeq : N = Egrp H t W := h2a.1.symm
  have hNC : IsNormalComplementOf N C (twoPoint H t) := hP1.2.2.2
  have hN_le_D : N ≤ twoPoint H t := hNC.1
  have hD_le_NGN : twoPoint H t ≤ Subgroup.normalizer (N : Set G) := hNC.2.1
  have hNinfC : N ⊓ C = ⊥ := hNC.2.2.1
  have hNsupC : N ⊔ C = twoPoint H t := hNC.2.2.2
  have hC_le_A : C ≤ A := inf_le_left
  have hC_le_cent : C ≤ Subgroup.centralizer (P : Set G) := inf_le_right
  have hC_le_V : C ≤ V := hC_le_A.trans hA_le_V
  have hC_le_D : C ≤ twoPoint H t := hC_le_V.trans hV_le_D
  have hC_norm_N : C ≤ Subgroup.normalizer (N : Set G) := hC_le_D.trans hD_le_NGN
  have hP_le_E : P ≤ Egrp H t W := by rw [← hE'supP]; exact le_sup_right
  -- ## `M = [A,P] ≤ A`, `M ≤ N`
  have hM_le_A : M ≤ A := Subgroup.le_normalizer_iff_commutator_le_left.mp hP_norm_A
  have hM_le_N : M ≤ N := by
    show Work.NormalComplement.Design.commSub A P ≤
      (Work.NormalComplement.Kgrp (twoPoint H t) t ⊔
        Work.NormalComplement.Design.commSub A P) ⊔ P
    exact le_trans le_sup_right le_sup_left
  -- ## `E'` is normalised by `E ⊇ P`
  have hE'_norm : Egrp H t W ≤ Subgroup.normalizer (E' : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator]
    have h1 : Subgroup.map (MulAut.conj e) (Egrp H t W) = Egrp H t W :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer he)
    rw [h1]
  have hP_le_NG_E' : P ≤ Subgroup.normalizer (E' : Set G) := hP_le_E.trans hE'_norm
  -- ## `C` normalises `M`
  have hC_norm_M : C ≤ Subgroup.normalizer (M : Set G) := by
    intro c hc
    have hMeq : M = ⁅A, P⁆ := rfl
    rw [hMeq, Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator]
    have h1 : Subgroup.map (MulAut.conj c) A = A :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (hC_le_A hc))
    have h2 : Subgroup.map (MulAut.conj c) P = P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.centralizer_le_normalizer (P : Set G) (hC_le_cent hc))
    rw [h1, h2]
  -- ## `A ⊓ N = M`
  have hA_inf_N : A ⊓ N = M := by
    refine le_antisymm ?_ (le_inf hM_le_A hM_le_N)
    intro x hx
    obtain ⟨hxA, hxN⟩ := Subgroup.mem_inf.mp hx
    have hxE'P : x ∈ E' ⊔ P := by
      have hx1 : x ∈ (Work.NormalComplement.Kgrp (twoPoint H t) t ⊔
          Work.NormalComplement.Design.commSub A P) ⊔ P := hxN
      rwa [← hE'eq] at hx1
    obtain ⟨y, hy, q, hq, hxq⟩ := (Work.NormalComplement.mem_sup_mul hP_le_NG_E').mp hxE'P
    have hyV : y ∈ V := by
      have hyy : y = x * q⁻¹ := by rw [hxq]; group
      rw [hyy]
      exact V.mul_mem (hA_le_V hxA) (V.inv_mem (hP_le_V hq))
    have hyM : y ∈ M := by
      have hmem : y ∈ E' ⊓ V := Subgroup.mem_inf.mpr ⟨hy, hyV⟩
      rwa [hE'V] at hmem
    have hqA : q ∈ A := by
      have hqq : q = y⁻¹ * x := by rw [hxq]; group
      rw [hqq]
      exact A.mul_mem (A.inv_mem (hM_le_A hyM)) hxA
    have hqbot : q = 1 := by
      have hmem : q ∈ A ⊓ P := Subgroup.mem_inf.mpr ⟨hqA, hq⟩
      rwa [hAinf] at hmem
    rw [hxq, hqbot, mul_one]
    exact hyM
  -- ## `A = M ⊔ C`
  have hA_eq : A = M ⊔ C := by
    refine le_antisymm ?_ (sup_le hM_le_A hC_le_A)
    intro a ha
    have haNC : a ∈ N ⊔ C := by
      rw [hNsupC]
      exact hV_le_D (hA_le_V ha)
    obtain ⟨n, hn, c, hc, hanc⟩ := (Work.NormalComplement.mem_sup_mul hC_norm_N).mp haNC
    have hnA : n ∈ A := by
      have hnn : n = a * c⁻¹ := by rw [hanc]; group
      rw [hnn]
      exact A.mul_mem ha (A.inv_mem (hC_le_A hc))
    have hnM : n ∈ M := by
      have hmem : n ∈ A ⊓ N := Subgroup.mem_inf.mpr ⟨hnA, hn⟩
      rwa [hA_inf_N] at hmem
    exact (Work.NormalComplement.mem_sup_mul hC_norm_M).mpr ⟨n, hnM, c, hc, hanc⟩
  -- ## `M ⊓ C = ⊥`
  have hMinfC : M ⊓ C = ⊥ := by
    have h2 : M ⊓ C ≤ N ⊓ C := le_inf (inf_le_left.trans hM_le_N) inf_le_right
    rw [hNinfC] at h2
    exact le_bot_iff.mp h2
  -- ## counting
  have hcardA : Nat.card ↥A = Nat.card ↥M * Nat.card ↥C := by
    have h1 := Work.NormalComplement.card_sup_mul_card_inf (H := M) (K := C) hC_norm_M
    rw [hMinfC, Subgroup.card_bot, mul_one, ← hA_eq] at h1
    exact h1
  have hcardV : Nat.card ↥V = Nat.card ↥A * p := by
    have h1 := Work.NormalComplement.card_sup_mul_card_inf (H := A) (K := P) hP_norm_A
    rw [hAsup, hAinf, Subgroup.card_bot, mul_one, hPcard] at h1
    exact h1
  calc Nat.card ↥(Submission.Blueprint.centD H t) = Nat.card ↥V := rfl
    _ = Nat.card ↥A * p := hcardV
    _ = (Nat.card ↥M * Nat.card ↥C) * p := by rw [← hcardA]
    _ = Nat.card ↥M * p * Nat.card ↥C := by ring
    _ = Nat.card ↥(E' ⊓ V) * p * Nat.card ↥C := by rw [← hE'V]

end Work.NormalComplement.NC4
