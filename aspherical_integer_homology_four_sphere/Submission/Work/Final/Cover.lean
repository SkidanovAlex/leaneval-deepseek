/-
# `Final/`: the Mayer–Vietoris long exact sequence of an open cover

`Work.Final.coverMVLES` is the Mayer–Vietoris long exact sequence

```
⋯ → H_k(U ∩ V) → H_k(U) ⊞ H_k(V) → H_k(C^{U,V}) → H_{k-1}(U ∩ V) → ⋯
```

of an open cover `U ∪ V = X`, in the index convention of `Work.HomologyMV.MVLES`
(`(k,0) = H_k(U ∩ V)`, `(k,1) = H_k(U) ⊞ H_k(V)`, `(k,2) = H_k(C^{U,V})`, the homology of the
*specific* chain complex `Work.Cohomology.smallChains U V`, which `Work.Cohomology.smallIso`
identifies with the singular homology of `X`).

The mathematical input is `Work.Cohomology.mv_H_exact₁/₂/₃` together with the one node that the
library does not provide, the degree-`0` exactness
`Work.Final.MVExactDegreeZero` (surjectivity of the degree-`0` Mayer–Vietoris map, delegated and
proved in `Submission/Work/Final/mvRightX_zero_surjective.lean`).  The bookkeeping is the cyclic
index `Work.HomologyMV.mvSucc`: `(k,2) ↦ (k-1,0)` lowers the degree, the terms in negative degrees
are the zero module, and a few `eqToHom`s align the library's index `n` with the index `k.toNat` of
the sequence.

## Main results

* `Work.Final.coverMVLES` — the long exact sequence;
* `Work.Final.coverMVLES_H_zero/one/two` — its terms are `HInter`, `HBiprod`, `HSmall`
  (definitional, for `k ≥ 0`);
* `Work.Final.coverMVLES_hX` — the `(k,2)`-slot is the singular homology of `X`;
* `Work.Final.coverD_exact` — exactness at every node.
-/
import Submission.Work.Final.Framework
import Submission.Work.HomologyMV.Basic
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Homology.MayerVietoris

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology
open scoped Topology

namespace Work.Final

noncomputable section

variable {X : TopCat}

/-! ## §1  Three transfer lemmas for `Function.Exact` -/

theorem functionExact_comp_surjective {A A' B C : ModuleCat ℤ} (u : A' ⟶ A) (f : A ⟶ B)
    (g : B ⟶ C) (hu : Function.Surjective u) (h : Function.Exact f g) :
    Function.Exact (u ≫ f) g := by
  intro y
  rw [h y]
  refine ⟨fun ⟨a, ha⟩ => ?_, fun ⟨a, ha⟩ => ?_⟩
  · obtain ⟨a', rfl⟩ := hu a
    exact ⟨a', by simpa [CategoryTheory.comp_apply] using ha⟩
  · exact ⟨u a, by simpa [CategoryTheory.comp_apply] using ha⟩

theorem functionExact_comp_iso {A B B' C : ModuleCat ℤ} (e : B ≅ B') (f : A ⟶ B) (g : B ⟶ C)
    (h : Function.Exact f g) : Function.Exact (f ≫ e.hom) (e.inv ≫ g) := by
  intro y
  have h2 : (e.inv ≫ g) y = g (e.inv y) := CategoryTheory.comp_apply e.inv g y
  rw [h2, h (e.inv y)]
  refine ⟨fun ⟨a, ha⟩ => ?_, fun ⟨a, ha⟩ => ?_⟩
  · exact ⟨a, by rw [CategoryTheory.comp_apply, ha, e.inv_hom_id_apply]⟩
  · exact ⟨a, by
      rw [← e.hom_inv_id_apply (f a)]
      rw [CategoryTheory.comp_apply] at ha
      rw [ha]⟩

theorem functionExact_comp_injective {A B C C' : ModuleCat ℤ} (w : C ⟶ C') (f : A ⟶ B)
    (g : B ⟶ C) (hw : Function.Injective w) (h : Function.Exact f g) :
    Function.Exact f (g ≫ w) := by
  intro y
  have h2 : (g ≫ w) y = w (g y) := CategoryTheory.comp_apply g w y
  rw [h2]
  rw [show (0 : C') = w 0 from (map_zero w.hom).symm, hw.eq_iff]
  exact h y

theorem function_injective_eqToHom {P Q : ModuleCat ℤ} (h : P = Q) :
    Function.Injective (eqToHom h : P ⟶ Q) := by
  subst h
  intro a b hab
  simpa using hab

theorem function_surjective_eqToHom {P Q : ModuleCat ℤ} (h : P = Q) :
    Function.Surjective (eqToHom h : P ⟶ Q) := by
  subst h
  intro b
  exact ⟨b, by simp⟩

/-! ## §2  The terms and the maps of the sequence -/

/-- The zero module, used for the terms in negative degrees. -/
abbrev mvZero : ModuleCat ℤ := ModuleCat.of ℤ PUnit

/-- The first Mayer–Vietoris map in degree `k`: `H_k(U ∩ V) → H_k(U) ⊞ H_k(V)`. -/
abbrev mvF (U V : Set X) (k : ℕ) :
    Work.Cohomology.HInter U V k ⟶ Work.Cohomology.HBiprod U V k :=
  HomologicalComplex.homologyMap (Work.Cohomology.mvLeft U V) k

/-- The second Mayer–Vietoris map in degree `k`: `H_k(U) ⊞ H_k(V) → H_k(C^{U,V})`. -/
abbrev mvG (U V : Set X) (k : ℕ) :
    Work.Cohomology.HBiprod U V k ⟶ Work.Cohomology.HSmall U V k :=
  HomologicalComplex.homologyMap (Work.Cohomology.mvRight U V) k

/-- The connecting map: `H_{k+1}(C^{U,V}) → H_k(U ∩ V)`. -/
abbrev mvD (U V : Set X) (k : ℕ) :
    Work.Cohomology.HSmall U V (k + 1) ⟶ Work.Cohomology.HInter U V k :=
  Work.Cohomology.mvδ U V k

/-- **The terms of the Mayer–Vietoris sequence**, as a function of
`Work.HomologyMV.MVI = ℤ × Fin 3`: `(k,0) = H_k(U ∩ V)`, `(k,1) = H_k(U) ⊞ H_k(V)`,
`(k,2) = H_k(C^{U,V})`, and the zero module in negative degrees. -/
def coverH (U V : Set X) (i : Work.HomologyMV.MVI) : ModuleCat ℤ :=
  if 0 ≤ i.1 then
    (if i.2 = 0 then Work.Cohomology.HInter U V i.1.toNat
     else if i.2 = 1 then Work.Cohomology.HBiprod U V i.1.toNat
     else Work.Cohomology.HSmall U V i.1.toNat)
  else mvZero

@[simp] theorem coverH_zero (U V : Set X) {k : ℤ} (hk : 0 ≤ k) :
    coverH U V (k, 0) = Work.Cohomology.HInter U V k.toNat := by
  simp only [coverH, ite_eq_left hk]
  simp

@[simp] theorem coverH_one (U V : Set X) {k : ℤ} (hk : 0 ≤ k) :
    coverH U V (k, 1) = Work.Cohomology.HBiprod U V k.toNat := by
  simp only [coverH, ite_eq_left hk]
  simp

@[simp] theorem coverH_two (U V : Set X) {k : ℤ} (hk : 0 ≤ k) :
    coverH U V (k, 2) = Work.Cohomology.HSmall U V k.toNat := by
  simp only [coverH, ite_eq_left hk]
  simp

@[simp] theorem coverH_neg (U V : Set X) {k : ℤ} (hk : ¬ 0 ≤ k) (r : Fin 3) :
    coverH U V (k, r) = mvZero := by
  simp only [coverH, ite_eq_right hk]

/-- **The maps of the Mayer–Vietoris sequence.**  In degree `k ≥ 0` they are the library maps
`mvF k`, `mvG k` and the connecting map `mvD (k-1)`; in negative degrees (and from `(0,2)` to
`(-1,0)`) the terms are zero modules and the maps are zero.  The `eqToHom`s transport the library
maps, which are stated for the terms `HInter`, `HBiprod`, `HSmall`, to the terms of `coverH`. -/
noncomputable def coverD (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) :
    ∀ i : Work.HomologyMV.MVI, coverH U V i ⟶ coverH U V (Work.HomologyMV.mvSucc i)
  | (k, 0) => by
    by_cases hk : 0 ≤ k
    · exact eqToHom (coverH_zero U V hk) ≫ mvF U V k.toNat ≫ eqToHom (coverH_one U V hk).symm
    · exact eqToHom (coverH_neg U V hk 0) ≫ (0 : mvZero ⟶ mvZero)
        ≫ eqToHom (coverH_neg U V hk 1).symm
  | (k, 1) => by
    by_cases hk : 0 ≤ k
    · exact eqToHom (coverH_one U V hk) ≫ mvG U V k.toNat ≫ eqToHom (coverH_two U V hk).symm
    · exact eqToHom (coverH_neg U V hk 1) ≫ (0 : mvZero ⟶ mvZero)
        ≫ eqToHom (coverH_neg U V hk 2).symm
  | (k, 2) => by
    by_cases hk1 : 1 ≤ k
    · have hk : 0 ≤ k := by omega
      have hk' : 0 ≤ k - 1 := by omega
      have h1 : k.toNat = (k - 1).toNat + 1 := by omega
      exact eqToHom (coverH_two U V hk)
        ≫ eqToHom (congrArg (fun n => Work.Cohomology.HSmall U V n) h1)
        ≫ mvD U V ((k - 1).toNat)
        ≫ eqToHom (coverH_zero U V hk').symm
    · by_cases hk0 : 0 ≤ k
      · exact eqToHom (coverH_two U V hk0)
          ≫ (0 : Work.Cohomology.HSmall U V k.toNat ⟶ mvZero)
          ≫ eqToHom (coverH_neg U V (by omega : ¬ 0 ≤ k - 1) 0).symm
      · exact eqToHom (coverH_neg U V hk0 2) ≫ (0 : mvZero ⟶ mvZero)
          ≫ eqToHom (coverH_neg U V (by omega : ¬ 0 ≤ k - 1) 0).symm

/-! ## §3  The values of `coverD` at each index (they are the casted library maps) -/

theorem coverD_zero (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    {k : ℤ} (hk : 0 ≤ k) :
    coverD U V hU hV hcov (k, 0)
      = eqToHom (coverH_zero U V hk) ≫ mvF U V k.toNat
        ≫ eqToHom (coverH_one U V hk).symm := by
  rw [coverD]
  rw [dif_pos hk]
  try rfl

theorem coverD_one (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    {k : ℤ} (hk : 0 ≤ k) :
    coverD U V hU hV hcov (k, 1)
      = eqToHom (coverH_one U V hk) ≫ mvG U V k.toNat
        ≫ eqToHom (coverH_two U V hk).symm := by
  rw [coverD]
  rw [dif_pos hk]
  try rfl

theorem coverD_two (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    {k : ℤ} (hk : 1 ≤ k) :
    coverD U V hU hV hcov (k, 2)
      = eqToHom (coverH_two U V (by omega))
        ≫ eqToHom (congrArg (fun n => Work.Cohomology.HSmall U V n)
            (by omega : k.toNat = (k - 1).toNat + 1))
        ≫ mvD U V ((k - 1).toNat)
        ≫ eqToHom (coverH_zero U V (by omega : 0 ≤ k - 1)).symm := by
  rw [coverD]
  rw [dif_pos hk]
  try rfl

/-! ## §3b  Values of `coverD` at the remaining indices, and general transport lemmas -/

theorem coverD_two_zero (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) {k : ℤ} (hk0 : 0 ≤ k) (hk1 : ¬ 1 ≤ k) :
    coverD U V hU hV hcov (k, 2)
      = eqToHom (coverH_two U V hk0)
        ≫ (0 : Work.Cohomology.HSmall U V k.toNat ⟶ mvZero)
        ≫ eqToHom (coverH_neg U V (r := (0 : Fin 3)) (by omega : ¬ 0 ≤ k - 1)).symm := by
  rw [coverD]
  rw [dif_neg hk1, dif_pos hk0]
  try rfl

theorem coverD_zero_neg (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) {k : ℤ} (hk : ¬ 0 ≤ k) :
    coverD U V hU hV hcov (k, 0)
      = eqToHom (coverH_neg U V hk 0) ≫ (0 : mvZero ⟶ mvZero)
        ≫ eqToHom (coverH_neg U V hk 1).symm := by
  rw [coverD, dif_neg hk]
  try rfl

theorem coverD_one_neg (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) {k : ℤ} (hk : ¬ 0 ≤ k) :
    coverD U V hU hV hcov (k, 1)
      = eqToHom (coverH_neg U V hk 1) ≫ (0 : mvZero ⟶ mvZero)
        ≫ eqToHom (coverH_neg U V hk 2).symm := by
  rw [coverD, dif_neg hk]
  try rfl

theorem coverD_two_neg (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) {k : ℤ} (hk : ¬ 0 ≤ k) :
    coverD U V hU hV hcov (k, 2)
      = eqToHom (coverH_neg U V hk 2) ≫ (0 : mvZero ⟶ mvZero)
        ≫ eqToHom (coverH_neg U V (by omega : ¬ 0 ≤ k - 1) 0).symm := by
  rw [coverD, dif_neg (by omega : ¬ 1 ≤ k), dif_neg hk]
  try rfl

theorem function_injective_of_iso {P Q : ModuleCat ℤ} (e : P ≅ Q) :
    Function.Injective ⇑e.hom := by
  intro a b hab
  have h1 := congrArg (fun z => e.inv z) hab
  simpa using h1

theorem function_surjective_of_iso {P Q : ModuleCat ℤ} (e : P ≅ Q) :
    Function.Surjective ⇑e.hom := by
  intro b
  exact ⟨e.inv b, by simp⟩

/-- **Transport of `Function.Exact` across isomorphisms of the three terms**: if `Exact f g` holds
with `f : A ⟶ B`, `g : B ⟶ C`, then `Exact (eA.hom ≫ f ≫ eB.inv) (eB.hom ≫ g ≫ eC.inv)` for any
isomorphisms `eA : A' ≅ A`, `eB : B' ≅ B`, `eC : C' ≅ C`. -/
theorem functionExact_transport {A B C A' B' C' : ModuleCat ℤ} (eA : A' ≅ A) (eB : B' ≅ B)
    (eC : C' ≅ C) {f : A ⟶ B} {g : B ⟶ C} (h : Function.Exact f g) :
    Function.Exact (eA.hom ≫ f ≫ eB.inv) (eB.hom ≫ g ≫ eC.inv) := by
  have h1 := functionExact_comp_iso eB.symm f g h
  have h2 := functionExact_comp_injective eC.inv (f ≫ eB.inv) (eB.hom ≫ g)
    (function_injective_of_iso eC.symm) h1
  exact functionExact_comp_surjective eA.hom (f ≫ eB.inv) (eB.hom ≫ g ≫ eC.inv)
    (function_surjective_of_iso eA) h2

/-- `homologyMap` depends only on the index, up to the canonical isomorphisms of the objects. -/
theorem homologyMap_eqToHom_congr {C D : ChainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D) {i j : ℕ}
    (h : i = j) :
    HomologicalComplex.homologyMap φ i
      = eqToHom (congrArg (fun n => C.homology n) h)
        ≫ HomologicalComplex.homologyMap φ j
        ≫ eqToHom (congrArg (fun n => D.homology n) h).symm := by
  subst h
  simp

theorem mvG_eqToHom_congr (U V : Set X) {i j : ℕ} (h : i = j) :
    mvG U V i
      = eqToHom (congrArg (fun n => Work.Cohomology.HBiprod U V n) h)
        ≫ mvG U V j
        ≫ eqToHom (congrArg (fun n => Work.Cohomology.HSmall U V n) h).symm :=
  homologyMap_eqToHom_congr (Work.Cohomology.mvRight U V) h

/-! ## §4  The degree-`0` exactness, and the long exact sequence -/

/-- **The degree-`0` Mayer–Vietoris input.**  The first Mayer–Vietoris map
`H_0(U) ⊞ H_0(V) → H_0(C^{U,V})` is onto, i.e. the sequence is exact at the last node of its
degree-`0` part.  This is the only node of the Mayer–Vietoris long exact sequence that the ported
library `Submission/Work/Cohomology/` does not provide. -/
def MVExactDegreeZero (U V : Set X) : Prop :=
  Function.Exact (mvG U V 0) (0 : Work.Cohomology.HSmall U V 0 ⟶ mvZero)

/-- **The degree-`0` input from the surjectivity of the classical Mayer–Vietoris map**
`H_0(U) ⊞ H_0(V) → H_0(X)` (`Work.Cohomology.mvRightX`), which is the form in which the statement
is proved (`Work.Final.mvRightX_zero_surjective`). -/
theorem mvExactDegreeZero_of_mvRightX (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ)
    (h : (Work.Cohomology.mvRightX U V hU hV hcov 0).hom.range = ⊤) :
    MVExactDegreeZero U V := by
  have hinj : Function.Injective ⇑(Work.Cohomology.smallIso U V hU hV hcov 0).hom :=
    function_injective_of_iso _
  have hsurj : Function.Surjective ⇑(mvG U V 0) := by
    have h' : Function.Surjective ⇑(Work.Cohomology.mvRightX U V hU hV hcov 0).hom :=
      LinearMap.range_eq_top.mp h
    intro y
    obtain ⟨x, hx⟩ := h' ((Work.Cohomology.smallIso U V hU hV hcov 0).hom y)
    refine ⟨x, hinj ?_⟩
    rw [← hx]
    rfl
  intro y
  constructor
  · intro _
    exact hsurj y
  · intro _
    rfl

/-- **Exactness of the Mayer–Vietoris sequence at every node.** -/
theorem coverD_exact (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hmv0 : MVExactDegreeZero U V) :
    ∀ i : Work.HomologyMV.MVI,
      Function.Exact (coverD U V hU hV hcov i)
        (coverD U V hU hV hcov (Work.HomologyMV.mvSucc i)) := by
  intro i
  obtain ⟨k, r⟩ := i
  match r with
  | 0 => -- r = 0: the node (k,0), pair `(d (k,0), d (k,1))`
    show Function.Exact (coverD U V hU hV hcov (k, 0)) (coverD U V hU hV hcov (k, 1))
    by_cases hk : 0 ≤ k
    · rw [coverD_zero U V hU hV hcov hk, coverD_one U V hU hV hcov hk]
      exact functionExact_transport (eqToIso (coverH_zero U V hk))
        (eqToIso (coverH_one U V hk)) (eqToIso (coverH_two U V hk))
        (Work.HomologyMV.functionExact_of_shortExact _ _ _
          (Work.Cohomology.mv_H_exact₂ U V k.toNat))
    · haveI : Subsingleton ↑(coverH U V (Work.HomologyMV.mvSucc (k, 0))) := by
        rw [Work.HomologyMV.mvSucc_zero, coverH_neg U V hk 1]
        infer_instance
      exact Work.HomologyMV.functionExact_of_subsingleton_mid _ _
  | 1 => -- r = 1: the node (k,1), pair `(d (k,1), d (k,2))`
    show Function.Exact (coverD U V hU hV hcov (k, 1)) (coverD U V hU hV hcov (k, 2))
    by_cases hk : 0 ≤ k
    · by_cases hk0 : k = 0
      · -- the degree-0 node: the surjectivity input
        subst hk0
        rw [coverD_one U V hU hV hcov hk,
          coverD_two_zero U V hU hV hcov hk (by omega)]
        exact functionExact_transport (eqToIso (coverH_one U V hk))
          (eqToIso (coverH_two U V hk))
          (eqToIso (coverH_neg U V (r := (0 : Fin 3)) (by omega : ¬ 0 ≤ (0 : ℤ) - 1)))
          hmv0
      · -- the nodes of degree `k ≥ 1`
        have hk1 : 1 ≤ k := by omega
        have h1 : k.toNat = (k - 1).toNat + 1 := by omega
        have hk2 : 0 ≤ k - 1 := by omega
        rw [coverD_one U V hU hV hcov hk, coverD_two U V hU hV hcov hk1,
          mvG_eqToHom_congr U V h1]
        exact functionExact_transport
          (eqToIso (coverH_one U V hk)
            ≪≫ eqToIso (congrArg (fun n => Work.Cohomology.HBiprod U V n) h1))
          (eqToIso (coverH_two U V hk)
            ≪≫ eqToIso (congrArg (fun n => Work.Cohomology.HSmall U V n) h1))
          (eqToIso (coverH_zero U V hk2))
          (Work.HomologyMV.functionExact_of_shortExact _ _ _
            (Work.Cohomology.mv_H_exact₃ U V ((k - 1).toNat)))
    · haveI : Subsingleton ↑(coverH U V (Work.HomologyMV.mvSucc (k, 1))) := by
        rw [Work.HomologyMV.mvSucc_one, coverH_neg U V hk 2]
        infer_instance
      exact Work.HomologyMV.functionExact_of_subsingleton_mid _ _
  | 2 => -- r = 2: the node (k,2), pair `(d (k,2), d (k-1,0))`
    show Function.Exact (coverD U V hU hV hcov (k, 2)) (coverD U V hU hV hcov (k - 1, 0))
    by_cases hk1 : 1 ≤ k
    · -- the nodes of degree `k ≥ 1`
      have hk : 0 ≤ k := by omega
      have hk2 : 0 ≤ k - 1 := by omega
      have h1 : k.toNat = (k - 1).toNat + 1 := by omega
      rw [coverD_two U V hU hV hcov hk1, coverD_zero U V hU hV hcov hk2]
      exact functionExact_transport
        (eqToIso (coverH_two U V hk)
          ≪≫ eqToIso (congrArg (fun n => Work.Cohomology.HSmall U V n) h1))
        (eqToIso (coverH_zero U V hk2))
        (eqToIso (coverH_one U V hk2))
        (Work.HomologyMV.functionExact_of_shortExact _ _ _
          (Work.Cohomology.mv_H_exact₁ U V ((k - 1).toNat)))
    · haveI : Subsingleton ↑(coverH U V (Work.HomologyMV.mvSucc (k, 2))) := by
        rw [Work.HomologyMV.mvSucc_two, coverH_neg U V (by omega : ¬ 0 ≤ k - 1) 0]
        infer_instance
      exact Work.HomologyMV.functionExact_of_subsingleton_mid _ _

/-- **The Mayer–Vietoris long exact sequence** of the open cover `U ∪ V = X`, in the indexing of
`Work.HomologyMV.MVLES`. -/
def coverMVLES (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hmv0 : MVExactDegreeZero U V) : Work.HomologyMV.MVLES where
  H := coverH U V
  d := coverD U V hU hV hcov
  exact := coverD_exact U V hU hV hcov hmv0

@[simp] theorem coverMVLES_H_zero (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (hmv0 : MVExactDegreeZero U V) (k : ℕ) :
    (coverMVLES U V hU hV hcov hmv0).H ((k : ℤ), 0) = Work.Cohomology.HInter U V k := by
  simp only [coverMVLES, coverH]
  exact coverH_zero U V (Int.natCast_nonneg k)

@[simp] theorem coverMVLES_H_one (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (hmv0 : MVExactDegreeZero U V) (k : ℕ) :
    (coverMVLES U V hU hV hcov hmv0).H ((k : ℤ), 1) = Work.Cohomology.HBiprod U V k := by
  simp only [coverMVLES, coverH]
  exact coverH_one U V (Int.natCast_nonneg k)

theorem coverMVLES_H_two (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (hmv0 : MVExactDegreeZero U V) (k : ℕ) :
    (coverMVLES U V hU hV hcov hmv0).H ((k : ℤ), 2) = Work.Cohomology.HSmall U V k := by
  simp only [coverMVLES]
  exact coverH_two U V (Int.natCast_nonneg k)

/-- **The `X`-slot of the Mayer–Vietoris sequence is the singular homology of `X`.** -/
def coverMVLES_hX (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hmv0 : MVExactDegreeZero U V) (k : ℕ) :
    (coverMVLES U V hU hV hcov hmv0).H ((k : ℤ), 2)
      ≅ LeanEval.Topology.intHomology k (TopCat.of X) :=
  eqToIso (coverMVLES_H_two U V hU hV hcov hmv0 k)
    ≪≫ Work.Cohomology.smallIso U V hU hV hcov k
    ≪≫ eqToIso (by rw [Work.Homology.intHomology_eq])

end

end Work.Final
