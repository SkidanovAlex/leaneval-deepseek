import Mathlib
import Submission.Work.ThomBordism.localThom_iUnion_aux
import Submission.Work.ThomBordism.iUnion.extra
import Submission.Work.ThomBordism.Tower.ConeTheory

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# Gluing of the cone tower over a chain of open pieces

The mapping cone `ConeC Z n W m = BaseC W (m+1) × TotC Z W (m+n)` of the cochain-level Thom map
`ψ = psiAbs` is a product of two cochain complexes, so compatible families of cone elements over a
family of pieces glue and separate.

This file provides, for a family of pieces that forms a **chain** under inclusion and whose union is
written `⋃₀ D`:

* `chainLO` — the chain hypothesis makes inclusion a `LinearOrder` on `↥D`;
* `baseRes_eq_of_forall_lin`, `totRes_eq_of_forall_lin`, `coneRes_eq_of_forall_lin` — separation
  over an increasing family indexed by an arbitrary linear order;
* `coneRes_sep_chain` — the same for `⋃₀ D`;
* `coneGlue_lin`, `coneGlue_chain`, `coneGlueMembersC` — gluing of a compatible family of cone
  elements, the last one with a prescribed equation `coneD (+1) p`.

These are the `ConeC` analogues of the proven `ExtraC` lemmas of
`Submission.Work.ThomBordism.iUnion.extraGlueMembers`.
-/

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology

namespace Work.ThomBordism.iUnion.ConeAux

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## The chain order on the members of a chain of sets -/

/-- **The chain order.**  On the members of a chain `D` of sets, inclusion is a linear order:
totality is exactly the chain hypothesis. -/
def chainLO (D : Set (Set B))
    (hdchain : ∀ W ∈ D, ∀ W' ∈ D, W ⊆ W' ∨ W' ⊆ W) : LinearOrder ↥D := by
  classical
  letI : DecidableEq ↥D := Classical.decEq _
  letI : Min ↥D := ⟨fun a b => if (a : Set B) ⊆ (b : Set B) then a else b⟩
  letI : Max ↥D := ⟨fun a b => if (a : Set B) ⊆ (b : Set B) then b else a⟩
  letI : Ord ↥D := ⟨fun a b => compareOfLessAndEq a b⟩
  exact LinearOrder.mk
    (le_total := fun a b => hdchain a.1 a.2 b.1 b.2)
    (toDecidableLE := Classical.decRel _) (toDecidableEq := Classical.decEq _)
    (toDecidableLT := Classical.decRel _)
    (min_def := fun _ _ => rfl) (max_def := fun _ _ => rfl)
    (compare_eq_compareOfLessAndEq := fun _ _ => rfl)

/-- `coneRes` does not depend on the proof of the inclusion of the pieces. -/
theorem coneRes_proof_irrel (Z : RealBundle B F ι) (n : ℕ) {W W' : Set B} (h h' : W ⊆ W')
    (m : ℕ) : coneRes Z n h m = coneRes Z n h' m := by
  rw [Subsingleton.elim h h']

/-! ## Separation, for an arbitrary linear order -/

/-- **Separation for the absolute-cochain tower.** -/
theorem baseRes_eq_of_forall_lin {J : Type} [LinearOrder J] {V : J → Set B}
    (hopen : ∀ j, IsOpen (V j)) (hmono : Monotone V) (k : ℕ)
    {x y : BaseC (⋃ j, V j) k}
    (h : ∀ j, baseRes (Set.subset_iUnion V j) k x = baseRes (Set.subset_iUnion V j) k y) :
    x = y := by
  rw [← sub_eq_zero]
  refine baseRes_sep_lin V hopen hmono k ?_
  intro j
  rw [map_sub, h j, sub_self]

/-- **Separation for the total tower.** -/
theorem totRes_eq_of_forall_lin (Z : RealBundle B F ι) {J : Type} [LinearOrder J]
    {V : J → Set B} (hopen : ∀ j, IsOpen (V j)) (hmono : Monotone V) (k : ℕ)
    {x y : TotC Z (⋃ j, V j) k}
    (h : ∀ j, rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono (Set.subset_iUnion V j)) k x
      = rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono (Set.subset_iUnion V j)) k y) :
    x = y := by
  rw [← sub_eq_zero]
  refine totRes_sep_lin Z V hopen hmono k ?_
  intro j
  rw [map_sub, h j, sub_self]

/-- **Separation for the cone.** -/
theorem coneRes_eq_of_forall_lin (Z : RealBundle B F ι) (n : ℕ) {J : Type} [LinearOrder J]
    {V : J → Set B} (hopen : ∀ j, IsOpen (V j)) (hmono : Monotone V) (m : ℕ)
    {x y : ConeC Z n (⋃ j, V j) m}
    (h : ∀ j, coneRes Z n (Set.subset_iUnion V j) m x = coneRes Z n (Set.subset_iUnion V j) m y) :
    x = y := by
  refine Prod.ext ?_ ?_
  · refine baseRes_eq_of_forall_lin hopen hmono (m + 1) (fun j => ?_)
    have h1 := congrArg Prod.fst (h j)
    simpa only [coneRes_fst] using h1
  · refine totRes_eq_of_forall_lin Z hopen hmono (m + n) (fun j => ?_)
    have h1 := congrArg Prod.snd (h j)
    simpa only [coneRes_snd] using h1

/-! ## Separation over a chain, with the union written `⋃₀ D` -/

/-- **Separation for the cone over a chain of open sets.** -/
theorem coneRes_sep_chain {D : Set (Set B)} (hopen : ∀ W ∈ D, IsOpen W)
    (hdchain : ∀ W ∈ D, ∀ W' ∈ D, W ⊆ W' ∨ W' ⊆ W)
    (Z : RealBundle B F ι) (n : ℕ) (m : ℕ) {U : Set B}
    (hU : U = ⋃ j : ↥D, ((j : Set B))) (hinc : ∀ W : ↥D, (W : Set B) ⊆ U)
    {x y : ConeC Z n U m}
    (h : ∀ W : ↥D, coneRes Z n (hinc W) m x = coneRes Z n (hinc W) m y) : x = y := by
  letI : LinearOrder ↥D := chainLO D hdchain
  subst hU
  refine coneRes_eq_of_forall_lin Z n (V := fun j : ↥D => (j : Set B))
    (fun j => hopen (j : Set B) j.2) (fun a b hab => hab) m ?_
  intro W
  have hp : hinc W = Set.subset_iUnion (fun j : ↥D => (j : Set B)) W := Subsingleton.elim _ _
  simpa only [hp] using h W

/-! ## Gluing, for an arbitrary linear order and over a chain -/

/-- **Gluing of a compatible family of cone elements** over an increasing family of open pieces
indexed by an arbitrary linear order. -/
theorem coneGlue_lin (Z : RealBundle B F ι) (n : ℕ) {J : Type} [LinearOrder J] (W : J → Set B)
    (hopen : ∀ a, IsOpen (W a)) (hmono : Monotone W) (m : ℕ)
    (q : (a : J) → ConeC Z n (W a) m)
    (hq : ∀ a b (hab : a ≤ b), coneRes Z n (hmono hab) m (q b) = q a) :
    ∃! Q : ConeC Z n (⋃ a, W a) m, ∀ a, coneRes Z n (Set.subset_iUnion W a) m Q = q a := by
  obtain ⟨g, hg, -⟩ := baseGlue_lin W hopen hmono (m + 1) (fun a => (q a).1) (fun a b hab => by
    have h1 := congrArg Prod.fst (hq a b hab)
    simpa only [coneRes_fst] using h1)
  obtain ⟨g', hg', -⟩ := totGlue_lin Z W hopen hmono (m + n) (fun a => (q a).2)
    (fun a b hab => by
      have h1 := congrArg Prod.snd (hq a b hab)
      simpa only [coneRes_snd] using h1)
  refine ⟨(g, g'), ?_, ?_⟩
  · intro a
    exact Prod.ext (hg a) (hg' a)
  · intro Y hY
    refine Prod.ext ?_ ?_
    · refine baseRes_eq_of_forall_lin hopen hmono (m + 1) (fun a => ?_)
      have h1 := congrArg Prod.fst (hY a)
      simp only [coneRes_fst] at h1
      exact h1.trans (hg a).symm
    · refine totRes_eq_of_forall_lin Z hopen hmono (m + n) (fun a => ?_)
      have h1 := congrArg Prod.snd (hY a)
      simp only [coneRes_snd] at h1
      exact h1.trans (hg' a).symm

/-- **Gluing of a compatible family of cone elements over a chain of open sets.**  The pieces are
the members of `D`; the union is `U`, which the caller identifies with `⋃₀ D`. -/
theorem coneGlue_chain {D : Set (Set B)} (hopen : ∀ W ∈ D, IsOpen W)
    (hdchain : ∀ W ∈ D, ∀ W' ∈ D, W ⊆ W' ∨ W' ⊆ W)
    (Z : RealBundle B F ι) (n : ℕ) (m : ℕ) (q : (W : ↥D) → ConeC Z n (W : Set B) m)
    (hq : ∀ (W W' : ↥D) (h : (W : Set B) ⊆ W'), coneRes Z n h m (q W') = q W)
    {U : Set B} (hU : U = ⋃ j : ↥D, ((j : Set B)))
    (hinc : ∀ W : ↥D, (W : Set B) ⊆ U) :
    ∃! Q : ConeC Z n U m, ∀ W : ↥D, coneRes Z n (hinc W) m Q = q W := by
  letI : LinearOrder ↥D := chainLO D hdchain
  subst hU
  obtain ⟨Q, hQ, huniq⟩ := coneGlue_lin Z n (fun j : ↥D => (j : Set B))
    (fun j => hopen (j : Set B) j.2) (fun a b hab => hab) m q (fun a b hab => hq a b hab)
  refine ⟨Q, ?_, ?_⟩
  · intro W
    exact hQ W
  · intro Y hY
    exact huniq Y (fun W => hY W)

/-! ## Gluing with a prescribed cone differential -/

/-- **The cone gluing over a chain, with a prescribed cone primitive.**  Given a chain `D` of members
of a family `C` of open sets (through `D₀`), compatible cone elements `q W` on the members of `D`
whose `coneD`-images are the restrictions of a fixed cone-`(m+1)`-primitive `p` over `⋃₀ D₀`, there
is a cone element `Q` over `⋃₀ D` restricting to `q W` on every `W ∈ D` and whose `coneD`-image is
the restriction of `p`. -/
theorem coneGlueMembersC (Z : RealBundle B F ι) (n : ℕ) (m : ℕ)
    (C : Set (Set B)) (hC : ∀ W ∈ C, IsOpen W) (τ : Work.Thom.PieceCoh Z (⋃₀ C) n)
    (D₀ : Set (Set B)) (hD₀ : D₀ ⊆ C)
    {D : Set (Set B)} (hD : D ⊆ D₀) (hdchain : ∀ W ∈ D, ∀ W' ∈ D, W ⊆ W' ∨ W' ⊆ W)
    (p : ConeC Z n (⋃₀ D₀) (m + 1))
    (q : (W : ↥D) → ConeC Z n (W : Set B) m)
    (hq : ∀ (W W' : ↥D) (h : (W : Set B) ⊆ W'),
      coneRes Z n h m (q W') = q W)
    (heq : ∀ W : ↥D, coneD Z n (⋃₀ C) τ (W : Set B)
        (Set.subset_sUnion_of_mem (hD₀ (hD W.2))) m (q W)
      = coneRes Z n (Set.subset_sUnion_of_mem (hD W.2)) (m + 1) p) :
    ∃ Q : ConeC Z n (⋃₀ D) m,
      (∀ W : ↥D, coneRes Z n (Set.subset_sUnion_of_mem W.2) m Q = q W) ∧
      coneD Z n (⋃₀ C) τ (⋃₀ D) (Set.sUnion_mono (hD.trans hD₀)) m Q
        = coneRes Z n (Set.sUnion_mono hD) (m + 1) p := by
  classical
  have hDopen : ∀ W ∈ D, IsOpen W := fun W hW => hC W (hD₀ (hD hW))
  obtain ⟨Q, hQ₀, -⟩ := coneGlue_chain hDopen hdchain Z n m q hq
    (U := ⋃₀ D) Set.sUnion_eq_iUnion (fun W => Set.subset_sUnion_of_mem W.2)
  have hQ : ∀ W : ↥D, coneRes Z n (Set.subset_sUnion_of_mem W.2) m Q = q W := fun W => hQ₀ W
  refine ⟨Q, hQ, ?_⟩
  refine coneRes_sep_chain hDopen hdchain Z n (m + 1) (U := ⋃₀ D)
    Set.sUnion_eq_iUnion (fun W => Set.subset_sUnion_of_mem W.2) (fun W => ?_)
  calc coneRes Z n (Set.subset_sUnion_of_mem W.2) (m + 1)
        (coneD Z n (⋃₀ C) τ (⋃₀ D) (Set.sUnion_mono (hD.trans hD₀)) m Q)
      = coneD Z n (⋃₀ C) τ (W : Set B) (Set.subset_sUnion_of_mem (hD₀ (hD W.2))) m
          (coneRes Z n (Set.subset_sUnion_of_mem W.2) m Q) :=
        coneRes_coneD Z n (⋃₀ C) τ (Set.subset_sUnion_of_mem W.2)
          (Set.subset_sUnion_of_mem (hD₀ (hD W.2))) (Set.sUnion_mono (hD.trans hD₀)) m Q
    _ = coneD Z n (⋃₀ C) τ (W : Set B) (Set.subset_sUnion_of_mem (hD₀ (hD W.2))) m (q W) := by
        rw [hQ W]
    _ = coneRes Z n (Set.subset_sUnion_of_mem (hD W.2)) (m + 1) p := heq W
    _ = coneRes Z n (Set.subset_sUnion_of_mem W.2) (m + 1)
          (coneRes Z n (Set.sUnion_mono hD) (m + 1) p) := by
        rw [coneRes_comp Z n (Set.subset_sUnion_of_mem W.2) (Set.sUnion_mono hD) (m + 1) p]

/-! ## Independence of the inclusion proofs -/

/-- The chosen representative of the restricted class does not depend on the proof of the
inclusion. -/
theorem tauRepAt_proof_irrel (Z : RealBundle B F ι) (n : ℕ) (U : Set B)
    (τ : Work.Thom.PieceCoh Z U n) {W : Set B} (h h' : W ⊆ U) :
    tauRepAt Z n U τ W h = tauRepAt Z n U τ W h' := by
  simp only [tauRepAt]

/-- `psiAbs` does not depend on the proof of the inclusion. -/
theorem psiAbs_proof_irrel (Z : RealBundle B F ι) (n : ℕ) (U : Set B)
    (τ : Work.Thom.PieceCoh Z U n) {W : Set B} (h h' : W ⊆ U) (m : ℕ) (a : BaseC W m) :
    psiAbs Z n U τ W h m a = psiAbs Z n U τ W h' m a := by
  apply Subtype.ext
  simp only [psiAbs, Subtype.coe_mk]

/-- `psiAbsLM` does not depend on the proof of the inclusion. -/
theorem psiAbsLM_proof_irrel (Z : RealBundle B F ι) (n : ℕ) (U : Set B)
    (τ : Work.Thom.PieceCoh Z U n) {W : Set B} (h h' : W ⊆ U) (m : ℕ) :
    psiAbsLM Z n U τ W h m = psiAbsLM Z n U τ W h' m :=
  LinearMap.ext (fun a => psiAbs_proof_irrel (Z := Z) n U τ h h' m a)

/-- The cone differential does not depend on the proof of the inclusion. -/
theorem coneD_proof_irrel (Z : RealBundle B F ι) (n : ℕ) (U : Set B)
    (τ : Work.Thom.PieceCoh Z U n) {W : Set B} (h h' : W ⊆ U) (m : ℕ) :
    coneD Z n U τ W h m = coneD Z n U τ W h' m := by
  funext q
  obtain ⟨a, b⟩ := q
  simp only [coneD, psiAbsLM_proof_irrel (Z := Z) n U τ h h' (m + 1)]

/-- The Extra differential does not depend on the proof of the inclusion. -/
theorem extraD_proof_irrel (Z : RealBundle B F ι) (n : ℕ) (U : Set B)
    (τ : Work.Thom.PieceCoh Z U n) {W : Set B} (h h' : W ⊆ U) :
    extraD Z n U τ W h = extraD Z n U τ W h' := by
  funext q
  obtain ⟨a, b⟩ := q
  simp only [extraD, psiAbsLM_proof_irrel (Z := Z) n U τ h h' 0]

/-- The cone-cycle condition does not depend on the proof of the inclusion. -/
theorem ConeCycle_proof_irrel (Z : RealBundle B F ι) (n : ℕ) (U : Set B)
    (τ : Work.Thom.PieceCoh Z U n) {W : Set B} (h h' : W ⊆ U) (m : ℕ)
    (p : ConeC Z n W m) :
    ConeCycle Z n U τ W h m p ↔ ConeCycle Z n U τ W h' m p := by
  unfold ConeCycle
  rw [coneD_proof_irrel (Z := Z) n U τ h h' m]

/-- `ConeBoundaryPos` does not depend on the proof of the inclusion. -/
theorem ConeBoundaryPos_proof_irrel (Z : RealBundle B F ι) (n : ℕ) (U : Set B)
    (τ : Work.Thom.PieceCoh Z U n) {W : Set B} (h h' : W ⊆ U) (m : ℕ)
    (p : ConeC Z n W (m + 1)) :
    ConeBoundaryPos Z n U τ W h m p ↔ ConeBoundaryPos Z n U τ W h' m p := by
  unfold ConeBoundaryPos
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, by rw [← coneD_proof_irrel (Z := Z) n U τ h h' m]; exact hq⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, by rw [coneD_proof_irrel (Z := Z) n U τ h h' m]; exact hq⟩

/-- **`ConeCyclicPos` does not depend on the proof of the inclusion.** -/
theorem ConeCyclicPos_proof_irrel (Z : RealBundle B F ι) (n : ℕ) (U : Set B)
    (τ : Work.Thom.PieceCoh Z U n) {W : Set B} (h h' : W ⊆ U) (m : ℕ) :
    ConeCyclicPos Z n U τ W h m ↔ ConeCyclicPos Z n U τ W h' m := by
  constructor
  · intro hp p hpcyc
    exact (ConeBoundaryPos_proof_irrel Z n U τ h h' m p).mp
      (hp p ((ConeCycle_proof_irrel Z n U τ h h' (m + 1) p).mpr hpcyc))
  · intro hp p hpcyc
    exact (ConeBoundaryPos_proof_irrel Z n U τ h h' m p).mpr
      (hp p ((ConeCycle_proof_irrel Z n U τ h h' (m + 1) p).mp hpcyc))

/-- **`ConeCyclicZero` does not depend on the proof of the inclusion.** -/
theorem ConeCyclicZero_proof_irrel (Z : RealBundle B F ι) (n : ℕ) (U : Set B)
    (τ : Work.Thom.PieceCoh Z U n) {W : Set B} (h h' : W ⊆ U) :
    ConeCyclicZero Z n U τ W h ↔ ConeCyclicZero Z n U τ W h' := by
  constructor
  · intro hp p hpcyc
    obtain ⟨q, hq⟩ := hp p ((ConeCycle_proof_irrel Z n U τ h h' 0 p).mpr hpcyc)
    exact ⟨q, by rw [← extraD_proof_irrel (Z := Z) n U τ h h']; exact hq⟩
  · intro hp p hpcyc
    obtain ⟨q, hq⟩ := hp p ((ConeCycle_proof_irrel Z n U τ h h' 0 p).mp hpcyc)
    exact ⟨q, by rw [extraD_proof_irrel (Z := Z) n U τ h h']; exact hq⟩

/-- The cone differential is subtractive. -/
theorem coneD_sub (Z : RealBundle B F ι) (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n)
    (W : Set B) (hW : W ⊆ U) (m : ℕ) (q q' : ConeC Z n W m) :
    coneD Z n U τ W hW m (q - q') = coneD Z n U τ W hW m q - coneD Z n U τ W hW m q' := by
  refine Prod.ext ?_ ?_
  · show -(cochainDiffLM ℤ (baseSSet W) (m + 1) ((q - q').1))
      = -(cochainDiffLM ℤ (baseSSet W) (m + 1) q.1)
        - -(cochainDiffLM ℤ (baseSSet W) (m + 1) q'.1)
    rw [Prod.fst_sub, map_sub]
    abel
  · show psiAbsLM Z n U τ W hW (m + 1) ((q - q').1) + totShiftD Z n W m ((q - q').2)
      = (psiAbsLM Z n U τ W hW (m + 1) q.1 + totShiftD Z n W m q.2)
        - (psiAbsLM Z n U τ W hW (m + 1) q'.1 + totShiftD Z n W m q'.2)
    rw [Prod.fst_sub, Prod.snd_sub, map_sub, totShiftD_sub]
    abel

end

end Work.ThomBordism.iUnion.ConeAux
