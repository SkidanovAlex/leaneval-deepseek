import Mathlib
import Submission.Work.ThomBordism.Tower.Defs
import Submission.Work.ThomBordism.Tower.BaseTheory
import Submission.Work.ThomBordism.Tower.psiAbs_natural
import Submission.Work.ThomBordism.Tower.totGlue

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cone tower: restrictions, naturality, surjectivity

This module develops the theory of the restriction maps `coneRes` on the mapping-cone complexes of
the cochain-level Thom map `psiAbs` (`Work.ThomBordism.ConeC`), which is what carries the tower
argument of `Work.ThomBordism.tower_surj`:

* `coneRes_comp` — the restrictions are compatible with composition of inclusions;
* `rcResLM_totShiftD` — the shifted differential `totShiftD` of the total complex commutes with the
  relative-cochain restriction (the shifted form of `rcResLM_comm`);
* `coneRes_coneD` — **the cone differential commutes with the restriction** (the first component is
  `baseRes_comm`, the second `psiAbs_natural` and `rcResLM_totShiftD`);
* `coneRes_surjective` — the restriction is surjective.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology
open scoped Simplicial

namespace Work.ThomBordism

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- **The cone restriction is compatible with composition of inclusions.** -/
theorem coneRes_comp (Z : RealBundle B F ι) (n : ℕ) {S S' T : Set B} (h : S ⊆ S')
    (h' : S' ⊆ T) (m : ℕ) (q : ConeC Z n T m) :
    coneRes Z n h m (coneRes Z n h' m q) = coneRes Z n (h.trans h') m q := by
  refine Prod.ext ?_ ?_
  · show baseRes h (m + 1) (baseRes h' (m + 1) q.1) = baseRes (h.trans h') (m + 1) q.1
    rw [← LinearMap.comp_apply, baseRes_comp]
  · show rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (m + n)
        (rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h') (m + n) q.2)
      = rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono (h.trans h')) (m + n) q.2
    have hpm : Set.preimage_mono (f := Z.proj) (h.trans h')
        = (Set.preimage_mono (f := Z.proj) h).trans (Set.preimage_mono (f := Z.proj) h') :=
      Subsingleton.elim _ _
    rw [← LinearMap.comp_apply, rcResLM_comp, hpm]

/-- The shift of the total differential by a degree equality commutes with the restriction. -/
theorem rcResLM_cast (Z : RealBundle B F ι) {S T : Set B} (h : S ⊆ T) {a b : ℕ} (e : a = b)
    (x : TotC Z T a) :
    rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) b (e ▸ x)
      = e ▸ (rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) a x) := by
  cases e
  rfl

/-- The shifted differential of the total complex, as the consecutive differential plus the degree
cast `Nat.add_right_comm m 1 n`. -/
theorem totShiftD_eq_cast (Z : RealBundle B F ι) (n : ℕ) (W : Set B) (m : ℕ)
    (x : TotC Z W (m + n)) :
    totShiftD Z n W m x
      = (Nat.add_right_comm m 1 n).symm ▸ (rcDiff (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' W) (m + n) x) := by
  rw [totShiftD, totComplex_d_transfer, totComplex_d_consecutive]

/-- **The shifted differential of the total complex commutes with the restriction.** -/
theorem rcResLM_totShiftD (Z : RealBundle B F ι) (n : ℕ) {S T : Set B} (h : S ⊆ T) (m : ℕ)
    (x : TotC Z T (m + n)) :
    rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) ((m + 1) + n)
        (totShiftD Z n T m x)
      = totShiftD Z n S m (rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (m + n) x) := by
  rw [totShiftD_eq_cast Z n T m x, totShiftD_eq_cast Z n S m _,
    rcResLM_cast Z h (Nat.add_right_comm m 1 n).symm]
  exact congrArg (fun y => (Nat.add_right_comm m 1 n).symm ▸ y)
    (rcResLM_comm (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (m + n) x)

/-- **The cone differential commutes with the restriction** (from `psiAbs_natural` and
`rcResLM_totShiftD`). -/
theorem coneRes_coneD (Z : RealBundle B F ι) (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n)
    {W W' : Set B} (h : W ⊆ W') (hW : W ⊆ U) (hW' : W' ⊆ U) (m : ℕ) (q : ConeC Z n W' m) :
    coneRes Z n h (m + 1) (coneD Z n U τ W' hW' m q)
      = coneD Z n U τ W hW m (coneRes Z n h m q) := by
  refine Prod.ext ?_ ?_
  · show baseRes h ((m + 1) + 1) (-(cochainDiffLM ℤ (baseSSet W') (m + 1) q.1))
      = -(cochainDiffLM ℤ (baseSSet W) (m + 1) (baseRes h (m + 1) q.1))
    rw [map_neg, baseRes_comm]
  · show rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) ((m + 1) + n)
        (psiAbs Z n U τ W' hW' (m + 1) q.1 + totShiftD Z n W' m q.2)
      = psiAbs Z n U τ W hW (m + 1) (baseRes h (m + 1) q.1)
        + totShiftD Z n W m (rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (m + n) q.2)
    have hpsi : rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) ((m + 1) + n)
          (psiAbs Z n U τ W' hW' (m + 1) q.1)
        = psiAbs Z n U τ W hW (m + 1) (baseRes h (m + 1) q.1) :=
      Tower.psiAbs_natural Z n U τ h hW hW' (m + 1) q.1
    rw [map_add, hpsi, rcResLM_totShiftD Z n h m q.2]

/-- **The cone restriction is surjective.** -/
theorem coneRes_surjective (Z : RealBundle B F ι) (n : ℕ) {S T : Set B} (h : S ⊆ T) (m : ℕ) :
    Function.Surjective (coneRes Z n h m) := by
  intro q
  obtain ⟨a, ha⟩ := baseRes_surjective h (m + 1) q.1
  obtain ⟨b, hb⟩ := rcResLM_surjective (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (m + n) q.2
  exact ⟨(a, b), Prod.ext ha hb⟩

end

end Work.ThomBordism

namespace Work.ThomBordism

noncomputable section

open CategoryTheory CategoryTheory.Limits

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- **Separation for the total tower.**  Two elements of the total complex over the union of an
increasing open family which restrict to the same element on every piece are equal. -/
theorem totRes_eq_of_forall (Z : RealBundle B F ι) (W : ℕ → Set B) (hopen : ∀ a, IsOpen (W a))
    (hmono : ∀ a b, a ≤ b → W a ⊆ W b) (k : ℕ) {x y : TotC Z (⋃ a, W a) k}
    (h : ∀ a, rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono (Set.subset_iUnion W a)) k x
      = rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono (Set.subset_iUnion W a)) k y) :
    x = y := by
  let f : (a : ℕ) → TotC Z (W a) k :=
    fun a => rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono (Set.subset_iUnion W a)) k x
  have hf : ∀ a b (hab : a ≤ b),
      rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono (hmono a b hab)) k (f b) = f a := by
    intro a b hab
    show rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono (hmono a b hab)) k
        (rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono (Set.subset_iUnion W b)) k x)
      = rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono (Set.subset_iUnion W a)) k x
    rw [← LinearMap.comp_apply, rcResLM_comp,
      rcResLM_proof_irrel (A := Work.Thom.zeroComplement Z)
        ((Set.preimage_mono (hmono a b hab)).trans (Set.preimage_mono (Set.subset_iUnion W b)))
        (Set.preimage_mono (Set.subset_iUnion W a)) k]
  obtain ⟨g, hg, hguniq⟩ := Tower.totGlue Z W hopen hmono k f hf
  have hx : x = g := hguniq x (fun a => rfl)
  have hy : y = g := hguniq y (fun a => by rw [← h a])
  exact hx.trans hy.symm

/-- **Separation for the cone tower.** -/
theorem coneRes_eq_of_forall (Z : RealBundle B F ι) (n : ℕ) (W : ℕ → Set B)
    (hopen : ∀ a, IsOpen (W a)) (hmono : ∀ a b, a ≤ b → W a ⊆ W b) (m : ℕ)
    {x y : ConeC Z n (⋃ a, W a) m}
    (h : ∀ a, coneRes Z n (Set.subset_iUnion W a) m x
      = coneRes Z n (Set.subset_iUnion W a) m y) :
    x = y := by
  refine Prod.ext ?_ ?_
  · refine baseRes_eq_of_forall W hopen (fun a b h => hmono a b h) (m + 1) (fun a => ?_)
    have := congrArg Prod.fst (h a)
    simpa only [coneRes_fst] using this
  · exact totRes_eq_of_forall Z W hopen hmono (m + n) (fun a => by
      have := congrArg Prod.snd (h a)
      simpa only [coneRes_snd] using this)

/-- **Gluing for the cone tower.**  A compatible family of cone elements over the pieces glues to a
unique cone element over the union. -/
theorem coneGlue (Z : RealBundle B F ι) (n : ℕ) (W : ℕ → Set B) (hopen : ∀ a, IsOpen (W a))
    (hmono : ∀ a b, a ≤ b → W a ⊆ W b) (m : ℕ)
    (q : (a : ℕ) → ConeC Z n (W a) m)
    (hq : ∀ a b (hab : a ≤ b), coneRes Z n (hmono a b hab) m (q b) = q a) :
    ∃! Q : ConeC Z n (⋃ a, W a) m, ∀ a, coneRes Z n (Set.subset_iUnion W a) m Q = q a := by
  obtain ⟨g, hg, -⟩ := baseGlue W hopen (fun a b h => hmono a b h) (m + 1)
    (fun a => (q a).1) (fun a b hab => by
      have := congrArg Prod.fst (hq a b hab)
      simpa only [coneRes_fst] using this)
  obtain ⟨g', hg', -⟩ := Tower.totGlue Z W hopen hmono (m + n)
    (fun a => (q a).2) (fun a b hab => by
      have := congrArg Prod.snd (hq a b hab)
      simpa only [coneRes_snd] using this)
  refine ⟨(g, g'), ?_, ?_⟩
  · intro a
    exact Prod.ext (hg a) (hg' a)
  · intro Y hY
    refine (coneRes_eq_of_forall Z n W hopen hmono m (fun a => ?_)).symm
    rw [hY a]
    exact Prod.ext (hg a) (hg' a)

end

end Work.ThomBordism

namespace Work.ThomBordism

noncomputable section

open CategoryTheory CategoryTheory.Limits

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- `baseRes` along a self-inclusion is the identity. -/
theorem baseRes_self {S : Set B} (h : S ⊆ S) (k : ℕ) : baseRes h k = LinearMap.id := by
  apply LinearMap.ext
  intro x
  rw [baseRes_apply, LinearMap.id_apply]
  rw [show pdIncl (M := TopCat.of B) S S h = 𝟙 (TopCat.of S) from pdIncl_self (TopCat.of B) S h]
  rw [dualChainMap_id, HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]

/-- `coneRes` along a self-inclusion is the identity. -/
theorem coneRes_self (Z : RealBundle B F ι) (n : ℕ) {S : Set B} (h : S ⊆ S) (m : ℕ)
    (q : ConeC Z n S m) : coneRes Z n h m q = q := by
  refine Prod.ext ?_ ?_
  · show baseRes h (m + 1) q.1 = q.1
    rw [baseRes_self h (m + 1)]
    rfl
  · show rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono (f := Z.proj) h) (m + n) q.2
      = q.2
    have hf : Set.preimage_mono (f := Z.proj) h
        = Set.Subset.refl (Z.proj ⁻¹' S) := Subsingleton.elim _ _
    rw [hf]
    exact rcResLM_self (Work.Thom.zeroComplement Z) (Set.Subset.refl (Z.proj ⁻¹' S)) (m + n) q.2

end

end Work.ThomBordism
