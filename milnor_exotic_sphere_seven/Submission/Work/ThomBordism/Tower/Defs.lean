import Mathlib
import Submission.Work.ThomBordism.chainSetup_cone
import Submission.Work.Cohomology.rcKern_iUnion_limit
import Submission.Work.Cohomology.rcResLM_surjective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The tower of cone complexes over an increasing family of open pieces

This module fixes the vocabulary of the *tower* argument for
`Work.ThomBordism.tower_surj`: for `W ⊆ W'` two pieces of the base,

* `Work.ThomBordism.baseRes h k` is the restriction of the absolute `k`-cochains of the piece `W'`
  to the piece `W` (the transpose of the chain map induced by the inclusion `W ↪ W'`), and
* `Work.ThomBordism.coneRes Z n h m` is the induced restriction on the mapping-cone complexes
  `ConeC Z n W' m → ConeC Z n W m`, componentwise (`baseRes` on the base component and the
  relative-cochain restriction `rcResLM` of the pair `(X|_•, X|_•∖0)` on the total component).

Both are restriction maps, i.e. they are compatible with composition of inclusions
(`baseRes_comp_of_eq`, `coneRes_comp_of_eq`) and — the content of
`Work.ThomBordism.psiAbs_natural` — with the cone differentials.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology

namespace Work.ThomBordism

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- **Restriction of absolute cochains.**  For `W ⊆ W'` and `k : ℕ`, the pullback of a `k`-cochain
on the piece `W'` to the piece `W`, i.e. the transpose of the chain map induced by the inclusion
`pdIncl W' W h : W ↪ W'`. -/
def baseRes {W W' : Set B} (h : W ⊆ W') (k : ℕ) : BaseC W' k →ₗ[ℤ] BaseC W k :=
  ModuleCat.Hom.hom ((dualChainMap ℤ (TopCat.of W) (TopCat.of W')
    (pdIncl (M := TopCat.of B) W' W h)).f k)

/-- The defining formula of `baseRes`. -/
theorem baseRes_apply {W W' : Set B} (h : W ⊆ W') (k : ℕ) (a : BaseC W' k) :
    baseRes h k a = (ModuleCat.Hom.hom ((dualChainMap ℤ (TopCat.of W) (TopCat.of W')
      (pdIncl (M := TopCat.of B) W' W h)).f k)) a := rfl

/-- **Restriction of the mapping cone.**  For `W ⊆ W'` the restriction of the cone complex of the
Thom cup map: `baseRes` on the base component and the relative cochain restriction of the Thom pair
on the total component. -/
def coneRes (Z : RealBundle B F ι) (n : ℕ) {W W' : Set B} (h : W ⊆ W') (m : ℕ) :
    ConeC Z n W' m → ConeC Z n W m :=
  fun q => (baseRes h (m + 1) q.1,
    rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (m + n) q.2)

/-- The defining formula of `coneRes`. -/
theorem coneRes_apply (Z : RealBundle B F ι) (n : ℕ) {W W' : Set B} (h : W ⊆ W') (m : ℕ)
    (q : ConeC Z n W' m) :
    coneRes Z n h m q = (baseRes h (m + 1) q.1,
      rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (m + n) q.2) := rfl

/-- `coneRes` sends the zero element to the zero element. -/
@[simp] theorem coneRes_zero (Z : RealBundle B F ι) (n : ℕ) {W W' : Set B} (h : W ⊆ W')
    (m : ℕ) : coneRes Z n h m (0 : ConeC Z n W' m) = 0 := by
  refine Prod.ext ?_ ?_
  · show baseRes h (m + 1) (0 : BaseC W' (m + 1)) = (0 : BaseC W (m + 1))
    simp
  · show rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (m + n)
        (0 : TotC Z W' (m + n)) = (0 : TotC Z W (m + n))
    simp

/-- `coneRes` is additive. -/
theorem coneRes_add (Z : RealBundle B F ι) (n : ℕ) {W W' : Set B} (h : W ⊆ W') (m : ℕ)
    (q q' : ConeC Z n W' m) : coneRes Z n h m (q + q') = coneRes Z n h m q + coneRes Z n h m q' := by
  refine Prod.ext ?_ ?_
  · show baseRes h (m + 1) ((q + q').1) = baseRes h (m + 1) q.1 + baseRes h (m + 1) q'.1
    rw [Prod.fst_add, map_add]
  · show rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (m + n) ((q + q').2)
        = rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (m + n) q.2
          + rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (m + n) q'.2
    rw [Prod.snd_add, map_add]

/-- `coneRes` is negated by negation. -/
theorem coneRes_neg (Z : RealBundle B F ι) (n : ℕ) {W W' : Set B} (h : W ⊆ W') (m : ℕ)
    (q : ConeC Z n W' m) : coneRes Z n h m (-q) = -coneRes Z n h m q := by
  refine Prod.ext ?_ ?_
  · show baseRes h (m + 1) ((-q).1) = -(baseRes h (m + 1) q.1)
    rw [Prod.fst_neg, map_neg]
  · show rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (m + n) ((-q).2)
        = -(rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (m + n) q.2)
    rw [Prod.snd_neg, map_neg]

/-- `coneRes` is subtractive. -/
theorem coneRes_sub (Z : RealBundle B F ι) (n : ℕ) {W W' : Set B} (h : W ⊆ W') (m : ℕ)
    (q q' : ConeC Z n W' m) : coneRes Z n h m (q - q') = coneRes Z n h m q - coneRes Z n h m q' := by
  refine Prod.ext ?_ ?_
  · show baseRes h (m + 1) ((q - q').1) = baseRes h (m + 1) q.1 - baseRes h (m + 1) q'.1
    rw [Prod.fst_sub, map_sub]
  · show rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (m + n) ((q - q').2)
        = rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (m + n) q.2
          - rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (m + n) q'.2
    rw [Prod.snd_sub, map_sub]

/-- `coneRes` lands componentwise in the restriction of the total complex. -/
theorem coneRes_fst (Z : RealBundle B F ι) (n : ℕ) {W W' : Set B} (h : W ⊆ W') (m : ℕ)
    (q : ConeC Z n W' m) : (coneRes Z n h m q).1 = baseRes h (m + 1) q.1 := rfl

/-- The second component of `coneRes`. -/
theorem coneRes_snd (Z : RealBundle B F ι) (n : ℕ) {W W' : Set B} (h : W ⊆ W') (m : ℕ)
    (q : ConeC Z n W' m) :
    (coneRes Z n h m q).2
      = rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (m + n) q.2 := rfl

end

end Work.ThomBordism
