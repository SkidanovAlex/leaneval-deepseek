import Mathlib
import Submission.Work.Whitney.TautSection
import Submission.Work.Whitney.SectionStability
import Submission.Work.Thom.tautQuotientComap
import Submission.Work.Thom.chernClass_homeo
import Submission.Work.Whitney.exists_bundleIso_comap_tautQuotient_whitneySum
import Submission.Work.Whitney.chernClass_whitneySum_rank_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Whitney

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-- The punctured projection `π_E : E∖0 → B` of the realification of `E`. -/
abbrev punctProjE {ι : Type} {m : ℕ}
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι) :
    C(↥(Work.Thom.zeroComplement (Work.Thom.realification E)), B) :=
  (Work.Thom.bundleProj (Work.Thom.realification E)).comp
    (Work.Thom.subtypeMap (Work.Thom.zeroComplement (Work.Thom.realification E)))

/-- Continuity of the tautological section of `π_E^*E`, as a map of total spaces. -/
theorem continuous_tautSectionTotalE {ι : Type} {m : ℕ}
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι) :
    Continuous (fun x : ↥(Work.Thom.zeroComplement (Work.Thom.realification E)) =>
      (⟨x, (x : (Work.Thom.realification E).TotalSpace).2⟩ :
        (Work.Thom.realification (Work.Thom.bundleComap E (punctProjE E))).TotalSpace)) := by
  rw [show (Work.Thom.realification (Work.Thom.bundleComap E (punctProjE E)))
      = Work.Thom.bundleComap (Work.Thom.realification E) (punctProjE E)
      from Work.Thom.realification_bundleComap E (punctProjE E)]
  exact continuous_tautologicalSection (Work.Thom.realification E)

/-- The tautological section of `A = π_E^*E`: `x ↦ ⟨x, x⟩`, a continuous nowhere-zero section. -/
def tautSectionE {ι : Type} {m : ℕ}
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι) :
    C(↥(Work.Thom.zeroComplement (Work.Thom.realification E)),
      ↥(Work.Thom.zeroComplement
        (Work.Thom.realification (Work.Thom.bundleComap E (punctProjE E))))) where
  toFun x :=
    ⟨(⟨x, (x : (Work.Thom.realification E).TotalSpace).2⟩ :
        (Work.Thom.realification (Work.Thom.bundleComap E (punctProjE E))).TotalSpace),
      x.2⟩
  continuous_toFun := Continuous.subtype_mk (continuous_tautSectionTotalE E) (fun x => x.2)

/-- The tautological section lies over the identity. -/
theorem tautSectionE_proj {ι : Type} {m : ℕ}
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι) :
    ∀ x, (((tautSectionE E x : ↥(Work.Thom.zeroComplement
        (Work.Thom.realification (Work.Thom.bundleComap E (punctProjE E))))) :
      (Work.Thom.realification (Work.Thom.bundleComap E (punctProjE E))).TotalSpace)).1 = x :=
  fun x => rfl

/-- **The tautological quotient of `π_E^*E`, pulled back along the tautological section, is the
tautological quotient of `E`**: `σ^*(Q_{π^*E}) = Q_E`. -/
theorem bundleComap_tautQuotient_tautSectionE {ι : Type} [Fintype ι] {m : ℕ}
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι) :
    Work.Thom.bundleComap
        (Work.Thom.tautQuotient (Work.Thom.bundleComap E (punctProjE E))) (tautSectionE E)
      = Work.Thom.tautQuotient E := by
  have hcomp : (Work.Thom.punctMap E (punctProjE E)).comp (tautSectionE E)
      = ContinuousMap.id ↥(Work.Thom.zeroComplement (Work.Thom.realification E)) := by
    ext x
    · rw [ContinuousMap.comp_apply, Work.Thom.punctMap_apply]
      rfl
    · rw [ContinuousMap.comp_apply, Work.Thom.punctMap_apply]
      rfl
  rw [Work.Thom.tautQuotient, Work.Thom.tautQuotient,
    (Work.Thom.tautQuotientCore_comap E (punctProjE E)).symm,
    Work.Thom.bundleComap_comp, hcomp, Work.Thom.bundleComap_id]

/-- **Isomorphism-invariance of the Chern classes across a re-indexing of the model fibre.** -/
theorem chernClass_eq_of_cast_fibre_iso {a b : ℕ} (h : a = b) {B : Type} [TopologicalSpace B]
    {ι ι' : Type} [Fintype ι] [Fintype ι']
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι')
    (e : Work.Thom.BundleIso Z Z') (j : ℕ) :
    Work.Thom.chernClass a j Z = Work.Thom.chernClass b j Z' := by
  subst h
  exact Work.Thom.chernClass_BundleIso Z Z' e

/-- **Stability of the Chern classes along a nowhere-zero section, in a direct sum**: if the complex
bundle `A` of rank `r+1` carries the continuous nowhere-zero section `σ`, then for every complex
bundle `B` of rank `s+1`, the Chern classes of `A ⊕ B` are those of `σ^*(Q_A) ⊕ B`. -/
theorem pullbackEq_whitneySum_stability {Y : Type} [TopologicalSpace Y]
    {ι_A ι_B : Type} [Fintype ι_A] [Fintype ι_B] {r s : ℕ}
    (A : VectorBundleCore ℂ Y (EuclideanSpace ℂ (Fin (r + 1))) ι_A)
    (B : VectorBundleCore ℂ Y (EuclideanSpace ℂ (Fin (s + 1))) ι_B)
    (σ : C(Y, ↥(Work.Thom.zeroComplement (Work.Thom.realification A))))
    (hσ : ∀ y, (((σ y : ↥(Work.Thom.zeroComplement (Work.Thom.realification A))) :
      (Work.Thom.realification A).TotalSpace)).1 = y) (k : ℕ) :
    Work.Thom.chernClass ((r + 1) + (s + 1)) k
        (Work.Whitney.whitneySum (m₁ := r+1) (m₂ := s+1) A B)
      = Work.Thom.chernClass (r + (s + 1)) k
          (Work.Whitney.whitneySum (m₁ := r) (m₂ := s+1)
            (Work.Thom.bundleComap (Work.Thom.tautQuotient (m := r) A) σ) B) := by
  obtain ⟨sB, hsB, ⟨iso⟩⟩ :=
    exists_bundleIso_comap_tautQuotient_whitneySum A B σ hσ
  have hcens : Work.Thom.chernClass (((r + 1) + s) + 1) k
      (Work.Whitney.whitneySum (m₁ := r+1) (m₂ := s+1) A B)
      = Work.Thom.chernClass ((r + 1) + s) k
          (Work.Thom.bundleComap
            (Work.Thom.tautQuotient (m := (r+1)+s)
              (Work.Whitney.whitneySum (m₁ := r+1) (m₂ := s+1) A B)) sB) :=
    Work.Whitney.chernClass_eq_of_nowhereZeroSection
      (Z := Work.Whitney.whitneySum (m₁ := r+1) (m₂ := s+1) A B) (σ := sB) hsB k
  refine hcens.trans ?_
  exact chernClass_eq_of_cast_fibre_iso (by omega : (r + 1) + s = r + (s + 1)) _ _ iso k

theorem chernClass_whitneySum_pullback_eq {B : Type} [TopologicalSpace B]
    {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] {m₁ m₂ k : ℕ}
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m₁ + 1))) ι₁)
    (F : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Work.Thom.chernClass ((m₁ + 1) + m₂) k
        (Work.Thom.bundleComap (Work.Whitney.whitneySum E F)
          ((Work.Thom.bundleProj (Work.Thom.realification E)).comp
            (Work.Thom.subtypeMap (Work.Thom.zeroComplement (Work.Thom.realification E)))))
      = Work.Thom.chernClass (m₁ + m₂) k
          (Work.Whitney.whitneySum (Work.Thom.tautQuotient E)
            (Work.Thom.bundleComap F ((Work.Thom.bundleProj (Work.Thom.realification E)).comp
              (Work.Thom.subtypeMap (Work.Thom.zeroComplement (Work.Thom.realification E)))))) := by
  cases m₂ with
  | zero =>
    rw [Work.Whitney.whitneySum_bundleComap]
    rw [chernClass_whitneySum_rank_zero
      (Z := Work.Thom.bundleComap E (punctProjE E))
      (W := Work.Thom.bundleComap F (punctProjE E)) k]
    rw [chernClass_whitneySum_rank_zero
      (Z := Work.Thom.tautQuotient E)
      (W := Work.Thom.bundleComap F (punctProjE E)) k]
    rw [Work.Whitney.chernClass_eq_of_nowhereZeroSection
      (Z := Work.Thom.bundleComap E (punctProjE E)) (σ := tautSectionE E) (tautSectionE_proj E) k]
    rw [bundleComap_tautQuotient_tautSectionE E]
  | succ s =>
    rw [Work.Whitney.whitneySum_bundleComap]
    rw [pullbackEq_whitneySum_stability (r := m₁) (s := s)
      (A := Work.Thom.bundleComap E (punctProjE E))
      (B := Work.Thom.bundleComap F (punctProjE E)) (σ := tautSectionE E) (tautSectionE_proj E) k]
    rw [bundleComap_tautQuotient_tautSectionE E]

end

end Work.Whitney
