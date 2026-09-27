import Mathlib
import Submission.Work.Drive.classTripleRegular
import Submission.Work.Drive.classTripleSystem
import Submission.Work.Drive.genericRegularizationSquare
import Submission.Work.Drive.classSystem_hsurj
import Submission.Work.Drive.exists_perturbation_family_gl
import Submission.Work.Drive.classTripleRegular_conditions_of_classSystem_regular

/-!
# The assembly of `L5`: `∃ small A, ClassTripleRegular (linCapping (A k) ∘ P k)`

This file puts together the pieces of the `L5` lane (see
`Submission/Work/Drive/L5_CHAIN_STATUS.md`): the class system of `classTripleSystem.lean`, the
square-case parametric Sard of `genericRegularizationSquare.lean`, the parameter-derivative lemma
`classSystem_hsurj` (in the ball-restricted form the Sard statement consumes), the concrete
perturbation family `exists_perturbation_family_gl`, and the conversion
`classTripleRegular_conditions_of_classSystem_regular`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology LinearAlgebra.Projectivization

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-! ## 0. Two elementary facts about the parameter boxes -/

/-- The unit box of the square parameter space is compact: it is the image of the compact box of
`Amb n` under the block projection. -/
lemma isCompact_tgtBox (n : ℕ) : IsCompact (tgtBox n) := by
  have h : tgtBox n = sqProj n '' Submission.Drive.unitBox n := by
    ext y
    constructor
    · intro hy
      exact ⟨sqSnoc n y, sqSnoc_mem_unitBox hy, sqProj_sqSnoc n y⟩
    · rintro ⟨x, hx, rfl⟩
      intro i
      have := hx (Fin.castSucc i)
      simpa [sqProj_apply] using this
  rw [h]
  exact (isCompact_unitBox n).image (sqProj n).continuous

/-- The parameter-derivative of the class system is onto at a zero, from the *joint* surjectivity of
the perturbation family — in the ball-restricted form in which the parametric-Sard statement
consumes it. -/
theorem classSystem_hsurj_ball {m : ℕ} (V : Fin 3 → EuclideanSpace ℝ (Fin 2) → Eucl 3)
    (A : EuclideanSpace ℝ (Fin m) → Fin 3 → Eucl 3 →L[ℝ] Eucl 3)
    (hA : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin m) × Eucl 3 => A z.1 k z.2))
    (ε₀ : ℝ) (hjoint : ∀ (p : EuclideanSpace ℝ (Fin m)) (y : Tgt 6), ‖p‖ ≤ ε₀ →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) =>
        fun k : Fin 3 => A p' k (V k (parOf y k))) p))
    (p : EuclideanSpace ℝ (Fin m)) (y : Tgt 6) (hp : ‖p‖ ≤ ε₀)
    (hVne : ∀ k, V k (parOf y k) ≠ 0)
    (hAinj : ∀ k, Function.Injective (A p k))
    (hzero : classSystem V A p y = 0) :
    Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) =>
      classSystem V A p' y) p) := by
  set G : EuclideanSpace ℝ (Fin m) → (Fin 3 → Eucl 3) :=
    fun p' k => A p' k (V k (parOf y k)) with hG
  have hGsurj : Function.Surjective (fderiv ℝ G p) := hjoint p y hp
  have hGdiff : DifferentiableAt ℝ G p := by
    rw [hG]
    rw [differentiableAt_pi]
    intro k
    have hAz : DifferentiableAt ℝ
        (fun z : EuclideanSpace ℝ (Fin m) × Eucl 3 => A z.1 k z.2) (p, V k (parOf y k)) :=
      ((hA k).differentiable (by simp)).differentiableAt
    have hpair : DifferentiableAt ℝ
        (fun p' : EuclideanSpace ℝ (Fin m) => (p', V k (parOf y k))) p :=
      differentiableAt_id.prodMk (differentiableAt_const (V k (parOf y k)))
    exact hAz.comp p hpair
  have hx0 : G p 0 ≠ 0 := by
    intro h
    exact hVne 0 (hAinj 0 (by simpa using h))
  have hcsDiff : DifferentiableAt ℝ ClassSystemHsurj.csMap (G p) :=
    (ClassSystemHsurj.hasFDerivAt_csMap (G p)).differentiableAt
  have hfun : (fun p' : EuclideanSpace ℝ (Fin m) => classSystem V A p' y)
      = (fun p' => ClassSystemHsurj.csMap (G p')) := rfl
  rw [hfun]
  have hcomp : fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) =>
        ClassSystemHsurj.csMap (G p')) p
      = (fderiv ℝ ClassSystemHsurj.csMap (G p)).comp (fderiv ℝ G p) :=
    fderiv_comp (f := G) (g := ClassSystemHsurj.csMap) p hcsDiff hGdiff
  rw [hcomp]
  intro z
  obtain ⟨a, ha⟩ := ClassSystemHsurj.csMap_fderiv_surjective (x := G p) hx0 z
  obtain ⟨b, hb⟩ := hGsurj a
  exact ⟨b, by rw [ContinuousLinearMap.comp_apply, hb, ha]⟩

/-! ## 1. The plane parameters as a point of `Tgt 6` -/

/-- Stacking three plane parameters into a point of `Tgt 6`. -/
def stackY (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) : Tgt 6 :=
  WithLp.toLp 2 (fun j : Fin 6 =>
    let g := (finProdFinEquiv (m := 3) (n := 2)).symm j
    y g.1 g.2)

@[simp] lemma parOf_stackY (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) (k : Fin 3) :
    parOf (stackY y) k = y k := by
  ext i
  show (WithLp.toLp 2 (fun j : Fin 6 => let g := (finProdFinEquiv (m := 3) (n := 2)).symm j
    y g.1 g.2)).ofLp (parC k i) = y k i
  rw [WithLp.ofLp_toLp, parC, Equiv.symm_apply_apply]

lemma openSquare_mem_tgtBox {y : Fin 3 → EuclideanSpace ℝ (Fin 2)}
    (hy : ∀ k, openSquare (y k)) : stackY y ∈ tgtBox 6 := by
  refine mem_tgtBox_six (fun k => ?_)
  rw [parOf_stackY]
  intro i
  fin_cases i
  · exact ⟨(hy k).1.1.le, (hy k).1.2.le⟩
  · exact ⟨(hy k).2.1.le, (hy k).2.2.le⟩

/-- The class map of a class-perturbed plane presentation is the projectivisation of the perturbed
lift. -/
lemma planeClassMap_linCapping_eq_of_lift {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {V : EuclideanSpace ℝ (Fin 2) → Eucl 3} (hVne : ∀ y, V y ≠ 0)
    (hVcls : ∀ y ∈ Submission.Drive.unitBox 1,
      Projectivization.mk ℝ (V y) (hVne y) = planeClassMap P y)
    (A : Eucl 3 ≃L[ℝ] Eucl 3) {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ Submission.Drive.unitBox 1) (h : A (V y) ≠ 0) :
    planeClassMap ((linCapping A) ∘ P) y
      = Projectivization.mk ℝ (A (V y)) h := by
  rw [show planeClassMap ((linCapping A) ∘ P) y
      = Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective (planeClassMap P y) from
    congrArg Prod.snd (cappingSpaceHomeoProj_linCapping A (P y))]
  rw [← hVcls y hy, Projectivization.map_mk]
  rfl

/-- The perturbation family applied to a parameter, as plain continuous linear maps. -/
abbrev famCLM (A : EuclideanSpace ℝ (Fin 48) → Fin 3 →
    (EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4)))
    (p : EuclideanSpace ℝ (Fin 48)) : Fin 3 → EuclideanSpace ℝ (Fin 4) →L[ℝ]
      EuclideanSpace ℝ (Fin 4) :=
  fun k => (A p k : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))

/-- The class system of the concrete perturbation family. -/
abbrev famSystem (V : Fin 3 → EuclideanSpace ℝ (Fin 2) → Eucl 3)
    (A : EuclideanSpace ℝ (Fin 48) → Fin 3 →
      (EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4))) :
    EuclideanSpace ℝ (Fin 48) × Tgt 6 → Tgt 6 :=
  fun x => classSystem V (famCLM A) x.1 x.2

/-- **The main genericity theorem of the `L5` lane.**  Given plane presentations together with the
unperturbed seam and immersion data and non-vanishing smooth lifts of their class maps, there are
arbitrarily small perturbations `A k` of the classes for which the perturbed triple is
`ClassTripleRegular`. -/
theorem exists_small_classTripleRegular
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Ctop (P k))
    (hPseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y → P k y = P k (seamInv2 y))
    (hci : ∀ y : Fin 3 → EuclideanSpace ℝ (Fin 2), (∀ k, openSquare (y k)) → ∀ k,
      Function.Injective (mfderiv (𝓡 2) (𝓡 3) (planeClassMap (P k)) (mk2 (y k 0) (y k 1))))
    (V : Fin 3 → EuclideanSpace ℝ (Fin 2) → Eucl 3)
    (hVne : ∀ k y, V k y ≠ 0)
    (hVsmooth : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V k))
    (hVcls : ∀ k y, y ∈ Submission.Drive.unitBox 1 →
      Projectivization.mk ℝ (V k y) (hVne k y) = planeClassMap (P k) y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3,
      (∀ k, ‖(A k : Eucl 3 →L[ℝ] Eucl 3) - 1‖ < ε) ∧
      ClassTripleRegular (fun k => linCapping (A k) ∘ P k) := by
  classical
  obtain ⟨A, ε₀, hε₀, hA0, hAbound, hAsmooth, hAjoint, hAinj⟩ := exists_perturbation_family_gl
  set ε₁ : ℝ := min (ε / 32) (ε₀ / 2) with hε₁
  have hε₁pos : 0 < ε₁ := lt_min (by linarith) (by linarith)
  have hε₁ε₀ : ε₁ < ε₀ := (min_le_right _ _).trans_lt (by linarith)
  have hε₁ε : ε₁ ≤ ε / 32 := min_le_left _ _
  -- the system is smooth
  have hsys : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (famSystem V A) :=
    contDiff_classSystem V (famCLM A) hVsmooth (fun k => hAsmooth k)
  -- its parameter derivative is onto at every zero of the box
  have hsurj : ∀ (p : EuclideanSpace ℝ (Fin 48)) (z : Tgt 6), ‖p‖ ≤ ε₀ → z ∈ tgtBox 6 →
      famSystem V A (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin 48) =>
        famSystem V A (p', z)) p) := fun p z hp hz h0 =>
    classSystem_hsurj_ball V (famCLM A) (fun k => hAsmooth k) ε₀
      (fun p' y' hp' => hAjoint p' (fun k => V k (parOf y' k)) hp'
        (fun k => hVne k (parOf y' k)))
      p z hp (fun k => hVne k (parOf z k)) (fun k => hAinj k p hp) h0
  obtain ⟨p, hpε, hpreg⟩ := exists_forall_good_square_on_compact_ball 48 6 (tgtBox 6)
    (isCompact_tgtBox 6) (fun _ h => h) ε₀ ε₁ hε₀ hε₁pos hε₁ε₀ (famSystem V A) hsys hsurj
  refine ⟨A p, ?_, ?_⟩
  · intro k
    have h1 : ‖(A p k : Eucl 3 →L[ℝ] Eucl 3) - 1‖ ≤ 16 * ‖p‖ := hAbound k p
    have h2 : 16 * ‖p‖ < 16 * ε₁ := by linarith
    have h3 : 16 * ε₁ ≤ 16 * (ε / 32) := by linarith
    linarith
  · refine ⟨fun k => (contMDiff_linCapping (A p k)).comp (hP k), ?_, ?_, ?_⟩
    · intro k y hy
      exact congrArg (linCapping (A p k)) (hPseam k y hy)
    · intro y hy k
      exact injective_mfderiv_cls_linCapping (A p k) (P k) (mk2 (y k 0) (y k 1))
        (mdifferentiableAt_cls_of_contMDiff (hP k) _) (hci y hy k)
    · intro y hy hcommon
      have hybox : ∀ k, parOf (stackY y) k ∈ Submission.Drive.unitBox 1 := by
        intro k
        rw [parOf_stackY]
        intro i
        fin_cases i
        · exact ⟨(hy k).1.1.le, (hy k).1.2.le⟩
        · exact ⟨(hy k).2.1.le, (hy k).2.2.le⟩
      have hconv : ∀ k, (parOf (stackY y) k) 0 ∈ Set.Ioo (0 : ℝ) 1 ∧
          (parOf (stackY y) k) 1 ∈ Set.Ioo (0 : ℝ) 1 := fun k =>
        (parOf_stackY y k) ▸ hy k
      have hprop : ∀ k : Fin 3, ∃ a : ℝ,
          a • (A p 0 : Eucl 3 →L[ℝ] Eucl 3) (V 0 (parOf (stackY y) 0))
            = (A p k : Eucl 3 →L[ℝ] Eucl 3) (V k (parOf (stackY y) k)) := by
        intro k
        have h0 : (A p 0 : Eucl 3 →L[ℝ] Eucl 3) (V 0 (parOf (stackY y) 0)) ≠ 0 :=
          fun h => hVne 0 (parOf (stackY y) 0) ((A p 0).injective (by simpa using h))
        have hk : (A p k : Eucl 3 →L[ℝ] Eucl 3) (V k (parOf (stackY y) k)) ≠ 0 :=
          fun h => hVne k (parOf (stackY y) k) ((A p k).injective (by simpa using h))
        have heq : Projectivization.mk ℝ ((A p k : Eucl 3 →L[ℝ] Eucl 3)
              (V k (parOf (stackY y) k))) hk
            = Projectivization.mk ℝ ((A p 0 : Eucl 3 →L[ℝ] Eucl 3)
              (V 0 (parOf (stackY y) 0))) h0 := by
          have h1 := hcommon k
          rw [← parOf_stackY y k, ← parOf_stackY y 0] at h1
          rw [planeClassMap_linCapping_eq_of_lift (hVne k) (hVcls k) (A p k)
                (hybox k) hk,
            planeClassMap_linCapping_eq_of_lift (hVne 0) (hVcls 0) (A p 0)
                (hybox 0) h0] at h1
          exact h1
        obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℝ _ _ hk h0).mp heq
        exact ⟨(a : ℝ), ha⟩
      have hzero : classSystem V (famCLM A) p (stackY y) = 0 :=
        classSystem_eq_zero_of_proportional V (famCLM A) p (stackY y) hprop
      have hpε₀ : ‖p‖ ≤ ε₀ := le_of_lt (lt_of_lt_of_le hpε hε₁ε₀.le)
      have hres := classTripleRegular_conditions_of_classSystem_regular P V hVne hVsmooth hVcls
        (A p) p (stackY y) hconv (fun k => hAinj k p hpε₀) hzero
        (hpreg (stackY y) (openSquare_mem_tgtBox hy) hzero)
      exact hres.2

end

end Work.Drive
