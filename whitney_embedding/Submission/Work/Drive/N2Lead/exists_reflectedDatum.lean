import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2Lead.saddlePinDefs

/-!
# The coordinate-swap reflection of a window datum

`Work.Drive.N2Lead.exists_reflectedDatum` rebuilds a window datum `D` with the two model
coordinates of **every** chart exchanged and the two chart signs `s₁`, `s₂` simultaneously
exchanged.  Every field of the datum that mentions a chart does so through its source, its target,
its inverse, the norm of its values (`modelBall`), the product `φ y 0 * φ y 1` (`chartQ`, the saddle
pin set), or the *pair* `(s₁ * φ y 0, s₂ * φ y 1)` in the model ODE — and all of these are
invariant under the exchange.  In particular all the data attached to the marked index `j`
(`ρ j`, `C j`, `ηd`, `x j`, `Φ`, the pin sets) are those of `D`, and if the marked signs of `D` are
`(-1, 1)` then those of the reflected datum are `(1, -1)`.

The exchange is the linear isometry `swapE2 : (z₀, z₁) ↦ (z₁, z₀)` of the model plane; the chart at
index `i` becomes `swapChart (D.φ i) := (D.φ i).trans swapE2.toOpenPartialHomeomorph`.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

/-- The coordinate swap `(z₀, z₁) ↦ (z₁, z₀)` of the model plane `ℝ²`, as a linear isometry. -/
noncomputable def swapE2 : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 1)

lemma swapE2_apply_apply (z : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    swapE2 z i = z (1 - i) := by
  fin_cases i <;>
    simp [swapE2, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]

lemma swapE2_zero (z : EuclideanSpace ℝ (Fin 2)) : swapE2 z 0 = z 1 := by
  simpa using swapE2_apply_apply z 0

lemma swapE2_one (z : EuclideanSpace ℝ (Fin 2)) : swapE2 z 1 = z 0 := by
  simpa using swapE2_apply_apply z 1

lemma swapE2_contMDiff :
    ContMDiff (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) swapE2 :=
  (LinearIsometryEquiv.contDiff swapE2).contMDiff

/-- The chart obtained from `φ` by exchanging the two model coordinates. -/
noncomputable def swapChart {M : Type*} [TopologicalSpace M]
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)) :=
  φ.trans (Homeomorph.toOpenPartialHomeomorph swapE2.toHomeomorph)

variable {M : Type*} [TopologicalSpace M]

lemma swapChart_source (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) :
    (swapChart φ).source = φ.source := by
  rw [swapChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, Set.preimage_univ, Set.inter_univ]

lemma swapChart_apply (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (y : M) :
    swapChart φ y = swapE2 (φ y) := by
  rw [swapChart, OpenPartialHomeomorph.trans_apply,
    Homeomorph.toOpenPartialHomeomorph_apply, LinearIsometryEquiv.coe_toHomeomorph]

lemma swapChart_symm_apply (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (z : EuclideanSpace ℝ (Fin 2)) :
    (swapChart φ).symm z = φ.symm (swapE2.symm z) := by
  rw [swapChart, OpenPartialHomeomorph.coe_trans_symm,
    Homeomorph.toOpenPartialHomeomorph_symm_apply, ← LinearIsometryEquiv.toHomeomorph_symm,
    LinearIsometryEquiv.coe_toHomeomorph]
  rfl

lemma swapChart_target (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) :
    (swapChart φ).target = swapE2.symm ⁻¹' φ.target := by
  rw [swapChart, OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target, Set.univ_inter,
    Homeomorph.toOpenPartialHomeomorph_symm_apply, ← LinearIsometryEquiv.toHomeomorph_symm,
    LinearIsometryEquiv.coe_toHomeomorph]

theorem exists_reflectedDatum {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (h1 : D.s₁ D.j = -1) (h2 : D.s₂ D.j = 1) :
    ∃ D' : Work.Drive.N2.WindowDatum f p,
      D'.s₁ D'.j = 1 ∧ D'.s₂ D'.j = -1 ∧
      (D'.φ D'.j).source = (D.φ D.j).source ∧
      (∀ y : M, y ∈ (D.φ D.j).source →
        ∀ i : Fin 2, D'.φ D'.j y i = D.φ D.j y (1 - i)) ∧
      D'.ρ D'.j = D.ρ D.j ∧ D'.C D'.j = D.C D.j ∧ D'.ηd = D.ηd ∧
      D'.x D'.j = D.x D.j ∧ (∀ y : ℝ × M, D'.Φ y = D.Φ y) ∧
      (∀ (v m : ℝ), Work.Drive.N2Lead.saddlePin D' v m =
        Work.Drive.N2Lead.saddlePin D v m) := by
  classical
  -- the exchanged chart family and signs
  let φ' : Fin D.N → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)) :=
    fun i => swapChart (D.φ i)
  let s₁' : Fin D.N → ℝ := fun i => D.s₂ i
  let s₂' : Fin D.N → ℝ := fun i => D.s₁ i
  have hsrc : ∀ i, (φ' i).source = (D.φ i).source := fun i => swapChart_source (D.φ i)
  have happ : ∀ i (y : M), φ' i y = swapE2 (D.φ i y) := fun i y => swapChart_apply (D.φ i) y
  have hsymm : ∀ i (z : EuclideanSpace ℝ (Fin 2)),
      (φ' i).symm z = (D.φ i).symm (swapE2.symm z) :=
    fun i z => swapChart_symm_apply (D.φ i) z
  have htgt : ∀ i, (φ' i).target = swapE2.symm ⁻¹' (D.φ i).target :=
    fun i => swapChart_target (D.φ i)
  have hnorm : ∀ i (y : M), ‖φ' i y‖ = ‖D.φ i y‖ := by
    intro i y
    rw [happ i y, swapE2.norm_map]
  have hball : ∀ i (r : ℝ),
      Work.Drive.N2.modelBall (φ' i) r = Work.Drive.N2.modelBall (D.φ i) r := by
    intro i r
    ext y
    simp only [Work.Drive.N2.modelBall, Set.mem_ofPred_eq, hsrc i]
    by_cases hy : y ∈ (D.φ i).source
    · simp [hy, hnorm i y]
    · simp [hy]
  let D' : Work.Drive.N2.WindowDatum f p :=
    { N := D.N
      x := D.x
      φ := φ'
      s₁ := s₁'
      s₂ := s₂'
      ρ := D.ρ
      C := D.C
      j := D.j
      hxj := D.hxj
      hinj := D.hinj
      hcrit := D.hcrit
      hcover := D.hcover
      hρ := D.hρ
      hsrc := by
        intro i
        rw [hsrc i]
        exact D.hsrc i
      hcen := by
        intro i
        rw [happ i (D.x i), D.hcen i, map_zero]
      hsgn := by
        intro i
        exact ⟨(D.hsgn i).2, (D.hsgn i).1⟩
      hval := by
        intro i y hy
        have hy' : y ∈ (D.φ i).source := by rwa [hsrc i] at hy
        have hq : s₁' i * (φ' i y 0) ^ 2 + s₂' i * (φ' i y 1) ^ 2
            = D.s₁ i * (D.φ i y 0) ^ 2 + D.s₂ i * (D.φ i y 1) ^ 2 := by
          rw [happ i y, swapE2_zero, swapE2_one]
          ring
        simp only [Work.Drive.N2.chartQ]
        rw [hq]
        exact D.hval i y hy'
      hφ := by
        intro i
        have hσ : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) swapE2 Set.univ :=
          swapE2_contMDiff.contMDiffOn
        have hcomp : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun y : M => swapE2 (D.φ i y)) (D.φ i).source :=
          hσ.comp (D.hφ i) (fun y _ => Set.mem_univ _)
        rw [hsrc i]
        refine hcomp.congr ?_
        intro y _
        exact happ i y
      hφ' := by
        intro i
        have hσ : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun z : EuclideanSpace ℝ (Fin 2) => swapE2.symm z)
            (swapE2.symm ⁻¹' (D.φ i).target) :=
          ((LinearIsometryEquiv.contDiff swapE2.symm).contMDiff).contMDiffOn.mono
            (Set.subset_univ _)
        have hcomp : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun z : EuclideanSpace ℝ (Fin 2) => (D.φ i).symm (swapE2.symm z))
            (swapE2.symm ⁻¹' (D.φ i).target) :=
          (D.hφ' i).comp hσ (fun z hz => hz)
        rw [htgt i]
        refine hcomp.congr ?_
        intro z _
        exact hsymm i z
      hdisj := by
        intro i j' hij
        rw [hsrc i, hsrc j']
        exact D.hdisj i j' hij
      hCsub := by
        intro i
        rw [hsrc i]
        exact D.hCsub i
      hCclosed := D.hCclosed
      hCcl := by
        intro i
        rw [hsrc i]
        exact D.hCcl i
      hCball := by
        intro i
        rw [hball i (D.ρ i / 8)]
        exact D.hCball i
      hCop := by
        intro i
        change Work.Drive.N2.modelBall (φ' i) (D.ρ i) ⊆ D.C i
        rw [hball i (D.ρ i)]
        exact D.hCop i
      ηd := D.ηd
      hηd := D.hηd
      hηd' := D.hηd'
      hsep := D.hsep
      hsepK := by
        intro i j' hij z hz
        rw [hball i (D.ρ i / 8)] at hz
        exact D.hsepK i j' hij z hz
      Φ := D.Φ
      hΦsm := D.hΦsm
      hΦ0 := D.hΦ0
      hΦcomp := D.hΦcomp
      hlevel := by
        intro y t hy
        refine D.hlevel y t ?_
        intro u hu i
        have h1 : D.Φ (u, y) ∉ Work.Drive.N2.modelBall (φ' i) (D.ρ i / 8) := hy u hu i
        rwa [hball i (D.ρ i / 8)] at h1
      hODE := by
        intro i y t ht
        obtain ⟨h0, h1⟩ := D.hODE i y t ht
        constructor
        · have hfun : (fun σ : ℝ => φ' i (D.Φ (σ, y)) 0)
              = fun σ : ℝ => D.φ i (D.Φ (σ, y)) 1 := by
            funext σ
            rw [happ i (D.Φ (σ, y)), swapE2_zero]
          rw [hfun]
          have hval : Work.Drive.N2.chartMult (D.ρ i / 8) (‖φ' i (D.Φ (t, y))‖ ^ 2) *
                (s₁' i * φ' i (D.Φ (t, y)) 0)
              = Work.Drive.N2.chartMult (D.ρ i / 8) (‖D.φ i (D.Φ (t, y))‖ ^ 2) *
                (D.s₂ i * D.φ i (D.Φ (t, y)) 1) := by
            rw [happ i (D.Φ (t, y)), swapE2_zero, swapE2.norm_map]
          rw [hval]
          exact h1
        · have hfun : (fun σ : ℝ => φ' i (D.Φ (σ, y)) 1)
              = fun σ : ℝ => D.φ i (D.Φ (σ, y)) 0 := by
            funext σ
            rw [happ i (D.Φ (σ, y)), swapE2_one]
          rw [hfun]
          have hval : Work.Drive.N2.chartMult (D.ρ i / 8) (‖φ' i (D.Φ (t, y))‖ ^ 2) *
                (s₂' i * φ' i (D.Φ (t, y)) 1)
              = Work.Drive.N2.chartMult (D.ρ i / 8) (‖D.φ i (D.Φ (t, y))‖ ^ 2) *
                (D.s₁ i * D.φ i (D.Φ (t, y)) 0) := by
            rw [happ i (D.Φ (t, y)), swapE2_one, swapE2.norm_map]
          rw [hval]
          exact h0
      hmono := D.hmono }
  have hDφ : D'.φ = φ' := rfl
  have hDj : D'.j = D.j := rfl
  have hDs₁ : D'.s₁ = s₁' := rfl
  have hDs₂ : D'.s₂ = s₂' := rfl
  have hDρ : D'.ρ = D.ρ := rfl
  have hDC : D'.C = D.C := rfl
  have hDη : D'.ηd = D.ηd := rfl
  have hDx : D'.x = D.x := rfl
  have hDΦ : D'.Φ = D.Φ := rfl
  refine ⟨D', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hDs₁, hDj]
    exact h2
  · rw [hDs₂, hDj]
    exact h1
  · rw [hDφ, hDj]
    exact hsrc D.j
  · intro y _ i
    rw [hDφ, hDj, happ D.j y, swapE2_apply_apply]
  · rw [hDρ, hDj]
  · rw [hDC, hDj]
  · rw [hDη]
  · rw [hDx, hDj]
  · intro y
    rw [hDΦ]
  · intro v m
    ext x
    simp only [Work.Drive.N2Lead.saddlePin, Set.mem_ofPred_eq]
    have hkey : 2 * (φ' D.j x 0) * (φ' D.j x 1) = 2 * (D.φ D.j x 0) * (D.φ D.j x 1) := by
      rw [happ D.j x, swapE2_zero, swapE2_one]
      ring
    rw [hDφ, hDj, hDρ, hsrc D.j, hnorm D.j x, hkey]

end Work.Drive.N2Lead
