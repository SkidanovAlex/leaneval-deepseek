/-
# A globally smooth surrogate for the chart nonlinearity

The chart nonlinearity `Work.Diff.STE.Man.chartNonlin bg` is smooth only on the non-degeneracy
region `Set.univ ×ˢ {J | (reMat J.1).det ≠ 0}` (its principal part `secOpFlat` involves the matrix
inverse of the real part of the value jet).  The flat Cauchy problem, however, is stated for a
*globally* smooth nonlinearity.

This file produces such a global surrogate: given a compact `K` and a matrix-valued function `f`
which is *continuous on `K`* with `det (f p) ≠ 0` there, one finds a globally smooth
`Φ` which agrees with `chartNonlin bg` at every jet lying over `K`, i.e. at every point

  `(p.2, jetM (fun y => ofRealMat (f (p.1, y))) p.2)`,   `p ∈ K`.

The construction is a smooth cutoff *in the value variable only*: `K` is compact and `f` is
continuous, so the set `ofRealMat '' (f '' K)` of values is a compact subset of the open
non-degeneracy region, and the bump of `JointSmoothKit.exists_contDiff_tsupport_subset_isCompact`
can be used.  Multiplying `chartNonlin bg` by that bump makes the result smooth everywhere: where
the bump does not vanish we are inside the region where `chartNonlin bg` is smooth, and where it
vanishes the product is `0` on a whole neighbourhood.  In particular *no regularity of `f`
beyond continuity is used*: the (possibly junk) derivative components of the jet do not appear in
the cutoff.
-/
import Mathlib
import Submission.Work.Diff.STE.Lead.JointSmoothKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology

namespace Work.Diff.STE.Lead

theorem exists_smooth_surrogate_chartNonlin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (bg : (Fin (Work.Diff.STE.Man.dim E) → ℝ) → Work.Diff.EXT.MatE (E := E))
    (hbgsm : ContDiffOn ℝ (⊤ : ℕ∞) (Work.Diff.STE.Man.chartNonlin (E := E) bg)
      (Set.univ ×ˢ {J : Work.Diff.STE.Flat.Jet (Work.Diff.STE.Man.dim E) |
        (Work.Diff.STE.Flat.reMat (J.1)).det ≠ 0}))
    (f : ℝ × (Fin (Work.Diff.STE.Man.dim E) → ℝ) → Work.Diff.EXT.MatE (E := E))
    (K : Set (ℝ × (Fin (Work.Diff.STE.Man.dim E) → ℝ))) (hK : IsCompact K)
    (hfc : ContinuousOn f K)
    (hfdet : ∀ p ∈ K, (Matrix.of (f p)).det ≠ 0) :
    ∃ Φ : (Fin (Work.Diff.STE.Man.dim E) → ℝ) ×
        Work.Diff.STE.Flat.Jet (Work.Diff.STE.Man.dim E) →
        Work.Diff.STE.Flat.MatC (Work.Diff.STE.Man.dim E),
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      (∀ p ∈ K, Φ (p.2, Work.Diff.STE.Flat.jetM (fun y : Fin (Work.Diff.STE.Man.dim E) → ℝ =>
          Work.Diff.STE.Man.ofRealMat (E := E) (f (p.1, y))) p.2)
        = Work.Diff.STE.Man.chartNonlin (E := E) bg
            (p.2, Work.Diff.STE.Flat.jetM (fun y : Fin (Work.Diff.STE.Man.dim E) → ℝ =>
              Work.Diff.STE.Man.ofRealMat (E := E) (f (p.1, y))) p.2)) := by
  -- the non-degeneracy region in the value variable is open
  have hdetcont : Continuous (fun A : Work.Diff.STE.Flat.MatC (Work.Diff.STE.Man.dim E) =>
      (Work.Diff.STE.Flat.reMat A).det) := by
    apply Continuous.matrix_det
    apply continuous_matrix
    intro i j
    simp only [Work.Diff.STE.Flat.reMat_apply]
    exact Complex.continuous_re.comp ((continuous_apply j).comp (continuous_apply i))
  have hWopen : IsOpen {A : Work.Diff.STE.Flat.MatC (Work.Diff.STE.Man.dim E) |
      (Work.Diff.STE.Flat.reMat A).det ≠ 0} := isOpen_ne.preimage hdetcont
  -- `ofRealMat ∘ f` is continuous, so its image of `K` is compact
  have hofRcont : Continuous (fun A : Work.Diff.EXT.MatE (E := E) =>
      Work.Diff.STE.Man.ofRealMat (E := E) A) := by
    rw [continuous_pi_iff]
    intro i
    rw [continuous_pi_iff]
    intro j
    simp only [Work.Diff.STE.Man.ofRealMat_apply]
    exact Complex.continuous_ofReal.comp ((continuous_apply j).comp (continuous_apply i))
  have hSK : ((fun p : ℝ × (Fin (Work.Diff.STE.Man.dim E) → ℝ) =>
      Work.Diff.STE.Man.ofRealMat (E := E) (f p)) '' K) ⊆
      {A : Work.Diff.STE.Flat.MatC (Work.Diff.STE.Man.dim E) |
        (Work.Diff.STE.Flat.reMat A).det ≠ 0} := by
    rintro A ⟨p, hp, rfl⟩
    show (Work.Diff.STE.Flat.reMat (Work.Diff.STE.Man.ofRealMat (E := E) (f p))).det ≠ 0
    rw [Work.Diff.STE.Man.reMat_ofRealMat]
    exact hfdet p hp
  have hScomp : IsCompact ((fun p : ℝ × (Fin (Work.Diff.STE.Man.dim E) → ℝ) =>
      Work.Diff.STE.Man.ofRealMat (E := E) (f p)) '' K) :=
    hK.image_of_continuousOn (hofRcont.comp_continuousOn hfc)
  -- the cutoff in the value variable
  obtain ⟨θ, hθsm, hθtsup, hθone, hθnonneg⟩ :=
    exists_contDiff_tsupport_subset_isCompact hScomp hWopen hSK
  refine ⟨fun q => θ q.2.1 • Work.Diff.STE.Man.chartNonlin (E := E) bg q, ?_, ?_⟩
  -- smoothness: inside the support of `θ` the nonlinearity is smooth, outside the product vanishes
  · rw [contDiff_iff_contDiffAt]
    intro q
    by_cases hq : q.2.1 ∈ tsupport θ
    · have hqW : q.2.1 ∈ {A : Work.Diff.STE.Flat.MatC (Work.Diff.STE.Man.dim E) |
          (Work.Diff.STE.Flat.reMat A).det ≠ 0} := hθtsup hq
      have hVJopen : IsOpen {J : Work.Diff.STE.Flat.Jet (Work.Diff.STE.Man.dim E) |
          (Work.Diff.STE.Flat.reMat (J.1)).det ≠ 0} := by
        have h := hWopen.preimage (continuous_fst :
          Continuous (fun J : Work.Diff.STE.Flat.Jet (Work.Diff.STE.Man.dim E) => J.1))
        simpa using h
      have hmem : (Set.univ ×ˢ {J : Work.Diff.STE.Flat.Jet (Work.Diff.STE.Man.dim E) |
          (Work.Diff.STE.Flat.reMat (J.1)).det ≠ 0}) ∈ 𝓝 q :=
        IsOpen.mem_nhds (IsOpen.prod isOpen_univ hVJopen) ⟨trivial, hqW⟩
      have hsmθ : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : (Fin (Work.Diff.STE.Man.dim E) → ℝ) ×
          Work.Diff.STE.Flat.Jet (Work.Diff.STE.Man.dim E) => θ q.2.1) q := by fun_prop
      exact hsmθ.smul (hbgsm.contDiffAt hmem)
    · have h0 : θ =ᶠ[𝓝 q.2.1] (fun _ => (0 : ℝ)) :=
        notMem_tsupport_iff_eventuallyEq.mp hq
      have h0' : (fun q' : (Fin (Work.Diff.STE.Man.dim E) → ℝ) ×
            Work.Diff.STE.Flat.Jet (Work.Diff.STE.Man.dim E) => θ q'.2.1)
          =ᶠ[𝓝 q] (fun _ => (0 : ℝ)) :=
        h0.comp_tendsto ((continuous_fst.comp continuous_snd).continuousAt)
      refine (contDiffAt_const (c :=
        (0 : Work.Diff.STE.Flat.MatC (Work.Diff.STE.Man.dim E)))).congr_of_eventuallyEq ?_
      filter_upwards [h0'] with q' hq'
      rw [hq', zero_smul]
  -- agreement: the value at a jet over `K` lies in the image of `K`, where the cutoff is `1`
  · intro p hp
    have hpS : Work.Diff.STE.Man.ofRealMat (E := E) (f p) ∈
        ((fun p : ℝ × (Fin (Work.Diff.STE.Man.dim E) → ℝ) =>
          Work.Diff.STE.Man.ofRealMat (E := E) (f p)) '' K) := ⟨p, hp, rfl⟩
    have hθ1 : θ (Work.Diff.STE.Man.ofRealMat (E := E) (f p)) = 1 := hθone _ hpS
    have hjet : (Work.Diff.STE.Flat.jetM (fun y : Fin (Work.Diff.STE.Man.dim E) → ℝ =>
        Work.Diff.STE.Man.ofRealMat (E := E) (f (p.1, y))) p.2).1
        = Work.Diff.STE.Man.ofRealMat (E := E) (f p) := by
      simp only [Work.Diff.STE.Flat.jetM, Prod.mk.eta]
    dsimp only
    rw [hjet, hθ1, one_smul]

end Work.Diff.STE.Lead
