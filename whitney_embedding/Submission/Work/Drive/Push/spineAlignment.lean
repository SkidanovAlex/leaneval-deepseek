import Mathlib
import Submission.Work.Drive.Push.spineUnknottingLocal
import Submission.Work.Drive.Push.smoothReparamOn
import Submission.Work.Drive.Push.planeFamilyAlignment
import Submission.Work.Whitney.CutPush.spine_plane_family
import Submission.Work.Whitney.CutPush.fibered_alignment
import Submission.Work.Compat.MFDerivCongrV433

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# Straightening and aligning the spine (the first half of `Work.Drive.Push.tubeFlattening`)

`Work.Drive.Push.spineAlignment` has the same statement as `Work.Drive.Push.alignedSpine`, but is
proved from the bricks

* `exists_unknotting_of_spine_local` (straighten the arc),
* `exists_plane_family_of_spine` (the plane field along the spine),
* `smoothReparamOn` (clamp the parameter into a small interval around `[0,1]` on which the plane
  field still fixes `e` and its `e`-component does not vanish),
* `planeFamilyAlignment` (the alignment of a globally projecting family),
* `exists_fibered_alignment` (realise it as the derivative of a global diffeomorphism).
-/

namespace Work.Drive.Push

open scoped Manifold ContDiff
open Topology Set

set_option backward.isDefEq.respectTransparency false

/-- **The range of the derivative of the aligned sheet along the spine.**  Chain rule, together with
the two range identifications `range (mfderiv F (δ t)) = range (P t)` and
`range (M t ∘ P t) = range (P 0)`. -/
theorem range_mfderiv_aligned_comp' {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (F : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hF : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (A₂ : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
    (hA₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A₂)
    (a e : EuclideanSpace ℝ (Fin (2 * n)))
    (Mfam : ℝ → EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)))
    (hder : ∀ s : ℝ, ∀ v : EuclideanSpace ℝ (Fin (2 * n)),
      fderiv ℝ A₂ (a + s • e) v = Mfam s v)
    (δ : ℝ → M)
    (haff : ∀ t ∈ Set.Icc (0 : ℝ) 1, F (δ t) = a + t • e)
    (P : ℝ → EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)))
    (hPr : ∀ t ∈ Set.Icc (0 : ℝ) 1, LinearMap.range (P t).toLinearMap
      = LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F (δ t)).toLinearMap)
    (hMr : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      LinearMap.range ((Mfam t).toLinearMap.comp (P t).toLinearMap)
        = LinearMap.range (P 0).toLinearMap) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
        (fun y : M => A₂ (F y)) (δ t)).toLinearMap
      = LinearMap.range (P 0).toLinearMap := by
  intro t ht
  have hmdF : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F (δ t) :=
    hF.mdifferentiableAt (by simp)
  have hmdA : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) A₂ (F (δ t)) :=
    hA₂.contMDiff.mdifferentiableAt (by simp)
  have hchain : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
        (fun y : M => A₂ (F y)) (δ t)
      = (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) A₂ (F (δ t))).comp
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F (δ t)) :=
    mfderiv_comp (δ t) hmdA hmdF
  have hMA : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) A₂ (F (δ t)) = Mfam t := by
    rw [mfderiv_eq_fderiv]
    ext v
    rw [haff t ht, hder t v]
  rw [hchain, hMA, ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp,
    ← hPr t ht, ← LinearMap.range_comp, hMr t ht]

/-- **Straightening and aligning the spine.** -/
theorem spineAlignment {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (δ : ℝ → M)
    (hδ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) δ)
    (hδimm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → Function.Injective
      (mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) δ t))
    (hδinj : Set.InjOn δ (Set.Icc (0 : ℝ) 1))
    (O : Set M) (hO : IsOpen O) (hδO : δ '' Set.Icc (0 : ℝ) 1 ⊆ O) (hOinj : Set.InjOn f O) :
    ∃ (A₁ A₁i A₂ A₂i : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
      (K : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n))))
      (a e : EuclideanSpace ℝ (Fin (2 * n))),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A₁ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A₁i ∧
      Function.LeftInverse A₁i A₁ ∧ Function.RightInverse A₁i A₁ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A₂ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A₂i ∧
      Function.LeftInverse A₂i A₂ ∧ Function.RightInverse A₂i A₂ ∧
      e ≠ 0 ∧ Module.finrank ℝ K = n ∧
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → A₂ (A₁ (f (δ t))) = a + t • e) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
          (fun y : M => A₂ (A₁ (f y))) (δ t)).toLinearMap = K) := by
  classical
  -- ## 1. straighten the arc
  obtain ⟨A₁, A₁i, hA₁, hA₁i, hA₁l, hA₁r, hA₁aff⟩ :=
    exists_unknotting_of_spine_local hn f hf himm δ hδ hδimm hδinj O hO hδO hOinj
  set a : EuclideanSpace ℝ (Fin (2 * n)) := f (δ 0) with ha
  set e : EuclideanSpace ℝ (Fin (2 * n)) := f (δ 1) - f (δ 0) with hedef
  have he : e ≠ 0 := by
    intro hzero
    rw [hedef, sub_eq_zero] at hzero
    have h1 : δ 1 = δ 0 :=
      hOinj (hδO (mem_image_of_mem δ (by norm_num)))
        (hδO (mem_image_of_mem δ (by norm_num))) hzero
    have h2 : (1 : ℝ) = 0 := hδinj (by norm_num) (by norm_num) h1
    norm_num at h2
  have haff0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, A₁ (f (δ t)) = a + t • e := by
    intro t ht
    rw [ha, hedef]
    exact hA₁aff t ht
  set E₁ : M → EuclideanSpace ℝ (Fin (2 * n)) := fun y => A₁ (f y) with hE₁
  have hE₁sm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) E₁ :=
    hA₁.contMDiff.comp hf
  have hE₁imm : ∀ y : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) E₁ y) :=
    Work.Whitney.CutPush.mfderiv_comp_injective f hf himm A₁ A₁i hA₁ hA₁i hA₁l
  -- ## 2. the plane field
  obtain ⟨P, W, hWopen, hWIcc, hPsm, hPidem, hPadj, hPrange⟩ :=
    Work.Whitney.CutPush.exists_plane_family_of_spine f hf himm A₁ A₁i hA₁ hA₁i hA₁l δ hδ
  have hPrangeE : ∀ t ∈ W, LinearMap.range (P t).toLinearMap
      = LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) E₁ (δ t)).toLinearMap := by
    intro t ht
    rw [show E₁ = fun y : M => A₁ (f y) from hE₁]
    exact hPrange t ht
  have hPcont : Continuous fun t : ℝ => P t e :=
    hPsm.continuous.comp (continuous_id.prodMk continuous_const)
  have hfin_imm : ∀ (G : M → EuclideanSpace ℝ (Fin (2 * n))),
      (∀ y : M, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) G y)) →
      ∀ y : M, Module.finrank ℝ (LinearMap.range
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) G y).toLinearMap) = n := by
    intro G hG y
    have hker : LinearMap.ker ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) G y :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)))).toLinearMap = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro v w hvw
      exact hG y hvw
    haveI : FiniteDimensional ℝ (TangentSpace (𝓡 n) y) :=
      inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))
    have hrank := LinearMap.finrank_range_add_finrank_ker
      ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) G y :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)))).toLinearMap
    rw [hker, finrank_bot, add_zero] at hrank
    have hE : Module.finrank ℝ (TangentSpace (𝓡 n) y) = n := by
      show Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
      rw [finrank_euclideanSpace, Fintype.card_fin]
    rw [hE] at hrank
    exact hrank
  -- `e` is a tangent vector of the straightened arc, hence lies in the plane field
  have hinter : Set.Ioo (0 : ℝ) 1 ⊆ {t : ℝ | P t e = e} := by
    intro t ht
    show P t e = e
    have hmem : e ∈ LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) E₁ (δ t)).toLinearMap := by
      have hev : (fun u : ℝ => E₁ (δ u)) =ᶠ[𝓝 t] (fun u : ℝ => a + u • e) := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
        exact haff0 u ⟨hu.1.le, hu.2.le⟩
      have hmd1 : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) δ t := hδ.mdifferentiableAt (by simp)
      have hmd2 : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) E₁ (δ t) :=
        hE₁sm.mdifferentiableAt (by simp)
      have hcomp : mfderiv (modelWithCornersSelf ℝ ℝ)
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) (fun u : ℝ => E₁ (δ u)) t
          = (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) E₁ (δ t)).comp
            (mfderiv (modelWithCornersSelf ℝ ℝ)
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) δ t) := by
        simpa [Function.comp_def] using (mfderiv_comp (f := δ) (g := E₁) t hmd2 hmd1)
      have haff_deriv : mfderiv (modelWithCornersSelf ℝ ℝ)
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
          (fun u : ℝ => a + u • e) t 1 = e := by
        have hderiv : HasDerivAt (fun u : ℝ => a + u • e) e t := by
          have h2 : HasDerivAt (fun u : ℝ => (u : ℝ) • e) ((1 : ℝ) • e) t :=
            (hasDerivAt_id t).smul_const e
          simpa using h2.const_add a
        have hF : HasFDerivAt (fun u : ℝ => a + u • e)
            (ContinuousLinearMap.toSpanSingleton ℝ e) t := hderiv.hasFDerivAt
        rw [mfderiv_eq_fderiv, hF.fderiv]
        exact (ContinuousLinearMap.toSpanSingleton_apply ℝ e 1).trans (one_smul ℝ e)
      have hkey : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) E₁ (δ t))
          ((mfderiv (modelWithCornersSelf ℝ ℝ)
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) δ t) 1) = e := by
        have h1 : mfderiv (modelWithCornersSelf ℝ ℝ)
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
            (fun u : ℝ => E₁ (δ u)) t 1 = e := by
          rw [hev.mfderiv_eq_v433]
          exact haff_deriv
        rw [hcomp] at h1
        exact h1
      exact ⟨_, hkey⟩
    have htW : t ∈ W := hWIcc ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hrange := hPrangeE t htW
    have : e ∈ LinearMap.range (P t).toLinearMap := by rw [hrange]; exact hmem
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp this
    have hy' : P t y = e := hy
    have hidem' : P t (P t y) = P t y := by
      have := congrArg (fun L : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) =>
        L y) (hPidem t htW)
      simpa using this
    calc P t e = P t (P t y) := by rw [hy']
      _ = P t y := hidem'
      _ = e := hy'
  have hP0e : ∀ t ∈ Set.Icc (0 : ℝ) 1, P t e = e := by
    have hclosed : IsClosed {t : ℝ | P t e = e} := isClosed_eq hPcont continuous_const
    have hcl : closure (Set.Ioo (0 : ℝ) 1) ⊆ {t : ℝ | P t e = e} :=
      closure_minimal hinter hclosed
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hcl
    exact fun t ht => hcl ht
  -- ## 3. a small interval around `[0,1]` on which `P · e` does not vanish
  have hgood : IsOpen {s : ℝ | P s e ≠ 0} := by
    have hcompl : IsOpen ({(0 : EuclideanSpace ℝ (Fin (2 * n)))}ᶜ) := isOpen_compl_singleton
    exact hcompl.preimage hPcont
  have hIccsub : Set.Icc (0 : ℝ) 1 ⊆ {s : ℝ | P s e ≠ 0} := by
    intro s hs
    simp only [Set.mem_setOf_eq]
    rw [hP0e s hs]
    exact he
  obtain ⟨ρ₀, hρ₀pos, hρ₀⟩ := isCompact_Icc.exists_cthickening_subset_open hgood hIccsub
  set ρ : ℝ := min ρ₀ 1 with hρdef
  have hρpos : 0 < ρ := lt_min hρ₀pos one_pos
  have hρle : ρ ≤ ρ₀ := min_le_left _ _
  have hρle1 : ρ ≤ 1 := min_le_right _ _
  have hmono : Set.Icc (-ρ) (1 + ρ) ⊆ Metric.cthickening ρ₀ (Set.Icc (0 : ℝ) 1) := by
    intro s hs
    rcases le_or_gt s 0 with hs0 | hs0
    · refine Metric.mem_cthickening_of_dist_le s 0 ρ₀ _ ⟨le_rfl, zero_le_one⟩ ?_
      rw [Real.dist_eq, abs_of_nonpos (by linarith [hs.1])]
      linarith [hs.1, hρle]
    · rcases le_or_gt s 1 with hs1 | hs1
      · refine Metric.mem_cthickening_of_dist_le s s ρ₀ _ ⟨hs0.le, hs1⟩ ?_
        rw [dist_self]
        exact hρ₀pos.le
      · refine Metric.mem_cthickening_of_dist_le s 1 ρ₀ _ ⟨zero_le_one, le_rfl⟩ ?_
        rw [Real.dist_eq, abs_of_nonneg (by linarith)]
        linarith [hs.2, hρle]
  obtain ⟨φ, hφsm, hφid, hφrange⟩ := smoothReparamOn ρ hρpos
  -- ## 4. the clamped family and its alignment
  set P' : ℝ → EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
    fun t => P (φ t) with hP'def
  have hφmemW : ∀ t : ℝ, φ t ∈ W := by
    intro t
    have h1 := hφrange t
    exact hWIcc ⟨by linarith [h1.1, hρle1], by linarith [h1.2, hρle1]⟩
  have hP'sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin (2 * n)) => P' p.1 p.2) :=
    hPsm.comp ((hφsm.comp contDiff_fst).prodMk contDiff_snd)
  have hP'idem : ∀ t, P' t * P' t = P' t := fun t => hPidem (φ t) (hφmemW t)
  have hP'adj : ∀ t (x y : EuclideanSpace ℝ (Fin (2 * n))),
      inner ℝ (P' t x) y = inner ℝ x (P' t y) := fun t => hPadj (φ t) (hφmemW t)
  have hP'rank : ∀ t, Module.finrank ℝ (LinearMap.range (P' t).toLinearMap) = n := by
    intro t
    show Module.finrank ℝ (LinearMap.range (P (φ t)).toLinearMap) = n
    rw [hPrangeE (φ t) (hφmemW t)]
    exact hfin_imm E₁ hE₁imm (δ (φ t))
  have hP'good : ∀ t : ℝ, P' t e ≠ 0 := by
    intro t
    show P (φ t) e ≠ 0
    exact hρ₀ (hmono (hφrange t))
  have hP'e01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, P' t e = e := by
    intro t ht
    show P (φ t) e = e
    rw [hφid t ht]
    exact hP0e t ht
  obtain ⟨Mf, hMfsm, hMfsmInv, hMfe, hMfperp, hMfrange⟩ :=
    planeFamilyAlignment (N := 2 * n) (k := n) P' hP'sm hP'idem hP'adj hP'rank e he hP'good hP'e01
  -- ## 5. the range of `Mf t ∘ P t`
  have hPt_eq : ∀ t ∈ Set.Icc (0 : ℝ) 1, P t = P' t := by
    intro t ht
    show P t = P (φ t)
    rw [hφid t ht]
  have hPt0 : P' 0 = P 0 := by
    show P (φ 0) = P 0
    rw [hφid 0 (by norm_num)]
  have hKfin : Module.finrank ℝ (LinearMap.range (P 0).toLinearMap) = n := by
    rw [hPrangeE 0 (hWIcc (by constructor <;> norm_num))]
    exact hfin_imm E₁ hE₁imm (δ 0)
  have hPrIcc : ∀ t ∈ Set.Icc (0 : ℝ) 1, LinearMap.range (P t).toLinearMap
      = LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) E₁ (δ t)).toLinearMap :=
    fun t ht => hPrangeE t (hWIcc ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hMr : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      LinearMap.range ((Mf t).toLinearMap.comp (P t).toLinearMap)
        = LinearMap.range (P 0).toLinearMap := by
    intro t ht
    rw [LinearMap.range_comp, hPt_eq t ht]
    haveI : FiniteDimensional ℝ ↥(LinearMap.range (P 0).toLinearMap) :=
      LinearMap.finiteDimensional_range (P 0).toLinearMap
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro y ⟨z, hz, rfl⟩
      obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hz
      rw [← hu, ← hPt0]
      exact LinearMap.mem_range.mpr ⟨Mf t (P' t u), hMfrange t ht u⟩
    · rw [LinearEquiv.finrank_map_eq ((Mf t) : EuclideanSpace ℝ (Fin (2 * n)) ≃ₗ[ℝ]
          EuclideanSpace ℝ (Fin (2 * n))) (LinearMap.range (P' t).toLinearMap), hP'rank t, hKfin]
  -- ## 6. the alignment diffeomorphism
  obtain ⟨A₂, A₂i, hA₂, hA₂i, hA₂l, hA₂r, hA₂fix, hA₂deriv⟩ :=
    Work.Whitney.CutPush.exists_fibered_alignment Mf hMfsm hMfsmInv a e he hMfe hMfperp
  refine ⟨A₁, A₁i, A₂, A₂i, LinearMap.range (P 0).toLinearMap, a, e,
    hA₁, hA₁i, hA₁l, hA₁r, hA₂, hA₂i, hA₂l, hA₂r, he, hKfin, ?_, ?_⟩
  · intro t ht
    rw [haff0 t ht, hA₂fix t]
  · intro t ht
    have hA₂der : ∀ s : ℝ, ∀ v : EuclideanSpace ℝ (Fin (2 * n)),
        fderiv ℝ A₂ (a + s • e) v = Mf s v := fun s v => hA₂deriv s v
    have h := range_mfderiv_aligned_comp' (n := n) E₁ hE₁sm A₂ hA₂ a e
      (fun t => (Mf t : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))))
      hA₂der δ haff0 P hPrIcc hMr t ht
    exact h

end Work.Drive.Push
