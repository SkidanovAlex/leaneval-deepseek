import Mathlib
import Submission.Work.Drive.PushDisc.milnorLens
import Submission.Work.Drive.PushDisc.sheetModel
import Submission.Work.Drive.Whitney.whitneyDiscDefs
import Submission.Work.Drive.PushDisc.exists_goodLensParam_clean
import Submission.Work.Drive.PushDisc.regularDiscDefs
import Submission.Work.Drive.PushDisc.regularDiscZero_hbaseInj
import Submission.Work.Drive.PushDisc.regularDiscZero_hbaseImm
import Submission.Work.Drive.PushDisc.exists_chart_twoPlaneFraming
import Submission.Work.Drive.PushDisc.linearIndependent_fin_append_pair
import Submission.Work.Drive.PushDisc.linearIndependent_of_finrank_span_cons
import Submission.Work.Drive.PushDisc.sheetASub_span_frame

namespace Work.Drive.PushDisc

/-! ## Auxiliary lemmas for `exists_cleanLens` -/

private lemma li_pair_swap {E : Type*} [AddCommGroup E] [Module ℝ E] {u v : E}
    (h : LinearIndependent ℝ ![u, v]) : LinearIndependent ℝ ![v, u] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  obtain ⟨h1, h2⟩ := h t s (by rw [add_comm]; exact hst)
  exact ⟨h2, h1⟩

private lemma li_pair_neg_snd {E : Type*} [AddCommGroup E] [Module ℝ E] {u v : E}
    (h : LinearIndependent ℝ ![u, -v]) : LinearIndependent ℝ ![u, v] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  obtain ⟨h1, h2⟩ := h s (-t) (by simpa using hst)
  exact ⟨h1, by simpa using h2⟩

private lemma fderiv_pair_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × ℝ → E) (p : ℝ × ℝ) (u : ℝ × ℝ) :
    fderiv ℝ f p u = u.1 • fderiv ℝ f p (1, 0) + u.2 • fderiv ℝ f p (0, 1) := by
  have hsplit : u = u.1 • ((1, 0) : ℝ × ℝ) + u.2 • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  conv_lhs => rw [hsplit]
  rw [map_add, map_smul, map_smul]

private lemma fderiv_comp_inl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × ℝ → E) {x y : ℝ} (hf : DifferentiableAt ℝ f (x, y)) :
    fderiv ℝ (fun t : ℝ => f (t, y)) x
      = (fderiv ℝ f (x, y)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ) := by
  have h := fderiv_comp (x := x) (f := fun t : ℝ => (t, y)) (g := f) hf
    (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x)
  rw [show (fun t : ℝ => f (t, y)) = f ∘ (fun t : ℝ => (t, y)) from rfl, h,
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y).fderiv]

private lemma fderiv_comp_inr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × ℝ → E) {x y : ℝ} (hf : DifferentiableAt ℝ f (x, y)) :
    fderiv ℝ (fun t : ℝ => f (x, t)) y
      = (fderiv ℝ f (x, y)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) := by
  have h := fderiv_comp (x := y) (f := fun t : ℝ => (x, t)) (g := f) hf
    (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => (x, t)) y)
  rw [show (fun t : ℝ => f (x, t)) = f ∘ (fun t : ℝ => (x, t)) from rfl, h,
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y).fderiv]

private lemma hasDerivAt_arch (x : ℝ) : HasDerivAt arch (-2 * x) x := by
  have h : HasDerivAt (fun z : ℝ => 1 - z^2) (0 - 2 * x^(2-1)) x :=
    (hasDerivAt_const (x := x) (c := (1:ℝ))).sub (hasDerivAt_pow 2 x)
  have h2 : HasDerivAt (fun z : ℝ => 1 - z^2) (-2 * x) x := by simpa using h
  exact h2

private lemma fderiv_row_bottom {k : ℕ} (Δ : ℝ × ℝ → Work.Drive.Whitney.Mdl k) (x : ℝ)
    (hrow : ∀ t : ℝ, Δ (t, 0) = ((t, 0, 0, 0) : Work.Drive.Whitney.Mdl k))
    (hd : DifferentiableAt ℝ Δ (x, 0)) :
    fderiv ℝ Δ (x, 0) (1, 0) = ((1, 0, 0, 0) : Work.Drive.Whitney.Mdl k) := by
  have key : fderiv ℝ (fun t : ℝ => Δ (t, 0)) x
      = (fderiv ℝ Δ (x, 0)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ) :=
    fderiv_comp_inl Δ hd
  rw [show (fun t : ℝ => Δ (t, 0))
      = fun t : ℝ => ((t, 0, 0, 0) : Work.Drive.Whitney.Mdl k) from funext hrow] at key
  have hL : (fderiv ℝ (fun t : ℝ => ((t, 0, 0, 0) : Work.Drive.Whitney.Mdl k)) x) 1
      = ((1, 0, 0, 0) : Work.Drive.Whitney.Mdl k) := by
    have h : fderiv ℝ (fun t : ℝ => ((t, 0, 0, 0) : Work.Drive.Whitney.Mdl k)) x
        = ContinuousLinearMap.inl ℝ ℝ
            (ℝ × EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) :=
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) x
        (0 : ℝ × EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))).fderiv
    rw [h]
    rfl
  have h1 := congrArg (fun L : ℝ →L[ℝ] Work.Drive.Whitney.Mdl k => L 1) key
  rw [hL] at h1
  simpa using h1.symm

private lemma fderiv_vertical_of_row {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × ℝ → E) (c G : E) (x : ℝ)
    (hrow : ∀ t : ℝ, f (x, t) = c + t • G) (hd : DifferentiableAt ℝ f (x, 0)) :
    fderiv ℝ f (x, 0) (0, 1) = G := by
  have hcomp := fderiv_comp_inr f hd
  rw [show (fun t : ℝ => f (x, t)) = fun t : ℝ => c + t • G from funext hrow] at hcomp
  have h2 : (fderiv ℝ (fun t : ℝ => c + t • G) 0) 1 = G := by
    have h : fderiv ℝ (fun t : ℝ => c + t • G) 0 = ContinuousLinearMap.toSpanSingleton ℝ G := by
      rw [show (fun t : ℝ => c + t • G)
          = (fun t : ℝ => c + ContinuousLinearMap.toSpanSingleton ℝ G t) from by
        funext t; rw [ContinuousLinearMap.toSpanSingleton_apply]]
      rw [fderiv_const_add, ContinuousLinearMap.fderiv]
    rw [h, ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  have h3 := congrArg (fun L : ℝ →L[ℝ] E => L 1) hcomp
  rw [h2] at h3
  simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using h3.symm

private lemma fderiv_row_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Δ : ℝ × ℝ → E) (B : ℝ → E) (x : ℝ)
    (hrow : ∀ t : ℝ, Δ (t, arch t) = B t)
    (hd : DifferentiableAt ℝ Δ (x, arch x)) (hBd : DifferentiableAt ℝ B x) :
    fderiv ℝ Δ (x, arch x) (1, 0)
      = fderiv ℝ B x 1 + (2 * x) • fderiv ℝ Δ (x, arch x) (0, 1) := by
  have hφ : HasDerivAt (fun t : ℝ => (t, arch t)) (1, -2 * x) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_arch x)
  have hchain : HasDerivAt (fun t : ℝ => Δ (t, arch t))
      ((fderiv ℝ Δ (x, arch x)) (1, -2 * x)) x :=
    hd.hasFDerivAt.comp_hasDerivAt x hφ
  have hB : HasDerivAt (fun t : ℝ => Δ (t, arch t)) (fderiv ℝ B x 1) x := by
    rw [show (fun t : ℝ => Δ (t, arch t)) = B from funext hrow]
    exact hBd.hasFDerivAt.hasDerivAt
  have huniq : (fderiv ℝ Δ (x, arch x)) (1, -2 * x) = fderiv ℝ B x 1 := hchain.unique hB
  rw [fderiv_pair_apply Δ (x, arch x) (1, -2 * x), one_smul] at huniq
  rw [← huniq, add_assoc, ← add_smul]
  simp

private lemma range_mfderiv_comp_clm {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : M → F) (L : F →L[ℝ] G) (y : M)
    (hg : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ F) g y) :
    (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ G) (fun z => L (g z)) y).range
      = Submodule.map L.toLinearMap
          (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersSelf ℝ F) g y).range := by
  have h1 : (fun z : M => L (g z)) = ⇑L ∘ g := rfl
  rw [h1, mfderiv_comp y L.mdifferentiableAt hg, mfderiv_eq_fderiv, L.fderiv]
  exact LinearMap.range_comp _ _

set_option maxHeartbeats 1000000 in
theorem exists_cleanLens {k : ℕ} (hk : 2 ≤ k) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΦimm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => Φ (f y)) y))
    (γ₁ γ₂ : ℝ → M)
    (hγ₁ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (B g : ℝ → Work.Drive.Whitney.Mdl k) (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hBg : ∀ x : ℝ, B x - (x, 0, 0, 0) = Work.Drive.PushDisc.arch x • g x)
    (hBinj : Set.InjOn B (Set.Icc (-1 : ℝ) 1))
    (hBimm : ∀ x ∈ Set.Icc (-1 : ℝ) 1, fderiv ℝ B x 1 ≠ 0)
    (hBoff : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ x' ∈ Set.Icc (-1 : ℝ) 1,
      B x = (x', 0, 0, 0) → x = x' ∧ (x = 1 ∨ x = -1))
    (hcorn1 : LinearIndependent ℝ ![g 1, ((1 : ℝ), 0, 0, 0)])
    (hcornm1 : LinearIndependent ℝ ![g (-1), ((-1 : ℝ), 0, 0, 0)])
    (hg1 : g 1 ∉ Work.Drive.PushDisc.sheetASub k)
    (hgm1 : g (-1) ∉ Work.Drive.PushDisc.sheetASub k)
    (V : ℝ → Fin k → Work.Drive.Whitney.Mdl k)
    (hbotRan : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => Φ (f y))
          (γ₁ (Work.Drive.Whitney.sigR x))).range = Work.Drive.PushDisc.sheetASub k)
    (htopRan : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => Φ (f y))
          (γ₂ (Work.Drive.Whitney.sigR x))).range
        = Submodule.span ℝ (Set.range (Fin.cons (fderiv ℝ B x 1) (V x))))
    (htopRank : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      Module.finrank ℝ ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => Φ (f y))
          (γ₂ (Work.Drive.Whitney.sigR x))).range) = k + 1)
    (hgc1 : g 1 ∉ (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => Φ (f y))
          (γ₂ 1)).range)
    (hgcm1 : g (-1) ∉ (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => Φ (f y))
          (γ₂ 0)).range) :
    ∃ Δ : ℝ × ℝ → Work.Drive.Whitney.Mdl k,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => fderiv ℝ Δ q (1, 0)) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => fderiv ℝ Δ q (0, 1)) ∧
      (∀ x : ℝ, Δ (x, 0) = (x, 0, 0, 0)) ∧
      (∀ x : ℝ, Δ (x, Work.Drive.PushDisc.arch x) = B x) ∧
      (∀ x y : ℝ, 1 ≤ |x| → Δ (x, y) = (x, 0, 0, 0) + y • g x) ∧
      Set.InjOn Δ Work.Drive.PushDisc.lensK ∧
      (∀ p ∈ Work.Drive.PushDisc.lensK, Function.Injective (fderiv ℝ Δ p)) ∧
      (∀ p ∈ Work.Drive.PushDisc.lensKo, ∀ z : M, Δ p ≠ Φ (f z)) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, LinearIndependent ℝ
        (Fin.append (Work.Drive.PushDisc.planeFrame k (fun q => fderiv ℝ Δ q (1, 0))
          (fun q => fderiv ℝ Δ q (0, 1)) (x, 0)) (Work.Drive.PushDisc.iotaU k))) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, LinearIndependent ℝ
        (Fin.append (Work.Drive.PushDisc.planeFrame k (fun q => fderiv ℝ Δ q (1, 0))
          (fun q => fderiv ℝ Δ q (0, 1)) (x, Work.Drive.PushDisc.arch x)) (V x))) := by
  classical
  have hk3 : 3 ≤ k + 1 := by omega
  have hlensK : lensK = lens := rfl
  have hlensOpen : lensKo = lensOpen := rfl
  -- the linear identification of the model space with `ℝ^{2(k+1)}`
  let eC : Work.Drive.Whitney.Mdl k ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * (k + 1))) :=
    (Work.Drive.PushDisc.mdlEquivL (n := k + 1) (k := k) rfl).toContinuousLinearEquiv
  let eT : Work.Drive.Whitney.Mdl k →L[ℝ] EuclideanSpace ℝ (Fin (2 * (k + 1))) :=
    (eC : Work.Drive.Whitney.Mdl k →L[ℝ] EuclideanSpace ℝ (Fin (2 * (k + 1))))
  let sT : EuclideanSpace ℝ (Fin (2 * (k + 1))) →L[ℝ] Work.Drive.Whitney.Mdl k :=
    (eC.symm : EuclideanSpace ℝ (Fin (2 * (k + 1))) →L[ℝ] Work.Drive.Whitney.Mdl k)
  let w : Work.Drive.Whitney.Mdl k := ((1 : ℝ), 0, 0, 0)
  have hT_diffAt : ∀ y : Work.Drive.Whitney.Mdl k, DifferentiableAt ℝ (⇑eT) y :=
    fun y => ((eT.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).differentiable (by simp)).differentiableAt
  have hS_diffAt : ∀ z : EuclideanSpace ℝ (Fin (2 * (k + 1))), DifferentiableAt ℝ (⇑sT) z :=
    fun z => ((sT.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).differentiable (by simp)).differentiableAt
  let Aclm : ℝ →L[ℝ] EuclideanSpace ℝ (Fin (2 * (k + 1))) :=
    eT.comp (ContinuousLinearMap.inl ℝ ℝ
      (ℝ × EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)))
  let A' : ℝ → EuclideanSpace ℝ (Fin (2 * (k + 1))) := ⇑Aclm
  let B' : ℝ → EuclideanSpace ℝ (Fin (2 * (k + 1))) := ⇑eT ∘ B
  let g' : ℝ → EuclideanSpace ℝ (Fin (2 * (k + 1))) := ⇑eT ∘ g
  let D' : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * (k + 1))) :=
    fun q => (1 - q.2) • A' q.1 + q.2 • B' q.1
  let Δ₀' : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * (k + 1))) :=
    regularDiscZero D' A' B' g' 1
  have hker : LinearMap.ker (eC : Work.Drive.Whitney.Mdl k →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (2 * (k + 1)))) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact eC.injective
  have hAval : ∀ x : ℝ, A' x = eC ((x, 0, 0, 0) : Work.Drive.Whitney.Mdl k) := by
    intro x
    show Aclm x = eC ((x, 0, 0, 0) : Work.Drive.Whitney.Mdl k)
    simp only [Aclm, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    rfl
  -- ## smoothness of the Euclidean model data
  have hA'sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A' := Aclm.contDiff
  have hB'sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B' := by
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑eT ∘ B)
    exact eT.contDiff.comp hB
  have hg'sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g' := by
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑eT ∘ g)
    exact eT.contDiff.comp hg
  have hD'sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) D' := by
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => (1 - q.2) • A' q.1 + q.2 • B' q.1)
    exact ((contDiff_const.sub contDiff_snd).smul (hA'sm.comp contDiff_fst)).add
      (contDiff_snd.smul (hB'sm.comp contDiff_fst))
  have hΔ₀'sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ₀' :=
    contDiff_regularDiscZero hD'sm hA'sm hB'sm hg'sm (by norm_num)
  -- ## the rows of the base map
  have hD'bot : ∀ x : ℝ, D' (x, 0) = A' x := by
    intro x; simp [D']
  have hD'top : ∀ x : ℝ, D' (x, 1) = B' x := by
    intro x; simp [D']
  have hg'val : ∀ x : ℝ, arch x • g' x = B' x - A' x := by
    intro x
    show arch x • eC (g x) = eC (B x) - A' x
    rw [← map_smul, ← hBg x, map_sub, ← hAval x]
  -- ## base injectivity and base immersion
  have hinjA : Set.InjOn A' (Set.Icc (-1 : ℝ) 1) := by
    intro x _ y _ hxy
    have h := congrArg (fun z : EuclideanSpace ℝ (Fin (2 * (k + 1))) => eC.symm z) hxy
    have h2 : ((x, 0, 0, 0) : Work.Drive.Whitney.Mdl k) = (y, 0, 0, 0) := by
      have h1 : eC.symm (A' x) = ((x, 0, 0, 0) : Work.Drive.Whitney.Mdl k) := by
        rw [hAval x]; exact eC.symm_apply_apply _
      have h3 : eC.symm (A' y) = ((y, 0, 0, 0) : Work.Drive.Whitney.Mdl k) := by
        rw [hAval y]; exact eC.symm_apply_apply _
      exact (h1.symm.trans h).trans h3
    have h4 : ((x, 0, 0, 0) : Work.Drive.Whitney.Mdl k).1
        = ((y, 0, 0, 0) : Work.Drive.Whitney.Mdl k).1 :=
      congrArg (fun z : Work.Drive.Whitney.Mdl k => z.1) h2
    simpa using h4
  have hinjB : Set.InjOn B' (Set.Icc (-1 : ℝ) 1) := by
    intro x hx y hy hxy
    have h : eC (B x) = eC (B y) := hxy
    exact hBinj hx hy (eC.injective h)
  have hdisj : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      A' x = B' y → x = y ∧ x ^ 2 = 1 := by
    intro x hx y hy hxy
    have hxy' : B y = ((x, 0, 0, 0) : Work.Drive.Whitney.Mdl k) := by
      have h0 := congrArg (fun z : EuclideanSpace ℝ (Fin (2 * (k + 1))) => eC.symm z) hxy
      have h1 : eC.symm (A' x) = ((x, 0, 0, 0) : Work.Drive.Whitney.Mdl k) := by
        rw [hAval x]; exact eC.symm_apply_apply _
      have h2 : eC.symm (B' y) = B y := by
        show eC.symm (eC (B y)) = B y
        exact eC.symm_apply_apply _
      exact ((h1.symm.trans h0).trans h2).symm
    obtain ⟨hyx, hcor⟩ := hBoff y hy x hx hxy'
    refine ⟨hyx.symm, ?_⟩
    have hxpm : x = 1 ∨ x = -1 := by
      rcases hcor with h | h
      · exact Or.inl (hyx ▸ h)
      · exact Or.inr (hyx ▸ h)
    rcases hxpm with h | h <;> rw [h] <;> norm_num
  have hbaseInj : ∀ p ∈ lens, ∀ q ∈ lens, p ≠ q →
      (∀ k : Fin 2 × Fin 2, lensBump 1 k p = lensBump 1 k q) → Δ₀' p ≠ Δ₀' q :=
    regularDiscZero_hbaseInj (ρ := 1) one_pos (δ := 1) one_pos hD'bot hD'top hg'val
      hinjA hinjB hdisj
  have hderA : ∀ x : ℝ, fderiv ℝ A' x = Aclm := fun x => Aclm.fderiv
  have hAderiv : ∀ x ∈ Set.Icc (-1 : ℝ) 1, fderiv ℝ A' x 1 ≠ 0 := by
    intro x _
    rw [hderA x]
    show eC ((1, 0, 0, 0) : Work.Drive.Whitney.Mdl k) ≠ 0
    intro hc
    have hz : ((1 : ℝ), 0, 0, 0) = (0 : Work.Drive.Whitney.Mdl k) := by
      apply eC.injective
      rw [hc, map_zero]
    simp at hz
  have hBderiv : ∀ x ∈ Set.Icc (-1 : ℝ) 1, fderiv ℝ B' x 1 ≠ 0 := by
    intro x hx
    have hder : fderiv ℝ B' x = eT.comp (fderiv ℝ B x) := by
      have h3 : fderiv ℝ B' x = (fderiv ℝ (⇑eT) (B x)).comp (fderiv ℝ B x) :=
        fderiv_comp (x := x) (f := B) (g := ⇑eT)
          (hT_diffAt (B x))
          ((hB.contDiffAt (x := x)).differentiableAt (by simp))
      rw [ContinuousLinearMap.fderiv] at h3
      exact h3
    rw [hder, ContinuousLinearMap.comp_apply]
    intro hc
    exact hBimm x hx (eC.injective (by rw [map_zero]; exact hc))
  have hderA1 : ∀ x : ℝ, (fderiv ℝ A' x) 1 = eC w := by
    intro x
    rw [hderA x]
    show eC ((1, 0, 0, 0) : Work.Drive.Whitney.Mdl k) = eC w
    rfl
  have hindPos : LinearIndependent ℝ ![(fderiv ℝ A' 1) 1, g' 1] := by
    have h1 : LinearIndependent ℝ ![eC w, eC (g 1)] := by
      have h0 : LinearIndependent ℝ ((eC : Work.Drive.Whitney.Mdl k →ₗ[ℝ]
          EuclideanSpace ℝ (Fin (2 * (k + 1)))) ∘ ![g 1, w]) :=
        hcorn1.map' (eC : Work.Drive.Whitney.Mdl k →ₗ[ℝ]
          EuclideanSpace ℝ (Fin (2 * (k + 1)))) hker
      have h2 : (eC : Work.Drive.Whitney.Mdl k →ₗ[ℝ]
            EuclideanSpace ℝ (Fin (2 * (k + 1)))) ∘ ![g 1, w] = ![eC (g 1), eC w] := by
        funext i; fin_cases i <;> simp [w]
      rw [h2] at h0
      exact li_pair_swap h0
    rwa [hderA1 1, show g' 1 = eC (g 1) from rfl]
  have hindNeg : LinearIndependent ℝ ![(fderiv ℝ A' (-1)) 1, g' (-1)] := by
    have h1 : LinearIndependent ℝ ![eC w, eC (g (-1))] := by
      have hcm : LinearIndependent ℝ ![g (-1), -w] := by
        have h := hcornm1
        rwa [show ((-1 : ℝ), 0, 0, 0) = -w from by ext <;> simp [w]] at h
      have h0 : LinearIndependent ℝ ((eC : Work.Drive.Whitney.Mdl k →ₗ[ℝ]
          EuclideanSpace ℝ (Fin (2 * (k + 1)))) ∘ ![g (-1), -w]) :=
        hcm.map' (eC : Work.Drive.Whitney.Mdl k →ₗ[ℝ]
          EuclideanSpace ℝ (Fin (2 * (k + 1)))) hker
      have h2 : (eC : Work.Drive.Whitney.Mdl k →ₗ[ℝ]
            EuclideanSpace ℝ (Fin (2 * (k + 1)))) ∘ ![g (-1), -w] = ![eC (g (-1)), -eC w] := by
        funext i; fin_cases i
        · simp
        · simp [map_neg]
      rw [h2] at h0
      exact li_pair_swap (li_pair_neg_snd h0)
    rwa [hderA1 (-1), show g' (-1) = eC (g (-1)) from rfl]
  have hbaseImm : ∀ p ∈ lens, ∀ UW : ℝ × ℝ, UW ≠ 0 →
      (∀ k : Fin 2 × Fin 2,
        UW.1 * fderiv ℝ (lensBump 1 k) p (1, 0)
          + UW.2 * fderiv ℝ (lensBump 1 k) p (0, 1) = 0) →
      UW.1 • (fderiv ℝ Δ₀' p) (1, 0) + UW.2 • (fderiv ℝ Δ₀' p) (0, 1) ≠ 0 :=
    regularDiscZero_hbaseImm (ρ := 1) one_pos (δ := 1) one_pos hD'sm hA'sm hB'sm hg'sm
      hD'bot hD'top hg'val hAderiv hBderiv hindNeg hindPos
  -- ## the generic perturbation
  have hΦf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M => Φ (f y)) :=
    hΦ.contMDiff.comp hf
  have hFsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : M => eC (Φ (f y))) :=
    (eT.contDiff.contMDiff).comp hΦf
  have hFimm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
      (fun y : M => eC (Φ (f y))) y) := by
    intro y
    have hcomp : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
        (fun y : M => eC (Φ (f y))) y
        = eT.comp (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
            (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => Φ (f y)) y) := by
      have h3 : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
          (fun z : M => eT ((fun y : M => Φ (f y)) z)) y
          = (mfderiv (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
              (⇑eT) ((fun y : M => Φ (f y)) y)).comp
            (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
              (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k))
              (fun y : M => Φ (f y)) y) :=
        mfderiv_comp (f := fun y : M => Φ (f y)) y
          ((eT.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).contMDiff.mdifferentiableAt (by simp))
          (hΦf.mdifferentiableAt (by simp))
      rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at h3
      exact h3
    rw [hcomp]
    intro u v huv
    have huv' : eT ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
          (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => Φ (f y)) y) u)
        = eT ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
          (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => Φ (f y)) y) v) := huv
    exact hΦimm y (eC.injective huv')
  obtain ⟨v, hvball, hvimm, hvinj, hvclean, hvcolBot, hvcolTop⟩ :=
    exists_goodLensParam_clean (n := k + 1) hk3 (f := fun y : M => eC (Φ (f y)))
      hFsm hFimm γ₁ γ₂ hγ₁ hγ₂ 1 one_pos Δ₀' hΔ₀'sm hbaseInj hbaseImm 1 one_pos
  -- ## the answer
  let Δ : ℝ × ℝ → Work.Drive.Whitney.Mdl k := fun q => eC.symm (lensMap Δ₀' 1 v q)
  have hΔdef : ∀ q : ℝ × ℝ, Δ q = eC.symm (lensMap Δ₀' 1 v q) := fun q => rfl
  have hlensPert : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lensPert 1 v) := by
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => ∑ k : Fin 2 × Fin 2, lensBump 1 k p • v k)
    exact ContDiff.sum (fun k _ => (contDiff_lensBump 1 k).smul contDiff_const)
  have hlensMap : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lensMap Δ₀' 1 v) := by
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => Δ₀' p + lensPert 1 v p)
    exact hΔ₀'sm.add hlensPert
  have hΔsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ := by
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑sT ∘ lensMap Δ₀' 1 v)
    exact sT.contDiff.comp hlensMap
  have hΔdiff : ∀ q : ℝ × ℝ, DifferentiableAt ℝ Δ q :=
    fun q => (hΔsm.contDiffAt (x := q)).differentiableAt (by simp)
  have hder1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => fderiv ℝ Δ q (1, 0)) := by
    have h := ContDiff.contDiff_fderiv_apply (𝕜 := ℝ) (f := Δ) hΔsm
      (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)
    exact h.comp (contDiff_id.prodMk contDiff_const)
  have hder2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => fderiv ℝ Δ q (0, 1)) := by
    have h := ContDiff.contDiff_fderiv_apply (𝕜 := ℝ) (f := Δ) hΔsm
      (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)
    exact h.comp (contDiff_id.prodMk contDiff_const)
  have htrans : ∀ (q u : ℝ × ℝ),
      eC (fderiv ℝ Δ q u) = fderiv ℝ (lensMap Δ₀' 1 v) q u := by
    intro q u
    have hfun : (fun z : ℝ × ℝ => eC (Δ z)) = lensMap Δ₀' 1 v := by
      funext z
      show eC (eC.symm (lensMap Δ₀' 1 v z)) = lensMap Δ₀' 1 v z
      rw [eC.apply_symm_apply]
    have hcomp : fderiv ℝ (fun z : ℝ × ℝ => eC (Δ z)) q = eT.comp (fderiv ℝ Δ q) := by
      have h3 : fderiv ℝ (fun z : ℝ × ℝ => eC (Δ z)) q
          = (fderiv ℝ (⇑eT) (Δ q)).comp (fderiv ℝ Δ q) :=
        fderiv_comp (x := q) (f := Δ) (g := ⇑eT) (hT_diffAt (Δ q)) (hΔdiff q)
      rw [ContinuousLinearMap.fderiv] at h3
      exact h3
    have h1 : fderiv ℝ (fun z : ℝ × ℝ => eC (Δ z)) q u = eC (fderiv ℝ Δ q u) := by
      rw [hcomp]; rfl
    rw [← h1, hfun]
  -- ## the rows of `Δ`
  have hrow0 : ∀ x : ℝ, Δ (x, 0) = ((x, 0, 0, 0) : Work.Drive.Whitney.Mdl k) := by
    intro x
    rw [hΔdef (x, 0)]
    have h1 : lensMap Δ₀' 1 v (x, 0) = A' x := by
      rw [show lensMap Δ₀' 1 v (x, 0) = Δ₀' (x, 0) + lensPert 1 v (x, 0) from rfl,
        lensPert_eq_zero_bot, add_zero]
      exact regularDiscZero_bot hD'bot x
    rw [h1, hAval x]
    exact eC.symm_apply_apply ((x, 0, 0, 0) : Work.Drive.Whitney.Mdl k)
  have hrowTop : ∀ x : ℝ, Δ (x, arch x) = B x := by
    intro x
    rw [hΔdef (x, arch x)]
    have h1 : lensMap Δ₀' 1 v (x, arch x) = B' x := by
      rw [show lensMap Δ₀' 1 v (x, arch x) = Δ₀' (x, arch x) + lensPert 1 v (x, arch x)
          from rfl, lensPert_eq_zero_top, add_zero]
      exact regularDiscZero_top one_pos hg'val hD'top x
    rw [h1]
    show eC.symm (eC (B x)) = B x
    rw [eC.symm_apply_apply]
  have hrowOff : ∀ x y : ℝ, 1 ≤ |x| →
      Δ (x, y) = ((x, 0, 0, 0) : Work.Drive.Whitney.Mdl k) + y • g x := by
    intro x y hx
    rw [hΔdef (x, y)]
    have hp : lensPert 1 v (x, y) = 0 := by
      rw [lensPert]
      exact Finset.sum_eq_zero
        (fun k _ => by rw [lensBump_eq_zero_of_abs_one_le (by norm_num : (0:ℝ) < 1) hx, zero_smul])
    have hd : discCorr D' A' B' g' 1 (x, y) = 0 := by
      simp only [discCorr]
      rw [lensTheta_eq_zero (by norm_num : (0:ℝ) < 1) (by nlinarith [sq_nonneg x]), zero_smul]
    have hΔ₀ : Δ₀' (x, y) = A' x + y • g' x := by
      show regularDiscZero D' A' B' g' 1 (x, y) = A' x + y • g' x
      simp only [regularDiscZero, hd, add_zero]
    rw [show lensMap Δ₀' 1 v (x, y) = Δ₀' (x, y) + lensPert 1 v (x, y) from rfl,
      hp, add_zero, hΔ₀]
    have hkey : A' x + y • g' x
        = eC (((x, 0, 0, 0) : Work.Drive.Whitney.Mdl k) + y • g x) := by
      rw [map_add, map_smul, hAval x]
      rfl
    show eC.symm (A' x + y • g' x) = ((x, 0, 0, 0) : Work.Drive.Whitney.Mdl k) + y • g x
    rw [hkey, eC.symm_apply_apply]
  -- ## injectivity, immersivity and cleanliness
  have hinjOn : Set.InjOn Δ lensK := by
    intro p hp q hq hpq
    have hp' : p ∈ lens := hlensK ▸ hp
    have hq' : q ∈ lens := hlensK ▸ hq
    exact hvinj hp' hq' (eC.symm.injective hpq)
  have himm : ∀ p ∈ lensK, Function.Injective (fderiv ℝ Δ p) := by
    intro p hp
    have hp' : p ∈ lens := hlensK ▸ hp
    have hcomp : fderiv ℝ Δ p = sT.comp (fderiv ℝ (lensMap Δ₀' 1 v) p) := by
      have h3 : fderiv ℝ Δ p = (fderiv ℝ (⇑sT) (lensMap Δ₀' 1 v p)).comp
          (fderiv ℝ (lensMap Δ₀' 1 v) p) :=
        fderiv_comp (x := p) (f := lensMap Δ₀' 1 v) (g := ⇑sT)
          (hS_diffAt (lensMap Δ₀' 1 v p))
          ((hlensMap.contDiffAt (x := p)).differentiableAt (by simp))
      rw [ContinuousLinearMap.fderiv] at h3
      exact h3
    rw [hcomp]
    intro a b hab
    have h1 : sT (fderiv ℝ (lensMap Δ₀' 1 v) p a) = sT (fderiv ℝ (lensMap Δ₀' 1 v) p b) := by
      simpa [ContinuousLinearMap.comp_apply] using hab
    exact hvimm p hp' (eC.symm.injective h1)
  have hclean : ∀ p ∈ lensKo, ∀ z : M, Δ p ≠ Φ (f z) := by
    intro p hp z hz
    refine hvclean p ?_ z ?_
    · exact hlensOpen ▸ hp
    · have h := congrArg (fun u => eC u) hz
      have h2 : eC (Δ p) = lensMap Δ₀' 1 v p := by
        rw [hΔdef p, eC.apply_symm_apply]
      rw [h2] at h
      exact h
  -- ## the two frame rows
  have hframe1 : ∀ x ∈ Set.Icc (-1 : ℝ) 1, LinearIndependent ℝ
      (Fin.append (planeFrame k (fun q => fderiv ℝ Δ q (1, 0))
        (fun q => fderiv ℝ Δ q (0, 1)) (x, 0)) (iotaU k)) := by
    intro x hx
    have ha : fderiv ℝ Δ (x, 0) (1, 0) = ((1, 0, 0, 0) : Work.Drive.Whitney.Mdl k) :=
      fderiv_row_bottom Δ x hrow0 (hΔdiff (x, 0))
    have hη : fderiv ℝ Δ (x, 0) (0, 1) ∉ sheetASub k := by
      by_cases hxlt : |x| < 1
      · have hxioo : x ∈ Set.Ioo (-1 : ℝ) 1 := by
          rw [abs_lt] at hxlt
          exact ⟨hxlt.1, hxlt.2⟩
        have hcol := hvcolBot x hxioo
        have hrange0 : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
              (fun y : M => eC (Φ (f y))) (γ₁ (Work.Drive.Whitney.sigR x))).range
            = Submodule.map eT.toLinearMap
                (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
                  (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k))
                  (fun y : M => Φ (f y)) (γ₁ (Work.Drive.Whitney.sigR x))).range := by
          show (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
              (fun z : M => eT ((fun y : M => Φ (f y)) z)) (γ₁ (Work.Drive.Whitney.sigR x))).range
            = Submodule.map eT.toLinearMap
                (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
                  (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k))
                  (fun y : M => Φ (f y)) (γ₁ (Work.Drive.Whitney.sigR x))).range
          exact range_mfderiv_comp_clm (n := k + 1) (g := fun y : M => Φ (f y)) (L := eT)
            (y := γ₁ (Work.Drive.Whitney.sigR x)) (hΦf.mdifferentiableAt (by simp))
        have hrange : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
              (fun y : M => eC (Φ (f y))) (γ₁ (Work.Drive.Whitney.sigR x))).range
            = Submodule.map eT.toLinearMap (sheetASub k) := by
          rw [hrange0, hbotRan x hx]
        intro hmem
        apply hcol
        rw [hrange]
        exact Submodule.mem_map.mpr ⟨fderiv ℝ Δ (x, 0) (0, 1), hmem, htrans (x, 0) (0, 1)⟩
      · have hxabs : |x| = 1 := le_antisymm (abs_le.mpr (Set.mem_Icc.mp hx)) (le_of_not_gt hxlt)
        have hxpm : x = 1 ∨ x = -1 := by
          have h2 : x ^ 2 = 1 := by rw [← sq_abs, hxabs]; norm_num
          exact sq_eq_one_iff.mp h2
        have hη1 : fderiv ℝ Δ (x, 0) (0, 1) = g x :=
          fderiv_vertical_of_row Δ ((x, 0, 0, 0) : Work.Drive.Whitney.Mdl k) (g x) x
            (fun t => hrowOff x t (le_of_not_gt hxlt)) (hΔdiff (x, 0))
        rw [hη1]
        rcases hxpm with rfl | rfl
        · exact hg1
        · exact hgm1
    obtain ⟨hV, hbV⟩ := linearIndependent_of_finrank_span_cons
      (E := Work.Drive.Whitney.Mdl k) (V := iotaU k)
      (b := ((1, 0, 0, 0) : Work.Drive.Whitney.Mdl k)) (by
        rw [← sheetASub_span_frame k]
        exact finrank_sheetASub k)
    have hbη : fderiv ℝ Δ (x, 0) (0, 1) ∉
        Submodule.span ℝ (Set.range (Fin.cons ((1, 0, 0, 0) : Work.Drive.Whitney.Mdl k)
          (iotaU k))) := by
      rwa [← sheetASub_span_frame k]
    have ha' : fderiv ℝ Δ (x, 0) (1, 0)
        = ((1, 0, 0, 0) : Work.Drive.Whitney.Mdl k)
          + (2 * (0 : ℝ)) • fderiv ℝ Δ (x, 0) (0, 1) := by
      simp [ha]
    have hres := linearIndependent_fin_append_pair (E := Work.Drive.Whitney.Mdl k)
      hV hbV hbη ha'
    simpa [planeFrame] using hres
  have hframe2 : ∀ x ∈ Set.Icc (-1 : ℝ) 1, LinearIndependent ℝ
      (Fin.append (planeFrame k (fun q => fderiv ℝ Δ q (1, 0))
        (fun q => fderiv ℝ Δ q (0, 1)) (x, arch x)) (V x)) := by
    intro x hx
    have ha : fderiv ℝ Δ (x, arch x) (1, 0)
        = fderiv ℝ B x 1 + (2 * x) • fderiv ℝ Δ (x, arch x) (0, 1) :=
      fderiv_row_top Δ B x hrowTop (hΔdiff (x, arch x))
        ((hB.contDiffAt (x := x)).differentiableAt (by simp))
    have hη : fderiv ℝ Δ (x, arch x) (0, 1) ∉
        Submodule.span ℝ (Set.range (Fin.cons (fderiv ℝ B x 1) (V x))) := by
      by_cases hxlt : |x| < 1
      · have hxioo : x ∈ Set.Ioo (-1 : ℝ) 1 := by
          rw [abs_lt] at hxlt
          exact ⟨hxlt.1, hxlt.2⟩
        have hcol := hvcolTop x hxioo
        have hrange0 : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
              (fun y : M => eC (Φ (f y))) (γ₂ (Work.Drive.Whitney.sigR x))).range
            = Submodule.map eT.toLinearMap
                (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
                  (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k))
                  (fun y : M => Φ (f y)) (γ₂ (Work.Drive.Whitney.sigR x))).range := by
          show (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
              (fun z : M => eT ((fun y : M => Φ (f y)) z)) (γ₂ (Work.Drive.Whitney.sigR x))).range
            = Submodule.map eT.toLinearMap
                (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
                  (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k))
                  (fun y : M => Φ (f y)) (γ₂ (Work.Drive.Whitney.sigR x))).range
          exact range_mfderiv_comp_clm (n := k + 1) (g := fun y : M => Φ (f y)) (L := eT)
            (y := γ₂ (Work.Drive.Whitney.sigR x)) (hΦf.mdifferentiableAt (by simp))
        have hrange : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
              (fun y : M => eC (Φ (f y))) (γ₂ (Work.Drive.Whitney.sigR x))).range
            = Submodule.map eT.toLinearMap
                (Submodule.span ℝ (Set.range (Fin.cons (fderiv ℝ B x 1) (V x)))) := by
          rw [hrange0, htopRan x hx]
        intro hmem
        apply hcol
        rw [hrange]
        exact Submodule.mem_map.mpr ⟨fderiv ℝ Δ (x, arch x) (0, 1), hmem,
          htrans (x, arch x) (0, 1)⟩
      · have hx1 : (1 : ℝ) ≤ |x| := le_of_not_gt hxlt
        have hxpm : x = 1 ∨ x = -1 := by
          have hxabs : |x| = 1 := le_antisymm (abs_le.mpr (Set.mem_Icc.mp hx)) hx1
          have h2 : x ^ 2 = 1 := by rw [← sq_abs, hxabs]; norm_num
          exact sq_eq_one_iff.mp h2
        have har : arch x = 0 := by
          have hxabs : |x| = 1 := le_antisymm (abs_le.mpr (Set.mem_Icc.mp hx)) hx1
          have h2 : x ^ 2 = 1 := by rw [← sq_abs, hxabs]; norm_num
          simp only [arch]
          linarith
        have hη1 : fderiv ℝ Δ (x, arch x) (0, 1) = g x := by
          rw [show (x, arch x) = (x, (0 : ℝ)) from by rw [har]]
          exact fderiv_vertical_of_row Δ ((x, 0, 0, 0) : Work.Drive.Whitney.Mdl k) (g x) x
            (fun t => hrowOff x t hx1) (hΔdiff (x, 0))
        rw [hη1]
        rw [← htopRan x hx]
        rcases hxpm with rfl | rfl
        · rw [Work.Drive.Whitney.sigR_one]
          exact hgc1
        · rw [Work.Drive.Whitney.sigR_neg_one]
          exact hgcm1
    obtain ⟨hV, hbV⟩ := linearIndependent_of_finrank_span_cons
      (E := Work.Drive.Whitney.Mdl k) (V := V x) (b := fderiv ℝ B x 1) (by
        rw [← htopRan x hx]
        exact htopRank x hx)
    exact linearIndependent_fin_append_pair hV hbV hη ha
  exact ⟨Δ, hΔsm, hder1, hder2, hrow0, hrowTop, hrowOff, hinjOn, himm, hclean,
    hframe1, hframe2⟩

end Work.Drive.PushDisc
