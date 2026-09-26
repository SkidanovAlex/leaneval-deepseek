import Mathlib
import Submission.Work.Smooth.OneManifold.Defs
import Submission.Work.Smooth.OneManifold.Basic
import Submission.Work.Smooth.OneManifold.Bridge
import Submission.Work.Smooth.Morse.Surface.param_local_injective
import Submission.Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen

/-!
# A regular level set of `g|_F` is locally Euclidean of dimension one

`Work.Smooth.OneManifold.IsLocallyEuclidean Z` says that every point of `Z` has a neighbourhood in
`Z` homeomorphic to `ℝ` (`Work.Smooth.SphereJordan.IsLocallyArc`); it is the local hypothesis under
which the classification of compact one-dimensional subsets of the surface
(`Submission/Work/Smooth/OneManifold/Classify.lean`) is stated.  This file proves it for the
regular level sets of the challenge:

`levelSet_isLocallyEuclidean_of_regularValue`:
for a `C¹` function `g` on `ℝ³` and a regular value `t` of `g|_F`
(`Work.Smooth.Morse.IsRegularValue`), the level set `Z = F ∩ {g = t}`, where `F = torus ψ` is the
embedded torus of the challenge, is locally Euclidean of dimension one.

## The argument

Let `pullback ψ g = g ∘ param ψ` be `g` read in the parameter plane of the torus and let `x ∈ Z`
be a point over the parameter `p`.  Since `t` is a regular value, `f' = fderiv ℝ (pullback ψ g) p`
does not vanish, so its kernel is a line in `ℝ²`; choosing the transverse linear functional
`trans f'` (whose kernel is complementary to `ker f'`) and applying the implicit function theorem
to the pair `(pullback ψ g, trans f')`, the plane level set `{pullback ψ g = t}` is, near `p`,
the graph of a function of `trans f'`:

* `exists_planeChart`: there is an open set `B` of parameters, inside any prescribed ball around
  the level set of `p`, and a homeomorphism `e : ℝ ≃ₜ ↥(B ∩ {pullback ψ g = t})` with `e 0 = p`.

The implicit function data is `ImplicitFunctionData.toOpenPartialHomeomorph`, whose inverse is the
parametrisation of the level piece; the homeomorphism of the plane chart is exactly that inverse.

Since the parametrisation `param ψ` is a local homeomorphism of the plane onto the surface (it is
the covering map of the torus, composed with the diffeomorphism `ψ`), it is injective on a ball
around `p` (`Work.Smooth.Morse.Surface.param_local_injective`); `B` is chosen small enough for
this.  Then

`param ψ ∘ e : ℝ → F`

is continuous and injective, and it is surjective onto `V = param ψ '' (B ∩ {pullback ψ g = t})`,
which is open in `Z` because the parametrisation is an open map onto the surface
(`Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen`, together with the identification
`param ψ '' (B ∩ {pullback ψ g = t}) = param ψ '' B ∩ Z` of `param_image_inter_levelParam`).  It
is an open map for the same reason.  Hence it is a homeomorphism of `ℝ` onto the neighbourhood `V`
of `x` in `Z`, i.e. an arc chart of `Z` at `x`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.OneManifold

noncomputable section

open scoped Topology

/-! ## A transverse linear functional -/

/-- The coordinates of a linear functional on `ℝ × ℝ`. -/
private lemma fderiv_apply_eq (f' : ℝ × ℝ →L[ℝ] ℝ) (v : ℝ × ℝ) :
    f' v = f' (1, 0) * v.1 + f' (0, 1) * v.2 := by
  have hv : v = (v.1, (0 : ℝ)) + ((0 : ℝ), v.2) := by ext <;> simp
  have h1 : ((v.1, (0 : ℝ)) : ℝ × ℝ) = v.1 • ((1 : ℝ), (0 : ℝ)) := by ext <;> simp
  have h2 : (((0 : ℝ), v.2) : ℝ × ℝ) = v.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  conv_lhs => rw [hv, map_add, h1, h2, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- One of the two coordinates of a nonzero functional does not vanish. -/
private lemma coeffs_ne {f' : ℝ × ℝ →L[ℝ] ℝ} (h : f' ≠ 0) :
    f' (1, 0) ≠ 0 ∨ f' (0, 1) ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact h (ContinuousLinearMap.ext fun v => by
    rw [fderiv_apply_eq, hc.1, hc.2]; simp)

private lemma coeffs_sq_pos {f' : ℝ × ℝ →L[ℝ] ℝ} (h : f' ≠ 0) :
    0 < (f' (1, 0)) ^ 2 + (f' (0, 1)) ^ 2 := by
  rcases coeffs_ne h with h0 | h1
  · nlinarith [sq_pos_of_ne_zero h0, sq_nonneg (f' (0, 1))]
  · nlinarith [sq_pos_of_ne_zero h1, sq_nonneg (f' (1, 0))]

/-- A nonzero functional on `ℝ × ℝ` is surjective. -/
private lemma range_eq_top_of_ne_zero {f' : ℝ × ℝ →L[ℝ] ℝ} (h : f' ≠ 0) : f'.range = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro c
  obtain ⟨v, hv⟩ : ∃ v : ℝ × ℝ, f' v ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h (ContinuousLinearMap.ext fun v => by simpa using hc v)
  refine ⟨(c / f' v) • v, ?_⟩
  rw [map_smul, smul_eq_mul]
  exact div_mul_cancel₀ c hv

/-- The functional transverse to `f'`. -/
private def trans (f' : ℝ × ℝ →L[ℝ] ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  f' (0, 1) • ContinuousLinearMap.fst ℝ ℝ ℝ - f' (1, 0) • ContinuousLinearMap.snd ℝ ℝ ℝ

private lemma trans_apply (f' : ℝ × ℝ →L[ℝ] ℝ) (v : ℝ × ℝ) :
    trans f' v = f' (0, 1) * v.1 - f' (1, 0) * v.2 := by
  simp [trans, smul_eq_mul]

private lemma trans_ne_zero {f' : ℝ × ℝ →L[ℝ] ℝ} (h : f' ≠ 0) : trans f' ≠ 0 := by
  intro hz
  have hpos := coeffs_sq_pos h
  have hv := congrArg (fun L : ℝ × ℝ →L[ℝ] ℝ => L (-(f' (0, 1)), f' (1, 0))) hz
  simp only [ContinuousLinearMap.zero_apply] at hv
  rw [trans_apply] at hv
  nlinarith [hv, hpos]

private lemma isCompl_ker_trans {f' : ℝ × ℝ →L[ℝ] ℝ} (h : f' ≠ 0) :
    IsCompl f'.ker (trans f').ker := by
  have hpos := coeffs_sq_pos h
  constructor
  · rw [LinearMap.disjoint_ker]
    intro v hv hgv
    have ha : f' (1, 0) * v.1 + f' (0, 1) * v.2 = 0 := by
      rw [← fderiv_apply_eq f' v]; exact hv
    have hb : f' (0, 1) * v.1 - f' (1, 0) * v.2 = 0 := by
      rw [← trans_apply f' v]; exact hgv
    have h1 : v.1 = 0 := by
      have hkey : ((f' (1, 0)) ^ 2 + (f' (0, 1)) ^ 2) * v.1 = 0 := by
        linear_combination f' (1, 0) * ha + f' (0, 1) * hb
      nlinarith [hkey, hpos]
    have h2 : v.2 = 0 := by
      have hkey : ((f' (1, 0)) ^ 2 + (f' (0, 1)) ^ 2) * v.2 = 0 := by
        linear_combination f' (0, 1) * ha - f' (1, 0) * hb
      nlinarith [hkey, hpos]
    ext <;> simp [h1, h2]
  · rw [Submodule.codisjoint_iff_exists_add_eq]
    intro z
    have hpt : f' ((f' (1, 0), f' (0, 1)) : ℝ × ℝ) = (f' (1, 0)) ^ 2 + (f' (0, 1)) ^ 2 := by
      rw [fderiv_apply_eq]; ring
    have hpt' : trans f' ((f' (1, 0), f' (0, 1)) : ℝ × ℝ) = 0 := by
      rw [trans_apply]; ring
    have hmap : f' (z - (f' z / ((f' (1, 0)) ^ 2 + (f' (0, 1)) ^ 2)) •
            ((f' (1, 0), f' (0, 1)) : ℝ × ℝ))
        = f' z - (f' z / ((f' (1, 0)) ^ 2 + (f' (0, 1)) ^ 2)) *
            f' ((f' (1, 0), f' (0, 1)) : ℝ × ℝ) := by
      rw [map_sub, map_smul, smul_eq_mul]
    have hmap' : trans f' ((f' z / ((f' (1, 0)) ^ 2 + (f' (0, 1)) ^ 2)) •
            ((f' (1, 0), f' (0, 1)) : ℝ × ℝ))
        = (f' z / ((f' (1, 0)) ^ 2 + (f' (0, 1)) ^ 2)) *
            trans f' ((f' (1, 0), f' (0, 1)) : ℝ × ℝ) := by
      rw [map_smul, smul_eq_mul]
    refine ⟨z - (f' z / ((f' (1, 0)) ^ 2 + (f' (0, 1)) ^ 2)) •
              ((f' (1, 0), f' (0, 1)) : ℝ × ℝ),
            (f' z / ((f' (1, 0)) ^ 2 + (f' (0, 1)) ^ 2)) •
              ((f' (1, 0), f' (0, 1)) : ℝ × ℝ), ?_, ?_, ?_⟩
    · show (f' : ℝ × ℝ → ℝ) (z - (f' z / ((f' (1, 0)) ^ 2 + (f' (0, 1)) ^ 2)) •
            ((f' (1, 0), f' (0, 1)) : ℝ × ℝ)) = 0
      rw [hmap, hpt, div_mul_cancel₀ _ (ne_of_gt hpos), sub_self]
    · show (trans f' : ℝ × ℝ → ℝ) ((f' z / ((f' (1, 0)) ^ 2 + (f' (0, 1)) ^ 2)) •
            ((f' (1, 0), f' (0, 1)) : ℝ × ℝ)) = 0
      rw [hmap', hpt', mul_zero]
    · abel

/-! ## The plane chart lemma -/

/-- **A regular level set in the plane is locally a graph.**  If `f : ℝ × ℝ → ℝ` is strictly
differentiable at `p` with `f p = t` and nonzero derivative, then there is an open set `B`
(contained in any prescribed ball around `p` near the level set) and a homeomorphism of `ℝ` onto
`B ∩ {f = t}` sending `0` to `p`.

The proof is the implicit function theorem: with `f' = fderiv ℝ f p` and the transverse functional
`trans f'` (whose kernel is complementary to `ker f'`), the map `x ↦ (f x, trans f' x)` is an open
partial homeomorphism `E`, and the piece of the level set cut out by a small interval of values of
`trans f'` is parametrised by that interval, with inverse `x ↦ trans f' x`. -/
private theorem exists_planeChart {f : ℝ × ℝ → ℝ} {f' : ℝ × ℝ →L[ℝ] ℝ} {p : ℝ × ℝ} {t δ : ℝ}
    (hsd : HasStrictFDerivAt f f' p) (hp : f p = t) (hd : f' ≠ 0) (hδ : 0 < δ) :
    ∃ (B : Set (ℝ × ℝ)) (e : ℝ ≃ₜ ↥(B ∩ {q : ℝ × ℝ | f q = t})),
      IsOpen B ∧ B ∩ {q : ℝ × ℝ | f q = t} ⊆ Metric.ball p δ ∧
        ((e 0 : ↥(B ∩ {q : ℝ × ℝ | f q = t})) : ℝ × ℝ) = p := by
  classical
  set φ : ImplicitFunctionData ℝ (ℝ × ℝ) ℝ ℝ :=
    { leftFun := f
      leftDeriv := f'
      rightFun := trans f'
      rightDeriv := trans f'
      pt := p
      hasStrictFDerivAt_leftFun := hsd
      hasStrictFDerivAt_rightFun := ContinuousLinearMap.hasStrictFDerivAt (trans f')
      range_leftDeriv := range_eq_top_of_ne_zero hd
      range_rightDeriv := range_eq_top_of_ne_zero (trans_ne_zero hd)
      isCompl_ker := isCompl_ker_trans hd } with hφ
  set E : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) := φ.toOpenPartialHomeomorph with hE
  have hφleft : φ.leftFun = f := by rw [hφ]
  have hφright : φ.rightFun = trans f' := by rw [hφ]
  have hφpt : φ.pt = p := by rw [hφ]
  have hE_apply : ∀ x : ℝ × ℝ, E x = (f x, trans f' x) := by
    intro x
    rw [hE, ImplicitFunctionData.toOpenPartialHomeomorph_coe, ImplicitFunctionData.prodFun_apply,
      hφleft, hφright]
  have hsrc : p ∈ E.source := by
    rw [hE, ← hφpt]
    exact φ.pt_mem_toOpenPartialHomeomorph_source
  have htgt : (t, trans f' p) ∈ E.target := by
    rw [hE]
    have h := φ.map_pt_mem_toOpenPartialHomeomorph_target
    have h' : (φ.leftFun φ.pt, φ.rightFun φ.pt) = (t, trans f' p) := by
      rw [hφleft, hφright, hφpt, hp]
    rwa [h'] at h
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (E.open_target.mem_nhds htgt)
  have hcont : ContinuousAt (fun u : ℝ => E.symm (t, u)) (trans f' p) :=
    (E.continuousAt_symm htgt).comp (by fun_prop)
  obtain ⟨η, hη, hηsub⟩ := Metric.continuousAt_iff.mp hcont (δ / 2) (by linarith)
  have hpval : E.symm (t, trans f' p) = p := by
    have h1 : E p = (t, trans f' p) := by rw [hE_apply, hp]
    rw [← h1]
    exact E.left_inv hsrc
  set c : ℝ := min r η / 2 with hcdef
  have hcpos : 0 < c := by rw [hcdef]; exact half_pos (lt_min hr hη)
  have hcr : c < r := by rw [hcdef]; have := min_le_left r η; linarith
  have hcη : c < η := by rw [hcdef]; have := min_le_right r η; linarith
  set B : Set (ℝ × ℝ) :=
    E.source ∩ {q : ℝ × ℝ | trans f' q ∈ Set.Ioo (trans f' p - c) (trans f' p + c)} with hBdef
  have hBopen : IsOpen B := by
    rw [hBdef]
    exact E.open_source.inter (isOpen_Ioo.preimage (trans f').continuous)
  have hseg : ∀ u : ℝ, u ∈ Set.Ioo (trans f' p - c) (trans f' p + c) → (t, u) ∈ E.target := by
    intro u hu
    apply hball
    rw [Metric.mem_ball]
    have hdist : dist (t, u) (t, trans f' p) = |u - trans f' p| := by
      rw [Prod.dist_eq, Real.dist_eq, sub_self, abs_zero]
      exact max_eq_right (abs_nonneg _)
    rw [hdist]
    exact lt_of_lt_of_le (abs_lt.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩) hcr.le
  have hBsub : B ∩ {q : ℝ × ℝ | f q = t} ⊆ Metric.ball p δ := by
    intro q hq
    obtain ⟨⟨hqsrc, hqI⟩, hqt⟩ := hq
    have hqval : q = E.symm (t, trans f' q) := by
      have h1 : E q = (t, trans f' q) := by rw [hE_apply, hqt]
      rw [← h1]
      exact (E.left_inv hqsrc).symm
    have hgt : dist (trans f' q) (trans f' p) < η := by
      rw [Real.dist_eq]
      exact lt_of_lt_of_le (abs_lt.mpr ⟨by linarith [hqI.1], by linarith [hqI.2]⟩) hcη.le
    have hstep : dist (E.symm (t, trans f' q)) (E.symm (t, trans f' p)) < δ / 2 := hηsub hgt
    rw [Metric.mem_ball, hqval]
    rw [hpval] at hstep
    linarith
  set w : ℝ ≃ₜ ↥(Set.Ioo (trans f' p - c) (trans f' p + c)) :=
    homeomorphIooCentre (trans f' p) c hcpos with hwdef
  have hw0 : (w 0 : ℝ) = trans f' p := homeomorphIooCentre_zero (trans f' p) c hcpos
  have hFmem : ∀ u : ℝ, E.symm (t, (w u : ℝ)) ∈ B ∩ {q : ℝ × ℝ | f q = t} := by
    intro u
    have h1 : (t, (w u : ℝ)) ∈ E.target := hseg _ (w u).2
    have h2 : E (E.symm (t, (w u : ℝ))) = (t, (w u : ℝ)) := E.right_inv h1
    have h3 : E (E.symm (t, (w u : ℝ)))
        = (f (E.symm (t, (w u : ℝ))), trans f' (E.symm (t, (w u : ℝ)))) := hE_apply _
    rw [h3] at h2
    refine ⟨⟨E.symm.mapsTo h1, ?_⟩, congrArg Prod.fst h2⟩
    have h4 : trans f' (E.symm (t, (w u : ℝ))) = (w u : ℝ) := congrArg Prod.snd h2
    show trans f' (E.symm (t, (w u : ℝ))) ∈
      Set.Ioo (trans f' p - c) (trans f' p + c)
    rw [h4]
    exact (w u).2
  let F : ℝ → ↥(B ∩ {q : ℝ × ℝ | f q = t}) := fun u => ⟨E.symm (t, (w u : ℝ)), hFmem u⟩
  have hzIoo : ∀ z : ↥(B ∩ {q : ℝ × ℝ | f q = t}),
      trans f' (z : ℝ × ℝ) ∈ Set.Ioo (trans f' p - c) (trans f' p + c) :=
    fun z => z.2.1.2
  have hzS : ∀ z : ↥(B ∩ {q : ℝ × ℝ | f q = t}), f (z : ℝ × ℝ) = t := fun z => z.2.2
  have hzsrc : ∀ z : ↥(B ∩ {q : ℝ × ℝ | f q = t}), (z : ℝ × ℝ) ∈ E.source :=
    fun z => z.2.1.1
  let G : ↥(B ∩ {q : ℝ × ℝ | f q = t}) → ℝ :=
    fun z => w.symm ⟨trans f' (z : ℝ × ℝ), hzIoo z⟩
  have hFG : ∀ u : ℝ, G (F u) = u := by
    intro u
    have h1 : (t, (w u : ℝ)) ∈ E.target := hseg _ (w u).2
    have h2 : E (E.symm (t, (w u : ℝ))) = (t, (w u : ℝ)) := E.right_inv h1
    have h3 := hE_apply (E.symm (t, (w u : ℝ)))
    rw [h3] at h2
    have h4 : trans f' (E.symm (t, (w u : ℝ))) = (w u : ℝ) := congrArg Prod.snd h2
    have h5 : (⟨trans f' (F u : ℝ × ℝ), hzIoo (F u)⟩ :
        ↥(Set.Ioo (trans f' p - c) (trans f' p + c))) = w u := Subtype.ext h4
    show w.symm ⟨trans f' (F u : ℝ × ℝ), hzIoo (F u)⟩ = u
    rw [h5]
    exact w.symm_apply_apply u
  have hGF : ∀ z : ↥(B ∩ {q : ℝ × ℝ | f q = t}), F (G z) = z := by
    intro z
    apply Subtype.ext
    show E.symm (t, (w (G z) : ℝ)) = (z : ℝ × ℝ)
    have hy := Homeomorph.apply_symm_apply w
      (⟨trans f' (z : ℝ × ℝ), hzIoo z⟩ :
        ↥(Set.Ioo (trans f' p - c) (trans f' p + c)))
    have h1 : (w (G z) : ℝ) = trans f' (z : ℝ × ℝ) := (congrArg Subtype.val hy.symm).symm
    rw [h1]
    have h2 : E (z : ℝ × ℝ) = (t, trans f' (z : ℝ × ℝ)) := by
      rw [hE_apply, hzS z]
    rw [← h2]
    exact E.left_inv (hzsrc z)
  have hFcont : Continuous F := by
    refine Continuous.subtype_mk ?_ hFmem
    have hfun : (fun u : ℝ => E.symm (t, (w u : ℝ))) =
        E.symm ∘ (fun u : ℝ => (t, (w u : ℝ))) := rfl
    rw [hfun]
    exact E.continuousOn_symm.comp_continuous
      (Continuous.prodMk continuous_const (continuous_subtype_val.comp w.continuous))
      (fun u => hseg _ (w u).2)
  have hGcont : Continuous G := by
    have h1 : Continuous (fun z : ↥(B ∩ {q : ℝ × ℝ | f q = t}) =>
        (⟨trans f' (z : ℝ × ℝ), hzIoo z⟩ :
          ↥(Set.Ioo (trans f' p - c) (trans f' p + c)))) :=
      Continuous.subtype_mk ((trans f').continuous.comp continuous_subtype_val) hzIoo
    exact w.symm.continuous.comp h1
  let hhomeo : ℝ ≃ₜ ↥(B ∩ {q : ℝ × ℝ | f q = t}) :=
    { toFun := F
      invFun := G
      left_inv := hFG
      right_inv := hGF
      continuous_toFun := hFcont
      continuous_invFun := hGcont }
  refine ⟨B, hhomeo, hBopen, hBsub, ?_⟩
  show E.symm (t, (w 0 : ℝ)) = p
  rw [hw0]
  exact hpval

/-! ## The level set in the parameter plane -/

/-- The level set of the pull-back, in the parameter plane. -/
private def levelParam (ψ : Submission.Diffeo) (g : R3 → ℝ) (t : ℝ) : Set (ℝ × ℝ) :=
  {q : ℝ × ℝ | Work.Smooth.Morse.pullback ψ g q = t}

/-- The image under the parametrisation of a subset of the plane level set. -/
private theorem param_image_inter_levelParam (ψ : Submission.Diffeo) (g : R3 → ℝ) (t : ℝ)
    (B : Set (ℝ × ℝ)) :
    Work.Smooth.Morse.param ψ '' (B ∩ levelParam ψ g t)
      = Work.Smooth.Morse.param ψ '' B ∩ Work.Smooth.Morse.levelSet ψ g t := by
  ext y
  constructor
  · rintro ⟨q, ⟨hqB, hq⟩, rfl⟩
    refine ⟨⟨q, hqB, rfl⟩, ?_⟩
    rw [Work.Smooth.Morse.mem_levelSet]
    exact ⟨Work.Smooth.Morse.param_mem ψ q, hq⟩
  · rintro ⟨⟨q, hqB, rfl⟩, hy⟩
    rw [Work.Smooth.Morse.mem_levelSet] at hy
    exact ⟨q, ⟨hqB, hy.2⟩, rfl⟩

/-! ## The main theorem -/

/-- **A regular level set of `g|_F` is locally Euclidean of dimension one.**

Every point of `Z = levelSet ψ g t = F ∩ {g = t}`, where `F = torus ψ` is the embedded torus of
the challenge and `t` is a regular value of `g|_F`, has a neighbourhood in `Z` homeomorphic to `ℝ`.

Let `p` be a parameter point with `param ψ p = x`.  Since `t` is a regular value, `fderiv ℝ
(pullback ψ g) p ≠ 0`, so by the implicit function theorem
(`exists_planeChart`) the plane level set `{pullback ψ g = t}` is, near `p`, the graph over an
open set `B` of parameters: there is a homeomorphism `e : ℝ ≃ₜ ↥(B ∩ {pullback ψ g = t})` with
`e 0 = p`, and `B` is chosen so small (inside the radius on which `param ψ` is injective) that
the parametrisation is injective on `B ∩ {pullback ψ g = t}`.

Then `param ψ ∘ e : ℝ → F` is a continuous bijection onto `V = param ψ '' (B ∩ {pullback ψ g = t})`,
which is open in `Z` because `param ψ` is an open map onto the surface
(`param_image_inter_levelParam` identifies `V = param ψ '' B ∩ Z`); it is an open map because the
image of an open set of parameters is open in the surface.  Hence it is a homeomorphism of `ℝ`
onto the neighbourhood `V` of `x` in `Z`. -/
theorem levelSet_isLocallyEuclidean_of_regularValue (ψ : Submission.Diffeo)
    {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ} (hg : ContDiff ℝ 1 g) {t : ℝ}
    (hreg : Work.Smooth.Morse.IsRegularValue ψ g t) :
    Work.Smooth.OneManifold.IsLocallyEuclidean (Work.Smooth.Morse.levelSet ψ g t) := by
  intro x
  obtain ⟨p, hp⟩ : ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = (x : R3) := x.2.1
  have hpull : Work.Smooth.Morse.pullback ψ g p = t := by
    show g (Work.Smooth.Morse.param ψ p) = t
    rw [hp]
    exact x.2.2
  have hd : fderiv ℝ (Work.Smooth.Morse.pullback ψ g) p ≠ 0 :=
    (Work.Smooth.Morse.isRegularValue_iff ψ g t).mp hreg p hpull
  have hdiff : ContDiff ℝ 1 (Work.Smooth.Morse.pullback ψ g) :=
    Work.Smooth.Morse.pullback_contDiff_one ψ hg
  obtain ⟨ε, hε, hinj⟩ := Work.Smooth.Morse.Surface.param_local_injective ψ p
  obtain ⟨B, e, hBopen, hBsub, he0⟩ :=
    exists_planeChart (f := Work.Smooth.Morse.pullback ψ g)
      (f' := fderiv ℝ (Work.Smooth.Morse.pullback ψ g) p)
      (hsd := hdiff.contDiffAt.hasStrictFDerivAt (by norm_num)) hpull hd hε
  have hinjB : Set.InjOn (Work.Smooth.Morse.param ψ) (B ∩ levelParam ψ g t) :=
    fun a ha b hb hab => hinj (hBsub ha) (hBsub hb) hab
  let V : Set R3 := Work.Smooth.Morse.param ψ '' (B ∩ levelParam ψ g t)
  have hVsub : V ⊆ Work.Smooth.Morse.levelSet ψ g t := by
    rintro y ⟨q, hq, rfl⟩
    rw [Work.Smooth.Morse.mem_levelSet]
    exact ⟨Work.Smooth.Morse.param_mem ψ q, hq.2⟩
  have hVopen : IsOpenInSet (Work.Smooth.Morse.levelSet ψ g t) V := by
    have hEq : V = Work.Smooth.Morse.param ψ '' B ∩ Work.Smooth.Morse.levelSet ψ g t :=
      param_image_inter_levelParam ψ g t B
    rw [hEq]
    exact isOpenInSet_inter_of_isOpenInCarrier (Work.Smooth.Morse.levelSet_subset_carrier ψ g t)
      (Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ hBopen)
  have hxV : (x : R3) ∈ V := by
    refine ⟨p, ⟨?_, hpull⟩, hp⟩
    rw [← he0]
    exact (e 0).2.1
  let F : ℝ → ↥V := fun u =>
    ⟨Work.Smooth.Morse.param ψ (e u : ℝ × ℝ), ⟨(e u : ℝ × ℝ), (e u).2, rfl⟩⟩
  have hFinj : Function.Injective F := by
    intro u v huv
    have h1 : Work.Smooth.Morse.param ψ (e u : ℝ × ℝ)
        = Work.Smooth.Morse.param ψ (e v : ℝ × ℝ) := by
      have h := congrArg (fun y : ↥V => (y : R3)) huv
      simpa using h
    have h2 : (e u : ℝ × ℝ) = (e v : ℝ × ℝ) := hinjB (e u).2 (e v).2 h1
    exact e.injective (Subtype.ext h2)
  have hFsurj : Function.Surjective F := by
    intro y
    obtain ⟨q, hq, hqy⟩ := y.2
    refine ⟨e.symm ⟨q, hq⟩, ?_⟩
    apply Subtype.ext
    show Work.Smooth.Morse.param ψ (e (e.symm ⟨q, hq⟩) : ℝ × ℝ) = (y : R3)
    rw [Homeomorph.apply_symm_apply]
    exact hqy
  have hFcont : Continuous F :=
    Continuous.subtype_mk
      ((Work.Smooth.Morse.param_continuous ψ).comp
        (continuous_subtype_val.comp e.continuous)) _
  have hFopen : IsOpenMap F := by
    intro O hO
    have hOS : IsOpen (e '' O) := e.isOpenMap O hO
    obtain ⟨B₁, hB₁open, hB₁eq⟩ := isOpen_induced_iff.mp hOS
    let B₂ : Set (ℝ × ℝ) := B ∩ B₁
    have hB₂open : IsOpen B₂ := hBopen.inter hB₁open
    have hbase : ∀ q : ℝ × ℝ, q ∈ B₂ ∩ levelParam ψ g t ↔ q ∈ Subtype.val '' (e '' O) := by
      intro q
      constructor
      · rintro ⟨⟨hqB, hqB₁⟩, hqL⟩
        refine ⟨⟨q, ⟨hqB, hqL⟩⟩, ?_, rfl⟩
        rw [← hB₁eq]
        exact hqB₁
      · rintro ⟨z, hz, rfl⟩
        have hzB₁ : (z : ℝ × ℝ) ∈ B₁ := by
          rw [← hB₁eq] at hz
          exact hz
        exact ⟨⟨z.2.1, hzB₁⟩, z.2.2⟩
    have hFim : F '' O
        = Subtype.val ⁻¹' (Work.Smooth.Morse.param ψ '' (B₂ ∩ levelParam ψ g t)) := by
      ext y
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨(e u : ℝ × ℝ), (hbase (e u : ℝ × ℝ)).mpr ⟨e u, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩
      · rintro ⟨q, hq, hqy⟩
        obtain ⟨z, hz, hzq⟩ := (hbase q).mp hq
        obtain ⟨u, hu, hzu⟩ := hz
        have hzF : F u = y := by
          apply Subtype.ext
          show Work.Smooth.Morse.param ψ (e u : ℝ × ℝ) = (y : R3)
          rw [hzu, hzq]
          exact hqy
        exact ⟨u, hu, hzF⟩
    rw [hFim]
    have hZopen : IsOpenInSet (Work.Smooth.Morse.levelSet ψ g t)
        (Work.Smooth.Morse.param ψ '' (B₂ ∩ levelParam ψ g t)) := by
      rw [param_image_inter_levelParam ψ g t B₂]
      exact isOpenInSet_inter_of_isOpenInCarrier (Work.Smooth.Morse.levelSet_subset_carrier ψ g t)
        (Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ hB₂open)
    have hcont : Continuous (fun y : ↥V =>
        (⟨(y : R3), hVsub y.2⟩ : ↥(Work.Smooth.Morse.levelSet ψ g t))) :=
      Continuous.subtype_mk continuous_subtype_val _
    convert hZopen.preimage hcont using 1
    ext y
    rfl
  have h0 : (Equiv.ofBijective F ⟨hFinj, hFsurj⟩).toHomeomorphOfContinuousOpen hFcont hFopen 0
      = (⟨(x : R3), hxV⟩ : ↥V) := by
    apply Subtype.ext
    show Work.Smooth.Morse.param ψ (e 0 : ℝ × ℝ) = (x : R3)
    rw [he0]
    exact hp
  refine ⟨{ V := Subtype.val ⁻¹' V
            isOpen_V := hVopen
            mem_V := hxV
            homeo := ((Equiv.ofBijective F ⟨hFinj, hFsurj⟩).toHomeomorphOfContinuousOpen
                hFcont hFopen).trans
              (Work.Smooth.SphereJordan.LocalArc.subtypeSubtypeHomeomorph hVsub)
            homeo_zero := ?_ }⟩
  rw [Homeomorph.trans_apply, h0]
  apply Subtype.ext
  apply Subtype.ext
  rfl

end

end Work.Smooth.OneManifold
