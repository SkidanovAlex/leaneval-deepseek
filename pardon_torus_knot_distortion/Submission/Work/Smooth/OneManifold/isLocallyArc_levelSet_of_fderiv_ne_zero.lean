import Mathlib
import Submission.Work.Smooth.OneManifold.Plane.Basic
import Submission.Work.Smooth.Morse.Regular.arc_data_snd

/-!
# A regular level set in the plane is locally an arc

If `f : ℝ × ℝ → ℝ` is `C¹` at `p`, with `f p = t` and `fderiv ℝ f p ≠ 0`, then near `p` the
level set `{q | f q = t}` is a one-dimensional submanifold of the plane, hence locally an arc
(`Work.Smooth.SphereJordan.IsLocallyArc`).

The proof is the implicit function theorem in its "local homeomorphism" form.  With
`f' = fderiv ℝ f p ≠ 0` we build the transverse linear functional `trans f'` (whose kernel is a
complement of `ker f'`); then `E q = (f q, trans f' q)` is a `C¹` local homeomorphism near `p`,
because its derivative is the invertible linear map with components `(f', trans f')`.  Cutting the
target of `E` by a small interval of second coordinates gives an open set `B` around `p` such that
`E` restricts to a homeomorphism of `B ∩ {f = t}` with (an open interval of) `ℝ`.
-/

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

/-! ## The local homeomorphism of the level set -/

/-- **A regular level set in the plane is locally a graph, hence a neighbourhood of `p` in it is
homeomorphic to `ℝ`.**  If `f` is strictly differentiable at `p` with derivative `f' ≠ 0` and
`f p = t`, then there is an open set `B ∋ p` and a homeomorphism `e : ℝ ≃ₜ ↥(B ∩ {f = t})` sending
`0` to `p`.

The proof is the implicit function theorem: with the transverse functional `trans f'` (whose kernel
is complementary to `ker f'`), the map `q ↦ (f q, trans f' q)` is an open partial homeomorphism `E`,
and the piece of the level set cut out by a small interval of values of `trans f'` is parametrised
by that interval, with inverse `q ↦ trans f' q`. -/
private theorem exists_arcChart_levelSet {f : ℝ × ℝ → ℝ} {f' : ℝ × ℝ →L[ℝ] ℝ}
    {p : ℝ × ℝ} {t : ℝ}
    (hsd : HasStrictFDerivAt f f' p) (hp : f p = t) (hd : f' ≠ 0) :
    ∃ (B : Set (ℝ × ℝ)) (e : ℝ ≃ₜ ↥(B ∩ {q : ℝ × ℝ | f q = t})),
      IsOpen B ∧ p ∈ B ∧ ((e 0 : ↥(B ∩ {q : ℝ × ℝ | f q = t})) : ℝ × ℝ) = p := by
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
  have hpval : E.symm (t, trans f' p) = p := by
    have h1 : E p = (t, trans f' p) := by rw [hE_apply, hp]
    rw [← h1]
    exact E.left_inv hsrc
  set c : ℝ := r / 2 with hcdef
  have hcpos : 0 < c := by rw [hcdef]; exact half_pos hr
  have hcr : c < r := by rw [hcdef]; linarith
  set B : Set (ℝ × ℝ) :=
    E.source ∩ {q : ℝ × ℝ | trans f' q ∈ Set.Ioo (trans f' p - c) (trans f' p + c)} with hBdef
  have hBopen : IsOpen B := by
    rw [hBdef]
    exact E.open_source.inter (isOpen_Ioo.preimage (trans f').continuous)
  have hmemB : p ∈ B := by
    rw [hBdef]
    exact ⟨hsrc, by constructor <;> linarith⟩
  have hseg : ∀ u : ℝ, u ∈ Set.Ioo (trans f' p - c) (trans f' p + c) → (t, u) ∈ E.target := by
    intro u hu
    apply hball
    rw [Metric.mem_ball]
    have hdist : dist (t, u) (t, trans f' p) = |u - trans f' p| := by
      rw [Prod.dist_eq, Real.dist_eq, sub_self, abs_zero]
      exact max_eq_right (abs_nonneg _)
    rw [hdist]
    exact lt_of_lt_of_le (abs_lt.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩) hcr.le
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
  refine ⟨B, hhomeo, hBopen, hmemB, ?_⟩
  show E.symm (t, (w 0 : ℝ)) = p
  rw [hw0]
  exact hpval

/-! ## The requested lemma -/

/-- **A regular level set in the plane is locally an arc.**  If `f : ℝ × ℝ → ℝ` is `C¹` at `p`,
with `f p = t` and nonzero derivative, then there is an open neighbourhood `V` of `p` such that
`V ∩ {f = t}` is locally an arc. -/
theorem isLocallyArc_levelSet_of_fderiv_ne_zero {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {t : ℝ}
    (hf : ContDiffAt ℝ 1 f p) (hp : f p = t) (hd : fderiv ℝ f p ≠ 0) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ p ∈ V ∧
      Work.Smooth.SphereJordan.IsLocallyArc ↥(V ∩ {q : ℝ × ℝ | f q = t}) := by
  obtain ⟨B, e, hBopen, hpB, -⟩ :=
    exists_arcChart_levelSet (f := f) (f' := fderiv ℝ f p) (p := p) (t := t)
      (hsd := hf.hasStrictFDerivAt (by norm_num)) hp hd
  exact ⟨B, hBopen, hpB, isLocallyArc_of_homeomorph e isLocallyArc_real⟩

end

end Work.Smooth.OneManifold
