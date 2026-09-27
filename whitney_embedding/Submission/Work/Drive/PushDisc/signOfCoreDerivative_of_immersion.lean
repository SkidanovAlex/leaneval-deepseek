import Mathlib
import Submission.Work.Drive.PushDisc.signCoreBricks
import Submission.Work.Drive.PushDisc.asymSignDefs
import Submission.Work.Drive.PushDisc.asymSignTransport
import Submission.Work.Drive.PushDisc.pairDet_model
import Submission.Work.Drive.PushDisc.det_fderiv_mul_pos
import Submission.Work.Whitney.pairDet_mul_sign_iff_of_isArcChain

/-!
# `Work.Drive.PushDisc.signOfCoreDerivative_of_immersion`

The sign coherence of the *core* derivative of the second sheet of a Whitney bigon.

The statement (requested by the consumer `Work.Drive.PushDisc.asymChartDataOfTiny`) is:

```
∃ a b : ℝ,
  HasDerivAt (fun x : ℝ => (Φ (f (c₂.symm ((splitE k) (x, 0))))).2.1) a (-1) ∧
  HasDerivAt (fun x : ℝ => (Φ (f (c₂.symm ((splitE k) (x, 0))))).2.1) b 1 ∧ a * b < 0
```

i.e. *the derivative of the height of the core of the second sheet along the `x`-line changes sign
between the two crossings of the bigon*.  The plan of the proof is exactly the one recorded in the
docstring of `Work.Drive.PushDisc.signOfCoreDerivative`:

* `pairDet f c₁ c₂ p₁ p₂ = det (pairEquiv ∘ dΘ ∘ pairZ'⁻¹) * det e(p₁) * a`,
  `pairDet f c₁ c₂ q₁ q₂ = det (pairEquiv ∘ dΘ ∘ pairZ'⁻¹) * det e(q₁) * b`,
  where `e` is the `(x,u)`-Jacobian of the *first* sheet and `a`, `b` are the two core derivatives
  (this is `Work.Drive.PushDisc.det_pairZ_coprod_components`, the block computation of the crossing);
* `0 < det (pairEquiv ∘ dΘ ∘ pairZ'⁻¹) at p₁ * det (pairEquiv ∘ dΘ ∘ pairZ'⁻¹) at q₁`
  (positivity of the global chart factor, `det_fderiv_mul_pos`);
* `0 < det e(p₁) * det e(q₁)`: the *immersion* hypothesis makes `e` invertible along the arc `γ₁`,
  and its determinant is continuous and never zero on `[0,1]`, hence of constant sign;
* `hsign` gives `pairDet f c₁ c₂ p₁ p₂ * pairDet f c₁ c₂ q₁ q₂ < 0` (transport along the two arcs,
  `pairDet_mul_sign_iff_of_isArcChain` against the two *constant* chains).

Multiplying out gives `a * b < 0`.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Set Filter

namespace Work.Drive.PushDisc

/-- `EE k = E^{k+1} × E^{k+1}`, the codomain of `Work.Projection.pairEquiv`. -/
abbrev EE (k : ℕ) := EuclideanSpace ℝ (Fin (k + 1)) × EuclideanSpace ℝ (Fin (k + 1))

/-- `PP k = ℝ × E^k`, the block of the model space. -/
abbrev PP (k : ℕ) := ℝ × EuclideanSpace ℝ (Fin k)

/-! ## The `(x,u)`- and `(y,v)`-projections of the model space -/

/-- The `(x,u)`-projection of the model space. -/
noncomputable def Xu (k : ℕ) : Work.Drive.Whitney.Mdl k →ₗ[ℝ] PP k :=
  (LinearMap.fst ℝ (PP k) (PP k)).comp (pairZ k).toLinearMap

/-- The `(y,v)`-projection of the model space. -/
noncomputable def Yv (k : ℕ) : Work.Drive.Whitney.Mdl k →ₗ[ℝ] PP k :=
  (LinearMap.snd ℝ (PP k) (PP k)).comp (pairZ k).toLinearMap

@[simp] theorem Xu_apply (k : ℕ) (ξ : Work.Drive.Whitney.Mdl k) :
    Xu k ξ = (ξ.1, ξ.2.2.1) := rfl

@[simp] theorem Yv_apply (k : ℕ) (ξ : Work.Drive.Whitney.Mdl k) :
    Yv k ξ = (ξ.2.1, ξ.2.2.2) := rfl

theorem pairZ_eq_prod (k : ℕ) :
    (pairZ k).toLinearMap = (Xu k).prod (Yv k) := by
  apply LinearMap.ext
  intro ξ
  simp [Xu, Yv, Function.prod]

theorem pairZ_comp_incLM (k : ℕ) :
    (pairZ k).toLinearMap.comp (incLM k)
      = (LinearMap.id : PP k →ₗ[ℝ] PP k).prod (0 : PP k →ₗ[ℝ] PP k) := by
  apply LinearMap.ext
  intro p
  simp [pairZ, incLM_apply, LinearMap.prod_apply, Function.prod]

theorem pairZ_symm_comp_toLinearMap (k : ℕ) :
    (pairZ k).symm.toLinearMap.comp (pairZ k).toLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp

/-! ## The block determinant of a crossing in the model coordinates -/

/-- **The determinant of the split crossing in the `(x,u)`,`(y,v)` coordinates**, for a first sheet
which is a graph over its own `(x,u)`-shadow (its jet is `incLM ∘ e`) and a second sheet whose
`(x,v)`-block is the identity (its jet is `pairZ⁻¹ ∘ (g₁.prod (y'.prod snd))`). -/
theorem det_pairZ_coprod_of_shape {k : ℕ}
    (A' B' : PP k →ₗ[ℝ] Work.Drive.Whitney.Mdl k)
    (hA : ∀ w, Yv k (A' w) = 0)
    (hB : ∀ w, (Yv k (B' w)).2 = w.2) :
    LinearMap.det ((pairZ k).toLinearMap.comp (A'.coprod B'))
      = LinearMap.det ((Xu k).comp A')
        * (((LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin k))).comp ((Yv k).comp B'))
            ((1 : ℝ), 0)) := by
  set e : PP k →ₗ[ℝ] PP k := (Xu k).comp A' with he
  set g₁ : PP k →ₗ[ℝ] PP k := (Xu k).comp B' with hg₁
  set y' : PP k →ₗ[ℝ] ℝ :=
    (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin k))).comp ((Yv k).comp B') with hy'
  have hYvA : (Yv k).comp A' = 0 := by
    apply LinearMap.ext
    intro w
    simpa using hA w
  have hYvB : (Yv k).comp B'
      = y'.prod (LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin k))) := by
    apply LinearMap.ext
    intro w
    refine Prod.ext ?_ ?_
    · simp [y']
    · simpa using hB w
  have hAeq : A' = (incLM k).comp e := by
    have h1 : (pairZ k).toLinearMap.comp A'
        = ((LinearMap.id : PP k →ₗ[ℝ] PP k).prod (0 : PP k →ₗ[ℝ] PP k)).comp e := by
      rw [pairZ_eq_prod k, LinearMap.prod_comp, hYvA, he]
      apply LinearMap.ext
      intro w
      rfl
    have h2 : (pairZ k).toLinearMap.comp ((incLM k).comp e)
        = ((LinearMap.id : PP k →ₗ[ℝ] PP k).prod (0 : PP k →ₗ[ℝ] PP k)).comp e := by
      rw [← LinearMap.comp_assoc, pairZ_comp_incLM k, LinearMap.prod_comp]
    have h3 : (pairZ k).toLinearMap.comp A'
        = (pairZ k).toLinearMap.comp ((incLM k).comp e) := by rw [h1, h2]
    apply LinearMap.ext
    intro w
    exact (pairZ k).injective (by simpa using congrArg (fun L => L w) h3)
  have hBeq : B' = (pairZ k).symm.toLinearMap.comp
      (g₁.prod (y'.prod (LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin k))))) := by
    have h1 : (pairZ k).toLinearMap.comp B'
        = g₁.prod (y'.prod (LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin k)))) := by
      rw [pairZ_eq_prod k, LinearMap.prod_comp, hYvB, hg₁]
    rw [← h1, ← LinearMap.comp_assoc, pairZ_symm_comp_toLinearMap k, LinearMap.id_comp]
  rw [hAeq, hBeq]
  exact det_pairZ_coprod_components e g₁ y'

/-! ## The transport to the `(x,v)`,`(y,v)`-coordinates -/

theorem pairZ'_toLinearMap (k : ℕ) :
    (pairZ' k).toLinearMap = ((splitE k).prodCongr (splitE k)).toLinearMap.comp
      (pairZ k).toLinearMap := by
  rw [pairZ', LinearEquiv.coe_trans, LinearEquiv.coe_prodCongr]

/-- **Transport of the crossing determinant to the block form**: replacing the two `E^{k+1}`-jets by
their `ℝ × E^k`-versions (through the splitting `splitE k`) does not change the determinant. -/
theorem det_pairZ'_coprod_eq {k : ℕ}
    (A B : EuclideanSpace ℝ (Fin (k + 1)) →ₗ[ℝ] Work.Drive.Whitney.Mdl k) :
    LinearMap.det ((pairZ' k).toLinearMap.comp (A.coprod B))
      = LinearMap.det ((pairZ k).toLinearMap.comp
          ((A.comp (splitE k).toLinearMap).coprod (B.comp (splitE k).toLinearMap))) := by
  set s := (splitE k).prodCongr (splitE k) with hs
  set Z := (pairZ k).toLinearMap.comp
      ((A.comp (splitE k).toLinearMap).coprod (B.comp (splitE k).toLinearMap)) with hZ
  have hZ' : (pairZ' k).toLinearMap = s.toLinearMap.comp (pairZ k).toLinearMap :=
    pairZ'_toLinearMap k
  have hAB : A.coprod B
      = ((A.comp (splitE k).toLinearMap).coprod (B.comp (splitE k).toLinearMap)).comp
          s.symm.toLinearMap := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    simp [hs, LinearMap.coprod_apply, LinearMap.prodMap_apply,
      LinearEquiv.coe_prodCongr]
  have hcomp : (pairZ' k).toLinearMap.comp (A.coprod B)
      = s.toLinearMap.comp (Z.comp s.symm.toLinearMap) := by
    rw [hZ', hAB, hZ]
    rfl
  rw [hcomp, LinearMap.det_conj]

/-! ## The positivity of the global-chart factor -/

/-- **The two `(pairEquiv ∘ dΘ ∘ pairZ'⁻¹)`-determinants have positive product**: they are conjugate
to `dΘ ξ ∘ Q` for a single linear isomorphism `Q`, so `det_fderiv_mul_pos` applies. -/
theorem det_pairEquiv_comp_pairZ'_mul_pos {k : ℕ}
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΘΦ : ∀ y, Θ (Φ y) = y) (hΦΘ : ∀ ξ, Φ (Θ ξ) = ξ) (ξ₁ ξ₂ : Work.Drive.Whitney.Mdl k) :
    0 < LinearMap.det ((Work.Projection.pairEquiv (k + 1)).toLinearMap.comp
            ((fderiv ℝ Θ ξ₁).toLinearMap.comp (pairZ' k).symm.toLinearMap)) *
        LinearMap.det ((Work.Projection.pairEquiv (k + 1)).toLinearMap.comp
            ((fderiv ℝ Θ ξ₂).toLinearMap.comp (pairZ' k).symm.toLinearMap)) := by
  have hQ := det_fderiv_mul_pos (k := k) Θ Φ
    ((Work.Projection.pairEquiv (k + 1)).trans (pairZ' k).symm) hΘ hΦ hΘΦ hΦΘ ξ₁ ξ₂
  have hL : ∀ ξ : Work.Drive.Whitney.Mdl k,
      LinearMap.det ((Work.Projection.pairEquiv (k + 1)).toLinearMap.comp
          ((fderiv ℝ Θ ξ).toLinearMap.comp (pairZ' k).symm.toLinearMap))
      = LinearMap.det ((((Work.Projection.pairEquiv (k + 1)).trans (pairZ' k).symm).toLinearMap).comp
          (fderiv ℝ Θ ξ).toLinearMap) := by
    intro ξ
    have hconj := LinearMap.det_conj
      ((((Work.Projection.pairEquiv (k + 1)).trans (pairZ' k).symm).toLinearMap).comp
        (fderiv ℝ Θ ξ).toLinearMap) (pairZ' k)
    rw [← hconj]
    congr 1
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.coe_trans]
    rw [LinearEquiv.apply_symm_apply]
  rw [hL ξ₁, hL ξ₂]
  exact hQ

/-! ## Chart-representation differentiability -/

/-- **The chart representation of a smooth map is differentiable** (general normed codomain). -/
theorem differentiableAt_comp_symm_of_isSmoothChart_general {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : M → F}
    (hg : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ F) ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} (hc : Work.Whitney.IsSmoothChart c)
    {p : M} (hp : p ∈ c.source) :
    DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => g (c.symm u)) (c p) := by
  have h1 : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ F) ((⊤ : ℕ∞) : WithTop ℕ∞) g (c.symm (c p)) := by
    rw [c.left_inv hp]
    exact hg.contMDiffAt
  have h2 : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm (c p) :=
    hc.2.contMDiffAt (c.open_target.mem_nhds (c.map_source hp))
  exact (((ContMDiffAt.comp (x := c p) h1 h2).contDiffAt).differentiableAt (by simp))

/-- **The first sheet lies in the plane `{y = 0, v = 0}`**: hence the `(y,v)`-part of its jet
vanishes. -/
theorem Yv_comp_fderiv_first {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → EuclideanSpace ℝ (Fin (2 * (k + 1)))}
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (hc : Work.Whitney.IsSmoothChart c)
    (hsh : ∀ x : M, x ∈ c.source → (Φ (f x)).2.1 = 0 ∧ (Φ (f x)).2.2.2 = 0)
    {x : M} (hx : x ∈ c.source) :
    ∀ w : PP k, Yv k ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
      Φ (f (c.symm u))) (c x)) ((splitE k) w)) = 0 := by
  set G : EuclideanSpace ℝ (Fin (k + 1)) → Work.Drive.Whitney.Mdl k :=
    fun u => Φ (f (c.symm u)) with hG
  have hGsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ ∘ f) :=
    hΦsm.contMDiff.comp hf
  have hGd : DifferentiableAt ℝ G (c x) :=
    differentiableAt_comp_symm_of_isSmoothChart_general hGsm hc hx
  have hYvG : (fun u => Yv k (G u)) =ᶠ[𝓝 (c x)] (fun _ => (0 : PP k)) := by
    filter_upwards [c.open_target.mem_nhds (c.map_source hx)] with u hu
    obtain ⟨h1, h2⟩ := hsh (c.symm u) (c.symm_mapsTo hu)
    simp only [hG]
    rw [Yv_apply, h1, h2]
    rfl
  have h0 : fderiv ℝ (fun u => Yv k (G u)) (c x) = 0 := by
    rw [hYvG.fderiv_eq]
    simp
  have hcomp : fderiv ℝ (fun u => Yv k (G u)) (c x)
      = (LinearMap.toContinuousLinearMap (Yv k)).comp (fderiv ℝ G (c x)) := by
    have hd : DifferentiableAt ℝ (fun z : Work.Drive.Whitney.Mdl k => Yv k z) (G (c x)) :=
      (LinearMap.toContinuousLinearMap (Yv k)).differentiableAt
    have h := fderiv_comp (x := c x) (f := G)
      (g := fun z : Work.Drive.Whitney.Mdl k => Yv k z) hd hGd
    have hfe : fderiv ℝ (fun z : Work.Drive.Whitney.Mdl k => Yv k z) (G (c x))
        = LinearMap.toContinuousLinearMap (Yv k) :=
      (LinearMap.toContinuousLinearMap (Yv k)).hasFDerivAt.fderiv
    rw [hfe] at h
    exact h
  have hzero : (LinearMap.toContinuousLinearMap (Yv k)).comp (fderiv ℝ G (c x)) = 0 := by
    rw [← hcomp, h0]
  intro w
  have hw := congrArg (fun (L : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] PP k) =>
    L ((splitE k) w)) hzero
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
    LinearMap.coe_toContinuousLinearMap'] using hw

/-- The continuous linear functional `ξ ↦ ξ.2.2.2` on the model space. -/
noncomputable def projV (k : ℕ) :
    Work.Drive.Whitney.Mdl k →ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
  (LinearMap.snd ℝ (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k))).comp
    ((LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))).comp
      (LinearMap.snd ℝ ℝ (ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)))))

@[simp] theorem projV_apply (k : ℕ) (ξ : Work.Drive.Whitney.Mdl k) :
    projV k ξ = ξ.2.2.2 := rfl

/-- **The second sheet is a graph over its `(x,v)`-coordinates**: the `v`-component of its jet is
the `v`-component of the identity. -/
theorem Yv_snd_comp_fderiv_second {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → EuclideanSpace ℝ (Fin (2 * (k + 1)))}
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (hc : Work.Whitney.IsSmoothChart c)
    (hsh : ∀ u : EuclideanSpace ℝ (Fin (k + 1)), u ∈ c.target →
      (Φ (f (c.symm u))).2.2.2 = ((splitE k).symm u).2)
    {x : M} (hx : x ∈ c.source) :
    ∀ w : PP k, (Yv k ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
      Φ (f (c.symm u))) (c x)) ((splitE k) w))).2 = w.2 := by
  set G : EuclideanSpace ℝ (Fin (k + 1)) → Work.Drive.Whitney.Mdl k :=
    fun u => Φ (f (c.symm u)) with hG
  have hGsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ ∘ f) :=
    hΦsm.contMDiff.comp hf
  have hGd : DifferentiableAt ℝ G (c x) :=
    differentiableAt_comp_symm_of_isSmoothChart_general hGsm hc hx
  have hv : (fun u => projV k (G u)) =ᶠ[𝓝 (c x)] (fun u => ((splitE k).symm u).2) := by
    filter_upwards [c.open_target.mem_nhds (c.map_source hx)] with u hu
    simpa only [projV_apply] using hsh u hu
  have hA : fderiv ℝ (fun u => projV k (G u)) (c x)
      = (LinearMap.toContinuousLinearMap (projV k)).comp (fderiv ℝ G (c x)) := by
    have hd : DifferentiableAt ℝ (fun z : Work.Drive.Whitney.Mdl k => projV k z) (G (c x)) :=
      (LinearMap.toContinuousLinearMap (projV k)).differentiableAt
    have h := fderiv_comp (x := c x) (f := G)
      (g := fun z : Work.Drive.Whitney.Mdl k => projV k z) hd hGd
    have hfe : fderiv ℝ (fun z : Work.Drive.Whitney.Mdl k => projV k z) (G (c x))
        = LinearMap.toContinuousLinearMap (projV k) :=
      (LinearMap.toContinuousLinearMap (projV k)).hasFDerivAt.fderiv
    rw [hfe] at h
    exact h
  have hB : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => ((splitE k).symm u).2) (c x)
      = LinearMap.toContinuousLinearMap
          ((LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin k))).comp
            (splitE k).symm.toLinearMap) := by
    have hfun : (fun u : EuclideanSpace ℝ (Fin (k + 1)) => ((splitE k).symm u).2)
        = ⇑(LinearMap.toContinuousLinearMap
            ((LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin k))).comp
              (splitE k).symm.toLinearMap)) := rfl
    rw [hfun]
    exact (LinearMap.toContinuousLinearMap
      ((LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin k))).comp
        (splitE k).symm.toLinearMap)).hasFDerivAt.fderiv
  have hkey : fderiv ℝ (fun u => projV k (G u)) (c x)
      = LinearMap.toContinuousLinearMap
          ((LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin k))).comp
            (splitE k).symm.toLinearMap) := hv.fderiv_eq.trans hB
  intro w
  have hw := congrArg (fun (L : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] EuclideanSpace ℝ (Fin k)) =>
    L ((splitE k) w)) hkey
  simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
    LinearMap.snd_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply] at hw
  have hthis : (Yv k ((fderiv ℝ G (c x)) ((splitE k) w))).2
      = (fderiv ℝ (fun u => projV k (G u)) (c x)) ((splitE k) w) := by
    rw [hA]
    simp only [ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
      Yv_apply, projV_apply]
  rw [hthis, hw]


/-! ## The chart is an immersion, so its representation of `f` is one -/

/-- **The manifold derivative of the inverse of a smooth chart is injective.** -/
theorem injective_mfderiv_symm_of_isSmoothChart {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} (hc : Work.Whitney.IsSmoothChart c)
    {p : M} (hp : p ∈ c.source) :
    Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c.symm (c p)) := by
  have hcsm : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c p :=
    hc.1.contMDiffAt (c.open_source.mem_nhds hp)
  have hsmm : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm (c p) :=
    hc.2.contMDiffAt (c.open_target.mem_nhds (c.map_source hp))
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have h1 : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c (c.symm (c p)) := by
    rw [c.left_inv hp]; exact hcsm.mdifferentiableAt hne
  have h2 : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c.symm (c p) :=
    hsmm.mdifferentiableAt hne
  have hcomp : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (c ∘ c.symm) (c p)
      = (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c (c.symm (c p))).comp
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c.symm (c p)) :=
    mfderiv_comp (f := c.symm) (x := c p) h1 h2
  rw [c.left_inv hp] at hcomp
  have heq : c ∘ c.symm =ᶠ[𝓝 (c p)] id := by
    filter_upwards [c.open_target.mem_nhds (c.map_source hp)] with z hz
    rw [Function.comp_apply, c.right_inv hz]
    rfl
  rw [heq.mfderiv_eq, mfderiv_id] at hcomp
  exact (ContinuousLinearMap.leftInverse_of_comp hcomp.symm).injective

/-- **The chart representation of an immersion is an immersion.** -/
theorem injective_fderiv_comp_symm_of_isSmoothChart {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → EuclideanSpace ℝ (Fin (2 * (k + 1)))}
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) f y))
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1)))}
    (hc : Work.Whitney.IsSmoothChart c) {p : M} (hp : p ∈ c.source) :
    Function.Injective (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
      f (c.symm u)) (c p)) := by
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hfd : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) f (c.symm (c p)) := by
    rw [c.left_inv hp]; exact hf.contMDiffAt.mdifferentiableAt hne
  have hcs : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) c.symm (c p) :=
    (hc.2.contMDiffAt (c.open_target.mem_nhds (c.map_source hp))).mdifferentiableAt hne
  have hcomp : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
        (f ∘ c.symm) (c p)
      = (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) f p).comp
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) c.symm (c p)) := by
    have h := mfderiv_comp (f := c.symm) (x := c p) hfd hcs
    rw [c.left_inv hp] at h
    exact h
  have hinj : Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
      (f ∘ c.symm) (c p)) := by
    rw [hcomp]
    exact (himm p).comp (injective_mfderiv_symm_of_isSmoothChart hc hp)
  have hfdeq : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => f (c.symm u)) (c p)
      = mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
          (fun u : EuclideanSpace ℝ (Fin (k + 1)) => f (c.symm u)) (c p) :=
    mfderiv_eq_fderiv.symm
  rwa [hfdeq]


/-! ## The factorisation of one crossing determinant -/

/-- **The crossing determinant factors as (global chart factor) × (first-sheet `(x,u)`-Jacobian) ×
(core derivative).** -/
theorem pairDet_factor_of_model {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → EuclideanSpace ℝ (Fin (2 * (k + 1)))}
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hΘΦ : ∀ y : EuclideanSpace ℝ (Fin (2 * (k + 1))), Θ (Φ y) = y)
    (c₁ c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (hc₁ : Work.Whitney.IsSmoothChart c₁) (hc₂ : Work.Whitney.IsSmoothChart c₂)
    {a b : M} (ha : a ∈ c₁.source) (hb : b ∈ c₂.source) (hfab : f a = f b)
    (hsh₁ : ∀ x : M, x ∈ c₁.source → (Φ (f x)).2.1 = 0 ∧ (Φ (f x)).2.2.2 = 0)
    (hsh₂ : ∀ u : EuclideanSpace ℝ (Fin (k + 1)), u ∈ c₂.target →
      (Φ (f (c₂.symm u))).2.2.2 = ((splitE k).symm u).2) :
    Work.Whitney.pairDet f c₁ c₂ a b
      = LinearMap.det ((Work.Projection.pairEquiv (k + 1)).toLinearMap.comp
            ((fderiv ℝ Θ (Φ (f a))).toLinearMap.comp (pairZ' k).symm.toLinearMap)) *
        (LinearMap.det ((Xu k).comp
            ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₁.symm u)))
              (c₁ a)).toLinearMap.comp (splitE k).toLinearMap)) *
          (((LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin k))).comp ((Yv k).comp
            ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u)))
              (c₂ b)).toLinearMap.comp (splitE k).toLinearMap))) ((1 : ℝ), 0))) := by
  set T := (fderiv ℝ Θ (Φ (f a))).toLinearMap with hT
  set A := (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₁.symm u)))
    (c₁ a)).toLinearMap with hAdef
  set B := (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u)))
    (c₂ b)).toLinearMap with hBdef
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hAchain : (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
      f (c₁.symm u)) (c₁ a)).toLinearMap = T.comp A := by
    have hΘd : DifferentiableAt ℝ Θ (Φ (f (c₁.symm (c₁ a)))) :=
      (hΘsm.differentiable hne).differentiableAt
    have hGd : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
        Φ (f (c₁.symm u))) (c₁ a) :=
      differentiableAt_comp_symm_of_isSmoothChart_general (hΦsm.contMDiff.comp hf) hc₁ ha
    have hcomp := fderiv_comp (x := c₁ a)
      (f := fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₁.symm u)))
      (g := Θ) hΘd hGd
    have hfun : (fun u : EuclideanSpace ℝ (Fin (k + 1)) => f (c₁.symm u))
        = Θ ∘ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₁.symm u))) := by
      funext u
      exact (hΘΦ _).symm
    rw [hfun, hcomp, c₁.left_inv ha]
    rfl
  have hBchain : (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
      f (c₂.symm u)) (c₂ b)).toLinearMap = T.comp B := by
    have hΘd : DifferentiableAt ℝ Θ (Φ (f (c₂.symm (c₂ b)))) :=
      (hΘsm.differentiable hne).differentiableAt
    have hGd : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
        Φ (f (c₂.symm u))) (c₂ b) :=
      differentiableAt_comp_symm_of_isSmoothChart_general (hΦsm.contMDiff.comp hf) hc₂ hb
    have hcomp := fderiv_comp (x := c₂ b)
      (f := fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u)))
      (g := Θ) hΘd hGd
    have hfun : (fun u : EuclideanSpace ℝ (Fin (k + 1)) => f (c₂.symm u))
        = Θ ∘ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u))) := by
      funext u
      exact (hΘΦ _).symm
    rw [hfun, hcomp, c₂.left_inv hb, ← hfab]
    rfl
  rw [pairDet_model f T c₁ c₂ a b A B hAchain hBchain,
    det_pairEquiv_transport T A B, det_pairZ'_coprod_eq A B]
  rw [det_pairZ_coprod_of_shape (A.comp (splitE k).toLinearMap)
    (B.comp (splitE k).toLinearMap)
    (fun w => Yv_comp_fderiv_first hf Φ hΦsm c₁ hc₁ hsh₁ ha w)
    (fun w => Yv_snd_comp_fderiv_second hf Φ hΦsm c₂ hc₂ hsh₂ hb w)]


/-! ## Sign coherence of the first sheet's `(x,u)`-Jacobian along the arc -/

/-- **The `(x,u)`-Jacobian determinant of the first sheet is continuous along the arc.** -/
theorem continuous_det_firstJet {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → EuclideanSpace ℝ (Fin (2 * (k + 1)))}
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (hc : Work.Whitney.IsSmoothChart c)
    {γ : ℝ → M} (hγ : Continuous γ) (hsub : γ '' Set.Icc (0 : ℝ) 1 ⊆ c.source) :
    ContinuousOn (fun t : ℝ => LinearMap.det
      ((Xu k).comp ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
        Φ (f (c.symm u))) (c (γ t))).toLinearMap.comp (splitE k).toLinearMap)))
      (Set.Icc (0 : ℝ) 1) := by
  -- the chart expression of the first sheet is `C^∞` on `c.target`
  have hGcd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c.symm u))) c.target := by
    have h1 : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Φ ∘ f) Set.univ :=
      ContMDiffOn.comp (hΦsm.contMDiff.contMDiffOn (s := Set.univ))
        (hf.contMDiffOn (s := Set.univ)) (fun x _ => trivial)
    have h2 : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c.symm u))) c.target :=
      ContMDiffOn.comp (f := c.symm) (g := Φ ∘ f) (s := c.target) (t := Set.univ)
        h1 hc.2 (fun u _ => trivial)
    exact h2.contDiffOn
  have hfderiv : ContinuousOn (fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
      fderiv ℝ (fun w : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c.symm w))) u) c.target :=
    hGcd.continuousOn_fderiv_of_isOpen c.open_target (by simp)
  -- the curve `t ↦ c (γ t)` lies in `c.target`
  have hcurve : ContinuousOn (fun t : ℝ => c (γ t)) (Set.Icc (0 : ℝ) 1) :=
    c.continuousOn.comp hγ.continuousOn (fun t ht => hsub ⟨t, ht, rfl⟩)
  have hmaps : Set.MapsTo (fun t : ℝ => c (γ t)) (Set.Icc (0 : ℝ) 1) c.target :=
    fun t ht => c.map_source (hsub ⟨t, ht, rfl⟩)
  have hfdc : ContinuousOn (fun t : ℝ =>
      fderiv ℝ (fun w : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c.symm w))) (c (γ t)))
      (Set.Icc (0 : ℝ) 1) :=
    hfderiv.comp hcurve hmaps
  -- the linear map `L ↦ (Xu k) ∘ (L ∘ σ)`
  let T : (EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] Work.Drive.Whitney.Mdl k) →ₗ[ℝ]
      (PP k →L[ℝ] PP k) :=
    { toFun := fun L => (LinearMap.toContinuousLinearMap (Xu k)).comp
        (L.comp (LinearMap.toContinuousLinearMap (splitE k).toLinearMap))
      map_add' := by
        intro L M
        rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
      map_smul' := by
        intro a L
        rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, RingHom.id_apply] }
  have hTc : Continuous ⇑T := LinearMap.continuous_of_finiteDimensional T
  have hd : Continuous fun L : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] Work.Drive.Whitney.Mdl k =>
      (T L).det := ContinuousLinearMap.continuous_det.comp hTc
  have hd' : ContinuousOn (fun t : ℝ => (T (fderiv ℝ
      (fun w : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c.symm w))) (c (γ t)))).det)
      (Set.Icc (0 : ℝ) 1) := hd.comp_continuousOn hfdc
  have hTval : ∀ L : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] Work.Drive.Whitney.Mdl k,
      T L = (LinearMap.toContinuousLinearMap (Xu k)).comp
        (L.comp (LinearMap.toContinuousLinearMap (splitE k).toLinearMap)) := fun L => rfl
  have hdet : ∀ L : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] Work.Drive.Whitney.Mdl k,
      (T L).det = LinearMap.det ((Xu k).comp
        (L.toLinearMap.comp (splitE k).toLinearMap)) := by
    intro L
    rw [hTval L]
    rfl
  refine hd'.congr ?_
  intro t ht
  exact (hdet _).symm



/-- A linear map into the model space whose `(y,v)`-part vanishes lands in the plane of the first
sheet, hence is `incLM` applied to its `(x,u)`-part. -/
theorem eq_incLM_comp_of_Yv_comp_eq_zero {k : ℕ}
    {L : PP k →ₗ[ℝ] Work.Drive.Whitney.Mdl k} (hYv : (Yv k).comp L = 0) :
    L = (incLM k).comp ((Xu k).comp L) := by
  have h1 : (pairZ k).toLinearMap.comp L
      = ((LinearMap.id : PP k →ₗ[ℝ] PP k).prod (0 : PP k →ₗ[ℝ] PP k)).comp
          ((Xu k).comp L) := by
    rw [pairZ_eq_prod k, LinearMap.prod_comp, hYv]
    apply LinearMap.ext
    intro w
    rfl
  have h2 : (pairZ k).toLinearMap.comp ((incLM k).comp ((Xu k).comp L))
      = ((LinearMap.id : PP k →ₗ[ℝ] PP k).prod (0 : PP k →ₗ[ℝ] PP k)).comp
          ((Xu k).comp L) := by
    rw [← LinearMap.comp_assoc, pairZ_comp_incLM k, LinearMap.prod_comp]
  have h3 : (pairZ k).toLinearMap.comp L
      = (pairZ k).toLinearMap.comp ((incLM k).comp ((Xu k).comp L)) := h1.trans h2.symm
  apply LinearMap.ext
  intro w
  exact (pairZ k).injective (by simpa using congrArg (fun L => L w) h3)

/-- **Non-vanishing of the first sheet's `(x,u)`-Jacobian determinant** — the immersion hypothesis
makes every jet along the first sheet injective, and the `(x,u)`-part of an injective jet into the
plane is invertible. -/
theorem det_firstJet_ne_zero {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → EuclideanSpace ℝ (Fin (2 * (k + 1)))}
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) f y))
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hΘΦ : ∀ y : EuclideanSpace ℝ (Fin (2 * (k + 1))), Θ (Φ y) = y)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (hc : Work.Whitney.IsSmoothChart c)
    (hsh : ∀ x : M, x ∈ c.source → (Φ (f x)).2.1 = 0 ∧ (Φ (f x)).2.2.2 = 0)
    {x : M} (hx : x ∈ c.source) :
    LinearMap.det ((Xu k).comp ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
      Φ (f (c.symm u))) (c x)).toLinearMap.comp (splitE k).toLinearMap)) ≠ 0 := by
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hΦd : Differentiable ℝ Φ := hΦsm.differentiable hne
  have hΘd : Differentiable ℝ Θ := hΘsm.differentiable hne
  have hinjΦ : ∀ y : EuclideanSpace ℝ (Fin (2 * (k + 1))),
      Function.Injective (fderiv ℝ Φ y) := by
    intro y
    have h := fderiv_comp (x := y) (f := Φ) (g := Θ) (hΘd (Φ y)) (hΦd y)
    rw [show (Θ ∘ Φ) = id from funext hΘΦ, fderiv_id] at h
    exact (ContinuousLinearMap.leftInverse_of_comp h.symm).injective
  have hfd1 : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => f (c.symm u)) (c x) :=
    Work.Whitney.differentiableAt_comp_symm_of_isSmoothChart (n := k + 1) hf hc hx
  have hL : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c.symm u))) (c x)
      = (fderiv ℝ Φ (f x)).comp
        (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => f (c.symm u)) (c x)) := by
    have hΦd' : DifferentiableAt ℝ Φ (f (c.symm (c x))) := hΦd.differentiableAt
    have h := fderiv_comp (x := c x)
      (f := fun u : EuclideanSpace ℝ (Fin (k + 1)) => f (c.symm u)) (g := Φ) hΦd' hfd1
    rw [c.left_inv hx] at h
    exact h
  have hLinj : Function.Injective
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c.symm u))) (c x)) := by
    rw [hL]
    exact (hinjΦ (f x)).comp
      (injective_fderiv_comp_symm_of_isSmoothChart hf himm hc hx)
  have hYv : (Yv k).comp
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c.symm u))) (c x)).toLinearMap
      = 0 := by
    apply LinearMap.ext
    intro w
    obtain ⟨w', rfl⟩ := (splitE k).surjective w
    simpa using Yv_comp_fderiv_first hf Φ hΦsm c hc hsh hx w'
  set L := (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c.symm u))) (c x)).toLinearMap
    with hLdef
  set A' := L.comp (splitE k).toLinearMap with hA'def
  have hinjL : Function.Injective L := hLinj
  have hinjA' : Function.Injective A' := by
    rw [hA'def]
    exact hinjL.comp (splitE k).injective
  have hinc : A' = (incLM k).comp ((Xu k).comp A') := by
    rw [hA'def, ← LinearMap.comp_assoc]
    apply eq_incLM_comp_of_Yv_comp_eq_zero
    rw [← LinearMap.comp_assoc, hYv, LinearMap.zero_comp]
  have heinj : Function.Injective ((Xu k).comp A') := by
    intro u v huv
    apply hinjA'
    rw [hinc]
    simp only [LinearMap.comp_apply, huv]
  intro h0
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h0) (LinearMap.ker_eq_bot.mpr heinj)


/-- **Sign coherence of the first sheet's `(x,u)`-Jacobian along the arc.**  The determinant is
continuous and never zero on `[0,1]`, so it has the same sign at the two endpoints. -/
theorem det_firstJet_mul_pos {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → EuclideanSpace ℝ (Fin (2 * (k + 1)))}
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) f y))
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hΘΦ : ∀ y : EuclideanSpace ℝ (Fin (2 * (k + 1))), Θ (Φ y) = y)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (hc : Work.Whitney.IsSmoothChart c)
    (hsh : ∀ x : M, x ∈ c.source → (Φ (f x)).2.1 = 0 ∧ (Φ (f x)).2.2.2 = 0)
    {γ : ℝ → M} (hγ : Continuous γ) (hsub : γ '' Set.Icc (0 : ℝ) 1 ⊆ c.source) :
    0 < LinearMap.det ((Xu k).comp ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
          Φ (f (c.symm u))) (c (γ 0))).toLinearMap.comp (splitE k).toLinearMap)) *
        LinearMap.det ((Xu k).comp ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
          Φ (f (c.symm u))) (c (γ 1))).toLinearMap.comp (splitE k).toLinearMap)) := by
  let φ : ℝ → ℝ := fun t => LinearMap.det ((Xu k).comp
    ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c.symm u)))
      (c (γ t))).toLinearMap.comp (splitE k).toLinearMap))
  have hφ0 : φ 0 = LinearMap.det ((Xu k).comp
      ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c.symm u)))
        (c (γ 0))).toLinearMap.comp (splitE k).toLinearMap)) := rfl
  have hφ1 : φ 1 = LinearMap.det ((Xu k).comp
      ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c.symm u)))
        (c (γ 1))).toLinearMap.comp (splitE k).toLinearMap)) := rfl
  have hcont : ContinuousOn φ (Set.Icc (0 : ℝ) 1) :=
    continuous_det_firstJet hf Φ hΦsm c hc hγ hsub
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, φ t ≠ 0 := fun t ht =>
    det_firstJet_ne_zero hf himm Φ hΦsm Θ hΘsm hΘΦ c hc hsh (hsub ⟨t, ht, rfl⟩)
  have hmain : 0 < φ 0 * φ 1 := by
    by_contra hcon
    have hcon' : φ 0 * φ 1 ≤ 0 := not_lt.mp hcon
    have h0 : φ 0 ≠ 0 := hne 0 ⟨le_refl _, by norm_num⟩
    have h1 : φ 1 ≠ 0 := hne 1 ⟨by norm_num, le_refl _⟩
    have hmem0 : (φ 0 : ℝ) ∈ φ '' Set.Icc (0 : ℝ) 1 := ⟨0, ⟨le_refl _, by norm_num⟩, rfl⟩
    have hmem1 : (φ 1 : ℝ) ∈ φ '' Set.Icc (0 : ℝ) 1 := ⟨1, ⟨by norm_num, le_refl _⟩, rfl⟩
    have hpc : IsPreconnected (φ '' Set.Icc (0 : ℝ) 1) :=
      isPreconnected_Icc.image φ hcont
    have hord := hpc.ordConnected
    rw [mul_nonpos_iff] at hcon'
    rcases hcon' with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have hmem : (0 : ℝ) ∈ Set.Icc (φ 1) (φ 0) := ⟨hb, ha⟩
      obtain ⟨t, ht, htx⟩ : (0 : ℝ) ∈ φ '' Set.Icc (0 : ℝ) 1 :=
        hord.out hmem1 hmem0 hmem
      exact hne t ht htx
    · have hmem : (0 : ℝ) ∈ Set.Icc (φ 0) (φ 1) := ⟨ha, hb⟩
      obtain ⟨t, ht, htx⟩ : (0 : ℝ) ∈ φ '' Set.Icc (0 : ℝ) 1 :=
        hord.out hmem0 hmem1 hmem
      exact hne t ht htx
  rw [hφ0, hφ1] at hmain
  exact hmain


/-! ## The pinned chart and the derivative of the core height -/

/-- The `(y)`-projection of the model space. -/
noncomputable def projY (k : ℕ) : Work.Drive.Whitney.Mdl k →ₗ[ℝ] ℝ :=
  (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))).comp
    (LinearMap.snd ℝ ℝ (ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))))

@[simp] theorem projY_apply (k : ℕ) (ξ : Work.Drive.Whitney.Mdl k) :
    projY k ξ = ξ.2.1 := rfl

/-- **The pinning identifies the chart coordinate.**  If `Φ (f x) = (s,0,0,0)` and the second
sheet of `f` in the chart `c` is the graph of its `(x,v)`-coordinates, then `c x = splitE (s,0)`. -/
theorem chart_eq_splitE_of_phi_pin {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → EuclideanSpace ℝ (Fin (2 * (k + 1)))}
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    {x : M} (hx : x ∈ c.source)
    (hsh : ∀ y : M, y ∈ c.source →
      Φ (f y) = (((splitE k).symm (c y)).1, (Φ (f y)).2.1,
        (Φ (f y)).2.2.1, ((splitE k).symm (c y)).2))
    {s : ℝ} (hval : Φ (f x) = ((s : ℝ), 0, 0, 0)) :
    c x = (splitE k) ((s : ℝ), (0 : EuclideanSpace ℝ (Fin k))) := by
  have h1 := hsh x hx
  have hx1 : ((splitE k).symm (c x)).1 = s := by
    have h := congrArg (fun ξ : Work.Drive.Whitney.Mdl k => ξ.1) h1
    rw [hval] at h
    simpa using h.symm
  have hx2 : ((splitE k).symm (c x)).2 = 0 := by
    have h := congrArg (fun ξ : Work.Drive.Whitney.Mdl k => ξ.2.2.2) h1
    rw [hval] at h
    simpa using h.symm
  have hw : (splitE k).symm (c x) = ((s : ℝ), (0 : EuclideanSpace ℝ (Fin k))) :=
    Prod.ext hx1 hx2
  rw [← hw, LinearEquiv.apply_symm_apply]

/-- **The derivative of the core height along the `x`-line is the `y`-component of the second
sheet's jet.** -/
theorem hasDerivAt_core_of_pinned {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → EuclideanSpace ℝ (Fin (2 * (k + 1)))}
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (hc₂ : Work.Whitney.IsSmoothChart c₂)
    {x : M} (hx : x ∈ c₂.source)
    (hsh₂ : ∀ y : M, y ∈ c₂.source →
      Φ (f y) = (((splitE k).symm (c₂ y)).1, (Φ (f y)).2.1,
        (Φ (f y)).2.2.1, ((splitE k).symm (c₂ y)).2))
    {s : ℝ} (hval : Φ (f x) = ((s : ℝ), 0, 0, 0)) :
    HasDerivAt (fun t : ℝ =>
        (Φ (f (c₂.symm ((splitE k) (t, (0 : EuclideanSpace ℝ (Fin k))))))).2.1)
      (((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u)))
        (c₂ x)) ((splitE k) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))))).2.1) s := by
  have hcx : c₂ x = (splitE k) ((s : ℝ), (0 : EuclideanSpace ℝ (Fin k))) :=
    chart_eq_splitE_of_phi_pin Φ c₂ hx hsh₂ hval
  have hGd : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u)))
      ((splitE k) ((s : ℝ), (0 : EuclideanSpace ℝ (Fin k)))) := by
    rw [← hcx]
    exact differentiableAt_comp_symm_of_isSmoothChart_general (hΦsm.contMDiff.comp hf) hc₂ hx
  have hG : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u)))
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u)))
        ((splitE k) ((s : ℝ), (0 : EuclideanSpace ℝ (Fin k)))))
      ((splitE k) ((s : ℝ), (0 : EuclideanSpace ℝ (Fin k)))) := hGd.hasFDerivAt
  have hder : HasDerivAt (fun t : ℝ => (splitE k) (t, (0 : EuclideanSpace ℝ (Fin k))))
      ((splitE k) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k)))) s := by
    have hid : HasDerivAt (fun t : ℝ => t) (1 : ℝ) s := hasDerivAt_id s
    have h1 : HasDerivAt (fun t : ℝ => ((t, (0 : EuclideanSpace ℝ (Fin k))) : PP k))
        ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) s :=
      HasFDerivAt.comp_hasDerivAt s
        (ContinuousLinearMap.inl ℝ ℝ (EuclideanSpace ℝ (Fin k))).hasFDerivAt hid
    exact HasFDerivAt.comp_hasDerivAt s
      (LinearMap.toContinuousLinearMap (splitE k).toLinearMap).hasFDerivAt h1
  have hstep_c : HasDerivAt ((fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u))) ∘
      (fun t : ℝ => (splitE k) (t, (0 : EuclideanSpace ℝ (Fin k)))))
      ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u)))
        ((splitE k) ((s : ℝ), (0 : EuclideanSpace ℝ (Fin k)))))
        ((splitE k) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))))) s :=
    HasFDerivAt.comp_hasDerivAt s hG hder
  have hstep : HasDerivAt (fun t : ℝ =>
      Φ (f (c₂.symm ((splitE k) (t, (0 : EuclideanSpace ℝ (Fin k)))))))
      ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u)))
        ((splitE k) ((s : ℝ), (0 : EuclideanSpace ℝ (Fin k)))))
        ((splitE k) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))))) s := hstep_c
  have hproj_c : HasDerivAt
      ((LinearMap.toContinuousLinearMap (projY k)) ∘
        ((fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u))) ∘
          (fun t : ℝ => (splitE k) (t, (0 : EuclideanSpace ℝ (Fin k))))))
      (((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u)))
        ((splitE k) ((s : ℝ), (0 : EuclideanSpace ℝ (Fin k)))))
        ((splitE k) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))))).2.1) s :=
    HasFDerivAt.comp_hasDerivAt s
      (LinearMap.toContinuousLinearMap (projY k)).hasFDerivAt hstep_c
  have hproj : HasDerivAt (fun t : ℝ =>
      (Φ (f (c₂.symm ((splitE k) (t, (0 : EuclideanSpace ℝ (Fin k))))))).2.1)
      (((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u)))
        ((splitE k) ((s : ℝ), (0 : EuclideanSpace ℝ (Fin k)))))
        ((splitE k) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))))).2.1) s := hproj_c
  rw [← hcx] at hproj
  exact hproj


/-! ## The target theorem -/

theorem signOfCoreDerivative_of_immersion {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → EuclideanSpace ℝ (Fin (2 * (k + 1)))}
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) f y))
    {γ₁ γ₂ : ℝ → M} {p₁ p₂ q₁ q₂ : M}
    (hγ₁ : Continuous γ₁) (hγ₂ : Continuous γ₂)
    (hp₁ : γ₁ 0 = p₁) (hq₁ : γ₁ 1 = q₁) (hp₂ : γ₂ 0 = p₂) (hq₂ : γ₂ 1 = q₂)
    (hsign : Work.Whitney.OppositeType f γ₁ γ₂ p₁ p₂ q₁ q₂)
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hΘΦ : ∀ y : EuclideanSpace ℝ (Fin (2 * (k + 1))), Θ (Φ y) = y)
    (hΦΘ : ∀ ξ : Work.Drive.Whitney.Mdl k, Φ (Θ ξ) = ξ)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hpinP : Φ (f p₁) = ((-1 : ℝ), 0, 0, 0))
    (hpinQ : Φ (f q₁) = ((1 : ℝ), 0, 0, 0))
    (c₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (hc₁ : Work.Whitney.IsSmoothChart c₁)
    (hsrc₁ : γ₁ '' Set.Icc (0 : ℝ) 1 ⊆ c₁.source)
    (hp₁₁ : p₁ ∈ c₁.source) (hq₁₁ : q₁ ∈ c₁.source)
    (hsh₁ : ∀ x : M, x ∈ c₁.source → (Φ (f x)).2.1 = 0 ∧ (Φ (f x)).2.2.2 = 0)
    (c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (hc₂ : Work.Whitney.IsSmoothChart c₂)
    (hsrc₂ : γ₂ '' Set.Icc (0 : ℝ) 1 ⊆ c₂.source)
    (hp₂₂ : p₂ ∈ c₂.source) (hq₂₂ : q₂ ∈ c₂.source)
    (hsh₂ : ∀ x : M, x ∈ c₂.source →
      Φ (f x) = (((Work.Drive.PushDisc.splitE k).symm (c₂ x)).1, (Φ (f x)).2.1,
        (Φ (f x)).2.2.1, ((Work.Drive.PushDisc.splitE k).symm (c₂ x)).2)) :
    ∃ a b : ℝ,
      HasDerivAt (fun x : ℝ =>
        (Φ (f (c₂.symm ((Work.Drive.PushDisc.splitE k) (x, 0))))).2.1) a (-1) ∧
      HasDerivAt (fun x : ℝ =>
        (Φ (f (c₂.symm ((Work.Drive.PushDisc.splitE k) (x, 0))))).2.1) b 1 ∧ a * b < 0 := by
  obtain ⟨-, -, -, -, c₁', c₂', c₃', c₄', hm₁, hm₂, hm₃, hm₄, haC, hbC, hprod0⟩ := hsign
  have hchain₁ : Work.Whitney.IsArcChain γ₁ c₁ c₁ :=
    Work.Whitney.isArcChain_const (hsrc₁ ⟨0, ⟨le_refl _, zero_le_one⟩, rfl⟩)
      (hsrc₁ ⟨1, ⟨zero_le_one, le_refl _⟩, rfl⟩) hc₁ hsrc₁
  have hchain₂ : Work.Whitney.IsArcChain γ₂ c₂ c₂ :=
    Work.Whitney.isArcChain_const (hsrc₂ ⟨0, ⟨le_refl _, zero_le_one⟩, rfl⟩)
      (hsrc₂ ⟨1, ⟨zero_le_one, le_refl _⟩, rfl⟩) hc₂ hsrc₂
  have hprod : Work.Whitney.pairDet f c₁ c₂ p₁ p₂ * Work.Whitney.pairDet f c₁ c₂ q₁ q₂ < 0 :=
    ((Work.Whitney.pairDet_mul_sign_iff_of_isArcChain hf hγ₁ hγ₂ hp₁ hq₁ hp₂ hq₂
      hp₁₁ hp₂₂ hq₁₁ hq₂₂ hm₁ hm₂ hm₃ hm₄ hchain₁ hchain₂ haC hbC).2).mpr hprod0
  have hsh₂' : ∀ u : EuclideanSpace ℝ (Fin (k + 1)), u ∈ c₂.target →
      (Φ (f (c₂.symm u))).2.2.2 = ((splitE k).symm u).2 := by
    intro u hu
    have hx : c₂.symm u ∈ c₂.source := c₂.symm_mapsTo hu
    have hcu : c₂ (c₂.symm u) = u := c₂.right_inv hu
    have h := congrArg (fun ξ : Work.Drive.Whitney.Mdl k => ξ.2.2.2) (hsh₂ (c₂.symm u) hx)
    simpa [hcu] using h
  have hvalP : Φ (f p₂) = ((-1 : ℝ), 0, 0, 0) := by rw [← hfp, hpinP]
  have hvalQ : Φ (f q₂) = ((1 : ℝ), 0, 0, 0) := by rw [← hfq, hpinQ]
  have hfacP := pairDet_factor_of_model hf Φ Θ hΦsm hΘsm hΘΦ c₁ c₂ hc₁ hc₂
    hp₁₁ hp₂₂ hfp hsh₁ hsh₂'
  have hfacQ := pairDet_factor_of_model hf Φ Θ hΦsm hΘsm hΘΦ c₁ c₂ hc₁ hc₂
    hq₁₁ hq₂₂ hfq hsh₁ hsh₂'
  have hK := det_pairEquiv_comp_pairZ'_mul_pos Θ Φ hΘsm hΦsm hΘΦ hΦΘ (Φ (f p₁)) (Φ (f q₁))
  have hE := det_firstJet_mul_pos hf himm Φ hΦsm Θ hΘsm hΘΦ c₁ hc₁ hsh₁ hγ₁ hsrc₁
  rw [hp₁, hq₁] at hE
  have haP := hasDerivAt_core_of_pinned hf Φ hΦsm c₂ hc₂ hp₂₂ hsh₂ hvalP
  have hbQ := hasDerivAt_core_of_pinned hf Φ hΦsm c₂ hc₂ hq₂₂ hsh₂ hvalQ
  set a : ℝ := ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u)))
    (c₂ p₂)) ((splitE k) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))))).2.1 with ha_def
  set b : ℝ := ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u)))
    (c₂ q₂)) ((splitE k) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))))).2.1 with hb_def
  have haP' : HasDerivAt (fun x : ℝ =>
      (Φ (f (c₂.symm ((splitE k) (x, (0 : EuclideanSpace ℝ (Fin k))))))).2.1) a (-1) := haP
  have hbQ' : HasDerivAt (fun x : ℝ =>
      (Φ (f (c₂.symm ((splitE k) (x, (0 : EuclideanSpace ℝ (Fin k))))))).2.1) b 1 := hbQ
  refine ⟨a, b, haP', hbQ', ?_⟩
  set Kp : ℝ := LinearMap.det ((Work.Projection.pairEquiv (k + 1)).toLinearMap.comp
    ((fderiv ℝ Θ (Φ (f p₁))).toLinearMap.comp (pairZ' k).symm.toLinearMap)) with hKp
  set Kq : ℝ := LinearMap.det ((Work.Projection.pairEquiv (k + 1)).toLinearMap.comp
    ((fderiv ℝ Θ (Φ (f q₁))).toLinearMap.comp (pairZ' k).symm.toLinearMap)) with hKq
  set ep : ℝ := LinearMap.det ((Xu k).comp
    ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₁.symm u)))
      (c₁ p₁)).toLinearMap.comp (splitE k).toLinearMap)) with hep
  set eqd : ℝ := LinearMap.det ((Xu k).comp
    ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₁.symm u)))
      (c₁ q₁)).toLinearMap.comp (splitE k).toLinearMap)) with heqd
  have hyP : ((LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin k))).comp ((Yv k).comp
      ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u)))
        (c₂ p₂)).toLinearMap.comp (splitE k).toLinearMap)))
      ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) = a := rfl
  have hyQ : ((LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin k))).comp ((Yv k).comp
      ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u)))
        (c₂ q₂)).toLinearMap.comp (splitE k).toLinearMap)))
      ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) = b := rfl
  have hKpos : 0 < Kp * Kq := by
    rw [hKp, hKq]
    exact hK
  have hEpos : 0 < ep * eqd := by
    rw [hep, heqd]
    exact hE
  have hprod' : Work.Whitney.pairDet f c₁ c₂ p₁ p₂ * Work.Whitney.pairDet f c₁ c₂ q₁ q₂
      = ((Kp * Kq) * (ep * eqd)) * (a * b) := by
    rw [hfacP, hfacQ, hyP, hyQ]
    simp only [hKp, hKq, hep, heqd]
    ring
  rw [hprod'] at hprod
  have hmain : 0 < (Kp * Kq) * (ep * eqd) := mul_pos hKpos hEpos
  by_contra hcon
  push_neg at hcon
  nlinarith [hmain, hprod, hcon]

end Work.Drive.PushDisc
