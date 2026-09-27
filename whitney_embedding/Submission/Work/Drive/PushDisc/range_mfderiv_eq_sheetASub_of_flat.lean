import Mathlib
import Submission.Work.Drive.Whitney.range_mfderiv_le_of_mem_open
import Submission.Work.Drive.Whitney.foldCollar
import Submission.Work.Drive.PushDisc.exists_chart_twoPlaneFraming
import Submission.Work.Drive.PushDisc.milnorLens
import Submission.Work.Drive.PushDisc.sheetModel
import Submission.Work.Compat.MFDerivCongrV433

/-!
# The tangent plane of the flat first sheet

If a smooth immersion `g = Φ ∘ f` of a `(k+1)`-manifold takes its values in the model sheet
`sheetA = {ξ | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0}` on an open set `U`, then at every point of `U` its
tangent plane is *exactly* the sheet plane `sheetASub k`: containment is the "tangent space of a
linear subspace is the subspace" fact, and equality follows from `finrank (sheetASub k) = k + 1`
together with injectivity of the derivative (the immersion assumption).
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff
open Filter Topology Set Module

set_option linter.style.haveILetI false

/-- **The derivative of a map which takes its values in a linear subspace lands in it.**

Generalisation of `Work.Drive.Whitney.range_mfderiv_le_of_mem_open` to an arbitrary
finite-dimensional real normed target `F`.  If `g : M → F` is `C^∞` on the smooth
`n`-manifold `M` and takes its values in the submodule `K` on an open set `U ∋ x`, then
`range (mfderiv g x) ≤ K`. -/
theorem range_mfderiv_le_of_mem_open_gen {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (g : M → F) (hg : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ F) ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (K : Submodule ℝ F) (U : Set M) (hUo : IsOpen U) (x : M) (hxU : x ∈ U)
    (hU : ∀ y ∈ U, g y ∈ K) :
    LinearMap.range ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ F) g x).toLinearMap) ≤ K := by
  classical
  haveI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) 1 M :=
    IsManifold.of_le (m := 1) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)
  let c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) x
  have hxs : x ∈ c.source := mem_chart_source _ _
  have ha : c x ∈ c.target := c.map_source hxs
  let G : EuclideanSpace ℝ (Fin n) → F := fun y => g (c.symm y)
  -- `K` is closed, being a finite-dimensional subspace of a normed space
  have hKc : IsClosed (K : Set F) := Submodule.closed_of_finiteDimensional K
  have hcs : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (c.symm : _ → M) (c x) :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas _ _) ha
  have hgmd : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ F) g x :=
    (hg x).mdifferentiableAt (by simp)
  have hGmd : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ F) G (c x) :=
    MDifferentiableAt.comp_of_eq (c x) hgmd hcs (c.left_inv hxs)
  have hGderiv : HasFDerivAt G (fderiv ℝ G (c x)) (c x) := hGmd.differentiableAt.hasFDerivAt
  -- the chart representation lands in `K` near `c x`
  have hmem : ∀ᶠ y in 𝓝 (c x), G y ∈ K := by
    have hcont : ContinuousAt (c.symm : EuclideanSpace ℝ (Fin n) → M) (c x) :=
      (c.symm).continuousAt (by rw [OpenPartialHomeomorph.symm_source]; exact ha)
    have htend : Tendsto (c.symm : EuclideanSpace ℝ (Fin n) → M) (𝓝 (c x)) (𝓝 x) := by
      have h := hcont.tendsto
      rwa [c.left_inv hxs] at h
    have hU' : ∀ᶠ y in 𝓝 (c x), c.symm y ∈ U := htend.eventually (hUo.mem_nhds hxU)
    filter_upwards [hU'] with y hy
    exact hU _ hy
  -- `mfderiv g x` is the chart derivative composed with the derivative of the chart
  have hcmd : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (c : M → _) x :=
    mdifferentiableAt_atlas (chart_mem_atlas _ _) hxs
  have heq : g =ᶠ[𝓝 x] G ∘ c := by
    filter_upwards [c.open_source.mem_nhds hxs] with y hy
    show g y = g (c.symm (c y))
    rw [c.left_inv hy]
  have hcomp := mfderiv_comp x hGmd hcmd
  have hdecomp : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ F) g x
      = (fderiv ℝ G (c x)).comp (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c x) := by
    have h1 : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ F) g x
        = mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ F) (G ∘ c) x :=
      Filter.EventuallyEq.mfderiv_eq_v433 heq
    rw [h1, hcomp, mfderiv_eq_fderiv]
    rfl
  -- assemble
  change (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ F) g x).range ≤ K
  refine le_trans ?_ (Work.Drive.Whitney.range_le_of_eventually_mem_submodule K hKc hGderiv hmem)
  rw [hdecomp]
  exact LinearMap.range_comp_le_range _ _

theorem range_mfderiv_eq_sheetASub_of_flat {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΦimm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => Φ (f y)) y))
    (γ : ℝ → M) (hγ : Continuous γ)
    (U : Set M) (hUo : IsOpen U) (hU : γ '' Set.Icc (0 : ℝ) 1 ⊆ U)
    (hflat : ∀ x ∈ U, Φ (f x) ∈ Work.Drive.Whitney.sheetA) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => Φ (f y)) (γ t)).range
        = Work.Drive.PushDisc.sheetASub k := by
  intro t ht
  have hγtU : γ t ∈ U := hU ⟨t, ht, rfl⟩
  -- the composite is smooth
  have hg_sm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M => Φ (f y)) := hΦ.contMDiff.comp hf
  -- containment of the tangent plane in the sheet
  have hle : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => Φ (f y)) (γ t)).range
        ≤ sheetASub k :=
    range_mfderiv_le_of_mem_open_gen (fun y : M => Φ (f y)) hg_sm (sheetASub k) U hUo (γ t) hγtU
      (fun y hy => mem_sheetASub.mpr (hflat y hy))
  -- equality, by the dimension count
  haveI hfinS : FiniteDimensional ℝ ↥(sheetASub k) :=
    Submodule.finiteDimensional_of_le (le_top : sheetASub k ≤ ⊤)
  refine Submodule.eq_of_le_of_finrank_eq (S₂ := sheetASub k) hle ?_
  haveI : FiniteDimensional ℝ
      (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) (γ t)) :=
    (inferInstance : FiniteDimensional ℝ (EuclideanSpace ℝ (Fin (k + 1))))
  have hdom : Module.finrank ℝ
      (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) (γ t)) = k + 1 := by
    rw [show Module.finrank ℝ
          (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) (γ t))
        = Module.finrank ℝ (EuclideanSpace ℝ (Fin (k + 1))) from rfl, finrank_euclideanSpace_fin]
  have hker : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k))
      (fun y : M => Φ (f y)) (γ t)).toLinearMap.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr (hΦimm (γ t))
  have hrank := LinearMap.finrank_range_add_finrank_ker
    (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k))
      (fun y : M => Φ (f y)) (γ t)).toLinearMap
  have hfin : Module.finrank ℝ
      ↥(mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k))
        (fun y : M => Φ (f y)) (γ t)).range = k + 1 := by
    have hk0 : Module.finrank ℝ
        ↥((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
          (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k))
          (fun y : M => Φ (f y)) (γ t)).toLinearMap.ker) = 0 := by
      rw [hker, finrank_bot]
    rw [hk0, add_zero, hdom] at hrank
    exact hrank
  exact hfin.trans (finrank_sheetASub k).symm

end Work.Drive.PushDisc
