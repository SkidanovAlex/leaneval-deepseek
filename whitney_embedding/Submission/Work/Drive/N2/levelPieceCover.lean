import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.exists_finite_levelCover
import Submission.Work.Compat.MFDerivCongrV433

/-!
# Covering a compact piece of a level set of a function on a surface by finitely many curves

`Work.Drive.N2.levelPieceCover`: let `f : M → ℝ` be smooth on a compact surface `M`, let `U` be open
with no critical point of `f` on `closure U`, let `b : ℝ`, and let `K ⊆ closure U` be compact with
`f = b` on `K`.  Then there are finitely many curves `γ i : ℝ → M`, smooth on open sets `V i ⊆ ℝ`,
which lie in the level set `{f = b}`, are immersions there, cover `ker (df)` by their derivative, and
whose images cover `K`.

The proof is local: near a regular point `x₀` of `f`, the level set is (in the chart at `x₀`) the
image of an explicit `C^∞` curve `F : ℝ → ℝ²` with injective derivative, covering the level set in an
open set (`Work.Drive.N2.exists_levelParam_of_isRegular`); pulling back by the chart gives a manifold
curve `γ` which is an immersion into the level set (`exists_local_levelParam` below).  Restricting to
a small neighbourhood of `x₀` in which `f` has no critical point upgrades this to the two conditions
`mfderiv γ t 1 ≠ 0` and `mfderiv f (γ t) v = 0 → v ∈ range (mfderiv γ t)` (via the dimension count
`Work.Drive.N2.range_eq_ker_dim_two`).  Compactness of `K` supplies a finite subcover.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff
open Filter Topology

set_option linter.style.haveILetI false

/-- **From an injective parametrisation of a level set to the "immersion + covers the kernel"
conditions.**  If `γ : ℝ → M` is smooth on the open set `V`, takes values in `{f = b}` there, has
injective differential there, and every point of `γ '' V` is a regular point of `f`
(`(mfderiv f (γ t)) ≠ 0`), then the derivative of `γ` is nonzero and its image is the whole kernel of
`mfderiv f (γ t)` (both tangent spaces have dimension `2` and `1` respectively). -/
lemma inj_imp_ne_zero_and_surj {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ f)
    (b : ℝ) (γ : ℝ → M) (V : Set ℝ)
    (hVopen : IsOpen V)
    (hγsm : ContMDiffOn 𝓘(ℝ,ℝ) (𝓡 2) ∞ γ V)
    (hlev : ∀ t ∈ V, f (γ t) = b)
    (hinj : ∀ t ∈ V, Function.Injective (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t))
    (hreg : ∀ t ∈ V, mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ t) ≠ 0) :
    (∀ t ∈ V, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t 1 ≠ 0) ∧
    (∀ t ∈ V, ∀ v : TangentSpace (𝓡 2) (γ t),
        mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ t) v = 0 →
          ∃ w : TangentSpace (𝓘(ℝ,ℝ)) t, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t w = v) := by
  constructor
  · intro t ht h0
    have hz : mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t (0:ℝ) = 0 := ContinuousLinearMap.map_zero _
    have h2 : (1:ℝ) = 0 := hinj t ht (h0.trans hz.symm)
    exact one_ne_zero h2
  · intro t ht v hv
    have hγmd : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2) γ t :=
      (hγsm.contMDiffAt (hVopen.mem_nhds ht)).mdifferentiableAt (by simp)
    have hconst : (f ∘ γ) =ᶠ[𝓝 t] (fun _ => b) := by
      filter_upwards [hVopen.mem_nhds ht] with s hs
      exact hlev s hs
    have h1 : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (f ∘ γ) t = 0 := by
      rw [Filter.EventuallyEq.mfderiv_eq_v433 hconst (x := t)]
      exact mfderiv_const
    have h2 : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (f ∘ γ) t =
        (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ t)) ∘L (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t) :=
      mfderiv_comp t (hf.mdifferentiableAt (by simp)) hγmd
    have hker : ∀ w : TangentSpace (𝓘(ℝ,ℝ)) t,
        mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ t) (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t w) = 0 := by
      intro w
      have h3 : (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ t)) ∘L (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t) = 0 := by
        rw [← h2]; exact h1
      show ((mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ t)) ∘L (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t)) w = 0
      rw [h3]; rfl
    have hfin : Module.finrank ℝ (TangentSpace (𝓡 2) (γ t)) = 2 := by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2
      exact finrank_euclideanSpace_fin
    haveI : FiniteDimensional ℝ (TangentSpace (𝓡 2) (γ t)) :=
      inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 2)))
    have hL : Function.Injective (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t).toLinearMap := hinj t ht
    have hM' : (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ t)).toLinearMap ≠ 0 := by
      intro h
      exact hreg t ht (ContinuousLinearMap.ext fun v => by
        have := DFunLike.congr_fun h v
        simpa using this)
    exact range_eq_ker_dim_two hfin (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t).toLinearMap
      (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ t)).toLinearMap hL hM' hker v hv

/-- **Local parametrisation of the level set of a smooth function on a surface at a regular point.**

Let `f : M → ℝ` be smooth on a surface `M`, let `x₀` with `f x₀ = b` be a regular point of `f`
(`mfderiv f x₀ ≠ 0`).  Then there are an open neighbourhood `U` of `x₀`, an open set `V ⊆ ℝ`
containing `0`, and a curve `γ : ℝ → M` with `γ` smooth on `V`, taking values in `{f = b}` on `V`,
having injective differential on `V`, whose points are all regular points of `f`, and such that
`{f = b} ∩ U ⊆ γ '' V`.

The curve is built in the chart at `x₀` (`exists_levelParam_of_isRegular`); the set `V` is further
restricted to the preimage of the open set of regular points of the chart representative, which
supplies the last two conditions without any continuity assumption on `mfderiv`. -/
theorem exists_local_levelParam {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ f) (b : ℝ) (x₀ : M)
    (hx₀b : f x₀ = b) (hx₀reg : mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f x₀ ≠ 0) :
    ∃ (U : Set M) (V : Set ℝ) (γ : ℝ → M),
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen V ∧ 0 ∈ V ∧
      ContMDiffOn 𝓘(ℝ,ℝ) (𝓡 2) ∞ γ V ∧
      (∀ t ∈ V, f (γ t) = b) ∧
      (∀ t ∈ V, Function.Injective (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t)) ∧
      (∀ t ∈ V, mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ t) ≠ 0) ∧
      ({x : M | f x = b} ∩ U ⊆ γ '' V) := by
  classical
  set e := extChartAt (𝓡 2) x₀ with hedef
  have hx₀src : x₀ ∈ e.source := by
    rw [hedef, extChartAt_source]; exact mem_chart_source _ _
  have hy₀ : e x₀ ∈ e.target := e.map_source hx₀src
  have hΩ : IsOpen e.target := isOpen_extChartAt_target (I := 𝓡 2) x₀
  have hgp : f (e.symm (e x₀)) = b := by rw [e.left_inv hx₀src]; exact hx₀b
  have hg : ContDiffOn ℝ ∞ (fun y : EuclideanSpace ℝ (Fin 2) => f (e.symm y)) e.target := by
    have h1 : ContMDiffOn 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) (𝓡 2) ∞ (e.symm) e.target :=
      contMDiffOn_extChartAt_symm (I := 𝓡 2) x₀
    have h2 : ContMDiffOn (𝓡 2) 𝓘(ℝ,ℝ) ∞ f Set.univ := hf.contMDiffOn
    exact (h2.comp h1 (Set.subset_univ _)).contDiffOn
  have hd : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => f (e.symm y)) (e x₀) ≠ 0 := by
    intro h
    exact hx₀reg ((mfderiv_eq_zero_iff_chartRep f hf x₀ x₀ hx₀src).mpr h)
  obtain ⟨V, F, U, hV, h0V, hU, hpU, hF0, hFsm, hlev, hFinj, hcov⟩ :=
    exists_levelParam_of_isRegular finrank_euclideanSpace_fin
      (fun y : EuclideanSpace ℝ (Fin 2) => f (e.symm y)) (e x₀) b e.target hΩ hy₀ hg hgp hd
  set γ : ℝ → M := fun t => e.symm (F t) with hγdef
  set V' : Set ℝ := V ∩ F ⁻¹' e.target with hV'def
  set U' : Set M := e.source ∩ e ⁻¹' U with hU'def
  have hV'sub : V' ⊆ V := Set.inter_subset_left
  have hV'open : IsOpen V' := by
    rw [hV'def]
    refine isOpen_iff_mem_nhds.mpr fun t ht => ?_
    have htV : t ∈ V := ht.1
    have hFcont : ContinuousAt F t := hFsm.continuousOn.continuousAt (hV.mem_nhds htV)
    exact Filter.inter_mem (hV.mem_nhds htV)
      (hFcont.preimage_mem_nhds ((isOpen_extChartAt_target (I := 𝓡 2) x₀).mem_nhds ht.2))
  have hU'open : IsOpen U' := by
    rw [hU'def]
    refine (continuousOn_extChartAt (I := 𝓡 2) x₀).isOpen_inter_preimage
      (isOpen_extChartAt_source (I := 𝓡 2) x₀) hU
  have hx₀U' : x₀ ∈ U' := by
    rw [hU'def]; exact ⟨hx₀src, hpU⟩
  have hγsm : ContMDiffOn 𝓘(ℝ,ℝ) (𝓡 2) ∞ γ V' := by
    rw [hγdef]
    refine (contMDiffOn_extChartAt_symm (I := 𝓡 2) x₀).comp ?_ ?_
    · exact hFsm.contMDiffOn.mono hV'sub
    · rw [hV'def]
      rintro t ⟨-, ht⟩
      exact ht
  have hlev' : ∀ t ∈ V', f (γ t) = b := fun t ht => hlev t (hV'sub ht)
  have hinj' : ∀ t ∈ V', Function.Injective (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t) := by
    intro t ht
    have htV : t ∈ V := hV'sub ht
    have hFt_tgt : F t ∈ e.target := ht.2
    have hc : MDifferentiableAt 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) (𝓡 2) (e.symm) (F t) := by
      have h := mdifferentiableWithinAt_extChartAt_symm (I := 𝓡 2) (x := x₀) hFt_tgt
      rw [ModelWithCorners.range_eq_univ] at h
      simpa [MDifferentiableAt, MDifferentiableWithinAt, ChartedSpace.LiftPropAt, hedef] using h
    have hF : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) F t :=
      (hFsm.contDiffAt (hV.mem_nhds htV)).contMDiffAt.mdifferentiableAt (by simp)
    have hcomp : mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t =
        (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) (𝓡 2) (e.symm) (F t)) ∘L
          mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) F t := by
      rw [hγdef]
      exact mfderiv_comp t hc hF
    rw [hcomp]
    have hinv : Function.Injective
        (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) (𝓡 2) (e.symm) (F t)) := by
      have h := isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 2) (x := x₀) hFt_tgt
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using h.injective
    intro x y hxy
    have h1 : (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) (𝓡 2) (e.symm) (F t))
        ((mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) F t) x)
        = (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) (𝓡 2) (e.symm) (F t))
        ((mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) F t) y) := hxy
    have h2 : (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) F t) x
        = (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) F t) y := hinv h1
    rw [mfderiv_eq_fderiv] at h2
    exact hFinj t htV h2
  have hcov' : {x : M | f x = b} ∩ U' ⊆ γ '' V' := by
    rintro x ⟨hxb, hxU⟩
    have hxsrc : x ∈ e.source := hxU.1
    have heU : e x ∈ U := hxU.2
    have hexb : e x ∈ {y : EuclideanSpace ℝ (Fin 2) | f (e.symm y) = b} := by
      show f (e.symm (e x)) = b
      rw [e.left_inv hxsrc]
      exact hxb
    obtain ⟨t, htV, htF⟩ := hcov ⟨hexb, heU⟩
    refine ⟨t, ?_, ?_⟩
    · rw [hV'def]
      refine ⟨htV, ?_⟩
      show F t ∈ e.target
      rw [htF]
      exact e.map_source hxsrc
    · rw [hγdef]
      show e.symm (F t) = x
      rw [htF, e.left_inv hxsrc]
  -- The open set of chart points at which the chart representative is regular.
  set S : Set (EuclideanSpace ℝ (Fin 2)) :=
    e.target ∩ (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => f (e.symm y))) ⁻¹' {L | L ≠ 0}
    with hSdef
  have hSopen : IsOpen S := by
    rw [hSdef]
    exact (hg.continuousOn_fderiv_of_isOpen hΩ (by simp)).isOpen_inter_preimage hΩ isOpen_ne
  -- The corresponding open set of regular points of `f` in the chart at `x₀`.
  set N : Set M := e.source ∩ e ⁻¹' S with hNdef
  have hNopen : IsOpen N := by
    rw [hNdef]
    exact (continuousOn_extChartAt (I := 𝓡 2) x₀).isOpen_inter_preimage
      (isOpen_extChartAt_source (I := 𝓡 2) x₀) hSopen
  have hx₀S : e x₀ ∈ S := by
    rw [hSdef]; exact ⟨hy₀, hd⟩
  have hx₀N : x₀ ∈ N := by
    rw [hNdef]; exact ⟨hx₀src, hx₀S⟩
  have hNreg : ∀ z ∈ N, mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f z ≠ 0 := by
    intro z hz h0
    have hzS : e z ∈ S := hz.2
    have hzne : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => f (e.symm y)) (e z) ≠ 0 := hzS.2
    exact hzne ((mfderiv_eq_zero_iff_chartRep f hf x₀ z hz.1).mp h0)
  have hγ0 : γ 0 = x₀ := by
    rw [hγdef]
    show e.symm (F 0) = x₀
    rw [hF0, e.left_inv hx₀src]
  refine ⟨U' ∩ N, V' ∩ γ ⁻¹' N, γ, hU'open.inter hNopen, ⟨hx₀U', hx₀N⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hγsm.continuousOn.isOpen_inter_preimage hV'open hNopen
  · refine ⟨⟨h0V, ?_⟩, ?_⟩
    · show F 0 ∈ e.target
      rw [hF0]; exact hy₀
    · show γ 0 ∈ N
      rw [hγ0]; exact hx₀N
  · exact hγsm.mono Set.inter_subset_left
  · intro t ht; exact hlev' t ht.1
  · intro t ht; exact hinj' t ht.1
  · intro t ht
    exact hNreg (γ t) ht.2
  · rintro x ⟨hxb, hxU⟩
    obtain ⟨t, htV', hxt⟩ := hcov' ⟨hxb, hxU.1⟩
    exact ⟨t, ⟨htV', by show γ t ∈ N; rw [hxt]; exact hxU.2⟩, hxt⟩

open scoped Manifold ContDiff in
theorem levelPieceCover {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (U : Set M) (hU : IsOpen U) (hcrit : ∀ x ∈ closure U, ¬ Work.Drive.Morse.IsCritical f x)
    {b : ℝ} (K : Set M) (hK : IsCompact K) (hKU : K ⊆ closure U) (hKb : K ⊆ {x | f x = b}) :
    ∃ (N : ℕ) (γ : Fin N → ℝ → M) (V : Fin N → Set ℝ),
      (∀ i, IsOpen (V i)) ∧
      (∀ i, ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) ∞ (γ i) (V i)) ∧
      (∀ i t, t ∈ V i → f (γ i t) = b) ∧
      (∀ i t, t ∈ V i → mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (γ i) t 1 ≠ 0) ∧
      (∀ i t, t ∈ V i → ∀ v : TangentSpace (𝓡 2) (γ i t),
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (γ i t) v = 0 →
          ∃ w : TangentSpace (𝓘(ℝ, ℝ)) t, mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (γ i) t w = v) ∧
      (K ⊆ ⋃ i, γ i '' V i) := by
  classical
  -- Local parametrisation of the level set at every point of `K`.
  have hlocal : ∀ q : {x : M // x ∈ K},
      ∃ (Uq : Set M) (Vq : Set ℝ) (γq : ℝ → M),
        IsOpen Uq ∧ q.1 ∈ Uq ∧ IsOpen Vq ∧
        ContMDiffOn 𝓘(ℝ,ℝ) (𝓡 2) ∞ γq Vq ∧
        (∀ t ∈ Vq, f (γq t) = b) ∧
        (∀ t ∈ Vq, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γq t 1 ≠ 0) ∧
        (∀ t ∈ Vq, ∀ v : TangentSpace (𝓡 2) (γq t),
            mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γq t) v = 0 →
              ∃ w : TangentSpace (𝓘(ℝ,ℝ)) t, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γq t w = v) ∧
        ({x : M | f x = b} ∩ Uq ⊆ γq '' Vq) := by
    intro q
    have hqreg : mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f q.1 ≠ 0 := by
      simpa [Work.Drive.Morse.IsCritical] using hcrit q.1 (hKU q.2)
    obtain ⟨Uq, Vq, γq, hUq, hqUq, hVq, h0Vq, hγq, hlevq, hinjq, hregq, hcovq⟩ :=
      exists_local_levelParam f hf b q.1 (hKb q.2) hqreg
    obtain ⟨hne, hsurj⟩ := inj_imp_ne_zero_and_surj f hf b γq Vq hVq hγq hlevq hinjq hregq
    exact ⟨Uq, Vq, γq, hUq, hqUq, hVq, hγq, hlevq, hne, hsurj, hcovq⟩
  choose Uq Vq γq hUqopen hqUq hVqopen hγqsm hlevq hneq hsurjq hcovq using hlocal
  -- A finite subcover of `K`, reindexed by `Fin t.card`.
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover Uq hUqopen
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hqUq ⟨x, hx⟩⟩)
  let γ : Fin t.card → ℝ → M := fun k => γq (t.equivFin.symm k)
  let V : Fin t.card → Set ℝ := fun k => Vq (t.equivFin.symm k)
  refine ⟨t.card, γ, V, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; exact hVqopen _
  · intro k; exact hγqsm _
  · intro k s hs; exact hlevq _ s hs
  · intro k s hs; exact hneq _ s hs
  · intro k s hs v hv; exact hsurjq _ s hs v hv
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
    refine Set.mem_iUnion.mpr ⟨t.equivFin ⟨i, hi⟩, ?_⟩
    have hsymm : t.equivFin.symm (t.equivFin ⟨i, hi⟩) = ⟨i, hi⟩ := Equiv.symm_apply_apply _ _
    show x ∈ γq (t.equivFin.symm (t.equivFin ⟨i, hi⟩)) '' Vq (t.equivFin.symm (t.equivFin ⟨i, hi⟩))
    rw [hsymm]
    exact hcovq i ⟨hKb hx, hxi⟩

end Work.Drive.N2
