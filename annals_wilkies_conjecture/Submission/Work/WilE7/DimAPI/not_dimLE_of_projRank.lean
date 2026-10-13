/-
  `Work.WilE7.DimAPI.not_dimLE_of_projRank` (node C3 of the E7 main design).

  A `Good` absolute stratum `S : Stratum 0 (n + m)` and a point `z ∈ S.X.set` with projection rank
  `> K` make the base projection `π_n (absSet S)` thick in the `DimLE` sense: it has a
  `(K+1)`-dimensional coordinate projection with non-empty interior.

  The argument.  Write `G` for the equation map `w ↦ (a ↦ eaEval S.X.c (S.h a) w)` on
  `ℝ^{0+(n+m)}`; at `z` it is analytic, `G z = 0` and `fderiv ℝ G z` is onto (`range = ⊤`, the
  rank condition in `Stratum.Good`), while `jac S z = fderiv ℝ G z`.  Choose `K + 1` base
  coordinates `e` on which the projection `basePrLin` is a surjection of the tangent space
  `ker (jac S z) = ker (fderiv ℝ G z)` (possible because `projRank S z > K`).  Then the map
  `Φ w = append (G w) (A w - A z)`, with `A = π_e ∘ basePrLin`, is analytic at `z` with
  *surjective* derivative there: the first component accounts for the `G`-directions, the second
  for the `(K+1)` chosen base directions inside the kernel.  So `Φ` is open at `z`
  (`image_mem_nhds_of_surj_fderiv`), and for every small `y` there is `w` near `z` with
  `G w = 0` and `A w = A z + y`; `Stratum.Good` upgrades `G w = 0` to `w ∈ S.X.set`.  Hence
  `A z` is interior to `A '' S.X.set ⊆ (· ∘ e) '' (π_n (absSet S))`, contradicting `DimLE · K`.
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE5.Basic
import Submission.Work.WilE5.Calc.hasFDerivAt_eaEval
import Submission.Work.WilE7.Nondrop.FibreCalc
import Submission.Work.WilE7.Dim.image_mem_nhds_of_surj_fderiv
import Submission.Work.WilE7.Dim.dimLE_of_chart
import Submission.Work.WilE9.Ift.AppendCLM
import Submission.Work.WilE7.DimAPI.exists_coordProj_surj_of_le_finrank
import Submission.Work.WilE7.DimAPI.jac_eq_fderiv
import Submission.Work.WilE7.DimAPI.range_fderiv_good_eq_top

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology
namespace Work.WilE7.DimAPI
open WilkiesDesign WilkiesDesign.E

/-- The general form of `Work.WilE7.DimAPI.exists_coordProj_surj_of_le_finrank`, for a linear map
out of an arbitrary finite-dimensional space: if the rank of `A` is at least `m`, then `m`
coordinates of the target can be chosen so that the corresponding projection is surjective on the
range of `A`. -/
lemma exists_coordProj_surj_of_le_finrank' {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] {n m : ℕ} (A : E →ₗ[ℝ] (Fin n → ℝ))
    (h : m ≤ Module.finrank ℝ A.range) :
    ∃ e : Fin m ↪ Fin n, Function.Surjective (fun v : E => (A v) ∘ e) := by
  let φ : (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] E :=
    LinearEquiv.ofFinrankEq (Fin (Module.finrank ℝ E) → ℝ) E (by rw [Module.finrank_fin_fun])
  have hrange : (A.comp (φ : (Fin (Module.finrank ℝ E) → ℝ) →ₗ[ℝ] E)).range = A.range := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr φ.surjective, Submodule.map_top]
  have h' : m ≤ Module.finrank ℝ (A.comp (φ : (Fin (Module.finrank ℝ E) → ℝ) →ₗ[ℝ] E)).range :=
    hrange ▸ h
  obtain ⟨e, he⟩ := exists_coordProj_surj_of_le_finrank
    (A.comp (φ : (Fin (Module.finrank ℝ E) → ℝ) →ₗ[ℝ] E)) h'
  refine ⟨e, ?_⟩
  intro y
  obtain ⟨v, hv⟩ := he y
  exact ⟨φ v, by simpa [LinearMap.comp_apply] using hv⟩

theorem not_dimLE_of_projRank {n m : ℕ} (S : WilkiesDesign.E.Stratum 0 (n + m)) (hS : S.Good)
    {z : Fin (0 + (n + m)) → ℝ} (hz : z ∈ S.X.set) {K : ℕ}
    (hK : K < Work.WilE7.MainDesign.projRank S z) :
    ¬ WilkiesDesign.DimLE
      (WilkiesDesign.E.projFirst n m '' Work.WilE7.MainDesign.absSet S) K := by
  intro hdim
  -- `basePrLin` is `projFirst` after `absPt`
  have hbase : ∀ w : Fin (0 + (n + m)) → ℝ,
      Work.WilE7.MainDesign.basePrLin n m w = projFirst n m (Work.WilE7.MainDesign.absPt w) :=
    fun w => rfl
  -- the equation map of the stratum
  let G : (Fin (0 + (n + m)) → ℝ) → (Fin S.j → ℝ) := fun w a => eaEval S.X.c (S.h a) w
  have hGan : ∀ w, AnalyticAt ℝ G w :=
    fun w => AnalyticAt.pi (fun a => Work.WilE5.Strat.analyticAt_eaEval S.X.c (S.h a) w)
  have hGz : G z = 0 := funext fun a => Work.WilE5.Stratum.good_eqs hS hz a
  have hGtop : (fderiv ℝ G z).range = ⊤ := range_fderiv_good_eq_top S hS hz
  have hjac : ((Work.WilE7.MainDesign.jac S z :
        (Fin (0 + (n + m)) → ℝ) →ₗ[ℝ] (Fin S.j → ℝ)))
      = ((fderiv ℝ G z : (Fin (0 + (n + m)) → ℝ) →L[ℝ] (Fin S.j → ℝ)) :
          (Fin (0 + (n + m)) → ℝ) →ₗ[ℝ] (Fin S.j → ℝ)) := jac_eq_fderiv S z
  have hker : (Work.WilE7.MainDesign.jac S z).ker
      = ((fderiv ℝ G z : (Fin (0 + (n + m)) → ℝ) →L[ℝ] (Fin S.j → ℝ)) :
          (Fin (0 + (n + m)) → ℝ) →ₗ[ℝ] (Fin S.j → ℝ)).ker := by rw [hjac]
  -- the tangent space projects onto `projRank S z > K` coordinates
  have hle : K + 1 ≤ Module.finrank ℝ
      (((Work.WilE7.MainDesign.basePrLin n m).comp
        (Submodule.subtype (((fderiv ℝ G z : (Fin (0 + (n + m)) → ℝ) →L[ℝ] (Fin S.j → ℝ)) :
          (Fin (0 + (n + m)) → ℝ) →ₗ[ℝ] (Fin S.j → ℝ)).ker))).range) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    rw [← hker]
    have hfin : Module.finrank ℝ ((LinearMap.ker (Work.WilE7.MainDesign.jac S z)).map
        (Work.WilE7.MainDesign.basePrLin n m)) = Work.WilE7.MainDesign.projRank S z := rfl
    omega
  obtain ⟨e, he⟩ := exists_coordProj_surj_of_le_finrank'
    ((Work.WilE7.MainDesign.basePrLin n m).comp
      (Submodule.subtype (((fderiv ℝ G z : (Fin (0 + (n + m)) → ℝ) →L[ℝ] (Fin S.j → ℝ)) :
          (Fin (0 + (n + m)) → ℝ) →ₗ[ℝ] (Fin S.j → ℝ)).ker))) hle
  -- the `(K+1)` chosen base coordinates
  let A : (Fin (0 + (n + m)) → ℝ) →L[ℝ] (Fin (K + 1) → ℝ) :=
    (Work.WilE7.Dim.coordProj e).comp (Work.WilE7.MainDesign.basePrLin n m).toContinuousLinearMap
  have hA_apply : ∀ w, A w = (projFirst n m (Work.WilE7.MainDesign.absPt w)) ∘ (⇑e) := by
    intro w
    rw [show A w = (Work.WilE7.Dim.coordProj e) ((Work.WilE7.MainDesign.basePrLin n m) w) from rfl,
      Work.WilE7.Dim.coordProj_apply, hbase w]
  -- the auxiliary map `Φ w = (G w, A w - A z)`
  let Φ : (Fin (0 + (n + m)) → ℝ) → (Fin (S.j + (K + 1)) → ℝ) :=
    fun w => Work.WilE9.Ift.appendCLM S.j (K + 1) (G w, A w - A z)
  have hΦan : AnalyticAt ℝ Φ z := by
    have h1 : AnalyticAt ℝ (fun w => (G w, A w - A z)) z :=
      (hGan z).prod ((A.analyticAt z).sub (analyticAt_const (v := A z) (x := z)))
    have h2 : AnalyticAt ℝ (fun p : (Fin S.j → ℝ) × (Fin (K+1) → ℝ) =>
        Work.WilE9.Ift.appendCLM S.j (K+1) p) (G z, A z - A z) :=
      (Work.WilE9.Ift.appendCLM S.j (K+1)).analyticAt _
    have h3 := AnalyticAt.comp (f := fun w => (G w, A w - A z)) (x := z) h2 h1
    simpa [Φ, Function.comp_def] using h3
  have hstr : HasStrictFDerivAt Φ
      ((Work.WilE9.Ift.appendCLM S.j (K+1)).comp ((fderiv ℝ G z).prod A)) z := by
    have h1 : HasStrictFDerivAt (fun w : (Fin (0 + (n + m)) → ℝ) => (G w, A w - A z))
        ((fderiv ℝ G z).prod A) z := by
      have h := ((hGan z).hasStrictFDerivAt).prodMk
        (A.hasStrictFDerivAt.sub (hasStrictFDerivAt_const (A z) z))
      simpa using h
    have h2 := (Work.WilE9.Ift.appendCLM S.j (K+1)).hasStrictFDerivAt.comp z h1
    simpa [Φ, Function.comp_def] using h2
  have hΦder : fderiv ℝ Φ z
      = (Work.WilE9.Ift.appendCLM S.j (K+1)).comp ((fderiv ℝ G z).prod A) :=
    hstr.hasFDerivAt.fderiv
  -- the derivative of `Φ` at `z` is surjective
  have hsurj : Function.Surjective (fderiv ℝ Φ z) := by
    rw [hΦder]
    intro t
    let u : Fin S.j → ℝ := fun a => t (Fin.castAdd (K+1) a)
    let y : Fin (K+1) → ℝ := fun i => t (Fin.natAdd S.j i)
    have hsurjG : Function.Surjective (fderiv ℝ G z) := by
      intro w'
      have hw' : w' ∈ (fderiv ℝ G z).range := by rw [hGtop]; exact Submodule.mem_top
      exact LinearMap.mem_range.mp hw'
    obtain ⟨v1, hv1⟩ := hsurjG u
    obtain ⟨v2, hv2⟩ := he (y - A v1)
    have hv2ker : (fderiv ℝ G z) (v2 : Fin (0 + (n + m)) → ℝ) = 0 := v2.2
    have hv2A : A v2 = y - A v1 := by
      rw [hA_apply v2]
      simp only [LinearMap.comp_apply] at hv2
      simpa [hbase (v2 : Fin (0 + (n + m)) → ℝ)] using hv2
    refine ⟨v1 + v2, ?_⟩
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, map_add, map_add,
      hv1, hv2ker, hv2A, add_zero, Work.WilE9.Ift.appendCLM_apply]
    have h2 : A v1 + (y - A v1) = y := by abel
    rw [h2]
    funext i
    cases i using Fin.addCases with
    | left a => rw [Fin.append_left]
    | right j => rw [Fin.append_right]
  have happ0 : Fin.append (0 : Fin S.j → ℝ) (0 : Fin (K+1) → ℝ) = 0 := by
    funext i
    cases i using Fin.addCases with
    | left a => simp
    | right j => simp
  have hΦz : Φ z = 0 := by
    show Work.WilE9.Ift.appendCLM S.j (K+1) (G z, A z - A z) = 0
    rw [hGz, sub_self, Work.WilE9.Ift.appendCLM_apply, happ0]
  -- `Good` upgrades `G w = 0` to membership, near `z`
  have hloc : ∀ᶠ w in 𝓝 z, G w = 0 → w ∈ S.X.set := by
    filter_upwards [Work.WilE5.Stratum.good_local hS hz] with w hw hG0
    exact hw (funext fun i => Fin.elim0 i) (fun a => congrFun hG0 a)
  obtain ⟨U₀, hU₀sub, hU₀open, hU₀z⟩ := mem_nhds_iff.mp hloc
  have hmem : Φ '' U₀ ∈ 𝓝 (0 : Fin (S.j + (K+1)) → ℝ) := by
    have h := Work.WilE7.Dim.image_mem_nhds_of_surj_fderiv hΦan hsurj U₀ (hU₀open.mem_nhds hU₀z)
    rwa [hΦz] at h
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hmem
  -- the preimage radius in the `(K+1)` base coordinates
  have hcont : Continuous (fun y : Fin (K+1) → ℝ => Fin.append (0 : Fin S.j → ℝ) y) := by
    have h1 : (fun y : Fin (K+1) → ℝ => Fin.append (0 : Fin S.j → ℝ) y)
        = fun y => (Work.WilE9.Ift.appendCLM S.j (K+1)) (0, y) := by
      funext y; rw [Work.WilE9.Ift.appendCLM_apply]
    rw [h1]
    exact (Work.WilE9.Ift.appendCLM S.j (K+1)).continuous.comp
      (continuous_const.prodMk continuous_id)
  have hpre : (fun y : Fin (K+1) → ℝ => Fin.append (0 : Fin S.j → ℝ) y) ⁻¹'
      Metric.ball (0 : Fin (S.j + (K+1)) → ℝ) ε ∈ 𝓝 (0 : Fin (K+1) → ℝ) := by
    refine hcont.continuousAt.preimage_mem_nhds ?_
    simpa [happ0] using Metric.ball_mem_nhds (0 : Fin (S.j+(K+1)) → ℝ) hεpos
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hpre
  -- `A z` is interior to `A '' S.X.set`
  have hball_sub : Metric.ball (A z) δ ⊆ A '' S.X.set := by
    intro v hv
    have hy : v - A z ∈ Metric.ball (0 : Fin (K+1) → ℝ) δ := by
      simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hv
    obtain ⟨w, hwU, hwΦ⟩ := hε (hδ hy)
    have hwΦ' : Fin.append (G w) (A w - A z) = Fin.append (0 : Fin S.j → ℝ) (v - A z) := by
      simpa [Φ, Work.WilE9.Ift.appendCLM_apply] using hwΦ
    have hGw : G w = 0 := by
      funext a
      have hh := congrFun hwΦ' (Fin.castAdd (K+1) a)
      rw [Fin.append_left, Fin.append_left] at hh
      exact hh
    have hAw : A w - A z = v - A z := by
      funext i
      have hh := congrFun hwΦ' (Fin.natAdd S.j i)
      rw [Fin.append_right, Fin.append_right] at hh
      exact hh
    refine ⟨w, hU₀sub hwU hGw, ?_⟩
    have h1 : A w = A z + (v - A z) := by rw [← hAw]; abel
    rw [h1]; abel
  have hnbd : A '' S.X.set ∈ 𝓝 (A z) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds (A z) hδpos) hball_sub
  have hint : A z ∈ interior (A '' S.X.set) := mem_interior_iff_mem_nhds.mpr hnbd
  have hsub2 : A '' S.X.set ⊆ (fun x : Fin n → ℝ => x ∘ (⇑e)) ''
      (projFirst n m '' Work.WilE7.MainDesign.absSet S) := by
    rintro _ ⟨w, hwS, rfl⟩
    exact ⟨projFirst n m (Work.WilE7.MainDesign.absPt w),
      ⟨Work.WilE7.MainDesign.absPt w, ⟨w, hwS, rfl⟩, rfl⟩, (hA_apply w).symm⟩
  have hne : (interior ((fun x : Fin n → ℝ => x ∘ (⇑e)) ''
      (projFirst n m '' Work.WilE7.MainDesign.absSet S))).Nonempty :=
    ⟨A z, interior_mono hsub2 hint⟩
  rw [hdim e] at hne
  exact hne.ne_empty rfl

end Work.WilE7.DimAPI
