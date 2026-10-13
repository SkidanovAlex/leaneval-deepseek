/-
  WilE7 / DimAPI — D1' : the equal-dimension open-map statement for a linear map that is
  injective on the tangent space of a stratum.

  `L : ℝ^{N2} → ℝ^N` maps the absolute stratum `T` into the absolute stratum `S`, is injective on
  the tangent space `ker (jac T z)`, and the two strata have the same dimension
  (`N2 - T.j = N - S.j`).  Then, near `absPt z`, the image `L '' absSet T` covers `absSet S`: for
  every neighbourhood `U` of `absPt z` in `ℝ^{N2}`, almost every point of `absSet S` near
  `L (absPt z)` is the `L`-image of a point of `absSet T ∩ U`.

  ## Proof plan

  Transport `L` to `Lhat := L ∘ absPt`, so that `Lhat (T.X.set) ⊆ fiber S.X.set pt0 = absSet S`,
  and `hinj` says `Lhat` is injective on `ker (jac T z) = ker (fderiv (eqMap T) z)`.

  * `absSet S = fiber S.X.set pt0` (`absSet_eq_fiber`), so `fnpFibre S pt0` is the equation map of
    `absSet S` and `fnpFibre S pt0 w₀ = 0` for `w₀ := L (absPt z)`.
  * `Work.WilE7.Nondrop.analyticLevelSetChartRange` applied to `eqMap T` at `z` gives a chart
    `γT : ker (fderiv (eqMap T) z) → ℝ^{0+N2}` of the level set `{eqMap T = 0}` near `z`, with
    `γT 0 = z`, `γT` analytic at `0`, and `range (d γT 0) = ker (fderiv (eqMap T) z)`.
    `range (fderiv (eqMap T) z) = ⊤` comes from `Stratum.Good` (the Jacobian of a `Good` stratum
    has full row rank).
  * `γ := Lhat ∘ γT : ker (fderiv (eqMap T) z) → ℝ^N` is then an analytic immersion of a
    dimension-`n` piece of the level set of `fnpFibre S pt0`, where
    `n = finrank (ker (fderiv (eqMap T) z)) = (0 + N2) - T.j = N - S.j
       = finrank (ker (fderiv (fnpFibre S pt0) w₀))`
    — this is exactly the hypothesis `hdim`.
  * The abstract lemma `levelSet_subset_image_of_inj` (proved in
    `Submission.Work.WilE7.DimAPI.levelSet_subset_image_of_inj`) then says that every neighbourhood
    of `0` in the parameter space parametrises a neighbourhood of `w₀` *inside* the level set.
  * Since `Stratum.Good` identifies the level set near a point of the stratum with the stratum
    itself (`Work.WilE5.Stratum.good_local`), this gives exactly the required germ statement.
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.DimAPI.ProjRankAux
import Submission.Work.WilE7.Nondrop.FibreCalc
import Submission.Work.WilE7.Nondrop.analyticLevelSetChartRange
import Submission.Work.WilE5.Calc.hasFDerivAt_eaEval
import Submission.Work.WilE7.DimAPI.levelSet_subset_image_of_inj

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.DimAPI

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.Nondrop

/-! ## The empty base point and the `absPt` reindexing -/

/-- The unique point of `ℝ⁰`. -/
private def pt0 : Fin 0 → ℝ := fun i => i.elim0

private lemma absPt_apply_natAdd {N : ℕ} (z : Fin (0 + N) → ℝ) (i : Fin N) :
    MainDesign.absPt z i = z (Fin.natAdd 0 i) :=
  congrArg z (by ext; simp [Fin.natAdd])

private lemma absPt_append (N : ℕ) (y : Fin N → ℝ) :
    MainDesign.absPt (Fin.append pt0 y) = y := by
  funext i
  rw [absPt_apply_natAdd, Fin.append_right]

private lemma append_absPt (N : ℕ) (z : Fin (0 + N) → ℝ) :
    Fin.append pt0 (MainDesign.absPt z) = z := by
  funext i
  refine Fin.addCases (fun j => j.elim0) (fun l => ?_) i
  rw [Fin.append_right, absPt_apply_natAdd]

/-- The absolute stratum `S` in `ℝ^N` is the fibre of `S.X.set` over the empty base point. -/
private theorem absSet_eq_fiber {N : ℕ} (S : Stratum 0 N) :
    MainDesign.absSet S = fiber S.X.set pt0 := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    show Fin.append pt0 (MainDesign.absPt z) ∈ S.X.set
    rwa [append_absPt]
  · intro hy
    exact ⟨Fin.append pt0 y, hy, absPt_append N y⟩

/-! ## The Jacobian of a stratum is the derivative of its equation map -/

private theorem jac_eq_fderiv_apply {p q : ℕ} (S : Stratum p q) (z : Fin (p + q) → ℝ)
    (v : Fin (p + q) → ℝ) : MainDesign.jac S z v = fderiv ℝ (eqMap S) z v := by
  rw [MainDesign.jac]
  show (Matrix.of fun (a : Fin S.j) (l : Fin (p + q)) =>
      eaEval S.X.c (eaD S.X.c l (S.h a)) z).mulVecLin v
    = fderiv ℝ (fun w : Fin (p + q) → ℝ => fun a : Fin S.j => eaEval S.X.c (S.h a) w) z v
  ext a
  rw [Matrix.mulVecLin_apply, Matrix.mulVec, fderiv_pi]
  · simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, Matrix.of_apply]
    rw [(Work.WilE5.Calc.hasFDerivAt_eaEval S.X.c (S.h a) z).fderiv]
    simp [dotProduct, Finset.sum_apply, smul_eq_mul]
  · intro a
    exact (Work.WilE5.Calc.hasFDerivAt_eaEval S.X.c (S.h a) z).differentiableAt

private theorem fderiv_eqMap_eq_jac {p q : ℕ} (S : Stratum p q) (z : Fin (p + q) → ℝ) :
    ((fderiv ℝ (eqMap S) z : (Fin (p + q) → ℝ) →L[ℝ] (Fin S.j → ℝ)) :
      (Fin (p + q) → ℝ) →ₗ[ℝ] (Fin S.j → ℝ)) = MainDesign.jac S z := by
  apply LinearMap.ext
  intro v
  exact (jac_eq_fderiv_apply S z v).symm

private theorem ker_fderiv_eqMap_eq_ker_jac {p q : ℕ} (S : Stratum p q) (z : Fin (p + q) → ℝ) :
    (fderiv ℝ (eqMap S) z).ker = LinearMap.ker (MainDesign.jac S z) := by
  rw [fderiv_eqMap_eq_jac S z]

/-- A `Good` stratum has full row rank Jacobian at each of its points. -/
private theorem range_jac_eq_top' {p q : ℕ} (S : Stratum p q) (hS : S.Good)
    {z : Fin (p + q) → ℝ} (hz : z ∈ S.X.set) : (MainDesign.jac S z).range = ⊤ := by
  have hgood : ((Matrix.of fun (a : Fin S.j) (l : Fin (p + q)) =>
      eaEval S.X.c (eaD S.X.c l (S.h a)) z).submatrix id (Work.WilE5.yDir p)).rank = S.j := by
    have h := Work.WilE5.Stratum.good_rank hS hz
    have hsub : (Matrix.of fun (a : Fin S.j) (l : Fin (p + q)) =>
        eaEval S.X.c (eaD S.X.c l (S.h a)) z).submatrix id (Work.WilE5.yDir p)
        = (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
          eaEval S.X.c (eaD S.X.c (Work.WilE5.yDir p l) (S.h a)) z) := by
      ext a l
      simp [Matrix.submatrix_apply]
    rw [hsub]
    exact h
  have hupper : (Matrix.of fun (a : Fin S.j) (l : Fin (p + q)) =>
      eaEval S.X.c (eaD S.X.c l (S.h a)) z).rank ≤ S.j := by
    simpa using Matrix.rank_le_card_height (Matrix.of fun (a : Fin S.j) (l : Fin (p + q)) =>
      eaEval S.X.c (eaD S.X.c l (S.h a)) z)
  have hle := Matrix.rank_submatrix_le (Matrix.of fun (a : Fin S.j) (l : Fin (p + q)) =>
      eaEval S.X.c (eaD S.X.c l (S.h a)) z) id (Work.WilE5.yDir p)
  have hM : (Matrix.of fun (a : Fin S.j) (l : Fin (p + q)) =>
      eaEval S.X.c (eaD S.X.c l (S.h a)) z).rank = S.j :=
    le_antisymm hupper (Eq.trans_le hgood.symm hle)
  rw [MainDesign.jac]
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fin_fun]
  exact hM

private theorem range_fderiv_eqMap_eq_top {p q : ℕ} (S : Stratum p q) (hS : S.Good)
    {z : Fin (p + q) → ℝ} (hz : z ∈ S.X.set) : (fderiv ℝ (eqMap S) z).range = ⊤ := by
  rw [fderiv_eqMap_eq_jac S z]
  exact range_jac_eq_top' S hS hz

private theorem finrank_range_fderiv_eqMap {p q : ℕ} (S : Stratum p q) (hS : S.Good)
    {z : Fin (p + q) → ℝ} (hz : z ∈ S.X.set) :
    Module.finrank ℝ ↥((fderiv ℝ (eqMap S) z).range) = S.j := by
  rw [range_fderiv_eqMap_eq_top S hS hz, finrank_top]
  exact Module.finrank_fin_fun ℝ

private theorem finrank_ker_eqMap {p q : ℕ} (S : Stratum p q) (hS : S.Good)
    {z : Fin (p + q) → ℝ} (hz : z ∈ S.X.set) :
    Module.finrank ℝ (fderiv ℝ (eqMap S) z).ker = (p + q) - S.j := by
  have h1 : Module.finrank ℝ ↥((fderiv ℝ (eqMap S) z).range)
      + Module.finrank ℝ (fderiv ℝ (eqMap S) z).ker
      = Module.finrank ℝ (Fin (p + q) → ℝ) :=
    LinearMap.finrank_range_add_finrank_ker _
  have h2 : Module.finrank ℝ ↥((fderiv ℝ (eqMap S) z).range) = S.j :=
    finrank_range_fderiv_eqMap S hS hz
  have h3 : Module.finrank ℝ (Fin (p + q) → ℝ) = p + q := Module.finrank_fin_fun ℝ
  omega

/-! ## D1' -/

theorem openMap_of_equalDim {N N2 : ℕ} (S : WilkiesDesign.E.Stratum 0 N)
    (T : WilkiesDesign.E.Stratum 0 N2) (hS : S.Good) (hT : T.Good)
    (L : (Fin N2 → ℝ) →ₗ[ℝ] (Fin N → ℝ))
    (hmap : L '' Work.WilE7.MainDesign.absSet T ⊆ Work.WilE7.MainDesign.absSet S)
    (hinj : ∀ z ∈ T.X.set, ∀ v ∈ LinearMap.ker (Work.WilE7.MainDesign.jac T z),
      L (Work.WilE7.MainDesign.absPt v) = 0 → v = 0)
    (hdim : N2 - T.j = N - S.j) :
    ∀ z ∈ T.X.set, ∀ U ∈ nhds (Work.WilE7.MainDesign.absPt z), ∀ᶠ w in nhds (L (Work.WilE7.MainDesign.absPt z)),
      w ∈ Work.WilE7.MainDesign.absSet S → w ∈ L '' (Work.WilE7.MainDesign.absSet T ∩ U) := by
  classical
  intro z hzT U hU
  -- the reindexed linear map `Lhat = L ∘ absPt` and the base point `w₀`
  set Lhat : (Fin (0 + N2) → ℝ) →L[ℝ] (Fin N → ℝ) :=
    (LinearMap.toContinuousLinearMap L).comp (absPtCLM N2) with hLhat
  have hLhat_apply : ∀ v : Fin (0 + N2) → ℝ, Lhat v = L (MainDesign.absPt v) := by
    intro v
    rw [hLhat, ContinuousLinearMap.comp_apply]
    simp
  set w₀ : Fin N → ℝ := L (MainDesign.absPt z) with hw₀
  have hw₀_abs : w₀ ∈ MainDesign.absSet S := by
    rw [hw₀]
    exact hmap ⟨MainDesign.absPt z, ⟨z, hzT, rfl⟩, rfl⟩
  have hw₀_fib : w₀ ∈ fiber S.X.set pt0 := by
    rwa [absSet_eq_fiber] at hw₀_abs
  have hw₀_append : Fin.append pt0 w₀ ∈ S.X.set := hw₀_fib
  have hw₀_zero : fnpFibre S pt0 w₀ = 0 := fnpFibre_eq_zero_of_mem S hS pt0 w₀ hw₀_fib
  -- the `S`-side level set: surjectivity and kernel dimension
  have hSsurj : (fderiv ℝ (fnpFibre S pt0) w₀).range = ⊤ :=
    fnpFibre_range_eq_top_of_rank S pt0 w₀ (Work.WilE5.Stratum.good_rank hS hw₀_append)
  have hSker : Module.finrank ℝ (fderiv ℝ (fnpFibre S pt0) w₀).ker = N - S.j :=
    fnpFinrank_ker S pt0 w₀ hSsurj
  -- the `T`-side equation map: surjectivity, kernel and its dimension
  have hTsurj : (fderiv ℝ (eqMap T) z).range = ⊤ := range_fderiv_eqMap_eq_top T hT hzT
  have hTkerjac : (fderiv ℝ (eqMap T) z).ker = LinearMap.ker (MainDesign.jac T z) :=
    ker_fderiv_eqMap_eq_ker_jac T z
  have hTdim : Module.finrank ℝ (fderiv ℝ (eqMap T) z).ker = (0 + N2) - T.j := by
    simpa using finrank_ker_eqMap T hT hzT
  haveI : CompleteSpace ↥((fderiv ℝ (eqMap T) z).ker) :=
    (fderiv ℝ (eqMap T) z).isClosed_ker.completeSpace_coe
  -- the chart of the `T`-level set at `z`
  obtain ⟨γT, VT, WT, χT, hVTopen, hWTopen, h0VT, hzWT, hγT0, hγTan, hγTVTW, hγTlev, hγTsurj,
    hγTinjOn, hγTrange, hχTan, hχTinv⟩ :=
    Work.WilE7.Nondrop.analyticLevelSetChartRange (eqMap T) z
      (fun y => analyticAt_eqMap T y) hTsurj
  -- the parametrisation of `absSet T` near `absPt z`
  set γ : ↥((fderiv ℝ (eqMap T) z).ker) → (Fin N → ℝ) := fun s => Lhat (γT s) with hγ
  have hγ0 : γ 0 = w₀ := by
    rw [show γ 0 = Lhat (γT 0) from rfl, hγT0, hLhat_apply, hw₀]
  have hγan : AnalyticAt ℝ γ 0 := by
    have h := (Lhat.analyticAt (γT 0)).comp hγTan
    simpa [hγ, Function.comp_def] using h
  -- injectivity of the differential of the chart
  have hγTinj : Function.Injective (fderiv ℝ γT 0) := by
    have hker : Module.finrank ℝ (LinearMap.ker ((fderiv ℝ γT 0 :
        ↥((fderiv ℝ (eqMap T) z).ker) →L[ℝ] (Fin (0 + N2) → ℝ)) :
        ↥((fderiv ℝ (eqMap T) z).ker) →ₗ[ℝ] (Fin (0 + N2) → ℝ))) = 0 := by
      have h1 := LinearMap.finrank_range_add_finrank_ker ((fderiv ℝ γT 0 :
          ↥((fderiv ℝ (eqMap T) z).ker) →L[ℝ] (Fin (0 + N2) → ℝ)) :
          ↥((fderiv ℝ (eqMap T) z).ker) →ₗ[ℝ] (Fin (0 + N2) → ℝ))
      rw [hγTrange] at h1
      omega
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)
  -- injectivity of the differential of `γ`
  have hγder : fderiv ℝ γ 0 = Lhat.comp (fderiv ℝ γT 0) := by
    have h := fderiv_comp (x := (0 : ↥((fderiv ℝ (eqMap T) z).ker))) (f := γT)
      (g := fun w : Fin (0 + N2) → ℝ => Lhat w) Lhat.differentiableAt hγTan.differentiableAt
    rw [ContinuousLinearMap.fderiv] at h
    simpa [hγ, hγT0, Function.comp_def] using h
  have hγinj : Function.Injective (fderiv ℝ γ 0) := by
    intro s s' hss'
    have h1 : Lhat ((fderiv ℝ γT 0) s) = Lhat ((fderiv ℝ γT 0) s') := by
      simpa [hγder, ContinuousLinearMap.comp_apply] using hss'
    have h2 : (fderiv ℝ γT 0) (s - s') = (fderiv ℝ γT 0) s - (fderiv ℝ γT 0) s' :=
      map_sub _ _ _
    have h3 : Lhat ((fderiv ℝ γT 0) (s - s')) = 0 := by
      rw [h2, map_sub, h1, sub_self]
    have h4 : (fderiv ℝ γT 0) (s - s') ∈ LinearMap.ker (MainDesign.jac T z) := by
      rw [← hTkerjac]
      have hmem : (fderiv ℝ γT 0) (s - s') ∈ (fderiv ℝ γT 0).range :=
        LinearMap.mem_range.mpr ⟨s - s', rfl⟩
      rwa [hγTrange] at hmem
    have h5 : (fderiv ℝ γT 0) (s - s') = 0 :=
      hinj z hzT _ h4 (by rw [← hLhat_apply]; exact h3)
    have h6 : s - s' = 0 := hγTinj (by simpa using h5)
    exact sub_eq_zero.mp h6
  -- the level-set condition for `γ`
  have hlevel : ∀ᶠ s in nhds (0 : ↥((fderiv ℝ (eqMap T) z).ker)),
      fnpFibre S pt0 (γ s) = fnpFibre S pt0 w₀ := by
    have hloc : ∀ᶠ z' in nhds z, (∀ a, eaEval T.X.c (T.h a) z' = 0) → z' ∈ T.X.set :=
      (Work.WilE5.Stratum.good_local hT hzT).mono
        (fun z' h => h (Subsingleton.elim _ _))
    have hγTtend : Tendsto γT (nhds (0 : ↥((fderiv ℝ (eqMap T) z).ker))) (nhds z) := by
      have h := hγTan.continuousAt.tendsto
      rwa [hγT0] at h
    have hlev : ∀ᶠ s in nhds (0 : ↥((fderiv ℝ (eqMap T) z).ker)),
        eqMap T (γT s) = eqMap T z :=
      Filter.mem_of_superset (hVTopen.mem_nhds h0VT) (fun s hs => hγTlev s hs)
    have hmemT : ∀ᶠ s in nhds (0 : ↥((fderiv ℝ (eqMap T) z).ker)), γT s ∈ T.X.set := by
      filter_upwards [hγTtend.eventually hloc, hlev] with s hs1 hs2
      exact hs1 (fun a => by
        have h := congrFun hs2 a
        rw [eqMap_apply, eqMap_apply] at h
        rw [h]
        exact congrFun (eqMap_eq_zero_of_good T hT hzT) a)
    filter_upwards [hmemT] with s hs
    rw [hw₀_zero]
    show fnpFibre S pt0 (Lhat (γT s)) = 0
    rw [hLhat_apply]
    have hmem : L (MainDesign.absPt (γT s)) ∈ MainDesign.absSet S :=
      hmap ⟨MainDesign.absPt (γT s), ⟨γT s, hs, rfl⟩, rfl⟩
    have hfib : L (MainDesign.absPt (γT s)) ∈ fiber S.X.set pt0 := by
      rwa [absSet_eq_fiber S] at hmem
    exact fnpFibre_eq_zero_of_mem S hS pt0 _ hfib
  -- the dimension identity for the two level sets
  have hdimE : Module.finrank ℝ (fderiv ℝ (fnpFibre S pt0) w₀).ker
      = Module.finrank ℝ ↥((fderiv ℝ (eqMap T) z).ker) := by
    rw [hSker, hTdim, Nat.zero_add, hdim]
  -- the reference neighbourhood of `0` in the parameter space
  have hU₁ : MainDesign.absPt ⁻¹' U ∈ nhds z := by
    have hcont : Continuous (MainDesign.absPt (N := N2)) := by
      have h : (fun z : Fin (0 + N2) → ℝ => absPtCLM N2 z) = MainDesign.absPt := by
        funext z
        exact absPtCLM_apply z
      rw [← h]
      exact (absPtCLM N2).continuous
    exact hcont.continuousAt.preimage_mem_nhds (by simpa using hU)
  have hlocT : ∀ᶠ z' in nhds z, (∀ a, eaEval T.X.c (T.h a) z' = 0) → z' ∈ T.X.set :=
    (Work.WilE5.Stratum.good_local hT hzT).mono (fun z' h => h (Subsingleton.elim _ _))
  obtain ⟨W₀, hW₀mem, hW₀sub⟩ := Filter.eventually_iff_exists_mem.mp hlocT
  set A : Set ↥((fderiv ℝ (eqMap T) z).ker) :=
    VT ∩ γT ⁻¹' (MainDesign.absPt ⁻¹' U ∩ W₀) with hA
  have hAmem : A ∈ nhds (0 : ↥((fderiv ℝ (eqMap T) z).ker)) := by
    rw [hA]
    refine Filter.inter_mem (hVTopen.mem_nhds h0VT) ?_
    refine hγTan.continuousAt.preimage_mem_nhds ?_
    rw [hγT0]
    exact Filter.inter_mem hU₁ hW₀mem
  -- the covering conclusion
  obtain ⟨O, hO, hOprop⟩ := levelSet_subset_image_of_inj (fnpFibre S pt0) w₀
    (fnpFibre_analytic S pt0) hSsurj hγ0 hγan hγinj hdimE hlevel A hAmem
  refine Filter.mem_of_superset hO (fun w hw hwS => ?_)
  have hwfib : w ∈ fiber S.X.set pt0 := by rwa [absSet_eq_fiber] at hwS
  have hwzero : fnpFibre S pt0 w = 0 := fnpFibre_eq_zero_of_mem S hS pt0 w hwfib
  obtain ⟨s, hsA, hγs⟩ := hOprop w hw (by rw [hwzero, hw₀_zero])
  rw [hA] at hsA
  obtain ⟨hsV, hsUW⟩ := hsA
  obtain ⟨hsU, hsW⟩ := hsUW
  refine ⟨MainDesign.absPt (γT s), ⟨?_, hsU⟩, ?_⟩
  · exact ⟨γT s, hW₀sub (γT s) hsW (fun a => by
      have h := congrFun (hγTlev s hsV) a
      rw [eqMap_apply, eqMap_apply] at h
      rw [h]
      exact congrFun (eqMap_eq_zero_of_good T hT hzT) a), rfl⟩
  · rw [← hγs]
    show L (MainDesign.absPt (γT s)) = Lhat (γT s)
    exact (hLhat_apply (γT s)).symm

end Work.WilE7.DimAPI
