/-
  Area E7: the **non-drop half** of the frontier dimension drop (`Work.WilE7.frontier_nondrop`).

  Statement of the target: if `S`, `S'` are `Good` strata of `ℝ^{p+q}`, the set of `S'` lies in the
  fibrewise frontier of the set of `S`, and at a point `z ∈ S'.X.set` the *fibrewise* Jacobian of
  the equations of `S` still has the maximal rank `S.j` (the rank does not drop at the frontier
  point), then the fibre codimension strictly increases: `S.j < S'.j`.

  NOTE: the statement handed to us spells the frozen name `WilkiesDesign.E.eaD` as
  `WilkesDesign.E.eaD`; that identifier does not exist, so the statement as handed over does not
  elaborate by itself.  The file below provides `WilkesDesign.E.eaD` as an alias of
  `WilkiesDesign.E.eaD`, so the requested statement is reproduced verbatim (and elaborates).

  ## Proof

  Write `x = projFirst p q z`, `y = projSnd p q z` (so `z = (x,y)`) and let
  `F = fnpFibre S x`, `F' = fnpFibre S' x` be the fibre maps of the two strata (the tuples of
  their equations in the fibre coordinates).

  * At `z`, `∂_y S.h` has rank `S.j`, hence `dF_y` is surjective; by `Good`, `dF'_y` is
    surjective as well.
  * `S'.X.set` is contained in the fibrewise frontier of `S.X.set`, so near `y` every point of the
    fibre level set of `S'` is a limit point of the `S`-fibre, on which `F` vanishes; hence
    `F' = 0` implies `F = 0` near `y` (`fnpFibre_eventually`).
  * Parametrising the level set `{F' = 0}` near `y` by the kernel of `dF'_y`
    (`Nondrop.analyticLevelSetChartRange`) and differentiating `F` along that parametrisation with
    the chain rule exhibits `ker dF'_y` as a submodule of `ker dF_y`; rank–nullity then gives
    `q - S'.j ≤ q - S.j`, i.e. `S.j ≤ S'.j`.
  * If `S.j = S'.j` then `{F' = 0} ⊆ {F = 0}` near `y` and the kernels have equal dimension, so by
    `Nondrop.levelSet_eq_near_of_subset` also `{F = 0} ⊆ {F' = 0}` near `y`.  But then a point of
    the `S`-fibre close to `y` (which exists because `y` lies in the closure of that fibre, while
    the fibres of `S` and `S'` are disjoint) would lie in the `S'`-set — a contradiction.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.FiberCutDefs
import Submission.Work.WilE7.cover_step
import Submission.Work.WilE5.Basic
import Submission.Work.WilE7.Nondrop.FibreCalc
import Submission.Work.WilE7.Nondrop.analyticLevelSetChartRange
import Submission.Work.WilE7.Nondrop.levelSet_eq_near_of_subset

set_option autoImplicit false

noncomputable section
open Classical Filter Topology
open scoped Topology
namespace Work.WilE7

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! The statement handed to us spells the frozen name `WilkiesDesign.E.eaD` as
`WilkesDesign.E.eaD`.  That identifier does not exist, so the statement as handed over does not
elaborate.  `WilkesDesign.E.eaD` below is an alias for the (only) intended function
`WilkiesDesign.E.eaD`; with it, the requested statement elaborates verbatim. -/
namespace WilkesDesign

namespace E

/-- Alias of `WilkiesDesign.E.eaD` (the statement's spelling). -/
abbrev eaD {k r : ℕ} (c : WilkiesDesign.E.EAChain k r) (i : Fin k)
    (Q : WilkiesDesign.E.EAPoly k r) : WilkiesDesign.E.EAPoly k r :=
  WilkiesDesign.E.eaD c i Q

end E

end WilkesDesign

/-! ## The two analytic ingredients (proved in parallel, in `Submission/Work/WilE7/Nondrop/`) -/

/-- The fibre chart of the delegated lemma `Work.WilE7.Nondrop.analyticLevelSetChartRange`. -/
private theorem fnp_chartRange {n k : ℕ} (g : (Fin n → ℝ) → (Fin k → ℝ)) (p : Fin n → ℝ)
    (hg : ∀ q, AnalyticAt ℝ g q) (hsurj : (fderiv ℝ g p).range = ⊤) :
    ∃ (γ : (fderiv ℝ g p).ker → (Fin n → ℝ)) (V : Set (fderiv ℝ g p).ker)
      (U : Set (Fin n → ℝ)) (χ : (Fin n → ℝ) → (fderiv ℝ g p).ker),
      IsOpen V ∧ IsOpen U ∧ (0 : (fderiv ℝ g p).ker) ∈ V ∧ p ∈ U ∧ γ 0 = p ∧
      AnalyticAt ℝ γ 0 ∧ (∀ v ∈ V, γ v ∈ U) ∧ (∀ v ∈ V, g (γ v) = g p) ∧
      (∀ y ∈ U, g y = g p → ∃ v ∈ V, γ v = y) ∧ Set.InjOn γ V ∧
      (fderiv ℝ γ 0).range = (fderiv ℝ g p).ker ∧
      AnalyticAt ℝ χ p ∧ (∀ y ∈ U, g y = g p → χ y ∈ V ∧ γ (χ y) = y) :=
  Nondrop.analyticLevelSetChartRange g p hg hsurj

/-- The level-set equality of the delegated lemma `Work.WilE7.Nondrop.levelSet_eq_near_of_subset`. -/
private theorem fnp_levelSet {n k k' : ℕ} (g : (Fin n → ℝ) → (Fin k → ℝ))
    (g' : (Fin n → ℝ) → (Fin k' → ℝ)) (p : Fin n → ℝ)
    (hg : ∀ y, AnalyticAt ℝ g y) (hg' : ∀ y, AnalyticAt ℝ g' y)
    (hgp : g p = 0) (hg'p : g' p = 0)
    (hs : (fderiv ℝ g p).range = ⊤) (hs' : (fderiv ℝ g' p).range = ⊤)
    (hdim : Module.finrank ℝ (fderiv ℝ g' p).ker = Module.finrank ℝ (fderiv ℝ g p).ker)
    (hsub : ∀ᶠ y in nhds p, g' y = 0 → g y = 0) :
    ∀ᶠ y in nhds p, g y = 0 → g' y = 0 :=
  Nondrop.levelSet_eq_near_of_subset g g' p hg hg' hgp hg'p hs hs' hdim hsub

/-! ## The main theorem -/

theorem frontier_nondrop_proved {p q : ℕ} (S S' : WilkiesDesign.E.Stratum p q)
    (hGood : S.Good) (hGood' : S'.Good)
    (hsub : S'.X.set ⊆ WilkiesDesign.E.fiberClosure S.X.set \ S.X.set)
    (z : Fin (p + q) → ℝ) (hz : z ∈ S'.X.set)
    (hrank : (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
      WilkiesDesign.E.eaEval S.X.c (WilkesDesign.E.eaD S.X.c (Fin.natAdd p l) (S.h a)) z).rank = S.j) :
    S.j < S'.j := by
  set x : Fin p → ℝ := projFirst p q z with hx
  set y : Fin q → ℝ := projSnd p q z with hy
  have hzy : Fin.append x y = z := by
    rw [hx, hy]
    exact Nondrop.fnpAppend_proj z
  -- full row rank of the fibrewise Jacobian of `S` at `z`, in fibre coordinates
  have hrankx : (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
      eaEval S.X.c (eaD S.X.c (Work.WilE5.yDir p l) (S.h a)) (Fin.append x y)).rank = S.j := by
    rw [hzy]
    simpa only [WilkesDesign.E.eaD, Work.WilE5.yDir] using hrank
  have hrankx' : (Matrix.of fun (b : Fin S'.j) (l : Fin q) =>
      eaEval S'.X.c (eaD S'.X.c (Work.WilE5.yDir p l) (S'.h b)) (Fin.append x y)).rank = S'.j := by
    have h := Work.WilE5.Stratum.good_rank (S := S') hGood' hz
    rw [← hzy] at h
    exact h
  have htop : (fderiv ℝ (Nondrop.fnpFibre S x) y).range = ⊤ :=
    Nondrop.fnpFibre_range_eq_top_of_rank S x y hrankx
  have htop' : (fderiv ℝ (Nondrop.fnpFibre S' x) y).range = ⊤ :=
    Nondrop.fnpFibre_range_eq_top_of_rank S' x y hrankx'
  -- the fibrewise frontier of `S` is approached by `S'`: the `S`-equations vanish on the
  -- fibre level set of `S'` near `y`
  have hvan : ∀ᶠ y' in nhds y, Nondrop.fnpFibre S' x y' = 0 → Nondrop.fnpFibre S x y' = 0 :=
    Nondrop.fnpFibre_eventually S S' hGood hGood' hsub x y (by rw [hzy]; exact hz)
  -- `y` lies in the closure of the `S`-fibre over `x`
  have hcl : y ∈ closure (fiber S.X.set x) := by
    have h1 : projFirst p q z = x := hx.symm
    have h2 : projSnd p q z = y := hy.symm
    have h := (hsub hz).1
    simpa [fiberClosure, h1, h2] using h
  -- both fibre maps vanish at `y`
  have hg'p : Nondrop.fnpFibre S' x y = 0 := by
    refine Nondrop.fnpFibre_eq_zero_of_mem S' hGood' x y ?_
    show Fin.append x y ∈ S'.X.set
    rw [hzy]
    exact hz
  have hgp : Nondrop.fnpFibre S x y = 0 :=
    Nondrop.fnpFibre_eq_zero_of_mem_closure S hGood x y hcl
  -- ## Step 1: `S.j ≤ S'.j`
  have hle : S.j ≤ S'.j := by
    obtain ⟨γ, V, U, χ, hVo, hUo, h0V, hyU, hγ0, hγan, hγVU, hγsol, hγsurj, hγinj, hγrange,
      hχan, hχinv⟩ :=
      fnp_chartRange (Nondrop.fnpFibre S' x) y (Nondrop.fnpFibre_analytic S' x) htop'
    -- `S` vanishes along the parametrisation of the `S'`-level set
    have hcomp0 : (Nondrop.fnpFibre S x) ∘ γ =ᶠ[nhds 0] 0 := by
      have hvan' : ∀ᶠ y' in nhds (γ 0),
          Nondrop.fnpFibre S' x y' = 0 → Nondrop.fnpFibre S x y' = 0 := by
        simpa only [hγ0] using hvan
      filter_upwards [(show Tendsto γ (nhds 0) (nhds (γ 0)) from hγan.continuousAt).eventually hvan',
        hVo.mem_nhds h0V] with v hv hvV
      exact hv (by rw [hγsol v hvV, hg'p])
    -- hence the composite has zero derivative at `0`
    have hzero : fderiv ℝ ((Nondrop.fnpFibre S x) ∘ γ) 0 = 0 := by
      rw [Filter.EventuallyEq.fderiv_eq hcomp0]
      simp
    -- the chain rule identifies it with `dF_y ∘ dγ_0`
    have hcr := fderiv_comp (f := γ) (g := Nondrop.fnpFibre S x)
      (x := (0 : (fderiv ℝ (Nondrop.fnpFibre S' x) y).ker))
      (by rw [hγ0]; exact (Nondrop.fnpFibre_analytic S x y).differentiableAt)
      hγan.differentiableAt
    rw [hγ0] at hcr
    rw [hcr] at hzero
    have hchain : (fderiv ℝ (Nondrop.fnpFibre S x) y) ∘SL (fderiv ℝ γ 0) = 0 := hzero
    have hpoint : ∀ v, (fderiv ℝ (Nondrop.fnpFibre S x) y) ((fderiv ℝ γ 0) v) = 0 := by
      intro v
      have h : ((fderiv ℝ (Nondrop.fnpFibre S x) y) ∘SL (fderiv ℝ γ 0)) v = 0 := by
        rw [hchain]
        simp
      rwa [ContinuousLinearMap.comp_apply] at h
    -- the fibre kernel of `S'` is the range of `dγ_0`, hence sits in the fibre kernel of `S`
    have hker_le : (fderiv ℝ (Nondrop.fnpFibre S' x) y).ker
        ≤ (fderiv ℝ (Nondrop.fnpFibre S x) y).ker := by
      rw [← hγrange]
      intro u hu
      rw [show (fderiv ℝ γ 0).range
            = LinearMap.range ((fderiv ℝ γ 0) :
                (fderiv ℝ (Nondrop.fnpFibre S' x) y).ker →ₗ[ℝ] (Fin q → ℝ)) from rfl,
        LinearMap.mem_range] at hu
      obtain ⟨v, rfl⟩ := hu
      rw [show (fderiv ℝ (Nondrop.fnpFibre S x) y).ker
            = LinearMap.ker ((fderiv ℝ (Nondrop.fnpFibre S x) y) :
                (Fin q → ℝ) →ₗ[ℝ] (Fin S.j → ℝ)) from rfl,
        LinearMap.mem_ker]
      exact hpoint v
    have h1 : Module.finrank ℝ (fderiv ℝ (Nondrop.fnpFibre S' x) y).ker
        ≤ Module.finrank ℝ (fderiv ℝ (Nondrop.fnpFibre S x) y).ker :=
      Submodule.finrank_mono hker_le
    have h2 : Module.finrank ℝ (fderiv ℝ (Nondrop.fnpFibre S' x) y).ker = q - S'.j :=
      Nondrop.fnpFinrank_ker S' x y htop'
    have h3 : Module.finrank ℝ (fderiv ℝ (Nondrop.fnpFibre S x) y).ker = q - S.j :=
      Nondrop.fnpFinrank_ker S x y htop
    have h4 : S.j ≤ q := Nondrop.fnpRank_le S x y htop
    have h5 : S'.j ≤ q := Nondrop.fnpRank_le S' x y htop'
    omega
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  -- ## Step 2: the rank cannot stay constant; the two fibre level sets coincide
  exfalso
  have hdim : Module.finrank ℝ (fderiv ℝ (Nondrop.fnpFibre S' x) y).ker
      = Module.finrank ℝ (fderiv ℝ (Nondrop.fnpFibre S x) y).ker := by
    rw [Nondrop.fnpFinrank_ker S' x y htop', Nondrop.fnpFinrank_ker S x y htop, heq]
  have hgot : ∀ᶠ y' in nhds y, Nondrop.fnpFibre S x y' = 0 → Nondrop.fnpFibre S' x y' = 0 :=
    fnp_levelSet (Nondrop.fnpFibre S x) (Nondrop.fnpFibre S' x) y (Nondrop.fnpFibre_analytic S x)
      (Nondrop.fnpFibre_analytic S' x) hgp hg'p htop htop' hdim hvan
  -- the `Good`-fullness of `S'` at `z`, transported to the fibre over `x`
  have hcont : Tendsto (fun y' : Fin q → ℝ => Fin.append x y') (nhds y) (nhds z) := by
    rw [← hzy]
    exact (Nondrop.fnpAppend_hasFDerivAt x y).continuousAt
  have hfull : ∀ᶠ y' in nhds y, Nondrop.fnpFibre S x y' = 0 →
      Nondrop.fnpFibre S' x y' = 0 ∧ Fin.append x y' ∈ S'.X.set := by
    filter_upwards [hgot, hcont.eventually ((hGood' z hz).2.2)] with y' hy1 hy2
    intro h0
    refine ⟨hy1 h0, ?_⟩
    refine hy2 ?_ ?_
    · have h1 : projFirst p q (Fin.append x y') = x := by
        funext i; simp [projFirst, Fin.append_left]
      rw [h1, hx]
    · intro b
      exact congrFun (hy1 h0) b
  -- a point of the `S`-fibre close to `y` that satisfies the two `eventual` conditions
  obtain ⟨w, hwP, hwW⟩ := mem_closure_iff_nhds.mp hcl
    {y' : Fin q → ℝ | Nondrop.fnpFibre S x y' = 0 →
      Nondrop.fnpFibre S' x y' = 0 ∧ Fin.append x y' ∈ S'.X.set} hfull
  have hmemS : Fin.append x w ∈ S.X.set := hwW
  have hFw : Nondrop.fnpFibre S x w = 0 := by
    refine Nondrop.fnpFibre_eq_zero_of_mem S hGood x w ?_
    show Fin.append x w ∈ S.X.set
    exact hwW
  obtain ⟨-, hmem'⟩ := hwP hFw
  exact (hsub hmem').2 hmemS

end Work.WilE7
