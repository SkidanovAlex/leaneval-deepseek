import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.projFirst_fiberClosure
import Submission.Work.WilE7.eventually_mem_fiber_of_good
import Submission.Work.WilE7.Auxiliary.fibreFDeriv
import Submission.Work.WilE7.Auxiliary.rangePiEqTopOfRank
import Submission.Work.WilE5.Basic
import Submission.Work.WilE5.Strat.flatConormalTools
import Submission.Work.WilE9.Ift.AppendCLM

set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped Topology
open Classical

namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E

/-! ## An analytic chart of a full-rank level set

This is the implicit function theorem in the form used below: a level set `g = g p` of an
analytic map `g` whose derivative at `p` is surjective is, near `p`, the image of an open subset
of the kernel of the derivative.  We keep both the parametrisation `γ` and the "inverse" `σ`
(continuous, `σ p = 0`), so that every point of the level set near `p` is `γ v` with `v = σ y`
*close to* `σ p = 0`.  (A self-contained copy of `Work.WilE7.Aux.analyticChart`.) -/

theorem fgAnalyticChart {n k : ℕ} (g : (Fin n → ℝ) → (Fin k → ℝ)) (p : Fin n → ℝ)
    (hg : ∀ y, AnalyticAt ℝ g y) (hsurj : (fderiv ℝ g p).range = ⊤) :
    ∃ (γ : (fderiv ℝ g p).ker → (Fin n → ℝ)) (σ : (Fin n → ℝ) → (fderiv ℝ g p).ker)
      (V : Set (fderiv ℝ g p).ker) (U : Set (Fin n → ℝ)),
      IsOpen V ∧ IsOpen U ∧ (0 : (fderiv ℝ g p).ker) ∈ V ∧ p ∈ U ∧ γ 0 = p ∧
      AnalyticAt ℝ γ 0 ∧ ContinuousOn γ V ∧ Continuous σ ∧ σ p = 0 ∧
      (∀ v ∈ V, γ v ∈ U ∧ g (γ v) = g p) ∧
      (∀ y ∈ U, g y = g p → σ y ∈ V ∧ γ (σ y) = y) := by
  let f' : (Fin n → ℝ) →L[ℝ] (Fin k → ℝ) := fderiv ℝ g p
  have hgp : HasStrictFDerivAt g f' p := (hg p).hasStrictFDerivAt
  have hker : f'.ker.ClosedComplemented :=
    f'.ker_closedComplemented_of_finiteDimensional_range
  haveI : CompleteSpace f'.ker := f'.isClosed_ker.completeSpace_coe
  let C : (Fin n → ℝ) →L[ℝ] f'.ker := Classical.choose hker
  let φ : ImplicitFunctionData ℝ (Fin n → ℝ) (Fin k → ℝ) f'.ker :=
    HasStrictFDerivAt.implicitFunctionDataOfComplemented g f' hgp hsurj hker
  have hleft : ∀ x, φ.leftFun x = g x := fun x => rfl
  have hright : ∀ x, φ.rightFun x = C (x - p) := fun x => rfl
  have hpt : φ.pt = p := rfl
  -- the map `x ↦ (g x, C (x - p))` is analytic at `p`
  have hC_an : AnalyticAt ℝ (fun x : Fin n → ℝ => C (x - p)) p := by
    have h3 := (C.analyticAt p).sub (analyticAt_const (v := C p) (x := p))
    have heq : (⇑C) - (fun _ : Fin n → ℝ => C p) = (fun x : Fin n → ℝ => C (x - p)) := by
      funext x; simp
    rwa [heq] at h3
  have hΦ : AnalyticAt ℝ φ.prodFun p := by
    have h := (hg p).prod hC_an
    have heq : φ.prodFun = (fun x : Fin n → ℝ => (g x, C (x - p))) := by
      funext x
      rw [ImplicitFunctionData.prodFun_apply, hleft, hright]
    rw [heq]
    exact h
  -- its derivative is the linear equivalence `x ↦ (f' x, C x)`
  let e : (Fin n → ℝ) ≃L[ℝ] (Fin k → ℝ) × f'.ker :=
    φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv φ.range_leftDeriv
      φ.range_rightDeriv φ.isCompl_ker
  have hfderiv : fderiv ℝ φ.prodFun p =
      (e : (Fin n → ℝ) →L[ℝ] (Fin k → ℝ) × f'.ker) := by
    have h := φ.hasStrictFDerivAt.hasFDerivAt.fderiv
    rw [hpt] at h
    exact h
  -- the inverse of a local analytic homeomorphism is analytic
  have hsymm : AnalyticAt ℝ (⇑φ.toOpenPartialHomeomorph.symm)
      ((g p, (0 : f'.ker)) : (Fin k → ℝ) × f'.ker) := by
    have h1 : AnalyticAt ℝ (⇑φ.toOpenPartialHomeomorph) p := by
      simpa [ImplicitFunctionData.toOpenPartialHomeomorph_coe] using hΦ
    have h2 : fderiv ℝ (⇑φ.toOpenPartialHomeomorph) p = e := by
      simpa [ImplicitFunctionData.toOpenPartialHomeomorph_coe] using hfderiv
    have h3 := φ.toOpenPartialHomeomorph.analyticAt_symm'
      (φ.pt_mem_toOpenPartialHomeomorph_source) h1 h2
    simpa [ImplicitFunctionData.toOpenPartialHomeomorph_apply, hleft, hright, hpt] using h3
  let γ : f'.ker → (Fin n → ℝ) := fun v => φ.toOpenPartialHomeomorph.symm (g p, v)
  have hγ_an : AnalyticAt ℝ γ 0 := by
    have h2 : AnalyticAt ℝ (fun v : f'.ker => ((g p, v) : (Fin k → ℝ) × f'.ker)) 0 := by
      have h := (analyticAt_const (v := g p) (x := (0 : f'.ker))).prod
        (analyticAt_id (𝕜 := ℝ) (z := (0 : f'.ker)))
      simpa using h
    simpa [γ, Function.comp_def] using hsymm.comp h2
  let V : Set f'.ker := {v | ((g p, v) : (Fin k → ℝ) × f'.ker) ∈ φ.toOpenPartialHomeomorph.target}
  let U : Set (Fin n → ℝ) := φ.toOpenPartialHomeomorph.source
  let σ : (Fin n → ℝ) → f'.ker := fun y => C (y - p)
  have hTarget : ((g p, (0 : f'.ker)) : (Fin k → ℝ) × f'.ker) ∈
      φ.toOpenPartialHomeomorph.target := by
    have h := φ.toOpenPartialHomeomorph.map_source (φ.pt_mem_toOpenPartialHomeomorph_source)
    simpa [ImplicitFunctionData.toOpenPartialHomeomorph_apply, hleft, hright, hpt] using h
  have hσcont : Continuous σ := by
    have h : Continuous (fun y : Fin n → ℝ => C (y - p)) := by
      apply Continuous.comp C.continuous
      exact continuous_id.sub continuous_const
    exact h
  have hσp : σ p = 0 := by
    show C (p - p) = 0
    rw [sub_self]
    exact map_zero C
  have hγcont : ContinuousOn γ V := by
    have hf : Continuous (fun v : f'.ker => ((g p, v) : (Fin k → ℝ) × f'.ker)) :=
      continuous_const.prodMk continuous_id
    have h1 : ContinuousOn (⇑φ.toOpenPartialHomeomorph.symm)
        φ.toOpenPartialHomeomorph.target := φ.toOpenPartialHomeomorph.continuousOn_invFun
    exact h1.comp hf.continuousOn (fun v hv => hv)
  refine ⟨γ, σ, V, U, ?_, ?_, ?_, ?_, ?_, hγ_an, hγcont, hσcont, hσp, ?_, ?_⟩
  · exact φ.toOpenPartialHomeomorph.open_target.preimage
      (continuous_const.prodMk continuous_id)
  · exact φ.toOpenPartialHomeomorph.open_source
  · exact hTarget
  · simpa [hpt] using φ.pt_mem_toOpenPartialHomeomorph_source
  · show φ.toOpenPartialHomeomorph.symm (g p, (0 : f'.ker)) = p
    have h0 : ((g p, (0 : f'.ker)) : (Fin k → ℝ) × f'.ker) = φ.toOpenPartialHomeomorph p := by
      rw [ImplicitFunctionData.toOpenPartialHomeomorph_apply]
      simp [hleft, hright]
    rw [h0]
    exact φ.toOpenPartialHomeomorph.left_inv (φ.pt_mem_toOpenPartialHomeomorph_source)
  · intro v hv
    constructor
    · exact φ.toOpenPartialHomeomorph.map_target hv
    · have h := congr_arg Prod.fst (φ.toOpenPartialHomeomorph.right_inv hv)
      simpa [ImplicitFunctionData.toOpenPartialHomeomorph_apply, hleft, hright, γ] using h
  · intro y hy hgy
    have hEq : ((g p, C (y - p)) : (Fin k → ℝ) × f'.ker) = φ.toOpenPartialHomeomorph y := by
      rw [ImplicitFunctionData.toOpenPartialHomeomorph_apply]
      simp [hleft, hright, hgy]
    constructor
    · show ((g p, C (y - p)) : (Fin k → ℝ) × f'.ker) ∈ φ.toOpenPartialHomeomorph.target
      rw [hEq]
      exact φ.toOpenPartialHomeomorph.map_source hy
    · show φ.toOpenPartialHomeomorph.symm (g p, C (y - p)) = y
      rw [hEq]
      exact φ.toOpenPartialHomeomorph.left_inv hy

/-! ## The fibre level-set map of a stratum -/

/-- The fibre map of a stratum over a base point. -/
def fgFibreMap {p q : ℕ} (S : Stratum p q) (x : Fin p → ℝ) : (Fin q → ℝ) → (Fin S.j → ℝ) :=
  fun y a => eaEval S.X.c (S.h a) (Fin.append x y)

/-- The fibre map of a stratum is analytic. -/
lemma analyticAt_fgFibreMap {p q : ℕ} (S : Stratum p q) (x : Fin p → ℝ) (y : Fin q → ℝ) :
    AnalyticAt ℝ (fgFibreMap S x) y := by
  unfold fgFibreMap
  refine AnalyticAt.pi (fun a => ?_)
  have happ : AnalyticAt ℝ (fun y' : Fin q → ℝ => Fin.append x y') y := by
    have h1 : (fun y' : Fin q → ℝ => Fin.append x y')
        = (Work.WilE9.Ift.appendCLM p q) ∘ (fun y' : Fin q → ℝ => (x, y')) := by
      funext y'
      simp [Function.comp_apply, Work.WilE9.Ift.appendCLM_apply]
    rw [h1]
    exact ((Work.WilE9.Ift.appendCLM p q).analyticAt (x, y)).comp
      ((analyticAt_const (v := x)).prod analyticAt_id)
  exact (Work.WilE5.Strat.analyticAt_eaEval S.X.c (S.h a) (Fin.append x y)).comp happ

/-- At a point of a `Good` stratum the fibre derivative of the fibre map is surjective: the
fibrewise Jacobian of the defining equations has full row rank `S.j`. -/
lemma range_fderiv_fgFibreMap {p q : ℕ} (S : Stratum p q) (hGood : S.Good) (x : Fin p → ℝ)
    (y : Fin q → ℝ) (hy : Fin.append x y ∈ S.X.set) :
    (fderiv ℝ (fgFibreMap S x) y).range = ⊤ := by
  have hfirst : projFirst p q (Fin.append x y) = x := by
    funext i; simp [projFirst, Fin.append_left]
  have hsecond : projSnd p q (Fin.append x y) = y := by
    funext i; simp [projSnd, Fin.append_right]
  have h1 := Work.WilE7.Aux.fibreFDeriv S.X.c S.h (Fin.append x y)
  rw [hfirst, hsecond] at h1
  have h1' : fderiv ℝ (fgFibreMap S x) y
      = ContinuousLinearMap.pi (fun a : Fin S.j => (∑ l : Fin q,
          eaEval S.X.c (eaD S.X.c (Work.WilE5.yDir p l) (S.h a)) (Fin.append x y) •
            (ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ))) := h1
  rw [h1']
  exact Work.WilE7.Aux.rangePiEqTopOfRank
    (fun (a : Fin S.j) (l : Fin q) =>
      eaEval S.X.c (eaD S.X.c (Work.WilE5.yDir p l) (S.h a)) (Fin.append x y))
    (Work.WilE5.Stratum.good_rank hGood hy)

/-! ## The germ of a `Good` stratum's fibre is connected to its component -/

/-- **The fibre of a `Good` stratum is locally connected to its component.**  At a point `z` of a
`Good` stratum `S`, the fibre of `S.X.set` over `projFirst p q z` is locally, near `projSnd p q z`,
equal to the level set of the fibre map, which is a submersion (the fibrewise Jacobian of `S.h`
has full row rank `S.j`).  The implicit function theorem (`fgAnalyticChart`) exhibits the level
set near `projSnd p q z` as the preconnected image `γ '' (ball 0 δ)` of a ball in the kernel of
the derivative, and every point of the level set close to `projSnd p q z` is of the form `γ v`
with `v = σ y` close to `σ (projSnd p q z) = 0`, hence lies in that preconnected image. -/
theorem fiber_germ_subset_component {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (hGood : S.Good)
    (z : Fin (p + q) → ℝ) (hz : z ∈ S.X.set) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y' : Fin q → ℝ, dist y' (WilkiesDesign.E.projSnd p q z) < ε →
      y' ∈ WilkiesDesign.E.fiber S.X.set (WilkiesDesign.E.projFirst p q z) →
      y' ∈ connectedComponentIn
        (WilkiesDesign.E.fiber S.X.set (WilkiesDesign.E.projFirst p q z))
        (WilkiesDesign.E.projSnd p q z) := by
  classical
  have hsplit : Fin.append (projFirst p q z) (projSnd p q z) = z := append_projFirst_projSnd z
  have hzS : Fin.append (projFirst p q z) (projSnd p q z) ∈ S.X.set := by
    rw [hsplit]; exact hz
  -- the fibre level-set map
  let g : (Fin q → ℝ) → (Fin S.j → ℝ) := fgFibreMap S (projFirst p q z)
  have hgz : g (projSnd p q z) = 0 := by
    funext a
    dsimp only [g, fgFibreMap]
    rw [hsplit]
    exact Work.WilE5.Stratum.good_eqs hGood hz a
  have hgan : ∀ y, AnalyticAt ℝ g y := fun y => analyticAt_fgFibreMap S (projFirst p q z) y
  have hsurj : (fderiv ℝ g (projSnd p q z)).range = ⊤ :=
    range_fderiv_fgFibreMap S hGood (projFirst p q z) (projSnd p q z) hzS
  -- the implicit-function chart of the level set `g = g (projSnd p q z)`
  obtain ⟨γ, σ, V, U, hVo, hUo, h0V, hy0U, hγ0, hγan, hγcont, hσcont, hσ0, hVg, hσγ⟩ :=
    fgAnalyticChart g (projSnd p q z) hgan hsurj
  -- near `projSnd p q z` the fibre is the level set of `g`
  have hevfib : ∀ᶠ y' in 𝓝 (projSnd p q z),
      (∀ a, eaEval S.X.c (S.h a) (Fin.append (projFirst p q z) y') = 0) →
      y' ∈ fiber S.X.set (projFirst p q z) :=
    eventually_mem_fiber_of_good S hGood (projFirst p q z) (projSnd p q z) hzS
  -- radii: `r₁` for `U`, `r₂` for the "fibre = level set" neighbourhood, `δ` for the chart
  obtain ⟨r₁, hr₁pos, hr₁⟩ := Metric.isOpen_iff.mp hUo (projSnd p q z) hy0U
  obtain ⟨r₂, hr₂pos, hr₂⟩ := Metric.eventually_nhds_iff.mp hevfib
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ :=
    Metric.isOpen_iff.mp hVo (0 : (fderiv ℝ g (projSnd p q z)).ker) h0V
  have hballγ : Metric.ball (projSnd p q z) (min r₁ r₂) ∈ 𝓝 (γ 0) := by
    rw [hγ0]
    exact Metric.ball_mem_nhds (projSnd p q z) (lt_min hr₁pos hr₂pos)
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ :=
    Metric.mem_nhds_iff.mp (hγan.continuousAt.preimage_mem_nhds hballγ)
  let δ : ℝ := min δ₁ δ₂
  have hδpos : 0 < δ := lt_min hδ₁pos hδ₂pos
  have hballσ : Metric.ball (0 : (fderiv ℝ g (projSnd p q z)).ker) δ ∈
      𝓝 (σ (projSnd p q z)) := by
    rw [hσ0]
    exact Metric.ball_mem_nhds (0 : (fderiv ℝ g (projSnd p q z)).ker) hδpos
  obtain ⟨ε₀, hε₀pos, hε₀⟩ :=
    Metric.mem_nhds_iff.mp (hσcont.continuousAt.preimage_mem_nhds hballσ)
  -- the preconnected piece of the level set through the fibre point
  have hWpre : IsPreconnected (Metric.ball (0 : (fderiv ℝ g (projSnd p q z)).ker) δ) :=
    (convex_ball (0 : (fderiv ℝ g (projSnd p q z)).ker) δ).isPreconnected
  have hWV : Metric.ball (0 : (fderiv ℝ g (projSnd p q z)).ker) δ ⊆ V := by
    intro v hv
    exact hδ₁ (Metric.mem_ball.mpr
      (lt_of_lt_of_le (Metric.mem_ball.mp hv) (min_le_left δ₁ δ₂)))
  have hγWpre : IsPreconnected (γ '' Metric.ball (0 : (fderiv ℝ g (projSnd p q z)).ker) δ) :=
    hWpre.image γ (hγcont.mono hWV)
  have hγWfib : γ '' Metric.ball (0 : (fderiv ℝ g (projSnd p q z)).ker) δ
      ⊆ fiber S.X.set (projFirst p q z) := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨-, hgv⟩ := hVg v (hWV hv)
    have hdist : dist (γ v) (projSnd p q z) < r₂ :=
      lt_of_lt_of_le (Metric.mem_ball.mp (hδ₂ (Metric.mem_ball.mpr
        (lt_of_lt_of_le (Metric.mem_ball.mp hv) (min_le_right δ₁ δ₂))))) (min_le_right r₁ r₂)
    exact hr₂ hdist (fun a => congrFun (hgv.trans hgz) a)
  have hy0mem : projSnd p q z ∈ γ '' Metric.ball (0 : (fderiv ℝ g (projSnd p q z)).ker) δ :=
    ⟨0, Metric.mem_ball.mpr (by simpa using hδpos), hγ0⟩
  have hsub := hγWpre.subset_connectedComponentIn hy0mem hγWfib
  -- the radius of the germ
  refine ⟨min ε₀ r₁, lt_min hε₀pos hr₁pos, ?_⟩
  intro y' hy'dist hy'fib
  have hy'U : y' ∈ U :=
    hr₁ (Metric.mem_ball.mpr (lt_of_lt_of_le hy'dist (min_le_right ε₀ r₁)))
  have hgy' : g y' = 0 := by
    funext a
    dsimp only [g, fgFibreMap]
    exact Work.WilE5.Stratum.good_eqs hGood hy'fib a
  have hσball : σ y' ∈ Metric.ball (0 : (fderiv ℝ g (projSnd p q z)).ker) δ :=
    hε₀ (Metric.mem_ball.mpr (lt_of_lt_of_le hy'dist (min_le_left ε₀ r₁)))
  obtain ⟨-, hσγ'⟩ := hσγ y' hy'U (hgy'.trans hgz.symm)
  exact hsub ⟨σ y', hσball, hσγ'⟩

end Work.WilE7
