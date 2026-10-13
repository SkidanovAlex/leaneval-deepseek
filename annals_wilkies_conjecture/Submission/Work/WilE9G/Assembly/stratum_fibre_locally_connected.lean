/-
  Subproject WilE9G / Assembly — **D2**: the fibres of the base projection along a `Good` ambient
  stratum are locally connected at a base-submersive point.

  Let `S : AmbStratum N` be `Good`, `z ∈ S.X.set`, and suppose `z` is not a critical point of the
  base projection `π_n = projBase hn` restricted to the stratum.  Since the equations' Jacobian
  has full row rank `S.j` at `z` (`AmbStratum.rank`), the combined map

      `F = (π_n, h) : ℝ^N → ℝ^n × ℝ^{S.j}`

  is a submersion at `z` (`range_fderiv_pairMap`).  The implicit function theorem in the analytic
  chart form `Work.WilE7.fgAnalyticChart` (applied to `F` read as a map to `ℝ^{n + S.j}` via
  `appendCLM`) exhibits the level set `F = F z` near `z` as the image `γ '' ball 0 δ` of a ball in
  `ker (dF)_z`.  Two facts then give the result:

  * `γ '' ball 0 δ` is preconnected (image of a convex set under a continuous map) and contains
    `z = γ 0`;
  * by `Good`'s locality clause, every point of it *is* in `S.X.set` — it satisfies `h = 0` and
    lies close enough to `z` — and it satisfies `π_n = π_n z` by construction;

  so it is a preconnected subset of `S.X.set ∩ {π_n = π_n z}` containing `z`, hence contained in
  the connected component.  Conversely, every `z' ∈ S.X.set` close to `z` with `π_n z' = π_n z`
  satisfies `F z' = F z` (the equations vanish on `S.X.set`) and, being in `U`, is `γ (σ z')` with
  `σ z'` in the ball — so it lies in that preconnected piece.

  This is the ambient version of `Work.WilE7.fiber_germ_subset_component`, with the fibrewise
  full-rank hypothesis replaced by the pair (`AmbStratum.rank`, `IsBaseSubmersiveAt`).
-/
import Mathlib
import Submission.Work.WilE9G.Amb
import Submission.Work.WilE9G.Jac
import Submission.Work.WilE9G.Basic
import Submission.Work.WilE7.fiber_germ_subset_component
import Submission.Work.WilE5.Flat.fderiv_pi_eaEval_apply
import Submission.Work.WilE9.Ift.AppendCLM

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G.Assembly
open WilkiesDesign WilkiesDesign.E Work.WilE9G

/-
  The auxiliary constructions of this file, kept in their own namespace so that they cannot
  collide with the other files of `Work.WilE9G.Assembly`.
-/
namespace Sflc

/-! ## The projection as a continuous linear map -/

/-- The projection to the first `n` coordinates, as a continuous linear map. -/
def projBaseCLM {N n : ℕ} (hn : n ≤ N) : (Fin N → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i : Fin n => ContinuousLinearMap.proj (Fin.castLE hn i))

theorem projBaseCLM_apply {N n : ℕ} (hn : n ≤ N) (v : Fin N → ℝ) :
    projBaseCLM hn v = projBase hn v := by
  funext i
  simp [projBaseCLM, projBase]

theorem hasFDerivAt_projBase {N n : ℕ} (hn : n ≤ N) (z : Fin N → ℝ) :
    HasFDerivAt (fun w : Fin N → ℝ => projBase hn w) (projBaseCLM hn) z := by
  convert (projBaseCLM hn).hasFDerivAt using 2
  funext v
  rw [projBaseCLM_apply]

/-! ## The tuple of defining equations -/

/-- The tuple of the defining equations of an ambient stratum, as a map to `ℝ^{S.j}`. -/
def eqMap {N : ℕ} (S : AmbStratum N) : (Fin N → ℝ) → (Fin S.j → ℝ) :=
  fun w a => eaEval S.X.c (S.h a) w

theorem hasFDerivAt_eqMap {N : ℕ} (S : AmbStratum N) (z : Fin N → ℝ) :
    HasFDerivAt (eqMap S)
      (ContinuousLinearMap.pi (fun a : Fin S.j => ∑ l : Fin N,
        (eaEval S.X.c (eaD S.X.c l (S.h a)) z) •
          (ContinuousLinearMap.proj l : (Fin N → ℝ) →L[ℝ] ℝ))) z :=
  hasFDerivAt_pi.mpr
    (fun a : Fin S.j => Work.WilE5.Calc.hasFDerivAt_eaEval S.X.c (S.h a) z)

theorem fderiv_eqMap {N : ℕ} (S : AmbStratum N) (z : Fin N → ℝ) :
    fderiv ℝ (eqMap S) z
      = ContinuousLinearMap.pi (fun a : Fin S.j => ∑ l : Fin N,
          (eaEval S.X.c (eaD S.X.c l (S.h a)) z) •
            (ContinuousLinearMap.proj l : (Fin N → ℝ) →L[ℝ] ℝ)) :=
  (hasFDerivAt_eqMap S z).fderiv

/-- The equations' Jacobian has full row rank at a point of a `Good` stratum, so the differential
of the tuple of equations is surjective. -/
theorem range_fderiv_eqMap {N : ℕ} (S : AmbStratum N) (hS : S.Good) {z : Fin N → ℝ}
    (hz : z ∈ S.X.set) : (fderiv ℝ (eqMap S) z).range = ⊤ := by
  rw [fderiv_eqMap]
  exact Work.WilE7.Aux.rangePiEqTopOfRank
    (fun (a : Fin S.j) (l : Fin N) => eaEval S.X.c (eaD S.X.c l (S.h a)) z)
    (AmbStratum_rank S hS hz)

/-- Component `a` of the differential of the tuple of equations is the differential of the `a`-th
equation. -/
theorem fderiv_eqMap_apply {N : ℕ} (S : AmbStratum N) (z v : Fin N → ℝ) (a : Fin S.j) :
    (fderiv ℝ (eqMap S) z v) a
      = (fderiv ℝ (fun w : Fin N → ℝ => eaEval S.X.c (S.h a) w) z) v := by
  rw [fderiv_eqMap, ContinuousLinearMap.pi_apply,
    (Work.WilE5.Calc.hasFDerivAt_eaEval S.X.c (S.h a) z).fderiv]

/-! ## The combined map `(π_n, h)` -/

/-- Packing the pair `(π_n w, h w)` into a single vector of `ℝ^{n + S.j}`. -/
def ambMap {N n : ℕ} (hn : n ≤ N) (S : AmbStratum N) :
    (Fin N → ℝ) → (Fin (n + S.j) → ℝ) :=
  fun w => Work.WilE9.Ift.appendCLM n S.j (projBase hn w, eqMap S w)

theorem ambMap_apply {N n : ℕ} (hn : n ≤ N) (S : AmbStratum N) (w : Fin N → ℝ) :
    ambMap hn S w = Fin.append (projBase hn w) (eqMap S w) :=
  Work.WilE9.Ift.appendCLM_apply n S.j (projBase hn w) (eqMap S w)

/-- `appendCLM` is injective: the two blocks of a vector of `ℝ^{n+q}` determine it. -/
theorem appendCLM_injective (n q : ℕ) :
    Function.Injective (Work.WilE9.Ift.appendCLM n q) := by
  intro p p' h
  obtain ⟨v, w⟩ := p
  obtain ⟨v', w'⟩ := p'
  have hv : v = v' := by
    funext i
    have hi := congrFun h (Fin.castAdd q i)
    simpa [Work.WilE9.Ift.appendCLM_apply] using hi
  have hw : w = w' := by
    funext l
    have hl := congrFun h (Fin.natAdd n l)
    simpa [Work.WilE9.Ift.appendCLM_apply] using hl
  simp [hv, hw]

/-- `appendCLM` is surjective. -/
theorem appendCLM_surjective (n q : ℕ) :
    Function.Surjective (Work.WilE9.Ift.appendCLM n q) := by
  intro y
  refine ⟨(fun i : Fin n => y (Fin.castAdd q i), fun l : Fin q => y (Fin.natAdd n l)), ?_⟩
  ext s
  refine Fin.addCases (fun i => ?_) (fun l => ?_) s <;>
    simp [Work.WilE9.Ift.appendCLM_apply]

/-- The two blocks of `ambMap` are determined by its value. -/
theorem ambMap_inj {N n : ℕ} (hn : n ≤ N) (S : AmbStratum N) {w w' : Fin N → ℝ}
    (h : ambMap hn S w = ambMap hn S w') :
    projBase hn w = projBase hn w' ∧ eqMap S w = eqMap S w' := by
  have hpair : (projBase hn w, eqMap S w) = (projBase hn w', eqMap S w') :=
    appendCLM_injective n S.j (show Work.WilE9.Ift.appendCLM n S.j (projBase hn w, eqMap S w)
      = Work.WilE9.Ift.appendCLM n S.j (projBase hn w', eqMap S w') from h)
  exact ⟨congr_arg Prod.fst hpair, congr_arg Prod.snd hpair⟩

theorem hasFDerivAt_pairMap {N n : ℕ} (hn : n ≤ N) (S : AmbStratum N) (z : Fin N → ℝ) :
    HasFDerivAt (fun w : Fin N → ℝ => (projBase hn w, eqMap S w))
      ((projBaseCLM hn).prod (fderiv ℝ (eqMap S) z)) z :=
  (hasFDerivAt_projBase hn z).prodMk (hasFDerivAt_eqMap S z).differentiableAt.hasFDerivAt

theorem hasFDerivAt_ambMap {N n : ℕ} (hn : n ≤ N) (S : AmbStratum N) (z : Fin N → ℝ) :
    HasFDerivAt (ambMap hn S)
      ((Work.WilE9.Ift.appendCLM n S.j).comp
        ((projBaseCLM hn).prod (fderiv ℝ (eqMap S) z))) z := by
  have hcomp := (Work.WilE9.Ift.appendCLM n S.j).hasFDerivAt.comp z (hasFDerivAt_pairMap hn S z)
  refine hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
  rfl

theorem fderiv_ambMap {N n : ℕ} (hn : n ≤ N) (S : AmbStratum N) (z : Fin N → ℝ) :
    fderiv ℝ (ambMap hn S) z
      = (Work.WilE9.Ift.appendCLM n S.j).comp
          ((projBaseCLM hn).prod (fderiv ℝ (eqMap S) z)) :=
  (hasFDerivAt_ambMap hn S z).fderiv

/-- **The combined map is a submersion at a base-submersive point of a `Good` stratum.**  Given
`(w, v) ∈ ℝ^n × ℝ^{S.j}`, choose `ξ₁` with `dh(z) ξ₁ = v` (`AmbStratum.rank`); the
base-submersivity hypothesis supplies `ξ₂` with `π_n ξ₂ = w - π_n ξ₁` and `dh(z) ξ₂ = 0`; then
`F'(z) (ξ₁ + ξ₂) = (w, v)`. -/
theorem surjective_pairMap {N n : ℕ} (hn : n ≤ N) (S : AmbStratum N) (hS : S.Good)
    {z : Fin N → ℝ} (hz : z ∈ S.X.set) (hsub : AmbStratum.IsBaseSubmersiveAt S hn z) :
    Function.Surjective ((projBaseCLM hn).prod (fderiv ℝ (eqMap S) z)) := by
  intro y
  have hsurj_eq : Function.Surjective (fderiv ℝ (eqMap S) z) :=
    LinearMap.range_eq_top.mp (range_fderiv_eqMap S hS hz)
  obtain ⟨ξ₁, hξ₁⟩ := hsurj_eq y.2
  obtain ⟨ξ₂, hξ₂₁, hξ₂₂⟩ := hsub (y.1 - projBase hn ξ₁)
  have hξ₂₀ : fderiv ℝ (eqMap S) z ξ₂ = 0 := by
    funext a
    rw [fderiv_eqMap_apply]
    exact hξ₂₂ a
  have h1 : (projBaseCLM hn) (ξ₁ + ξ₂) = y.1 := by
    rw [map_add, projBaseCLM_apply, projBaseCLM_apply, hξ₂₁]
    abel
  have h2 : (fderiv ℝ (eqMap S) z) (ξ₁ + ξ₂) = y.2 := by
    rw [map_add, hξ₁, hξ₂₀, add_zero]
  refine ⟨ξ₁ + ξ₂, ?_⟩
  change ((projBaseCLM hn) (ξ₁ + ξ₂), (fderiv ℝ (eqMap S) z) (ξ₁ + ξ₂)) = y
  rw [h1, h2]

/-- The differential of the combined map is surjective at a base-submersive point of a `Good`
stratum. -/
theorem range_fderiv_ambMap {N n : ℕ} (hn : n ≤ N) (S : AmbStratum N) (hS : S.Good)
    {z : Fin N → ℝ} (hz : z ∈ S.X.set) (hsub : AmbStratum.IsBaseSubmersiveAt S hn z) :
    (fderiv ℝ (ambMap hn S) z).range = ⊤ := by
  have hC : Function.Surjective (Work.WilE9.Ift.appendCLM n S.j) := appendCLM_surjective n S.j
  have hD : Function.Surjective ((projBaseCLM hn).prod (fderiv ℝ (eqMap S) z)) :=
    surjective_pairMap hn S hS hz hsub
  rw [fderiv_ambMap]
  refine LinearMap.range_eq_top.mpr fun y => ?_
  obtain ⟨p, hp⟩ := hC y
  obtain ⟨ξ, hξ⟩ := hD p
  exact ⟨ξ, by
    change (Work.WilE9.Ift.appendCLM n S.j)
      (((projBaseCLM hn).prod (fderiv ℝ (eqMap S) z)) ξ) = y
    rw [hξ, hp]⟩

end Sflc

open Sflc

/-! ## The main statement -/

theorem stratum_fibre_locally_connected {N n : ℕ} (hn : n ≤ N)
    (S : Work.WilE9G.AmbStratum N) (hS : S.Good) {z : Fin N → ℝ} (hz : z ∈ S.X.set)
    (hsub : Work.WilE9G.AmbStratum.IsBaseSubmersiveAt S hn z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z' : Fin N → ℝ, z' ∈ S.X.set → dist z' z < ε →
      Work.WilE9G.projBase hn z' = Work.WilE9G.projBase hn z →
      z' ∈ connectedComponentIn
        (S.X.set ∩ {w | Work.WilE9G.projBase hn w = Work.WilE9G.projBase hn z}) z := by
  classical
  -- the equations vanish at `z`
  have hgz : eqMap S z = 0 := by
    funext a
    exact (hS z hz).1 a
  -- `ambMap` is analytic everywhere
  have hgan : ∀ y : Fin N → ℝ, AnalyticAt ℝ (ambMap hn S) y := by
    intro y
    have h1 : AnalyticAt ℝ (fun w : Fin N → ℝ => projBase hn w) y := by
      have hfun : (fun w : Fin N → ℝ => projBase hn w) = ⇑(projBaseCLM hn) :=
        funext fun v => projBaseCLM_apply hn v
      rw [hfun]
      exact (projBaseCLM hn).analyticAt y
    have h2 : AnalyticAt ℝ (⇑(Work.WilE9.Ift.appendCLM n S.j) ∘
        fun w : Fin N → ℝ => (projBase hn w, eqMap S w)) y :=
      AnalyticAt.comp (f := fun w : Fin N → ℝ => (projBase hn w, eqMap S w)) (x := y)
        ((Work.WilE9.Ift.appendCLM n S.j).analyticAt (projBase hn y, eqMap S y))
        (h1.prod (AnalyticAt.pi fun a : Fin S.j =>
          Work.WilE5.Strat.analyticAt_eaEval S.X.c (S.h a) y))
    exact h2.congr (Filter.Eventually.of_forall fun w => rfl)
  have hsurj := range_fderiv_ambMap hn S hS hz hsub
  -- the implicit-function chart of the level set `F = F z`
  obtain ⟨γ, σ, V, U, hVo, hUo, h0V, hzU, hγ0, hγan, hγcont, hσcont, hσ0, hVg, hσγ⟩ :=
    Work.WilE7.fgAnalyticChart (ambMap hn S) z hgan hsurj
  -- `Good`'s locality clause, in metric form
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.eventually_nhds_iff.mp (hS z hz).2.2
  -- radii
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.isOpen_iff.mp hVo 0 h0V
  have hγcontAt : ContinuousAt γ 0 := hγcont.continuousAt (hVo.mem_nhds h0V)
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.mem_nhds_iff.mp
    (hγcontAt.preimage_mem_nhds (by rw [hγ0]; exact Metric.ball_mem_nhds z hε₁pos))
  let δ : ℝ := min δ₁ δ₂
  have hδpos : 0 < δ := lt_min hδ₁pos hδ₂pos
  have hWV : Metric.ball (0 : (fderiv ℝ (ambMap hn S) z).ker) δ ⊆ V := by
    intro v hv
    exact hδ₁ (Metric.mem_ball.mpr
      (lt_of_lt_of_le (Metric.mem_ball.mp hv) (min_le_left δ₁ δ₂)))
  -- the preconnected piece of the level set through `z`
  have hWpre : IsPreconnected (Metric.ball (0 : (fderiv ℝ (ambMap hn S) z).ker) δ) :=
    (convex_ball (0 : (fderiv ℝ (ambMap hn S) z).ker) δ).isPreconnected
  have hγWpre : IsPreconnected (γ '' Metric.ball (0 : (fderiv ℝ (ambMap hn S) z).ker) δ) :=
    hWpre.image γ (hγcont.mono hWV)
  have hmem0 : z ∈ γ '' Metric.ball (0 : (fderiv ℝ (ambMap hn S) z).ker) δ :=
    ⟨0, Metric.mem_ball.mpr (by simpa using hδpos), hγ0⟩
  have hγWsub : γ '' Metric.ball (0 : (fderiv ℝ (ambMap hn S) z).ker) δ ⊆
      S.X.set ∩ {w | projBase hn w = projBase hn z} := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨-, hgv⟩ := hVg v (hWV hv)
    obtain ⟨hproj, hzero⟩ := ambMap_inj hn S hgv
    have hdist : dist (γ v) z < ε₁ :=
      Metric.mem_ball.mp (hδ₂ (Metric.mem_ball.mpr
        (lt_of_lt_of_le (Metric.mem_ball.mp hv) (min_le_right δ₁ δ₂))))
    exact ⟨hε₁ hdist (fun a => congrFun (hzero.trans hgz) a), hproj⟩
  have hsub' := hγWpre.subset_connectedComponentIn hmem0 hγWsub
  -- the radii for `σ` and for the chart domain `U`
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := Metric.mem_nhds_iff.mp
    (hσcont.continuousAt.preimage_mem_nhds (by
      rw [hσ0]
      exact Metric.ball_mem_nhds (0 : (fderiv ℝ (ambMap hn S) z).ker) hδpos))
  obtain ⟨r₁, hr₁pos, hr₁⟩ := Metric.isOpen_iff.mp hUo z hzU
  refine ⟨min ε₀ r₁, lt_min hε₀pos hr₁pos, ?_⟩
  intro z' hz'X hz'dist hz'proj
  have hz'U : z' ∈ U :=
    hr₁ (Metric.mem_ball.mpr (lt_of_lt_of_le hz'dist (min_le_right ε₀ r₁)))
  have hpair : (projBase hn z', eqMap S z') = (projBase hn z, eqMap S z) := by
    have h0 : eqMap S z' = 0 := by
      funext a
      exact (hS z' hz'X).1 a
    rw [hz'proj, h0, hgz]
  have hgz' : ambMap hn S z' = ambMap hn S z := by
    show Work.WilE9.Ift.appendCLM n S.j (projBase hn z', eqMap S z')
      = Work.WilE9.Ift.appendCLM n S.j (projBase hn z, eqMap S z)
    rw [hpair]
  have hσball : σ z' ∈ Metric.ball (0 : (fderiv ℝ (ambMap hn S) z).ker) δ :=
    hε₀ (Metric.mem_ball.mpr (lt_of_lt_of_le hz'dist (min_le_left ε₀ r₁)))
  obtain ⟨-, hσγ'⟩ := hσγ z' hz'U hgz'
  exact hsub' ⟨σ z', hσball, hσγ'⟩

end Work.WilE9G.Assembly
