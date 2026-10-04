/-
# Kit for the joint-smoothness assembly (`Work.Diff.STE.Lead.jointSmooth_of_solves_deTurck`)

This module collects the small definitions and elementary lemmas on which the assembly of the
target lemma `Work.Diff.STE.Lead.jointSmooth_of_solves_deTurck` runs, and which the delegated
pieces of that assembly (`Gf_tower_jointContinuous`, `chartMat_solves_chartNonlin`,
`exists_smooth_surrogate_chartNonlin`, `section_contMDiffWithinAt_of_frameMat_at`) also use.

* `flatToE_eq_chartCoordSymm` : the two flat coordinates in use in the workspace (`B3.flatToE`
  and `Man.chartCoordSymm`) agree;
* `chartMatC` : the *flat chart matrix* of a section in the `g₀`-orthonormal frame of the chart at
  `D.x₀ i` (i.e. `B3.Gf`), as a complex matrix valued function — this is the unknown fed to the
  bootstrap `Work.Diff.STE.Lead.contDiffOn_of_solves_jet`;
* `reMatE_chartMatC` : its real part is `B3.Gf`;
* `det_Gf_ne_zero` : the flat chart matrix of a positive definite section is invertible — this is
  what makes the chart nonlinearity meaningful;
* `exists_contDiff_tsupport_subset_isCompact` : the smooth bump of a compact subset of an open set
  (used to globalise a nonlinearity which is only smooth on the non-degeneracy region);
* `pdList_eq_pdVec_get` : the bridge between the `pdList`-indexed jet tower of the bootstrap and
  the `pdVec`-indexed one of the B3 jet-tower continuity lemma.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.LowJetAux
import Submission.Work.Diff.STE.B3.transport_Rres_contDiffOn
import Submission.Work.Diff.STE.Man.chartNonlin_eq_pPhiJet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff BigOperators Topology
open Set Filter Bundle

namespace Work.Diff.STE.Lead

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## 1. The flat coordinates agree -/

/-- `B3.flatToE` and `Man.chartCoordSymm` are the same flat coordinate of the chart at `x₀`. -/
lemma flatToE_eq_chartCoordSymm (x₀ : M) (z : Fin (Module.finrank ℝ E) → ℝ) :
    Work.Diff.STE.flatToE (I := I) x₀ z
      = Work.Diff.STE.Man.chartCoordSymm I x₀ z := by
  simp only [Work.Diff.STE.flatToE, Work.Diff.STE.Man.chartCoordSymm,
    Work.Diff.STE.Man.chartCentre, map_add, LinearEquiv.symm_apply_apply]

/-! ## 2. The flat chart matrix, as a complex matrix -/

/-- **The flat chart matrix** of a section, in the `g₀`-orthonormal frame of the chart at
`D.x₀ i`, as a complex matrix valued function.  This is the unknown of the flat chart PDE. -/
noncomputable def chartMatC (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀) :
    (Fin (Module.finrank ℝ E) → ℝ) →
      Work.Diff.STE.Flat.MatC (Work.Diff.STE.Man.dim E) :=
  fun z => Work.Diff.STE.Man.ofRealMat (E := E) (Work.Diff.STE.B3.Gf (I := I) (M := M) D h i z)

@[simp] lemma chartMatC_apply (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (a b : Fin (Module.finrank ℝ E)) :
    chartMatC (I := I) (M := M) D h i z a b
      = ((Work.Diff.STE.B3.Gf (I := I) (M := M) D h i z a b : ℝ) : ℂ) := rfl

/-- The real part of `chartMatC` is `B3.Gf`. -/
lemma reMatE_chartMatC (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) :
    Work.Diff.STE.Man.reMatE (E := E) (chartMatC (I := I) (M := M) D h i z)
      = Work.Diff.STE.B3.Gf (I := I) (M := M) D h i z := by
  funext a b
  simp only [Work.Diff.STE.Man.reMatE, Work.Diff.STE.Man.ofRealMat, chartMatC,
    Complex.ofReal_re]

/-! ## 3. The flat chart matrix is invertible -/

/-- **The flat chart matrix of a positive definite section is invertible**: this is
`Work.Diff.STE.B3.det_chartMatOf_of_pos` read in the flat coordinate of the chart at `D.x₀ i`. -/
lemma det_Gf_ne_zero (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (i : ι₀) {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ i) :
    (Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h i z)).det ≠ 0 := by
  have h := Work.Diff.STE.B3.det_chartMatOf_of_pos (I := I) (M := M) h hsym hpos (D.x₀ i)
    (D.htarget i z hz)
  simpa only [Work.Diff.STE.B3.Gf, Work.Diff.STE.B3.yf] using h

/-! ## 4. Smooth bumps of a compact set inside an open set -/

/-- **A bump at a point with an explicit inner ball**: if `s` is a neighbourhood of `x`, there is a
smooth `f : E → ℝ` with values in `[0,1]`, closed support in `s`, equal to `1` on a whole
`Euclidean` ball around `x`.  (This is `exists_contDiff_tsupport_subset` with the inner radius of
the `ContDiffBump` exposed; the reason we need it is that the finite-cover construction of a bump
of a compact set requires the individual bumps to be `1` on *neighbourhoods* of the covering
points.) -/
lemma exists_contDiff_one_nhds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s : Set E} {x : E} (hs : s ∈ 𝓝 x) :
    ∃ (f : E → ℝ) (r : ℝ), 0 < r ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧ tsupport f ⊆ s ∧
      (∀ y, 0 ≤ f y ∧ f y ≤ 1) ∧ (∀ y, Euclidean.dist y x ≤ r → f y = 1) := by
  obtain ⟨d, d_pos, hd : Euclidean.closedBall x d ⊆ s⟩ :=
    Euclidean.nhds_basis_closedBall.mem_iff.1 hs
  let c : ContDiffBump (toEuclidean x) :=
    { rIn := d / 2, rOut := d, rIn_pos := half_pos d_pos, rIn_lt_rOut := half_lt_self d_pos }
  let f : E → ℝ := c ∘ toEuclidean
  have f_supp : Function.support f ⊆ Euclidean.ball x d := by
    intro y hy
    have : toEuclidean y ∈ Function.support c := by
      simpa only [f, Function.mem_support, Function.comp_apply, Ne] using hy
    rwa [c.support_eq] at this
  have f_tsupp : tsupport f ⊆ Euclidean.closedBall x d := by
    rw [tsupport, ← Euclidean.closure_ball _ d_pos.ne']
    exact closure_mono f_supp
  refine ⟨f, d / 2, half_pos d_pos, ?_, f_tsupp.trans hd,
    fun y => ⟨c.nonneg, c.le_one⟩, ?_⟩
  · exact c.contDiff.comp (ContinuousLinearEquiv.contDiff _)
  · intro y hy
    exact c.one_of_mem_closedBall (by simpa only [Euclidean.dist, Metric.mem_closedBall] using hy)

/-- **Smooth bump of a compact subset of an open set**: if `K` is compact and `K ⊆ U` with `U`
open, there is a smooth function `θ` with values in `[0,1]`, equal to `1` on `K` and with closed
support inside `U`. -/
lemma exists_contDiff_tsupport_subset_isCompact {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ θ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ ∧ tsupport θ ⊆ U ∧ (∀ x ∈ K, θ x = 1) ∧
      (∀ x, 0 ≤ θ x) := by
  classical
  have hpt : ∀ x : K, ∃ (f : E → ℝ) (r : ℝ), 0 < r ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧
      tsupport f ⊆ U ∧ (∀ y, 0 ≤ f y ∧ f y ≤ 1) ∧
      (∀ y, Euclidean.dist y (x : E) ≤ r → f y = 1) :=
    fun x => exists_contDiff_one_nhds (hU.mem_nhds (hKU x.2))
  choose g r hr hgsm hgtsup hgbd hg1 using hpt
  have hcov : K ⊆ ⋃ x : K, Euclidean.ball (x : E) (r x) := by
    intro y hy
    have h := hr ⟨y, hy⟩
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, by
      show Euclidean.dist y y < r ⟨y, hy⟩
      simpa only [Euclidean.dist, dist_self] using h⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun x : K => Euclidean.ball (x : E) (r x))
    (fun x => Euclidean.isOpen_ball) hcov
  refine ⟨fun y => 1 - ∏ x ∈ T, (1 - g x y), ?_, ?_, ?_, ?_⟩
  · have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => ∏ x ∈ T, (1 - g x y)) := by
      fun_prop
    exact contDiff_const.sub h1
  · have hsupp : Function.support (fun y => 1 - ∏ x ∈ T, (1 - g x y))
        ⊆ ⋃ x ∈ T, Function.support (g x) := by
      intro y hy
      simp only [Function.mem_support, sub_ne_zero] at hy
      by_contra hcon
      simp only [Set.mem_iUnion, not_exists, not_and] at hcon
      have h1 : ∀ x ∈ T, g x y = 0 := by
        intro x hx
        have := hcon x hx
        simpa only [Function.mem_support, not_not] using this
      have h2 : (∏ x ∈ T, (1 - g x y)) = ∏ x ∈ T, (1 : ℝ) :=
        Finset.prod_congr rfl (fun x hx => by rw [h1 x hx, sub_zero])
      have h3 : (∏ x ∈ T, (1 - g x y)) = 1 := by rw [h2, Finset.prod_const_one]
      exact hy (by simp [h3])
    calc tsupport (fun y => 1 - ∏ x ∈ T, (1 - g x y))
        = closure (Function.support fun y => 1 - ∏ x ∈ T, (1 - g x y)) := rfl
      _ ⊆ closure (⋃ x ∈ T, Function.support (g x)) := closure_mono hsupp
      _ ⊆ closure (⋃ x ∈ T, tsupport (g x)) :=
          closure_mono (Set.iUnion₂_mono fun x _ => subset_tsupport (g x))
      _ = ⋃ x ∈ T, closure (tsupport (g x)) := Finset.closure_biUnion T _
      _ = ⋃ x ∈ T, tsupport (g x) := by
          refine Set.iUnion₂_congr fun x _ => ?_
          exact (isClosed_tsupport (g x)).closure_eq
      _ ⊆ U := Set.iUnion₂_subset fun x _ => hgtsup x
  · intro y hy
    have hyy := hT hy
    rw [Set.mem_iUnion] at hyy
    obtain ⟨x, hxx⟩ := hyy
    rw [Set.mem_iUnion] at hxx
    obtain ⟨hxT, hxy⟩ := hxx
    have h1 : g x y = 1 := hg1 x y (le_of_lt hxy)
    have hzero : (∏ z ∈ T, (1 - g z y)) = 0 :=
      Finset.prod_eq_zero hxT (by rw [h1]; ring)
    simp [hzero]
  · intro y
    have h1 : ∀ x ∈ T, (1 - g x y : ℝ) ≤ 1 := fun x _ => by linarith [(hgbd x y).1]
    have h2 : ∀ x ∈ T, (0 : ℝ) ≤ 1 - g x y := fun x _ => sub_nonneg.mpr (hgbd x y).2
    have h3 : (∏ x ∈ T, (1 - g x y)) ≤ 1 := Finset.prod_le_one₀ h2 h1
    linarith

/-! ## 5. `pdList` versus `pdVec` -/

/-- **The two jet-tower conventions agree**: `pdList l` is `pdVec` indexed by the `Fin`-vector of
the entries of `l`. -/
lemma pdList_eq_pdVec_get {n : ℕ} (l : List (Fin n)) (f : (Fin n → ℝ) → ℂ) :
    Work.Diff.STE.pdList l f
      = Work.Diff.STE.pdVec l.length (fun i : Fin l.length => l.get i) f := by
  simp only [Work.Diff.STE.pdVec, List.ofFn_get]

end Work.Diff.STE.Lead
