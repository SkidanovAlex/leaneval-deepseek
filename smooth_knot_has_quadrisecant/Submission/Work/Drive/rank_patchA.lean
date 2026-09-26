import Mathlib
import Submission.Work.Drive.rankPatchDefs
import Submission.Transversality
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv

/-!
# The patch `P_a` of the bad locus has differential of rank four

`Work.Drive.rank_patchA`: at every data point `x : TripleData` with nonzero chord vector
`d = dataP x - dataQ x`, the two patch conditions `(dataColl, dataYa)` of patch `P_a` have a
differential of rank at least four.

The proof exhibits the four independent directions of the data space `Space⁶` explicitly:

* the *pure position* knob `δM` : moving the middle point `M ↦ M + m` changes only the
  collinearity factor, with derivative `(m × d, 0)` — a two-dimensional family of
  variations, because `m ↦ m × d` has a two-dimensional range (`rpa_crossLin`, rank two by
  rank–nullity, kernel `ℝ d` for `d ≠ 0`);
* the *pure velocity* knob `δA` : changing `A ↦ A + a` changes only the tangent–chord factor,
  with derivative `(0, a × d)` — another two-dimensional family;

the two knobs live in the two complementary factors, so the derivative of `patchA` sends the
four-dimensional space `(range (· × d)) × (range (· × d))` injectively into its range.

The derivative computations are done along the two affine lines `s ↦ x + s • e` through `x`
(`rpa_dirM`, `rpa_dirA`), using the Leibniz rule `hasDerivAt_cross3_curves` for the cross
product and `fderiv_along_axis_eq_deriv` to identify the curve derivative with the value of
the Fréchet derivative on the direction `e`.
-/

open scoped Matrix

-- The hypothesis `hcol` records that the data point lies on the patch; the rank bound below
-- only needs the chord vector to be nonzero, so `hcol` is not used in the proof.
set_option linter.unusedVariables false

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-! ## The two perturbation directions of the data space

`TripleData = Space⁶` is the data `(P, Q, M, A, B, C) = (r a, r b, r m, v a, v b, v m)`. -/

/-- The data perturbation that moves the middle point: `(0, 0, m, 0, 0, 0)`. -/
def rpa_dirM (m : Space) : TripleData := (0, 0, m, 0, 0, 0)

/-- The data perturbation that changes the velocity at the first point:
`(0, 0, 0, a, 0, 0)`. -/
def rpa_dirA (a : Space) : TripleData := (0, 0, 0, a, 0, 0)

/-! ## Smoothness of the patch map -/

/-- `patchA` is `C¹`: it is built from the coordinate projections of the data, differences
and cross products of them. -/
lemma rpa_contDiff_patchA : ContDiff ℝ 1 patchA := by
  have hcross : ContDiff ℝ 1 (fun p : Space × Space => cross3 p.1 p.2) := by
    simpa [cross3] using (Commons.Analysis.CrossProduct.cross3_contDiff).of_le le_top
  have h1 : ContDiff ℝ 1
      (fun X : TripleData => (dataP X - dataQ X, dataP X - dataM X)) := by
    unfold dataP dataQ dataM
    fun_prop
  have h2 : ContDiff ℝ 1 (fun X : TripleData => (dataA X, dataP X - dataQ X)) := by
    unfold dataA dataP dataQ
    fun_prop
  have hp := (hcross.comp h1).prodMk (hcross.comp h2)
  unfold patchA dataColl dataYa
  exact hp

/-! ## The derivatives along the two affine lines

These four lemmas compute the derivative at `0` of `s ↦ dataColl (x + s • e)` and
`s ↦ dataYa (x + s • e)` for the two perturbations `e = rpa_dirM m` and `e = rpa_dirA a`.
Note that `dataColl` depends on the data only through `(P, Q, M)` and `dataYa` only through
`(A, P, Q)`, so the "mixed" components are constant along the lines. -/

/-- Along the middle-point perturbation, the collinearity factor has derivative `m × d`. -/
lemma rpa_hasDerivAt_dataColl_dirM (x : TripleData) (m : Space) :
    HasDerivAt (fun s : ℝ => dataColl (x + s • rpa_dirM m))
      (cross3 m (dataP x - dataQ x)) 0 := by
  have hu : HasDerivAt (fun _ : ℝ => dataP x - dataQ x) (0 : Space) 0 :=
    hasDerivAt_const 0 _
  have hbase : HasDerivAt (fun s : ℝ => s • m) m 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const m
  have hv : HasDerivAt (fun s : ℝ => dataP x - (dataM x + s • m)) (-m) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => dataM x + s • m) m 0 :=
      hbase.const_add (dataM x)
    exact h1.const_sub (dataP x)
  have h := hasDerivAt_cross3_curves _ _ hu hv
  have h' : HasDerivAt (fun s : ℝ => dataColl (x + s • rpa_dirM m))
      (cross3 (0 : Space) (dataP x - (dataM x + (0 : ℝ) • m)) +
        cross3 (dataP x - dataQ x) (-m)) 0 := by
    apply HasDerivAt.congr_of_eventuallyEq h
    filter_upwards with s
    simp [dataColl, dataP, dataQ, dataM, rpa_dirM]
  apply HasDerivAt.congr_deriv h'
  rw [cross3_zero_left, zero_add, cross3_neg_right]
  rw [cross3_anticomm (u := m) (v := dataP x - dataQ x), neg_neg]

/-- Along the middle-point perturbation, the tangent–chord factor at the first point is
constant. -/
lemma rpa_hasDerivAt_dataYa_dirM (x : TripleData) (m : Space) :
    HasDerivAt (fun s : ℝ => dataYa (x + s • rpa_dirM m)) (0 : Space) 0 := by
  apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const (0 : ℝ) (dataYa x))
  filter_upwards with s
  simp [dataYa, dataP, dataQ, dataA, rpa_dirM]

/-- Along the first-velocity perturbation, the collinearity factor is constant. -/
lemma rpa_hasDerivAt_dataColl_dirA (x : TripleData) (a : Space) :
    HasDerivAt (fun s : ℝ => dataColl (x + s • rpa_dirA a)) (0 : Space) 0 := by
  apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const (0 : ℝ) (dataColl x))
  filter_upwards with s
  simp [dataColl, dataP, dataQ, dataM, rpa_dirA]

/-- Along the first-velocity perturbation, the tangent–chord factor has derivative `a × d`. -/
lemma rpa_hasDerivAt_dataYa_dirA (x : TripleData) (a : Space) :
    HasDerivAt (fun s : ℝ => dataYa (x + s • rpa_dirA a))
      (cross3 a (dataP x - dataQ x)) 0 := by
  have hbase : HasDerivAt (fun s : ℝ => s • a) a 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const a
  have hu : HasDerivAt (fun s : ℝ => dataA x + s • a) a 0 := hbase.const_add (dataA x)
  have hv : HasDerivAt (fun _ : ℝ => dataP x - dataQ x) (0 : Space) 0 :=
    hasDerivAt_const 0 _
  have h := hasDerivAt_cross3_curves _ _ hu hv
  have h' : HasDerivAt (fun s : ℝ => dataYa (x + s • rpa_dirA a))
      (cross3 a (dataP x - dataQ x) + cross3 (dataA x + (0 : ℝ) • a) (0 : Space)) 0 := by
    apply HasDerivAt.congr_of_eventuallyEq h
    filter_upwards with s
    simp [dataYa, dataP, dataQ, dataA, rpa_dirA]
  apply HasDerivAt.congr_deriv h'
  rw [cross3_zero_right, add_zero]

/-! ## The values of the Fréchet derivative on the two directions -/

/-- The differential of `patchA` at `x` on the middle-point direction `rpa_dirM m`. -/
lemma rpa_fderiv_dirM (x : TripleData) (m : Space) :
    (fderiv ℝ patchA x) (rpa_dirM m)
      = (cross3 m (dataP x - dataQ x), (0 : Space)) := by
  have hdiff : DifferentiableAt ℝ patchA x :=
    (rpa_contDiff_patchA.differentiable (by norm_num)).differentiableAt
  have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := patchA) (p := x) (e := rpa_dirM m) hdiff
  have h2 : HasDerivAt (fun s : ℝ => patchA (x + s • rpa_dirM m))
      (cross3 m (dataP x - dataQ x), (0 : Space)) 0 := by
    have hp := (rpa_hasDerivAt_dataColl_dirM x m).prodMk (rpa_hasDerivAt_dataYa_dirM x m)
    apply HasDerivAt.congr_of_eventuallyEq hp
    filter_upwards with s
    simp [patchA]
  exact h1.unique h2

/-- The differential of `patchA` at `x` on the first-velocity direction `rpa_dirA a`. -/
lemma rpa_fderiv_dirA (x : TripleData) (a : Space) :
    (fderiv ℝ patchA x) (rpa_dirA a)
      = ((0 : Space), cross3 a (dataP x - dataQ x)) := by
  have hdiff : DifferentiableAt ℝ patchA x :=
    (rpa_contDiff_patchA.differentiable (by norm_num)).differentiableAt
  have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := patchA) (p := x) (e := rpa_dirA a) hdiff
  have h2 : HasDerivAt (fun s : ℝ => patchA (x + s • rpa_dirA a))
      ((0 : Space), cross3 a (dataP x - dataQ x)) 0 := by
    have hp := (rpa_hasDerivAt_dataColl_dirA x a).prodMk (rpa_hasDerivAt_dataYa_dirA x a)
    apply HasDerivAt.congr_of_eventuallyEq hp
    filter_upwards with s
    simp [patchA]
  exact h1.unique h2

/-! ## The linear map `u ↦ u × d` and its rank -/

/-- The cross product with a fixed vector `d`, as a linear map of the other argument. -/
def rpa_crossLin (d : Space) : Space →ₗ[ℝ] Space where
  toFun := fun u => cross3 u d
  map_add' := fun u v => cross3_add_left u v d
  map_smul' := fun c u => cross3_smul_left c u d

@[simp] lemma rpa_crossLin_apply (d u : Space) : rpa_crossLin d u = cross3 u d := rfl

/-- The kernel of `u ↦ u × d` is the line spanned by `d` (for `d ≠ 0`). -/
lemma rpa_ker_crossLin {d : Space} (hd : d ≠ 0) :
    LinearMap.ker (rpa_crossLin d) = Submodule.span ℝ ({d} : Set Space) := by
  ext u
  simp only [LinearMap.mem_ker, rpa_crossLin_apply, Submodule.mem_span_singleton]
  constructor
  · intro h
    rcases (cross3_eq_zero_iff_smul_local u d).mp h with h0 | ⟨t, ht⟩
    · exact ⟨0, by rw [h0, zero_smul]⟩
    · have ht0 : t ≠ 0 := by
        rintro rfl
        rw [zero_smul] at ht
        exact hd ht
      exact ⟨t⁻¹, by rw [ht, smul_smul, inv_mul_cancel₀ ht0, one_smul]⟩
  · rintro ⟨t, rfl⟩
    rw [cross3_smul_left, cross3_self, smul_zero]

/-- `u ↦ u × d` has rank two for `d ≠ 0` (rank–nullity). -/
lemma rpa_finrank_range_crossLin {d : Space} (hd : d ≠ 0) :
    Module.finrank ℝ (LinearMap.range (rpa_crossLin d)) = 2 := by
  have hdim : Module.finrank ℝ Space = 3 := by
    simp [LeanEval.KnotTheory.Quadrisecant.Space]
  have h1 : Module.finrank ℝ (LinearMap.ker (rpa_crossLin d)) = 1 := by
    rw [rpa_ker_crossLin hd]
    exact finrank_span_singleton hd
  have h2 := LinearMap.finrank_range_add_finrank_ker (rpa_crossLin d)
  omega

/-! ## The main statement -/

/-- **The patch `P_a` has differential of rank four.**  At any data point with nonzero chord
vector, the two patch conditions `(dataColl, dataYa)` vary in at least four independent
directions as the data vary: two in the collinearity factor and two in the tangent–chord factor
(a pure velocity variation `δA ↦ δA × d`, image `d^⊥`), the two factors being complementary.

These are exactly the variations realised by the coefficient directions of the bounded-degree
trigonometric-sum perturbation family. -/
theorem rank_patchA (x : Work.Drive.TripleData)
    (hd : Work.Drive.dataP x - Work.Drive.dataQ x ≠ 0)
    (hcol : Work.Drive.dataColl x = 0) :
    4 ≤ Module.finrank ℝ
      (LinearMap.range ((fderiv ℝ Work.Drive.patchA x).toLinearMap)) := by
  set D : TripleData →ₗ[ℝ] Space × Space := (fderiv ℝ patchA x).toLinearMap with hD
  set f : Space →ₗ[ℝ] Space := rpa_crossLin (dataP x - dataQ x) with hf
  have hfr : Module.finrank ℝ (LinearMap.range f) = 2 := by
    rw [hf]
    exact rpa_finrank_range_crossLin hd
  have hdirM : ∀ m : Space, D (rpa_dirM m) = (f m, 0) := by
    intro m
    rw [hD]
    change (fderiv ℝ patchA x) (rpa_dirM m) = (f m, 0)
    rw [rpa_fderiv_dirM x m]
    rfl
  have hdirA : ∀ a : Space, D (rpa_dirA a) = (0, f a) := by
    intro a
    rw [hD]
    change (fderiv ℝ patchA x) (rpa_dirA a) = ((0 : Space), f a)
    rw [rpa_fderiv_dirA x a]
    rfl
  let Ψ : ((LinearMap.range f) × (LinearMap.range f)) →ₗ[ℝ] (LinearMap.range D) :=
    { toFun := fun p =>
        ⟨(p.1.1, p.2.1), by
          obtain ⟨m, hm⟩ := p.1.2
          obtain ⟨a, ha⟩ := p.2.2
          refine ⟨rpa_dirM m + rpa_dirA a, ?_⟩
          rw [map_add, hdirM m, hdirA a, hm, ha]
          simp⟩
      map_add' := fun p q => rfl
      map_smul' := fun c p => rfl }
  have hΨ : Function.Injective Ψ := by
    intro p q hpq
    have h1 : (p.1.1, p.2.1) = (q.1.1, q.2.1) := by
      have := congrArg Subtype.val hpq
      simpa [Ψ] using this
    have h2 : p.1.1 = q.1.1 := congrArg Prod.fst h1
    have h3 : p.2.1 = q.2.1 := congrArg Prod.snd h1
    exact Prod.ext (Subtype.ext h2) (Subtype.ext h3)
  have hle := LinearMap.finrank_le_finrank_of_injective (f := Ψ) hΨ
  have hfin : Module.finrank ℝ ((LinearMap.range f) × (LinearMap.range f)) = 4 := by
    rw [Module.finrank_prod, hfr]
  omega

end

end Work.Drive
