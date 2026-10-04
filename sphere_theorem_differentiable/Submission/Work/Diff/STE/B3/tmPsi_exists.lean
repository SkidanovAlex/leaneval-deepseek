/-
# `Work.Diff.STE.B3.tmPsi_exists`

The residual `Ψ` of the B3 transport identity (`Work.Diff.STE.B3.tmPsi`, defined in
`Submission/Work/Diff/STE/B3/transport_tame_defs.lean`) is a function of the *state*
`(z, V, W)`: the flat coordinate `z`, the ON-frame chart matrix `V` of the section and its first
jet `W`.  Its third summand feeds the matrix `tmGK z V` into the *unclamped* inverse inside the
lower-order DeTurck operator `pN`, so `tmPsi` is `C^∞` only on the locus where `det (tmGK z V) ≠ 0`
(and where the chart data of the B3 datum is smooth, i.e. on the flat image of the chart target).

The target of this file asks for a **globally** `C^∞` function `Φ` which

* reproduces `tmPsi (z, Mf z, ∂Mf z)` on the closed `2σ j` ball (for every section `h` whose chart
  matrix has determinant in a fixed window `[a,b]`), and
* has all its jets bounded on the compact box `{‖z‖ ≤ R, |V| ≤ MV, |W| ≤ MW}`.

The construction is the standard one: multiply `tmPsi` by two *smooth separators*, one in the flat
coordinate (`ζ`, equal to `1` on the `2σ j` ball and supported on the locus where the chart data is
smooth) and one in the state matrix (`β (det (tmGK z V))`, with `β := tmClampBump a b ha hab` a bump
equal to `1` on `[a,b]` and supported away from `0`).  The product is globally smooth because
`tmPsi` is smooth wherever `det (tmGK z V) ≠ 0` (the first separator removes the rest of the bad
`z`-locus, the second the bad `V`-locus, where it vanishes identically on a neighbourhood).
-/
import Mathlib
import Submission.Work.Diff.STE.B3.transport_tame_defs
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.tmGK_eq_Gf
import Submission.Work.Diff.STE.B3.tmNom_aux
import Submission.Work.Diff.STE.B3.transport_Mf_second
import Submission.Work.Diff.STE.B3.tmPsi_state_contDiffOn

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set

namespace Work.Diff.STE.B3

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

noncomputable section

/-! ## 1. The state space and the two domains -/

/-- The state space of `tmPsi`: the flat coordinate, the ON-frame chart matrix and its first jet. -/
abbrev TmsSt (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (Fin (Module.finrank ℝ E) → ℝ) ×
    (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) ×
    (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ)

/-- The good set of flat coordinates: the flat image of the chart target, with invertible frame
matrix.  This is the set on which all the chart data of the B3 datum is `C^∞` in `z`. -/
def tmsGood (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    Set (Fin (Module.finrank ℝ E) → ℝ) :=
  {z | Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target ∧
    (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0}

/-- The locus on which `tmPsi` is `C^∞`: the product of the good set of flat coordinates with the
invertibility of the state matrix. -/
def tmsDom (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) : Set (TmsSt E) :=
  {w | Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target ∧
    (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0 ∧ (Matrix.of w.2.1).det ≠ 0}

/-! ## 2. Calculus helpers for the chart data -/

/-- The determinant of a matrix family with `C^∞` entries is `C^∞` (the cofactor formula). -/
lemma tms_det_of_entries {n : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {X : Y → Matrix (Fin n) (Fin n) ℝ} {y : Y}
    (hX : ∀ i j, ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) (fun y' => X y' i j) y) :
    ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) (fun y' => (X y').det) y := by
  classical
  have hfun : (fun y' : Y => (X y').det)
      = fun y' => ∑ σ : Equiv.Perm (Fin n),
          (↑(Equiv.Perm.sign σ) : ℝ) * ∏ k, X y' (σ k) k := by
    funext y'
    rw [Matrix.det_apply']
  rw [hfun]
  refine ContDiffAt.sum (fun σ _ => contDiffAt_const.mul ?_)
  exact contDiffAt_prod (t := Finset.univ) (f := fun k y' => X y' (σ k) k)
    (fun k _ => hX (σ k) k)

/-- Composing a smooth function with a continuous linear map. -/
lemma tms_clm_comp {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : F →L[ℝ] G) {f : X → F} {x : X}
    (hf : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) f x) :
    ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) (fun y => L (f y)) x :=
  L.contDiff.contDiffAt.comp x hf

/-- The entries of the state matrix, as functions of the state, are `C^∞`. -/
lemma tms_contDiffAt_entry_V {w : TmsSt E} (i j : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
      (fun w' : TmsSt E => w'.2.1 i j) w := by
  have h1 : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) (fun w' : TmsSt E => w'.2.1) w :=
    contDiffAt_snd.fst
  have h2 : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) (fun w' : TmsSt E => w'.2.1 i) w :=
    tms_clm_comp (ContinuousLinearMap.proj (φ := fun _ : Fin (Module.finrank ℝ E) =>
      (Fin (Module.finrank ℝ E) → ℝ)) i) h1
  exact tms_clm_comp (ContinuousLinearMap.proj (φ := fun _ : Fin (Module.finrank ℝ E) => ℝ) j) h2

/-- The determinant of the state matrix is `C^∞` in the state. -/
lemma tms_contDiffAt_det_V {w : TmsSt E} :
    ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
      (fun w' : TmsSt E => (Matrix.of w'.2.1).det) w :=
  tms_det_of_entries (Y := TmsSt E) (X := fun w' => Matrix.of w'.2.1)
    (fun i j => tms_contDiffAt_entry_V i j)

/-- The determinant of the frame matrix `Ff` is `C^∞` on the flat image of the chart target. -/
lemma tms_contDiffAt_det_Ff (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
      (fun y : Fin (Module.finrank ℝ E) → ℝ => (Matrix.of (Ff (I := I) (M := M) D j y)).det) z :=
  tms_det_of_entries (Y := Fin (Module.finrank ℝ E) → ℝ)
    (X := fun y => Matrix.of (Ff (I := I) (M := M) D j y))
    (fun i k => Ff_contDiffAt (I := I) (M := M) D j i k hz)

/-- `tmsGood D j` is open. -/
lemma tms_good_isOpen (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    IsOpen (tmsGood D j) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨hz1, hz2⟩ := hz
  refine Filter.inter_mem ?_ ?_
  · exact ((isOpen_extChartAt_target (I := I) (D.x₀ j)).preimage
      (Work.Diff.STE.contDiff_flatToE (I := I) (D.x₀ j)).continuous).mem_nhds hz1
  · exact (tms_contDiffAt_det_Ff D j hz1).continuousAt.preimage_mem_nhds
      (isOpen_ne.mem_nhds hz2)

/-- The entries of the nominal coordinate-frame chart matrix `tmGK` are `C^∞` in the state, on the
locus where the chart data of `D` is smooth and the frame matrix is invertible. -/
lemma tms_contDiffAt_tmGK_entry (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {w : TmsSt E}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0)
    (i k : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
      (fun w' : TmsSt E => tmGK (I := I) (M := M) D j w'.1 w'.2.1 i k) w := by
  have hF : ∀ i a : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun w' : TmsSt E => Finvf (I := I) (M := M) D j w'.1 i a) w := fun i a =>
    (tmNom_inv_entry_ContDiffAt (X := fun y : Fin (Module.finrank ℝ E) → ℝ =>
        Matrix.of (Ff (I := I) (M := M) D j y))
      (fun p q => Ff_contDiffAt (I := I) (M := M) D j p q hz) hdet i a).comp w
      contDiffAt_fst
  have hV : ∀ a b : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) (fun w' : TmsSt E => w'.2.1 a b) w :=
    fun a b => tms_contDiffAt_entry_V a b
  simp only [tmGK, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  refine ContDiffAt.sum (fun a _ => ?_)
  refine ContDiffAt.mul ?_ ?_
  · refine ContDiffAt.sum (fun b _ => ?_)
    exact (hF i b).mul (hV b a)
  · exact hF k a

/-- The determinant of `tmGK z V` is `C^∞` in the state. -/
lemma tms_contDiffAt_det_tmGK (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {w : TmsSt E}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0) :
    ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
      (fun w' : TmsSt E => (Matrix.of (tmGK (I := I) (M := M) D j w'.1 w'.2.1)).det) w :=
  tms_det_of_entries (Y := TmsSt E)
    (X := fun w' => Matrix.of (tmGK (I := I) (M := M) D j w'.1 w'.2.1))
    (fun i k => tms_contDiffAt_tmGK_entry D j hz hdet i k)

/-- **The determinant of `tmGK z V`.**  Since `Finvf z` is the honest inverse of `Ff z`, the frame
change gives `det (tmGK z V) = (det (Ff z))⁻¹ ^ 2 * det V`; in particular `tmGK z V` is invertible
exactly when `det V ≠ 0` (given `det (Ff z) ≠ 0`). -/
lemma tms_det_tmGK_eq (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    {V : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ}
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0) :
    (Matrix.of (tmGK (I := I) (M := M) D j z V)).det
      = ((Matrix.of (Ff (I := I) (M := M) D j z)).det)⁻¹ ^ 2 * (Matrix.of V).det := by
  have hFin : (Matrix.of (Finvf (I := I) (M := M) D j z)).det
      = ((Matrix.of (Ff (I := I) (M := M) D j z)).det)⁻¹ := by
    rw [Finvf_eq_inv (I := I) (M := M) D j z, Matrix.det_nonsing_inv,
      congrFun Ring.inverse_eq_inv']
  have hmain : (Matrix.of (tmGK (I := I) (M := M) D j z V)).det
      = (Matrix.of (Finvf (I := I) (M := M) D j z)).det
        * (Matrix.of V).det * (Matrix.of (Finvf (I := I) (M := M) D j z)).det := by
    rw [show Matrix.of (tmGK (I := I) (M := M) D j z V)
        = Matrix.of (Finvf (I := I) (M := M) D j z) * Matrix.of V
          * (Matrix.of (Finvf (I := I) (M := M) D j z))ᵀ from rfl]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  rw [hmain, hFin]
  ring

/-! ## 3. The separators -/

/-- The bump `tmClampBump a b ha hab` equals `1` on `[a,b]`. -/
lemma tms_beta_one (a b t : ℝ) (ha : 0 < a) (hab : a < b) (hat : a ≤ t) (htb : t ≤ b) :
    tmClampBump (n := Module.finrank ℝ E) a b ha hab t = 1 := by
  have hmem : t ∈ Metric.closedBall ((a + b) / 2) ((b - a) / 2) := by
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> linarith
  have h := ContDiffBump.one_of_mem_closedBall
    (⟨(b - a) / 2, b / 2, by linarith, by linarith⟩ : ContDiffBump ((a + b) / 2)) hmem
  simpa only [tmClampBump] using h

/-- The bump `tmClampBump a b ha hab` is supported away from `0`. -/
lemma tms_beta_tsupport (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    tsupport (tmClampBump (n := Module.finrank ℝ E) a b ha hab) ⊆ {t : ℝ | t ≠ 0} := by
  have hbump : tmClampBump (n := Module.finrank ℝ E) a b ha hab
      = ⇑(⟨(b - a) / 2, b / 2, by linarith, by linarith⟩ : ContDiffBump ((a + b) / 2)) := rfl
  intro t ht
  rw [hbump, ContDiffBump.tsupport_eq] at ht
  simp only [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] at ht
  intro h0
  rw [h0, zero_sub, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (a + b) / 2)] at ht
  linarith

/-- The bump `tmClampBump a b ha hab` is `C^∞`. -/
lemma tms_beta_smooth (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
      (tmClampBump (n := Module.finrank ℝ E) a b ha hab) :=
  (⟨(b - a) / 2, b / 2, by linarith, by linarith⟩ : ContDiffBump ((a + b) / 2)).contDiff (n := ⊤)

/-- A `C^∞` bump on the flat coordinate, equal to `1` on the closed `2σ j` ball and supported on
`tmsGood D j` (in particular on the chart target, so that all the chart data is smooth there). -/
lemma tms_exists_zeta (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    ∃ ζ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ,
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) ζ ∧
      (∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j → ζ z = 1) ∧
      tsupport ζ ⊆ tmsGood D j := by
  haveI : SigmaCompactSpace (Fin (Module.finrank ℝ E) → ℝ) := inferInstance
  have hK : IsCompact (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j)) :=
    isCompact_closedBall _ _
  have hKU : Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j)
      ⊆ tmsGood D j := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact ⟨D.htarget j z hz, det_Ff_ne_zero (I := I) (M := M) D j hz⟩
  obtain ⟨ε, hεpos, hε⟩ := hK.exists_cthickening_subset_open (tms_good_isOpen D j) hKU
  obtain ⟨f, hf0, hf1, _hf01⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed (I := 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ))
      (M := Fin (Module.finrank ℝ E) → ℝ) (n := ⊤)
      (s := (Metric.thickening ε (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ)
        (2 * D.σ j)))ᶜ)
      (t := Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j))
      Metric.isOpen_thickening.isClosed_compl hK.isClosed
      (Set.disjoint_left.mpr fun x hx hxK => hx (Metric.self_subset_thickening hεpos _ hxK))
  refine ⟨fun z => f z, contMDiff_iff_contDiff.mp f.contMDiff, ?_, ?_⟩
  · intro z hz
    exact hf1 (by rw [Metric.mem_closedBall, dist_zero_right]; exact hz)
  · have hsupp : Function.support (fun z => f z) ⊆
        Metric.thickening ε (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j)) := by
      intro z hz
      by_contra hz'
      exact hz (hf0 hz')
    intro z hz
    exact hε (Metric.closure_thickening_subset_cthickening ε _ (closure_mono hsupp hz))

/-! ## 4. The state membership -/

/-- The locus `tmsDom D j` is a neighbourhood of every state that satisfies its three conditions. -/
lemma tms_dom_mem_nhds (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {w : TmsSt E}
    (h1 : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target)
    (h2 : (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0)
    (h3 : (Matrix.of w.2.1).det ≠ 0) :
    tmsDom D j ∈ nhds w := by
  have hA : ∀ᶠ x in nhds w, Work.Diff.STE.flatToE (I := I) (D.x₀ j) x.1 ∈
      (extChartAt I (D.x₀ j)).target := by
    have hcont : Continuous (fun x : TmsSt E => Work.Diff.STE.flatToE (I := I) (D.x₀ j) x.1) :=
      (Work.Diff.STE.contDiff_flatToE (I := I) (D.x₀ j)).continuous.comp continuous_fst
    exact hcont.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_target (I := I) (D.x₀ j)).mem_nhds h1)
  have hB : ∀ᶠ x in nhds w, (Matrix.of (Ff (I := I) (M := M) D j x.1)).det ≠ 0 :=
    ((tms_contDiffAt_det_Ff D j h1).comp w contDiffAt_fst).continuousAt.preimage_mem_nhds
      (isOpen_ne.mem_nhds h2)
  have hC : ∀ᶠ x in nhds w, (Matrix.of x.2.1).det ≠ 0 :=
    (tms_contDiffAt_det_V (E := E) (w := w)).continuousAt.preimage_mem_nhds
      (isOpen_ne.mem_nhds h3)
  filter_upwards [hA, hB, hC] with x hx1 hx2 hx3
  exact ⟨hx1, hx2, hx3⟩

/-! ## 5. The function `Φ` and its smoothness -/

/-- The function `Φ` of the target: `tmPsi` multiplied by the two separators. -/
def tmsPhiFun (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (ζ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) :
    TmsSt E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun w a' b' =>
    ζ w.1 * (tmClampBump (n := Module.finrank ℝ E) a b ha hab
      ((Matrix.of (tmGK (I := I) (M := M) D j w.1 w.2.1)).det)
      * tmPsi (I := I) (M := M) D j a b ha hab w.1 w.2.1 w.2.2 a' b')

/-- **Smoothness of the scalar components of `Φ`.**  Away from the support of the coordinate cutoff
`ζ` the function vanishes; otherwise it is the product of smooth factors, the middle one being
either `1`-times-a-smooth-`tmPsi` (where `det (tmGK z V) ≠ 0`, the differential domain of `tmPsi`)
or `0` on a whole neighbourhood (where the separator bump vanishes, which happens in particular
wherever the frame-change determinant `det (tmGK z V) = (det (Ff z))⁻¹ ^ 2 * det V` is `0`). -/
lemma tmsPhi_scalar_smooth (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (ζ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hζ : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) ζ)
    (hζsupp : tsupport ζ ⊆ tmsGood D j)
    (hpsi : ∀ a' b' : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
        (fun w : TmsSt E => tmPsi (I := I) (M := M) D j a b ha hab w.1 w.2.1 w.2.2 a' b')
        (tmsDom D j))
    (a' b' : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
      (fun w : TmsSt E => tmsPhiFun D j a b ha hab ζ w a' b') := by
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : w.1 ∈ tsupport ζ
  · have hgood : w.1 ∈ tmsGood D j := hζsupp hw
    obtain ⟨hzt, hzdet⟩ := hgood
    have hdetfun : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun w' : TmsSt E => (Matrix.of (tmGK (I := I) (M := M) D j w'.1 w'.2.1)).det) w :=
      tms_contDiffAt_det_tmGK D j hzt hzdet
    by_cases hdet0 : (Matrix.of (tmGK (I := I) (M := M) D j w.1 w.2.1)).det
        ∈ tsupport (tmClampBump (n := Module.finrank ℝ E) a b ha hab)
    · have hne : (Matrix.of (tmGK (I := I) (M := M) D j w.1 w.2.1)).det ≠ 0 :=
        tms_beta_tsupport (E := E) a b ha hab hdet0
      have hVne : (Matrix.of w.2.1).det ≠ 0 := by
        intro h0
        exact hne (by rw [tms_det_tmGK_eq D j hzdet, h0, mul_zero])
      have h1 : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
          (fun w' : TmsSt E => tmPsi (I := I) (M := M) D j a b ha hab w'.1 w'.2.1 w'.2.2 a' b')
          w :=
        (hpsi a' b').contDiffAt (tms_dom_mem_nhds D j hzt hzdet hVne)
      have h2 : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
          (fun w' : TmsSt E => tmClampBump (n := Module.finrank ℝ E) a b ha hab
            ((Matrix.of (tmGK (I := I) (M := M) D j w'.1 w'.2.1)).det)) w :=
        (tms_beta_smooth (E := E) a b ha hab).contDiffAt.comp w hdetfun
      have h3 : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
          (fun w' : TmsSt E => ζ w'.1) w := hζ.contDiffAt.comp w contDiffAt_fst
      refine (h3.mul (h2.mul h1)).congr_of_eventuallyEq ?_
      exact Filter.EventuallyEq.of_eq (funext fun w' => rfl)
    · have hpre : (fun w' : TmsSt E =>
            (Matrix.of (tmGK (I := I) (M := M) D j w'.1 w'.2.1)).det) ⁻¹'
          (tsupport (tmClampBump (n := Module.finrank ℝ E) a b ha hab))ᶜ ∈ nhds w :=
        hdetfun.continuousAt.preimage_mem_nhds
          ((isClosed_tsupport (tmClampBump (n := Module.finrank ℝ E) a b ha hab)).isOpen_compl.mem_nhds
            hdet0)
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hpre] with w' hw'
      simp only [tmsPhiFun, image_eq_zero_of_notMem_tsupport hw', mul_zero, zero_mul]
  · have hzeta0 : ∀ᶠ w' in nhds w, ζ w'.1 = 0 := by
      have hnb : (tsupport ζ)ᶜ ∈ nhds w.1 := (isClosed_tsupport ζ).isOpen_compl.mem_nhds hw
      filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hnb] with w' hw'
      exact image_eq_zero_of_notMem_tsupport hw'
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hzeta0] with w' hw'
    simp only [tmsPhiFun, hw', zero_mul]

/-- **`Φ` is globally `C^∞`.** -/
lemma tmsPhi_smooth (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (ζ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hζ : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) ζ)
    (hζsupp : tsupport ζ ⊆ tmsGood D j)
    (hpsi : ∀ a' b' : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
        (fun w : TmsSt E => tmPsi (I := I) (M := M) D j a b ha hab w.1 w.2.1 w.2.2 a' b')
        (tmsDom D j)) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (tmsPhiFun D j a b ha hab ζ) := by
  rw [contDiff_pi]
  intro a'
  rw [contDiff_pi]
  intro b'
  exact tmsPhi_scalar_smooth D j a b ha hab ζ hζ hζsupp hpsi a' b'

/-! ## 6. The identity clause -/

/-- On the closed `2σ j` ball, `Φ` reproduces `tmPsi` evaluated at the chart data of any section
`h` whose chart matrix has determinant in the window `[a,b]`. -/
lemma tmsPhi_identity (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (ζ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hζ1 : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j → ζ z = 1)
    (R : ℝ) (hR2 : 2 * D.σ j ≤ R)
    (htgt : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ R →
      Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target)
    (hreg : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ R →
      (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hwin : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j →
      a ≤ (Matrix.of (fun i k : Fin (Module.finrank ℝ E) =>
            Gf (I := I) (M := M) D h j z i k)).det ∧
      (Matrix.of (fun i k : Fin (Module.finrank ℝ E) =>
            Gf (I := I) (M := M) D h j z i k)).det ≤ b)
    (z : Fin (Module.finrank ℝ E) → ℝ) (hz : ‖z‖ ≤ 2 * D.σ j)
    (a' b' : Fin (Module.finrank ℝ E)) :
    tmsPhiFun D j a b ha hab ζ
        (z, Mf (I := I) (M := M) D h j z,
          fun c d r => Work.Diff.STE.pdR r (D.mat j h c d) z) a' b'
      = tmPsi (I := I) (M := M) D j a b ha hab z (fun c d => D.mat j h c d z)
          (fun c d r => Work.Diff.STE.pdR r (D.mat j h c d) z) a' b' := by
  have hzR : ‖z‖ ≤ R := le_trans hz hR2
  have hg := tmGK_eq_Gf (I := I) (M := M) D h j z (htgt z hzR) (hreg z hzR)
  have hβ : tmClampBump (n := Module.finrank ℝ E) a b ha hab
      ((Matrix.of (tmGK (I := I) (M := M) D j z (Mf (I := I) (M := M) D h j z))).det) = 1 := by
    rw [hg]
    exact tms_beta_one a b _ ha hab (hwin z hz).1 (hwin z hz).2
  have hMf : Mf (I := I) (M := M) D h j z = fun c d => D.mat j h c d z := rfl
  have hsimp : tmsPhiFun D j a b ha hab ζ
      (z, Mf (I := I) (M := M) D h j z,
        fun c d r => Work.Diff.STE.pdR r (D.mat j h c d) z) a' b'
      = tmPsi (I := I) (M := M) D j a b ha hab z (Mf (I := I) (M := M) D h j z)
          (fun c d r => Work.Diff.STE.pdR r (D.mat j h c d) z) a' b' := by
    simp only [tmsPhiFun, hζ1 z hz, hβ, one_mul]
  rw [hsimp, hMf]

/-! ## 7. The compact box -/

/-- The compact box of states on which the jet bounds of the target are required. -/
def tmsBox (R MV MW : ℝ) : Set (TmsSt E) :=
  Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) R ×ˢ
    (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) MV ×ˢ
      Metric.closedBall (0 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
        Fin (Module.finrank ℝ E) → ℝ) MW)

lemma tmsBox_isCompact (R MV MW : ℝ) : IsCompact (tmsBox (E := E) R MV MW) :=
  (isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))

lemma tmsBox_mem {R MV MW : ℝ} (hMV : 0 ≤ MV) (hMW : 0 ≤ MW)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    {V : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ}
    {W : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ}
    (hz : ‖z‖ ≤ R) (hV : ∀ p q : Fin (Module.finrank ℝ E), |V p q| ≤ MV)
    (hW : ∀ p q r : Fin (Module.finrank ℝ E), |W p q r| ≤ MW) :
    (z, V, W) ∈ tmsBox (E := E) R MV MW := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]; exact hz
  · rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hMV]
    intro p
    rw [pi_norm_le_iff_of_nonneg hMV]
    intro q
    show ‖V p q‖ ≤ MV
    rw [Real.norm_eq_abs]
    exact hV p q
  · rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hMW]
    intro p
    rw [pi_norm_le_iff_of_nonneg hMW]
    intro q
    rw [pi_norm_le_iff_of_nonneg hMW]
    intro r
    show ‖W p q r‖ ≤ MW
    rw [Real.norm_eq_abs]
    exact hW p q r

/-! ## 8. The jets bound -/

/-- The componentwise version of `Φ` is `C^∞` when `Φ` is. -/
lemma tms_contDiff_proj {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {ι : Type*} [Fintype ι] {Φ : X → ι → ι → ℝ}
    (hΦ : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) Φ) (a' b' : ι) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun q : X => Φ q a' b') :=
  ((contDiff_pi.mp ((contDiff_pi.mp hΦ) a')) b')

/-- The iterated derivatives of a component of `Φ` are continuous. -/
lemma tms_component_continuous {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {ι : Type*} [Fintype ι] {Φ : X → ι → ι → ℝ}
    (hΦ : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) Φ) (k : ℕ) (a' b' : ι) :
    Continuous (fun p : X => iteratedFDeriv ℝ k (fun q : X => Φ q a' b') p) :=
  ContDiff.continuous_iteratedFDeriv (m := k)
    (by exact WithTop.coe_le_coe.mpr le_top) (tms_contDiff_proj hΦ a' b')

/-- **A uniform bound for a finite family of functions, each bounded on the same set.** -/
lemma tms_finite_max_bound {ι X : Type*} [Fintype ι] {K : Set X} (f : ι → X → ℝ)
    (h : ∀ i, ∃ C, 0 ≤ C ∧ ∀ p ∈ K, f i p ≤ C) :
    ∃ C, 0 ≤ C ∧ ∀ i, ∀ p ∈ K, f i p ≤ C := by
  classical
  have key : ∀ s : Finset ι, ∃ C, 0 ≤ C ∧ ∀ i ∈ s, ∀ p ∈ K, f i p ≤ C := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · exact ⟨0, le_refl 0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    · intro a s ha ih
      obtain ⟨C, hC0, hC⟩ := ih
      obtain ⟨Ca, hCa0, hCa⟩ := h a
      refine ⟨max Ca C, le_max_of_le_left hCa0, ?_⟩
      intro i hi p hp
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact le_trans (hCa p hp) (le_max_left _ _)
      · exact le_trans (hC i hi p hp) (le_max_right _ _)
  obtain ⟨C, hC0, hC⟩ := key Finset.univ
  exact ⟨C, hC0, fun i p hp => hC i (Finset.mem_univ i) p hp⟩

/-- **The jet bounds**: for a globally `C^∞` `Φ` and a compact set `K`, the iterated derivatives
of the components of `Φ` are uniformly bounded on `K` by a sequence `D'` depending only on `Φ` and
`K`. -/
lemma tms_compact_jet_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {ι : Type*} [Fintype ι]
    (Φ : X → ι → ι → ℝ) (hΦ : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) Φ)
    (K : Set X) (hK : IsCompact K) :
    ∃ D' : ℕ → ℝ, (∀ m : ℕ, 0 ≤ D' m) ∧
      ∀ (m k : ℕ), k ≤ m → ∀ (p : X) (a' b' : ι), p ∈ K →
        ‖iteratedFDeriv ℝ k (fun q : X => Φ q a' b') p‖ ≤ D' m := by
  classical
  have key : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Fin (m + 1)) (a' b' : ι) (p : X), p ∈ K →
      ‖iteratedFDeriv ℝ (k : ℕ) (fun q : X => Φ q a' b') p‖ ≤ C := by
    intro m
    have hpt : ∀ j : Fin (m + 1) × ι × ι, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K,
        ‖iteratedFDeriv ℝ (j.1 : ℕ) (fun q : X => Φ q j.2.1 j.2.2) p‖ ≤ C := by
      intro j
      obtain ⟨Cj, hCj⟩ := hK.exists_bound_of_continuousOn
        (f := fun p : X => iteratedFDeriv ℝ (j.1 : ℕ) (fun q : X => Φ q j.2.1 j.2.2) p)
        ((tms_component_continuous hΦ (j.1 : ℕ) j.2.1 j.2.2).continuousOn)
      exact ⟨max Cj 0, le_max_right _ _, fun p hp => le_trans (hCj p hp) (le_max_left _ _)⟩
    obtain ⟨C, hC0, hC⟩ := tms_finite_max_bound (K := K) (ι := Fin (m + 1) × ι × ι)
      (f := fun j : Fin (m + 1) × ι × ι => fun p : X => ‖iteratedFDeriv ℝ (j.1 : ℕ)
        (fun q : X => Φ q j.2.1 j.2.2) p‖) hpt
    exact ⟨C, hC0, fun k a' b' p hp => hC (k, a', b') p hp⟩
  choose D' hD'0 hD' using key
  exact ⟨D', hD'0, fun m k hkm p a' b' hp => hD' m ⟨k, Nat.lt_succ_of_le hkm⟩ a' b' p hp⟩

/-! ## 9. The target -/

theorem tmPsi_exists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (j : ι₀) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (R : ℝ) (hR : 0 < R) (hR2 : 2 * D.σ j ≤ R)
    (htgt : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ R →
      Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target)
    (hreg : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ R →
      (Matrix.of (Work.Diff.STE.B3.Ff (I := I) (M := M) D j z)).det ≠ 0)
    (MV MW : ℝ) (hMV : 0 ≤ MV) (hMW : 0 ≤ MW) :
    ∃ (Φ : ((Fin (Module.finrank ℝ E) → ℝ) ×
            (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) ×
            (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
              Fin (Module.finrank ℝ E) → ℝ)) →
          Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
      (D' : ℕ → ℝ),
      (∀ m : ℕ, 0 ≤ D' m) ∧
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) Φ ∧
      (∀ (m : ℕ) (k : ℕ), k ≤ m →
        ∀ (z : Fin (Module.finrank ℝ E) → ℝ)
          (V : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
          (W : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
            Fin (Module.finrank ℝ E) → ℝ)
          (a' b' : Fin (Module.finrank ℝ E)),
          ‖z‖ ≤ R → (∀ p q : Fin (Module.finrank ℝ E), |V p q| ≤ MV) →
          (∀ p q r : Fin (Module.finrank ℝ E), |W p q r| ≤ MW) →
          ‖iteratedFDeriv ℝ k (fun p : (Fin (Module.finrank ℝ E) → ℝ) ×
              (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) ×
              (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
                Fin (Module.finrank ℝ E) → ℝ) => Φ p a' b')
            (z, V, W)‖ ≤ D' m) ∧
      (∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hwin : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j →
          a ≤ (Matrix.of (fun i k : Fin (Module.finrank ℝ E) =>
                Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k)).det ∧
          (Matrix.of (fun i k : Fin (Module.finrank ℝ E) =>
                Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k)).det ≤ b)
        (hVb : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ R →
          ∀ p q : Fin (Module.finrank ℝ E), |D.mat j h p q z| ≤ MV)
        (hWb : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ R →
          ∀ p q r : Fin (Module.finrank ℝ E),
            |Work.Diff.STE.pdR r (D.mat j h p q) z| ≤ MW),
        ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j →
        ∀ a' b' : Fin (Module.finrank ℝ E),
        Φ (z, (fun c d => D.mat j h c d z),
            (fun c d r => Work.Diff.STE.pdR r (D.mat j h c d) z)) a' b'
          = Work.Diff.STE.B3.tmPsi (I := I) (M := M) D j a b ha hab z
              (fun c d => D.mat j h c d z)
              (fun c d r => Work.Diff.STE.pdR r (D.mat j h c d) z) a' b') := by
  classical
  obtain ⟨ζ, hζ, hζ1, hζsupp⟩ := tms_exists_zeta (I := I) (M := M) (g₀ := g₀) D j
  have hpsi : ∀ a' b' : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
        (fun w : TmsSt E => tmPsi (I := I) (M := M) D j a b ha hab w.1 w.2.1 w.2.2 a' b')
        (tmsDom D j) := fun a' b' => tmPsi_state_contDiffOn D j a b ha hab a' b'
  have hcont : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (tmsPhiFun D j a b ha hab ζ) :=
    tmsPhi_smooth D j a b ha hab ζ hζ hζsupp hpsi
  obtain ⟨D', hD'0, hD'⟩ :=
    tms_compact_jet_bound (tmsPhiFun D j a b ha hab ζ) hcont
      (tmsBox (E := E) R MV MW) (tmsBox_isCompact R MV MW)
  refine ⟨tmsPhiFun D j a b ha hab ζ, D', hD'0, hcont, ?_, ?_⟩
  · intro m k hkm z V W a' b' hz hV hW
    exact hD' m k hkm (z, V, W) a' b' (tmsBox_mem hMV hMW hz hV hW)
  · intro h hwin hVb hWb z hz a' b'
    exact tmsPhi_identity D j a b ha hab ζ hζ1 R hR2 htgt hreg h hwin z hz a' b'

end

end Work.Diff.STE.B3
