/-
# Auxiliary lemmas for the assembly of `transport_deTurck_general`

This file collects the lemmas that the final assembly of
`Work.Diff.STE.B3.transport_deTurck_general` needs and that are independent of the section `h`:

* smoothness of the determinant as a function of the entries of a matrix;
* a **real-valued, general-codomain** version of the cutoff lemma
  `Work.Diff.STE.B3.contDiff_mul_cutoff` (a smooth bump times a function that is smooth on the
  pullback of an open set along a projection is smooth);
* the symmetry of the clamped inverse `tmGKi` for a symmetric state matrix, which supplies the
  symmetry hypothesis of `Work.Diff.STE.B3.tmA_props_weak`;
* the smoothness of the state data `z ↦ (z, Mf z)` of a section and of the composite coefficient
  family `γ z = tmGKi (z, Mf z)`;
* the **uniform composite jet bounds** for the coefficient family `γ` and for the residual state map
  `(z, Mf z, ∂Mf z) ↦ tmPsi …`, obtained from `Work.Diff.STE.B3.compJetBoundB3`.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.TransportAux
import Submission.Work.Diff.STE.B3.tmA_props_weak
import Submission.Work.Diff.STE.B3.compJetBoundB3
import Submission.Work.Diff.STE.B3.tmGKi_state_contDiffOn
import Submission.Work.Diff.STE.B3.tmPsi_state_contDiffOn
import Submission.Work.Diff.STE.B3.mat_jet_bound_global
import Submission.Work.Diff.STE.B3.transport_tame_defs
import Submission.Work.Diff.STE.B3.transport_exists_cutoff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The flat-coordinate index type. -/
local notation "Idx" => Fin (Module.finrank ℝ E)

/-! ## 1. The determinant is a smooth function of the entries -/

/-- The determinant of a matrix is a smooth function of its entries. -/
lemma det_entry_contDiff {n : ℕ} :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
      (fun V : Fin n → Fin n → ℝ => (Matrix.of V).det) := by
  have h : (fun V : Fin n → Fin n → ℝ => (Matrix.of V).det)
      = fun V => ∑ σ : Equiv.Perm (Fin n), (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, V (σ i) i := by
    funext V
    rw [Matrix.det_apply']
    simp only [Matrix.of_apply]
  rw [h]
  fun_prop

/-- The `0`-jet of a function is the function itself. -/
lemma pdVec_zero_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (l : Fin 0 → ι) (f : (ι → ℝ) → ℂ) :
    Work.Diff.STE.pdVec 0 l f = f := by
  rw [Work.Diff.STE.pdVec, Work.Diff.STE.pdList, List.ofFn_zero, List.foldr_nil]

/-- **`pdVec` only depends on the germ.**  Two functions that agree near `x` have the same iterated
partial derivatives at `x`.  (A local copy of `Work.Diff.STE.B3.pdVec_congr_germ`.) -/
theorem pdVec_congr_germ_loc {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f g : (ι → ℝ) → ℂ} {x : ι → ℝ} (h : f =ᶠ[nhds x] g) (m : ℕ) (l : Fin m → ι) :
    Work.Diff.STE.pdVec m l f x = Work.Diff.STE.pdVec m l g x := by
  have hpd : ∀ (k : ℕ) (l : Fin (k + 1) → ι) (u : (ι → ℝ) → ℂ),
      Work.Diff.STE.pdVec (k + 1) l u
        = Work.Diff.STE.pd (l 0) (Work.Diff.STE.pdVec k (Fin.tail l) u) := by
    intro k l u
    have h0 : List.ofFn l = l 0 :: List.ofFn (Fin.tail l) := by
      conv_lhs => rw [← Fin.cons_self_tail l]
      rw [List.ofFn_cons]
    simp only [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]
    rw [h0, List.foldr_cons]
  suffices H : ∀ m (l : Fin m → ι),
      Work.Diff.STE.pdVec m l f =ᶠ[nhds x] Work.Diff.STE.pdVec m l g by
    exact (H m l).eq_of_nhds
  intro m
  induction m with
  | zero =>
      intro l
      rw [pdVec_zero_eq l f, pdVec_zero_eq l g]
      exact h
  | succ k ih =>
      intro l
      rw [hpd k l f, hpd k l g]
      have hfd : fderiv ℝ (Work.Diff.STE.pdVec k (Fin.tail l) f)
          =ᶠ[nhds x] fderiv ℝ (Work.Diff.STE.pdVec k (Fin.tail l) g) :=
        Filter.EventuallyEq.fderiv (𝕜 := ℝ) (ih (Fin.tail l))
      filter_upwards [hfd] with y hy
      change fderiv ℝ (Work.Diff.STE.pdVec k (Fin.tail l) f) y (Pi.single (l 0) 1)
        = fderiv ℝ (Work.Diff.STE.pdVec k (Fin.tail l) g) y (Pi.single (l 0) 1)
      rw [hy]

/-! ## 2. A real-valued cutoff lemma with an arbitrary projection -/

/-- **A smooth bump times a locally smooth function is smooth** (real-valued, arbitrary projection).

Let `pr : P → X` be smooth, `χ : X → ℝ` a smooth cutoff whose `tsupport` lies in the open set `U`,
and `ψ : P → ℝ` a function smooth on `pr ⁻¹' U`.  Then `p ↦ χ (pr p) * ψ p` is smooth on all of `P`.

This is the real-valued version of `Work.Diff.STE.B3.contDiff_mul_cutoff` with the projection landing
in an arbitrary normed space rather than in `Fin n → ℝ`. -/
theorem contDiff_mul_cutoff_real {X P : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (pr : P → X) (hpr : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) pr)
    (χ : X → ℝ) (hχsm : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) χ)
    (ψ : P → ℝ) {U : Set X} (hU : IsOpen U)
    (hψ : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) ψ (pr ⁻¹' U))
    (hsupp : tsupport χ ⊆ U) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun p : P => χ (pr p) * ψ p) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : pr p ∈ U
  · have hnhds : pr ⁻¹' U ∈ nhds p :=
      hpr.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hp)
    have hψ' : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) ψ p := hψ.contDiffAt hnhds
    have hχ' : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) (fun q : P => χ (pr q)) p :=
      (hχsm.contDiffAt).comp p hpr.contDiffAt
    exact hχ'.mul hψ'
  · have hnotin : pr p ∉ tsupport χ := fun h => hp (hsupp h)
    have hopen : IsOpen (tsupport χ)ᶜ := isClosed_closure.isOpen_compl
    have hnhds : pr ⁻¹' (tsupport χ)ᶜ ∈ nhds p :=
      hpr.continuous.continuousAt.preimage_mem_nhds (hopen.mem_nhds hnotin)
    refine ContDiffAt.congr_of_eventuallyEq (f := fun _ : P => (0 : ℝ)) contDiffAt_const ?_
    refine Filter.eventually_of_mem hnhds ?_
    intro q hq
    simp only [Set.mem_preimage, Set.mem_compl_iff] at hq
    show χ (pr q) * ψ q = (0 : ℝ)
    rw [image_eq_zero_of_notMem_tsupport hq, zero_mul]

/-! ## 2b. A cutoff with all four properties -/

/-- **A smooth cutoff for a compact set inside an open set**, with values in `[0,1]`.

This is `Work.Diff.STE.B3.transport_exists_cutoff` with the additional conclusion `η ≤ 1`, which the
periodisation `Work.Diff.STE.B3.tmA` needs. -/
theorem exists_cutoff_le_one {n : ℕ} (K U : Set (Fin n → ℝ)) (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ η : (Fin n → ℝ) → ℝ, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) η ∧
      (∀ z, 0 ≤ η z) ∧ (∀ z, η z ≤ 1) ∧ (∀ z ∈ K, η z = 1) ∧ tsupport η ⊆ U := by
  obtain ⟨δ, hδpos, hδ⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨f, hf0, hf1, hf01⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed (I := 𝓘(ℝ, Fin n → ℝ)) (M := Fin n → ℝ) (n := ⊤)
      (s := (Metric.thickening δ K)ᶜ) (t := K)
      Metric.isOpen_thickening.isClosed_compl
      hK.isClosed
      (Set.disjoint_left.mpr fun x hx hxK => hx (Metric.self_subset_thickening hδpos K hxK))
  refine ⟨fun z => f z, ?_, fun z => (hf01 z).1, fun z => (hf01 z).2, fun z hz => hf1 hz, ?_⟩
  · exact contMDiff_iff_contDiff.mp f.contMDiff
  · have hsupp : Function.support (fun z => f z) ⊆ Metric.thickening δ K := by
      intro w hw
      by_contra hw'
      exact hw (hf0 hw')
    intro z hz
    exact hδ (Metric.closure_thickening_subset_cthickening δ K (closure_mono hsupp hz))

/-! ## 3. Symmetry of `tmGK` and of the clamped inverse -/

/-- The nominal coordinate chart matrix of a symmetric state matrix is symmetric. -/
lemma tmGK_symm (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Idx → ℝ) (V : Idx → Idx → ℝ) (hV : ∀ p q, V p q = V q p) :
    tmGK (I := I) (M := M) D j z V = (tmGK (I := I) (M := M) D j z V)ᵀ := by
  have hVs : (Matrix.of V : Matrix Idx Idx ℝ)ᵀ = Matrix.of V := by
    ext p q
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    exact hV q p
  show Matrix.of (Finvf (I := I) (M := M) D j z) * Matrix.of V
      * (Matrix.of (Finvf (I := I) (M := M) D j z))ᵀ
    = (Matrix.of (Finvf (I := I) (M := M) D j z) * Matrix.of V
      * (Matrix.of (Finvf (I := I) (M := M) D j z))ᵀ)ᵀ
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hVs, Matrix.mul_assoc]

/-- The clamped inverse of a symmetric matrix is symmetric. -/
lemma tmInv_symm {n : ℕ} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) : tmInv a b ha hab A = (tmInv a b ha hab A)ᵀ := by
  have h1 : (A⁻¹)ᵀ = A⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hA]
  unfold tmInv
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one, h1]

/-- **The clamped inverse `tmGKi` is symmetric in a symmetric state matrix.** -/
lemma tmGKi_symm (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (z : Idx → ℝ) (V : Idx → Idx → ℝ) (hV : ∀ p q, V p q = V q p) (p q : Idx) :
    tmGKi (I := I) (M := M) D j a b ha hab z V p q
      = tmGKi (I := I) (M := M) D j a b ha hab z V q p := by
  show tmInv a b ha hab (tmGK (I := I) (M := M) D j z V) p q
      = tmInv a b ha hab (tmGK (I := I) (M := M) D j z V) q p
  have hsym := tmInv_symm (n := Module.finrank ℝ E) a b ha hab
    (tmGK (I := I) (M := M) D j z V) (tmGK_symm (I := I) (M := M) D j z V hV).symm
  have h := congrFun (congrFun hsym q) p
  simp only [Matrix.transpose_apply] at h
  exact h.symm

/-! ## 4. The smoothness of the state data of a section -/

/-- The ON-frame chart matrix of a section is smooth on the ball (as a matrix-valued map). -/
lemma Mf_contDiffOn (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀) {R : ℝ}
    (hR : ∀ z : Idx → ℝ, ‖z‖ < R → Work.Diff.STE.flatToE (I := I) (D.x₀ j) z
      ∈ (extChartAt I (D.x₀ j)).target) :
    ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
      (fun z : Idx → ℝ => Mf (I := I) (M := M) D h j z) (Metric.ball 0 R) := by
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
  exact ((contDiffAt_pi).mpr (fun p => (contDiffAt_pi).mpr (fun q =>
    mat_contDiffAt_of_chartData (I := I) (M := M) D h hsmooth j p q z (hR z hz)))).contDiffWithinAt

/-- The state map `z ↦ (z, Mf z)` of a section is smooth on the ball. -/
lemma Mf_state_contDiffOn (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀) {R : ℝ}
    (hR : ∀ z : Idx → ℝ, ‖z‖ < R → Work.Diff.STE.flatToE (I := I) (D.x₀ j) z
      ∈ (extChartAt I (D.x₀ j)).target) :
    ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
      (fun z : Idx → ℝ => (z, Mf (I := I) (M := M) D h j z)) (Metric.ball 0 R) :=
  ContDiffOn.prodMk contDiff_id.contDiffOn (Mf_contDiffOn D h hsmooth j hR)

/-- The coefficient family `γ z = tmGKi (z, Mf z)` is smooth on the ball. -/
lemma tmGKi_comp_Mf_contDiffOn (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) {R : ℝ}
    (hRreg : ∀ z : Idx → ℝ, ‖z‖ < R →
      (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target ∧
        (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0)) (p q : Idx) :
    ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
      (fun z : Idx → ℝ => tmGKi (I := I) (M := M) D j a b ha hab z
        (Mf (I := I) (M := M) D h j z) p q) (Metric.ball 0 R) :=
  ((tmGKi_state_contDiffOn (I := I) (M := M) D j a b ha hab p q).comp
    (Mf_state_contDiffOn D h hsmooth j (fun z hz => (hRreg z hz).1))
    (fun z hz => by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
      exact hRreg z hz)).congr (fun z _ => rfl)

/-! ## 5. Uniform composite jet bounds -/

/-- The smoothness of the state function `(z, V, W) ↦ tmGKi z V p q` on the states of interest: the
flat coordinate in the chart target (so that the frame is available) with the frame matrix
invertible, and any state matrix. -/
lemma tmGKi_state3_contDiffOn (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) {R' : ℝ}
    (hRreg : ∀ z : Idx → ℝ, ‖z‖ < R' →
      (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target ∧
        (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0)) (p q : Idx) :
    ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
      (fun w : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) =>
        ((tmGKi (I := I) (M := M) D j a b ha hab w.1 w.2.1 p q : ℝ) : ℂ))
      {w : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
        ‖w.1‖ < R' ∧ (Matrix.of w.2.1).det ≠ 0} := by
  have hpr : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
      (fun w : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) => (w.1, w.2.1))
      {w : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
        ‖w.1‖ < R' ∧ (Matrix.of w.2.1).det ≠ 0} :=
    (ContDiff.prodMk contDiff_fst (contDiff_fst.comp contDiff_snd)).contDiffOn
  have hmap : MapsTo
      (fun w : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) => (w.1, w.2.1))
      {w : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
        ‖w.1‖ < R' ∧ (Matrix.of w.2.1).det ≠ 0}
      {w : (Idx → ℝ) × (Idx → Idx → ℝ) |
        Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target ∧
          (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0} :=
    fun w hw => hRreg w.1 hw.1
  exact (Complex.ofRealCLM.contDiff.comp_contDiffOn
    ((tmGKi_state_contDiffOn (I := I) (M := M) D j a b ha hab p q).comp hpr hmap)).congr
    (fun w _ => rfl)

/-- **Uniform jet bound for the coefficient family `γ z = tmGKi (z, Mf z)`.**

For every pair of indices, the `pdVec`-jets of `z ↦ tmGKi (z, Mf z) p q` up to order `k` are bounded
on the closed ball of radius `R` by a constant that is uniform in the section `h`; it depends only on
`D`, `j`, the clamp window, the radii `R < R'`, the ellipticity constant `lam` of `Mf` on `‖z‖ < R'`
and the jet bound `KG` of `Mf` up to order `k + 1`. -/
theorem tmGKi_comp_jets_bound
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) {R R' : ℝ} (hRR' : R < R')
    (hRreg : ∀ z : Idx → ℝ, ‖z‖ < R' →
      (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target ∧
        (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0))
    {lam KG : ℝ} (hlam : 0 < lam) (hKG : 0 ≤ KG) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : (Idx → ℝ) → Idx → Idx → ℝ),
        (∀ s t : Idx, ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
          (fun z : Idx → ℝ => u z s t) {z : Idx → ℝ | ‖z‖ < R'}) →
        (∀ z : Idx → ℝ, ‖z‖ < R' → ∀ ξ : Idx → ℝ,
          lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j', u z i j' * ξ i * ξ j') →
        (∀ (m : ℕ) (hm : m ≤ k + 1) (β : Fin m → Idx) (z : Idx → ℝ) (s t : Idx),
          ‖z‖ < R' →
          ‖Work.Diff.STE.pdVec m β (fun y : Idx → ℝ => ((u y s t : ℝ) : ℂ)) z‖ ≤ KG) →
        ∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Idx) (z : Idx → ℝ), ‖z‖ ≤ R → ∀ p q : Idx,
          ‖Work.Diff.STE.pdVec m β (fun y : Idx → ℝ =>
            ((tmGKi (I := I) (M := M) D j a b ha hab y (u y) p q : ℝ) : ℂ)) z‖ ≤ C := by
  classical
  have hbound : ∀ p q : Idx, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : (Idx → ℝ) → Idx → Idx → ℝ),
        (∀ s t : Idx, ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
          (fun z : Idx → ℝ => u z s t) {z : Idx → ℝ | ‖z‖ < R'}) →
        (∀ z : Idx → ℝ, ‖z‖ < R' → ∀ ξ : Idx → ℝ,
          lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j', u z i j' * ξ i * ξ j') →
        (∀ (m : ℕ) (hm : m ≤ k + 1) (β : Fin m → Idx) (z : Idx → ℝ) (s t : Idx),
          ‖z‖ < R' →
          ‖Work.Diff.STE.pdVec m β (fun y : Idx → ℝ => ((u y s t : ℝ) : ℂ)) z‖ ≤ KG) →
        ∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Idx) (z : Idx → ℝ), ‖z‖ ≤ R →
          ‖Work.Diff.STE.pdVec m β (fun y : Idx → ℝ =>
            ((tmGKi (I := I) (M := M) D j a b ha hab y (u y) p q : ℝ) : ℂ)) z‖ ≤ C := by
    intro p q
    obtain ⟨C, hC0, hC⟩ := compJetBoundB3 (n := Module.finrank ℝ E) (k := k)
      (fun z V _ => ((tmGKi (I := I) (M := M) D j a b ha hab z V p q : ℝ) : ℂ)) R R' hRR'
      (tmGKi_state3_contDiffOn (I := I) (M := M) D j a b ha hab hRreg p q) lam KG hlam hKG
    exact ⟨C, hC0, hC⟩
  choose Cx hCx using hbound
  refine ⟨∑ p, ∑ q, Cx p q,
    Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun q _ => (hCx p q).1)),
    fun u hu_sm hu_ell hu_jet m hm β z hz p q => ?_⟩
  refine le_trans ((hCx p q).2 u hu_sm hu_ell hu_jet m hm β z hz) ?_
  have h1 : Cx p q ≤ ∑ q' : Idx, Cx p q' :=
    Finset.single_le_sum (fun a _ => (hCx p a).1) (Finset.mem_univ q)
  have h2 : (∑ q' : Idx, Cx p q') ≤ ∑ p' : Idx, ∑ q' : Idx, Cx p' q' :=
    Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => (hCx a b).1))
      (Finset.mem_univ p)
  linarith

end Work.Diff.STE.B3
