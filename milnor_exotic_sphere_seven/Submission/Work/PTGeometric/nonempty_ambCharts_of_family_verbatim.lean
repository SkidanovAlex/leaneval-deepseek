import Mathlib
import Submission.Work.PTGeometric.nonempty_ambCharts
import Submission.Work.PTGeometric.nonempty_ambCharts_of_family
import Submission.Work.PTGeometric.ell_apply_frame_eq
import Submission.Work.PTGeometric.AmbientPerturbation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Grassmannian charts on a *prescribed* family of open sets

`Work.PTGeometric.AmbCharts n k M P m` collects `m` open sets `U l` covering `M`, a linear coordinate
`ell l` injective on the moving planes over `U l`, and a smooth `ell l`-adapted frame of those planes.
The theorem `Work.PTGeometric.nonempty_ambCharts_of_family` produces such a family *inside* a
prescribed one, around prescribed points.

This file proves the **verbatim** version, in which the prescribed open sets themselves are the charts
of the family:

> given finitely many open sets `U j` and coordinates `ell j` which are injective on the moving planes
> over `closure (U j)`, there is a chart family `C` with, for every `j`, an index `l` such that
> `C.ell l = ell j` and `C.U l = U j`.

The mathematical content is that a smooth `ell`-adapted frame which is correct on *all* of `U` can be
produced from the invertibility of the Gram operator `Λ y = ell ∘ P y ∘ ell†` on the compact set
`closure U`.  Concretely one covers `closure U` by finitely many of the neighbourhoods
`V x = {y | ∑ i, ‖(Λ y - Λ x) eᵢ‖² < (rad x / 2)²}` (where `rad x = (2‖(Λ x)⁻¹‖ + 1)⁻¹`, on which
`Λ y` is invertible by `Work.PTGeometric.isInvertible_of_norm_sub_le`), takes the smooth cut-off
`χ x = smoothTransition (((rad x)² - sq x ·)/((rad x)² - (rad x/2)²))` — equal to `1` on `V x` and with
topological support inside the invertibility locus — and multiplies the frames by the single factor
`Ξ = smoothTransition (∑ x ∈ t, χ x)`, which is `1` on `U` because some `χ x` equals `1` there.  The
frame `Ξ • P y (ell† ((Λ y)⁻¹ eⱼ))` is then smooth on all of `M` (`χ • f` with `tsupport χ` inside the
open set where `f` is smooth is smooth: `contMDiff_smul_of_contMDiffOn_of_tsupport_subset_end`) and
`ell`-adapted on `U` (`Work.PTGeometric.ell_frame_sum`).

No separation axiom on `M` is used: everything is built from smooth functions on `M`.

## Main results

* `Work.PTGeometric.exists_chart_frame` — the frame adapted to a prescribed coordinate on a prescribed
  open set;
* `Work.PTGeometric.nonempty_ambCharts_of_family_verbatim` — the chart family containing the
  prescribed charts verbatim.
-/

set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace Work.PTGeometric

open scoped Manifold ContDiff
open Function Set Topology

noncomputable section

variable {n k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
  [IsManifold (𝓡∂ ((8 + k) + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **A smooth `ℓ`-adapted frame of the moving planes over a prescribed open set.**  If the linear
coordinate `ℓ : ℝⁿ → ℝᵏ` is injective on the plane of `P y` for every `y` in the *closure* of `U`,
then there is a frame `e` of those planes, smooth on all of `M`, which is `ℓ`-adapted on `U`:
`ℓ (∑ j, t j • e j y) = t` for `y ∈ U`.

The frame is `y ↦ Ξ y • P y (ℓ† ((Λ y)⁻¹ eⱼ))` where `Λ y = ℓ ∘ P y ∘ ℓ†` and `Ξ` is a smooth function
equal to `1` on `U` whose topological support lies inside the (open) locus where `Λ ·` is invertible. -/
theorem exists_chart_frame {P : M → EndOp n} [CompactSpace M]
    (hP : ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, EndOp n) ((⊤ : ℕ∞) : WithTop ℕ∞) P)
    (hproj : ∀ x, P x ∈ Gr n k) (ℓ : Amb n →L[ℝ] Amb k) (U : Set M)
    (hnear : ∀ y ∈ closure U, ∀ z : Amb n, P y z = z → ℓ z = 0 → z = 0) :
    ∃ e : Fin k → M → Amb n,
      (∀ j, ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Amb n) ((⊤ : ℕ∞) : WithTop ℕ∞) (e j)) ∧
      (∀ j y, y ∈ U → P y (e j y) = e j y) ∧
      (∀ y ∈ U, ∀ t : Amb k,
        ℓ ((Finset.univ : Finset (Fin k)).sum fun j => t j • e j y) = t) := by
  classical
  -- the Gram operator of the coordinate `ℓ` over the moving planes
  let Λ : M → EndOp k := fun y => ℓ.comp ((P y).comp ℓ.adjoint)
  have hΛsm : ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, EndOp k) ((⊤ : ℕ∞) : WithTop ℕ∞) Λ :=
    (contMDiff_const (𝕜 := ℝ) (I := 𝓡∂ ((8 + k) + 1))
      (I' := 𝓘(ℝ, Amb n →L[ℝ] Amb k)) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (c := ℓ)).clm_comp
      (hP.clm_comp contMDiff_const)
  have hclW : closure U ⊆ {y : M | (Λ y).IsInvertible} := fun y hy =>
    (isInvertible_comp_adjoint_iff ℓ (P y) (hproj y)).mpr (hnear y hy)
  -- the radius of invertibility around each point, and the smallness function
  let rad : M → ℝ := fun x => (2 * ‖(Λ x).inverse‖ + 1)⁻¹
  have hrad_pos : ∀ x : M, 0 < rad x := fun x => inv_pos.mpr (by positivity)
  have hrad_nonneg : ∀ x : M, 0 ≤ rad x := fun x => (hrad_pos x).le
  let sq : M → M → ℝ := fun x y =>
    ∑ i : Fin k, ‖(Λ y - Λ x) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
  have hsq_sm : ∀ x : M, ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) (sq x) := by
    intro x
    refine ContMDiff.sum (𝕜 := ℝ) (I := 𝓘(ℝ, ℝ)) (I' := 𝓡∂ ((8 + k) + 1))
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fun i _ => ?_
    have h1 : ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Amb k) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : M => (Λ y - Λ x) (EuclideanSpace.single i (1 : ℝ))) :=
      (hΛsm.sub contMDiff_const).clm_apply contMDiff_const
    exact (contDiff_norm_sq (𝕜 := ℝ) (E := Amb k)).contMDiff.comp h1
  -- the neighbourhoods on which `Λ` is invertible
  let V : M → Set M := fun x => {y | sq x y < (rad x / 2) ^ 2}
  have hV_open : ∀ x, IsOpen (V x) :=
    fun x => isOpen_lt (hsq_sm x).continuous continuous_const
  have hV_mem : ∀ x, x ∈ V x := by
    intro x
    have hzero : sq x x = 0 := by
      simp only [sq]
      refine Finset.sum_eq_zero fun i _ => ?_
      simp
    show sq x x < (rad x / 2) ^ 2
    rw [hzero]
    exact pow_pos (by linarith [hrad_pos x]) 2
  have hbound : ∀ x, (Λ x).IsInvertible → ∀ y, sq x y ≤ (rad x) ^ 2 → ‖Λ y - Λ x‖ ≤ rad x := by
    intro x _ y hy
    have h1 := opNorm_sq_le_sum_norm_sq (Λ y - Λ x)
    have h3 : ‖Λ y - Λ x‖ ^ 2 ≤ (rad x) ^ 2 :=
      le_trans h1 (by simpa only [sq] using hy)
    calc ‖Λ y - Λ x‖ = Real.sqrt (‖Λ y - Λ x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((rad x) ^ 2) := Real.sqrt_le_sqrt h3
      _ = rad x := Real.sqrt_sq (hrad_nonneg x)
  have hV_inv : ∀ x, (Λ x).IsInvertible → V x ⊆ {y : M | (Λ y).IsInvertible} := by
    intro x hx y hy
    exact isInvertible_of_norm_sub_le hx
      (hbound x hx y (le_trans hy.le (by nlinarith [hrad_nonneg x])))
  -- a finite cover of `closure U` by such neighbourhoods, indexed by points of `closure U`
  obtain ⟨t, ht⟩ : ∃ t : Finset {y : M // y ∈ closure U}, closure U ⊆ ⋃ x ∈ t, V x.1 := by
    refine (isClosed_closure.isCompact).elim_finite_subcover
      (fun x : {y : M // y ∈ closure U} => V x.1) (fun x => hV_open x.1) ?_
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hV_mem y⟩
  -- the cut-offs
  let chi : {y : M // y ∈ closure U} → M → ℝ := fun x y =>
    Real.smoothTransition (((rad x.1) ^ 2 - sq x.1 y) / ((rad x.1) ^ 2 - (rad x.1 / 2) ^ 2))
  have hchi_sm : ∀ x : {y : M // y ∈ closure U}, ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) (chi x) := by
    intro x
    exact (Real.smoothTransition.contDiff (n := ⊤)).contMDiff.comp
      (((contMDiff_const (c := (rad x.1) ^ 2)).sub (hsq_sm x.1)).div_const _)
  have hchi_one : ∀ (x : {y : M // y ∈ closure U}) (y : M), y ∈ V x.1 → chi x y = 1 := by
    intro x y hy
    have hD : 0 < (rad x.1) ^ 2 - (rad x.1 / 2) ^ 2 := by nlinarith [hrad_pos x.1]
    have hy' : sq x.1 y < (rad x.1 / 2) ^ 2 := hy
    refine Real.smoothTransition.one_of_one_le ?_
    rw [le_div_iff₀ hD]
    nlinarith [hy'.le]
  have hchi_nonneg : ∀ (x : {y : M // y ∈ closure U}) (y : M), 0 ≤ chi x y :=
    fun x y => Real.smoothTransition.nonneg _
  have hchi_zero : ∀ (x : {y : M // y ∈ closure U}) (y : M),
      (rad x.1) ^ 2 ≤ sq x.1 y → chi x y = 0 := by
    intro x y hy
    have hD : 0 < (rad x.1) ^ 2 - (rad x.1 / 2) ^ 2 := by nlinarith [hrad_pos x.1]
    refine Real.smoothTransition.zero_of_nonpos ?_
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hD.le
  have hchi_tsupp : ∀ x : {y : M // y ∈ closure U},
      tsupport (chi x) ⊆ {y : M | (Λ y).IsInvertible} := by
    intro x
    have hsupp : Function.support (chi x) ⊆ {y : M | sq x.1 y ≤ (rad x.1) ^ 2} := by
      intro y hy
      by_contra hcon
      exact hy (hchi_zero x y (le_of_not_ge hcon))
    have hclosed : IsClosed {y : M | sq x.1 y ≤ (rad x.1) ^ 2} :=
      isClosed_le (hsq_sm x.1).continuous continuous_const
    have h1 : closure (Function.support (chi x)) ⊆ {y : M | sq x.1 y ≤ (rad x.1) ^ 2} :=
      closure_minimal hsupp hclosed
    intro y hy
    exact isInvertible_of_norm_sub_le (hclW x.2) (hbound x.1 (hclW x.2) y (h1 hy))
  -- the single global cut-off, equal to `1` on `U`
  let Ξ : M → ℝ := fun y => Real.smoothTransition (∑ x ∈ t, chi x y)
  have hΞ_sm : ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) Ξ := by
    refine (Real.smoothTransition.contDiff (n := ⊤)).contMDiff.comp ?_
    exact ContMDiff.sum (𝕜 := ℝ) (I := 𝓘(ℝ, ℝ)) (I' := 𝓡∂ ((8 + k) + 1))
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fun x _ => hchi_sm x
  have hΞ_one : ∀ y ∈ U, Ξ y = 1 := by
    intro y hy
    have hmem : y ∈ (⋃ x ∈ t, V x.1 : Set M) := ht (subset_closure hy)
    simp only [mem_iUnion] at hmem
    obtain ⟨x, hxt, hxV⟩ := hmem
    have h1 : (1 : ℝ) ≤ ∑ z ∈ t, chi z y := by
      calc (1 : ℝ) = chi x y := (hchi_one x y hxV).symm
        _ ≤ ∑ z ∈ t, chi z y :=
            Finset.single_le_sum (fun z _ => hchi_nonneg z y) hxt
    exact Real.smoothTransition.one_of_one_le h1
  have hΞ_tsupp : tsupport Ξ ⊆ {y : M | (Λ y).IsInvertible} := by
    have hsupp : Function.support Ξ ⊆ ⋃ x ∈ t, tsupport (chi x) := by
      intro y hy
      by_contra hcon
      have hzero : (∑ z ∈ t, chi z y) = 0 := by
        refine Finset.sum_eq_zero fun z hz => ?_
        by_contra hc
        exact hcon (mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨hz,
          subset_tsupport (chi z) (by simpa only [Function.mem_support] using hc)⟩⟩)
      have hΞy : Ξ y = 0 := by
        simp only [Ξ, hzero]
        exact Real.smoothTransition.zero_of_nonpos le_rfl
      exact (by simpa only [Function.mem_support] using hy : Ξ y ≠ 0) hΞy
    have hclosed : IsClosed (⋃ x ∈ t, tsupport (chi x)) :=
      isClosed_biUnion_finset fun x _ => isClosed_tsupport _
    refine (closure_minimal hsupp hclosed).trans ?_
    intro y hy
    simp only [mem_iUnion] at hy
    obtain ⟨x, hxt, hxy⟩ := hy
    exact hchi_tsupp x hxy
  -- the frame
  let e : Fin k → M → Amb n := fun j y =>
    Ξ y • P y (ℓ.adjoint ((Λ y).inverse (EuclideanSpace.single j (1 : ℝ))))
  have he_sm : ∀ j, ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Amb n) ((⊤ : ℕ∞) : WithTop ℕ∞) (e j) := by
    intro j
    show ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Amb n) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M => Ξ y • P y (ℓ.adjoint ((Λ y).inverse (EuclideanSpace.single j (1 : ℝ)))))
    refine contMDiff_smul_of_contMDiffOn_of_tsupport_subset_end (k := k) (M := M)
      (s := {y : M | (Λ y).IsInvertible}) ?_ hΞ_sm ?_ hΞ_tsupp
    · exact isOpen_setOf_isInvertible_end.preimage hΛsm.continuous
    · have h1 : ContMDiffOn (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, EndOp k) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y => (Λ y).inverse) {y : M | (Λ y).IsInvertible} :=
        contMDiffOn_inverse_end Λ hΛsm
      have h2 : ContMDiffOn (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Amb k) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y => (Λ y).inverse (EuclideanSpace.single j (1 : ℝ)))
          {y : M | (Λ y).IsInvertible} :=
        h1.clm_apply contMDiffOn_const
      have h3 : ContMDiffOn (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Amb n) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y => ℓ.adjoint ((Λ y).inverse (EuclideanSpace.single j (1 : ℝ))))
          {y : M | (Λ y).IsInvertible} :=
        ℓ.adjoint.contMDiff.comp_contMDiffOn h2
      exact hP.contMDiffOn.clm_apply h3
  have he_mem : ∀ j y, y ∈ U → P y (e j y) = e j y := by
    intro j y hy
    have hΞ1 : Ξ y = 1 := hΞ_one y hy
    show P y (Ξ y • P y (ℓ.adjoint ((Λ y).inverse (EuclideanSpace.single j (1 : ℝ)))))
      = Ξ y • P y (ℓ.adjoint ((Λ y).inverse (EuclideanSpace.single j (1 : ℝ))))
    rw [hΞ1, one_smul]
    exact mem_Gr_apply_apply (hproj y) _
  have he_frame : ∀ y ∈ U, ∀ t : Amb k,
      ℓ ((Finset.univ : Finset (Fin k)).sum fun j => t j • e j y) = t := by
    intro y hy t
    have hΞ1 : Ξ y = 1 := hΞ_one y hy
    have hkey : ∀ j : Fin k,
        e j y = P y (ℓ.adjoint ((Λ y).inverse (EuclideanSpace.single j (1 : ℝ)))) := by
      intro j
      simp only [e, hΞ1, one_smul]
    simp only [hkey]
    exact ell_frame_sum (hproj y) ℓ (fun z hz h0 => hnear y (subset_closure hy) z hz h0) t
  exact ⟨e, he_sm, he_mem, he_frame⟩

/-- **The chart family containing a prescribed family of charts verbatim.**  Given finitely many open
sets `U j` and coordinates `ell j` injective on the moving planes over `closure (U j)`, there is a chart
family `C : AmbCharts n k M P m'` which, for every `j`, has an index `l` with `C.ell l = ell j` and
`C.U l = U j`.

Each prescribed chart is materialised as an ordinary chart of the family: its frame is built by
`exists_chart_frame`, and the covering requirement of `AmbCharts` is met by the extra charts supplied
by `Work.PTGeometric.nonempty_ambCharts`. -/
theorem nonempty_ambCharts_of_family_verbatim {n k : ℕ} (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M] [CompactSpace M]
    {P : M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hP : ContMDiff (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) P)
    (hproj : ∀ x, P x ∈ Work.PTGeometric.Gr n k)
    (m : ℕ) (ell : Fin m → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (U : Fin m → Set M)
    (hUopen : ∀ j, IsOpen (U j))
    (hcl : ∀ j, closure (U j) ⊆
      {y : M | ∀ z : EuclideanSpace ℝ (Fin n), P y z = z → ell j z = 0 → z = 0}) :
    ∃ m' : ℕ, ∃ C : Work.PTGeometric.AmbCharts n k M P m', ∀ j : Fin m, ∃ l : Fin m',
      C.ell l = ell j ∧ C.U l = U j := by
  classical
  -- a smooth frame adapted to each prescribed chart
  have hframe : ∀ j : Fin m, ∃ e : Fin k → M → Amb n,
      (∀ i, ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Amb n) ((⊤ : ℕ∞) : WithTop ℕ∞) (e i)) ∧
      (∀ i y, y ∈ U j → P y (e i y) = e i y) ∧
      (∀ y ∈ U j, ∀ t : Amb k,
        ell j ((Finset.univ : Finset (Fin k)).sum fun i => t i • e i y) = t) := fun j =>
    exists_chart_frame hP hproj (ell j) (U j) (fun y hy z hz h0 => hcl j hy z hz h0)
  choose e he using hframe
  -- an additional chart family, to cover the source
  obtain ⟨N, hC₀⟩ := nonempty_ambCharts (n := n) (k := k) M hP hproj
  obtain ⟨C₀⟩ := hC₀
  refine ⟨m + N, ?_, ?_⟩
  · refine { ell := fun l => Sum.elim ell C₀.ell (finSumFinEquiv.symm l)
             U := fun l => Sum.elim U C₀.U (finSumFinEquiv.symm l)
             e := fun l => Sum.elim e C₀.e (finSumFinEquiv.symm l)
             isOpen_U := ?_
             covers := ?_
             contMDiff_e := ?_
             ell_inj := ?_
             mem_e := ?_
             ell_frame := ?_ }
    · intro l
      cases h : finSumFinEquiv.symm l with
      | inl i => exact hUopen i
      | inr i => exact C₀.isOpen_U i
    · intro x
      obtain ⟨l, hl⟩ := C₀.covers x
      refine ⟨finSumFinEquiv (Sum.inr l), ?_⟩
      show x ∈ Sum.elim U C₀.U (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr l)))
      rw [Equiv.symm_apply_apply]
      exact hl
    · intro l i
      cases h : finSumFinEquiv.symm l with
      | inl a => exact (he a).1 i
      | inr a => exact C₀.contMDiff_e a i
    · intro l y hy z hz h0
      cases h : finSumFinEquiv.symm l with
      | inl a =>
        rw [h] at hy h0
        exact hcl a (subset_closure hy) z hz h0
      | inr a =>
        rw [h] at hy h0
        exact C₀.ell_inj a y hy z hz h0
    · intro l i y hy
      cases h : finSumFinEquiv.symm l with
      | inl a =>
        rw [h] at hy
        exact (he a).2.1 i y hy
      | inr a =>
        rw [h] at hy
        exact C₀.mem_e a i y hy
    · intro l y hy t
      cases h : finSumFinEquiv.symm l with
      | inl a =>
        rw [h] at hy
        exact (he a).2.2 y hy t
      | inr a =>
        rw [h] at hy
        exact C₀.ell_frame a y hy t
  · intro j
    refine ⟨finSumFinEquiv (Sum.inl j), ?_, ?_⟩
    · show Sum.elim ell C₀.ell (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) = ell j
      rw [Equiv.symm_apply_apply]
      rfl
    · show Sum.elim U C₀.U (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) = U j
      rw [Equiv.symm_apply_apply]
      rfl

end

end Work.PTGeometric
