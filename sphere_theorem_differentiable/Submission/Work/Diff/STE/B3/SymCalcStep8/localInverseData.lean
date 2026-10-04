import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep8.localInvKit
import Submission.Work.Diff.STE.B3.SymCalcStep8.exists_injOn_thickening
import Submission.Work.Diff.STE.B3.SymCalcStep8.isOpen_image_of_det_ne_zero
import Submission.Work.Diff.STE.B3.SymCalcStep8.exists_bump_tsupport_subset
import Submission.Work.Diff.STE.B3.SymCalcStep8.lidInvWhere_contDiffAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep8

open Set Filter Metric

/-- Assembly of the target from the five independent ingredients:
`hthick` (injectivity of `θ` on a thickening of `K`), `hdetThick` (non-vanishing determinant on a
thickening of `K`, from the toolkit), `hopen` (openness of the image of an open set on which the
determinant does not vanish), `hbump` (a smooth bump equal to `1` on an open neighbourhood of a
compact set whose topological support stays inside a given open set) and `hsmooth` (smoothness of
the canonical inverse on `θ '' S`).

Given `ε, δ` from the two thickening statements, the set `S := thickening ε K ∩ thickening δ K` is
an open neighbourhood of `K` on which `θ` is injective with non-vanishing determinant.  The
canonical inverse `lidInvWhere θ S` inverts `θ` on `S`; it is smooth on the open set `θ '' S`.  A
bump `χ` with `tsupport χ ⊆ θ '' S` equal to `1` on an open neighbourhood `W` of `θ '' K` then
multiplies it into a globally smooth map `σ`, which still inverts `θ` on the open set
`U := {z ∈ S | θ z ∈ W}`, and satisfies `θ (σ y) = y` for `y ∈ W`. -/
private theorem localInverseData_aux {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ : (ι → ℝ) → (ι → ℝ)) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (K : Set (ι → ℝ)) (hK : IsCompact K)
    (hthick : ∃ ε > 0, ∀ x y, x ∈ Metric.thickening ε K → y ∈ Metric.thickening ε K →
      θ x = θ y → x = y)
    (hdetThick : ∃ δ > 0, ∀ z, z ∈ Metric.thickening δ K → (fderiv ℝ θ z).det ≠ 0)
    (hopen : ∀ (S : Set (ι → ℝ)), IsOpen S → (∀ z ∈ S, (fderiv ℝ θ z).det ≠ 0) →
      IsOpen (θ '' S))
    (hbump : ∀ (K' : Set (ι → ℝ)), IsCompact K' → ∀ (S : Set (ι → ℝ)), IsOpen S → K' ⊆ S →
      ∃ W : Set (ι → ℝ), IsOpen W ∧ K' ⊆ W ∧ W ⊆ S ∧
        ∃ χ : (ι → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ (∀ y ∈ W, χ y = 1) ∧ tsupport χ ⊆ S)
    (hsmooth : ∀ (S : Set (ι → ℝ)), IsOpen S → Set.InjOn θ S →
      (∀ z ∈ S, ∃ g : (ι → ℝ) → (ι → ℝ), ContDiffAt ℝ (⊤ : ℕ∞) g (θ z) ∧
        ContinuousAt g (θ z) ∧ (∀ᶠ x in nhds z, g (θ x) = x) ∧
        (∀ᶠ y in nhds (θ z), θ (g y) = y)) →
      ∀ y ∈ θ '' S, ContDiffAt ℝ (⊤ : ℕ∞) (lidInvWhere θ S) y) :
    ∃ σ : (ι → ℝ) → (ι → ℝ), ContDiff ℝ (⊤ : ℕ∞) σ ∧
      ∃ U : Set (ι → ℝ), IsOpen U ∧ K ⊆ U ∧ (∀ z ∈ U, σ (θ z) = z) ∧
      ∃ W : Set (ι → ℝ), IsOpen W ∧ θ '' K ⊆ W ∧ (∀ y ∈ W, θ (σ y) = y) := by
  obtain ⟨ε, hεpos, hε⟩ := hthick
  obtain ⟨δ, hδpos, hδ⟩ := hdetThick
  set S : Set (ι → ℝ) := Metric.thickening ε K ∩ Metric.thickening δ K
  have hSopen : IsOpen S := Metric.isOpen_thickening.inter Metric.isOpen_thickening
  have hKS : K ⊆ S := fun z hz =>
    ⟨Metric.self_subset_thickening hεpos K hz, Metric.self_subset_thickening hδpos K hz⟩
  have hinjS : Set.InjOn θ S := fun x hx y hy hxy => hε x y hx.1 hy.1 hxy
  have hSdet : ∀ z ∈ S, (fderiv ℝ θ z).det ≠ 0 := fun z hz => hδ z hz.2
  have hθS : ∀ y ∈ θ '' S, θ (lidInvWhere θ S y) = y := fun y hy => by
    obtain ⟨z, hzS, hzy⟩ := hy
    exact (lidInvWhere_spec ⟨z, hzS, hzy⟩).2
  have hσ₀θ : ∀ z ∈ S, lidInvWhere θ S (θ z) = z := fun z hz => lidInvWhere_apply_mem hinjS hz
  have hsm : ∀ y ∈ θ '' S, ContDiffAt ℝ (⊤ : ℕ∞) (lidInvWhere θ S) y :=
    hsmooth S hSopen hinjS (fun z hz => lid_exists_local_inverse_data θ hθ (hSdet z hz))
  have hK' : IsCompact (θ '' K) := hK.image (f := θ) hθ.continuous
  obtain ⟨W, hWopen, hKW, hWsub, χ, hχsm, hχone, hχtsup⟩ :=
    hbump (θ '' K) hK' (θ '' S) (hopen S hSopen hSdet) (Set.image_mono hKS)
  refine ⟨fun y => χ y • lidInvWhere θ S y, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport χ
    · exact (hχsm.contDiffAt (x := y)).smul (hsm y (hχtsup hy))
    · have hev : (fun x => χ x • lidInvWhere θ S x) =ᶠ[nhds y] (fun _ => (0 : ι → ℝ)) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with x hx
        rw [hx]
        exact zero_smul ℝ (lidInvWhere θ S x)
      exact (contDiffAt_const (c := (0 : ι → ℝ))).congr_of_eventuallyEq hev
  · refine ⟨{z | z ∈ S ∧ θ z ∈ W}, hSopen.inter (hWopen.preimage hθ.continuous),
      fun z hz => ⟨hKS hz, hKW (Set.mem_image_of_mem θ hz)⟩, ?_, W, hWopen, hKW, ?_⟩
    · intro z hz
      change χ (θ z) • lidInvWhere θ S (θ z) = z
      have h1 : χ (θ z) • lidInvWhere θ S (θ z) = lidInvWhere θ S (θ z) := by
        rw [hχone (θ z) hz.2, one_smul]
      rw [h1, hσ₀θ z hz.1]
    · intro y hy
      change θ (χ y • lidInvWhere θ S y) = y
      have h1 : χ y • lidInvWhere θ S y = lidInvWhere θ S y := by rw [hχone y hy, one_smul]
      rw [h1]
      exact hθS y (hWsub hy)

/-- **Local-inverse data of an injective local diffeomorphism on a compact set.**

If `θ : (ι → ℝ) → (ι → ℝ)` is smooth, `K` is compact, `θ` is injective on `K` and
`det (fderiv ℝ θ) ≠ 0` on `K`, then there are a globally smooth `σ : (ι → ℝ) → (ι → ℝ)` and open
sets `U ⊇ K`, `W ⊇ θ '' K` such that `σ` inverts `θ` on this data: `σ (θ z) = z` for `z ∈ U` and
`θ (σ y) = y` for `y ∈ W`.

Route: (1) `∃ ε > 0` such that `θ` is injective on the `ε`-neighbourhood `S_ε` of `K` and
`det (fderiv ℝ θ) ≠ 0` on `S_ε` (compactness + the local injectivity of the inverse function
theorem, `ContDiffAt.localInverse` / `HasStrictFDerivAt.eventually_left_inverse` and the usual
sequence argument).  (2) `σ₀ := (θ|_{S_ε})⁻¹ : θ '' S_ε → S_ε` is smooth (pointwise from
`OpenPartialHomeomorph.contDiffAt_symm` / `ContDiffAt.to_localInverse`, using that on `θ '' S_ε`
the set-theoretic inverse coincides with every local inverse, by injectivity of `θ` on `S_ε`).
(3) Globally extend to a smooth `σ` by `σ := χ • σ₀' + (1 - χ) • c₀`, where `σ₀'` is `σ₀` extended
by `0`, `χ` is a smooth bump with `support χ = s` for an open `s` with
`K' := θ '' K ⊆ s ⊆ closure s ⊆ θ '' S_ε` (`exists_contDiff_support_eq_eq_one_iff`, plus
`IsCompact.exists_cthickening_subset_open`), and `c₀` is a fixed point; then
`U := {z ∈ S_ε | χ (θ z) = 1}` and `W := {y | χ y = 1} ∩ θ '' S_ε` work. -/
theorem localInverseData {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ : (ι → ℝ) → (ι → ℝ)) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (K : Set (ι → ℝ)) (hK : IsCompact K) (hinj : Set.InjOn θ K)
    (hdet : ∀ z ∈ K, (fderiv ℝ θ z).det ≠ 0) :
    ∃ σ : (ι → ℝ) → (ι → ℝ), ContDiff ℝ (⊤ : ℕ∞) σ ∧
      ∃ U : Set (ι → ℝ), IsOpen U ∧ K ⊆ U ∧ (∀ z ∈ U, σ (θ z) = z) ∧
      ∃ W : Set (ι → ℝ), IsOpen W ∧ θ '' K ⊆ W ∧ (∀ y ∈ W, θ (σ y) = y) :=
  localInverseData_aux θ hθ K hK
    (exists_injOn_thickening θ hθ K hK hinj hdet)
    (lid_exists_thickening_det_ne_zero θ hθ K hK hdet)
    (fun S hS hd => isOpen_image_of_det_ne_zero θ hθ S hS hd)
    (fun K' hK' S hS hKS => exists_bump_tsupport_subset K' hK' S hS hKS)
    (fun S hS hinjS hd => lidInvWhere_contDiffAt θ S hS hinjS hd)

end Work.Diff.STE.B3.SymCalcStep8
