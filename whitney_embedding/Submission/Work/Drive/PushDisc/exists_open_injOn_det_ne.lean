import Mathlib
import Submission.Work.Drive.PushDisc.injOn_nhds_of_compact_euclidean
import Submission.Work.Drive.PushDisc.exists_globalDiffeo_of_embedding
import Submission.Work.Drive.PushDisc.sheetModel

/-!
# Injectivity and constant Jacobian sign on a neighbourhood of a compact star-shaped set

`Work.Drive.PushDisc.exists_open_injOn_det_ne` is the elementary globalisation input of the
`θ`-assembly: a `C^∞` self-map `θ` of the model space `Mdl k = ℝ × ℝ × ℝ^k × ℝ^k` which is
injective on a compact star-shaped set `C ∋ 0` and whose derivative is injective at every point of
`C` is injective on a whole open neighbourhood `O ⊇ C`, and on that neighbourhood the Jacobian
determinant `det (fderiv ℝ θ ·)` has a *constant* sign.

The proof has three independent parts.

* **Local injectivity** (`local_injOn_of_injective_fderiv_fin`): a `C^∞` map between
  finite-dimensional real normed spaces whose derivative at a point is injective is injective on a
  neighbourhood of that point.  This is the generalisation to arbitrary finite-dimensional normed
  spaces of `Work.Embedding.local_injOn_of_injective_fderiv` (which is stated for Euclidean spaces):
  the derivative `A` has a linear left inverse `g`, which is automatically continuous; the inverse
  function theorem applied to `G ∘ θ` (with `G` a continuous linear left inverse of `A`) yields a
  local *left* inverse of `G ∘ θ`, hence injectivity of `G ∘ θ`, hence of `θ`.

* **Neighbourhood of injectivity** (`Work.Routing.injOn_nhds_of_compact_of_locallyInjOn`): a map
  that is continuous and locally injective at the points of a compact set `C` and injective on `C`
  is injective on a neighbourhood of `C`.

* **Constant sign of the Jacobian**: `det (fderiv ℝ θ ξ) ≠ 0` on `C` because the derivative is
  injective (`det_toLinearMap_ne_zero_of_injective_fin`); `ξ ↦ det (fderiv ℝ θ ξ)` is continuous
  (`ContDiff.continuous_fderiv` and `ContinuousLinearMap.continuous_det`); and `C` is preconnected
  since it is star-shaped (`StarConvex.isPathConnected`).  A preconnected subset of `ℝ` avoiding `0`
  lies in `Ioi 0` or in `Iio 0`
  (`isPreconnected_subset_Ioi_or_Iio_of_not_mem_zero`), so the sign is constant on `C` and hence on
  a neighbourhood of `C`, obtained by intersecting with `{det > 0}` or `{det < 0}`.
-/

namespace Work.Drive.PushDisc

open scoped ContDiff

/-! ## A general local-injectivity brick -/

/-- **Local injectivity of a smooth map with injective derivative (finite-dimensional normed
spaces).**  If `ψ : E → F` is `C^∞` on an open set `V` containing `u₀` and `fderiv ℝ ψ u₀` is
injective, then `ψ` is injective on some open neighbourhood of `u₀`.

This is the finite-dimensional version of `Work.Embedding.local_injOn_of_injective_fderiv`, valid
for arbitrary finite-dimensional real normed spaces `E`, `F` (the model space `Mdl k` of the
Whitney development is not a bare `EuclideanSpace ℝ (Fin n)`). -/
theorem local_injOn_of_injective_fderiv_fin {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {ψ : E → F} {V : Set E} (hV : IsOpen V) {u₀ : E} (hu₀ : u₀ ∈ V)
    (hψ : ContDiffOn ℝ ∞ ψ V) (hinj : Function.Injective (fderiv ℝ ψ u₀)) :
    ∃ W : Set E, IsOpen W ∧ u₀ ∈ W ∧ Set.InjOn ψ W := by
  classical
  set A : E →L[ℝ] F := fderiv ℝ ψ u₀ with hA
  have hker : LinearMap.ker A.toLinearMap = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  obtain ⟨g, hg⟩ := A.toLinearMap.exists_leftInverse_of_injective hker
  let G : F →L[ℝ] E := LinearMap.toContinuousLinearMap g
  have hGA : G ∘L A = ContinuousLinearMap.id ℝ E := by
    apply ContinuousLinearMap.ext
    intro v
    have hv := LinearMap.congr_fun hg v
    simpa [G] using hv
  have hnz : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hψat : ContDiffAt ℝ ∞ ψ u₀ := hψ.contDiffAt (hV.mem_nhds hu₀)
  have hΨcont : ContDiffAt ℝ ∞ (fun u => G (ψ u)) u₀ :=
    G.contDiff.contDiffAt.comp u₀ hψat
  have hΨderiv : HasFDerivAt (fun u => G (ψ u)) (G ∘L A) u₀ :=
    HasFDerivAt.comp u₀ (G.hasFDerivAt (x := ψ u₀)) (hψat.differentiableAt hnz |>.hasFDerivAt)
  have hΨderiv' : HasFDerivAt (fun u => G (ψ u))
      ((ContinuousLinearEquiv.refl ℝ E) : E →L[ℝ] E) u₀ := by
    have h := hΨderiv.congr_fderiv hGA
    simpa [ContinuousLinearEquiv.coe_refl] using h
  have hS : HasStrictFDerivAt (fun u => G (ψ u))
      ((ContinuousLinearEquiv.refl ℝ E) : E →L[ℝ] E) u₀ :=
    hΨcont.hasStrictFDerivAt' hΨderiv' hnz
  obtain ⟨S, hSmem, hSinj⟩ := Filter.eventually_iff_exists_mem.mp hS.eventually_left_inverse
  obtain ⟨W, hWsub, hWopen, hu₀W⟩ := mem_nhds_iff.mp hSmem
  refine ⟨W, hWopen, hu₀W, ?_⟩
  intro a ha b hb hab
  have h1 := hSinj a (hWsub ha)
  have h2 := hSinj b (hWsub hb)
  rw [← h1, ← h2, congrArg G hab]

/-! ## Determinant of an injective endomorphism -/

/-- An injective continuous linear endomorphism of a finite-dimensional real normed space has
non-zero determinant. -/
theorem det_toLinearMap_ne_zero_of_injective_fin {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (A : E →L[ℝ] E)
    (h : Function.Injective A) : A.toLinearMap.det ≠ 0 := by
  intro h0
  have hker : A.toLinearMap.ker ≠ ⊥ := LinearMap.det_eq_zero_iff_ker_ne_bot.mp h0
  rw [LinearMap.ker_eq_bot.mpr h] at hker
  exact hker rfl

/-! ## A preconnected set of reals avoiding zero has constant sign -/

/-- A preconnected subset of `ℝ` not containing `0` lies either in `(0,∞)` or in `(-∞,0)`. -/
lemma isPreconnected_subset_Ioi_or_Iio_of_not_mem_zero {S : Set ℝ} (hS : IsPreconnected S)
    (h0 : (0:ℝ) ∉ S) : S ⊆ Set.Ioi 0 ∨ S ⊆ Set.Iio 0 := by
  by_cases h : ∃ x ∈ S, 0 < x
  · left
    rintro y hy
    by_contra hy'
    rw [Set.mem_Ioi, not_lt] at hy'
    have hy0 : y < 0 := lt_of_le_of_ne hy' (by rintro rfl; exact h0 hy)
    obtain ⟨x, hx, hx0⟩ := h
    exact h0 (hS.ordConnected.out hy hx (Set.mem_Icc.mpr ⟨hy0.le, hx0.le⟩))
  · right
    intro y hy
    by_contra hy'
    rw [Set.mem_Iio, not_lt] at hy'
    have hle : y ≤ 0 := by
      by_contra hlt
      rw [not_le] at hlt
      exact h ⟨y, hy, hlt⟩
    have : y = 0 := le_antisymm hle hy'
    exact h0 (this ▸ hy)

/-! ## The target -/

theorem exists_open_injOn_det_ne {k : ℕ}
    (θ : Work.Drive.Whitney.Mdl k → Work.Drive.Whitney.Mdl k)
    (hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ)
    (C : Set (Work.Drive.Whitney.Mdl k)) (hC : IsCompact C)
    (hCstar : StarConvex ℝ (0 : Work.Drive.Whitney.Mdl k) C)
    (h0C : (0 : Work.Drive.Whitney.Mdl k) ∈ C)
    (hImm : ∀ ξ ∈ C, Function.Injective (fderiv ℝ θ ξ))
    (hInj : Set.InjOn θ C) :
    ∃ O : Set (Work.Drive.Whitney.Mdl k), IsOpen O ∧ C ⊆ O ∧ Set.InjOn θ O ∧
      ((∀ ξ ∈ O, 0 < (fderiv ℝ θ ξ).toLinearMap.det) ∨
       (∀ ξ ∈ O, (fderiv ℝ θ ξ).toLinearMap.det < 0)) := by
  classical
  let D : Work.Drive.Whitney.Mdl k → ℝ := fun ξ => (fderiv ℝ θ ξ).toLinearMap.det
  have hDcont : Continuous D :=
    ContinuousLinearMap.continuous_det.comp (hθ.continuous_fderiv (by simp))
  have hDne : ∀ ξ ∈ C, D ξ ≠ 0 := fun ξ hξ =>
    det_toLinearMap_ne_zero_of_injective_fin (fderiv ℝ θ ξ) (hImm ξ hξ)
  obtain ⟨O₁, hO₁open, hCO₁, hInj₁⟩ : ∃ O : Set (Work.Drive.Whitney.Mdl k),
      IsOpen O ∧ C ⊆ O ∧ Set.InjOn θ O :=
    Work.Routing.injOn_nhds_of_compact_of_locallyInjOn hC
      (fun x hx => local_injOn_of_injective_fderiv_fin isOpen_univ (Set.mem_univ x)
        hθ.contDiffOn (hImm x hx))
      (fun x _ => hθ.continuous.continuousAt) hInj
  have hpre : IsPreconnected C := (hCstar.isPathConnected h0C).isConnected.isPreconnected
  have hpreImg : IsPreconnected (D '' C) := hpre.image D hDcont.continuousOn
  have h0not : (0:ℝ) ∉ D '' C := by
    rintro ⟨ξ, hξ, h0⟩
    exact hDne ξ hξ h0
  rcases isPreconnected_subset_Ioi_or_Iio_of_not_mem_zero hpreImg h0not with hpos | hneg
  · refine ⟨O₁ ∩ D ⁻¹' Set.Ioi 0, hO₁open.inter (isOpen_Ioi.preimage hDcont), ?_, ?_, Or.inl ?_⟩
    · intro ξ hξ; exact ⟨hCO₁ hξ, hpos ⟨ξ, hξ, rfl⟩⟩
    · exact hInj₁.mono Set.inter_subset_left
    · intro ξ hξ; exact hξ.2
  · refine ⟨O₁ ∩ D ⁻¹' Set.Iio 0, hO₁open.inter (isOpen_Iio.preimage hDcont), ?_, ?_, Or.inr ?_⟩
    · intro ξ hξ; exact ⟨hCO₁ hξ, hneg ⟨ξ, hξ, rfl⟩⟩
    · exact hInj₁.mono Set.inter_subset_left
    · intro ξ hξ; exact hξ.2

end Work.Drive.PushDisc
