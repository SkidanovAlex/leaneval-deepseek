import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Toolkit for the local-inverse construction on a compact set

This is the shared vocabulary of `Work.Diff.STE.B3.SymCalcStep8.localInverseData`: the
inverse-function-theorem conversion of a non-vanishing Jacobian determinant into a smooth local
inverse, the local injectivity it yields, and the neighbourhood on which the determinant does not
vanish.

* `lidCleOfDetNeZero` : a continuous linear endomorphism of `ι → ℝ` with non-zero determinant,
  packaged as a continuous linear equivalence with the same underlying map.
* `lid_exists_local_inverse_data` : at a point where `det (fderiv ℝ θ) ≠ 0`, `θ` has a smooth local
  inverse `g` (`ContDiffAt ℝ ∞ g (θ z)`), continuous at `θ z`, with `g (θ x) = x` eventually near `z`
  and `θ (g y) = y` eventually near `θ z`.
* `lid_injOn_nhds` : hence `θ` is injective on a neighbourhood of `z`.
* `lid_exists_thickening_det_ne_zero` : if `K` is compact and `det (fderiv ℝ θ) ≠ 0` on `K`, then
  the determinant is non-zero on a thickening of `K`.

These lemmas depend on nothing beyond Mathlib.
-/

noncomputable section

namespace Work.Diff.STE.B3.SymCalcStep8

open Set Filter Metric Classical

/-- **Invertible derivative from non-zero determinant.**  A continuous linear endomorphism of
`ι → ℝ` whose determinant is non-zero can be regarded as a continuous linear equivalence with the
same underlying map. -/
lemma lid_exists_cleOfDetNeZero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) →L[ℝ] (ι → ℝ)) (hf : f.det ≠ 0) :
    ∃ f' : (ι → ℝ) ≃L[ℝ] (ι → ℝ), (f' : (ι → ℝ) →L[ℝ] (ι → ℝ)) = f := by
  have hker : (f : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)).ker = ⊥ := by
    by_contra h
    exact hf ((LinearMap.det_eq_zero_iff_ker_ne_bot).mpr h)
  have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl
      (f := (f : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)))).mp hinj
  have hrange : (f : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)).range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  exact ⟨ContinuousLinearEquiv.ofBijective f hker hrange, ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

/-- The continuous linear equivalence produced by `lid_exists_cleOfDetNeZero`. -/
def lidCleOfDetNeZero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) →L[ℝ] (ι → ℝ)) (hf : f.det ≠ 0) : (ι → ℝ) ≃L[ℝ] (ι → ℝ) :=
  Classical.choose (lid_exists_cleOfDetNeZero f hf)

@[simp]
lemma lidCleOfDetNeZero_coe {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) →L[ℝ] (ι → ℝ)) (hf : f.det ≠ 0) :
    (lidCleOfDetNeZero f hf : (ι → ℝ) →L[ℝ] (ι → ℝ)) = f :=
  Classical.choose_spec (lid_exists_cleOfDetNeZero f hf)

/-- **Smooth local inverse at a point with non-zero Jacobian determinant.**  If `θ` is smooth and
`det (fderiv ℝ θ z) ≠ 0`, then there is a map `g`, smooth at `θ z` and continuous there, which is a
two-sided local inverse of `θ` at `z`: `g (θ x) = x` for `x` near `z` and `θ (g y) = y` for `y` near
`θ z`. -/
theorem lid_exists_local_inverse_data {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ : (ι → ℝ) → (ι → ℝ)) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) {z : ι → ℝ}
    (hz : (fderiv ℝ θ z).det ≠ 0) :
    ∃ g : (ι → ℝ) → (ι → ℝ), ContDiffAt ℝ (⊤ : ℕ∞) g (θ z) ∧ ContinuousAt g (θ z) ∧
      (∀ᶠ x in nhds z, g (θ x) = x) ∧ (∀ᶠ y in nhds (θ z), θ (g y) = y) := by
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hst : HasStrictFDerivAt θ (fderiv ℝ θ z) z := (hθ.contDiffAt (x := z)).hasStrictFDerivAt hn
  have hst' : HasStrictFDerivAt θ (lidCleOfDetNeZero (fderiv ℝ θ z) hz :
      (ι → ℝ) →L[ℝ] (ι → ℝ)) z := by
    rw [lidCleOfDetNeZero_coe]; exact hst
  have hfd' : HasFDerivAt θ (lidCleOfDetNeZero (fderiv ℝ θ z) hz :
      (ι → ℝ) →L[ℝ] (ι → ℝ)) z := hst'.hasFDerivAt
  refine ⟨(hθ.contDiffAt (x := z)).localInverse
      (f' := lidCleOfDetNeZero (fderiv ℝ θ z) hz) hfd' hn, ?_, ?_, ?_, ?_⟩
  · exact (hθ.contDiffAt (x := z)).to_localInverse hfd' hn
  · exact ((hθ.contDiffAt (x := z)).to_localInverse hfd' hn).continuousAt
  · exact hst'.eventually_left_inverse
  · exact hst'.eventually_right_inverse

/-- **Local injectivity from a non-zero Jacobian determinant.** -/
lemma lid_injOn_nhds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ : (ι → ℝ) → (ι → ℝ)) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) {z : ι → ℝ}
    (hz : (fderiv ℝ θ z).det ≠ 0) :
    ∃ U : Set (ι → ℝ), U ∈ nhds z ∧ Set.InjOn θ U := by
  obtain ⟨g, -, -, hleft, -⟩ := lid_exists_local_inverse_data θ hθ hz
  exact ⟨{x | g (θ x) = x}, hleft, fun a ha b hb hab => by rw [← ha, ← hb, hab]⟩

/-- **Non-vanishing determinant on a thickening of a compact set.** -/
theorem lid_exists_thickening_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ : (ι → ℝ) → (ι → ℝ)) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (K : Set (ι → ℝ)) (hK : IsCompact K) (hdet : ∀ z ∈ K, (fderiv ℝ θ z).det ≠ 0) :
    ∃ δ > 0, ∀ z, z ∈ Metric.thickening δ K → (fderiv ℝ θ z).det ≠ 0 := by
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hc : Continuous fun z : ι → ℝ => (fderiv ℝ θ z).det :=
    ContinuousLinearMap.continuous_det.comp (hθ.continuous_fderiv hn)
  have hclosed : IsClosed {z : ι → ℝ | (fderiv ℝ θ z).det = 0} := isClosed_eq hc continuous_const
  obtain ⟨δ, hδpos, hδsub⟩ :=
    hK.exists_thickening_subset_open hclosed.isOpen_compl (fun z hz => hdet z hz)
  exact ⟨δ, hδpos, fun z hz => hδsub hz⟩

/-- **The canonical set-theoretic inverse.**  `lidInvWhere θ S y` is the (chosen) element `z ∈ S`
with `θ z = y`, if such an element exists, and `0` otherwise. -/
noncomputable def lidInvWhere {E : Type*} [Zero E] (θ : E → E) (S : Set E) (y : E) : E :=
  if h : ∃ z, z ∈ S ∧ θ z = y then h.choose else 0

lemma lidInvWhere_of_mem {E : Type*} [Zero E] {θ : E → E} {S : Set E} {y : E}
    (h : ∃ z, z ∈ S ∧ θ z = y) : lidInvWhere θ S y = h.choose := by
  rw [lidInvWhere]; exact dite_eq_left h

/-- Membership and the defining equation for `lidInvWhere`. -/
lemma lidInvWhere_spec {E : Type*} [Zero E] {θ : E → E} {S : Set E} {y : E}
    (h : ∃ z, z ∈ S ∧ θ z = y) : lidInvWhere θ S y ∈ S ∧ θ (lidInvWhere θ S y) = y := by
  rw [lidInvWhere_of_mem h]; exact h.choose_spec

/-- On `S` the canonical inverse is a genuine inverse. -/
lemma lidInvWhere_apply_mem {E : Type*} [Zero E] {θ : E → E} {S : Set E}
    (hinj : Set.InjOn θ S) {z : E} (hz : z ∈ S) : lidInvWhere θ S (θ z) = z := by
  obtain ⟨h1, h2⟩ := lidInvWhere_spec (θ := θ) (S := S) (y := θ z) ⟨z, hz, rfl⟩
  exact hinj h1 hz h2

/-- Injectivity pins down the canonical inverse: any element of `S` mapping to `y` is it. -/
lemma lidInvWhere_eq_of {E : Type*} [Zero E] {θ : E → E} {S : Set E} {y g : E}
    (hinj : Set.InjOn θ S) (hgS : g ∈ S) (hgθ : θ g = y)
    (h : ∃ z, z ∈ S ∧ θ z = y) : lidInvWhere θ S y = g := by
  rw [lidInvWhere_of_mem h]
  exact hinj h.choose_spec.1 hgS (h.choose_spec.2.trans hgθ.symm)

end Work.Diff.STE.B3.SymCalcStep8
