import Mathlib
import Submission.Work.ThomBordism.ambientLocalDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The capped chart model class on the normal bundle

For the target `Work.ThomBordism.collapseLocalisation_ambient`, the ambient class
`Work.ThomBordism.ambientStandardClass E C x` (a class on the *tube* pair) is the pull-back, along
the tube inverse `C.inv`, of a class on the *normal bundle* pair `(ν, ν∖0)` supported near the zero
section:

* the **radial capping** `cap E ε` is a positive fibrewise radial rescaling which is the identity on
  the closed disc bundle of radius `ε` (hence on the image of `C.inv`), so that the composite
  `chartAffine E x ∘ cap E ε` is a legitimate map of pairs `(ν,ν∖0) → (ℝ^{8+k}, {0}ᶜ)`;
* `chartModelClass E C x` is the pull-back of the determinate model class
  `Work.ThomBordism.stdModelGen (8+k)` along it.

Since `cap E ε ∘ C.inv = C.inv` identically, the identity
`(tubeInvMap E C)^* (chartModelClass E C x) = ambientStandardClass E C x` is a formal consequence of
`chartAffine_inv` and the congruence/functoriality lemmas for `relCohMap`.
-/

open CategoryTheory Filter Topology

namespace Work.ThomBordism

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- The coefficient of the radial capping: identity on `[0,ε]`, capping above at `ε`. -/
noncomputable def capCoeff (ε r : ℝ) : ℝ := if r = 0 then 1 else min r ε / r

theorem capCoeff_pos {ε : ℝ} (hε : 0 < ε) : ∀ r, 0 ≤ r → 0 < capCoeff ε r := by
  intro r hr
  rw [capCoeff]
  by_cases h : r = 0
  · simp [h]
  · rw [if_neg h]
    have h2 : 0 < r := lt_of_le_of_ne hr (Ne.symm h)
    exact div_pos (lt_min h2 hε) h2

theorem capCoeff_mul {ε : ℝ} (hε : 0 ≤ ε) {r : ℝ} (hr : 0 ≤ r) :
    capCoeff ε r * r = min r ε := by
  rw [capCoeff]
  by_cases h : r = 0
  · subst h
    rw [if_pos rfl, one_mul, min_eq_left hε]
  · rw [if_neg h, div_mul_cancel₀ _ h]

theorem capCoeff_nonneg {ε : ℝ} (hε : 0 ≤ ε) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ capCoeff ε r := by
  rw [capCoeff]
  by_cases h : r = 0
  · rw [if_pos h]; norm_num
  · rw [if_neg h]
    exact div_nonneg (le_min hr hε) hr

theorem capCoeff_eq_min_div {ε r : ℝ} (hr : r ≠ 0) :
    capCoeff ε r = min r ε / r := by
  rw [capCoeff, if_neg hr]

/-- The radial capping of the normal bundle: the identity on the closed disc bundle of radius `ε`,
compressing everything outside onto it. -/
noncomputable def cap (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (ε : ℝ) :
    Work.Tubular.NormalTotal E → Work.Tubular.NormalTotal E :=
  Work.ThomBordism.radialRescale E (capCoeff ε)

/-- The norm of the capping is `min (‖p‖) ε`. -/
theorem normalNorm_cap (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (hε : 0 ≤ ε) (p : Work.Tubular.NormalTotal E) :
    Work.Tubular.normalNorm E (cap E ε p)
      = min (Work.Tubular.normalNorm E p) ε := by
  rw [cap, Work.ThomBordism.normalNorm_radialRescale,
    abs_of_nonneg (capCoeff_nonneg hε (Work.Tubular.normalNorm_nonneg E p)),
    capCoeff_mul hε (Work.Tubular.normalNorm_nonneg E p)]

/-- A radial rescaling whose coefficient is `1` at the norm of `p` fixes `p`. -/
theorem radialRescale_eq_self (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (φ : ℝ → ℝ) {p : Work.Tubular.NormalTotal E} (hφ : φ (Work.Tubular.normalNorm E p) = 1) :
    Work.ThomBordism.radialRescale E φ p = p := by
  apply Subtype.ext
  rw [Work.ThomBordism.radialRescale_coe, hφ, one_smul]

/-- The capping fixes the closed disc bundle of radius `ε`. -/
theorem cap_eq_self_of_le (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (hε : 0 ≤ ε) {p : Work.Tubular.NormalTotal E} (hp : Work.Tubular.normalNorm E p ≤ ε) :
    cap E ε p = p := by
  refine radialRescale_eq_self E _ ?_
  by_cases hr : Work.Tubular.normalNorm E p = 0
  · rw [capCoeff, if_pos hr]
  · rw [capCoeff_eq_min_div hr, min_eq_left hp, div_self hr]

/-- The capping lands in the closed disc bundle of radius `ε`. -/
theorem cap_mem_disc (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (hε : 0 ≤ ε) (p : Work.Tubular.NormalTotal E) :
    Work.Tubular.normalNorm E (cap E ε p) ≤ ε := by
  rw [normalNorm_cap E hε]
  exact min_le_right _ _

/-- The capping is the identity on the image of the tube inverse. -/
theorem cap_inv (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) {y : Work.Tubular.Euc (8 + k)} (hy : y ∈ C.U) :
    cap E ε (C.inv y) = C.inv y :=
  cap_eq_self_of_le E C.eps_pos.le (C.inv_mem y hy)

/-- **The chart map, capped, is a map of pairs** `(ν, ν∖0) → (ℝ^{8+k}, {0}ᶜ)`. -/
theorem chartAffine_cap_ne_zero (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt) {p : Work.Tubular.NormalTotal E}
    (hp : p ∈ Work.Tubular.normalNonzero E) : chartAffine E x (cap E ε p) ≠ 0 := by
  intro h0
  have htube : Work.Tubular.tubeMap E (cap E ε p) = E.e x := by
    have h := congrArg (fun z : Work.Tubular.Euc (8 + k) => z + E.e x) h0
    rw [chartAffine_apply] at h
    rw [sub_add_cancel] at h
    simpa [Work.Tubular.tubeMap] using h
  have hzero : Work.Tubular.tubeMap E (Work.Tubular.zeroSectionNormal E x) = E.e x :=
    Work.ThomBordism.tubeMap_zeroSectionNormal E x
  have hnorm0 : Work.Tubular.normalNorm E (Work.Tubular.zeroSectionNormal E x) = 0 := by
    rw [Work.Tubular.zeroSectionNormal]
    simp
  have hle : Work.Tubular.normalNorm E (cap E ε p) ≤ ε := cap_mem_disc E C.eps_pos.le p
  have heq : cap E ε p = Work.Tubular.zeroSectionNormal E x := by
    have h1 := congrArg C.inv (htube.trans hzero.symm)
    rw [C.inv_tubeMap _ hle, C.inv_tubeMap _ (by rw [hnorm0]; exact C.eps_pos.le)] at h1
    exact h1
  have hcapnorm := normalNorm_cap (E := E) (ε := ε) C.eps_pos.le p
  have hmin : min (Work.Tubular.normalNorm E p) ε = 0 :=
    hcapnorm.symm.trans (by
      have h1 : Work.Tubular.normalNorm E (cap E ε p) = 0 := by
        rw [heq, hnorm0]
      exact h1)
  rw [Work.Tubular.mem_normalNonzero] at hp
  by_cases h : Work.Tubular.normalNorm E p ≤ ε
  · rw [min_eq_left h] at hmin; exact hp hmin
  · rw [min_eq_right (not_le.mp h).le] at hmin
    exact absurd hmin (ne_of_gt C.eps_pos)

theorem continuous_capCoeff {ε : ℝ} (hε : 0 < ε) : Continuous (capCoeff ε) := by
  have hnear : ∀ r : ℝ, r ≠ 0 → |r| ≤ ε → capCoeff ε r = 1 := by
    intro r hr hle
    rw [capCoeff_eq_min_div hr, min_eq_left (abs_le.mp hle).2, div_self hr]
  refine continuous_iff_continuousAt.mpr fun r₀ => ?_
  by_cases hr₀ : r₀ = 0
  · subst hr₀
    refine ContinuousAt.congr (continuousAt_const (y := (1 : ℝ))) ?_
    have hmem : Set.Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) :=
      isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr hε, hε⟩
    filter_upwards [hmem] with r hr
    by_cases h : r = 0
    · rw [h, capCoeff, if_pos rfl]
    · exact (hnear r h (le_of_lt (abs_lt.mpr hr))).symm
  · have hcont : ContinuousAt (fun r : ℝ => min r ε / r) r₀ := by fun_prop
    refine hcont.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hr₀] with r hr
    exact (capCoeff_eq_min_div hr).symm

end

end Work.ThomBordism
