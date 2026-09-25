import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy

open scoped NNReal ENNReal ContDiff Topology
open Set Filter Function

namespace Work.CR.Flat.Cauchy

/-- If `u` is smooth then so is `z ↦ ∂̄_j u z`: the `j`-th `∂̄`-derivative is the fixed
linear combination
`(1/2)((fderiv ℝ u z)(e_j) + i·(fderiv ℝ u z)(i·e_j))`
of two directional derivatives, and `z ↦ fderiv ℝ u z` is smooth for smooth `u`. -/
lemma contDiff_dbarCoord_of_contDiff {n : ℕ} (j : Fin n) {u : (Fin n → ℂ) → ℂ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => dbarCoord j u z) := by
  rw [show (fun z => dbarCoord j u z) =
      (fun z : Fin n → ℂ => (1 / 2 : ℂ) *
        (fderiv ℝ u z (Pi.single j 1) + Complex.I * fderiv ℝ u z (Pi.single j Complex.I)))
      from by funext z; rw [dbarCoord]]
  have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ u) := hu.fderiv_right le_rfl
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => fderiv ℝ u z (Pi.single j (1 : ℂ))) := hfd.clm_apply contDiff_const
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => fderiv ℝ u z (Pi.single j Complex.I)) := hfd.clm_apply contDiff_const
  exact ContDiff.mul contDiff_const (h1.add (ContDiff.mul contDiff_const h2))

/-- **A smooth cutoff adapted to two nested polydiscs.**

For `0 < r₁ j < r₂ j` there is a smooth `η : ℂⁿ → ℝ` with values in `[0,1]`, equal to `1` on the
closed polydisc of multiracius `r₁`, vanishing outside the open polydisc of multiracius `r₂`
(i.e. `η z = 0` as soon as `∃ j, r₂ j ≤ ‖z j - c j‖`), and such that the complexified bump and all
its `∂̄_j`-derivatives are compactly supported; the `∂̄_j`-derivatives are smooth as well.

The regularity of `η` is `ContDiff ℝ ∞` (smooth), written below as
`ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)`, *not* `ContDiff ℝ ⊤`: the latter is real-analyticity in this
Mathlib (`contDiff_omega_iff_analyticOnNhd`) and is impossible for a non-trivial cutoff.

Construction: `η z = ∏ j, (⟨r₁ j, r₂ j, h1 j, h2 j⟩ : ContDiffBump (c j)) (z j)`, using
`ContDiffBump.one_of_mem_closedBall` and `ContDiffBump.zero_of_le_dist`; compact support follows
since `η` (and hence `∂̄ j η`) vanishes off the compact closed polydisc of multiradius `r₂`.

Please prove this directly (do NOT import the module
`Submission.Work.CR.Flat.Cauchy.exists_polydiscCutoff`, which contains a false statement with a
`sorry`); the construction is short. -/
theorem polydiscCutoff {n : ℕ} {c : Fin n → ℂ} {r₁ r₂ : Fin n → ℝ} (k : ℕ)
    (h1 : ∀ j, 0 < r₁ j) (h2 : ∀ j, r₁ j < r₂ j) :
    ∃ η : (Fin n → ℂ) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧ (∀ z, 0 ≤ η z ∧ η z ≤ 1) ∧
      (∀ z, (∀ j, ‖z j - c j‖ ≤ r₁ j) → η z = 1) ∧
      (∀ z, (∃ j, r₂ j ≤ ‖z j - c j‖) → η z = 0) ∧
      HasCompactSupport (fun z => (η z : ℂ)) ∧
      (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z => Work.CR.Flat.dbarCoord j (fun y => (η y : ℂ)) z)) ∧
      (∀ j, HasCompactSupport (fun z => Work.CR.Flat.dbarCoord j (fun y => (η y : ℂ)) z)) := by
  classical
  have _hk : k = k := rfl
  -- The one-variable bumps and their product.
  let B : ∀ j, ContDiffBump (c j) := fun j => ⟨r₁ j, r₂ j, h1 j, h2 j⟩
  let η : (Fin n → ℂ) → ℝ := fun z => ∏ j, B j (z j)
  -- The closed polydisc of multiradius `r₂`, which carries the support.
  let K : Set (Fin n → ℂ) := {z | ∀ j, ‖z j - c j‖ ≤ r₂ j}
  have hK : IsCompact K := by
    have h : K = Set.univ.pi (fun j => Metric.closedBall (c j) (r₂ j)) := by
      ext z; simp [K, Metric.mem_closedBall, dist_eq_norm]
    rw [h]
    exact isCompact_univ_pi fun j => isCompact_closedBall _ _
  -- Smoothness of the bump.
  have hηcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η := by
    refine contDiff_prod fun j _ => ?_
    exact (ContDiffBump.contDiff (n := ⊤) (f := B j)).comp (contDiff_apply ℝ ℂ j)
  -- The pointwise bounds.
  have hη0 : ∀ z, 0 ≤ η z := fun z => Finset.prod_nonneg fun j _ => (B j).nonneg
  have hη1 : ∀ z, η z ≤ 1 := fun z =>
    Finset.prod_le_one₀ (fun j _ => (B j).nonneg) fun j _ => (B j).le_one
  -- `η` is `1` on the closed polydisc of multiradius `r₁` …
  have hηone : ∀ z, (∀ j, ‖z j - c j‖ ≤ r₁ j) → η z = 1 := by
    intro z hz
    exact Finset.prod_eq_one fun j _ => (B j).one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, dist_eq_norm]; exact hz j)
  -- … and `0` outside the open polydisc of multiradius `r₂`.
  have hηzero : ∀ z, (∃ j, r₂ j ≤ ‖z j - c j‖) → η z = 0 := by
    rintro z ⟨j, hj⟩
    exact Finset.prod_eq_zero (Finset.mem_univ j) ((B j).zero_of_le_dist (by
      rw [dist_eq_norm]; exact hj))
  have hηnotK : ∀ z, ¬ (∀ j, ‖z j - c j‖ ≤ r₂ j) → η z = 0 := by
    intro z hz
    rw [not_forall] at hz
    obtain ⟨j, hj⟩ := hz
    exact hηzero z ⟨j, le_of_lt (not_le.mp hj)⟩
  -- Compact support of the complexified bump.
  have hsupp : HasCompactSupport (fun z => (η z : ℂ)) := by
    refine HasCompactSupport.of_support_subset_isCompact (K := K) hK ?_
    intro z hz
    by_contra hzK
    simp only [Function.mem_support, ne_eq] at hz
    exact hz (by simp [hηnotK z hzK])
  -- Smoothness of the complexified bump and of its `∂̄`-derivatives.
  have hud : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (η z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hηcd
  have hdcd : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => Work.CR.Flat.dbarCoord j (fun y => (η y : ℂ)) z) :=
    fun j => contDiff_dbarCoord_of_contDiff j hud
  -- Compact support of the `∂̄`-derivatives: the function is *locally* zero off `K`, hence its
  -- derivative vanishes there.
  have hdsupp : ∀ i, HasCompactSupport
      (fun z => Work.CR.Flat.dbarCoord i (fun y => (η y : ℂ)) z) := by
    intro i
    refine HasCompactSupport.of_support_subset_isCompact (K := K) hK ?_
    intro z hz
    by_contra hzK
    obtain ⟨j, hj⟩ : ∃ j, r₂ j < ‖z j - c j‖ := by
      have hzK' : ¬ (∀ j, ‖z j - c j‖ ≤ r₂ j) := fun hh => hzK hh
      rw [not_forall] at hzK'
      obtain ⟨j, hj⟩ := hzK'
      exact ⟨j, not_le.mp hj⟩
    -- `η` vanishes on a whole neighbourhood of `z`, since the `j`-th coordinate inequality is
    -- strict there.
    have hev : (fun y => (η y : ℂ)) =ᶠ[𝓝 z] 0 := by
      have hS : {w : Fin n → ℂ | r₂ j < ‖w j - c j‖} ∈ 𝓝 z :=
        IsOpen.mem_nhds
          (isOpen_lt continuous_const ((continuous_apply j).sub continuous_const).norm) hj
      filter_upwards [hS] with w hw
      simp [hηzero w ⟨j, le_of_lt hw⟩]
    have hf0 : fderiv ℝ (fun y => (η y : ℂ)) z = 0 := by
      rw [hev.fderiv_eq]; simp
    simp only [Function.mem_support, ne_eq] at hz
    exact hz (by simp [Work.CR.Flat.dbarCoord, hf0])
  exact ⟨η, hηcd, fun z => ⟨hη0 z, hη1 z⟩, hηone, hηzero, hsupp, hdcd, hdsupp⟩

end Work.CR.Flat.Cauchy
