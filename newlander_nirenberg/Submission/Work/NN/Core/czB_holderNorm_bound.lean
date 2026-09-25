import Mathlib
import Submission.Work.NN.Core.bmPotential_dCoord_eq
import Submission.Work.CR.Flat.Cauchy.bmDzKernel_cz_bound
import Submission.Work.NN.Core.bmPotentialHolderContinuous
import Submission.Work.CR.Flat.Holder.Bilinear
import Submission.Work.NN.Core.czB_near_bound
import Submission.Work.NN.Core.czB_far_bound

/-!
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The global `C^{0,α}` bound for `∂_{z_i}(bmPotential F)`

For a family `F` of `C¹` functions with `F j z = 0` whenever `‖z‖ ≥ R` (so each `F j` is
compactly supported in the sup-ball of radius `R`),

  `‖∂_i (bmPotential F)‖_{C^{0,α}(ℂⁿ)} ≤ C · Σ_j ‖F j‖_{C^{0,α}(ℂⁿ)}`.

The estimate is proved in two halves, each a separate lemma proved elsewhere:

* `Work.NN.Core.czB_near_bound` — the bound on the ball `‖z‖ ≤ 4(√n(R+1))+4`, which is the
  polydisc statement `bmPotential_dCoord_holderNorm_le` combined with the uniform-in-`z`
  Calderón–Zygmund bound `bmDzKernel_cz_bound`;
* `Work.NN.Core.czB_far_bound` — the bound outside that ball, where the support of `F` stays away
  from the singular set of the kernel so that the integration-by-parts representation
  `∂_i(bmPotential F)(z) = -Σ_j ∫_{eucBall 4ρ} bmDzKernel i j x (F j(z+x) - F j z) dx` can be
  estimated by the support of the datum.

This file proves the reduction of the target theorem to those two halves: the two halves give a
pointwise sup bound and a pointwise `α`-Hölder bound on the inner and outer regions, a mixed pair
is handled by radially projecting the outer point onto the sphere `‖z‖ = threshold` (so that the
two resulting pairs are inner–inner and outer–outer), and the pointwise bounds are converted into
the `ℝ≥0∞`-valued `C^{0,α}` norm.
-/
noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.NN.Core

/-! ## Elementary scaling lemmas -/

/-- Radial projection of a point with `m ≤ ‖v‖` onto the sphere of radius `m`. -/
lemma norm_smul_div_self {n : ℕ} {m : ℝ} (hm : 0 < m) {v : Fin n → ℂ} (hv : m ≤ ‖v‖) :
    ‖(m / ‖v‖) • v‖ = m := by
  have hvpos : 0 < ‖v‖ := lt_of_lt_of_le hm hv
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hm.le (norm_nonneg v))]
  exact div_mul_cancel₀ m (ne_of_gt hvpos)

/-- The distance from the radial projection to the original point. -/
lemma norm_smul_div_self_sub {n : ℕ} {m : ℝ} (hm : 0 < m) {v : Fin n → ℂ} (hv : m ≤ ‖v‖) :
    ‖(m / ‖v‖) • v - v‖ = ‖v‖ - m := by
  have hvpos : 0 < ‖v‖ := lt_of_lt_of_le hm hv
  have hle : m / ‖v‖ - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one hvpos]; exact hv
  have h1 : (m / ‖v‖) • v - v = ((m / ‖v‖) - 1) • v := by rw [sub_smul, one_smul]
  rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonpos hle, neg_sub, sub_mul, one_mul,
    div_mul_cancel₀ _ (ne_of_gt hvpos)]

/-! ## The mixed case of a Hölder estimate -/

/-- A mixed pair (one point inside the ball of radius `m`, one outside) is controlled by
projecting the outer point radially onto the sphere `‖z‖ = m`. -/
lemma holder_sub_le_mixed {n : ℕ} {α : ℝ} (hα0 : 0 < α) {u : (Fin n → ℂ) → ℂ}
    {CN CF m T : ℝ} (hm : 0 < m) (hT : 0 ≤ T) (hCN : 0 ≤ CN) (hCF : 0 ≤ CF)
    (hN : ∀ z z' : Fin n → ℂ, ‖z‖ ≤ m → ‖z'‖ ≤ m →
      ‖u z - u z'‖ ≤ CN * ‖z - z'‖ ^ α * T)
    (hF : ∀ z z' : Fin n → ℂ, m ≤ ‖z‖ → m ≤ ‖z'‖ →
      ‖u z - u z'‖ ≤ CF * ‖z - z'‖ ^ α * T) :
    (∀ z z' : Fin n → ℂ, ‖z‖ ≤ m → m ≤ ‖z'‖ →
        ‖u z - u z'‖ ≤ (2 ^ α * CN + CF) * ‖z - z'‖ ^ α * T) ∧
    (∀ z z' : Fin n → ℂ, m ≤ ‖z‖ → ‖z'‖ ≤ m →
        ‖u z - u z'‖ ≤ (2 ^ α * CN + CF) * ‖z - z'‖ ^ α * T) := by
  have h2a : (0 : ℝ) ≤ 2 ^ α := Real.rpow_nonneg (by norm_num) α
  have h2a1 : (1 : ℝ) ≤ 2 ^ α := Real.one_le_rpow (by norm_num) hα0.le
  have key : ∀ z z' : Fin n → ℂ, ‖z‖ ≤ m → m ≤ ‖z'‖ →
      ‖u z - u z'‖ ≤ (2 ^ α * CN + CF) * ‖z - z'‖ ^ α * T := by
    intro z z' hz hz'
    set ψ : Fin n → ℂ := (m / ‖z'‖) • z' with hψdef
    have hψnorm : ‖ψ‖ = m := by
      rw [hψdef]; exact norm_smul_div_self hm hz'
    have hψdist : ‖ψ - z'‖ = ‖z'‖ - m := by
      rw [hψdef]; exact norm_smul_div_self_sub hm hz'
    have hd : (0 : ℝ) ≤ ‖z - z'‖ := norm_nonneg _
    have hz'le : ‖z'‖ - m ≤ ‖z - z'‖ := by
      have h2 : ‖z'‖ ≤ ‖z‖ + ‖z - z'‖ := by
        calc ‖z'‖ = ‖z + (z' - z)‖ := by rw [show z + (z' - z) = z' from by abel]
          _ ≤ ‖z‖ + ‖z' - z‖ := norm_add_le _ _
          _ = ‖z‖ + ‖z - z'‖ := by rw [norm_sub_rev]
      linarith
    have hψle : ‖z - ψ‖ ≤ 2 * ‖z - z'‖ := by
      have h3 : ‖z - ψ‖ ≤ ‖z - z'‖ + ‖z' - ψ‖ := by
        have h4 := norm_add_le (z - z') (z' - ψ)
        rwa [show (z - z') + (z' - ψ) = z - ψ from by abel] at h4
      have h5 : ‖z' - ψ‖ ≤ ‖z - z'‖ := by
        rw [norm_sub_rev, hψdist]; exact hz'le
      linarith
    have hpn := hN z ψ hz (le_of_eq hψnorm)
    have hpf := hF ψ z' hψnorm.ge hz'
    have htri : ‖u z - u z'‖ ≤ ‖u z - u ψ‖ + ‖u ψ - u z'‖ := by
      have h4 := norm_add_le (u z - u ψ) (u ψ - u z')
      rwa [show (u z - u ψ) + (u ψ - u z') = u z - u z' from by ring] at h4
    have hstep1 : ‖u z - u ψ‖ ≤ CN * (2 * ‖z - z'‖) ^ α * T :=
      le_trans hpn (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) hψle hα0.le) hCN) hT)
    have hstep2 : ‖u ψ - u z'‖ ≤ CF * ‖z - z'‖ ^ α * T :=
      le_trans hpf (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) (by rw [hψdist]; exact hz'le) hα0.le) hCF) hT)
    calc ‖u z - u z'‖
        ≤ CN * (2 * ‖z - z'‖) ^ α * T + CF * ‖z - z'‖ ^ α * T := le_trans htri (add_le_add hstep1 hstep2)
      _ = (2 ^ α * CN + CF) * ‖z - z'‖ ^ α * T := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hd]; ring
  constructor
  · exact key
  · intro z z' hz hz'
    have h := key z' z hz' hz
    rw [← norm_sub_rev (u z) (u z'), ← norm_sub_rev z z'] at h
    exact h

/-! ## From the pointwise bounds to the `C^{0,α}` norm -/

/-- The `0`-th iterated derivative (i.e. the function itself) evaluated at a point. -/
lemma ofReal_norm_le_iterDerivNorm_zero {n : ℕ} {f : (Fin n → ℂ) → ℂ} (z : Fin n → ℂ) :
    ENNReal.ofReal ‖f z‖ ≤ Work.CR.Flat.iterDerivNorm 0 f Set.univ := by
  rw [Work.CR.Flat.iterDerivNorm_zero]
  exact le_iSup₂_of_le z (Set.mem_univ z) le_rfl

/-- If the `C^{0,α}` norm of `f` on `univ` is finite then so are its two summands. -/
lemma holderNorm_zero_summands_ne_top {n : ℕ} {α : ℝ} {f : (Fin n → ℂ) → ℂ}
    (h : Work.CR.Flat.holderNorm 0 α f Set.univ ≠ ⊤) :
    Work.CR.Flat.iterDerivNorm 0 f Set.univ ≠ ⊤ ∧
      Work.CR.Flat.holderSeminorm 0 α f Set.univ ≠ ⊤ := by
  have hsum : Work.CR.Flat.holderNorm 0 α f Set.univ
      = Work.CR.Flat.iterDerivNorm 0 f Set.univ
        + Work.CR.Flat.holderSeminorm 0 α f Set.univ := by
    rw [Work.CR.Flat.holderNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  constructor
  · intro h'; exact h (by rw [hsum, h', top_add])
  · intro h'; exact h (by rw [hsum, h', add_top])

/-- The `C^{0,α}` norm of a family as an `ofReal` of the sum of the `toReal` data. -/
lemma holderNorm_zero_sum_eq_ofReal {n : ℕ} {α : ℝ} {F : Fin n → (Fin n → ℂ) → ℂ}
    (h : ∀ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ ≠ ⊤) :
    (∑ j : Fin n, Work.CR.Flat.holderNorm 0 α (F j) Set.univ)
      = ENNReal.ofReal (∑ j : Fin n,
          ((Work.CR.Flat.iterDerivNorm 0 (F j) Set.univ).toReal
            + (Work.CR.Flat.holderSeminorm 0 α (F j) Set.univ).toReal)) := by
  rw [ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hsum : Work.CR.Flat.holderNorm 0 α (F j) Set.univ
        = Work.CR.Flat.iterDerivNorm 0 (F j) Set.univ
          + Work.CR.Flat.holderSeminorm 0 α (F j) Set.univ := by
      rw [Work.CR.Flat.holderNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hsum, ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (holderNorm_zero_summands_ne_top (h j)).1,
      ENNReal.ofReal_toReal (holderNorm_zero_summands_ne_top (h j)).2]
  · intro j _
    exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg


/-! ## The reduction: two halves give the global estimate -/

/-- If the near-field and far-field estimates for `∂_i (bmPotential F)` hold, then the global
`C^{0,α}` estimate follows. -/
lemma czB_holderNorm_bound_of {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (R : ℝ) (hR : 0 ≤ R)
    (hnear : ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Fin n → (Fin n → ℂ) → ℂ) (A K : Fin n → ℝ),
      (∀ j, ContDiff ℝ 1 (F j)) →
      (∀ j, 0 ≤ A j) → (∀ j, 0 ≤ K j) →
      (∀ j z, R ≤ ‖z‖ → F j z = 0) →
      (∀ j z, ‖F j z‖ ≤ A j) →
      (∀ j x y, ‖F j x - F j y‖ ≤ K j * ‖x - y‖ ^ α) →
      ∀ i : Fin n,
        (∀ z : Fin n → ℂ, ‖z‖ ≤ 4 * (Real.sqrt n * (R + 1)) + 4 →
          ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z‖
            ≤ C * ∑ j, (A j + K j)) ∧
        (∀ z z' : Fin n → ℂ, ‖z‖ ≤ 4 * (Real.sqrt n * (R + 1)) + 4 →
          ‖z'‖ ≤ 4 * (Real.sqrt n * (R + 1)) + 4 →
          ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z
            - Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z'‖
            ≤ C * ‖z - z'‖ ^ α * ∑ j, (A j + K j)))
    (hfar : ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Fin n → (Fin n → ℂ) → ℂ) (A K : Fin n → ℝ),
      (∀ j, ContDiff ℝ 1 (F j)) →
      (∀ j, 0 ≤ A j) → (∀ j, 0 ≤ K j) →
      (∀ j z, R ≤ ‖z‖ → F j z = 0) →
      (∀ j z, ‖F j z‖ ≤ A j) →
      (∀ j x y, ‖F j x - F j y‖ ≤ K j * ‖x - y‖ ^ α) →
      ∀ i : Fin n,
        (∀ z : Fin n → ℂ, 4 * (Real.sqrt n * (R + 1)) + 4 ≤ ‖z‖ →
          ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z‖
            ≤ C * ∑ j, (A j + K j)) ∧
        (∀ z z' : Fin n → ℂ, 4 * (Real.sqrt n * (R + 1)) + 4 ≤ ‖z‖ →
          4 * (Real.sqrt n * (R + 1)) + 4 ≤ ‖z'‖ →
          ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z
            - Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z'‖
            ≤ C * ‖z - z'‖ ^ α * ∑ j, (A j + K j))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, ContDiff ℝ 1 (F j)) →
      (∀ j, HasCompactSupport (F j)) →
      (∀ j z, R ≤ ‖z‖ → F j z = 0) →
      ∀ i : Fin n,
        Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord i
          (Work.CR.Flat.Cauchy.bmPotential F) z) Set.univ
          ≤ ENNReal.ofReal C * ∑ j : Fin n, Work.CR.Flat.holderNorm 0 α (F j) Set.univ := by
  obtain ⟨CN, hCN, hnear'⟩ := hnear
  obtain ⟨CF, hCF, hfar'⟩ := hfar
  have h2a : (0 : ℝ) ≤ 2 ^ α := Real.rpow_nonneg (by norm_num) α
  have h2a1 : (1 : ℝ) ≤ 2 ^ α := Real.one_le_rpow (by norm_num) hα0.le
  have hC1 : (0 : ℝ) ≤ max CN CF := le_trans hCN (le_max_left _ _)
  have hC2 : (0 : ℝ) ≤ 2 ^ α * CN + CF := add_nonneg (mul_nonneg h2a hCN) hCF
  have hCtot : (0 : ℝ) ≤ max CN CF + (2 ^ α * CN + CF) := add_nonneg hC1 hC2
  have hCbig : (0 : ℝ) < max CN CF + (2 ^ α * CN + CF) + 1 := by linarith
  refine ⟨max CN CF + (2 ^ α * CN + CF) + 1, le_of_lt hCbig, ?_⟩
  intro F hF _hcs hvan i
  by_cases htop : (∑ j : Fin n, Work.CR.Flat.holderNorm 0 α (F j) Set.univ) = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hCbig)]
    exact le_top
  · have hfin : ∀ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ ≠ ⊤ := by
      intro j hj
      exact htop (top_le_iff.mp (hj ▸ Finset.single_le_sum
        (f := fun i => Work.CR.Flat.holderNorm 0 α (F i) Set.univ)
        (fun i _ => bot_le) (Finset.mem_univ j)))
    have hpart : ∀ j, Work.CR.Flat.iterDerivNorm 0 (F j) Set.univ ≠ ⊤ ∧
        Work.CR.Flat.holderSeminorm 0 α (F j) Set.univ ≠ ⊤ :=
      fun j => holderNorm_zero_summands_ne_top (hfin j)
    let A : Fin n → ℝ := fun j => (Work.CR.Flat.iterDerivNorm 0 (F j) Set.univ).toReal
    let K : Fin n → ℝ := fun j => (Work.CR.Flat.holderSeminorm 0 α (F j) Set.univ).toReal
    have hA0 : ∀ j, 0 ≤ A j := fun j => ENNReal.toReal_nonneg
    have hK0 : ∀ j, 0 ≤ K j := fun j => ENNReal.toReal_nonneg
    have hAb : ∀ j z, ‖F j z‖ ≤ A j := by
      intro j z
      have h1 : ENNReal.ofReal ‖F j z‖ ≤ Work.CR.Flat.iterDerivNorm 0 (F j) Set.univ :=
        ofReal_norm_le_iterDerivNorm_zero z
      have h2 := ENNReal.toReal_mono (hpart j).1 h1
      rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at h2
    have hKb : ∀ j x y, ‖F j x - F j y‖ ≤ K j * ‖x - y‖ ^ α := by
      intro j x y
      rcases eq_or_ne x y with rfl | hxy
      · simp [Real.zero_rpow hα0.ne']
      · have hden : 0 < ‖x - y‖ ^ α :=
          Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
        have h1 : ENNReal.ofReal (‖F j x - F j y‖ / ‖x - y‖ ^ α)
            ≤ Work.CR.Flat.holderSeminorm 0 α (F j) Set.univ := by
          have h := Work.CR.Flat.le_holderSeminorm 0 α (F j) Set.univ (Set.mem_univ x)
            (Set.mem_univ y) hxy
          rwa [Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub] at h
        have h2 : ‖F j x - F j y‖ / ‖x - y‖ ^ α ≤ K j := by
          have h3 := ENNReal.toReal_mono (hpart j).2 h1
          rwa [ENNReal.toReal_ofReal (div_nonneg (norm_nonneg _) hden.le)] at h3
        calc ‖F j x - F j y‖ = (‖F j x - F j y‖ / ‖x - y‖ ^ α) * ‖x - y‖ ^ α :=
              (div_mul_cancel₀ _ hden.ne').symm
          _ ≤ K j * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_right h2 hden.le
    obtain ⟨hsupN, hholN⟩ := hnear' F A K hF hA0 hK0 hvan hAb hKb i
    obtain ⟨hsupF, hholF⟩ := hfar' F A K hF hA0 hK0 hvan hAb hKb i
    let m : ℝ := 4 * (Real.sqrt n * (R + 1)) + 4
    have hmpos : 0 < m := by
      have h1 : (0 : ℝ) ≤ Real.sqrt n * (R + 1) :=
        mul_nonneg (Real.sqrt_nonneg n) (by linarith)
      show 0 < 4 * (Real.sqrt n * (R + 1)) + 4
      linarith
    have hTnn : (0 : ℝ) ≤ ∑ j, (A j + K j) :=
      Finset.sum_nonneg fun j _ => add_nonneg (hA0 j) (hK0 j)
    -- the pointwise sup bound
    have hsup : ∀ z : Fin n → ℂ,
        ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z‖
          ≤ max CN CF * ∑ j, (A j + K j) := by
      intro z
      rcases lt_or_ge ‖z‖ m with hz | hz
      · exact le_trans (hsupN z (le_of_lt hz)) (mul_le_mul_of_nonneg_right (le_max_left _ _) hTnn)
      · exact le_trans (hsupF z hz) (mul_le_mul_of_nonneg_right (le_max_right _ _) hTnn)
    -- the pointwise Hölder bound
    have hhol : ∀ z z' : Fin n → ℂ,
        ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z
          - Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z'‖
          ≤ (2 ^ α * CN + CF) * ‖z - z'‖ ^ α * ∑ j, (A j + K j) := by
      intro z z'
      rcases eq_or_ne z z' with hzz | hne
      · subst hzz
        simp [Real.zero_rpow hα0.ne']
      · rcases lt_or_ge ‖z‖ m with hz | hz
        · rcases lt_or_ge ‖z'‖ m with hz' | hz'
          · refine le_trans (hholN z z' (le_of_lt hz) (le_of_lt hz')) ?_
            have h1 : CN ≤ 2 ^ α * CN + CF := by
              have := mul_le_mul_of_nonneg_right h2a1 hCN; linarith
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              h1 (Real.rpow_nonneg (norm_nonneg _) α)) hTnn
          · exact (holder_sub_le_mixed hα0 hmpos hTnn hCN hCF hholN hholF).1 z z' (le_of_lt hz) hz'
        · rcases lt_or_ge ‖z'‖ m with hz' | hz'
          · exact (holder_sub_le_mixed hα0 hmpos hTnn hCN hCF hholN hholF).2 z z' hz (le_of_lt hz')
          · refine le_trans (hholF z z' hz hz') ?_
            have h1 : CF ≤ 2 ^ α * CN + CF := by
              have := mul_nonneg h2a hCN; linarith
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              h1 (Real.rpow_nonneg (norm_nonneg _) α)) hTnn
    -- the `ℝ≥0∞`-valued statement
    have hsum_eq : (∑ j : Fin n, Work.CR.Flat.holderNorm 0 α (F j) Set.univ)
        = ENNReal.ofReal (∑ j, (A j + K j)) := holderNorm_zero_sum_eq_ofReal hfin
    have hstep1 : Work.CR.Flat.iterDerivNorm 0
          (fun z => Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z) Set.univ
        ≤ ENNReal.ofReal (max CN CF * ∑ j, (A j + K j)) :=
      iterDerivNorm_zero_le_ofReal (mul_nonneg hC1 hTnn) hsup
    have hstep2 : Work.CR.Flat.holderSeminorm 0 α
          (fun z => Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z) Set.univ
        ≤ ENNReal.ofReal ((2 ^ α * CN + CF) * ∑ j, (A j + K j)) :=
      holderSeminorm_zero_le_ofReal (mul_nonneg hC2 hTnn) fun z z' =>
        (by
          have h := hhol z z'
          calc ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z
                - Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z'‖
              ≤ (2 ^ α * CN + CF) * ‖z - z'‖ ^ α * ∑ j, (A j + K j) := h
            _ = ((2 ^ α * CN + CF) * ∑ j, (A j + K j)) * ‖z - z'‖ ^ α := by ring)
    rw [Work.CR.Flat.holderNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hsum_eq]
    calc Work.CR.Flat.iterDerivNorm 0
            (fun z => Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z) Set.univ
          + Work.CR.Flat.holderSeminorm 0 α
            (fun z => Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z) Set.univ
        ≤ ENNReal.ofReal (max CN CF * ∑ j, (A j + K j))
          + ENNReal.ofReal ((2 ^ α * CN + CF) * ∑ j, (A j + K j)) := add_le_add hstep1 hstep2
      _ = ENNReal.ofReal ((max CN CF + (2 ^ α * CN + CF)) * ∑ j, (A j + K j)) := by
          rw [← ENNReal.ofReal_add (mul_nonneg hC1 hTnn) (mul_nonneg hC2 hTnn)]
          ring_nf
      _ = ENNReal.ofReal (max CN CF + (2 ^ α * CN + CF))
            * ENNReal.ofReal (∑ j, (A j + K j)) := ENNReal.ofReal_mul hCtot
      _ ≤ ENNReal.ofReal (max CN CF + (2 ^ α * CN + CF) + 1)
            * ENNReal.ofReal (∑ j, (A j + K j)) :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by linarith)) zero_le

/-! ## The target statement -/

theorem czB_holderNorm_bound {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, ContDiff ℝ 1 (F j)) →
      (∀ j, HasCompactSupport (F j)) →
      (∀ j z, R ≤ ‖z‖ → F j z = 0) →
      ∀ i : Fin n,
        Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord i
          (Work.CR.Flat.Cauchy.bmPotential F) z) Set.univ
          ≤ ENNReal.ofReal C * ∑ j : Fin n, Work.CR.Flat.holderNorm 0 α (F j) Set.univ :=
  czB_holderNorm_bound_of hn hα0 hα1 R hR
    (czB_near_bound (n := n) hn hα0 hα1 (R := R) hR)
    (czB_far_bound (n := n) hn hα0 hα1 (R := R) hR)

end Work.NN.Core
