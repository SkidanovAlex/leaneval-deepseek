import Mathlib
import Submission.Work.BW.basisRed_defs
import Submission.Work.BW.basisRed_wNorm_isLatticeNorm
import Submission.Work.BW.Minkowski2.defs
import Submission.Work.BW.Minkowski2.volume_wNorm_ball
import Submission.Work.BW.Minkowski2.succMinL_eq_succMinBody

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.Minkowski2

open MeasureTheory

/-- `wNorm A c` is continuous. -/
private lemma continuous_wNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → ℝ) :
    Continuous (Work.BW.wNorm A c) := by
  have hw : Work.BW.wNorm A c = fun y : Fin n → ℝ =>
      ∑ i : Fin n, c i * |(A.map (Int.castRingHom ℝ)).mulVec y i| := rfl
  rw [hw]
  have hM : Continuous fun y : Fin n → ℝ => (A.map (Int.castRingHom ℝ)).mulVec y :=
    (Matrix.toLin' (A.map (Int.castRingHom ℝ))).continuous_of_finiteDimensional
  refine continuous_finset_sum _ (fun i _ => ?_)
  exact continuous_const.mul (continuous_abs.comp ((continuous_apply i).comp hM))

/-- **Minkowski's second inequality for the weighted `ℓ¹` body**, conditional on the general
Minkowski second-theorem input `hint` (for the standard lattice `ℤᵈ`).

Let `A : Matrix (Fin n) (Fin n) ℤ` have `det A ≠ 0` and let `c : Fin n → ℝ` be positive. The
lattice `A ℤⁿ` has covolume `|det A|`, and the weighted `ℓ¹` body `{x | ∑ᵢ cᵢ |xᵢ| ≤ 1}` has
volume `2^n / (n! ∏ᵢ cᵢ)` (`Work.BW.vol_wl1_ball`); pulling the body back along `A` (change of
variables, `Real.map_matrix_volume_pi_eq_smul_volume_pi`) gives the body
`{y | ∑ᵢ cᵢ |(A y)ᵢ| ≤ 1} = {y | Work.BW.wNorm A c y ≤ 1}`, of volume
`2^n / (n! ∏ᵢ cᵢ |det A|)`. Minkowski's second inequality `λ₁⋯λₙ · vol ≤ 2^n` therefore reads
`∏ⱼ λⱼ ≤ n! · |det A| · ∏ᵢ cᵢ`, where `λⱼ` is the `j`-th successive minimum of the lattice `ℤⁿ`
with respect to the body `{y | Work.BW.wNorm A c y ≤ 1}`, i.e. `Work.BW.succMinL (wNorm A c) j`
(identified with `Work.BW.succMinBody (latOf 1)` by `succMinL_eq_succMinBody`). -/
theorem wNorm_bound_of_int
    (hint : ∀ (d : ℕ) (K : Set (Fin d → ℝ)), Convex ℝ K → (∀ x ∈ K, -x ∈ K) → IsClosed K →
      Bornology.IsBounded K → (interior K).Nonempty →
      (∏ j : Fin d, Work.BW.succMinBody (Work.BW.latOf (1 : Matrix (Fin d) (Fin d) ℤ)) K (j.1 + 1))
        * MeasureTheory.volume.real K ≤ 2 ^ d)
    {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det ≠ 0) (c : Fin n → ℝ)
    (hc : ∀ i, 0 < c i) :
    ∏ j : Fin n, Work.BW.succMinL (Work.BW.wNorm A c) (j.1 + 1) ≤
      (n.factorial : ℝ) * |((A.det : ℤ) : ℝ)| * ∏ i, c i := by
  have hF : Work.BW.IsLatticeNorm (Work.BW.wNorm A c) :=
    Work.BW.basisRed_wNorm_isLatticeNorm A hA c hc
  have hcont : Continuous (Work.BW.wNorm A c) := continuous_wNorm A c
  set K : Set (Fin n → ℝ) := {y | Work.BW.wNorm A c y ≤ 1} with hK
  set P : ℝ := ∏ j : Fin n, Work.BW.succMinL (Work.BW.wNorm A c) (j.1 + 1) with hP
  set D : ℝ := (n.factorial : ℝ) * (∏ i, c i) * |((A.det : ℤ) : ℝ)| with hD
  have hKconv : Convex ℝ K := by
    intro x hx y hy a b ha hb hab
    simp only [hK, Set.mem_setOf_eq] at hx hy ⊢
    have h1 : Work.BW.wNorm A c (a • x + b • y)
        ≤ Work.BW.wNorm A c (a • x) + Work.BW.wNorm A c (b • y) := hF.add_le _ _
    have h2 : Work.BW.wNorm A c (a • x) = a * Work.BW.wNorm A c x := by
      rw [hF.smul, abs_of_nonneg ha]
    have h3 : Work.BW.wNorm A c (b • y) = b * Work.BW.wNorm A c y := by
      rw [hF.smul, abs_of_nonneg hb]
    nlinarith [h1, h2, h3, hx, hy, hab]
  have hKsym : ∀ x ∈ K, -x ∈ K := by
    intro x hx
    simp only [hK, Set.mem_setOf_eq] at hx ⊢
    have h : Work.BW.wNorm A c (-x) = Work.BW.wNorm A c x := by simpa using hF.smul (-1) x
    rw [h]; exact hx
  have hKcl : IsClosed K := by
    rw [hK]
    exact isClosed_le hcont continuous_const
  have hKbd : Bornology.IsBounded K := by
    have hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ x : Fin n → ℝ, δ * ‖x‖ ≤ Work.BW.wNorm A c x := by
      by_cases hn0 : n = 0
      · subst hn0
        refine ⟨1, one_pos, fun x => ?_⟩
        have hx0 : x = 0 := Subsingleton.elim x 0
        subst hx0
        rw [(hF.eq_zero 0).mpr rfl]
        simp
      · haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn0⟩⟩
        have hcomp : IsCompact (Metric.sphere (0 : Fin n → ℝ) 1) := isCompact_sphere 0 1
        have hne : (Metric.sphere (0 : Fin n → ℝ) 1).Nonempty :=
          NormedSpace.sphere_nonempty.mpr (by norm_num)
        obtain ⟨δ, hδpos, hδle⟩ := hcomp.exists_forall_le' hcont.continuousOn (a := 0)
          (by
            intro b hb
            have hb' : ‖b‖ = 1 := by rwa [Metric.mem_sphere, dist_zero_right] at hb
            exact lt_of_le_of_ne (hF.nonneg b) (fun h0 => by
              have hb0 : b = 0 := (hF.eq_zero b).mp h0.symm
              rw [hb0, norm_zero] at hb'
              exact one_ne_zero hb'.symm))
        refine ⟨δ, hδpos, fun x => ?_⟩
        rcases eq_or_ne x 0 with hx0 | hxne
        · subst hx0
          rw [(hF.eq_zero 0).mpr rfl]
          simp
        · have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hxne
          have hmem : (‖x‖⁻¹) • x ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
            rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), inv_mul_cancel₀ hnx]
          have hle := hδle _ hmem
          rw [hF.smul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))] at hle
          have hstep := mul_le_mul_of_nonneg_left hle (le_of_lt (norm_pos_iff.mpr hxne))
          rw [← mul_assoc, mul_inv_cancel₀ hnx, one_mul] at hstep
          rw [mul_comm δ ‖x‖]
          exact hstep
    obtain ⟨δ, hδpos, hδbound⟩ := hδ
    rw [Metric.isBounded_iff_subset_closedBall (0 : Fin n → ℝ)]
    refine ⟨δ⁻¹, fun x hx => ?_⟩
    simp only [hK, Set.mem_setOf_eq] at hx
    rw [Metric.mem_closedBall, dist_zero_right, inv_eq_one_div, le_div_iff₀ hδpos]
    linarith [hδbound x, hx]
  have hKi : (interior K).Nonempty := by
    refine ⟨0, ?_⟩
    rw [hK]
    refine interior_maximal (t := {y : Fin n → ℝ | Work.BW.wNorm A c y < 1}) (fun y hy => ?_)
      (isOpen_lt hcont continuous_const) ?_
    · exact le_of_lt (by simpa using hy)
    · show Work.BW.wNorm A c 0 < 1
      rw [(hF.eq_zero 0).mpr rfl]
      norm_num
  have hB := hint n K hKconv hKsym hKcl hKbd hKi
  have hvol : volume.real K = 2 ^ n / D := by
    rw [hK, volume_wNorm_ball A hA c hc, hD]
  have hid : ∀ j : Fin n, Work.BW.succMinL (Work.BW.wNorm A c) (j.1 + 1) =
      Work.BW.succMinBody (Work.BW.latOf (1 : Matrix (Fin n) (Fin n) ℤ)) K (j.1 + 1) :=
    fun j => succMinL_eq_succMinBody (Work.BW.wNorm A c) hF (by omega)
  have hmain : P * (2 ^ n / D) ≤ 2 ^ n := by
    have h1 : P = ∏ j : Fin n,
        Work.BW.succMinBody (Work.BW.latOf (1 : Matrix (Fin n) (Fin n) ℤ)) K (j.1 + 1) := by
      rw [hP]
      exact Finset.prod_congr rfl (fun j _ => hid j)
    rw [h1, ← hvol]
    exact hB
  have hDpos : 0 < D := by
    rw [hD]
    refine mul_pos (mul_pos (by positivity : (0 : ℝ) < (n.factorial : ℝ))
      (by exact Finset.prod_pos (fun i _ => hc i))) ?_
    · exact abs_pos.mpr (by exact_mod_cast hA)
  have hfin : P ≤ D := by
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    have hstep := mul_le_mul_of_nonneg_right hmain (by positivity : (0 : ℝ) ≤ D / 2 ^ n)
    have hleft : P * (2 ^ n / D) * (D / 2 ^ n) = P := by
      field_simp
    have hright : 2 ^ n * (D / 2 ^ n) = D := by
      field_simp
    rwa [hleft, hright] at hstep
  have hgoal : (n.factorial : ℝ) * |((A.det : ℤ) : ℝ)| * ∏ i, c i = D := by
    rw [hD]; ring
  rw [hgoal]
  exact hfin

end Work.BW.Minkowski2
