import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.Fam1Id
import Submission.Work.FTS.PhiStar.FlatWAux.ModeZDeriv
import Submission.Work.FTS.PhiStar.FlatWAux.Expansion
import Submission.Work.FTS.PhiStar.FlatWAux.PzDthComm
import Submission.Work.FTS.PhiStar.FlatWAux.TsumLopDeriv
import Submission.Work.FTS.PhiStar.FlatWAux.TsumLopDerivU
import Submission.Work.FTS.PhiStar.FlatWAux.TsumLopDerivAux.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.AngDeriv
import Submission.Work.FTS.PhiStar.FlatWAux.QmDerivBound
import Submission.Work.FTS.PhiStar.FlatWAux.QmLopBound
import Submission.Work.FTS.PhiStar.FlatWAux.Decomp
import Submission.Work.FTS.PhiStar.FlatWAux.ModeRescaledSmooth
import Submission.Work.FTS.PhiStar.FlatWAux.RadGreenPhiAjFlat
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Series.EneAux.eFamOdeDerivAux
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.Construction.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.Fam2Diff.TsumContDiff
import Submission.Work.FTS.PhiStar.FlatWAux.Fam2Diff.QmSmooth
import Submission.Work.FTS.PhiStar.FlatWAux.Fam2Diff.LopExpansion
import Submission.Work.FTS.PhiStar.FlatWAux.Fam2Diff.SummBounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

section Helpers

/-- `iteratedDeriv r (deriv g) = iteratedDeriv (r+1) g`. -/
lemma iteratedDeriv_deriv_eq (r : ℕ) (g : ℝ → ℝ) :
    iteratedDeriv r (deriv g) = iteratedDeriv (r + 1) g := by
  induction r with
  | zero => rw [iteratedDeriv_zero, Nat.zero_add, iteratedDeriv_one]
  | succ r ih =>
      rw [iteratedDeriv_succ (n := r) (f := deriv g), ih,
        iteratedDeriv_succ (n := r + 1) (f := g)]

/-- The cast comparison `(i+1) + 1 ≤ i + 2` in `WithTop ℕ∞`. -/
lemma cast_succ_le (i : ℕ) :
    ((i + 1 : ℕ) : WithTop ℕ∞) + 1 ≤ ((i + 2 : ℕ) : WithTop ℕ∞) := by
  have h : ((i + 1 : ℕ) : WithTop ℕ∞) + 1 = ((i + 1 + 1 : ℕ) : WithTop ℕ∞) := by
    push_cast
    ring
  rw [h]

/-- `sin 2θ ≠ 0` on the open interval. -/
lemma s2_ne_zero_of_mem {θ' : ℝ} (hθ' : θ' ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Construction.s2 θ' ≠ 0 := by
  rw [Work.Construction.s2_eq, Real.sin_two_mul]
  exact mul_ne_zero
    (mul_ne_zero two_ne_zero
      (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ'.1 (by linarith [hθ'.2, Real.pi_pos]))))
    (ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ'.1], hθ'.2⟩))

/-- Locality of the iterates of `Lop = sin(2θ) ∂_θ` on an open set. -/
lemma Lop_iter_congr (i : ℕ) {u v : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (h : Set.EqOn u v U) : ∀ θ ∈ U, (Work.Spaces.Lop^[i]) u θ = (Work.Spaces.Lop^[i]) v θ := by
  induction i with
  | zero => intro θ hθ; exact h hθ
  | succ i ih =>
      intro θ hθ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      simp only [Work.Spaces.Lop]
      congr 1
      exact Filter.EventuallyEq.deriv_eq (by
        filter_upwards [hU.mem_nhds hθ] with θ' hθ'
        exact ih θ' hθ')

/-- `Lop^[i]` of a constant multiple (as functions, unconditionally). -/
lemma Lop_iter_const_mul (i : ℕ) (c : ℝ) (u : ℝ → ℝ) :
    (Work.Spaces.Lop^[i]) (fun θ => c * u θ) = fun θ => c * (Work.Spaces.Lop^[i]) u θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      funext θ
      simp only [Work.Spaces.Lop]
      rw [ih, deriv_const_mul_field]
      ring

/-- Smoothness of the rescaled `𝒜^j φ` on `(0,∞)`. -/
lemma contDiffOn_radj (α : ℝ) (j n : ℕ) :
    ContDiffOn ℝ n (fun z' => (z' + 1) / z' * Ajit α j (VocabO.phiA α) z') (Set.Ioi 0) := by
  have h1 : ContDiffOn ℝ n (fun z' : ℝ => (z' + 1) / z') (Set.Ioi 0) :=
    (contDiffOn_id.add contDiffOn_const).div contDiffOn_id (fun z hz => ne_of_gt hz)
  exact h1.mul (contDiffOn_Ajit_phiA α j n)

/-- Smoothness of the rescaled radial Green function on `(0,∞)`. -/
lemma contDiffOn_radJ (α : ℝ) (m n : ℕ) :
    ContDiffOn ℝ n (fun z' => (z' + 1) / z'
      * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z') (Set.Ioi 0) := by
  have h1 : ContDiffOn ℝ n (fun z' : ℝ => (z' + 1) / z') (Set.Ioi 0) :=
    (contDiffOn_id.add contDiffOn_const).div contDiffOn_id (fun z hz => ne_of_gt hz)
  exact h1.mul (contDiffOn_radGreen α m n (contDiffOn_Ajit_phiA α J n))

/-- The purely algebraic rearrangement of the resummed leading terms and the remainder modes:
distributing the factor `(z'+1)/z'` into the radial profiles. -/
lemma psi_alg (α : ℝ) (ψ : ℝ → ℝ) (θ : ℝ) (i : ℕ) (z' : ℝ) :
    ((z' + 1) / z' * α ^ 2)
        * ((∑ j ∈ Finset.range J, α ^ j * Ajit α j (VocabO.phiA α) z'
              * (Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ)
          + α ^ J * (∑' m : ℕ, Series.bmode m ψ
              * ((Gegenbauer.lam m)⁻¹) ^ J
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'
              * (Work.Spaces.Lop^[i]) (deriv (Qm m)) θ))
      = α ^ 2 * ((∑ j ∈ Finset.range J, α ^ j * (Work.Spaces.Lop^[i])
              (Work.FTS.PhiStar.Linv (chia ψ j)) θ * ((z' + 1) / z' * Ajit α j (VocabO.phiA α) z'))
          + α ^ J * (∑' m : ℕ, (Series.bmode m ψ
              * ((Gegenbauer.lam m)⁻¹) ^ J
              * (Work.Spaces.Lop^[i]) (deriv (Qm m)) θ)
              * ((z' + 1) / z' * Radial.radGreen α m
                  (Ajit α J (VocabO.phiA α)) z'))) := by
  rw [show ((z' + 1) / z' * α ^ 2)
        * ((∑ j ∈ Finset.range J, α ^ j * Ajit α j (VocabO.phiA α) z'
              * (Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ)
          + α ^ J * (∑' m : ℕ, Series.bmode m ψ
              * ((Gegenbauer.lam m)⁻¹) ^ J
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'
              * (Work.Spaces.Lop^[i]) (deriv (Qm m)) θ))
      = α ^ 2 * (((z' + 1) / z')
          * ((∑ j ∈ Finset.range J, α ^ j * Ajit α j (VocabO.phiA α) z'
                * (Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ)
            + α ^ J * (∑' m : ℕ, Series.bmode m ψ
                * ((Gegenbauer.lam m)⁻¹) ^ J
                * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'
                * (Work.Spaces.Lop^[i]) (deriv (Qm m)) θ))) from by ring]
  congr 1
  rw [mul_add]
  congr 1
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  · rw [show (z' + 1) / z' * (α ^ J * (∑' m : ℕ, Series.bmode m ψ
          * ((Gegenbauer.lam m)⁻¹) ^ J
          * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'
          * (Work.Spaces.Lop^[i]) (deriv (Qm m)) θ))
        = α ^ J * ((z' + 1) / z' * (∑' m : ℕ, Series.bmode m ψ
          * ((Gegenbauer.lam m)⁻¹) ^ J
          * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'
          * (Work.Spaces.Lop^[i]) (deriv (Qm m)) θ)) from by ring]
    congr 1
    rw [← tsum_mul_left]
    exact tsum_congr (fun m => by ring)

end Helpers

section Angle

/-- **The angular identity.**  For every `z' > 0`, the `i`-fold `D_θ` (preceded by one `∂_θ`) of
the rescaled series is the resummed expression: the leading profiles contribute
`Lop^[i] (Linv (chia ψ j))` and the remainder modes contribute `Lop^[i] (∂_θ Qm m)`. -/
lemma Lop_angle_id (α : ℝ) (ψ : ℝ → ℝ) (θ : ℝ) (i : ℕ) (hi6 : i ≤ 6)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hb0 : Series.bmode 0 ψ = 0)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Series.bmode m ψ| ≤ C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
      |Gegenbauer.eFam m θ'| ≤ C * (2 * (m : ℝ) + 1))
    (hrb : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
          * Radial.radGreen α m (VocabO.phiA α) z'') z'| ≤ C / Gegenbauer.lam m)
    (hrbJ : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
          * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'') z'|
        ≤ C / Gegenbauer.lam m)
    (hexp : ∀ m : ℕ, 1 ≤ m → ∀ z' : ℝ, 0 < z' →
      Radial.radGreen α m (VocabO.phiA α) z'
        = (∑ j ∈ Finset.range J,
            (α ^ j / (Radial.lamR m) ^ (j + 1)) * Ajit α j (VocabO.phiA α) z')
          + (α ^ J / (Radial.lamR m) ^ J)
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z')
    (hchiasm : ∀ j : ℕ, j ≤ J → ∀ n : ℕ,
      ContDiffOn ℝ n (chia ψ j) (Set.Ioo 0 (Real.pi / 2)))
    (hWtDeriv : ∀ j : ℕ, 1 ≤ j → j ≤ J → ∀ θ' : ℝ, θ' ∈ Set.Ioo 0 (Real.pi / 2) →
      deriv (Wt ψ j) θ' = Work.FTS.PhiStar.Linv (chia ψ (j - 1)) θ') :
    ∀ z' : ℝ, 0 < z' →
      (Work.Spaces.Lop^[i]) (deriv (fun θ'' => (z' + 1) / z'
          * (Series.psiSeries α (RemSource α ψ) z' θ'' / Work.Construction.s2 θ''))) θ
        = ((z' + 1) / z' * α ^ 2)
            * ((∑ j ∈ Finset.range J, α ^ j * Ajit α j (VocabO.phiA α) z'
                  * (Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ)
              + α ^ J * (∑' m : ℕ, Series.bmode m ψ
                    * ((Gegenbauer.lam m)⁻¹) ^ J
                    * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'
                    * (Work.Spaces.Lop^[i]) (deriv (Qm m)) θ)) := by
  obtain ⟨CrJ, hCrJ0, hrbJ'⟩ := hrbJ
  have hrbJ0 : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
          * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'') z'|
        ≤ C / Gegenbauer.lam m := ⟨CrJ, hCrJ0, hrbJ'⟩
  -- smoothness of the rescaled profiles
  have hWt_sm : ∀ j : ℕ, 1 ≤ j → j ≤ J → ∀ n : ℕ,
      ContDiffOn ℝ n (Wt ψ j) (Set.Ioo 0 (Real.pi / 2)) := by
    intro j hj1 hjJ n
    have hs2sm : ContDiffOn ℝ n (Work.Construction.s2) (Set.Ioo 0 (Real.pi / 2)) := by
      show ContDiffOn ℝ n (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2))
      fun_prop
    have hdiv : ContDiffOn ℝ n (fun θ' : ℝ => chia ψ j θ' / Work.Construction.s2 θ')
        (Set.Ioo 0 (Real.pi / 2)) :=
      (hchiasm j hjJ n).div hs2sm (fun θ' hθ' => s2_ne_zero_of_mem hθ')
    refine hdiv.congr (fun θ' hθ' => ?_)
    show Wt ψ j θ' = chia ψ j θ' / Work.Construction.s2 θ'
    rw [chia_eq, eq_div_iff (s2_ne_zero_of_mem hθ')]
    ring
  -- the majorant for the θ-derivatives of the divided modes
  let BQ : ℕ → ℝ := fun m => (2 ^ (2 * 8 + 2) + 100) * (2 * (m : ℝ) + 1) ^ 18 + 2
  have hBQ0 : ∀ m : ℕ, 0 ≤ BQ m := fun m => by
    change (0 : ℝ) ≤ (2 ^ (2 * 8 + 2) + 100) * (2 * (m : ℝ) + 1) ^ 18 + 2
    positivity
  have hQbd : ∀ (m r : ℕ), r ≤ 8 → ∀ θ' : ℝ, θ' ∈ Set.Ioo 0 (Real.pi / 2) →
      |iteratedDeriv r (Qm m) θ'| ≤ BQ m := by
    intro m r hr θ' hθ'
    change |iteratedDeriv r (Qm m) θ'| ≤
      (2 ^ (2 * 8 + 2) + 100) * (2 * (m : ℝ) + 1) ^ 18 + 2
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rcases Nat.eq_zero_or_pos r with rfl | hr1
      · rw [iteratedDeriv_zero, Fam2Diff.QmSmooth.2.1 θ' hθ']
        norm_num
      · rw [Fam2Diff.QmSmooth.2.2 r hr1 θ' hθ', abs_zero]
        positivity
    · rcases Nat.eq_zero_or_pos r with rfl | hr1
      · rw [iteratedDeriv_zero]
        refine le_trans (Qm_sup_bound hm hθ') ?_
        have h1 : (1 : ℝ) ≤ 2 * (m : ℝ) + 1 := by
          have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
          linarith
        have h2 : (2 * (m : ℝ) + 1) ^ 2 ≤ (2 * (m : ℝ) + 1) ^ 18 :=
          pow_le_pow_right₀ h1 (by norm_num)
        have h5 : (0 : ℝ) < 2 * (m : ℝ) + 1 := by linarith
        have h6 : (0 : ℝ) < (2 * (m : ℝ) + 1) ^ 18 := pow_pos h5 18
        have h7 : 100 * (2 * (m : ℝ) + 1) ^ 2 ≤ 100 * (2 * (m : ℝ) + 1) ^ 18 :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
        have h8 : (100 : ℝ) ≤ 2 ^ (2 * 8 + 2) + 100 := by norm_num
        nlinarith [h6, h7, h8]
      · refine le_trans (Qm_iteratedDeriv_bound (m := m) (l := r) hm hθ') ?_
        have h1 : (1 : ℝ) ≤ 2 * (m : ℝ) + 1 := by
          have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
          linarith
        have h2 : (2 : ℝ) ^ (2 * r + 2) ≤ 2 ^ 18 :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have h4 : (2 * (m : ℝ) + 1) ^ (r + 3) ≤ (2 * (m : ℝ) + 1) ^ 18 :=
          pow_le_pow_right₀ h1 (by omega)
        have h5 : (0 : ℝ) < 2 * (m : ℝ) + 1 := by linarith
        have h6 : (0 : ℝ) < (2 * (m : ℝ) + 1) ^ 18 := pow_pos h5 18
        have h8 : (2 : ℝ) ^ 18 ≤ 2 ^ (2 * 8 + 2) :=
          pow_le_pow_right₀ (by norm_num) (by norm_num)
        calc 2 ^ (2 * r + 2) * (2 * (m : ℝ) + 1) ^ (r + 3)
            ≤ 2 ^ 18 * (2 * (m : ℝ) + 1) ^ 18 :=
              mul_le_mul h2 h4 (by positivity) (by positivity)
          _ ≤ (2 ^ (2 * 8 + 2) + 100) * (2 * (m : ℝ) + 1) ^ 18 + 2 := by
              nlinarith [h6, h8]
  intro z' hz'
  -- the tail coefficient and the two angular pieces
  let coef : ℕ → ℝ := fun m => Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
      * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'
  let Sf : ℝ → ℝ := fun y => ∑ j ∈ Finset.range J,
      α ^ j * Ajit α j (VocabO.phiA α) z' * Wt ψ (j + 1) y
  let Tf : ℝ → ℝ := fun y => ∑' m : ℕ, coef m * Qm m y
  let Hf : ℝ → ℝ := fun y => Sf y + α ^ J * Tf y
  have hSf_e : Sf = ∑ j ∈ Finset.range J,
      (fun y : ℝ => α ^ j * Ajit α j (VocabO.phiA α) z' * Wt ψ (j + 1) y) := by
    funext y
    show (∑ j ∈ Finset.range J, α ^ j * Ajit α j (VocabO.phiA α) z' * Wt ψ (j + 1) y) = _
    rw [Finset.sum_apply]
  -- summability of the θ-majorant
  have hsumθ : Summable (fun m : ℕ => |Series.bmode m ψ|
      * ((Gegenbauer.lam m)⁻¹) ^ J
      * |Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'| * BQ m) := by
    change Summable (fun m : ℕ => |Series.bmode m ψ|
      * ((Gegenbauer.lam m)⁻¹) ^ J
      * |Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'|
        * ((2 ^ (2 * 8 + 2) + 100) * (2 * (m : ℝ) + 1) ^ 18 + 2))
    exact (Fam2Diff.SummBounds hi6 hz' hθ hb0 hdec hrbJ0).1
  have hcBθ : Summable (fun m : ℕ => |coef m| * BQ m) := by
    have hfun : (fun m : ℕ => |coef m| * BQ m) = fun m : ℕ => |Series.bmode m ψ|
        * ((Gegenbauer.lam m)⁻¹) ^ J
        * |Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'| * BQ m := by
      funext m
      simp only [coef]
      rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (lam_nonneg m)) J)]
    rw [hfun]
    exact hsumθ
  have hQ8 : ∀ m : ℕ, ContDiffOn ℝ 8 (Qm m) (Set.Ioo 0 (Real.pi / 2)) :=
    fun m => Fam2Diff.QmSmooth.1 m
  have hQcd : ∀ m : ℕ, ContDiffOn ℝ (i + 2) (Qm m) (Set.Ioo 0 (Real.pi / 2)) :=
    fun m => (hQ8 m).of_le (by exact_mod_cast (by omega : i + 2 ≤ 8))
  have hTA := Fam2Diff.TsumContDiff (k := i + 2) (c := coef) (q := fun m => Qm m)
    (B := BQ) (a := 0) (b := Real.pi / 2) (by linarith [Real.pi_pos]) hBQ0 hcBθ hQcd
    (fun m r hr θ'' hθ'' => by
      change |iteratedDeriv r (Qm m) θ''| ≤ BQ m
      exact hQbd m r (by omega) θ'' hθ'')
  have hTf_sm : ContDiffOn ℝ (i + 2) Tf (Set.Ioo 0 (Real.pi / 2)) := hTA.1
  have hSf_sm : ContDiffOn ℝ (i + 2) Sf (Set.Ioo 0 (Real.pi / 2)) := by
    refine ContDiffOn.sum (fun j hj => ?_)
    have hjJ : j < J := Finset.mem_range.mp hj
    have hjJ' : j + 1 ≤ J := by simp only [J] at hjJ ⊢; omega
    exact contDiffOn_const.mul (hWt_sm (j + 1) (by omega) hjJ' (i + 2))
  have hHf_sm : ContDiffOn ℝ (i + 2) Hf (Set.Ioo 0 (Real.pi / 2)) :=
    hSf_sm.add (contDiffOn_const.mul hTf_sm)
  have hderivHf_sm : ContDiffOn ℝ (i + 1) (deriv Hf) (Set.Ioo 0 (Real.pi / 2)) :=
    hHf_sm.deriv_of_isOpen isOpen_Ioo (cast_succ_le i)
  have hderivTf_sm : ContDiffOn ℝ (i + 1) (deriv Tf) (Set.Ioo 0 (Real.pi / 2)) :=
    hTf_sm.deriv_of_isOpen isOpen_Ioo (cast_succ_le i)
  have hderivSf_sm : ContDiffOn ℝ (i + 1) (deriv Sf) (Set.Ioo 0 (Real.pi / 2)) :=
    hSf_sm.deriv_of_isOpen isOpen_Ioo (cast_succ_le i)
  -- the `Decomp` hypotheses
  have hQ0 : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ θ' : ℝ,
      θ' ∈ Set.Ioo 0 (Real.pi / 2) → |Qm m θ'| ≤ C * (2 * (m : ℝ) + 1) ^ 2 :=
    ⟨100, by norm_num, fun m hm θ' hθ' => by simpa using Qm_sup_bound hm hθ'⟩
  have hsrc : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ z'' : ℝ, 0 < z'' →
      |(z'' + 1) / z'' * Radial.radGreen α m (VocabO.phiA α) z''| ≤ C / Gegenbauer.lam m := by
    obtain ⟨Cr, hCr0, hrb'⟩ := hrb
    refine ⟨Cr, hCr0, fun m hm z'' hz'' => ?_⟩
    simpa using hrb' m hm 0 (by norm_num) z'' hz''
  have hrem : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ z'' : ℝ, 0 < z'' →
      |(z'' + 1) / z'' * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z''|
        ≤ C / Gegenbauer.lam m := by
    refine ⟨CrJ, hCrJ0, fun m hm z'' hz'' => ?_⟩
    simpa using hrbJ' m hm 0 (by norm_num) z'' hz''
  -- the `Decomp` form of the slice
  have hslice : Set.EqOn
      (fun y => (z' + 1) / z'
        * (Series.psiSeries α (RemSource α ψ) z' y / Work.Construction.s2 y))
      (fun y => (z' + 1) / z' * (α ^ 2 * Hf y)) (Set.Ioo 0 (Real.pi / 2)) := by
    intro y hy
    show (z' + 1) / z' * (Series.psiSeries α (RemSource α ψ) z' y / Work.Construction.s2 y)
      = (z' + 1) / z' * (α ^ 2 * Hf y)
    rw [Decomp α ψ z' y hy hz' hb0 hdec hQ0 hgr hsrc hrem hexp]
  have hderiv_eq : Set.EqOn
      (deriv (fun y => (z' + 1) / z'
        * (Series.psiSeries α (RemSource α ψ) z' y / Work.Construction.s2 y)))
      (fun y => (z' + 1) / z' * α ^ 2 * deriv Hf y) (Set.Ioo 0 (Real.pi / 2)) := by
    intro y hy
    have hev : (fun y => (z' + 1) / z'
        * (Series.psiSeries α (RemSource α ψ) z' y / Work.Construction.s2 y))
        =ᶠ[𝓝 y] (fun y => (z' + 1) / z' * (α ^ 2 * Hf y)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hy] with y' hy'
      exact hslice hy'
    show deriv (fun y => (z' + 1) / z'
        * (Series.psiSeries α (RemSource α ψ) z' y / Work.Construction.s2 y)) y
      = (z' + 1) / z' * α ^ 2 * deriv Hf y
    rw [hev.deriv_eq, deriv_const_mul_field, deriv_const_mul_field]
    ring
  -- the value of `iteratedDeriv (r+1) Sf`
  have hSf_val : ∀ r : ℕ, iteratedDeriv (r + 1) Sf θ
      = ∑ j ∈ Finset.range J, α ^ j * Ajit α j (VocabO.phiA α) z'
          * iteratedDeriv (r + 1) (Wt ψ (j + 1)) θ := by
    intro r
    have hcd : ∀ j ∈ Finset.range J, ContDiffAt ℝ (r + 1)
        (fun y : ℝ => α ^ j * Ajit α j (VocabO.phiA α) z' * Wt ψ (j + 1) y) θ := by
      intro j hj
      have hjJ : j < J := Finset.mem_range.mp hj
      have hjJ' : j + 1 ≤ J := by simp only [J] at hjJ ⊢; omega
      exact (contDiffOn_const.mul (hWt_sm (j + 1) (by omega) hjJ' (r + 1))).contDiffAt
        (isOpen_Ioo.mem_nhds hθ)
    have hsum := iteratedDeriv_sum (n := r + 1) (x := θ) (I := Finset.range J)
      (f := fun j y => α ^ j * Ajit α j (VocabO.phiA α) z' * Wt ψ (j + 1) y) hcd
    rw [hSf_e, hsum]
    exact Finset.sum_congr rfl (fun j _ => by rw [iteratedDeriv_const_mul_field])
  -- the leading contribution
  have hLead : (∑ r ∈ Finset.range (i + 1),
        Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Sf θ)
      = ∑ j ∈ Finset.range J, α ^ j * Ajit α j (VocabO.phiA α) z'
          * (Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ := by
    have hsum_eq : ∀ j : ℕ, j < J →
        (∑ r ∈ Finset.range (i + 1), Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ
            * iteratedDeriv (r + 1) (Wt ψ (j + 1)) θ)
          = (Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ := by
      intro j hjJ
      have hj1 : 1 ≤ j + 1 := by omega
      have hjJ' : j + 1 ≤ J := by simp only [J] at hjJ ⊢; omega
      have hgj : ContDiffOn ℝ (i + 1) (deriv (Wt ψ (j + 1))) (Set.Ioo 0 (Real.pi / 2)) :=
        (hWt_sm (j + 1) hj1 hjJ' (i + 2)).deriv_of_isOpen isOpen_Ioo (cast_succ_le i)
      have hWW : (Work.Spaces.Lop^[i]) (deriv (Wt ψ (j + 1))) θ
          = (Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ := by
        refine Lop_iter_congr i isOpen_Ioo (fun y hy => ?_) θ hθ
        have h := hWtDeriv (j + 1) hj1 hjJ' y hy
        rw [h, show j + 1 - 1 = j from by omega]
      have hsum_eq' : (∑ r ∈ Finset.range (i + 1),
          Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ
            * iteratedDeriv (r + 1) (Wt ψ (j + 1)) θ)
          = (Work.Spaces.Lop^[i]) (deriv (Wt ψ (j + 1))) θ := by
        rw [Fam2Diff.LopExpansion i isOpen_Ioo hgj θ hθ]
        exact Finset.sum_congr rfl (fun r _ => by rw [iteratedDeriv_deriv_eq])
      rw [hsum_eq', hWW]
    calc ∑ r ∈ Finset.range (i + 1),
            Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Sf θ
        = ∑ r ∈ Finset.range (i + 1), ∑ j ∈ Finset.range J,
            Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * (α ^ j
              * Ajit α j (VocabO.phiA α) z' * iteratedDeriv (r + 1) (Wt ψ (j + 1)) θ) := by
          refine Finset.sum_congr rfl (fun r _ => ?_)
          rw [hSf_val r, Finset.mul_sum]
      _ = ∑ j ∈ Finset.range J, ∑ r ∈ Finset.range (i + 1),
            Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * (α ^ j
              * Ajit α j (VocabO.phiA α) z' * iteratedDeriv (r + 1) (Wt ψ (j + 1)) θ) :=
          Finset.sum_comm
      _ = ∑ j ∈ Finset.range J, (α ^ j * Ajit α j (VocabO.phiA α) z')
            * ∑ r ∈ Finset.range (i + 1),
                Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ
                  * iteratedDeriv (r + 1) (Wt ψ (j + 1)) θ := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun r _ => by ring)
      _ = ∑ j ∈ Finset.range J, α ^ j * Ajit α j (VocabO.phiA α) z'
            * (Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [hsum_eq j (Finset.mem_range.mp hj)]
  -- the tail contribution
  have hTail : (Work.Spaces.Lop^[i]) (deriv Tf) θ
      = ∑' m : ℕ, coef m * (Work.Spaces.Lop^[i]) (deriv (Qm m)) θ := by
    have h := TsumLopDerivU coef (fun m => Qm m) BQ hBQ0 hcBθ hQ8
      (fun m r hr θ'' hθ'' => by
        change |iteratedDeriv r (Qm m) θ''| ≤ BQ m
        exact hQbd m r hr θ'' hθ'') i hi6 θ hθ
    exact h
  -- the total
  have hAll : (Work.Spaces.Lop^[i]) (deriv Hf) θ
      = (∑ j ∈ Finset.range J, α ^ j * Ajit α j (VocabO.phiA α) z'
            * (Work.Spaces.Lop^[i]) (Work.FTS.PhiStar.Linv (chia ψ j)) θ)
        + α ^ J * (∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
            * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'
            * (Work.Spaces.Lop^[i]) (deriv (Qm m)) θ) := by
    have h1 : (Work.Spaces.Lop^[i]) (deriv Hf) θ
        = ∑ r ∈ Finset.range (i + 1),
            Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Hf θ := by
      rw [Fam2Diff.LopExpansion i isOpen_Ioo hderivHf_sm θ hθ]
      exact Finset.sum_congr rfl (fun r _ => by rw [iteratedDeriv_deriv_eq])
    have h2 : (∑ r ∈ Finset.range (i + 1),
            Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Hf θ)
        = (∑ r ∈ Finset.range (i + 1),
              Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Sf θ)
          + α ^ J * (∑ r ∈ Finset.range (i + 1),
              Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Tf θ) := by
      have hp : ∀ r ∈ Finset.range (i + 1),
          Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Hf θ
            = Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Sf θ
              + α ^ J * (Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ
                  * iteratedDeriv (r + 1) Tf θ) := by
        intro r hr
        have hle' : (r + 1 : ℕ) ≤ i + 2 := by
          have := Finset.mem_range.mp hr
          omega
        have hSf_cd : ContDiffAt ℝ (r + 1) Sf θ :=
          (hSf_sm.contDiffAt (isOpen_Ioo.mem_nhds hθ)).of_le (by exact_mod_cast hle')
        have hTf_cd : ContDiffAt ℝ (r + 1) Tf θ :=
          (hTf_sm.contDiffAt (isOpen_Ioo.mem_nhds hθ)).of_le (by exact_mod_cast hle')
        have hB_cd : ContDiffAt ℝ (r + 1) (fun y => α ^ J * Tf y) θ :=
          contDiffAt_const.mul hTf_cd
        have hHf_eq : Hf = Sf + fun y => α ^ J * Tf y := rfl
        rw [hHf_eq, iteratedDeriv_add hSf_cd hB_cd, iteratedDeriv_const_mul (α ^ J) hTf_cd]
        ring
      calc (∑ r ∈ Finset.range (i + 1),
              Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Hf θ)
          = ∑ r ∈ Finset.range (i + 1),
              (Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Sf θ
                + α ^ J * (Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ
                    * iteratedDeriv (r + 1) Tf θ)) := Finset.sum_congr rfl hp
        _ = (∑ r ∈ Finset.range (i + 1),
                Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Sf θ)
              + ∑ r ∈ Finset.range (i + 1),
                α ^ J * (Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ
                    * iteratedDeriv (r + 1) Tf θ) := Finset.sum_add_distrib
        _ = (∑ r ∈ Finset.range (i + 1),
                Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Sf θ)
              + α ^ J * (∑ r ∈ Finset.range (i + 1),
                Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ
                  * iteratedDeriv (r + 1) Tf θ) := by rw [Finset.mul_sum]
    have h3 : (∑ r ∈ Finset.range (i + 1),
            Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Tf θ)
          = ∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'
              * (Work.Spaces.Lop^[i]) (deriv (Qm m)) θ := by
      have h2' : (∑ r ∈ Finset.range (i + 1),
            Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) Tf θ)
          = (Work.Spaces.Lop^[i]) (deriv Tf) θ := by
        rw [Fam2Diff.LopExpansion i isOpen_Ioo hderivTf_sm θ hθ]
        exact Finset.sum_congr rfl (fun r _ => by rw [iteratedDeriv_deriv_eq])
      rw [h2', hTail]
    rw [h1, h2, hLead, h3]
  -- the identification of the derivative of the slice
  have hval : (Work.Spaces.Lop^[i]) (deriv (fun θ'' => (z' + 1) / z'
        * (Series.psiSeries α (RemSource α ψ) z' θ'' / Work.Construction.s2 θ''))) θ
      = (z' + 1) / z' * α ^ 2 * (Work.Spaces.Lop^[i]) (deriv Hf) θ := by
    rw [Lop_iter_congr i isOpen_Ioo hderiv_eq θ hθ, Lop_iter_const_mul]
  rw [hval, hAll]

end Angle

end Work.FTS.PhiStar.FlatWAux
