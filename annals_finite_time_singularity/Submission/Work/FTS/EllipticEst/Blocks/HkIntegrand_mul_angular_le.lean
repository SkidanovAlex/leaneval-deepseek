import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.Lop_iter_mul
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.GbarSetup
import Submission.Work.FTS.EllipticEst.sinIter_weight_bound
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.Blocks.DthIter_angular_mul_expand
import Submission.Work.FTS.EllipticEst.Blocks.LopIter_sin_two_le
import Submission.Work.FTS.EllipticEst.Blocks.LopIter_sin_sq_le
import Submission.Work.FTS.EllipticEst.Blocks.angular_sq_mul_Wt_sq_le
import Submission.Work.FTS.EllipticEst.Blocks.angular_sq_mul_Wt_sq_le_radial

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Blocks

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The angular factor commutes with `D_z` -/

theorem DzIter_angular_mul (i : ℕ) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (fun z θ => a θ * f z θ)
      = fun z θ => a θ * Work.Spaces.DzIter i f z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      show z * deriv (fun z' => a θ * Work.Spaces.DzIter i f z' θ) z
          = a θ * (z * deriv (fun z' => Work.Spaces.DzIter i f z' θ) z)
      rw [deriv_const_mul_field]
      ring

/-! ## The termwise bound for one Leibniz summand -/

theorem angular_summand_sq_le_le (k : ℕ) (a : ℝ → ℝ) (K : ℕ → ℝ)
    (ha1 : ∀ θ : ℝ, |a θ| ≤ 1) (hK : ∀ m : ℕ, 0 ≤ K m)
    (hKb : ∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.FTS.EllipticEst.LopIter m a θ) ^ 2 ≤ K m * (Real.sin (2 * θ)) ^ 2) :
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (i j m : ℕ), α ≤ 1 → 1 ≤ i → i + j ≤ k → m ≤ i →
      ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
        ((i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
            * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ (i.choose m : ℝ) ^ 2 * (K m + 1) * Work.Spaces.HkIntegrand α k f z θ := by
  intro α f i j m hα1 hi1 hij hmi z θ hθ0 hθ1
  have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hHe : 0 ≤ Work.Spaces.HkIntegrand α k f z θ := Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hjk : j ≤ k := by omega
  have hmk : m ≤ k := by omega
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    have ha2 : (a θ) ^ 2 ≤ 1 := by
      have h := pow_le_pow_left₀ (abs_nonneg (a θ)) (ha1 θ) 2
      rwa [sq_abs, one_pow] at h
    have hmix := Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i j hi1 hij
    have h0c : ((i.choose 0 : ℝ)) = 1 := by simp
    rw [h0c, Nat.sub_zero]
    simp only [Work.FTS.EllipticEst.LopIter_zero, Nat.cast_one, one_mul]
    calc (a θ * Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        = (a θ) ^ 2 * (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
      _ ≤ 1 * Work.Spaces.HkIntegrand α k f z θ :=
          mul_le_mul ha2 hmix (sq_nonneg _) (by norm_num)
      _ ≤ 1 ^ 2 * (K 0 + 1) * Work.Spaces.HkIntegrand α k f z θ := by
          have h1 : (1 : ℝ) ≤ K 0 + 1 := by linarith [hK 0]
          calc (1 : ℝ) * Work.Spaces.HkIntegrand α k f z θ
              ≤ (K 0 + 1) * Work.Spaces.HkIntegrand α k f z θ :=
                mul_le_mul_of_nonneg_right h1 hHe
            _ = 1 ^ 2 * (K 0 + 1) * Work.Spaces.HkIntegrand α k f z θ := by ring
  · rcases Nat.lt_or_eq_of_le hmi with hlt | heq
    · -- 1 ≤ m < i, so 1 ≤ i - m
      have hpos' : 1 ≤ i - m := by omega
      have hd := hKb m hpos hmk θ hθIoo
      have h6 := angular_sq_mul_Wt_sq_le (K := K m) (d := Work.FTS.EllipticEst.LopIter m a θ)
        (u := Work.Spaces.mixed j (i - m) f z θ) (α := α) (z := z) (θ := θ)
        (hK m) hθIoo hd
      have hmix := Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ (i - m) j hpos' (by omega)
      calc ((i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2
          = (i.choose m : ℝ) ^ 2 * ((Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2) := by ring
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m * (Work.Spaces.mixed j (i - m) f z θ
              * Work.Spaces.Wt α z θ) ^ 2) := mul_le_mul_of_nonneg_left h6 (sq_nonneg _)
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m * Work.Spaces.HkIntegrand α k f z θ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmix (hK m)) (sq_nonneg _)
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m + 1) * Work.Spaces.HkIntegrand α k f z θ := by
            have h1 : K m * Work.Spaces.HkIntegrand α k f z θ
                ≤ (K m + 1) * Work.Spaces.HkIntegrand α k f z θ :=
              mul_le_mul_of_nonneg_right (by linarith) hHe
            calc (i.choose m : ℝ) ^ 2 * (K m * Work.Spaces.HkIntegrand α k f z θ)
                ≤ (i.choose m : ℝ) ^ 2 * ((K m + 1) * Work.Spaces.HkIntegrand α k f z θ) :=
                  mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
              _ = (i.choose m : ℝ) ^ 2 * (K m + 1) * Work.Spaces.HkIntegrand α k f z θ := by ring
    · -- m = i, so i - m = 0
      have hz0 : i - m = 0 := by omega
      have hd := hKb m hpos hmk θ hθIoo
      have h7 := angular_sq_mul_Wt_sq_le_radial (K := K m) (d := Work.FTS.EllipticEst.LopIter m a θ)
        (u := Work.Spaces.mixed j (i - m) f z θ) (α := α) (z := z) (θ := θ)
        hα1 (hK m) hθIoo hd
      rw [hz0, Work.Spaces.mixed_zero_right] at h7
      have hz' : (Work.Spaces.DzIter j f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ Work.Spaces.HkIntegrand α k f z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α k f z θ j hjk
      rw [hz0, Work.Spaces.mixed_zero_right]
      calc ((i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.DzIter j f z θ * Work.Spaces.Wt α z θ) ^ 2
          = (i.choose m : ℝ) ^ 2 * ((Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2) := by ring
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m * (Work.Spaces.DzIter j f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) :=
            mul_le_mul_of_nonneg_left h7 (sq_nonneg _)
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m * Work.Spaces.HkIntegrand α k f z θ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz' (hK m)) (sq_nonneg _)
        _ ≤ (i.choose m : ℝ) ^ 2 * (K m + 1) * Work.Spaces.HkIntegrand α k f z θ := by
            have h1 : K m * Work.Spaces.HkIntegrand α k f z θ
                ≤ (K m + 1) * Work.Spaces.HkIntegrand α k f z θ :=
              mul_le_mul_of_nonneg_right (by linarith) hHe
            calc (i.choose m : ℝ) ^ 2 * (K m * Work.Spaces.HkIntegrand α k f z θ)
                ≤ (i.choose m : ℝ) ^ 2 * ((K m + 1) * Work.Spaces.HkIntegrand α k f z θ) :=
                  mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
              _ = (i.choose m : ℝ) ^ 2 * (K m + 1) * Work.Spaces.HkIntegrand α k f z θ := by ring

/-! ## The generic estimate -/

theorem HkIntegrand_angular_mul_le (k : ℕ) (a : ℝ → ℝ) (K : ℕ → ℝ)
    (ha1 : ∀ θ : ℝ, |a θ| ≤ 1)
    (ha : ∀ θ : ℝ, ContDiffAt ℝ ⊤ a θ)
    (hK : ∀ m : ℕ, 0 ≤ K m)
    (hKb : ∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.FTS.EllipticEst.LopIter m a θ) ^ 2 ≤ K m * (Real.sin (2 * θ)) ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.HkIntegrand α k (fun z θ => a θ * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ := by
  set KB : ℝ := ∑ m ∈ Finset.range (k + 1), (K m + 1) with hKBdef
  have hKBpos : 0 < KB := by
    rw [hKBdef]
    exact Finset.sum_pos (fun m _ => by linarith [hK m])
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos k)⟩
  set CB : ℝ := ((2 : ℝ) ^ k) ^ 2 with hCBdef
  have hCBnonneg : 0 ≤ CB := by rw [hCBdef]; positivity
  set Cpair : ℝ := ((k : ℝ) + 1) * CB * KB with hCpairdef
  have hCpairnonneg : 0 ≤ Cpair := by rw [hCpairdef]; positivity
  set C1 : ℝ := ((k : ℝ) + 1) ^ 2 * Cpair with hC1def
  refine ⟨((k : ℝ) + 1) + C1, by positivity, ?_⟩
  intro α f hα hα1 hf z θ hz hθ0 hθ1
  have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hHe : 0 ≤ Work.Spaces.HkIntegrand α k f z θ := Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hZi : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => a θ * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ ((k : ℝ) + 1) * Work.Spaces.HkIntegrand α k f z θ := by
    have hterm : ∀ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => a θ * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [DzIter_angular_mul i a f]
      have ha2 : (a θ) ^ 2 ≤ 1 := by
        have h := pow_le_pow_left₀ (abs_nonneg (a θ)) (ha1 θ) 2
        rwa [sq_abs, one_pow] at h
      calc (a θ * Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = (a θ) ^ 2 * (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
        _ ≤ 1 * (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
            mul_le_mul_of_nonneg_right ha2 (sq_nonneg _)
        _ = (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := one_mul _
        _ ≤ Work.Spaces.HkIntegrand α k f z θ := Work.Spaces.sq_le_HkIntegrand_z α k f z θ i hik
    calc (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => a θ * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range (k + 1), Work.Spaces.HkIntegrand α k f z θ :=
          Finset.sum_le_sum hterm
      _ = ((k : ℝ) + 1) * Work.Spaces.HkIntegrand α k f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hMi : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ C1 * Work.Spaces.HkIntegrand α k f z θ := by
    have hpair : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1),
        (1 ≤ i ∧ i + j ≤ k) →
        (Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ Cpair * Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi j hj hc
      obtain ⟨hi1, hij⟩ := hc
      have hik : i ≤ k := by omega
      have hjk : j ≤ k := by omega
      have hexp : Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ
          = ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ := by
        have hag : Work.FTS.EllipticEst.SmoothOpen (fun z θ => a θ * f z θ) := by
          have haG : ContDiff ℝ ⊤ a := contDiff_iff_contDiffAt.mpr ha
          have haC : ContDiff ℝ Work.Stability.smoothOrder a := haG.of_le le_top
          have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
              (fun p : ℝ × ℝ => a p.2) Q0 :=
            haC.contDiffOn.comp contDiffOn_snd (fun p _ => Set.mem_univ p.2)
          have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Q0 := hf
          have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
              (fun p : ℝ × ℝ => a p.2 * f p.1 p.2) Q0 := h1.mul h2
          exact h3
        rw [← Work.FTS.EllipticEst.SmoothOpen.DthIter_DzIter_eq_mixed hag j i hz hθIoo]
        rw [DzIter_angular_mul j a f]
        rw [DthIter_angular_mul_expand ha hf i j hz hθIoo]
        exact Finset.sum_congr rfl fun m _ => by
          rw [Work.FTS.EllipticEst.SmoothOpen.DthIter_DzIter_eq_mixed hf j (i - m) hz hθIoo]
      rw [hexp]
      have hstep : (∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ) * Work.Spaces.Wt α z θ
          = ∑ m ∈ Finset.range (i + 1), ((i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) := by
        rw [Finset.sum_mul]
      rw [hstep]
      have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
        (f := fun m => (i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
          * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ)
      have hbound : ∑ m ∈ Finset.range (i + 1), ((i.choose m : ℝ)
            * Work.FTS.EllipticEst.LopIter m a θ
            * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ CB * KB * Work.Spaces.HkIntegrand α k f z θ := by
        have hchoose : ∀ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 ≤ CB := by
          intro m hm
          have h1 : (i.choose m : ℝ) ≤ (2 : ℝ) ^ k := by
            have h2 : i.choose m ≤ 2 ^ k := le_trans (Nat.choose_le_two_pow i m)
              (Nat.pow_le_pow_right (by norm_num) hik)
            exact_mod_cast h2
          calc (i.choose m : ℝ) ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
            _ = CB := by rw [hCBdef]
        have hsumKB : ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 * (K m + 1)
            ≤ CB * KB := by
          have hstep1 : ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 * (K m + 1)
              ≤ ∑ m ∈ Finset.range (i + 1), CB * (K m + 1) := by
            refine Finset.sum_le_sum fun m hm => ?_
            exact mul_le_mul_of_nonneg_right (hchoose m hm) (by linarith [hK m])
          have hstep2 : ∑ m ∈ Finset.range (i + 1), CB * (K m + 1)
              = CB * ∑ m ∈ Finset.range (i + 1), (K m + 1) := by
            rw [Finset.mul_sum]
          have hstep3 : ∑ m ∈ Finset.range (i + 1), (K m + 1) ≤ KB := by
            rw [hKBdef]
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro m hm
              simp only [Finset.mem_range] at hm ⊢
              omega
            · intro m _ _
              linarith [hK m]
          calc _ ≤ ∑ m ∈ Finset.range (i + 1), CB * (K m + 1) := hstep1
            _ = CB * ∑ m ∈ Finset.range (i + 1), (K m + 1) := hstep2
            _ ≤ CB * KB := mul_le_mul_of_nonneg_left hstep3 hCBnonneg
        calc ∑ m ∈ Finset.range (i + 1), ((i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2
            ≤ ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 * (K m + 1)
                * Work.Spaces.HkIntegrand α k f z θ := by
              refine Finset.sum_le_sum fun m hm => ?_
              have hmi : m ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
              exact angular_summand_sq_le_le k a K ha1 hK hKb α f i j m hα1 hi1 hij hmi
                z θ hθ0 hθ1
          _ = Work.Spaces.HkIntegrand α k f z θ
                * ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) ^ 2 * (K m + 1) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun m _ => by ring
          _ ≤ Work.Spaces.HkIntegrand α k f z θ * (CB * KB) :=
              mul_le_mul_of_nonneg_left hsumKB hHe
          _ = CB * KB * Work.Spaces.HkIntegrand α k f z θ := by ring
      have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
        rw [Finset.card_range]
        push_cast
        ring
      calc (∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m a θ
              * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ (((Finset.range (i + 1)).card : ℕ) : ℝ) * ∑ m ∈ Finset.range (i + 1),
              ((i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
                * Work.Spaces.mixed j (i - m) f z θ * Work.Spaces.Wt α z θ) ^ 2 := hcs
        _ ≤ (((i : ℝ) + 1)) * (CB * KB * Work.Spaces.HkIntegrand α k f z θ) := by
            rw [hcard]
            exact mul_le_mul_of_nonneg_left hbound (by positivity)
        _ ≤ ((k : ℝ) + 1) * (CB * KB * Work.Spaces.HkIntegrand α k f z θ) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have : (i : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hik
            linarith
        _ = Cpair * Work.Spaces.HkIntegrand α k f z θ := by
            rw [hCpairdef]
            ring
    calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ ∑ _i ∈ Finset.range (k + 1), ∑ _j ∈ Finset.range (k + 1),
            Cpair * Work.Spaces.HkIntegrand α k f z θ := by
          refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · rw [if_pos hc]
            exact hpair i hi j hj hc
          · rw [if_neg hc]
            exact mul_nonneg hCpairnonneg hHe
      _ = C1 * Work.Spaces.HkIntegrand α k f z θ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rw [hC1def]
          push_cast
          ring
  rw [Work.Spaces.HkIntegrand]
  refine le_trans (add_le_add hZi hMi) (le_of_eq ?_)
  ring

/-! ## The target theorem -/

/-- **Multiplying by a bounded angular profile does not increase the `H^k`-integrand.**  For
`f` smooth on the open quadrant and `a` one of the two profiles occurring in the `ℛ`-transfer,

`HkIntegrand α k (a·f) ≤ C_k HkIntegrand α k f`   pointwise on the open quadrant,

with `a θ = sin 2θ` resp. `a θ = sin²θ`.  The constant depends only on `k` (not on `α ≤ 1`).

PLACEMENT.  Put this in namespace `Work.FTS.EllipticEst.Blocks` (so the fully qualified name is
`Work.FTS.EllipticEst.Blocks.HkIntegrand_mul_angular_le`).

ROUTE.  `D_z` and `D_θ` commute and `a` depends on `θ` only, so the pure-`D_z` summands satisfy
`D_z^i(a·f) = a·D_z^i f` exactly, and `|a| ≤ 1` gives those terms.  For the mixed summands,
`D_θ^i(D_z^j(a f)) = D_θ^i(a · u_j)` with `u_j = D_z^j f z ·`, and the iterated Leibniz rule
`Lop_iter_mul` for the derivation `L = D_θ = sin(2θ)∂_θ` (with `D_θ^i` = `LopIter i`) expands it
as `∑_{m ≤ i} C(i,m) (D_θ^m a)(D_θ^{i-m} u_j)`.  For `m ≥ 1`, `D_θ^m a = L^m a` is divisible by
`sin 2θ` (because `L = sin(2θ)∂_θ` maps functions divisible by `sin 2θ` into themselves) and
bounded (a trig polynomial), so the corresponding term is bounded by a constant times
`(D_θ^{i-m}u_j)² w² sin^{2-γ}` with `2 - γ ≥ 0`, and `sin^{2-γ} ≤ sin^{-γ}` resp.
`sin^{2-γ} ≤ sin^{-η}`; these are summands of `HkIntegrand α k f` (at index `i-m ≥ 1` in the
mixed sum, or at `i-m = 0` in the `D_z`-sum, where the weight `w/sin^{η/2}` is the one
dominating `sin^{2-γ}`).  The `m = 0` term is `|a|·|D_θ^iu_j|·Wt ≤ |D_θ^iu_j|·Wt`, again a
summand of `HkIntegrand α k f`.  Summing the finitely many terms (with the binomial
coefficients, for the `k+1` values of `i` and `j ≤ k`) gives the stated constant. -/
theorem HkIntegrand_mul_angular_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.HkIntegrand α k (fun z θ => Real.sin (2 * θ) * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ) ∧
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.HkIntegrand α k (fun z θ => Real.sin θ ^ 2 * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ) := by
  obtain ⟨K2, hK2nn, hK2b⟩ := LopIter_sin_two_le k
  obtain ⟨K3, hK3nn, hK3b⟩ := LopIter_sin_sq_le k
  have hsin2 : ∀ θ : ℝ, ContDiffAt ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) θ := by
    have hlin : ContDiff ℝ ⊤ (fun t : ℝ => 2 * t) := contDiff_const.mul contDiff_id
    have h : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) :=
      (Real.contDiff_sin (n := ⊤)).comp hlin
    exact fun θ => h.contDiffAt
  have hsinsq : ∀ θ : ℝ, ContDiffAt ℝ ⊤ (fun θ : ℝ => Real.sin θ ^ 2) θ := by
    have h : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin θ ^ 2) := (Real.contDiff_sin (n := ⊤)).pow 2
    exact fun θ => h.contDiffAt
  have ha1sq : ∀ θ : ℝ, |Real.sin θ ^ 2| ≤ 1 := by
    intro θ
    rw [abs_of_nonneg (sq_nonneg _)]
    calc Real.sin θ ^ 2 = |Real.sin θ| ^ 2 := by rw [sq_abs]
      _ ≤ 1 := pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one θ)
  obtain ⟨C2, hC2pos, hC2⟩ := HkIntegrand_angular_mul_le k (fun θ => Real.sin (2 * θ))
    (fun _ => K2) (fun θ => Real.abs_sin_le_one (2 * θ)) hsin2 (fun _ => hK2nn)
    (fun m _ hmk θ hθ => hK2b m hmk θ hθ)
  obtain ⟨C3, hC3pos, hC3⟩ := HkIntegrand_angular_mul_le k (fun θ => Real.sin θ ^ 2)
    (fun _ => K3) ha1sq hsinsq (fun _ => hK3nn)
    (fun m hm1 hmk θ hθ => by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact hK3b m' (by omega) θ hθ)
  refine ⟨max C2 C3, lt_max_of_lt_left hC2pos, ?_⟩
  intro α f hα hα1 hf
  refine ⟨?_, ?_⟩
  · intro z θ hz hθ0 hθ1
    exact le_trans (hC2 α f hα hα1 hf z θ hz hθ0 hθ1)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Work.Spaces.HkIntegrand_nonneg α k f z θ))
  · intro z θ hz hθ0 hθ1
    exact le_trans (hC3 α f hα hα1 hf z θ hz hθ0 hθ1)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Work.Spaces.HkIntegrand_nonneg α k f z θ))

end Work.FTS.EllipticEst.Blocks
