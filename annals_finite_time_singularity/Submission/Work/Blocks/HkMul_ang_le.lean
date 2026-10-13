import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.Lop_iter_mul
import Submission.Work.FTS.EllipticEst.sinIter_weight_bound
import Submission.Work.FTS.EllipticEst.Blocks.LopIter_sin_sq_le
import Submission.Work.FTS.EllipticEst.Blocks.LopIter_sin_two_le
import Submission.Work.FTS.EllipticEst.Blocks.DthIter_angular_mul_expand
import Submission.Work.FTS.EllipticEst.Blocks.angular_sq_mul_Wt_sq_le
import Submission.Work.FTS.EllipticEst.Blocks.angular_sq_mul_Wt_sq_le_radial
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.Coercivity.HkIntegrand_endpoint_zero
import Submission.Work.FTS.LocData.HkMem_of_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary smoothness and boundedness of the two angular profiles -/

private theorem contDiffAt_sin_two (θ : ℝ) :
    ContDiffAt ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) θ := by
  have hlin : ContDiff ℝ ⊤ (fun t : ℝ => 2 * t) := contDiff_const.mul contDiff_id
  have h : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) :=
    (Real.contDiff_sin (n := ⊤)).comp hlin
  exact h.contDiffAt

private theorem contDiffAt_sin_sq (θ : ℝ) :
    ContDiffAt ℝ ⊤ (fun θ : ℝ => Real.sin θ ^ 2) θ := by
  have h : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin θ ^ 2) := (Real.contDiff_sin (n := ⊤)).pow 2
  exact h.contDiffAt

private theorem abs_sin_two_le_one (θ : ℝ) : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one _

private theorem abs_sin_sq_le_one (θ : ℝ) : |Real.sin θ ^ 2| ≤ 1 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  calc Real.sin θ ^ 2 = |Real.sin θ| ^ 2 := by rw [sq_abs]
    _ ≤ 1 := pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one θ)

/-! ## Multiplying by an angular profile preserves `SmoothOpen` -/

private theorem smoothOpen_angMul {a : ℝ → ℝ} (ha : ∀ θ : ℝ, ContDiffAt ℝ ⊤ a θ)
    {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => a θ * f z θ) := by
  have haG : ContDiff ℝ ⊤ a := contDiff_iff_contDiffAt.mpr ha
  have haC : ContDiff ℝ Work.Stability.smoothOrder a := haG.of_le le_top
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a p.2)
      Work.FTS.EllipticEst.Q0 :=
    haC.contDiffOn.comp contDiffOn_snd (fun p _ => Set.mem_univ p.2)
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => a p.2 * f p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    h1.mul hf
  exact h3

/-! ## The angular factor commutes with `D_z` -/

private theorem DzIter_angular_mul (i : ℕ) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (fun z θ => a θ * f z θ)
      = fun z θ => a θ * Work.Spaces.DzIter i f z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      show z * deriv (fun z' => a θ * Work.Spaces.DzIter i f z' θ) z
          = a θ * (z * deriv (fun z' => Work.Spaces.DzIter i f z' θ) z)
      rw [deriv_const_mul_field (a θ)]
      ring

/-! ## The termwise bound for one Leibniz summand -/

private theorem angular_summand_sq_le_le (k : ℕ) (a : ℝ → ℝ) (K : ℕ → ℝ)
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
      have h6 := Work.FTS.EllipticEst.Blocks.angular_sq_mul_Wt_sq_le
        (K := K m) (d := Work.FTS.EllipticEst.LopIter m a θ)
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
      have h7 := Work.FTS.EllipticEst.Blocks.angular_sq_mul_Wt_sq_le_radial
        (K := K m) (d := Work.FTS.EllipticEst.LopIter m a θ)
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

/-! ## The generic estimate on the open quadrant -/

private theorem HkIntegrand_ang_mul_le_int (k : ℕ) (a : ℝ → ℝ) (K : ℕ → ℝ)
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
  have hKBnn : 0 ≤ KB := le_of_lt hKBpos
  set CB : ℝ := ((2 : ℝ) ^ k) ^ 2 with hCBdef
  have hCBnonneg : 0 ≤ CB := by rw [hCBdef]; positivity
  set Cpair : ℝ := ((k : ℝ) + 1) * CB * KB with hCpairdef
  have hCpairnonneg : 0 ≤ Cpair := by
    rw [hCpairdef]
    exact mul_nonneg (mul_nonneg (by positivity) hCBnonneg) hKBnn
  set C1 : ℝ := ((k : ℝ) + 1) ^ 2 * Cpair with hC1def
  have hC1nonneg : 0 ≤ C1 := by
    rw [hC1def]
    exact mul_nonneg (sq_nonneg _) hCpairnonneg
  refine ⟨((k : ℝ) + 1) + C1, by linarith, ?_⟩
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
        have hag : Work.FTS.EllipticEst.SmoothOpen (fun z θ => a θ * f z θ) :=
          smoothOpen_angMul ha hf
        rw [← Work.FTS.EllipticEst.SmoothOpen.DthIter_DzIter_eq_mixed hag j i hz hθIoo]
        rw [DzIter_angular_mul j a f]
        rw [Work.FTS.EllipticEst.Blocks.DthIter_angular_mul_expand ha hf i j hz hθIoo]
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
      have hCBKBnn : 0 ≤ CB * KB * Work.Spaces.HkIntegrand α k f z θ :=
        mul_nonneg (mul_nonneg hCBnonneg hKBnn) hHe
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
            refine mul_le_mul_of_nonneg_right ?_ hCBKBnn
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

/-! ## Extension to the closed quadrant -/

/-- The pointwise inequality, known on the *open* quadrant, extends to the closed quadrant
`Iz ×ˢ Iθ`: on the two boundary lines `z = 0` and `sin(2θ) = 0` both `ℋ^k`-integrands
vanish (`HkIntegrand_zero_fst`, `HkIntegrand_eq_zero_of_sin_eq_zero`). -/
private theorem closed_of_interior {k : ℕ} {a : ℝ → ℝ} {C : ℝ}
    (hint : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.HkIntegrand α k (fun z θ => a θ * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ) :
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f →
      ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => a θ * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ := by
  intro α f hα hα1 hf z hz θ hθ
  have hzge : (0 : ℝ) ≤ z := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hz
  have hθb : (0 : ℝ) ≤ θ ∧ θ ≤ Real.pi / 2 := by
    simpa only [Work.Spaces.Iθ, Set.mem_Icc] using hθ
  rcases eq_or_lt_of_le hzge with h0 | hpos
  · rw [← h0, Work.FTS.LocData.HkIntegrand_zero_fst α k (fun z θ => a θ * f z θ) θ,
      Work.FTS.LocData.HkIntegrand_zero_fst α k f θ, mul_zero]
  · by_cases hs : Real.sin (2 * θ) = 0
    · rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k (fun z θ => a θ * f z θ) z θ hs,
        Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k f z θ hs, mul_zero]
    · have hθ1 : 0 < θ := by
        rcases eq_or_lt_of_le hθb.1 with h | h
        · exact absurd (by rw [← h]; simp) hs
        · exact h
      have hθ2 : θ < Real.pi / 2 := by
        rcases lt_or_eq_of_le hθb.2 with h | h
        · exact h
        · exact absurd (by rw [h, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring,
            Real.sin_pi]) hs
      exact hint α f hα hα1 hf z θ hpos hθ1 hθ2

/-! ## The pointwise inequality on the closed quadrant, for the two profiles -/

private theorem HkIntegrand_mul_ang_le_pt (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f →
      (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => Real.sin (2 * θ) * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ) ∧
      (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => Real.sin θ ^ 2 * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ) := by
  obtain ⟨K2, hK2nn, hK2b⟩ := Work.FTS.EllipticEst.Blocks.LopIter_sin_two_le k
  obtain ⟨K3, hK3nn, hK3b⟩ := Work.FTS.EllipticEst.Blocks.LopIter_sin_sq_le k
  obtain ⟨C2, hC2pos, hC2int⟩ := HkIntegrand_ang_mul_le_int k (fun θ => Real.sin (2 * θ))
    (fun _ => K2) abs_sin_two_le_one contDiffAt_sin_two (fun _ => hK2nn)
    (fun m _ hmk θ hθ => hK2b m hmk θ hθ)
  obtain ⟨C3, hC3pos, hC3int⟩ := HkIntegrand_ang_mul_le_int k (fun θ => Real.sin θ ^ 2)
    (fun _ => K3) abs_sin_sq_le_one contDiffAt_sin_sq (fun _ => hK3nn)
    (fun m hm1 hmk θ hθ => by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact hK3b m' (by omega) θ hθ)
  refine ⟨max C2 C3, lt_max_of_lt_left hC2pos, ?_⟩
  intro α f hα hα1 hf
  constructor
  · refine closed_of_interior (k := k) (a := fun θ => Real.sin (2 * θ)) (C := max C2 C3)
      (fun α f hα hα1 hf z θ hz hθ0 hθ1 => le_trans (hC2int α f hα hα1 hf z θ hz hθ0 hθ1)
        (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Work.Spaces.HkIntegrand_nonneg α k f z θ))) α f hα hα1 hf
  · refine closed_of_interior (k := k) (a := fun θ => Real.sin θ ^ 2) (C := max C2 C3)
      (fun α f hα hα1 hf z θ hz hθ0 hθ1 => le_trans (hC3int α f hα hα1 hf z θ hz hθ0 hθ1)
        (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Work.Spaces.HkIntegrand_nonneg α k f z θ))) α f hα hα1 hf

/-! ## Transfer of `HkMem` and `HkSq` along a pointwise domination of the integrand -/

private theorem HkSq_le_of_integrand_le (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ} (C : ℝ)
    (hmf : Work.Spaces.HkMem α k f)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k g z θ ≤ C * Work.Spaces.HkIntegrand α k f z θ) :
    Work.Spaces.HkSq α k g ≤ C * Work.Spaces.HkSq α k f := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
        ≤ C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) := by
    intro z hz
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α k f z θ :=
      MeasureTheory.integral_mono_of_nonneg
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun θ => Work.Spaces.HkIntegrand α k g z θ)
        (g := fun θ => C * Work.Spaces.HkIntegrand α k f z θ)
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
        ((hmf.1 z hz).const_mul C)
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => hpt z hz θ hθ)
    rwa [MeasureTheory.integral_const_mul] at h1
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  have h2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k g z θ)
      ≤ ∫ z in Work.Spaces.Iz, C * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f z θ) :=
    MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
      (g := fun z => C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ))
      (Filter.Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
      (hmf.2.const_mul C)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  rwa [MeasureTheory.integral_const_mul] at h2

private theorem HkMem_of_integrand_le (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ} (C : ℝ)
    (hcontg : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmf : Work.Spaces.HkMem α k f)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k g z θ ≤ C * Work.Spaces.HkIntegrand α k f z θ) :
    Work.Spaces.HkMem α k g :=
  Work.FTS.LocData.HkMem_of_majorant α k hcontg
    (fun z hz => (hmf.1 z hz).const_mul C)
    (by
      have h := hmf.2.const_mul C
      have hkey : (fun z => ∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α k f z θ)
          = fun z => C * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
        funext z
        rw [MeasureTheory.integral_const_mul]
      rw [hkey]
      exact h)
    hpt

/-
**Bounded angular profiles do not increase the weighted `ℋ^k`-integrand.**

Namespace `Work.FTS.EllipticEst.Blocks` (fully qualified name
`Work.FTS.EllipticEst.Blocks.HkMul_ang_le`).

CONTENT.  For `f` `C^∞` on the open quadrant `Q0 = (0,∞) × (0,π/2)`
(`Work.FTS.EllipticEst.SmoothOpen f`) and every `α ∈ (0,1]`, the two profiles
`a θ = sin 2θ` and `a θ = sin²θ` satisfy, pointwise on the whole closed quadrant,

  `HkIntegrand α k (a · f) ≤ C_k · HkIntegrand α k f`,

and consequently (with `HkMem` of `f` as the honesty hypothesis)
`HkMem α k (a · f)` and `HkSq α k (a·f) ≤ C_k · HkSq α k f`.

The constant depends only on `k`, never on `α ∈ (0,1]`.

ROUTE (verified by a reviewer).  `D_z` and `D_θ` commute with the `θ`-only factor `a`, so the
pure-`D_z` summands satisfy `D_z^i(a·f) = a·(D_z^if)` exactly and `|a| ≤ 1` gives those terms.
For the mixed summands, the iterated Leibniz rule for the derivation `L = D_θ = sin(2θ)∂_θ`
(`Work.FTS.EllipticEst.Lop_iter_mul`, sorry-free: `L^i(f·g) = Σ_{m≤i} C(i,m)(L^mf)(L^{i-m}g)`)
expands `D_θ^i(D_z^j(a f)) = Σ_{m ≤ i} C(i,m) (D_θ^m a)(D_θ^{i-m}D_z^j f)`.  Every term with
`m < i` is a summand of `HkIntegrand α k f` (at the mixed index `i-m ≥ 1`, same `j`) after
using `sin(2θ)² ≤ 1` and the boundedness of `D_θ^m a`; the term `m = i` is the `D_z`-family
summand `(D_z^j f)²·w²·sin(2θ)^{-γ}` times `(D_θ^i a)²`, and one needs
`(D_θ^i a)² · sin(2θ)^{-γ} ≤ C_i`, i.e. `sin(2θ)^{2-γ} ≤ C_i`.  For `a = sin 2θ` this is the
(sorry-free) weighted angular iterate bound `Work.FTS.EllipticEst.sinIter_weight_bound`
(`D_θ^i(sin 2θ) = sinIter i`); for `a = sin²θ` it is
`Work.FTS.EllipticEst.Blocks.LopIter_sin_sq_le` (sorry-free, `(D_θ^m(sin²θ))² ≤ K·sin(2θ)²`
for `m ≥ 1`).  Again `2 - γ ≥ -η` because `γ = 1 + α/10 ≤ 11/10` and `η = 99/100`, so the
weights with exponent `-γ` are dominated by those with `-η`; the exponent `2-γ` is positive, so
`sin(2θ)^{2-γ} ≤ 1 ≤ sin(2θ)^{-η}` too.

At the two boundary lines `sin(2θ) = 0` and at `z = 0` both sides of the pointwise inequality
vanish (`HkIntegrand_eq_zero_of_sin` / `w 0 = 0`; the same computation as the private lemmas of
`Submission/Work/FTS/EllipticEst/HkNorm_add_le.lean`), so the pointwise inequality extends to
the closed quadrant `Iz ×ˢ Iθ`.

The `HkMem`/`HkSq` consequences follow from the pointwise inequality on the closed quadrant by
`MeasureTheory.integral_mono_of_nonneg` slice by slice (`HkMem f` makes the dominating slice
integrable), then again in `z`; this is the pattern of
`Work.FTS.EllipticEst.HkSq_add_le_of_pointwise`
(`Submission/Work/FTS/EllipticEst/HkNorm_add_le.lean`, sorry-free).

NOTE: this strictly extends the (still `sorry`) sibling
`Submission/Work/FTS/EllipticEst/Blocks/HkIntegrand_mul_angular_le.lean`, which you may read and
port but must not import (it is not sorry-free).  The hypotheses `0 < α`, `α ≤ 1` are exactly
what the `γ`-weight comparison needs.
-/
theorem HkMul_ang_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f →
      (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => Real.sin (2 * θ) * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ) ∧
      (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => Real.sin θ ^ 2 * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ) ∧
      (Work.Spaces.HkMem α k f →
        Work.Spaces.HkMem α k (fun z θ => Real.sin (2 * θ) * f z θ) ∧
        Work.Spaces.HkSq α k (fun z θ => Real.sin (2 * θ) * f z θ)
          ≤ C * Work.Spaces.HkSq α k f ∧
        Work.Spaces.HkMem α k (fun z θ => Real.sin θ ^ 2 * f z θ) ∧
        Work.Spaces.HkSq α k (fun z θ => Real.sin θ ^ 2 * f z θ)
          ≤ C * Work.Spaces.HkSq α k f) := by
  obtain ⟨C, hCpos, hpt⟩ := HkIntegrand_mul_ang_le_pt k
  refine ⟨C, hCpos, ?_⟩
  intro α f hα hα1 hf
  obtain ⟨hpt2, hpt3⟩ := hpt α f hα hα1 hf
  refine ⟨hpt2, hpt3, ?_⟩
  intro hmem
  have hSO2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.sin (2 * θ) * f z θ) :=
    smoothOpen_angMul contDiffAt_sin_two hf
  have hSO3 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.sin θ ^ 2 * f z θ) :=
    smoothOpen_angMul contDiffAt_sin_sq hf
  have hc2 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α k (fun z θ => Real.sin (2 * θ) * f z θ) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand hSO2 α k
  have hc3 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α k (fun z θ => Real.sin θ ^ 2 * f z θ) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand hSO3 α k
  exact ⟨HkMem_of_integrand_le α k C hc2 hmem hpt2,
    HkSq_le_of_integrand_le α k C hmem hpt2,
    HkMem_of_integrand_le α k C hc3 hmem hpt3,
    HkSq_le_of_integrand_le α k C hmem hpt3⟩

end Work.Blocks

namespace Work.FTS.EllipticEst.Blocks

/-- Compatibility alias of `Work.Blocks.HkMul_ang_le` under the fully qualified name quoted by
the consumers of the elliptic-estimates chapter (the assembly of
`Work.FTS.EllipticEst.Rop_EllResid_le` refers to this statement as
`Work.FTS.EllipticEst.Blocks.HkMul_ang_le`). -/
theorem HkMul_ang_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f →
      (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => Real.sin (2 * θ) * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ) ∧
      (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => Real.sin θ ^ 2 * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k f z θ) ∧
      (Work.Spaces.HkMem α k f →
        Work.Spaces.HkMem α k (fun z θ => Real.sin (2 * θ) * f z θ) ∧
        Work.Spaces.HkSq α k (fun z θ => Real.sin (2 * θ) * f z θ)
          ≤ C * Work.Spaces.HkSq α k f ∧
        Work.Spaces.HkMem α k (fun z θ => Real.sin θ ^ 2 * f z θ) ∧
        Work.Spaces.HkSq α k (fun z θ => Real.sin θ ^ 2 * f z θ)
          ≤ C * Work.Spaces.HkSq α k f) :=
  Work.Blocks.HkMul_ang_le k

end Work.FTS.EllipticEst.Blocks
