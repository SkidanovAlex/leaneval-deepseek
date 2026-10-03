/-
# The almost-orthogonality of the minor-arc parts of two blocks (`PairingFarBd`)

Krause--Mirek--Tao, §5.2.  For two blocks `I_i`, `I_j` at distance at least
`2 coeffSum P + 5 + 2^{deg P + 1}` the pairing of the minor-arc parts
`u_i = (1 - Π)Ã_N^{**}(f_i, h|)` decays like `(A^2 + K ⟨l⟩^2 2^{-16 d l}) ⟨i-j⟩^{-8}`, where `A` is
the constant of the local `ℓ²` bound of `struct-iii-second` and `K` is independent of `l`, `N`.

The proof splits the `x`-sum into the blocks `I_m` (`tsum_eq_sum_blocks`), applies Cauchy--Schwarz
to each block, and bounds each factor `‖u_i·1_{I_m}‖_{ℓ²}` by

* the local bound `A ‖f_i‖_{ℓ²}` when `|m - i| ≤ coeffSum P + 2 + 2^{deg P}`,
* the blockwise off-decay `OffBlockBd` otherwise (where `|m-i| ≥ coeffSum P + 3 + 2^{deg P}`).

For `|i - j| ≥ 2(coeffSum P + 2 + 2^{deg P}) + 1` the two near windows are disjoint, so the
product of the two factors, summed over `m`, is dominated by
`(A^2 + K₂^2 ((2W+1)^2 2^16 + C₈))⟨i-j⟩^{-8}` with `K₂ = Koff ⟨l⟩ 2^{-8dl}` (the kernel estimate
`kernel_sum_le` at `M = 8` and the window estimate `windowSum_bound`).
-/
import Mathlib
import Submission.Work.KMTAreas.A4Z.SivMainCore

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.Analysis.InverseTheory
open Work.Analysis.EndVar

namespace Work.KMTAreas.A4Z

/-! ## Elementary `ℓ²` facts for the blockwise estimates -/

theorem l2norm_le_of_eLpNorm_le {g : ℤ → ℂ} (hg : MemLp g 2 Measure.count) {X : ℝ} (hX : 0 ≤ X)
    (h : eLpNorm g 2 Measure.count ≤ ENNReal.ofReal X) : l2norm g ≤ X := by
  have h1 : eLpNorm g 2 Measure.count = ENNReal.ofReal (l2norm g) :=
    eLpNorm_two_eq_ofReal_l2norm (Work.KMTAreas.A4.memLp_two_count_summable_norm_sq hg)
  rw [h1] at h
  exact (ENNReal.ofReal_le_ofReal_iff hX).mp h

theorem l2norm_le_mul_of_eLpNorm_le {g ψ : ℤ → ℂ} (hg : MemLp g 2 Measure.count)
    (hψ : MemLp ψ 2 Measure.count) {c : ℝ} (hc : 0 ≤ c)
    (h : eLpNorm g 2 Measure.count ≤ ENNReal.ofReal c * eLpNorm ψ 2 Measure.count) :
    l2norm g ≤ c * l2norm ψ := by
  have h1 : eLpNorm g 2 Measure.count = ENNReal.ofReal (l2norm g) :=
    eLpNorm_two_eq_ofReal_l2norm (Work.KMTAreas.A4.memLp_two_count_summable_norm_sq hg)
  have h2 : eLpNorm ψ 2 Measure.count = ENNReal.ofReal (l2norm ψ) :=
    eLpNorm_two_eq_ofReal_l2norm (Work.KMTAreas.A4.memLp_two_count_summable_norm_sq hψ)
  rw [h1, h2, ← ENNReal.ofReal_mul hc] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc (l2norm_nonneg _))).mp h

theorem summable_norm_sq_trunc (s : Finset ℤ) (g : ℤ → ℂ) :
    Summable (fun x : ℤ => ‖(if x ∈ s then g x else 0 : ℂ)‖ ^ 2) :=
  summable_of_ne_finset_zero (s := s) fun x hx => by rw [if_neg hx]; norm_num

theorem l2norm_trunc_le (s : Finset ℤ) (g : ℤ → ℂ) (hg : Summable (fun x : ℤ => ‖g x‖ ^ 2)) :
    l2norm (fun x : ℤ => if x ∈ s then g x else 0) ≤ l2norm g :=
  l2norm_mono (fun x => by
    by_cases hx : x ∈ s
    · rw [if_pos hx]
    · rw [if_neg hx]; simp) (summable_norm_sq_trunc s g) hg

theorem norm_finset_sum_mul_le (s : Finset ℤ) (u v : ℤ → ℂ) :
    ‖∑ x ∈ s, u x * star (v x)‖
      ≤ Real.sqrt (∑ x ∈ s, ‖u x‖ ^ 2) * Real.sqrt (∑ x ∈ s, ‖v x‖ ^ 2) := by
  have h1 : ‖∑ x ∈ s, u x * star (v x)‖ ≤ ∑ x ∈ s, ‖u x‖ * ‖v x‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul, norm_star]
  have h2 : (∑ x ∈ s, ‖u x‖ * ‖v x‖) ^ 2 ≤ (∑ x ∈ s, ‖u x‖ ^ 2) * (∑ x ∈ s, ‖v x‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq s (fun x => ‖u x‖) (fun x => ‖v x‖)
  have h3 : (0 : ℝ) ≤ ∑ x ∈ s, ‖u x‖ * ‖v x‖ :=
    Finset.sum_nonneg fun x _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  calc ‖∑ x ∈ s, u x * star (v x)‖ ≤ ∑ x ∈ s, ‖u x‖ * ‖v x‖ := h1
    _ = Real.sqrt ((∑ x ∈ s, ‖u x‖ * ‖v x‖) ^ 2) := (Real.sqrt_sq h3).symm
    _ ≤ Real.sqrt ((∑ x ∈ s, ‖u x‖ ^ 2) * (∑ x ∈ s, ‖v x‖ ^ 2)) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt (∑ x ∈ s, ‖u x‖ ^ 2) * Real.sqrt (∑ x ∈ s, ‖v x‖ ^ 2) :=
        Real.sqrt_mul (Finset.sum_nonneg fun x _ => sq_nonneg _) _

theorem sqrt_sum_sq_eq_l2norm_trunc (s : Finset ℤ) (g : ℤ → ℂ) :
    Real.sqrt (∑ x ∈ s, ‖g x‖ ^ 2) = l2norm (fun x : ℤ => if x ∈ s then g x else 0) := by
  rw [l2norm, l2sq, tsum_eq_sum (s := s) (fun x hx => by rw [if_neg hx]; norm_num)]
  refine congrArg Real.sqrt (Finset.sum_congr rfl fun x hx => ?_)
  rw [if_pos hx]

/-- Cauchy--Schwarz on a single block. -/
theorem block_pairing_le (s : Finset ℤ) (u v : ℤ → ℂ) :
    ‖∑ x ∈ s, u x * star (v x)‖
      ≤ l2norm (fun x : ℤ => if x ∈ s then u x else 0)
        * l2norm (fun x : ℤ => if x ∈ s then v x else 0) := by
  rw [← sqrt_sum_sq_eq_l2norm_trunc s u, ← sqrt_sum_sq_eq_l2norm_trunc s v]
  exact norm_finset_sum_mul_le s u v

/-! ## The blockwise bound on the factor `u_i · 1_{I_m}` -/

/-- **The blockwise bound for the minor-arc part.**  On the block `I_m` the factor `u_i` is bounded
by the local bound `A ‖f_i‖` if `m` is in the near window `|m - i| ≤ coeffSum P + 2 + 2^{deg P}`,
and by the off-decay `Koff ⟨l⟩ 2^{-8dl} ⟨m-i⟩^{-8} ‖f_i‖` otherwise. -/
theorem block_factor_le (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) (ρ : ℝ)
    {Cρ₀ Koff : ℝ} (hKoff : 0 ≤ Koff) (hBd : OffBlockBd P ρ Cρ₀ Koff)
    {N l : ℕ} (hN : 1 ≤ N) {Cρ : ℝ} (hCρ : Cρ₀ ≤ Cρ)
    (hgood : GoodMajorArcs ρ Cρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)))
    {f h : ℤ → ℂ} (hf : MemLp f 2 Measure.count) (hh : ∀ x : ℤ, ‖h x‖ ≤ 1)
    (i m : ℤ) {A : ℝ} (hA : 0 ≤ A)
    (hli : eLpNorm (minorPart P ρ N l f h i) 2 Measure.count
        ≤ ENNReal.ofReal (A * l2norm (zPiece (blockLen P N) f i))) :
    l2norm (fun x : ℤ => if x ∈ Finset.Ico (m * blockLen P N) ((m + 1) * blockLen P N)
        then minorPart P ρ N l f h i x else 0)
      ≤ (A * (if |(((m - i : ℤ) : ℝ))| ≤ ((coeffSum P + 2 + 2 ^ P.natDegree : ℤ) : ℝ)
            then 1 else 0)
          + Koff * (max ((l : ℝ)) 1) * (2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ)))
            * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
        * l2norm (zPiece (blockLen P N) f i) := by
  set L : ℤ := blockLen P N with hLdef
  set ai : ℝ := l2norm (zPiece L f i) with haidef
  set Wd : ℤ := coeffSum P + 2 + 2 ^ P.natDegree with hWddef
  set K2 : ℝ := Koff * (max ((l : ℝ)) 1)
    * (2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ))) with hK2def
  have hLpos : 0 < L := blockLen_pos P hN
  have hai0 : 0 ≤ ai := l2norm_nonneg _
  have hK20 : 0 ≤ K2 := by
    rw [hK2def]
    exact mul_nonneg (mul_nonneg hKoff (le_trans zero_le_one (le_max_right _ _)))
      (Real.rpow_nonneg (by norm_num) _)
  have hset : Finset.Ico (m * blockLen P N) ((m + 1) * blockLen P N)
      = Finset.Ico (m * L) ((m + 1) * L) := by rw [hLdef]
  by_cases hcase : coeffSum P + 3 + 2 ^ P.natDegree ≤ |m - i|
  · -- far from the window: the off-decay applies
    have hsupp_d : ∀ x : ℤ, x ∉ suppWin P N i → dPiece P N f h i x = 0 := by
      intro x hx
      by_contra hne
      exact hx (zPiece_dPiece_support P hP hN f h i x hne)
    have hmain := hBd N l Cρ hN hCρ hgood i m (dPiece P N f h i)
      (memLp_dPiece P N hN hf hh i) hsupp_d hcase
    -- the truncation of `u_i` is the negative of the truncation of `Π dPiece_i`
    have htrunc : (fun x : ℤ => if x ∈ Finset.Ico (m * blockLen P N)
          ((m + 1) * blockLen P N) then minorPart P ρ N l f h i x else 0)
        = - (fun x : ℤ => if x ∈ Finset.Ico (m * blockLen P N)
            ((m + 1) * blockLen P N) then
              Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N))
                (dPiece P N f h i) x else 0) := by
      funext x
      by_cases hx : x ∈ Finset.Ico (m * blockLen P N) ((m + 1) * blockLen P N)
      · have hd0 : dPiece P N f h i x = 0 := by
          by_contra hne
          have hmem := ediv_mem_suppWin hN (zPiece_dPiece_support P hP hN f h i x hne)
          have hm : m = x / blockLen P N :=
            ediv_eq_of_mem_Ico hLpos (Finset.mem_Ico.mp hx).1 (Finset.mem_Ico.mp hx).2
          have hfar_m : coeffSum P + 3 + 2 ^ P.natDegree ≤ |x / blockLen P N - i| := by
            rw [← hm]; exact hcase
          have h2d : (0 : ℤ) < 2 ^ P.natDegree := by positivity
          omega
        rw [if_pos hx, Pi.neg_apply, if_pos hx, minorPart, hd0, zero_sub, projTwo_apply]
      · rw [if_neg hx, Pi.neg_apply, if_neg hx, neg_zero]
    -- `‖dPiece_i‖ ≤ ai`
    have hd_le : eLpNorm (dPiece P N f h i) 2 Measure.count ≤ ENNReal.ofReal ai := by
      have h1 := eLpNorm_ahalfTransposeTwo_le N P hN (f := zPiece L f i)
        (h := (hWin P N i).indicator h) (fun x => by
          by_cases hx : x ∈ hWin P N i
          · rw [Set.indicator_of_mem hx]; exact hh x
          · rw [Set.indicator_of_notMem hx]; simp)
      rw [eLpNorm_two_eq_ofReal_l2norm (summable_norm_sq_zPiece hLpos f i)] at h1
      exact h1
    have hdp_mem : MemLp (dPiece P N f h i) 2 Measure.count := memLp_dPiece P N hN hf hh i
    have hdpi : l2norm (dPiece P N f h i) ≤ ai :=
      l2norm_le_of_eLpNorm_le hdp_mem hai0 hd_le
    have htr_mem : MemLp (fun x : ℤ => if x ∈ Finset.Ico (m * blockLen P N)
          ((m + 1) * blockLen P N) then
            Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N))
              (dPiece P N f h i) x else 0) 2 Measure.count := by
      refine MeasureTheory.memLp_iff.mpr ?_
      rw [lt_top_iff_ne_top]
      exact ne_top_of_le_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hdp_mem.eLpNorm_lt_top.ne) hmain
    have hK2nn : 0 ≤ Koff * (max ((l : ℝ)) 1)
        * (2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ))) :=
      mul_nonneg (mul_nonneg hKoff (le_trans zero_le_one (le_max_right _ _)))
        (Real.rpow_nonneg (by norm_num) _)
    have hbr : 0 ≤ Koff * (max ((l : ℝ)) 1)
        * (2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ)))
        * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)) :=
      mul_nonneg hK2nn (Real.rpow_nonneg (by positivity) _)
    have hstep1 : l2norm (fun x : ℤ => if x ∈ Finset.Ico (m * blockLen P N)
          ((m + 1) * blockLen P N) then
            Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N))
              (dPiece P N f h i) x else 0)
        ≤ (Koff * (max ((l : ℝ)) 1) * (2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ)))
            * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))) * l2norm (dPiece P N f h i) :=
      l2norm_le_mul_of_eLpNorm_le htr_mem hdp_mem hbr hmain
    have hstep2 : l2norm (fun x : ℤ => if x ∈ Finset.Ico (m * blockLen P N)
          ((m + 1) * blockLen P N) then
            Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N))
              (dPiece P N f h i) x else 0) ≤ K2 * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)) * ai := by
      refine hstep1.trans ?_
      rw [hK2def]
      exact mul_le_mul_of_nonneg_left hdpi hbr
    rw [htrunc]
    have hneg : l2norm (- (fun x : ℤ => if x ∈ Finset.Ico (m * blockLen P N)
          ((m + 1) * blockLen P N) then
            Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N))
              (dPiece P N f h i) x else 0))
        = l2norm (fun x : ℤ => if x ∈ Finset.Ico (m * blockLen P N)
            ((m + 1) * blockLen P N) then
              Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N))
                (dPiece P N f h i) x else 0) := by
      simp only [l2norm, l2sq]
      exact congrArg Real.sqrt (tsum_congr fun x => by rw [Pi.neg_apply, norm_neg])
    rw [hneg]
    refine hstep2.trans ?_
    have hif : ¬ |(((m - i : ℤ) : ℝ))| ≤ ((coeffSum P + 2 + 2 ^ P.natDegree : ℤ) : ℝ) := by
      rw [← Int.cast_abs]
      intro hcon
      have hle : |m - i| ≤ coeffSum P + 2 + 2 ^ P.natDegree := by exact_mod_cast hcon
      have h2d : (0 : ℤ) < 2 ^ P.natDegree := by positivity
      omega
    rw [if_neg hif, mul_zero, zero_add]
  · -- inside the near window: the local bound suffices
    push_neg at hcase
    have hnear : |m - i| ≤ coeffSum P + 2 + 2 ^ P.natDegree := by omega
    have hif : |(((m - i : ℤ) : ℝ))| ≤ ((coeffSum P + 2 + 2 ^ P.natDegree : ℤ) : ℝ) := by
      rw [← Int.cast_abs]
      exact_mod_cast hnear
    have h1 : l2norm (fun x : ℤ => if x ∈ Finset.Ico (m * blockLen P N)
          ((m + 1) * blockLen P N) then minorPart P ρ N l f h i x else 0) ≤ A * ai := by
      refine (l2norm_trunc_le _ _ (summable_norm_sq_minorPart P ρ N l hN hf hh i)).trans ?_
      exact l2norm_le_of_eLpNorm_le (memLp_minorPart P ρ N l hN hf hh i)
        (mul_nonneg hA hai0) hli
    rw [if_pos hif, mul_one]
    refine h1.trans ?_
    have hnn : 0 ≤ K2 * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)) * ai :=
      mul_nonneg (mul_nonneg hK20 (Real.rpow_nonneg (by positivity) _)) hai0
    nlinarith [hnn]


/-! ## Summability of the shifted power kernels -/

theorem summable_pow8_sub (j : ℤ) :
    Summable (fun m : ℤ => (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))) := by
  have h := (Equiv.summable_iff (f := fun y : ℤ => (1 + |(((y : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
    (Equiv.addRight (-j))).mpr summable_pow8
  refine h.congr fun m => ?_
  simp only [Function.comp, Equiv.coe_addRight]
  rw [show (m + -j : ℤ) = m - j by ring]

theorem summable_pow16_sub (j : ℤ) :
    Summable (fun m : ℤ => (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(16 : ℝ))) := by
  refine Summable.of_nonneg_of_le (fun m => Real.rpow_nonneg (by positivity) _) (fun m => ?_)
    (summable_pow8_sub j)
  exact Real.rpow_le_rpow_of_exponent_le
    (by linarith [abs_nonneg (((m - j : ℤ) : ℝ))]) (by norm_num : (-(16 : ℝ)) ≤ -(8 : ℝ))

theorem summable_pow8_mul_pow8 (i j : ℤ) :
    Summable (fun m : ℤ => (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))
      * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))) := by
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (by positivity) _)) (fun m => ?_)
    (((summable_pow16_sub i).add (summable_pow16_sub j)).mul_right (1/2))
  have h1 : (0 : ℝ) ≤ (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have h2 : (0 : ℝ) ≤ (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have h3 : ((1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))) ^ 2
      = (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(16 : ℝ)) := by
    rw [← Real.rpow_natCast ((1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))) 2,
      ← Real.rpow_mul (by positivity)]
    norm_num
  have h4 : ((1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))) ^ 2
      = (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(16 : ℝ)) := by
    rw [← Real.rpow_natCast ((1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))) 2,
      ← Real.rpow_mul (by positivity)]
    norm_num
  nlinarith [sq_nonneg ((1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))
    - (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))), h3, h4]

/-! ## The window estimate -/

theorem windowBound_self {W : ℤ} (hW : 0 ≤ W) {i j : ℤ} (hfar : 2 * W + 1 ≤ |i - j|) :
    (∑' m : ℤ, (if |(((m - i : ℤ) : ℝ))| ≤ (W : ℝ) then (1 : ℝ) else 0)
        * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
      ≤ (2 * (W : ℝ) + 1) * 2 ^ 8 * (1 + |(((i - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)) := by
  have hW0 : (0 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
  have hfarR : 2 * (W : ℝ) + 1 ≤ |(((i - j : ℤ) : ℝ))| := by
    rw [← Int.cast_abs]
    exact_mod_cast hfar
  have hDW : (W : ℝ) ≤ |(((i - j : ℤ) : ℝ))| := by linarith
  have hsupp : ∀ m : ℤ, m ∉ Finset.Icc (i - W) (i + W) →
      (if |(((m - i : ℤ) : ℝ))| ≤ (W : ℝ) then (1 : ℝ) else 0) = 0 := by
    intro m hm
    rw [if_neg]
    intro hcon
    refine hm (Finset.mem_Icc.mpr ?_)
    obtain ⟨hh1, hh2⟩ := abs_le.mp hcon
    push_cast at hh1 hh2
    constructor
    · have h2 : ((i - W : ℤ) : ℝ) ≤ ((m : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast h2
    · have h2 : ((m : ℤ) : ℝ) ≤ ((i + W : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast h2
  rw [tsum_eq_sum (s := Finset.Icc (i - W) (i + W)) (fun m hm => by rw [hsupp m hm, zero_mul])]
  have hterm : ∀ m ∈ Finset.Icc (i - W) (i + W),
      (if |(((m - i : ℤ) : ℝ))| ≤ (W : ℝ) then (1 : ℝ) else 0)
        * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))
      ≤ (1 + (|(((i - j : ℤ) : ℝ))| - (W : ℝ))) ^ (-(8 : ℝ)) := by
    intro m hm
    have hmw : |(((m - i : ℤ) : ℝ))| ≤ (W : ℝ) := by
      rw [Finset.mem_Icc] at hm
      rw [abs_le]
      have h1 : ((i - W : ℤ) : ℝ) ≤ ((m : ℤ) : ℝ) := by exact_mod_cast hm.1
      have h2 : ((m : ℤ) : ℝ) ≤ ((i + W : ℤ) : ℝ) := by exact_mod_cast hm.2
      constructor <;> (push_cast at h1 h2 ⊢; linarith)
    rw [if_pos hmw, one_mul]
    refine Real.rpow_le_rpow_of_nonpos (by linarith [abs_nonneg (((m - j : ℤ) : ℝ))]) ?_ (by norm_num)
    have htri : |(((i - j : ℤ) : ℝ))| ≤ |(((i - m : ℤ) : ℝ))| + |(((m - j : ℤ) : ℝ))| := by
      have hcast : (((i - j : ℤ) : ℝ)) = ((i - m : ℤ) : ℝ) + ((m - j : ℤ) : ℝ) := by push_cast; ring
      rw [hcast]
      exact abs_add_le _ _
    have him : |(((i - m : ℤ) : ℝ))| ≤ (W : ℝ) := by
      rw [show (((i - m : ℤ) : ℝ)) = -(((m - i : ℤ) : ℝ)) by push_cast; ring, abs_neg]
      exact hmw
    linarith
  have hcard : (((Finset.Icc (i - W) (i + W)).card : ℕ) : ℝ) ≤ 2 * (W : ℝ) + 1 := by
    rw [Int.card_Icc]
    have h2D : (0 : ℤ) ≤ i + W + 1 - (i - W) := by linarith
    have hnat : ((((i + W + 1 - (i - W)).toNat) : ℤ)) ≤ 2 * W + 1 := by
      rw [Int.toNat_of_nonneg h2D]
      linarith
    exact_mod_cast hnat
  have hfinal : (1 + (|(((i - j : ℤ) : ℝ))| - (W : ℝ))) ^ (-(8 : ℝ))
      ≤ 2 ^ 8 * (1 + |(((i - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)) := by
    have h2 : (1 + |(((i - j : ℤ) : ℝ))|) ≤ 2 * (1 + (|(((i - j : ℤ) : ℝ))| - (W : ℝ))) := by
      linarith
    calc (1 + (|(((i - j : ℤ) : ℝ))| - (W : ℝ))) ^ (-(8 : ℝ))
        ≤ ((1 + |(((i - j : ℤ) : ℝ))|) / 2) ^ (-(8 : ℝ)) := by
          refine Real.rpow_le_rpow_of_nonpos
            (by linarith [abs_nonneg (((i - j : ℤ) : ℝ)), hW0]) ?_ (by norm_num)
          linarith
      _ = (1 + |(((i - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)) * 2 ^ 8 := by
          have h2p : (2 : ℝ) ^ (-(8 : ℝ)) = ((2 : ℝ) ^ 8)⁻¹ := by
            rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
            norm_num
          rw [Real.div_rpow (by linarith [abs_nonneg (((i - j : ℤ) : ℝ))])
              (by norm_num : (0 : ℝ) ≤ 2), h2p, div_eq_mul_inv, inv_inv]
      _ = 2 ^ 8 * (1 + |(((i - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)) := by ring
  calc (∑ m ∈ Finset.Icc (i - W) (i + W),
        (if |(((m - i : ℤ) : ℝ))| ≤ (W : ℝ) then (1 : ℝ) else 0)
          * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
      ≤ ∑ m ∈ Finset.Icc (i - W) (i + W), (1 + (|(((i - j : ℤ) : ℝ))| - (W : ℝ))) ^ (-(8 : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (((Finset.Icc (i - W) (i + W)).card : ℕ) : ℝ)
          * (1 + (|(((i - j : ℤ) : ℝ))| - (W : ℝ))) ^ (-(8 : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (W : ℝ) + 1) * (1 + (|(((i - j : ℤ) : ℝ))| - (W : ℝ))) ^ (-(8 : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (by linarith [abs_nonneg (((i - j : ℤ) : ℝ)), hW0]) _)
    _ ≤ (2 * (W : ℝ) + 1) * (2 ^ 8 * (1 + |(((i - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))) :=
        mul_le_mul_of_nonneg_left hfinal (by linarith)
    _ = (2 * (W : ℝ) + 1) * 2 ^ 8 * (1 + |(((i - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)) := by ring


/-! ## Window membership helpers -/

theorem mem_Icc_of_abs_le {W i m : ℤ} (h : |(((m - i : ℤ) : ℝ))| ≤ (W : ℝ)) :
    m ∈ Finset.Icc (i - W) (i + W) := by
  rw [Finset.mem_Icc]
  obtain ⟨h1, h2⟩ := abs_le.mp h
  push_cast at h1 h2
  constructor
  · have h3 : ((i - W : ℤ) : ℝ) ≤ ((m : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast h3
  · have h3 : ((m : ℤ) : ℝ) ≤ ((i + W : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast h3

theorem abs_le_of_mem_Icc {W i m : ℤ} (h : m ∈ Finset.Icc (i - W) (i + W)) :
    |(((m - i : ℤ) : ℝ))| ≤ (W : ℝ) := by
  rw [Finset.mem_Icc] at h
  have h1 : ((i - W : ℤ) : ℝ) ≤ ((m : ℤ) : ℝ) := by exact_mod_cast h.1
  have h2 : ((m : ℤ) : ℝ) ≤ ((i + W : ℤ) : ℝ) := by exact_mod_cast h.2
  rw [abs_le]
  constructor <;> (push_cast at h1 h2 ⊢; linarith)

/-! ## The almost-orthogonality -/

theorem pairingFarBdSelf (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) (ρ : ℝ)
    {Cρ₀ Koff : ℝ} (hKoff : 0 ≤ Koff) (hBd : OffBlockBd P ρ Cρ₀ Koff) :
    ∃ K : ℝ, 0 < K ∧ PairingFarBd P ρ Cρ₀ K := by
  obtain ⟨C₈, hC₈pos, hC₈le⟩ := kernel_sum_le 8 (by norm_num)
  set Wz : ℤ := coeffSum P + 2 + 2 ^ P.natDegree with hWzdef
  have hWz0 : 0 ≤ Wz := by
    rw [hWzdef]
    have h1 : (0 : ℤ) ≤ coeffSum P := coeffSum_nonneg P
    have h2 : (0 : ℤ) ≤ 2 ^ P.natDegree := by positivity
    linarith
  have hWd0 : (0 : ℝ) ≤ (Wz : ℝ) := by exact_mod_cast hWz0
  refine ⟨Koff ^ 2 * ((2 * (Wz : ℝ) + 1) ^ 2 * 2 ^ 16 + C₈) + 1, by positivity, ?_⟩
  · intro N l Cρ hN hCρ hgood f h i j A
    refine fun (hMem : MemLp f 2 Measure.count) (hbdd : ∀ x : ℤ, ‖h x‖ ≤ 1)
      (hA0 : 0 ≤ A) (hthr : 2 * coeffSum P + 5 + 2 ^ (P.natDegree + 1) ≤ |i - j|)
      (hli : eLpNorm (minorPart P ρ N l f h i) 2 Measure.count
        ≤ ENNReal.ofReal (A * l2norm (zPiece (blockLen P N) f i)))
      (hlj : eLpNorm (minorPart P ρ N l f h j) 2 Measure.count
        ≤ ENNReal.ofReal (A * l2norm (zPiece (blockLen P N) f j))) => ?_
    have hfar' : 2 * Wz + 1 ≤ |i - j| := by
      rw [hWzdef]
      rw [show (2:ℤ) ^ (P.natDegree + 1) = 2 * 2 ^ P.natDegree by rw [pow_succ]; ring] at hthr
      linarith
    set L : ℤ := blockLen P N with hLdef
    set ai : ℝ := l2norm (zPiece L f i) with haidef
    set aj : ℝ := l2norm (zPiece L f j) with hajdef
    set Pii : ℤ → ℝ := fun m => if |(((m - i : ℤ) : ℝ))| ≤ (Wz : ℝ) then 1 else 0 with hPiidef
    set Pij : ℤ → ℝ := fun m => if |(((m - j : ℤ) : ℝ))| ≤ (Wz : ℝ) then 1 else 0 with hPijdef
    set K2 : ℝ := Koff * (max ((l : ℝ)) 1)
      * (2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ))) with hK2def
    set Dg : ℝ := (1 + |(((i - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)) with hDgdef
    have hLpos : 0 < L := blockLen_pos P hN
    have hai0 : 0 ≤ ai := l2norm_nonneg _
    have haj0 : 0 ≤ aj := l2norm_nonneg _
    have hDg0 : 0 ≤ Dg := Real.rpow_nonneg (by linarith [abs_nonneg (((i - j : ℤ) : ℝ))]) _
    have hK20 : 0 ≤ K2 := by
      rw [hK2def]
      exact mul_nonneg (mul_nonneg hKoff (le_trans zero_le_one (le_max_right _ _)))
        (Real.rpow_nonneg (by norm_num) _)
    -- 1. the factor bounds on each block
    have hfac : ∀ m : ℤ, l2norm (fun x : ℤ => if x ∈ Finset.Ico (m * L) ((m + 1) * L)
        then minorPart P ρ N l f h i x else 0)
        ≤ (A * Pii m + K2 * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))) * ai := by
      intro m
      have h := block_factor_le P hP ρ hKoff hBd hN hCρ hgood hMem hbdd i m hA0 hli
      simp only [hPiidef, hK2def, haidef, hLdef]
      exact h
    have hfacj : ∀ m : ℤ, l2norm (fun x : ℤ => if x ∈ Finset.Ico (m * L) ((m + 1) * L)
        then minorPart P ρ N l f h j x else 0)
        ≤ (A * Pij m + K2 * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))) * aj := by
      intro m
      have h := block_factor_le P hP ρ hKoff hBd hN hCρ hgood hMem hbdd j m hA0 hlj
      simp only [hPijdef, hK2def, hajdef, hLdef]
      exact h
    have hPii0 : ∀ m : ℤ, 0 ≤ (A * Pii m
        + K2 * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))) * ai := by
      intro m
      refine mul_nonneg (add_nonneg (mul_nonneg hA0 ?_)
        (mul_nonneg hK20 (Real.rpow_nonneg (by positivity) _))) hai0
      simp only [hPiidef]
      split_ifs <;> norm_num
    -- 2. the per-block bound
    have hterm : ∀ m : ℤ,
        ‖∑ x ∈ Finset.Ico (m * L) ((m + 1) * L),
            minorPart P ρ N l f h i x * star (minorPart P ρ N l f h j x)‖
          ≤ (A * Pii m + K2 * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
            * (A * Pij m + K2 * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))) * (ai * aj) := by
      intro m
      have h1 := block_pairing_le (Finset.Ico (m * L) ((m + 1) * L))
        (minorPart P ρ N l f h i) (minorPart P ρ N l f h j)
      calc ‖∑ x ∈ Finset.Ico (m * L) ((m + 1) * L),
              minorPart P ρ N l f h i x * star (minorPart P ρ N l f h j x)‖
          ≤ l2norm (fun x : ℤ => if x ∈ Finset.Ico (m * L) ((m + 1) * L)
              then minorPart P ρ N l f h i x else 0)
            * l2norm (fun x : ℤ => if x ∈ Finset.Ico (m * L) ((m + 1) * L)
              then minorPart P ρ N l f h j x else 0) := h1
        _ ≤ ((A * Pii m + K2 * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))) * ai)
            * ((A * Pij m + K2 * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))) * aj) :=
            mul_le_mul (hfac m) (hfacj m) (l2norm_nonneg _) (hPii0 m)
        _ = (A * Pii m + K2 * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
            * (A * Pij m + K2 * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))) * (ai * aj) := by ring
    -- 3. summabilities
    have hS1 : Summable (fun m : ℤ => Pii m * Pij m) := by
      refine summable_of_ne_finset_zero (s := Finset.Icc (i - Wz) (i + Wz)) fun m hm => ?_
      simp only [hPiidef, hPijdef]
      by_cases hc : |(((m - i : ℤ) : ℝ))| ≤ (Wz : ℝ)
      · exact absurd (mem_Icc_of_abs_le hc) hm
      · rw [if_neg hc, zero_mul]
    have hS2 : Summable (fun m : ℤ => Pii m * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))) := by
      refine summable_of_ne_finset_zero (s := Finset.Icc (i - Wz) (i + Wz)) fun m hm => ?_
      simp only [hPiidef]
      by_cases hc : |(((m - i : ℤ) : ℝ))| ≤ (Wz : ℝ)
      · exact absurd (mem_Icc_of_abs_le hc) hm
      · rw [if_neg hc, zero_mul]
    have hS3 : Summable (fun m : ℤ => Pij m * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))) := by
      refine summable_of_ne_finset_zero (s := Finset.Icc (j - Wz) (j + Wz)) fun m hm => ?_
      simp only [hPijdef]
      by_cases hc : |(((m - j : ℤ) : ℝ))| ≤ (Wz : ℝ)
      · exact absurd (mem_Icc_of_abs_le hc) hm
      · rw [if_neg hc, zero_mul]
    have hS4 : Summable (fun m : ℤ => (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))
        * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))) := summable_pow8_mul_pow8 i j
    have hmaj0 : Summable (fun m : ℤ =>
        (A * Pii m + K2 * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
          * (A * Pij m + K2 * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)))) := by
      have hE : ∀ m : ℤ, (A * Pii m + K2 * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
            * (A * Pij m + K2 * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
          = A ^ 2 * (Pii m * Pij m)
              + (A * K2 * (Pii m * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
                + A * K2 * (Pij m * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))))
              + K2 ^ 2 * ((1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))
                * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))) := fun m => by ring
      rw [show (fun m : ℤ => (A * Pii m + K2 * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
              * (A * Pij m + K2 * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))))
          = fun m : ℤ => A ^ 2 * (Pii m * Pij m)
              + (A * K2 * (Pii m * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
                + A * K2 * (Pij m * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))))
              + K2 ^ 2 * ((1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))
                * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))) from funext hE]
      exact ((hS1.mul_left _).add ((hS2.mul_left _).add (hS3.mul_left _))).add (hS4.mul_left _)
    have hmaj : Summable (fun m : ℤ =>
        (A * Pii m + K2 * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
          * (A * Pij m + K2 * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))) * (ai * aj)) :=
      hmaj0.mul_right _
    have hpair_summ : Summable (fun x : ℤ => ‖minorPart P ρ N l f h i x
        * star (minorPart P ρ N l f h j x)‖) := by
      refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_)
        (((summable_norm_sq_minorPart P ρ N l hN hMem hbdd i).add
          (summable_norm_sq_minorPart P ρ N l hN hMem hbdd j)).mul_right (1/2 : ℝ))
      rw [norm_mul, norm_star]
      nlinarith [sq_nonneg (‖minorPart P ρ N l f h i x‖ - ‖minorPart P ρ N l f h j x‖)]
    have hnorm_summ : Summable (fun m : ℤ => ‖∑ x ∈ Finset.Ico (m * L) ((m + 1) * L),
        minorPart P ρ N l f h i x * star (minorPart P ρ N l f h j x)‖) :=
      Summable.of_nonneg_of_le (fun m => norm_nonneg _) hterm hmaj
    -- 4. the arithmetic of the Schur kernel
    have hzero : (∑' m : ℤ, Pii m * Pij m) = 0 := by
      have hfin : (fun m : ℤ => Pii m * Pij m) = fun m : ℤ => 0 := by
        funext m
        simp only [hPiidef, hPijdef]
        by_cases hc1 : |(((m - i : ℤ) : ℝ))| ≤ (Wz : ℝ)
        · by_cases hc2 : |(((m - j : ℤ) : ℝ))| ≤ (Wz : ℝ)
          · exfalso
            have htri : |(((i - j : ℤ) : ℝ))| ≤ 2 * (Wz : ℝ) := by
              have hcast : (((i - j : ℤ) : ℝ)) = ((i - m : ℤ) : ℝ) + ((m - j : ℤ) : ℝ) := by
                push_cast; ring
              have h1 : |(((i - m : ℤ) : ℝ))| ≤ (Wz : ℝ) := by
                rw [show (((i - m : ℤ) : ℝ)) = -(((m - i : ℤ) : ℝ)) by push_cast; ring, abs_neg]
                exact hc1
              calc |(((i - j : ℤ) : ℝ))| = |((i - m : ℤ) : ℝ) + ((m - j : ℤ) : ℝ)| := by rw [hcast]
                _ ≤ |((i - m : ℤ) : ℝ)| + |((m - j : ℤ) : ℝ)| := abs_add_le _ _
                _ ≤ (Wz : ℝ) + (Wz : ℝ) := add_le_add h1 hc2
                _ = 2 * (Wz : ℝ) := by ring
            have hfarR : 2 * (Wz : ℝ) + 1 ≤ |(((i - j : ℤ) : ℝ))| := by
              rw [← Int.cast_abs]
              exact_mod_cast hfar'
            linarith
          · rw [if_pos hc1, if_neg hc2, mul_zero]
        · rw [if_neg hc1, zero_mul]
      rw [hfin]; simp
    have hwin_i : (∑' m : ℤ, Pii m * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
        ≤ (2 * (Wz : ℝ) + 1) * 2 ^ 8 * Dg := by
      have h := windowBound_self (W := Wz) hWz0 hfar'
      rw [hDgdef]
      simpa only [hPiidef] using h
    have hwin_j : (∑' m : ℤ, Pij m * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
        ≤ (2 * (Wz : ℝ) + 1) * 2 ^ 8 * Dg := by
      have h := windowBound_self (W := Wz) hWz0 (i := j) (j := i) (by
        rw [show |j - i| = |i - j| from abs_sub_comm j i]
        exact hfar')
      have hcast : |(((j - i : ℤ) : ℝ))| = |(((i - j : ℤ) : ℝ))| := by
        rw [show (((j - i : ℤ) : ℝ)) = -(((i - j : ℤ) : ℝ)) by push_cast; ring, abs_neg]
      rw [hcast] at h
      simp only [hDgdef] at h ⊢
      simpa only [hPijdef] using h
    have hkk : (∑' m : ℤ, (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))
        * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))) ≤ C₈ * Dg := by
      rw [hDgdef]
      exact hC₈le i j
    have hamgm : 2 * A * K2 * ((2 * (Wz : ℝ) + 1) * 2 ^ 8 * Dg)
        ≤ (A ^ 2 + K2 ^ 2 * (2 * (Wz : ℝ) + 1) ^ 2 * 2 ^ 16) * Dg := by
      have h1 : 2 * A * (K2 * (2 * (Wz : ℝ) + 1) * 2 ^ 8)
          ≤ A ^ 2 + (K2 * (2 * (Wz : ℝ) + 1) * 2 ^ 8) ^ 2 := by
        nlinarith [sq_nonneg (A - K2 * (2 * (Wz : ℝ) + 1) * 2 ^ 8)]
      calc 2 * A * K2 * ((2 * (Wz : ℝ) + 1) * 2 ^ 8 * Dg)
          = 2 * A * (K2 * (2 * (Wz : ℝ) + 1) * 2 ^ 8) * Dg := by ring
        _ ≤ (A ^ 2 + (K2 * (2 * (Wz : ℝ) + 1) * 2 ^ 8) ^ 2) * Dg :=
            mul_le_mul_of_nonneg_right h1 hDg0
        _ = (A ^ 2 + K2 ^ 2 * (2 * (Wz : ℝ) + 1) ^ 2 * 2 ^ 16) * Dg := by ring
    have hS1' : Summable (fun m : ℤ => A ^ 2 * (Pii m * Pij m)) := hS1.mul_left _
    have hS2' : Summable (fun m : ℤ => A * K2 * (Pii m
        * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)))) := hS2.mul_left _
    have hS3' : Summable (fun m : ℤ => A * K2 * (Pij m
        * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)))) := hS3.mul_left _
    have hS4' : Summable (fun m : ℤ => K2 ^ 2 * ((1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))
        * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)))) := hS4.mul_left _
    have harith : (∑' m : ℤ, (A * Pii m + K2 * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
          * (A * Pij m + K2 * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))))
        ≤ (A ^ 2 + K2 ^ 2 * ((2 * (Wz : ℝ) + 1) ^ 2 * 2 ^ 16 + C₈)) * Dg := by
      have hE : ∀ m : ℤ, (A * Pii m + K2 * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
            * (A * Pij m + K2 * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
          = A ^ 2 * (Pii m * Pij m)
              + (A * K2 * (Pii m * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
                + A * K2 * (Pij m * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))))
              + K2 ^ 2 * ((1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))
                * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))) := fun m => by ring
      have hsplit : (∑' m : ℤ, (A * Pii m + K2 * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
            * (A * Pij m + K2 * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))))
          = (∑' m : ℤ, A ^ 2 * (Pii m * Pij m))
            + ((∑' m : ℤ, A * K2 * (Pii m * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))))
              + (∑' m : ℤ, A * K2 * (Pij m * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)))))
            + (∑' m : ℤ, K2 ^ 2 * ((1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))
              * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)))) := by
        rw [tsum_congr hE]
        rw [Summable.tsum_add (hS1'.add (hS2'.add hS3')) hS4',
          Summable.tsum_add hS1' (hS2'.add hS3'), Summable.tsum_add hS2' hS3']
      rw [hsplit]
      have h1 : (∑' m : ℤ, A ^ 2 * (Pii m * Pij m)) = 0 := by
        rw [tsum_mul_left, hzero, mul_zero]
      have h2 : (∑' m : ℤ, A * K2 * (Pii m * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))))
          ≤ A * K2 * ((2 * (Wz : ℝ) + 1) * 2 ^ 8 * Dg) := by
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left hwin_i (mul_nonneg hA0 hK20)
      have h3 : (∑' m : ℤ, A * K2 * (Pij m * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))))
          ≤ A * K2 * ((2 * (Wz : ℝ) + 1) * 2 ^ 8 * Dg) := by
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left hwin_j (mul_nonneg hA0 hK20)
      have h4 : (∑' m : ℤ, K2 ^ 2 * ((1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))
          * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)))) ≤ K2 ^ 2 * (C₈ * Dg) := by
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left hkk (sq_nonneg K2)
      have h5 : A * K2 * ((2 * (Wz : ℝ) + 1) * 2 ^ 8 * Dg)
          + A * K2 * ((2 * (Wz : ℝ) + 1) * 2 ^ 8 * Dg)
          ≤ (A ^ 2 + K2 ^ 2 * (2 * (Wz : ℝ) + 1) ^ 2 * 2 ^ 16) * Dg := by
        linarith [hamgm]
      linarith [h1, h2, h3, h4, h5]
    -- 5. the pairing
    have hblock_summ : Summable (fun m : ℤ => ∑ x ∈ Finset.Ico (m * L) ((m + 1) * L),
        minorPart P ρ N l f h i x * star (minorPart P ρ N l f h j x)) := hnorm_summ.of_norm
    have hmain : ‖∑' x : ℤ, minorPart P ρ N l f h i x * star (minorPart P ρ N l f h j x)‖
        ≤ (A ^ 2 + K2 ^ 2 * ((2 * (Wz : ℝ) + 1) ^ 2 * 2 ^ 16 + C₈)) * Dg * (ai * aj) := by
      calc ‖∑' x : ℤ, minorPart P ρ N l f h i x * star (minorPart P ρ N l f h j x)‖
          = ‖∑' m : ℤ, ∑ x ∈ Finset.Ico (m * L) ((m + 1) * L),
              minorPart P ρ N l f h i x * star (minorPart P ρ N l f h j x)‖ := by
            rw [tsum_eq_sum_blocks hLpos hpair_summ]
        _ ≤ ∑' m : ℤ, ‖∑ x ∈ Finset.Ico (m * L) ((m + 1) * L),
              minorPart P ρ N l f h i x * star (minorPart P ρ N l f h j x)‖ :=
            norm_tsum_le_tsum_norm hnorm_summ
        _ ≤ ∑' m : ℤ, (A * Pii m + K2 * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
              * (A * Pij m + K2 * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))) * (ai * aj) :=
            Summable.tsum_le_tsum hterm hnorm_summ hmaj
        _ = (∑' m : ℤ, (A * Pii m + K2 * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
              * (A * Pij m + K2 * (1 + |(((m - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)))) * (ai * aj) := by
            rw [tsum_mul_right]
        _ ≤ (A ^ 2 + K2 ^ 2 * ((2 * (Wz : ℝ) + 1) ^ 2 * 2 ^ 16 + C₈)) * Dg * (ai * aj) :=
            mul_le_mul_of_nonneg_right harith (mul_nonneg hai0 haj0)
    -- 6. rewriting to the shape of the conclusion
    have hK2sq : K2 ^ 2 = Koff ^ 2 * (max ((l : ℝ)) 1) ^ 2
        * (2 : ℝ) ^ (-(16 * (P.natDegree : ℝ) * (l : ℝ))) := by
      rw [hK2def]
      have hpow : ((2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ)))) ^ 2
          = (2 : ℝ) ^ (-(16 * (P.natDegree : ℝ) * (l : ℝ))) := by
        rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ)))) 2,
          ← Real.rpow_mul (by norm_num)]
        congr 1
        ring
      rw [mul_pow, mul_pow, hpow]
    have hfin : (A ^ 2 + K2 ^ 2 * ((2 * (Wz : ℝ) + 1) ^ 2 * 2 ^ 16 + C₈)) * Dg * (ai * aj)
        ≤ (A ^ 2 + (Koff ^ 2 * ((2 * (Wz : ℝ) + 1) ^ 2 * 2 ^ 16 + C₈) + 1)
            * (max ((l : ℝ)) 1) ^ 2 * (2 : ℝ) ^ (-(16 * (P.natDegree : ℝ) * (l : ℝ))))
          * (1 + |(((i - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)) * ai * aj := by
      have hX0 : (0 : ℝ) ≤ (2 * (Wz : ℝ) + 1) ^ 2 * 2 ^ 16 + C₈ := by positivity
      have hp0 : (0 : ℝ) ≤ (max ((l : ℝ)) 1) ^ 2
          * (2 : ℝ) ^ (-(16 * (P.natDegree : ℝ) * (l : ℝ))) := by positivity
      have hkey : K2 ^ 2 * ((2 * (Wz : ℝ) + 1) ^ 2 * 2 ^ 16 + C₈)
          ≤ (Koff ^ 2 * ((2 * (Wz : ℝ) + 1) ^ 2 * 2 ^ 16 + C₈) + 1)
            * (max ((l : ℝ)) 1) ^ 2 * (2 : ℝ) ^ (-(16 * (P.natDegree : ℝ) * (l : ℝ))) := by
        rw [hK2sq]
        have h1 : (0 : ℝ) ≤ Koff ^ 2 * ((2 * (Wz : ℝ) + 1) ^ 2 * 2 ^ 16 + C₈) :=
          mul_nonneg (sq_nonneg Koff) hX0
        nlinarith [h1, hp0, hX0]
      have h2 : A ^ 2 + K2 ^ 2 * ((2 * (Wz : ℝ) + 1) ^ 2 * 2 ^ 16 + C₈)
          ≤ A ^ 2 + (Koff ^ 2 * ((2 * (Wz : ℝ) + 1) ^ 2 * 2 ^ 16 + C₈) + 1)
            * (max ((l : ℝ)) 1) ^ 2 * (2 : ℝ) ^ (-(16 * (P.natDegree : ℝ) * (l : ℝ))) := by
        linarith [hkey]
      have h3 : (A ^ 2 + K2 ^ 2 * ((2 * (Wz : ℝ) + 1) ^ 2 * 2 ^ 16 + C₈)) * Dg * (ai * aj)
          ≤ (A ^ 2 + (Koff ^ 2 * ((2 * (Wz : ℝ) + 1) ^ 2 * 2 ^ 16 + C₈) + 1)
            * (max ((l : ℝ)) 1) ^ 2 * (2 : ℝ) ^ (-(16 * (P.natDegree : ℝ) * (l : ℝ))))
            * Dg * (ai * aj) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hDg0)
          (mul_nonneg hai0 haj0)
      refine h3.trans (le_of_eq ?_)
      rw [hDgdef]
      ring
    exact hmain.trans hfin

end Work.KMTAreas.A4Z
