import Mathlib
import Submission.Work.NN.Core.beltrami_theta_setup
import Submission.Work.NN.Core.holderNorm_le_of_tendsto

noncomputable section

open scoped NNReal ENNReal
open Set Filter

namespace Work.NN.Core

/-- A family of functions `H : Fin n → (Fin n → ℂ) → ℂ` vanishes off a polydisc. -/
private lemma fam_diff_vanishes {n : ℕ} {ρ : Fin n → ℝ}
    {A B : Fin n → (Fin n → ℂ) → ℂ}
    (hA : ∀ j z, z ∉ Work.CR.Flat.polydisc 0 ρ → A j z = 0)
    (hB : ∀ j z, z ∉ Work.CR.Flat.polydisc 0 ρ → B j z = 0) :
    ∀ j z, z ∉ Work.CR.Flat.polydisc 0 ρ → (A - B) j z = 0 := by
  intro j z hz
  simp only [Pi.sub_apply, hA j z hz, hB j z hz, sub_zero]

/-- The family norm of a difference is finite if both components are. -/
private lemma famNorm_sub_lt_top {n : ℕ} {α : ℝ} {H H' : Fin n → (Fin n → ℂ) → ℂ}
    (h : Work.NN.Core.BTheta.famNorm α H < ⊤) (h' : Work.NN.Core.BTheta.famNorm α H' < ⊤) :
    Work.NN.Core.BTheta.famNorm α (H - H') < ⊤ :=
  lt_of_le_of_lt (Work.NN.Core.BTheta.famNorm_sub_le H H') (ENNReal.add_lt_top.mpr ⟨h, h'⟩)

/-- Finiteness of the family norm gives finiteness of each component. -/
private lemma famNorm_apply_lt_top {n : ℕ} {α : ℝ} {H : Fin n → (Fin n → ℂ) → ℂ}
    (h : Work.NN.Core.BTheta.famNorm α H < ⊤) (j : Fin n) :
    Work.CR.Flat.holderNorm 0 α (H j) Set.univ < ⊤ :=
  lt_of_le_of_lt (Work.NN.Core.BTheta.famNorm_apply_le (α := α) H j) h

/-- **Banach fixed point** for an operator `T` on families that is additive, vanishes off the
polydisc, and is a contraction of ratio `lam ≤ 1/2` in the family `C^{0,α}`-norm.

The solution is produced as the pointwise limit of the Picard iteration
`Y 0 = 0`, `Y (m+1) = T (Y m) + S`; the contraction estimate bounds `famNorm (Y m - Yinf)` by
`O(lam^m)`, so the limit solves `Y = T Y + S`. -/
theorem famNorm_contraction_fixedpoint {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    (T : (Fin n → (Fin n → ℂ) → ℂ) → (Fin n → (Fin n → ℂ) → ℂ)) (lam : ℝ)
    (hlam0 : 0 ≤ lam) (hlamhalf : lam ≤ 1 / 2)
    (hT0 : T 0 = 0)
    (hTvan : ∀ Y j z, z ∉ Work.CR.Flat.polydisc 0 ρ → T Y j z = 0)
    (hTsub : ∀ Y Y' : Fin n → (Fin n → ℂ) → ℂ,
      (∀ j, Work.CR.Flat.holderNorm 0 α (Y j) Set.univ < ⊤) →
      (∀ j z, z ∉ Work.CR.Flat.polydisc 0 ρ → Y j z = 0) →
      (∀ j, Work.CR.Flat.holderNorm 0 α (Y' j) Set.univ < ⊤) →
      (∀ j z, z ∉ Work.CR.Flat.polydisc 0 ρ → Y' j z = 0) →
      ∀ j z, T Y j z - T Y' j z = T (Y - Y') j z)
    (hTbound : ∀ Y : Fin n → (Fin n → ℂ) → ℂ,
      (∀ j, Work.CR.Flat.holderNorm 0 α (Y j) Set.univ < ⊤) →
      (∀ j z, z ∉ Work.CR.Flat.polydisc 0 ρ → Y j z = 0) →
      Work.NN.Core.BTheta.famNorm α (T Y) ≤ ENNReal.ofReal lam * Work.NN.Core.BTheta.famNorm α Y)
    {S : Fin n → (Fin n → ℂ) → ℂ}
    (hSvan : ∀ j z, z ∉ Work.CR.Flat.polydisc 0 ρ → S j z = 0)
    (hSfin : Work.NN.Core.BTheta.famNorm α S < ⊤) :
    ∃ Y : Fin n → (Fin n → ℂ) → ℂ,
      (∀ j, Work.CR.Flat.holderNorm 0 α (Y j) Set.univ < ⊤) ∧
      (∀ j z, z ∉ Work.CR.Flat.polydisc 0 ρ → Y j z = 0) ∧
      (∀ j z, Y j z = T Y j z + S j z) := by
  classical
  have hlam1 : lam < 1 := by linarith
  have h1lam : (0 : ℝ) < 1 - lam := by linarith
  -- the size of the source term, as a real number
  set s : ℝ := (Work.NN.Core.BTheta.famNorm α S).toReal with hsdef
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  have hSeq : Work.NN.Core.BTheta.famNorm α S = ENNReal.ofReal s := by
    rw [hsdef]; exact (ENNReal.ofReal_toReal (ne_of_lt hSfin)).symm
  -- the Picard iteration
  let Y : ℕ → Fin n → (Fin n → ℂ) → ℂ := fun m =>
    Nat.rec (0 : Fin n → (Fin n → ℂ) → ℂ) (fun _ Yk => T Yk + S) m
  have Y_zero : Y 0 = 0 := rfl
  have Y_succ : ∀ m, Y (m + 1) = T (Y m) + S := fun m => rfl
  -- vanishing of every iterate off the polydisc
  have hYvan : ∀ m, ∀ j z, z ∉ Work.CR.Flat.polydisc 0 ρ → Y m j z = 0 := by
    intro m
    induction m with
    | zero => intro j z _; rw [Y_zero]; rfl
    | succ m ih =>
        intro j z hz
        rw [Y_succ m]
        simp only [Pi.add_apply, hTvan (Y m) j z hz, hSvan j z hz, add_zero]
  -- finiteness of every iterate
  have hYfin : ∀ m, Work.NN.Core.BTheta.famNorm α (Y m) < ⊤ := by
    intro m
    induction m with
    | zero => rw [Y_zero]; simp
    | succ m ih =>
        rw [Y_succ m]
        refine lt_of_le_of_lt (Work.NN.Core.BTheta.famNorm_add_le (T (Y m)) S) ?_
        refine ENNReal.add_lt_top.mpr ⟨?_, hSfin⟩
        exact lt_of_le_of_lt (hTbound (Y m) (fun j => famNorm_apply_lt_top ih j) (hYvan m))
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ih)
  -- the geometric partial sums of `lam`
  set pgeom : ℕ → ℝ := fun m => ∑ i ∈ Finset.range m, lam ^ i with hpgeom
  have hpgeom_nn : ∀ m, 0 ≤ pgeom m := fun m => Finset.sum_nonneg fun i _ => pow_nonneg hlam0 i
  have hpgeom_succ : ∀ m, pgeom (m + 1) = 1 + lam * pgeom m := by
    intro m
    have h2 : (∑ i ∈ Finset.range m, lam ^ (i + 1)) = lam * pgeom m := by
      rw [hpgeom, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [pow_succ']
    calc pgeom (m + 1) = ∑ i ∈ Finset.range (m + 1), lam ^ i := rfl
      _ = (∑ i ∈ Finset.range m, lam ^ (i + 1)) + lam ^ 0 := Finset.sum_range_succ' _ _
      _ = lam * pgeom m + 1 := by rw [h2, pow_zero]
      _ = 1 + lam * pgeom m := by ring
  have hpgeom_bound : ∀ m, pgeom m ≤ 1 / (1 - lam) := by
    intro m
    induction m with
    | zero => show (0 : ℝ) ≤ 1 / (1 - lam); exact div_nonneg zero_le_one h1lam.le
    | succ m ih =>
        rw [hpgeom_succ m]
        have h2 : lam * pgeom m ≤ lam * (1 / (1 - lam)) := mul_le_mul_of_nonneg_left ih hlam0
        have h3 : lam * (1 / (1 - lam)) = 1 / (1 - lam) - 1 := by field_simp; ring
        linarith
  -- a uniform bound on the iterates
  have hbd : ∀ m, Work.NN.Core.BTheta.famNorm α (Y m) ≤ ENNReal.ofReal (s * pgeom m) := by
    intro m
    induction m with
    | zero => rw [Y_zero]; simp
    | succ m ih =>
        rw [Y_succ m]
        refine (Work.NN.Core.BTheta.famNorm_add_le (T (Y m)) S).trans ?_
        have h1 : Work.NN.Core.BTheta.famNorm α (T (Y m)) ≤
            ENNReal.ofReal lam * Work.NN.Core.BTheta.famNorm α (Y m) :=
          hTbound (Y m) (fun j => famNorm_apply_lt_top (hYfin m) j) (hYvan m)
        have h1' : ENNReal.ofReal lam * Work.NN.Core.BTheta.famNorm α (Y m)
            ≤ ENNReal.ofReal lam * ENNReal.ofReal (s * pgeom m) := mul_le_mul_right ih _
        refine (add_le_add (h1.trans h1') le_rfl).trans ?_
        rw [hSeq, ← ENNReal.ofReal_mul hlam0, ← ENNReal.ofReal_add
          (mul_nonneg hlam0 (mul_nonneg hs0 (hpgeom_nn m))) hs0]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hpgeom_succ m]
        nlinarith [hs0, hlam0, hpgeom_nn m]
  -- consecutive differences shrink geometrically
  have hdiff : ∀ m, Work.NN.Core.BTheta.famNorm α (Y (m + 1) - Y m)
      ≤ ENNReal.ofReal (lam ^ m * s) := by
    intro m
    induction m with
    | zero =>
        have h0 : Y (0 + 1) - Y 0 = S := by
          rw [Y_succ 0, Y_zero, hT0]; simp
        rw [h0, hSeq, pow_zero, one_mul]
    | succ m ih =>
        have hsub : Y (m + 1 + 1) - Y (m + 1) = T (Y (m + 1) - Y m) := by
          have h1 : Y (m + 1 + 1) - Y (m + 1)
              = (T (Y (m + 1)) + S) - (T (Y m) + S) := by rw [Y_succ (m + 1), Y_succ m]
          have h2 : (T (Y (m + 1)) + S) - (T (Y m) + S) = T (Y (m + 1)) - T (Y m) := by
            funext j z; simp only [Pi.add_apply, Pi.sub_apply]; ring
          have h3 : T (Y (m + 1)) - T (Y m) = T (Y (m + 1) - Y m) := by
            funext j z
            exact hTsub (Y (m + 1)) (Y m) (fun j => famNorm_apply_lt_top (hYfin (m + 1)) j)
              (hYvan (m + 1)) (fun j => famNorm_apply_lt_top (hYfin m) j) (hYvan m) j z
          rw [h1, h2, h3]
        rw [hsub]
        refine (hTbound (Y (m + 1) - Y m)
          (fun j => famNorm_apply_lt_top
            (famNorm_sub_lt_top (hYfin (m + 1)) (hYfin m)) j)
          (fam_diff_vanishes (hYvan (m + 1)) (hYvan m))).trans ?_
        refine (mul_le_mul_right ih _).trans ?_
        rw [← ENNReal.ofReal_mul hlam0]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [pow_succ]
        exact le_of_eq (by ring)
  -- the tail estimate for the iteration
  have hcau : ∀ m m' : ℕ, m ≤ m' → Work.NN.Core.BTheta.famNorm α (Y m' - Y m)
      ≤ ENNReal.ofReal (s * (lam ^ m / (1 - lam))) := by
    intro m m' hmm
    have hsub : Y m' - Y m = ∑ i ∈ Finset.range (m' - m), (Y (m + i + 1) - Y (m + i)) := by
      funext j z
      have h := Work.NN.Core.BTheta.sub_eq_sum_range (fun i => Y i j z) m (m' - m)
      rw [show m + (m' - m) = m' from Nat.add_sub_cancel' hmm] at h
      simpa only [Pi.sub_apply, Finset.sum_apply] using h
    rw [hsub]
    refine (Work.NN.Core.BTheta.famNorm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hdiff (m + i)).trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (pow_nonneg hlam0 _) hs0)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ∑ i ∈ Finset.range (m' - m), lam ^ (m + i) * s
        = s * (lam ^ m * pgeom (m' - m)) := by
          rw [hpgeom, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [pow_add]
          ring
      _ ≤ s * (lam ^ m * (1 / (1 - lam))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hpgeom_bound _)
            (pow_nonneg hlam0 m)) hs0
      _ = s * (lam ^ m / (1 - lam)) := by ring
  have hcau' : ∀ m m' : ℕ, Work.NN.Core.BTheta.famNorm α (Y m - Y m')
      ≤ ENNReal.ofReal (s * (lam ^ (min m m') / (1 - lam))) := by
    intro m m'
    rcases le_total m m' with hle | hle
    · rw [min_eq_left hle]
      have h := hcau m m' hle
      rwa [show Y m - Y m' = -(Y m' - Y m) from by
        funext a b; simp only [Pi.sub_apply, Pi.neg_apply]; ring,
        Work.NN.Core.BTheta.famNorm_neg (α := α)]
    · rw [min_eq_right hle]
      exact hcau m' m hle
  -- the tail bound tends to `0`
  have htendlam : Tendsto (fun m : ℕ => s * (lam ^ m / (1 - lam))) atTop (nhds 0) := by
    have h1 : Tendsto (fun m : ℕ => lam ^ m) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hlam0 hlam1
    have h2 : Tendsto (fun m : ℕ => (s / (1 - lam)) * lam ^ m) atTop
        (nhds ((s / (1 - lam)) * 0)) := tendsto_const_nhds.mul h1
    rw [mul_zero] at h2
    refine h2.congr' (Eventually.of_forall fun m => ?_)
    ring
  -- pointwise Cauchy, hence pointwise convergent
  have hlim : ∀ (j : Fin n) (z : Fin n → ℂ), ∃ y : ℂ, Tendsto (fun m => Y m j z) atTop (nhds y) := by
    intro j z
    refine cauchySeq_tendsto_of_complete ?_
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨M, hM⟩ := eventually_atTop.1 ((tendsto_order.1 htendlam).2 ε hε)
    refine ⟨M, fun m hm m' hm' => ?_⟩
    rw [dist_eq_norm]
    have hmin : M ≤ min m m' := le_min hm hm'
    have h1 : ENNReal.ofReal ‖Y m j z - Y m' j z‖ ≤
        ENNReal.ofReal (s * (lam ^ (min m m') / (1 - lam))) :=
      ((Work.CR.Flat.norm_apply_le_holderNorm 0 α ((Y m - Y m') j) Set.univ
        (Set.mem_univ z)).trans (Work.NN.Core.BTheta.famNorm_apply_le (α := α) (Y m - Y m') j)).trans
        (hcau' m m')
    have h2 : ‖Y m j z - Y m' j z‖ ≤ s * (lam ^ (min m m') / (1 - lam)) := by
      refine (ENNReal.ofReal_le_ofReal_iff ?_).mp h1
      positivity
    have h3 : s * (lam ^ (min m m') / (1 - lam)) ≤ s * (lam ^ M / (1 - lam)) := by
      refine mul_le_mul_of_nonneg_left ?_ hs0
      refine div_le_div_of_nonneg_right ?_ h1lam.le
      exact pow_le_pow_of_le_one hlam0 hlam1.le hmin
    have h4 : s * (lam ^ M / (1 - lam)) < ε := hM M le_rfl
    linarith
  choose Yinf hYinf using hlim
  -- finiteness of the limit's `C^{0,α}`-norm
  have hYinf_fin : ∀ j, Work.CR.Flat.holderNorm 0 α (Yinf j) Set.univ < ⊤ := by
    intro j
    have hcont : ∀ m, ContDiffOn ℝ (0 : ℕ∞) ((Y m) j) Set.univ := fun m =>
      contDiffOn_zero.mpr ((continuous_of_holderNorm_zero_lt_top hα0
        (famNorm_apply_lt_top (hYfin m) j)).continuousOn)
    have hbound : ∀ m, Work.CR.Flat.holderNorm 0 α ((Y m) j) Set.univ
        ≤ ENNReal.ofReal (s * (1 / (1 - lam))) := fun m =>
      (Work.NN.Core.BTheta.famNorm_apply_le (α := α) (Y m) j).trans
        ((hbd m).trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (hpgeom_bound m) hs0)))
    have hcaum : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m m' : ℕ, M ≤ m → M ≤ m' →
        Work.CR.Flat.holderNorm 0 α ((Y m - Y m') j) Set.univ ≤ ENNReal.ofReal ε := by
      intro ε hε
      obtain ⟨M, hM⟩ := eventually_atTop.1 ((tendsto_order.1 htendlam).2 ε hε)
      refine ⟨M, fun m m' hm hm' => ?_⟩
      have hmin : M ≤ min m m' := le_min hm hm'
      refine (Work.NN.Core.BTheta.famNorm_apply_le (α := α) (Y m - Y m') j).trans
        ((hcau' m m').trans ?_)
      refine ENNReal.ofReal_le_ofReal ?_
      have h3 : s * (lam ^ (min m m') / (1 - lam)) ≤ s * (lam ^ M / (1 - lam)) := by
        refine mul_le_mul_of_nonneg_left ?_ hs0
        refine div_le_div_of_nonneg_right ?_ h1lam.le
        exact pow_le_pow_of_le_one hlam0 hlam1.le hmin
      linarith [hM M le_rfl]
    obtain ⟨h1, -⟩ := Work.NN.Core.holderNorm_le_of_tendsto (X := Fin n → ℂ) (k := 0) (α := α)
      (P := Set.univ) isOpen_univ (C := s * (1 / (1 - lam))) (by positivity)
      hcont hbound (fun z _ => hYinf j z) hcaum
    exact lt_of_le_of_lt h1 ENNReal.ofReal_lt_top
  have hYinf_fam_fin : Work.NN.Core.BTheta.famNorm α Yinf < ⊤ :=
    Work.NN.Core.BTheta.famNorm_lt_top hYinf_fin
  -- the limit vanishes off the polydisc
  have hYinf_van : ∀ j z, z ∉ Work.CR.Flat.polydisc 0 ρ → Yinf j z = 0 := by
    intro j z hz
    have h0 : Tendsto (fun m => Y m j z) atTop (nhds 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards with m
      exact (hYvan m j z hz).symm
    exact tendsto_nhds_unique (hYinf j z) h0
  -- the tail of the iteration compared with the limit
  have hYinf_diff : ∀ m j, Work.CR.Flat.holderNorm 0 α ((Y m - Yinf) j) Set.univ
      ≤ ENNReal.ofReal (s * (lam ^ m / (1 - lam))) := by
    intro m j
    have hconv : ∀ z ∈ (Set.univ : Set (Fin n → ℂ)),
        Tendsto (fun k => (Y m - Y (m + k)) j z) atTop (nhds ((Y m - Yinf) j z)) := by
      intro z _
      have h1 : Tendsto (fun k => Y (m + k) j z) atTop (nhds (Yinf j z)) := by
        have h2 : (fun k : ℕ => Y (m + k) j z) = fun k => Y (k + m) j z := by
          funext k; rw [Nat.add_comm]
        rw [h2]
        exact (hYinf j z).comp (tendsto_add_atTop_nat m)
      have h2 : Tendsto (fun k => Y m j z - Y (m + k) j z) atTop (nhds (Y m j z - Yinf j z)) :=
        tendsto_const_nhds.sub h1
      simpa only [Pi.sub_apply] using h2
    have hcont : ∀ k : ℕ, ContDiffOn ℝ (0 : ℕ∞) ((Y m - Y (m + k)) j) Set.univ := fun k => by
      have h1 : Continuous ((Y m) j - (Y (m + k)) j) :=
        (continuous_of_holderNorm_zero_lt_top hα0
          (famNorm_apply_lt_top (hYfin m) j)).sub
        (continuous_of_holderNorm_zero_lt_top hα0
          (famNorm_apply_lt_top (hYfin (m + k)) j))
      have h2 : ((Y m - Y (m + k)) j) = ((Y m) j - (Y (m + k)) j) := rfl
      rw [h2]
      exact contDiffOn_zero.mpr h1.continuousOn
    have hbound : ∀ k : ℕ, Work.CR.Flat.holderNorm 0 α ((Y m - Y (m + k)) j) Set.univ
        ≤ ENNReal.ofReal (s * (lam ^ m / (1 - lam))) := fun k => by
      have h := hcau' m (m + k)
      rw [min_eq_left (Nat.le_add_right m k)] at h
      refine (Work.NN.Core.BTheta.famNorm_apply_le (α := α) (Y m - Y (m + k)) j).trans h
    have hcaum : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ k k' : ℕ, M ≤ k → M ≤ k' →
        Work.CR.Flat.holderNorm 0 α ((Y m - Y (m + k)) j - (Y m - Y (m + k')) j) Set.univ
          ≤ ENNReal.ofReal ε := by
      intro ε hε
      obtain ⟨M, hM⟩ := eventually_atTop.1 ((tendsto_order.1 htendlam).2 ε hε)
      refine ⟨M, fun k k' hk hk' => ?_⟩
      have hmin : M ≤ min (m + k') (m + k) := le_min (by linarith) (by linarith)
      have hsub : ((Y m - Y (m + k)) j - (Y m - Y (m + k')) j)
          = (Y (m + k') - Y (m + k)) j := by
        funext a; simp only [Pi.sub_apply]; ring
      rw [hsub]
      refine (Work.NN.Core.BTheta.famNorm_apply_le (α := α) (Y (m + k') - Y (m + k)) j).trans
        ((hcau' (m + k') (m + k)).trans ?_)
      refine ENNReal.ofReal_le_ofReal ?_
      have h3 : s * (lam ^ (min (m + k') (m + k)) / (1 - lam)) ≤ s * (lam ^ M / (1 - lam)) := by
        refine mul_le_mul_of_nonneg_left ?_ hs0
        refine div_le_div_of_nonneg_right ?_ h1lam.le
        exact pow_le_pow_of_le_one hlam0 hlam1.le hmin
      linarith [hM M le_rfl]
    obtain ⟨h1, -⟩ := Work.NN.Core.holderNorm_le_of_tendsto (X := Fin n → ℂ) (k := 0) (α := α)
      (P := Set.univ) isOpen_univ (C := s * (lam ^ m / (1 - lam))) (by positivity)
      hcont hbound hconv hcaum
    exact h1
  have hfam_diff : ∀ m, Work.NN.Core.BTheta.famNorm α (Y m - Yinf)
      ≤ ENNReal.ofReal ((n : ℝ) * (s * (lam ^ m / (1 - lam)))) := by
    intro m
    have hsum : Work.NN.Core.BTheta.famNorm α (Y m - Yinf)
        = ∑ j, Work.CR.Flat.holderNorm 0 α ((Y m - Yinf) j) Set.univ := rfl
    rw [hsum]
    refine (Finset.sum_le_sum fun j _ => hYinf_diff m j).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  -- the fixed point equation
  have hfeq : ∀ j z, Yinf j z = T Yinf j z + S j z := by
    intro j z
    have hconvY : Tendsto (fun m => Y (m + 1) j z) atTop (nhds (Yinf j z)) :=
      (hYinf j z).comp (tendsto_add_atTop_nat 1)
    have hconvT : Tendsto (fun m => T (Y m) j z) atTop (nhds (T Yinf j z)) := by
      have hb : ∀ m, ‖T (Y m) j z - T Yinf j z‖
          ≤ lam * ((n : ℝ) * (s * (lam ^ m / (1 - lam)))) := by
        intro m
        have hsub : T (Y m) j z - T Yinf j z = T (Y m - Yinf) j z :=
          hTsub (Y m) Yinf (fun j => famNorm_apply_lt_top (hYfin m) j) (hYvan m)
            (fun j => hYinf_fin j) hYinf_van j z
        rw [hsub]
        have h1 : ENNReal.ofReal ‖T (Y m - Yinf) j z‖
            ≤ Work.NN.Core.BTheta.famNorm α (T (Y m - Yinf)) :=
          (Work.CR.Flat.norm_apply_le_holderNorm 0 α (T (Y m - Yinf) j) Set.univ
            (Set.mem_univ z)).trans
            (Work.NN.Core.BTheta.famNorm_apply_le (α := α) (T (Y m - Yinf)) j)
        have h2 : Work.NN.Core.BTheta.famNorm α (T (Y m - Yinf))
            ≤ ENNReal.ofReal lam * Work.NN.Core.BTheta.famNorm α (Y m - Yinf) :=
          hTbound (Y m - Yinf)
            (fun j => famNorm_apply_lt_top (famNorm_sub_lt_top (hYfin m) hYinf_fam_fin) j)
            (fam_diff_vanishes (hYvan m) hYinf_van)
        have h3 : Work.NN.Core.BTheta.famNorm α (T (Y m - Yinf))
            ≤ ENNReal.ofReal (lam * ((n : ℝ) * (s * (lam ^ m / (1 - lam))))) := by
          refine h2.trans ?_
          calc ENNReal.ofReal lam * Work.NN.Core.BTheta.famNorm α (Y m - Yinf)
              ≤ ENNReal.ofReal lam
                * ENNReal.ofReal ((n : ℝ) * (s * (lam ^ m / (1 - lam)))) :=
                mul_le_mul_right (hfam_diff m) _
            _ = ENNReal.ofReal (lam * ((n : ℝ) * (s * (lam ^ m / (1 - lam))))) :=
                (ENNReal.ofReal_mul hlam0).symm
        have h4 : ENNReal.ofReal ‖T (Y m - Yinf) j z‖
            ≤ ENNReal.ofReal (lam * ((n : ℝ) * (s * (lam ^ m / (1 - lam))))) := h1.trans h3
        refine (ENNReal.ofReal_le_ofReal_iff ?_).mp h4
        positivity
      refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
      refine squeeze_zero (fun m => norm_nonneg _) hb ?_
      have h1 : Tendsto (fun m : ℕ => s * (lam ^ m / (1 - lam))) atTop (nhds 0) := htendlam
      have h2 : Tendsto (fun m : ℕ => lam * ((n : ℝ) * (s * (lam ^ m / (1 - lam))))) atTop
          (nhds (lam * ((n : ℝ) * 0))) :=
        tendsto_const_nhds.mul (tendsto_const_nhds.mul h1)
      simpa using h2
    have hlim2 : Tendsto (fun m => T (Y m) j z + S j z) atTop (nhds (T Yinf j z + S j z)) :=
      hconvT.add tendsto_const_nhds
    refine tendsto_nhds_unique hconvY ?_
    refine hlim2.congr' (Eventually.of_forall fun m => ?_)
    simp only [Y_succ m, Pi.add_apply]
  exact ⟨Yinf, hYinf_fin, hYinf_van, hfeq⟩

end Work.NN.Core
