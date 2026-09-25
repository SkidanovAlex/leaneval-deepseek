import Mathlib
import Submission.Work.NN.Final.SeeleyLoc
import Submission.Work.NN.Seeley.seeleyTV_hSN_le
import Submission.Work.CR.Flat.Holder.Bilinear


open scoped NNReal ENNReal ContDiff Topology BigOperators
open Set Filter

namespace Work.NN.Final

/-- Elementary counting bound: for nonnegative extended reals `a`, `b` indexed by `ℕ`,
`∑_{j ≤ n} a j * b (n - j) ≤ (∑_{j ≤ n} a j) * (∑_{j ≤ n} b j)` (the left-hand side is a
sub-sum of the double sum, using `n - j ≤ n`). -/
private lemma sum_shift_le {n : ℕ} (a b : ℕ → ℝ≥0∞) :
    (∑ j ∈ Finset.range (n + 1), a j * b (n - j))
      ≤ (∑ j ∈ Finset.range (n + 1), a j) * (∑ k ∈ Finset.range (n + 1), b k) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  refine mul_le_mul' le_rfl ?_
  exact Finset.single_le_sum (fun k _ => zero_le)
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.sub_le n j)))

/-- Sup-norm bound for the `i`-th iterated derivative of the `m`-th Seeley term on the open lower slab `seLw W δ`, in terms of the `C^i` sup-norms of `g` on the open upper half space `seUp W`. -/
theorem seeleyLoc_term_gDN_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℕ → ℝ} (hb1 : ∀ m, 1 ≤ b m) {W : Set E} (hW : IsOpen W)
    {δ : ℝ} {i : ℕ} {g : E × ℝ → ℂ}
    (hg : ContDiffOn ℝ (i : WithTop ENat) g (seHp W)) (m : ℕ) :
    Work.NN.Final.gDN i (seeleyTerm a b g m) (seLw W δ)
      ≤ ENNReal.ofReal (|a m| * (b m) ^ i *
          (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * seeleyCutB j))
        * (∑ j ∈ Finset.range (i + 1), Work.CR.Flat.Holder.iDN j g (seUp W)) := by
  have hbm : 0 ≤ b m := by linarith [hb1 m]
  have hΩ : IsOpen (seLw W δ) := isOpen_seLw hW δ
  have hU : IsOpen (seUp W) := isOpen_seUp hW
  -- rewrite the Seeley term as a bounded bilinear map applied to a real cutoff and the sheared `g`
  have hEq : seeleyTerm a b g m
      = (fun p : E × ℝ => ((a m) • Work.NN.Seeley.lsmulL)
          (seeleyCut (-(b m) * p.2)) (g (p.1, -(b m) * p.2))) := by
    funext p
    rw [seeleyTerm_apply]
    simp only [smul_apply, Work.NN.Seeley.lsmulL,
      ContinuousLinearMap.lsmul_apply, smul_smul]
    rw [Complex.real_smul, Complex.ofReal_mul]; ring
  -- smoothness of the two factors on the open slab
  have hχ : ContDiffOn ℝ (i : WithTop ℕ∞)
      (fun p : E × ℝ => seeleyCut (-(b m) * p.2)) (seLw W δ) := by
    have h : ContDiff ℝ ∞ (fun p : E × ℝ => seeleyCut (-(b m) * p.2)) := by
      have h2 : ContDiff ℝ ∞ (fun p : E × ℝ => -(b m) * p.2) := by fun_prop
      exact seeleyCut_contDiff.comp h2
    exact (h.of_le (by simp)).contDiffOn
  have hMapsTo : Set.MapsTo (fun p : E × ℝ => (p.1, -(b m) * p.2)) (seLw W δ) (seUp W) := by
    intro p hp
    simp only [mem_seLw] at hp
    simp only [mem_seUp]
    exact ⟨hp.1, by nlinarith [hb1 m, hp.2.2]⟩
  have hΨ : ContDiffOn ℝ (i : WithTop ℕ∞)
      (fun p : E × ℝ => g (p.1, -(b m) * p.2)) (seLw W δ) := by
    have hshear : ContDiff ℝ ∞ (fun p : E × ℝ => (p.1, -(b m) * p.2)) := by fun_prop
    exact ContDiffOn.comp (hg.mono seUp_subset_seHp)
      (hshear.of_le (by simp)).contDiffOn hMapsTo
  -- the bilinear Leibniz bound for the within-derivatives
  have hbil := Work.CR.Flat.Holder.iDN_bilinear_le
    ((a m) • Work.NN.Seeley.lsmulL) i hχ hΨ hΩ.uniqueDiffOn
  rw [hEq, gDN_eq_iDN hΩ]
  refine hbil.trans ?_
  have hSnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * seeleyCutB j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (seeleyCutB_nonneg j)
  have hBnd : ENNReal.ofReal ‖(a m) • Work.NN.Seeley.lsmulL‖ ≤ ENNReal.ofReal |a m| := by
    refine ENNReal.ofReal_le_ofReal ?_
    refine (ContinuousLinearMap.opNorm_smul_le (a m) Work.NN.Seeley.lsmulL).trans ?_
    rw [Real.norm_eq_abs]
    calc |a m| * ‖Work.NN.Seeley.lsmulL‖ ≤ |a m| * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.opNorm_lsmul_le (abs_nonneg _)
      _ = |a m| := mul_one _
  have hχbnd : ∀ j ∈ Finset.range (i + 1),
      Work.CR.Flat.Holder.iDN j (fun p : E × ℝ => seeleyCut (-(b m) * p.2)) (seLw W δ)
        ≤ ENNReal.ofReal ((b m) ^ j * seeleyCutB j) := by
    intro j _
    rw [← gDN_eq_iDN hΩ j]
    exact (gDN_cutoff_le (X := E) (c := -(b m)) (i := j) (Ω := seLw W δ)).trans
      (le_of_eq (by rw [abs_neg, abs_of_nonneg hbm]))
  have hΨbnd : ∀ j ∈ Finset.range (i + 1),
      Work.CR.Flat.Holder.iDN (i - j) (fun p : E × ℝ => g (p.1, -(b m) * p.2)) (seLw W δ)
        ≤ ENNReal.ofReal ((b m) ^ (i - j)) * Work.CR.Flat.Holder.iDN (i - j) g (seUp W) := by
    intro j _
    rw [← gDN_eq_iDN hΩ (i - j)]
    have hc : (1 : ℝ) ≤ |(-(b m))| := by rw [abs_neg, abs_of_nonneg hbm]; exact hb1 m
    have hsub : (fun p : E × ℝ => (p.1, -(b m) * p.2)) '' (seLw W δ) ⊆ seUp W :=
      shear_image_seLw_subset_seUp (by linarith [hb1 m])
    have hu : ContDiffOn ℝ (((i - j : ℕ)) : WithTop ENat) g (seUp W) :=
      (hg.mono seUp_subset_seHp).of_le (by exact_mod_cast Nat.sub_le i j)
    exact (gDN_comp_shear_le (c := -(b m)) hc hU hΩ hsub hu).trans
      (le_of_eq (by rw [abs_neg, abs_of_nonneg hbm, gDN_eq_iDN hU]))
  -- the term-by-term bound
  have hterm : ∀ j ∈ Finset.range (i + 1),
      (i.choose j : ℝ≥0∞) *
        (Work.CR.Flat.Holder.iDN j (fun p : E × ℝ => seeleyCut (-(b m) * p.2)) (seLw W δ)
         * Work.CR.Flat.Holder.iDN (i - j) (fun p : E × ℝ => g (p.1, -(b m) * p.2))
             (seLw W δ))
      ≤ ENNReal.ofReal ((b m) ^ i) *
          (ENNReal.ofReal ((i.choose j : ℝ) * seeleyCutB j)
            * Work.CR.Flat.Holder.iDN (i - j) g (seUp W)) := by
    intro j hj
    have hjle : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hsc : 0 ≤ seeleyCutB j := seeleyCutB_nonneg j
    have h2 : (b m) ^ (i - j) * (b m) ^ j = (b m) ^ i := by
      rw [← pow_add, Nat.sub_add_cancel hjle]
    have heq : (i.choose j : ℝ) * ((b m) ^ j * seeleyCutB j * (b m) ^ (i - j))
        = (b m) ^ i * ((i.choose j : ℝ) * seeleyCutB j) := by
      rw [← h2]; ring
    calc (i.choose j : ℝ≥0∞) *
          (Work.CR.Flat.Holder.iDN j (fun p : E × ℝ => seeleyCut (-(b m) * p.2)) (seLw W δ)
           * Work.CR.Flat.Holder.iDN (i - j) (fun p : E × ℝ => g (p.1, -(b m) * p.2))
               (seLw W δ))
        ≤ (i.choose j : ℝ≥0∞) *
            (ENNReal.ofReal ((b m) ^ j * seeleyCutB j)
              * (ENNReal.ofReal ((b m) ^ (i - j))
                  * Work.CR.Flat.Holder.iDN (i - j) g (seUp W))) :=
          mul_le_mul' le_rfl (mul_le_mul' (hχbnd j hj) (hΨbnd j hj))
      _ = ENNReal.ofReal ((i.choose j : ℝ) * ((b m) ^ j * seeleyCutB j * (b m) ^ (i - j)))
            * Work.CR.Flat.Holder.iDN (i - j) g (seUp W) := by
          rw [← ENNReal.ofReal_natCast (i.choose j),
            Work.NN.Seeley.ofReal_three_mul (Nat.cast_nonneg _)
              (mul_nonneg (pow_nonneg hbm j) hsc) (pow_nonneg hbm (i - j))]
      _ = ENNReal.ofReal ((b m) ^ i) *
          (ENNReal.ofReal ((i.choose j : ℝ) * seeleyCutB j)
            * Work.CR.Flat.Holder.iDN (i - j) g (seUp W)) := by
          rw [heq, ENNReal.ofReal_mul (pow_nonneg hbm i), mul_assoc]
  -- assemble
  calc ENNReal.ofReal ‖(a m) • Work.NN.Seeley.lsmulL‖ *
        (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
          (Work.CR.Flat.Holder.iDN j (fun p : E × ℝ => seeleyCut (-(b m) * p.2)) (seLw W δ)
           * Work.CR.Flat.Holder.iDN (i - j) (fun p : E × ℝ => g (p.1, -(b m) * p.2))
               (seLw W δ)))
      ≤ ENNReal.ofReal |a m| *
          (ENNReal.ofReal ((b m) ^ i) *
            (ENNReal.ofReal (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * seeleyCutB j)
              * (∑ j ∈ Finset.range (i + 1), Work.CR.Flat.Holder.iDN j g (seUp W)))) := by
        refine mul_le_mul' hBnd ?_
        calc (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
              (Work.CR.Flat.Holder.iDN j (fun p : E × ℝ => seeleyCut (-(b m) * p.2)) (seLw W δ)
               * Work.CR.Flat.Holder.iDN (i - j) (fun p : E × ℝ => g (p.1, -(b m) * p.2))
                   (seLw W δ)))
            ≤ ∑ j ∈ Finset.range (i + 1), ENNReal.ofReal ((b m) ^ i) *
                (ENNReal.ofReal ((i.choose j : ℝ) * seeleyCutB j)
                  * Work.CR.Flat.Holder.iDN (i - j) g (seUp W)) :=
              Finset.sum_le_sum hterm
          _ = ENNReal.ofReal ((b m) ^ i) *
                (∑ j ∈ Finset.range (i + 1),
                  ENNReal.ofReal ((i.choose j : ℝ) * seeleyCutB j)
                  * Work.CR.Flat.Holder.iDN (i - j) g (seUp W)) := by
              rw [Finset.mul_sum]
          _ ≤ ENNReal.ofReal ((b m) ^ i) *
                ((∑ j ∈ Finset.range (i + 1),
                    ENNReal.ofReal ((i.choose j : ℝ) * seeleyCutB j))
                  * (∑ j ∈ Finset.range (i + 1), Work.CR.Flat.Holder.iDN j g (seUp W))) := by
              refine mul_le_mul' le_rfl ?_
              exact sum_shift_le (n := i)
                (fun j => ENNReal.ofReal ((i.choose j : ℝ) * seeleyCutB j))
                (fun k => Work.CR.Flat.Holder.iDN k g (seUp W))
          _ = ENNReal.ofReal ((b m) ^ i) *
                (ENNReal.ofReal (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * seeleyCutB j)
                  * (∑ j ∈ Finset.range (i + 1), Work.CR.Flat.Holder.iDN j g (seUp W))) := by
              rw [ENNReal.ofReal_sum_of_nonneg
                (fun j _ => mul_nonneg (Nat.cast_nonneg _) (seeleyCutB_nonneg j))]
    _ = ENNReal.ofReal (|a m| * (b m) ^ i *
          (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * seeleyCutB j)) *
        (∑ j ∈ Finset.range (i + 1), Work.CR.Flat.Holder.iDN j g (seUp W)) := by
        rw [Work.NN.Seeley.ofReal_three_mul (abs_nonneg (a m)) (pow_nonneg hbm i) hSnn]
        congr 1
        ring_nf

end Work.NN.Final
