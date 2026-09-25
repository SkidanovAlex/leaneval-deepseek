import Mathlib
import Submission.Work.NN.Seeley.Setup
import Submission.Work.NN.Seeley.ProdBounds
import Submission.Work.NN.Seeley.Glob
import Submission.Work.NN.Seeley.gDN_bilinear_le

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

namespace Work.NN.Seeley

open Work.NN.Final
open Work.CR.Flat.Holder

/-- Real scalar multiplication viewed as a bilinear map scaled by `k`: `(r, z) ↦ (k * r) • z`. -/
def seeleyScalarBilin (k : ℝ) : ℝ →L[ℝ] ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.lsmul ℝ ℝ).comp (k • ContinuousLinearMap.id ℝ ℝ)

@[simp] lemma seeleyScalarBilin_apply (k r : ℝ) (z : ℂ) : seeleyScalarBilin k r z = (k * r) • z := by
  simp only [seeleyScalarBilin, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]

lemma norm_seeleyScalarBilin_le (k : ℝ) : ‖seeleyScalarBilin k‖ ≤ |k| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg k) fun r => ?_
  show ‖(seeleyScalarBilin k r : ℂ →L[ℝ] ℂ)‖ ≤ |k| * ‖r‖
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
  rw [seeleyScalarBilin_apply]
  calc ‖(k * r) • z‖ ≤ ‖(k * r : ℝ)‖ * ‖z‖ := norm_smul_le _ _
    _ = (|k| * ‖r‖) * ‖z‖ := by rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]

/-- Sup-norm bound for the `m`-th Seeley term over the open lower slab, with a constant uniform
in `m` (the explicit `m`-dependence is `|a m| * (b m)^i`).  Suggested proof: write
`seeleyTV a b δ g m p = (a m) • ((seeleyCut (-(b m) * p.2)) • seeleyV δ g (p.1, -(b m) * p.2))`,
use `iDN_bilinear_le` (`Work.CR.Flat.Holder`) with the scalar-multiplication bilinear map for the
two scalar multiplications, `gDN_cutoff_le` (from `ProdBounds`) for the cutoff factor and
`gDN_comp_prod_snd_le` (from `ProdBounds`) for the shear, together with `gDN_eq_iDN` on the open
lower slab and the fact that the shear image of the lower slab is contained in the open upper
half space, where `seeleyV δ g = g`.  The `m`-dependence collects to `|a m| * (b m)^i`. -/
theorem seeleyTV_iDN_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {δ : ℝ} (hδ : 0 < δ) {a b : ℕ → ℝ} (hb1 : ∀ m, 1 ≤ b m) {g : X × ℝ → ℂ}
    (hg : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) g {p : X × ℝ | -δ < p.2}) (i : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
      Work.CR.Flat.Holder.iDN i (Work.NN.Final.seeleyTV a b δ g m)
          {p : X × ℝ | -δ < p.2 ∧ p.2 < 0}
        ≤ ENNReal.ofReal (|a m| * (b m) ^ i * C) *
            (∑ j ∈ Finset.range (i + 1),
              Work.CR.Flat.Holder.iDN j g {p : X × ℝ | 0 < p.2}) := by
  set K : ℝ := ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * seeleyCutB j with hK
  have hKnonneg : 0 ≤ K := by
    rw [hK]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (seeleyCutB_nonneg j)
  refine ⟨K + 1, by linarith, fun m => ?_⟩
  set c : ℝ := -(b m) with hc
  have hbm1 : (1 : ℝ) ≤ b m := hb1 m
  have hbpos : (0 : ℝ) < b m := lt_of_lt_of_le one_pos hbm1
  have habs : |c| = b m := by rw [hc, abs_neg, abs_of_nonneg hbpos.le]
  have hmaxc : max 1 |c| = b m := by rw [habs]; exact max_eq_right hbm1
  set Ω : Set (X × ℝ) := {p : X × ℝ | -δ < p.2 ∧ p.2 < 0} with hΩdef
  set U : Set (X × ℝ) := {p : X × ℝ | 0 < p.2} with hUdef
  have hΩ : IsOpen Ω := by
    rw [hΩdef]
    exact (isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const)
  have hU : IsOpen U := by
    rw [hUdef]
    exact isOpen_lt continuous_const continuous_snd
  set S : ℝ≥0∞ := ∑ j ∈ Finset.range (i + 1), iDN j g U with hS
  have hGle : ∀ k, k ≤ i → iDN k g U ≤ S := by
    intro k hk
    rw [hS]
    exact Finset.single_le_sum (s := Finset.range (i + 1)) (f := fun j => iDN j g U)
      (fun j _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  -- continuity of the two factors
  have hφcont : ContDiff ℝ (i : WithTop ℕ∞) (fun p : X × ℝ => seeleyCut (c * p.2)) := by
    have h2 : ContDiff ℝ ∞ (fun p : X × ℝ => c * p.2) := by fun_prop
    exact (seeleyCut_contDiff.comp h2).of_le (by simp)
  have hψcont : ContDiff ℝ (i : WithTop ℕ∞)
      (fun p : X × ℝ => seeleyV δ g (p.1, c * p.2)) := by
    have hV : ContDiff ℝ (i : WithTop ℕ∞) (seeleyV δ g) := seeleyV_contDiff_fin hδ hg i
    exact hV.comp_continuousLinearMap (g := seeleyLam (X := X) c)
  -- the cutoff factor
  have hA : ∀ j, gDN j (fun p : X × ℝ => seeleyCut (c * p.2)) Ω
      ≤ ENNReal.ofReal ((b m) ^ j * seeleyCutB j) := by
    intro j
    have h := gDN_cutoff_le (X := X) (c := c) (i := j) (Ω := Ω)
    rwa [habs] at h
  -- the sheared localised function
  have hB : ∀ k, gDN k (fun p : X × ℝ => seeleyV δ g (p.1, c * p.2)) Ω
      ≤ ENNReal.ofReal ((b m) ^ k) * iDN k g U := by
    intro k
    have himage : (fun p : X × ℝ => (p.1, c * p.2)) '' Ω ⊆ U := by
      rintro q ⟨p, hp, rfl⟩
      rw [hΩdef] at hp
      rw [hUdef]
      show 0 < c * p.2
      rw [hc]
      have hp2 : p.2 < 0 := hp.2
      nlinarith [hbm1]
    have hcomp := gDN_comp_prod_snd_le (X := X) (c := c) (i := k)
      (seeleyV_contDiff_fin hδ hg k) (Ω := Ω)
    calc gDN k (fun p : X × ℝ => seeleyV δ g (p.1, c * p.2)) Ω
        ≤ ENNReal.ofReal ((max 1 |c|) ^ k) * gDN k (seeleyV δ g)
            ((fun p : X × ℝ => (p.1, c * p.2)) '' Ω) := hcomp
      _ = ENNReal.ofReal ((b m) ^ k) * gDN k (seeleyV δ g)
            ((fun p : X × ℝ => (p.1, c * p.2)) '' Ω) := by rw [hmaxc]
      _ ≤ ENNReal.ofReal ((b m) ^ k) * gDN k (seeleyV δ g) U := by
          refine mul_le_mul_of_nonneg_left ?_ bot_le
          exact gDN_mono himage k (seeleyV δ g)
      _ = ENNReal.ofReal ((b m) ^ k) * iDN k g U := by
          have h1 : gDN k (seeleyV δ g) U = iDN k g U := by
            rw [gDN_congr_of_isOpen hU (fun q hq => ?_), gDN_eq_iDN hU k g]
            have hq' : 0 < q.2 := by rwa [hUdef] at hq
            exact seeleyV_eq δ g (hδ := hδ) (by linarith)
          rw [h1]
  -- the bilinear (Leibniz) bound
  set T : ℝ≥0∞ := ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
      (gDN j (fun p : X × ℝ => seeleyCut (c * p.2)) Ω *
        gDN (i - j) (fun p : X × ℝ => seeleyV δ g (p.1, c * p.2)) Ω) with hTdef
  have hbil : gDN i (fun p : X × ℝ =>
        seeleyScalarBilin (a m) (seeleyCut (c * p.2)) (seeleyV δ g (p.1, c * p.2))) Ω
      ≤ ENNReal.ofReal ‖seeleyScalarBilin (a m)‖ * T := by
    rw [hTdef]
    exact gDN_bilinear_le (seeleyScalarBilin (a m)) i hφcont hψcont
  -- arithmetic on the sum
  have hsum1 : T ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
      (ENNReal.ofReal ((b m) ^ j * seeleyCutB j) *
        (ENNReal.ofReal ((b m) ^ (i - j)) * iDN (i - j) g U)) := by
    rw [hTdef]
    refine Finset.sum_le_sum fun j _ => ?_
    exact mul_le_mul' le_rfl (mul_le_mul' (hA j) (hB (i - j)))
  have hsum2 : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
      (ENNReal.ofReal ((b m) ^ j * seeleyCutB j) *
        (ENNReal.ofReal ((b m) ^ (i - j)) * iDN (i - j) g U)))
      ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
        (ENNReal.ofReal ((b m) ^ i * seeleyCutB j) * S) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hjle : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hpow : ((b m) ^ j * seeleyCutB j) * (b m) ^ (i - j) = (b m) ^ i * seeleyCutB j := by
      calc ((b m) ^ j * seeleyCutB j) * (b m) ^ (i - j)
          = seeleyCutB j * ((b m) ^ j * (b m) ^ (i - j)) := by ring
        _ = seeleyCutB j * (b m) ^ (j + (i - j)) := by rw [pow_add]
        _ = seeleyCutB j * (b m) ^ i := by rw [Nat.add_sub_cancel' hjle]
        _ = (b m) ^ i * seeleyCutB j := by ring
    have hstep : ENNReal.ofReal ((b m) ^ j * seeleyCutB j) *
          (ENNReal.ofReal ((b m) ^ (i - j)) * iDN (i - j) g U)
        = ENNReal.ofReal ((b m) ^ i * seeleyCutB j) * iDN (i - j) g U := by
      rw [← mul_assoc,
        ← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hbpos.le j) (seeleyCutB_nonneg j)), hpow]
    calc (i.choose j : ℝ≥0∞) * (ENNReal.ofReal ((b m) ^ j * seeleyCutB j) *
            (ENNReal.ofReal ((b m) ^ (i - j)) * iDN (i - j) g U))
        = (i.choose j : ℝ≥0∞) * (ENNReal.ofReal ((b m) ^ i * seeleyCutB j) *
              iDN (i - j) g U) := by rw [hstep]
      _ ≤ (i.choose j : ℝ≥0∞) * (ENNReal.ofReal ((b m) ^ i * seeleyCutB j) * S) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl (hGle (i - j) (Nat.sub_le i j)))
  have hsum3 : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
        (ENNReal.ofReal ((b m) ^ i * seeleyCutB j) * S))
      = (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
          ENNReal.ofReal ((b m) ^ i * seeleyCutB j)) * S := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsum4 : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
        ENNReal.ofReal ((b m) ^ i * seeleyCutB j)) = ENNReal.ofReal ((b m) ^ i * K) := by
    have hstep : ∀ j, (i.choose j : ℝ≥0∞) * ENNReal.ofReal ((b m) ^ i * seeleyCutB j)
        = ENNReal.ofReal ((i.choose j : ℝ) * ((b m) ^ i * seeleyCutB j)) := by
      intro j
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    rw [Finset.sum_congr rfl (fun j _ => hstep j),
      ← ENNReal.ofReal_sum_of_nonneg (fun j _ =>
        mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (pow_nonneg hbpos.le i) (seeleyCutB_nonneg j))), hK]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hT : T ≤ ENNReal.ofReal ((b m) ^ i * K) * S := by
    refine hsum1.trans (hsum2.trans (hsum3.le.trans ?_))
    rw [hsum4]
  -- the Seeley term is the bilinear expression
  have hTV : seeleyTV a b δ g m = fun p : X × ℝ =>
      seeleyScalarBilin (a m) (seeleyCut (c * p.2)) (seeleyV δ g (p.1, c * p.2)) := by
    funext p
    simp only [seeleyTV, seeleyScalarBilin_apply, hc, smul_smul]
  calc iDN i (seeleyTV a b δ g m) Ω
      = gDN i (seeleyTV a b δ g m) Ω := (gDN_eq_iDN hΩ i _).symm
    _ = gDN i (fun p : X × ℝ =>
          seeleyScalarBilin (a m) (seeleyCut (c * p.2)) (seeleyV δ g (p.1, c * p.2))) Ω := by rw [hTV]
    _ ≤ ENNReal.ofReal ‖seeleyScalarBilin (a m)‖ * T := hbil
    _ ≤ ENNReal.ofReal |a m| * T :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (norm_seeleyScalarBilin_le (a m))) le_rfl
    _ ≤ ENNReal.ofReal |a m| * (ENNReal.ofReal ((b m) ^ i * K) * S) :=
        mul_le_mul' le_rfl hT
    _ = ENNReal.ofReal (|a m| * (b m) ^ i * K) * S := by
        rw [show (|a m| * (b m) ^ i * K) = |a m| * ((b m) ^ i * K) from by ring,
          ENNReal.ofReal_mul (abs_nonneg (a m)), mul_assoc]
    _ ≤ ENNReal.ofReal (|a m| * (b m) ^ i * (K + 1)) * S := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        have h1 : (0:ℝ) ≤ |a m| := abs_nonneg _
        have h2 : (0:ℝ) ≤ (b m) ^ i := pow_nonneg hbpos.le i
        exact mul_le_mul_of_nonneg_left (by linarith : K ≤ K + 1) (mul_nonneg h1 h2)

end Work.NN.Seeley
