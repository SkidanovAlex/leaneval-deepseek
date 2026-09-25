import Mathlib
import Submission.Work.NN.Seeley.seeleyTV_hSN_le

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

set_option linter.unusedSectionVars false

namespace Work.NN.Seeley

open Work.NN.Final

set_option maxHeartbeats 1000000 in
theorem seeleyTV_hSN_le_uniform {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {δ : ℝ} (hδ : 0 < δ) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {a b : ℕ → ℝ}
    (hb1 : ∀ m, 1 ≤ b m) (i : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : X × ℝ → ℂ,
      (∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) g {p : X × ℝ | -δ < p.2}) →
      ∀ m : ℕ,
      Work.CR.Flat.Holder.hSN i α (Work.NN.Final.seeleyTV a b δ g m)
          {p : X × ℝ | -δ < p.2 ∧ p.2 < 0}
        ≤ ENNReal.ofReal (|a m| * (b m) ^ (i + 2) * C) *
            (∑ j ∈ Finset.range (i + 1),
              (Work.CR.Flat.Holder.iDN j g {p : X × ℝ | 0 < p.2}
                + Work.CR.Flat.Holder.hSN j α g {p : X × ℝ | 0 < p.2})) := by
  -- the constant
  set Mc : ℝ := ∑ j ∈ Finset.range (i + 1),
      (i.choose j : ℝ) * (2 * seeleyCutB j + seeleyCutB (j + 1) + seeleyCutB j) with hMc
  set M : ℝ := 1 + Mc with hM
  have hMc_nonneg : 0 ≤ Mc := by
    rw [hMc]
    refine Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) ?_
    have h1 := seeleyCutB_nonneg j
    have h2 := seeleyCutB_nonneg (j + 1)
    linarith
  have hMpos : 0 < M := by rw [hM]; linarith
  refine ⟨‖lsmulL‖ * M + 1, by linarith [mul_nonneg (norm_nonneg lsmulL) hMpos.le], ?_⟩
  intro g hg m
  -- the two open sets
  set Ω : Set (X × ℝ) := {p : X × ℝ | -δ < p.2 ∧ p.2 < 0} with hΩ
  set U : Set (X × ℝ) := {p : X × ℝ | 0 < p.2} with hU
  have hΩopen : IsOpen Ω := by
    rw [hΩ]
    exact (isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const)
  have hUopen : IsOpen U := by
    rw [hU]
    exact isOpen_lt continuous_const continuous_snd
  -- replace `hSN` by `gSN`, and `iDN`/`hSN` over the open set `U` by `gDN`/`gSN`
  rw [← gSN_eq_hSN hΩopen i α (seeleyTV a b δ g m)]
  have hS : (∑ j ∈ Finset.range (i + 1),
        (Work.CR.Flat.Holder.iDN j g U + Work.CR.Flat.Holder.hSN j α g U))
      = ∑ j ∈ Finset.range (i + 1), (gDN j g U + gSN j α g U) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← gDN_eq_iDN hUopen j g, ← gSN_eq_hSN hUopen j α g]
  rw [hS]
  -- the product decomposition
  set χ : X × ℝ → ℝ := fun p => seeleyCut (-(b m) * p.2) with hχ
  set Ψ : X × ℝ → ℂ := fun p => seeleyV δ g (p.1, -(b m) * p.2) with hΨ
  have hTV : seeleyTV a b δ g m = fun p : X × ℝ => ((a m) • lsmulL) (χ p) (Ψ p) := by
    funext p
    simp only [hχ, hΨ, seeleyTV, lsmulL, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.lsmul_apply, smul_smul]
  rw [hTV]
  -- smoothness
  have hχsmooth : ContDiff ℝ (i : WithTop ℕ∞) χ := by
    rw [hχ]
    have harg : ContDiff ℝ ∞ (fun p : X × ℝ => -(b m) * p.2) :=
      ContinuousLinearMap.contDiff ((-(b m)) • ContinuousLinearMap.snd ℝ X ℝ)
    exact (seeleyCut_contDiff.comp harg).of_le (by simp)
  have hΨsmooth : ContDiff ℝ (i : WithTop ℕ∞) Ψ := by
    rw [hΨ]
    have hv : ContDiff ℝ ∞ (seeleyV δ g) := seeleyV_contDiff hδ hg
    have hshear : ContDiff ℝ ∞ (fun p : X × ℝ => (p.1, -(b m) * p.2)) :=
      ContinuousLinearMap.contDiff (seeleyLam (X := X) (-(b m)))
    exact (hv.comp hshear).of_le (by simp)
  -- the bilinear Leibniz bound
  have hbil := gSN_bilinear_le ((a m) • lsmulL) i α hχsmooth hΨsmooth (Ω := Ω)
  refine hbil.trans ?_
  -- the four ingredient bounds
  have hχSN : ∀ j, j ≤ i → gSN j α χ Ω ≤
      ENNReal.ofReal ((b m) ^ ((j : ℝ) + 1 + α) * (2 * seeleyCutB j + seeleyCutB (j + 1))) := by
    intro j hj
    have hc : (1 : ℝ) ≤ |(-(b m))| := by
      rw [abs_neg, abs_of_nonneg (by linarith [hb1 m])]
      exact hb1 m
    have h := gSN_cutoff_le (X := X) (c := -(b m)) (i := j) (α := α) (Ω := Ω) hc hα hα1
    rw [hχ]
    refine h.trans (le_of_eq ?_)
    rw [abs_neg, abs_of_nonneg (by linarith [hb1 m])]
  have hχDN : ∀ j, j ≤ i → gDN j χ Ω ≤ ENNReal.ofReal ((b m) ^ j * seeleyCutB j) := by
    intro j hj
    have h := gDN_cutoff_le (X := X) (c := -(b m)) (i := j) (Ω := Ω)
    rw [hχ]
    refine h.trans (le_of_eq ?_)
    rw [abs_neg, abs_of_nonneg (by linarith [hb1 m])]
  have hΨDN : ∀ j, j ≤ i → gDN j Ψ Ω ≤ ENNReal.ofReal ((b m) ^ j) * gDN j g U := by
    intro j hj
    rw [hΨ]
    exact gDN_seeleyV_shear_le hδ hg (hb1 m) j
  have hΨSN : ∀ j, j ≤ i → gSN j α Ψ Ω ≤ ENNReal.ofReal ((b m) ^ ((j : ℝ) + α)) * gSN j α g U := by
    intro j hj
    rw [hΨ]
    exact gSN_seeleyV_shear_le hδ hg (hb1 m) j hα
  -- the coefficient bounds
  have hcoef : ∀ j ∈ Finset.range (i + 1),
      (i.choose j : ℝ) * (2 * seeleyCutB j + seeleyCutB (j + 1)) ≤ M ∧
      (i.choose j : ℝ) * seeleyCutB j ≤ M := by
    intro j hj
    have hle : (i.choose j : ℝ) *
        (2 * seeleyCutB j + seeleyCutB (j + 1) + seeleyCutB j) ≤ Mc := by
      rw [hMc]
      refine Finset.single_le_sum
        (f := fun k => (i.choose k : ℝ) *
          (2 * seeleyCutB k + seeleyCutB (k + 1) + seeleyCutB k)) ?_ hj
      intro k _
      refine mul_nonneg (by positivity) ?_
      have h1 := seeleyCutB_nonneg k
      have h2 := seeleyCutB_nonneg (k + 1)
      linarith
    have hsb := seeleyCutB_nonneg j
    have hsb' := seeleyCutB_nonneg (j + 1)
    have hcj : (0 : ℝ) ≤ (i.choose j : ℝ) := Nat.cast_nonneg _
    constructor
    · have h' : (i.choose j : ℝ) * (2 * seeleyCutB j + seeleyCutB (j + 1)) ≤
          (i.choose j : ℝ) * (2 * seeleyCutB j + seeleyCutB (j + 1) + seeleyCutB j) := by
        nlinarith [hcj, hsb]
      rw [hM]; linarith
    · have h' : (i.choose j : ℝ) * seeleyCutB j ≤
          (i.choose j : ℝ) * (2 * seeleyCutB j + seeleyCutB (j + 1) + seeleyCutB j) := by
        nlinarith [hcj, hsb, hsb']
      rw [hM]; linarith
  -- the term-by-term bound
  have hterm : ∀ j ∈ Finset.range (i + 1),
      (i.choose j : ENNReal) * (gSN j α χ Ω * gDN (i - j) Ψ Ω + gDN j χ Ω * gSN (i - j) α Ψ Ω)
      ≤ ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) *
          (gDN (i - j) g U + gSN (i - j) α g U) := by
    intro j hj
    have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hij : i - j ≤ i := Nat.sub_le i j
    obtain ⟨hcoefA, hcoefB⟩ := hcoef j hj
    have hb0 : (0 : ℝ) < b m := by linarith [hb1 m]
    have hbge : (1 : ℝ) ≤ b m := hb1 m
    have hbbE : 0 ≤ (b m) ^ ((i : ℝ) + 2) := Real.rpow_nonneg hb0.le _
    have hKnn : 0 ≤ 2 * seeleyCutB j + seeleyCutB (j + 1) := by
      have h1 := seeleyCutB_nonneg j
      have h2 := seeleyCutB_nonneg (j + 1)
      linarith
    have hA := hχSN j hji
    have hB := hΨDN (i - j) hij
    have hC := hχDN j hji
    have hD := hΨSN (i - j) hij
    have htermA : (i.choose j : ENNReal) * (gSN j α χ Ω * gDN (i - j) Ψ Ω)
        ≤ ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) * gDN (i - j) g U := by
      have hmain : (i.choose j : ENNReal) * (gSN j α χ Ω * gDN (i - j) Ψ Ω)
          ≤ ENNReal.ofReal ((i.choose j : ℝ) * ((b m) ^ ((j : ℝ) + 1 + α) *
                (2 * seeleyCutB j + seeleyCutB (j + 1)) * (b m) ^ (i - j)))
              * gDN (i - j) g U := by
        calc (i.choose j : ENNReal) * (gSN j α χ Ω * gDN (i - j) Ψ Ω)
            ≤ (i.choose j : ENNReal) *
                (ENNReal.ofReal ((b m) ^ ((j : ℝ) + 1 + α) *
                    (2 * seeleyCutB j + seeleyCutB (j + 1))) *
                  (ENNReal.ofReal ((b m) ^ (i - j)) * gDN (i - j) g U)) :=
              mul_le_mul' le_rfl (mul_le_mul' hA hB)
          _ = ENNReal.ofReal ((i.choose j : ℝ) * ((b m) ^ ((j : ℝ) + 1 + α) *
                    (2 * seeleyCutB j + seeleyCutB (j + 1)) * (b m) ^ (i - j)))
                * gDN (i - j) g U := by
              rw [← ENNReal.ofReal_natCast (i.choose j),
                ofReal_three_mul (Nat.cast_nonneg _) (mul_nonneg
                  (Real.rpow_nonneg hb0.le _) hKnn) (pow_nonneg hb0.le _) _]
      refine hmain.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
      have hpow : (b m) ^ ((j : ℝ) + 1 + α) * (b m) ^ (i - j) ≤ (b m) ^ ((i : ℝ) + 2) := by
        rw [real_rpow_mul_pow hb0 hji]
        refine Real.rpow_le_rpow_of_exponent_le hbge ?_
        have hji' : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast hji
        linarith
      calc (i.choose j : ℝ) * ((b m) ^ ((j : ℝ) + 1 + α) *
              (2 * seeleyCutB j + seeleyCutB (j + 1)) * (b m) ^ (i - j))
          = ((b m) ^ ((j : ℝ) + 1 + α) * (b m) ^ (i - j)) *
              ((i.choose j : ℝ) * (2 * seeleyCutB j + seeleyCutB (j + 1))) := by ring
        _ ≤ (b m) ^ ((i : ℝ) + 2) * M :=
            mul_le_mul hpow hcoefA (mul_nonneg (by positivity) hKnn) hbbE
    have htermB : (i.choose j : ENNReal) * (gDN j χ Ω * gSN (i - j) α Ψ Ω)
        ≤ ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) * gSN (i - j) α g U := by
      have hmain : (i.choose j : ENNReal) * (gDN j χ Ω * gSN (i - j) α Ψ Ω)
          ≤ ENNReal.ofReal ((i.choose j : ℝ) * ((b m) ^ j * seeleyCutB j *
                (b m) ^ (((i - j : ℕ) : ℝ) + α))) * gSN (i - j) α g U := by
        calc (i.choose j : ENNReal) * (gDN j χ Ω * gSN (i - j) α Ψ Ω)
            ≤ (i.choose j : ENNReal) *
                (ENNReal.ofReal ((b m) ^ j * seeleyCutB j) *
                  (ENNReal.ofReal ((b m) ^ (((i - j : ℕ) : ℝ) + α)) *
                    gSN (i - j) α g U)) :=
              mul_le_mul' le_rfl (mul_le_mul' hC hD)
          _ = ENNReal.ofReal ((i.choose j : ℝ) * ((b m) ^ j * seeleyCutB j *
                    (b m) ^ (((i - j : ℕ) : ℝ) + α))) * gSN (i - j) α g U := by
              rw [← ENNReal.ofReal_natCast (i.choose j),
                ofReal_three_mul (Nat.cast_nonneg _)
                  (mul_nonneg (pow_nonneg hb0.le _) (seeleyCutB_nonneg j))
                  (Real.rpow_nonneg hb0.le _) _]
      refine hmain.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
      have hpow : (b m) ^ j * (b m) ^ (((i - j : ℕ) : ℝ) + α) ≤ (b m) ^ ((i : ℝ) + 2) := by
        rw [real_pow_mul_rpow hb0 hji]
        refine Real.rpow_le_rpow_of_exponent_le hbge ?_
        linarith
      calc (i.choose j : ℝ) * ((b m) ^ j * seeleyCutB j * (b m) ^ (((i - j : ℕ) : ℝ) + α))
          = ((b m) ^ j * (b m) ^ (((i - j : ℕ) : ℝ) + α)) * ((i.choose j : ℝ) * seeleyCutB j) := by
            ring
        _ ≤ (b m) ^ ((i : ℝ) + 2) * M :=
            mul_le_mul hpow hcoefB (mul_nonneg (by positivity) (seeleyCutB_nonneg j)) hbbE
    calc (i.choose j : ENNReal) *
            (gSN j α χ Ω * gDN (i - j) Ψ Ω + gDN j χ Ω * gSN (i - j) α Ψ Ω)
        = (i.choose j : ENNReal) * (gSN j α χ Ω * gDN (i - j) Ψ Ω) +
            (i.choose j : ENNReal) * (gDN j χ Ω * gSN (i - j) α Ψ Ω) := by rw [mul_add]
      _ ≤ ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) * gDN (i - j) g U +
            ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) * gSN (i - j) α g U :=
          add_le_add htermA htermB
      _ = ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) *
            (gDN (i - j) g U + gSN (i - j) α g U) := by rw [← mul_add]
  -- the sum bound
  have hP : (∑ j ∈ Finset.range (i + 1), (i.choose j : ENNReal) *
        (gSN j α χ Ω * gDN (i - j) Ψ Ω + gDN j χ Ω * gSN (i - j) α Ψ Ω))
      ≤ ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) *
          (∑ j ∈ Finset.range (i + 1), (gDN j g U + gSN j α g U)) := by
    rw [← sum_range_sub_eq (fun k => gDN k g U + gSN k α g U) i]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hBmnorm : ‖(a m) • lsmulL‖ ≤ |a m| * ‖lsmulL‖ := by
    simpa only [Real.norm_eq_abs] using ContinuousLinearMap.opNorm_smul_le (a m) lsmulL
  have hbbE : 0 ≤ (b m) ^ ((i : ℝ) + 2) := Real.rpow_nonneg (by linarith [hb1 m]) _
  have hreal : (|a m| * ‖lsmulL‖) * ((b m) ^ ((i : ℝ) + 2) * M)
      ≤ |a m| * (b m) ^ (i + 2) * (‖lsmulL‖ * M + 1) := by
    rw [show (b m) ^ (i + 2) = (b m) ^ ((i : ℝ) + 2) from by
      rw [← Real.rpow_natCast (b m) (i + 2),
        show ((i + 2 : ℕ) : ℝ) = (i : ℝ) + 2 by push_cast; ring]]
    have hkey : (|a m| * ‖lsmulL‖) * ((b m) ^ ((i : ℝ) + 2) * M)
        = |a m| * (b m) ^ ((i : ℝ) + 2) * (‖lsmulL‖ * M) := by ring
    rw [hkey]
    exact mul_le_mul_of_nonneg_left (by linarith)
      (mul_nonneg (abs_nonneg _) hbbE)
  calc ENNReal.ofReal ‖(a m) • lsmulL‖ *
        (∑ j ∈ Finset.range (i + 1), (i.choose j : ENNReal) *
          (gSN j α χ Ω * gDN (i - j) Ψ Ω + gDN j χ Ω * gSN (i - j) α Ψ Ω))
      ≤ ENNReal.ofReal ‖(a m) • lsmulL‖ *
          (ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) *
            (∑ j ∈ Finset.range (i + 1), (gDN j g U + gSN j α g U))) :=
        mul_le_mul' le_rfl hP
    _ ≤ ENNReal.ofReal (|a m| * ‖lsmulL‖) *
          (ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) *
            (∑ j ∈ Finset.range (i + 1), (gDN j g U + gSN j α g U))) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hBmnorm) le_rfl
    _ = ENNReal.ofReal ((|a m| * ‖lsmulL‖) * ((b m) ^ ((i : ℝ) + 2) * M)) *
          (∑ j ∈ Finset.range (i + 1), (gDN j g U + gSN j α g U)) :=
        ofReal_mul_ofReal_mul (mul_nonneg (abs_nonneg (a m)) (norm_nonneg lsmulL))
          (mul_nonneg hbbE hMpos.le) _
    _ ≤ ENNReal.ofReal (|a m| * (b m) ^ (i + 2) * (‖lsmulL‖ * M + 1)) *
          (∑ j ∈ Finset.range (i + 1), (gDN j g U + gSN j α g U)) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl
end Work.NN.Seeley
