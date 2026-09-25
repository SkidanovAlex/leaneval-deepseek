import Mathlib
import Submission.Work.NN.Final.SeeleyLoc
import Submission.Work.NN.Final.seeleyLoc_term_gSN_le

noncomputable section

open scoped NNReal ENNReal ContDiff Topology BigOperators
open Set Filter

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.NN.Final

open Work.CR.Flat.Holder

/-- Uniform-in-`W`, `δ`, `g` Hölder-seminorm bound for the `i`-th iterated derivative of the `m`-th Seeley term on the open lower slab `seLw W δ`.  Same as `seeleyLoc_term_gSN_le` but with the constant chosen before `W`, `δ` and `g`, which is what a caller needs in order to build a single constant valid for all `g`. -/
theorem seeleyLoc_term_gSN_le_uniform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℕ → ℝ} (hb1 : ∀ m, 1 ≤ b m) {i : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : Set E), IsOpen W → ∀ (δ : ℝ) (g : E × ℝ → ℂ),
      ContDiffOn ℝ (i : WithTop ENat) g (seHp W) → ∀ m : ℕ,
      Work.NN.Final.gSN i α (seeleyTerm a b g m) (seLw W δ)
        ≤ ENNReal.ofReal (|a m| * (b m) ^ (i + 2) * C)
          * (∑ j ∈ Finset.range (i + 1),
              (Work.CR.Flat.Holder.iDN j g (seUp W) + Work.CR.Flat.Holder.hSN j α g (seUp W))) := by
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
  refine ⟨M + 1, by linarith, ?_⟩
  intro W hW δ g hg m
  set Ω : Set (E × ℝ) := seLw W δ with hΩdef
  set U : Set (E × ℝ) := seUp W with hUdef
  have hΩopen : IsOpen Ω := by rw [hΩdef]; exact isOpen_seLw hW δ
  have hUopen : IsOpen U := by rw [hUdef]; exact isOpen_seUp hW
  have hΩuniv : UniqueDiffOn ℝ Ω := hΩopen.uniqueDiffOn
  have hgU : ContDiffOn ℝ (i : WithTop ENat) g U := by
    rw [hUdef]
    exact hg.mono seUp_subset_seHp
  -- replace the `hSN`/`iDN` pair on the open set `U` by `gSN`/`gDN`
  rw [gSN_eq_hSN hΩopen i α (seeleyTerm a b g m)]
  have hS : (∑ j ∈ Finset.range (i + 1),
        (Work.CR.Flat.Holder.iDN j g U + Work.CR.Flat.Holder.hSN j α g U))
      = ∑ j ∈ Finset.range (i + 1), (gDN j g U + gSN j α g U) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← gDN_eq_iDN hUopen j g, ← gSN_eq_hSN hUopen j α g]
  rw [hS]
  -- the product decomposition of the `m`-th term
  set χ : E × ℝ → ℝ := fun p => seeleyCut (-(b m) * p.2) with hχ
  set Ψ : E × ℝ → ℂ := fun p => g (p.1, -(b m) * p.2) with hΨ
  have hTV : seeleyTerm a b g m = fun p : E × ℝ => (a m) • ((χ p) • (Ψ p)) := by
    funext p
    simp only [hχ, hΨ, seeleyTerm, Complex.real_smul]
  rw [hTV]
  -- smoothness of the two factors on the open set `Ω`
  have hχsmooth : ContDiff ℝ (i : WithTop ENat) χ := by
    rw [hχ]
    have harg : ContDiff ℝ ∞ (fun p : E × ℝ => -(b m) * p.2) :=
      ContinuousLinearMap.contDiff ((-(b m)) • ContinuousLinearMap.snd ℝ E ℝ)
    exact (seeleyCut_contDiff.comp harg).of_le (by simp)
  have hχOn : ContDiffOn ℝ (i : WithTop ENat) χ Ω := hχsmooth.contDiffOn
  have hΨOn : ContDiffOn ℝ (i : WithTop ENat) Ψ Ω := by
    rw [hΨ]
    have hshear : ContDiffOn ℝ (i : WithTop ENat) (fun p : E × ℝ => (p.1, -(b m) * p.2)) Ω :=
      ((ContinuousLinearMap.contDiff (seeleyLam (X := E) (-(b m)))).of_le le_top).contDiffOn
    have hsub : Set.MapsTo (fun p : E × ℝ => (p.1, -(b m) * p.2)) Ω U := fun p hp => by
      rw [hΩdef] at hp
      simp only [mem_seLw] at hp
      rw [hUdef]
      simp only [mem_seUp]
      exact ⟨hp.1, by nlinarith [hp.2.2, hb1 m]⟩
    exact hgU.comp hshear hsub
  -- the bilinear Leibniz bound
  have hbil := hSN_smul_mul_le (α := α) (c := a m) hχOn hΨOn hΩuniv
  refine hbil.trans ?_
  -- the four ingredient bounds
  have hχSN : ∀ j, j ≤ i → hSN j α χ Ω ≤
      ENNReal.ofReal ((b m) ^ ((j : ℝ) + 1 + α) * (2 * seeleyCutB j + seeleyCutB (j + 1))) := by
    intro j _
    have hc : (1 : ℝ) ≤ |(-(b m))| := by
      rw [abs_neg, abs_of_nonneg (by linarith [hb1 m])]
      exact hb1 m
    have h := Work.NN.Seeley.gSN_cutoff_le (X := E) (c := -(b m)) (i := j) (α := α) (Ω := Ω)
      hc hα hα1
    rw [← gSN_eq_hSN hΩopen j α χ, hχ]
    refine h.trans (le_of_eq ?_)
    rw [abs_neg, abs_of_nonneg (by linarith [hb1 m])]
  have hχDN : ∀ j, j ≤ i → iDN j χ Ω ≤ ENNReal.ofReal ((b m) ^ j * seeleyCutB j) := by
    intro j _
    have h := Work.NN.Final.gDN_cutoff_le (X := E) (c := -(b m)) (i := j) (Ω := Ω)
    rw [← gDN_eq_iDN hΩopen j χ, hχ]
    refine h.trans (le_of_eq ?_)
    rw [abs_neg, abs_of_nonneg (by linarith [hb1 m])]
  have hΨDN : ∀ j, j ≤ i → iDN j Ψ Ω ≤ ENNReal.ofReal ((b m) ^ j) * gDN j g U := by
    intro j hj
    have hc : (1 : ℝ) ≤ |(-(b m))| := by
      rw [abs_neg, abs_of_nonneg (by linarith [hb1 m])]
      exact hb1 m
    have hsub : (fun p : E × ℝ => (p.1, (-(b m)) * p.2)) '' Ω ⊆ U := by
      rw [hΩdef, hUdef]
      exact shear_image_seLw_subset_seUp (W := W) (δ := δ) (by linarith [hb1 m])
    have h := gDN_comp_shear_le (E := E) (c := -(b m)) hc (A := U) (Ω := Ω) hUopen hΩopen hsub
      (u := g) (hgU.of_le (Nat.cast_le.mpr hj))
    rw [← gDN_eq_iDN hΩopen j Ψ, hΨ]
    refine h.trans (le_of_eq ?_)
    rw [abs_neg, abs_of_nonneg (by linarith [hb1 m])]
  have hΨSN : ∀ j, j ≤ i → hSN j α Ψ Ω ≤ ENNReal.ofReal ((b m) ^ ((j : ℝ) + α)) * gSN j α g U := by
    intro j hj
    have hc : (1 : ℝ) ≤ |(-(b m))| := by
      rw [abs_neg, abs_of_nonneg (by linarith [hb1 m])]
      exact hb1 m
    have hsub : (fun p : E × ℝ => (p.1, (-(b m)) * p.2)) '' Ω ⊆ U := by
      rw [hΩdef, hUdef]
      exact shear_image_seLw_subset_seUp (W := W) (δ := δ) (by linarith [hb1 m])
    have h := gSN_comp_shear_le (E := E) (c := -(b m)) hc hα (A := U) (Ω := Ω) hUopen hΩopen hsub
      (u := g) (hgU.of_le (Nat.cast_le.mpr hj))
    rw [← gSN_eq_hSN hΩopen j α Ψ, hΨ]
    refine h.trans (le_of_eq ?_)
    rw [abs_neg, abs_of_nonneg (by linarith [hb1 m])]
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
      (i.choose j : ℝ≥0∞) * (hSN j α χ Ω * iDN (i - j) Ψ Ω + iDN j χ Ω * hSN (i - j) α Ψ Ω)
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
    have htermA : (i.choose j : ℝ≥0∞) * (hSN j α χ Ω * iDN (i - j) Ψ Ω)
        ≤ ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) * gDN (i - j) g U := by
      have hmain : (i.choose j : ℝ≥0∞) * (hSN j α χ Ω * iDN (i - j) Ψ Ω)
          ≤ ENNReal.ofReal ((i.choose j : ℝ) * ((b m) ^ ((j : ℝ) + 1 + α) *
                (2 * seeleyCutB j + seeleyCutB (j + 1)) * (b m) ^ (i - j)))
              * gDN (i - j) g U := by
        calc (i.choose j : ℝ≥0∞) * (hSN j α χ Ω * iDN (i - j) Ψ Ω)
            ≤ (i.choose j : ℝ≥0∞) *
                (ENNReal.ofReal ((b m) ^ ((j : ℝ) + 1 + α) *
                    (2 * seeleyCutB j + seeleyCutB (j + 1))) *
                  (ENNReal.ofReal ((b m) ^ (i - j)) * gDN (i - j) g U)) :=
              mul_le_mul' le_rfl (mul_le_mul' hA hB)
          _ = ENNReal.ofReal ((i.choose j : ℝ) * ((b m) ^ ((j : ℝ) + 1 + α) *
                    (2 * seeleyCutB j + seeleyCutB (j + 1)) * (b m) ^ (i - j)))
                * gDN (i - j) g U := by
              rw [← ENNReal.ofReal_natCast (i.choose j),
                Work.NN.Seeley.ofReal_three_mul (Nat.cast_nonneg _) (mul_nonneg
                  (Real.rpow_nonneg hb0.le _) hKnn) (pow_nonneg hb0.le _) _]
      refine hmain.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
      have hpow : (b m) ^ ((j : ℝ) + 1 + α) * (b m) ^ (i - j) ≤ (b m) ^ ((i : ℝ) + 2) := by
        rw [Work.NN.Seeley.real_rpow_mul_pow hb0 hji]
        refine Real.rpow_le_rpow_of_exponent_le hbge ?_
        have hji' : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast hji
        linarith
      calc (i.choose j : ℝ) * ((b m) ^ ((j : ℝ) + 1 + α) *
              (2 * seeleyCutB j + seeleyCutB (j + 1)) * (b m) ^ (i - j))
          = ((b m) ^ ((j : ℝ) + 1 + α) * (b m) ^ (i - j)) *
              ((i.choose j : ℝ) * (2 * seeleyCutB j + seeleyCutB (j + 1))) := by ring
        _ ≤ (b m) ^ ((i : ℝ) + 2) * M :=
            mul_le_mul hpow hcoefA (mul_nonneg (by positivity) hKnn) hbbE
    have htermB : (i.choose j : ℝ≥0∞) * (iDN j χ Ω * hSN (i - j) α Ψ Ω)
        ≤ ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) * gSN (i - j) α g U := by
      have hmain : (i.choose j : ℝ≥0∞) * (iDN j χ Ω * hSN (i - j) α Ψ Ω)
          ≤ ENNReal.ofReal ((i.choose j : ℝ) * ((b m) ^ j * seeleyCutB j *
                (b m) ^ (((i - j : ℕ) : ℝ) + α))) * gSN (i - j) α g U := by
        calc (i.choose j : ℝ≥0∞) * (iDN j χ Ω * hSN (i - j) α Ψ Ω)
            ≤ (i.choose j : ℝ≥0∞) *
                (ENNReal.ofReal ((b m) ^ j * seeleyCutB j) *
                  (ENNReal.ofReal ((b m) ^ (((i - j : ℕ) : ℝ) + α)) *
                    gSN (i - j) α g U)) :=
              mul_le_mul' le_rfl (mul_le_mul' hC hD)
          _ = ENNReal.ofReal ((i.choose j : ℝ) * ((b m) ^ j * seeleyCutB j *
                    (b m) ^ (((i - j : ℕ) : ℝ) + α))) * gSN (i - j) α g U := by
              rw [← ENNReal.ofReal_natCast (i.choose j),
                Work.NN.Seeley.ofReal_three_mul (Nat.cast_nonneg _)
                  (mul_nonneg (pow_nonneg hb0.le _) (seeleyCutB_nonneg j))
                  (Real.rpow_nonneg hb0.le _) _]
      refine hmain.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
      have hpow : (b m) ^ j * (b m) ^ (((i - j : ℕ) : ℝ) + α) ≤ (b m) ^ ((i : ℝ) + 2) := by
        rw [Work.NN.Seeley.real_pow_mul_rpow hb0 hji]
        refine Real.rpow_le_rpow_of_exponent_le hbge ?_
        linarith
      calc (i.choose j : ℝ) * ((b m) ^ j * seeleyCutB j * (b m) ^ (((i - j : ℕ) : ℝ) + α))
          = ((b m) ^ j * (b m) ^ (((i - j : ℕ) : ℝ) + α)) * ((i.choose j : ℝ) * seeleyCutB j) := by
            ring
        _ ≤ (b m) ^ ((i : ℝ) + 2) * M :=
            mul_le_mul hpow hcoefB (mul_nonneg (by positivity) (seeleyCutB_nonneg j)) hbbE
    calc (i.choose j : ℝ≥0∞) *
            (hSN j α χ Ω * iDN (i - j) Ψ Ω + iDN j χ Ω * hSN (i - j) α Ψ Ω)
        = (i.choose j : ℝ≥0∞) * (hSN j α χ Ω * iDN (i - j) Ψ Ω) +
            (i.choose j : ℝ≥0∞) * (iDN j χ Ω * hSN (i - j) α Ψ Ω) := by rw [mul_add]
      _ ≤ ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) * gDN (i - j) g U +
            ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) * gSN (i - j) α g U :=
          add_le_add htermA htermB
      _ = ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) *
            (gDN (i - j) g U + gSN (i - j) α g U) := by rw [← mul_add]
  -- the sum bound
  have hP : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
        (hSN j α χ Ω * iDN (i - j) Ψ Ω + iDN j χ Ω * hSN (i - j) α Ψ Ω))
      ≤ ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) *
          (∑ j ∈ Finset.range (i + 1), (gDN j g U + gSN j α g U)) := by
    rw [← Work.NN.Seeley.sum_range_sub_eq (fun k => gDN k g U + gSN k α g U) i]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  -- the numerical comparison
  have hb0 : (0 : ℝ) < b m := by linarith [hb1 m]
  have hbbE : 0 ≤ (b m) ^ ((i : ℝ) + 2) := Real.rpow_nonneg hb0.le _
  have hreal : |a m| * ((b m) ^ ((i : ℝ) + 2) * M) ≤ |a m| * (b m) ^ (i + 2) * (M + 1) := by
    rw [show (b m) ^ (i + 2) = (b m) ^ ((i : ℝ) + 2) from by
      rw [← Real.rpow_natCast (b m) (i + 2),
        show ((i + 2 : ℕ) : ℝ) = (i : ℝ) + 2 by push_cast; ring]]
    calc |a m| * ((b m) ^ ((i : ℝ) + 2) * M)
        = |a m| * (b m) ^ ((i : ℝ) + 2) * M := by ring
      _ ≤ |a m| * (b m) ^ ((i : ℝ) + 2) * (M + 1) := by
          refine mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (abs_nonneg _) hbbE)
  calc ENNReal.ofReal |a m| * (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
          (hSN j α χ Ω * iDN (i - j) Ψ Ω + iDN j χ Ω * hSN (i - j) α Ψ Ω))
      ≤ ENNReal.ofReal |a m| * (ENNReal.ofReal ((b m) ^ ((i : ℝ) + 2) * M) *
          (∑ j ∈ Finset.range (i + 1), (gDN j g U + gSN j α g U))) :=
        mul_le_mul' le_rfl hP
    _ = ENNReal.ofReal (|a m| * ((b m) ^ ((i : ℝ) + 2) * M)) *
          (∑ j ∈ Finset.range (i + 1), (gDN j g U + gSN j α g U)) :=
        Work.NN.Seeley.ofReal_mul_ofReal_mul (abs_nonneg _) (mul_nonneg hbbE hMpos.le) _
    _ ≤ ENNReal.ofReal (|a m| * (b m) ^ (i + 2) * (M + 1)) *
          (∑ j ∈ Finset.range (i + 1), (gDN j g U + gSN j α g U)) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl


end Work.NN.Final
