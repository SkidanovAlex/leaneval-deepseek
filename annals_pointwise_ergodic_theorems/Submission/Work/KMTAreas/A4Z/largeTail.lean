/-
# Area A4Z: the large-`N` branch of `lipTwoGenTail`, with the spatial tail clauses

`Work.KMTAreas.A4Z.LargeTailBranch P` is the unscaled large-`N` branch of Proposition `lip-2`
(the paper's §5.2) *with* the two spatial tail clauses needed by the Hahn step of Corollary
`struct-dual`: the `ℓ¹`-fringe at the input's window `[-A N^d, A N^d]` and the `ℓ²`-tail beyond
every `R N^d`.

The proof is the §5.2 chain of `Submission/Work/KMTAreas/A4/lip2Gen.lean` (`lip2Gen_mainCase`)
with two modifications:

* the projection back to `g` is performed with `Work.KMTAreas.A4Z.projectionAll`, which exposes
  the explicit windowed convolution `G₀ = star (win M s * g)` together with its `ℓ¹`-fringe
  `≤ C M` at the window `A N^d` and its `ℓ²`-tail `≤ C² R^{-1} N^d`; the chain's own
  `Work.KMTAreas.A4.massToG` returns an *existential* `G` and therefore says nothing about its
  spatial tails;
* the *arc level* `k` reported in the conclusion is chosen at the *top* of the admissible range
  `2^k ≤ Ck δ^{-(c+1)}/N^d`.  This makes the projection window `M = max 2 (2^{-k})` large, hence
  the explicit `ℓ¹`-fringe `≤ C M ≲ δ^{c+1} N^d` — which is what makes the fringe clause hold
  with the *same* `D, c` as the correlation clause.
-/
import Mathlib
import Submission.Work.KMTAreas.A4Z.glue
import Submission.Work.KMTAreas.A4Z.projectionSelf
import Submission.Work.KMTAreas.A4Z.chain.arcCorrelation
import Submission.Work.KMTAreas.A4.lip2GenWeyl
import Submission.Work.KMTAreas.A4.lip2GenArcMassA
import Submission.Work.KMTAreas.A4.lip2GenSavg
import Submission.Work.KMTAreas.A4.lip2GenWindowTail
import Submission.Work.KMTAreas.A4.lip2GenNumericB
import Submission.Work.KMTAreas.A4.lip2GenTailArith
import Submission.Work.KMTAreas.A4.lip2GenMuArith

set_option autoImplicit false
set_option maxHeartbeats 25000000

open scoped BigOperators
open Polynomial
open Work.Analysis.InverseTheory

namespace Work.KMTAreas.A4Z

theorem largeTail (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree)
    (hPel : Work.KMTContract.PeluseInverseKMT P) : LargeTailBranch P := by
  classical
  intro A hA
  have hA1 : (1 : ℝ) ≤ A := hA
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  set A' : ℝ := max 2 A with hA'def
  have hA'1 : (1 : ℝ) ≤ A' := le_trans (by norm_num) (le_max_left 2 A)
  have h2A'1 : (0 : ℝ) < 2 * A' + 1 := by linarith only [le_max_left (2:ℝ) A]
  have hA'2 : (2 : ℝ) ≤ A' := le_max_left 2 A
  have hAA' : A ≤ A' := le_max_right 2 A
  -- the free-window fine inverse theorem
  have hlip : Work.KMTAreas.A4.LipL1FineA P := lipL1FineA P hP hPel
  obtain ⟨CA, K1, C0, K0, hCA0, hK10, hC00, hK00, hAC⟩ :=
    Work.KMTAreas.A4Z.chain.arcCorrelation P hP hlip A' hA'1
  -- the auxiliary steps of §5.2
  obtain ⟨CE, hCE0, hExtract⟩ := Work.KMTAreas.A4.lip2ArcExtract
  obtain ⟨Ct, hCt0, hTail⟩ := Work.KMTAreas.A4.lip2GenWindowTail
  obtain ⟨CS, hCS0, hSavg⟩ := Work.KMTAreas.A4.lip2GenSavg
  have hWeyl : Work.KMTAreas.A4.WeylIccStatement P := Work.KMTAreas.A4.lip2GenWeyl P hP
  obtain ⟨CW, KW, hCW0, hKW0, hWeyl2⟩ := hWeyl
  obtain ⟨Cm, Km, hCm0, hKm0, hArcMass⟩ :=
    Work.KMTAreas.A4.lip2GenArcMassA P hP A' hA'1 CW KW hCW0 hKW0 hWeyl2
  -- the projection with the two spatial tail clauses
  obtain ⟨Cg, hCg0, hProj⟩ := projectionSelf P A hA1
  -- the numeric bookkeeping of the chain
  set CN3 : ℝ := 2 + (2 * Ct * (CE * (CA + 1)) ^ 2 * CA + 1) / (128 * CA) with hCN3def
  have hCN3pos : 0 < CN3 := by rw [hCN3def]; positivity
  obtain ⟨D_B, KbigB, CbigB, cB, hDB0, hKbigB0, hCbigB0, hcB0, hNum⟩ :=
    Work.KMTAreas.A4.lip2GenNumericB P hP CA (2 * K1) C0 K0 CE Ct CS CN3 Cm Km CW KW Cg A'
      hA'2 hCA0 (by positivity) hC00 hK00 hCE0 hCt0 hCS0 hCN3pos le_rfl hCm0 hKm0
      hCW0 hKW0 hCg0
  -- ### the final constants of the unscaled large-`N` branch
  set KA : ℝ := 2 * K1 with hKAdef
  have hKA0 : 0 < KA := by rw [hKAdef]; linarith only [hK10]
  set D0 : ℝ := CS * CE ^ 4 * (CA + 1) ^ 4 * CA ^ 2 * CN3 ^ 2 with hD0def
  have hD00 : 0 < D0 := by rw [hD0def]; positivity
  -- the final exponent `c` is large enough for the three `δ`-comparisons
  set c : ℝ := max (max cB (KbigB - 1)) (KA * (P.natDegree : ℝ) + 8 * KA * Km - 1) with hcdef
  have hc0 : 0 < c :=
    lt_of_lt_of_le hcB0 (le_trans (le_max_left cB (KbigB - 1)) (le_max_left _ _))
  have hc_cB : cB ≤ c := le_trans (le_max_left cB _) (le_max_left _ _)
  have hc_KbigB : KbigB ≤ c + 1 := by
    have h : KbigB - 1 ≤ c := le_trans (le_max_right cB (KbigB - 1)) (le_max_left _ _)
    linarith only [h]
  have hc_KA : KA * (P.natDegree : ℝ) + 8 * KA * Km ≤ c + 1 := by
    have h : KA * (P.natDegree : ℝ) + 8 * KA * Km - 1 ≤ c := le_max_right _ _
    linarith only [h]
  -- the global rescaling of the output
  set lam : ℝ := 1 / (Cg * (2 * A' + 1)) with hlamdef
  have hlam0 : 0 < lam := by rw [hlamdef]; positivity
  have hlamCg : lam * Cg = 1 / (2 * A' + 1) := by rw [hlamdef]; field_simp
  set D : ℝ := lam * D_B / 2 with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  set C2 : ℝ := 1 / (2 * A' + 1) with hC2def
  have hC2pos : 0 < C2 := by rw [hC2def]; positivity
  -- the level constant of the arithmetic scale
  set Yb : ℝ := (1 + A * D0) ^ Km with hYbdef
  have hYb0 : 0 < Yb := by rw [hYbdef]; positivity
  set Cl : ℝ := CbigB with hCldef
  have hCl0 : 0 < Cl := by rw [hCldef]; exact hCbigB0
  set Ck : ℝ := max (max (4 * Cm * Yb * (128 * CA) ^ P.natDegree)
      (2 * (256 * CA) ^ P.natDegree)) (16 * Cg / D_B) + 1 with hCkdef
  have hCk0 : 0 < Ck := by rw [hCkdef]; positivity
  have hCk_Yb : 4 * Cm * Yb * (128 * CA) ^ P.natDegree ≤ Ck := by
    rw [hCkdef]
    have h1 : 4 * Cm * Yb * (128 * CA) ^ P.natDegree
        ≤ max (4 * Cm * Yb * (128 * CA) ^ P.natDegree) (2 * (256 * CA) ^ P.natDegree) :=
      le_max_left _ _
    have h2 : max (4 * Cm * Yb * (128 * CA) ^ P.natDegree) (2 * (256 * CA) ^ P.natDegree)
        ≤ max (max (4 * Cm * Yb * (128 * CA) ^ P.natDegree)
            (2 * (256 * CA) ^ P.natDegree)) (16 * Cg / D_B) := le_max_left _ _
    linarith only [h1, h2]
  have hCk_256 : 2 * (256 * CA) ^ P.natDegree ≤ Ck := by
    rw [hCkdef]
    have h1 : 2 * (256 * CA) ^ P.natDegree
        ≤ max (4 * Cm * Yb * (128 * CA) ^ P.natDegree) (2 * (256 * CA) ^ P.natDegree) :=
      le_max_right _ _
    have h2 : max (4 * Cm * Yb * (128 * CA) ^ P.natDegree) (2 * (256 * CA) ^ P.natDegree)
        ≤ max (max (4 * Cm * Yb * (128 * CA) ^ P.natDegree)
            (2 * (256 * CA) ^ P.natDegree)) (16 * Cg / D_B) := le_max_left _ _
    linarith only [h1, h2]
  have hCk_Cg : 16 * Cg / D_B ≤ Ck := by
    rw [hCkdef]
    have h2 : 16 * Cg / D_B
        ≤ max (max (4 * Cm * Yb * (128 * CA) ^ P.natDegree)
            (2 * (256 * CA) ^ P.natDegree)) (16 * Cg / D_B) := le_max_right _ _
    linarith only [h2]
  set Kbig : ℝ := max (max KbigB (c / (P.natDegree : ℝ) + 1)) K0 with hKbigdef
  have hKbig0 : 0 < Kbig := lt_of_lt_of_le hKbigB0 (le_trans (le_max_left _ _) (le_max_left _ _))
  have hKbig_KbigB : KbigB ≤ Kbig := le_trans (le_max_left _ _) (le_max_left _ _)
  have hKbig_K0 : K0 ≤ Kbig := le_max_right _ _
  have hKbig_d : c ≤ Kbig * (P.natDegree : ℝ) := by
    have h : c / (P.natDegree : ℝ) + 1 ≤ Kbig := le_trans (le_max_right _ _) (le_max_left _ _)
    have hd : (0 : ℝ) < (P.natDegree : ℝ) := by
      have : 0 < P.natDegree := by omega
      exact_mod_cast this
    rw [div_add_one hd.ne', div_le_iff₀ hd] at h
    linarith only [h, hd]
  set Cbig : ℝ := max (max (CbigB + 1) (8 * Cg / D_B + 1)) C0 with hCbigdef
  have hCbig0 : 0 < Cbig := by rw [hCbigdef]; positivity
  have hCbig_CbigB : CbigB ≤ Cbig := by
    rw [hCbigdef]
    have h1 : CbigB ≤ CbigB + 1 := by linarith only []
    exact le_trans (le_trans h1 (le_max_left _ _)) (le_max_left _ _)
  have hCbig_Cg : 8 * Cg / D_B ≤ Cbig := by
    rw [hCbigdef]
    have h1 : 8 * Cg / D_B ≤ 8 * Cg / D_B + 1 := by linarith only []
    exact le_trans (le_trans h1 (le_max_right _ _)) (le_max_left _ _)
  have hCbig_C0 : C0 ≤ Cbig := le_max_right _ _
  have hCbig1 : (1 : ℝ) ≤ Cbig := by
    rw [hCbigdef]
    have h1 : (1 : ℝ) ≤ CbigB + 1 := by linarith only [hCbigB0]
    exact le_trans (le_trans h1 (le_max_left _ _)) (le_max_left _ _)
  refine ⟨c, D, Kbig, Cbig, Cl, Ck, C2, hc0, hDpos, hKbig0, hCbig0, hCl0, hCk0, hC2pos, ?_⟩
  intro ρ hρ0 hρ1 N N₀ δ f g h hN hδ0 hδ1 hN0lo hN0hi hfs hgs hhs hfb hgb hhb hcorr hbig
  have hδinv1 : (1 : ℝ) ≤ δ⁻¹ := (one_le_inv₀ hδ0).mpr hδ1
  have hδinv0 : (0 : ℝ) < δ⁻¹ := inv_pos.mpr hδ0
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNdpos : (0 : ℝ) < (N : ℝ) ^ P.natDegree := pow_pos hNpos _
  have hNd1 : (1 : ℝ) ≤ (N : ℝ) ^ P.natDegree := one_le_pow₀ (by exact_mod_cast hN)
  have hd1 : 1 ≤ P.natDegree - 1 := by have := hP; omega
  have hN01 : 1 ≤ N₀ := by
    by_contra hcon
    have h0 : N₀ = 0 := by omega
    rw [h0] at hN0lo
    simp only [Nat.cast_zero] at hN0lo
    have hpos : (0 : ℝ) < A * (N : ℝ) ^ P.natDegree / 2 := div_pos (mul_pos hA0 hNdpos) two_pos
    linarith only [hN0lo, hpos]
  -- the large-`N` hypothesis of the numeric lemma
  have h9B : CbigB * δ⁻¹ ^ KbigB ≤ (N : ℝ) := by
    refine le_trans ?_ hbig
    exact mul_le_mul hCbig_CbigB
      (Real.rpow_le_rpow_of_exponent_le hδinv1 hKbig_KbigB) (by positivity) (by positivity)
  -- the height hypothesis of the fine inverse theorem
  have hC0K0 : C0 * δ⁻¹ ^ K0 ≤ (N : ℝ) ^ (P.natDegree - 1) := by
    have h1 : C0 * δ⁻¹ ^ K0 ≤ Cbig * δ⁻¹ ^ Kbig :=
      mul_le_mul hCbig_C0 (Real.rpow_le_rpow_of_exponent_le hδinv1 hKbig_K0)
        (by positivity) (by positivity)
    have h3 : (N : ℝ) ≤ (N : ℝ) ^ (P.natDegree - 1) := by
      calc (N : ℝ) = (N : ℝ) ^ (1 : ℕ) := (pow_one _).symm
        _ ≤ (N : ℝ) ^ (P.natDegree - 1) :=
            pow_le_pow_right₀ (by exact_mod_cast hN) hd1
    exact le_trans (le_trans h1 hbig) h3
  -- the window hypotheses of the chain, at the parameter `A'`
  have hN0lo2 : (N : ℝ) ^ P.natDegree / A' ≤ (N₀ : ℝ) := by
    -- `1/A' ≤ A/2` because `A' ≥ 2 ≥ 2/A`
    have hAA'2 : 2 ≤ A * A' := by nlinarith only [mul_nonneg (sub_nonneg.2 hA1) (sub_nonneg.2 hA'2), hA1, hA'2]
    have h1 : 1 / A' ≤ A / 2 := by
      rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_two hA'2)]
      nlinarith only [hAA'2]
    have h2 : (N : ℝ) ^ P.natDegree / A' ≤ A * (N : ℝ) ^ P.natDegree / 2 := by
      have h3 : (N : ℝ) ^ P.natDegree / A' = (N : ℝ) ^ P.natDegree * (1 / A') := by ring
      have h4 : A * (N : ℝ) ^ P.natDegree / 2 = (N : ℝ) ^ P.natDegree * (A / 2) := by ring
      rw [h3, h4]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    exact le_trans h2 hN0lo
  have hN0hi2 : (N₀ : ℝ) ≤ A' * (N : ℝ) ^ P.natDegree :=
    le_trans hN0hi (mul_le_mul_of_nonneg_right hAA' hNdpos.le)
  -- the arc correlation
  obtain ⟨k1, 𝔸, F, hFb, hFsum, hFone, hFsupp, hAcard, hk1, hcorrF⟩ :=
    hAC ρ hρ0 hρ1 N N₀ δ f g h hN hδ0 hδ1 hN0lo2 hN0hi2 hfs hgs hhs hfb hgb hhb hcorr hC0K0
  -- the single-arc extraction
  have hX1 : ∀ x : ℤ, ‖AhalfTranspose N P h g x‖ ≤ 1 := fun x => by
    simpa using Work.KMTAreas.A4.norm_AhalfTranspose_le N P h g
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1) hhb hgb x
  have hk1pos : (0 : ℝ) < (2 : ℝ) ^ k1 := zpow_pos (by norm_num) k1
  obtain ⟨γ, F2, hF2supp, hF2sum, hF2b, hF2one, hF2pair⟩ :=
    hExtract 𝔸 ((2 : ℝ) ^ k1) hk1pos F (AhalfTranspose N P h g) (CA * δ⁻¹ ^ K1)
      hFsum hFb (by positivity) hX1 hFsupp
  have hcard : ((𝔸.card : ℝ) + 1) ≤ (CA + 1) * δ⁻¹ ^ K1 := by
    have h1 : (1 : ℝ) ≤ δ⁻¹ ^ K1 := Real.one_le_rpow hδinv1 hK10.le
    linarith only [hAcard, h1]
  have hCEle : CE * ((𝔸.card : ℝ) + 1) ≤ CE * ((CA + 1) * δ⁻¹ ^ K1) :=
    mul_le_mul_of_nonneg_left hcard hCE0.le
  have hδpow2 : δ⁻¹ ^ (2 * K1) = δ⁻¹ ^ K1 * δ⁻¹ ^ K1 := by
    rw [show (2 : ℝ) * K1 = K1 + K1 from by ring, Real.rpow_add hδinv0]
  have hF2bn : ∀ x : ℤ, ‖F2 x‖ ≤ CE * (CA + 1) * CA * δ⁻¹ ^ (2 * K1) := by
    intro x
    have h1 : CE * ((𝔸.card : ℝ) + 1) * (CA * δ⁻¹ ^ K1)
        ≤ CE * ((CA + 1) * δ⁻¹ ^ K1) * (CA * δ⁻¹ ^ K1) :=
      mul_le_mul hCEle le_rfl (by positivity) (by positivity)
    have h2 : CE * ((CA + 1) * δ⁻¹ ^ K1) * (CA * δ⁻¹ ^ K1)
        = CE * (CA + 1) * CA * δ⁻¹ ^ (2 * K1) := by
      rw [hδpow2]; ring
    exact (hF2b x).trans (h1.trans (le_of_eq h2))
  have hF2one2 : (∑' x : ℤ, ‖F2 x‖)
      ≤ CE * (CA + 1) * CA * δ⁻¹ ^ (2 * K1) * (N : ℝ) ^ P.natDegree := by
    have h1 : CE * ((𝔸.card : ℝ) + 1) * (∑' x : ℤ, ‖F x‖)
        ≤ CE * ((CA + 1) * δ⁻¹ ^ K1)
          * (CA * δ⁻¹ ^ K1 * (N : ℝ) ^ P.natDegree) :=
      mul_le_mul hCEle hFone (tsum_nonneg fun x => norm_nonneg _) (by positivity)
    have h2 : CE * ((CA + 1) * δ⁻¹ ^ K1) * (CA * δ⁻¹ ^ K1 * (N : ℝ) ^ P.natDegree)
        = CE * (CA + 1) * CA * δ⁻¹ ^ (2 * K1) * (N : ℝ) ^ P.natDegree := by
      rw [hδpow2]; ring
    exact (hF2one.trans h1).trans (le_of_eq h2)
  have hcorrF2 : δ ^ (2 * K1) / (CE * (CA + 1)) * (N : ℝ) ^ P.natDegree
      ≤ ‖bilinPair (AhalfTranspose N P h g) F2‖ := by
    have h1 : δ ^ K1 * (N : ℝ) ^ P.natDegree
        ≤ CE * (CA + 1) * δ⁻¹ ^ K1 * ‖bilinPair (AhalfTranspose N P h g) F2‖ := by
      have h2 : CE * ((𝔸.card : ℝ) + 1) * ‖bilinPair (AhalfTranspose N P h g) F2‖
          ≤ CE * ((CA + 1) * δ⁻¹ ^ K1) * ‖bilinPair (AhalfTranspose N P h g) F2‖ :=
        mul_le_mul_of_nonneg_right hCEle (norm_nonneg _)
      have h3 : CE * ((CA + 1) * δ⁻¹ ^ K1) * ‖bilinPair (AhalfTranspose N P h g) F2‖
          = CE * (CA + 1) * δ⁻¹ ^ K1 * ‖bilinPair (AhalfTranspose N P h g) F2‖ := by ring
      exact le_trans hcorrF (le_trans hF2pair (le_trans h2 (le_of_eq h3)))
    have hQpos : 0 < CE * (CA + 1) * δ⁻¹ ^ K1 := by positivity
    have h5 : δ ^ K1 * (N : ℝ) ^ P.natDegree / (CE * (CA + 1) * δ⁻¹ ^ K1)
        ≤ ‖bilinPair (AhalfTranspose N P h g) F2‖ :=
      (div_le_iff₀ hQpos).mpr (h1.trans (le_of_eq (mul_comm _ _)))
    have h6 : δ ^ K1 * (N : ℝ) ^ P.natDegree / (CE * (CA + 1) * δ⁻¹ ^ K1)
        = δ ^ (2 * K1) / (CE * (CA + 1)) * (N : ℝ) ^ P.natDegree := by
      have hδK : δ ^ (2 * K1) = δ ^ K1 * δ ^ K1 := by
        rw [show (2 : ℝ) * K1 = K1 + K1 from by ring, Real.rpow_add hδ0]
      rw [hδK, Real.inv_rpow hδ0.le K1, inv_eq_one_div, mul_one_div, div_mul_eq_mul_div]
      have hδKne : δ ^ K1 ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hδ0 _)
      have hQne : (CE * (CA + 1)) ≠ 0 := by positivity
      field_simp
    rw [h6] at h5
    exact h5
  -- the scales of the §5.2 argument
  set M : ℝ := max 2 ((N : ℝ) * δ ^ (2 * K1) / (128 * CA)) with hMdef
  set Y : ℝ := max 1 ((2 * Ct * (CE * (CA + 1)) ^ 2 * CA + 1)
    * δ⁻¹ ^ ((2 * K1 + 2 * K1) / 11)) with hYdef
  set S : ℝ := (N : ℝ) + M * Y with hSdef
  have hM2 : 2 ≤ M := by rw [hMdef]; exact le_max_left 2 _
  have hY1 : 1 ≤ Y := by rw [hYdef]; exact le_max_left 1 _
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM2
  have hYpos : 0 < Y := lt_of_lt_of_le (by norm_num) hY1
  have hSge : (N : ℝ) + M * Y ≤ S := le_of_eq hSdef.symm
  have hSN : (N : ℝ) ≤ S := by
    rw [hSdef]
    linarith only [mul_pos hMpos hYpos]
  have hS1 : 1 ≤ S := le_trans (by exact_mod_cast hN) hSN
  have hSpos : 0 < S := lt_of_lt_of_le hNpos hSN
  have hSle_hyp : S ≤ (N : ℝ) + (max 2 ((N : ℝ) * δ ^ (2 * K1) / (128 * CA)))
      * (max 1 ((2 * Ct * (CE * (CA + 1)) ^ 2 * CA + 1)
        * δ⁻¹ ^ ((2 * K1 + 2 * K1) / 11))) := by
    rw [hSdef, hMdef, hYdef]
  have hk1n : (2 : ℝ) ^ k1 ≤ CA * δ⁻¹ ^ (2 * K1) / (N : ℝ) := by
    refine le_trans hk1 (div_le_div_of_nonneg_right ?_ hNpos.le)
    have h2 : (1 : ℝ) ≤ δ⁻¹ ^ K1 := Real.one_le_rpow hδinv1 hK10.le
    have h3 : δ⁻¹ ^ K1 ≤ δ⁻¹ ^ K1 * δ⁻¹ ^ K1 :=
      le_mul_of_one_le_right (zero_le_one.trans h2) h2
    calc CA * δ⁻¹ ^ K1 ≤ CA * (δ⁻¹ ^ K1 * δ⁻¹ ^ K1) :=
          mul_le_mul_of_nonneg_left h3 hCA0.le
      _ = CA * δ⁻¹ ^ (2 * K1) := by rw [hδpow2]
  -- the `μ`-free conclusions of the numeric lemma
  have hμd0 : 0 < δ ^ (8 * (2 * K1)) * (N : ℝ) ^ P.natDegree
      / (CS * CE ^ 4 * (CA + 1) ^ 4 * CA ^ 2 * CN3 ^ 2) := by positivity
  obtain ⟨_, hk16, _, hMle, _, hSle, _, _, _⟩ :=
    hNum N N₀ δ k1 (δ ^ (8 * (2 * K1)) * (N : ℝ) ^ P.natDegree
      / (CS * CE ^ 4 * (CA + 1) ^ 4 * CA ^ 2 * CN3 ^ 2)) S
      hN hδ0 hδ1 hk1n hN0hi2 hμd0 le_rfl h9B hSle_hyp
  have h4k : 4 * (2 : ℝ) ^ k1 ≤ 1 / (2 * M) := by
    have hMle' : M ≤ 1 / (8 * (2 : ℝ) ^ k1) := by rw [hMdef]; exact hMle
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (2 : ℝ) ^ k1)).mp hMle'
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * M)]
    nlinarith only [h]
  have hsupp2 : FourierSupportIn F2 (Work.KMTAreas.A4.arcSet γ (1 / (2 * M))) :=
    FourierSupportIn.mono (Work.KMTAreas.A4.arcSet_mono_radius h4k) hF2supp
  -- the tail beyond `|s| <= S`
  have hYarith : (2 * Ct * (CE * (CA + 1)) ^ 2 * CA + 1)
      * δ⁻¹ ^ ((2 * K1 + 2 * K1) / 11) ≤ Y := by
    rw [hYdef]; exact le_max_right 1 _
  have htail : (∑' s : ℤ, (if S < |((s : ℝ))| then
        ‖∑' y : ℤ, h y * F2 (y + s) * Work.KMTAreas.A4.lip2Avg N P M γ g s y‖ else 0))
      ≤ (δ ^ (2 * K1) / (CE * (CA + 1))) * (N : ℝ) ^ P.natDegree / 2 := by
    have h1 := hTail P (γ := γ) (F := F2) (g := g) (h := h)
      (le_trans (by norm_num) hM2) hY1 hSge hF2sum hhb hgb
    have h2 : Ct * Y⁻¹ ^ 11 * (∑' x : ℤ, ‖F2 x‖)
        ≤ Ct * Y⁻¹ ^ 11
          * (CE * (CA + 1) * CA * δ⁻¹ ^ (2 * K1) * (N : ℝ) ^ P.natDegree) :=
      mul_le_mul_of_nonneg_left hF2one2 (by positivity)
    have h3 := Work.KMTAreas.A4.lip2GenTailArith (CA := CA) (KA := 2 * K1) (CE := CE)
      (Ct := Ct) (Y := Y) (Bf := CE * (CA + 1) * CA * δ⁻¹ ^ (2 * K1))
      (Nd := (N : ℝ) ^ P.natDegree) (δ := δ)
      hCA0 (by positivity) hCE0 hCt0 hδ0 hδ1 (by positivity) rfl hYarith
    exact h1.trans (h2.trans h3)
  -- the pigeonhole over the shifts plus Plancherel
  obtain ⟨s, hsS, hSavg2⟩ := hSavg (N := N) (M := M) (γ := γ) (F := F2) (g := g) (h := h)
    (BF := CE * (CA + 1) * CA * δ⁻¹ ^ (2 * K1))
    (lF := CE * (CA + 1) * CA * δ⁻¹ ^ (2 * K1) * (N : ℝ) ^ P.natDegree)
    (ε := δ ^ (2 * K1) / (CE * (CA + 1))) (S := S)
    hN P hM2 hF2sum hsupp2 hgb hhb ((FinSupp.of_supportIn hgs).summable.norm)
      ((FinSupp.of_supportIn hhs).summable.norm) (by positivity) (by positivity) hF2bn hF2one2
      hS1 hSN hcorrF2 htail
  -- the level mass
  set μ : ℝ := ∫ t in (0 : ℝ)..1, ‖Work.A3.kmtFhat g t‖ ^ 2
      * ‖Work.KMTAreas.A4.winSumIcc M γ t P s (((N / 2 + 1 : ℕ) : ℤ)) ((N : ℤ))‖ ^ 2 with hμdef
  rw [hμdef] at hSavg2
  have hμ8 : δ ^ (8 * (2 * K1)) * (N : ℝ) ^ P.natDegree
      / (CS * CE ^ 4 * (CA + 1) ^ 4 * CA ^ 2 * CN3 ^ 2) ≤ μ :=
    Work.KMTAreas.A4.lip2GenMuArith (CA := CA) (KA := 2 * K1) (CE := CE) (CS := CS) (CN3 := CN3)
      (ε := δ ^ (2 * K1) / (CE * (CA + 1))) (S := S)
      (Bf := CE * (CA + 1) * CA * δ⁻¹ ^ (2 * K1))
      (B1 := CE * (CA + 1) * CA * δ⁻¹ ^ (2 * K1) * (N : ℝ) ^ P.natDegree)
      (μ := μ) (δ := δ) (N := N) (d := P.natDegree)
      hCA0 (by positivity) hCE0 hCS0 hCN3pos hδ0 hδ1 hN hSpos rfl rfl rfl hSle hSavg2
  have hμ0 : 0 < μ := lt_of_lt_of_le hμd0 hμ8
  -- the remaining numeric conclusions
  obtain ⟨_, _, _, _, hArcM, _, hCmKm, hCmKmN, hDmu⟩ :=
    hNum N N₀ δ k1 μ S hN hδ0 hδ1 hk1n hN0hi2 hμ0 hμ8 h9B hSle_hyp
  -- the frequency pigeonhole (arc mass)
  obtain ⟨α, r, l, k, hr0, hr14, h2rk, hα, hαneg, h2l, h2k, hmassle⟩ :=
    hArcMass ρ hρ0 hρ1 (N := N) (N₀ := N₀) (M := M) (s := s) (γ := γ)
      (a := ((N / 2 + 1 : ℕ) : ℤ)) (b := (N : ℤ)) (g := g) (μ := μ)
      hN hN01 hM2 (by omega) hN0lo2 hN0hi2 hgs hgb ((FinSupp.of_supportIn hgs).summable.norm)
      hμ0 hArcM (le_of_eq hμdef)
  -- ### the endgame: the projection onto the arc, the major-arc level and the two tails
  -- `δ⁻¹ ^ x * δ ^ x = 1`
  have hδinv_mul : ∀ x : ℝ, δ⁻¹ ^ x * δ ^ x = 1 := by
    intro x
    rw [Real.inv_rpow hδ0.le, ← Real.rpow_neg hδ0.le, ← Real.rpow_add hδ0, neg_add_cancel,
      Real.rpow_zero]
  have hδmul_inv : ∀ x : ℝ, δ ^ x * δ⁻¹ ^ x = 1 := by
    intro x; rw [mul_comm]; exact hδinv_mul x
  have hδcombine : ∀ a b : ℝ, δ⁻¹ ^ a * δ⁻¹ ^ b * δ ^ (a + b) = 1 := by
    intro a b
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < δ⁻¹), hδinv_mul]
  have hδpow_le_one : ∀ y : ℝ, 0 ≤ y → δ ^ y ≤ 1 := fun y hy =>
    Real.rpow_le_one hδ0.le hδ1 hy
  set YΩ : ℝ := 1 + (N₀ : ℝ) / μ with hYΩdef
  set μ' : ℝ := μ / (Cm * YΩ ^ Km) with hμ'def
  have hYΩ1 : 1 ≤ YΩ := by
    rw [hYΩdef]
    have : 0 ≤ (N₀ : ℝ) / μ := div_nonneg (Nat.cast_nonneg _) hμ0.le
    linarith only [this]
  have hμ'0 : 0 < μ' := by
    rw [hμ'def]
    exact div_pos hμ0 (mul_pos hCm0 (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos hYΩ1) _))
  have hmassle' : μ' ≤ ∫ ξ in Work.KMTAreas.A4.arcSet α r,
      ‖ZFourier g ξ‖ ^ 2 ∂AddCircle.haarAddCircle := by
    rw [hμ'def, hYΩdef]
    exact hmassle
  -- (i) `YΩ ≤ (1 + A D0) δ^{-8 KA}` and hence `YΩ^Km ≤ Yb δ^{-8 KA Km}`
  have hYΩ_le : YΩ ≤ (1 + A * D0) * δ⁻¹ ^ (8 * KA) := by
    have hμ8'' : δ ^ (8 * KA) * (N : ℝ) ^ P.natDegree / D0 ≤ μ := by
      rw [hKAdef]; exact hμ8
    have hN0μ : (N₀ : ℝ) / μ ≤ A * D0 * δ⁻¹ ^ (8 * KA) := by
      rw [div_le_iff₀ hμ0]
      calc (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree := hN0hi
        _ = A * D0 * δ⁻¹ ^ (8 * KA)
              * (δ ^ (8 * KA) * (N : ℝ) ^ P.natDegree / D0) := by
              rw [Real.inv_rpow hδ0.le]
              field_simp
        _ ≤ A * D0 * δ⁻¹ ^ (8 * KA) * μ :=
              mul_le_mul_of_nonneg_left hμ8'' (by positivity)
    have h1 : (1 : ℝ) ≤ δ⁻¹ ^ (8 * KA) :=
      Real.one_le_rpow hδinv1 (by rw [hKAdef]; positivity)
    rw [hYΩdef]
    linarith only [hN0μ, h1]
  have hYΩpow : YΩ ^ Km ≤ Yb * δ⁻¹ ^ (8 * KA * Km) := by
    have h1 : YΩ ^ Km ≤ ((1 + A * D0) * δ⁻¹ ^ (8 * KA)) ^ Km :=
      Real.rpow_le_rpow (by rw [hYΩdef]; positivity) hYΩ_le (by positivity)
    have h2 : ((1 + A * D0) * δ⁻¹ ^ (8 * KA)) ^ Km
        = (1 + A * D0) ^ Km * δ⁻¹ ^ (8 * KA * Km) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ δ⁻¹) (8 * KA) Km]
    rw [hYbdef]
    exact h1.trans (le_of_eq h2)
  -- (ii) the projection level, at the top of the admissible range, and the window
  have hlevpos : 0 < Ck * δ⁻¹ ^ (c + 1) / (4 * (N : ℝ) ^ P.natDegree) := by positivity
  obtain ⟨kp, hkp_ge, hkp_le⟩ := Work.KMTAreas.A4.lipExistsZpowTwo hlevpos
  set Mpr : ℝ := max 2 ((2 : ℝ) ^ (-kp)) with hMprdef
  have hMpr2 : 2 ≤ Mpr := by rw [hMprdef]; exact le_max_left 2 _
  have hMpr0 : 0 < Mpr := lt_of_lt_of_le (by norm_num) hMpr2
  have hMpr_inv : 1 / Mpr ≤ (2 : ℝ) ^ kp := by
    have h1 : 1 / Mpr ≤ 1 / ((2 : ℝ) ^ (-kp)) :=
      one_div_le_one_div_of_le (zpow_pos (by norm_num) (-kp))
        (by rw [hMprdef]; exact le_max_right 2 _)
    have h2 : (1 : ℝ) / ((2 : ℝ) ^ (-kp)) = (2 : ℝ) ^ kp := by
      rw [one_div, zpow_neg, inv_inv]
    rwa [h2] at h1
  have h2rM : 2 * r ≤ Cm * YΩ ^ Km / M ^ P.natDegree := by
    have h2k' : (2 : ℝ) ^ k ≤ Cm * YΩ ^ Km / M ^ P.natDegree := h2k
    exact le_trans h2rk h2k'
  have hMge : (N : ℝ) * δ ^ (2 * K1) / (128 * CA) ≤ M := by
    rw [hMdef]; exact le_max_right 2 _
  have hratio_le : (N : ℝ) ^ P.natDegree / M ^ P.natDegree
      ≤ (128 * CA) ^ P.natDegree * δ⁻¹ ^ (KA * (P.natDegree : ℝ)) := by
    have hMge' : ((N : ℝ) * δ ^ (2 * K1) / (128 * CA)) ^ P.natDegree ≤ M ^ P.natDegree :=
      pow_le_pow_left₀ (by positivity) hMge P.natDegree
    have hid : ((N : ℝ) * δ ^ (2 * K1) / (128 * CA)) ^ P.natDegree
        = (N : ℝ) ^ P.natDegree * δ ^ (KA * (P.natDegree : ℝ)) / (128 * CA) ^ P.natDegree := by
      rw [hKAdef, div_pow, mul_pow, ← Real.rpow_natCast (δ ^ (2 * K1)) P.natDegree,
        ← Real.rpow_mul hδ0.le (2 * K1) (P.natDegree : ℝ)]
      try ring
    have hinv : 1 / M ^ P.natDegree
        ≤ 1 / ((N : ℝ) ^ P.natDegree * δ ^ (KA * (P.natDegree : ℝ))
            / (128 * CA) ^ P.natDegree) := by
      rw [← hid]
      exact one_div_le_one_div_of_le (by positivity) hMge'
    have hsimp : 1 / ((N : ℝ) ^ P.natDegree * δ ^ (KA * (P.natDegree : ℝ))
          / (128 * CA) ^ P.natDegree)
        = (128 * CA) ^ P.natDegree * δ⁻¹ ^ (KA * (P.natDegree : ℝ))
            / (N : ℝ) ^ P.natDegree := by
      rw [Real.inv_rpow hδ0.le]
      field_simp
    rw [hsimp] at hinv
    rw [div_eq_mul_one_div]
    calc (N : ℝ) ^ P.natDegree * (1 / M ^ P.natDegree)
        ≤ (N : ℝ) ^ P.natDegree
            * ((128 * CA) ^ P.natDegree * δ⁻¹ ^ (KA * (P.natDegree : ℝ))
                / (N : ℝ) ^ P.natDegree) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (128 * CA) ^ P.natDegree * δ⁻¹ ^ (KA * (P.natDegree : ℝ)) := by
          field_simp
  have hkey : 8 * r * (N : ℝ) ^ P.natDegree * δ ^ (c + 1)
      ≤ 4 * Cm * Yb * (128 * CA) ^ P.natDegree := by
    have hstep : 2 * r ≤ Cm * YΩ ^ Km / M ^ P.natDegree := h2rM
    calc 8 * r * (N : ℝ) ^ P.natDegree * δ ^ (c + 1)
        = 4 * (2 * r) * ((N : ℝ) ^ P.natDegree * δ ^ (c + 1)) := by ring
      _ ≤ 4 * (Cm * YΩ ^ Km / M ^ P.natDegree)
            * ((N : ℝ) ^ P.natDegree * δ ^ (c + 1)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ = 4 * Cm * YΩ ^ Km * ((N : ℝ) ^ P.natDegree / M ^ P.natDegree) * δ ^ (c + 1) := by ring
      _ ≤ 4 * Cm * (Yb * δ⁻¹ ^ (8 * KA * Km))
            * ((128 * CA) ^ P.natDegree * δ⁻¹ ^ (KA * (P.natDegree : ℝ))) * δ ^ (c + 1) := by
          have h1 : YΩ ^ Km * ((N : ℝ) ^ P.natDegree / M ^ P.natDegree)
              ≤ (Yb * δ⁻¹ ^ (8 * KA * Km))
                * ((128 * CA) ^ P.natDegree * δ⁻¹ ^ (KA * (P.natDegree : ℝ))) :=
            mul_le_mul hYΩpow hratio_le (by positivity) (by positivity)
          calc 4 * Cm * YΩ ^ Km * ((N : ℝ) ^ P.natDegree / M ^ P.natDegree) * δ ^ (c + 1)
              = 4 * Cm * (YΩ ^ Km * ((N : ℝ) ^ P.natDegree / M ^ P.natDegree))
                  * δ ^ (c + 1) := by ring
            _ ≤ 4 * Cm * ((Yb * δ⁻¹ ^ (8 * KA * Km))
                  * ((128 * CA) ^ P.natDegree * δ⁻¹ ^ (KA * (P.natDegree : ℝ))))
                  * δ ^ (c + 1) := by
                refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                exact mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = 4 * Cm * (Yb * δ⁻¹ ^ (8 * KA * Km))
                  * ((128 * CA) ^ P.natDegree * δ⁻¹ ^ (KA * (P.natDegree : ℝ))) * δ ^ (c + 1) := by
                ring
      _ = 4 * Cm * Yb * (128 * CA) ^ P.natDegree
            * (δ⁻¹ ^ (8 * KA * Km) * δ⁻¹ ^ (KA * (P.natDegree : ℝ)) * δ ^ (c + 1)) := by ring
      _ ≤ 4 * Cm * Yb * (128 * CA) ^ P.natDegree * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hcomb : δ⁻¹ ^ (8 * KA * Km) * δ⁻¹ ^ (KA * (P.natDegree : ℝ)) * δ ^ (c + 1)
              = δ ^ ((c + 1) - (KA * (P.natDegree : ℝ) + 8 * KA * Km)) := by
            have hsplit : δ ^ (c + 1) = δ ^ (8 * KA * Km + KA * (P.natDegree : ℝ))
                * δ ^ ((c + 1) - (8 * KA * Km + KA * (P.natDegree : ℝ))) := by
              rw [← Real.rpow_add hδ0]
              congr 1
              ring
            rw [hsplit]
            calc δ⁻¹ ^ (8 * KA * Km) * δ⁻¹ ^ (KA * (P.natDegree : ℝ))
                  * (δ ^ (8 * KA * Km + KA * (P.natDegree : ℝ))
                      * δ ^ ((c + 1) - (8 * KA * Km + KA * (P.natDegree : ℝ))))
                = (δ⁻¹ ^ (8 * KA * Km) * δ⁻¹ ^ (KA * (P.natDegree : ℝ))
                    * δ ^ (8 * KA * Km + KA * (P.natDegree : ℝ)))
                  * δ ^ ((c + 1) - (8 * KA * Km + KA * (P.natDegree : ℝ))) := by ring
              _ = 1 * δ ^ ((c + 1) - (8 * KA * Km + KA * (P.natDegree : ℝ))) := by
                  rw [hδcombine]
              _ = δ ^ ((c + 1) - (KA * (P.natDegree : ℝ) + 8 * KA * Km)) := by
                  rw [one_mul]
                  congr 1
                  ring
          rw [hcomb]
          exact Real.rpow_le_one hδ0.le hδ1 (by linarith only [hc_KA])
      _ = 4 * Cm * Yb * (128 * CA) ^ P.natDegree := mul_one _
  have h2r_le : 2 * r ≤ (2 : ℝ) ^ kp := by
    refine le_trans ?_ hkp_ge
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (N : ℝ) ^ P.natDegree)]
    have heq : 2 * r * (4 * (N : ℝ) ^ P.natDegree)
        = 8 * r * (N : ℝ) ^ P.natDegree := by ring
    rw [heq]
    have hδc : δ⁻¹ ^ (c + 1) * δ ^ (c + 1) = 1 := hδinv_mul (c + 1)
    calc 8 * r * (N : ℝ) ^ P.natDegree
        = (8 * r * (N : ℝ) ^ P.natDegree * δ ^ (c + 1)) * δ⁻¹ ^ (c + 1) := by
          have h1 : δ ^ (c + 1) * δ⁻¹ ^ (c + 1) = 1 := hδmul_inv (c + 1)
          calc 8 * r * (N : ℝ) ^ P.natDegree
              = 8 * r * (N : ℝ) ^ P.natDegree * (δ ^ (c + 1) * δ⁻¹ ^ (c + 1)) := by
                rw [h1, mul_one]
            _ = (8 * r * (N : ℝ) ^ P.natDegree * δ ^ (c + 1)) * δ⁻¹ ^ (c + 1) := by ring
      _ ≤ (4 * Cm * Yb * (128 * CA) ^ P.natDegree) * δ⁻¹ ^ (c + 1) :=
          mul_le_mul_of_nonneg_right hkey (by positivity)
      _ ≤ Ck * δ⁻¹ ^ (c + 1) := mul_le_mul_of_nonneg_right hCk_Yb (by positivity)
  -- (iii) the window `Mpr` is admissible for the arc of radius `r`
  have hMr_le : 2 * Mpr * r ≤ 1 := by
    have h4r : 4 * r ≤ 1 := by linarith only [hr14]
    have h2rkp : 2 * r * (2 : ℝ) ^ (-kp) ≤ 1 := by
      have h1 : (2 : ℝ) ^ (-kp) * (2 : ℝ) ^ kp = 1 := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), neg_add_cancel, zpow_zero]
      calc 2 * r * (2 : ℝ) ^ (-kp) ≤ (2 : ℝ) ^ kp * (2 : ℝ) ^ (-kp) :=
            mul_le_mul_of_nonneg_right h2r_le (by positivity)
        _ = 1 := by rw [mul_comm]; exact h1
    have hmax : 2 * Mpr * r = max (4 * r) (2 * r * (2 : ℝ) ^ (-kp)) := by
      have h : 2 * Mpr * r = max ((2 * r) * 2) ((2 * r) * (2 : ℝ) ^ (-kp)) := by
        rw [show 2 * Mpr * r = (2 * r) * Mpr by ring, hMprdef]
        exact mul_max_of_nonneg 2 ((2 : ℝ) ^ (-kp)) (by positivity : (0 : ℝ) ≤ 2 * r)
      rw [h]
      congr 1 <;> ring
    rw [hmax]
    exact max_le h4r h2rkp
  -- (iv) the arc-mass comparison and the projection with both tails
  have hs : (((Quotient.out α : ℝ)) : FreqCircle) = α := Quotient.out_eq α
  have hcmp := Work.KMTAreas.A4.arcMass_le_windowMass g
    ((FinSupp.of_supportIn hgs).summable.norm)
    (M := Mpr) (s := (Quotient.out α : ℝ)) (r := r) hMpr2 hr0 hMr_le
  rw [hs] at hcmp
  have hmass'' : μ' ≤ ∫ t in (0 : ℝ)..1,
      ‖Work.A3.kmtFhat g t‖ ^ 2 * (Work.KMTAreas.A4.winFT Mpr (Quotient.out α : ℝ) t).re := by
    refine (hmassle'.trans hcmp).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [Work.KMTAreas.A4.kmtFhat_eq_ZFourier g t]
  obtain ⟨G0, hG0b, hG0sum, hG0one, hG0supp, hG0pair, hG0fringe, hG0tail⟩ :=
    hProj N hN N₀ hN0hi g ((FinSupp.of_supportIn hgs).summable.norm) hgb hgs
      Mpr (Quotient.out α : ℝ) μ' hMpr2 hmass''
  -- its Fourier support lies in the major arcs at the level `kp`
  have hG0supp' : FourierSupportIn G0 (majorArc ρ l kp) := by
    have h1 : FourierSupportIn G0 (Work.KMTAreas.A4.arcSet (-α) (1 / Mpr)) := by
      simpa only [hs] using hG0supp
    exact FourierSupportIn.mono (Work.KMTAreas.A4.arcSet_subset_majorArc hαneg hMpr_inv) h1
  have hnorm_lam : ‖((lam : ℝ) : ℂ)‖ = lam := by
    rw [Complex.norm_real, Real.norm_of_nonneg hlam0.le]
  refine ⟨fun x => ((lam : ℝ) : ℂ) * G0 x, l, kp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) the sup bound
    intro x
    calc ‖((lam : ℝ) : ℂ) * G0 x‖ = lam * ‖G0 x‖ := by rw [norm_mul, hnorm_lam]
      _ ≤ lam * Cg := mul_le_mul_of_nonneg_left (hG0b x) hlam0.le
      _ = 1 / (2 * A' + 1) := hlamCg
      _ ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith only [hA'2]
  · -- (2) summability
    exact (hG0sum.mul_left lam).congr fun x => by rw [norm_mul, hnorm_lam]
  · -- (3) the `ℓ¹` mass
    have hsum : (∑' x : ℤ, ‖((lam : ℝ) : ℂ) * G0 x‖) = lam * ∑' x : ℤ, ‖G0 x‖ := by
      rw [← tsum_mul_left]
      exact tsum_congr fun x => by rw [norm_mul, hnorm_lam]
    have hgle : (∑' x : ℤ, ‖g x‖) ≤ 2 * (N₀ : ℝ) + 1 := by
      have h := ellOne_le_of_supportIn g N₀ hgs (C := 1) (fun x => hgb x)
      simpa [ellOne] using h
    have hNdA : 2 * (N₀ : ℝ) + 1 ≤ (2 * A' + 1) * (N : ℝ) ^ P.natDegree := by
      have h1 : 2 * (N₀ : ℝ) ≤ 2 * A' * (N : ℝ) ^ P.natDegree := by linarith only [hN0hi2]
      calc 2 * (N₀ : ℝ) + 1 ≤ 2 * A' * (N : ℝ) ^ P.natDegree + (N : ℝ) ^ P.natDegree := by
            linarith only [h1, hNd1]
        _ = (2 * A' + 1) * (N : ℝ) ^ P.natDegree := by ring
    rw [hsum]
    calc lam * (∑' x : ℤ, ‖G0 x‖)
        ≤ lam * (Cg * (2 * (N₀ : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left
            (hG0one.trans (mul_le_mul_of_nonneg_left hgle hCg0.le)) hlam0.le
      _ ≤ lam * (Cg * ((2 * A' + 1) * (N : ℝ) ^ P.natDegree)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hNdA hCg0.le) hlam0.le
      _ = (lam * Cg) * ((2 * A' + 1) * (N : ℝ) ^ P.natDegree) := by ring
      _ = (1 / (2 * A' + 1)) * ((2 * A' + 1) * (N : ℝ) ^ P.natDegree) := by rw [hlamCg]
      _ ≤ 1 + (N : ℝ) ^ P.natDegree := by
          have h1 : (1 / (2 * A' + 1)) * ((2 * A' + 1) * (N : ℝ) ^ P.natDegree)
              = (N : ℝ) ^ P.natDegree := by
            field_simp
          rw [h1]
          linarith only [hNd1]
  · -- (4) the Fourier support
    have hsm : (fun x => ((lam : ℝ) : ℂ) * G0 x) = ((lam : ℝ) : ℂ) • G0 := rfl
    rw [hsm]
    exact Work.KMTAreas.A4.FourierSupportIn_const_mul hG0sum ((lam : ℝ) : ℂ) hG0supp'
  · -- (5) the arithmetic height
    have hCmKm' : Cm * YΩ ^ Km ≤ CbigB * δ⁻¹ ^ KbigB := by
      rw [hYΩdef]
      exact hCmKm
    have h1 : δ⁻¹ ^ KbigB ≤ δ⁻¹ ^ (c + 1) :=
      Real.rpow_le_rpow_of_exponent_le hδinv1 hc_KbigB
    rw [hCldef]
    exact le_trans h2l (le_trans hCmKm' (mul_le_mul_of_nonneg_left h1 hCbigB0.le))
  · -- (6) the continuous height, by construction of `kp`
    calc (2 : ℝ) ^ kp ≤ 2 * (Ck * δ⁻¹ ^ (c + 1) / (4 * (N : ℝ) ^ P.natDegree)) := hkp_le
      _ = Ck * δ⁻¹ ^ (c + 1) / (2 * (N : ℝ) ^ P.natDegree) := by ring
      _ ≤ Ck * δ⁻¹ ^ (c + 1) / (N : ℝ) ^ P.natDegree :=
          div_le_div_of_nonneg_left (by positivity) hNdpos (by linarith only [hNdpos])
  · -- (7) the correlation
    have hsmul : bilinPair g (fun x => ((lam : ℝ) : ℂ) * G0 x)
        = ((lam : ℝ) : ℂ) * bilinPair g G0 := by
      rw [bilinPair, bilinPair, ← tsum_mul_left]
      exact tsum_congr fun x => by ring
    have hμ'le : D_B * δ ^ cB * (N : ℝ) ^ P.natDegree ≤ μ' := by
      rw [hμ'def]
      exact hDmu
    have hDle : D * δ ^ c * (N : ℝ) ^ P.natDegree
        ≤ lam * (D_B * δ ^ c * (N : ℝ) ^ P.natDegree) := by
      have h2 : lam * D_B / 2 ≤ lam * D_B := by linarith only [mul_pos hlam0 hDB0]
      calc D * δ ^ c * (N : ℝ) ^ P.natDegree
          = lam * D_B / 2 * δ ^ c * (N : ℝ) ^ P.natDegree := by rw [hDdef]
        _ ≤ lam * D_B * δ ^ c * (N : ℝ) ^ P.natDegree := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = lam * (D_B * δ ^ c * (N : ℝ) ^ P.natDegree) := by ring
    rw [hsmul, norm_mul, hnorm_lam]
    calc D * δ ^ c * (N : ℝ) ^ P.natDegree
        ≤ lam * (D_B * δ ^ c * (N : ℝ) ^ P.natDegree) := hDle
      _ ≤ lam * (D_B * δ ^ cB * (N : ℝ) ^ P.natDegree) := by
          refine mul_le_mul_of_nonneg_left ?_ hlam0.le
          have h1 : δ ^ c ≤ δ ^ cB :=
            Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hc_cB
          have h2 : D_B * δ ^ c ≤ D_B * δ ^ cB := mul_le_mul_of_nonneg_left h1 hDB0.le
          have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : (0:ℝ) ≤ (N:ℝ)^P.natDegree)
          linarith only [h3]
      _ ≤ lam * μ' := mul_le_mul_of_nonneg_left hμ'le hlam0.le
      _ ≤ lam * ‖bilinPair g G0‖ := mul_le_mul_of_nonneg_left hG0pair hlam0.le
  · -- (8) the `ℓ¹` fringe
    have hfringe : (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)|
          then ‖((lam : ℝ) : ℂ) * G0 x‖ else 0))
        = lam * (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)|
            then ‖G0 x‖ else 0)) := by
      rw [← tsum_mul_left]
      exact tsum_congr fun x => by
        by_cases hx : A * (N : ℝ) ^ P.natDegree < |(x : ℝ)|
        · rw [if_pos hx, if_pos hx, norm_mul, hnorm_lam]
        · rw [if_neg hx, if_neg hx, mul_zero]
    rw [hfringe]
    have hMpr_bd : Mpr ≤ max 2 (4 * (N : ℝ) ^ P.natDegree * δ ^ (c + 1) / Ck) := by
      have h1 : (2 : ℝ) ^ (-kp) ≤ 4 * (N : ℝ) ^ P.natDegree * δ ^ (c + 1) / Ck := by
        calc (2 : ℝ) ^ (-kp) = (((2 : ℝ) ^ kp))⁻¹ := zpow_neg (2 : ℝ) kp
          _ ≤ (Ck * δ⁻¹ ^ (c + 1) / (4 * (N : ℝ) ^ P.natDegree))⁻¹ :=
              (inv_le_inv₀ (zpow_pos (by norm_num : (0 : ℝ) < 2) kp) hlevpos).mpr hkp_ge
          _ = 4 * (N : ℝ) ^ P.natDegree * δ ^ (c + 1) / Ck := by
              rw [Real.inv_rpow hδ0.le]
              field_simp
      rw [hMprdef]
      exact max_le_max le_rfl h1
    have hCgbd : Cg * Mpr ≤ max (2 * Cg)
        (4 * Cg * (N : ℝ) ^ P.natDegree * δ ^ (c + 1) / Ck) := by
      calc Cg * Mpr ≤ Cg * max 2 (4 * (N : ℝ) ^ P.natDegree * δ ^ (c + 1) / Ck) :=
            mul_le_mul_of_nonneg_left hMpr_bd hCg0.le
        _ = max (Cg * 2) (Cg * (4 * (N : ℝ) ^ P.natDegree * δ ^ (c + 1) / Ck)) :=
            mul_max_of_nonneg 2 _ hCg0.le
        _ = max (2 * Cg) (4 * Cg * (N : ℝ) ^ P.natDegree * δ ^ (c + 1) / Ck) := by ring
    have hCd : Cbig ^ P.natDegree ≤ δ ^ c * (N : ℝ) ^ P.natDegree := by
      have h1 : (Cbig * δ⁻¹ ^ Kbig) ^ P.natDegree ≤ (N : ℝ) ^ P.natDegree :=
        pow_le_pow_left₀ (by positivity) hbig P.natDegree
      have h2 : (Cbig * δ⁻¹ ^ Kbig) ^ P.natDegree
          = Cbig ^ P.natDegree * δ⁻¹ ^ (Kbig * (P.natDegree : ℝ)) := by
        rw [mul_pow, ← Real.rpow_natCast (δ⁻¹ ^ Kbig) P.natDegree,
          ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ δ⁻¹) Kbig (P.natDegree : ℝ)]
      rw [h2] at h1
      have h3 : (Cbig ^ P.natDegree * δ⁻¹ ^ (Kbig * (P.natDegree : ℝ)))
            * δ ^ (Kbig * (P.natDegree : ℝ)) ≤ (N : ℝ) ^ P.natDegree
              * δ ^ (Kbig * (P.natDegree : ℝ)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h4 : (Cbig ^ P.natDegree * δ⁻¹ ^ (Kbig * (P.natDegree : ℝ)))
            * δ ^ (Kbig * (P.natDegree : ℝ)) = Cbig ^ P.natDegree := by
        rw [mul_assoc, hδinv_mul, mul_one]
      rw [h4] at h3
      have h5 : δ ^ (Kbig * (P.natDegree : ℝ)) ≤ δ ^ c :=
        Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith only [hKbig_d])
      have h6 : (N : ℝ) ^ P.natDegree * δ ^ (Kbig * (P.natDegree : ℝ))
          ≤ (N : ℝ) ^ P.natDegree * δ ^ c :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
      calc Cbig ^ P.natDegree
          ≤ (N : ℝ) ^ P.natDegree * δ ^ (Kbig * (P.natDegree : ℝ)) := h3
        _ ≤ (N : ℝ) ^ P.natDegree * δ ^ c := h6
        _ = δ ^ c * (N : ℝ) ^ P.natDegree := by ring
    have hgoal : Cg * Mpr ≤ D_B * δ ^ c * (N : ℝ) ^ P.natDegree / 4 := by
      refine le_trans hCgbd (max_le ?_ ?_)
      · have h1 : 8 * Cg ≤ D_B * Cbig ^ P.natDegree := by
          have h2 : 8 * Cg / D_B ≤ Cbig := hCbig_Cg
          rw [div_le_iff₀ hDB0] at h2
          have h3 : Cbig ≤ Cbig ^ P.natDegree := by
            have h5 : (1 : ℝ) ≤ Cbig := hCbig1
            calc Cbig = Cbig ^ (1 : ℕ) := (pow_one _).symm
              _ ≤ Cbig ^ P.natDegree := pow_le_pow_right₀ h5 (by omega)
          calc 8 * Cg ≤ Cbig * D_B := h2
            _ ≤ Cbig ^ P.natDegree * D_B := mul_le_mul_of_nonneg_right h3 hDB0.le
            _ = D_B * Cbig ^ P.natDegree := by ring
        have h2 : 8 * Cg ≤ D_B * δ ^ c * (N : ℝ) ^ P.natDegree :=
          h1.trans (by
            calc D_B * Cbig ^ P.natDegree ≤ D_B * (δ ^ c * (N : ℝ) ^ P.natDegree) :=
                  mul_le_mul_of_nonneg_left hCd hDB0.le
              _ = D_B * δ ^ c * (N : ℝ) ^ P.natDegree := by ring)
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
        linarith only [h2]
      · have h1 : 16 * Cg / Ck ≤ D_B := by
          rw [div_le_iff₀ hCk0]
          rw [div_le_iff₀ hDB0] at hCk_Cg
          linarith only [hCk_Cg]
        have h2 : 16 * Cg * δ / Ck ≤ D_B := by
          rw [div_le_iff₀ hCk0]
          have h4 : 16 * Cg ≤ D_B * Ck := by
            rw [div_le_iff₀ hCk0] at h1; exact h1
          linarith only [mul_le_mul_of_nonneg_left hδ1 hCg0.le, h4]
        have h3 : 4 * (4 * Cg * (N : ℝ) ^ P.natDegree * δ ^ (c + 1))
            ≤ D_B * δ ^ c * (N : ℝ) ^ P.natDegree * Ck := by
          have h5 : δ ^ (c + 1) = δ ^ c * δ := by
            rw [Real.rpow_add hδ0 c 1, Real.rpow_one]
            try ring
          have h6 : 16 * Cg * δ ≤ D_B * Ck := by
            rw [div_le_iff₀ hCk0] at h2; exact h2
          rw [h5]
          calc 4 * (4 * Cg * (N : ℝ) ^ P.natDegree * (δ ^ c * δ))
              = (16 * Cg * δ) * ((N : ℝ) ^ P.natDegree * δ ^ c) := by ring
            _ ≤ (D_B * Ck) * ((N : ℝ) ^ P.natDegree * δ ^ c) :=
                mul_le_mul_of_nonneg_right h6 (by positivity)
            _ = D_B * δ ^ c * (N : ℝ) ^ P.natDegree * Ck := by ring
        calc 4 * Cg * (N : ℝ) ^ P.natDegree * δ ^ (c + 1) / Ck
            = (4 * (4 * Cg * (N : ℝ) ^ P.natDegree * δ ^ (c + 1))) / (4 * Ck) := by
              field_simp
          _ ≤ (D_B * δ ^ c * (N : ℝ) ^ P.natDegree * Ck) / (4 * Ck) :=
              div_le_div_of_nonneg_right h3 (by positivity)
          _ = D_B * δ ^ c * (N : ℝ) ^ P.natDegree / 4 := by
              field_simp
    calc lam * (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G0 x‖ else 0))
        ≤ lam * (Cg * Mpr) := mul_le_mul_of_nonneg_left hG0fringe hlam0.le
      _ ≤ lam * (D_B * δ ^ c * (N : ℝ) ^ P.natDegree / 4) :=
          mul_le_mul_of_nonneg_left hgoal hlam0.le
      _ = D * δ ^ c * (N : ℝ) ^ P.natDegree / 2 := by rw [hDdef]; ring
  · -- (9) the `ℓ²` tail
    intro R hR
    have htail : (∑' x : ℤ, (if R * (N : ℝ) ^ P.natDegree < |(x : ℝ)|
          then ‖((lam : ℝ) : ℂ) * G0 x‖ ^ 2 else 0))
        = lam ^ 2 * (∑' x : ℤ, (if R * (N : ℝ) ^ P.natDegree < |(x : ℝ)|
            then ‖G0 x‖ ^ 2 else 0)) := by
      rw [show (fun x : ℤ => (if R * (N : ℝ) ^ P.natDegree < |(x : ℝ)|
            then ‖((lam : ℝ) : ℂ) * G0 x‖ ^ 2 else 0))
          = fun x : ℤ => lam ^ 2 * (if R * (N : ℝ) ^ P.natDegree < |(x : ℝ)|
              then ‖G0 x‖ ^ 2 else 0) from funext fun x => by
            by_cases hx : R * (N : ℝ) ^ P.natDegree < |(x : ℝ)|
            · rw [if_pos hx, if_pos hx, norm_mul, hnorm_lam]; ring
            · rw [if_neg hx, if_neg hx, mul_zero]]
      rw [tsum_mul_left]
    rw [htail]
    have h := hG0tail R hR
    rw [Real.rpow_neg_one] at h
    rw [hC2def]
    calc lam ^ 2 * (∑' x : ℤ, (if R * (N : ℝ) ^ P.natDegree < |(x : ℝ)|
            then ‖G0 x‖ ^ 2 else 0))
        ≤ lam ^ 2 * (Cg ^ 2 * R⁻¹ * (N : ℝ) ^ P.natDegree) :=
          mul_le_mul_of_nonneg_left h (sq_nonneg lam)
      _ = (lam * Cg) ^ 2 * R ^ (-(1 : ℝ)) * (N : ℝ) ^ P.natDegree := by
          rw [Real.rpow_neg_one]; ring
      _ = (1 / (2 * A' + 1)) ^ 2 * R ^ (-(1 : ℝ)) * (N : ℝ) ^ P.natDegree := by
          rw [hlamCg]

end Work.KMTAreas.A4Z
