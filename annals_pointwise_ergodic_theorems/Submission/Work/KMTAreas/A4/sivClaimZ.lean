/-
# Corollary `siv` of Krause--Mirek--Tao §5.1: removing the support hypotheses
-/
import Mathlib
import Submission.Work.KMTAreas.A4.improvOneZDefs
import Submission.Work.KMTAreas.A4.sivGeomAux
import Submission.Work.KMTAreas.A4Z.kmtProj_comp_add
import Submission.Work.KMTAreas.A4Z.eLpNorm_comp_add_count
import Submission.Commons.Analysis.Fourier.finset_bracket_lattice_le
import Submission.Work.KMTAreas.A4Z.schur_finite
import Submission.Work.KMTAreas.A4Z.supportIn_eLpNorm_le
import Submission.Work.KMTAreas.A4.sivPairDecay
import Submission.Work.KMTAreas.A5.Basic
import Submission.Work.KMTAreas.A5.logbPowLeConstMulRpow
import Submission.Work.KMTAreas.A7.KmtProjCrude
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory (AhalfTranspose SupportIn)
open Work.Analysis.IonescuWainger (GoodMajorArcs)
open Work.Analysis.EndVar (logN)

/-! ## Cauchy--Schwarz for the bilinear pairing -/

theorem enorm_bilinPair_le (u v : ℤ → ℂ) :
    ‖∑' x : ℤ, u x * v x‖ₑ
      ≤ eLpNorm u 2 Measure.count * eLpNorm v 2 Measure.count := by
  have h1 : ‖∑' x : ℤ, u x * v x‖ₑ ≤ ∑' x : ℤ, ‖u x * v x‖ₑ := enorm_tsum_le_tsum_enorm
  have h2 : (∑' x : ℤ, ‖u x * v x‖ₑ)
      = eLpNorm (fun x : ℤ => u x * v x) 1 Measure.count := by
    rw [eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm), lintegral_count]
  have h3 : eLpNorm (fun x : ℤ => u x * v x) 1 Measure.count
      ≤ 1 * eLpNorm u 2 Measure.count * eLpNorm v 2 Measure.count :=
    eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (fun a b : ℂ => a * b) 1 (by first | fun_prop | exact continuous_mul | exact continuous_inner | (simp only [Function.uncurry_def]; fun_prop)) (measurable_of_countable u).aestronglyMeasurable (measurable_of_countable v).aestronglyMeasurable (by filter_upwards with x; simp) (p := 2) (q := 2) (r := 1)
  calc ‖∑' x : ℤ, u x * v x‖ₑ ≤ ∑' x : ℤ, ‖u x * v x‖ₑ := h1
    _ = eLpNorm (fun x : ℤ => u x * v x) 1 Measure.count := h2
    _ ≤ 1 * eLpNorm u 2 Measure.count * eLpNorm v 2 Measure.count := h3
    _ = eLpNorm u 2 Measure.count * eLpNorm v 2 Measure.count := by rw [one_mul]

theorem enorm_pairing_le_mul {u v : ℤ → ℂ} {A A' : ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (hu : eLpNorm u 2 Measure.count ≤ ENNReal.ofReal A)
    (hv : eLpNorm v 2 Measure.count ≤ ENNReal.ofReal A') :
    ‖∑' x : ℤ, u x * star (v x)‖ ≤ A * A' := by
  have hstar : eLpNorm (fun x : ℤ => star (v x)) 2 Measure.count
      = eLpNorm v 2 Measure.count := eLpNorm_star
  have h1 : ‖∑' x : ℤ, u x * star (v x)‖ₑ ≤ ENNReal.ofReal (A * A') := by
    refine (enorm_bilinPair_le u (fun x => star (v x))).trans ?_
    rw [hstar]
    calc eLpNorm u 2 Measure.count * eLpNorm v 2 Measure.count
        ≤ ENNReal.ofReal A * ENNReal.ofReal A' := mul_le_mul' hu hv
      _ = ENNReal.ofReal (A * A') := (ENNReal.ofReal_mul hA).symm
  calc ‖∑' x : ℤ, u x * star (v x)‖ = (‖∑' x : ℤ, u x * star (v x)‖ₑ).toReal := by simp
    _ ≤ (ENNReal.ofReal (A * A')).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    _ = A * A' := ENNReal.toReal_ofReal (mul_nonneg hA hA')

/-- The modulus of the `ℓ²` pairing is symmetric in its two arguments. -/
theorem norm_pairing_comm (u v : ℤ → ℂ) :
    ‖∑' x : ℤ, u x * star (v x)‖ = ‖∑' x : ℤ, v x * star (u x)‖ := by
  have h : ∑' x : ℤ, v x * star (u x) = star (∑' x : ℤ, u x * star (v x)) := by
    rw [tsum_star]
    refine tsum_congr fun x => ?_
    simp only [star_mul, star_star]
  rw [h, norm_star]

/-! ## The per-block bound from the windowed Corollary `struct-iii` -/

/-- A function supported in `[-M,M]` and bounded by `B` is in `ℓ²` against counting measure;
its `ℒ²` seminorm is bounded by `B * √(2M+1)` but only finiteness is needed here. -/
theorem memLp_two_of_supportIn_bound {f : ℤ → ℂ} {B : ℝ} {M : ℕ}
    (hsupp : SupportIn f M) (hbd : ∀ y : ℤ, ‖f y‖ ≤ B) : MemLp f 2 Measure.count := by
  have hsum : Summable (fun y : ℤ => ‖f y‖ ^ 2) := by
    refine summable_of_ne_finset_zero (s := Finset.Icc (-(M : ℤ)) M) fun y hy => ?_
    have hz : f y = 0 := by
      by_contra hne
      exact hy (SupportIn.mem_Icc hsupp hne)
    rw [hz]
    simp
  exact MeasureTheory.memLp_iff.mpr (by
    rw [eLpNorm_two_eq_ofReal_l2norm hsum]
    exact ENNReal.ofReal_lt_top)

theorem norm_le_sqrt_l2sq {g : ℤ → ℂ} (hg : MemLp g 2 Measure.count) (y : ℤ) :
    ‖g y‖ ≤ Real.sqrt (l2sq g) := by
  have h1 : ‖g y‖ ^ 2 ≤ ∑' z : ℤ, ‖g z‖ ^ 2 := by
    simpa using (memLp_two_count_summable_norm_sq hg).sum_le_tsum ({y} : Finset ℤ)
      (fun z _ => sq_nonneg _)
  calc ‖g y‖ = Real.sqrt (‖g y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑' z : ℤ, ‖g z‖ ^ 2) := Real.sqrt_le_sqrt h1

theorem eLpNorm_blkE_le (P : Polynomial ℤ) (hP : 1 ≤ P.natDegree) {c₀ ρ Cρ : ℝ} {C : NNReal}
    (hS : StructiiiAHyp P (3 * (coefBd P : ℝ) + 4) c₀ ρ Cρ C)
    {N : ℕ} (hN : 1 ≤ N) (l : ℕ) {h g : ℤ → ℂ} (hh : ∀ x : ℤ, ‖h x‖ ≤ 1)
    (hg : MemLp g 2 Measure.count)
    (hgood : GoodMajorArcs ρ Cρ l ((l : ℤ) - logN N)) (i : ℤ) :
    eLpNorm (blkE P N ρ l h g i) 2 Measure.count
      ≤ (C : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(c₀ * (l : ℝ))))
          * ENNReal.ofReal (l2norm (blkPiece P N g i)) := by
  have hW : (0 : ℤ) ≤ (winBd P N : ℤ) := by positivity
  have hψs : SupportIn (fun y : ℤ => blkPiece P N g i (y + blkCtr P N i)) (blkRad P N) := by
    intro y hy
    change blkPiece P N g i (y + blkCtr P N i) = 0
    rw [blkPiece]
    by_cases hc : i * (blkLen P N : ℤ) ≤ y + blkCtr P N i ∧
        y + blkCtr P N i < (i + 1) * (blkLen P N : ℤ)
    · exfalso
      have hmem : blkAlpha P N i ≤ y + blkCtr P N i ∧ y + blkCtr P N i ≤ blkBeta P N i :=
        ⟨by simp only [blkAlpha]; linarith [hc.1, hW],
         by simp only [blkBeta]; linarith [hc.2, hW]⟩
      have h := abs_sub_blkCtr_le P N i (y + blkCtr P N i) hmem.1 hmem.2
      have hy' : |y| ≤ (blkRad P N : ℤ) := by
        have : (y + blkCtr P N i) - blkCtr P N i = y := by ring
        rwa [this] at h
      have h3 : ((y.natAbs : ℕ) : ℤ) ≤ (blkRad P N : ℤ) := by
        rw [Int.natCast_natAbs]; exact hy'
      omega
    · exact if_neg hc
  have hχs : SupportIn (fun y : ℤ => winPiece P N h i (y + blkCtr P N i)) (blkRad P N) := by
    intro y hy
    change winPiece P N h i (y + blkCtr P N i) = 0
    rw [winPiece]
    by_cases hc : blkAlpha P N i ≤ y + blkCtr P N i ∧ y + blkCtr P N i ≤ blkBeta P N i
    · exfalso
      have h := abs_sub_blkCtr_le P N i (y + blkCtr P N i) hc.1 hc.2
      have hy' : |y| ≤ (blkRad P N : ℤ) := by
        have : (y + blkCtr P N i) - blkCtr P N i = y := by ring
        rwa [this] at h
      have h3 : ((y.natAbs : ℕ) : ℤ) ≤ (blkRad P N : ℤ) := by
        rw [Int.natCast_natAbs]; exact hy'
      omega
    · exact if_neg hc
  have hψmem : MemLp (fun y : ℤ => blkPiece P N g i (y + blkCtr P N i)) 2 Measure.count :=
    memLp_two_of_supportIn_bound hψs fun y => by
      rw [blkPiece]
      split
      · exact norm_le_sqrt_l2sq hg _
      · simp
  have hχ1 : ∀ y : ℤ, ‖winPiece P N h i (y + blkCtr P N i)‖ ≤ 1 :=
    fun y => norm_winPiece_le hh i _
  have hradcast : (blkRad P N : ℝ) = (3 * (coefBd P : ℝ) + 2) * (N : ℝ) ^ P.natDegree := by
    rw [blkRad, blkLen, winBd]; push_cast; ring
  have hNd0 : (0 : ℝ) ≤ (N : ℝ) ^ P.natDegree := by positivity
  have hA1 : (N : ℝ) ^ P.natDegree / (3 * (coefBd P : ℝ) + 4) ≤ (blkRad P N : ℝ) := by
    rw [hradcast, div_le_iff₀ (by positivity)]
    nlinarith [hNd0, coefBd_pos P]
  have hA2 : (blkRad P N : ℝ) + (N : ℝ)
      ≤ (3 * (coefBd P : ℝ) + 4) * (N : ℝ) ^ P.natDegree := by
    have hNle : (N : ℝ) ≤ (N : ℝ) ^ P.natDegree := by
      have h1 : N ≤ N ^ P.natDegree := by
        calc N = N ^ 1 := (pow_one N).symm
          _ ≤ N ^ P.natDegree := Nat.pow_le_pow_right hN hP
      exact_mod_cast h1
    rw [hradcast]
    nlinarith [hNd0, hNle, coefBd_pos P]
  have hmain := hS N (blkRad P N) l (fun y : ℤ => blkPiece P N g i (y + blkCtr P N i))
    (fun y : ℤ => winPiece P N h i (y + blkCtr P N i)) hN hA1 hA2 hψs hχs hψmem hχ1 hgood
  have hshiftA : AhalfTranspose N P (fun y : ℤ => winPiece P N h i (y + blkCtr P N i))
        (fun y : ℤ => blkPiece P N g i (y + blkCtr P N i))
      = fun y : ℤ => blkDual P N h g i (y + blkCtr P N i) := by
    rw [AhalfTranspose_comp_add]; rfl
  have hLHS : (fun y : ℤ => AhalfTranspose N P
          (fun y : ℤ => winPiece P N h i (y + blkCtr P N i))
          (fun y : ℤ => blkPiece P N g i (y + blkCtr P N i)) y
        - Work.KMTContract.kmtProj ρ l ((l : ℤ) - logN N)
            (AhalfTranspose N P (fun y : ℤ => winPiece P N h i (y + blkCtr P N i))
              (fun y : ℤ => blkPiece P N g i (y + blkCtr P N i))) y)
      = fun y : ℤ => blkE P N ρ l h g i (y + blkCtr P N i) := by
    funext y
    rw [hshiftA, Work.KMTAreas.A4Z.kmtProj_comp_add]
    rfl
  rw [hLHS, Work.KMTAreas.A4Z.eLpNorm_comp_add_count] at hmain
  rw [Work.KMTAreas.A4Z.eLpNorm_comp_add_count,
    eLpNorm_two_eq_ofReal_l2norm (summable_norm_sq_blkPiece P N g i)] at hmain
  exact hmain

/-! ## `MemLp` for the pieces -/

theorem kmtProj_finset_sum_bounded {ι : Type*} (ρ : ℝ) (l : ℕ) (k : ℤ) (S : Finset ι)
    (u : ι → ℤ → ℂ) (hu : ∀ i ∈ S, Work.KMTAreas.A5.BoundedZ (u i)) :
    Work.KMTContract.kmtProj ρ l k (fun y : ℤ => ∑ i ∈ S, u i y)
      = fun y : ℤ => ∑ i ∈ S, Work.KMTContract.kmtProj ρ l k (u i) y := by
  classical
  have hbounded : ∀ s : Finset ι, (∀ i ∈ s, Work.KMTAreas.A5.BoundedZ (u i)) →
      Work.KMTAreas.A5.BoundedZ (fun y : ℤ => ∑ i ∈ s, u i y) := by
    intro s
    induction s using Finset.induction with
    | empty => intro _; exact ⟨0, by simp⟩
    | insert b t hb ih2 =>
        intro hs
        have hb1 : Work.KMTAreas.A5.BoundedZ (u b) := hs b (Finset.mem_insert_self b t)
        have hb2 : Work.KMTAreas.A5.BoundedZ (fun y : ℤ => ∑ i ∈ t, u i y) :=
          ih2 (fun i hi => hs i (Finset.mem_insert_of_mem hi))
        obtain ⟨C1, hC1⟩ := hb1
        obtain ⟨C2, hC2⟩ := hb2
        refine ⟨C1 + C2, fun y => ?_⟩
        have hstep : (fun y : ℤ => ∑ i ∈ insert b t, u i y) y
            = u b y + (fun y : ℤ => ∑ i ∈ t, u i y) y := by
          simp only [Finset.sum_insert hb, Pi.add_apply]
        rw [hstep]
        exact (norm_add_le _ _).trans (add_le_add (hC1 y) (hC2 y))
  have hmain : ∀ S : Finset ι, (∀ i ∈ S, Work.KMTAreas.A5.BoundedZ (u i)) →
      Work.KMTContract.kmtProj ρ l k (fun y : ℤ => ∑ i ∈ S, u i y)
        = fun y : ℤ => ∑ i ∈ S, Work.KMTContract.kmtProj ρ l k (u i) y := by
    intro S
    induction S using Finset.induction with
    | empty =>
        intro _
        simp only [Finset.sum_empty]
        exact Work.KMTContract.kmtProj_zero ρ l k
    | insert a s ha ih =>
        intro hu
        have hua : Work.KMTAreas.A5.BoundedZ (u a) := hu a (Finset.mem_insert_self a s)
        have hus : ∀ i ∈ s, Work.KMTAreas.A5.BoundedZ (u i) :=
          fun i hi => hu i (Finset.mem_insert_of_mem hi)
        have hsum : Work.KMTAreas.A5.BoundedZ (fun y : ℤ => ∑ i ∈ s, u i y) :=
          hbounded s hus
        funext y
        rw [show (fun y : ℤ => ∑ i ∈ insert a s, u i y)
            = u a + (fun y : ℤ => ∑ i ∈ s, u i y) from by
          funext y
          rw [Finset.sum_insert ha, Pi.add_apply]]
        rw [Work.KMTAreas.A5.kmtProj_add_bounded ρ l k hua hsum, Pi.add_apply, ih hus,
          Finset.sum_insert ha]
  exact hmain S hu

theorem boundedZ_blkDual (P : Polynomial ℤ) {N : ℕ} (hN : 1 ≤ N) {h g : ℤ → ℂ}
    (hh : ∀ x : ℤ, ‖h x‖ ≤ 1) (hg : MemLp g 2 Measure.count) (i : ℤ) :
    Work.KMTAreas.A5.BoundedZ (blkDual P N h g i) := by
  refine ⟨Real.sqrt (l2sq g), fun x => ?_⟩
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcard : ((Finset.Ioc (N / 2) N).card : ℝ) ≤ (N : ℝ) := by
    have h1 : (Finset.Ioc (N / 2) N).card ≤ N := by
      calc (Finset.Ioc (N / 2) N).card ≤ (Finset.Ioc 0 N).card :=
            Finset.card_le_card fun m hm => by
              simp only [Finset.mem_Ioc] at hm ⊢; omega
        _ = N := by simp
    exact_mod_cast h1
  rw [blkDual, AhalfTranspose]
  have hNinv : ‖(((N : ℝ)⁻¹ : ℝ) : ℂ)‖ = (N : ℝ)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc ‖(N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
        winPiece P N h i (x - (n : ℤ)) * blkPiece P N g i (x + P.eval (n : ℤ) - (n : ℤ))‖
      = (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.Ioc (N / 2) N,
          winPiece P N h i (x - (n : ℤ)) * blkPiece P N g i (x + P.eval (n : ℤ) - (n : ℤ))‖ := by
        rw [norm_mul, hNinv]
    _ ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, Real.sqrt (l2sq g) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        have h1 : ‖winPiece P N h i (x - (n : ℤ))‖ ≤ 1 := norm_winPiece_le hh i _
        have h2 : ‖blkPiece P N g i (x + P.eval (n : ℤ) - (n : ℤ))‖ ≤ Real.sqrt (l2sq g) := by
          rw [blkPiece]
          split
          · exact norm_le_sqrt_l2sq hg _
          · simp
        calc ‖winPiece P N h i (x - (n : ℤ)) * blkPiece P N g i (x + P.eval (n : ℤ) - (n : ℤ))‖
            = ‖winPiece P N h i (x - (n : ℤ))‖ * ‖blkPiece P N g i (x + P.eval (n : ℤ) - (n : ℤ))‖ :=
              norm_mul _ _
          _ ≤ 1 * Real.sqrt (l2sq g) := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
          _ = Real.sqrt (l2sq g) := one_mul _
    _ = (N : ℝ)⁻¹ * ((Finset.Ioc (N / 2) N).card : ℝ) * Real.sqrt (l2sq g) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ Real.sqrt (l2sq g) := by
        have h2 : (N : ℝ)⁻¹ * ((Finset.Ioc (N / 2) N).card : ℝ) ≤ 1 := by
          rw [inv_mul_le_iff₀ hNpos]; linarith
        calc (N : ℝ)⁻¹ * ((Finset.Ioc (N / 2) N).card : ℝ) * Real.sqrt (l2sq g)
            ≤ 1 * Real.sqrt (l2sq g) :=
              mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
          _ = Real.sqrt (l2sq g) := one_mul _

/-! ## The geometric mean -/

theorem min_le_sqrt_mul {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    min p q ≤ Real.sqrt (p * q) := by
  have h : (min p q) ^ 2 ≤ p * q := by
    rcases le_total p q with hle | hle
    · rw [min_eq_left hle]; nlinarith
    · rw [min_eq_right hle]; nlinarith
  calc min p q ≤ Real.sqrt ((min p q) ^ 2) := (Real.sqrt_sq (le_min hp hq)).ge
    _ ≤ Real.sqrt (p * q) := Real.sqrt_le_sqrt h

/-! ## The absorption of the polylogarithmic factor -/

theorem max_pow_four_le_const (c : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ l : ℕ, (max ((l : ℝ)) 1) ^ 4 ≤ K * (2 : ℝ) ^ (c * (l : ℝ)) := by
  obtain ⟨K0, hK0, hK0b⟩ := Work.KMTAreas.A5.logbPowLeConstMulRpow (P := (4 : ℝ)) (c := c / 4)
    (by norm_num) (by positivity)
  refine ⟨K0 + 1, by linarith, fun l => ?_⟩
  have hx1 : (1 : ℝ) ≤ (2 : ℝ) ^ l := one_le_pow₀ (by norm_num)
  have hlogb : Real.logb 2 ((2 : ℝ) ^ l) = (l : ℝ) := by
    rw [Real.logb, Real.log_pow]
    have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    field_simp
  have h := hK0b ((2 : ℝ) ^ l) hx1
  rw [hlogb] at h
  have hpow : ((2 : ℝ) ^ l) ^ (c / 4 * 4) = (2 : ℝ) ^ (c * (l : ℝ)) := by
    rw [← Real.rpow_natCast (2 : ℝ) l, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hpow] at h
  have hmax : (max ((l : ℝ)) 1) ^ 4 = (max 1 ((l : ℝ))) ^ (4 : ℕ) := by rw [max_comm]
  rw [hmax]
  have hconv : (max 1 ((l : ℝ))) ^ (4 : ℕ) = (max 1 ((l : ℝ))) ^ (4 : ℝ) :=
    (Real.rpow_natCast _ 4).symm
  rw [hconv]
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ (c * (l : ℝ)) := by positivity
  calc (max 1 (l : ℝ)) ^ (4 : ℝ) ≤ K0 * (2 : ℝ) ^ (c * (l : ℝ)) := h
    _ ≤ (K0 + 1) * (2 : ℝ) ^ (c * (l : ℝ)) := by nlinarith

theorem max_pow_eight_le_const (c : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ l : ℕ, (max ((l : ℝ)) 1) ^ 8 ≤ K * (2 : ℝ) ^ (c * (l : ℝ)) := by
  obtain ⟨K0, hK0, hK0b⟩ := Work.KMTAreas.A5.logbPowLeConstMulRpow (P := (8 : ℝ)) (c := c / 8)
    (by norm_num) (by positivity)
  refine ⟨K0 + 1, by linarith, fun l => ?_⟩
  have hx1 : (1 : ℝ) ≤ (2 : ℝ) ^ l := one_le_pow₀ (by norm_num)
  have hlogb : Real.logb 2 ((2 : ℝ) ^ l) = (l : ℝ) := by
    rw [Real.logb, Real.log_pow]
    have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    field_simp
  have h := hK0b ((2 : ℝ) ^ l) hx1
  rw [hlogb] at h
  have hpow : ((2 : ℝ) ^ l) ^ (c / 8 * 8) = (2 : ℝ) ^ (c * (l : ℝ)) := by
    rw [← Real.rpow_natCast (2 : ℝ) l, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hpow] at h
  have hmax : (max ((l : ℝ)) 1) ^ 8 = (max 1 ((l : ℝ))) ^ (8 : ℕ) := by rw [max_comm]
  rw [hmax]
  have hconv : (max 1 ((l : ℝ))) ^ (8 : ℕ) = (max 1 ((l : ℝ))) ^ (8 : ℝ) :=
    (Real.rpow_natCast _ 8).symm
  rw [hconv]
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ (c * (l : ℝ)) := by positivity
  calc (max 1 (l : ℝ)) ^ (8 : ℝ) ≤ K0 * (2 : ℝ) ^ (c * (l : ℝ)) := h
    _ ≤ (K0 + 1) * (2 : ℝ) ^ (c * (l : ℝ)) := by nlinarith

theorem one_div_four_le_inv_sq {m : ℤ} (hm : |((m : ℤ) : ℝ)| ≤ 1) :
    (4 : ℝ)⁻¹ ≤ ((1 + ((m : ℝ)) ^ 2)⁻¹) ^ 2 := by
  have hsq : ((m : ℝ)) ^ 2 ≤ 1 := by
    have h1 : |((m : ℤ) : ℝ)| ^ 2 ≤ 1 := by
      calc |((m : ℤ) : ℝ)| ^ 2 = |((m : ℤ) : ℝ)| * |((m : ℤ) : ℝ)| := by ring
        _ ≤ 1 * 1 := mul_self_le_mul_self (abs_nonneg _) hm
        _ = 1 := by norm_num
    rwa [sq_abs] at h1
  have h1 : (2 : ℝ)⁻¹ ≤ (1 + ((m : ℝ)) ^ 2)⁻¹ := by
    rw [inv_le_inv₀ (by norm_num) (by positivity)]
    linarith
  calc (4 : ℝ)⁻¹ = ((2 : ℝ)⁻¹) ^ 2 := by norm_num
    _ ≤ ((1 + ((m : ℝ)) ^ 2)⁻¹) ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2

theorem kernel_compare_real {x : ℝ} (hx : 1 ≤ x) :
    x ^ (-(4 : ℝ)) ≤ 4 * ((1 + x ^ 2)⁻¹ ^ 2) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have h1 : 1 + x ^ 2 ≤ 2 * x ^ 2 := by nlinarith
  have hkey : (1 + x ^ 2) ^ 2 ≤ 4 * x ^ 4 := by nlinarith [h1, hx0, sq_nonneg (x ^ 2)]
  have hx4 : (0 : ℝ) < x ^ 4 := by positivity
  have h4pos : (0 : ℝ) < 4 * ((1 + x ^ 2)⁻¹ ^ 2) := by positivity
  have hfin : ((4 : ℝ) * ((1 + x ^ 2)⁻¹ ^ 2))⁻¹ = ((1 + x ^ 2) ^ 2) / 4 := by
    rw [inv_pow, mul_inv, inv_inv]
    ring
  have hpow : x ^ (-(4 : ℝ)) = (x ^ 4)⁻¹ := by
    rw [show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx0.le,
      Real.rpow_natCast]
  rw [hpow, inv_le_comm₀ hx4 h4pos, hfin]
  linarith [hkey]

theorem kernel_compare {m : ℤ} :
    (max 1 |((m : ℤ) : ℝ)|) ^ (-(4 : ℝ)) ≤ 4 * ((1 + ((m : ℝ)) ^ 2)⁻¹ ^ 2) := by
  rcases eq_or_ne m 0 with hm0 | hm0
  · subst hm0
    norm_num
  · have hsq1 : (1 : ℝ) ≤ ((m : ℝ)) ^ 2 := by
      have h1 : (1 : ℤ) ≤ m ^ 2 := by
        rcases lt_or_gt_of_ne hm0 with h | h <;> nlinarith
      exact_mod_cast h1
    have habs : (1 : ℝ) ≤ |((m : ℤ) : ℝ)| := by
      have h2 : |((m : ℤ) : ℝ)| ^ 2 = ((m : ℝ)) ^ 2 := sq_abs _
      nlinarith [hsq1, h2, abs_nonneg ((m : ℤ) : ℝ)]
    have hmax : max 1 |((m : ℤ) : ℝ)| = |((m : ℤ) : ℝ)| := max_eq_right habs
    rw [hmax]
    have := kernel_compare_real habs
    simpa using this

theorem sivGoodMajorArcs_mono {ρ C C' : ℝ} {l : ℕ} {k : ℤ} (h : GoodMajorArcs ρ C l k)
    (hle : C' ≤ C) : GoodMajorArcs ρ C' l k := by
  rw [GoodMajorArcs] at h ⊢
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) := Real.rpow_nonneg (by norm_num) _
  linarith [h, mul_le_mul_of_nonneg_right hle h2]

theorem kmtProj_sub_bounded (ρ : ℝ) (l : ℕ) (k : ℤ) {u v : ℤ → ℂ}
    (hu : Work.KMTAreas.A5.BoundedZ u) (hv : Work.KMTAreas.A5.BoundedZ v) :
    Work.KMTContract.kmtProj ρ l k (u - v)
      = Work.KMTContract.kmtProj ρ l k u - Work.KMTContract.kmtProj ρ l k v := by
  have h1 : u - v = u + ((-1 : ℂ) • v) := by
    funext y; simp [sub_eq_add_neg]
  rw [h1, Work.KMTAreas.A5.kmtProj_add_bounded ρ l k hu
      (Work.KMTAreas.A5.boundedZ_smul (-1) hv),
    Work.KMTAreas.A5.kmtProj_smul_bounded ρ l k (-1) hv]
  funext y
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem AhalfTranspose_sub (N : ℕ) (P : Polynomial ℤ) (h u v : ℤ → ℂ) :
    AhalfTranspose N P h (u - v) = AhalfTranspose N P h u - AhalfTranspose N P h v := by
  funext y
  rw [Pi.sub_apply]
  simp only [AhalfTranspose]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [Pi.sub_apply]
  ring

theorem boundedZ_ahalfTranspose (P : Polynomial ℤ) {N : ℕ} (hN : 1 ≤ N) {h u : ℤ → ℂ}
    (hh : ∀ x : ℤ, ‖h x‖ ≤ 1) {Bv : ℝ} (hBv : 0 ≤ Bv) (hu : ∀ y : ℤ, ‖u y‖ ≤ Bv) :
    Work.KMTAreas.A5.BoundedZ (AhalfTranspose N P h u) := by
  refine ⟨Bv, fun y => ?_⟩
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcard : ((Finset.Ioc (N / 2) N).card : ℝ) ≤ (N : ℝ) := by
    have h1 : (Finset.Ioc (N / 2) N).card ≤ N := by
      calc (Finset.Ioc (N / 2) N).card ≤ (Finset.Ioc 0 N).card :=
            Finset.card_le_card fun m hm => by
              simp only [Finset.mem_Ioc] at hm ⊢; omega
        _ = N := by simp
    exact_mod_cast h1
  rw [AhalfTranspose]
  have hNinv : ‖(((N : ℝ)⁻¹ : ℝ) : ℂ)‖ = (N : ℝ)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc ‖(N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
        h (y - (n : ℤ)) * u (y + P.eval (n : ℤ) - (n : ℤ))‖
      = (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.Ioc (N / 2) N,
          h (y - (n : ℤ)) * u (y + P.eval (n : ℤ) - (n : ℤ))‖ := by
        rw [norm_mul, hNinv]
    _ ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, Bv := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (norm_sum_le (Finset.Ioc (N / 2) N)
            (fun n => h (y - (n : ℤ)) * u (y + P.eval (n : ℤ) - (n : ℤ)))).trans
          (Finset.sum_le_sum fun n _ => ?_)
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hh _)).trans (hu _)
    _ = (N : ℝ)⁻¹ * ((Finset.Ioc (N / 2) N).card : ℝ) * Bv := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ Bv := by
        have h2 : (N : ℝ)⁻¹ * ((Finset.Ioc (N / 2) N).card : ℝ) ≤ 1 := by
          rw [inv_mul_le_iff₀ hNpos]; linarith
        calc (N : ℝ)⁻¹ * ((Finset.Ioc (N / 2) N).card : ℝ) * Bv ≤ 1 * Bv :=
              mul_le_mul_of_nonneg_right h2 hBv
          _ = Bv := one_mul _

theorem sivPairDecayAux (P : Polynomial ℤ) (hP : 1 ≤ P.natDegree) {ρ : ℝ}
    (hOff : OffDecayClaim ρ) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ K : ℝ, 0 < K ∧ ∀ (N l : ℕ) (A : ℝ) (h g : ℤ → ℂ),
      1 ≤ N → 0 ≤ A → (∀ x : ℤ, ‖h x‖ ≤ 1) → MemLp g 2 Measure.count →
      GoodMajorArcs ρ Cρ l ((l : ℤ) - logN N) →
      (∀ i : ℤ, eLpNorm (blkE P N ρ l h g i) 2 Measure.count
          ≤ ENNReal.ofReal (A * l2norm (blkPiece P N g i))) →
      ∀ i j : ℤ, i + 2 ≤ j →
        ‖∑' x : ℤ, blkE P N ρ l h g i x * star (blkE P N ρ l h g j x)‖
          ≤ K * A * (max ((l : ℝ)) 1) ^ 8 * (max 1 (((j - i : ℤ)) : ℝ)) ^ (-(4 : ℝ))
              * l2norm (blkPiece P N g i) * l2norm (blkPiece P N g j) := by
  obtain ⟨Cρ, hCρ, K, hK, hpdc⟩ := sivPairDecay P hP hOff (M := 8) (by norm_num)
  refine ⟨Cρ, hCρ, K, hK, fun N l A h g hN hA hh hg hgood hE i j hij => ?_⟩
  have h' := hpdc N l A h g hN hA hh hg hgood hE i j hij
  have hpow : (max 1 (((j - i : ℤ)) : ℝ)) ^ (-((((8 : ℕ) : ℝ)) / 2))
      = (max 1 (((j - i : ℤ)) : ℝ)) ^ (-(4 : ℝ)) := by
    rw [show ((((8 : ℕ) : ℝ)) / 2) = (4 : ℝ) by norm_num]
  rw [hpow] at h'
  exact h'

theorem sivClaimZ (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree)
    (hIII : ∀ (A : ℝ), 1 ≤ A → Work.KMTAreas.A4.StructiiiAClaim P A)
    (hOff : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → Work.KMTAreas.A4.OffDecayClaim ρ) :
    Work.KMTAreas.A4.SivClaimZ P := by
  classical
  have hb : (1 : ℝ) ≤ (coefBd P : ℝ) := by exact_mod_cast coefBd_pos P
  obtain ⟨c₀, hc₀, hIIIc⟩ := hIII (3 * (coefBd P : ℝ) + 4) (by linarith)
  refine ⟨c₀ / 4, by positivity, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨Cρ₀, hCρ₀, C₀, hC₀pos, hS0⟩ := hIIIc ρ hρ0 hρ1
  obtain ⟨Cρ_pd, hCρ_pd, K_pd, hK_pd, hPD⟩ :=
    sivPairDecayAux P (by omega) (hOff ρ hρ0 hρ1)
  obtain ⟨Kabs, hKabs, hAbs⟩ := max_pow_eight_le_const (c₀ / 2) (by positivity)
  have hS₂sum : Summable (fun m : ℤ => (1 + ((m : ℝ)) ^ 2)⁻¹) :=
    Commons.Analysis.Fourier.summable_one_add_sq_int
  have hS₂sq : Summable (fun m : ℤ => ((1 + ((m : ℝ)) ^ 2)⁻¹) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hS₂sum
    have h1 : (1 + ((m : ℝ)) ^ 2)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]
      nlinarith [sq_nonneg ((m : ℝ))]
    calc ((1 + ((m : ℝ)) ^ 2)⁻¹) ^ 2
        = (1 + ((m : ℝ)) ^ 2)⁻¹ * (1 + ((m : ℝ)) ^ 2)⁻¹ := sq _
      _ ≤ 1 * (1 + ((m : ℝ)) ^ 2)⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (1 + ((m : ℝ)) ^ 2)⁻¹ := one_mul _
  set S₂ : ℝ := ∑' m : ℤ, ((1 + ((m : ℝ)) ^ 2)⁻¹) ^ 2 with hS₂def
  have hS₂0 : 0 ≤ S₂ := by rw [hS₂def]; exact tsum_nonneg fun m => by positivity
  set Ke : ℝ := max (4 * K_pd * (C₀ : ℝ) * Kabs) (4 * (C₀ : ℝ) ^ 2) + 1 with hKedef
  have hKe0 : 0 < Ke := by rw [hKedef]; positivity
  have hKe_far : 4 * K_pd * (C₀ : ℝ) * Kabs ≤ Ke := by
    rw [hKedef]
    linarith [le_max_left (4 * K_pd * (C₀ : ℝ) * Kabs) (4 * (C₀ : ℝ) ^ 2)]
  have hKe_near : 4 * (C₀ : ℝ) ^ 2 ≤ Ke := by
    rw [hKedef]
    linarith [le_max_right (4 * K_pd * (C₀ : ℝ) * Kabs) (4 * (C₀ : ℝ) ^ 2)]
  have hCpos : (0 : ℝ) < Real.sqrt (Ke * S₂) + 1 := by positivity
  set Cc : NNReal := ⟨Real.sqrt (Ke * S₂) + 1, le_of_lt hCpos⟩ with hCcdef
  have hCc : (Cc : ENNReal) = ENNReal.ofReal (Real.sqrt (Ke * S₂) + 1) := by
    rw [hCcdef]
    exact ENNReal.ofReal_coe_nnreal.symm
  refine ⟨max Cρ₀ Cρ_pd, by positivity, Cc, ?_, ?_⟩
  · rw [hCcdef]
    exact_mod_cast hCpos
  intro N l g h hN hg hh hgood
  have hgood₀ : GoodMajorArcs ρ Cρ₀ l ((l : ℤ) - logN N) :=
    sivGoodMajorArcs_mono hgood (le_max_left _ _)
  have hgood_pd : GoodMajorArcs ρ Cρ_pd l ((l : ℤ) - logN N) :=
    sivGoodMajorArcs_mono hgood (le_max_right _ _)
  set T : ℝ := (2 : ℝ) ^ (-(c₀ * (l : ℝ))) with hTdef
  have hT0 : 0 < T := Real.rpow_pos_of_pos (by norm_num) _
  set A : ℝ := (C₀ : ℝ) * T with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hblk : ∀ i : ℤ, eLpNorm (blkE P N ρ l h g i) 2 Measure.count
      ≤ ENNReal.ofReal (A * l2norm (blkPiece P N g i)) := by
    intro i
    refine (eLpNorm_blkE_le P (by omega) hS0 hN l hh hg hgood₀ i).trans (le_of_eq ?_)
    rw [hAdef, hTdef, ← ENNReal.ofReal_coe_nnreal (p := C₀),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (C₀ : ℝ)),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (C₀ : ℝ) * (2 : ℝ) ^ (-(c₀ * (l : ℝ))))]
  set κ : ℤ → ℝ :=
    fun m => Ke * (2 : ℝ) ^ (-(c₀ / 2 * (l : ℝ))) * ((1 + ((m : ℝ)) ^ 2)⁻¹) ^ 2 with hκdef
  have hκ0 : ∀ m : ℤ, 0 ≤ κ m := by intro m; rw [hκdef]; positivity
  have hκsum : Summable κ := by
    rw [hκdef]
    exact hS₂sq.mul_left _
  have hpair : ∀ i j : ℤ, ‖∑' x : ℤ, blkE P N ρ l h g i x * star (blkE P N ρ l h g j x)‖
      ≤ κ (i - j) * l2norm (blkPiece P N g i) * l2norm (blkPiece P N g j) := by
    intro i j
    set ai := l2norm (blkPiece P N g i) with hai
    set aj := l2norm (blkPiece P N g j) with haj
    have hai0 : 0 ≤ ai := by rw [hai]; exact l2norm_nonneg _
    have haj0 : 0 ≤ aj := by rw [haj]; exact l2norm_nonneg _
    have hP : ‖∑' x : ℤ, blkE P N ρ l h g i x * star (blkE P N ρ l h g j x)‖
        ≤ A * A * (ai * aj) := by
      have h := enorm_pairing_le_mul (u := blkE P N ρ l h g i) (v := blkE P N ρ l h g j)
        (A := A * ai) (A' := A * aj) (mul_nonneg hA0 hai0) (mul_nonneg hA0 haj0)
        (hblk i) (hblk j)
      calc _ ≤ (A * ai) * (A * aj) := h
        _ = A * A * (ai * aj) := by ring
    -- the near-diagonal arithmetic: `A * A ≤ κ m` for `|m| ≤ 1`
    have hslack : ∀ m : ℤ, |(((m : ℤ)) : ℝ)| ≤ 1 → A * A ≤ κ m := by
      intro m hm
      rw [hAdef, hTdef, hκdef]
      have hXX : (2 : ℝ) ^ (-(c₀ * (l : ℝ))) * (2 : ℝ) ^ (-(c₀ * (l : ℝ)))
          = (2 : ℝ) ^ (-(2 * c₀ * (l : ℝ))) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
      have hle1 : (2 : ℝ) ^ (-(2 * c₀ * (l : ℝ))) ≤ (2 : ℝ) ^ (-(c₀ / 2 * (l : ℝ))) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        nlinarith [hc₀, (show (0 : ℝ) ≤ (l : ℝ) from Nat.cast_nonneg l)]
      have h4 : (C₀ : ℝ) ^ 2 ≤ Ke * ((1 + (((m : ℤ)) : ℝ) ^ 2)⁻¹) ^ 2 := by
        have h1 := one_div_four_le_inv_sq hm
        nlinarith [h1, hKe_near]
      calc ((C₀ : ℝ) * (2 : ℝ) ^ (-(c₀ * (l : ℝ))))
            * ((C₀ : ℝ) * (2 : ℝ) ^ (-(c₀ * (l : ℝ))))
          = ((C₀ : ℝ) ^ 2)
              * ((2 : ℝ) ^ (-(c₀ * (l : ℝ))) * (2 : ℝ) ^ (-(c₀ * (l : ℝ)))) := by ring
        _ = ((C₀ : ℝ) ^ 2) * (2 : ℝ) ^ (-(2 * c₀ * (l : ℝ))) := by rw [hXX]
        _ ≤ ((C₀ : ℝ) ^ 2) * (2 : ℝ) ^ (-(c₀ / 2 * (l : ℝ))) :=
            mul_le_mul_of_nonneg_left hle1 (by positivity)
        _ ≤ (Ke * ((1 + (((m : ℤ)) : ℝ) ^ 2)⁻¹) ^ 2)
              * (2 : ℝ) ^ (-(c₀ / 2 * (l : ℝ))) :=
            mul_le_mul_of_nonneg_right h4 (by positivity)
        _ = Ke * (2 : ℝ) ^ (-(c₀ / 2 * (l : ℝ)))
              * ((1 + (((m : ℤ)) : ℝ) ^ 2)⁻¹) ^ 2 := by ring
    rcases lt_trichotomy i j with hij | heq | hji
    · by_cases h2 : i + 2 ≤ j
      · -- far case: the pair decay of `hPD`
        have hQ := hPD N l A h g hN hA0 hh hg hgood_pd hblk i j h2
        have hQ' : ‖∑' x : ℤ, blkE P N ρ l h g i x * star (blkE P N ρ l h g j x)‖
            ≤ K_pd * A * (max ((l : ℝ)) 1) ^ 8
              * (max 1 |(((j - i : ℤ)) : ℝ)|) ^ (-(4 : ℝ)) * (ai * aj) := by
          refine hQ.trans (le_of_eq ?_)
          have habs : |(((j - i : ℤ)) : ℝ)| = (((j - i : ℤ)) : ℝ) :=
            abs_of_nonneg (by exact_mod_cast (show (0 : ℤ) ≤ j - i by omega))
          rw [habs]
          simp only [hai, haj]
          ring
        refine hQ'.trans ?_
        rw [show κ (i - j) * ai * aj = κ (i - j) * (ai * aj) by ring]
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hai0 haj0)
        rw [hκdef, hAdef, hTdef]
        calc K_pd * ((C₀ : ℝ) * (2 : ℝ) ^ (-(c₀ * (l : ℝ)))) * (max ((l : ℝ)) 1) ^ 8
              * (max 1 |(((j - i : ℤ)) : ℝ)|) ^ (-(4 : ℝ))
            ≤ K_pd * ((C₀ : ℝ) * (2 : ℝ) ^ (-(c₀ * (l : ℝ))))
              * (Kabs * (2 : ℝ) ^ ((c₀ / 2) * (l : ℝ)))
              * (max 1 |(((j - i : ℤ)) : ℝ)|) ^ (-(4 : ℝ)) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              exact mul_le_mul_of_nonneg_left (hAbs l) (by positivity)
          _ = K_pd * (C₀ : ℝ) * Kabs * (2 : ℝ) ^ (-(c₀ / 2 * (l : ℝ)))
              * (max 1 |(((j - i : ℤ)) : ℝ)|) ^ (-(4 : ℝ)) := by
              have hexp : (2 : ℝ) ^ (-(c₀ * (l : ℝ))) * (2 : ℝ) ^ ((c₀ / 2) * (l : ℝ))
                  = (2 : ℝ) ^ (-(c₀ / 2 * (l : ℝ))) := by
                rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
                congr 1
                ring
              rw [← hexp]
              ring
          _ ≤ K_pd * (C₀ : ℝ) * Kabs * (2 : ℝ) ^ (-(c₀ / 2 * (l : ℝ)))
              * (4 * ((1 + (((i - j : ℤ)) : ℝ) ^ 2)⁻¹) ^ 2) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have h := kernel_compare (m := i - j)
              have habs2 : |(((j - i : ℤ)) : ℝ)| = |(((i - j : ℤ)) : ℝ)| := by
                rw [show (((j - i : ℤ)) : ℝ) = -(((i - j : ℤ)) : ℝ) by push_cast; ring,
                  abs_neg]
              rw [habs2]
              exact h
          _ ≤ Ke * (2 : ℝ) ^ (-(c₀ / 2 * (l : ℝ)))
              * ((1 + (((i - j : ℤ)) : ℝ) ^ 2)⁻¹) ^ 2 := by
              have h4 : K_pd * (C₀ : ℝ) * Kabs * 4 ≤ Ke := by linarith [hKe_far]
              have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (-(c₀ / 2 * (l : ℝ)))
                  * ((1 + (((i - j : ℤ)) : ℝ) ^ 2)⁻¹) ^ 2 := by positivity
              nlinarith [h4, hpos]
      · -- near case: `j ≤ i + 1`
        have hm1 : |(((i - j : ℤ)) : ℝ)| ≤ 1 := by
          have h3 : |(i - j : ℤ)| ≤ 1 := by
            rw [abs_le]
            constructor <;> omega
          exact_mod_cast h3
        refine hP.trans ?_
        rw [show κ (i - j) * ai * aj = κ (i - j) * (ai * aj) by ring]
        exact mul_le_mul_of_nonneg_right (hslack (i - j) hm1) (mul_nonneg hai0 haj0)
    · -- `i = j`
      subst heq
      have hm1 : |(((i - i : ℤ)) : ℝ)| ≤ 1 := by simp
      refine hP.trans ?_
      rw [show κ (i - i) * ai * aj = κ (i - i) * (ai * aj) by ring]
      exact mul_le_mul_of_nonneg_right (hslack (i - i) hm1) (mul_nonneg hai0 haj0)
    · by_cases h2 : j + 2 ≤ i
      · -- far case: apply the pair decay to the pair `(j, i)`
        have hQ := hPD N l A h g hN hA0 hh hg hgood_pd hblk j i h2
        rw [norm_pairing_comm (blkE P N ρ l h g j) (blkE P N ρ l h g i)] at hQ
        have hQ' : ‖∑' x : ℤ, blkE P N ρ l h g i x * star (blkE P N ρ l h g j x)‖
            ≤ K_pd * A * (max ((l : ℝ)) 1) ^ 8
              * (max 1 |(((i - j : ℤ)) : ℝ)|) ^ (-(4 : ℝ)) * (ai * aj) := by
          refine hQ.trans (le_of_eq ?_)
          have habs : |(((i - j : ℤ)) : ℝ)| = (((i - j : ℤ)) : ℝ) :=
            abs_of_nonneg (by exact_mod_cast (show (0 : ℤ) ≤ i - j by omega))
          rw [habs]
          simp only [hai, haj]
          ring
        refine hQ'.trans ?_
        rw [show κ (i - j) * ai * aj = κ (i - j) * (ai * aj) by ring]
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hai0 haj0)
        rw [hκdef, hAdef, hTdef]
        calc K_pd * ((C₀ : ℝ) * (2 : ℝ) ^ (-(c₀ * (l : ℝ)))) * (max ((l : ℝ)) 1) ^ 8
              * (max 1 |(((i - j : ℤ)) : ℝ)|) ^ (-(4 : ℝ))
            ≤ K_pd * ((C₀ : ℝ) * (2 : ℝ) ^ (-(c₀ * (l : ℝ))))
              * (Kabs * (2 : ℝ) ^ ((c₀ / 2) * (l : ℝ)))
              * (max 1 |(((i - j : ℤ)) : ℝ)|) ^ (-(4 : ℝ)) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              exact mul_le_mul_of_nonneg_left (hAbs l) (by positivity)
          _ = K_pd * (C₀ : ℝ) * Kabs * (2 : ℝ) ^ (-(c₀ / 2 * (l : ℝ)))
              * (max 1 |(((i - j : ℤ)) : ℝ)|) ^ (-(4 : ℝ)) := by
              have hexp : (2 : ℝ) ^ (-(c₀ * (l : ℝ))) * (2 : ℝ) ^ ((c₀ / 2) * (l : ℝ))
                  = (2 : ℝ) ^ (-(c₀ / 2 * (l : ℝ))) := by
                rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
                congr 1
                ring
              rw [← hexp]
              ring
          _ ≤ K_pd * (C₀ : ℝ) * Kabs * (2 : ℝ) ^ (-(c₀ / 2 * (l : ℝ)))
              * (4 * ((1 + (((i - j : ℤ)) : ℝ) ^ 2)⁻¹) ^ 2) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact kernel_compare (m := i - j)
          _ ≤ Ke * (2 : ℝ) ^ (-(c₀ / 2 * (l : ℝ)))
              * ((1 + (((i - j : ℤ)) : ℝ) ^ 2)⁻¹) ^ 2 := by
              have h4 : K_pd * (C₀ : ℝ) * Kabs * 4 ≤ Ke := by linarith [hKe_far]
              have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (-(c₀ / 2 * (l : ℝ)))
                  * ((1 + (((i - j : ℤ)) : ℝ) ^ 2)⁻¹) ^ 2 := by positivity
              nlinarith [h4, hpos]
      · -- near case: `i ≤ j + 1`
        have hm1 : |(((i - j : ℤ)) : ℝ)| ≤ 1 := by
          have h3 : |(i - j : ℤ)| ≤ 1 := by
            rw [abs_le]
            constructor <;> omega
          exact_mod_cast h3
        refine hP.trans ?_
        rw [show κ (i - j) * ai * aj = κ (i - j) * (ai * aj) by ring]
        exact mul_le_mul_of_nonneg_right (hslack (i - j) hm1) (mul_nonneg hai0 haj0)
  -- the Schur bound for a finite set of blocks
  have hSchur : ∀ S : Finset ℤ,
      eLpNorm (fun y : ℤ => ∑ i ∈ S, blkE P N ρ l h g i y) 2 Measure.count
        ≤ ENNReal.ofReal (Real.sqrt (Ke * S₂) + 1)
            * ENNReal.ofReal ((2 : ℝ) ^ (-(c₀ / 4 * (l : ℝ)))) * eLpNorm g 2 Measure.count := by
    intro S
    have hu : ∀ i ∈ S, Summable (fun x : ℤ => ‖blkE P N ρ l h g i x‖ ^ 2) := by
      intro i _
      have h1 : eLpNorm (blkE P N ρ l h g i) 2 Measure.count < ⊤ :=
        lt_of_le_of_lt (hblk i) ENNReal.ofReal_lt_top
      exact memLp_two_count_summable_norm_sq
        (MeasureTheory.memLp_iff.mpr h1)
    have hsch := Work.KMTAreas.A4Z.schur_finite S (fun i x => blkE P N ρ l h g i x)
      (fun i => l2norm (blkPiece P N g i)) κ (fun i => l2norm_nonneg _) hκ0 hκsum hu
      (fun i _ j _ => hpair i j)
    have hl2 : (∑ i ∈ S, (l2norm (blkPiece P N g i)) ^ 2) ≤ ∑' x : ℤ, ‖g x‖ ^ 2 := by
      have h1 : ∀ i : ℤ, (l2norm (blkPiece P N g i)) ^ 2 = l2sq (blkPiece P N g i) :=
        fun i => sq_l2norm (summable_norm_sq_blkPiece P N g i)
      rw [Finset.sum_congr rfl fun i _ => h1 i]
      exact sum_l2sq_blkPiece_le P N hN (memLp_two_count_summable_norm_sq hg) S
    have hsumκ : (∑' m : ℤ, κ m) = Ke * (2 : ℝ) ^ (-(c₀ / 2 * (l : ℝ))) * S₂ := by
      rw [hκdef, hS₂def, tsum_mul_left]
    have hbound : (∑' m : ℤ, κ m) * (∑ i ∈ S, (l2norm (blkPiece P N g i)) ^ 2)
        ≤ Ke * (2 : ℝ) ^ (-(c₀ / 2 * (l : ℝ))) * S₂ * (∑' x : ℤ, ‖g x‖ ^ 2) := by
      rw [hsumκ]
      exact mul_le_mul_of_nonneg_left hl2 (by positivity)
    have hl2sum : Summable (fun x : ℤ => ‖∑ i ∈ S, blkE P N ρ l h g i x‖ ^ 2) := by
      have hmem : MemLp (fun x : ℤ => ∑ i ∈ S, blkE P N ρ l h g i x) 2 Measure.count := by
        have heq : (fun x : ℤ => ∑ i ∈ S, blkE P N ρ l h g i x)
            = ∑ i ∈ S, blkE P N ρ l h g i := by
          funext x
          simp only [Finset.sum_apply]
        rw [heq]
        refine MeasureTheory.memLp_iff.mpr ?_
        refine lt_of_le_of_lt (eLpNorm_sum_le (μ := Measure.count) (p := (2 : ENNReal))
          (s := S) (f := fun i => blkE P N ρ l h g i) (by norm_num)) ?_
        exact ENNReal.sum_lt_top.mpr fun i _ => lt_of_le_of_lt (hblk i) ENNReal.ofReal_lt_top
      exact memLp_two_count_summable_norm_sq hmem
    have hstep : eLpNorm (fun y : ℤ => ∑ i ∈ S, blkE P N ρ l h g i y) 2 Measure.count
        ≤ ENNReal.ofReal (Real.sqrt (Ke * S₂) * (2 : ℝ) ^ (-(c₀ / 4 * (l : ℝ)))
            * Real.sqrt (∑' x : ℤ, ‖g x‖ ^ 2)) := by
      rw [eLpNorm_two_eq_ofReal_l2norm hl2sum, l2norm, l2sq]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      refine (hsch.trans hbound).trans (le_of_eq ?_)
      rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg (le_of_lt hKe0) hS₂0),
        Real.sq_sqrt (tsum_nonneg fun x => sq_nonneg _),
        show ((2 : ℝ) ^ (-(c₀ / 4 * (l : ℝ)))) ^ 2 = (2 : ℝ) ^ (-(c₀ / 2 * (l : ℝ))) by
          rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(c₀ / 4 * (l : ℝ)))) 2,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          ring]
      ring
    have hZ : eLpNorm g 2 Measure.count
        = ENNReal.ofReal (Real.sqrt (∑' x : ℤ, ‖g x‖ ^ 2)) := by
      rw [eLpNorm_two_eq_ofReal_l2norm (memLp_two_count_summable_norm_sq hg), l2norm, l2sq]
    have hprod : ENNReal.ofReal (Real.sqrt (Ke * S₂) + 1)
          * ENNReal.ofReal ((2 : ℝ) ^ (-(c₀ / 4 * (l : ℝ))))
          * ENNReal.ofReal (Real.sqrt (∑' x : ℤ, ‖g x‖ ^ 2))
        = ENNReal.ofReal ((Real.sqrt (Ke * S₂) + 1) * (2 : ℝ) ^ (-(c₀ / 4 * (l : ℝ)))
            * Real.sqrt (∑' x : ℤ, ‖g x‖ ^ 2)) := by
      rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ Real.sqrt (Ke * S₂) + 1 by positivity)]
      rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (Real.sqrt (Ke * S₂) + 1)
        * (2 : ℝ) ^ (-(c₀ / 4 * (l : ℝ))) by positivity)]
    calc eLpNorm (fun y : ℤ => ∑ i ∈ S, blkE P N ρ l h g i y) 2 Measure.count
        ≤ ENNReal.ofReal (Real.sqrt (Ke * S₂) * (2 : ℝ) ^ (-(c₀ / 4 * (l : ℝ)))
            * Real.sqrt (∑' x : ℤ, ‖g x‖ ^ 2)) := hstep
      _ ≤ ENNReal.ofReal ((Real.sqrt (Ke * S₂) + 1) * (2 : ℝ) ^ (-(c₀ / 4 * (l : ℝ)))
            * Real.sqrt (∑' x : ℤ, ‖g x‖ ^ 2)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(c₀ / 4 * (l : ℝ))) := by positivity
          have h2 : (0 : ℝ) ≤ Real.sqrt (∑' x : ℤ, ‖g x‖ ^ 2) := Real.sqrt_nonneg _
          nlinarith [h1, h2, Real.sqrt_nonneg (Ke * S₂)]
      _ = ENNReal.ofReal (Real.sqrt (Ke * S₂) + 1)
            * ENNReal.ofReal ((2 : ℝ) ^ (-(c₀ / 4 * (l : ℝ))))
            * eLpNorm g 2 Measure.count := by
          rw [hZ, ← hprod]
  -- the limit step
  set gK : ℕ → ℤ → ℂ := fun K y => ∑ i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
    blkPiece P N g i y with hgKdef
  have hKeS0 : 0 < Real.sqrt (Ke * S₂) + 1 := by positivity
  obtain ⟨Cp, hCp0, hCp⟩ := Work.KMTAreas.A7.KmtProjCrude (ρ := ρ) l ((l : ℤ) - logN N)
    (q := 2) (by norm_num)
  set kk : ℤ := (l : ℤ) - logN N with hkk
  have hCp' : ∀ f : ℤ → ℂ, eLpNorm (Work.KMTContract.kmtProj ρ l kk f) 2 Measure.count
      ≤ (Cp : ENNReal) * eLpNorm f 2 Measure.count := by
    intro f
    have h := hCp f
    rw [show ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) from by norm_num,
      ENNReal.ofReal_coe_nnreal] at h
    exact h
  have hCop : ∀ u : ℤ → ℂ, eLpNorm (fun y : ℤ => AhalfTranspose N P h u y
      - Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h u) y) 2 Measure.count
      ≤ (1 + (Cp : ENNReal)) * eLpNorm u 2 Measure.count := by
    intro u
    calc eLpNorm (fun y : ℤ => AhalfTranspose N P h u y
          - Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h u) y) 2 Measure.count
        ≤ eLpNorm (AhalfTranspose N P h u) 2 Measure.count
          + eLpNorm (Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h u)) 2 Measure.count :=
          eLpNorm_sub_le (by norm_num)
      _ ≤ eLpNorm u 2 Measure.count
          + (Cp : ENNReal) * eLpNorm (AhalfTranspose N P h u) 2 Measure.count :=
          add_le_add (eLpNorm_ahalfTranspose_le_of_bdd N P hh) (hCp' _)
      _ ≤ eLpNorm u 2 Measure.count + (Cp : ENNReal) * eLpNorm u 2 Measure.count :=
          add_le_add le_rfl (mul_le_mul' le_rfl (eLpNorm_ahalfTranspose_le_of_bdd N P hh))
      _ = (1 + (Cp : ENNReal)) * eLpNorm u 2 Measure.count := by ring
  set B : ENNReal := ENNReal.ofReal (Real.sqrt (Ke * S₂) + 1)
      * ENNReal.ofReal ((2 : ℝ) ^ (-(c₀ / 4 * (l : ℝ)))) * eLpNorm g 2 Measure.count with hBdef
  -- the block truncations
  have hgK_le : ∀ K : ℕ, ∀ y : ℤ, ‖gK K y‖ ≤ Real.sqrt (l2sq g) := by
    intro K y
    have h1 : gK K y = if y / (blkLen P N : ℤ) ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)
        then g y else 0 := by
      rw [hgKdef]
      exact sum_blkPiece_eq P N hN g _ y
    rw [h1]
    by_cases h : y / (blkLen P N : ℤ) ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)
    · rw [if_pos h]; exact norm_le_sqrt_l2sq hg y
    · rw [if_neg h]; simp
  have hSchurK : ∀ K : ℕ, eLpNorm (fun y : ℤ => AhalfTranspose N P h (gK K) y
        - Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h (gK K)) y) 2 Measure.count
      ≤ B := by
    intro K
    have hid : (fun y : ℤ => AhalfTranspose N P h (gK K) y
          - Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h (gK K)) y)
        = fun y : ℤ => ∑ i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), blkE P N ρ l h g i y := by
      funext y
      have h1 : AhalfTranspose N P h (gK K)
          = ∑ i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), blkDual P N h g i := by
        funext z
        simp only [Finset.sum_apply]
        rw [hgKdef]
        exact (sum_blkDual_finset P (by omega) N hN (Finset.Icc (-(K : ℤ)) (K : ℤ)) h g z).symm
      have h2 : Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h (gK K))
          = ∑ i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
              Work.KMTContract.kmtProj ρ l kk (blkDual P N h g i) := by
        rw [h1]
        have hb : (fun y : ℤ => ∑ i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), blkDual P N h g i y)
            = ∑ i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), blkDual P N h g i := by
          funext z
          simp only [Finset.sum_apply]
        have hb2 : (fun y : ℤ => ∑ i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
              Work.KMTContract.kmtProj ρ l kk (blkDual P N h g i) y)
            = ∑ i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
              Work.KMTContract.kmtProj ρ l kk (blkDual P N h g i) := by
          funext z
          simp only [Finset.sum_apply]
        rw [← hb, ← hb2]
        exact kmtProj_finset_sum_bounded ρ l kk (Finset.Icc (-(K : ℤ)) (K : ℤ))
          (fun i x => blkDual P N h g i x) (fun i _ => boundedZ_blkDual P hN hh hg i)
      rw [congrFun h1 y, congrFun h2 y]
      simp only [Finset.sum_apply]
      rw [← Finset.sum_sub_distrib]
      rfl
    rw [hid]
    exact hSchur _
  have hdiff : ∀ K : ℕ, eLpNorm (fun y : ℤ => (AhalfTranspose N P h g y
        - Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h g) y)
        - (AhalfTranspose N P h (gK K) y
          - Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h (gK K)) y)) 2 Measure.count
      ≤ (1 + (Cp : ENNReal)) * eLpNorm (fun y : ℤ => g y - gK K y) 2 Measure.count := by
    intro K
    have hA : AhalfTranspose N P h (fun z : ℤ => g z - gK K z)
        = AhalfTranspose N P h g - AhalfTranspose N P h (gK K) :=
      AhalfTranspose_sub N P h g (gK K)
    have hA2 : Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h (fun z : ℤ => g z - gK K z))
        = Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h g)
          - Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h (gK K)) := by
      rw [hA]
      exact kmtProj_sub_bounded ρ l kk
        (boundedZ_ahalfTranspose P hN hh (Real.sqrt_nonneg _) (norm_le_sqrt_l2sq hg))
        (boundedZ_ahalfTranspose P hN hh (Real.sqrt_nonneg _) (hgK_le K))
    have heq : (fun y : ℤ => (AhalfTranspose N P h g y
            - Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h g) y)
          - (AhalfTranspose N P h (gK K) y
            - Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h (gK K)) y))
        = fun y : ℤ => AhalfTranspose N P h (fun z : ℤ => g z - gK K z) y
            - Work.KMTContract.kmtProj ρ l kk
                (AhalfTranspose N P h (fun z : ℤ => g z - gK K z)) y := by
      funext y
      rw [congrFun hA y, congrFun hA2 y]
      simp only [Pi.sub_apply]
      ring
    rw [heq]
    exact hCop (fun z : ℤ => g z - gK K z)
  have hgdiff : ∀ K : ℕ, (fun y : ℤ => ‖g y - gK K y‖ ^ 2)
      = fun y : ℤ => (if y ∈ Finset.Ico (-((K : ℤ) * (blkLen P N : ℤ)))
          (((K : ℤ) + 1) * (blkLen P N : ℤ)) then 0 else ‖g y‖ ^ 2) := by
    intro K
    funext y
    have h1 : gK K y = if y / (blkLen P N : ℤ) ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)
        then g y else 0 := by
      rw [hgKdef]; exact sum_blkPiece_eq P N hN g _ y
    rw [h1]
    by_cases h : y ∈ Finset.Ico (-((K : ℤ) * (blkLen P N : ℤ)))
        (((K : ℤ) + 1) * (blkLen P N : ℤ))
    · have hm : y / (blkLen P N : ℤ) ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) :=
        (ediv_mem_Icc_iff (blkLen_pos_int P hN) (K : ℤ) y).mpr h
      rw [if_pos hm, if_pos h]; simp
    · have hm : ¬ (y / (blkLen P N : ℤ) ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)) :=
        fun hc => h ((ediv_mem_Icc_iff (blkLen_pos_int P hN) (K : ℤ) y).mp hc)
      rw [if_neg hm, if_neg h]; simp
  have hL1 : (1 : ℤ) ≤ (blkLen P N : ℤ) := by
    have h1 : 1 ≤ blkLen P N := by
      rw [blkLen]
      have h2 : 1 ≤ 2 * coefBd P + 2 := by have := coefBd_pos P; omega
      have h3 : 1 ≤ N ^ P.natDegree := one_le_pow₀ hN
      calc (1 : ℕ) = 1 * 1 := by ring
        _ ≤ (2 * coefBd P + 2) * N ^ P.natDegree := Nat.mul_le_mul h2 h3
    exact_mod_cast h1
  have htail0 : Filter.Tendsto (fun K : ℕ => l2sq (fun y : ℤ => g y - gK K y))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun K : ℕ => ∑' y : ℤ,
        (if y ∈ Finset.Ico (-((K : ℤ) * (blkLen P N : ℤ)))
          (((K : ℤ) + 1) * (blkLen P N : ℤ)) then 0 else ‖g y‖ ^ 2))
        Filter.atTop (nhds 0) :=
      tendsto_tail_Ico (fun y : ℤ => ‖g y‖ ^ 2) (memLp_two_count_summable_norm_sq hg)
        (fun y => sq_nonneg _) hL1
    refine h1.congr' ?_
    filter_upwards with K
    rw [l2sq]
    exact tsum_congr fun y => (congrFun (hgdiff K) y).symm
  have htail : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ,
      (1 + (Cp : ENNReal)) * eLpNorm (fun y : ℤ => g y - gK K y) 2 Measure.count
        ≤ ENNReal.ofReal ε := by
    intro ε hε
    have h1 : ∀ᶠ K : ℕ in Filter.atTop, l2sq (fun y : ℤ => g y - gK K y)
        ≤ (ε / (1 + (Cp : ℝ))) ^ 2 := by
      have h2 : (0 : ℝ) < (ε / (1 + (Cp : ℝ))) ^ 2 := by
        have : (0 : ℝ) < ε / (1 + (Cp : ℝ)) := by
          apply div_pos hε
          have := hCp0
          push_cast
          positivity
        positivity
      exact (Metric.tendsto_nhds.mp htail0 _ h2).mono fun K hK => by
        rw [Real.dist_eq, sub_zero] at hK
        exact le_of_lt (lt_of_abs_lt hK)
    obtain ⟨K, hK⟩ := Filter.Eventually.exists h1
    refine ⟨K, ?_⟩
    have hsum : Summable (fun y : ℤ => ‖g y - gK K y‖ ^ 2) := by
      refine Summable.of_nonneg_of_le (fun y => by positivity) (fun y => ?_)
        (memLp_two_count_summable_norm_sq hg)
      rw [congrFun (hgdiff K) y]
      by_cases h : y ∈ Finset.Ico (-((K : ℤ) * (blkLen P N : ℤ)))
          (((K : ℤ) + 1) * (blkLen P N : ℤ))
      · rw [if_pos h]
        exact sq_nonneg _
      · rw [if_neg h]
    have heL : eLpNorm (fun y : ℤ => g y - gK K y) 2 Measure.count
        = ENNReal.ofReal (Real.sqrt (l2sq (fun y : ℤ => g y - gK K y))) :=
      eLpNorm_two_eq_ofReal_l2norm hsum
    have hε0 : (0 : ℝ) ≤ ε / (1 + (Cp : ℝ)) := by
      apply div_nonneg hε.le
      have := hCp0
      push_cast
      positivity
    have hsqrt : Real.sqrt (l2sq (fun y : ℤ => g y - gK K y)) ≤ ε / (1 + (Cp : ℝ)) := by
      refine Real.sqrt_le_iff.mpr ⟨hε0, ?_⟩
      calc l2sq (fun y : ℤ => g y - gK K y) ≤ (ε / (1 + (Cp : ℝ))) ^ 2 := hK
        _ = (ε / (1 + (Cp : ℝ))) ^ 2 := rfl
    rw [heL]
    have hcomb : (1 + (Cp : ENNReal)) * ENNReal.ofReal (Real.sqrt (l2sq (fun y : ℤ => g y - gK K y)))
        ≤ ENNReal.ofReal ((1 + (Cp : ℝ)) * (ε / (1 + (Cp : ℝ)))) := by
      have hone : (1 + (Cp : ENNReal)) = ENNReal.ofReal (1 + (Cp : ℝ)) := by
        rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_one,
          ENNReal.ofReal_coe_nnreal]
      rw [hone, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 + (Cp : ℝ))]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hsqrt (by positivity))
    refine hcomb.trans (le_of_eq ?_)
    have hpos : (1 + (Cp : ℝ)) ≠ 0 := by
      have := hCp0; push_cast; positivity
    rw [show (1 + (Cp : ℝ)) * (ε / (1 + (Cp : ℝ))) = ε by field_simp]
  have hfinal : eLpNorm (fun y : ℤ => AhalfTranspose N P h g y
      - Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h g) y) 2 Measure.count ≤ B := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨K, hK⟩ := htail (ε : ℝ) (by exact_mod_cast hε)
    have htri : eLpNorm (fun y : ℤ => AhalfTranspose N P h g y
        - Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h g) y) 2 Measure.count
        ≤ eLpNorm (fun y : ℤ => (AhalfTranspose N P h g y
            - Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h g) y)
            - (AhalfTranspose N P h (gK K) y
              - Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h (gK K)) y)) 2 Measure.count
          + eLpNorm (fun y : ℤ => AhalfTranspose N P h (gK K) y
              - Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h (gK K)) y) 2 Measure.count := by
      have hadd := eLpNorm_add_le (μ := Measure.count) (p := (2 : ENNReal))
        (f := fun y : ℤ => (AhalfTranspose N P h g y
            - Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h g) y)
            - (AhalfTranspose N P h (gK K) y
              - Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h (gK K)) y))
          (g := fun y : ℤ => AhalfTranspose N P h (gK K) y
              - Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h (gK K)) y) (by norm_num : (1 : ENNReal) ≤ 2)
      have hFG : (fun y : ℤ => (AhalfTranspose N P h g y
              - Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h g) y)
              - (AhalfTranspose N P h (gK K) y
                - Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h (gK K)) y))
          + (fun y : ℤ => AhalfTranspose N P h (gK K) y
                - Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h (gK K)) y)
        = fun y : ℤ => AhalfTranspose N P h g y
            - Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h g) y := by
        funext y
        simp only [Pi.add_apply]
        ring
      rw [hFG] at hadd
      exact hadd
    refine htri.trans (le_trans (add_le_add (hdiff K) (hSchurK K)) ?_)
    refine (add_le_add hK le_rfl).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_coe_nnreal, add_comm]
  calc eLpNorm (fun y : ℤ => AhalfTranspose N P h g y
        - Work.KMTContract.kmtProj ρ l kk (AhalfTranspose N P h g) y) 2 Measure.count
      ≤ B := hfinal
    _ = (Cc : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(c₀ / 4 * (l : ℝ))))
          * eLpNorm g 2 Measure.count := by
        rw [hBdef, hCc]

end Work.KMTAreas.A4
