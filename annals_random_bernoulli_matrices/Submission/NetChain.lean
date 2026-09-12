import Mathlib
import Submission.NetArgument
import Submission.IncompReduction
import Submission.NormalSplit
import Submission.Commons.Probability.RandomMatrix.rect_spectral_measurable

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Measure Filter unitInterval

namespace Submission.NetChain

attribute [local instance] Classical.propDecidable

open Submission.Admissible
open Submission.MagicVector
open Submission.IncompReduction
open Submission.NormalVectorMatrix (colVec colVec_coeff)
open Submission.Section5D (Acoord holeN)
open Commons.LinearAlgebra.Net (sqNorm compressible)

/-!
# The net argument: deterministic chain

The lattice approximation `spv` of the unit normal `Y_n` lies in the finite net
`NetT` built from the good set `Dset`, and the image of `spv` under the random
matrix is small whenever the spectral event holds.  This reduces the annulus
probability to a union bound over the net.
-/

/-- The finite net of lattice approximations: reorderings of good lattice
points. -/
def NetT {n : ℕ} (p : unitInterval) (s L T LAC : ℝ) (N : ℕ) (A : Fin n → Finset ℤ)
    (PiSet : Finset (Equiv.Perm (Fin n))) : Finset (Fin n → ℤ) :=
  PiSet.biUnion (fun π => (Submission.NetArgument.Dset p s L T LAC N A).image
    (fun d : Fin n → ℤ => fun i : Fin n => d (π.symm i)))

/-- Membership in the net. -/
lemma mem_NetT {n : ℕ} {p : unitInterval} {s L T LAC : ℝ} {N : ℕ} {A : Fin n → Finset ℤ}
    {PiSet : Finset (Equiv.Perm (Fin n))} {z : Fin n → ℤ} :
    z ∈ NetT p s L T LAC N A PiSet ↔
      ∃ π ∈ PiSet, (fun i : Fin n => z (π i))
        ∈ Submission.NetArgument.Dset p s L T LAC N A := by
  classical
  unfold NetT
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨π, hπ, hz⟩
    rw [Finset.mem_image] at hz
    obtain ⟨d, hd, hdz⟩ := hz
    refine ⟨π, hπ, ?_⟩
    have hdeq : (fun i : Fin n => (fun j : Fin n => d (π.symm j)) (π i)) = d := by
      funext i
      simp
    rw [← hdz, hdeq]
    exact hd
  · rintro ⟨π, hπ, hz⟩
    refine ⟨π, hπ, ?_⟩
    rw [Finset.mem_image]
    exact ⟨fun i : Fin n => z (π i), hz, by funext i; simp⟩

/-- Cardinality of the net. -/
lemma NetT_card_le {n : ℕ} (p : unitInterval) (s L T LAC : ℝ) (N : ℕ)
    (A : Fin n → Finset ℤ) (PiSet : Finset (Equiv.Perm (Fin n))) :
    (NetT p s L T LAC N A PiSet).card
      ≤ PiSet.card * (Submission.NetArgument.Dset p s L T LAC N A).card := by
  classical
  have h1 : (NetT p s L T LAC N A PiSet).card
      ≤ ∑ π ∈ PiSet, ((Submission.NetArgument.Dset p s L T LAC N A).image
          (fun d : Fin n → ℤ => fun i : Fin n => d (π.symm i))).card := by
    unfold NetT
    exact Finset.card_biUnion_le
  refine le_trans h1 ?_
  have h2 : ∀ π ∈ PiSet, ((Submission.NetArgument.Dset p s L T LAC N A).image
      (fun d : Fin n → ℤ => fun i : Fin n => d (π.symm i))).card
        ≤ (Submission.NetArgument.Dset p s L T LAC N A).card :=
    fun π _ => Finset.card_image_le
  calc (∑ π ∈ PiSet, ((Submission.NetArgument.Dset p s L T LAC N A).image
          (fun d : Fin n → ℤ => fun i : Fin n => d (π.symm i))).card)
      ≤ ∑ _π ∈ PiSet, (Submission.NetArgument.Dset p s L T LAC N A).card :=
        Finset.sum_le_sum h2
    _ = PiSet.card * (Submission.NetArgument.Dset p s L T LAC N A).card := by
        rw [Finset.sum_const, smul_eq_mul]

/-- The unit normal is orthogonal to the `(emb k)`-th column, in coordinates. -/
lemma kernel_emb {n : ℕ} (hn : 1 ≤ n) (N : Matrix (Fin n) (Fin n) ℝ) (k : Fin (n - 1)) :
    (∑ i : Fin n, N i (Submission.GeoBridge.emb k) * (nVec N).ofLp i) = 0 := by
  have hid : inner ℝ (colVec N (Submission.GeoBridge.emb k)) (nVec N)
      = ∑ i : Fin n, (colVec N (Submission.GeoBridge.emb k)).ofLp i * (nVec N).ofLp i := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.inner_apply]
  have h0 : inner ℝ (colVec N (Submission.GeoBridge.emb k)) (nVec N) = 0 := by
    have h := nVec_orthogonal_emb N k
    rwa [real_inner_comm] at h
  rw [hid] at h0
  have hsum : (∑ i : Fin n, (colVec N (Submission.GeoBridge.emb k)).ofLp i * (nVec N).ofLp i)
      = ∑ i : Fin n, N i (Submission.GeoBridge.emb k) * (nVec N).ofLp i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [colVec_coeff]
  rw [hsum] at h0
  exact h0

/-- Elementary bound `(a+b)² ≤ 2a² + 2b²`. -/
lemma sq_add_le_two (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- Splitting a sum of doubled squares. -/
lemma sum_two_sq {m : ℕ} (A B : Fin m → ℝ) :
    (∑ k : Fin m, (2 * (A k) ^ 2 + 2 * (B k) ^ 2))
      = 2 * (∑ k : Fin m, (A k) ^ 2) + 2 * (∑ k : Fin m, (B k) ^ 2) := by
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Deterministic estimate: if `y` is in the kernel of the row matrix and `spv`
is a lattice vector within `1` in `ℓ_∞` and within `C√n` in the coordinate sum,
then the row sums of `spv` are small in `ℓ₂`. -/
lemma small_image_bound {n : ℕ} (hn2 : 2 ≤ n) (B : Matrix (Fin n) (Fin n) ℝ) {s p C : ℝ}
    (hsp : |s + p| ≤ 1) {y : Fin n → ℝ}
    (hkern : ∀ k : Fin (n - 1),
      (∑ i : Fin n, (B i (Submission.GeoBridge.emb k) + s) * y i) = 0)
    {spv : Fin n → ℤ} (hd1 : ∀ i : Fin n, |y i - (spv i : ℝ)| ≤ 1)
    (hd2 : |(∑ i : Fin n, y i) - (∑ i : Fin n, (spv i : ℝ))|
      ≤ Real.sqrt ((12 : ℝ) * (n : ℝ) / 11))
    (hspec : ∀ v : Fin n → ℝ,
      (∑ k : Fin (n - 1), ((∑ i : Fin n, (B i (Submission.GeoBridge.emb k) - p) * v i)) ^ 2)
        ≤ (C * Real.sqrt (n : ℝ)) ^ 2 * (∑ i : Fin n, (v i) ^ 2)) :
    (∑ k : Fin (n - 1), (Submission.NetArgument.qSum B s spv k) ^ 2)
      ≤ ((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ)) ^ 2 := by
  set w : Fin n → ℝ := fun i => (spv i : ℝ) - y i with hw
  have hw1 : ∀ i : Fin n, |w i| ≤ 1 := by
    intro i
    rw [hw, abs_sub_comm]
    exact hd1 i
  have hwsum : |(∑ i : Fin n, w i)| ≤ Real.sqrt ((12 : ℝ) * (n : ℝ) / 11) := by
    have heq : (∑ i : Fin n, w i) = (∑ i : Fin n, (spv i : ℝ)) - ∑ i : Fin n, y i := by
      rw [hw, Finset.sum_sub_distrib]
    rw [heq, abs_sub_comm]
    exact hd2
  have hw2 : (∑ i : Fin n, (w i) ^ 2) ≤ (n : ℝ) := by
    calc (∑ i : Fin n, (w i) ^ 2) ≤ ∑ _i : Fin n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          rw [sq_le_one_iff_abs_le_one]
          exact hw1 i
      _ = (n : ℝ) := by simp
  have hWs : ((∑ i : Fin n, w i)) ^ 2 ≤ (12 : ℝ) * (n : ℝ) / 11 := by
    have h12 : (0 : ℝ) ≤ (12 : ℝ) * (n : ℝ) / 11 := by positivity
    have h := hwsum
    rw [show (12 : ℝ) * (n : ℝ) / 11 = (Real.sqrt ((12 : ℝ) * (n : ℝ) / 11)) ^ 2 by
      rw [Real.sq_sqrt h12]]
    rw [sq_le_sq, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact h
  have hrow : ∀ k : Fin (n - 1), Submission.NetArgument.qSum B s spv k
      = (∑ i : Fin n, (B i (Submission.GeoBridge.emb k) - p) * w i)
        + (s + p) * (∑ i : Fin n, w i) := by
    intro k
    have h1 : Submission.NetArgument.qSum B s spv k
        = ∑ i : Fin n, (B i (Submission.GeoBridge.emb k) + s) * (y i + w i) := by
      rw [Submission.NetArgument.qSum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hw]
      ring
    rw [h1]
    have h2 : (∑ i : Fin n, (B i (Submission.GeoBridge.emb k) + s) * (y i + w i))
        = (∑ i : Fin n, (B i (Submission.GeoBridge.emb k) + s) * y i)
          + (∑ i : Fin n, (B i (Submission.GeoBridge.emb k) - p) * w i)
          + (∑ i : Fin n, (s + p) * w i) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h2, hkern k, Finset.mul_sum]
    ring
  have hA : (∑ k : Fin (n - 1),
        ((∑ i : Fin n, (B i (Submission.GeoBridge.emb k) - p) * w i)) ^ 2)
      ≤ (C * Real.sqrt (n : ℝ)) ^ 2 * (n : ℝ) := by
    calc _ ≤ (C * Real.sqrt (n : ℝ)) ^ 2 * (∑ i : Fin n, (w i) ^ 2) := hspec w
      _ ≤ (C * Real.sqrt (n : ℝ)) ^ 2 * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hw2 (by positivity)
  have hstep : (∑ k : Fin (n - 1), (Submission.NetArgument.qSum B s spv k) ^ 2)
      ≤ 2 * (∑ k : Fin (n - 1),
            ((∑ i : Fin n, (B i (Submission.GeoBridge.emb k) - p) * w i)) ^ 2)
        + 2 * (((n - 1 : ℕ) : ℝ) * ((s + p) * (∑ i : Fin n, w i)) ^ 2) := by
    calc (∑ k : Fin (n - 1), (Submission.NetArgument.qSum B s spv k) ^ 2)
        = ∑ k : Fin (n - 1),
            ((∑ i : Fin n, (B i (Submission.GeoBridge.emb k) - p) * w i)
              + (s + p) * (∑ i : Fin n, w i)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hrow k]
      _ ≤ ∑ k : Fin (n - 1),
            (2 * ((∑ i : Fin n, (B i (Submission.GeoBridge.emb k) - p) * w i)) ^ 2
              + 2 * ((s + p) * (∑ i : Fin n, w i)) ^ 2) :=
          Finset.sum_le_sum (fun k _ => sq_add_le_two _ _)
      _ = 2 * (∑ k : Fin (n - 1),
            ((∑ i : Fin n, (B i (Submission.GeoBridge.emb k) - p) * w i)) ^ 2)
          + 2 * (∑ _k : Fin (n - 1), ((s + p) * (∑ i : Fin n, w i)) ^ 2) :=
          sum_two_sq _ _
      _ = 2 * (∑ k : Fin (n - 1),
            ((∑ i : Fin n, (B i (Submission.GeoBridge.emb k) - p) * w i)) ^ 2)
          + 2 * (((n - 1 : ℕ) : ℝ) * ((s + p) * (∑ i : Fin n, w i)) ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine le_trans hstep ?_
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hnn : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    rw [this]
    linarith
  have hsq : ((s + p) * (∑ i : Fin n, w i)) ^ 2 ≤ (12 : ℝ) * (n : ℝ) / 11 := by
    rw [mul_pow]
    have h1 : (s + p) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]
      exact hsp
    calc (s + p) ^ 2 * (∑ i : Fin n, w i) ^ 2 ≤ 1 * ((12 : ℝ) * (n : ℝ) / 11) :=
          mul_le_mul h1 hWs (sq_nonneg _) (by norm_num)
      _ = (12 : ℝ) * (n : ℝ) / 11 := by ring
  have hb : 2 * (∑ k : Fin (n - 1),
        ((∑ i : Fin n, (B i (Submission.GeoBridge.emb k) - p) * w i)) ^ 2)
      + 2 * (((n - 1 : ℕ) : ℝ) * ((s + p) * (∑ i : Fin n, w i)) ^ 2)
      ≤ 2 * (C ^ 2 * (n : ℝ) ^ 2) + 2 * ((n : ℝ) * ((12 : ℝ) * (n : ℝ) / 11)) := by
    have h1 : (C * Real.sqrt (n : ℝ)) ^ 2 * (n : ℝ) = C ^ 2 * (n : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hn0]
      ring
    rw [h1] at hA
    have h2 : ((n - 1 : ℕ) : ℝ) * ((s + p) * (∑ i : Fin n, w i)) ^ 2
        ≤ (n : ℝ) * ((12 : ℝ) * (n : ℝ) / 11) :=
      mul_le_mul hnn hsq (sq_nonneg _) hn0
    linarith
  have hc : 2 * (C ^ 2 * (n : ℝ) ^ 2) + 2 * ((n : ℝ) * ((12 : ℝ) * (n : ℝ) / 11))
      ≤ ((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ)) ^ 2 := by
    have hs : (0 : ℝ) ≤ 2 * C ^ 2 + 24 / 11 := by positivity
    have hroot : (Real.sqrt (2 * C ^ 2 + 24 / 11)) ^ 2 = 2 * C ^ 2 + 24 / 11 :=
      Real.sq_sqrt hs
    have hr0 : (0 : ℝ) ≤ Real.sqrt (2 * C ^ 2 + 24 / 11) := Real.sqrt_nonneg _
    have hexp : ((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ)) ^ 2
        = (2 * C ^ 2 + 24 / 11) * (n : ℝ) ^ 2
          + 2 * Real.sqrt (2 * C ^ 2 + 24 / 11) * (n : ℝ) ^ 2 + (n : ℝ) ^ 2 := by
      rw [add_mul, one_mul, add_sq, mul_pow, hroot]
      ring
    rw [hexp]
    have hpos : (0 : ℝ) ≤ 2 * Real.sqrt (2 * C ^ 2 + 24 / 11) * (n : ℝ) ^ 2 + (n : ℝ) ^ 2 := by
      positivity
    nlinarith [hpos]
  linarith

/-- **Deterministic chain**: on the annulus event and the spectral event, the
lattice approximation `spv` of the unit normal belongs to the net `NetT` and
its image under the random matrix is small. -/
lemma chain_subset {n : ℕ} (hn2 : 2 ≤ n) {p : unitInterval} (hp1 : (p : ℝ) < 1)
    {δ ν T s L LAC C : ℝ} (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 2) (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (hT0 : 0 < T) (hTν : T ≤ ν / 2) (hL1 : 1 ≤ L) (hLAC : LAC ≤ L * ν / 256)
    (hs : |s| ≤ 1) (hsp : |s + (p : ℝ)| ≤ 1)
    (PiSet : Finset (Equiv.Perm (Fin n)))
    (hPi : ∀ (y : Fin n → ℝ), sqNorm y = 1 → ¬ compressible δ ν y →
      ∀ (th : ℝ), 0 < th → T / 2 ≤ th → th ≤ T → ∀ (w : Fin n → ℤ),
        (∀ i : Fin n, |(Real.sqrt (n : ℝ) / th) * y i - (w i : ℝ)| ≤ 1) →
        ∃ π ∈ PiSet, ∀ i : Fin n, w (π i) ∈ Acoord n δ ν T i)
    {Ω : Type*} [MeasurableSpace Ω] (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    {G : Set Ω} (hG : G ⊆ {ω : Ω | ∀ v : Fin n → ℝ,
        (∑ k : Fin (n - 1),
            ((∑ i : Fin n, (B ω i (Submission.GeoBridge.emb k) - (p : ℝ)) * v i)) ^ 2)
          ≤ (C * Real.sqrt (n : ℝ)) ^ 2 * (∑ i : Fin n, (v i) ^ 2)}) :
    ({ω : Ω | ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω))
          ∧ T / 2 < Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L
          ∧ Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ T}
        ∩ G)
      ⊆ {ω : Ω | ∃ z ∈ NetT p s L T LAC (holeN ν T) (Acoord n δ ν T) PiSet,
              (∑ k : Fin (n - 1), (Submission.NetArgument.qSum (B ω) s z k) ^ 2)
                ≤ ((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ)) ^ 2} := by
  rintro ω ⟨hann, hGω⟩
  obtain ⟨hinc, hth1, hth2⟩ := hann
  have hn1 : 1 ≤ n := by omega
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn1)
  let M : Matrix (Fin n) (Fin n) ℝ := shiftMatrix s (B ω)
  have hx1 : sqNorm (Submission.NormalSplit.yfnOf s (B ω)) = 1 :=
    Submission.GeoBridge.sqNorm_ofLp_of_unit (nVec_unit hn1 M)
  have hth0 : 0 < Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L :=
    Submission.Threshold.threshold_pos p _ hp1 (by linarith)
  obtain ⟨spv, hspv1, hspv2, hspv3, hspv4⟩ :=
    Submission.MagicVector.magic_spv p hn1 (Submission.NormalSplit.yfnOf s (B ω)) hL1 hp1
  obtain ⟨π, hπmem, hDmem⟩ :=
    Submission.NetArgument.cover_mem_Dset hn2 hp1 hδ0 hδ12 hν0 hν1 hT0 hTν hL1 hLAC hx1 hinc
      (le_of_lt hth1) hth2 hspv1 hspv2 hspv3 hspv4 hs (PiSet := PiSet) hPi
  have hnetmem : spv ∈ NetT p s L T LAC (holeN ν T) (Acoord n δ ν T) PiSet :=
    mem_NetT.mpr ⟨π, hπmem, hDmem⟩
  refine ⟨spv, hnetmem, ?_⟩
  have hkern0 : ∀ k : Fin (n - 1),
      (∑ i : Fin n, (B ω i (Submission.GeoBridge.emb k) + s)
        * (Submission.NormalSplit.yfnOf s (B ω) i)) = 0 := by
    intro k
    have h := kernel_emb hn1 M k
    simp only [M, shiftMatrix_apply] at h
    simpa [Submission.NormalSplit.yfnOf] using h
  have hkern : ∀ k : Fin (n - 1),
      (∑ i : Fin n, (B ω i (Submission.GeoBridge.emb k) + s)
        * ((Real.sqrt (n : ℝ)
            / Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L)
          * Submission.NormalSplit.yfnOf s (B ω) i)) = 0 := by
    intro k
    have h1 : (∑ i : Fin n, (B ω i (Submission.GeoBridge.emb k) + s)
        * ((Real.sqrt (n : ℝ)
            / Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L)
          * Submission.NormalSplit.yfnOf s (B ω) i))
        = (Real.sqrt (n : ℝ)
            / Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L)
          * (∑ i : Fin n, (B ω i (Submission.GeoBridge.emb k) + s)
            * Submission.NormalSplit.yfnOf s (B ω) i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h1, hkern0 k, mul_zero]
  refine small_image_bound hn2 (B ω) hsp (y := fun i => (Real.sqrt (n : ℝ)
      / Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L)
        * Submission.NormalSplit.yfnOf s (B ω) i) hkern (spv := spv) hspv1 hspv4 ?_
  intro v
  exact (hG hGω) v

end Submission.NetChain
