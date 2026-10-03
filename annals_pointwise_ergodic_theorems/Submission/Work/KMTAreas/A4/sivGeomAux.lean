/-
# Elementary geometry of the blocks for Corollary `siv`
-/
import Mathlib
import Submission.Work.KMTAreas.A4.sivDefs

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory (AhalfTranspose)

/-- `|P(n)| ≤ winBd P N` for `0 ≤ n ≤ N`. -/
theorem abs_eval_le_winBd {P : Polynomial ℤ} {N : ℕ} {n : ℤ}
    (hn1 : 0 ≤ n) (hn2 : n ≤ (N : ℤ)) (hN : 1 ≤ N) :
    |P.eval n| ≤ (winBd P N : ℤ) := by
  have h1 : ((coefBd P - 1 : ℕ) : ℤ) ≤ (coefBd P : ℤ) := by
    have := Nat.sub_le (coefBd P) 1
    exact_mod_cast this
  have h2 : (0 : ℤ) ≤ (N : ℤ) ^ P.natDegree := by positivity
  calc |P.eval n| ≤ ((coefBd P - 1 : ℕ) : ℤ) * (N : ℤ) ^ P.natDegree :=
        abs_eval_le_coefBd hn1 hn2 hN
    _ ≤ (coefBd P : ℤ) * (N : ℤ) ^ P.natDegree := mul_le_mul_of_nonneg_right h1 h2
    _ = (winBd P N : ℤ) := by rw [winBd]; push_cast; ring

/-- `|P(n) - n| ≤ winBd P N` for `0 ≤ n ≤ N`. -/
theorem abs_eval_sub_le_winBd {P : Polynomial ℤ} (hP : 1 ≤ P.natDegree) {N : ℕ} {n : ℤ}
    (hn1 : 0 ≤ n) (hn2 : n ≤ (N : ℤ)) (hN : 1 ≤ N) :
    |P.eval n - n| ≤ (winBd P N : ℤ) := by
  have hcb : ((coefBd P - 1 : ℕ) : ℤ) + 1 = (coefBd P : ℤ) := by
    have h := coefBd_pos P
    omega
  have h1 : ((coefBd P - 1 : ℕ) : ℤ) * (N : ℤ) ^ P.natDegree + (N : ℤ) ^ P.natDegree
      = (winBd P N : ℤ) := by
    rw [winBd]; push_cast; rw [← hcb]; ring
  have hNle : (N : ℤ) ≤ (N : ℤ) ^ P.natDegree := by
    have h2 : N ≤ N ^ P.natDegree := by
      calc N = N ^ 1 := (pow_one N).symm
        _ ≤ N ^ P.natDegree := Nat.pow_le_pow_right hN hP
    exact_mod_cast h2
  have hnl : |n| ≤ (N : ℤ) := by rw [abs_of_nonneg hn1]; exact hn2
  calc |P.eval n - n| ≤ |P.eval n| + |n| := abs_sub _ _
    _ ≤ ((coefBd P - 1 : ℕ) : ℤ) * (N : ℤ) ^ P.natDegree + (N : ℤ) ^ P.natDegree :=
        add_le_add (abs_eval_le_coefBd hn1 hn2 hN) (le_trans hnl hNle)
    _ = (winBd P N : ℤ) := h1

theorem blkLen_pos_int (P : Polynomial ℤ) {N : ℕ} (hN : 1 ≤ N) : 0 < (blkLen P N : ℤ) := by
  have h1 : 0 < blkLen P N := by
    rw [blkLen]
    have h2 : 0 < N ^ P.natDegree := pow_pos (by omega) _
    have h3 : 0 < 2 * coefBd P + 2 := by omega
    exact Nat.mul_pos h3 h2
  exact_mod_cast h1

/-- The block pieces sum to `g` over a set of blocks. -/
theorem sum_blkPiece_eq (P : Polynomial ℤ) (N : ℕ) (hN : 1 ≤ N) (g : ℤ → ℂ)
    (S : Finset ℤ) (x : ℤ) :
    ∑ i ∈ S, blkPiece P N g i x = if x / (blkLen P N : ℤ) ∈ S then g x else 0 := by
  have hL := blkLen_pos_int P hN
  by_cases hmem : x / (blkLen P N : ℤ) ∈ S
  · rw [if_pos hmem, Finset.sum_eq_single (x / (blkLen P N : ℤ))]
    · rw [blkPiece, if_pos (mem_Ico_of_ediv_eq hL rfl)]
    · intro i _ hi
      rw [blkPiece, if_neg]
      intro hc
      exact hi (ediv_eq_of_mem_Ico hL hc.1 hc.2)
    · intro hnot; exact absurd hmem hnot
  · rw [if_neg hmem]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [blkPiece, if_neg]
    intro hc
    exact hmem (by rw [← ediv_eq_of_mem_Ico hL hc.1 hc.2]; exact hi)

/-- The block index of `x` is in `[-K,K]` exactly when `x` lies in the block interval. -/
theorem ediv_mem_Icc_iff {L : ℤ} (hL : 0 < L) (K : ℤ) (x : ℤ) :
    x / L ∈ Finset.Icc (-K) K ↔ x ∈ Finset.Ico (-(K * L)) ((K + 1) * L) := by
  rw [Finset.mem_Icc, Finset.mem_Ico]
  constructor
  · intro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [Int.le_ediv_iff_mul_le hL] at h1
      linarith
    · have hxsplit : L * (x / L) + x % L = x := Int.mul_ediv_add_emod x L
      have hem : x % L < L := Int.emod_lt_of_pos x hL
      have hsp : (x / L + 1) * L = L * (x / L) + L := by ring
      have h4 : x < (x / L + 1) * L := by rw [hsp]; omega
      have h3 : x / L + 1 ≤ K + 1 := by omega
      calc x < (x / L + 1) * L := h4
        _ ≤ (K + 1) * L := Int.mul_le_mul_of_nonneg_right h3 hL.le
  · intro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [Int.le_ediv_iff_mul_le hL]
      linarith
    · have h3 : x / L < K + 1 := by
        refine Int.ediv_lt_of_lt_mul hL ?_
        have hsp : ((K : ℤ) + 1) * L = K * L + L := by ring
        rw [hsp]
        linarith
      omega

/-- The block sum over `[-K,K]` is the truncation to the block interval. -/
theorem blkSum_eq (P : Polynomial ℤ) (N : ℕ) (hN : 1 ≤ N) (K : ℕ) (g : ℤ → ℂ) (x : ℤ) :
    ∑ i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), blkPiece P N g i x
      = if x ∈ Finset.Ico (-((K : ℤ) * (blkLen P N : ℤ)))
            (((K : ℤ) + 1) * (blkLen P N : ℤ)) then g x else 0 := by
  rw [sum_blkPiece_eq P N hN g _ x]
  by_cases h : x / (blkLen P N : ℤ) ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)
  · rw [if_pos h, if_pos ((ediv_mem_Icc_iff (blkLen_pos_int P hN) (K : ℤ) x).mp h)]
  · rw [if_neg h, if_neg (fun hc => h ((ediv_mem_Icc_iff (blkLen_pos_int P hN) (K : ℤ) x).mpr hc))]

/-- **The finite partition identity.** -/
theorem sum_blkDual_finset (P : Polynomial ℤ) (hP : 1 ≤ P.natDegree) (N : ℕ) (hN : 1 ≤ N)
    (S : Finset ℤ) (h g : ℤ → ℂ) (y : ℤ) :
    (∑ i ∈ S, blkDual P N h g i y)
      = AhalfTranspose N P h (fun z => ∑ i ∈ S, blkPiece P N g i z) y := by
  have hwin : ∀ (n : ℕ), 0 ≤ (n : ℤ) → (n : ℤ) ≤ (N : ℤ) → ∀ (i : ℤ),
      blkPiece P N g i (y + P.eval (n : ℤ) - (n : ℤ)) ≠ 0 →
      winPiece P N h i (y - (n : ℤ)) = h (y - (n : ℤ)) := by
    intro n hn1 hn2 i hi
    have hb : |P.eval (n : ℤ)| ≤ (winBd P N : ℤ) := abs_eval_le_winBd hn1 hn2 hN
    rw [blkPiece] at hi
    by_cases hc : i * (blkLen P N : ℤ) ≤ y + P.eval (n : ℤ) - (n : ℤ) ∧
        y + P.eval (n : ℤ) - (n : ℤ) < (i + 1) * (blkLen P N : ℤ)
    · rw [winPiece, if_pos]
      obtain ⟨hb1, hb2⟩ := abs_le.mp hb
      constructor <;> simp only [blkAlpha, blkBeta] <;> linarith [hc.1, hc.2]
    · exact absurd (if_neg hc) hi
  calc (∑ i ∈ S, blkDual P N h g i y)
      = ∑ i ∈ S, (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, winPiece P N h i (y - (n : ℤ))
          * blkPiece P N g i (y + P.eval (n : ℤ) - (n : ℤ)) :=
        Finset.sum_congr rfl fun i _ => by rw [blkDual, AhalfTranspose]
    _ = (N : ℝ)⁻¹ * ∑ i ∈ S, ∑ n ∈ Finset.Ioc (N / 2) N, winPiece P N h i (y - (n : ℤ))
          * blkPiece P N g i (y + P.eval (n : ℤ) - (n : ℤ)) := by
        rw [Finset.mul_sum]
    _ = (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, ∑ i ∈ S, winPiece P N h i (y - (n : ℤ))
          * blkPiece P N g i (y + P.eval (n : ℤ) - (n : ℤ)) := by
        rw [Finset.sum_comm]
    _ = (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, h (y - (n : ℤ))
          * (∑ i ∈ S, blkPiece P N g i (y + P.eval (n : ℤ) - (n : ℤ))) := by
        congr 1
        refine Finset.sum_congr rfl fun n hn => ?_
        refine (Finset.sum_congr rfl fun i _ => ?_).trans (Finset.mul_sum ..).symm
        by_cases h0 : blkPiece P N g i (y + P.eval (n : ℤ) - (n : ℤ)) = 0
        · rw [h0, mul_zero, mul_zero]
        · rw [hwin n (by positivity) (by exact_mod_cast (Finset.mem_Ioc.mp hn).2) i h0]
    _ = AhalfTranspose N P h (fun z => ∑ i ∈ S, blkPiece P N g i z) y := by
        rw [AhalfTranspose, Finset.mul_sum]

theorem AhalfTranspose_comp_add (N : ℕ) (P : Polynomial ℤ) (t : ℤ) (h g : ℤ → ℂ) :
    AhalfTranspose N P (fun x => h (x + t)) (fun x => g (x + t))
      = fun x => AhalfTranspose N P h g (x + t) := by
  funext y
  rw [AhalfTranspose, AhalfTranspose]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  ring_nf

theorem l2sq_blkPiece (P : Polynomial ℤ) (N : ℕ) (g : ℤ → ℂ) (i : ℤ) :
    l2sq (blkPiece P N g i)
      = ∑ x ∈ Finset.Ico (i * (blkLen P N : ℤ)) ((i + 1) * (blkLen P N : ℤ)), ‖g x‖ ^ 2 := by
  have hvan : ∀ x ∉ Finset.Ico (i * (blkLen P N : ℤ)) ((i + 1) * (blkLen P N : ℤ)),
      ‖blkPiece P N g i x‖ ^ 2 = 0 := by
    intro x hx
    rw [blkPiece, if_neg]
    · simp
    · intro hc; exact hx (Finset.mem_Ico.mpr hc)
  rw [l2sq, tsum_eq_sum hvan]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [blkPiece, if_pos (Finset.mem_Ico.mp hx)]

theorem summable_norm_sq_blkPiece (P : Polynomial ℤ) (N : ℕ) (g : ℤ → ℂ) (i : ℤ) :
    Summable (fun x : ℤ => ‖blkPiece P N g i x‖ ^ 2) := by
  refine summable_of_ne_finset_zero
    (s := Finset.Ico (i * (blkLen P N : ℤ)) ((i + 1) * (blkLen P N : ℤ))) fun x hx => ?_
  rw [blkPiece, if_neg]
  · simp
  · intro hc; exact hx (Finset.mem_Ico.mpr hc)

/-- The block sums of a finite set of blocks are at most the `ℓ²` mass of `g`. -/
theorem sum_l2sq_blkPiece_le (P : Polynomial ℤ) (N : ℕ) (hN : 1 ≤ N) {g : ℤ → ℂ}
    (hg : Summable (fun x : ℤ => ‖g x‖ ^ 2)) (S : Finset ℤ) :
    ∑ i ∈ S, l2sq (blkPiece P N g i) ≤ ∑' x : ℤ, ‖g x‖ ^ 2 := by
  have hL := blkLen_pos_int P hN
  have hterm : ∀ i : ℤ, l2sq (blkPiece P N g i)
      = ∑' x : ℤ, (if x / (blkLen P N : ℤ) = i then ‖g x‖ ^ 2 else 0) := by
    intro i
    rw [l2sq]
    refine tsum_congr fun x => ?_
    by_cases h : x / (blkLen P N : ℤ) = i
    · rw [if_pos h, blkPiece, if_pos (mem_Ico_of_ediv_eq hL h.symm)]
    · rw [if_neg h, blkPiece, if_neg]
      · simp
      · intro hc
        exact h (ediv_eq_of_mem_Ico hL hc.1 hc.2).symm
  have hsm : ∀ i : ℤ, Summable (fun x : ℤ =>
      (if x / (blkLen P N : ℤ) = i then ‖g x‖ ^ 2 else 0)) := by
    intro i
    refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_) hg
    split
    · exact le_rfl
    · exact sq_nonneg _
  calc ∑ i ∈ S, l2sq (blkPiece P N g i)
      = ∑ i ∈ S, ∑' x : ℤ, (if x / (blkLen P N : ℤ) = i then ‖g x‖ ^ 2 else 0) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = ∑' x : ℤ, ∑ i ∈ S, (if x / (blkLen P N : ℤ) = i then ‖g x‖ ^ 2 else 0) :=
        (Summable.tsum_finsetSum (fun i _ => hsm i)).symm
    _ ≤ ∑' x : ℤ, ‖g x‖ ^ 2 := by
        refine Summable.tsum_le_tsum (fun x => ?_) (summable_sum fun i _ => hsm i) hg
        by_cases hx : x / (blkLen P N : ℤ) ∈ S
        · rw [Finset.sum_eq_single (x / (blkLen P N : ℤ))]
          · rw [if_pos rfl]
          · intro i _ hi; rw [if_neg (fun h => hi h.symm)]
          · intro hnot; exact absurd hx hnot
        · have hzero : ∀ i ∈ S,
              (if x / (blkLen P N : ℤ) = i then ‖g x‖ ^ 2 else 0) = 0 := by
            intro i hi
            rw [if_neg]
            intro hcon
            exact hx (hcon ▸ hi)
          rw [Finset.sum_eq_zero hzero]
          exact sq_nonneg _

/-- The tail of a summable sequence off a cofinal family of finite sets. -/
theorem tendsto_tail_finset (f : ℤ → ℝ) (hf : Summable f) (I : ℕ → Finset ℤ)
    (hI : Filter.Tendsto I Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun K : ℕ => ∑' x : ℤ, (if x ∈ I K then 0 else f x))
      Filter.atTop (nhds 0) := by
  have hcomp := hf.hasSum.comp hI
  have hpt : ∀ K : ℕ, (∑' x : ℤ, (if x ∈ I K then 0 else f x))
      = (∑' x, f x) - ∑ x ∈ I K, f x := by
    intro K
    have h := Summable.sum_add_tsum_compl (s := I K) hf
    rw [_root_.tsum_subtype] at h
    have h' : ∑' (x : ℤ), ((I K : Set ℤ))ᶜ.indicator f x
        = ∑' x : ℤ, (if x ∈ I K then 0 else f x) := by
      refine tsum_congr fun x => ?_
      by_cases hx : x ∈ I K
      · rw [if_pos hx, Set.indicator_of_notMem (by simpa using hx)]
      · rw [if_neg hx, Set.indicator_of_mem (by simpa using hx)]
    rw [h'] at h
    linarith
  have h2 : Filter.Tendsto (fun K : ℕ => (∑' x, f x) - ∑ x ∈ I K, f x)
      Filter.atTop (nhds ((∑' x, f x) - ∑' x, f x)) := tendsto_const_nhds.sub hcomp
  have h3 := h2.congr' (Filter.Eventually.of_forall fun K => (hpt K).symm)
  simpa using h3

theorem tendsto_Icc_atTop :
    Filter.Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  rw [Filter.eventually_atTop]
  refine ⟨b.sup (fun x : ℤ => x.natAbs) + 1, fun N hN => ?_⟩
  intro x hx
  rw [Finset.mem_Icc]
  have h1 : x.natAbs ≤ b.sup (fun x : ℤ => x.natAbs) :=
    Finset.le_sup (f := fun x : ℤ => x.natAbs) hx
  have h2 : x.natAbs ≤ N := by omega
  have h3 : (x.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast h2
  have h4 : x ≤ x.natAbs := Int.le_natAbs
  have h5 : -x ≤ x.natAbs := by
    have := Int.le_natAbs (a := -x)
    simpa using this
  omega

/-- The `ℓ²` mass of a summable sequence vanishes off the block interval `[-KL, (K+1)L)`. -/
theorem tendsto_tail_Ico (f : ℤ → ℝ) (hf : Summable f) (hnn : ∀ x : ℤ, 0 ≤ f x)
    {L : ℤ} (hL : 1 ≤ L) :
    Filter.Tendsto (fun K : ℕ => ∑' x : ℤ,
        (if x ∈ Finset.Ico (-((K : ℤ) * L)) (((K : ℤ) + 1) * L) then 0 else f x))
      Filter.atTop (nhds 0) := by
  have hpt : ∀ (s : Finset ℤ), (∑' x : ℤ, (if x ∈ s then 0 else f x))
      = (∑' x, f x) - ∑ x ∈ s, f x := by
    intro s
    have h := Summable.sum_add_tsum_compl (s := s) hf
    rw [_root_.tsum_subtype] at h
    have h' : ∑' (x : ℤ), ((s : Set ℤ))ᶜ.indicator f x
        = ∑' x : ℤ, (if x ∈ s then 0 else f x) := by
      refine tsum_congr fun x => ?_
      by_cases hx : x ∈ s
      · rw [if_pos hx, Set.indicator_of_notMem (by simpa using hx)]
      · rw [if_neg hx, Set.indicator_of_mem (by simpa using hx)]
    rw [h'] at h
    linarith
  have h2 : Filter.Tendsto (fun K : ℕ => ∑' x : ℤ,
      (if x ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) then 0 else f x)) Filter.atTop (nhds 0) :=
    tendsto_tail_finset f hf (fun K => Finset.Icc (-(K : ℤ)) (K : ℤ)) tendsto_Icc_atTop
  have hsub : ∀ K : ℕ, Finset.Icc (-(K : ℤ)) (K : ℤ)
      ⊆ Finset.Ico (-((K : ℤ) * L)) (((K : ℤ) + 1) * L) := by
    intro K x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_Ico]
    obtain ⟨h1, h2⟩ := hx
    have hK0 : (0 : ℤ) ≤ (K : ℤ) := by positivity
    constructor <;> nlinarith
  refine squeeze_zero (fun K => ?_) (fun K => ?_) h2
  · rw [hpt]
    exact sub_nonneg.mpr (hf.sum_le_tsum _ fun x _ => hnn x)
  · rw [hpt, hpt]
    have hle : ∑ x ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), f x
        ≤ ∑ x ∈ Finset.Ico (-((K : ℤ) * L)) (((K : ℤ) + 1) * L), f x :=
      Finset.sum_le_sum_of_subset_of_nonneg (hsub K) (fun x _ _ => hnn x)
    linarith

end Work.KMTAreas.A4
