import Mathlib
import Submission.SS3core
import Submission.XTransfer
import Submission.DirSet
import Submission.PolyaCore

/-!
# Isolated task: SS3 assembly -- star-decay lifts to fattening-decay

Self-contained statements.  Prove `polyDecay_fat_of_star_decay` (no other
placeholders may remain in this file; add helper lemmas freely).  Uses
`Submission.SS3core.segment_growth` (the uniform single-segment growth
lemma) and `Submission.ChebPower.isCompact_star`.

STATEMENT: let `S : Finset ℂ` with `hSne : S.Nonempty` and every spike
endpoint nonzero, and suppose `PolyDecayOn (star S)` with rate `(C, θ)`
(`θ < 1`).  Then for a suitable `ε > 0`, `PolyDecayOn (FatStar S ε)`.

SETUP AND GEOMETRY (develop the pieces below, then assemble):
* `spikeEndpoints S` is the finite set of segment endpoints: the hedgehog
  `star S = ⋃_{w ∈ spikeEndpoints S} [0, w]` (`Submission.DirSet.
  spikeEndpoints`, `XTransfer.star`); every `w ∈ spikeEndpoints S` is
  nonzero (conjugates of the nonzero α are nonzero).  Let
  `L_min := min over w ∈ spikeEndpoints S of ‖w‖` (positive) and
  `L_max := max` (≥ L_min).  You may take `L_min > 0` and an upper bound
  `L_max` as HYPOTHESES if easier: e.g. `hLmin : ∀ w ∈ spikeEndpoints S,
  0 < ‖w‖` plus `hLmax : ∀ w ∈ spikeEndpoints S, ‖w‖ ≤ L_max` with
  `1 ≤ L_max`, and `hLminb : ∀ w ∈ spikeEndpoints S, L_min ≤ ‖w‖` for a
  positive `L_min` (choose `L_min := min'`).
* KEY GEOMETRIC FACT to prove: for every `X ∈ FatStar S ε` with
  `0 < ε ≤ L_min` there is a spike endpoint `w ∈ spikeEndpoints S` with
  `‖X/w − t‖ ≤ ε/‖w‖` for some `t ∈ [0,1]`-ish, i.e. `X` is within `ε` of
  the segment `[0, w]` and `ε/‖w‖ ≤ ε/L_min` (so the normalized distance
  `δ := ε/‖w‖` satisfies `δ ≤ ε/L_min`).  (If `X` is within `ε` of
  `star S`, it is within `ε` of `[0,w]` for some `w ∈ spikeEndpoints S`
  by definition of `star`; then `δ := ε/‖w‖ ≤ ε/L_min`.)
* Apply `Submission.SS3core.segment_growth` to the normalized polynomial
  `q(Y) := p.eval (w · Y)` (degree `j`, bounded on `[0,1]` by the bound of
  `p` on `[0,w]`, which is `≤ C·θ^j` since `[0,w] ⊆ star S`), with
  `δ := ε/‖w‖ ≤ ε/L_min`, `z := X/w`-normalized: get
  `‖p.eval X‖ ≤ C·θ^j · (1 + 2√(ε/L_min) + 4·(ε/L_min))^j · (2j + 1)` for
  every `X ∈ FatStar S ε` and every `j`.
* PARAMETER CHOICE: since `θ < 1` and `base(η) := 1 + 2√η + 4η` satisfies
  `base(η) → 1` as `η → 0`, choose `0 < ε ≤ L_min` with
  `θ · base(ε/L_min) < 1` (possible: `base(ε/L_min) < 1/θ` for small ε;
  `1/θ > 1`).  Then with `θ'' ∈ (θ·base(ε/L_min), 1)` fixed, the factor
  `(2j+1)` is absorbed: `(2j+1)·(θ·base)^j ≤ C'·θ''^j` for all `j ≥ 1`
  (the sequence `(2j+1)·((θ·base)/θ'')^j` is bounded, since the base ratio
  is `< 1`; bound `(2j+1)·r^j` by `max_{j≥1} (2j+1)r^j ≤ 3/r`-type or
  simply by `(3/r)·(r')^j`-style -- prove a small helper
  `exists_mul_pow_le`: for `0 ≤ r < 1` there is `K` with
  `∀ j ≥ 1, (2j+1)·r^j ≤ K`).
* ASSEMBLE: the same witnesses `p_j` (from `PolyDecayOn (star S)`) give
  the bound on `FatStar S ε` with rate `θ'' < 1` and constant `C·K`,
  i.e. `PolyDecayOn (FatStar S ε)`.

MAIN THEOREM:
theorem polyDecay_fat_of_star_decay {S : Finset ℂ} (hSne : S.Nonempty)
    {C θ : ℝ} (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hdec : ∀ j ≥ 1, ∃ p : ℂ[X], p.Monic ∧ p.natDegree = j ∧
              ∀ X ∈ star S, ‖p.eval X‖ ≤ C * θ ^ j) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ C' θ' : ℝ, 0 ≤ θ' ∧ θ' < 1 ∧
        ∀ j ≥ 1, ∃ p : ℂ[X], p.Monic ∧ p.natDegree = j ∧
          ∀ X ∈ FatStar S ε, ‖p.eval X‖ ≤ C' * θ' ^ j

Notes: you may add hypotheses about the spike endpoints being nonzero /
bounded (`∀ w ∈ spikeEndpoints S, w ≠ 0`; boundedness of `star S` from
`ChebPower.isCompact_star`).  Helper facts to prove and use:
`XTransfer.mem_star`-style membership of `star S` as a union of segments
over `spikeEndpoints S`; normalization `X ∈ [0,w]` iff `X/w ∈ [0,1]`
(for `w ≠ 0`, after choosing a branch -- better: prove that if
`dist(X, [0,w]) ≤ ε` then `∃ t ∈ [0,1]`-type real with
`‖X - (t : ℂ)·w‖ ≤ ε` (real scalar multiple), and set
`z := X/w`-scaled so that `segment_growth` applies with the segment
`[0,1]`); real `≤`/`sqrt` arithmetic for `base`.  Do NOT change the main
theorem's statement except to add hypothesis parameters that are
genuinely needed (state them explicitly).
-/

noncomputable section

open scoped Real Polynomial Topology BigOperators

namespace Submission.SS3asm

open Submission.XTransfer
open Submission.PolyaCore
open Submission.DirSet

/-- Polynomial decay on `K` with explicit rate (monic witnesses). -/
def PolyDecayRate (K : Set ℂ) (C θ : ℝ) : Prop :=
  ∀ j : ℕ, 1 ≤ j →
    ∃ p : ℂ[X], p.Monic ∧ p.natDegree = j ∧
      ∀ X ∈ K, ‖p.eval X‖ ≤ C * θ ^ j

/-- Real smul equals complex multiplication by the coercion. -/
lemma real_smul_eq_ofReal_mul (t : ℝ) (w : ℂ) : t • w = (t : ℂ) * w := by
  rw [Algebra.smul_def]
  norm_num

/-- Squared conjugates are spike endpoints. -/
lemma mem_spikeEndpoints_sq {S : Finset ℂ} {z : ℂ} (hz : z ∈ S) :
    z ^ 2 ∈ spikeEndpoints S := by
  rw [spikeEndpoints]
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)

/-- Fourth powers of conjugates are spike endpoints. -/
lemma mem_spikeEndpoints_pow4 {S : Finset ℂ} {z : ℂ} (hz : z ∈ S) :
    z ^ 4 ∈ spikeEndpoints S := by
  rw [spikeEndpoints]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)

/-- A spike endpoint is a square or a fourth power of an element of `S`. -/
lemma spikeEndpoints_mem_sq_or_pow4 {S : Finset ℂ} {w : ℂ} (hw : w ∈ spikeEndpoints S) :
    (∃ z ∈ S, w = z ^ 2) ∨ (∃ z ∈ S, w = z ^ 4) := by
  rw [spikeEndpoints] at hw
  rcases Finset.mem_union.mp hw with hw | hw
  · rcases Finset.mem_image.mp hw with ⟨z, hz, hwz⟩
    exact Or.inl ⟨z, hz, hwz.symm⟩
  · rcases Finset.mem_image.mp hw with ⟨z, hz, hwz⟩
    exact Or.inr ⟨z, hz, hwz.symm⟩

/-- The star is covered by the spike segments. -/
lemma star_subset_spikeSeg {S : Finset ℂ} {Y : ℂ} (hY : Y ∈ Submission.XTransfer.star S) :
    ∃ w ∈ spikeEndpoints S, Y ∈ segment ℝ (0 : ℂ) w := by
  rcases hY with ⟨z, hz, hseg2 | hseg4⟩
  · exact ⟨z ^ 2, mem_spikeEndpoints_sq hz, hseg2⟩
  · exact ⟨z ^ 4, mem_spikeEndpoints_pow4 hz, hseg4⟩

/-- Every spike segment `[0, w]` is contained in `star S`. -/
lemma spike_segment_subset_star {S : Finset ℂ} {w : ℂ} (hw : w ∈ spikeEndpoints S) :
    segment ℝ (0 : ℂ) w ⊆ Submission.XTransfer.star S := by
  intro Y hY
  rw [spikeEndpoints] at hw
  rcases Finset.mem_union.mp hw with hw | hw
  · rcases Finset.mem_image.mp hw with ⟨z, hz, rfl⟩
    exact ⟨z, hz, Or.inl hY⟩
  · rcases Finset.mem_image.mp hw with ⟨z, hz, rfl⟩
    exact ⟨z, hz, Or.inr hY⟩

/-- A point within `ε` of `star S` lies within `ε` of one spike segment. -/
lemma fatStar_mem_dist_spike {S : Finset ℂ} {ε : ℝ} {X : ℂ} (hX : X ∈ FatStar S ε) :
    ∃ w ∈ spikeEndpoints S, ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ ‖X - t • w‖ ≤ ε := by
  classical
  rcases hX with ⟨Y, hYstar, hXY⟩
  rcases star_subset_spikeSeg hYstar with ⟨w, hw, hYw⟩
  rcases (mem_segment_zero_iff w Y).mp hYw with ⟨t, ht, hYeq⟩
  refine ⟨w, hw, t, ht, ?_⟩
  calc
    ‖X - t • w‖ = ‖X - Y‖ := by rw [← hYeq]
    _ ≤ ε := hXY

/-- Membership of a real scalar multiple in the segment `[0, w]`. -/
lemma smul_mem_segment_zero (w : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t • w ∈ segment ℝ (0 : ℂ) w := by
  exact (mem_segment_zero_iff w (t • w)).mpr ⟨t, ht, rfl⟩


/-- The growth base `1 + 2√η + 4η`. -/
def baseEta (η : ℝ) : ℝ := 1 + 2 * Real.sqrt η + 4 * η

lemma baseEta_nonneg {η : ℝ} (hη : 0 ≤ η) : 0 ≤ baseEta η := by
  dsimp [baseEta]
  nlinarith [Real.sqrt_nonneg η]

lemma baseEta_mono {η₁ η₂ : ℝ} (h : η₁ ≤ η₂) : baseEta η₁ ≤ baseEta η₂ := by
  dsimp [baseEta]
  have hsq : Real.sqrt η₁ ≤ Real.sqrt η₂ := Real.sqrt_le_sqrt h
  nlinarith

/-- Existence of a scale making `θ · base(scale) < 1`. -/
lemma exists_scale {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ θ * baseEta s < 1 := by
  by_cases hz : θ = 0
  · refine ⟨1, by norm_num, le_rfl, ?_⟩
    simp [hz]
  · have hθ : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hz)
    let A : ℝ := (1 - θ) / θ
    have hA : 0 < A := div_pos (sub_pos.mpr hθ1) hθ
    let s : ℝ := min (min 1 (A / 16)) ((A / 4) ^ 2)
    have hA16 : 0 < A / 16 := div_pos hA (by norm_num)
    have hA4 : 0 < A / 4 := div_pos hA (by norm_num)
    have hA4sq : 0 < (A / 4) ^ 2 := sq_pos_of_pos hA4
    have hmin1 : 0 < min 1 (A / 16) := lt_min (by norm_num) hA16
    have hs0 : 0 < s := by
      dsimp [s]
      exact lt_min hmin1 hA4sq
    have hs1 : s ≤ 1 := by
      dsimp [s]
      exact le_trans (min_le_left (min 1 (A / 16)) ((A / 4) ^ 2)) (min_le_left 1 (A / 16))
    have hs16 : s ≤ A / 16 := by
      dsimp [s]
      exact le_trans (min_le_left (min 1 (A / 16)) ((A / 4) ^ 2)) (min_le_right 1 (A / 16))
    have hs4sq : s ≤ (A / 4) ^ 2 := by
      dsimp [s]
      exact min_le_right (min 1 (A / 16)) ((A / 4) ^ 2)
    have hsq : Real.sqrt s ≤ A / 4 := by
      have h1 := Real.sqrt_le_sqrt hs4sq
      have hsqb : Real.sqrt ((A / 4) ^ 2) = A / 4 := by
        rw [Real.sqrt_sq_eq_abs]
        exact abs_of_nonneg hA4.le
      exact le_trans h1 (le_of_eq hsqb)
    have h4s : 4 * s ≤ A / 4 := by nlinarith [hs16]
    have hb : baseEta s ≤ 1 + 3 * A / 4 := by
      dsimp [baseEta]
      nlinarith [hsq, h4s]
    have hle : θ * baseEta s ≤ θ * (1 + 3 * A / 4) := mul_le_mul_of_nonneg_left hb hθ.le
    have hstr : θ * (1 + 3 * A / 4) < θ * (1 + A) := by
      apply mul_lt_mul_of_pos_left _ hθ
      nlinarith [hA]
    have hfin : θ * (1 + A) = 1 := by
      dsimp [A]
      field_simp [hθ.ne']
      ring
    refine ⟨s, hs0, hs1, ?_⟩
    nlinarith [hle, hstr, hfin]

/-- The polynomial factor is absorbed by a slightly worse rate:
`(2j+1)·r^j` is bounded for `0 ≤ r < 1`. -/
lemma exists_mul_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j : ℕ, 1 ≤ j → (2 * j + 1) * r ^ j ≤ K := by
  classical
  let f : ℕ → ℝ := fun j => (2 * (j : ℝ) + 1) * r ^ j
  have hden : 0 < 1 - r := sub_pos.mpr hr1
  rcases exists_nat_ge (1 / (1 - r) : ℝ) with ⟨N, hN⟩
  have hNm : (N : ℝ) * (1 - r) ≥ 1 := by
    have hstep : (1 - r) * (N : ℝ) ≥ (1 - r) * (1 / (1 - r)) :=
      mul_le_mul_of_nonneg_left hN (sub_nonneg.mpr hr1.le)
    have hcancel : (1 - r) * (1 / (1 - r)) = 1 := by field_simp [hden.ne']
    nlinarith
  have hnonneg : 0 ≤ 1 - r := sub_nonneg.mpr hr1.le
  have hratio : ∀ m : ℕ, N ≤ m → (2 * (m : ℝ) + 3) * r ≤ 2 * (m : ℝ) + 1 := by
    intro m hm
    have hmm : (N : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
    have h1m : (1 - r) * (m : ℝ) ≥ (1 - r) * (N : ℝ) :=
      mul_le_mul_of_nonneg_left hmm hnonneg
    have hbig : 2 * (m : ℝ) * (1 - r) ≥ 3 * r - 1 := by
      nlinarith [hNm, h1m]
    nlinarith
  have hmono : ∀ m : ℕ, N ≤ m → f (m + 1) ≤ f m := by
    intro m hm
    have hrpow : 0 ≤ r ^ m := pow_nonneg hr0 m
    calc
      f (m + 1) = (2 * (m : ℝ) + 3) * r * r ^ m := by
        dsimp [f]
        norm_num
        rw [pow_succ]
        ring
      _ ≤ (2 * (m : ℝ) + 1) * r ^ m := by
        exact mul_le_mul_of_nonneg_right (hratio m hm) hrpow
  have htail : ∀ j : ℕ, N ≤ j → f j ≤ f N := by
    intro j hj
    refine Nat.le_induction (P := fun n _ => f n ≤ f N) ?base ?succ j hj
    · rfl
    · intro n hn ih
      exact le_trans (hmono n hn) ih
  have hterm0 : ∀ i : ℕ, 0 ≤ f i := by
    intro i
    dsimp [f]
    exact mul_nonneg (by positivity) (pow_nonneg hr0 i)
  let K : ℝ := (∑ i ∈ Finset.range N, f i) + f N
  refine ⟨K, ?_, ?_⟩
  · dsimp [K]
    exact add_nonneg (Finset.sum_nonneg (fun i hi => hterm0 i)) (hterm0 N)
  · intro j hj
    by_cases hjl : j < N
    · have hmem : j ∈ Finset.range N := by simpa using hjl
      have hsingle : f j ≤ ∑ i ∈ Finset.range N, f i :=
        Finset.single_le_sum (fun i hi => hterm0 i) hmem
      dsimp [K]
      nlinarith [hsingle, hterm0 N]
    · have hge : N ≤ j := le_of_not_gt hjl
      have ht := htail j hge
      dsimp [K]
      have hsum0 : 0 ≤ ∑ i ∈ Finset.range N, f i := Finset.sum_nonneg (fun i hi => hterm0 i)
      nlinarith [ht, hsum0]

/-- After scaling by `w`, a point `X` within `ε` of `t•w` is within
`ε/‖w‖` of the real point `t`. -/
lemma norm_div_sub_ofReal_le {X w : ℂ} (hw : w ≠ 0) {ε : ℝ} {t : ℝ}
    (h : ‖X - t • w‖ ≤ ε) : ‖X / w - (t : ℂ)‖ ≤ ε / ‖w‖ := by
  have hnorm : ‖X / w - (t : ℂ)‖ = ‖X - t • w‖ / ‖w‖ := by
    have h : X / w - (t : ℂ) = (X - t • w) / w := by
      rw [Algebra.smul_def]
      norm_num
      field_simp [hw]
    rw [h, norm_div]
  rw [hnorm]
  exact div_le_div_of_nonneg_right h (norm_nonneg w)

/-- Evaluating the rescaled polynomial at `X/w` recovers `p.eval X`. -/
lemma comp_rescale_eval_div {p : ℂ[X]} {w : ℂ} (hw : w ≠ 0) (X : ℂ) :
    (p.comp (Polynomial.C w * Polynomial.X)).eval (X / w) = p.eval X := by
  rw [Polynomial.eval_comp]
  simp
  field_simp [hw]

/-- On the real segment, the rescaled polynomial takes the values of `p`
on the complex segment `[0, w]`. -/
lemma comp_rescale_eval_ofReal {p : ℂ[X]} (w : ℂ) (t : ℝ) :
    (p.comp (Polynomial.C w * Polynomial.X)).eval (t : ℂ) = p.eval (t • w) := by
  rw [Polynomial.eval_comp]
  simp
  congr 1
  ring_nf

/-- Degree bound for the rescaled polynomial. -/
lemma comp_rescale_natDegree_le {p : ℂ[X]} (w : ℂ) {j : ℕ} (hpdeg : p.natDegree ≤ j) :
    (p.comp (Polynomial.C w * Polynomial.X)).natDegree ≤ j := by
  calc
    (p.comp (Polynomial.C w * Polynomial.X)).natDegree ≤ p.natDegree * (Polynomial.C w * Polynomial.X).natDegree := Polynomial.natDegree_comp_le
    _ ≤ j * 1 := by
      apply Nat.mul_le_mul hpdeg
      by_cases hw : w = 0
      · simp [hw]
      · rw [Polynomial.natDegree_C_mul hw, Polynomial.natDegree_X]
    _ ≤ j := by simp

theorem polyDecay_fat_of_star_decay {S : Finset ℂ} (hSne : S.Nonempty)
    (hw0 : ∀ w ∈ spikeEndpoints S, w ≠ 0)
    {C θ : ℝ} (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hdec : PolyDecayRate (Submission.XTransfer.star S) C θ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ C' θ' : ℝ, 0 ≤ θ' ∧ θ' < 1 ∧ PolyDecayRate (FatStar S ε) C' θ' := by
  classical
  let sp : Finset ℂ := spikeEndpoints S
  have hsp_ne : sp.Nonempty := by
    rcases hSne with ⟨z, hz⟩
    exact ⟨z ^ 2, mem_spikeEndpoints_sq hz⟩
  let ns : Finset ℝ := sp.image (fun w : ℂ => ‖w‖)
  have hns_ne : ns.Nonempty := by
    rcases hsp_ne with ⟨w, hw⟩
    refine ⟨‖w‖, ?_⟩
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
  let m : ℝ := ns.min' hns_ne
  have hm_mem : m ∈ ns := Finset.min'_mem ns hns_ne
  have hm_ge0 : 0 ≤ m := by
    rcases (Finset.mem_image.mp hm_mem) with ⟨w, hw, hwm⟩
    rw [← hwm]
    exact norm_nonneg w
  have hm_pos : 0 < m := by
    rcases (Finset.mem_image.mp hm_mem) with ⟨w, hw, hwm⟩
    rw [← hwm]
    exact norm_pos_iff.mpr (hw0 w hw)
  have hm_le : ∀ w ∈ sp, m ≤ ‖w‖ := by
    intro w hw
    exact Finset.min'_le ns ‖w‖ (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
  rcases exists_scale (hθ0 := hθ0) (hθ1 := hθ1) with ⟨s, hs0, hs1, hsθ⟩
  let ε : ℝ := s * m
  have hε0 : 0 < ε := by
    dsimp [ε]
    exact mul_pos hs0 hm_pos
  have hε_le_w : ∀ w ∈ sp, ε ≤ ‖w‖ := by
    intro w hw
    dsimp [ε]
    calc
      s * m ≤ 1 * m := mul_le_mul_of_nonneg_right hs1 hm_ge0
      _ = m := by ring
      _ ≤ ‖w‖ := hm_le w hw
  let θb : ℝ := θ * baseEta s
  have hθb0 : 0 ≤ θb := by
    dsimp [θb]
    exact mul_nonneg hθ0 (baseEta_nonneg hs0.le)
  have hθb1 : θb < 1 := by
    dsimp [θb]
    exact hsθ
  let θ' : ℝ := (1 + θb) / 2
  have hθ'0 : 0 ≤ θ' := by
    dsimp [θ']
    nlinarith
  have hθ'1 : θ' < 1 := by
    dsimp [θ']
    nlinarith [hθb1]
  have hθ'_pos : 0 < θ' := by
    dsimp [θ']
    nlinarith [hθb0]
  have hθb_lt_θ' : θb < θ' := by
    dsimp [θ']
    nlinarith [hθb1]
  let r : ℝ := θb / θ'
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg hθb0 hθ'0
  have hr1 : r < 1 := by
    dsimp [r]
    exact (div_lt_one₀ hθ'_pos).mpr hθb_lt_θ'
  rcases exists_mul_pow_le hr0 hr1 with ⟨K, hK0, hKbd⟩
  let C' : ℝ := C * K
  have hC'0 : 0 ≤ C' := by
    dsimp [C']
    exact mul_nonneg hC hK0
  refine ⟨ε, hε0, C', θ', hθ'0, hθ'1, ?_⟩
  -- main claim: PolyDecayRate (FatStar S ε) C' θ'
  intro j hj
  rcases hdec j hj with ⟨p, hpmonic, hpdeg, hpbound⟩
  refine ⟨p, hpmonic, hpdeg, ?_⟩
  intro X hX
  rcases fatStar_mem_dist_spike hX with ⟨w, hwsp, t, ht01, hXdist⟩
  have hwne : w ≠ 0 := hw0 w hwsp
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  -- δ := ε / ‖w‖
  let δ : ℝ := ε / ‖w‖
  have hδ0 : 0 < δ := by
    dsimp [δ]
    exact div_pos hε0 hwpos
  have hδ_le_s : δ ≤ s := by
    dsimp [δ]
    have hmw : m ≤ ‖w‖ := hm_le w hwsp
    have hε_le : ε ≤ s * ‖w‖ := by
      dsimp [ε]
      exact mul_le_mul_of_nonneg_left hmw hs0.le
    exact (div_le_iff₀ hwpos).2 hε_le
  have hδ1 : δ ≤ 1 := le_trans hδ_le_s hs1
  have hbδs : baseEta δ ≤ baseEta s := baseEta_mono hδ_le_s
  -- the normalized witness t for the point X/w
  have hzδ : ‖X / w - (t : ℂ)‖ ≤ ε / ‖w‖ := norm_div_sub_ofReal_le (hw := hwne) hXdist
  set q : ℂ[X] := p.comp (Polynomial.C w * Polynomial.X) with hqdef
  have hdegq : q.natDegree ≤ j := by
    rw [hqdef]
    exact comp_rescale_natDegree_le w (le_of_eq hpdeg)
  let M : ℝ := C * θ ^ j
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg hC (pow_nonneg hθ0 j)
  -- q is bounded by M on [0,1]
  have hq : ∀ t0 : ℝ, t0 ∈ Set.Icc (0 : ℝ) 1 → ‖q.eval (t0 : ℂ)‖ ≤ M := by
    intro t0 ht0
    rw [hqdef]
    have hseg : t0 • w ∈ segment ℝ (0 : ℂ) w := smul_mem_segment_zero w ht0
    have hstar : t0 • w ∈ Submission.XTransfer.star S := spike_segment_subset_star hwsp hseg
    calc
      ‖(p.comp (Polynomial.C w * Polynomial.X)).eval (t0 : ℂ)‖ = ‖p.eval (t0 • w)‖ := by
        rw [comp_rescale_eval_ofReal]
      _ ≤ C * θ ^ j := hpbound (t0 • w) hstar
      _ = M := by rfl
  have hsg := Submission.SS3core.segment_growth (n := j) (q := q) hj hdegq (M := M) hM hq
      (δ := δ) hδ0 hδ1 (z := X / w) ⟨t, ht01, hzδ⟩
  -- ‖p.eval X‖ ≤ C * θ^j * baseEta δ^j * (2j + 1)
  have hqe : q.eval (X / w) = p.eval X := by
    rw [hqdef]
    exact comp_rescale_eval_div (p := p) (w := w) hwne X
  have hmain : ‖p.eval X‖ ≤ C * θ ^ j * baseEta δ ^ j * (2 * (j : ℝ) + 1) := by
    calc
      ‖p.eval X‖ = ‖q.eval (X / w)‖ := by rw [hqe]
      _ ≤ M * (1 + 2 * Real.sqrt δ + 4 * δ) ^ j * (2 * (j : ℝ) + 1) := hsg
      _ = C * θ ^ j * baseEta δ ^ j * (2 * (j : ℝ) + 1) := by rfl
  -- bound baseEta δ^j by baseEta s^j
  have hbpow : baseEta δ ^ j ≤ baseEta s ^ j := pow_le_pow_left₀ (baseEta_nonneg hδ0.le) hbδs j
  have hc1 : 0 ≤ C * θ ^ j * (2 * (j : ℝ) + 1) := by
    positivity
  have hle2 : ‖p.eval X‖ ≤ C * θ ^ j * baseEta s ^ j * (2 * (j : ℝ) + 1) := by
    calc
      ‖p.eval X‖ ≤ (C * θ ^ j * (2 * (j : ℝ) + 1)) * baseEta δ ^ j := by
        calc
          ‖p.eval X‖ ≤ C * θ ^ j * baseEta δ ^ j * (2 * (j : ℝ) + 1) := hmain
          _ = (C * θ ^ j * (2 * (j : ℝ) + 1)) * baseEta δ ^ j := by ring
      _ ≤ (C * θ ^ j * (2 * (j : ℝ) + 1)) * baseEta s ^ j := mul_le_mul_of_nonneg_left hbpow hc1
      _ = C * θ ^ j * baseEta s ^ j * (2 * (j : ℝ) + 1) := by ring
  -- reassemble θ·baseEta s = θb, powers
  have hθpow : θ ^ j * baseEta s ^ j = θb ^ j := by
    rw [← mul_pow]
  have hb : C * θ ^ j * baseEta s ^ j = C * θb ^ j := by
    calc
      C * θ ^ j * baseEta s ^ j = C * (θ ^ j * baseEta s ^ j) := by ring
      _ = C * θb ^ j := by rw [hθpow]
  have hle3 : ‖p.eval X‖ ≤ C * θb ^ j * (2 * (j : ℝ) + 1) := by
    calc
      ‖p.eval X‖ ≤ C * θ ^ j * baseEta s ^ j * (2 * (j : ℝ) + 1) := hle2
      _ = (C * θ ^ j * baseEta s ^ j) * (2 * (j : ℝ) + 1) := by ring
      _ = (C * θb ^ j) * (2 * (j : ℝ) + 1) := by rw [hb]
      _ = C * θb ^ j * (2 * (j : ℝ) + 1) := by ring
  -- θb^j (2j+1) = θ'^j ((2j+1) r^j), r := θb/θ'
  have hθ'r : θ' * r = θb := by
    dsimp [r]
    field_simp [hθ'_pos.ne']
  have hpowr : θb ^ j = θ' ^ j * r ^ j := by
    calc
      θb ^ j = (θ' * r) ^ j := by rw [hθ'r]
      _ = θ' ^ j * r ^ j := by rw [mul_pow]
  have hb2 : C * θb ^ j * (2 * (j : ℝ) + 1) = C * θ' ^ j * ((2 * (j : ℝ) + 1) * r ^ j) := by
    calc
      C * θb ^ j * (2 * (j : ℝ) + 1) = C * (θb ^ j * (2 * (j : ℝ) + 1)) := by ring
      _ = C * (θ' ^ j * r ^ j * (2 * (j : ℝ) + 1)) := by rw [hpowr]
      _ = C * θ' ^ j * ((2 * (j : ℝ) + 1) * r ^ j) := by ring
  -- (2j+1) r^j ≤ K
  have hKj : (2 * (j : ℝ) + 1) * r ^ j ≤ K := by
    have hbnd := hKbd j hj
    simpa using hbnd
  have hθ'pow : 0 ≤ θ' ^ j := pow_nonneg hθ'0 j
  have hle4 : C * θb ^ j * (2 * (j : ℝ) + 1) ≤ C * θ' ^ j * K := by
    calc
      C * θb ^ j * (2 * (j : ℝ) + 1) = C * θ' ^ j * ((2 * (j : ℝ) + 1) * r ^ j) := hb2
      _ ≤ C * θ' ^ j * K := by
        exact mul_le_mul_of_nonneg_left hKj (mul_nonneg hC hθ'pow)
  -- final: C * θ'^j * K = C' * θ'^j
  have hfinal : ‖p.eval X‖ ≤ C' * θ' ^ j := by
    calc
      ‖p.eval X‖ ≤ C * θb ^ j * (2 * (j : ℝ) + 1) := hle3
      _ ≤ C * θ' ^ j * K := hle4
      _ = (C * K) * θ' ^ j := by ring
      _ = C' * θ' ^ j := by rfl
  exact hfinal

end Submission.SS3asm

end
