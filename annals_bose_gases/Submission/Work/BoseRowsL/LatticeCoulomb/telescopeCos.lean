import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowsL.LatticeCoulomb.telAxisLe
import Submission.Work.BoseRowsL.LatticeCoulomb.telFiberBound
import Submission.Work.BoseRowsL.LatticeCoulomb.telQSum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.telescopeCos`

The telescoping cosine bound for the lattice Coulomb kernel: for the set of nonzero lattice
points of norm at most `R`,

`(1 - cos (2π z_j)) · |Σ_n cos (2π⟪nvec n, z⟫)/‖nvec n‖²| ≤ 100`.

The proof telescopes the factor `1 - cos` against the shift `n ↦ n ± e_j`: writing
`cos θ (1 - cos φ) = cos θ - cos(θ+φ)/2 - cos(θ-φ)/2` with `φ = 2π z_j` and `θ = 2π⟪nvec n,z⟫`
turns the sum into a sum of second differences of the kernel `1/‖nvec ·‖²` over the carrier
`telW T j = T ∪ (T+e_j) ∪ (T-e_j)`.  Splitting the carrier along the `j`-th coordinate into
*fibres* (`telEq j`, `telWp`) and applying

* the `1`-dimensional second-difference bound `telFiberBound`,
* the axis bound `telAxisLe`,
* the shell summation `restShellSum` and the arithmetic bound `telQSum`,

gives the uniform estimate `Σ_m |telG T j m| ≤ 100`.
-/

noncomputable section
open scoped Real BigOperators Topology
open MeasureTheory Metric

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false

variable {R : ℝ} {T : Finset (Fin 3 → ℤ)} {j : Fin 3}

/-- The carrier in the product coordinates. -/
def telWp (T : Finset (Fin 3 → ℤ)) (j : Fin 3) : Finset (ℤ × ({i : Fin 3 // i ≠ j} → ℤ)) :=
  (telW T j).map (telEq j).toEmbedding

lemma tel_mem_Wp {x : ℤ × ({i : Fin 3 // i ≠ j} → ℤ)} :
    x ∈ telWp T j ↔ (telEq j).symm x ∈ telW T j := by
  rw [telWp, Finset.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩; simpa using ha
  · intro h; exact ⟨(telEq j).symm x, h, by simp⟩

lemma tel_mem_W_iff (m : Fin 3 → ℤ) :
    m ∈ telW T j ↔ (m ∈ T ∨ m - telE j ∈ T ∨ m + telE j ∈ T) := by
  simp only [telW, Finset.mem_union]
  rw [mem_image_add_iff, mem_image_sub_iff]
  tauto

lemma tel_symm_eq_zero_iff (j : Fin 3) (x : ℤ × ({i : Fin 3 // i ≠ j} → ℤ)) :
    (telEq j).symm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h2 : x = telEq j 0 := by rw [← h, Equiv.apply_symm_apply]
    rw [h2]
    refine Prod.ext ?_ ?_
    · rw [telEq_fst]; rfl
    · funext i
      rw [telEq_snd]; rfl
  · intro h
    rw [h, Equiv.symm_apply_eq]
    rfl

lemma tel_inT_iff (hR : 0 ≤ R) (hTmem : ∀ n, n ∈ T ↔ n ≠ 0 ∧ ‖nvec n‖ ≤ R)
    (k : ℤ) (q : {i : Fin 3 // i ≠ j} → ℤ) :
    (telEq j).symm (k, q) ∈ T ↔ ((k, q) ≠ 0 ∧ (k : ℝ) ^ 2 + telQSq q ≤ R ^ 2) := by
  rw [hTmem]
  constructor
  · rintro ⟨hne, hle⟩
    refine ⟨?_, ?_⟩
    · intro hx; exact hne ((tel_symm_eq_zero_iff j (k, q)).mpr hx)
    · have h2 : ‖nvec ((telEq j).symm (k, q))‖ ^ 2 ≤ R ^ 2 := by
        nlinarith [norm_nonneg (nvec ((telEq j).symm (k, q))), hle]
      have h3 := h2
      rw [tel_normSq_symm] at h3
      push_cast at h3
      exact h3
  · rintro ⟨hne, hle⟩
    refine ⟨?_, ?_⟩
    · intro h; exact hne ((tel_symm_eq_zero_iff j (k, q)).mp h)
    · have h3 : ‖nvec ((telEq j).symm (k, q))‖ = Real.sqrt ((k : ℝ) ^ 2 + telQSq q) := by
        have h4 : (‖nvec ((telEq j).symm (k, q))‖) ^ 2 = (k : ℝ) ^ 2 + telQSq q := by
          have h5 := tel_normSq_symm (j := j) (k, q)
          simpa using h5
        rw [← h4, Real.sqrt_sq (norm_nonneg _)]
      rw [h3]
      have := Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq hR] at this

lemma tel_K_sq_le {Q : ℝ} (hQR : Q ≤ R ^ 2) :
    ((⌊Real.sqrt (R ^ 2 - Q)⌋₊ : ℝ)) ^ 2 ≤ R ^ 2 - Q := by
  have h3 : (0 : ℝ) ≤ (⌊Real.sqrt (R ^ 2 - Q)⌋₊ : ℝ) := Nat.cast_nonneg _
  have h1 : (⌊Real.sqrt (R ^ 2 - Q)⌋₊ : ℝ) ≤ Real.sqrt (R ^ 2 - Q) :=
    Nat.floor_le (Real.sqrt_nonneg _)
  have h4 : (⌊Real.sqrt (R ^ 2 - Q)⌋₊ : ℝ) ^ 2 ≤ (Real.sqrt (R ^ 2 - Q)) ^ 2 :=
    pow_le_pow_left₀ h3 h1 2
  rwa [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ R ^ 2 - Q)] at h4

lemma tel_sqrt_lt {Q : ℝ} (hQR : Q ≤ R ^ 2) :
    R ^ 2 - Q < ((⌊Real.sqrt (R ^ 2 - Q)⌋₊ : ℝ) + 1) ^ 2 := by
  have h1 : Real.sqrt (R ^ 2 - Q) < (⌊Real.sqrt (R ^ 2 - Q)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have h4 : (Real.sqrt (R ^ 2 - Q)) ^ 2 < ((⌊Real.sqrt (R ^ 2 - Q)⌋₊ : ℝ) + 1) ^ 2 :=
    pow_lt_pow_left₀ h1 (Real.sqrt_nonneg _) (by norm_num)
  rwa [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ R ^ 2 - Q)] at h4

/-- Membership in `T` along the axis is governed by the integer floor of `√(R²-Q)`. -/
lemma tel_abs_le_K_iff {Q : ℝ} (hQR : Q ≤ R ^ 2) (k : ℤ) :
    (|k| ≤ ((⌊Real.sqrt (R ^ 2 - Q)⌋₊ : ℕ) : ℤ)) ↔ ((k : ℝ) ^ 2 + Q ≤ R ^ 2) := by
  constructor
  · intro h
    have h2 : (|(k : ℝ)|) ≤ (⌊Real.sqrt (R ^ 2 - Q)⌋₊ : ℝ) := by
      rw [← Int.cast_abs]
      exact_mod_cast h
    have h5 : (|(k : ℝ)|) ^ 2 ≤ (⌊Real.sqrt (R ^ 2 - Q)⌋₊ : ℝ) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h2 2
    rw [sq_abs] at h5
    have h3 := tel_K_sq_le (R := R) hQR
    linarith
  · intro h
    by_contra hcon
    push_neg at hcon
    have h1 : (((⌊Real.sqrt (R ^ 2 - Q)⌋₊ : ℕ) : ℤ) + 1) ≤ |k| := by omega
    have h2 : ((⌊Real.sqrt (R ^ 2 - Q)⌋₊ : ℝ) + 1) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]
      push_cast
      exact_mod_cast h1
    have h3 := tel_sqrt_lt (R := R) hQR
    have h4 : (0 : ℝ) ≤ (⌊Real.sqrt (R ^ 2 - Q)⌋₊ : ℝ) + 1 := by positivity
    nlinarith [h2, h3, h4, abs_nonneg (k : ℝ), sq_abs (k : ℝ)]

/-- The summand of the `1`-dimensional fibre bound. -/
def telFib (R Q : ℝ) (k : ℤ) : ℝ :=
  (if |k| ≤ ((⌊Real.sqrt (R ^ 2 - Q)⌋₊ : ℕ) : ℤ) then 1 / (((k : ℝ)) ^ 2 + Q) else 0)
    - (1 / 2) * (if |k - 1| ≤ ((⌊Real.sqrt (R ^ 2 - Q)⌋₊ : ℕ) : ℤ) then
        1 / (((k : ℝ) - 1) ^ 2 + Q) else 0)
    - (1 / 2) * (if |k + 1| ≤ ((⌊Real.sqrt (R ^ 2 - Q)⌋₊ : ℕ) : ℤ) then
        1 / (((k : ℝ) + 1) ^ 2 + Q) else 0)

lemma tel_Q_le_of_mem (hTmem : ∀ n, n ∈ T ↔ n ≠ 0 ∧ ‖nvec n‖ ≤ R)
    (k : ℤ) (q' : {i : Fin 3 // i ≠ j} → ℤ)
    (h : (telEq j).symm (k, q') ∈ telW T j) : telQSq q' ≤ R ^ 2 := by
  rw [tel_mem_W_iff] at h
  rcases h with h1 | h2 | h3
  · have hle := (hTmem _).mp h1 |>.2
    have h4 : ((k : ℝ)) ^ 2 + telQSq q' ≤ R ^ 2 := by
      have h4' : ‖nvec ((telEq j).symm (k, q'))‖ ^ 2 ≤ R ^ 2 := by
        nlinarith [norm_nonneg (nvec ((telEq j).symm (k, q'))), hle]
      have h5 := h4'
      rw [tel_normSq_symm] at h5
      push_cast at h5
      exact h5
    linarith [sq_nonneg (k : ℝ)]
  · rw [telEq_symm_sub_E] at h2
    have hle := (hTmem _).mp h2 |>.2
    have h4 : ((k : ℝ) - 1) ^ 2 + telQSq q' ≤ R ^ 2 := by
      have h4' : ‖nvec ((telEq j).symm (k - 1, q'))‖ ^ 2 ≤ R ^ 2 := by
        nlinarith [norm_nonneg (nvec ((telEq j).symm (k - 1, q'))), hle]
      have h5 := h4'
      rw [tel_normSq_symm] at h5
      push_cast at h5
      exact h5
    linarith [sq_nonneg ((k : ℝ) - 1)]
  · rw [telEq_symm_add_E] at h3
    have hle := (hTmem _).mp h3 |>.2
    have h4 : ((k : ℝ) + 1) ^ 2 + telQSq q' ≤ R ^ 2 := by
      have h4' : ‖nvec ((telEq j).symm (k + 1, q'))‖ ^ 2 ≤ R ^ 2 := by
        nlinarith [norm_nonneg (nvec ((telEq j).symm (k + 1, q'))), hle]
      have h5 := h4'
      rw [tel_normSq_symm] at h5
      push_cast at h5
      exact h5
    linarith [sq_nonneg ((k : ℝ) + 1)]

/-- **The per-fibre bound.**  For a nonzero value of the two remaining coordinates, the sum of the
absolute values of the telescoping coefficients over that fibre is bounded by the `1`-dimensional
second-difference bound plus the boundary term. -/
lemma tel_fiber_le (hR : 1 ≤ R) (hTmem : ∀ n, n ∈ T ↔ n ≠ 0 ∧ ‖nvec n‖ ≤ R)
    (q : {i : Fin 3 // i ≠ j} → ℤ) (hq : q ≠ 0) :
    (∑ x ∈ (telWp T j).filter (fun x => x.2 = q), |telG T j ((telEq j).symm x)|)
      ≤ 27 / (10 * (Real.sqrt (telQSq q)) ^ 3) + min (10 / R ^ 2) (4 / telQSq q) := by
  classical
  have hR0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR
  have hQnn : (0 : ℝ) ≤ telQSq q := telQSq_nonneg q
  have hsq : (Real.sqrt (telQSq q)) ^ 2 = telQSq q := Real.sq_sqrt hQnn
  set s := (telWp T j).filter (fun x => x.2 = q) with hs
  by_cases hemp : s.Nonempty
  · obtain ⟨x0, hx0⟩ := hemp
    have hx0W : x0 ∈ telWp T j := (Finset.mem_filter.mp hx0).1
    have hx0q : x0.2 = q := (Finset.mem_filter.mp hx0).2
    have hQle : telQSq q ≤ R ^ 2 := by
      obtain ⟨k0, q0⟩ := x0
      have h0 : telQSq q0 ≤ R ^ 2 :=
        tel_Q_le_of_mem (T := T) (j := j) hTmem k0 q0 ((tel_mem_Wp).mp hx0W)
      rwa [show q0 = q from hx0q] at h0
    set K : ℕ := ⌊Real.sqrt (R ^ 2 - telQSq q)⌋₊ with hK
    have hK1 : ((K : ℝ)) ^ 2 + telQSq q ≤ R ^ 2 := by
      have := tel_K_sq_le (R := R) hQle
      rw [hK]; linarith
    have hK2 : R ^ 2 < (((K : ℝ)) + 1) ^ 2 + telQSq q := by
      have := tel_sqrt_lt (R := R) hQle
      rw [hK]; linarith
    have hρ : 1 ≤ Real.sqrt (telQSq q) := by
      rw [Real.one_le_sqrt]
      exact tel_one_le_telQSq hq
    -- the pointwise identification of the summands
    have hpoint : ∀ x ∈ s, |telG T j ((telEq j).symm x)| = |telFib R (telQSq q) x.1| := by
      rintro ⟨k, qq⟩ hx
      have hxq : qq = q := (Finset.mem_filter.mp hx).2
      subst qq
      have hne : (k, q) ≠ 0 := by
        intro h0
        have h1 : q = 0 := by
          have := congrArg (fun y : ℤ × ({i : Fin 3 // i ≠ j} → ℤ) => y.2) h0
          simpa using this
        exact hq h1
      have hne1 : (k - 1, q) ≠ 0 := by
        intro h0
        have h1 : q = 0 := by
          have := congrArg (fun y : ℤ × ({i : Fin 3 // i ≠ j} → ℤ) => y.2) h0
          simpa using this
        exact hq h1
      have hne2 : (k + 1, q) ≠ 0 := by
        intro h0
        have h1 : q = 0 := by
          have := congrArg (fun y : ℤ × ({i : Fin 3 // i ≠ j} → ℤ) => y.2) h0
          simpa using this
        exact hq h1
      have hKiff := tel_abs_le_K_iff (R := R) (Q := telQSq q) hQle
      have hKc : (|k| ≤ ((⌊Real.sqrt (R ^ 2 - telQSq q)⌋₊ : ℕ) : ℤ)) ↔
          ((k : ℝ) ^ 2 + telQSq q ≤ R ^ 2) := hKiff k
      have hK1c := hKiff (k - 1)
      have hK2c := hKiff (k + 1)
      have e1 : (if (telEq j).symm (k, q) ∈ T then 1 / ‖nvec ((telEq j).symm (k, q))‖ ^ 2 else 0)
          = (if |k| ≤ ((⌊Real.sqrt (R ^ 2 - telQSq q)⌋₊ : ℕ) : ℤ) then
              1 / (((k : ℝ)) ^ 2 + telQSq q) else 0) := by
        by_cases h : (telEq j).symm (k, q) ∈ T
        · have h2 := (tel_inT_iff (R := R) (T := T) (j := j) hR0 hTmem k q).mp h
          rw [if_pos h, if_pos (hKc.mpr h2.2)]
          simp [tel_normSq_symm]
        · rw [if_neg h, if_neg (fun hh => h ((tel_inT_iff (R := R) (T := T) (j := j) hR0 hTmem
              k q).mpr ⟨hne, hKc.mp hh⟩))]
      have e2 : (if (telEq j).symm (k, q) - telE j ∈ T then
            1 / ‖nvec ((telEq j).symm (k, q) - telE j)‖ ^ 2 else 0)
          = (if |k - 1| ≤ ((⌊Real.sqrt (R ^ 2 - telQSq q)⌋₊ : ℕ) : ℤ) then
              1 / (((k : ℝ) - 1) ^ 2 + telQSq q) else 0) := by
        rw [telEq_symm_sub_E]
        by_cases h : (telEq j).symm (k - 1, q) ∈ T
        · have h2 := (tel_inT_iff (R := R) (T := T) (j := j) hR0 hTmem (k - 1) q).mp h
          rw [if_pos h, if_pos (hK1c.mpr h2.2)]
          simp [tel_normSq_symm]
        · rw [if_neg h, if_neg (fun hh => h ((tel_inT_iff (R := R) (T := T) (j := j) hR0 hTmem
              (k - 1) q).mpr ⟨hne1, hK1c.mp hh⟩))]
      have e3 : (if (telEq j).symm (k, q) + telE j ∈ T then
            1 / ‖nvec ((telEq j).symm (k, q) + telE j)‖ ^ 2 else 0)
          = (if |k + 1| ≤ ((⌊Real.sqrt (R ^ 2 - telQSq q)⌋₊ : ℕ) : ℤ) then
              1 / (((k : ℝ) + 1) ^ 2 + telQSq q) else 0) := by
        rw [telEq_symm_add_E]
        by_cases h : (telEq j).symm (k + 1, q) ∈ T
        · have h2 := (tel_inT_iff (R := R) (T := T) (j := j) hR0 hTmem (k + 1) q).mp h
          rw [if_pos h, if_pos (hK2c.mpr h2.2)]
          simp [tel_normSq_symm]
        · rw [if_neg h, if_neg (fun hh => h ((tel_inT_iff (R := R) (T := T) (j := j) hR0 hTmem
              (k + 1) q).mpr ⟨hne2, hK2c.mp hh⟩))]
      rw [telG, telFib, e1, e2, e3]
    -- reindex the fibre sum
    have hinj : Set.InjOn (Prod.fst : ℤ × ({i : Fin 3 // i ≠ j} → ℤ) → ℤ) ↑s := by
      intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_filter] at ha hb
      exact Prod.ext hab (by rw [ha.2, hb.2])
    have hsum : (∑ x ∈ s, |telG T j ((telEq j).symm x)|)
        = ∑ k ∈ s.image Prod.fst, |telFib R (telQSq q) k| := by
      have h1 : (∑ x ∈ s, |telG T j ((telEq j).symm x)|)
          = ∑ x ∈ s, |telFib R (telQSq q) x.1| := Finset.sum_congr rfl hpoint
      rw [h1]
      exact (Finset.sum_image (f := fun k => |telFib R (telQSq q) k|) hinj).symm
    rw [hsum]
    -- the fibre is contained in the interval
    have hsub : s.image Prod.fst ⊆ Finset.Icc (-(K : ℤ) - 1) ((K : ℤ) + 1) := by
      rintro k hk
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hxW, hxq⟩ := Finset.mem_filter.mp hx
      obtain ⟨k0, q0⟩ := x
      have hq0 : q0 = q := hxq
      have hmW := (tel_mem_Wp).mp hxW
      rw [tel_mem_W_iff] at hmW
      have hKiff := tel_abs_le_K_iff (R := R) (Q := telQSq q) hQle
      have key : ∀ y : ℤ, (telEq j).symm (y, q0) ∈ T → |y| ≤ (K : ℤ) := by
        intro y hy
        have h2 := (tel_inT_iff (R := R) (T := T) (j := j) hR0 hTmem y q0).mp hy
        exact (hKiff y).mpr (by rw [hq0] at h2; simpa using h2.2)
      rw [Finset.mem_Icc]
      rcases hmW with h1 | h2 | h3
      · obtain ⟨ha, hb⟩ := abs_le.mp (key k0 h1)
        constructor <;> omega
      · rw [telEq_symm_sub_E] at h2
        obtain ⟨ha, hb⟩ := abs_le.mp (key (k0 - 1) h2)
        constructor <;> omega
      · rw [telEq_symm_add_E] at h3
        obtain ⟨ha, hb⟩ := abs_le.mp (key (k0 + 1) h3)
        constructor <;> omega
    -- apply the `1`-dimensional bound
    have h1d := telFiberBound R (Real.sqrt (telQSq q)) hR hρ K (by rw [hsq]; exact hK1)
      (by rw [hsq]; exact hK2)
    have hrewrite : ∀ k : ℤ, |telFib R (telQSq q) k|
        = |(if |k| ≤ (K : ℤ) then 1 / (((k : ℝ)) ^ 2 + (Real.sqrt (telQSq q)) ^ 2) else 0)
            - (1 / 2) * (if |k - 1| ≤ (K : ℤ) then
                1 / (((k : ℝ) - 1) ^ 2 + (Real.sqrt (telQSq q)) ^ 2) else 0)
            - (1 / 2) * (if |k + 1| ≤ (K : ℤ) then
                1 / (((k : ℝ) + 1) ^ 2 + (Real.sqrt (telQSq q)) ^ 2) else 0)| := by
      intro k
      rw [telFib, hK, hsq]
    calc ∑ k ∈ s.image Prod.fst, |telFib R (telQSq q) k|
        ≤ ∑ k ∈ Finset.Icc (-(K : ℤ) - 1) ((K : ℤ) + 1), |telFib R (telQSq q) k| :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => abs_nonneg _)
      _ = ∑ k ∈ Finset.Icc (-(K : ℤ) - 1) ((K : ℤ) + 1),
            |(if |k| ≤ (K : ℤ) then 1 / (((k : ℝ)) ^ 2 + (Real.sqrt (telQSq q)) ^ 2) else 0)
              - (1 / 2) * (if |k - 1| ≤ (K : ℤ) then
                  1 / (((k : ℝ) - 1) ^ 2 + (Real.sqrt (telQSq q)) ^ 2) else 0)
              - (1 / 2) * (if |k + 1| ≤ (K : ℤ) then
                  1 / (((k : ℝ) + 1) ^ 2 + (Real.sqrt (telQSq q)) ^ 2) else 0)| :=
          Finset.sum_congr rfl (fun k _ => hrewrite k)
      _ ≤ 27 / (10 * (Real.sqrt (telQSq q)) ^ 3) + min (10 / R ^ 2) (4 / (Real.sqrt (telQSq q)) ^ 2) := h1d
      _ = 27 / (10 * (Real.sqrt (telQSq q)) ^ 3) + min (10 / R ^ 2) (4 / telQSq q) := by rw [hsq]
  · rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.sum_empty]
    positivity

/-- Integer absolute value against a natural bound. -/
lemma tel_natAbs_le_iff {a : ℤ} {N : ℕ} :
    a.natAbs ≤ N ↔ -(N : ℤ) ≤ a ∧ a ≤ (N : ℤ) := by
  rw [← Nat.cast_le (α := ℤ), ← Int.abs_eq_natAbs]
  exact abs_le

/-- The `ℓ^∞`-norm of the rest coordinates is at most their Euclidean norm. -/
lemma telAbs_le_floor_sqrt {j : Fin 3} (q : {i : Fin 3 // i ≠ j} → ℤ) :
    telAbs q ≤ ⌊Real.sqrt (telQSq q)⌋₊ := by
  rw [telAbs, Finset.sup_le_iff]
  intro i _
  apply Nat.le_floor
  have h1 : (((q i : ℝ)) ^ 2) ≤ telQSq q := by
    rw [telQSq]
    exact Finset.single_le_sum (f := fun k : {i : Fin 3 // i ≠ j} => ((q k : ℝ)) ^ 2)
      (fun k _ => by positivity) (Finset.mem_univ i)
  have h2 := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq_eq_abs] at h2
  simpa [Int.natCast_natAbs]

lemma telAbs_le_sqrt {j : Fin 3} (q : {i : Fin 3 // i ≠ j} → ℤ) :
    ((telAbs q : ℕ) : ℝ) ≤ Real.sqrt (telQSq q) :=
  le_trans (by exact_mod_cast telAbs_le_floor_sqrt q) (Nat.floor_le (Real.sqrt_nonneg _))

/-- Membership in the box of side `2N+1` is the `ℓ^∞`-bound on the rest coordinates. -/
lemma tel_mem_box_iff {j : Fin 3} {N : ℕ} {q : {i : Fin 3 // i ≠ j} → ℤ} :
    q ∈ Fintype.piFinset (fun _ : {i : Fin 3 // i ≠ j} => Finset.Icc (-(N : ℤ)) (N : ℤ))
      ↔ telAbs q ≤ N := by
  rw [Fintype.mem_piFinset, telAbs, Finset.sup_le_iff]
  constructor
  · intro h i _
    exact tel_natAbs_le_iff.mpr (Finset.mem_Icc.mp (h i))
  · intro h i
    exact Finset.mem_Icc.mpr (tel_natAbs_le_iff.mp (h i (Finset.mem_univ i)))

/-- A nonzero rest point has `ℓ^∞`-norm at least `1`. -/
lemma tel_one_le_telAbs {j : Fin 3} {q : {i : Fin 3 // i ≠ j} → ℤ} (hq : q ≠ 0) :
    1 ≤ telAbs q := by
  obtain ⟨i, hi⟩ : ∃ i, q i ≠ 0 := by
    by_contra h
    exact hq (funext fun i => not_not.mp (not_exists.mp h i))
  have h3 : (1 : ℕ) ≤ (q i).natAbs := by
    have h4 : (1 : ℤ) ≤ |q i| := Int.one_le_abs hi
    rw [Int.abs_eq_natAbs] at h4
    exact_mod_cast h4
  refine le_trans h3 ?_
  rw [telAbs]
  exact Finset.le_sup (f := fun i => (q i).natAbs) (Finset.mem_univ i)

/-- The shell decomposition, with a real-indexed weight. -/
lemma tel_shell_sum (N : ℕ) (ψ : ℝ → ℝ) :
    (∑ q ∈ Fintype.piFinset (fun _ : {i : Fin 3 // i ≠ j} => Finset.Icc (-(N : ℤ)) (N : ℤ)),
        ψ (((telAbs q : ℕ)) : ℝ))
      = ψ ((0 : ℤ) : ℝ)
        + ∑ M ∈ Finset.Icc 1 N, (8 * (M : ℝ)) * ψ ((((M : ℕ) : ℤ) : ℝ)) := by
  have h := restShellSum j N (fun M : ℤ => ψ ((M : ℝ)))
  rw [← h]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  simp [telAbs]

/-- **The sum over the rest coordinates.**  Splitting off the axis term and using the shell
decomposition of the box reduces the total to the one-dimensional arithmetic bound. -/
lemma tel_qsum_le (hR : 1 ≤ R) (Q : Finset ({i : Fin 3 // i ≠ j} → ℤ))
    (hQ : ∀ q ∈ Q, q = 0 ∨ telQSq q ≤ R ^ 2) :
    (∑ q ∈ Q, (if q = 0 then 7
        else 27 / (10 * (Real.sqrt (telQSq q)) ^ 3) + min (10 / R ^ 2) (4 / telQSq q))) ≤ 99 := by
  classical
  set N : ℕ := ⌊R⌋₊ with hN
  set box : Finset ({i : Fin 3 // i ≠ j} → ℤ) :=
    Fintype.piFinset (fun _ : {i : Fin 3 // i ≠ j} => Finset.Icc (-(N : ℤ)) (N : ℤ)) with hbox
  have hNle : (N : ℝ) ≤ R := by rw [hN]; exact Nat.floor_le (le_trans zero_le_one hR)
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hφnn : ∀ q : {i : Fin 3 // i ≠ j} → ℤ,
      0 ≤ 27 / (10 * (((telAbs q : ℕ)) : ℝ) ^ 3)
        + min (10 / R ^ 2) (4 / (((telAbs q : ℕ)) : ℝ) ^ 2) := by
    intro q
    have h3 : (0 : ℝ) ≤ (((telAbs q : ℕ)) : ℝ) := Nat.cast_nonneg _
    have h1 : 0 ≤ 27 / (10 * (((telAbs q : ℕ)) : ℝ) ^ 3) :=
      div_nonneg (by norm_num) (by positivity)
    have h2 : 0 ≤ min (10 / R ^ 2) (4 / (((telAbs q : ℕ)) : ℝ) ^ 2) :=
      le_min (div_nonneg (by norm_num) (sq_nonneg R))
        (div_nonneg (by norm_num) (by positivity))
    linarith
  have hboxmem : ∀ q ∈ Q, q ∈ box := by
    intro q hq
    rcases hQ q hq with h0 | h0
    · rw [h0, hbox, tel_mem_box_iff, telAbs, Finset.sup_le_iff]
      intro i _; simp
    · rw [hbox, tel_mem_box_iff]
      have h1 := telAbs_le_sqrt q
      have h2 : Real.sqrt (telQSq q) ≤ R := by
        rw [Real.sqrt_le_iff]
        exact ⟨le_trans zero_le_one hR, h0⟩
      exact Nat.le_floor (le_trans h1 h2)
  -- Step 1: restrict to the box
  have hstep : (∑ q ∈ Q, (if q = 0 then 7
        else 27 / (10 * (Real.sqrt (telQSq q)) ^ 3) + min (10 / R ^ 2) (4 / telQSq q)))
      ≤ ∑ q ∈ box, (if q = 0 then 7
        else 27 / (10 * (Real.sqrt (telQSq q)) ^ 3) + min (10 / R ^ 2) (4 / telQSq q)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hboxmem
    intro q _ _
    by_cases h0 : q = 0
    · rw [if_pos h0]; norm_num
    · rw [if_neg h0]
      have h1 : 0 ≤ 27 / (10 * (Real.sqrt (telQSq q)) ^ 3) :=
        div_nonneg (by norm_num) (by positivity)
      have h2 : 0 ≤ min (10 / R ^ 2) (4 / telQSq q) :=
        le_min (div_nonneg (by norm_num) (by positivity))
          (div_nonneg (by norm_num) (telQSq_nonneg q))
      linarith
  refine le_trans hstep ?_
  -- Step 2: split off the origin
  have hzero : (0 : {i : Fin 3 // i ≠ j} → ℤ) ∈ box := by
    rw [hbox, tel_mem_box_iff, telAbs, Finset.sup_le_iff]
    intro i _
    simp
  have hψ0 : (if (0 : {i : Fin 3 // i ≠ j} → ℤ) = 0 then 7
      else 27 / (10 * (Real.sqrt (telQSq (j := j) 0)) ^ 3) + min (10 / R ^ 2)
        (4 / telQSq (j := j) 0)) = 7 := by simp
  have hsplit : (∑ q ∈ box, (if q = 0 then 7
        else 27 / (10 * (Real.sqrt (telQSq q)) ^ 3) + min (10 / R ^ 2) (4 / telQSq q)))
      = (∑ q ∈ box.erase 0, (if q = 0 then 7
        else 27 / (10 * (Real.sqrt (telQSq q)) ^ 3) + min (10 / R ^ 2) (4 / telQSq q))) + 7 := by
    rw [← Finset.sum_erase_add box
      (fun q => (if q = 0 then 7
        else 27 / (10 * (Real.sqrt (telQSq q)) ^ 3) + min (10 / R ^ 2) (4 / telQSq q))) hzero, hψ0]
  rw [hsplit]
  have hrest : (∑ q ∈ box.erase 0, (if q = 0 then 7
        else 27 / (10 * (Real.sqrt (telQSq q)) ^ 3) + min (10 / R ^ 2) (4 / telQSq q)))
      ≤ ∑ M ∈ Finset.Icc 1 N, (8 * (M : ℝ)) *
          (27 / (10 * (M : ℝ) ^ 3) + min (10 / R ^ 2) (4 / (M : ℝ) ^ 2)) := by
    have hpt : ∀ q ∈ box.erase 0, (if q = 0 then 7
          else 27 / (10 * (Real.sqrt (telQSq q)) ^ 3) + min (10 / R ^ 2) (4 / telQSq q))
          ≤ 27 / (10 * (((telAbs q : ℕ)) : ℝ) ^ 3)
            + min (10 / R ^ 2) (4 / (((telAbs q : ℕ)) : ℝ) ^ 2) := by
      intro q hq
      have hq0 : q ≠ 0 := (Finset.mem_erase.mp hq).1
      have hρ : ((telAbs q : ℕ) : ℝ) ≤ Real.sqrt (telQSq q) := telAbs_le_sqrt q
      have h1 : (1 : ℝ) ≤ ((telAbs q : ℕ) : ℝ) := by
        exact_mod_cast tel_one_le_telAbs hq0
      rw [if_neg hq0]
      have hden3 : 10 * (((telAbs q : ℕ)) : ℝ) ^ 3 ≤ 10 * (Real.sqrt (telQSq q)) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hρ 3) (by norm_num)
      have hden2 : (((telAbs q : ℕ)) : ℝ) ^ 2 ≤ telQSq q := by
        have hsq := Real.sq_sqrt (telQSq_nonneg q)
        have := pow_le_pow_left₀ (by positivity) hρ 2
        rwa [hsq] at this
      have h3 : 27 / (10 * (Real.sqrt (telQSq q)) ^ 3)
          ≤ 27 / (10 * (((telAbs q : ℕ)) : ℝ) ^ 3) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hden3
      have h4 : min (10 / R ^ 2) (4 / telQSq q)
          ≤ min (10 / R ^ 2) (4 / (((telAbs q : ℕ)) : ℝ) ^ 2) :=
        min_le_min_left _ (div_le_div_of_nonneg_left (by norm_num) (by positivity) hden2)
      linarith
    refine le_trans (Finset.sum_le_sum hpt) ?_
    have hsub : box.erase 0 ⊆ box := Finset.erase_subset _ _
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hφnn _)) ?_
    rw [hbox, tel_shell_sum N (fun t : ℝ => 27 / (10 * t ^ 3) + min (10 / R ^ 2) (4 / t ^ 2))]
    have h0 : 27 / (10 * ((0 : ℤ) : ℝ) ^ 3)
        + min (10 / R ^ 2) (4 / ((0 : ℤ) : ℝ) ^ 2) = 0 := by
      have hR2 : (0 : ℝ) ≤ 10 / R ^ 2 := div_nonneg (by norm_num) (sq_nonneg R)
      have h1 : 27 / (10 * ((0 : ℤ) : ℝ) ^ 3) = 0 := by norm_num
      have h2 : 4 / ((0 : ℤ) : ℝ) ^ 2 = 0 := by norm_num
      rw [h1, h2, min_eq_right hR2, add_zero]
    rw [h0, zero_add]
    apply Finset.sum_le_sum
    intro M _
    have hMM : 27 / (10 * ((((M : ℕ) : ℤ) : ℝ)) ^ 3) + min (10 / R ^ 2) (4 / ((((M : ℕ) : ℤ) : ℝ)) ^ 2)
        = 27 / (10 * (M : ℝ) ^ 3) + min (10 / R ^ 2) (4 / (M : ℝ) ^ 2) := by
      rw [Int.cast_natCast]
    rw [hMM]
  have hbound := telQSum R hR N hNle
  linarith

/-- A nonzero lattice vector has norm at least `1`. -/
lemma tel_one_le_norm {n : Fin 3 → ℤ} (hn : n ≠ 0) : 1 ≤ ‖nvec n‖ := by
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
    by_contra h
    exact hn (funext fun i => not_not.mp (not_exists.mp h i))
  have h1 : (1 : ℝ) ≤ |((n i : ℤ) : ℝ)| := by
    have h2 : (1 : ℤ) ≤ |n i| := Int.one_le_abs hi
    exact_mod_cast h2
  have h3 : |((n i : ℤ) : ℝ)| ≤ ‖nvec n‖ := by
    rw [← Real.norm_eq_abs, ← nvec_apply]
    exact PiLp.norm_apply_le (p := 2) _ i
  linarith

/-- **The `3`-dimensional estimate.**  The absolute sum of the telescoping coefficients over the
carrier is at most `100`. -/
theorem telEstimate (R : ℝ) (hR : 1 ≤ R) (T : Finset (Fin 3 → ℤ)) (j : Fin 3)
    (h1 : ∀ n ∈ T, n ≠ 0) (h2 : ∀ n ∈ T, ‖nvec n‖ ≤ R)
    (h4 : ∀ n : Fin 3 → ℤ, n ≠ 0 → ‖nvec n‖ ≤ R → n ∈ T) :
    ∑ m ∈ telW T j, |telG T j m| ≤ 100 := by
  have hTmem : ∀ n, n ∈ T ↔ n ≠ 0 ∧ ‖nvec n‖ ≤ R :=
    fun n => ⟨fun h => ⟨h1 n h, h2 n h⟩, fun h => h4 n h.1 h.2⟩
  have hstep1 : (∑ m ∈ telW T j, |telG T j m|)
      = ∑ x ∈ telWp T j, |telG T j ((telEq j).symm x)| := by
    rw [telWp, Finset.sum_map]
    exact Finset.sum_congr rfl (fun m _ => by
      have h : (telEq j).toEmbedding m = telEq j m := rfl
      rw [h, Equiv.symm_apply_apply])
  rw [hstep1]
  set Q := (telWp T j).image Prod.snd with hQ
  rw [← Finset.sum_fiberwise_of_maps_to (s := telWp T j) (t := Q) (g := Prod.snd)
    (fun x hx => Finset.mem_image_of_mem _ hx) (fun x => |telG T j ((telEq j).symm x)|)]
  have hQproper : ∀ q ∈ Q, q = 0 ∨ telQSq q ≤ R ^ 2 := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    by_cases hq0 : x.2 = 0
    · exact Or.inl hq0
    · exact Or.inr (tel_Q_le_of_mem (T := T) (j := j) hTmem x.1 x.2 ((tel_mem_Wp).mp hx))
  calc ∑ q ∈ Q, ∑ x ∈ (telWp T j).filter (fun x => x.2 = q),
          |telG T j ((telEq j).symm x)|
      ≤ ∑ q ∈ Q, (if q = 0 then 7
          else 27 / (10 * (Real.sqrt (telQSq q)) ^ 3) + min (10 / R ^ 2) (4 / telQSq q)) := by
        refine Finset.sum_le_sum (fun q _ => ?_)
        by_cases hq0 : q = 0
        · rw [if_pos hq0, hq0]
          exact telAxisLe R hR T j h1 h2 h4
        · rw [if_neg hq0]
          exact tel_fiber_le (T := T) (j := j) hR hTmem q hq0
    _ ≤ 99 := tel_qsum_le hR Q hQproper
    _ ≤ 100 := by norm_num

/-- **The telescoping cosine bound.** -/
theorem telescopeCos (R : ℝ) (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (z : E3)
    (h1 : ∀ n ∈ T, n ≠ 0) (h2 : ∀ n ∈ T, ‖nvec n‖ ≤ R)
    (h4 : ∀ n : Fin 3 → ℤ, n ≠ 0 → ‖nvec n‖ ≤ R → n ∈ T) :
    (1 - Real.cos (2 * Real.pi * z.ofLp j))
      * |∑ n ∈ T, Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2| ≤ 100 := by

  by_cases hR : R < 1
  · have hTempty : T = ∅ := by
      ext n
      constructor
      · intro hn
        exfalso
        have h2n : ‖nvec n‖ ≤ R := h2 n hn
        have h3 := tel_one_le_norm (h1 n hn)
        linarith
      · intro hn; exact absurd hn (by simp)
    rw [hTempty]
    simp
  · push_neg at hR
    have hmain : (1 - Real.cos (2 * Real.pi * z.ofLp j))
          * (∑ n ∈ T, Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2)
        = ∑ m ∈ telW T j, telG T j m * Real.cos (telTh z m) := telIdent T j z
    have hbound : |∑ m ∈ telW T j, telG T j m * Real.cos (telTh z m)| ≤ 100 := by
      calc |∑ m ∈ telW T j, telG T j m * Real.cos (telTh z m)|
          ≤ ∑ m ∈ telW T j, |telG T j m * Real.cos (telTh z m)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ telW T j, |telG T j m| := by
            refine Finset.sum_le_sum (fun m _ => ?_)
            calc |telG T j m * Real.cos (telTh z m)|
                = |telG T j m| * |Real.cos (telTh z m)| := abs_mul _ _
              _ ≤ |telG T j m| * 1 :=
                  mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
              _ = |telG T j m| := mul_one _
        _ ≤ 100 := telEstimate R hR T j h1 h2 h4
    calc (1 - Real.cos (2 * Real.pi * z.ofLp j))
          * |∑ n ∈ T, Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2|
        = |(1 - Real.cos (2 * Real.pi * z.ofLp j))
            * (∑ n ∈ T, Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2)| := by
          rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
      _ = |∑ m ∈ telW T j, telG T j m * Real.cos (telTh z m)| := by rw [hmain]
      _ ≤ 100 := hbound


end Work.BoseRowsL.LatticeCoulomb
