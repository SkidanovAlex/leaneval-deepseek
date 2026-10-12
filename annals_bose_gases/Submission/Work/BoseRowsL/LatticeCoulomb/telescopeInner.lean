import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseRowsL.LatticeCoulomb.teleEst
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.telescopeInner`

The **inner-product telescoping bound**: with `T` the lattice ball `{n ≠ 0 : ‖nvec n‖ ≤ R}`,

`|Σ_{n∈T} sin(2π⟪n,z⟫)·⟪n, sigBullet z⟫·(−2/‖n‖⁴) + gam z·Σ_{n∈T}cos(2π⟪n,z⟫)/‖n‖²| ≤ 1000`.

## Proof

Decompose the first sum into coordinates: `⟪nvec n, sigBullet z⟫ = Σ_j (nvec n)_j (sigBullet z)_j`
and `gam z = Σ_j (sigBullet z)_j sin (2π z_j)`, so the target is
`Σ_j (sigBullet z)_j·V_j` with `V_j` the *one-coordinate* telescope

`V_j = Σ_{n∈T} sin(2π⟪n,z⟫)·(−2 n_j/‖n‖⁴) + sin (2π z_j)·Σ_{n∈T}cos(2π⟪n,z⟫)/‖n‖²`.

By `telescope_identity` (summation by parts against the Coulomb kernel `teleH`), `V_j` equals
`(1/2)cos(2π z_j)·teleSh1 + (1/2)sin(2π z_j)·teleSh2 + Σ sin·teleErr`, and the two shell sums are
supported on the thin set where the indicators `1_T(· ± e_j)` differ, where
`tele_shell_sum` bounds their `teleH`-weight by `300`.  With `|Σ sin·teleErr| ≤ 700`
(`teleErr_sum`) this gives `|V_j| ≤ 1150`, and `|(sigBullet z)_j| ≤ 1/4`
(`tele_sigBullet_coord`) yields `|Σ_j (sigBullet z)_j V_j| ≤ (3/4)·1150 < 1000`.
-/

noncomputable section

open scoped Real BigOperators Topology
open MeasureTheory Metric

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false

/-! ## Elementary API for the indicator -/

private lemma teleInd_eq_one_iff' (T : Finset (Fin 3 → ℤ)) (m : Fin 3 → ℤ) :
    teleInd T m = 1 ↔ m ∈ T := by
  constructor
  · intro h
    by_contra hmem
    rw [teleInd_of_notMem hmem] at h
    exact one_ne_zero h.symm
  · exact teleInd_of_mem

private lemma teleInd_ne_iff' (T : Finset (Fin 3 → ℤ)) (a b : Fin 3 → ℤ) :
    teleInd T a ≠ teleInd T b ↔ (a ∈ T ∧ b ∉ T) ∨ (a ∉ T ∧ b ∈ T) := by
  constructor
  · intro h
    by_cases ha : a ∈ T <;> by_cases hb : b ∈ T
    · exact absurd (by rw [teleInd_of_mem ha, teleInd_of_mem hb]) h
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hb⟩
    · exact absurd (by rw [teleInd_of_notMem ha, teleInd_of_notMem hb]) h
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · rw [teleInd_of_mem ha, teleInd_of_notMem hb]; norm_num
    · rw [teleInd_of_notMem ha, teleInd_of_mem hb]; norm_num

/-- The lattice basis vector has norm one. -/
private lemma tele_norm_latE (j : Fin 3) : ‖nvec (teleE j)‖ = 1 := by
  have h2 : ‖nvec (teleE j)‖ ^ 2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ)]
    rw [Finset.sum_eq_single j]
    · simp [tele_nvec_teleE_self]
    · intro i _ hi
      simp [nvec_apply, teleE_ne hi]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  nlinarith [norm_nonneg (nvec (teleE j))]

private lemma tele_norm_ge_sub (m : Fin 3 → ℤ) (j : Fin 3) :
    ‖nvec m‖ ≥ ‖nvec (m + teleE j)‖ - 1 := by
  have h : nvec m = nvec (m + teleE j) - nvec (teleE j) := by
    rw [tele_nvec_add]; abel
  have h3 : ‖nvec (m + teleE j)‖ - ‖nvec (teleE j)‖ ≤ ‖nvec m‖ := by
    rw [h]
    exact le_trans (le_abs_self _) (abs_norm_sub_norm_le _ _)
  rw [tele_norm_latE] at h3
  linarith

private lemma tele_norm_ge_sub' (m : Fin 3 → ℤ) (j : Fin 3) :
    ‖nvec m‖ ≥ ‖nvec (m - teleE j)‖ - 1 := by
  have h : nvec m = nvec (m - teleE j) + nvec (teleE j) := by
    rw [tele_nvec_sub]; abel
  have h3 : ‖nvec (m - teleE j)‖ ≤ ‖nvec m‖ + ‖nvec (teleE j)‖ := by
    rw [h]
    have := norm_sub_le (nvec (m - teleE j) + nvec (teleE j)) (nvec (teleE j))
    simpa using this
  rw [tele_norm_latE] at h3
  linarith

private lemma tele_norm_le_add (m : Fin 3 → ℤ) (j : Fin 3) :
    ‖nvec (m + teleE j)‖ ≤ ‖nvec m‖ + 1 := by
  rw [tele_nvec_add]
  calc ‖nvec m + nvec (teleE j)‖ ≤ ‖nvec m‖ + ‖nvec (teleE j)‖ := norm_add_le _ _
    _ = ‖nvec m‖ + 1 := by rw [tele_norm_latE]

private lemma tele_norm_le_add' (m : Fin 3 → ℤ) (j : Fin 3) :
    ‖nvec (m - teleE j)‖ ≤ ‖nvec m‖ + 1 := by
  rw [tele_nvec_sub]
  calc ‖nvec m - nvec (teleE j)‖ ≤ ‖nvec m‖ + ‖nvec (teleE j)‖ := norm_sub_le _ _
    _ = ‖nvec m‖ + 1 := by rw [tele_norm_latE]

/-- The carrier of the shell sums consists of the three pieces. -/
private lemma tele_mem_carrier {T : Finset (Fin 3 → ℤ)} {j : Fin 3} {m : Fin 3 → ℤ}
    (hm : m ∈ teleCarrier T j) :
    m ∈ T ∨ (∃ n ∈ T, n + teleE j = m) ∨ (∃ n ∈ T, n - teleE j = m) := by
  simp only [teleCarrier, Finset.mem_union, Finset.mem_image] at hm
  rcases hm with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-! ## The geometry of the two shells -/

/-- The upper norm bound on the first shell. -/
private lemma tele_shell1_hi (R : ℝ) (T : Finset (Fin 3 → ℤ)) (j : Fin 3)
    (h2 : ∀ n ∈ T, ‖nvec n‖ ≤ R)
    (h4 : ∀ n : Fin 3 → ℤ, n ≠ 0 → ‖nvec n‖ ≤ R → n ∈ T) :
    ∀ m ∈ teleShell1 T j, ‖nvec m‖ ≤ R + 1 := by
  intro m hm
  have hmem : m ∈ teleCarrier T j := (Finset.mem_filter.mp hm).1
  rcases tele_mem_carrier hmem with h | ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
  · linarith [h2 m h]
  · have := tele_norm_le_add n j
    linarith [h2 n hn, this]
  · have := tele_norm_le_add' n j
    linarith [h2 n hn, this]

/-- The lower norm alternative on the first shell. -/
private lemma tele_shell1_lo (R : ℝ) (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (hR : 1 ≤ R)
    (h2 : ∀ n ∈ T, ‖nvec n‖ ≤ R)
    (h4 : ∀ n : Fin 3 → ℤ, n ≠ 0 → ‖nvec n‖ ≤ R → n ∈ T) :
    ∀ m ∈ teleShell1 T j, R - 1 ≤ ‖nvec m‖ ∨ ‖nvec m‖ ≤ 1 := by
  intro m hm
  have hmem : m ∈ teleCarrier T j := (Finset.mem_filter.mp hm).1
  have hind : teleInd T (m - teleE j) ≠ teleInd T (m + teleE j) := (Finset.mem_filter.mp hm).2
  rcases le_or_gt (‖nvec m‖) 1 with hle | hgt
  · exact Or.inr hle
  · refine Or.inl ?_
    -- in this branch `‖m‖ > 1`, so a neighbour of `m` that is outside `T` has norm `> R`
    have hOut : ∀ n : Fin 3 → ℤ, n ∉ T → n ≠ 0 → R < ‖nvec n‖ := by
      intro n hnT hn0
      by_contra hc
      push_neg at hc
      exact hnT (h4 n hn0 hc)
    rcases (teleInd_ne_iff' T (m - teleE j) (m + teleE j)).mp hind with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · -- `m - e ∈ T`, `m + e ∉ T`
      have h0 : m + teleE j ≠ 0 := by
        intro hz
        have hmm : m = -(teleE j) := eq_neg_of_add_eq_zero_left hz
        rw [hmm, tele_nvec_neg, norm_neg, tele_norm_latE] at hgt
        linarith
      have hRlt := hOut _ hb h0
      have := tele_norm_ge_sub m j
      linarith
    · -- `m + e ∈ T`, `m - e ∉ T`
      have h0 : m - teleE j ≠ 0 := by
        intro hz
        have hmm : m = teleE j := sub_eq_zero.mp hz
        rw [hmm, tele_norm_latE] at hgt
        linarith
      have hRlt := hOut _ ha h0
      have := tele_norm_ge_sub' m j
      linarith

/-- The upper norm bound on the second shell. -/
private lemma tele_shell2_hi (R : ℝ) (T : Finset (Fin 3 → ℤ)) (j : Fin 3)
    (h2 : ∀ n ∈ T, ‖nvec n‖ ≤ R)
    (h4 : ∀ n : Fin 3 → ℤ, n ≠ 0 → ‖nvec n‖ ≤ R → n ∈ T) :
    ∀ m ∈ teleShell2 T j, ‖nvec m‖ ≤ R + 1 := by
  intro m hm
  have hmem : m ∈ teleCarrier T j := (Finset.mem_filter.mp hm).1
  rcases tele_mem_carrier hmem with h | ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
  · linarith [h2 m h]
  · have := tele_norm_le_add n j
    linarith [h2 n hn, this]
  · have := tele_norm_le_add' n j
    linarith [h2 n hn, this]

/-- The lower norm alternative on the second shell. -/
private lemma tele_shell2_lo (R : ℝ) (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (hR : 1 ≤ R)
    (h1 : ∀ n ∈ T, n ≠ 0) (h2 : ∀ n ∈ T, ‖nvec n‖ ≤ R)
    (h4 : ∀ n : Fin 3 → ℤ, n ≠ 0 → ‖nvec n‖ ≤ R → n ∈ T) :
    ∀ m ∈ teleShell2 T j, R - 1 ≤ ‖nvec m‖ ∨ ‖nvec m‖ ≤ 1 := by
  intro m hm
  have hmem : m ∈ teleCarrier T j := (Finset.mem_filter.mp hm).1
  have hcoef : 2 * teleInd T m - teleInd T (m - teleE j) - teleInd T (m + teleE j) ≠ 0 :=
    (Finset.mem_filter.mp hm).2
  have hOut : ∀ n : Fin 3 → ℤ, n ∉ T → n ≠ 0 → R < ‖nvec n‖ := by
    intro n hnT hn0
    by_contra hc
    push_neg at hc
    exact hnT (h4 n hn0 hc)
  rcases le_or_gt (‖nvec m‖) 1 with hle | hgt
  · exact Or.inr hle
  · refine Or.inl ?_
    -- `m ∉ T` gives `R < ‖m‖`; `m ∈ T` with a neighbour outside `T` gives the estimate
    rcases tele_mem_carrier hmem with h | ⟨n, hn, heq⟩ | ⟨n, hn, heq⟩
    · by_cases hb : m + teleE j ∈ T
      · by_cases hc : m - teleE j ∈ T
        · -- both neighbours in `T`: the coefficient condition forces `m ∉ T`-like behaviour
          exfalso
          rw [teleInd_of_mem h, teleInd_of_mem hc, teleInd_of_mem hb] at hcoef
          norm_num at hcoef
        · have h0 : m - teleE j ≠ 0 := by
            intro hz
            have hmm : m = teleE j := sub_eq_zero.mp hz
            rw [hmm, tele_norm_latE] at hgt
            linarith
          have hRlt := hOut _ hc h0
          have := tele_norm_ge_sub' m j
          linarith
      · have h0 : m + teleE j ≠ 0 := by
          intro hz
          have hmm : m = -(teleE j) := eq_neg_of_add_eq_zero_left hz
          rw [hmm, tele_nvec_neg, norm_neg, tele_norm_latE] at hgt
          linarith
        have hRlt := hOut _ hb h0
        have := tele_norm_ge_sub m j
        linarith
    · -- `m = n + e` with `n ∈ T`
      by_cases hmT : m ∈ T
      · have hne : m + teleE j ∉ T := by
          intro hb
          rw [teleInd_of_mem hmT, teleInd_of_mem hb] at hcoef
          have h1' : teleInd T (m - teleE j) = 1 := by
            have hsub : m - teleE j = n := by rw [← heq]; abel
            rw [hsub]; exact teleInd_of_mem hn
          rw [h1'] at hcoef
          norm_num at hcoef
        have h0 : m + teleE j ≠ 0 := by
          intro hz
          have hmm : m = -(teleE j) := eq_neg_of_add_eq_zero_left hz
          rw [hmm, tele_nvec_neg, norm_neg, tele_norm_latE] at hgt
          linarith
        have hRlt := hOut _ hne h0
        have := tele_norm_ge_sub m j
        linarith
      · have hm0 : m ≠ 0 := by
          intro hz
          rw [hz] at hgt
          simp only [nvec_zero, norm_zero] at hgt
          exact absurd hgt (by norm_num)
        have hRlt := hOut m hmT hm0
        linarith
    · -- `m = n - e` with `n ∈ T`
      by_cases hmT : m ∈ T
      · have hne : m - teleE j ∉ T := by
          intro hb
          rw [teleInd_of_mem hmT, teleInd_of_mem hb] at hcoef
          have h1' : teleInd T (m + teleE j) = 1 := by
            have hsub : m + teleE j = n := by rw [← heq]; abel
            rw [hsub]; exact teleInd_of_mem hn
          rw [h1'] at hcoef
          norm_num at hcoef
        have h0 : m - teleE j ≠ 0 := by
          intro hz
          have hmm : m = teleE j := sub_eq_zero.mp hz
          rw [hmm, tele_norm_latE] at hgt
          linarith
        have hRlt := hOut _ hne h0
        have := tele_norm_ge_sub' m j
        linarith
      · have hm0 : m ≠ 0 := by
          intro hz
          rw [hz] at hgt
          simp only [nvec_zero, norm_zero] at hgt
          exact absurd hgt (by norm_num)
        have hRlt := hOut m hmT hm0
        linarith

/-! ## The one-coordinate telescope -/

private theorem tele_component (R : ℝ) (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (z : E3)
    (h1 : ∀ n ∈ T, n ≠ 0) (h2 : ∀ n ∈ T, ‖nvec n‖ ≤ R)
    (h4 : ∀ n : Fin 3 → ℤ, n ≠ 0 → ‖nvec n‖ ≤ R → n ∈ T) :
    |(∑ n ∈ T, Real.sin (2 * Real.pi * inner ℝ (nvec n) z)
        * (-2 * (nvec n).ofLp j / ‖nvec n‖ ^ 4))
      + Real.sin (2 * Real.pi * z.ofLp j)
        * (∑ n ∈ T, Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2)| ≤ 1150 := by
  by_cases hR : 1 ≤ R
  · have hB : (∑ n ∈ T, Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2)
        = ∑ n ∈ T, teleH n * Real.cos (telePhi z n) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [teleH, telePhi]; ring
    have hA : (∑ n ∈ T, Real.sin (2 * Real.pi * inner ℝ (nvec n) z)
        * (-2 * (nvec n).ofLp j / ‖nvec n‖ ^ 4))
        = ∑ n ∈ T, Real.sin (telePhi z n) * (-2 * (nvec n).ofLp j / ‖nvec n‖ ^ 4) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [telePhi]
    have hEr : |∑ n ∈ T, Real.sin (telePhi z n) * teleErr j n| ≤ 700 := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum fun n _ => ?_) (teleErr_sum j T h1)
      calc |Real.sin (telePhi z n) * teleErr j n|
          = |Real.sin (telePhi z n)| * |teleErr j n| := abs_mul _ _
        _ ≤ 1 * |teleErr j n| :=
            mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)
        _ = |teleErr j n| := one_mul _
    have hS1 : |teleSh1 T j z| ≤ 300 :=
      le_trans (abs_teleSh1_le T j z)
        (tele_shell_sum R (teleShell1 T j) hR (tele_shell1_lo R T j hR h2 h4)
          (tele_shell1_hi R T j h2 h4))
    have hS2 : |teleSh2 T j z| ≤ 600 := by
      refine le_trans (abs_teleSh2_le T j z) ?_
      have h300 : (∑ m ∈ teleShell2 T j, teleH m) ≤ 300 :=
        tele_shell_sum R (teleShell2 T j) hR (tele_shell2_lo R T j hR h1 h2 h4)
          (tele_shell2_hi R T j h2 h4)
      calc (∑ m ∈ teleShell2 T j, 2 * teleH m)
          = 2 * ∑ m ∈ teleShell2 T j, teleH m := by rw [Finset.mul_sum]
        _ ≤ 2 * 300 := mul_le_mul_of_nonneg_left h300 (by norm_num)
        _ = 600 := by norm_num
    have key : (∑ n ∈ T, Real.sin (telePhi z n) * (-2 * (nvec n).ofLp j / ‖nvec n‖ ^ 4))
        + Real.sin (2 * Real.pi * z.ofLp j) * (∑ n ∈ T, teleH n * Real.cos (telePhi z n))
        = (1 / 2) * (Real.cos (2 * Real.pi * z.ofLp j) * teleSh1 T j z)
          + (1 / 2) * (Real.sin (2 * Real.pi * z.ofLp j) * teleSh2 T j z)
          + (∑ n ∈ T, Real.sin (telePhi z n) * teleErr j n) := by
      have hsplit : (∑ n ∈ T, Real.sin (telePhi z n) * (-2 * (nvec n).ofLp j / ‖nvec n‖ ^ 4))
          = (1 / 2) * (∑ n ∈ T,
                Real.sin (telePhi z n) * (teleH (n + teleE j) - teleH (n - teleE j)))
            + ∑ n ∈ T, Real.sin (telePhi z n) * teleErr j n := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [tele_weight_eq j n]
        ring
      rw [hsplit, telescope_identity]
      ring
    rw [hB, hA, key]
    have hcos : |Real.cos (2 * Real.pi * z.ofLp j)| ≤ 1 := Real.abs_cos_le_one _
    have hsin : |Real.sin (2 * Real.pi * z.ofLp j)| ≤ 1 := Real.abs_sin_le_one _
    have h1' : |(1 / 2) * (Real.cos (2 * Real.pi * z.ofLp j) * teleSh1 T j z)|
        ≤ 1 / 2 * 300 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_mul]
      calc (1 / 2) * (|Real.cos (2 * Real.pi * z.ofLp j)| * |teleSh1 T j z|)
          ≤ (1 / 2) * (1 * 300) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact mul_le_mul hcos hS1 (abs_nonneg _) (by norm_num)
        _ = 1 / 2 * 300 := by ring
    have h2' : |(1 / 2) * (Real.sin (2 * Real.pi * z.ofLp j) * teleSh2 T j z)|
        ≤ 1 / 2 * 600 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_mul]
      calc (1 / 2) * (|Real.sin (2 * Real.pi * z.ofLp j)| * |teleSh2 T j z|)
          ≤ (1 / 2) * (1 * 600) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact mul_le_mul hsin hS2 (abs_nonneg _) (by norm_num)
        _ = 1 / 2 * 600 := by ring
    have hsum := abs_add_le
      ((1 / 2) * (Real.cos (2 * Real.pi * z.ofLp j) * teleSh1 T j z))
      ((1 / 2) * (Real.sin (2 * Real.pi * z.ofLp j) * teleSh2 T j z))
    have habs := abs_add_le
      ((1 / 2) * (Real.cos (2 * Real.pi * z.ofLp j) * teleSh1 T j z)
        + (1 / 2) * (Real.sin (2 * Real.pi * z.ofLp j) * teleSh2 T j z))
      (∑ n ∈ T, Real.sin (telePhi z n) * teleErr j n)
    linarith [habs, hsum, h1', h2', hEr]
  · -- `R < 1`: the ball is empty
    push_neg at hR
    have hTe : T = ∅ := by
      ext n
      simp only [Finset.notMem_empty, iff_false]
      intro hn
      have hn0 := h1 n hn
      have hle := h2 n hn
      have h1' := tele_one_le_norm hn0
      linarith
    subst hTe
    simp

/-! ## The target -/

theorem telescopeInner (R : ℝ) (T : Finset (Fin 3 → ℤ)) (z : E3)
    (h1 : ∀ n ∈ T, n ≠ 0) (h2 : ∀ n ∈ T, ‖nvec n‖ ≤ R)
    (h4 : ∀ n : Fin 3 → ℤ, n ≠ 0 → ‖nvec n‖ ≤ R → n ∈ T) :
    |(∑ n ∈ T, Real.sin (2 * Real.pi * inner ℝ (nvec n) z)
        * (inner ℝ (nvec n) (sigBullet z)) * (-2 / ‖nvec n‖ ^ 4))
      + gam z * (∑ n ∈ T, Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2)| ≤ 1000 := by
  -- coordinate expansion of `gam` and of the inner product
  have hgam : gam z = ∑ j : Fin 3, (sigBullet z).ofLp j * Real.sin (2 * Real.pi * z.ofLp j) := by
    rw [gam, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sinVec_apply, RCLike.inner_apply]
    simp
    ring
  have hinner : ∀ n : Fin 3 → ℤ,
      inner ℝ (nvec n) (sigBullet z)
        = ∑ j : Fin 3, (nvec n).ofLp j * (sigBullet z).ofLp j := by
    intro n
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [RCLike.inner_apply]
    simp
    ring
  -- rewrite the target as `Σ_j β_j V_j`
  have hrewrite : (∑ n ∈ T, Real.sin (2 * Real.pi * inner ℝ (nvec n) z)
        * (inner ℝ (nvec n) (sigBullet z)) * (-2 / ‖nvec n‖ ^ 4))
      + gam z * (∑ n ∈ T, Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2)
      = ∑ j : Fin 3, (sigBullet z).ofLp j
          * ((∑ n ∈ T, Real.sin (2 * Real.pi * inner ℝ (nvec n) z)
              * (-2 * (nvec n).ofLp j / ‖nvec n‖ ^ 4))
            + Real.sin (2 * Real.pi * z.ofLp j)
              * (∑ n ∈ T, Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2)) := by
    have hstep : ∀ n : Fin 3 → ℤ,
        Real.sin (2 * Real.pi * inner ℝ (nvec n) z) * (inner ℝ (nvec n) (sigBullet z))
            * (-2 / ‖nvec n‖ ^ 4)
          = ∑ j : Fin 3, (sigBullet z).ofLp j
              * (Real.sin (2 * Real.pi * inner ℝ (nvec n) z)
                  * (-2 * (nvec n).ofLp j / ‖nvec n‖ ^ 4)) := by
      intro n
      rw [hinner n]
      rw [show Real.sin (2 * Real.pi * inner ℝ (nvec n) z)
            * (∑ j : Fin 3, (nvec n).ofLp j * (sigBullet z).ofLp j) * (-2 / ‖nvec n‖ ^ 4)
          = Real.sin (2 * Real.pi * inner ℝ (nvec n) z)
            * ((∑ j : Fin 3, (nvec n).ofLp j * (sigBullet z).ofLp j) * (-2 / ‖nvec n‖ ^ 4))
          by ring]
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have h1 : (∑ n ∈ T, Real.sin (2 * Real.pi * inner ℝ (nvec n) z)
        * (inner ℝ (nvec n) (sigBullet z)) * (-2 / ‖nvec n‖ ^ 4))
        = ∑ j : Fin 3, (sigBullet z).ofLp j
            * (∑ n ∈ T, Real.sin (2 * Real.pi * inner ℝ (nvec n) z)
                * (-2 * (nvec n).ofLp j / ‖nvec n‖ ^ 4)) := by
      calc (∑ n ∈ T, Real.sin (2 * Real.pi * inner ℝ (nvec n) z)
              * (inner ℝ (nvec n) (sigBullet z)) * (-2 / ‖nvec n‖ ^ 4))
          = ∑ n ∈ T, ∑ j : Fin 3, (sigBullet z).ofLp j
              * (Real.sin (2 * Real.pi * inner ℝ (nvec n) z)
                  * (-2 * (nvec n).ofLp j / ‖nvec n‖ ^ 4)) :=
            Finset.sum_congr rfl fun n _ => hstep n
        _ = ∑ j : Fin 3, ∑ n ∈ T, (sigBullet z).ofLp j
              * (Real.sin (2 * Real.pi * inner ℝ (nvec n) z)
                  * (-2 * (nvec n).ofLp j / ‖nvec n‖ ^ 4)) := Finset.sum_comm
        _ = ∑ j : Fin 3, (sigBullet z).ofLp j
              * (∑ n ∈ T, Real.sin (2 * Real.pi * inner ℝ (nvec n) z)
                  * (-2 * (nvec n).ofLp j / ‖nvec n‖ ^ 4)) :=
            Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
    have h2 : gam z * (∑ n ∈ T, Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2)
        = ∑ j : Fin 3, (sigBullet z).ofLp j
            * (Real.sin (2 * Real.pi * z.ofLp j)
                * (∑ n ∈ T, Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2)) := by
      rw [hgam, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h1, h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hrewrite]
  have hb : ∀ j : Fin 3, |(sigBullet z).ofLp j| ≤ 1 / 4 := tele_sigBullet_coord z
  have hterm : ∀ j : Fin 3,
      |(sigBullet z).ofLp j
        * ((∑ n ∈ T, Real.sin (2 * Real.pi * inner ℝ (nvec n) z)
            * (-2 * (nvec n).ofLp j / ‖nvec n‖ ^ 4))
          + Real.sin (2 * Real.pi * z.ofLp j)
            * (∑ n ∈ T, Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2))|
        ≤ (1 / 4) * 1150 := by
    intro j
    rw [abs_mul]
    refine mul_le_mul (hb j) (tele_component R T j z h1 h2 h4) (abs_nonneg _) (by norm_num)
  calc |∑ j : Fin 3, (sigBullet z).ofLp j
        * ((∑ n ∈ T, Real.sin (2 * Real.pi * inner ℝ (nvec n) z)
            * (-2 * (nvec n).ofLp j / ‖nvec n‖ ^ 4))
          + Real.sin (2 * Real.pi * z.ofLp j)
            * (∑ n ∈ T, Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2))|
      ≤ ∑ j : Fin 3, |(sigBullet z).ofLp j
        * ((∑ n ∈ T, Real.sin (2 * Real.pi * inner ℝ (nvec n) z)
            * (-2 * (nvec n).ofLp j / ‖nvec n‖ ^ 4))
          + Real.sin (2 * Real.pi * z.ofLp j)
            * (∑ n ∈ T, Real.cos (2 * Real.pi * inner ℝ (nvec n) z) / ‖nvec n‖ ^ 2))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3, (1 / 4) * 1150 := Finset.sum_le_sum fun j _ => hterm j
    _ ≤ 1000 := by norm_num

end Work.BoseRowsL.LatticeCoulomb
