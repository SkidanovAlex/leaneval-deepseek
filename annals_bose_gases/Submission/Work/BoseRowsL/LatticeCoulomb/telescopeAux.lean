import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseRowsL.LatticeCoulomb.kernelDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.telescopeAux`

Vocabulary for the **telescoping proof** of
`Work.BoseRowsL.LatticeCoulomb.telescopeInner`.

## The identity in one line

The telescoping replaces the singular weight `-2 n_j/‖nvec n‖⁴` by the *symmetric difference*
of the Coulomb kernel `teleH n = ‖nvec n‖⁻²`:

`-2 n_j/‖nvec n‖⁴ = (1/2)(teleH (n+e_j) − teleH (n−e_j)) + teleErr j n`,  `|teleErr j n| ≲ ‖n‖⁻⁵`

and the summation by parts
`Σ_{n∈T} u(n)(teleH(n+e_j) − teleH(n−e_j)) = Σ_m teleH(m)(u(m−e_j) − u(m+e_j))`
(with `u = 1_T·sin(telePhi ·)`) converts the conditionally convergent lattice sum into the
**shell** sums `teleSh1`, `teleSh2`, supported on the `O(1)`-volume annulus where the two
indicators `1_T(m−e_j)`, `1_T(m+e_j)` differ.

## Contents

* the vocabulary (`teleE`, `teleH`, `telePhi`, `teleErr`, `teleInd`, `teleCarrier`,
  `teleSh1`, `teleSh2`, `teleShell1`, `teleShell2`) and its elementary API;
* `sum_shift_add` / `sum_shift_sub` — the finite reindexing behind the summation by parts;
* `sin_telePhi_add/sub`, `cos_telePhi_add/sub` — the angle-addition for the shifted phase;
* `abs_teleSh1_le`, `abs_teleSh2_le` — the support (shell) reduction of the two shell sums;
* `telescope_identity` — the telescoping identity itself.

The numerical estimates live in the children `teleErrBound`, `teleErrSmall`, `teleFifthSum`,
`teleShellSum`, `teleSigBullet`; the assembly is `telescopeInner`.
-/

noncomputable section

open scoped Real BigOperators Topology
open MeasureTheory Metric

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false

/-! ## The lattice basis vector and its shifts -/

/-- The `j`-th lattice basis vector `e_j`. -/
def teleE (j : Fin 3) : Fin 3 → ℤ := fun i => if i = j then 1 else 0

@[simp] lemma teleE_self (j : Fin 3) : teleE j j = 1 := by simp [teleE]

lemma teleE_ne {i j : Fin 3} (h : i ≠ j) : teleE j i = 0 := by simp [teleE, h]

lemma tele_nvec_add (n m : Fin 3 → ℤ) : nvec (n + m) = nvec n + nvec m := by
  ext i
  simp [nvec, PiLp.toLp_apply]

lemma tele_nvec_sub (n m : Fin 3 → ℤ) : nvec (n - m) = nvec n - nvec m := by
  ext i
  simp [nvec, PiLp.toLp_apply]

lemma tele_nvec_neg (n : Fin 3 → ℤ) : nvec (-n) = -nvec n := by
  ext i
  simp [nvec, PiLp.toLp_apply]

lemma tele_norm_nvec_neg (n : Fin 3 → ℤ) : ‖nvec (-n)‖ = ‖nvec n‖ := by
  rw [tele_nvec_neg, norm_neg]

lemma tele_nvec_teleE_self (j : Fin 3) : (nvec (teleE j)).ofLp j = 1 := by
  rw [nvec_apply, teleE_self]; norm_num

lemma tele_nvec_teleE_ne {i j : Fin 3} (h : i ≠ j) : (nvec (teleE j)).ofLp i = 0 := by
  rw [nvec_apply, teleE_ne h]; norm_num

/-- The coordinate form of the inner product of a lattice vector with a real vector. -/
lemma tele_inner_nvec_eq (n : Fin 3 → ℤ) (z : E3) :
    inner ℝ (nvec n) z = ∑ i : Fin 3, z.ofLp i * (n i : ℝ) := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [nvec_apply, RCLike.inner_apply]
    simp

/-- The sum of the coordinates of `e_j` against `z`. -/
lemma tele_sum_latE (j : Fin 3) (z : E3) :
    (∑ i : Fin 3, z.ofLp i * ((teleE j i : ℤ) : ℝ)) = z.ofLp j := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [teleE_ne hi]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

lemma tele_inner_add_E (n : Fin 3 → ℤ) (j : Fin 3) (z : E3) :
    inner ℝ (nvec (n + teleE j)) z = inner ℝ (nvec n) z + z.ofLp j := by
  rw [tele_inner_nvec_eq, tele_inner_nvec_eq]
  have hsplit : (∑ i : Fin 3, z.ofLp i * (((n + teleE j) i : ℤ) : ℝ))
      = ∑ i : Fin 3,
          (z.ofLp i * ((n i : ℤ) : ℝ) + z.ofLp i * ((teleE j i : ℤ) : ℝ)) :=
    Finset.sum_congr rfl fun i _ => by
      simp only [Pi.add_apply, Int.cast_add]
      ring
  rw [hsplit, Finset.sum_add_distrib, tele_sum_latE]

lemma tele_inner_sub_E (n : Fin 3 → ℤ) (j : Fin 3) (z : E3) :
    inner ℝ (nvec (n - teleE j)) z = inner ℝ (nvec n) z - z.ofLp j := by
  have h : n - teleE j = n + (-(teleE j)) := by abel
  rw [h, tele_inner_nvec_eq, tele_inner_nvec_eq]
  have hsplit : (∑ i : Fin 3, z.ofLp i * (((n + -(teleE j)) i : ℤ) : ℝ))
      = ∑ i : Fin 3,
          (z.ofLp i * ((n i : ℤ) : ℝ) + z.ofLp i * (((-(teleE j)) i : ℤ) : ℝ)) :=
    Finset.sum_congr rfl fun i _ => by
      simp only [Pi.add_apply, Int.cast_add]
      ring
  have hneg : (∑ i : Fin 3, z.ofLp i * (((-(teleE j)) i : ℤ) : ℝ)) = -z.ofLp j := by
    have h1 : ∀ i : Fin 3, z.ofLp i * (((-(teleE j)) i : ℤ) : ℝ)
        = -(z.ofLp i * ((teleE j i : ℤ) : ℝ)) := by
      intro i
      by_cases hi : i = j
      · subst hi; simp
      · simp [teleE_ne hi]
    calc (∑ i : Fin 3, z.ofLp i * (((-(teleE j)) i : ℤ) : ℝ))
        = ∑ i : Fin 3, -(z.ofLp i * ((teleE j i : ℤ) : ℝ)) :=
          Finset.sum_congr rfl fun i _ => h1 i
      _ = -(∑ i : Fin 3, z.ofLp i * ((teleE j i : ℤ) : ℝ)) :=
          Finset.sum_neg_distrib (s := Finset.univ)
            (f := fun i : Fin 3 => z.ofLp i * ((teleE j i : ℤ) : ℝ))
      _ = -z.ofLp j := by rw [tele_sum_latE]
  rw [hsplit, Finset.sum_add_distrib, hneg]
  ring

/-! ## The kernel, the phase and the telescoping error -/

/-- `teleH n = ‖nvec n‖⁻²`; at the origin Lean's convention `1/0 = 0` gives `teleH 0 = 0`. -/
def teleH (n : Fin 3 → ℤ) : ℝ := 1 / ‖nvec n‖ ^ 2

/-- `telePhi z n = 2π⟪nvec n, z⟫`. -/
def telePhi (z : E3) (n : Fin 3 → ℤ) : ℝ := 2 * Real.pi * inner ℝ (nvec n) z

lemma telePhi_add (z : E3) (n : Fin 3 → ℤ) (j : Fin 3) :
    telePhi z (n + teleE j) = telePhi z n + 2 * Real.pi * z.ofLp j := by
  rw [telePhi, telePhi, tele_inner_add_E]; ring

lemma telePhi_sub (z : E3) (n : Fin 3 → ℤ) (j : Fin 3) :
    telePhi z (n - teleE j) = telePhi z n - 2 * Real.pi * z.ofLp j := by
  rw [telePhi, telePhi, tele_inner_sub_E]; ring

lemma telePhi_neg (z : E3) (n : Fin 3 → ℤ) : telePhi z (-n) = -telePhi z n := by
  rw [telePhi, telePhi, tele_nvec_neg, inner_neg_left]; ring

/-- The telescoping error: the difference between the singular weight `-2 n_j/‖n‖⁴` and the
symmetric difference `(1/2)(teleH (n+e_j) - teleH (n-e_j))` of the Coulomb kernel. -/
def teleErr (j : Fin 3) (n : Fin 3 → ℤ) : ℝ :=
  -2 * (nvec n).ofLp j / ‖nvec n‖ ^ 4 - (1 / 2) * (teleH (n + teleE j) - teleH (n - teleE j))

/-- The telescoping identity at the level of a single lattice point. -/
lemma tele_weight_eq (j : Fin 3) (n : Fin 3 → ℤ) :
    -2 * (nvec n).ofLp j / ‖nvec n‖ ^ 4
      = (1 / 2) * (teleH (n + teleE j) - teleH (n - teleE j)) + teleErr j n := by
  rw [teleErr]; ring

lemma teleH_nonneg (n : Fin 3 → ℤ) : 0 ≤ teleH n := by
  rw [teleH]; positivity

/-- The trigonometric identities for the shifted phase. -/
lemma sin_telePhi_add (z : E3) (n : Fin 3 → ℤ) (j : Fin 3) :
    Real.sin (telePhi z (n + teleE j))
      = Real.sin (telePhi z n) * Real.cos (2 * Real.pi * z.ofLp j)
        + Real.cos (telePhi z n) * Real.sin (2 * Real.pi * z.ofLp j) := by
  rw [telePhi_add, Real.sin_add]

lemma sin_telePhi_sub (z : E3) (n : Fin 3 → ℤ) (j : Fin 3) :
    Real.sin (telePhi z (n - teleE j))
      = Real.sin (telePhi z n) * Real.cos (2 * Real.pi * z.ofLp j)
        - Real.cos (telePhi z n) * Real.sin (2 * Real.pi * z.ofLp j) := by
  rw [telePhi_sub, Real.sin_sub]

lemma cos_telePhi_add (z : E3) (n : Fin 3 → ℤ) (j : Fin 3) :
    Real.cos (telePhi z (n + teleE j))
      = Real.cos (telePhi z n) * Real.cos (2 * Real.pi * z.ofLp j)
        - Real.sin (telePhi z n) * Real.sin (2 * Real.pi * z.ofLp j) := by
  rw [telePhi_add, Real.cos_add]

lemma cos_telePhi_sub (z : E3) (n : Fin 3 → ℤ) (j : Fin 3) :
    Real.cos (telePhi z (n - teleE j))
      = Real.cos (telePhi z n) * Real.cos (2 * Real.pi * z.ofLp j)
        + Real.sin (telePhi z n) * Real.sin (2 * Real.pi * z.ofLp j) := by
  rw [telePhi_sub, Real.cos_sub]

/-! ## The indicator, the carrier and the shell sums -/

/-- The indicator function of the finite set `T`, as a real-valued function. -/
def teleInd (T : Finset (Fin 3 → ℤ)) (m : Fin 3 → ℤ) : ℝ := if m ∈ T then 1 else 0

lemma teleInd_nonneg (T : Finset (Fin 3 → ℤ)) (m : Fin 3 → ℤ) : 0 ≤ teleInd T m := by
  unfold teleInd; split <;> norm_num

lemma teleInd_le_one (T : Finset (Fin 3 → ℤ)) (m : Fin 3 → ℤ) : teleInd T m ≤ 1 := by
  unfold teleInd; split <;> norm_num

lemma teleInd_of_mem {T : Finset (Fin 3 → ℤ)} {m : Fin 3 → ℤ} (h : m ∈ T) :
    teleInd T m = 1 := by simp [teleInd, h]

lemma teleInd_of_notMem {T : Finset (Fin 3 → ℤ)} {m : Fin 3 → ℤ} (h : m ∉ T) :
    teleInd T m = 0 := by simp [teleInd, h]

/-- `teleCarrier T j = T ∪ (T + e_j) ∪ (T − e_j)`: the carrier of the shell sums. -/
def teleCarrier (T : Finset (Fin 3 → ℤ)) (j : Fin 3) : Finset (Fin 3 → ℤ) :=
  T ∪ T.image (fun n => n + teleE j) ∪ T.image (fun n => n - teleE j)

lemma mem_teleCarrier_self {T : Finset (Fin 3 → ℤ)} {j : Fin 3} {n : Fin 3 → ℤ}
    (h : n ∈ T) : n ∈ teleCarrier T j := by
  simp only [teleCarrier, Finset.mem_union]
  exact Or.inl (Or.inl h)

lemma mem_teleCarrier_add {T : Finset (Fin 3 → ℤ)} {j : Fin 3} {n : Fin 3 → ℤ}
    (h : n ∈ T) : n + teleE j ∈ teleCarrier T j := by
  simp only [teleCarrier, Finset.mem_union, Finset.mem_image]
  exact Or.inl (Or.inr ⟨n, h, rfl⟩)

lemma mem_teleCarrier_sub {T : Finset (Fin 3 → ℤ)} {j : Fin 3} {n : Fin 3 → ℤ}
    (h : n ∈ T) : n - teleE j ∈ teleCarrier T j := by
  simp only [teleCarrier, Finset.mem_union, Finset.mem_image]
  exact Or.inr ⟨n, h, rfl⟩

lemma tele_carrier_filter_sub (T : Finset (Fin 3 → ℤ)) (j : Fin 3) :
    (teleCarrier T j).filter (fun m => m - teleE j ∈ T)
      = T.image (fun n => n + teleE j) := by
  ext m
  constructor
  · intro hm
    have hmem : m - teleE j ∈ T := (Finset.mem_filter.mp hm).2
    exact Finset.mem_image.mpr ⟨m - teleE j, hmem, by abel⟩
  · intro hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    exact Finset.mem_filter.mpr ⟨mem_teleCarrier_add hn, by simpa using hn⟩

lemma tele_carrier_filter_add (T : Finset (Fin 3 → ℤ)) (j : Fin 3) :
    (teleCarrier T j).filter (fun m => m + teleE j ∈ T)
      = T.image (fun n => n - teleE j) := by
  ext m
  constructor
  · intro hm
    have hmem : m + teleE j ∈ T := (Finset.mem_filter.mp hm).2
    exact Finset.mem_image.mpr ⟨m + teleE j, hmem, by abel⟩
  · intro hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    exact Finset.mem_filter.mpr ⟨mem_teleCarrier_sub hn, by simpa using hn⟩

/-- The summation by parts (`+` shift): reindexing the sum over `T + e_j`. -/
lemma sum_shift_add (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (f : (Fin 3 → ℤ) → ℝ) :
    (∑ n ∈ T, f (n + teleE j))
      = ∑ m ∈ teleCarrier T j, teleInd T (m - teleE j) * f m := by
  rw [← Finset.sum_image (s := T) (g := fun n : Fin 3 → ℤ => n + teleE j) (f := f)
    (fun a _ b _ hab => add_right_cancel hab)]
  rw [← tele_carrier_filter_sub T j, Finset.sum_filter]
  exact Finset.sum_congr rfl fun m _ => by
    by_cases h : m - teleE j ∈ T
    · simp [teleInd, h]
    · simp [teleInd, h]

/-- The summation by parts (`−` shift): reindexing the sum over `T - e_j`. -/
lemma sum_shift_sub (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (f : (Fin 3 → ℤ) → ℝ) :
    (∑ n ∈ T, f (n - teleE j))
      = ∑ m ∈ teleCarrier T j, teleInd T (m + teleE j) * f m := by
  rw [← Finset.sum_image (s := T) (g := fun n : Fin 3 → ℤ => n - teleE j) (f := f)
    (fun a _ b _ hab => by
      have h : a + (-(teleE j)) = b + (-(teleE j)) := by simpa [sub_eq_add_neg] using hab
      exact add_right_cancel h)]
  rw [← tele_carrier_filter_add T j, Finset.sum_filter]
  exact Finset.sum_congr rfl fun m _ => by
    by_cases h : m + teleE j ∈ T
    · simp [teleInd, h]
    · simp [teleInd, h]

/-- The `sin`-weighted shell sum. -/
def teleSh1 (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (z : E3) : ℝ :=
  ∑ m ∈ teleCarrier T j,
    teleH m * Real.sin (telePhi z m) * (teleInd T (m - teleE j) - teleInd T (m + teleE j))

/-- The `cos`-weighted shell sum. -/
def teleSh2 (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (z : E3) : ℝ :=
  ∑ m ∈ teleCarrier T j,
    teleH m * Real.cos (telePhi z m)
      * (2 * teleInd T m - teleInd T (m - teleE j) - teleInd T (m + teleE j))

/-- The support of the first shell sum. -/
def teleShell1 (T : Finset (Fin 3 → ℤ)) (j : Fin 3) : Finset (Fin 3 → ℤ) :=
  (teleCarrier T j).filter (fun m => teleInd T (m - teleE j) ≠ teleInd T (m + teleE j))

/-- The support of the second shell sum. -/
def teleShell2 (T : Finset (Fin 3 → ℤ)) (j : Fin 3) : Finset (Fin 3 → ℤ) :=
  (teleCarrier T j).filter
    (fun m => 2 * teleInd T m - teleInd T (m - teleE j) - teleInd T (m + teleE j) ≠ 0)

lemma teleShell1_subset (T : Finset (Fin 3 → ℤ)) (j : Fin 3) :
    teleShell1 T j ⊆ teleCarrier T j := Finset.filter_subset _ _

lemma teleShell2_subset (T : Finset (Fin 3 → ℤ)) (j : Fin 3) :
    teleShell2 T j ⊆ teleCarrier T j := Finset.filter_subset _ _

lemma teleSh1_eq_shell (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (z : E3) :
    teleSh1 T j z
      = ∑ m ∈ teleShell1 T j,
          teleH m * Real.sin (telePhi z m)
            * (teleInd T (m - teleE j) - teleInd T (m + teleE j)) := by
  rw [teleSh1, teleShell1, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases h : teleInd T (m - teleE j) ≠ teleInd T (m + teleE j)
  · rw [if_pos h]
  · rw [if_neg h]
    have heq : teleInd T (m - teleE j) - teleInd T (m + teleE j) = 0 := by
      have h' : teleInd T (m - teleE j) = teleInd T (m + teleE j) := not_ne_iff.mp h
      rw [h', sub_self]
    rw [heq]; ring

/-- The first shell sum is dominated by the `teleH`-weight of its support. -/
lemma abs_teleSh1_le (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (z : E3) :
    |teleSh1 T j z| ≤ ∑ m ∈ teleShell1 T j, teleH m := by
  rw [teleSh1_eq_shell]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun m hm => ?_
  have h1 : |teleH m * Real.sin (telePhi z m)
      * (teleInd T (m - teleE j) - teleInd T (m + teleE j))| ≤ teleH m := by
    have hsin : |Real.sin (telePhi z m)| ≤ 1 := Real.abs_sin_le_one _
    have hcoef : |teleInd T (m - teleE j) - teleInd T (m + teleE j)| ≤ 1 := by
      have ha := teleInd_nonneg T (m - teleE j)
      have hb := teleInd_nonneg T (m + teleE j)
      have hc := teleInd_le_one T (m - teleE j)
      have hd := teleInd_le_one T (m + teleE j)
      rw [abs_le]
      constructor <;> linarith
    have hH := teleH_nonneg m
    rw [abs_mul, abs_mul, abs_of_nonneg hH]
    calc teleH m * |Real.sin (telePhi z m)|
          * |teleInd T (m - teleE j) - teleInd T (m + teleE j)|
        ≤ teleH m * 1 * 1 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hsin hH) hcoef (abs_nonneg _) ?_
          positivity
      _ = teleH m := by ring
  exact h1

lemma teleSh2_eq_shell (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (z : E3) :
    teleSh2 T j z
      = ∑ m ∈ teleShell2 T j,
          teleH m * Real.cos (telePhi z m)
            * (2 * teleInd T m - teleInd T (m - teleE j) - teleInd T (m + teleE j)) := by
  rw [teleSh2, teleShell2, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases h : 2 * teleInd T m - teleInd T (m - teleE j) - teleInd T (m + teleE j) ≠ 0
  · rw [if_pos h]
  · rw [if_neg h]
    rw [not_ne_iff.mp h]; ring

/-- The second shell sum is dominated by twice the `teleH`-weight of its support. -/
lemma abs_teleSh2_le (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (z : E3) :
    |teleSh2 T j z| ≤ ∑ m ∈ teleShell2 T j, 2 * teleH m := by
  rw [teleSh2_eq_shell]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun m hm => ?_
  have h1 : |teleH m * Real.cos (telePhi z m)
      * (2 * teleInd T m - teleInd T (m - teleE j) - teleInd T (m + teleE j))|
      ≤ 2 * teleH m := by
    have hcos : |Real.cos (telePhi z m)| ≤ 1 := Real.abs_cos_le_one _
    have hcoef : |2 * teleInd T m - teleInd T (m - teleE j) - teleInd T (m + teleE j)| ≤ 2 := by
      have ha := teleInd_nonneg T m
      have hb := teleInd_nonneg T (m - teleE j)
      have hc := teleInd_nonneg T (m + teleE j)
      have hd := teleInd_le_one T m
      have he := teleInd_le_one T (m - teleE j)
      have hf := teleInd_le_one T (m + teleE j)
      rw [abs_le]
      constructor <;> linarith
    have hH := teleH_nonneg m
    rw [abs_mul, abs_mul, abs_of_nonneg hH]
    calc teleH m * |Real.cos (telePhi z m)|
          * |2 * teleInd T m - teleInd T (m - teleE j) - teleInd T (m + teleE j)|
        ≤ teleH m * 1 * 2 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hcos hH) hcoef (abs_nonneg _) ?_
          positivity
      _ = 2 * teleH m := by ring
  exact h1

/-- The `cos`-weighted indicator sum over the carrier, in terms of `teleSh2` and the
`T`-restricted sum. -/
lemma tele_ind_add_eq (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (z : E3) :
    (∑ m ∈ teleCarrier T j,
        teleH m * Real.cos (telePhi z m)
          * (teleInd T (m - teleE j) + teleInd T (m + teleE j)))
      = 2 * (∑ n ∈ T, teleH n * Real.cos (telePhi z n)) - teleSh2 T j z := by
  have hone : ∀ m : Fin 3 → ℤ,
      teleH m * Real.cos (telePhi z m)
          * (teleInd T (m - teleE j) + teleInd T (m + teleE j))
        = 2 * (teleH m * Real.cos (telePhi z m) * teleInd T m)
          - teleH m * Real.cos (telePhi z m)
              * (2 * teleInd T m - teleInd T (m - teleE j) - teleInd T (m + teleE j)) := by
    intro m; ring
  have htwo : (∑ m ∈ teleCarrier T j, teleH m * Real.cos (telePhi z m) * teleInd T m)
      = ∑ n ∈ T, teleH n * Real.cos (telePhi z n) := by
    have hsub : T ⊆ teleCarrier T j := fun n hn => mem_teleCarrier_self hn
    refine (Finset.sum_subset hsub ?_).symm.trans ?_
    · intro m _ hmT
      rw [teleInd_of_notMem hmT]; ring
    · exact Finset.sum_congr rfl fun n hn => by rw [teleInd_of_mem hn]; ring
  have hcongr : (∑ m ∈ teleCarrier T j, 2 * (teleH m * Real.cos (telePhi z m) * teleInd T m))
      = 2 * ∑ m ∈ teleCarrier T j, teleH m * Real.cos (telePhi z m) * teleInd T m :=
    (Finset.mul_sum _ _ (2 : ℝ)).symm
  rw [Finset.sum_congr rfl fun m _ => hone m, Finset.sum_sub_distrib, hcongr, htwo, teleSh2]

/-- **The telescoping identity.**  The symmetric difference of the Coulomb kernel summed
against `sin (telePhi z ·)` equals the two shell sums, weighted by `cos` and `sin` of
`2π z_j`, plus the `2 B_T` term that cancels against the target's `sin (2π z_j) B_T`. -/
lemma telescope_identity (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (z : E3) :
    (∑ n ∈ T, Real.sin (telePhi z n) * (teleH (n + teleE j) - teleH (n - teleE j)))
      = Real.cos (2 * Real.pi * z.ofLp j) * teleSh1 T j z
        - Real.sin (2 * Real.pi * z.ofLp j)
          * (2 * (∑ n ∈ T, teleH n * Real.cos (telePhi z n)) - teleSh2 T j z) := by
  set c : ℝ := Real.cos (2 * Real.pi * z.ofLp j) with hc
  set s : ℝ := Real.sin (2 * Real.pi * z.ofLp j) with hs
  have h1 : (∑ n ∈ T, Real.sin (telePhi z n) * (teleH (n + teleE j) - teleH (n - teleE j)))
      = (∑ n ∈ T, Real.sin (telePhi z n) * teleH (n + teleE j))
        - (∑ n ∈ T, Real.sin (telePhi z n) * teleH (n - teleE j)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have h2a : (∑ n ∈ T, Real.sin (telePhi z n) * teleH (n + teleE j))
      = ∑ m ∈ teleCarrier T j,
          teleInd T (m - teleE j) * (Real.sin (telePhi z (m - teleE j)) * teleH m) := by
    refine Eq.trans ?_ (sum_shift_add T j
      (fun m => Real.sin (telePhi z (m - teleE j)) * teleH m))
    exact Finset.sum_congr rfl fun n _ => by rw [add_sub_cancel_right]
  have h2b : (∑ n ∈ T, Real.sin (telePhi z n) * teleH (n - teleE j))
      = ∑ m ∈ teleCarrier T j,
          teleInd T (m + teleE j) * (Real.sin (telePhi z (m + teleE j)) * teleH m) := by
    refine Eq.trans ?_ (sum_shift_sub T j
      (fun m => Real.sin (telePhi z (m + teleE j)) * teleH m))
    exact Finset.sum_congr rfl fun n _ => by rw [sub_add_cancel]
  have h3 : (∑ m ∈ teleCarrier T j,
        teleInd T (m - teleE j) * (Real.sin (telePhi z (m - teleE j)) * teleH m))
      - (∑ m ∈ teleCarrier T j,
        teleInd T (m + teleE j) * (Real.sin (telePhi z (m + teleE j)) * teleH m))
      = c * (∑ m ∈ teleCarrier T j,
            teleH m * Real.sin (telePhi z m)
              * (teleInd T (m - teleE j) - teleInd T (m + teleE j)))
        - s * (∑ m ∈ teleCarrier T j,
            teleH m * Real.cos (telePhi z m)
              * (teleInd T (m - teleE j) + teleInd T (m + teleE j))) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [sin_telePhi_sub, sin_telePhi_add]
    simp only [hc, hs]
    ring
  rw [h1, h2a, h2b, h3, tele_ind_add_eq, teleSh1]

end Work.BoseRowsL.LatticeCoulomb
