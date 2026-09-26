import Mathlib

/-!
# The connected direction slices of the local complement of a union of equal discs

Analytic core of `frontierComponentLocallyArc`: the set of directions from which a point of the
local complement is reachable is an arc of the direction circle.  This file contains the two
reusable ingredients:

* `re_star_exp_I_mul` : `⟪e^{iθ}, v⟫ = ‖v‖ cos (arg v - θ)` (the real inner product of the unit
  direction `e^{iθ}` with `v`), stated after rotating the configuration so that the free direction
  is `1`;
* `exists_int_near_two_pi`, `cos_ge_iff` : `cos x ≥ cos β` (for `0 ≤ β ≤ π`) exactly when `x` is
  within `β` of a multiple of `2π`.
-/

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

/-- **The real inner product of the unit direction `e^{iθ}` with a vector `v`.** -/
theorem re_star_exp_I_mul (θ : ℝ) (v : ℂ) :
    (star (Complex.exp ((θ : ℂ) * Complex.I)) * v).re
      = ‖v‖ * Real.cos (Complex.arg v - θ) := by
  have h1 : star (Complex.exp ((θ : ℂ) * Complex.I))
      = Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
    show starRingEnd ℂ (Complex.exp ((θ : ℂ) * Complex.I)) = _
    rw [← Complex.exp_conj]
    congr 1
    show starRingEnd ℂ ((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have h2 : ∀ x y : ℝ, Complex.exp ((x : ℂ) * Complex.I) * Complex.exp ((y : ℂ) * Complex.I)
      = Complex.exp (((x + y : ℝ) : ℂ) * Complex.I) := by
    intro x y
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have key : ∀ w : ℂ, (Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * w).re
      = ‖w‖ * Real.cos (Complex.arg w - θ) := by
    intro w
    have hw : w = ((‖w‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg w : ℂ) * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I w).symm
    conv_lhs => rw [hw]
    rw [show Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)
          * (((‖w‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg w : ℂ) * Complex.I))
        = ((‖w‖ : ℝ) : ℂ) * (Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)
            * Complex.exp ((Complex.arg w : ℂ) * Complex.I)) from by ring,
      h2 (-θ) (Complex.arg w),
      show ((-θ) + Complex.arg w : ℝ) = Complex.arg w - θ from by ring,
      Complex.exp_ofReal_mul_I]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_self, add_zero]
  rw [h1]
  exact key v

/-- **Nearest multiple of `2π`.** -/
theorem exists_int_near_two_pi (x : ℝ) : ∃ k : ℤ, |x - 2 * (k : ℝ) * Real.pi| ≤ Real.pi := by
  refine ⟨⌊x / (2 * Real.pi) + 1 / 2⌋, ?_⟩
  set m : ℝ := ((⌊x / (2 * Real.pi) + 1 / 2⌋ : ℤ) : ℝ) with hm
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 : m ≤ x / (2 * Real.pi) + 1 / 2 := by rw [hm]; exact Int.floor_le _
  have h2 : x / (2 * Real.pi) + 1 / 2 < m + 1 := by
    rw [hm]; exact Int.lt_floor_add_one _
  have hlow : 2 * m * Real.pi - Real.pi ≤ x := by
    have h : m - 1 / 2 ≤ x / (2 * Real.pi) := by linarith
    have := (le_div_iff₀ h2π).mp h
    linarith
  have hhigh : x ≤ 2 * m * Real.pi + Real.pi := by
    have h : x / (2 * Real.pi) < m + 1 / 2 := by linarith
    have := (div_lt_iff₀ h2π).mp h
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- `cos |x| = cos x`. -/
theorem cos_abs (x : ℝ) : Real.cos |x| = Real.cos x := by
  rcases abs_cases x with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]
  · rw [h, Real.cos_neg]

/-- **The `cos`-threshold set is the set of points within `β` of a multiple of `2π`.** -/
theorem cos_ge_iff {β x : ℝ} (hβ0 : 0 ≤ β) (hβπ : β ≤ Real.pi) :
    Real.cos β ≤ Real.cos x ↔ ∃ k : ℤ, |x - 2 * (k : ℝ) * Real.pi| ≤ β := by
  have hβmem : β ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hβ0, hβπ⟩
  have hper : ∀ (k : ℤ) (y : ℝ), Real.cos (y + (-(k : ℤ) : ℤ) * (2 * Real.pi))
      = Real.cos y := fun k y => Real.cos_periodic.int_mul (-k) y
  have hcosk : ∀ (k : ℤ) (y : ℝ), Real.cos (y - 2 * (k : ℝ) * Real.pi) = Real.cos y := by
    intro k y
    rw [show y - 2 * (k : ℝ) * Real.pi = y + (-(k : ℤ) : ℤ) * (2 * Real.pi) by
      push_cast; ring]
    exact hper k y
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_int_near_two_pi x
    refine ⟨k, ?_⟩
    have hcos : Real.cos (x - 2 * (k : ℝ) * Real.pi) = Real.cos x := hcosk k x
    by_contra hcon
    rw [not_le] at hcon
    have hsmem : |x - 2 * (k : ℝ) * Real.pi| ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨abs_nonneg _, hk⟩
    have hlt : Real.cos |x - 2 * (k : ℝ) * Real.pi| < Real.cos β :=
      Real.strictAntiOn_cos hβmem hsmem hcon
    rw [cos_abs, hcos] at hlt
    exact absurd h (not_le.mpr hlt)
  · rintro ⟨k, hk⟩
    have hcos : Real.cos (x - 2 * (k : ℝ) * Real.pi) = Real.cos x := hcosk k x
    have hsmem : |x - 2 * (k : ℝ) * Real.pi| ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨abs_nonneg _, le_trans hk hβπ⟩
    have hle : Real.cos β ≤ Real.cos |x - 2 * (k : ℝ) * Real.pi| :=
      Real.strictAntiOn_cos.antitoneOn hsmem hβmem hk
    rw [cos_abs, hcos] at hle
    exact hle


/-- **A pairwise-intersecting family of intervals has interval union.**  Finiteness supplies the
maximum of the left endpoints and the minimum of the right endpoints, and pairwise intersection
makes every point between them lie in one of the intervals. -/
theorem biUnion_Icc_eq_Icc {ι : Type*} (s : Finset ι) (hne : s.Nonempty) (a b : ι → ℝ)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, (Set.Icc (a i) (b i) ∩ Set.Icc (a j) (b j)).Nonempty) :
    (⋃ i ∈ s, Set.Icc (a i) (b i)) = Set.Icc (s.inf' hne a) (s.sup' hne b) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro y hy
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
    exact ⟨le_trans (Finset.inf'_le a hi) hyi.1, le_trans hyi.2 (Finset.le_sup' b hi)⟩
  · intro y hy
    obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_mem_eq_inf' hne a
    obtain ⟨j₀, hj₀, hmax⟩ := Finset.exists_mem_eq_sup' hne b
    have hyi : a i₀ ≤ y := hmin ▸ hy.1
    by_cases hle : y ≤ b i₀
    · exact Set.mem_iUnion₂.mpr ⟨i₀, hi₀, ⟨hyi, hle⟩⟩
    · rw [not_le] at hle
      have hsub : (Set.Icc (a i₀) (b i₀) ∩ Set.Icc (a j₀) (b j₀)).Nonempty := hpair i₀ hi₀ j₀ hj₀
      obtain ⟨z, hz1, hz2⟩ := hsub
      have haj : a j₀ ≤ b i₀ := le_trans hz2.1 hz1.2
      have hyj : a j₀ ≤ y := le_trans haj hle.le
      exact Set.mem_iUnion₂.mpr ⟨j₀, hj₀, ⟨hyj, hmax ▸ hy.2⟩⟩



/-! ## The branch of `arg` in `(π/2, 3π/2)` for vectors with negative real part -/

/-- The branch of `arg` of a vector, moved into `(0, 2π)` (and, for `Re v < 0`, into
`(π/2, 3π/2)`). -/
def argBranch (v : ℂ) : ℝ := if 0 ≤ v.arg then v.arg else v.arg + 2 * Real.pi

theorem exp_argBranch {v : ℂ} : Complex.exp ((argBranch v : ℂ) * Complex.I)
    = Complex.exp ((v.arg : ℂ) * Complex.I) := by
  rw [argBranch]
  split_ifs with h
  · rfl
  · rw [show ((v.arg + 2 * Real.pi : ℝ) : ℂ) * Complex.I
        = (v.arg : ℂ) * Complex.I + 1 * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring,
      Complex.exp_add]
    rw [show (1 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) = 2 * (Real.pi : ℂ) * Complex.I by ring,
      Complex.exp_two_pi_mul_I, mul_one]

theorem argBranch_mem {v : ℂ} (hv : v.re < 0) :
    argBranch v ∈ Set.Ioo (Real.pi / 2) (3 * Real.pi / 2) := by
  have hv0 : v ≠ 0 := by
    intro h; rw [h] at hv; simp at hv
  have harg : v.arg ∈ Set.Ioc (-Real.pi) Real.pi := ⟨Complex.neg_pi_lt_arg v, Complex.arg_le_pi v⟩
  have hcos : Real.cos v.arg < 0 := by
    rw [Complex.cos_arg hv0]
    exact div_neg_of_neg_of_pos hv (norm_pos_iff.mpr hv0)
  have hπ : 0 < Real.pi := Real.pi_pos
  rw [argBranch]
  split_ifs with h
  · have hmem : v.arg ∈ Set.Icc (0 : ℝ) Real.pi := ⟨h, Complex.arg_le_pi v⟩
    have hmem2 : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
    have hlt : Real.pi / 2 < v.arg := by
      by_contra hcon
      rw [not_lt] at hcon
      have := Real.strictAntiOn_cos.antitoneOn hmem hmem2 hcon
      rw [Real.cos_pi_div_two] at this
      linarith
    exact ⟨hlt, by linarith [Complex.arg_le_pi v]⟩
  · rw [not_le] at h
    have hmem : -v.arg ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨by linarith, by linarith [Complex.neg_pi_lt_arg v]⟩
    have hmem2 : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
    have hlt : Real.pi / 2 < -v.arg := by
      by_contra hcon
      rw [not_lt] at hcon
      have := Real.strictAntiOn_cos.antitoneOn hmem hmem2 hcon
      rw [Real.cos_pi_div_two, Real.cos_neg] at this
      linarith
    constructor <;> linarith [Complex.neg_pi_lt_arg v]

theorem argBranch_enorm_exp {v : ℂ} (hv0 : v ≠ 0) :
    ((‖v‖ : ℝ) : ℂ) * Complex.exp ((argBranch v : ℂ) * Complex.I) = v := by
  rw [exp_argBranch]
  exact Complex.norm_mul_exp_arg_mul_I v

theorem cos_argBranch_sub (v : ℂ) (θ : ℝ) :
    Real.cos (argBranch v - θ) = Real.cos (v.arg - θ) := by
  rw [argBranch]
  split_ifs with h
  · rfl
  · have hper : Real.cos (v.arg - θ + ((1 : ℤ) : ℝ) * (2 * Real.pi))
        = Real.cos (v.arg - θ) := Real.cos_periodic.int_mul 1 (v.arg - θ)
    rw [show v.arg + 2 * Real.pi - θ = v.arg - θ + ((1 : ℤ) : ℝ) * (2 * Real.pi) by
      push_cast; ring]
    exact hper

/-- The real inner product of the unit direction `e^{iθ}` with `v`, in terms of the branch
`argBranch v ∈ (π/2, 3π/2)`. -/
theorem re_star_exp_I_mul_argBranch {v : ℂ} (hv0 : v ≠ 0) (θ : ℝ) :
    (star (Complex.exp ((θ : ℂ) * Complex.I)) * v).re
      = ‖v‖ * Real.cos (argBranch v - θ) := by
  rw [re_star_exp_I_mul θ v, cos_argBranch_sub]

/-! ## The forbidden set of angles for a single threshold -/

/-- The angles `θ` with `cos (φ - θ) ≥ cos β`, i.e. the translates of `[φ - β, φ + β]`. -/
def forbidden (φ β : ℝ) : Set ℝ := ⋃ k : ℤ, Set.Icc (φ - β - 2 * (k : ℝ) * Real.pi)
  (φ + β - 2 * (k : ℝ) * Real.pi)

theorem cos_lt_cos_iff_notMem_forbidden {φ θ β : ℝ} (hβ0 : 0 ≤ β) (hβπ : β ≤ Real.pi) :
    Real.cos (φ - θ) < Real.cos β ↔ θ ∉ forbidden φ β := by
  rw [forbidden]
  simp only [Set.mem_iUnion, not_exists, Set.mem_Icc]
  constructor
  · intro hlt k hk
    obtain ⟨hk1, hk2⟩ := hk
    have hge : Real.cos β ≤ Real.cos (φ - θ) :=
      (cos_ge_iff hβ0 hβπ).mpr ⟨k, by rw [abs_le]; constructor <;> linarith⟩
    linarith
  · intro h
    by_contra hcon
    rw [not_lt] at hcon
    obtain ⟨j, hj⟩ := (cos_ge_iff hβ0 hβπ).mp hcon
    refine h j ⟨?_, ?_⟩
    · rw [abs_le] at hj; linarith [hj.1]
    · rw [abs_le] at hj; linarith [hj.2]

/-! ## Step (1) of the assembly: merging the forbidden intervals over the indices -/

/-- `inf'` of a shifted finite family. -/
theorem inf'_sub_shift {ι : Type*} {s : Finset ι} (h : s.Nonempty) (f : ι → ℝ) (t : ℝ) :
    s.inf' h (fun i => f i - t) = s.inf' h f - t := by
  refine le_antisymm ?_ ?_
  · obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_mem_eq_inf' h f
    calc s.inf' h (fun i => f i - t) ≤ f i₀ - t := Finset.inf'_le (fun i => f i - t) hi₀
      _ = s.inf' h f - t := by rw [hmin]
  · refine Finset.le_inf' h (fun i => f i - t) (a := s.inf' h f - t) (fun i hi => ?_)
    have := Finset.inf'_le f hi
    linarith

/-- `sup'` of a shifted finite family. -/
theorem sup'_sub_shift {ι : Type*} {s : Finset ι} (h : s.Nonempty) (f : ι → ℝ) (t : ℝ) :
    s.sup' h (fun i => f i - t) = s.sup' h f - t := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le h (fun i => f i - t) (a := s.sup' h f - t) (fun i hi => ?_)
    have := Finset.le_sup' f hi
    linarith
  · obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_mem_eq_sup' h f
    calc s.sup' h f - t = f i₀ - t := by rw [hmax]
      _ ≤ s.sup' h (fun i => f i - t) := Finset.le_sup' (fun i => f i - t) hi₀

/-- **The forbidden intervals at a fixed translate merge.** -/
theorem iUnion_Icc_shift {ι : Type*} [Fintype ι] [Nonempty ι] (φ : ι → ℝ) {β : ℝ}
    (hpair : ∀ i j, |φ i - φ j| ≤ 2 * β) (k : ℤ) :
    (⋃ i, Set.Icc (φ i - β - 2 * (k : ℝ) * Real.pi) (φ i + β - 2 * (k : ℝ) * Real.pi))
      = Set.Icc (Finset.univ.inf' Finset.univ_nonempty φ - β - 2 * (k : ℝ) * Real.pi)
          (Finset.univ.sup' Finset.univ_nonempty φ + β - 2 * (k : ℝ) * Real.pi) := by
  have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
  have hpair' : ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ Finset.univ,
      (Set.Icc (φ i - β - 2 * (k : ℝ) * Real.pi) (φ i + β - 2 * (k : ℝ) * Real.pi)
        ∩ Set.Icc (φ j - β - 2 * (k : ℝ) * Real.pi)
            (φ j + β - 2 * (k : ℝ) * Real.pi)).Nonempty := by
    intro i _ j _
    have hij := abs_le.mp (hpair i j)
    refine ⟨(φ i + φ j) / 2 - 2 * (k : ℝ) * Real.pi, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
  rw [show (⋃ i, Set.Icc (φ i - β - 2 * (k : ℝ) * Real.pi)
        (φ i + β - 2 * (k : ℝ) * Real.pi))
      = (⋃ i ∈ (Finset.univ : Finset ι), Set.Icc (φ i - β - 2 * (k : ℝ) * Real.pi)
          (φ i + β - 2 * (k : ℝ) * Real.pi)) from by simp]
  rw [biUnion_Icc_eq_Icc Finset.univ hne
    (fun i => φ i - β - 2 * (k : ℝ) * Real.pi)
    (fun i => φ i + β - 2 * (k : ℝ) * Real.pi) hpair']
  rw [show (fun i : ι => φ i - β - 2 * (k : ℝ) * Real.pi)
        = (fun i : ι => φ i - (β + 2 * (k : ℝ) * Real.pi)) from by funext i; ring,
    show (fun i : ι => φ i + β - 2 * (k : ℝ) * Real.pi)
        = (fun i : ι => φ i - (-(β) + 2 * (k : ℝ) * Real.pi)) from by funext i; ring]
  rw [inf'_sub_shift hne φ (β + 2 * (k : ℝ) * Real.pi),
    sup'_sub_shift hne φ (-(β) + 2 * (k : ℝ) * Real.pi)]
  ring_nf

/-- **The union of the forbidden sets over the indices is the union of the translates of the merged
interval.** -/
theorem iUnion_forbidden_eq {ι : Type*} [Fintype ι] [Nonempty ι] (φ : ι → ℝ) {β : ℝ}
    (hpair : ∀ i j, |φ i - φ j| ≤ 2 * β) :
    (⋃ i, forbidden (φ i) β) =
      ⋃ k : ℤ, Set.Icc (Finset.univ.inf' Finset.univ_nonempty φ - β - 2 * (k : ℝ) * Real.pi)
        (Finset.univ.sup' Finset.univ_nonempty φ + β - 2 * (k : ℝ) * Real.pi) := by
  simp only [forbidden]
  rw [Set.iUnion_comm]
  refine le_antisymm ?_ ?_
  · rw [Set.iUnion_subset_iff]
    intro k
    rw [iUnion_Icc_shift φ hpair k]
    exact Set.subset_iUnion (fun k' : ℤ => Set.Icc
      (Finset.univ.inf' Finset.univ_nonempty φ - β - 2 * (k' : ℝ) * Real.pi)
      (Finset.univ.sup' Finset.univ_nonempty φ + β - 2 * (k' : ℝ) * Real.pi)) k
  · rw [Set.iUnion_subset_iff]
    intro k
    rw [← iUnion_Icc_shift φ hpair k]
    exact Set.subset_iUnion (fun i' : ℤ => ⋃ i, Set.Icc (φ i - β - 2 * (i' : ℝ) * Real.pi)
      (φ i + β - 2 * (i' : ℝ) * Real.pi)) k

/-! ## Step (2) of the assembly: the complement description of the legal angles -/

/-- **The legal angles.** -/
theorem cos_all_lt_iff_notMem {ι : Type*} [Fintype ι] [Nonempty ι] (φ : ι → ℝ) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβπ : β ≤ Real.pi) (hpair : ∀ i j, |φ i - φ j| ≤ 2 * β) (θ : ℝ) :
    (∀ i, Real.cos (φ i - θ) < Real.cos β) ↔
      θ ∉ ⋃ k : ℤ, Set.Icc
        (Finset.univ.inf' Finset.univ_nonempty φ - β - 2 * (k : ℝ) * Real.pi)
        (Finset.univ.sup' Finset.univ_nonempty φ + β - 2 * (k : ℝ) * Real.pi) := by
  rw [← iUnion_forbidden_eq φ hpair]
  rw [Set.mem_iUnion, not_exists]
  exact forall_congr' fun i => cos_lt_cos_iff_notMem_forbidden hβ0 hβπ

/-- **The threshold condition as a cosine condition.** -/
theorem slice_threshold_iff {v : ℂ} {β c' r : ℝ} (hr : 0 < r) (hvnorm : ‖v‖ = r)
    (hcosβ : Real.cos β = c' / r) (θ : ℝ) :
    (star (Complex.exp ((θ : ℂ) * Complex.I)) * v).re < c'
      ↔ Real.cos (argBranch v - θ) < Real.cos β := by
  have hv0 : v ≠ 0 := by
    intro h
    rw [h] at hvnorm
    simp at hvnorm
    linarith
  rw [re_star_exp_I_mul_argBranch hv0 θ, hvnorm, hcosβ, lt_div_iff₀ hr,
    mul_comm (Real.cos (argBranch v - θ)) r]

/-! ## Step (3) of the assembly: pushing a legal angle into the fundamental window -/

/-- **Step (3).** -/
theorem exists_translate_mem_Ioo {A B θ : ℝ}
    (h : θ ∉ ⋃ k : ℤ, Set.Icc (A - 2 * (k : ℝ) * Real.pi) (B - 2 * (k : ℝ) * Real.pi)) :
    ∃ k : ℤ, θ - 2 * ((k : ℝ) + 1) * Real.pi ∈ Set.Ioo (B - 2 * Real.pi) A ∧
      Complex.exp (((θ - 2 * ((k : ℝ) + 1) * Real.pi : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((θ : ℂ) * Complex.I) := by
  set k : ℤ := ⌊(θ - A) / (2 * Real.pi)⌋ with hk
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 : ((k : ℝ)) ≤ (θ - A) / (2 * Real.pi) := by rw [hk]; exact Int.floor_le _
  have h2 : (θ - A) / (2 * Real.pi) < (k : ℝ) + 1 := by
    rw [hk]; exact Int.lt_floor_add_one _
  have hlow : A + 2 * (k : ℝ) * Real.pi ≤ θ := by
    have := (le_div_iff₀ h2π).mp h1
    linarith
  have hhigh : θ < A + 2 * (k : ℝ) * Real.pi + 2 * Real.pi := by
    have := (div_lt_iff₀ h2π).mp h2
    linarith
  have hnot : ¬ (A + 2 * (k : ℝ) * Real.pi ≤ θ ∧ θ ≤ B + 2 * (k : ℝ) * Real.pi) := by
    intro hc
    refine h (Set.mem_iUnion.mpr ⟨-k, ?_⟩)
    simp only [Set.mem_Icc] at hc ⊢
    constructor <;> push_cast at hc ⊢ <;> linarith
  have hlowB : B + 2 * (k : ℝ) * Real.pi < θ :=
    not_le.mp fun hle => hnot ⟨hlow, hle⟩
  refine ⟨k, ?_, ?_⟩
  · have hkey : 2 * ((k : ℝ) + 1) * Real.pi = 2 * (k : ℝ) * Real.pi + 2 * Real.pi := by ring
    rw [Set.mem_Ioo, hkey]
    constructor <;> linarith
  · rw [show ((θ - 2 * ((k : ℝ) + 1) * Real.pi : ℝ) : ℂ) * Complex.I
        = (θ : ℂ) * Complex.I + ((-(k + 1) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
      push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ## Step (4) of the assembly -/

/-- **The fundamental window avoids all translates.** -/
theorem notMem_iUnion_Icc_of_mem_Ioo {A B θ : ℝ} (h : θ ∈ Set.Ioo (B - 2 * Real.pi) A) :
    θ ∉ ⋃ k : ℤ, Set.Icc (A - 2 * (k : ℝ) * Real.pi) (B - 2 * (k : ℝ) * Real.pi) := by
  rw [Set.mem_iUnion]
  rintro ⟨k, hk⟩
  simp only [Set.mem_Icc] at hk
  simp only [Set.mem_Ioo] at h
  have hπ : 0 < Real.pi := Real.pi_pos
  by_cases hk0 : k ≤ 0
  · have hk1 : (0 : ℝ) ≤ -(k : ℝ) := by
      have : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
      linarith
    have hle : A ≤ A - 2 * (k : ℝ) * Real.pi := by nlinarith
    linarith [hk.1, h.2, hle]
  · rw [not_le] at hk0
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
    have hle : B - 2 * (k : ℝ) * Real.pi ≤ B - 2 * Real.pi := by nlinarith
    linarith [hk.2, h.1, hle]

/-- A unit complex number is the exponential of its argument. -/
theorem exp_arg_of_norm_one {u : ℂ} (hu : ‖u‖ = 1) :
    Complex.exp ((Complex.arg u : ℂ) * Complex.I) = u := by
  have h := Complex.norm_mul_exp_arg_mul_I u
  rw [hu] at h
  simpa using h

/-- **Slice-joining.**  If all the active centres lie in the open half-plane `{Re < 0}` (i.e. the
free direction has been rotated to `1`), then for all sufficiently small thresholds `c` the set of
unit directions `u` with `⟪u, v i⟫ < c` for every `i` is an arc of the direction circle: it is the
image of an interval of length `< 2π` under `θ ↦ e^{i θ}`.

Consequently the relation "joined inside the slice" is transitive there, which is the step that
makes the local complement of `⋃ w ∈ Q, closedBall w r` preconnected (see
`.mytmp/NOTES_aux.md`, `localComplementPreconnected`).

Proof plan (ingredients all in this file): `cos_ge_iff` turns the condition
`⟪e^{iθ}, v i⟫ < c` into `θ ∉ ⋃ k, Icc (φ i - β + 2 k π) (φ i + β + 2 k π)` with
`φ i := (v i).arg` (here `Re (v i) < 0` gives `φ i ∈ (π/2, 3π/2)` after shifting the branch) and
`β := arccos (c / r)`; `biUnion_Icc_eq_Icc` shows the union of the *base* intervals over `i` is the
single interval `Icc (min φ - β) (max φ + β)` as soon as `2 β ≥ max φ - min φ` (possible for small
`c` since `max φ - min φ < π`), and the `k = -1, 0` shifts give exactly the two forbidden pieces in
`(-2π, 2π)`, whose complement component through `0` is
`Ioo (max φ + β - 2 π) (min φ - β)`. -/
theorem slice_isArc {ι : Type*} [Fintype ι] [Nonempty ι] (v : ι → ℂ) {r : ℝ} (hr : 0 < r)
    (hv : ∀ i, ‖v i‖ = r) (hfree : ∀ i, (v i).re < 0) :
    ∃ c > 0, ∀ c' ∈ Set.Ioo (0 : ℝ) c, ∃ a b : ℝ, a < b ∧ b - a < 2 * Real.pi ∧
      {u : ℂ | ‖u‖ = 1 ∧ ∀ i, (star u * v i).re < c'} =
        {Complex.exp ((θ : ℂ) * Complex.I) | θ ∈ Set.Ioo a b} := by
  classical
  have hve : ∀ i, v i ≠ 0 := by
    intro i h
    have := hfree i
    rw [h] at this
    simp at this
  set φ : ι → ℝ := fun i => argBranch (v i) with hφdef
  have hφmem : ∀ i, φ i ∈ Set.Ioo (Real.pi / 2) (3 * Real.pi / 2) := fun i =>
    argBranch_mem (hfree i)
  set Φmin : ℝ := Finset.univ.inf' Finset.univ_nonempty φ with hΦmindef
  set Φmax : ℝ := Finset.univ.sup' Finset.univ_nonempty φ with hΦmaxdef
  have hΦle : ∀ i, Φmin ≤ φ i := fun i => Finset.inf'_le φ (Finset.mem_univ i)
  have hleΦ : ∀ i, φ i ≤ Φmax := fun i => Finset.le_sup' φ (Finset.mem_univ i)
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have hspan : Φmax - Φmin < Real.pi := by
    obtain ⟨i₁, -, hi₁⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty φ
    obtain ⟨i₂, -, hi₂⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty φ
    have h1 : Φmax < 3 * Real.pi / 2 := by rw [hΦmaxdef, hi₁]; exact (hφmem i₁).2
    have h2 : Real.pi / 2 < Φmin := by rw [hΦmindef, hi₂]; exact (hφmem i₂).1
    linarith
  have hcos_pos : 0 < Real.cos ((Φmax - Φmin) / 2) := by
    refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩ <;> linarith [hΦle i₀, hleΦ i₀]
  refine ⟨r * Real.cos ((Φmax - Φmin) / 2), mul_pos hr hcos_pos, ?_⟩
  intro c' hc'
  obtain ⟨hc'0, hc'lt⟩ := hc'
  set β : ℝ := Real.arccos (c' / r) with hβdef
  have hβ0 : 0 ≤ β := Real.arccos_nonneg _
  have hβπ : β ≤ Real.pi := Real.arccos_le_pi _
  have hrat0 : 0 < c' / r := div_pos hc'0 hr
  have hrat1 : c' / r ≤ 1 := by
    rw [div_le_one hr]
    have h1 : Real.cos ((Φmax - Φmin) / 2) ≤ 1 := Real.cos_le_one _
    nlinarith [hc'lt, h1, hr]
  have hcosβ : Real.cos β = c' / r := Real.cos_arccos (by linarith) hrat1
  have hβgt : (Φmax - Φmin) / 2 < β := by
    have h := Real.arccos_lt_arccos (x := c' / r) (y := Real.cos ((Φmax - Φmin) / 2))
      (by linarith) (by rw [div_lt_iff₀ hr]; nlinarith [hc'lt]) (Real.cos_le_one _)
    rwa [Real.arccos_cos (by linarith [hΦle i₀, hleΦ i₀]) (by linarith)] at h
  have hβpos : 0 < β := by
    have h0 : 0 ≤ (Φmax - Φmin) / 2 := by linarith [hΦle i₀, hleΦ i₀]
    linarith
  have hβlt : β < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr hrat0
  have hpair : ∀ i j, |φ i - φ j| ≤ 2 * β := by
    intro i j
    have h1 : φ i - φ j ≤ Φmax - Φmin := by linarith [hleΦ i, hΦle j]
    have h2 : φ j - φ i ≤ Φmax - Φmin := by linarith [hleΦ j, hΦle i]
    have h3 : Φmax - Φmin ≤ 2 * β := by linarith
    rw [abs_sub_le_iff]
    constructor <;> linarith
  refine ⟨Φmax + β - 2 * Real.pi, Φmin - β, ?_, ?_, ?_⟩
  · linarith
  · have h4 : Φmin ≤ Φmax := by linarith [hΦle i₀, hleΦ i₀]
    linarith
  · ext u
    constructor
    · intro hu
      obtain ⟨hu1, hu2⟩ := hu
      have harg := exp_arg_of_norm_one hu1
      have hthr : ∀ i, Real.cos (φ i - Complex.arg u) < Real.cos β := by
        intro i
        have h1 : (star (Complex.exp (((Complex.arg u : ℝ) : ℂ) * Complex.I)) * v i).re < c' := by
          rw [harg]
          exact hu2 i
        have h2 := (slice_threshold_iff hr (hv i) hcosβ (Complex.arg u)).mp h1
        simpa [hφdef] using h2
      have hnot := (cos_all_lt_iff_notMem φ (β := β) hβ0 hβπ hpair (Complex.arg u)).mp hthr
      obtain ⟨k, hk, hexp⟩ := exists_translate_mem_Ioo hnot
      exact ⟨Complex.arg u - 2 * ((k : ℝ) + 1) * Real.pi, hk, by rw [hexp, harg]⟩
    · rintro ⟨θ, hθ, rfl⟩
      have hnot : θ ∉ ⋃ k : ℤ,
          Set.Icc (Finset.univ.inf' Finset.univ_nonempty φ - β - 2 * (k : ℝ) * Real.pi)
            (Finset.univ.sup' Finset.univ_nonempty φ + β - 2 * (k : ℝ) * Real.pi) := by
        have h := notMem_iUnion_Icc_of_mem_Ioo (A := Φmin - β) (B := Φmax + β) hθ
        rw [hΦmindef, hΦmaxdef] at h
        exact h
      have hcos := (cos_all_lt_iff_notMem φ (β := β) hβ0 hβπ hpair θ).mpr hnot
      refine ⟨Complex.norm_exp_ofReal_mul_I θ, ?_⟩
      intro i
      rw [slice_threshold_iff hr (hv i) hcosβ θ]
      simpa [hφdef] using hcos i

end

end Work.Smooth.SphereJordan
