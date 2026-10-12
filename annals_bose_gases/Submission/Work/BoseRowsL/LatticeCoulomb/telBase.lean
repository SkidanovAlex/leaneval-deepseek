import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseRowsL.LatticeCoulomb.kernelDefs
import Submission.Work.BoseRowsL.LatticeCoulomb.restShellSum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open scoped Real BigOperators Topology
open MeasureTheory Metric

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false

/-! ### Setup: the unit vector, the phases, the splitting equivalence -/

/-- The `j`-th unit lattice vector of `ℤ³`. -/
def telE (j : Fin 3) : Fin 3 → ℤ := Pi.single j 1

@[simp] lemma telE_self (j : Fin 3) : telE j j = 1 := Pi.single_eq_same ..
@[simp] lemma telE_ne {i j : Fin 3} (h : i ≠ j) : telE j i = 0 := Pi.single_eq_of_ne h ..

lemma norm_sq_nvec_eq_sum (m : Fin 3 → ℤ) : ‖nvec m‖ ^ 2 = ∑ i, ((m i : ℝ)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [nvec_apply]

lemma tel_sum_split (f : Fin 3 → ℝ) (j : Fin 3) :
    (∑ i : Fin 3, f i) = f j + ∑ i : {i : Fin 3 // i ≠ j}, f i := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun i : Fin 3 => i ≠ j))
    (by intro x; simp) f]
  have h : Finset.univ.filter (fun i : Fin 3 => i ≠ j) = Finset.univ.erase j := by
    ext i; simp
  rw [h]
  have h2 := Finset.sum_erase_add (Finset.univ : Finset (Fin 3)) f (Finset.mem_univ j)
  linarith [h2]

/-- Splitting `ℤ³` into the `j`-th coordinate and the two remaining coordinates. -/
def telEq (j : Fin 3) : (Fin 3 → ℤ) ≃ ℤ × ({i : Fin 3 // i ≠ j} → ℤ) :=
  Equiv.piSplitAt j (fun _ : Fin 3 => ℤ)

/-- The squared norm of the two remaining coordinates. -/
def telQSq {j : Fin 3} (q : {i : Fin 3 // i ≠ j} → ℤ) : ℝ := ∑ i, ((q i : ℝ)) ^ 2

/-- The `ℓ^∞`-norm of the two remaining coordinates. -/
abbrev telAbs {j : Fin 3} (q : {i : Fin 3 // i ≠ j} → ℤ) : ℕ :=
  Finset.univ.sup fun i => (q i).natAbs

lemma telEq_fst (j : Fin 3) (m : Fin 3 → ℤ) : (telEq j m).1 = m j := rfl
lemma telEq_snd (j : Fin 3) (m : Fin 3 → ℤ) (i : {i : Fin 3 // i ≠ j}) :
    (telEq j m).2 i = m i := rfl

lemma telEq_symm_fst (j : Fin 3) (x : ℤ × ({i : Fin 3 // i ≠ j} → ℤ)) :
    ((telEq j).symm x) j = x.1 := by
  rw [← telEq_fst j ((telEq j).symm x), Equiv.apply_symm_apply]

lemma telEq_symm_snd (j : Fin 3) (x : ℤ × ({i : Fin 3 // i ≠ j} → ℤ))
    (i : {i : Fin 3 // i ≠ j}) : ((telEq j).symm x) i = x.2 i := by
  rw [← telEq_snd j ((telEq j).symm x) i, Equiv.apply_symm_apply]

lemma tel_normSq_symm (j : Fin 3) (x : ℤ × ({i : Fin 3 // i ≠ j} → ℤ)) :
    ‖nvec ((telEq j).symm x)‖ ^ 2 = (x.1 : ℝ) ^ 2 + telQSq x.2 := by
  rw [norm_sq_nvec_eq_sum, tel_sum_split (fun i : Fin 3 => (((telEq j).symm x) i : ℝ) ^ 2) j]
  simp only [telEq_symm_fst, telEq_symm_snd, telQSq]

lemma telQSq_nonneg {j : Fin 3} (q : {i : Fin 3 // i ≠ j} → ℤ) : 0 ≤ telQSq q :=
  Finset.sum_nonneg fun i _ => by positivity

lemma telQSq_pos {j : Fin 3} {q : {i : Fin 3 // i ≠ j} → ℤ} (hq : q ≠ 0) : 0 < telQSq q := by
  obtain ⟨i, hi⟩ : ∃ i, q i ≠ 0 := by
    by_contra h
    exact hq (funext fun i => not_not.mp (not_exists.mp h i))
  have h1 : (1 : ℝ) ≤ ((q i : ℝ)) ^ 2 := by
    have h2 : (1 : ℤ) ≤ (q i) ^ 2 := by
      have h3 : q i ≠ 0 := hi
      nlinarith [Int.one_le_abs h3, abs_nonneg (q i), sq_abs (q i)]
    exact_mod_cast h2
  have h2 : ((q i : ℝ)) ^ 2 ≤ telQSq q := by
    rw [telQSq]
    exact Finset.single_le_sum (f := fun k : {i : Fin 3 // i ≠ j} => ((q k : ℝ)) ^ 2)
      (fun k _ => by positivity) (Finset.mem_univ i)
  linarith

/-- A nonzero rest point has squared norm at least `1`. -/
lemma tel_one_le_telQSq {j : Fin 3} {q : {i : Fin 3 // i ≠ j} → ℤ} (hq : q ≠ 0) :
    1 ≤ telQSq q := by
  obtain ⟨i, hi⟩ : ∃ i, q i ≠ 0 := by
    by_contra h
    exact hq (funext fun i => not_not.mp (not_exists.mp h i))
  have h1 : (1 : ℝ) ≤ ((q i : ℝ)) ^ 2 := by
    have h2 : (1 : ℤ) ≤ (q i) ^ 2 := by
      have h3 : q i ≠ 0 := hi
      nlinarith [Int.one_le_abs h3, abs_nonneg (q i), sq_abs (q i)]
    exact_mod_cast h2
  have h2 : ((q i : ℝ)) ^ 2 ≤ telQSq q := by
    rw [telQSq]
    exact Finset.single_le_sum (f := fun k : {i : Fin 3 // i ≠ j} => ((q k : ℝ)) ^ 2)
      (fun k _ => by positivity) (Finset.mem_univ i)
  linarith

lemma telEq_symm_add_E (j : Fin 3) (k : ℤ) (q : {i : Fin 3 // i ≠ j} → ℤ) :
    (telEq j).symm (k, q) + telE j = (telEq j).symm (k + 1, q) := by
  refine (Equiv.eq_symm_apply (telEq j)).mpr ?_
  refine Prod.ext ?_ ?_
  · rw [telEq_fst, Pi.add_apply, telEq_symm_fst, telE_self]
  · funext i
    rw [telEq_snd, Pi.add_apply, telEq_symm_snd, telE_ne i.2, add_zero]

lemma telEq_symm_sub_E (j : Fin 3) (k : ℤ) (q : {i : Fin 3 // i ≠ j} → ℤ) :
    (telEq j).symm (k, q) - telE j = (telEq j).symm (k - 1, q) := by
  refine (Equiv.eq_symm_apply (telEq j)).mpr ?_
  refine Prod.ext ?_ ?_
  · rw [telEq_fst, Pi.sub_apply, telEq_symm_fst, telE_self]
  · funext i
    rw [telEq_snd, Pi.sub_apply, telEq_symm_snd, telE_ne i.2, sub_zero]

/-! ### The phases -/

/-- The phase `2π⟪nvec n, z⟫` of the lattice point `n`. -/
def telTh (z : E3) (n : Fin 3 → ℤ) : ℝ := 2 * Real.pi * inner ℝ (nvec n) z

/-- The phase increment in the `j`-th direction. -/
def telPh (z : E3) (j : Fin 3) : ℝ := 2 * Real.pi * z.ofLp j

lemma nvec_add (m n : Fin 3 → ℤ) : nvec (m + n) = nvec m + nvec n := by
  ext i
  simp [nvec_apply]

lemma nvec_zsmul (k : ℤ) (m : Fin 3 → ℤ) : nvec (k • m) = (k : ℝ) • nvec m := by
  ext i
  simp [nvec_apply]

lemma inner_nvec_telE (j : Fin 3) (z : E3) : inner ℝ (nvec (telE j)) z = z.ofLp j := by
  rw [PiLp.inner_apply]
  simp only [nvec_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [telE, hb]
  · intro h; exact absurd (Finset.mem_univ j) h

lemma norm_nvec_telE (j : Fin 3) : ‖nvec (telE j)‖ = 1 := by
  have h : ‖nvec (telE j)‖ ^ 2 = 1 := by
    rw [norm_sq_nvec_eq_sum]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [telE, hb]
    · intro h; exact absurd (Finset.mem_univ j) h
  nlinarith [norm_nonneg (nvec (telE j))]

lemma inner_nvec_add_zsmul (m : Fin 3 → ℤ) (k : ℤ) (j : Fin 3) (z : E3) :
    inner ℝ (nvec (m + k • telE j)) z = inner ℝ (nvec m) z + (k : ℝ) * z.ofLp j := by
  rw [nvec_add, nvec_zsmul, inner_add_left, real_inner_smul_left, inner_nvec_telE]

lemma telTh_add (z : E3) (j : Fin 3) (m : Fin 3 → ℤ) :
    telTh z (m + telE j) = telTh z m + telPh z j := by
  have h : m + telE j = m + (1 : ℤ) • telE j := by simp
  rw [h, telTh, telTh, telPh, inner_nvec_add_zsmul]
  push_cast
  ring

lemma telTh_sub (z : E3) (j : Fin 3) (m : Fin 3 → ℤ) :
    telTh z (m - telE j) = telTh z m - telPh z j := by
  have h : m - telE j = m + (-1 : ℤ) • telE j := by rw [sub_eq_add_neg]; simp
  rw [h, telTh, telTh, telPh, inner_nvec_add_zsmul]
  push_cast
  ring

/-! ### The telescoping identity -/

/-- The set of points appearing in the telescoping identity. -/
def telW (T : Finset (Fin 3 → ℤ)) (j : Fin 3) : Finset (Fin 3 → ℤ) :=
  (T ∪ T.image (fun n => n + telE j)) ∪ T.image (fun n => n - telE j)

/-- The telescoping coefficient. -/
def telG (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (m : Fin 3 → ℤ) : ℝ :=
  (if m ∈ T then 1 / ‖nvec m‖ ^ 2 else 0)
    - (1 / 2) * (if m - telE j ∈ T then 1 / ‖nvec (m - telE j)‖ ^ 2 else 0)
    - (1 / 2) * (if m + telE j ∈ T then 1 / ‖nvec (m + telE j)‖ ^ 2 else 0)

lemma tel_self_subset_W (T : Finset (Fin 3 → ℤ)) (j : Fin 3) : T ⊆ telW T j := by
  intro m hm
  simp only [telW, Finset.mem_union]
  exact Or.inl (Or.inl hm)

lemma tel_image_add_subset_W (T : Finset (Fin 3 → ℤ)) (j : Fin 3) :
    T.image (fun n => n + telE j) ⊆ telW T j := by
  intro m hm
  simp only [telW, Finset.mem_union]
  exact Or.inl (Or.inr hm)

lemma tel_image_sub_subset_W (T : Finset (Fin 3 → ℤ)) (j : Fin 3) :
    T.image (fun n => n - telE j) ⊆ telW T j := by
  intro m hm
  simp only [telW, Finset.mem_union]
  exact Or.inr hm

lemma mem_image_add_iff (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (m : Fin 3 → ℤ) :
    m ∈ T.image (fun n => n + telE j) ↔ m - telE j ∈ T := by
  constructor
  · intro h
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp h
    simpa using hn
  · intro h
    exact Finset.mem_image.mpr ⟨m - telE j, h, by abel⟩

lemma mem_image_sub_iff (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (m : Fin 3 → ℤ) :
    m ∈ T.image (fun n => n - telE j) ↔ m + telE j ∈ T := by
  constructor
  · intro h
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp h
    simpa using hn
  · intro h
    exact Finset.mem_image.mpr ⟨m + telE j, h, by abel⟩

/-- **The telescoping identity.** -/
theorem telIdent (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (z : E3) :
    (1 - Real.cos (telPh z j)) * (∑ n ∈ T, Real.cos (telTh z n) / ‖nvec n‖ ^ 2)
      = ∑ m ∈ telW T j, telG T j m * Real.cos (telTh z m) := by
  classical
  have h1 : (1 - Real.cos (telPh z j)) * (∑ n ∈ T, Real.cos (telTh z n) / ‖nvec n‖ ^ 2)
      = ∑ n ∈ T, (Real.cos (telTh z n) - (1 / 2) * Real.cos (telTh z (n + telE j))
            - (1 / 2) * Real.cos (telTh z (n - telE j))) / ‖nvec n‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [telTh_add, telTh_sub, Real.cos_add, Real.cos_sub]
    ring
  rw [h1]
  have h2 : ∀ n ∈ T, (Real.cos (telTh z n) - (1 / 2) * Real.cos (telTh z (n + telE j))
            - (1 / 2) * Real.cos (telTh z (n - telE j))) / ‖nvec n‖ ^ 2
        = Real.cos (telTh z n) / ‖nvec n‖ ^ 2
          - (1 / 2) * (Real.cos (telTh z (n + telE j)) / ‖nvec n‖ ^ 2)
          - (1 / 2) * (Real.cos (telTh z (n - telE j)) / ‖nvec n‖ ^ 2) := by
    intro n _; ring
  rw [Finset.sum_congr rfl h2, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hshift₁ : (∑ n ∈ T, (1 / 2) * (Real.cos (telTh z (n + telE j)) / ‖nvec n‖ ^ 2))
      = ∑ m ∈ T.image (fun n => n + telE j),
          (1 / 2) * (Real.cos (telTh z m) / ‖nvec (m - telE j)‖ ^ 2) := by
    rw [Finset.sum_image (f := fun m => (1 / 2) * (Real.cos (telTh z m) / ‖nvec (m - telE j)‖ ^ 2))
      (g := fun n => n + telE j) (s := T) (fun a _ b _ h => by simpa using h)]
    simp only [add_sub_cancel_right]
  have hshift₂ : (∑ n ∈ T, (1 / 2) * (Real.cos (telTh z (n - telE j)) / ‖nvec n‖ ^ 2))
      = ∑ m ∈ T.image (fun n => n - telE j),
          (1 / 2) * (Real.cos (telTh z m) / ‖nvec (m + telE j)‖ ^ 2) := by
    rw [Finset.sum_image (f := fun m => (1 / 2) * (Real.cos (telTh z m) / ‖nvec (m + telE j)‖ ^ 2))
      (g := fun n => n - telE j) (s := T) (fun a _ b _ h => by simpa using h)]
    simp only [sub_add_cancel]
  rw [hshift₁, hshift₂]
  have hT : (∑ m ∈ telW T j, (if m ∈ T then Real.cos (telTh z m) / ‖nvec m‖ ^ 2 else 0))
      = ∑ m ∈ T, Real.cos (telTh z m) / ‖nvec m‖ ^ 2 := by
    rw [← Finset.sum_filter]
    congr 1
    ext m
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact h2
    · intro h; exact ⟨tel_self_subset_W T j h, h⟩
  have hI : (∑ m ∈ telW T j,
        (if m - telE j ∈ T then Real.cos (telTh z m) / ‖nvec (m - telE j)‖ ^ 2 else 0))
      = ∑ m ∈ T.image (fun n => n + telE j),
          Real.cos (telTh z m) / ‖nvec (m - telE j)‖ ^ 2 := by
    rw [← Finset.sum_filter]
    congr 1
    ext m
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨-, h⟩; exact (mem_image_add_iff T j m).mpr h
    · intro h
      exact ⟨tel_image_add_subset_W T j h, (mem_image_add_iff T j m).mp h⟩
  have hJ : (∑ m ∈ telW T j,
        (if m + telE j ∈ T then Real.cos (telTh z m) / ‖nvec (m + telE j)‖ ^ 2 else 0))
      = ∑ m ∈ T.image (fun n => n - telE j),
          Real.cos (telTh z m) / ‖nvec (m + telE j)‖ ^ 2 := by
    rw [← Finset.sum_filter]
    congr 1
    ext m
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨-, h⟩; exact (mem_image_sub_iff T j m).mpr h
    · intro h
      exact ⟨tel_image_sub_subset_W T j h, (mem_image_sub_iff T j m).mp h⟩
  have hsplit : (∑ m ∈ telW T j, telG T j m * Real.cos (telTh z m))
      = (∑ m ∈ telW T j, (if m ∈ T then Real.cos (telTh z m) / ‖nvec m‖ ^ 2 else 0))
        - (1 / 2) * (∑ m ∈ telW T j,
            (if m - telE j ∈ T then Real.cos (telTh z m) / ‖nvec (m - telE j)‖ ^ 2 else 0))
        - (1 / 2) * (∑ m ∈ telW T j,
            (if m + telE j ∈ T then Real.cos (telTh z m) / ‖nvec (m + telE j)‖ ^ 2 else 0)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp only [telG]
    split_ifs <;> ring
  rw [hsplit, hT, hI, hJ, Finset.mul_sum, Finset.mul_sum]

end Work.BoseRowsL.LatticeCoulomb
