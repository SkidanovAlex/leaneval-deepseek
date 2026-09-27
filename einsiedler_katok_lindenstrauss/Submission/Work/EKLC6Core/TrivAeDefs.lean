import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLRelCross.Instances

/-!
# `EKLC6Core.TrivAeDefs` — vocabulary for the a.e. triviality dichotomy

The target lemma `Work.EKLC6Core.trivial_ae_dichotomy` states that for an `A`-ergodic probability
`μ`, a leafwise system `ν = μ_x^U` on a conull set and the `A`-covariance on a conull set,
*a.e.* either `ν x = δ₁` or `ν x ≠ δ₁`.

The mathematical content is: the set `{x | ν x = δ₁}` is `A`-invariant, so ergodicity forces it
(null or conull).  The formal gap is measurability: the contract gives only that
`x ↦ ∫ f dν x` is measurable for `f` compactly supported continuous, so `{x | ν x = δ₁}` is not
immediately known to be measurable.

We produce a *concrete countable family of compactly supported continuous test functions*
`testFun i j m N` whose simultaneous vanishing on `ν x` is equivalent (for `x ∈ X'`) to
`ν x = δ₁`.  The family is built from the continuous functions

* `absEntry i j g = |gᵢⱼ - δᵢⱼ|`,
* `absSum g = ∑ᵢⱼ |gᵢⱼ|`     (a "norm" on the compactly-bounded part of `SL₃(ℝ)`)

by the formula `testFun i j m N g = min 1 (max 0 (absEntry i j g - 1/(m+1))) * min 1 (max 0 (N - absSum g))`,
which is compactly supported, nonnegative, and positive exactly where
`absEntry i j g > 1/(m+1)` and `absSum g < N`.  The union over `(i,j,m,N)` of the positivity sets is
the complement of `{1}`, so `∫ testFun i j m N dν x = 0` for all `i j m N` forces `ν x` to be
carried by `{1}`, and the normalisation `ν x (Box1 U) = 1` then gives `ν x = δ₁`.
-/

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## The matrix "norm" `absSum` and the entry functions -/

/-- `∑ᵢⱼ |Aᵢⱼ|`, a continuous function on matrices of all sizes (here `Fin 3`). -/
def absSumPi (g : Fin 3 → Fin 3 → ℝ) : ℝ := ∑ p : Fin 3 × Fin 3, |g p.1 p.2|

/-- `∑ᵢⱼ |Aᵢⱼ|` on `SL₃(ℝ)`, continuous and coercive on compactly bounded sets. -/
def absSum (g : SL3) : ℝ := absSumPi g

/-- `|gᵢⱼ - δᵢⱼ|`, the `(i,j)`-entry distance of `g` from `1`. -/
def absEntry (i j : Fin 3) (g : SL3) : ℝ := |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|

theorem continuous_absSumPi : Continuous absSumPi := by unfold absSumPi; fun_prop

theorem continuous_absSum : Continuous absSum :=
  continuous_absSumPi.comp continuous_subtype_val

theorem continuous_absEntry (i j : Fin 3) : Continuous (absEntry i j) := by
  unfold absEntry; fun_prop

/-- The set of matrices of `SL₃(ℝ)` with `absSum ≤ N` is compact (it is a closed subset of the
entrywise box `[-N,N]⁹ ∩ {det = 1}`). -/
theorem isCompact_absSumPi_le (N : ℕ) :
    IsCompact {g : SL3 | absSumPi (g : Fin 3 → Fin 3 → ℝ) ≤ (N:ℝ)} := by
  have hcont : Continuous (absSumPi : (Fin 3 → Fin 3 → ℝ) → ℝ) := continuous_absSumPi
  have hbox : IsCompact (Set.Icc (fun _ : Fin 3 => fun _ : Fin 3 => -(N:ℝ))
      (fun _ _ => (N:ℝ)) : Set (Fin 3 → Fin 3 → ℝ)) := isCompact_Icc
  have hclosed : IsClosed ({A : Fin 3 → Fin 3 → ℝ | absSumPi A ≤ (N:ℝ)}
      ∩ {A : Fin 3 → Fin 3 → ℝ | Matrix.det A = 1}) :=
    (isClosed_le hcont continuous_const).inter
      (isClosed_eq (Continuous.matrix_det continuous_id) continuous_const)
  have hsub : ({A : Fin 3 → Fin 3 → ℝ | absSumPi A ≤ (N:ℝ)}
      ∩ {A : Fin 3 → Fin 3 → ℝ | Matrix.det A = 1}) ⊆
      (Set.Icc (fun _ : Fin 3 => fun _ : Fin 3 => -(N:ℝ)) (fun _ _ => (N:ℝ))) := by
    intro A hA
    obtain ⟨h1, -⟩ := hA
    rw [Set.mem_Icc]
    constructor <;> intro i j
    · have hle : |A i j| ≤ absSumPi A := by
        unfold absSumPi
        exact Finset.single_le_sum (f := fun p : Fin 3 × Fin 3 => |A p.1 p.2|)
          (fun p _ => abs_nonneg _) (Finset.mem_univ (i, j))
      exact (abs_le.mp (hle.trans h1)).1
    · have hle : |A i j| ≤ absSumPi A := by
        unfold absSumPi
        exact Finset.single_le_sum (f := fun p : Fin 3 × Fin 3 => |A p.1 p.2|)
          (fun p _ => abs_nonneg _) (Finset.mem_univ (i, j))
      exact (abs_le.mp (hle.trans h1)).2
  have hK : IsCompact ({A : Fin 3 → Fin 3 → ℝ | absSumPi A ≤ (N:ℝ)}
      ∩ {A : Fin 3 → Fin 3 → ℝ | Matrix.det A = 1}) :=
    IsCompact.of_isClosed_subset hbox hclosed hsub
  have hemb : Topology.IsClosedEmbedding (Subtype.val : SL3 → (Fin 3 → Fin 3 → ℝ)) :=
    Work.EKLRelCross.isClosed_SL3.isClosedEmbedding_subtypeVal
  have hKc := hemb.isCompact_preimage hK
  have hEq : {g : SL3 | absSumPi (g : Fin 3 → Fin 3 → ℝ) ≤ (N:ℝ)} =
      Subtype.val ⁻¹' ({A : Fin 3 → Fin 3 → ℝ | absSumPi A ≤ (N:ℝ)}
      ∩ {A : Fin 3 → Fin 3 → ℝ | Matrix.det A = 1}) := by
    ext g
    change absSumPi (g : Fin 3 → Fin 3 → ℝ) ≤ (N:ℝ) ↔
      absSumPi (g : Fin 3 → Fin 3 → ℝ) ≤ (N:ℝ) ∧ Matrix.det (g : Fin 3 → Fin 3 → ℝ) = 1
    exact ⟨fun h => ⟨h, g.2⟩, fun h => h.1⟩
  exact hEq ▸ hKc

/-- The set of matrices of `SL₃(ℝ)` with `absSum ≤ N` is compact. -/
theorem isCompact_absSum_le (N : ℕ) : IsCompact {g : SL3 | absSum g ≤ (N:ℝ)} :=
  isCompact_absSumPi_le N

/-! ## The countable family of test functions -/

/-- The (unbundled) test function at `(i,j,m,N)`. -/
def testFunFun (i j : Fin 3) (m N : ℕ) : SL3 → ℝ :=
  fun g => min 1 (max 0 (absEntry i j g - ((m:ℝ)+1)⁻¹)) * min 1 (max 0 ((N:ℝ) - absSum g))

theorem testFunFun_continuous (i j : Fin 3) (m N : ℕ) : Continuous (testFunFun i j m N) := by
  unfold testFunFun absEntry absSum absSumPi
  fun_prop

theorem testFunFun_hasCompactSupport (i j : Fin 3) (m N : ℕ) :
    HasCompactSupport (testFunFun i j m N) := by
  have hsupp : Function.support (testFunFun i j m N) ⊆ {g : SL3 | absSum g ≤ (N:ℝ)} := by
    intro g hg
    simp only [testFunFun, Function.mem_support, Set.mem_ofPred_eq, ne_eq] at hg ⊢
    by_contra hcon
    push Not at hcon
    have h2 : min 1 (max 0 ((N:ℝ) - absSum g)) = 0 := by
      rw [max_eq_left (by linarith), min_eq_right (by norm_num)]
    rw [h2, mul_zero] at hg
    exact hg rfl
  exact IsCompact.of_isClosed_subset (isCompact_absSum_le N) (isClosed_tsupport _)
    (closure_minimal hsupp (isClosed_le continuous_absSum continuous_const))

/-- **The test function** `f_{i,j,m,N}`: compactly supported, continuous, nonnegative, positive
exactly where `absEntry i j > 1/(m+1)` and `absSum < N`. -/
def testFun (i j : Fin 3) (m N : ℕ) : CompactlySupportedContinuousMap SL3 ℝ :=
  ⟨⟨testFunFun i j m N, testFunFun_continuous i j m N⟩, testFunFun_hasCompactSupport i j m N⟩

@[simp] theorem testFun_coe (i j : Fin 3) (m N : ℕ) (g : SL3) :
    testFun i j m N g = testFunFun i j m N g := rfl

theorem testFun_nonneg (i j : Fin 3) (m N : ℕ) (g : SL3) : 0 ≤ testFun i j m N g := by
  simp only [testFun_coe, testFunFun]
  positivity

theorem testFun_pos_iff (i j : Fin 3) (m N : ℕ) (g : SL3) :
    0 < testFun i j m N g ↔ ((m:ℝ)+1)⁻¹ < absEntry i j g ∧ absSum g < (N:ℝ) := by
  simp only [testFun_coe, testFunFun]
  constructor
  · intro h
    have h1 : 0 < min 1 (max 0 (absEntry i j g - ((m:ℝ)+1)⁻¹)) :=
      pos_of_mul_pos_left h (by positivity)
    have h2 : 0 < min 1 (max 0 ((N:ℝ) - absSum g)) :=
      pos_of_mul_pos_right h (by positivity)
    refine ⟨?_, ?_⟩
    · rcases lt_max_iff.mp (lt_min_iff.mp h1).2 with hh | hh
      · exact absurd hh (not_lt.mpr (by norm_num))
      · exact sub_pos.mp hh
    · rcases lt_max_iff.mp (lt_min_iff.mp h2).2 with hh | hh
      · exact absurd hh (not_lt.mpr (by norm_num))
      · exact sub_pos.mp hh
  · intro ⟨h1, h2⟩
    have h3 : 0 < min 1 (max 0 (absEntry i j g - ((m:ℝ)+1)⁻¹)) := by
      rw [lt_min_iff]; exact ⟨by norm_num, lt_max_of_lt_right (by linarith)⟩
    have h4 : 0 < min 1 (max 0 ((N:ℝ) - absSum g)) := by
      rw [lt_min_iff]; exact ⟨by norm_num, lt_max_of_lt_right (by linarith)⟩
    exact mul_pos h3 h4

/-- The support of the test function. -/
theorem testFun_support (i j : Fin 3) (m N : ℕ) :
    Function.support (testFun i j m N) =
      {g : SL3 | ((m:ℝ)+1)⁻¹ < absEntry i j g ∧ absSum g < (N:ℝ)} := by
  ext g
  rw [Function.mem_support, Set.mem_ofPred_eq, ne_eq]
  constructor
  · intro h
    exact (testFun_pos_iff i j m N g).mp (lt_of_le_of_ne (testFun_nonneg i j m N g) (Ne.symm h))
  · intro h
    exact ne_of_gt ((testFun_pos_iff i j m N g).mpr h)

/-! ## The positivity sets cover `{1}ᶜ` -/

/-- Every `g ≠ 1` lies in the positivity set of some test function: some entry of `g` differs from
that of `1`, and `absSum g` is finite. -/
theorem exists_testFun_pos {g : SL3} (hg : g ≠ 1) :
    ∃ (i j : Fin 3) (m N : ℕ), g ∈ Function.support (testFun i j m N) := by
  have hne : (g : Matrix (Fin 3) (Fin 3) ℝ) ≠ 1 := by
    intro h
    exact hg (Subtype.ext h)
  obtain ⟨i, j, hij⟩ : ∃ i j : Fin 3, (g : Matrix (Fin 3) (Fin 3) ℝ) i j ≠ (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
    by_contra h
    push Not at h
    exact hne (Matrix.ext fun i j => h i j)
  have hpos : 0 < absEntry i j g := by
    simp only [absEntry]; exact abs_pos.mpr (sub_ne_zero.mpr hij)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
  refine ⟨i, j, m, ⌈absSum g⌉₊ + 1, ?_⟩
  rw [testFun_support]
  refine ⟨?_, ?_⟩
  · have : ((m:ℝ)+1)⁻¹ = 1 / ((m:ℝ)+1) := by rw [one_div]
    rw [this]; exact hm
  · have h1 : absSum g ≤ ((⌈absSum g⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈absSum g⌉₊ : ℕ) : ℝ) < (((⌈absSum g⌉₊ + 1 : ℕ)) : ℝ) := by
      exact_mod_cast Nat.lt_succ_self _
    exact lt_of_le_of_lt h1 h2

/-! ## The measurable set whose a.e.-triviality is the dichotomy -/

/-- **The good set.**  `x ∈ goodSet ν X'` means `x ∈ X'` and every test function integrates to `0`
against `ν x`; equivalently (see `goodSet_subset_dirac`) `ν x = δ₁`. -/
def goodSet (ν : X3 → Measure SL3) (X' : Set X3) : Set X3 :=
  X' ∩ ⋂ (p : Fin 3 × Fin 3 × ℕ × ℕ),
    {x : X3 | ∫ g, testFun p.1 p.2.1 p.2.2.1 p.2.2.2 g ∂(ν x) = 0}

theorem measurableSet_goodSet {μ : Measure X3} {U : Subgroup SL3}
    {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ U ν X') :
    MeasurableSet (goodSet ν X') := by
  refine hL.meas_dom.inter ?_
  refine MeasurableSet.iInter fun p => ?_
  exact (hL.measurable (testFun p.1 p.2.1 p.2.2.1 p.2.2.2)) (measurableSet_singleton 0)

/-- If `ν x = δ₁` and `x ∈ X'` then `x` lies in the good set. -/
theorem mem_goodSet_of_dirac {ν : X3 → Measure SL3} {X' : Set X3}
    {x : X3} (hx : x ∈ X') (h : ν x = Measure.dirac 1) : x ∈ goodSet ν X' := by
  refine ⟨hx, ?_⟩
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  intro p
  rw [h, MeasureTheory.integral_dirac, testFun_coe]
  simp only [testFunFun, absEntry]
  have h0 : |(1 : SL3) p.1 p.2.1 - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2.1| = 0 := by simp
  rw [h0]
  have : max 0 (0 - ((p.2.2.1:ℝ)+1)⁻¹) = 0 := by
    rw [max_eq_left]; linarith [inv_nonneg.mpr (by positivity : (0:ℝ) ≤ (p.2.2.1:ℝ)+1)]
  rw [this]
  simp

end Work.EKLC6Core
