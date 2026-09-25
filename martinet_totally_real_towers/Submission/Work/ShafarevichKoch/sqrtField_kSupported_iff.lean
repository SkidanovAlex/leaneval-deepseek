import Mathlib
import Submission.Work.ShafarevichKoch.sqrtField
import Submission.Work.ShafarevichKoch.kEmptyMaximalProP
import Submission.Work.ShafarevichKoch.VTwoUnramified
import Submission.Work.ShafarevichKoch.VTwo_eq_VTwoUnramified_sup_neg_one_Kc
import Submission.Work.QuadraticFields.sqClass_eq_zero_iff
import Submission.Work.ClassFieldTower.All

/-!
# `Work.ShafarevichKoch.sqrtField_kSupported_iff` -- the `κ`-triviality criterion

README §32.1/§32.3 defines the Kummer field `sqrtField x = K_∅(√x)` and records that it is Galois
over `Kc`.  The next elementary piece of the `κ`-route is the *triviality criterion*: the
extension `K_∅(√x)/K_∅` is trivial (i.e. `x` has a square root in `K_∅`, i.e. `√x` lies in the
maximal unramified pro-`2` extension) exactly when `x` lies in the chapter's *unramified Kummer
radical* `VTwoUnramified Kc M`.

## Main declarations

* `Work.ShafarevichKoch.adjoin_sqRoot_le_iff` -- the general field-theoretic criterion: for a field
  extension `E/F` with `E` algebraically closed, an intermediate field `K` contains all square roots
  of `x : F` iff `x` has a square root in `K`;
* `Work.ShafarevichKoch.sqrtField_eq_kSupported_iff` -- `K_∅(√x) = K_∅` iff `x` has a square root
  in `K_∅`;
* `Work.ShafarevichKoch.mem_VTwoUnramified_kEmpty_iff_sqrtField_eq` -- for `x ∈ Kcˣ`:
  `x ∈ V^{unr} ↔ sqrtField x = k_∅`;
* `Work.ShafarevichKoch.sqrtField_neg_one_ne_kSupported` -- the class of `-1` is *not* trivial;
* `Work.ShafarevichKoch.sqrtField_eq_kSupported_or` -- **the `κ`-route carries only one dimension**:
  for every `x ∈ V_∅ = VTwo Kc` the extension `K_∅(√x)/K_∅` is either trivial or the one cut out by
  `-1`.  Equivalently the extension-class map `κ` of README §32.1 takes at most two values, so it
  cannot by itself bound `#H²_cont(G_∅,𝔽₂)`; see README §33.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-! ## 1. The general criterion -/

section General

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- **When does an intermediate field contain the square roots of `x`?**  It contains *all* of them
if and only if `x` itself has a square root in it (over an algebraically closed ambient field).
The forward implication uses `IsAlgClosed.exists_eq_mul_self` to produce a square root of `x` in
`E`; the converse is the elementary fact that the two roots of `X² - x` are `±√x`. -/
theorem adjoin_sqRoot_le_iff (K : IntermediateField F E) (x : F) [IsAlgClosed E] :
    IntermediateField.adjoin F {y : E | y ^ 2 = algebraMap F E x} ≤ K ↔
      ∃ y : K, y ^ 2 = algebraMap F K x := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self (algebraMap F E x)
    have hzmem : z ^ 2 = algebraMap F E x := by rw [pow_two]; exact hz.symm
    have hzK : z ∈ K :=
      h (IntermediateField.subset_adjoin F {y : E | y ^ 2 = algebraMap F E x} hzmem)
    exact ⟨⟨z, hzK⟩, Subtype.ext hzmem⟩
  · rintro ⟨y, hy⟩
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    have hzE : z ^ 2 = algebraMap F E x := hz
    have hyE : (y : E) ^ 2 = algebraMap F E x := by
      have h1 : ((y ^ 2 : K) : E) = (y : E) ^ 2 := rfl
      have h2 : ((algebraMap F K x : K) : E) = algebraMap F E x := rfl
      rw [← h1, ← h2, hy]
    have hzz' : z ^ 2 = (y : E) ^ 2 := by rw [hzE, hyE]
    have hzz : z * z = (y : E) * (y : E) := by
      rw [pow_two] at hzz'
      simpa only [pow_two] using hzz'
    rcases mul_self_eq_mul_self_iff.mp hzz with h' | h'
    · rw [h']; exact y.2
    · rw [h']; exact K.neg_mem y.2

end General

/-! ## 2. The Kummer field of `Kc` -/

/-- **The triviality criterion for the Kummer field**: `K_∅(√x) = K_∅` if and only if `x` has a
square root inside the maximal unramified pro-`2` extension `K_∅ = kSupported Kc 2 ∅`. -/
theorem sqrtField_eq_kSupported_iff (x : Kc) :
    sqrtField x = kSupported Kc 2 (∅ : Finset ℕ) ↔
      ∃ y : ↥(kSupported Kc 2 (∅ : Finset ℕ)), y ^ 2 = algebraMap Kc _ x :=
  sup_eq_left.trans
    (adjoin_sqRoot_le_iff (K := kSupported Kc 2 (∅ : Finset ℕ)) (x := x))

/-- The triviality criterion, in the direction that is used: a square root of `x` inside `K_∅`
makes the Kummer field collapse. -/
theorem sqrtField_eq_kSupported_of_sq
    (x : Kc) (y : ↥(kSupported Kc 2 (∅ : Finset ℕ))) (hy : y ^ 2 = algebraMap Kc _ x) :
    sqrtField x = kSupported Kc 2 (∅ : Finset ℕ) :=
  (sqrtField_eq_kSupported_iff x).mpr ⟨y, hy⟩

/-- **`x ∈ V^{unr} ↔ K_∅(√x) = K_∅`**: the elementwise form of the triviality criterion, matching
the chapter's definition of the unramified Kummer radical (`VTwoUnramified`). -/
theorem mem_VTwoUnramified_kEmpty_iff_sqrtField_eq (x : Kcˣ) :
    x ∈ VTwoUnramified Kc (kEmptyMaximalProP Kc) ↔
      sqrtField ((x : Kcˣ) : Kc) = kSupported Kc 2 (∅ : Finset ℕ) := by
  rw [sqrtField_eq_kSupported_iff]
  change (∃ b : ↥(kSupported Kc 2 (∅ : Finset ℕ)), b ≠ 0 ∧
      b * b = algebraMap Kc ↥(kSupported Kc 2 (∅ : Finset ℕ)) ((x : Kcˣ) : Kc)) ↔
    (∃ y : ↥(kSupported Kc 2 (∅ : Finset ℕ)), y ^ 2 = algebraMap Kc _ ((x : Kcˣ) : Kc))
  constructor
  · rintro ⟨b, _hb0, hb⟩
    exact ⟨b, by rw [pow_two]; exact hb⟩
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_, ?_⟩
    · rintro rfl
      refine Units.ne_zero x ((algebraMap Kc ↥(kSupported Kc 2 (∅ : Finset ℕ))).injective ?_)
      rw [pow_two] at hb
      simpa using hb.symm
    · rw [pow_two] at hb
      exact hb

/-- **The square root of a square lies in `K_∅`**: `K_∅(√(x²)) = K_∅`, so the whole square class of
`x` is invisible to the `κ`-map. -/
theorem sqrtField_mul_self (x : Kc) :
    sqrtField (x * x) = kSupported Kc 2 (∅ : Finset ℕ) :=
  sqrtField_eq_kSupported_of_sq (x * x)
    (algebraMap Kc ↥(kSupported Kc 2 (∅ : Finset ℕ)) x) (by rw [pow_two, ← map_mul])

/-- **The class of `-1` is not trivial**: `√-1 ∉ K_∅`, because `Kc(√-1)/Kc` is ramified at the prime
over `2` (`no_sqrt_neg_one_in_maximalUnramified`). -/
theorem sqrtField_neg_one_ne_kSupported :
    sqrtField (-1 : Kc) ≠ kSupported Kc 2 (∅ : Finset ℕ) := by
  intro h
  obtain ⟨y, hy⟩ := (sqrtField_eq_kSupported_iff (-1 : Kc)).mp h
  rw [pow_two] at hy
  refine no_sqrt_neg_one_in_maximalUnramified (kEmptyMaximalProP Kc) ⟨?_b, ?_h⟩
  · exact y
  · show (y : (kEmptyMaximalProP Kc).K) * (y : (kEmptyMaximalProP Kc).K) = algebraMap Kc _ (-1 : Kc)
    exact hy

/-- **The two elements of `⟨-1⟩`**: in a commutative group, the subgroup generated by an involution
has exactly the two elements `1` and `-1`. -/
lemma closure_neg_one_eq_one_or (k : Kcˣ)
    (hk : k ∈ Subgroup.closure ({(-1 : Kcˣ)} : Set Kcˣ)) : k = 1 ∨ k = -1 := by
  rw [Subgroup.mem_closure_singleton] at hk
  obtain ⟨n, rfl⟩ := hk
  have h2 : ((-1 : Kcˣ) ^ (2 : ℤ)) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, neg_mul_neg, one_mul]
  rcases Int.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [show m + m = 2 * m by ring, zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

/-- **The `κ`-map carries at most one dimension.**  Every `x` of Koch's radical `V_∅ = VTwo Kc`
has `K_∅(√x) = K_∅` or `K_∅(√(-x)) = K_∅`, i.e. the extension class of `K_∅(√x)/K_∅` is either
trivial or the class of `-1`.  (This is the formal content of the correction recorded in README
§33: the "extension-class" form of the `κ`-route cannot bound `H²_cont(G_∅,𝔽₂)`.) -/
theorem sqrtField_eq_kSupported_or (x : Kcˣ) (hx : x ∈ VTwo Kc) :
    sqrtField ((x : Kcˣ) : Kc) = kSupported Kc 2 (∅ : Finset ℕ) ∨
      sqrtField ((-(x : Kcˣ) : Kcˣ) : Kc) = kSupported Kc 2 (∅ : Finset ℕ) := by
  have hle : VTwo Kc ≤ VTwoUnramified Kc (kEmptyMaximalProP Kc) ⊔
      Subgroup.closure ({(-1 : Kcˣ)} : Set Kcˣ) := by
    rw [VTwo_eq_VTwoUnramified_sup_neg_one_Kc (kEmptyMaximalProP Kc)]
    rw [sup_le_iff]
    refine ⟨le_rfl, ?_⟩
    intro s hs
    obtain ⟨y, hy⟩ := (Work.QuadraticFields.mem_squareSubgroup_iff).mp hs
    rw [← hy]
    exact Subgroup.mem_sup_left (sq_mem_VTwoUnramified Kc (kEmptyMaximalProP Kc) y)
  obtain ⟨h, hh, k, hk, hk_eq⟩ := Subgroup.mem_sup.mp (hle hx)
  rcases closure_neg_one_eq_one_or k hk with rfl | rfl
  · left
    rw [mul_one] at hk_eq
    rw [← hk_eq]
    exact (mem_VTwoUnramified_kEmpty_iff_sqrtField_eq h).mp hh
  · right
    rw [← hk_eq]
    have hneg : (-(h * (-1 : Kcˣ)) : Kcˣ) = h := by rw [mul_neg, neg_neg, mul_one]
    rw [hneg]
    exact (mem_VTwoUnramified_kEmpty_iff_sqrtField_eq h).mp hh

end Work.ShafarevichKoch
