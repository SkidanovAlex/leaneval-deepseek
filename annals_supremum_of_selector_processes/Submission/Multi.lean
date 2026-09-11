import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep

/-!
# Multiset selector framework (Park--Pham, Section 6 / App A.2)

A multiset over a finite type `X` is a function `m : X → ℕ`.  For `p : X → ℝ≥0`
(a "measure" mass vector) the multinomial random multiset of size `N` has
`P(W = m) = N! · ∏_x p(x)^{m x} / (m x)!`.

Basic multiset algebra + `MSys` ("multi system") deep-fragment API.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Multi

variable {X : Type*} [Fintype X]

/-- multiset membership: x appears at least once -/
def memM (m : X → ℕ) (x : X) : Prop := 0 < m x

/-- multiset subset: pointwise ≤ -/
def subM (m m' : X → ℕ) : Prop := ∀ x, m x ≤ m' x

/-- size (total multiplicity) -/
noncomputable def sizeM (m : X → ℕ) : ℕ := ∑ x : X, m x

/-- disjoint union (pointwise sum) -/
def addM (m m' : X → ℕ) : X → ℕ := fun x => m x + m' x

/-- multiset difference (coordinatewise truncated) -/
def subMM (m m' : X → ℕ) : X → ℕ := fun x => m x - m' x

/-- intersection ∧ (pointwise min) -/
def minM (m m' : X → ℕ) : X → ℕ := fun x => min (m x) (m' x)

/-- union ∨ (pointwise max) -/
def maxM (m m' : X → ℕ) : X → ℕ := fun x => max (m x) (m' x)

/-- support (as a set) -/
noncomputable def supp (m : X → ℕ) : Set X := {x | 0 < m x}

lemma subM_refl (m : X → ℕ) : subM m m := fun x => le_rfl
lemma subM_of_le {m m' : X → ℕ} (h : ∀ x, m x ≤ m' x) : subM m m' := h
lemma le_of_subM {m m' : X → ℕ} (h : subM m m') (x : X) : m x ≤ m' x := h x

lemma subM_trans {m₁ m₂ m₃ : X → ℕ} (h12 : subM m₁ m₂) (h23 : subM m₂ m₃) : subM m₁ m₃ :=
  fun x => le_trans (h12 x) (h23 x)

lemma subM_antisymm {m m' : X → ℕ} (h1 : subM m m') (h2 : subM m' m) : m = m' := by
  funext x
  exact le_antisymm (h1 x) (h2 x)

lemma subM_add_left (m : X → ℕ) {m' m'' : X → ℕ} (h : subM m' m'') : subM m' (addM m m'') := by
  intro x; unfold addM; exact le_trans (h x) (Nat.le_add_left _ _)

lemma subM_add_right (m : X → ℕ) {m' m'' : X → ℕ} (h : subM m' m'') : subM m' (addM m'' m) := by
  intro x; unfold addM; exact le_trans (h x) (Nat.le_add_right _ _)

lemma addM_assoc (a b c : X → ℕ) : addM (addM a b) c = addM a (addM b c) := by
  funext x; unfold addM; omega

lemma addM_comm (a b : X → ℕ) : addM a b = addM b a := by
  funext x; unfold addM; omega

lemma sizeM_zero : sizeM (fun _ : X => 0) = 0 := by simp [sizeM]

lemma sizeM_add (m m' : X → ℕ) : sizeM (addM m m') = sizeM m + sizeM m' := by
  unfold sizeM addM
  rw [Finset.sum_add_distrib]

lemma sizeM_mono {m m' : X → ℕ} (h : subM m m') : sizeM m ≤ sizeM m' := by
  unfold sizeM
  exact Finset.sum_le_sum (by intro x hx; exact h x)

lemma sizeM_eq_zero {m : X → ℕ} (hm : ∀ x, m x = 0) : sizeM m = 0 := by
  unfold sizeM; simp [hm]

lemma sizeM_pos_iff {m : X → ℕ} : 0 < sizeM m ↔ ∃ x, 0 < m x := by
  unfold sizeM
  constructor
  · intro h
    unfold sizeM at h
    by_contra hne
    have hz : ∀ x, m x = 0 := by
      intro x
      by_contra hx
      exact hne ⟨x, Nat.pos_of_ne_zero hx⟩
    have hsum : (∑ x : X, m x) = 0 := by
      exact Finset.sum_eq_zero (by intro x hx; exact hz x)
    omega
  · rintro ⟨x, hx⟩
    exact lt_of_lt_of_le hx (Finset.single_le_sum (by intro y hy; exact Nat.zero_le _)
      (Finset.mem_univ x))

lemma mem_supp_iff {m : X → ℕ} {x : X} : x ∈ supp m ↔ 0 < m x := Iff.rfl

lemma subM_subMM {m m' : X → ℕ} : subM (subMM m m') m := by
  intro x; unfold subMM; omega

/-- if W ⊆ S then W + (S∖W) = S -/
lemma addM_subMM_cancel {W S : X → ℕ} (h : subM W S) : addM W (subMM S W) = S := by
  funext x
  unfold addM subMM
  exact Nat.add_sub_of_le (h x)

/-- fragment-subsets of S∖W are disjoint from S∖W when written against S -/
lemma subM_subMM_of_subM {S W : X → ℕ} {U : X → ℕ} (h : subM U (subMM S W)) :
    subM U S := by
  intro x
  unfold subMM at h
  exact le_trans (h x) (Nat.sub_le (S x) (W x))

lemma subMM_eq_zero_of_ge {S W : X → ℕ} (x : X) (h : S x ≤ W x) : subMM S W x = 0 := by
  simp [subMM, h]

lemma subMM_pos_of_subM {S W : X → ℕ} {x : X} (h : W x < S x) : 0 < subMM S W x := by
  simp [subMM, h]

lemma addM_subMM_eq_of_lt {S W : X → ℕ} (x : X) (h : W x < S x) :
    addM W (subMM S W) x = S x := by
  unfold addM subMM
  omega

/-- min/max basic -/
lemma subM_minM_left (a b : X → ℕ) : subM (minM a b) a := by
  intro x; unfold minM; exact min_le_left _ _

lemma subM_minM_right (a b : X → ℕ) : subM (minM a b) b := by
  intro x; unfold minM; exact min_le_right _ _

lemma minM_idem (a : X → ℕ) : minM a a = a := by
  funext x; unfold minM; simp

lemma minM_comm (a b : X → ℕ) : minM a b = minM b a := by
  funext x; unfold minM; omega

lemma subM_maxM_left (a b : X → ℕ) : subM a (maxM a b) := by
  intro x; unfold maxM; exact le_max_left _ _

lemma subM_maxM_right (a b : X → ℕ) : subM b (maxM a b) := by
  intro x; unfold maxM; exact le_max_right _ _

lemma maxM_le {a b c : X → ℕ} (hac : subM a c) (hbc : subM b c) : subM (maxM a b) c := by
  intro x; unfold maxM; exact max_le (hac x) (hbc x)

lemma sizeM_maxM_le_add (a b : X → ℕ) : sizeM (maxM a b) ≤ sizeM a + sizeM b := by
  calc
    sizeM (maxM a b) = ∑ x : X, max (a x) (b x) := rfl
    _ ≤ ∑ x : X, (a x + b x) := by
          exact Finset.sum_le_sum (by intro x hx; omega)
    _ = sizeM a + sizeM b := by simp [sizeM, Finset.sum_add_distrib]

lemma sizeM_minM_le (a b : X → ℕ) : sizeM (minM a b) ≤ sizeM a := sizeM_mono (subM_minM_left a b)

/-- (eNμ)-weighted cost of a single multiset -/
noncomputable def wCost (c : ℝ) (p : X → ℝ) (m : X → ℕ) : ℝ :=
  ∏ x : X, (c * p x) ^ m x / Nat.factorial (m x)

/-- cover by multisets: each family member contains a cover element -/
def mCover (𝓕 : Set (X → ℕ)) (𝓖 : Finset (X → ℕ)) : Prop :=
  ∀ S ∈ 𝓕, ∃ G ∈ 𝓖, subM G S

/-- total cost of a cover -/
noncomputable def mTotalCost (c : ℝ) (p : X → ℝ) (𝓖 : Finset (X → ℕ)) : ℝ :=
  ∑ G ∈ 𝓖, wCost c p G

/-- m-small: cover with total cost ≤ 1/2 -/
def mSmall (c : ℝ) (p : X → ℝ) (𝓕 : Set (X → ℕ)) : Prop :=
  ∃ 𝓖 : Finset (X → ℕ), mCover 𝓕 𝓖 ∧ mTotalCost c p 𝓖 ≤ (2 : ℝ)⁻¹

/-- wCost of the pointwise-zero multiset is 1 -/
lemma mTotalCost_nonneg {c : ℝ} (hc : 0 ≤ c) {p : X → ℝ} (hp : ∀ x, 0 ≤ p x)
    (𝓖 : Finset (X → ℕ)) : 0 ≤ mTotalCost c p 𝓖 := by
  unfold mTotalCost
  exact Finset.sum_nonneg (by
    intro G hG
    unfold wCost
    exact Finset.prod_nonneg (by
      intro x hx
      have h1 : 0 ≤ c * p x := mul_nonneg hc (hp x)
      positivity))

/-- multiset masses: M! · Π μ(x)^{m x}/(m x)!  (valid probability when Σμ=1 and sizeM m = M) -/
noncomputable def mass (M : ℕ) (μ : X → ℝ) (m : X → ℕ) : ℝ :=
  (Nat.factorial M : ℝ) * ∏ x : X, μ x ^ m x / Nat.factorial (m x)

lemma mass_nonneg (M : ℕ) {μ : X → ℝ} (hμ : ∀ x, 0 ≤ μ x) (m : X → ℕ) : 0 ≤ mass M μ m := by
  unfold mass
  exact mul_nonneg (by positivity) (Finset.prod_nonneg (by
    intro x hx
    have h1 : 0 ≤ μ x ^ m x := pow_nonneg (hμ x) _
    positivity))

/-- size-M multisets form a finite set -/
noncomputable def msizeFinset (M : ℕ) : Finset (X → ℕ) := by
  classical
  exact (Finset.univ : Finset (X → Fin (M + 1))).image
    (fun v : X → Fin (M + 1) => fun x : X => (v x).val)

/-- every size-M multiset is in the finset (bounded coordinate) -/
lemma mem_msizeFinset {m : X → ℕ} {M : ℕ} (h : sizeM m = M) : m ∈ msizeFinset (X := X) M := by
  classical
  unfold msizeFinset
  refine (Finset.mem_image).2 ⟨?_, Finset.mem_univ _, ?_⟩
  · intro x
    have hb : m x ≤ M := by
      have hle : m x ≤ sizeM m := Finset.single_le_sum (by intro y hy; exact Nat.zero_le _)
        (Finset.mem_univ x)
      omega
    exact ⟨m x, by omega⟩
  · funext x
    simp

/-- multisets of exact size M (the finset above may contain smaller ones) -/
noncomputable def msizeExact (M : ℕ) : Finset (X → ℕ) :=
  (msizeFinset (X := X) M).filter (fun m : X → ℕ => sizeM m = M)

lemma mem_msizeExact {m : X → ℕ} {M : ℕ} (h : sizeM m = M) : m ∈ msizeExact (X := X) M := by
  classical
  rw [msizeExact, Finset.mem_filter]
  exact ⟨mem_msizeFinset h, h⟩

lemma mem_msizeExact_iff {m : X → ℕ} {M : ℕ} : m ∈ msizeExact (X := X) M ↔ sizeM m = M := by
  classical
  rw [msizeExact, Finset.mem_filter]
  constructor
  · intro hm; exact hm.2
  · intro h; exact ⟨mem_msizeFinset h, h⟩

/-- sums over all size-M multisets -/
noncomputable def mspaceSum {β : Type*} [AddCommMonoid β] (M : ℕ) (v : (X → ℕ) → β) : β :=
  ∑ m ∈ msizeExact (X := X) M, v m

/-- every finite multiset family has bounded size -/
lemma sizeM_le_of_finite {𝓕 : Set (X → ℕ)} (hF : Set.Finite 𝓕) :
    ∃ B : ℕ, ∀ S ∈ 𝓕, sizeM S ≤ B := by
  classical
  let l : Finset (X → ℕ) := hF.toFinset
  refine ⟨∑ S ∈ l, sizeM S, ?_⟩
  intro S hS
  have hmem : S ∈ l := by
    exact hF.mem_toFinset.mpr hS
  exact Finset.single_le_sum (by intro y hy; exact Nat.zero_le _) hmem

lemma sizeM_subMM_le (S W : X → ℕ) : sizeM (subMM S W) ≤ sizeM S := by
  exact sizeM_mono (subM_subMM (m := S) (m' := W))

/-- U with one copy of x removed -/
noncomputable def eraseOne (U : X → ℕ) (x : X) : X → ℕ :=
  fun y => if y = x then U x - 1 else U y

lemma eraseOne_self (U : X → ℕ) (x : X) : eraseOne U x x = U x - 1 := by simp [eraseOne]
lemma eraseOne_other (U : X → ℕ) {x y : X} (h : y ≠ x) : eraseOne U x y = U y := by simp [eraseOne, h]
lemma subM_eraseOne (U : X → ℕ) (x : X) : subM (eraseOne U x) U := by
  intro y
  by_cases hy : y = x
  · subst y; simp [eraseOne]
  · simp [eraseOne, hy]

lemma sizeM_eraseOne_add (U : X → ℕ) (x : X) (hx : 0 < U x) :
    sizeM (eraseOne U x) + 1 = sizeM U := by
  classical
  unfold sizeM eraseOne
  have hs : (∑ y : X, if y = x then U x - 1 else U y) =
      (U x - 1) + (∑ y ∈ (Finset.univ.erase x), U y) := by
    calc
      (∑ y : X, if y = x then U x - 1 else U y)
          = (∑ y ∈ ({x} : Finset X), if y = x then U x - 1 else U y)
              + (∑ y ∈ (Finset.univ.erase x), if y = x then U x - 1 else U y) := by
            rw [← Finset.sum_union]
            · congr 1
              ext y
              by_cases hy : y = x <;> simp [hy]
            · simp
      _ = (U x - 1) + (∑ y ∈ (Finset.univ.erase x), U y) := by
            simp
            apply Finset.sum_congr rfl
            intro y hy
            have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
            simp [hyx]
  have ht : (∑ y : X, U y) = U x + (∑ y ∈ (Finset.univ.erase x), U y) := by
    calc
      (∑ y : X, U y)
          = (∑ y ∈ ({x} : Finset X), U y) + (∑ y ∈ (Finset.univ.erase x), U y) := by
            rw [← Finset.sum_union]
            · congr 1
              ext y
              by_cases hy : y = x <;> simp [hy]
            · simp
      _ = U x + (∑ y ∈ (Finset.univ.erase x), U y) := by simp
  calc
    (∑ y : X, if y = x then U x - 1 else U y) + 1
        = (U x - 1) + (∑ y ∈ (Finset.univ.erase x), U y) + 1 := by rw [hs]
    _ = U x + (∑ y ∈ (Finset.univ.erase x), U y) := by omega
    _ = ∑ y : X, U y := by rw [ht]

lemma sizeM_eraseOne (U : X → ℕ) (x : X) (hx : 0 < U x) :
    sizeM (eraseOne U x) = sizeM U - 1 := by
  have h := sizeM_eraseOne_add U x hx
  omega


/-- splitting a univ-sum at coordinate x -/
lemma sum_univ_singleton_add {β : Type*} [AddCommMonoid β] (f : X → β) (x : X) :
    (∑ y : X, f y) = f x + (∑ y ∈ (Finset.univ.erase x), f y) := by
  classical
  calc
    (∑ y : X, f y)
        = (∑ y ∈ ({x} : Finset X), f y) + (∑ y ∈ (Finset.univ.erase x), f y) := by
          rw [← Finset.sum_union]
          · congr 1
            ext y
            by_cases hy : y = x <;> simp [hy]
          · simp
    _ = f x + (∑ y ∈ (Finset.univ.erase x), f y) := by simp

end Multi
end Submission
