import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A uniform positive-definiteness margin for a quadratically perturbed PSD form

Given two matrices `MA`, `MB : Fin n → Fin n → ℝ` such that

* `A v = ∑ᵢ ∑ⱼ MA i j * v i * v j` is nonnegative for every `v` (`A` is positive semidefinite), and
* `B v = ∑ᵢ ∑ⱼ MB i j * v i * v j` is strictly positive on every **nonzero** vector of the kernel of
  `A`,

we show that there is `ε > 0` such that for every `s ∈ (0, ε]` the perturbed form `A + s·B` is
positive definite, **uniformly** in the sense that there is a positive constant `m` (depending on
`s`) with `m * ‖v‖² ≤ A v + s * B v` for every `v`.

The proof goes through the compactness of the unit sphere: `v ↦ A v` is nonnegative and vanishes
only on the kernel, on which `B > 0`, and the perturbations stay positive for small `s` by
compactness; then the minimum of `A + s·B` over the unit sphere is positive.
-/

namespace Work.Diff.Alg.Pinch

/-- The quadratic form `v ↦ ∑ᵢ ∑ⱼ Mᵢⱼ vᵢ vⱼ` attached to a matrix `M`. -/
def quad {n : ℕ} (M : Fin n → Fin n → ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, M i j * v i * v j

/-- The squared Euclidean norm `∑ᵢ vᵢ²` on `Fin n → ℝ`. -/
def normSq {n : ℕ} (v : Fin n → ℝ) : ℝ := ∑ i, v i * v i

lemma continuous_quad {n : ℕ} (M : Fin n → Fin n → ℝ) : Continuous (quad M) := by
  unfold quad
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact (continuous_const.mul (continuous_apply i)).mul (continuous_apply j)

lemma continuous_normSq {n : ℕ} : Continuous (normSq (n := n)) := by
  unfold normSq
  apply continuous_finsetSum
  intro i _
  exact (continuous_apply i).mul (continuous_apply i)

lemma quad_smul {n : ℕ} (M : Fin n → Fin n → ℝ) (c : ℝ) (v : Fin n → ℝ) :
    quad M (c • v) = c ^ 2 * quad M v := by
  unfold quad
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma normSq_smul {n : ℕ} (c : ℝ) (v : Fin n → ℝ) :
    normSq (c • v) = c ^ 2 * normSq v := by
  unfold normSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma normSq_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ normSq v := by
  unfold normSq
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

lemma normSq_eq_zero_iff {n : ℕ} (v : Fin n → ℝ) : normSq v = 0 ↔ v = 0 := by
  unfold normSq
  constructor
  · intro h
    funext i
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ v j * v j := fun j _ => mul_self_nonneg (v j)
    have hi : v i * v i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h i (Finset.mem_univ i)
    exact mul_self_eq_zero.mp hi
  · intro h; simp [h]

lemma normSq_pos {n : ℕ} {v : Fin n → ℝ} (hv : v ≠ 0) : 0 < normSq v :=
  lt_of_le_of_ne (normSq_nonneg v) (fun h => hv ((normSq_eq_zero_iff v).mp h.symm))

/-- The unit `normSq`-sphere in `Fin n → ℝ` is compact. -/
theorem isCompact_normSq_eq_one (n : ℕ) : IsCompact {v : Fin n → ℝ | normSq v = 1} := by
  have hclosed : IsClosed {v : Fin n → ℝ | normSq v = 1} :=
    IsClosed.preimage continuous_normSq (isClosed_singleton (x := (1 : ℝ)))
  refine IsCompact.of_isClosed_subset
    (s := Set.Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1))
    (t := {v : Fin n → ℝ | normSq v = 1}) isCompact_Icc hclosed ?_
  intro v hv
  have hv' : normSq v = 1 := hv
  simp only [Set.mem_Icc, Pi.le_def]
  have hle : ∀ i, v i * v i ≤ normSq v := by
    intro i
    unfold normSq
    exact Finset.single_le_sum (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i)
  constructor
  · intro i
    have h : v i * v i ≤ 1 := by linarith [hle i, hv']
    have h2 : v i ^ 2 ≤ (1 : ℝ) ^ 2 := by rw [one_pow, pow_two]; exact h
    exact (abs_le_of_sq_le_sq' h2 zero_le_one).1
  · intro i
    have h : v i * v i ≤ 1 := by linarith [hle i, hv']
    have h2 : v i ^ 2 ≤ (1 : ℝ) ^ 2 := by rw [one_pow, pow_two]; exact h
    exact (abs_le_of_sq_le_sq' h2 zero_le_one).2

/-- **Compactness lemma.**  On a compact space, if `r ≥ 0` is continuous and `q` is continuous
and strictly positive on the zero set of `r`, then `r + s * q` is uniformly positive for all
sufficiently small `s > 0`. -/
theorem exists_eps_margin_compact {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (r q : X → ℝ) (hr : Continuous r) (hq : Continuous q) (hr0 : ∀ x, 0 ≤ r x)
    (hK : ∀ x, r x = 0 → 0 < q x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s ≤ ε →
      ∃ m : ℝ, 0 < m ∧ ∀ x : X, m ≤ r x + s * q x := by
  have key : ∀ t : ℝ, 0 < t → (∀ x, 0 < r x + t * q x) →
      ∃ m : ℝ, 0 < m ∧ ∀ x : X, m ≤ r x + t * q x := by
    intro t ht hpos
    obtain ⟨m, hm, hle⟩ := IsCompact.exists_forall_le' (s := Set.univ)
      (f := fun x => r x + t * q x) isCompact_univ
      ((hr.add (hq.const_mul t)).continuousOn) (a := 0) (fun x _ => hpos x)
    exact ⟨m, hm, fun x => hle x (Set.mem_univ x)⟩
  rcases (Set.eq_empty_or_nonempty ({x : X | q x ≤ 0} : Set X)) with hC | hCne
  · refine ⟨1, one_pos, fun t ht _ => key t ht (fun x => ?_)⟩
    have hqx : 0 < q x := by
      by_contra h
      have hle : q x ≤ 0 := not_lt.mp h
      have hmem : x ∈ ({y : X | q y ≤ 0} : Set X) := hle
      rw [hC] at hmem
      exact hmem
    nlinarith [hr0 x, mul_pos ht hqx]
  · have hCclosed : IsClosed ({x : X | q x ≤ 0} : Set X) := isClosed_le hq continuous_const
    have hCcompact : IsCompact ({x : X | q x ≤ 0} : Set X) :=
      IsCompact.of_isClosed_subset isCompact_univ hCclosed (Set.subset_univ _)
    have hrposC : ∀ x ∈ ({y : X | q y ≤ 0} : Set X), 0 < r x := by
      intro x hx
      rcases lt_or_eq_of_le (hr0 x) with h | h
      · exact h
      · exact absurd hx (not_le.mpr (hK x h.symm))
    obtain ⟨α, hαpos, hαle⟩ := IsCompact.exists_forall_le' (s := ({y : X | q y ≤ 0} : Set X))
      (f := r) hCcompact hr.continuousOn (a := 0) hrposC
    obtain ⟨x₁, _, hx₁⟩ := IsCompact.exists_isMaxOn (s := ({y : X | q y ≤ 0} : Set X))
      (f := fun y => -q y) hCcompact hCne (hq.neg.continuousOn)
    rw [isMaxOn_iff] at hx₁
    set B0 : ℝ := max (-q x₁) 0 with hB0
    have hB0nn : 0 ≤ B0 := by rw [hB0]; exact le_max_right _ _
    have hbound : ∀ y ∈ ({y : X | q y ≤ 0} : Set X), -B0 ≤ q y := by
      intro y hy
      have h1 : -q y ≤ B0 := by
        rw [hB0]
        exact le_trans (hx₁ y hy) (le_max_left _ _)
      linarith
    have hden : (0 : ℝ) < 2 * (B0 + 1) := by nlinarith
    refine ⟨α / (2 * (B0 + 1)), div_pos hαpos hden, fun t ht hte => key t ht (fun x => ?_)⟩
    by_cases hqx : q x ≤ 0
    · have h1 : α ≤ r x := hαle x hqx
      have h2 : -B0 ≤ q x := hbound x hqx
      have h4 : (α / (2 * (B0 + 1))) * B0 ≤ α / 2 := by
        rw [div_mul_eq_mul_div]
        rw [div_le_div_iff₀ hden two_pos]
        nlinarith [hαpos]
      have hsB : t * B0 ≤ α / 2 :=
        le_trans (mul_le_mul_of_nonneg_right hte hB0nn) h4
      have h3 : -(t * B0) ≤ t * q x := by
        have := mul_le_mul_of_nonneg_left h2 ht.le
        linarith
      linarith
    · have hqpos : 0 < q x := not_le.mp hqx
      nlinarith [hr0 x, mul_pos ht hqpos]

theorem exists_eps_margin_quad (n : ℕ) (hn : 1 ≤ n) (MA MB : Fin n → Fin n → ℝ)
    (hA : ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, MA i j * v i * v j)
    (hAB : ∀ v : Fin n → ℝ, v ≠ 0 → (∑ i, ∑ j, MA i j * v i * v j) = 0 →
      0 < ∑ i, ∑ j, MB i j * v i * v j) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s ≤ ε →
      ∃ m : ℝ, 0 < m ∧ ∀ v : Fin n → ℝ,
        m * (∑ i, v i * v i)
          ≤ (∑ i, ∑ j, MA i j * v i * v j) + s * (∑ i, ∑ j, MB i j * v i * v j) := by
  have hScompact : IsCompact ({v : Fin n → ℝ | normSq v = 1}) := isCompact_normSq_eq_one n
  haveI : CompactSpace {v : Fin n → ℝ | normSq v = 1} := isCompact_iff_compactSpace.mp hScompact
  obtain ⟨ε, hεpos, hε⟩ := exists_eps_margin_compact
    (X := {v : Fin n → ℝ | normSq v = 1})
    (fun u => quad MA u.1) (fun u => quad MB u.1)
    ((continuous_quad MA).comp continuous_subtype_val)
    ((continuous_quad MB).comp continuous_subtype_val)
    (fun u => hA u.1)
    (fun u hu => by
      have hune : u.1 ≠ 0 := by
        intro h
        have h1 : normSq u.1 = 0 := by rw [h]; simp [normSq]
        have : (0 : ℝ) = 1 := h1 ▸ u.2
        exact zero_ne_one this
      exact hAB u.1 hune hu)
  refine ⟨ε, hεpos, fun s hs hse => ?_⟩
  obtain ⟨m, hmpos, hmm⟩ := hε s hs hse
  refine ⟨m, hmpos, fun v => ?_⟩
  show m * normSq v ≤ quad MA v + s * quad MB v
  rcases eq_or_ne v 0 with rfl | hv0
  · simp [normSq, quad]
  · set c : ℝ := Real.sqrt (normSq v) with hc
    have hcpos : 0 < c := Real.sqrt_pos.mpr (normSq_pos hv0)
    have hcne : c ≠ 0 := ne_of_gt hcpos
    have hc2 : c ^ 2 = normSq v := Real.sq_sqrt (normSq_nonneg v)
    set w : Fin n → ℝ := c⁻¹ • v with hw
    have hwS : normSq w = 1 := by
      rw [hw, normSq_smul, ← hc2, ← mul_pow, inv_mul_cancel₀ hcne, one_pow]
    have hcw : c • w = v := by
      rw [hw, smul_smul, mul_inv_cancel₀ hcne, one_smul]
    have hvA : quad MA v = c ^ 2 * quad MA w := by rw [← hcw, quad_smul]
    have hvB : quad MB v = c ^ 2 * quad MB w := by rw [← hcw, quad_smul]
    have hmmw : m ≤ quad MA w + s * quad MB w := hmm ⟨w, hwS⟩
    calc m * normSq v = c ^ 2 * m := by rw [hc2]; ring
      _ ≤ c ^ 2 * (quad MA w + s * quad MB w) :=
            mul_le_mul_of_nonneg_left hmmw (sq_nonneg c)
      _ = quad MA v + s * quad MB v := by rw [hvA, hvB]; ring

end Work.Diff.Alg.Pinch
