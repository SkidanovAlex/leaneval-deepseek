import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseBoxFock.theta_window
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.window_ops` — the model's excited-window algebra

The model side of the box ↔ model bridge (`box_to_model`, BF3).  `ExcWindow 𝓜 n` is the
class of Fock vectors that FS's §9–§11 arguments (and therefore both `box_to_model` and
`model_kafz`) quantify over; here it is put into the concrete form the bridge needs:

* `deg α` is the total occupation `|α|`, and `nExc` acts diagonally on the monomials with
  eigenvalue `deg α - α 0` (`nExc_apply`), so

      `ExcWindow M n Ψ ↔ supp Ψ ⊆ {α : |α| ≤ n} ∩ {α : |α| - α 0 ≤ ⌊M⌋₊}`
      (`excwindow_iff`),

  i.e. the window is a **coordinate subspace of `RealFock m`**.  This makes `Ψ ≠ 0 ∧
  ExcWindow 𝓜 n Ψ` a checkable condition on the coefficient vector, and it is what lets an
  all-moments bound on the box state (`SpectralNPlusLe`) transfer to the model vector;
* the window is closed under `+`, `•`, monotone in both `M` and `n`, and contains `0`
  (`excwindow_add`, `excwindow_smul`, `excwindow_mono`, `excwindow_zero`) — used to move
  between the thresholds of `box_to_model` (`𝓜`) and of the §6/§9 gluing (`𝓜/2`, `𝓜/4`).

Everything is `sorry`-free and rests on `propext, Classical.choice, Quot.sound`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false

/-! ## 1. The occupation degrees of a multi-index -/

/-- The total occupation `|α| = Σ_i α_i`. -/
def deg {m : ℕ} (α : Fin m →₀ ℕ) : ℕ := α.sum fun _ k => k

/-- `|α|` as a sum over all coordinate indices (the support sum is the full sum). -/
lemma deg_eq_sum {m : ℕ} (α : Fin m →₀ ℕ) : deg α = ∑ i : Fin m, α i := by
  rw [deg, Finsupp.sum]
  exact Finset.sum_subset (Finset.subset_univ _) fun i _ hi =>
    by rw [Finsupp.notMem_support_iff.mp hi]

/-- Each occupation number is at most the total occupation. -/
lemma apply_le_deg {m : ℕ} (α : Fin m →₀ ℕ) (i : Fin m) : α i ≤ deg α := by
  rw [deg_eq_sum]
  exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)

/-! ## 2. `nExc` acts diagonally on the monomials -/

/-- A finitely supported function is the sum of its monomials. -/
lemma sum_single_support {m : ℕ} (Ψ : RealFock m) :
    (∑ α ∈ Ψ.support, Finsupp.single α (Ψ α)) = Ψ := by
  ext β
  rw [Finsupp.finsetSum_apply]
  by_cases hβ : β ∈ Ψ.support
  · rw [Finset.sum_eq_single β]
    · exact Finsupp.single_eq_same
    · intro b _ hb
      exact Finsupp.single_eq_of_ne (Ne.symm hb)
    · intro h
      exact absurd hβ h
  · rw [Finset.sum_eq_zero]
    · exact (Finsupp.notMem_support_iff.mp hβ).symm
    · intro a ha
      by_cases hab : a = β
      · exact absurd (hab ▸ ha) hβ
      · exact Finsupp.single_eq_of_ne (fun h : β = a => hab h.symm)

/-- **`nExc` acts diagonally on the monomials**: the eigenvalue is the *excited* occupation
`|α| - α 0`.  This is the model counterpart of the box identity `n₊ = N - n₀`. -/
lemma nExc_single_deg {m : ℕ} [NeZero m] (α : Fin m →₀ ℕ) :
    nExc (m := m) (Finsupp.single α (1 : ℝ))
      = ((deg α - α 0 : ℕ) : ℝ) • Finsupp.single α (1 : ℝ) := by
  rw [nExc, LinearMap.sub_apply, totNumOp_single, n0_single, ← sub_smul, deg_eq_sum,
    Nat.cast_sub (Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ (0 : Fin m))),
    Nat.cast_sum]

/-- **`nExc` acts diagonally on all monomial components.** -/
lemma nExc_apply {m : ℕ} [NeZero m] (Ψ : RealFock m) (α : Fin m →₀ ℕ) :
    (nExc (m := m) Ψ) α = ((deg α - α 0 : ℕ) : ℝ) * Ψ α := by
  conv_lhs => rw [← sum_single_support Ψ]
  rw [map_sum, Finsupp.finsetSum_apply]
  have hterm : ∀ b ∈ Ψ.support,
      (nExc (m := m) (Finsupp.single b (Ψ b))) α
        = (if b = α then ((deg α - α 0 : ℕ) : ℝ) * Ψ α else 0) := by
    intro b _
    have hb : Finsupp.single b (Ψ b) = (Ψ b) • Finsupp.single b (1 : ℝ) := by
      rw [Finsupp.smul_single]; simp
    rw [hb, map_smul, nExc_single_deg]
    rw [Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul]
    by_cases hba : b = α
    · subst hba
      rw [if_pos rfl, Finsupp.single_eq_same]
      ring
    · rw [if_neg hba, Finsupp.single_eq_of_ne (Ne.symm hba)]
      ring
  rw [Finset.sum_congr rfl hterm]
  by_cases hα : α ∈ Ψ.support
  · rw [Finset.sum_eq_single α]
    · simp
    · intro b _ hb
      exact if_neg (fun h : b = α => hb h)
    · intro h
      exact absurd hα h
  · rw [Finset.sum_eq_zero]
    · rw [Finsupp.notMem_support_iff.mp hα, mul_zero]
    · intro b hb
      exact if_neg (fun h : b = α => hα (h ▸ hb))

/-! ## 3. The eigenvalue components of a Fock vector -/

/-- The `j`-th excited component of `Ψ`: the part of `Ψ` carried by the monomials with
`|α| - α 0 = j`. -/
def excPart {m : ℕ} [NeZero m] (j : ℕ) (Ψ : RealFock m) : RealFock m :=
  ∑ α ∈ Ψ.support.filter (fun α => deg α - α 0 = j), Finsupp.single α (Ψ α)

/-- The iterates of `nExc` on Fock vectors (`nExcPow 0 = id`, `nExcPow (j+1) = nExc ∘
nExcPow j`); used to state the moment bounds of the window. -/
def nExcPow {m : ℕ} [NeZero m] : ℕ → RealFock m → RealFock m
  | 0, Ψ => Ψ
  | (j + 1), Ψ => nExc (nExcPow j Ψ)

/-- Each `excPart j Ψ` is an eigenvector of `nExc` with eigenvalue `j`. -/
lemma nExc_excPart {m : ℕ} [NeZero m] (j : ℕ) (Ψ : RealFock m) :
    nExc (m := m) (excPart j Ψ) = (j : ℝ) • excPart j Ψ := by
  rw [excPart, map_sum]
  have hterm : ∀ b ∈ Ψ.support.filter (fun α => deg α - α 0 = j),
      nExc (m := m) (Finsupp.single b (Ψ b)) = (j : ℝ) • Finsupp.single b (Ψ b) := by
    intro b hb
    rw [Finset.mem_filter] at hb
    have hb' : Finsupp.single b (Ψ b) = (Ψ b) • Finsupp.single b (1 : ℝ) := by
      rw [Finsupp.smul_single]; simp
    rw [hb', map_smul, nExc_single_deg, hb.2]
    rw [smul_comm]
  rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum]

/-- The excited components reassemble `Ψ` (the window hypothesis is what makes the sum
finite). -/
lemma sum_excPart {m : ℕ} [NeZero m] (M : ℝ) (Ψ : RealFock m)
    (hM : ∀ α ∈ Ψ.support, deg α ≤ ⌊M⌋₊ + α 0) :
    (∑ j ∈ Finset.range (⌊M⌋₊ + 1), excPart j Ψ) = Ψ := by
  have hstep : (∑ j ∈ Finset.range (⌊M⌋₊ + 1), excPart j Ψ)
      = ∑ α ∈ Ψ.support, Finsupp.single α (Ψ α) := by
    simp only [excPart]
    exact Finset.sum_fiberwise_of_maps_to (t := Finset.range (⌊M⌋₊ + 1))
      (g := fun α : Fin m →₀ ℕ => deg α - α 0) (f := fun α => Finsupp.single α (Ψ α))
      (fun α hα => by
        rw [Finset.mem_range, Nat.lt_succ_iff, Nat.sub_le_iff_le_add]
        exact hM α hα)
  rw [hstep, sum_single_support]

/-! ## 4. The window, concretely -/

/-- **The excited window in coordinates.**  `ExcWindow M n Ψ` holds exactly when every
monomial in the support of `Ψ` has at most `n` particles in total and at most `⌊M⌋₊`
particles outside the condensate mode `0`. -/
theorem excwindow_iff {m : ℕ} [NeZero m] (M : ℝ) (n : ℕ) (Ψ : RealFock m) :
    ExcWindow M n Ψ ↔
      (∀ α ∈ Ψ.support, deg α ≤ n) ∧
      (∀ α ∈ Ψ.support, deg α ≤ ⌊M⌋₊ + α 0) := by
  constructor
  · rintro ⟨⟨φ, hφ, hsum⟩, hpart⟩
    refine ⟨fun α hα => hpart α hα, ?_⟩
    intro α hα
    have hsumα : (∑ j ∈ Finset.range (⌊M⌋₊ + 1), (φ j) α) = Ψ α := by
      rw [← Finsupp.finsetSum_apply, hsum]
    have hne : Ψ α ≠ 0 := Finsupp.mem_support_iff.mp hα
    obtain ⟨j, hjmem, hjne⟩ :=
      Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsumα]; exact hne)
    have hjK : j < ⌊M⌋₊ + 1 := Finset.mem_range.mp hjmem
    have h1 : (nExc (m := m) (φ j)) α = (j : ℝ) * (φ j) α := by
      rw [hφ j, Finsupp.smul_apply, smul_eq_mul]
    have h2 : (nExc (m := m) (φ j)) α = ((deg α - α 0 : ℕ) : ℝ) * (φ j) α :=
      nExc_apply (φ j) α
    have heq : ((deg α - α 0 : ℕ) : ℝ) = (j : ℝ) := by
      rw [h2] at h1
      exact mul_right_cancel₀ hjne h1
    have hnat : deg α - α 0 = j := Nat.cast_injective heq
    have hdeg : deg α = (deg α - α 0) + α 0 :=
      (Nat.sub_add_cancel (apply_le_deg α 0)).symm
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun j => excPart j Ψ, fun j => nExc_excPart j Ψ,
        (sum_excPart M Ψ h2).symm⟩, h1⟩

/-- The window is a cone: stable under scalar multiplication. -/
lemma excwindow_smul {m : ℕ} [NeZero m] {M : ℝ} {n : ℕ} {Ψ : RealFock m}
    (h : ExcWindow M n Ψ) (c : ℝ) : ExcWindow M n (c • Ψ) := by
  rw [excwindow_iff] at h ⊢
  refine ⟨fun α hα => h.1 α ?_, fun α hα => h.2 α ?_⟩ <;>
  · rw [Finsupp.mem_support_iff, Finsupp.smul_apply, smul_eq_mul] at hα
    exact Finsupp.mem_support_iff.mpr fun hc => hα (by rw [hc, mul_zero])

/-- The window is stable under addition. -/
lemma excwindow_add {m : ℕ} [NeZero m] {M : ℝ} {n : ℕ} {Ψ Φ : RealFock m}
    (hΨ : ExcWindow M n Ψ) (hΦ : ExcWindow M n Φ) : ExcWindow M n (Ψ + Φ) := by
  rw [excwindow_iff] at hΨ hΦ ⊢
  refine ⟨?_, ?_⟩
  · intro α hα
    rw [Finsupp.mem_support_iff, Finsupp.add_apply] at hα
    rcases eq_or_ne (Ψ α) 0 with h | h
    · rw [h, zero_add] at hα
      exact hΦ.1 α (Finsupp.mem_support_iff.mpr hα)
    · exact hΨ.1 α (Finsupp.mem_support_iff.mpr h)
  · intro α hα
    rw [Finsupp.mem_support_iff, Finsupp.add_apply] at hα
    rcases eq_or_ne (Ψ α) 0 with h | h
    · rw [h, zero_add] at hα
      exact hΦ.2 α (Finsupp.mem_support_iff.mpr hα)
    · exact hΨ.2 α (Finsupp.mem_support_iff.mpr h)

/-- Monotonicity of the window in both thresholds. -/
lemma excwindow_mono {m : ℕ} [NeZero m] {M M' : ℝ} {n n' : ℕ} {Ψ : RealFock m}
    (h : ExcWindow M n Ψ) (hM : M ≤ M') (hn : n ≤ n') : ExcWindow M' n' Ψ := by
  rw [excwindow_iff] at h ⊢
  exact ⟨fun α hα => le_trans (h.1 α hα) hn,
    fun α hα => le_trans (h.2 α hα) (Nat.add_le_add_right (Nat.floor_mono hM) _)⟩

/-- `0` is in every window. -/
lemma excwindow_zero {m : ℕ} [NeZero m] (M : ℝ) (n : ℕ) : ExcWindow M n (0 : RealFock m) := by
  rw [excwindow_iff]
  exact ⟨fun α hα => absurd hα (by simp), fun α hα => absurd hα (by simp)⟩

end Work.BoseBoxFock
