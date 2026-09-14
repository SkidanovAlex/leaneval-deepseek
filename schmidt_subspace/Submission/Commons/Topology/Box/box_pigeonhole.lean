import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Submission.Commons.Set.Infinite.infinite_of_finite_cover

namespace Commons.Topology.Box

open _root_.Set

set_option linter.style.haveILetI false in
theorem box_pigeonhole {κ : Type*} [Fintype κ] (N : ℕ) (hN : 0 < N) (B : ℝ)
    (S : Set (κ → ℝ)) (hS : S.Infinite) (hbdd : ∀ t ∈ S, ∀ i, |t i| ≤ B) :
    ∃ m : κ → ℤ, (∀ i, -(N * (⌈B⌉₊ + 1)) ≤ m i ∧ m i ≤ N * (⌈B⌉₊ + 1)) ∧
      (S ∩ {t : κ → ℝ | ∀ i, (m i : ℝ) / N ≤ t i ∧
        t i < ((m i : ℝ) + 1) / N}).Infinite := by
  classical
  rcases isEmpty_or_nonempty κ with hE | hNE
  · -- κ empty: conclusion holds for any m, e.g. 0
    haveI : IsEmpty κ := hE
    refine ⟨fun i => isEmptyElim i, fun i => isEmptyElim i, ?_⟩
    have hbox : {t : κ → ℝ | ∀ i, ((fun i => isEmptyElim i : κ → ℤ) i : ℝ) / N ≤ t i ∧
        t i < (((fun i => isEmptyElim i : κ → ℤ) i : ℝ) + 1) / N} = Set.univ := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      intro i
      exact isEmptyElim i
    rw [hbox, Set.inter_univ]
    exact hS
  · obtain ⟨i₀⟩ := hNE
    obtain ⟨t₀, ht₀⟩ := hS.nonempty
    have hB0 : 0 ≤ B := le_trans (abs_nonneg (t₀ i₀)) (hbdd t₀ ht₀ i₀)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    let c : ℕ := N * (⌈B⌉₊ + 1)
    let lo : ℤ := -(c : ℤ)
    let hi : ℤ := (c : ℤ)
    let K : Set (κ → ℤ) := {m | ∀ i, m i ∈ Set.Icc lo hi}
    have hKfin : K.Finite := Set.Finite.pi' (fun _ : κ => Set.finite_Icc lo hi)
    let f : (κ → ℝ) → (κ → ℤ) := fun t i => ⌊(N : ℝ) * t i⌋
    have hfK : ∀ t ∈ S, f t ∈ K := by
      intro t ht i
      change lo ≤ ⌊(N : ℝ) * t i⌋ ∧ ⌊(N : ℝ) * t i⌋ ≤ hi
      obtain ⟨hge, hle⟩ := abs_le.mp (hbdd t ht i)
      have hceil : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
      have hcq : ((N * ⌈B⌉₊ : ℕ) : ℝ) ≤ (c : ℝ) := by
        have h : N * ⌈B⌉₊ ≤ c := by
          simp only [c]
          exact Nat.mul_le_mul_left N (Nat.le_succ ⌈B⌉₊)
        exact_mod_cast h
      have hcast : (N : ℝ) * (⌈B⌉₊ : ℝ) = ((N * ⌈B⌉₊ : ℕ) : ℝ) := by push_cast; ring
      constructor
      · apply Int.le_floor.mpr
        show ((lo : ℤ) : ℝ) ≤ (N : ℝ) * t i
        have h3 : -((⌈B⌉₊ : ℝ)) ≤ t i := by linarith
        have h4 : (N : ℝ) * (-(⌈B⌉₊ : ℝ)) ≤ (N : ℝ) * t i :=
          mul_le_mul_of_nonneg_left h3 (le_of_lt hNpos)
        have h5 : -((c : ℕ) : ℝ) ≤ (N : ℝ) * (-(⌈B⌉₊ : ℝ)) := by
          have hneg : (N : ℝ) * (-(⌈B⌉₊ : ℝ)) = -(((N * ⌈B⌉₊ : ℕ) : ℝ)) := by
            push_cast; ring
          rw [hneg]; linarith
        have hlo : ((lo : ℤ) : ℝ) = -((c : ℕ) : ℝ) := by simp [lo]
        rw [hlo]
        linarith
      · apply Int.floor_le_iff.mpr
        show (N : ℝ) * t i < ((hi : ℤ) : ℝ) + 1
        have h2 : (N : ℝ) * t i ≤ ((N * ⌈B⌉₊ : ℕ) : ℝ) := by
          have := mul_le_mul_of_nonneg_left (le_trans hle hceil) (le_of_lt hNpos)
          rw [hcast] at this
          linarith
        have hhi : ((hi : ℤ) : ℝ) = (c : ℝ) := by simp [hi]
        rw [hhi]
        linarith
    let box : (κ → ℤ) → Set (κ → ℝ) :=
      fun m => {t | ∀ i, (m i : ℝ) / N ≤ t i ∧ t i < ((m i : ℝ) + 1) / N}
    have hboxm : ∀ t ∈ S, t ∈ box (f t) := by
      intro t ht i
      show ((⌊(N : ℝ) * t i⌋ : ℤ) : ℝ) / N ≤ t i ∧
        t i < (((⌊(N : ℝ) * t i⌋ : ℤ) : ℝ) + 1) / N
      have h1 : ((⌊(N : ℝ) * t i⌋ : ℤ) : ℝ) ≤ (N : ℝ) * t i := Int.floor_le _
      have h2 : (N : ℝ) * t i < ((⌊(N : ℝ) * t i⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
      constructor
      · rw [div_le_iff₀ hNpos]
        linarith
      · rw [lt_div_iff₀ hNpos]
        linarith
    have hcover : S ⊆ ⋃ m : K, box m.1 := by
      intro t ht
      exact Set.mem_iUnion.mpr ⟨⟨f t, hfK t ht⟩, hboxm t ht⟩
    letI : Fintype K := hKfin.fintype
    obtain ⟨m, hm⟩ :=
      Commons.Set.Infinite.infinite_of_finite_cover hS (fun m : K => box m.1) hcover
    refine ⟨m.1, ?_, ?_⟩
    · intro i
      simpa [c, lo, hi, Set.mem_Icc] using m.2 i
    · exact hm

end Commons.Topology.Box