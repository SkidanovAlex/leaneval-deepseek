import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

set_option linter.unusedVariables false

namespace Commons.GeometryOfNumbers.Box

/-- Cardinality of the initial segment of `Fin N` defined by `val < m`, when `m ≤ N`. -/
private lemma fin_card_filter_val_lt {N m : ℕ} (hm : m ≤ N) :
    ((Finset.univ : Finset (Fin N)).filter (fun j : Fin N => j.val < m)).card = m := by
  have h : ((Finset.univ : Finset (Fin N)).filter (fun j : Fin N => j.val < m)).card
      = (Finset.range m).card := by
    apply Finset.card_bij
        (fun (b : Fin N) (_ : b ∈ Finset.univ.filter (fun j : Fin N => j.val < m)) => (b.val : ℕ))
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      exact Finset.mem_range.mpr hb
    · intro b _ b' _ heq
      exact Fin.ext heq
    · intro i hi
      refine ⟨⟨i, lt_of_lt_of_le (Finset.mem_range.mp hi) hm⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.mem_range.mp hi
  rw [h, Finset.card_range]

theorem eq_card_sInf_of_monotone {N : ℕ} (r : ℝ → ℕ)
    (hmono : Monotone r)
    (hstab : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ t' ∈ Set.Icc t (t + ε), r t' = r t)
    (hbound : ∀ t : ℝ, r t ≤ N)
    (htop : ∃ t : ℝ, 0 ≤ t ∧ r t = N)
    (lam : Fin N → ℝ)
    (hlam : ∀ j : Fin N, lam j = sInf {t : ℝ | 0 ≤ t ∧ j.val + 1 ≤ r t}) :
    ∀ t : ℝ, 0 ≤ t → r t = ((Finset.univ : Finset (Fin N)).filter (fun j => lam j ≤ t)).card := by
  classical
  -- The defining sets are nonempty.
  have hne : ∀ j : Fin N, ({t : ℝ | 0 ≤ t ∧ j.val + 1 ≤ r t}).Nonempty := by
    intro j
    obtain ⟨t0, ht0le, ht0N⟩ := htop
    refine ⟨t0, ht0le, ?_⟩
    have h1 : j.val + 1 ≤ N := Nat.succ_le_of_lt j.isLt
    calc j.val + 1 ≤ N := h1
      _ = r t0 := ht0N.symm
  -- The defining sets are bounded below.
  have hbdd : ∀ j : Fin N, BddBelow {t : ℝ | 0 ≤ t ∧ j.val + 1 ≤ r t} := by
    intro j
    refine ⟨0, ?_⟩
    rintro x ⟨hx, _⟩
    exact hx
  -- `lam j` is the least point with `j.val + 1 ≤ r`.
  have hmem : ∀ j : Fin N, lam j ∈ {t : ℝ | 0 ≤ t ∧ j.val + 1 ≤ r t} := by
    intro j
    set A : Set ℝ := {t : ℝ | 0 ≤ t ∧ j.val + 1 ≤ r t} with hA
    have hneA := hne j
    have hbddA := hbdd j
    have hsinf : sInf A = lam j := (hlam j).symm
    have hnonneg : 0 ≤ lam j := by
      rw [← hsinf]
      exact le_csInf hneA (fun b hb => hb.1)
    obtain ⟨ε, hεpos, hε⟩ := hstab (lam j)
    have hlt : sInf A < lam j + ε := by rw [hsinf]; linarith
    obtain ⟨t', ht'A, ht'lt⟩ := (csInf_lt_iff hbddA hneA).mp hlt
    have hle_t' : lam j ≤ t' := by
      rw [← hsinf]
      exact csInf_le hbddA ht'A
    have hrt : r t' = r (lam j) := hε t' ⟨hle_t', le_of_lt ht'lt⟩
    exact ⟨hnonneg, by rw [← hrt]; exact ht'A.2⟩
  -- Characterisation of `lam j ≤ t`.
  have hkey : ∀ (j : Fin N) (t : ℝ), 0 ≤ t → (lam j ≤ t ↔ j.val + 1 ≤ r t) := by
    intro j t ht
    constructor
    · intro hle
      exact le_trans (hmem j).2 (hmono hle)
    · intro h
      have htA : t ∈ {t : ℝ | 0 ≤ t ∧ j.val + 1 ≤ r t} := ⟨ht, h⟩
      have hle : sInf {t : ℝ | 0 ≤ t ∧ j.val + 1 ≤ r t} ≤ t := csInf_le (hbdd j) htA
      rwa [← hlam j] at hle
  intro t ht
  have hfilter : (Finset.univ : Finset (Fin N)).filter (fun j => lam j ≤ t)
      = (Finset.univ : Finset (Fin N)).filter (fun j => j.val + 1 ≤ r t) := by
    apply Finset.filter_congr
    intro j _
    exact hkey j t ht
  have hfilter2 : (Finset.univ : Finset (Fin N)).filter (fun j => j.val + 1 ≤ r t)
      = (Finset.univ : Finset (Fin N)).filter (fun j => j.val < r t) := by
    apply Finset.filter_congr
    intro j _
    exact Nat.succ_le_iff
  rw [hfilter, hfilter2, fin_card_filter_val_lt (hbound t)]

end Commons.GeometryOfNumbers.Box