import Mathlib
import Submission.Work.DFT.digitsBij
import Submission.Work.DFT.subDigitsFacts
import Submission.Work.DFT.phaseLin

set_option autoImplicit false

open scoped BigOperators

/-!
# `subIdx` as an involutive permutation of the flat index box

For positive radices `ts`, `HvdH.subIdx ts j k` is the flat index of the multi-index
`(jᵢ - kᵢ) mod tᵢ` (componentwise subtraction of the digit vectors).  The three facts
proved here are

* the digit vector of `subIdx ts j k` is the componentwise `subDigits` of the digit
  vectors (`digits_subIdx`),
* `subIdx ts j` is an involution of `{m | m < ts.prod}` (`subIdx_subIdx`),
* consequently `k ↦ subIdx ts j k` permutes the flat index box, so reindexing a sum
  along it changes nothing (`subIdx_sum_perm`).

This is the "subIdx" permutation used in the Bluestein/transform step.
-/

namespace Work.Transform

/-- Two natural lists of the same length that agree in `getD` at every index are equal. -/
private lemma list_eq_of_getD {l₁ l₂ : List ℕ} {n : ℕ} (h₁ : l₁.length = n) (h₂ : l₂.length = n)
    (h : ∀ i < n, l₁.getD i 0 = l₂.getD i 0) : l₁ = l₂ := by
  refine List.ext_getElem (by omega) (fun i hi1 hi2 => ?_)
  have hh := h i (by omega)
  rwa [List.getD_eq_getElem _ _ hi1, List.getD_eq_getElem _ _ hi2] at hh

/-- In a residue system of modulus `t`, subtracting the residue of `x + t - y` from
`x + t` returns `y` (for `y < t`). -/
private lemma sub_sub_mod (t x y : ℕ) (hy : y < t) :
    (x + t - (x + t - y) % t) % t = y := by
  have ht : 0 < t := by omega
  have hle : (x + t - y) % t ≤ x + t := by
    have := Nat.mod_lt (x + t - y) ht; omega
  have h1 : (x + t - (x + t - y) % t) ≡ (x + t) - (x + t - y) [MOD t] :=
    Nat.ModEq.sub hle (Nat.sub_le _ _) (Nat.ModEq.refl _) (Nat.mod_modEq _ _)
  have h2 : (x + t) - (x + t - y) = y := by omega
  rw [h2] at h1
  rw [Nat.ModEq] at h1
  rwa [Nat.mod_eq_of_lt hy] at h1

/-- Every mixed-radix digit of any `m` is below the corresponding radix. -/
private lemma digits_getD_lt : ∀ (ts : List ℕ), (∀ t ∈ ts, 0 < t) → ∀ (m i : ℕ),
    i < ts.length → (HvdH.digits ts m).getD i 0 < ts.getD i 0 := by
  intro ts
  induction ts with
  | nil => intro _ m i hi; simp at hi
  | cons t ts ih =>
      intro hpos m i hi
      have ht : 0 < t := hpos t (by simp)
      have hts : ∀ u ∈ ts, 0 < u := fun u hu => hpos u (by simp [hu])
      cases i with
      | zero =>
          rw [HvdH.digits]
          simpa [List.getD_cons_zero] using Nat.mod_lt (m / ts.prod) ht
      | succ k =>
          rw [HvdH.digits]
          simp only [List.getD_cons_succ]
          have hk : k < ts.length := by simp only [List.length_cons] at hi; omega
          exact ih hts (m % ts.prod) k hk

/-- The digit vector of `subIdx ts j k` is the componentwise subtraction of the digit
vectors of `j` and `k` (for arbitrary `j k`, not only indices below `ts.prod`). -/
theorem digits_subIdx (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t) (j k : ℕ) :
    HvdH.digits ts (HvdH.subIdx ts j k)
      = HvdH.subDigits ts (HvdH.digits ts j) (HvdH.digits ts k) := by
  obtain ⟨-, -, -, h4⟩ := Work.DFT.digitsBij ts hpos
  obtain ⟨hDlen, hDlt, -⟩ :=
    Work.DFT.subDigitsFacts ts (HvdH.digits ts j) (HvdH.digits ts k) hpos
      (Work.DFT.digits_length ts j) (Work.DFT.digits_length ts k)
  rw [HvdH.subIdx]
  exact (h4 _ hDlen hDlt).1

/-- On the box of bounded digit lists, `subDigits` is an involution: subtracting from
`X` the componentwise difference of `X` and `Y` returns `Y`. -/
theorem subDigits_subDigits (ts X Y : List ℕ) (hpos : ∀ t ∈ ts, 0 < t)
    (hX : X.length = ts.length) (hY : Y.length = ts.length)
    (_hXb : ∀ i < ts.length, X.getD i 0 < ts.getD i 0)
    (hYb : ∀ i < ts.length, Y.getD i 0 < ts.getD i 0) :
    HvdH.subDigits ts X (HvdH.subDigits ts X Y) = Y := by
  obtain ⟨hDlen, hDlt, hDget⟩ := Work.DFT.subDigitsFacts ts X Y hpos hX hY
  obtain ⟨hElen, -, hEget⟩ := Work.DFT.subDigitsFacts ts X (HvdH.subDigits ts X Y) hpos hX hDlen
  refine list_eq_of_getD hElen hY (fun i hi => ?_)
  rw [hEget i hi, hDget i hi]
  exact sub_sub_mod (ts.getD i 0) (X.getD i 0) (Y.getD i 0) (hYb i hi)

/-- `subIdx ts j` is an involution of the flat index box: `j - (j - k) = k`. -/
theorem subIdx_subIdx (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t) (j k : ℕ) (hk : k < ts.prod) :
    HvdH.subIdx ts j (HvdH.subIdx ts j k) = k := by
  obtain ⟨h1, -, -, -⟩ := Work.DFT.digitsBij ts hpos
  have hdig : HvdH.digits ts (HvdH.subIdx ts j (HvdH.subIdx ts j k)) = HvdH.digits ts k := by
    rw [digits_subIdx ts hpos j (HvdH.subIdx ts j k), digits_subIdx ts hpos j k]
    exact subDigits_subDigits ts (HvdH.digits ts j) (HvdH.digits ts k) hpos
      (Work.DFT.digits_length ts j) (Work.DFT.digits_length ts k)
      (fun i hi => digits_getD_lt ts hpos j i hi) (fun i hi => digits_getD_lt ts hpos k i hi)
  have hcongr := congrArg (HvdH.undigits ts) hdig
  rw [h1 _ (Work.DFT.subIdx_lt ts hpos j (HvdH.subIdx ts j k)), h1 _ hk] at hcongr
  exact hcongr

/-- Reindexing a sum over the flat index box along `k ↦ subIdx ts j k` changes nothing. -/
theorem subIdx_sum_perm (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t) (j : Fin ts.prod)
    (G : Fin ts.prod → ℂ) :
    (∑ k : Fin ts.prod,
        G ⟨HvdH.subIdx ts (j : ℕ) (k : ℕ), Work.DFT.subIdx_lt ts hpos (j : ℕ) (k : ℕ)⟩)
      = ∑ k : Fin ts.prod, G k := by
  let F : Fin ts.prod → Fin ts.prod := fun k =>
    ⟨HvdH.subIdx ts (j : ℕ) (k : ℕ), Work.DFT.subIdx_lt ts hpos (j : ℕ) (k : ℕ)⟩
  have hF : Function.Involutive F := by
    intro k
    apply Fin.ext
    exact subIdx_subIdx ts hpos (j : ℕ) (k : ℕ) k.isLt
  have hcomp := Equiv.sum_comp (Equiv.ofBijective F hF.bijective) G
  simpa [F] using hcomp

theorem subIdxPerm (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t) :
    (∀ j k : ℕ, HvdH.digits ts (HvdH.subIdx ts j k)
        = HvdH.subDigits ts (HvdH.digits ts j) (HvdH.digits ts k)) ∧
    (∀ j k : Fin ts.prod,
      HvdH.subIdx ts (j : ℕ) (HvdH.subIdx ts (j : ℕ) (k : ℕ)) = (k : ℕ)) ∧
    (∀ j : Fin ts.prod, ∀ G : Fin ts.prod → ℂ,
      (∑ k : Fin ts.prod,
          G ⟨HvdH.subIdx ts (j : ℕ) (k : ℕ), Work.DFT.subIdx_lt ts hpos (j : ℕ) (k : ℕ)⟩)
        = ∑ k : Fin ts.prod, G k) :=
  ⟨fun j k => digits_subIdx ts hpos j k,
   fun j k => subIdx_subIdx ts hpos (j : ℕ) (k : ℕ) k.isLt,
   fun j G => subIdx_sum_perm ts hpos j G⟩

end Work.Transform
