/-
  WilC4/sameSide_slot : from a `SameSide` pair `x₁ ≤ x₂` (with `0 < x₁`) and a *finite* breakpoint
  fibre `{x | Fin.cons x c ∈ B}` one can extract a genuine gap of the fibre which swallows the
  whole multiplicative window `[x₁/N, N x₂]` strictly in its interior.

  The point is that `SameSide` says every breakpoint `b` of the fibre satisfies `b < x₁/N` or
  `N x₂ < b`; since the fibre is finite we can push the ends of the interval just past the largest
  breakpoint below `x₁/N` (resp. the smallest breakpoint above `N x₂`) and still keep both ends
  positive/finite.  This is the geometric input used by the ULPM assembly: it turns the abstract
  "same side" hypothesis on a pair of points into an honest interval slot.
-/
import Mathlib
import Submission.Work.WilC4.ULPMRoute

namespace Work.WilC4

theorem sameSide_slot {k : ℕ} (N : ℕ) (hN : 2 ≤ N) {c : Fin k → ℝ}
    {B : Set (Fin (k + 1) → ℝ)} (hBfin : ({x : ℝ | Fin.cons x c ∈ B}).Finite)
    {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₁x₂ : x₁ ≤ x₂)
    (hss : Work.WilC4.Route.SameSide N {x : ℝ | Fin.cons x c ∈ B} x₁ x₂) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ (∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B) ∧
      (N : ℝ) * a < x₁ ∧ (N : ℝ) * x₂ < b := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have h : (0 : ℕ) < N := by omega
    exact_mod_cast h
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by
    have h : 1 ≤ N := by omega
    exact_mod_cast h
  -- The two ends of the multiplicative window.
  set r : ℝ := x₁ / (N : ℝ) with hrdef
  set s : ℝ := (N : ℝ) * x₂ with hsdef
  have hrpos : 0 < r := by rw [hrdef]; exact div_pos hx₁ hNpos
  have hspos : 0 < s := by
    rw [hsdef]; exact mul_pos hNpos (lt_of_lt_of_le hx₁ hx₁x₂)
  -- Every breakpoint of the fibre lies below `r` or above `s`.
  have hsep : ∀ d : ℝ, Fin.cons d c ∈ B → d < r ∨ s < d := by
    intro d hd
    rcases hss d hd with ⟨h1, _⟩ | ⟨_, h2⟩
    · left
      rw [hrdef, lt_div_iff₀ hNpos]
      linarith [h1]
    · right
      rw [hsdef]
      exact h2
  have hrs : r ≤ s := by
    rw [hrdef, hsdef]
    have h1 : x₁ / (N : ℝ) ≤ x₁ := by
      rw [div_le_iff₀ hNpos]; nlinarith [hNge1, hx₁]
    nlinarith [hNge1, hx₁, hx₁x₂]
  -- The fibre as a finset, and the two candidate interval ends.
  let Df : Finset ℝ := hBfin.toFinset
  have hDf : ∀ x : ℝ, x ∈ Df ↔ Fin.cons x c ∈ B := fun x => hBfin.mem_toFinset
  let Af : Finset ℝ := insert (r / 2) (Df.filter (fun d => d < r))
  let Bf : Finset ℝ := insert (2 * s) (Df.filter (fun d => s < d))
  have hAne : Af.Nonempty := Finset.insert_nonempty _ _
  have hBne : Bf.Nonempty := Finset.insert_nonempty _ _
  have hamax_lt_r : Af.max' hAne < r := by
    rw [Finset.max'_lt_iff]
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy'
    · linarith [hrpos]
    · exact (Finset.mem_filter.mp hy').2
  have hs_lt_bmin : s < Bf.min' hBne := by
    rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy'
    · linarith [hspos]
    · exact (Finset.mem_filter.mp hy').2
  refine ⟨Af.max' hAne, Bf.min' hBne, ?_, ?_, ?_, ?_, ?_⟩
  · -- `0 < a`
    have := Finset.le_max' Af (r / 2) (Finset.mem_insert_self _ _)
    linarith [hrpos]
  · -- `a < b`
    linarith [hamax_lt_r, hrs, hs_lt_bmin]
  · -- the open interval misses the fibre
    intro x hx hmem
    simp only [Set.mem_Ioo] at hx
    obtain ⟨hax, hxb⟩ := hx
    have hxD : x ∈ Df := (hDf x).mpr hmem
    rcases hsep x hmem with hlt | hgt
    · have hxA : x ∈ Af := Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hxD, hlt⟩))
      have := Finset.le_max' Af x hxA
      linarith
    · have hxB : x ∈ Bf := Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hxD, hgt⟩))
      have := Finset.min'_le Bf x hxB
      linarith
  · -- `N * a < x₁`
    have hlt : Af.max' hAne < x₁ / (N : ℝ) := by rw [← hrdef]; exact hamax_lt_r
    have := (lt_div_iff₀ hNpos).mp hlt
    linarith
  · -- `N * x₂ < b`
    exact hs_lt_bmin

end Work.WilC4
