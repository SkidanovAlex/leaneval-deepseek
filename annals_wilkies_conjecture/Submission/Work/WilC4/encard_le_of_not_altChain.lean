import Mathlib
import Submission.Work.WilC4.UnifDefs

namespace Work.WilC4

/-- If a finite set `s` of reals has at least `N + 1` elements, then its `N + 1` smallest
elements, together with the midpoints of consecutive ones, form an alternating chain of
length `N`. -/
theorem altChain_of_le_card {s : Finset ℝ} {N : ℕ} (h : N + 1 ≤ s.card) :
    AltChain N (s : Set ℝ) := by
  classical
  let g : Fin s.card ↪o ℝ := s.orderEmbOfFin rfl
  have hgmem : ∀ i, g i ∈ s := fun i => s.orderEmbOfFin_mem rfl i
  have hgrange : Set.range g = (s : Set ℝ) := s.range_orderEmbOfFin rfl
  refine ⟨fun j => g (Fin.castLE h j),
    fun j => (g (Fin.castLE h (Fin.castSucc j)) + g (Fin.castLE h (Fin.succ j))) / 2, ?_, ?_⟩
  · intro j; exact hgmem _
  · intro j
    set a := Fin.castLE h (Fin.castSucc j) with ha
    set b := Fin.castLE h (Fin.succ j) with hb
    have hab : a < b := by
      have hlt : (Fin.castLE h (Fin.castSucc j)) < (Fin.castLE h (Fin.succ j)) :=
        Fin.strictMono_castLE h Fin.castSucc_lt_succ
      simpa only [ha, hb] using hlt
    have hgab : g a < g b := (OrderEmbedding.lt_iff_lt g).mpr hab
    have hm1 : g a < (g a + g b) / 2 := by linarith
    have hm2 : (g a + g b) / 2 < g b := by linarith
    have haval : (a : ℕ) = (j : ℕ) := by simp [ha]
    have hbval : (b : ℕ) = (j : ℕ) + 1 := by simp [hb]
    refine ⟨?_, hm1, hm2⟩
    intro hmem
    have hy : (g a + g b) / 2 ∈ Set.range g := by rw [hgrange]; exact hmem
    obtain ⟨i, hi⟩ := hy
    have h1 : a < i := (OrderEmbedding.lt_iff_lt g).mp (by rw [hi]; exact hm1)
    have h2 : i < b := (OrderEmbedding.lt_iff_lt g).mp (by rw [hi]; exact hm2)
    have e1 : (a : ℕ) < (i : ℕ) := Fin.lt_def.mp h1
    have e2 : (i : ℕ) < (b : ℕ) := Fin.lt_def.mp h2
    omega

/-- Prove in namespace `Work.WilC4` (declaration name `Work.WilC4.encard_le_of_not_altChain`) in the
file `Submission/Work/WilC4/encard_le_of_not_altChain.lean`.  A finite subset of `ℝ` with no
alternating chain of length `N` (`Work.WilC4.AltChain`, meaning `N + 1` points of `S` separated by
`N` points outside `S`) has at most `N` elements: enumerate the `N + 1` smallest elements of `S`
increasingly with `Finset.orderEmbOfFin`; consecutive ones have midpoints outside `S`. -/
theorem encard_le_of_not_altChain {S : Set ℝ} {N : ℕ} (hfin : S.Finite)
    (h : ¬ Work.WilC4.AltChain N S) : S.encard ≤ (N : ℕ∞) := by
  have hcard : hfin.toFinset.card ≤ N := by
    by_contra hc
    rw [not_le] at hc
    have hle : N + 1 ≤ hfin.toFinset.card := hc
    have halt := altChain_of_le_card hle
    rw [Set.Finite.coe_toFinset hfin] at halt
    exact h halt
  rw [hfin.encard_eq_coe_toFinset_card]
  exact_mod_cast hcard

end Work.WilC4
