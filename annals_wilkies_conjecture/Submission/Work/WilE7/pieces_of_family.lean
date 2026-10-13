/-
  Area E7 (`Work.WilE7.pieces_of_family`): the first step of the level step `Core n → Core (n+1)`
  (`NOTES_S26_level_step.md` §4.1-4.2): flatten the fibre-cutting hypothesis `hFC` over a finite
  family, and reindex each piece by `vertSwap`, so that the vertical coordinate (the first fibre
  coordinate, the one kept by `π_{n+1}`) becomes the *last* fibre coordinate, which is what the S11
  cell lemmas use.  `vertSwap` fixes the base, so `πₙ`, `fmt` and `deg` are unchanged, and the
  fibres over `x ∈ ℝⁿ` are carried to each other by an explicit permutation of `Fin (M+1)`
  (`vertSwap_fiber_finite`).
-/
import Mathlib
import Submission.Work.WilE7.VertSwap
import Submission.Work.WilE7.vertSwap_fiber_finite
import Submission.Work.WilE9G.Assembly.poly_eval_mono

set_option autoImplicit false
noncomputable section
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

theorem pieces_of_family
    (hFC : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (n m : ℕ) (X : WilkiesDesign.E.SemiPf (n + m)),
      X.fmt ≤ F →
      ∃ L : List (WilkiesDesign.E.SemiPf (n + m)), L.length ≤ b.eval X.deg ∧
        (∀ Xh ∈ L, Xh.fmt ≤ a ∧ Xh.deg ≤ b.eval X.deg ∧
          ∀ x, (WilkiesDesign.E.fiber Xh.set x).Finite) ∧
        WilkiesDesign.E.projFirst n m '' X.set =
          ⋃ Xh ∈ L, WilkiesDesign.E.projFirst n m '' Xh.set)
    (F : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ),
      ∀ (D k n M : ℕ) (X : Fin k → WilkiesDesign.E.SemiPf (n + (M + 1))),
        (∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D) →
        ∃ (r : ℕ) (Y : Fin r → WilkiesDesign.E.SemiPf (n + (M + 1))),
          r ≤ k * B.eval D ∧
          (∀ l, ∃ S0 : WilkiesDesign.E.SemiPf (n + (M + 1)),
              (Y l) = Work.WilE7.SemiPf.reindex (Work.WilE7.vertSwap n M) S0 ∧
              S0.fmt ≤ A ∧ S0.deg ≤ B.eval D ∧
              ∀ x, (WilkiesDesign.E.fiber S0.set x).Finite) ∧
          (∀ l, (Y l).fmt ≤ A ∧ (Y l).deg ≤ B.eval D ∧
            ∀ x, (WilkiesDesign.E.fiber (Y l).set x).Finite) ∧
          (∀ i, WilkiesDesign.E.projFirst n (M + 1) '' (X i).set ⊆
            ⋃ l, WilkiesDesign.E.projFirst n (M + 1) '' (Y l).set) ∧
          (∀ l, ∃ i, WilkiesDesign.E.projFirst n (M + 1) '' (Y l).set ⊆
            WilkiesDesign.E.projFirst n (M + 1) '' (X i).set) := by
  obtain ⟨a, b, hb⟩ := hFC F
  refine ⟨a, b, ?_⟩
  intro D k n M X hX
  choose L hlen hpiece hcov using fun i : Fin k => hb n (M + 1) (X i) (hX i).1
  let ls : List (WilkiesDesign.E.SemiPf (n + (M + 1))) := (List.finRange k).flatMap L
  have hprov : ∀ l : Fin ls.length, ∃ i : Fin k, ls.get l ∈ L i := by
    intro l
    have hl : ls.get l ∈ (List.finRange k).flatMap L := List.get_mem ls l
    rw [List.mem_flatMap] at hl
    obtain ⟨i, -, hi⟩ := hl
    exact ⟨i, hi⟩
  have hdegle : ∀ (l : Fin ls.length) (i : Fin k), ls.get l ∈ L i → (ls.get l).deg ≤ b.eval D := by
    intro l i hi
    exact le_trans (hpiece i (ls.get l) hi).2.1
      (Work.WilE9G.Assembly.poly_eval_mono b (hX i).2)
  refine ⟨ls.length, fun l => Work.WilE7.SemiPf.reindex (vertSwap n M) (ls.get l),
    ?_, ?_, ?_, ?_, ?_⟩
  · -- the length bound
    have hkey : ∀ l : List (Fin k), (l.flatMap L).length ≤ l.length * b.eval D := by
      intro l
      induction l with
      | nil => simp
      | cons i t ih =>
          rw [List.flatMap_cons, List.length_append, List.length_cons]
          have h1 : (L i).length ≤ b.eval D :=
            le_trans (hlen i) (Work.WilE9G.Assembly.poly_eval_mono b (hX i).2)
          have : (t.length + 1) * b.eval D = b.eval D + t.length * b.eval D := by ring
          omega
    have hfin : (List.finRange k).length = k := List.length_finRange
    have := hkey (List.finRange k)
    rw [hfin] at this
    exact this
  · -- the presentation clause
    intro l
    obtain ⟨i, hi⟩ := hprov l
    exact ⟨ls.get l, rfl, (hpiece i (ls.get l) hi).1, hdegle l i hi,
      (hpiece i (ls.get l) hi).2.2⟩
  · -- the bounds for the swapped pieces
    intro l
    obtain ⟨i, hi⟩ := hprov l
    refine ⟨?_, ?_, ?_⟩
    · rw [vertSwap_fmt]
      exact (hpiece i (ls.get l) hi).1
    · rw [vertSwap_deg]
      exact hdegle l i hi
    · exact vertSwap_fiber_finite (ls.get l) (hpiece i (ls.get l) hi).2.2
  · -- the covering inclusion
    intro i z hz
    rw [hcov i] at hz
    simp only [Set.mem_iUnion] at hz ⊢
    obtain ⟨Xh, hXh, hz⟩ := hz
    have hmem : Xh ∈ ls := by
      simp only [ls, List.mem_flatMap]
      exact ⟨i, List.mem_finRange i, hXh⟩
    obtain ⟨l, hl⟩ := List.get_of_mem hmem
    refine ⟨l, ?_⟩
    show z ∈ WilkiesDesign.E.projFirst n (M + 1) ''
      (Work.WilE7.SemiPf.reindex (vertSwap n M) (ls.get l)).set
    rw [vertSwap_proj n M (ls.get l), hl]
    exact hz
  · -- the provenance
    intro l
    obtain ⟨i, hi⟩ := hprov l
    refine ⟨i, ?_⟩
    show WilkiesDesign.E.projFirst n (M + 1) ''
      (Work.WilE7.SemiPf.reindex (vertSwap n M) (ls.get l)).set ⊆ _
    rw [vertSwap_proj n M (ls.get l), hcov i]
    intro z hz
    simp only [Set.mem_iUnion] at hz ⊢
    exact ⟨ls.get l, hi, hz⟩

end Work.WilE7
