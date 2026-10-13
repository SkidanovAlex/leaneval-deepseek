import Mathlib
import Submission.Work.WilE8.Extend

namespace Work.WilE7.PadAux

open WilkiesDesign WilkiesDesign.E

/-- The `a`-coefficient of `EAChain.extend e c` at a coordinate `i` outside the image of `e` is
zero, since `extend` fills the new coordinates with `0`. -/
private lemma EAChain.extend_a_of_notMem {k k' r : ℕ} (e : Fin k → Fin k')
    (c : EAChain k r) (i : Fin k') (hi : ∀ i' : Fin k, e i' ≠ i) (j : Fin r) :
    (Work.WilE8.EAChain.extend e c).a j i = 0 := by
  simp only [Work.WilE8.EAChain.extend]
  split_ifs with h
  · exact absurd h.choose_spec (hi h.choose)
  · rfl

/-- `EAPoly.extend e Q` is a renaming of `Q` along `Sum.map e id`, so it involves no variable
`Sum.inl i` with `i` outside the image of `e`; hence its `Sum.inl i`-partial derivative vanishes. -/
private lemma pderiv_extend_zero {k k' r : ℕ} (e : Fin k → Fin k') (Q : EAPoly k r)
    (i : Fin k') (hi : ∀ i' : Fin k, e i' ≠ i) :
    MvPolynomial.pderiv (Sum.inl i) (Work.WilE8.EAPoly.extend e Q) = 0 := by
  classical
  rw [Work.WilE8.EAPoly.extend]
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hmem
  obtain ⟨a, _ha, hf⟩ := MvPolynomial.mem_vars_rename (Sum.map e id) Q hmem
  cases a with
  | inl i' =>
      simp [Sum.map] at hf
      exact hi i' hf
  | inr j => simp [Sum.map] at hf

theorem eaD_extend_zero {k k' r : ℕ} (e : Fin k → Fin k')
    (c : WilkiesDesign.E.EAChain k r) (i : Fin k') (hi : ∀ i' : Fin k, e i' ≠ i)
    (Q : WilkiesDesign.E.EAPoly k r) :
    WilkiesDesign.E.eaD (Work.WilE8.EAChain.extend e c) i (Work.WilE8.EAPoly.extend e Q) = 0 := by
  classical
  have hpderiv := pderiv_extend_zero e Q i hi
  unfold WilkiesDesign.E.eaD
  rw [hpderiv, Finset.sum_eq_zero (fun j _ => by
    rw [EAChain.extend_a_of_notMem e c i hi j]; simp), add_zero]

end Work.WilE7.PadAux
