import Mathlib
import Submission.Work.WilCrux.FailSetChainIff

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Classical

namespace Work.WilCrux

open WilkiesDesign

/-! ## 7. The set identity -/

/-- The `Ω`-construction `fmChain` is exactly the failure set with the level as a coordinate. -/
theorem fmChain_eq_target {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (j : Fin b) :
    fmChain a b (Work.WilG4b.derivGraph (Work.WilG4c.famFun G) (Fin.natAdd a j)) =
      {u : Fin (a + 1) → ℝ | 0 < u (Fin.last a) ∧
        Fin.init u ∈ failSet G j (u (Fin.last a))} := by
  ext X
  rw [Set.mem_ofPred_eq, fmChain_iff, failSet_iff]
  constructor
  · rintro ⟨hε, h⟩
    refine ⟨hε, fun η hη => ?_⟩
    obtain ⟨w, hhyp, hK⟩ := h η hη
    have hhyp' := (fmHyp_read X η w).mp hhyp
    refine ⟨w ∘ fmwpB a b, w ∘ fmzB a b, w ∘ fmzpB a b, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (fm_dist_iff (w ∘ fmwpB a b) (Fin.init X) η hη).mpr hhyp'.1
    · exact (fm_ne_zero_iff _).mpr hhyp'.2.1
    · exact (fm_norm_iff (w ∘ fmzB a b) η hη).mpr hhyp'.2.2.1
    · exact (fm_ne_zero_iff _).mpr hhyp'.2.2.2.1
    · exact (fm_norm_iff (w ∘ fmzpB a b) η hη).mpr hhyp'.2.2.2.2
    · have hneg := (fmK_fail_iff (Work.WilG4c.famFun G) (Fin.natAdd a j)
        (Work.WilG0.snocIt (fmE a) (fmB a b) (fmsnoc a X η) w)).mp hK
      rw [fm_comp_wpD, fm_comp_zD, fm_comp_zpD, fm_read_epsD, fm_readInit_epsE] at hneg
      exact hneg
  · rintro ⟨hε, h⟩
    refine ⟨hε, fun η hη => ?_⟩
    obtain ⟨w', z, z', h1, h2, h3, h4, h5, hcon⟩ := h η hη
    refine ⟨Fin.append (Fin.append w' z) z', ?_, ?_⟩
    · rw [fmHyp_read]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro i
        rw [show (Fin.append (Fin.append w' z) z') (fmwpB a b i) = w' i by
          simp only [fmwpB, Fin.append_left]]
        exact (fm_dist_iff w' (Fin.init X) η hη).mp h1 i
      · rw [fm_ne_zero_iff] at h2
        obtain ⟨j, hj⟩ := h2
        exact ⟨j, by rwa [show (Fin.append (Fin.append w' z) z') (fmzB a b j) = z j by
          simp only [fmzB, Fin.append_left, Fin.append_right]]⟩
      · intro j
        rw [show (Fin.append (Fin.append w' z) z') (fmzB a b j) = z j by
          simp only [fmzB, Fin.append_left, Fin.append_right]]
        exact (fm_norm_iff z η hη).mp h3 j
      · rw [fm_ne_zero_iff] at h4
        obtain ⟨j, hj⟩ := h4
        exact ⟨j, by rwa [show (Fin.append (Fin.append w' z) z') (fmzpB a b j) = z' j by
          simp only [fmzpB, Fin.append_right]]⟩
      · intro j
        rw [show (Fin.append (Fin.append w' z) z') (fmzpB a b j) = z' j by
          simp only [fmzpB, Fin.append_right]]
        exact (fm_norm_iff z' η hη).mp h5 j
    · refine (fmK_fail_iff (Work.WilG4c.famFun G) (Fin.natAdd a j) _).mpr ?_
      rw [fm_comp_wpD, fm_comp_zD, fm_comp_zpD, fm_curry_wpB, fm_curry_zB, fm_curry_zpB,
        fm_read_epsD, fm_readInit_epsE]
      exact hcon

/-! ## 8. The main theorem -/

/-- **`failSet` is `Ω`-definable, with the level `ε` as a coordinate, uniformly in `j`.**

The set `{u : Fin (a+1) → ℝ | 0 < u (Fin.last a) ∧ Fin.init u ∈ failSet G j (u (Fin.last a))}` of
pairs `(w, ε)`, `ε > 0`, at which the uniform Cauchy property of the `z_j`-partial fails.

Let `M := a + b`, `f := Work.WilG4c.famFun G`, `i := Fin.natAdd a j`.  By
`Work.WilG4b.derivGraph_mem` (using `hder`) together with `Work.WilG4c.graphOf_famFun`, the
derivative graph `T := Work.WilG4b.derivGraph f i ⊆ ℝ^{M+1}` is `Ω`-definable with format a
constant and degree a polynomial in `D`, *independent of* `j`, and
`u ∈ T ↔ Fin.init u ∈ Work.WilG4b.c1Loc f ∧ u (Fin.last M) = Work.WilG4b.dDir f i (Fin.init u)`.

Intended construction.  Work in the big ambient space with coordinates
`(w, ε, η, y, y', w', z, z')`, i.e. `N := (a + 1 + 1) + (1 + 1 + a + b + b)` (reading the first `a`
coordinates as `w`, then `ε`, then `η`, then `y`, then `y'`, then `a` coordinates `w'`, then the
`b` coordinates of `z`, then the `b` coordinates of `z'`).  This order is chosen so that the
quantifiers are peeled off the *end* with `Work.WilG0.projLastIter`: first `y, y'` (2 coordinates),
then `w', z, z'` (`a + 2*b` coordinates), then `η` (1 coordinate).

Let `e1 : Fin (M+1) → Fin N` read `(w', z, y)` as a point of the coordinate space of `T` (the `a`
coordinates of `w'`, then the `b` of `z`, then `y`), and likewise `e2` with `z'`, `y'`.  Then

* `K := {u | u ∘ e1 ∈ T ∧ u ∘ e2 ∈ T ∧ |y - y'| < ε}` is `Ω`-definable in `ℝ^N`
  (`Work.WilG5.coordPre_mem` for the two pullbacks, `Work.WilG1.Calc.pos_mem` on
  `X_{y'} - X_y + X_ε` and `X_y - X_{y'} + X_ε` for `|y - y'| < ε`, using that `ε` is now a
  *coordinate*);
* `K₁ := projLastIter (n) 2 K = {u | ∃ y y' (u∘e1 ∈ T ∧ u∘e2 ∈ T ∧ |y - y'| < ε)}`; its complement
  `K₁ᶜ` is the inner *failure* condition.  Intersect with the hypothesis set
  `HypSet := {dist w' w < η ∧ z ≠ 0 ∧ (∀j, |z_j| < η) ∧ z' ≠ 0 ∧ (∀j, |z'_j| < η)}` (all
  coordinate atoms, `‖z‖ < η ↔ ∀j |z_j| < η` uses `η > 0` via `pi_norm_lt_iff`);
* `K₂ := projLastIter (n') (a + 2*b) (K₁ᶜ ∩ HypSet) = {(w,ε,η) | ∃ w' z z', (Hyp ∧ ¬∃yy'(...))}`;
  `K₂ᶜ = {(w,ε,η) | ∀ w' z z', Hyp → ¬∃yy'(...)}`; intersect with `{0 < η}` and project away `η`
  (`projLastIter (n'') 1`), then complement: this yields
  `{(w,ε) | 0 < ε ∧ ∀ η (0 < η → ∃ w' z z' (Hyp ∧ ¬∃yy'(...)))}` — using `¬∃yy'(T1 ∧ T2 ∧ |y-y'| < ε)
  ↔ ¬(Fin.append w' z ∈ c1Loc f ∧ Fin.append w' z' ∈ c1Loc f ∧ |dDir ... - dDir ...| < ε)`, which is
  exactly the failure condition of `failSet` (`failSet = (goodSet)ᶜ`, and `goodSet`'s conclusion is
  precisely that conjunction).

Since the reindexings `e1`, `e2` depend only on `a`, `b`, and all remaining atoms are coordinate
comparisons (constant format and degree), the format is a constant `A` and the degree is `q.eval D`
for a fixed polynomial `q`, independent of `j`.  (`a = 0` and `b = 0` are harmless degenerate
cases.) -/
theorem failSet_mem (S : WilkiesDesign.SOMin) (hder : S.SharpDeriv) {a b F D : ℕ}
    (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hG : WilkiesDesign.CG.famGraph G ∈ S.Ω F D (a + b + 1)) :
    ∃ (A : ℕ) (q : Polynomial ℕ), ∀ (j : Fin b),
      {u : Fin (a + 1) → ℝ | 0 < u (Fin.last a) ∧
        Fin.init u ∈ failSet G j (u (Fin.last a))} ∈ S.Ω A (q.eval D) (a + 1) := by
  obtain ⟨a0, b0, hb0⟩ := Work.WilG4b.derivGraph_mem S hder (a + b) F
  refine ⟨a0 + (500 * (a + b) + 5000),
    Polynomial.C 2 * Work.WilG1.psubst b0 1 + Polynomial.C (10000 * (a + b) + 100000), ?_⟩
  intro j
  have hGf : graphOf (Work.WilG4c.famFun G) ∈ S.Ω F D (a + b + 1) := by
    rw [Work.WilG4c.graphOf_famFun]; exact hG
  have hT : Work.WilG4b.derivGraph (Work.WilG4c.famFun G) (Fin.natAdd a j) ∈
      S.Ω a0 ((Work.WilG1.psubst b0 1).eval D) ((a + b) + 1) := by
    have h := hb0 D (Work.WilG4c.famFun G) (Fin.natAdd a j) hGf
    rw [← Work.WilG1.eval_psubst b0 1 D] at h
    exact h
  have hmem := fmChain_mem S (Work.WilG4b.derivGraph (Work.WilG4c.famFun G) (Fin.natAdd a j))
    (F0 := a0) (degT := (Work.WilG1.psubst b0 1).eval D) hT
  rw [fmChain_eq_target G j] at hmem
  have hdeg : ((Polynomial.C 2 * Polynomial.X + Polynomial.C (10000 * (a + b) + 100000)).eval
        ((Work.WilG1.psubst b0 1).eval D)) =
      ((Polynomial.C 2 * Work.WilG1.psubst b0 1
        + Polynomial.C (10000 * (a + b) + 100000)).eval D) := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [hdeg] at hmem
  exact hmem

end Work.WilCrux
