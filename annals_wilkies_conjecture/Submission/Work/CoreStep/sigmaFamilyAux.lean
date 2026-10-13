/-
  CoreStep: the auxiliary lemmas used by the assembly of `Work.CoreStep.sigmaFamily`.

  These are the "mechanical" pieces of the Σ-assembly:
  * the polynomial degree bound `sigmaDegBound` (dominating six polynomial-in-`D` bounds);
  * the transport of the frontier decompositions into Σ-coverages
    (`sigmaFrontierCover`, `sigmaPairFrontierCover`);
  * the existence of the frontier decompositions of a `Good` stratum together with the dimension
    drop (`frontierDecomp`, `pairFrontierDecomp`).
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.CoreStep.GermDefs
import Submission.Work.CoreStep.SigmaFamDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.CoreStep

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep (pPair absReindex)

/-! ## The polynomial degree bound -/

theorem sigmaDegBound (Fp : ℕ) (b5 b5' b5'' b6 b6' : Polynomial ℕ) :
    ∃ B : Polynomial ℕ, ∀ D : ℕ,
      D ≤ B.eval D ∧ b6.eval D ≤ B.eval D ∧ b5'.eval (b6.eval D) ≤ B.eval D ∧
      b5.eval (2 * (1 + Fp) * (1 + 2 * D) ^ 2) ≤ B.eval D ∧
      b5.eval (2 * (Fp + 2) * (1 + 2 * D) ^ 2) ≤ B.eval D ∧
      b5''.eval (b6'.eval (b5.eval (2 * (Fp + 2) * (1 + 2 * D) ^ 2))) ≤ B.eval D := by
  refine ⟨Polynomial.X + b6 + b5'.comp b6 +
      b5.comp (Polynomial.C (2 * (1 + Fp)) * (1 + Polynomial.C 2 * Polynomial.X) ^ 2) +
      b5.comp (Polynomial.C (2 * (Fp + 2)) * (1 + Polynomial.C 2 * Polynomial.X) ^ 2) +
      b5''.comp (b6'.comp (b5.comp
        (Polynomial.C (2 * (Fp + 2)) * (1 + Polynomial.C 2 * Polynomial.X) ^ 2))),
    fun D => ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_ofNat]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-! ## Frontier coverages -/

theorem sigmaFrontierCover {n m : ℕ} (T : Stratum 0 (n + (m + 1)))
    (TL : List (Stratum 0 (n + (m + 1))))
    (h : closure T.X.set \ T.X.set = ⋃ V ∈ TL, V.X.set) :
    frontierSet n m T =
      ⋃ V ∈ TL, projFirst n (pPair n m) '' (sigAbs n m V).set := by
  have h1 : projFirst n (m + 1) '' (closure (absSet T) \ absSet T)
      = ⋃ V ∈ TL, projFirst n (m + 1) '' (absPt '' V.X.set) := by
    rw [frontier_absSet, h]
    rw [image_iUnion₂ (absPt) TL (fun V : Stratum 0 (n + (m + 1)) => V.X.set)]
    rw [image_iUnion₂ (projFirst n (m + 1)) TL
      (fun V : Stratum 0 (n + (m + 1)) => absPt '' V.X.set)]
  have h2 : ∀ V : Stratum 0 (n + (m + 1)),
      projFirst n (pPair n m) '' (sigAbs n m V).set
        = projFirst n (m + 1) '' (absPt '' V.X.set) := by
    intro V
    rw [sigAbs_proj n m V, absSet_eq_image]
  rw [frontierSet, h1]
  simp only [h2]

theorem sigmaPairFrontierCover {n m : ℕ} (V : Stratum 0 (pPair n m))
    (UL : List (Stratum 0 (pPair n m)))
    (h : closure V.X.set \ V.X.set = ⋃ U ∈ UL, U.X.set) :
    pairFrontierBaseFst n m V =
      ⋃ U ∈ UL, projFirst n (pPair n m) '' (sigPair n m U).set := by
  have h1 : pairBaseFst n m '' (closure (absPt '' V.X.set) \ absPt '' V.X.set)
      = ⋃ U ∈ UL, pairBaseFst n m '' (absPt '' U.X.set) := by
    rw [← absPt_image_closure (N := pPair n m),
      ← absPt_image_sdiff (N := pPair n m) (closure V.X.set) V.X.set, h]
    rw [image_iUnion₂ (absPt) UL (fun U : Stratum 0 (pPair n m) => U.X.set)]
    rw [image_iUnion₂ (pairBaseFst n m) UL
      (fun U : Stratum 0 (pPair n m) => absPt '' U.X.set)]
  have h2 : ∀ U : Stratum 0 (pPair n m),
      projFirst n (pPair n m) '' (sigPair n m U).set
        = pairBaseFst n m '' (absPt '' U.X.set) := by
    intro U
    rw [sigPair_proj n m U, pairSubBaseFst]
  rw [pairFrontierBaseFst, h1]
  simp only [h2]

/-! ## The frontier decompositions -/

theorem frontierDecomp
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
        ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
          (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
          X.set = (⋃ S ∈ L, S.X.set) ∧
          L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (hE6 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ)
      (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
      ∃ Y Y' : WilkiesDesign.E.SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
        Y'.deg ≤ b.eval X.deg ∧ Y.set = WilkiesDesign.E.fiberClosure X.set ∧
        Y'.set = WilkiesDesign.E.fiberClosure X.set \ X.set)
    (n m F : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))),
      T.Good → T.X.fmt ≤ F → ∃ TL : List (WilkiesDesign.E.Stratum 0 (n + (m + 1))),
        (∀ V ∈ TL, V.Good ∧ V.X.set ⊆ closure T.X.set \ T.X.set ∧ V.X.fmt ≤ a ∧
          V.deg ≤ b.eval T.deg) ∧
        (closure T.X.set \ T.X.set = ⋃ V ∈ TL, V.X.set) ∧
        (∀ V ∈ TL, V.X.set.Nonempty → T.j < V.j) := by
  obtain ⟨a6, b6, h6⟩ := hE6 F
  obtain ⟨a5, b5, h5⟩ := hE5 a6
  refine ⟨a5, b5.comp b6, fun T hT hfmt => ?_⟩
  obtain ⟨Y, Y', -, -, hY'f, hY'd, -, hY's⟩ := h6 0 (n + (m + 1)) T.X hfmt
  have hY'set : Y'.set = closure T.X.set \ T.X.set := by
    rw [hY's, fiberClosure_zero]
  obtain ⟨TL, -, hTLgood, hTLcov, -⟩ := h5 0 (n + (m + 1)) Y' hY'f
  have hsub : ∀ V ∈ TL, V.X.set ⊆ closure T.X.set \ T.X.set := by
    intro V hV
    have h1 : V.X.set ⊆ (⋃ S ∈ TL, S.X.set) := fun z hz => Set.mem_iUnion₂.mpr ⟨V, hV, hz⟩
    rw [← hTLcov, hY'set] at h1
    exact h1
  refine ⟨TL, ?_, ?_, ?_⟩
  · intro V hV
    refine ⟨(hTLgood V hV).2.2, hsub V hV, (hTLgood V hV).1, ?_⟩
    have h1 : V.deg ≤ b5.eval Y'.deg := (hTLgood V hV).2.1
    have h3 : T.X.deg ≤ T.deg := Nat.le_add_right _ _
    calc V.deg ≤ b5.eval Y'.deg := h1
      _ ≤ b5.eval (b6.eval T.X.deg) := pol_eval_mono_nat hY'd
      _ ≤ b5.eval (b6.eval T.deg) := pol_eval_mono_nat (pol_eval_mono_nat h3)
      _ = (b5.comp b6).eval T.deg := by rw [Polynomial.eval_comp]
  · rw [hY'set] at hTLcov
    exact hTLcov
  · intro V hV hne
    exact frontierDrop_abs T V hT (hTLgood V hV).2.2 (hsub V hV) hne

theorem pairFrontierDecomp
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
        ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
          (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
          X.set = (⋃ S ∈ L, S.X.set) ∧
          L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (hE6 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ)
      (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
      ∃ Y Y' : WilkiesDesign.E.SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
        Y'.deg ≤ b.eval X.deg ∧ Y.set = WilkiesDesign.E.fiberClosure X.set ∧
        Y'.set = WilkiesDesign.E.fiberClosure X.set \ X.set)
    (n m F : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (V : WilkiesDesign.E.Stratum 0 (pPair n m)),
        V.Good → V.X.fmt ≤ F →
        ∃ UL : List (WilkiesDesign.E.Stratum 0 (pPair n m)),
          (∀ U ∈ UL, U.Good ∧ U.X.set ⊆ closure V.X.set \ V.X.set ∧ U.X.fmt ≤ a ∧
            U.deg ≤ b.eval V.deg) ∧
          (closure V.X.set \ V.X.set = ⋃ U ∈ UL, U.X.set) ∧
          (∀ U ∈ UL, U.X.set.Nonempty → V.j < U.j) := by
  obtain ⟨a6, b6, h6⟩ := hE6 F
  obtain ⟨a5, b5, h5⟩ := hE5 a6
  refine ⟨a5, b5.comp b6, fun V hV hfmt => ?_⟩
  obtain ⟨Y, Y', -, -, hY'f, hY'd, -, hY's⟩ := h6 0 (pPair n m) V.X hfmt
  have hY'set : Y'.set = closure V.X.set \ V.X.set := by
    rw [hY's, fiberClosure_zero]
  obtain ⟨UL, -, hULgood, hULcov, -⟩ := h5 0 (pPair n m) Y' hY'f
  have hsub : ∀ U ∈ UL, U.X.set ⊆ closure V.X.set \ V.X.set := by
    intro U hU
    have h1 : U.X.set ⊆ (⋃ S ∈ UL, S.X.set) := fun z hz => Set.mem_iUnion₂.mpr ⟨U, hU, hz⟩
    rw [← hULcov, hY'set] at h1
    exact h1
  refine ⟨UL, ?_, ?_, ?_⟩
  · intro U hU
    refine ⟨(hULgood U hU).2.2, hsub U hU, (hULgood U hU).1, ?_⟩
    have h1 : U.deg ≤ b5.eval Y'.deg := (hULgood U hU).2.1
    have h3 : V.X.deg ≤ V.deg := Nat.le_add_right _ _
    calc U.deg ≤ b5.eval Y'.deg := h1
      _ ≤ b5.eval (b6.eval V.X.deg) := pol_eval_mono_nat hY'd
      _ ≤ b5.eval (b6.eval V.deg) := pol_eval_mono_nat (pol_eval_mono_nat h3)
      _ = (b5.comp b6).eval V.deg := by rw [Polynomial.eval_comp]
  · rw [hY'set] at hULcov
    exact hULcov
  · intro U hU hne
    exact frontierDrop_abs V U hV (hULgood U hU).2.2 (hsub U hU) hne

end Work.CoreStep
