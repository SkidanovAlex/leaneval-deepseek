/-
  WilG4a — final assembly.

  `WilkiesDesign.CG.G4_base_proved` is the hole `G4_base` of `Submission.Work.Wilkies.CG.Spec`,
  in the form corrected by the lead's audit of 2026-10-11
  (`sources/wilkiesG4/wilkies_g4_audit.md`): the first conjunct is the frozen `FLem S p 1`, and
  the second is `Work.WilG4a.F1AffineW S p` (BNZ Corollary 5.5 corrected, in the frozen
  `Fin 1 → ℝ` coordinates) rather than the frozen `F1Affine S p`, which the audit refutes at
  `p = 1`.  Since `F1Affine` implies `F1AffineW` (`F1AffineW_of_F1Affine`, in the lead-owned
  file), this is a faithful weakening, and the corresponding statement with `F1AffineW`
  replaced by `F1Affine` is *not* provable; `G4_base_proved_of_F1Affine` below records that
  reduction explicitly, so a caller who has the frozen statement recovers the original
  conclusion.

  Both halves are proved in this directory and transported to the frozen `Fin 1 → ℝ`
  coordinates by `fleem_one_of_fleem1` and (for the first half) nothing else — `FLem1` is the
  `ℝ`-coordinate form of `FLem S p 1`.

  Beside the spec hypotheses `S`, `hcd : S.SharpCD`, `hder : S.SharpDeriv` and `p`, the only
  extra arguments are the two one-dimensional inputs of area G3, taken as leading hypotheses
  verbatim (`hG3a` = `G3_discrete_Cr`, `hG3b` = `G3_affine_cover`).
-/
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.Bounds
import Submission.Work.WilG4a.ChartUnion
import Submission.Work.WilG4a.F1Affine1W
import Submission.Work.WilG4a.F1AffineW
import Submission.Work.WilG4a.signConst_decomposition
import Submission.Work.WilG4a.f1affine1_all
import Submission.Work.WilG4a.f1affine1W_all
import Submission.Work.WilG4a.f1affineW_of_f1affine1W
import Submission.Work.WilG4a.lipschitz_charts
import Submission.Work.WilG4a.pullback_graph_mem
import Submission.Work.WilG4a.affineChart_graph_mem
import Submission.Work.WilG4a.fleem1_of_parts_W
import Submission.Work.WilG4a.fleem_one_of_fleem1
import Submission.Work.WilG3.Discrete
import Submission.Work.WilG3.Cover

set_option autoImplicit false
noncomputable section
open Classical
namespace WilkiesDesign.CG

open WilkiesDesign

/-- The two one-dimensional inputs of area G3: BNZ Lemma 5.4 (`G3_discrete_Cr`) and the
Whitney-type affine cover (`G3_affine_cover`). -/
abbrev G3Hyp : Prop :=
  (∀ (r : ℕ) (f : ℝ → ℝ), ContDiffOn ℝ (r + 1) f (Set.Ioo 0 1) →
      (∀ x ∈ Set.Ioo (0 : ℝ) 1, f x ∈ Set.Ioo (0 : ℝ) 1) →
      (∀ j ≤ r + 1,
        (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ iteratedDerivWithin j f (Set.Ioo 0 1) x) ∨
        (∀ x ∈ Set.Ioo (0 : ℝ) 1, iteratedDerivWithin j f (Set.Ioo 0 1) x ≤ 0)) →
      ∀ M : ℝ, 1 < M → ∀ j ≤ r, ∀ x ∈ Set.Ioo (0 : ℝ) 1, (j : ℝ) / M < x →
        x < 1 - j / M → |iteratedDerivWithin j f (Set.Ioo 0 1) x| < M ^ j) ∧
  (∀ (r : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
      ∃ s : Finset (ℝ × ℝ), (s.card : ℝ) ≤ 8 * (r + 1) * (-Real.log ε + 2) ∧
        (∀ q ∈ s, 0 < q.1 ∧ q.1 < q.2 ∧ q.2 < 1 ∧
          (q.2 - q.1) * (r + 1) ≤ min q.1 (1 - q.2)) ∧
        Set.Icc ε (1 - ε) ⊆ ⋃ q ∈ s, Set.Icc q.1 q.2)

/-- The `n = 1` family lemma in `ℝ`-coordinates, as needed on the way to `FLem S p 1`. -/
theorem FLem1_proved (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (p : ℕ)
    (hG3a : ∀ (r : ℕ) (f : ℝ → ℝ), ContDiffOn ℝ (r + 1) f (Set.Ioo 0 1) →
      (∀ x ∈ Set.Ioo (0 : ℝ) 1, f x ∈ Set.Ioo (0 : ℝ) 1) →
      (∀ j ≤ r + 1,
        (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ iteratedDerivWithin j f (Set.Ioo 0 1) x) ∨
        (∀ x ∈ Set.Ioo (0 : ℝ) 1, iteratedDerivWithin j f (Set.Ioo 0 1) x ≤ 0)) →
      ∀ M : ℝ, 1 < M → ∀ j ≤ r, ∀ x ∈ Set.Ioo (0 : ℝ) 1, (j : ℝ) / M < x →
        x < 1 - j / M → |iteratedDerivWithin j f (Set.Ioo 0 1) x| < M ^ j)
    (hG3b : ∀ (r : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
      ∃ s : Finset (ℝ × ℝ), (s.card : ℝ) ≤ 8 * (r + 1) * (-Real.log ε + 2) ∧
        (∀ q ∈ s, 0 < q.1 ∧ q.1 < q.2 ∧ q.2 < 1 ∧
          (q.2 - q.1) * (r + 1) ≤ min q.1 (1 - q.2)) ∧
        Set.Icc ε (1 - ε) ⊆ ⋃ q ∈ s, Set.Icc q.1 q.2) :
    Work.WilG4a.FLem1 S p :=
  Work.WilG4a.fleem1_of_parts_W S hcd hder (Work.WilG4a.lipschitz_charts S hcd hder)
    (fun q F => Work.WilG4a.pullback_graph_mem S q F)
    (Work.WilG4a.f1affine1W_all S hcd hder
      (Work.WilG4a.signConst_decomposition S hcd hder) hG3a hG3b)
    (fun q F' => Work.WilG4a.affineChart_graph_mem S q F') p

/-- **`G4_base`** (BNZ §5.1), in the corrected form: the `n = 1` case of the family lemma
together with `F1AffineW` (BNZ Corollary 5.5 corrected), provided the two one-dimensional inputs
of area G3. -/
theorem G4_base_proved (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (p : ℕ)
    (hG3a : ∀ (r : ℕ) (f : ℝ → ℝ), ContDiffOn ℝ (r + 1) f (Set.Ioo 0 1) →
      (∀ x ∈ Set.Ioo (0 : ℝ) 1, f x ∈ Set.Ioo (0 : ℝ) 1) →
      (∀ j ≤ r + 1,
        (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ iteratedDerivWithin j f (Set.Ioo 0 1) x) ∨
        (∀ x ∈ Set.Ioo (0 : ℝ) 1, iteratedDerivWithin j f (Set.Ioo 0 1) x ≤ 0)) →
      ∀ M : ℝ, 1 < M → ∀ j ≤ r, ∀ x ∈ Set.Ioo (0 : ℝ) 1, (j : ℝ) / M < x →
        x < 1 - j / M → |iteratedDerivWithin j f (Set.Ioo 0 1) x| < M ^ j)
    (hG3b : ∀ (r : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
      ∃ s : Finset (ℝ × ℝ), (s.card : ℝ) ≤ 8 * (r + 1) * (-Real.log ε + 2) ∧
        (∀ q ∈ s, 0 < q.1 ∧ q.1 < q.2 ∧ q.2 < 1 ∧
          (q.2 - q.1) * (r + 1) ≤ min q.1 (1 - q.2)) ∧
        Set.Icc ε (1 - ε) ⊆ ⋃ q ∈ s, Set.Icc q.1 q.2) :
    FLem S p 1 ∧ Work.WilG4a.F1AffineW S p :=
  ⟨Work.WilG4a.fleem_one_of_fleem1 S p (FLem1_proved S hcd hder p hG3a hG3b),
    Work.WilG4a.f1affineW_of_f1affine1W S p
      (Work.WilG4a.f1affine1W_all S hcd hder
        (Work.WilG4a.signConst_decomposition S hcd hder) hG3a hG3b p)⟩

/-- The frozen statement of `G4_base` follows from the corrected one together with the
(audit-refuted) frozen `F1Affine`.  This records the exact relation between the two forms. -/
theorem G4_base_proved_of_F1Affine (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (p : ℕ)
    (hG3a : ∀ (r : ℕ) (f : ℝ → ℝ), ContDiffOn ℝ (r + 1) f (Set.Ioo 0 1) →
      (∀ x ∈ Set.Ioo (0 : ℝ) 1, f x ∈ Set.Ioo (0 : ℝ) 1) →
      (∀ j ≤ r + 1,
        (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ iteratedDerivWithin j f (Set.Ioo 0 1) x) ∨
        (∀ x ∈ Set.Ioo (0 : ℝ) 1, iteratedDerivWithin j f (Set.Ioo 0 1) x ≤ 0)) →
      ∀ M : ℝ, 1 < M → ∀ j ≤ r, ∀ x ∈ Set.Ioo (0 : ℝ) 1, (j : ℝ) / M < x →
        x < 1 - j / M → |iteratedDerivWithin j f (Set.Ioo 0 1) x| < M ^ j)
    (hG3b : ∀ (r : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
      ∃ s : Finset (ℝ × ℝ), (s.card : ℝ) ≤ 8 * (r + 1) * (-Real.log ε + 2) ∧
        (∀ q ∈ s, 0 < q.1 ∧ q.1 < q.2 ∧ q.2 < 1 ∧
          (q.2 - q.1) * (r + 1) ≤ min q.1 (1 - q.2)) ∧
        Set.Icc ε (1 - ε) ⊆ ⋃ q ∈ s, Set.Icc q.1 q.2)
    (hF1 : F1Affine S p) : FLem S p 1 ∧ F1Affine S p :=
  ⟨(G4_base_proved S hcd hder p hG3a hG3b).1, hF1⟩

/-- `G4_base` with the two one-dimensional inputs of area G3 discharged from area G3's proved
modules (`Submission.Work.WilG3.Discrete`, `Submission.Work.WilG3.Cover`). -/
theorem G4_base_proved_wired (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (p : ℕ) :
    FLem S p 1 ∧ Work.WilG4a.F1AffineW S p :=
  G4_base_proved S hcd hder p
    (fun r f hf hI hsign M hM j hj x hx hx2 =>
      G3_discrete_Cr_proved r f hf hI hsign M hM j hj x hx hx2)
    (fun r ε hε hε1 => G3_affine_cover_proved r ε hε hε1)

end WilkiesDesign.CG
