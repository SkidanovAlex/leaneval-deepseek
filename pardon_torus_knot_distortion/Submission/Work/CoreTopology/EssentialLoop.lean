import Submission.Work.CoreTopology.Disk
import Submission.Work.CoreTopology.PieceData
import Submission.Work.CoreTopology.positive_scale
import Submission.Work.CoreTopology.DoubleBubble
import Submission.Work.CoreTopology.MustBeInessential

/-!
# "Contains an essential loop" and the geometric form of Pardon's lemmas

This file collects the geometric predicates used by Pardon's argument, together with the
results already proved about them.

* `ParamTorus.ContainsEssentialLoop P U` (defined in `Work.CoreTopology.Winding`) says that a
  region `U ⊆ ℝ³` contains a closed curve of the torus `F = P.carrier` with nonzero winding
  vector — equivalently (since a loop of the torus is null-homotopic exactly when its winding
  vector vanishes) a loop not null-homotopic in `F`.
* `ContainsEssentialLoop U` is the case `P = standard`; `ContainsSimpleEssentialLoop U` requires
  the loop to be embedded (simple), which is the form in which Pardon's argument uses it.
* `essentialBallRadii` is the set of radii `r` for which some closed ball of radius `r`
  contains an essential loop of the standard torus; `positive_scale_set` records that this set
  is bounded below by the positive constant `1` (Pardon's Lemma 4).
* `mustbeinessential_geometric` and `double_bubble_geometric` are Pardon's Lemmas 2 and 3
  phrased with these predicates rather than with the abstract homological invariant.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CoreTopology

noncomputable section

/-- For the standard torus: the region `U ⊆ ℝ³` contains a closed curve of the torus with
nonzero winding vector.  Abbreviation for `ParamTorus.ContainsEssentialLoop standard`. -/
def ContainsEssentialLoop (U : Set R3) : Prop := standard.ContainsEssentialLoop U

theorem ContainsEssentialLoop.mono {U V : Set R3} (h : U ⊆ V)
    (hU : ContainsEssentialLoop U) : ContainsEssentialLoop V :=
  standard.containsEssentialLoop_mono h hU

/-- The region `U ⊆ ℝ³` contains a **simple** essential loop of the standard torus: a *simple*
(embedded) closed curve of the torus with nonzero winding vector whose image lies in `U`.  This
is the property Pardon's argument propagates: a genus-`1` subsurface of `F` contains such a
loop, and the components of `S ∩ F` are simple loops. -/
def ContainsSimpleEssentialLoop (U : Set R3) : Prop :=
  ∃ γ : ClosedCurve standard, IsSimple standard γ ∧ IsEssential standard γ ∧ ∀ t : ℝ, γ t ∈ U

theorem ContainsSimpleEssentialLoop.mono {U V : Set R3} (h : U ⊆ V)
    (hU : ContainsSimpleEssentialLoop U) : ContainsSimpleEssentialLoop V := by
  obtain ⟨γ, hsimp, hess, hmem⟩ := hU
  exact ⟨γ, hsimp, hess, fun t => h (hmem t)⟩

theorem ContainsSimpleEssentialLoop.toContainsEssentialLoop {U : Set R3}
    (hU : ContainsSimpleEssentialLoop U) : ContainsEssentialLoop U := by
  obtain ⟨γ, -, hess, hmem⟩ := hU
  exact ⟨γ, hess, hmem⟩

/-- The set of radii `r ≥ 0` for which some closed ball of radius `r` of `ℝ³` contains an
essential loop of the standard torus. -/
def essentialBallRadii : Set ℝ :=
  {r | 0 ≤ r ∧ ∃ (x : R3) (γ : ClosedCurve standard),
      IsEssential standard γ ∧ ∀ t : ℝ, γ t ∈ Metric.closedBall x r}

theorem one_le_of_mem_essentialBallRadii {r : ℝ} (hr : r ∈ essentialBallRadii) : 1 ≤ r := by
  obtain ⟨-, x, γ, hess, hmem⟩ := hr
  exact positive_scale x r γ hess hmem

/-- No ball of radius `< 1` contains a loop of the standard torus with nonzero winding vector
(Pardon's Lemma 4 in the form used in the proof). -/
theorem not_containsEssentialLoop_closedBall_of_lt_one (x : R3) {r : ℝ} (hr : r < 1) :
    ¬ ContainsEssentialLoop (Metric.closedBall x r) := by
  rintro ⟨γ, hess, hmem⟩
  exact absurd (positive_scale x r γ hess hmem) (not_le.mpr hr)

/-- No ball of radius `< 1` contains a *simple* loop of the standard torus with nonzero winding
vector. -/
theorem not_containsSimpleEssentialLoop_closedBall_of_lt_one (x : R3) {r : ℝ} (hr : r < 1) :
    ¬ ContainsSimpleEssentialLoop (Metric.closedBall x r) :=
  fun h => not_containsEssentialLoop_closedBall_of_lt_one x hr h.toContainsEssentialLoop

/-- **Pardon's Lemma 4 (`positive_scale`), in the form used in the proof.**  The set of radii
of balls of `ℝ³` that contain an essential loop of the standard torus is bounded below by the
positive constant `1`.  Iterating the double-bubble construction therefore cannot produce
arbitrarily small regions containing an essential loop. -/
theorem positive_scale_set : ∃ c : ℝ, 0 < c ∧ ∀ r ∈ essentialBallRadii, c ≤ r :=
  ⟨1, one_pos, fun _ hr => one_le_of_mem_essentialBallRadii hr⟩

/-- **Pardon's Lemma 2 (`mustbeinessential`) in the geometric vocabulary.**  If the sphere `S`
meets `β` in strictly fewer than `I(F, β)` points, then `S` contains no essential loop of the
torus.  The hypothesis `hclean` is the geometric content of the innermost argument (see
`Work.CoreTopology.mustbeinessential`). -/
theorem mustbeinessential_geometric (P : ParamTorus) (β : ClosedCurve P) (S : Set R3)
    (hclean : ∀ α : ClosedCurve P, IsEssential P α → (∀ t : ℝ, α.γ t ∈ S) →
      ∃ α' : ClosedCurve P, IsSimple P α' ∧ IsEssential P α' ∧
        BoundsDiskInComplement P α' ∧
        Set.encard (Set.range α'.γ ∩ Set.range β.γ) ≤
          Set.encard (Set.range α.γ ∩ Set.range β.γ))
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β) :
    ¬ P.ContainsEssentialLoop S := by
  rintro ⟨γ, hess, hmem⟩
  exact mustbeinessential P β S hclean hSβ γ hmem hess

/-- **Pardon's Lemma 3 (`doublebubble`), geometric form.**

Let `Sint` be the region inside the original sphere `S`, `H₁`, `H₂` the interiors of the two
halves of a double bubble, and `W : ℝ → Submodule ℚ A` the homological invariant along the
surgery family from `S` to the two halves (`W 0 = H.hom Sint` and
`W 1 = H.hom H₁ ⊔ H.hom H₂`).

Assume the dichotomy `0 / all` for the pieces, the surgery dimension bounds, and that
`F ∩ Sint` contains an essential loop.  Then so does `F ∩ H_i` for `i = 1` or `i = 2`. -/
theorem double_bubble_geometric {P : ParamTorus} {A : Type*} [AddCommGroup A] [Module ℚ A]
    [FiniteDimensional ℚ A] [Nontrivial A]
    (H : HomPieceData P A) (W : ℝ → Submodule ℚ A) (Sint H₁ H₂ : Set R3)
    (hlink : ∀ U : Set R3, H.HasEssentialLoop U ↔ P.ContainsEssentialLoop U)
    (hA : 1 < Module.finrank ℚ A)
    (hdich : H.Dichotomy)
    (hSess : P.ContainsEssentialLoop Sint)
    (hval : ∀ t : ℝ, W t = ⊥ ∨ W t = ⊤)
    (hstep : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε →
      Module.finrank ℚ ↥(W s) ≤ Module.finrank ℚ ↥(W t) + 1 ∧
      Module.finrank ℚ ↥(W t) ≤ Module.finrank ℚ ↥(W s) + 1)
    (hW0 : W 0 = H.hom Sint) (hdecomp : W 1 = H.hom H₁ ⊔ H.hom H₂) :
    P.ContainsEssentialLoop H₁ ∨ P.ContainsEssentialLoop H₂ := by
  rcases double_bubble H W Sint H₁ H₂ hA hdich ((hlink Sint).mpr hSess) hval hstep hW0 hdecomp
    with h | h
  · exact Or.inl ((hlink H₁).mp h)
  · exact Or.inr ((hlink H₂).mp h)

end

end Work.CoreTopology
