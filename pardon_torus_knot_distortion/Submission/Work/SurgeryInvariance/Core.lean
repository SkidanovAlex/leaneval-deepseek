import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.SurgeryInvariance.Abstract
import Submission.Work.SurgeryInvariance.WindingOf.homotopic_eq
import Submission.Work.SurgeryInvariance.DiscRegion.not_isEssential
import Submission.Work.SurgeryInvariance.Span.le_sup_of_splits
import Submission.Work.SurgeryInvariance.Span.union_eq_sup
import Submission.Work.SurgeryInvariance.SplitsBy.of_shape
import Submission.Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq
import Submission.Work.CoreTopology.EssentialLoop

/-!
# Surgery invariance of Pardon's essential-piece invariant

This is the main file of the subproject: it proves that along a one-parameter family of spheres
with finitely many `2`-surgeries (`Work.SurgeryInvariance.Sweep`) the region `F ∩ int(S_t)` either
contains an essential loop of `F` at *every* parameter or at none — so that Pardon's
`spherefamily` lemma holds, *without* the dichotomy `W t ∈ {⊥, ⊤}` and without the `1`-Lipschitz
dimension bound of `Work.CoreTopology.sphere_family`.

The proof replaces Pardon's `dim_ℚ im(H₁(F ∩ int S_t; ℚ) → H₁(F; ℚ)) ∈ {0, 2g}` by the *whole*
`ℚ`-subspace `WindingSpan P (F ∩ int S_t) ≤ ℚ²` and shows it is **constant**, in three steps:

* `RegionIsotopic.windingSpan_eq` — moving the sphere by an ambient isotopy of `ℝ³` preserving `F`
  transports loops and preserves their winding vectors, hence does not change the winding span
  (this is Pardon's "no surgery, no change");
* `SurgeryStep.windingSpan_eq` — a single `2`-surgery adds or removes the *interior of an embedded
  disc* `D` of `F`; a loop of the new region that is not in the old one lies in `D`, hence is
  inessential, so again the winding span does not change (this is Pardon's "changes by at most
  `1`", in the sharp form "changes by a loop of zero winding");
* `eq_of_locally_const` — a quantity on `ℝ` which is constant near every parameter is constant.

The dichotomy is *not* needed: the argument shows the full subspaces are equal, whence in
particular their vanishing is constant.  (`HomPieceData.Dichotomy` over *all* regions is in fact
false for the winding span: the meridian circle `{φ ↦ P.psi θ φ}` is a region whose winding span is
exactly `ℚ·(0,1)`, see `Work.SurgeryInvariance.WindingSpan.meridianCurve`.)
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.SurgeryInvariance

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The disc lemma and the surgery step -/

/-- **A disc of the surface carries no essential loop**: the winding span of an embedded disc of
`F` is zero. -/
theorem DiscRegion.windingSpan_eq_bot (D : DiscRegion P) :
    WindingSpan P D.carrier = ⊥ := by
  rw [WindingSpan_eq_bot_iff]
  rintro ⟨γ, hess, hγ⟩
  exact Work.SurgeryInvariance.DiscRegion.not_isEssential D γ hγ hess

/-- The interior of an embedded disc of `F` carries no essential loop either. -/
theorem DiscRegion.windingSpan_interior_eq_bot (D : DiscRegion P) :
    WindingSpan P D.interior = ⊥ :=
  le_antisymm (le_trans (WindingSpan_mono P D.interior_subset_carrier)
    (le_of_eq D.windingSpan_eq_bot)) bot_le

/-- The boundary circle of an embedded disc of `F` carries no essential loop: it bounds the disc.
This is the curve level statement of "the newly created (or destroyed) curve of `S_t ∩ F` at a
`2`-surgery is inessential in `F`". -/
theorem DiscRegion.windingSpan_boundary_eq_bot (D : DiscRegion P) :
    WindingSpan P D.boundary = ⊥ :=
  le_antisymm (le_trans (WindingSpan_mono P D.boundary_subset_carrier)
    (le_of_eq D.windingSpan_eq_bot)) bot_le

/-- `SplitsBy` plus a disc of zero winding content gives the span inequality. -/
theorem SplitsBy.windingSpan_le {A A' : Set R3} {D : DiscRegion P}
    (h : SplitsBy P A A' D) : WindingSpan P A ≤ WindingSpan P A' :=
  Work.SurgeryInvariance.Span.le_sup_of_splits h D.windingSpan_eq_bot

/-- **A single `2`-surgery does not change the winding span.** -/
theorem SurgeryStep.windingSpan_eq {A A' : Set R3} (h : SurgeryStep P A A') :
    WindingSpan P A = WindingSpan P A' := by
  obtain ⟨D, h1, h2, -⟩ := h
  exact le_antisymm h1.windingSpan_le h2.windingSpan_le

/-- **The cut-and-paste step, in its simplest form.**  If a region of `F` is the disjoint union of
two open pieces, one of which is the interior of an embedded disc, then the two pieces have the
same winding span: a loop of the larger piece either lies in the smaller one or lies in the disc,
and a disc carries no essential loop. -/
theorem windingSpan_eq_of_union_disc {A A' : Set R3} {D : DiscRegion P}
    (hopen : IsOpenInCarrier P A') (hdisj : Disjoint A' D.interior)
    (hcover : A = A' ∪ D.interior) : WindingSpan P A = WindingSpan P A' := by
  rw [hcover, Work.SurgeryInvariance.Span.union_eq_sup hopen D.open_interior' hdisj,
    D.windingSpan_interior_eq_bot, sup_bot_eq]

/-- **The atomic persistence statement.**  If a region is the disjoint union of an open piece and
the interior of an embedded disc, and it contains an essential loop, then the open piece does
too. -/
theorem containsEssentialLoop_of_union_disc {A A' : Set R3} {D : DiscRegion P}
    (hopen : IsOpenInCarrier P A') (hdisj : Disjoint A' D.interior)
    (hA : A = A' ∪ D.interior) (h : P.ContainsEssentialLoop A) :
    P.ContainsEssentialLoop A' :=
  (windingSpan_ne_bot_iff P A').mp (by
    rw [← windingSpan_eq_of_union_disc hopen hdisj hA]
    exact (windingSpan_ne_bot_iff P A).mpr h)

/-- The same cut-and-paste step for a piece of zero winding span (e.g. a piece whose loops are
known to be inessential by Pardon's inequality `Work.CoreTopology.mustbeinessential`). -/
theorem windingSpan_eq_of_union_zero_span {A A' Z : Set R3}
    (hopen : IsOpenInCarrier P A') (hopenZ : IsOpenInCarrier P Z) (hdisj : Disjoint A' Z)
    (hZ : WindingSpan P Z = ⊥) (hcover : A = A' ∪ Z) : WindingSpan P A = WindingSpan P A' := by
  rw [hcover, Work.SurgeryInvariance.Span.union_eq_sup hopen hopenZ hdisj, hZ, sup_bot_eq]

/-- **A single `2`-surgery, in the form "the change has zero winding content", does not change
the winding span.** -/
theorem SurgeryStepZero.windingSpan_eq {A A' : Set R3} (h : SurgeryStepZero P A A') :
    WindingSpan P A = WindingSpan P A' := by
  obtain ⟨Z, hZ, hA, hA', hZopen, hcase⟩ := h
  rcases hcase with ⟨hcover, hdisj⟩ | ⟨hcover, hdisj⟩
  · have hsplit : WindingSpan P (A' ∪ Z) = WindingSpan P A' ⊔ WindingSpan P Z :=
      Work.SurgeryInvariance.Span.union_eq_sup hA' hZopen hdisj
    rw [hcover, hsplit, hZ, sup_bot_eq]
  · have hsplit : WindingSpan P (A ∪ Z) = WindingSpan P A ⊔ WindingSpan P Z :=
      Work.SurgeryInvariance.Span.union_eq_sup hA hZopen hdisj
    rw [hcover, hsplit, hZ, sup_bot_eq]

/-- The geometric shape of a single `2`-surgery is a surgery in the "zero winding content" form,
taking `Z` to be the interior of the disc. -/
theorem SurgeryShape.toZero {A A' : Set R3} (h : SurgeryShape P A A') :
    SurgeryStepZero P A A' := by
  obtain ⟨D, hA, hA', hcase⟩ := h
  refine ⟨D.interior, D.windingSpan_interior_eq_bot, hA, hA', D.open_interior', ?_⟩
  rcases hcase with ⟨hc, hd⟩ | ⟨hc, hd⟩
  · exact Or.inl ⟨hc, hd⟩
  · exact Or.inr ⟨hc, hd⟩

/-- The geometric shape of a single `2`-surgery satisfies the loop-level surgery step. -/
theorem SurgeryShape.toStep {A A' : Set R3} (h : SurgeryShape P A A') :
    SurgeryStep P A A' := by
  obtain ⟨D, hA, hA', hcase⟩ := h
  rcases hcase with ⟨hcover, hdisj⟩ | ⟨hcover, hdisj⟩
  · refine ⟨D, Work.SurgeryInvariance.SplitsBy.of_shape hA' hcover hdisj, ?_, ?_⟩
    · intro γ hγ
      exact Or.inl (fun t => by rw [hcover]; exact Or.inl (hγ t))
    · rintro x (hx | hx)
      · have hx' : x ∈ A' ∪ D.interior := by rw [← hcover]; exact hx.1
        rcases hx' with h | h
        · exact absurd h hx.2
        · exact D.interior_subset_carrier h
      · have hx' : x ∈ A := by rw [hcover]; exact Or.inl hx.1
        exact absurd hx' hx.2
  · refine ⟨D, ?_, Work.SurgeryInvariance.SplitsBy.of_shape hA hcover hdisj, ?_⟩
    · intro γ hγ
      exact Or.inl (fun t => by rw [hcover]; exact Or.inl (hγ t))
    · rintro x (hx | hx)
      · have hx' : x ∈ A' := by rw [hcover]; exact Or.inl hx.1
        exact absurd hx' hx.2
      · have hx' : x ∈ A ∪ D.interior := by rw [← hcover]; exact hx.1
        rcases hx' with h | h
        · exact absurd h hx.2
        · exact D.interior_subset_carrier h

theorem SurgeryShape.windingSpan_eq {A A' : Set R3} (h : SurgeryShape P A A') :
    WindingSpan P A = WindingSpan P A' :=
  h.toStep.windingSpan_eq

/-! ## Isotopies -/

/-- The image of a closed curve under a map preserving the surface. -/
def curveMap (γ : Work.CoreTopology.ClosedCurve P) (h : R3 → R3) (hcont : Continuous h)
    (hh : ∀ x : R3, x ∈ P.carrier → h x ∈ P.carrier) : Work.CoreTopology.ClosedCurve P where
  γ := fun t => h (γ t)
  cont := hcont.comp γ.cont
  periodic := fun t => by rw [γ.periodic t]
  mem := fun t => hh (γ t) (γ.mem t)

/-- **An isotopy of the ambient space preserving `F` does not change the winding vector.**  The
curves `γ` and `h ∘ γ` are homotopic through the closed curves `H u ∘ γ`, so they have the same
winding vector by `Work.SurgeryInvariance.WindingOf.homotopic_eq`. -/
theorem windingOf_map_eq (γ : Work.CoreTopology.ClosedCurve P) {h : R3 → R3} (hcont : Continuous h)
    (hh : ∀ x : R3, x ∈ P.carrier → h x ∈ P.carrier)
    (H : ℝ → R3 → R3) (hHcont : Continuous (Function.uncurry H))
    (hH0 : ∀ x : R3, H 0 x = x) (hH1 : ∀ x : R3, H 1 x = h x)
    (hHmem : ∀ u : ℝ, ∀ x : R3, x ∈ P.carrier → H u x ∈ P.carrier) :
    windingOf P (curveMap γ h hcont hh) = windingOf P γ := by
  have hhom : Work.CoreTopology.Homotopic P γ (curveMap γ h hcont hh) := by
    refine ⟨fun u t => H u (γ t), ?_, ?_, ?_, ?_, ?_⟩
    · exact hHcont.comp (continuous_fst.prodMk (γ.cont.comp continuous_snd))
    · intro u t
      exact hHmem u (γ t) (γ.mem t)
    · intro t
      exact hH0 (γ t)
    · intro t
      exact hH1 (γ t)
    · intro u t
      exact congrArg (H u) (γ.periodic t)
  exact (Work.SurgeryInvariance.WindingOf.homotopic_eq hhom).symm

/-- The curve-level content of a region isotopy: loops are transported to loops with the same
winding vector, in both directions. -/
theorem RegionIsotopic.toEquivalent {X Y : Set R3} (h : RegionIsotopic P X Y) :
    RegionEquivalent P X Y := by
  obtain ⟨e, heF, heFinv, himage, ⟨H, hHcont, hH0, hH1, hHmem⟩,
    ⟨K, hKcont, hK0, hK1, hKmem⟩⟩ := h
  constructor
  · intro γ hγ
    refine ⟨curveMap γ e e.continuous heF,
      fun t => ?_, windingOf_map_eq γ e.continuous heF H hHcont hH0 hH1 hHmem⟩
    have hx : e (γ t) ∈ e '' X := ⟨γ t, hγ t, rfl⟩
    have hxY : e (γ t) ∈ Y := by rwa [himage] at hx
    show e (γ t) ∈ Y
    exact hxY
  · intro γ hγ
    refine ⟨curveMap γ e.symm e.symm.continuous heFinv,
      fun t => ?_, windingOf_map_eq γ e.symm.continuous heFinv K hKcont hK0 hK1 hKmem⟩
    have ht : γ t ∈ e '' X := by rw [himage]; exact hγ t
    obtain ⟨x, hx, hxe⟩ := ht
    have hs : e.symm (γ t) = x := by rw [← hxe, Homeomorph.symm_apply_apply]
    show e.symm (γ t) ∈ X
    rw [hs]
    exact hx

/-- **An ambient isotopy of `ℝ³` preserving `F` does not change the winding span.** -/
theorem RegionIsotopic.windingSpan_eq {X Y : Set R3} (h : RegionIsotopic P X Y) :
    WindingSpan P X = WindingSpan P Y :=
  Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq h.toEquivalent

/-! ## The sweep -/

/-- **The winding span is constant along a sweep.** -/
theorem Sweep.windingSpan_eq (S : Sweep P) (t : ℝ) :
    WindingSpan P (S.region t) = WindingSpan P (S.region 0) :=
  eq_of_locally_const (f := fun u : ℝ => WindingSpan P (S.region u)) (by
    intro u
    by_cases hu : u ∈ S.exc
    · obtain ⟨ε, hε, hshape⟩ := S.surgery u hu
      exact ⟨ε, hε, fun s hs => by
        rcases hshape s hs with h | h
        · exact h.windingSpan_eq.symm
        · exact h.windingSpan_eq.symm⟩
    · obtain ⟨ε, hε, -, hiso⟩ := S.regular u hu
      exact ⟨ε, hε, fun s hs => (hiso s hs).windingSpan_eq.symm⟩) t 0

/-- The essential-piece invariant is constant along a sweep: `F ∩ int(S_t)` contains an
essential loop for every `t`, or for none. -/
theorem Sweep.containsEssentialLoop_iff (S : Sweep P) (t : ℝ) :
    P.ContainsEssentialLoop (S.region t) ↔ P.ContainsEssentialLoop (S.region 0) := by
  rw [← windingSpan_ne_bot_iff P (S.region t), ← windingSpan_ne_bot_iff P (S.region 0),
    S.windingSpan_eq t]

/-- **Pardon's `spherefamily`.**  If `F ∩ int(S_0)` contains a loop that is essential in `F`,
then so does `F ∩ int(S_1)`. -/
theorem Sweep.spherefamily (S : Sweep P) (h : P.ContainsEssentialLoop (S.region 0)) :
    P.ContainsEssentialLoop (S.region 1) :=
  (S.containsEssentialLoop_iff 1).mpr h

/-- The surgery dimension bounds of `Work.CoreTopology.sphere_family` hold along a sweep — in the
sharp form of *equality* of the dimensions, not just the `1`-Lipschitz bound. -/
theorem Sweep.hstep (S : Sweep P) (t : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε →
      Module.finrank ℚ ↥(WindingSpan P (S.region s)) ≤
          Module.finrank ℚ ↥(WindingSpan P (S.region t)) + 1 ∧
      Module.finrank ℚ ↥(WindingSpan P (S.region t)) ≤
          Module.finrank ℚ ↥(WindingSpan P (S.region s)) + 1 := by
  refine ⟨1, one_pos, fun s _ => ?_⟩
  have h : WindingSpan P (S.region s) = WindingSpan P (S.region t) := by
    rw [S.windingSpan_eq s, S.windingSpan_eq t]
  rw [h]
  exact ⟨Nat.le_succ _, Nat.le_succ _⟩

/-! ## The double bubble -/

/-- **Pardon's `doublebubble` persistence, with the dichotomy and the surgery bound discharged.**

`A = F ∩ int(S)` is the region inside the original sphere, `H₁`, `H₂` those inside the two halves
of the double bubble, and `Z` is the piece through which the `2`-surgery takes place (an embedded
disc of `F`, or any region of zero winding content): the region inside `S` is the union of the two
halves together with `Z`.  If `F ∩ int(S)` contains an essential loop then so does one of the two
halves.

This is Pardon's `doublebubble` (Lemma 3) in the geometric vocabulary, obtained *without* the
dichotomy and without the Lipschitz surgery bound: the two halves together with `Z` fill the
original region, and `Z` contributes nothing to the winding span. -/
theorem double_bubble_persistence_of_zero_span {A H₁ H₂ Z : Set R3}
    (hopen₁ : IsOpenInCarrier P H₁) (hopen₂ : IsOpenInCarrier P H₂) (hdisj : Disjoint H₁ H₂)
    (hopenZ : IsOpenInCarrier P Z) (hdisjZ : Disjoint (H₁ ∪ H₂) Z)
    (hZ : WindingSpan P Z = ⊥)
    (hcover : A = (H₁ ∪ H₂) ∪ Z) (h0 : P.ContainsEssentialLoop A) :
    P.ContainsEssentialLoop H₁ ∨ P.ContainsEssentialLoop H₂ := by
  have hsplit : WindingSpan P ((H₁ ∪ H₂) ∪ Z) =
      WindingSpan P (H₁ ∪ H₂) ⊔ WindingSpan P Z :=
    Work.SurgeryInvariance.Span.union_eq_sup (isOpenInCarrier_union P hopen₁ hopen₂) hopenZ hdisjZ
  have hunion : WindingSpan P (H₁ ∪ H₂) = WindingSpan P H₁ ⊔ WindingSpan P H₂ :=
    Work.SurgeryInvariance.Span.union_eq_sup hopen₁ hopen₂ hdisj
  have hspanA : WindingSpan P A = WindingSpan P H₁ ⊔ WindingSpan P H₂ := by
    rw [hcover, hsplit, hunion, hZ, sup_bot_eq]
  have hne : WindingSpan P H₁ ⊔ WindingSpan P H₂ ≠ ⊥ := by
    rw [← hspanA]
    exact (windingSpan_ne_bot_iff P A).mpr h0
  have hnot : ¬ (WindingSpan P H₁ = ⊥ ∧ WindingSpan P H₂ = ⊥) := by
    rintro ⟨h1, h2⟩
    exact hne (by rw [h1, h2, sup_bot_eq])
  rcases not_and_or.mp hnot with h | h
  · exact Or.inl ((windingSpan_ne_bot_iff P H₁).mp h)
  · exact Or.inr ((windingSpan_ne_bot_iff P H₂).mp h)

/-- **Pardon's `doublebubble` persistence for a `2`-surgery through an embedded disc.** -/
theorem double_bubble_persistence {A H₁ H₂ : Set R3} {D : DiscRegion P}
    (hopen₁ : IsOpenInCarrier P H₁) (hopen₂ : IsOpenInCarrier P H₂) (hdisj : Disjoint H₁ H₂)
    (hdisjZ : Disjoint (H₁ ∪ H₂) D.interior)
    (hcover : A = (H₁ ∪ H₂) ∪ D.interior) (h0 : P.ContainsEssentialLoop A) :
    P.ContainsEssentialLoop H₁ ∨ P.ContainsEssentialLoop H₂ :=
  double_bubble_persistence_of_zero_span hopen₁ hopen₂ hdisj D.open_interior' hdisjZ
    D.windingSpan_interior_eq_bot hcover h0

/-- A `Sweep` whose first and last region are the two halves of a double bubble together with a
disc gives the double-bubble conclusion. -/
theorem Sweep.double_bubble {S : Sweep P} {H₁ H₂ : Set R3} {D : DiscRegion P}
    (hopen₁ : IsOpenInCarrier P H₁) (hopen₂ : IsOpenInCarrier P H₂) (hdisj : Disjoint H₁ H₂)
    (hdisjZ : Disjoint (H₁ ∪ H₂) D.interior)
    (hcover : S.region 1 = (H₁ ∪ H₂) ∪ D.interior)
    (h0 : P.ContainsEssentialLoop (S.region 0)) :
    P.ContainsEssentialLoop H₁ ∨ P.ContainsEssentialLoop H₂ :=
  double_bubble_persistence hopen₁ hopen₂ hdisj hdisjZ hcover (S.spherefamily h0)

end

end Work.SurgeryInvariance
