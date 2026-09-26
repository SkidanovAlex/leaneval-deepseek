import Submission.Work.SurgeryInvariance.Loops
import Submission.Work.SurgeryInvariance.WindingSpan.carrier_eq_top

/-!
# Basic API for the surgery vocabulary

Symmetry, reflexivity and the trivial (constant) sweep, so that the structures of this subproject
can be used without unfolding their definitions.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.SurgeryInvariance

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## Symmetry and reflexivity of the local moves -/

theorem RegionEquivalent.refl (X : Set R3) : RegionEquivalent P X X :=
  ⟨fun γ hγ => ⟨γ, hγ, rfl⟩, fun γ hγ => ⟨γ, hγ, rfl⟩⟩

theorem RegionEquivalent.symm {X Y : Set R3} (h : RegionEquivalent P X Y) :
    RegionEquivalent P Y X := ⟨h.2, h.1⟩

theorem RegionEquivalent.comm {X Y : Set R3} :
    RegionEquivalent P X Y ↔ RegionEquivalent P Y X :=
  ⟨RegionEquivalent.symm, RegionEquivalent.symm⟩

theorem RegionIsotopic.symm {X Y : Set R3} (h : RegionIsotopic P X Y) :
    RegionIsotopic P Y X := by
  obtain ⟨e, heF, heFinv, himage, ⟨H, hHcont, hH0, hH1, hHmem⟩,
    ⟨K, hKcont, hK0, hK1, hKmem⟩⟩ := h
  refine ⟨e.symm, heFinv, heF, ?_, ⟨K, hKcont, hK0, hK1, hKmem⟩, ?_⟩
  · rw [← himage]
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, hxy⟩
      rw [← hxy, Homeomorph.symm_apply_apply]
      exact hz
    · intro hx
      exact ⟨e x, ⟨x, hx, rfl⟩, Homeomorph.symm_apply_apply e x⟩
  · exact ⟨H, hHcont, hH0, hH1, hHmem⟩

theorem RegionIsotopic.refl' (X : Set R3) : RegionIsotopic P X X := RegionIsotopic.refl P X

theorem SurgeryStepZero.symm {A A' : Set R3} (h : SurgeryStepZero P A A') :
    SurgeryStepZero P A' A := by
  obtain ⟨Z, hZ, hA, hA', hZopen, hcase⟩ := h
  exact ⟨Z, hZ, hA', hA, hZopen, hcase.symm⟩

theorem SurgeryShape.symm {A A' : Set R3} (h : SurgeryShape P A A') :
    SurgeryShape P A' A := by
  obtain ⟨D, hA, hA', hcase⟩ := h
  exact ⟨D, hA', hA, hcase.symm⟩

/-! ## The trivial sweep -/

/-- **Every region gives a (trivial) sweep**: a family with no surgery at all. -/
def Sweep.const (U : Set R3) : Sweep P where
  region := fun _ => U
  exc := ∅
  regular := fun t _ => ⟨1, one_pos, by simp, fun s _ => RegionIsotopic.refl P U⟩
  surgery := by intro t ht; simp at ht

/-- Every region gives a trivial loop-level sweep. -/
def SweepLoops.const (U : Set R3) : SweepLoops P where
  region := fun _ => U
  exc := ∅
  regular := fun t _ => ⟨1, one_pos, by simp, fun s _ => RegionEquivalent.refl (P := P) U⟩
  surgery := by intro t ht; simp at ht

@[simp] theorem Sweep.const_region (U : Set R3) (t : ℝ) : (Sweep.const (P := P) U).region t = U :=
  rfl

/-! ## The ball-based form of the local model of a saddle

At a `2`-surgery the sphere family changes only inside a small ball `b` around the critical point,
and the trace `F ∩ b` of that ball on the surface is a disc.  The following two lemmas turn that
description into the surgery hypotheses used in this subproject: if `b` is an open ball whose trace
on `F` is the interior of an embedded disc `D`, and the two regions agree outside `b` with one of
them disjoint from `F ∩ b`, then the region changed by the disc interior of the surgery.
-/

/-- **The trace of an open set on the surface is open in the surface.**  In particular the region
`F ∩ int(S_t)` is open in `F` for free, and the trace `F ∩ b` of an open ball is open in `F`. -/
theorem isOpenInCarrier_carrier_inter {b : Set R3} (hb : IsOpen b) :
    IsOpenInCarrier P (P.carrier ∩ b) := by
  simpa [IsOpenInCarrier, Set.preimage_inter] using hb.preimage continuous_subtype_val

/-- **The ball description of a `2`-surgery gives the geometric surgery shape.** -/
theorem surgeryShape_of_ball {A A' b : Set R3} {D : DiscRegion P}
    (hb : IsOpen b) (hDb : D.interior = P.carrier ∩ b)
    (hopen : IsOpenInCarrier P A') (hA : A = A' ∪ (P.carrier ∩ b))
    (hdisj : Disjoint A' (P.carrier ∩ b)) : SurgeryShape P A A' := by
  have hZopen : IsOpenInCarrier P (P.carrier ∩ b) := isOpenInCarrier_carrier_inter (P := P) hb
  have hAopen : IsOpenInCarrier P A := by rw [hA]; exact isOpenInCarrier_union P hopen hZopen
  refine ⟨D, hAopen, hopen, Or.inl ⟨?_, ?_⟩⟩
  · rw [hA, hDb]
  · rw [hDb]; exact hdisj

/-- **The ball description of a `2`-surgery gives the zero-winding-content surgery step.** -/
theorem surgeryStepZero_of_ball {A A' b : Set R3} {D : DiscRegion P}
    (hb : IsOpen b) (hDb : D.interior = P.carrier ∩ b)
    (hopen : IsOpenInCarrier P A') (hA : A = A' ∪ (P.carrier ∩ b))
    (hdisj : Disjoint A' (P.carrier ∩ b)) : SurgeryStepZero P A A' :=
  (surgeryShape_of_ball hb hDb hopen hA hdisj).toZero

/-! ## Non-vacuity of Pardon's hypotheses -/

/-- **The hypotheses of Pardon's Lemma are consistent**: there is a sweep whose initial (and final)
region contains an essential loop — take the whole surface `F`, swept without any surgery. -/
theorem exists_sweep_with_essentialLoop (P : Work.CoreTopology.ParamTorus) :
    ∃ S : Sweep P,
      P.ContainsEssentialLoop (S.region 0) ∧ P.ContainsEssentialLoop (S.region 1) := by
  refine ⟨Sweep.const (P := P) P.carrier, ?_, ?_⟩
  · rw [Sweep.const_region]
    exact (windingSpan_ne_bot_iff P P.carrier).mp (by
      rw [Work.SurgeryInvariance.WindingSpan.carrier_eq_top]; exact top_ne_bot)
  · rw [Sweep.const_region]
    exact (windingSpan_ne_bot_iff P P.carrier).mp (by
      rw [Work.SurgeryInvariance.WindingSpan.carrier_eq_top]; exact top_ne_bot)

/-! ## Corollaries of the constancy of the winding span -/

/-- Along a sweep, if the winding span of one region is everything, so is that of every other. -/
theorem Sweep.windingSpan_eq_top (S : Sweep P) (h : WindingSpan P (S.region 0) = ⊤) (t : ℝ) :
    WindingSpan P (S.region t) = ⊤ :=
  (S.windingSpan_eq t).trans h

/-- Along a sweep, the dichotomy `⊥` / `⊤` only has to be checked at a single parameter. -/
theorem Sweep.dichotomy (S : Sweep P) (t : ℝ)
    (h : WindingSpan P (S.region t) = ⊥ ∨ WindingSpan P (S.region t) = ⊤) (s : ℝ) :
    WindingSpan P (S.region s) = ⊥ ∨ WindingSpan P (S.region s) = ⊤ := by
  have h' : WindingSpan P (S.region s) = WindingSpan P (S.region t) := by
    rw [S.windingSpan_eq s, S.windingSpan_eq t]
  rw [h']
  exact h

/-- **Pardon's `doublebubble` in the loop-level vocabulary.** -/
theorem SweepLoops.double_bubble {S : SweepLoops P} {H₁ H₂ : Set R3} {D : DiscRegion P}
    (hopen₁ : IsOpenInCarrier P H₁) (hopen₂ : IsOpenInCarrier P H₂) (hdisj : Disjoint H₁ H₂)
    (hdisjZ : Disjoint (H₁ ∪ H₂) D.interior)
    (hcover : S.region 1 = (H₁ ∪ H₂) ∪ D.interior)
    (h0 : P.ContainsEssentialLoop (S.region 0)) :
    P.ContainsEssentialLoop H₁ ∨ P.ContainsEssentialLoop H₂ :=
  double_bubble_persistence hopen₁ hopen₂ hdisj hdisjZ hcover (S.spherefamily h0)

end

end Work.SurgeryInvariance
