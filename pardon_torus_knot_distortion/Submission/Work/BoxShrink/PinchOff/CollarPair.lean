import Submission.Work.BoxShrink.PinchOff.TwoPiece
import Submission.Work.BoxShrink.PinchOff.SignSplit
import Submission.Work.BoxShrink.PinchOff.TwoGate
import Submission.Work.BoxShrink.PinchOff.Drop

/-!
# The pinch as a two-piece cover of the box region

The residual of the area (`DropCase`, `Drop.lean`) is: at a transverse, closed-tame configuration
whose box sphere and slice carry no essential loop, if the two half-regions carry no essential loop
then the box region is at most one-dimensional.  The whole chapter has so far paired the box region
against the two **closed halves**

  `UpperSide = Ω ∩ {G ≥ 0}`,  `LowerSide = Ω ∩ {G ≤ 0}`,

whose intersection is the slice `Σ` — and the connectors of the alternating-partition datum
(`PairingData.lean`) must lie inside that intersection, which is why the reduction so far needed
`Σ` to be path connected (`SliceConnected.lean`, `TwoGate.lean`).

This module removes that restriction.  The observation is that the *only* property of the two
halves the sign split uses (`SignSplit.lean`) is the containment `UpperSide ⊆ A`,
`LowerSide ⊆ B`; hence the box region may be paired against **any** two sets `A ⊇ UpperSide`,
`B ⊇ LowerSide` with `A ∪ B = Ω`, provided

* their intersection `A ∩ B` is **path connected** — this is the interface whose connectedness
  supplies the connectors of the datum, and it may be much bigger than the slice `Σ`;
* both pieces have **vanishing winding span**.

Such a pair is a `CollarPair`; the two-piece bound of `TwoPiece.lean` then gives `W(Ω) = ⊥`
(`windingSpan_Omega_eq_bot_of_collarPair`), which is `DropCase`.

* `CollarPairExists` and `dropCase_of_collarPairExists` — the residual in this vocabulary;
* `SpiderPinchData` — the form in which the pair is *produced* geometrically: a single connected set
  `N ⊇ Σ` inside `Ω` whose addition to either half preserves the vanishing of the span.  The pair
  is `(UpperSide ∪ N, LowerSide ∪ N)`, whose intersection is exactly `N`
  (`collarPair_of_spiderPinchData`), so the connectors of the datum are paths inside `N` — the
  "finger move" of Pardon's argument, which slides the crossings of a loop along the trace until
  consecutive crossings are joined inside the interface;
* `spiderPinchData_of_isPathConnected_sigma` — the case `N := Σ`, which recovers the reduction of
  `SliceConnected.lean` (a path connected slice);
* `spiderPinchData_of_spider_upper` — if `N` lies in the upper closed half then the `UpperSide ∪ N`
  condition is automatic and the whole residual is the *single* condition
  `W(LowerSide ∪ N) = ⊥`: the loops that have to be pushed off through `N` are exactly the loops
  that dip from the lower half into `N` and back.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
variable {A B : Set R3}

/-! ## The collar pair -/

/-- **A collar pair of the pinch**: two sets of the carrier containing the two closed halves, whose
union is the box region, whose intersection is path connected, and each of which has vanishing
winding span.  The interface `A ∩ B` plays the role of the slice in the pinch; it contains the
slice (`Sigma_subset_inter`) but may be much larger, and it is its path connectedness (not the
slice's) which the connectors of the datum require. -/
structure CollarPair (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (A B : Set R3) : Prop where
  /-- the upper closed half is contained in the first piece -/
  upperSide_subset : UpperSide ψ s c σ u ⊆ A
  /-- the lower closed half is contained in the second piece -/
  lowerSide_subset : LowerSide ψ s c σ u ⊆ B
  /-- the two pieces cover the box region -/
  cover : A ∪ B = Omega ψ s c σ
  /-- the interface is path connected: this is what supplies the connectors -/
  inter_connected : IsPathConnected (A ∩ B)
  /-- the first piece is inessential -/
  span_A : Work.SurgeryInvariance.WindingSpan (surface ψ) A = ⊥
  /-- the second piece is inessential -/
  span_B : Work.SurgeryInvariance.WindingSpan (surface ψ) B = ⊥

/-- The first piece of a collar pair lies on the surface. -/
theorem CollarPair.subset_carrier (h : CollarPair ψ s c σ u A B) :
    A ⊆ (surface ψ).carrier := by
  intro x hx
  have hx' : x ∈ A ∪ B := Or.inl hx
  rw [h.cover] at hx'
  exact Omega_subset_carrier hx'

/-- The second piece of a collar pair lies on the surface. -/
theorem CollarPair.subset_carrier_right (h : CollarPair ψ s c σ u A B) :
    B ⊆ (surface ψ).carrier := by
  intro x hx
  have hx' : x ∈ A ∪ B := Or.inr hx
  rw [h.cover] at hx'
  exact Omega_subset_carrier hx'

/-- The corner of a collar pair lies on the surface. -/
theorem CollarPair.inter_subset_carrier (h : CollarPair ψ s c σ u A B) :
    A ∩ B ⊆ (surface ψ).carrier :=
  fun _ hx => h.subset_carrier hx.1

/-- The slice is contained in the interface of a collar pair. -/
theorem CollarPair.sigma_subset_inter (h : CollarPair ψ s c σ u A B) :
    Sigma ψ s c σ u ⊆ A ∩ B :=
  fun _ hx => ⟨h.upperSide_subset (sigma_subset_upperSide hx),
    h.lowerSide_subset (sigma_subset_lowerSide hx)⟩

/-- **The box region is inessential from a collar pair and the crossing finiteness.**  The sign
split gives the connector-free datum for the pair (`SignSplit.lean`), the path connectedness of the
interface turns it into the datum with connectors (`PairingData.lean`), the two-piece bound
(`TwoPiece.lean`) gives `W(Ω) ≤ W(A) ⊔ W(B) = ⊥`.  This is the sharp form of `DropCase`. -/
theorem windingSpan_Omega_eq_bot_of_collarPair
    {A B : Set R3} (hfin : FiniteCrossing ψ s c σ u) (h : CollarPair ψ s c σ u A B) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) = ⊥ := by
  have hpart := alternatingPartitionDataWeak_of_finite_crossing_of_subset
    h.upperSide_subset h.lowerSide_subset (by rw [h.cover]) hfin
  have hbot := windingSpan_union_eq_bot_of_weakData_of_isPathConnected_inter
    h.subset_carrier h.subset_carrier_right hpart h.inter_connected h.span_A h.span_B
  rw [h.cover] at hbot
  exact hbot

/-! ## The residual in this vocabulary -/

/-- **The residual of the pinch as the existence of a collar pair.** -/
def CollarPairExists : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → ∃ A B : Set R3, CollarPair ψ s c σ u A B

/-- **The general position of the loops** (the box-local crossing finiteness, all configurations). -/
def FiniteCrossingAll : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → FiniteCrossing ψ s c σ u

/-- **The residual from a collar pair at every configuration.** -/
theorem dropCase_of_collarPairExists (h : CollarPairExists) (hfin : FiniteCrossingAll) :
    DropCase := by
  intro ψ s c σ u hT _hTa _hS _hZ _hbot
  obtain ⟨A, B, hpair⟩ := h ψ s c σ u hT
  have h0 := windingSpan_Omega_eq_bot_of_collarPair (A := A) (B := B) (hfin ψ s c σ u hT) hpair
  rw [h0, finrank_bot]
  omega

/-! ## Producing the pair from a single connected interface -/

/-- **The geometric datum which produces a collar pair**: one connected set containing the slice,
inside the box region, whose addition to either closed half preserves the vanishing of the winding
span.  The only content is the two span conditions: `N ⊆ UpperSide ∪ N` and `N ⊆ LowerSide ∪ N`
make `W(N) = ⊥` automatic, and the whole point is that adding `N` does not create an essential
loop in either piece. -/
def SpiderPinchData (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Prop :=
  ∃ N : Set R3, Sigma ψ s c σ u ⊆ N ∧ N ⊆ Omega ψ s c σ ∧ IsPathConnected N ∧
    Work.SurgeryInvariance.WindingSpan (surface ψ) (UpperSide ψ s c σ u ∪ N) = ⊥ ∧
    Work.SurgeryInvariance.WindingSpan (surface ψ) (LowerSide ψ s c σ u ∪ N) = ⊥

/-- **A connected interface produces a collar pair.**  The pair is
`(UpperSide ∪ N, LowerSide ∪ N)`; its intersection is exactly `N`, so the connectors of the datum
are paths inside `N`. -/
theorem collarPair_of_spiderPinchData {N : Set R3}
    (hslice : Sigma ψ s c σ u ⊆ N) (hN : N ⊆ Omega ψ s c σ) (hconn : IsPathConnected N)
    (hUp : Work.SurgeryInvariance.WindingSpan (surface ψ) (UpperSide ψ s c σ u ∪ N) = ⊥)
    (hLo : Work.SurgeryInvariance.WindingSpan (surface ψ) (LowerSide ψ s c σ u ∪ N) = ⊥) :
    CollarPair ψ s c σ u (UpperSide ψ s c σ u ∪ N) (LowerSide ψ s c σ u ∪ N) where
  upperSide_subset := Set.subset_union_left
  lowerSide_subset := Set.subset_union_left
  cover := by
    refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · rw [Omega_eq_upperSide_union_lowerSide]
      rcases hx with (hx | hx) | (hx | hx)
      · exact Or.inl hx
      · exact Omega_eq_upperSide_union_lowerSide ▸ hN hx
      · exact Or.inr hx
      · exact Omega_eq_upperSide_union_lowerSide ▸ hN hx
    · rw [Omega_eq_upperSide_union_lowerSide] at hx
      rcases hx with hx | hx
      · exact Or.inl (Or.inl hx)
      · exact Or.inr (Or.inl hx)
  inter_connected := by
    have hinter : (UpperSide ψ s c σ u ∪ N) ∩ (LowerSide ψ s c σ u ∪ N) = N := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_union]
      constructor
      · rintro ⟨hx | hx, hy | hy⟩
        · exact hslice (by rw [← upperSide_inter_lowerSide]; exact ⟨hx, hy⟩)
        · exact hy
        · exact hx
        · exact hx
      · intro hx
        exact ⟨Or.inr hx, Or.inr hx⟩
    rw [hinter]
    exact hconn
  span_A := hUp
  span_B := hLo

/-- **The residual from the connected-interface datum at every configuration.** -/
theorem collarPairExists_of_spiderPinchData
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → SpiderPinchData ψ s c σ u) :
    CollarPairExists := by
  intro ψ s c σ u hT
  obtain ⟨N, hslice, hN, hconn, hUp, hLo⟩ := h ψ s c σ u hT
  exact ⟨_, _, collarPair_of_spiderPinchData hslice hN hconn hUp hLo⟩

/-- **`DropCase` from the connected-interface datum.** -/
theorem dropCase_of_spiderPinchData
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → SpiderPinchData ψ s c σ u)
    (hfin : FiniteCrossingAll) : DropCase :=
  dropCase_of_collarPairExists (collarPairExists_of_spiderPinchData h) hfin

/-! ## Instances of the pair -/

/-- **The pair in the case of a path connected slice**: the two closed halves themselves.  This is
the case reduced in `SliceConnected.lean`; through the collar-pair formulation it is the instance
`N := Σ` of the connected-interface datum. -/
theorem collarPair_of_isPathConnected_sigma
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (hbot : Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) = ⊥)
    (hconn : IsPathConnected (Sigma ψ s c σ u)) :
    CollarPair ψ s c σ u (UpperSide ψ s c σ u) (LowerSide ψ s c σ u) where
  upperSide_subset := subset_rfl
  lowerSide_subset := subset_rfl
  cover := Omega_eq_upperSide_union_lowerSide.symm
  inter_connected := by
    rw [upperSide_inter_lowerSide]
    exact hconn
  span_A := windingSpan_upperSide_eq_bot_of_transverseSlice hT hbot
  span_B := windingSpan_lowerSide_eq_bot_of_transverseSlice hT hbot

/-- **The connected-interface datum with `N := Σ`**: a path connected slice carries it. -/
theorem spiderPinchData_of_isPathConnected_sigma
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (hbot : Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) = ⊥)
    (hconn : IsPathConnected (Sigma ψ s c σ u)) :
    SpiderPinchData ψ s c σ u := by
  refine ⟨Sigma ψ s c σ u, Subset.rfl, Sigma_subset_Omega, hconn, ?_, ?_⟩
  · rw [Set.union_eq_left.mpr sigma_subset_upperSide]
    exact windingSpan_upperSide_eq_bot_of_transverseSlice hT hbot
  · rw [Set.union_eq_left.mpr sigma_subset_lowerSide]
    exact windingSpan_lowerSide_eq_bot_of_transverseSlice hT hbot

/-- **`DropCase` in the case of a path connected slice**, through the collar-pair route: this
recovers `dropCase_of_finiteCrossing_of_isPathConnected_slice` (`SliceConnected.lean`). -/
theorem dropCase_of_finiteCrossing_of_isPathConnected_slice'
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
      IsPathConnected (Sigma ψ s c σ u) ∧ FiniteCrossing ψ s c σ u) :
    DropCase := by
  intro ψ s c σ u hT _hTa _hS _hZ hbot
  have hpair := collarPair_of_isPathConnected_sigma (ψ := ψ) (s := s) (c := c) (σ := σ) (u := u)
    hT hbot (h ψ s c σ u hT).1
  have h0 := windingSpan_Omega_eq_bot_of_collarPair (A := UpperSide ψ s c σ u)
    (B := LowerSide ψ s c σ u) (h ψ s c σ u hT).2 hpair
  rw [h0, finrank_bot]
  omega

/-! ## The sharpening when the interface lies in one closed half -/

/-- **If the connected interface lies in the upper closed half, the upper span condition is
automatic.**  The whole residual is then the *single* condition `W(LowerSide ∪ N) = ⊥`: adding the
interface to the upper half changes nothing (it is already inside it), and the content is that the
loops which dip from the lower half into the interface and back do not create an essential loop. -/
theorem spiderPinchData_of_spider_upper {N : Set R3} (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (hbot : Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) = ⊥)
    (hslice : Sigma ψ s c σ u ⊆ N) (hN : N ⊆ Omega ψ s c σ) (hNU : N ⊆ UpperSide ψ s c σ u)
    (hconn : IsPathConnected N)
    (hLo : Work.SurgeryInvariance.WindingSpan (surface ψ) (LowerSide ψ s c σ u ∪ N) = ⊥) :
    SpiderPinchData ψ s c σ u := by
  refine ⟨N, hslice, hN, hconn, ?_, hLo⟩
  rw [Set.union_eq_left.mpr hNU]
  exact windingSpan_upperSide_eq_bot_of_transverseSlice hT hbot

/-- **Dually**: if the connected interface lies in the lower closed half, the lower span condition
is automatic and the residual is the single condition `W(UpperSide ∪ N) = ⊥`. -/
theorem spiderPinchData_of_spider_lower {N : Set R3} (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (hbot : Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) = ⊥)
    (hslice : Sigma ψ s c σ u ⊆ N) (hN : N ⊆ Omega ψ s c σ) (hNL : N ⊆ LowerSide ψ s c σ u)
    (hconn : IsPathConnected N)
    (hUp : Work.SurgeryInvariance.WindingSpan (surface ψ) (UpperSide ψ s c σ u ∪ N) = ⊥) :
    SpiderPinchData ψ s c σ u := by
  refine ⟨N, hslice, hN, hconn, hUp, ?_⟩
  rw [Set.union_eq_left.mpr hNL]
  exact windingSpan_lowerSide_eq_bot_of_transverseSlice hT hbot

/-! ## The reduction is tight: the connected interface is equivalent to the sharp conclusion -/

/-- The upper closed half lies in the box region. -/
theorem upperSide_subset_omega : UpperSide ψ s c σ u ⊆ Omega ψ s c σ :=
  fun _ hx => hx.1

/-- The lower closed half lies in the box region. -/
theorem lowerSide_subset_omega : LowerSide ψ s c σ u ⊆ Omega ψ s c σ :=
  fun _ hx => hx.1

/-- **The connected-interface datum gives the sharp conclusion** `W(Ω) = ⊥` (and hence
`DropCase`), through the collar pair it defines. -/
theorem windingSpan_Omega_eq_bot_of_spiderPinchData (hfin : FiniteCrossing ψ s c σ u)
    (h : SpiderPinchData ψ s c σ u) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) = ⊥ := by
  obtain ⟨N, hslice, hN, hconn, hUp, hLo⟩ := h
  exact windingSpan_Omega_eq_bot_of_collarPair hfin
    (collarPair_of_spiderPinchData hslice hN hconn hUp hLo)

/-- **The reduction is tight**: at a configuration whose box region is path connected, the
connected-interface datum is *equivalent* to the sharp conclusion `W(Ω) = ⊥` — the direction `⟸`
is the instance `N := Ω` (a path connected box region is a connected interface, and adding it to
either half changes nothing).  So nothing is lost in replacing the loop-level conclusion by the
existence of a connected interface. -/
theorem spiderPinchData_iff_omega_eq_bot (hfin : FiniteCrossing ψ s c σ u)
    (hO : IsPathConnected (Omega ψ s c σ)) :
    SpiderPinchData ψ s c σ u ↔
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) = ⊥ := by
  constructor
  · exact windingSpan_Omega_eq_bot_of_spiderPinchData hfin
  · intro h
    refine ⟨Omega ψ s c σ, Sigma_subset_Omega, Subset.rfl, hO, ?_, ?_⟩
    · rw [Set.union_eq_right.mpr upperSide_subset_omega]
      exact h
    · rw [Set.union_eq_right.mpr lowerSide_subset_omega]
      exact h

end

end Work.BoxShrink.PinchOff
