import Mathlib
import Submission.Work.RatHurewicz.finiteGraphDefs

namespace Work.RatHurewicz.GraphPi

open scoped unitInterval

set_option linter.unusedSectionVars false

noncomputable section

variable {E V : Type} [Fintype E] [Fintype V] [TopologicalSpace E] [DiscreteTopology E]
  [TopologicalSpace V] [DiscreteTopology V]

/-! ## A global continuous retraction of the graph onto the edge parameter

The whole content of `midArcLift` is the continuity of the pointwise forced lift.  Rather than
proving that `psiFunGraph a b e` is an embedding on `{s | 1/4 < s < 3/4}` (which would need the
topology of the quotient to be understood locally), we exhibit a *global* continuous map
`arcPhi a b : GraphX a b → I` which is the identity on the parameter of every point of the middle
arc: because the endpoints of each edge are glued to the vertices, the value on a vertex is free,
and the map

`arcF : V ⊕ (E × I) → I`,  `Sum.inl v ↦ 0`,  `Sum.inr (e,s) ↦ min s (3 - 3 s)`

is well defined on representatives (both ends of an edge are sent to `0`) and continuous, hence
descends to the quotient.  On `[1/4, 3/4]` it is the identity. -/

/-- The continuous map of `I` fixing `[0,3/4]` and sending `1` to `0`. -/
def phiI (s : I) : I :=
  ⟨min (s : ℝ) (3 - 3 * (s : ℝ)), by
    refine ⟨le_min (s.2.1) (by linarith [s.2.2]), le_trans (min_le_left _ _) s.2.2⟩⟩

@[simp] lemma phiI_coe (s : I) : (phiI s : ℝ) = min (s : ℝ) (3 - 3 * (s : ℝ)) := rfl

lemma continuous_phiI : Continuous phiI := by
  apply Continuous.subtype_mk
  fun_prop

lemma phiI_eq_self {s : I} (h : (s : ℝ) ≤ 3 / 4) : phiI s = s := by
  ext; rw [phiI_coe]; exact min_eq_left (by linarith)

lemma phiI_eq_zero_of_coe_eq_zero {s : I} (h : (s : ℝ) = 0) : phiI s = 0 := by
  ext; rw [phiI_coe, h]; norm_num

lemma phiI_eq_zero_of_coe_eq_one {s : I} (h : (s : ℝ) = 1) : phiI s = 0 := by
  ext; rw [phiI_coe, h]; norm_num

/-- `arcF` on the disjoint union `V ⊕ (E × I)` of the vertex set and the edge strips: the vertices
and both ends of every edge are sent to `0`, the interior of an edge is sent to `phiI s`. -/
def arcF : V ⊕ (E × I) → I := Sum.elim (fun _ => (0 : I)) (fun p => phiI p.2)

lemma continuous_arcF : Continuous (arcF (E := E) (V := V)) :=
  Continuous.sumElim continuous_const (continuous_phiI.comp continuous_snd)

@[simp] lemma arcF_inl (v : V) : arcF (E := E) (Sum.inl v) = 0 := rfl
@[simp] lemma arcF_inr (e : E) (s : I) : arcF (V := V) (Sum.inr (e, s)) = phiI s := rfl

/-- `arcF` agrees with the canonical representative of a point. -/
lemma arcF_canon (a b : E → V) (p : V ⊕ (E × I)) :
    arcF (V := V) (Work.RatHurewicz.canon a b p) = arcF (V := V) p := by
  rcases p with v | ⟨e, s⟩
  · rfl
  · rw [Work.RatHurewicz.canon_inr]
    by_cases h0 : (s : ℝ) = 0
    · rw [if_pos h0, arcF_inl, arcF_inr]
      exact (phiI_eq_zero_of_coe_eq_zero h0).symm
    · by_cases h1 : (s : ℝ) = 1
      · rw [if_neg h0, if_pos h1, arcF_inl, arcF_inr]
        exact (phiI_eq_zero_of_coe_eq_one h1).symm
      · rw [if_neg h0, if_neg h1]

/-- `arcF` is constant on the classes of the graph relation. -/
lemma arcF_eq_of_eqvGen (a b : E → V) (p q : V ⊕ (E × I))
    (h : (Work.RatHurewicz.graphSetoid a b).r p q) :
    arcF (V := V) p = arcF (V := V) q := by
  have hc := Work.RatHurewicz.canon_eq_of_eqvGen a b h
  rw [← arcF_canon a b p, hc, arcF_canon a b q]

/-- The continuous retraction of the graph onto the parameter of the edge `e`. -/
def arcPhi (a b : E → V) : Work.RatHurewicz.GraphX a b → I :=
  Quotient.lift (s := Work.RatHurewicz.graphSetoid a b) (arcF (V := V))
    (arcF_eq_of_eqvGen a b)

lemma continuous_arcPhi (a b : E → V) : Continuous (arcPhi a b) :=
  Continuous.quotient_lift continuous_arcF (arcF_eq_of_eqvGen a b)

@[simp] lemma arcPhi_gq (a b : E → V) (p : V ⊕ (E × I)) :
    arcPhi a b (Work.RatHurewicz.gq a b p) = arcF (V := V) p :=
  Quotient.lift_mk (s := Work.RatHurewicz.graphSetoid a b) (arcF (V := V))
    (arcF_eq_of_eqvGen a b) p

/-- On the middle arc, `arcPhi` recovers the edge parameter. -/
lemma arcPhi_psi (a b : E → V) (e : E) {s : I} (h : (s : ℝ) ≤ 3 / 4) :
    arcPhi a b (Work.RatHurewicz.psiFunGraph a b e s) = s := by
  show arcF (V := V) (Sum.inr (e, s)) = s
  rw [arcF_inr]
  exact phiI_eq_self h

/-- A path whose image lies in the middle arc of a *fixed* edge lifts continuously to the edge
parameter.  The witness is forced pointwise by `gq_inr_inr_interior`, so only continuity is at
stake: on `{s : I | 1/4 < s < 3/4}` the map `psiFunGraph a b e` is an embedding (the preimage of an
interval `(a,b) ⊆ (1/4,3/4)` under `gq` is `Sum.inr '' ({e} × (a,b))`, open because `E` is
discrete), so `sg` is the continuous inverse of `psiFunGraph a b e` composed with `c`. -/
theorem midArcLift {E V : Type} [Fintype E] [Fintype V] [TopologicalSpace E] [DiscreteTopology E] [TopologicalSpace V] [DiscreteTopology V] (a b : E → V) {e : E} {x y : Work.RatHurewicz.GraphX a b} (c : Path x y)
    (hc : ∀ t, c t ∈ Work.RatHurewicz.midArc a b e) :
    ∃ sg : C(unitInterval, unitInterval), (∀ t, c t = Work.RatHurewicz.psiFunGraph a b e (sg t)) ∧
      (∀ t, (1 / 4 : ℝ) < (sg t : ℝ) ∧ (sg t : ℝ) < 3 / 4) := by
  have hcont : Continuous fun t : I => arcPhi a b (c t) :=
    (continuous_arcPhi a b).comp c.continuous
  refine ⟨⟨fun t => arcPhi a b (c t), hcont⟩, ?_, ?_⟩
  · intro t
    obtain ⟨s, hs1, hs2, hcs⟩ := hc t
    have hval : ((⟨fun t : I => arcPhi a b (c t), hcont⟩ : C(I, I)) t : ℝ)
        = (arcPhi a b (c t) : ℝ) := rfl
    have key : (arcPhi a b (c t) : ℝ) = (s : ℝ) := by
      rw [hcs]
      exact congrArg Subtype.val (arcPhi_psi a b e (le_of_lt hs2))
    have hsg : ((⟨fun t : I => arcPhi a b (c t), hcont⟩ : C(I, I)) t) = s := by
      apply Subtype.ext
      rw [hval, key]
    rw [← hsg] at hcs
    exact hcs
  · intro t
    obtain ⟨s, hs1, hs2, hcs⟩ := hc t
    have hval : ((⟨fun t : I => arcPhi a b (c t), hcont⟩ : C(I, I)) t : ℝ)
        = (arcPhi a b (c t) : ℝ) := rfl
    have key : (arcPhi a b (c t) : ℝ) = (s : ℝ) := by
      rw [hcs]
      exact congrArg Subtype.val (arcPhi_psi a b e (le_of_lt hs2))
    rw [hval, key]
    exact ⟨hs1, hs2⟩

end

end Work.RatHurewicz.GraphPi
