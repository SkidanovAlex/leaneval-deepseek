import Mathlib
import Submission.Work.BoxShrink.PinchOff.DiscNullHomotopic
import Submission.Work.BoxShrink.PinchOff.IB.Span
import Submission.Work.SurgeryInvariance.All
import Submission.Work.TorusCover.ParamTorus_exists_liftOf

/-!
# Pushing a lifted curve off the interiors of the disc translates

This file proves `Work.BoxShrink.PinchOff.pushoff_plane_interior`: given a lifted closed curve
`Λ : ℝ → ℂ` of the torus `P` lying in the preimage `Xtilde P X` of a region `X` of the surface
which is open in the carrier and contains the boundary circle `D.boundary` of an embedded disc `D`,
there is a quasi-periodic curve with the same period shift `periodPt a b`, still lying in
`Xtilde P X`, which avoids the interiors of *all* lattice translates of the lifted disc, i.e.
`Λ₁ t ∉ Xtilde P D.interior` for every `t`.

The proof has three steps.

* The quasi-periodic curve `Λ` projects to a closed curve `γ` of the torus, contained in `X`, whose
  winding vector is `(a, b)` — the projection is `2π`-periodic by the lattice periodicity of the
  parametrisation, and the pair `(re ∘ Λ, im ∘ Λ)` is a lift of it.
* `γ` can be pushed off the interior of the disc, with its winding vector unchanged: this is the
  local model of Pardon's pinch, here in its *general* form for an arbitrary parametrised torus and
  an arbitrary region containing the boundary circle (`PushOffGeneral.discPushOff_boundary`), proved
  below by the same construction as `Work.BoxShrink.PinchOff.discRoute_holds`: the parametric
  preimage of the interior of the disc is a union of open intervals, and on each of them the curve is
  rerouted along the boundary circle, by the homotopy `PushOffGeneral.Hfun` (a convex combination,
  in the parameter disc, between the curve and its rerouted version, so that it stays on the surface
  and is continuous at the endpoints of the intervals).  The generality needed here is that of an
  arbitrary region `X`: only the hypothesis `D.boundary ⊆ X` is used and not `D.carrier ⊆ X`, which
  is what makes the claim about the *plane* rather than about a particular box.
* Lifting the pushed-off closed curve back through the covering map `planePsi P` and straightening
  it out with the period shift `periodPt a b` produces `Λ₁`.
-/

namespace Work.BoxShrink.PinchOff

open LeanEval.KnotTheory.PardonDistortion
open Set
open Filter
open Classical
open scoped Topology
open Work.CoreTopology
open Work.SurgeryInvariance (DiscRegion)

noncomputable section

/-! ## The rerouting construction

The lemmas below carry out the construction of `Work.BoxShrink.PinchOff.discRoute_holds` (whose
box-specific form is not applicable here), in the generality needed for the plane statement: for an
arbitrary parametrised torus `P`, and with the hypothesis `D.boundary ⊆ X` in place of the stronger
`D.carrier ⊆ X` used in the box setting.  The construction is the rerouting of the excursions of a
loop through the interior of the disc along its boundary circle; the components of the parametric
preimage of the interior are open intervals (`compA`, `compB`), the disc coordinates are used
through the homeomorphism `discHomeo`, and the rerouting point `reroutePt` is the boundary point at
the interpolated angle. -/

namespace PushOffGeneral

variable {P : Work.CoreTopology.ParamTorus}


/-! ## 1. The closed disc as a homeomorph of `𝔻` -/

/-- The homeomorphism `𝔻 ≃ₜ D.carrier` induced by the parametrisation of an embedded disc. -/
def discHomeo {P : Work.CoreTopology.ParamTorus} (D : DiscRegion P) :
    Metric.closedBall (0 : ℂ) 1 ≃ₜ D.carrier :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofInjective D.e D.inj)
    (Continuous.subtype_mk D.e.continuous _)

/-- The parameter of a point of the disc. -/
def discPre {P : Work.CoreTopology.ParamTorus} (D : DiscRegion P) (x : R3)
    (hx : x ∈ D.carrier) : Metric.closedBall (0 : ℂ) 1 :=
  (discHomeo D).symm ⟨x, hx⟩

theorem discPre_spec {P : Work.CoreTopology.ParamTorus} (D : DiscRegion P) (x : R3)
    (hx : x ∈ D.carrier) : D.e (discPre D x hx) = x :=
  congrArg Subtype.val (Homeomorph.apply_symm_apply (discHomeo D) ⟨x, hx⟩)

theorem discPre_continuous {P : Work.CoreTopology.ParamTorus} (D : DiscRegion P) :
    Continuous (fun p : D.carrier => discPre D p.1 p.2) := (discHomeo D).symm.continuous

theorem discPre_norm_le {P : Work.CoreTopology.ParamTorus} (D : DiscRegion P) (x : R3)
    (hx : x ∈ D.carrier) : ‖((discPre D x hx : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ ≤ 1 := by
  have h := (discPre D x hx).2
  rwa [Metric.mem_closedBall, dist_zero_right] at h

theorem mem_interior_iff {P : Work.CoreTopology.ParamTorus} (D : DiscRegion P) (x : R3)
    (hx : x ∈ D.carrier) :
    x ∈ D.interior ↔ ‖((discPre D x hx : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ < 1 := by
  constructor
  · rintro ⟨z, hz, hzex⟩
    have : z = discPre D x hx := D.inj (by rw [hzex, discPre_spec])
    rw [← this]; exact hz
  · intro h
    exact ⟨discPre D x hx, h, discPre_spec D x hx⟩

theorem mem_boundary_iff {P : Work.CoreTopology.ParamTorus} (D : DiscRegion P) (x : R3)
    (hx : x ∈ D.carrier) :
    x ∈ D.boundary ↔ ‖((discPre D x hx : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1 := by
  constructor
  · rintro ⟨z, hz, hzex⟩
    have : z = discPre D x hx := D.inj (by rw [hzex, discPre_spec])
    rw [← this]; exact hz
  · intro h
    exact ⟨discPre D x hx, h, discPre_spec D x hx⟩

theorem carrier_eq_union {P : Work.CoreTopology.ParamTorus} (D : DiscRegion P) :
    D.carrier = D.interior ∪ D.boundary := by
  ext x
  constructor
  · intro hx
    by_cases hin : x ∈ D.interior
    · exact Or.inl hin
    · right
      refine (mem_boundary_iff D x hx).mpr (le_antisymm (discPre_norm_le D x hx) ?_)
      by_contra hlt
      exact hin ((mem_interior_iff D x hx).mpr (not_le.mp hlt))
  · rintro (h | h)
    · exact D.interior_subset_carrier h
    · exact D.boundary_subset_carrier h

theorem disjoint_interior_boundary {P : Work.CoreTopology.ParamTorus} (D : DiscRegion P) :
    Disjoint D.interior D.boundary := by
  rw [Set.disjoint_left]
  intro x hxi hxb
  have hc := D.interior_subset_carrier hxi
  have h1 := (mem_interior_iff D x hc).mp hxi
  have h2 := (mem_boundary_iff D x hc).mp hxb
  linarith

/-- The carrier of an embedded disc is closed in `ℝ³`. -/
theorem isClosed_carrier {P : Work.CoreTopology.ParamTorus} (D : DiscRegion P) :
    IsClosed D.carrier :=
  (isCompact_range D.e.continuous).isClosed


/-! ## 2. Components of a periodic open subset of `ℝ` -/

section Components

variable {U : Set ℝ}

/-- The left endpoint of the connected component of `t` in `U`. -/
def compA (U : Set ℝ) (t : ℝ) : ℝ := sInf (ordConnectedComponent U t)

/-- The right endpoint of the connected component of `t` in `U`. -/
def compB (U : Set ℝ) (t : ℝ) : ℝ := sSup (ordConnectedComponent U t)

theorem isOpen_ordConnectedComponent (hU : IsOpen U) (t : ℝ) :
    IsOpen (ordConnectedComponent U t) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hsub : uIcc t y ⊆ U := mem_ordConnectedComponent.mp hy
  rw [ordConnectedComponent_eq hsub]
  exact ordConnectedComponent_mem_nhds.mpr (hU.mem_nhds (ordConnectedComponent_subset hy))

/-- Shifting a `uIcc` interval. -/
theorem trans_uIcc (c a b z : ℝ) : z ∈ uIcc (a + c) b ↔ z - c ∈ uIcc a (b - c) := by
  have h1 : min (a + c) b = min a (b - c) + c := by
    have := min_add_add_right a (b - c) c
    rwa [show (b - c) + c = b by ring] at this
  have h2 : max (a + c) b = max a (b - c) + c := by
    have := max_add_add_right a (b - c) c
    rwa [show (b - c) + c = b by ring] at this
  have e1 : uIcc (a + c) b = Icc (min a (b - c) + c) (max a (b - c) + c) := by
    rw [show uIcc (a + c) b = Icc (min (a + c) b) (max (a + c) b) from rfl, h1, h2]
  have e2 : uIcc a (b - c) = Icc (min a (b - c)) (max a (b - c)) := rfl
  rw [e1, e2, mem_Icc, mem_Icc]
  constructor <;> intro ⟨hx, hy⟩ <;> constructor <;> linarith

/-- Translation of the order-connected component of a `2π`-periodic set. -/
theorem ordConnectedComponent_add_pi (hper : ∀ t : ℝ, t + 2 * Real.pi ∈ U ↔ t ∈ U) (t : ℝ) :
    ordConnectedComponent U (t + 2 * Real.pi)
      = (fun x => x + 2 * Real.pi) '' ordConnectedComponent U t := by
  ext y
  rw [mem_ordConnectedComponent]
  constructor
  · intro h
    refine ⟨y - 2 * Real.pi, ?_, by ring⟩
    rw [mem_ordConnectedComponent]
    intro z hz
    have hz' : z + 2 * Real.pi ∈ uIcc (t + 2 * Real.pi) y :=
      (trans_uIcc (2 * Real.pi) t y (z + 2 * Real.pi)).mpr (by simpa using hz)
    exact (hper z).mp (h hz')
  · rintro ⟨z, hz, hyz⟩
    subst hyz
    intro w hw
    have hsub : uIcc t z ⊆ U := mem_ordConnectedComponent.mp hz
    have hw' : w - 2 * Real.pi ∈ uIcc t z := by
      have h1 := (trans_uIcc (2 * Real.pi) t (z + 2 * Real.pi) w).mp (by simpa using hw)
      simpa using h1
    exact (by simpa using (hper (w - 2 * Real.pi)).mpr (hsub hw'))

theorem ordConnectedComponent_eq_of_mem {t t' : ℝ}
    (h : t' ∈ ordConnectedComponent U t) :
    ordConnectedComponent U t = ordConnectedComponent U t' :=
  ordConnectedComponent_eq (mem_ordConnectedComponent.mp h)

theorem compA_eq_of_mem {t t' : ℝ} (h : t' ∈ ordConnectedComponent U t) :
    compA U t' = compA U t := by
  rw [compA, compA, ordConnectedComponent_eq_of_mem (U := U) h]

theorem compB_eq_of_mem {t t' : ℝ} (h : t' ∈ ordConnectedComponent U t) :
    compB U t' = compB U t := by
  rw [compB, compB, ordConnectedComponent_eq_of_mem (U := U) h]

/-- The components of a periodic open proper subset of `ℝ` are bounded below. -/
theorem bddBelow_ordConnectedComponent (hU : IsOpen U)
    (hper : ∀ t : ℝ, t + 2 * Real.pi ∈ U ↔ t ∈ U) (hne : ∃ x, x ∉ U) (t : ℝ) :
    BddBelow (ordConnectedComponent U t) := by
  by_contra hb
  have hunb : ∀ a : ℝ, ∃ b ∈ ordConnectedComponent U t, b < a := by
    intro a
    by_contra h
    push_neg at h
    exact hb ⟨a, mem_lowerBounds.mpr (fun b hb' => h b hb')⟩
  have ht : t ∈ U := by
    by_contra ht
    rw [ordConnectedComponent_eq_empty.mpr ht] at hb
    exact hb bddBelow_empty
  have hsub : Iic t ⊆ ordConnectedComponent U t := by
    intro x hx
    obtain ⟨c, hc, hcx⟩ := hunb x
    have hct : uIcc c t ⊆ ordConnectedComponent U t :=
      (inferInstance : (ordConnectedComponent U t).OrdConnected).uIcc_subset hc
        (self_mem_ordConnectedComponent.mpr ht)
    exact hct (mem_uIcc.mpr (Or.inl ⟨le_of_lt hcx, hx⟩))
  have hC : ordConnectedComponent U t
      = (fun x => x + 2 * Real.pi) '' ordConnectedComponent U t := by
    rw [← ordConnectedComponent_add_pi hper t,
      ordConnectedComponent_eq_of_mem (U := U)
        (hsub (show t - 2 * Real.pi ∈ Iic t from by
          rw [mem_Iic]; linarith [Real.pi_pos])),
      ordConnectedComponent_eq_of_mem (U := U) (show t - 2 * Real.pi ∈
        ordConnectedComponent U (t + 2 * Real.pi) from by
          rw [ordConnectedComponent_add_pi hper t]
          exact ⟨t - 4 * Real.pi,
            hsub (show t - 4 * Real.pi ∈ Iic t from by
              rw [mem_Iic]; linarith [Real.pi_pos]), by ring⟩)]
  have step : ∀ y, y ∈ ordConnectedComponent U t ↔
      y - 2 * Real.pi ∈ ordConnectedComponent U t := by
    intro y; constructor
    · intro hy
      rw [hC] at hy
      obtain ⟨w, hw, hwy⟩ := hy
      have hyw : y = w + 2 * Real.pi := by simpa using hwy.symm
      have : y - 2 * Real.pi = w := by linarith
      rw [this]; exact hw
    · intro hy
      rw [hC]
      exact ⟨y - 2 * Real.pi, hy, by ring⟩
  have hIn : ∀ n : ℕ, Iic (t + 2 * Real.pi * (n : ℝ)) ⊆ ordConnectedComponent U t := by
    intro n; induction n with
    | zero => simpa using hsub
    | succ k ih =>
      intro y hy
      rw [step y]
      apply ih
      simp only [mem_Iic] at hy ⊢
      push_cast at hy
      linarith
  obtain ⟨x, hx⟩ := hne
  obtain ⟨n, hn⟩ := exists_nat_ge ((x - t) / (2 * Real.pi))
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hle : x ≤ t + 2 * Real.pi * (n : ℝ) := by
    have := (div_le_iff₀ h2pi).mp hn
    linarith
  exact hx (ordConnectedComponent_subset (hIn n hle))

/-- The components of a periodic open proper subset of `ℝ` are bounded above. -/
theorem bddAbove_ordConnectedComponent (hU : IsOpen U)
    (hper : ∀ t : ℝ, t + 2 * Real.pi ∈ U ↔ t ∈ U) (hne : ∃ x, x ∉ U) (t : ℝ) :
    BddAbove (ordConnectedComponent U t) := by
  by_contra hb
  have hunb : ∀ a : ℝ, ∃ b ∈ ordConnectedComponent U t, a < b := by
    intro a
    by_contra h
    push_neg at h
    exact hb ⟨a, mem_upperBounds.mpr (fun b hb' => h b hb')⟩
  have ht : t ∈ U := by
    by_contra ht
    rw [ordConnectedComponent_eq_empty.mpr ht] at hb
    exact hb bddAbove_empty
  have hsub : Ici t ⊆ ordConnectedComponent U t := by
    intro x hx
    obtain ⟨c, hc, hcx⟩ := hunb x
    have hct : uIcc c t ⊆ ordConnectedComponent U t :=
      (inferInstance : (ordConnectedComponent U t).OrdConnected).uIcc_subset hc
        (self_mem_ordConnectedComponent.mpr ht)
    exact hct (mem_uIcc.mpr (Or.inr ⟨hx, le_of_lt hcx⟩))
  have hC : ordConnectedComponent U t
      = (fun x => x + 2 * Real.pi) '' ordConnectedComponent U t := by
    rw [← ordConnectedComponent_add_pi hper t,
      ordConnectedComponent_eq_of_mem (U := U)
        (hsub (show t + 2 * Real.pi ∈ Ici t from by
          rw [mem_Ici]; linarith [Real.pi_pos]))]
  have step : ∀ y, y ∈ ordConnectedComponent U t ↔
      y - 2 * Real.pi ∈ ordConnectedComponent U t := by
    intro y; constructor
    · intro hy
      rw [hC] at hy
      obtain ⟨w, hw, hwy⟩ := hy
      have hyw : y = w + 2 * Real.pi := by simpa using hwy.symm
      have : y - 2 * Real.pi = w := by linarith
      rw [this]; exact hw
    · intro hy
      rw [hC]
      exact ⟨y - 2 * Real.pi, hy, by ring⟩
  have hIn : ∀ n : ℕ, Ici (t - 2 * Real.pi * (n : ℝ)) ⊆ ordConnectedComponent U t := by
    intro n; induction n with
    | zero => simpa using hsub
    | succ k ih =>
      intro y hy
      have hy' : t - 2 * Real.pi * (k : ℝ) ≤ y + 2 * Real.pi := by
        simp only [mem_Ici] at hy
        push_cast at hy
        linarith
      exact (by simpa using (step (y + 2 * Real.pi)).mp (ih hy'))
  obtain ⟨x, hx⟩ := hne
  obtain ⟨n, hn⟩ := exists_nat_ge ((t - x) / (2 * Real.pi))
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hle : t - 2 * Real.pi * (n : ℝ) ≤ x := by
    have := (div_le_iff₀ h2pi).mp hn
    linarith
  exact hx (ordConnectedComponent_subset (hIn n hle))

theorem sInf_image_add (C : Set ℝ) (hne : C.Nonempty) (hb : BddBelow C) (c : ℝ) :
    sInf ((fun x => x + c) '' C) = sInf C + c := by
  have hneF : ((fun x => x + c) '' C).Nonempty := hne.image _
  have hbF : BddBelow ((fun x => x + c) '' C) := by
    obtain ⟨a, ha⟩ := hb
    refine ⟨a + c, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have := mem_lowerBounds.mp ha x hx
    linarith
  refine le_antisymm ?_ ?_
  · have h : sInf ((fun x => x + c) '' C) - c ≤ sInf C :=
      le_csInf hne (fun x hx => by
        have := csInf_le hbF (show x + c ∈ (fun y => y + c) '' C from ⟨x, hx, rfl⟩)
        linarith)
    linarith
  · refine le_csInf hneF ?_
    rintro y ⟨x, hx, rfl⟩
    show sInf C + c ≤ x + c
    linarith [csInf_le hb hx]

theorem sSup_image_add (C : Set ℝ) (hne : C.Nonempty) (hb : BddAbove C) (c : ℝ) :
    sSup ((fun x => x + c) '' C) = sSup C + c := by
  have hneF : ((fun x => x + c) '' C).Nonempty := hne.image _
  have hbF : BddAbove ((fun x => x + c) '' C) := by
    obtain ⟨a, ha⟩ := hb
    refine ⟨a + c, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have := mem_upperBounds.mp ha x hx
    linarith
  refine le_antisymm ?_ ?_
  · refine csSup_le hneF ?_
    rintro y ⟨x, hx, rfl⟩
    show x + c ≤ sSup C + c
    linarith [le_csSup hb hx]
  · have h : sSup C ≤ sSup ((fun x => x + c) '' C) - c :=
      csSup_le hne (fun x hx => by
        have := le_csSup hbF (show x + c ∈ (fun y => y + c) '' C from ⟨x, hx, rfl⟩)
        linarith)
    linarith

theorem compA_add_pi (hU : IsOpen U)
    (hper : ∀ t : ℝ, t + 2 * Real.pi ∈ U ↔ t ∈ U) (hne : ∃ x, x ∉ U) {t : ℝ} (ht : t ∈ U) :
    compA U (t + 2 * Real.pi) = compA U t + 2 * Real.pi := by
  rw [compA, ordConnectedComponent_add_pi hper t,
    sInf_image_add (ordConnectedComponent U t) ⟨t, self_mem_ordConnectedComponent.mpr ht⟩
      (bddBelow_ordConnectedComponent hU hper hne t) (2 * Real.pi), compA]

theorem compB_add_pi (hU : IsOpen U)
    (hper : ∀ t : ℝ, t + 2 * Real.pi ∈ U ↔ t ∈ U) (hne : ∃ x, x ∉ U) {t : ℝ} (ht : t ∈ U) :
    compB U (t + 2 * Real.pi) = compB U t + 2 * Real.pi := by
  rw [compB, ordConnectedComponent_add_pi hper t,
    sSup_image_add (ordConnectedComponent U t) ⟨t, self_mem_ordConnectedComponent.mpr ht⟩
      (bddAbove_ordConnectedComponent hU hper hne t) (2 * Real.pi), compB]

theorem csInf_notMem (hU : IsOpen U) (t : ℝ) (hb : BddBelow (ordConnectedComponent U t)) :
    compA U t ∉ ordConnectedComponent U t := by
  intro hmem
  obtain ⟨ε, hε, hsub⟩ := (Metric.isOpen_iff.mp (isOpen_ordConnectedComponent hU t)) _ hmem
  have hball : compA U t - ε / 2 ∈ Metric.ball (compA U t) ε := by
    rw [Metric.mem_ball, dist_eq_norm,
      show compA U t - ε / 2 - compA U t = -(ε / 2) by ring, norm_neg,
      Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ ε / 2)]
    linarith
  have h1 : compA U t ≤ compA U t - ε / 2 := csInf_le hb (hsub hball)
  linarith

theorem csSup_notMem (hU : IsOpen U) (t : ℝ) (ha : BddAbove (ordConnectedComponent U t)) :
    compB U t ∉ ordConnectedComponent U t := by
  intro hmem
  obtain ⟨ε, hε, hsub⟩ := (Metric.isOpen_iff.mp (isOpen_ordConnectedComponent hU t)) _ hmem
  have hball : compB U t + ε / 2 ∈ Metric.ball (compB U t) ε := by
    rw [Metric.mem_ball, dist_eq_norm,
      show compB U t + ε / 2 - compB U t = ε / 2 by ring,
      Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ ε / 2)]
    linarith
  have h1 : compB U t + ε / 2 ≤ compB U t := le_csSup ha (hsub hball)
  linarith

theorem ordConnectedComponent_eq_Ioo (hU : IsOpen U) {t : ℝ} (ht : t ∈ U)
    (hb : BddBelow (ordConnectedComponent U t)) (ha : BddAbove (ordConnectedComponent U t)) :
    ordConnectedComponent U t = Ioo (compA U t) (compB U t) := by
  have hne : (ordConnectedComponent U t).Nonempty := ⟨t, self_mem_ordConnectedComponent.mpr ht⟩
  have hA : compA U t ∉ ordConnectedComponent U t := csInf_notMem hU t hb
  have hB : compB U t ∉ ordConnectedComponent U t := csSup_notMem hU t ha
  ext y; constructor
  · intro hy
    have h1 : compA U t ≤ y := csInf_le hb hy
    have h2 : y ≤ compB U t := le_csSup ha hy
    exact ⟨lt_of_le_of_ne h1 (fun heq => hA (heq ▸ hy)),
      lt_of_le_of_ne h2 (fun heq => hB (heq ▸ hy))⟩
  · rintro ⟨hy1, hy2⟩
    obtain ⟨c1, hc1, hc1y⟩ :=
      exists_lt_of_csInf_lt hne (show sInf (ordConnectedComponent U t) < y from hy1)
    obtain ⟨c2, hc2, hc2y⟩ :=
      exists_lt_of_lt_csSup hne (show y < sSup (ordConnectedComponent U t) from hy2)
    exact ((inferInstance : (ordConnectedComponent U t).OrdConnected).uIcc_subset hc1 hc2)
      (mem_uIcc.mpr (Or.inl ⟨le_of_lt hc1y, le_of_lt hc2y⟩))

/-- A component of a periodic open proper subset of `ℝ` is an open interval `(a,b)` with
`a,b ∉ U`, its endpoints move by `2π` under translation, and its points share it. -/
theorem comp_description (hU : IsOpen U)
    (hper : ∀ t : ℝ, t + 2 * Real.pi ∈ U ↔ t ∈ U) (hne : ∃ x, x ∉ U) {t : ℝ} (ht : t ∈ U) :
    compA U t < t ∧ t < compB U t ∧ compA U t ∉ U ∧ compB U t ∉ U ∧
      Ioo (compA U t) (compB U t) ⊆ U ∧
      ordConnectedComponent U t = Ioo (compA U t) (compB U t) ∧
      (∀ t' ∈ Ioo (compA U t) (compB U t),
        compA U t' = compA U t ∧ compB U t' = compB U t) ∧
      compA U (t + 2 * Real.pi) = compA U t + 2 * Real.pi ∧
      compB U (t + 2 * Real.pi) = compB U t + 2 * Real.pi := by
  have hb := bddBelow_ordConnectedComponent hU hper hne t
  have ha := bddAbove_ordConnectedComponent hU hper hne t
  have hIoo := ordConnectedComponent_eq_Ioo hU ht hb ha
  have hIooU : Ioo (compA U t) (compB U t) ⊆ U := hIoo ▸ ordConnectedComponent_subset
  have htC : t ∈ ordConnectedComponent U t := self_mem_ordConnectedComponent.mpr ht
  have hlt : compA U t < t ∧ t < compB U t := by
    rw [hIoo] at htC; exact htC
  have hAcar : compA U t ∉ U := by
    intro hmem
    apply csInf_notMem hU t hb
    rw [mem_ordConnectedComponent, uIcc_comm, uIcc_of_le hlt.1.le]
    intro z hz
    rcases mem_Icc.mp hz with ⟨hz1, hz2⟩
    rcases eq_or_lt_of_le hz1 with h | h
    · rw [← h]; exact hmem
    · exact hIooU (mem_Ioo.mpr ⟨h, lt_of_le_of_lt hz2 hlt.2⟩)
  have hBcar : compB U t ∉ U := by
    intro hmem
    apply csSup_notMem hU t ha
    rw [mem_ordConnectedComponent, uIcc_of_le hlt.2.le]
    intro z hz
    rcases mem_Icc.mp hz with ⟨hz1, hz2⟩
    rcases eq_or_lt_of_le hz2 with h | h
    · rw [h]; exact hmem
    · exact hIooU (mem_Ioo.mpr ⟨lt_of_lt_of_le hlt.1 hz1, h⟩)
  refine ⟨hlt.1, hlt.2, hAcar, hBcar, hIooU, hIoo, ?_, compA_add_pi hU hper hne ht,
    compB_add_pi hU hper hne ht⟩
  · intro t' ht'
    have : t' ∈ ordConnectedComponent U t := by rw [hIoo]; exact ht'
    exact ⟨compA_eq_of_mem (U := U) this, compB_eq_of_mem (U := U) this⟩

end Components



theorem circlePoint_periodic (θ : ℝ) : circlePoint (θ + 2 * Real.pi) = circlePoint θ := by
  apply Subtype.ext
  simp only [circlePoint, Subtype.coe_mk]
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨1, ?_⟩
  push_cast
  ring

theorem norm_circlePoint (θ : ℝ) : ‖(circlePoint θ : ℂ)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

theorem circlePoint_add_int_mul (θ : ℝ) (n : ℤ) :
    circlePoint (θ + (n : ℝ) * (2 * Real.pi)) = circlePoint θ := by
  apply Subtype.ext
  simp only [circlePoint, Subtype.coe_mk]
  rw [Complex.exp_eq_exp_iff_exists_int]
  exact ⟨n, by push_cast; ring⟩

theorem circlePoint_arg (z : Metric.closedBall (0 : ℂ) 1) (hz : ‖(z : ℂ)‖ = 1) :
    circlePoint (Complex.arg (z : ℂ)) = z := by
  apply Subtype.ext
  simp only [circlePoint, Subtype.coe_mk]
  have h := Complex.norm_mul_exp_arg_mul_I (z : ℂ)
  rw [hz] at h
  simpa using h

/-- The signed angular difference of two angles, normalised to `[-π, π]`. -/
def arcDelta (θa θb : ℝ) : ℝ :=
  if Real.pi < θb - θa then θb - θa - 2 * Real.pi
  else if θb - θa < -Real.pi then θb - θa + 2 * Real.pi
  else θb - θa

theorem arcDelta_mem_Icc (θa θb : ℝ) (ha : θa ∈ Set.Ioc (-Real.pi) Real.pi)
    (hb : θb ∈ Set.Ioc (-Real.pi) Real.pi) : arcDelta θa θb ∈ Set.Icc (-Real.pi) Real.pi := by
  have h1 := ha.1; have h2 := ha.2; have h3 := hb.1; have h4 := hb.2
  unfold arcDelta
  split_ifs with h5 h6
  · refine ⟨?_, le_of_lt (by linarith)⟩; linarith
  · refine ⟨le_of_lt (by linarith), ?_⟩; linarith
  · push_neg at h5 h6; exact ⟨h6, h5⟩

theorem circlePoint_arcDelta (θa θb : ℝ) :
    circlePoint (θa + arcDelta θa θb) = circlePoint θb := by
  unfold arcDelta
  split_ifs with h1 h2
  · rw [show θa + (θb - θa - 2 * Real.pi) = θb + ((-1 : ℤ) : ℝ) * (2 * Real.pi) from by
      push_cast; ring]
    exact circlePoint_add_int_mul θb (-1)
  · rw [show θa + (θb - θa + 2 * Real.pi) = θb + ((1 : ℤ) : ℝ) * (2 * Real.pi) from by
      push_cast; ring]
    exact circlePoint_add_int_mul θb 1
  · rw [show θa + (θb - θa) = θb from by ring]

/-- The parametric preimage of the interior of the disc. -/
def preimageSet (D : DiscRegion (P)) (γ : Work.CoreTopology.ClosedCurve (P)) :
    Set ℝ := {t | γ t ∈ D.interior}

theorem preimageSet_open (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) : IsOpen (preimageSet D γ) := by
  have hcont : Continuous (fun t : ℝ => (⟨γ t, γ.mem t⟩ : (P).carrier)) :=
    Continuous.subtype_mk γ.cont _
  have h := D.open_interior.preimage hcont
  show IsOpen (preimageSet D γ)
  exact h

theorem preimageSet_periodic (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) :
    ∀ t : ℝ, t + 2 * Real.pi ∈ preimageSet D γ ↔ t ∈ preimageSet D γ := by
  intro t
  simp only [preimageSet, mem_setOf_eq, γ.periodic t]

/-- The parameter of a point of the surface in the disc, with a junk value outside the disc. -/
def zoom (D : DiscRegion (P)) (γ : Work.CoreTopology.ClosedCurve (P))
    (t : ℝ) : Metric.closedBall (0 : ℂ) 1 :=
  if h : γ t ∈ D.carrier then discPre D (γ t) h else 0

theorem zoom_eq (D : DiscRegion (P)) (γ : Work.CoreTopology.ClosedCurve (P))
    {t : ℝ} (h : γ t ∈ D.carrier) : zoom D γ t = discPre D (γ t) h := dif_pos h

theorem D_e_zoom (D : DiscRegion (P)) (γ : Work.CoreTopology.ClosedCurve (P))
    {t : ℝ} (h : γ t ∈ D.carrier) : D.e (zoom D γ t) = γ t := by
  rw [zoom_eq D γ h, discPre_spec]

/-- The angle of a point of the boundary circle of the disc. -/
def angle (D : DiscRegion (P)) (γ : Work.CoreTopology.ClosedCurve (P))
    (t : ℝ) : ℝ := Complex.arg ((zoom D γ t : Metric.closedBall (0 : ℂ) 1) : ℂ)

theorem angle_mem_Ioc (D : DiscRegion (P)) (γ : Work.CoreTopology.ClosedCurve (P))
    (t : ℝ) : angle D γ t ∈ Set.Ioc (-Real.pi) Real.pi := Complex.arg_mem_Ioc _

theorem circlePoint_angle (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) {t : ℝ} (h : γ t ∈ D.boundary) :
    circlePoint (angle D γ t) = zoom D γ t := by
  have hc := D.boundary_subset_carrier h
  rw [angle, zoom_eq D γ hc]
  exact circlePoint_arg _ ((mem_boundary_iff D (γ t) hc).mp h)

/-- The fraction of the way from the left to the right end of the component of `t`. -/
noncomputable def compU (U : Set ℝ) (t : ℝ) : ℝ :=
  (t - compA U t) / (compB U t - compA U t)

/-- **The reroute point**: the point of the boundary circle at which the loop is placed at time
`t` in the push-off. -/
noncomputable def reroutePt (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) (t : ℝ) : Metric.closedBall (0 : ℂ) 1 :=
  circlePoint (angle D γ (compA (preimageSet D γ) t)
    + compU (preimageSet D γ) t
      * arcDelta (angle D γ (compA (preimageSet D γ) t))
          (angle D γ (compB (preimageSet D γ) t)))

/-! ## 4. The endpoints of a component are boundary points of the disc -/

theorem gamma_compA_mem_carrier (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) (hne : ∃ x, x ∉ preimageSet D γ)
    {t : ℝ} (ht : t ∈ preimageSet D γ) :
    γ (compA (preimageSet D γ) t) ∈ D.carrier := by
  haveI : (nhdsWithin (compA (preimageSet D γ) t) (Set.Ioi (compA (preimageSet D γ) t))).NeBot :=
    nhdsGT_neBot _
  obtain ⟨hlt1, hlt2, -, -, hIooU, -, -, -, -⟩ :=
    comp_description (preimageSet_open D γ) (preimageSet_periodic D γ) hne ht
  have htend : Tendsto γ
      (nhdsWithin (compA (preimageSet D γ) t) (Set.Ioi (compA (preimageSet D γ) t)))
      (nhds (γ (compA (preimageSet D γ) t))) :=
    (γ.cont.continuousAt (x := compA (preimageSet D γ) t)).mono_left inf_le_left
  refine (isClosed_carrier D).mem_of_tendsto htend ?_
  refine mem_of_superset (Ioo_mem_nhdsGT (lt_min hlt1 (lt_trans hlt1 hlt2))) ?_
  intro s hs
  exact D.interior_subset_carrier
    (hIooU (mem_Ioo.mpr ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩))

theorem gamma_compB_mem_carrier (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) (hne : ∃ x, x ∉ preimageSet D γ)
    {t : ℝ} (ht : t ∈ preimageSet D γ) :
    γ (compB (preimageSet D γ) t) ∈ D.carrier := by
  haveI : (nhdsWithin (compB (preimageSet D γ) t) (Set.Iio (compB (preimageSet D γ) t))).NeBot :=
    nhdsLT_neBot _
  obtain ⟨hlt1, hlt2, -, -, hIooU, -, -, -, -⟩ :=
    comp_description (preimageSet_open D γ) (preimageSet_periodic D γ) hne ht
  have htend : Tendsto γ
      (nhdsWithin (compB (preimageSet D γ) t) (Set.Iio (compB (preimageSet D γ) t)))
      (nhds (γ (compB (preimageSet D γ) t))) :=
    (γ.cont.continuousAt (x := compB (preimageSet D γ) t)).mono_left inf_le_left
  refine (isClosed_carrier D).mem_of_tendsto htend ?_
  refine mem_of_superset (Ioo_mem_nhdsLT (max_lt hlt2 (lt_trans hlt1 hlt2))) ?_
  intro s hs
  exact D.interior_subset_carrier
    (hIooU (mem_Ioo.mpr ⟨lt_of_le_of_lt (le_max_right _ _) hs.1, hs.2⟩))

theorem gamma_compA_mem_boundary (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) (hne : ∃ x, x ∉ preimageSet D γ)
    {t : ℝ} (ht : t ∈ preimageSet D γ) :
    γ (compA (preimageSet D γ) t) ∈ D.boundary := by
  have hc := gamma_compA_mem_carrier D γ hne ht
  have hnot : γ (compA (preimageSet D γ) t) ∉ D.interior :=
    (comp_description (preimageSet_open D γ) (preimageSet_periodic D γ) hne ht).2.2.1
  rw [carrier_eq_union] at hc
  rcases hc with h | h
  · exact absurd h hnot
  · exact h

theorem gamma_compB_mem_boundary (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) (hne : ∃ x, x ∉ preimageSet D γ)
    {t : ℝ} (ht : t ∈ preimageSet D γ) :
    γ (compB (preimageSet D γ) t) ∈ D.boundary := by
  have hc := gamma_compB_mem_carrier D γ hne ht
  have hnot : γ (compB (preimageSet D γ) t) ∉ D.interior :=
    (comp_description (preimageSet_open D γ) (preimageSet_periodic D γ) hne ht).2.2.2.1
  rw [carrier_eq_union] at hc
  rcases hc with h | h
  · exact absurd h hnot
  · exact h

theorem D_e_circlePoint_mem_boundary (D : DiscRegion (P)) (θ : ℝ) :
    D.e (circlePoint θ) ∈ D.boundary := by
  have hc : D.e (circlePoint θ) ∈ D.carrier := ⟨circlePoint θ, rfl⟩
  refine (mem_boundary_iff D _ hc).mpr ?_
  have hpre : discPre D (D.e (circlePoint θ)) hc = circlePoint θ := by
    show (discHomeo D).symm ⟨D.e (circlePoint θ), hc⟩ = circlePoint θ
    exact Homeomorph.symm_apply_apply (discHomeo D) (circlePoint θ)
  rw [hpre]; exact norm_circlePoint θ

/-! ## 5. Distance estimates on the boundary circle -/

theorem norm_sq_exp_mul_I_sub_one (y : ℝ) :
    ‖Complex.exp (y * Complex.I) - 1‖^2 = 2 - 2 * Real.cos y := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  nlinarith [Real.sin_sq_add_cos_sq y]

theorem norm_exp_mul_I_sub_one_le_of_abs_le {x y : ℝ} (hx : |x| ≤ |y|) (hy : |y| ≤ Real.pi) :
    ‖Complex.exp ((x : ℝ) * Complex.I) - 1‖ ≤ ‖Complex.exp ((y : ℝ) * Complex.I) - 1‖ := by
  have hsq : ‖Complex.exp ((x : ℝ) * Complex.I) - 1‖^2
      ≤ ‖Complex.exp ((y : ℝ) * Complex.I) - 1‖^2 := by
    rw [show ‖Complex.exp ((x : ℝ) * Complex.I) - 1‖^2 = 2 - 2 * Real.cos x from
        norm_sq_exp_mul_I_sub_one x,
      show ‖Complex.exp ((y : ℝ) * Complex.I) - 1‖^2 = 2 - 2 * Real.cos y from
        norm_sq_exp_mul_I_sub_one y]
    have h1 : Real.cos y = Real.cos |y| := (Real.cos_abs y).symm
    have h2 : Real.cos x = Real.cos |x| := (Real.cos_abs x).symm
    rw [h1, h2]
    have := Real.cos_le_cos_of_nonneg_of_le_pi (x := |x|) (y := |y|)
      (abs_nonneg x) (by linarith [abs_nonneg y]) hx
    linarith
  calc ‖Complex.exp ((x : ℝ) * Complex.I) - 1‖
      = Real.sqrt (‖Complex.exp ((x : ℝ) * Complex.I) - 1‖^2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖Complex.exp ((y : ℝ) * Complex.I) - 1‖^2) := Real.sqrt_le_sqrt hsq
    _ = ‖Complex.exp ((y : ℝ) * Complex.I) - 1‖ := Real.sqrt_sq (norm_nonneg _)

theorem norm_exp_mul_I_sub_one_le (x : ℝ) :
    ‖Complex.exp ((x : ℝ) * Complex.I) - 1‖ ≤ 2 * |x| := by
  rcases le_or_gt |x| 1 with h | h
  · have hnorm : ‖(((x : ℝ)) : ℂ) * Complex.I‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_I, mul_one]; simpa using h
    have := Complex.norm_exp_sub_one_le hnorm
    rw [norm_mul, Complex.norm_I, mul_one] at this
    simpa using this
  · have h2 : ‖Complex.exp ((x : ℝ) * Complex.I) - 1‖ ≤ 2 := by
      calc ‖Complex.exp ((x : ℝ) * Complex.I) - 1‖
          ≤ ‖Complex.exp ((x : ℝ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 1 + 1 := by rw [Complex.norm_exp_ofReal_mul_I]; norm_num
        _ = 2 := by norm_num
    linarith [abs_nonneg x]

theorem norm_circlePoint_sub_eq (θ φ : ℝ) :
    ‖(circlePoint θ : ℂ) - (circlePoint φ : ℂ)‖
      = ‖Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I) - 1‖ := by
  have hdecomp : (circlePoint θ : ℂ) - (circlePoint φ : ℂ)
      = Complex.exp (φ * Complex.I) * (Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I) - 1) := by
    show Complex.exp (θ * Complex.I) - Complex.exp (φ * Complex.I) = _
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hdecomp, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem norm_circlePoint_sub_le (θ φ : ℝ) :
    ‖(circlePoint θ : ℂ) - (circlePoint φ : ℂ)‖ ≤ 2 * |θ - φ| := by
  rw [norm_circlePoint_sub_eq]
  exact norm_exp_mul_I_sub_one_le (θ - φ)

theorem norm_circlePoint_sub_le_chord (θ d u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hd : |d| ≤ Real.pi) :
    ‖(circlePoint (θ + u * d) : ℂ) - (circlePoint θ : ℂ)‖
      ≤ ‖(circlePoint (θ + d) : ℂ) - (circlePoint θ : ℂ)‖ := by
  rw [norm_circlePoint_sub_eq, norm_circlePoint_sub_eq]
  have h1 : ((θ + u * d - θ : ℝ) : ℂ) = ((u * d : ℝ) : ℂ) := by push_cast; ring
  have h2 : ((θ + d - θ : ℝ) : ℂ) = ((d : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2]
  refine norm_exp_mul_I_sub_one_le_of_abs_le ?_ hd
  rw [abs_mul, abs_of_nonneg hu.1]
  nlinarith [abs_nonneg d, hu.2]

/-- The interpolation estimate at the right end of a chord. -/
theorem norm_circlePoint_interp_right_le (θ d u : ℝ) :
    ‖(circlePoint (θ + u * d) : ℂ) - (circlePoint (θ + d) : ℂ)‖ ≤ 2 * |(u - 1) * d| := by
  rw [norm_circlePoint_sub_eq]
  have h1 : ((θ + u * d - (θ + d) : ℝ) : ℂ) = (((u - 1) * d : ℝ) : ℂ) := by push_cast; ring
  rw [h1]
  exact norm_exp_mul_I_sub_one_le ((u - 1) * d)

/-! ## 6. Convergence of the disc parameters -/

/-- **The disc parameters converge when the surface points converge.** -/
theorem tendsto_zoom (D : DiscRegion (P)) (γ : Work.CoreTopology.ClosedCurve (P))
    {t₀ : ℝ} (hmem : γ t₀ ∈ D.carrier) :
    ∀ ε > 0, ∃ δ > 0, ∀ s : ℝ, γ s ∈ D.carrier → dist s t₀ < δ →
      dist (zoom D γ s) (zoom D γ t₀) < ε := by
  intro ε hε
  obtain ⟨δ', hδ'pos, hδ'⟩ := Metric.continuousAt_iff.mp
    (((discHomeo D).symm.continuous).continuousAt (x := (⟨γ t₀, hmem⟩ : D.carrier))) ε hε
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp (γ.cont.continuousAt (x := t₀)) δ' hδ'pos
  refine ⟨δ, hδpos, fun s hs hs' => ?_⟩
  have h1 : zoom D γ s = (discHomeo D).symm ⟨γ s, hs⟩ := by rw [zoom_eq D γ hs]; rfl
  have h2 : zoom D γ t₀ = (discHomeo D).symm ⟨γ t₀, hmem⟩ := by rw [zoom_eq D γ hmem]; rfl
  rw [h1, h2]
  refine hδ' (x := (⟨γ s, hs⟩ : D.carrier)) ?_
  rw [Subtype.dist_eq]
  exact hδ hs'

/-- `compU` lies in `(0,1)` on a component. -/
theorem compU_mem (D : DiscRegion (P)) (γ : Work.CoreTopology.ClosedCurve (P))
    (hne : ∃ x, x ∉ preimageSet D γ) {t : ℝ} (ht : t ∈ preimageSet D γ) :
    compU (preimageSet D γ) t ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨hlt1, hlt2, -, -, -, -, -, -, -⟩ :=
    comp_description (preimageSet_open D γ) (preimageSet_periodic D γ) hne ht
  rw [compU]
  have hpos : (0 : ℝ) < compB (preimageSet D γ) t - compA (preimageSet D γ) t := by linarith
  exact ⟨div_pos (by linarith) hpos, (div_lt_one hpos).mpr (by linarith)⟩

theorem angle_delta_abs_le (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) {t : ℝ}
    (ht : t ∈ preimageSet D γ) :
    |arcDelta (angle D γ (compA (preimageSet D γ) t)) (angle D γ (compB (preimageSet D γ) t))|
      ≤ Real.pi := by
  have := arcDelta_mem_Icc (angle D γ (compA (preimageSet D γ) t))
    (angle D γ (compB (preimageSet D γ) t)) (angle_mem_Ioc D γ _) (angle_mem_Ioc D γ _)
  rw [abs_le]; exact ⟨this.1, this.2⟩

theorem reroutePt_eq (D : DiscRegion (P)) (γ : Work.CoreTopology.ClosedCurve (P))
    (t : ℝ) : (reroutePt D γ t : ℂ) = (circlePoint (angle D γ (compA (preimageSet D γ) t)
      + compU (preimageSet D γ) t
        * arcDelta (angle D γ (compA (preimageSet D γ) t))
            (angle D γ (compB (preimageSet D γ) t))) : ℂ) := rfl

theorem zoom_compA_eq (D : DiscRegion (P)) (γ : Work.CoreTopology.ClosedCurve (P))
    (hne : ∃ x, x ∉ preimageSet D γ) {t : ℝ} (ht : t ∈ preimageSet D γ) :
    (zoom D γ (compA (preimageSet D γ) t) : ℂ)
      = (circlePoint (angle D γ (compA (preimageSet D γ) t)) : ℂ) := by
  rw [circlePoint_angle D γ (gamma_compA_mem_boundary D γ hne ht)]

theorem zoom_compB_eq (D : DiscRegion (P)) (γ : Work.CoreTopology.ClosedCurve (P))
    (hne : ∃ x, x ∉ preimageSet D γ) {t : ℝ} (ht : t ∈ preimageSet D γ) :
    (zoom D γ (compB (preimageSet D γ) t) : ℂ)
      = (circlePoint (angle D γ (compA (preimageSet D γ) t)
          + arcDelta (angle D γ (compA (preimageSet D γ) t))
              (angle D γ (compB (preimageSet D γ) t))) : ℂ) := by
  rw [congrArg Subtype.val (circlePoint_arcDelta (angle D γ (compA (preimageSet D γ) t))
    (angle D γ (compB (preimageSet D γ) t)))]
  rw [circlePoint_angle D γ (gamma_compB_mem_boundary D γ hne ht)]

/-- **The estimate at the left end of a component.** -/
theorem reroutePt_dist_left (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) (hne : ∃ x, x ∉ preimageSet D γ)
    {t : ℝ} (ht : t ∈ preimageSet D γ) :
    dist (reroutePt D γ t) (zoom D γ (compA (preimageSet D γ) t))
      ≤ 2 * Real.pi * compU (preimageSet D γ) t := by
  have hu := compU_mem D γ hne ht
  have hd := angle_delta_abs_le D γ ht
  have hdist : dist (reroutePt D γ t) (zoom D γ (compA (preimageSet D γ) t))
      = ‖(reroutePt D γ t : ℂ) - (zoom D γ (compA (preimageSet D γ) t) : ℂ)‖ := by
    rw [show dist (reroutePt D γ t) (zoom D γ (compA (preimageSet D γ) t))
      = dist ((reroutePt D γ t : ℂ)) ((zoom D γ (compA (preimageSet D γ) t) : ℂ)) from rfl,
      dist_eq_norm]
  rw [hdist, reroutePt_eq, zoom_compA_eq D γ hne ht]
  calc ‖(circlePoint (angle D γ (compA (preimageSet D γ) t)
        + compU (preimageSet D γ) t
          * arcDelta (angle D γ (compA (preimageSet D γ) t))
              (angle D γ (compB (preimageSet D γ) t))) : ℂ)
      - (circlePoint (angle D γ (compA (preimageSet D γ) t)) : ℂ)‖
      ≤ 2 * |(angle D γ (compA (preimageSet D γ) t)
              + compU (preimageSet D γ) t
                * arcDelta (angle D γ (compA (preimageSet D γ) t))
                    (angle D γ (compB (preimageSet D γ) t)))
            - angle D γ (compA (preimageSet D γ) t)| := norm_circlePoint_sub_le _ _
    _ = 2 * |compU (preimageSet D γ) t|
          * |arcDelta (angle D γ (compA (preimageSet D γ) t))
              (angle D γ (compB (preimageSet D γ) t))| := by
      rw [add_sub_cancel_left, abs_mul]; ring
    _ ≤ 2 * Real.pi * compU (preimageSet D γ) t := by
      rw [abs_of_nonneg (by linarith [hu.1])]
      nlinarith [abs_nonneg (arcDelta (angle D γ (compA (preimageSet D γ) t))
        (angle D γ (compB (preimageSet D γ) t))), hu.1, Real.pi_pos]

/-- **The estimate at the right end of a component.** -/
theorem reroutePt_dist_right (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) (hne : ∃ x, x ∉ preimageSet D γ)
    {t : ℝ} (ht : t ∈ preimageSet D γ) :
    dist (reroutePt D γ t) (zoom D γ (compB (preimageSet D γ) t))
      ≤ 2 * Real.pi * (1 - compU (preimageSet D γ) t) := by
  have hu := compU_mem D γ hne ht
  have hd := angle_delta_abs_le D γ ht
  have hdist : dist (reroutePt D γ t) (zoom D γ (compB (preimageSet D γ) t))
      = ‖(reroutePt D γ t : ℂ) - (zoom D γ (compB (preimageSet D γ) t) : ℂ)‖ := by
    rw [show dist (reroutePt D γ t) (zoom D γ (compB (preimageSet D γ) t))
      = dist ((reroutePt D γ t : ℂ)) ((zoom D γ (compB (preimageSet D γ) t) : ℂ)) from rfl,
      dist_eq_norm]
  rw [hdist, reroutePt_eq, zoom_compB_eq D γ hne ht]
  have hkey := norm_circlePoint_interp_right_le (angle D γ (compA (preimageSet D γ) t))
    (arcDelta (angle D γ (compA (preimageSet D γ) t)) (angle D γ (compB (preimageSet D γ) t)))
    (compU (preimageSet D γ) t)
  calc ‖(circlePoint (angle D γ (compA (preimageSet D γ) t)
        + compU (preimageSet D γ) t
          * arcDelta (angle D γ (compA (preimageSet D γ) t))
              (angle D γ (compB (preimageSet D γ) t))) : ℂ)
      - (circlePoint (angle D γ (compA (preimageSet D γ) t)
        + arcDelta (angle D γ (compA (preimageSet D γ) t))
            (angle D γ (compB (preimageSet D γ) t))) : ℂ)‖
      ≤ 2 * |(compU (preimageSet D γ) t - 1)
          * arcDelta (angle D γ (compA (preimageSet D γ) t))
              (angle D γ (compB (preimageSet D γ) t))| := hkey
    _ = 2 * |compU (preimageSet D γ) t - 1|
          * |arcDelta (angle D γ (compA (preimageSet D γ) t))
              (angle D γ (compB (preimageSet D γ) t))| := by rw [abs_mul]; ring
    _ ≤ 2 * Real.pi * (1 - compU (preimageSet D γ) t) := by
      rw [show compU (preimageSet D γ) t - 1 = -(1 - compU (preimageSet D γ) t) by ring,
        abs_neg, abs_of_nonneg (by linarith [hu.2])]
      nlinarith [abs_nonneg (arcDelta (angle D γ (compA (preimageSet D γ) t))
        (angle D γ (compB (preimageSet D γ) t))), hu.2]

/-- **The estimate through the chord.** -/
theorem reroutePt_dist_chord (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) (hne : ∃ x, x ∉ preimageSet D γ)
    {t : ℝ} (ht : t ∈ preimageSet D γ) (w : Metric.closedBall (0 : ℂ) 1) :
    dist (reroutePt D γ t) w
      ≤ 2 * dist (zoom D γ (compA (preimageSet D γ) t)) w
        + dist (zoom D γ (compB (preimageSet D γ) t)) w := by
  have hu := compU_mem D γ hne ht
  have hd := angle_delta_abs_le D γ ht
  have h1 : dist (reroutePt D γ t) w
      = ‖(reroutePt D γ t : ℂ) - (w : ℂ)‖ := by
    rw [show dist (reroutePt D γ t) w = dist ((reroutePt D γ t : ℂ)) (w : ℂ) from rfl,
      dist_eq_norm]
  have h2 : 2 * dist (zoom D γ (compA (preimageSet D γ) t)) w
      + dist (zoom D γ (compB (preimageSet D γ) t)) w
      = 2 * ‖(zoom D γ (compA (preimageSet D γ) t) : ℂ) - (w : ℂ)‖
        + ‖(zoom D γ (compB (preimageSet D γ) t) : ℂ) - (w : ℂ)‖ := by
    rw [show dist (zoom D γ (compA (preimageSet D γ) t)) w
        = dist ((zoom D γ (compA (preimageSet D γ) t) : ℂ)) (w : ℂ) from rfl, dist_eq_norm,
      show dist (zoom D γ (compB (preimageSet D γ) t)) w
        = dist ((zoom D γ (compB (preimageSet D γ) t) : ℂ)) (w : ℂ) from rfl, dist_eq_norm]
  rw [h1, h2]
  have hza := zoom_compA_eq D γ hne ht
  have hzb := zoom_compB_eq D γ hne ht
  have hchord : ‖(reroutePt D γ t : ℂ) - (zoom D γ (compA (preimageSet D γ) t) : ℂ)‖
      ≤ ‖(zoom D γ (compB (preimageSet D γ) t) : ℂ)
          - (zoom D γ (compA (preimageSet D γ) t) : ℂ)‖ := by
    rw [reroutePt_eq, hza, hzb]
    exact norm_circlePoint_sub_le_chord _ _ _ ⟨hu.1.le, hu.2.le⟩ hd
  have htri1 : ‖(zoom D γ (compB (preimageSet D γ) t) : ℂ)
      - (zoom D γ (compA (preimageSet D γ) t) : ℂ)‖
      ≤ ‖(zoom D γ (compB (preimageSet D γ) t) : ℂ) - (w : ℂ)‖
        + ‖(w : ℂ) - (zoom D γ (compA (preimageSet D γ) t) : ℂ)‖ := by
    rw [show (zoom D γ (compB (preimageSet D γ) t) : ℂ)
        - (zoom D γ (compA (preimageSet D γ) t) : ℂ)
        = ((zoom D γ (compB (preimageSet D γ) t) : ℂ) - (w : ℂ))
          + ((w : ℂ) - (zoom D γ (compA (preimageSet D γ) t) : ℂ)) by ring]
    exact norm_add_le _ _
  have htri2 : ‖(reroutePt D γ t : ℂ) - (w : ℂ)‖
      ≤ ‖(reroutePt D γ t : ℂ) - (zoom D γ (compA (preimageSet D γ) t) : ℂ)‖
        + ‖(zoom D γ (compA (preimageSet D γ) t) : ℂ) - (w : ℂ)‖ := by
    rw [show (reroutePt D γ t : ℂ) - (w : ℂ)
        = ((reroutePt D γ t : ℂ) - (zoom D γ (compA (preimageSet D γ) t) : ℂ))
          + ((zoom D γ (compA (preimageSet D γ) t) : ℂ) - (w : ℂ)) by ring]
    exact norm_add_le _ _
  rw [norm_sub_rev (w : ℂ) (zoom D γ (compA (preimageSet D γ) t) : ℂ)] at htri1
  linarith

/-! ## 7. Convergence of the reroute -/

theorem compA_le_self (D : DiscRegion (P)) (γ : Work.CoreTopology.ClosedCurve (P))
    (hne : ∃ x, x ∉ preimageSet D γ) {t t₀ : ℝ} (ht : t ∈ preimageSet D γ)
    (ht₀ : t₀ ∉ preimageSet D γ) (h : t₀ ≤ t) :
    t₀ ≤ compA (preimageSet D γ) t := by
  rcases lt_or_eq_of_le h with h | h
  · by_contra hc
    rw [not_le] at hc
    obtain ⟨hlt1, hlt2, -, -, hIooU, -, -, -, -⟩ :=
      comp_description (preimageSet_open D γ) (preimageSet_periodic D γ) hne ht
    exact ht₀ (hIooU (mem_Ioo.mpr ⟨hc, lt_trans h hlt2⟩))
  · exact absurd (h ▸ ht : t₀ ∈ preimageSet D γ) ht₀

theorem compB_le_self (D : DiscRegion (P)) (γ : Work.CoreTopology.ClosedCurve (P))
    (hne : ∃ x, x ∉ preimageSet D γ) {t t₀ : ℝ} (ht : t ∈ preimageSet D γ)
    (ht₀ : t₀ ∉ preimageSet D γ) (h : t ≤ t₀) :
    compB (preimageSet D γ) t ≤ t₀ := by
  rcases lt_or_eq_of_le h with h | h
  · by_contra hc
    rw [not_le] at hc
    obtain ⟨hlt1, hlt2, -, -, hIooU, -, -, -, -⟩ :=
      comp_description (preimageSet_open D γ) (preimageSet_periodic D γ) hne ht
    exact ht₀ (hIooU (mem_Ioo.mpr ⟨lt_trans hlt1 h, hc⟩))
  · exact absurd (h ▸ ht : t₀ ∈ preimageSet D γ) ht₀

/-- **The reroute points converge to the boundary point.** -/
theorem tendsto_reroutePt (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) (hne : ∃ x, x ∉ preimageSet D γ)
    {t₀ : ℝ} (ht₀ : t₀ ∉ preimageSet D γ) (hmem : γ t₀ ∈ D.carrier) :
    Tendsto (reroutePt D γ) (nhdsWithin t₀ (preimageSet D γ)) (nhds (zoom D γ t₀)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ε₁ : ℝ := ε / 8 with hε₁
  set ε₂ : ℝ := ε / (8 * Real.pi) with hε₂
  have hε₁pos : 0 < ε₁ := by rw [hε₁]; positivity
  have hε₂pos : 0 < ε₂ := by rw [hε₂]; positivity
  have hε₁lt : 3 * ε₁ < ε := by rw [hε₁]; linarith
  have hε₂lt : 2 * Real.pi * ε₂ + ε₁ < ε := by
    rw [hε₁, hε₂]; field_simp; nlinarith [Real.pi_pos]
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := tendsto_zoom D γ hmem ε₁ hε₁pos
  have hδpos : 0 < min (δ₁ / 2) (δ₁ * ε₂ / 2) :=
    lt_min (by linarith) (by nlinarith [hδ₁pos, hε₂pos])
  have hmem_ball : Metric.ball t₀ (min (δ₁ / 2) (δ₁ * ε₂ / 2)) ∩ preimageSet D γ ∈
      nhdsWithin t₀ (preimageSet D γ) := by
    rw [nhdsWithin, mem_inf_iff]
    exact ⟨Metric.ball t₀ (min (δ₁ / 2) (δ₁ * ε₂ / 2)), Metric.ball_mem_nhds t₀ hδpos,
      preimageSet D γ, Filter.mem_principal.mpr (subset_refl _), rfl⟩
  refine Filter.mem_of_superset hmem_ball ?_
  rintro t ⟨htball, htU⟩
  have htd : |t - t₀| < min (δ₁ / 2) (δ₁ * ε₂ / 2) := by
    rw [Metric.mem_ball, Real.dist_eq] at htball; exact htball
  have hu := compU_mem D γ hne htU
  obtain ⟨hlt1, hlt2, -, -, hIooU, -, -, -, -⟩ :=
    comp_description (preimageSet_open D γ) (preimageSet_periodic D γ) hne htU
  have hdlt : |t - t₀| < δ₁ / 2 := lt_of_lt_of_le htd (min_le_left _ _)
  have hdlt2 : |t - t₀| < δ₁ * ε₂ / 2 := lt_of_lt_of_le htd (min_le_right _ _)
  have hA : t₀ ≤ compA (preimageSet D γ) t →
      dist (zoom D γ (compA (preimageSet D γ) t)) (zoom D γ t₀) < ε₁ := by
    intro hc
    refine hδ₁ _ (gamma_compA_mem_carrier D γ hne htU) ?_
    rw [Real.dist_eq]
    have h1 : |compA (preimageSet D γ) t - t₀| ≤ |t - t₀| := by
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
    linarith
  have hB : compB (preimageSet D γ) t ≤ t₀ →
      dist (zoom D γ (compB (preimageSet D γ) t)) (zoom D γ t₀) < ε₁ := by
    intro hc
    refine hδ₁ _ (gamma_compB_mem_carrier D γ hne htU) ?_
    rw [Real.dist_eq]
    have h1 : |compB (preimageSet D γ) t - t₀| ≤ |t - t₀| := by
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
    linarith
  have hcase : t₀ ≤ compA (preimageSet D γ) t ∨ compB (preimageSet D γ) t ≤ t₀ := by
    rcases le_or_gt t₀ (compA (preimageSet D γ) t) with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      by_contra hc
      rw [not_le] at hc
      exact ht₀ (hIooU (mem_Ioo.mpr ⟨h, hc⟩))
  have hbound : dist (reroutePt D γ t) (zoom D γ t₀)
      < max (2 * Real.pi * ε₂ + ε₁) (3 * ε₁) := by
    have hchord := reroutePt_dist_chord D γ hne htU (zoom D γ t₀)
    have hleft := reroutePt_dist_left D γ hne htU
    have hright := reroutePt_dist_right D γ hne htU
    rcases hcase with hc | hc
    · have hAε := hA hc
      have hba_pos : (0 : ℝ) < compB (preimageSet D γ) t - compA (preimageSet D γ) t := by
        linarith
      rcases le_or_gt (compU (preimageSet D γ) t) ε₂ with hu2 | hu2
      · have h2 : 2 * Real.pi * compU (preimageSet D γ) t ≤ 2 * Real.pi * ε₂ := by
          nlinarith [Real.pi_pos]
        have htri := dist_triangle (reroutePt D γ t) (zoom D γ (compA (preimageSet D γ) t))
          (zoom D γ t₀)
        linarith [hleft, htri, hAε, h2, le_max_left (2 * Real.pi * ε₂ + ε₁) (3 * ε₁)]
      · have hba : compB (preimageSet D γ) t - compA (preimageSet D γ) t < δ₁ / 2 := by
          have h3 : compB (preimageSet D γ) t - compA (preimageSet D γ) t
              < (t - compA (preimageSet D γ) t) / ε₂ := by
            rw [compU] at hu2
            rw [lt_div_iff₀ hε₂pos]
            have h4 := (lt_div_iff₀ hba_pos).mp hu2
            linarith
          have h4 : t - compA (preimageSet D γ) t ≤ |t - t₀| := by
            rw [abs_of_nonneg (by linarith)]; linarith
          calc compB (preimageSet D γ) t - compA (preimageSet D γ) t
              < (t - compA (preimageSet D γ) t) / ε₂ := h3
            _ ≤ |t - t₀| / ε₂ := by gcongr
            _ < δ₁ / 2 := by
                rw [div_lt_iff₀ hε₂pos]
                have : δ₁ / 2 * ε₂ = δ₁ * ε₂ / 2 := by ring
                linarith
        have hBε : dist (zoom D γ (compB (preimageSet D γ) t)) (zoom D γ t₀) < ε₁ := by
          refine hδ₁ _ (gamma_compB_mem_carrier D γ hne htU) ?_
          rw [Real.dist_eq]
          have h1 : compB (preimageSet D γ) t - t₀
              = (compB (preimageSet D γ) t - compA (preimageSet D γ) t)
                + (compA (preimageSet D γ) t - t₀) := by ring
          calc |compB (preimageSet D γ) t - t₀|
              = |(compB (preimageSet D γ) t - compA (preimageSet D γ) t)
                + (compA (preimageSet D γ) t - t₀)| := by rw [h1]
            _ ≤ |compB (preimageSet D γ) t - compA (preimageSet D γ) t|
                + |compA (preimageSet D γ) t - t₀| := abs_add_le _ _
            _ = (compB (preimageSet D γ) t - compA (preimageSet D γ) t)
                + |compA (preimageSet D γ) t - t₀| := by rw [abs_of_pos hba_pos]
            _ < δ₁ / 2 + δ₁ / 2 := by
                have : |compA (preimageSet D γ) t - t₀| ≤ |t - t₀| := by
                  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
                linarith
            _ = δ₁ := by ring
        linarith [hchord, hAε, hBε,
          le_max_right (2 * Real.pi * ε₂ + ε₁) (3 * ε₁)]
    · have hBε := hB hc
      have hba_pos : (0 : ℝ) < compB (preimageSet D γ) t - compA (preimageSet D γ) t := by
        linarith
      rcases le_or_gt (1 - compU (preimageSet D γ) t) ε₂ with hu2 | hu2
      · have h2 : 2 * Real.pi * (1 - compU (preimageSet D γ) t) ≤ 2 * Real.pi * ε₂ := by
          nlinarith [Real.pi_pos]
        have htri := dist_triangle (reroutePt D γ t) (zoom D γ (compB (preimageSet D γ) t))
          (zoom D γ t₀)
        linarith [hright, htri, hBε, h2, le_max_left (2 * Real.pi * ε₂ + ε₁) (3 * ε₁)]
      · have hid : 1 - (t - compA (preimageSet D γ) t)
              / (compB (preimageSet D γ) t - compA (preimageSet D γ) t)
            = (compB (preimageSet D γ) t - t)
              / (compB (preimageSet D γ) t - compA (preimageSet D γ) t) := by
          field_simp; ring
        have h3 : compB (preimageSet D γ) t - compA (preimageSet D γ) t
            < (compB (preimageSet D γ) t - t) / ε₂ := by
          rw [compU, hid] at hu2
          rw [lt_div_iff₀ hε₂pos]
          have h4 := (lt_div_iff₀ hba_pos).mp hu2
          linarith
        have h4 : compB (preimageSet D γ) t - t ≤ |t - t₀| := by
          rw [abs_of_nonpos (by linarith)]; linarith
        have hba : compB (preimageSet D γ) t - compA (preimageSet D γ) t < δ₁ / 2 := by
          calc compB (preimageSet D γ) t - compA (preimageSet D γ) t
              < (compB (preimageSet D γ) t - t) / ε₂ := h3
            _ ≤ |t - t₀| / ε₂ := by gcongr
            _ < δ₁ / 2 := by
                rw [div_lt_iff₀ hε₂pos]
                have : δ₁ / 2 * ε₂ = δ₁ * ε₂ / 2 := by ring
                linarith
        have hAε : dist (zoom D γ (compA (preimageSet D γ) t)) (zoom D γ t₀) < ε₁ := by
          refine hδ₁ _ (gamma_compA_mem_carrier D γ hne htU) ?_
          rw [Real.dist_eq]
          have h1 : compA (preimageSet D γ) t - t₀
              = -(compB (preimageSet D γ) t - compA (preimageSet D γ) t)
                + (compB (preimageSet D γ) t - t₀) := by ring
          calc |compA (preimageSet D γ) t - t₀|
              = |-(compB (preimageSet D γ) t - compA (preimageSet D γ) t)
                + (compB (preimageSet D γ) t - t₀)| := by rw [h1]
            _ ≤ |-(compB (preimageSet D γ) t - compA (preimageSet D γ) t)|
                + |compB (preimageSet D γ) t - t₀| := abs_add_le _ _
            _ = (compB (preimageSet D γ) t - compA (preimageSet D γ) t)
                + |compB (preimageSet D γ) t - t₀| := by rw [abs_neg, abs_of_pos hba_pos]
            _ < δ₁ / 2 + δ₁ / 2 := by
                have : |compB (preimageSet D γ) t - t₀| ≤ |t - t₀| := by
                  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
                linarith
            _ = δ₁ := by ring
        linarith [hchord, hAε, hBε,
          le_max_right (2 * Real.pi * ε₂ + ε₁) (3 * ε₁)]
  exact lt_of_lt_of_le hbound (max_le hε₂lt.le hε₁lt.le)



/-- The convex combination of two points of the closed disc, clamped to `[0,1]`. -/
theorem comb_mem_closedBall (z w : Metric.closedBall (0 : ℂ) 1) (r : ℝ) (hr : r ∈ Set.Icc 0 1) :
    (1 - r) • (z : ℂ) + r • (w : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 :=
  (convex_iff_add_mem.mp (convex_closedBall (0 : ℂ) 1)) z.2 w.2 (sub_nonneg.mpr hr.2) hr.1 (by ring)

/-! ## 8. The push-off homotopy -/

theorem continuous_circlePoint : Continuous (fun θ : ℝ => ((circlePoint θ : ℂ))) := by
  have h : (fun θ : ℝ => ((circlePoint θ : ℂ))) = fun θ : ℝ => Complex.exp (θ * Complex.I) := rfl
  rw [h]
  exact Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

theorem zoom_congr (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) {a b : ℝ} (h : γ a = γ b) :
    zoom D γ a = zoom D γ b := by
  simp only [zoom, h]

theorem reroutePt_on_component (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) {t₀ : ℝ}
    (ht₀ : t₀ ∈ preimageSet D γ) {t : ℝ}
    (ht : t ∈ ordConnectedComponent (preimageSet D γ) t₀) :
    (reroutePt D γ t : ℂ) = (circlePoint (angle D γ (compA (preimageSet D γ) t₀)
      + ((t - compA (preimageSet D γ) t₀)
          / (compB (preimageSet D γ) t₀ - compA (preimageSet D γ) t₀))
        * arcDelta (angle D γ (compA (preimageSet D γ) t₀))
            (angle D γ (compB (preimageSet D γ) t₀))) : ℂ) := by
  have hA : compA (preimageSet D γ) t = compA (preimageSet D γ) t₀ :=
    compA_eq_of_mem (U := preimageSet D γ) ht
  have hB : compB (preimageSet D γ) t = compB (preimageSet D γ) t₀ :=
    compB_eq_of_mem (U := preimageSet D γ) ht
  simp only [reroutePt, compU]
  rw [hA, hB]

theorem continuousAt_reroutePt_of_mem (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) {t₀ : ℝ} (ht₀ : t₀ ∈ preimageSet D γ) :
    ContinuousAt (fun t : ℝ => (reroutePt D γ t : ℂ)) t₀ := by
  set a := compA (preimageSet D γ) t₀ with ha
  set b := compB (preimageSet D γ) t₀ with hb
  set θa := angle D γ a with hθa
  set d := arcDelta θa (angle D γ b) with hd
  have hV : ordConnectedComponent (preimageSet D γ) t₀ ∈ nhds t₀ :=
    (isOpen_ordConnectedComponent (preimageSet_open D γ) t₀).mem_nhds
      (self_mem_ordConnectedComponent.mpr ht₀)
  have hcont : ContinuousAt (fun t : ℝ => (circlePoint (θa + ((t - a) / (b - a)) * d) : ℂ)) t₀ :=
    (continuous_circlePoint.continuousAt).comp (by
      refine ContinuousAt.add continuousAt_const (ContinuousAt.mul ?_ continuousAt_const)
      exact (continuousAt_id.sub continuousAt_const).div_const (b - a))
  refine hcont.congr ?_
  filter_upwards [hV] with t ht
  have h1 := reroutePt_on_component D γ ht₀ ht
  rw [← ha, ← hb, ← hθa, ← hd] at h1
  exact h1.symm

theorem tendsto_zoom_within (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) {t₀ : ℝ} (hmem : γ t₀ ∈ D.carrier) :
    Tendsto (fun t : ℝ => (zoom D γ t : ℂ)) (nhdsWithin t₀ (preimageSet D γ))
      (nhds ((zoom D γ t₀ : ℂ))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := tendsto_zoom D γ hmem ε hε
  have hball : Metric.ball t₀ δ ∩ preimageSet D γ ∈ nhdsWithin t₀ (preimageSet D γ) := by
    rw [nhdsWithin, mem_inf_iff]
    exact ⟨Metric.ball t₀ δ, Metric.ball_mem_nhds t₀ hδpos, preimageSet D γ,
      Filter.mem_principal.mpr (subset_refl _), rfl⟩
  refine Filter.mem_of_superset hball ?_
  rintro t ⟨htb, htU⟩
  rw [Metric.mem_ball] at htb
  have := hδ t (D.interior_subset_carrier htU) htb
  simpa [Subtype.dist_eq] using this

theorem tendsto_reroutePt_C (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) (hne : ∃ x, x ∉ preimageSet D γ)
    {t₀ : ℝ} (ht₀ : t₀ ∉ preimageSet D γ) (hmem : γ t₀ ∈ D.carrier) :
    Tendsto (fun t : ℝ => (reroutePt D γ t : ℂ)) (nhdsWithin t₀ (preimageSet D γ))
      (nhds ((zoom D γ t₀ : ℂ))) :=
  (continuous_subtype_val.tendsto (zoom D γ t₀)).comp (tendsto_reroutePt D γ hne ht₀ hmem)

theorem reroutePt_add_two_pi (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) (hne : ∃ x, x ∉ preimageSet D γ)
    {t : ℝ} (ht : t ∈ preimageSet D γ) :
    reroutePt D γ (t + 2 * Real.pi) = reroutePt D γ t := by
  have hper := preimageSet_periodic D γ
  have hA : compA (preimageSet D γ) (t + 2 * Real.pi) = compA (preimageSet D γ) t + 2 * Real.pi :=
    compA_add_pi (preimageSet_open D γ) hper hne ht
  have hB : compB (preimageSet D γ) (t + 2 * Real.pi) = compB (preimageSet D γ) t + 2 * Real.pi :=
    compB_add_pi (preimageSet_open D γ) hper hne ht
  have hga : γ (compA (preimageSet D γ) (t + 2 * Real.pi)) = γ (compA (preimageSet D γ) t) := by
    rw [hA]; exact γ.periodic _
  have hgb : γ (compB (preimageSet D γ) (t + 2 * Real.pi)) = γ (compB (preimageSet D γ) t) := by
    rw [hB]; exact γ.periodic _
  have ha : angle D γ (compA (preimageSet D γ) (t + 2 * Real.pi))
      = angle D γ (compA (preimageSet D γ) t) := by
    simp only [angle]; rw [zoom_congr D γ hga]
  have hb : angle D γ (compB (preimageSet D γ) (t + 2 * Real.pi))
      = angle D γ (compB (preimageSet D γ) t) := by
    simp only [angle]; rw [zoom_congr D γ hgb]
  have hu : compU (preimageSet D γ) (t + 2 * Real.pi) = compU (preimageSet D γ) t := by
    simp only [compU]; rw [hA, hB]; ring
  simp only [reroutePt]
  rw [ha, hb, hu]

/-- **The push-off homotopy**: `γ` at `s = 0`, the rerouted loop at `s = 1`. -/
noncomputable def Hfun (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) (s t : ℝ) : R3 :=
  if h : γ t ∈ D.interior then
    D.e ⟨(1 - clamp s) • (zoom D γ t : ℂ) + (clamp s) • (reroutePt D γ t : ℂ),
      comb_mem_closedBall _ _ _ (clamp_mem_Icc s)⟩
  else γ t

theorem Hfun_apply_of_mem (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) {s t : ℝ} (h : γ t ∈ D.interior) :
    Hfun D γ s t = D.e ⟨(1 - clamp s) • (zoom D γ t : ℂ) + (clamp s) • (reroutePt D γ t : ℂ),
      comb_mem_closedBall _ _ _ (clamp_mem_Icc s)⟩ := dif_pos h

theorem Hfun_apply_of_notMem (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) {s t : ℝ} (h : γ t ∉ D.interior) :
    Hfun D γ s t = γ t := dif_neg h

theorem Hfun_zero (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) (t : ℝ) : Hfun D γ 0 t = γ t := by
  by_cases h : γ t ∈ D.interior
  · rw [Hfun_apply_of_mem D γ h]
    have hcomb : (1 - clamp 0) • (zoom D γ t : ℂ) + (clamp 0) • (reroutePt D γ t : ℂ)
        = (zoom D γ t : ℂ) := by rw [clamp_zero]; simp
    rw [show (⟨(1 - clamp 0) • (zoom D γ t : ℂ) + (clamp 0) • (reroutePt D γ t : ℂ),
        comb_mem_closedBall _ _ _ (clamp_mem_Icc 0)⟩ : Metric.closedBall (0:ℂ) 1) = zoom D γ t from
      Subtype.ext hcomb]
    exact D_e_zoom D γ (D.interior_subset_carrier h)
  · rw [Hfun_apply_of_notMem D γ h]

theorem Hfun_mem (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) (s t : ℝ) :
    Hfun D γ s t ∈ (P).carrier := by
  by_cases h : γ t ∈ D.interior
  · rw [Hfun_apply_of_mem D γ h]
    exact D.carrier_subset_surface ⟨_, rfl⟩
  · rw [Hfun_apply_of_notMem D γ h]
    exact γ.mem t

theorem Hfun_periodic (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) (hne : ∃ x, x ∉ preimageSet D γ)
    (s t : ℝ) : Hfun D γ s (t + 2 * Real.pi) = Hfun D γ s t := by
  by_cases h : γ t ∈ D.interior
  · have h' : γ (t + 2 * Real.pi) ∈ D.interior := by rw [γ.periodic t]; exact h
    rw [Hfun_apply_of_mem D γ h', Hfun_apply_of_mem D γ h]
    congr 1
    apply Subtype.ext
    show (1 - clamp s) • (zoom D γ (t + 2 * Real.pi) : ℂ)
        + (clamp s) • (reroutePt D γ (t + 2 * Real.pi) : ℂ)
      = (1 - clamp s) • (zoom D γ t : ℂ) + (clamp s) • (reroutePt D γ t : ℂ)
    rw [zoom_congr D γ (γ.periodic t), congrArg Subtype.val (reroutePt_add_two_pi D γ hne h)]
  · have h' : γ (t + 2 * Real.pi) ∉ D.interior := by rw [γ.periodic t]; exact h
    rw [Hfun_apply_of_notMem D γ h', Hfun_apply_of_notMem D γ h, γ.periodic t]


theorem Hfun_one (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) (t : ℝ) : Hfun D γ 1 t
    = if γ t ∈ D.interior then D.e (reroutePt D γ t) else γ t := by
  by_cases h : γ t ∈ D.interior
  · rw [Hfun_apply_of_mem D γ h, if_pos h]
    congr 1
    apply Subtype.ext
    show (1 - clamp 1) • (zoom D γ t : ℂ) + (clamp 1) • (reroutePt D γ t : ℂ)
      = (reroutePt D γ t : ℂ)
    rw [clamp_one]; simp
  · rw [Hfun_apply_of_notMem D γ h, if_neg h]

theorem Hfun_continuous (D : DiscRegion (P))
    (γ : Work.CoreTopology.ClosedCurve (P)) (hne : ∃ x, x ∉ preimageSet D γ) :
    Continuous (Function.uncurry (Hfun D γ)) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s₀, t₀⟩
  by_cases hmem : γ t₀ ∈ D.interior
  · have hcar : γ t₀ ∈ D.carrier := D.interior_subset_carrier hmem
    have hU : preimageSet D γ ∈ nhds t₀ := (preimageSet_open D γ).mem_nhds hmem
    have hz : ContinuousAt (fun p : ℝ × ℝ => (zoom D γ p.2 : ℂ)) (s₀, t₀) := by
      have hsub : Tendsto (fun p : ℝ × ℝ => p.2) (nhds (s₀, t₀))
          (nhdsWithin t₀ (preimageSet D γ)) := by
        rw [nhdsWithin_eq_nhds.mpr hU]
        exact continuous_snd.continuousAt
      exact Filter.Tendsto.comp (f := fun p : ℝ × ℝ => p.2)
        (g := fun t : ℝ => (zoom D γ t : ℂ)) (tendsto_zoom_within D γ hcar) hsub
    have hr : ContinuousAt (fun p : ℝ × ℝ => (reroutePt D γ p.2 : ℂ)) (s₀, t₀) :=
      Filter.Tendsto.comp (f := fun p : ℝ × ℝ => p.2)
        (g := fun t : ℝ => (reroutePt D γ t : ℂ))
        (continuousAt_reroutePt_of_mem D γ hmem) continuous_snd.continuousAt
    have hcomb : ContinuousAt (fun p : ℝ × ℝ => (⟨(1 - clamp p.1) • (zoom D γ p.2 : ℂ)
        + (clamp p.1) • (reroutePt D γ p.2 : ℂ),
          comb_mem_closedBall _ _ _ (clamp_mem_Icc p.1)⟩ : Metric.closedBall (0:ℂ) 1))
        (s₀, t₀) := by
      have hc : ContinuousAt (fun p : ℝ × ℝ => (1 - clamp p.1) • (zoom D γ p.2 : ℂ)
          + (clamp p.1) • (reroutePt D γ p.2 : ℂ)) (s₀, t₀) :=
        (((continuous_const.sub (continuous_clamp.comp continuous_fst)).continuousAt).smul hz).add
          (((continuous_clamp.comp continuous_fst).continuousAt).smul hr)
      rw [ContinuousAt, Metric.tendsto_nhds] at hc ⊢
      intro ε hε
      filter_upwards [hc ε hε] with p hp
      simpa [Subtype.dist_eq] using hp
    have hDe : ContinuousAt (fun p : ℝ × ℝ => D.e (⟨(1 - clamp p.1) • (zoom D γ p.2 : ℂ)
        + (clamp p.1) • (reroutePt D γ p.2 : ℂ),
          comb_mem_closedBall _ _ _ (clamp_mem_Icc p.1)⟩ : Metric.closedBall (0:ℂ) 1))
        (s₀, t₀) :=
      D.e.continuous.continuousAt.comp hcomb
    refine hDe.congr ?_
    filter_upwards [(continuous_snd.continuousAt).preimage_mem_nhds hU] with p hp
    exact (Hfun_apply_of_mem D γ hp).symm
  · by_cases hcar : γ t₀ ∈ D.carrier
    · set S : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.2 ∈ preimageSet D γ} with hS
      set l₁ : Filter (ℝ × ℝ) := nhds (s₀, t₀) ⊓ 𝓟 S with hl₁
      set l₂ : Filter (ℝ × ℝ) := nhds (s₀, t₀) ⊓ 𝓟 Sᶜ with hl₂
      have hSl₁ : S ∈ l₁ := by
        rw [hl₁, mem_inf_iff]
        exact ⟨univ, univ_mem, S, Filter.mem_principal.mpr (subset_refl _), (Set.univ_inter S).symm⟩
      have hScl₂ : Sᶜ ∈ l₂ := by
        rw [hl₂, mem_inf_iff]
        exact ⟨univ, univ_mem, Sᶜ, Filter.mem_principal.mpr (subset_refl _),
          (Set.univ_inter Sᶜ).symm⟩
      have hls : l₁ ⊔ l₂ = nhds (s₀, t₀) := by
        rw [hl₁, hl₂, ← inf_sup_left, Filter.sup_principal, Set.union_compl_self,
          Filter.principal_univ, inf_top_eq]
      have hsnd : Tendsto (fun p : ℝ × ℝ => p.2) l₁ (nhdsWithin t₀ (preimageSet D γ)) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨continuous_snd.continuousAt.mono_left inf_le_left, hSl₁⟩
      have hz : Tendsto (fun p : ℝ × ℝ => (zoom D γ p.2 : ℂ)) l₁ (nhds ((zoom D γ t₀ : ℂ))) :=
        Filter.Tendsto.comp (f := fun p : ℝ × ℝ => p.2)
          (g := fun t : ℝ => (zoom D γ t : ℂ)) (tendsto_zoom_within D γ hcar) hsnd
      have hr : Tendsto (fun p : ℝ × ℝ => (reroutePt D γ p.2 : ℂ)) l₁
          (nhds ((zoom D γ t₀ : ℂ))) :=
        Filter.Tendsto.comp (f := fun p : ℝ × ℝ => p.2)
          (g := fun t : ℝ => (reroutePt D γ t : ℂ)) (tendsto_reroutePt_C D γ hne hmem hcar) hsnd
      have hle : l₁ ≤ nhds (s₀, t₀) := inf_le_left
      have hclamp : Tendsto (fun p : ℝ × ℝ => clamp p.1) l₁ (nhds (clamp s₀)) :=
        ((continuous_clamp.comp continuous_fst).continuousAt).mono_left hle
      have hD1 : Tendsto (fun p : ℝ × ℝ => D.e (⟨(1 - clamp p.1) • (zoom D γ p.2 : ℂ)
          + (clamp p.1) • (reroutePt D γ p.2 : ℂ),
            comb_mem_closedBall _ _ _ (clamp_mem_Icc p.1)⟩ : Metric.closedBall (0:ℂ) 1)) l₁
          (nhds (γ t₀)) := by
        have hc : Tendsto (fun p : ℝ × ℝ => (1 - clamp p.1) • (zoom D γ p.2 : ℂ)
            + (clamp p.1) • (reroutePt D γ p.2 : ℂ)) l₁ (nhds ((zoom D γ t₀ : ℂ))) := by
          have h1 : Tendsto (fun p : ℝ × ℝ => (1 - clamp p.1) • (zoom D γ p.2 : ℂ)) l₁
              (nhds ((1 - clamp s₀) • (zoom D γ t₀ : ℂ))) :=
            (((continuous_const.sub (continuous_clamp.comp continuous_fst)).continuousAt).mono_left
              hle).smul hz
          have h2 : Tendsto (fun p : ℝ × ℝ => (clamp p.1) • (reroutePt D γ p.2 : ℂ)) l₁
              (nhds ((clamp s₀) • (zoom D γ t₀ : ℂ))) := hclamp.smul hr
          have h3 := h1.add h2
          have heq : (1 - clamp s₀) • (zoom D γ t₀ : ℂ) + (clamp s₀) • (zoom D γ t₀ : ℂ)
              = (zoom D γ t₀ : ℂ) := by rw [← add_smul, sub_add_cancel, one_smul]
          rwa [heq] at h3
        have h4 : Tendsto (fun p : ℝ × ℝ => (⟨(1 - clamp p.1) • (zoom D γ p.2 : ℂ)
            + (clamp p.1) • (reroutePt D γ p.2 : ℂ),
              comb_mem_closedBall _ _ _ (clamp_mem_Icc p.1)⟩ : Metric.closedBall (0:ℂ) 1)) l₁
            (nhds (zoom D γ t₀)) := by
          rw [Metric.tendsto_nhds] at hc ⊢
          intro ε hε
          filter_upwards [hc ε hε] with p hp
          simpa [Subtype.dist_eq] using hp
        have h5 : Tendsto (fun z : Metric.closedBall (0:ℂ) 1 => D.e z) (nhds (zoom D γ t₀))
            (nhds (γ t₀)) := by
          rw [show γ t₀ = D.e (zoom D γ t₀) from (D_e_zoom D γ hcar).symm]
          exact D.e.continuous.tendsto (zoom D γ t₀)
        exact Filter.Tendsto.comp h5 h4
      have hA : Tendsto (fun p : ℝ × ℝ => Function.uncurry (Hfun D γ) p) l₁
          (nhds (Function.uncurry (Hfun D γ) (s₀, t₀))) := by
        rw [show Function.uncurry (Hfun D γ) (s₀, t₀) = γ t₀ from
          Hfun_apply_of_notMem D γ hmem]
        refine Filter.Tendsto.congr' ?_ hD1
        filter_upwards [hSl₁] with p hp
        exact (Hfun_apply_of_mem D γ hp).symm
      have hB : Tendsto (fun p : ℝ × ℝ => Function.uncurry (Hfun D γ) p) l₂
          (nhds (Function.uncurry (Hfun D γ) (s₀, t₀))) := by
        rw [show Function.uncurry (Hfun D γ) (s₀, t₀) = γ t₀ from
          Hfun_apply_of_notMem D γ hmem]
        have hγ2 : Tendsto (fun p : ℝ × ℝ => γ p.2) l₂ (nhds (γ t₀)) :=
          (γ.cont.continuousAt.comp continuous_snd.continuousAt).mono_left inf_le_left
        refine Filter.Tendsto.congr' ?_ hγ2
        filter_upwards [hScl₂] with p hp
        exact (Hfun_apply_of_notMem D γ hp).symm
      rw [ContinuousAt, ← hls, tendsto_sup]
      exact ⟨hA, hB⟩
    · have hV : {p : ℝ × ℝ | γ p.2 ∉ D.carrier} ∈ nhds (s₀, t₀) := by
        have h1 : D.carrierᶜ ∈ nhds (γ t₀) := (isClosed_carrier D).isOpen_compl.mem_nhds hcar
        exact ((γ.cont.comp continuous_snd).continuousAt (x := (s₀, t₀))).preimage_mem_nhds h1
      have hγ2 : ContinuousAt (fun p : ℝ × ℝ => γ p.2) (s₀, t₀) :=
        γ.cont.continuousAt.comp continuous_snd.continuousAt
      refine hγ2.congr ?_
      filter_upwards [hV] with p hp
      exact (Hfun_apply_of_notMem D γ (fun hc => hp (D.interior_subset_carrier hc))).symm


/-- **The push-off of a loop off the interior of an embedded disc.**

Let `D` be an embedded disc of the surface `F = P.carrier` of a parametrised torus, let `X` be a
region of `F` containing the boundary circle `D.boundary`, and let `γ` be a closed curve of `F` with
values in `X`.  Then `γ` is homotopic, through closed curves of `F`, to a closed curve with values
in `X` which avoids the interior of `D`.

Only the boundary circle of the disc is needed (and not its interior): the part of `γ` that runs
through the interior of `D` is rerouted along the boundary circle, which meets `X` by hypothesis. -/
theorem discPushOff_boundary {P : Work.CoreTopology.ParamTorus} (D : DiscRegion P) {X : Set R3}
    (hsub : D.boundary ⊆ X) (γ : Work.CoreTopology.ClosedCurve P) (hγ : ∀ t : ℝ, γ t ∈ X) :
    ∃ γ' : Work.CoreTopology.ClosedCurve P,
      (∀ t : ℝ, γ' t ∈ X ∧ γ' t ∉ D.interior) ∧ Work.CoreTopology.Homotopic P γ γ' := by
  classical
  rcases eq_empty_or_nonempty (preimageSet D γ) with hempty | hne
  · refine ⟨γ, fun t => ⟨hγ t, ?_⟩, Work.CoreTopology.Homotopic.refl P γ⟩
    intro hcon
    have : t ∈ preimageSet D γ := hcon
    rw [hempty] at this
    exact this
  · by_cases huniv : preimageSet D γ = univ
    · have hcarrier : ∀ t, γ t ∈ D.carrier := fun t =>
        D.interior_subset_carrier (by
          have : t ∈ preimageSet D γ := by rw [huniv]; trivial
          exact this)
      refine ⟨Work.InnermostDisk.constCurve P (D.e (circlePoint 0)) (D.mem (circlePoint 0)),
        ?_, ?_⟩
      · intro t
        refine ⟨hsub (D_e_circlePoint_mem_boundary D 0), ?_⟩
        intro hc
        exact Set.disjoint_left.mp (disjoint_interior_boundary D) hc
          (D_e_circlePoint_mem_boundary D 0)
      · exact homotopic_constCurve_of_range_subset_discRegion D γ hcarrier (circlePoint 0)
    · have hne' : ∃ x, x ∉ preimageSet D γ := by
        by_contra h
        push_neg at h
        exact huniv (Set.eq_univ_iff_forall.mpr h)
      let γ' : Work.CoreTopology.ClosedCurve P :=
        { γ := fun t => Hfun D γ 1 t
          cont := (Hfun_continuous D γ hne').comp (continuous_const.prodMk continuous_id)
          periodic := fun t => Hfun_periodic D γ hne' 1 t
          mem := fun t => Hfun_mem D γ 1 t }
      have hγ'one : ∀ t, γ' t = (if γ t ∈ D.interior then D.e (reroutePt D γ t) else γ t) :=
        fun t => Hfun_one D γ t
      refine ⟨γ', ?_, ?_⟩
      · intro t
        by_cases h : γ t ∈ D.interior
        · rw [hγ'one t, if_pos h]
          exact ⟨hsub (D_e_circlePoint_mem_boundary D _),
            fun hc => Set.disjoint_left.mp (disjoint_interior_boundary D) hc
              (D_e_circlePoint_mem_boundary D _)⟩
        · rw [hγ'one t, if_neg h]
          exact ⟨hγ t, h⟩
      · exact ⟨Hfun D γ, Hfun_continuous D γ hne',
          fun s t => Hfun_mem D γ s t, fun t => Hfun_zero D γ t, fun t => rfl,
          fun s t => Hfun_periodic D γ hne' s t⟩

end PushOffGeneral

/-! ## The dictionary between quasi-periodic lifts and closed curves -/

/-- **The closed curve of the torus underlying a quasi-periodic lift.**  A continuous
`Λ : ℝ → ℂ` with `Λ (t + 2π) = Λ t + periodPt a b` projects, through the parametrisation
`planePsi P`, to a `2π`-periodic curve of the torus: the lattice periodicity of the
parametrisation makes the projection of the shift invisible. -/
def projCurve (P : Work.CoreTopology.ParamTorus) (Λ : ℝ → ℂ) (hΛc : Continuous Λ)
    (a b : ℤ) (hper : ∀ t : ℝ, Λ (t + 2 * Real.pi) = Λ t + periodPt a b) :
    Work.CoreTopology.ClosedCurve P where
  γ := fun t => planePsi P (Λ t)
  cont := (continuous_planePsi P).comp hΛc
  periodic := fun t => by
    show planePsi P (Λ (t + 2 * Real.pi)) = planePsi P (Λ t)
    rw [hper t, planePsi_add_periodPt]
  mem := fun t => planePsi_mem_carrier P (Λ t)

theorem projCurve_apply (P : Work.CoreTopology.ParamTorus) (Λ : ℝ → ℂ) (hΛc : Continuous Λ)
    (a b : ℤ) (hper : ∀ t : ℝ, Λ (t + 2 * Real.pi) = Λ t + periodPt a b) (t : ℝ) :
    projCurve P Λ hΛc a b hper t = planePsi P (Λ t) := rfl

/-- **The winding vector of the projected curve.**  The pair of real functions
`(re ∘ Λ, im ∘ Λ)` is a lift of the projected curve (the parametrisation is the composite of
`planePsi` with the identification `ℂ ≅ ℝ²`), and by `hΛper` it advances by `(a, b)` over one
period: hence the winding vector of the projection is `(a, b)`. -/
theorem windingOf_projCurve (P : Work.CoreTopology.ParamTorus) (Λ : ℝ → ℂ) (hΛc : Continuous Λ)
    (a b : ℤ) (hper : ∀ t : ℝ, Λ (t + 2 * Real.pi) = Λ t + periodPt a b) :
    Work.SurgeryInvariance.windingOf P (projCurve P Λ hΛc a b hper) = (a, b) := by
  classical
  let L : Work.CoreTopology.LiftOf P (projCurve P Λ hΛc a b hper) :=
    { Θ := fun t => (Λ t).re
      Φ := fun t => (Λ t).im
      contΘ := Complex.continuous_re.comp hΛc
      contΦ := Complex.continuous_im.comp hΛc
      lifts := fun t => rfl }
  have hspec := L.winding_spec
  have hre : L.Θ (2 * Real.pi) = L.Θ 0 + (a : ℝ) * (2 * Real.pi) := by
    have h := congrArg Complex.re (hper 0)
    simp only [Complex.add_re, periodPt_re, zero_add] at h
    simpa [L] using h
  have him : L.Φ (2 * Real.pi) = L.Φ 0 + (b : ℝ) * (2 * Real.pi) := by
    have h := congrArg Complex.im (hper 0)
    simp only [Complex.add_im, periodPt_im, zero_add] at h
    simpa [L] using h
  have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hfst : (L.winding).1 = a := by
    have hmul : ((L.winding).1 : ℝ) * (2 * Real.pi) = (a : ℝ) * (2 * Real.pi) := by
      linarith [hspec.1, hre]
    exact_mod_cast mul_right_cancel₀ h2π hmul
  have hsnd : (L.winding).2 = b := by
    have hmul : ((L.winding).2 : ℝ) * (2 * Real.pi) = (b : ℝ) * (2 * Real.pi) := by
      linarith [hspec.2, him]
    exact_mod_cast mul_right_cancel₀ h2π hmul
  have hLw : L.winding = (a, b) := Prod.ext hfst hsnd
  rw [Work.SurgeryInvariance.windingOf_eq P _ L]
  exact hLw

/-- **Straightening a closed curve with prescribed winding vector into a quasi-periodic lift.**
A closed curve `γ` of the torus with winding vector `(a, b)` has a lift `Λ₁ : ℝ → ℂ` to the
parameter plane which is quasi-periodic with shift `periodPt a b`. -/
theorem exists_quasiperiodic_of_winding (P : Work.CoreTopology.ParamTorus)
    (γ : Work.CoreTopology.ClosedCurve P) {a b : ℤ}
    (hw : Work.SurgeryInvariance.windingOf P γ = (a, b)) :
    ∃ Λ₁ : ℝ → ℂ, Continuous Λ₁ ∧
      (∀ t : ℝ, Λ₁ (t + 2 * Real.pi) = Λ₁ t + periodPt a b) ∧
      (∀ t : ℝ, planePsi P (Λ₁ t) = γ t) := by
  classical
  obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf P γ
  have hLw : L.winding = (a, b) := by
    rw [← Work.SurgeryInvariance.windingOf_eq P γ L]; exact hw
  have hfst : (L.winding).1 = a := by
    simpa using (congrArg Prod.fst hLw)
  have hsnd : (L.winding).2 = b := by
    simpa using (congrArg Prod.snd hLw)
  refine ⟨fun t => ((L.Θ t : ℝ) : ℂ) + ((L.Φ t : ℝ) : ℂ) * Complex.I, ?_, ?_, ?_⟩
  · exact (Complex.continuous_ofReal.comp L.contΘ).add
      ((Complex.continuous_ofReal.comp L.contΦ).mul continuous_const)
  · intro t
    have h1 : L.Θ (t + 2 * Real.pi) = L.Θ t + (a : ℝ) * (2 * Real.pi) := by
      have h := (L.period_shift_winding t).1
      rw [hfst] at h
      exact h
    have h2 : L.Φ (t + 2 * Real.pi) = L.Φ t + (b : ℝ) * (2 * Real.pi) := by
      have h := (L.period_shift_winding t).2
      rw [hsnd] at h
      exact h
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, periodPt_re]
      rw [h1]
      ring
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, mul_one, periodPt_im]
      rw [h2]
      ring
  · intro t
    rw [planePsi_apply]
    have hre : (((L.Θ t : ℝ) : ℂ) + ((L.Φ t : ℝ) : ℂ) * Complex.I).re = L.Θ t := by simp
    have him : (((L.Θ t : ℝ) : ℂ) + ((L.Φ t : ℝ) : ℂ) * Complex.I).im = L.Φ t := by simp
    rw [hre, him]
    exact L.lifts t

/-- **Pushing a lifted curve off the interiors of the disc translates.**

Let `D` be an embedded disc of the surface `F = P.carrier` of a parametrised torus `P`, let `X` be a
region of `F` open in the carrier and containing the boundary circle `D.boundary`, and let
`Λ : ℝ → ℂ` be a lift to the parameter plane of a closed curve of the torus whose image lies in `X`
(so `Λ` is continuous, quasi-periodic with shift `periodPt a b`, and lands in
`Xtilde P X = planePsi P ⁻¹' X`).  Then there is a quasi-periodic curve `Λ₁` with the same shift,
still landing in `Xtilde P X`, which avoids the interior of every lattice translate of the lifted
disc: `Λ₁ t ∉ Xtilde P D.interior` for all `t`.

Equivalently: the excursions of the lifted curve through the interior of a translate of the disc
can be rerouted along the boundary circle of that translate, without changing the period shift and
without leaving the preimage of `X`. -/
theorem pushoff_plane_interior
    {P : Work.CoreTopology.ParamTorus} {X : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (D : Work.SurgeryInvariance.DiscRegion P)
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hsub : D.boundary ⊆ X)
    {a b : ℤ} {Λ : ℝ → ℂ}
    (hΛc : Continuous Λ)
    (hΛper : ∀ t : ℝ, Λ (t + 2 * Real.pi) = Λ t + Work.BoxShrink.PinchOff.periodPt a b)
    (hΛmem : ∀ t : ℝ, Λ t ∈ Work.BoxShrink.PinchOff.Xtilde P X) :
    ∃ Λ₁ : ℝ → ℂ, Continuous Λ₁ ∧
      (∀ t : ℝ, Λ₁ (t + 2 * Real.pi) = Λ₁ t + Work.BoxShrink.PinchOff.periodPt a b) ∧
      (∀ t : ℝ, Λ₁ t ∈ Work.BoxShrink.PinchOff.Xtilde P X) ∧
      (∀ t : ℝ, Λ₁ t ∉ Work.BoxShrink.PinchOff.Xtilde P D.interior) := by
  classical
  have hγmem : ∀ t : ℝ, projCurve P Λ hΛc a b hΛper t ∈ X := by
    intro t
    rw [projCurve_apply, ← mem_Xtilde]
    exact hΛmem t
  have hwγ : Work.SurgeryInvariance.windingOf P (projCurve P Λ hΛc a b hΛper) = (a, b) :=
    windingOf_projCurve P Λ hΛc a b hΛper
  obtain ⟨γ', hγ'mem, hhom⟩ :=
    PushOffGeneral.discPushOff_boundary D hsub (projCurve P Λ hΛc a b hΛper) hγmem
  have hwγ' : Work.SurgeryInvariance.windingOf P γ' = (a, b) := by
    rw [← Work.SurgeryInvariance.WindingOf.homotopic_eq hhom]
    exact hwγ
  obtain ⟨Λ₁, hΛ₁c, hΛ₁per, hΛ₁proj⟩ := exists_quasiperiodic_of_winding P γ' hwγ'
  refine ⟨Λ₁, hΛ₁c, hΛ₁per, ?_, ?_⟩
  · intro t
    rw [mem_Xtilde, hΛ₁proj t]
    exact (hγ'mem t).1
  · intro t
    rw [mem_Xtilde, hΛ₁proj t]
    exact (hγ'mem t).2

end

end Work.BoxShrink.PinchOff
