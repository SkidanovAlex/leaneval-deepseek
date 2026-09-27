import Mathlib
import Submission.Work.Mostow.geodDeps
import Submission.Work.Mostow.axisDichotomy
import Submission.Work.Mostow.gapA.volH1Ico
import Submission.Work.Mostow.volH_le_fundamentalDomain

/-!
# The covolume bound along the axis of a discrete subgroup of `PO 1 1`

`PO 1 1` is the isometry group of `ℍ¹`, the hyperbolic line, and in the signed distance
coordinate `sc u = arsinh (u 0)` of the chart `E 1 = ℝ` it acts by maps of the form
`x ↦ Phi g 0 + x` (translations) or `x ↦ Phi g 0 - x` (reflections).

The theorem `Work.Mostow.geeAxisCovol` states: if `D` is a discrete subgroup and `g₀ ∈ D` is
fixed-point free with minimal displacement `L = hdist 0 (g₀ • 0)` among the fixed-point free
elements of `D`, then `L ≤ 2 · volH 1 DY` for every fundamental domain `DY` of `D`.

The proof exhibits a set `A` of `volH`-measure `L/2` whose `D`-translates are pairwise a.e.
disjoint: in the signed coordinate `A` is the half-open interval `[a, a + L/2)`, where `a` is a
fixed point of a reflection in `D` if `D` contains one, and `a = 0` otherwise.  The packing bound
`Work.Mostow.volH_le_fundamentalDomain` then gives `L/2 ≤ volH 1 DY`.  The two ingredients
controlling the translates are consequences of the minimality of `L`:

* a nontrivial translation of `D` has displacement at least `L`;
* the fixed points of two distinct reflections of `D` are at least `L/2` apart.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Pointwise

namespace GeeAxisCovolAux

open AxisDich

noncomputable section

/-- The signed coordinate of the `PO 1 1`-action is the action `Phi` on the line. -/
lemma sc_smul (g : PO 1 1) (u : E 1) : sc (g • u) = Phi g (sc u) := by
  have hu : g • u = g • pt (sc u) := by rw [pt_sc u]
  rw [hu]
  rfl

/-- Every isometry of `ℍ¹` is, in the signed coordinate, a translation or a reflection. -/
lemma Phi_form' (hI : HypIsoData 1) (g : PO 1 1) :
    (∀ x : ℝ, Phi g x = Phi g 0 + x) ∨ (∀ x : ℝ, Phi g x = Phi g 0 - x) := by
  rcases Phi_form hI g with ⟨c, hc | hc⟩
  · left
    intro x
    have h0 : Phi g 0 = c := by rw [hc]; ring
    rw [h0, hc]
  · right
    intro x
    have h0 : Phi g 0 = c := by rw [hc]; ring
    rw [h0, hc]

lemma Phi_mul_apply (hA : POBasic 1) (g h : PO 1 1) (x : ℝ) :
    Phi (g * h) x = Phi g (Phi h x) := by
  rw [Phi_mul hA g h]
  rfl

lemma Phi_inv_comp (hA : POBasic 1) (g : PO 1 1) (x : ℝ) : Phi g (Phi g⁻¹ x) = x := by
  have h : Phi (g * g⁻¹) x = Phi g (Phi g⁻¹ x) := Phi_mul_apply hA g g⁻¹ x
  rw [mul_inv_cancel, Phi_one hA] at h
  simpa using h.symm

/-- A "reflection" of the hyperbolic line: in the signed coordinate, `x ↦ Phi g 0 - x`. -/
def IsRefl (g : PO 1 1) : Prop := ∀ x : ℝ, Phi g x = Phi g 0 - x

/-- The composition of a reflection with the inverse of a reflection is a translation. -/
lemma IsRefl.mul (hA : POBasic 1) {g h : PO 1 1} (hg : IsRefl g) (hh : IsRefl h) :
    ∀ x : ℝ, Phi (g * h) x = Phi g 0 - Phi h 0 + x := by
  intro x
  rw [Phi_mul_apply hA g h x, hh x, hg (Phi h 0 - x)]
  ring

lemma IsRefl.inv_zero (hA : POBasic 1) {g : PO 1 1} (hg : IsRefl g) : Phi g⁻¹ 0 = Phi g 0 := by
  have h2 := Phi_inv_comp hA g 0
  rw [hg (Phi g⁻¹ 0)] at h2
  linarith

lemma IsRefl.inv (hA : POBasic 1) {g : PO 1 1} (hg : IsRefl g) : IsRefl g⁻¹ := by
  have h0 : Phi g⁻¹ 0 = Phi g 0 := IsRefl.inv_zero hA hg
  intro x
  have h := Phi_inv_comp hA g x
  rw [hg (Phi g⁻¹ x)] at h
  rw [h0]
  linarith

/-- The half-open interval of `ℍ¹` with signed coordinates in `[a, b)`. -/
def isc (a b : ℝ) : Set (E 1) := {u : E 1 | u 0 ∈ Set.Ico (Real.sinh a) (Real.sinh b)}

lemma mem_isc (a b : ℝ) (u : E 1) : u ∈ isc a b ↔ sc u ∈ Set.Ico a b := by
  simp only [isc, Set.mem_ofPred_eq, sc, Set.mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by
      have := (Real.arsinh_le_arsinh (x := Real.sinh a) (y := u 0)).mpr h1
      rwa [Real.arsinh_sinh] at this, by
      have := (Real.arsinh_lt_arsinh (x := u 0) (y := Real.sinh b)).mpr h2
      rwa [Real.arsinh_sinh] at this⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by
      have := (Real.sinh_le_sinh (x := a) (y := Real.arsinh (u 0))).mpr h1
      rwa [Real.sinh_arsinh] at this, by
      have := (Real.sinh_lt_sinh (x := Real.arsinh (u 0)) (y := b)).mpr h2
      rwa [Real.sinh_arsinh] at this⟩

lemma measurableSet_isc (a b : ℝ) : MeasurableSet (isc a b) := by
  have hcont : Continuous fun v : E 1 => v.ofLp (0 : Fin 1) :=
    PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0
  show MeasurableSet ((fun v : E 1 => v.ofLp (0 : Fin 1)) ⁻¹'
    Set.Ico (Real.sinh a) (Real.sinh b))
  exact measurableSet_Ico.preimage hcont.measurable

/-- The `volH 1`-measure of a chart interval is its signed length. -/
lemma volH_isc (a b : ℝ) (hab : a ≤ b) :
    volH 1 (isc a b) = ENNReal.ofReal (b - a) := by
  rw [isc, Work.Mostow.gapA.volH1Ico (Real.sinh a) (Real.sinh b)
    (Real.sinh_le_sinh.mpr hab), Real.arsinh_sinh, Real.arsinh_sinh]

/-- A single point of the hyperbolic line is `volH 1`-null. -/
lemma volH_sc_singleton (hI : HypIsoData 1) (a : ℝ) : volH 1 {w : E 1 | sc w = a} = 0 := by
  rw [volHNull]
  have hset : {w : E 1 | sc w = a} = {pt a} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hw
      exact sc_inj hI (by rw [hw, sc_pt])
    · intro hw
      rw [hw, sc_pt]
  rw [hset]
  exact measure_singleton (pt a)

end

end GeeAxisCovolAux

open GeeAxisCovolAux AxisDich in
/-- **Covolume bound along an axis in `ℍ¹`.** -/
theorem geeAxisCovol
    (hA : Submission.Mostow.POActionProp 1) (hI : Submission.Mostow.HypIsometryProp 1)
    (D : Subgroup (LeanEval.Geometry.MostowRigidity.PO 1 1)) (hdisc : _root_.IsDiscrete (D : Set (LeanEval.Geometry.MostowRigidity.PO 1 1)))
    (g₀ : LeanEval.Geometry.MostowRigidity.PO 1 1) (hg₀ : g₀ ∈ D)
    (hgf : ∀ x : Submission.Mostow.E 1, g₀ • x ≠ x)
    (hmin : ∀ h ∈ D, (∀ x : Submission.Mostow.E 1, h • x ≠ x) →
      Submission.Mostow.hdist (0 : Submission.Mostow.E 1) (g₀ • (0 : Submission.Mostow.E 1))
        ≤ Submission.Mostow.hdist (0 : Submission.Mostow.E 1) (h • (0 : Submission.Mostow.E 1)))
    (hsq : ∀ h ∈ D, h * h ∈ Subgroup.zpowers g₀)
    (DY : Set (Submission.Mostow.E 1))
    (hFD : MeasureTheory.IsFundamentalDomain D DY (Submission.Mostow.volH 1)) :
    ENNReal.ofReal (Submission.Mostow.hdist (0 : Submission.Mostow.E 1) (g₀ • (0 : Submission.Mostow.E 1)))
      ≤ 2 * Submission.Mostow.volH 1 DY := by
  have hA' : POBasic 1 := POBasic.ofProp hA
  have hI' : HypIsoData 1 := HypIsoData.ofProp hI
  set L : ℝ := hdist (0 : E 1) (g₀ • (0 : E 1)) with hL
  have hL_eq : L = |Phi g₀ 0| := by
    rw [hL]
    rw [hdist_zero_eq_sc, sc_smul, sc_zero]
  have hL_nonneg : 0 ≤ L := by rw [hL_eq]; exact abs_nonneg _
  -- A base point `a` of the half interval, with no reflection fixed point strictly inside it
  obtain ⟨a, haP⟩ : ∃ a : ℝ, ∀ h ∈ D, IsRefl h →
      Phi h 0 ≤ 2 * a ∨ 2 * a + L ≤ Phi h 0 := by
    by_cases hex : ∃ h ∈ D, IsRefl h
    · obtain ⟨r, hrD, hrrefl⟩ := hex
      refine ⟨Phi r 0 / 2, ?_⟩
      intro h hhD hhrefl
      by_cases hhr : h = r
      · refine Or.inl ?_
        rw [hhr]
        exact le_of_eq (by ring)
      · have hkinv : IsRefl r⁻¹ := IsRefl.inv hA' hrrefl
        have hkform : ∀ x : ℝ, Phi (h * r⁻¹) x = Phi h 0 - Phi r 0 + x := by
          intro x
          rw [IsRefl.mul hA' hhrefl hkinv x, IsRefl.inv_zero hA' hrrefl]
        have hk0 : Phi (h * r⁻¹) 0 = Phi h 0 - Phi r 0 := by
          simpa using hkform 0
        have hkne : Phi (h * r⁻¹) 0 ≠ 0 := by
          intro h0
          have hz : Phi h 0 - Phi r 0 = 0 := by rw [← hk0]; exact h0
          have h1 : h * r⁻¹ = 1 := (Phi_eq_one_iff hA' hI' _).mp (by
            intro x
            rw [hkform x, hz, zero_add])
          exact hhr (mul_inv_eq_one.mp h1)
        have hfpf : ∀ x : E 1, (h * r⁻¹) • x ≠ x := by
          intro x hx
          have h2 : sc x = Phi (h * r⁻¹) (sc x) := by
            have h2' := sc_smul (h * r⁻¹) x
            rw [hx] at h2'
            exact h2'
          rw [hkform (sc x)] at h2
          refine hkne ?_
          rw [hk0]
          linarith
        have hkD : h * r⁻¹ ∈ D := D.mul_mem hhD (D.inv_mem hrD)
        have hbnd := hmin (h * r⁻¹) hkD hfpf
        have hbnd' : L ≤ |Phi h 0 - Phi r 0| := by
          have h1 : hdist (0 : E 1) ((h * r⁻¹) • (0 : E 1)) = |Phi (h * r⁻¹) 0| := by
            rw [hdist_zero_eq_sc, sc_smul, sc_zero]
          rw [h1, hk0] at hbnd
          exact hbnd
        have h2 : 2 * (Phi r 0 / 2) = Phi r 0 := by ring
        by_cases hpos : 0 ≤ Phi h 0 - Phi r 0
        · refine Or.inr ?_
          have hge : L ≤ Phi h 0 - Phi r 0 := by rwa [abs_of_nonneg hpos] at hbnd'
          linarith
        · refine Or.inl ?_
          have hneg : Phi h 0 - Phi r 0 < 0 := lt_of_not_ge hpos
          have hle : L ≤ -(Phi h 0 - Phi r 0) := by rwa [abs_of_neg hneg] at hbnd'
          linarith
    · exact ⟨0, fun h hhD hhrefl => absurd ⟨h, hhD, hhrefl⟩ hex⟩
  set b : ℝ := a + L / 2 with hb
  have hb_le : a ≤ b := by rw [hb]; linarith
  set A : Set (E 1) := isc a b with hAdef
  have hAmeas : NullMeasurableSet A (volH 1) := by
    rw [hAdef]
    exact (measurableSet_isc a b).nullMeasurableSet
  have hAvol : volH 1 A = ENNReal.ofReal (L / 2) := by
    rw [hAdef, volH_isc a b hb_le, hb]
    congr 1
    ring
  have hnullpt : volH 1 {w : E 1 | sc w = a} = 0 := volH_sc_singleton hI' a
  have hdisj : ∀ γ : D, γ ≠ 1 → AEDisjoint (volH 1)
      ((fun x : E 1 => (γ : PO 1 1) • x) '' A) A := by
    intro γ hγne
    show volH 1 (((fun x : E 1 => (γ : PO 1 1) • x) '' A) ∩ A) = 0
    have hsub : ((fun x : E 1 => (γ : PO 1 1) • x) '' A) ∩ A ⊆ {w : E 1 | sc w = a} := by
      rintro w ⟨hw1, hw2⟩
      show sc w = a
      rw [hAdef] at hw1 hw2
      rcases hw1 with ⟨u, huA, huw⟩
      have hsu : sc u ∈ Set.Ico a b := (mem_isc a b u).mp huA
      have hsw : sc w ∈ Set.Ico a b := (mem_isc a b w).mp hw2
      have huw' : (γ : PO 1 1) • u = w := huw
      have hsw' : sc w = Phi (γ : PO 1 1) (sc u) := by
        have h3 : sc ((γ : PO 1 1) • u) = Phi (γ : PO 1 1) (sc u) := sc_smul (γ : PO 1 1) u
        rw [huw'] at h3
        exact h3
      rw [hb] at hsu hsw
      rcases Phi_form' hI' (γ : PO 1 1) with htr | href
      · exfalso
        have hd0 : Phi (γ : PO 1 1) 0 ≠ 0 := by
          intro h0
          have hγ1 : (γ : PO 1 1) = 1 :=
            (Phi_eq_one_iff hA' hI' _).mp (by intro x; rw [htr x, h0, zero_add])
          exact hγne (Subtype.ext hγ1)
        have hfpf : ∀ x : E 1, (γ : PO 1 1) • x ≠ x := by
          intro x hx
          have h2 : sc x = Phi (γ : PO 1 1) (sc x) := by
            have h2' := sc_smul (γ : PO 1 1) x
            rw [hx] at h2'
            exact h2'
          rw [htr (sc x)] at h2
          exact hd0 (by linarith)
        have hbnd := hmin (γ : PO 1 1) γ.2 hfpf
        have hbnd' : L ≤ |Phi (γ : PO 1 1) 0| := by
          have h1 : hdist (0 : E 1) ((γ : PO 1 1) • (0 : E 1)) = |Phi (γ : PO 1 1) 0| := by
            rw [hdist_zero_eq_sc, sc_smul, sc_zero]
          rw [h1] at hbnd
          exact hbnd
        have hEq : Phi (γ : PO 1 1) 0 = sc w - sc u := by
          rw [hsw', htr (sc u)]; ring
        have hsu1 : a ≤ sc u := hsu.1
        have hsu2 : sc u < a + L / 2 := hsu.2
        have hsw1 : a ≤ sc w := hsw.1
        have hsw2 : sc w < a + L / 2 := hsw.2
        have hlt : |sc w - sc u| < L / 2 := by
          rw [abs_lt]
          constructor <;> linarith
        rw [hEq] at hbnd'
        linarith
      · have haPγ := haP (γ : PO 1 1) γ.2 href
        have hsu1 : a ≤ sc u := hsu.1
        have hsu2 : sc u < a + L / 2 := hsu.2
        have hsw1 : a ≤ sc w := hsw.1
        have hsw2 : sc w < a + L / 2 := hsw.2
        have hd_eq : Phi (γ : PO 1 1) 0 = sc u + sc w := by
          have h := href (sc u)
          rw [← hsw'] at h
          linarith
        have hlo : 2 * a ≤ Phi (γ : PO 1 1) 0 := by rw [hd_eq]; linarith
        have hhi : Phi (γ : PO 1 1) 0 < 2 * a + L := by rw [hd_eq]; linarith
        rcases haPγ with h | h
        · have hEq2 : sc u + sc w = 2 * a := by rw [← hd_eq]; linarith
          linarith
        · linarith
    exact measure_mono_null hsub hnullpt
  have hpack := volH_le_fundamentalDomain (n := 1) hI hdisc (Γ := D) (D := DY) (A := A)
    hFD hAmeas hdisj
  calc ENNReal.ofReal (hdist (0 : E 1) (g₀ • (0 : E 1)))
      = ENNReal.ofReal L := by rw [← hL]
    _ = 2 * ENNReal.ofReal (L / 2) := by
        calc ENNReal.ofReal L = ENNReal.ofReal (2 * (L / 2)) := by
              congr 1; ring
          _ = ENNReal.ofReal 2 * ENNReal.ofReal (L / 2) := ENNReal.ofReal_mul (by norm_num)
          _ = 2 * ENNReal.ofReal (L / 2) := by norm_num
    _ = 2 * volH 1 A := by rw [hAvol]
    _ ≤ 2 * volH 1 DY := mul_le_mul_of_nonneg_left hpack (by norm_num)

end Work.Mostow
