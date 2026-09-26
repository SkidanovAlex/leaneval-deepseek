import Mathlib
import Submission.Work.SurgeryInvariance.All
import Submission.Work.CoreTopology.Winding

/-!
# The parameter plane of a parametrised torus

The winding vector of a closed curve of a parametrised torus `P` is read off from a lift of the
curve to the parameter plane.  This file sets up the parameter plane as the complex plane `ℂ` and
records the elementary dictionary between the torus and the plane:

* `planePsi P : ℂ → R3` is the parametrisation, read as a map of the plane;
* `periodPt a b = 2π (a + b i)` is the lattice element of the plane;
* `Xtilde P X = planePsi P ⁻¹' X` is the preimage of a subset of `ℝ³`;
* the lattice periodicity of `planePsi` and the resulting invariance of the preimages.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-! ## The parametrisation as a map of the plane -/

/-- The parametrisation of a parametrised torus, read as a map of the complex plane. -/
def planePsi (P : Work.CoreTopology.ParamTorus) : ℂ → R3 := fun z => P.psi z.re z.im

@[simp] theorem planePsi_apply (P : Work.CoreTopology.ParamTorus) (z : ℂ) :
    planePsi P z = P.psi z.re z.im := rfl

theorem continuous_planePsi (P : Work.CoreTopology.ParamTorus) : Continuous (planePsi P) :=
  P.cont.comp (Complex.continuous_re.prodMk Complex.continuous_im)

theorem planePsi_mem_carrier (P : Work.CoreTopology.ParamTorus) (z : ℂ) :
    planePsi P z ∈ P.carrier := P.psi_mem_carrier z.re z.im

/-- The lattice element `2π (a + b i)` of the parameter plane. -/
def periodPt (a b : ℤ) : ℂ :=
  (((a : ℝ) * (2 * Real.pi) : ℝ) : ℂ) + (((b : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I

@[simp] theorem periodPt_re (a b : ℤ) : (periodPt a b).re = (a : ℝ) * (2 * Real.pi) := by
  simp [periodPt]

@[simp] theorem periodPt_im (a b : ℤ) : (periodPt a b).im = (b : ℝ) * (2 * Real.pi) := by
  simp [periodPt]

theorem periodPt_zero : periodPt 0 0 = 0 := by
  apply Complex.ext <;> simp

theorem periodPt_ne_zero {a b : ℤ} (h : (a, b) ≠ (0, 0)) : periodPt a b ≠ 0 := by
  intro hz
  have h1 : (a : ℝ) * (2 * Real.pi) = 0 := by
    have := congrArg Complex.re hz; simpa using this
  have h2 : (b : ℝ) * (2 * Real.pi) = 0 := by
    have := congrArg Complex.im hz; simpa using this
  have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have ha : (a : ℝ) = 0 := (mul_eq_zero.mp h1).resolve_right hπ
  have hb : (b : ℝ) = 0 := (mul_eq_zero.mp h2).resolve_right hπ
  exact h (Prod.ext (by exact_mod_cast ha) (by exact_mod_cast hb))

/-! ## Periodicity -/

theorem psi_add_int_mul_two_pi_left (P : Work.CoreTopology.ParamTorus) (x y : ℝ) (a : ℤ) :
    P.psi (x + (a : ℝ) * (2 * Real.pi)) y = P.psi x y := by
  have hp : Function.Periodic (fun z : ℝ => P.psi z y) (2 * Real.pi) := fun z => P.per_left z y
  have h := hp.int_mul a x
  simpa [zsmul_eq_mul] using h

theorem psi_add_int_mul_two_pi_right (P : Work.CoreTopology.ParamTorus) (x y : ℝ) (b : ℤ) :
    P.psi x (y + (b : ℝ) * (2 * Real.pi)) = P.psi x y := by
  have hp : Function.Periodic (fun z : ℝ => P.psi x z) (2 * Real.pi) := fun z => P.per_right x z
  have h := hp.int_mul b y
  simpa [zsmul_eq_mul] using h

/-- **The parameter plane is periodic for the lattice `2π(ℤ + iℤ)`.** -/
theorem planePsi_add_periodPt (P : Work.CoreTopology.ParamTorus) (z : ℂ) (a b : ℤ) :
    planePsi P (z + periodPt a b) = planePsi P z := by
  have hre : (z + periodPt a b).re = z.re + (a : ℝ) * (2 * Real.pi) := by
    simp
  have him : (z + periodPt a b).im = z.im + (b : ℝ) * (2 * Real.pi) := by
    simp
  rw [planePsi_apply, planePsi_apply, hre, him,
    psi_add_int_mul_two_pi_left, psi_add_int_mul_two_pi_right]

/-- The lattice of the parameter plane. -/
def periodLattice : Set ℂ := Set.range (fun p : ℤ × ℤ => periodPt p.1 p.2)

theorem mem_periodLattice (z : ℂ) :
    z ∈ periodLattice ↔ ∃ a b : ℤ, periodPt a b = z := by
  constructor
  · rintro ⟨p, rfl⟩; exact ⟨p.1, p.2, rfl⟩
  · rintro ⟨a, b, rfl⟩; exact ⟨(a, b), rfl⟩

/-- **Finitely many lattice points lie in a ball.** -/
theorem finite_periodLattice_ball (R : ℝ) :
    {z ∈ periodLattice | ‖z‖ ≤ R}.Finite := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  set N : ℤ := (Nat.ceil (R / (2 * Real.pi) + 1) : ℤ) with hN
  have hNge : R / (2 * Real.pi) + 1 ≤ (N : ℝ) := by
    have h := Nat.le_ceil (R / (2 * Real.pi) + 1)
    simpa [hN] using h
  have hbase : {p : ℤ × ℤ | ‖periodPt p.1 p.2‖ ≤ R}.Finite := by
    have hcoord : ∀ p : ℤ × ℤ, ‖periodPt p.1 p.2‖ ≤ R →
        |(p.1 : ℝ)| ≤ (N : ℝ) ∧ |(p.2 : ℝ)| ≤ (N : ℝ) := by
      intro p hp
      have hle : ∀ x : ℝ, |x| * (2 * Real.pi) ≤ R → |x| ≤ (N : ℝ) := by
        intro x hx
        have h1 : |x| ≤ R / (2 * Real.pi) := (le_div_iff₀ hπ).mpr (by linarith)
        linarith
      constructor
      · refine hle _ ?_
        have h1 : |(periodPt p.1 p.2).re| ≤ ‖periodPt p.1 p.2‖ := Complex.abs_re_le_norm _
        rw [periodPt_re] at h1
        calc |(p.1 : ℝ)| * (2 * Real.pi) = |(p.1 : ℝ) * (2 * Real.pi)| := by
              rw [abs_mul, abs_of_pos hπ]
          _ ≤ R := le_trans h1 hp
      · refine hle _ ?_
        have h1 : |(periodPt p.1 p.2).im| ≤ ‖periodPt p.1 p.2‖ := Complex.abs_im_le_norm _
        rw [periodPt_im] at h1
        calc |(p.2 : ℝ)| * (2 * Real.pi) = |(p.2 : ℝ) * (2 * Real.pi)| := by
              rw [abs_mul, abs_of_pos hπ]
          _ ≤ R := le_trans h1 hp
    have hset : {p : ℤ × ℤ | ‖periodPt p.1 p.2‖ ≤ R} ⊆
        ((Finset.Icc (-N) N : Finset ℤ) : Set ℤ) ×ˢ ((Finset.Icc (-N) N : Finset ℤ) : Set ℤ) := by
      intro p hp
      obtain ⟨h1, h2⟩ := hcoord p hp
      have hb : ∀ a : ℤ, |(a : ℝ)| ≤ (N : ℝ) → a ∈ Finset.Icc (-N) N := by
        intro a ha
        rw [Finset.mem_Icc]
        constructor
        · have := (abs_le.mp ha).1
          exact_mod_cast this
        · have := (abs_le.mp ha).2
          exact_mod_cast this
      exact ⟨hb _ h1, hb _ h2⟩
    exact ((Finset.Icc (-N) N).finite_toSet.prod (Finset.Icc (-N) N).finite_toSet).subset hset
  -- transport along `periodPt`
  have hinj : Set.InjOn (fun p : ℤ × ℤ => periodPt p.1 p.2)
      {p : ℤ × ℤ | ‖periodPt p.1 p.2‖ ≤ R} := by
    intro p _ q _ hpq
    have h1 := congrArg Complex.re hpq
    have h2 := congrArg Complex.im hpq
    simp only [periodPt_re] at h1
    simp only [periodPt_im] at h2
    have hπ' : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have h1' : (p.1 : ℝ) = (q.1 : ℝ) := mul_right_cancel₀ hπ' h1
    have h2' : (p.2 : ℝ) = (q.2 : ℝ) := mul_right_cancel₀ hπ' h2
    exact Prod.ext (by exact_mod_cast h1') (by exact_mod_cast h2')
  have himg : (fun p : ℤ × ℤ => periodPt p.1 p.2) '' {p : ℤ × ℤ | ‖periodPt p.1 p.2‖ ≤ R}
      = {z ∈ periodLattice | ‖z‖ ≤ R} := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, rfl⟩, hp⟩
    · rintro ⟨⟨p, rfl⟩, hz⟩
      exact ⟨p, hz, rfl⟩
  rw [← himg]
  exact hbase.image _

/-! ## Preimages of subsets of `ℝ³` -/

/-- The preimage in the parameter plane of a subset of `ℝ³`. -/
def Xtilde (P : Work.CoreTopology.ParamTorus) (X : Set R3) : Set ℂ := planePsi P ⁻¹' X

@[simp] theorem mem_Xtilde (P : Work.CoreTopology.ParamTorus) (X : Set R3) (z : ℂ) :
    z ∈ Xtilde P X ↔ planePsi P z ∈ X := Iff.rfl

theorem Xtilde_mono (P : Work.CoreTopology.ParamTorus) {X Y : Set R3} (h : X ⊆ Y) :
    Xtilde P X ⊆ Xtilde P Y := fun _ hz => h hz

theorem Xtilde_add_periodPt (P : Work.CoreTopology.ParamTorus) (X : Set R3) (z : ℂ)
    (a b : ℤ) : z + periodPt a b ∈ Xtilde P X ↔ z ∈ Xtilde P X := by
  show planePsi P (z + periodPt a b) ∈ X ↔ planePsi P z ∈ X
  rw [planePsi_add_periodPt]

theorem Xtilde_add_periodLattice (P : Work.CoreTopology.ParamTorus) (X : Set R3) (z w : ℂ)
    (hw : w ∈ periodLattice) : z + w ∈ Xtilde P X ↔ z ∈ Xtilde P X := by
  rw [mem_periodLattice] at hw
  obtain ⟨a, b, rfl⟩ := hw
  exact Xtilde_add_periodPt P X z a b

theorem planePsi_add_periodLattice (P : Work.CoreTopology.ParamTorus) (z w : ℂ)
    (hw : w ∈ periodLattice) : planePsi P (z + w) = planePsi P z := by
  rw [mem_periodLattice] at hw
  obtain ⟨a, b, rfl⟩ := hw
  exact planePsi_add_periodPt P z a b

/-- **The preimage in the parameter plane of a set which is open in the carrier is open.**
`X` is open for the subspace topology of the carrier, and the carrier is precisely the image of
`planePsi`, so `planePsi ⁻¹' X` is the preimage of an honest open set of `ℝ³`. -/
theorem isOpen_Xtilde {P : Work.CoreTopology.ParamTorus} {X : Set R3}
    (hXc : X ⊆ P.carrier) (hX : Work.SurgeryInvariance.IsOpenInCarrier P X) :
    IsOpen (Xtilde P X) := by
  rw [Work.SurgeryInvariance.IsOpenInCarrier] at hX
  obtain ⟨U, hU, hUX⟩ := isOpen_induced_iff.mp hX
  have hXeq : X = U ∩ P.carrier := by
    apply Subset.antisymm
    · intro x hx
      refine ⟨?_, hXc hx⟩
      have h1 : (⟨x, hXc hx⟩ : P.carrier) ∈ Subtype.val ⁻¹' U := by
        rw [hUX]; exact hx
      exact h1
    · rintro x ⟨hxU, hxc⟩
      have h1 : (⟨x, hxc⟩ : P.carrier) ∈ Subtype.val ⁻¹' X := by
        rw [← hUX]; exact hxU
      exact h1
  have hEq : Xtilde P X = planePsi P ⁻¹' U := by
    ext z
    constructor
    · intro hz
      have h1 : planePsi P z ∈ X := hz
      rw [hXeq] at h1
      exact h1.1
    · intro hz
      have h1 : planePsi P z ∈ U ∩ P.carrier := ⟨hz, planePsi_mem_carrier P z⟩
      have h2 : planePsi P z ∈ X := by rw [hXeq]; exact h1
      exact h2
  rw [hEq]
  exact hU.preimage (continuous_planePsi P)

/-- The image of a closed curve of the torus is compact. -/
theorem isCompact_range_closedCurve {P : Work.CoreTopology.ParamTorus}
    (c : Work.CoreTopology.ClosedCurve P) : IsCompact (Set.range c.γ) := by
  have h : Set.range c.γ = c.γ '' Set.Icc (0 : ℝ) (2 * Real.pi) := by
    refine Set.Subset.antisymm ?_ (Set.image_subset_range _ _)
    rw [Work.CoreTopology.ClosedCurve.range_eq_image P c]
    exact Set.image_mono Set.Ico_subset_Icc_self
  rw [h]
  exact isCompact_Icc.image_of_continuousOn c.cont.continuousOn

end

end Work.BoxShrink.PinchOff
