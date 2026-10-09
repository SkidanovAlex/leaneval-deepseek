import Mathlib
import Submission.Work.SSGRoute.PT.ClassFormation
import Submission.Work.SSGRoute.PT.shapiro_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open scoped Classical

namespace Work.SSGRoute.PT

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (U : Subgroup G) [U.FiniteIndex]
variable {M : Type*} [AddCommGroup M] [DistribMulAction U M]

/-- `f x = coord x • f (secC (xU))` for `f` in the coinduced module. -/
theorem Coind.apply_eq (f : Coind G U M) (x : G) :
    f x = coord U x • f (secC U (x : G ⧸ U)) := by
  conv_lhs => rw [← show secC U (x : G ⧸ U) * (((coord U x)⁻¹ : U) : G) = x from by
    rw [Subgroup.coe_inv, coe_coord]
    group]
  rw [Coind.coe_mul]
  simp

/-- The explicit primitive of a `2`-cocycle `c` on `G` with values in `Coind^G_U M` whose
restriction to `U` is the coboundary of `b`. -/
def h2Primitive (b : U → M) (c : G × G → Coind G U M) : G → Coind G U M :=
  fun g => ⟨fun x =>
      coord U x • b (Shapiro.A 0 G U g (x : G ⧸ U))
      - (c (secC U (x : G ⧸ U), (Shapiro.A 0 G U g (x : G ⧸ U) : G)) : G → M) x
      + (c (g, secC U (g⁻¹ • (x : G ⧸ U))) : G → M) x, by
    intro x u
    have hc : (((x * (u : G) : G)) : G ⧸ U) = (x : G ⧸ U) := coset_mul U x u
    show coord U (x * (u : G)) • b (Shapiro.A 0 G U g (((x * (u : G) : G)) : G ⧸ U))
        - (c (secC U (((x * (u : G) : G)) : G ⧸ U),
              (Shapiro.A 0 G U g (((x * (u : G) : G)) : G ⧸ U) : G)) : G → M) (x * (u : G))
        + (c (g, secC U (g⁻¹ • (((x * (u : G) : G)) : G ⧸ U))) : G → M) (x * (u : G))
      = u⁻¹ • (coord U x • b (Shapiro.A 0 G U g (x : G ⧸ U))
        - (c (secC U (x : G ⧸ U), (Shapiro.A 0 G U g (x : G ⧸ U) : G)) : G → M) x
        + (c (g, secC U (g⁻¹ • (x : G ⧸ U))) : G → M) x)
    rw [hc, coord_mul U x u, Coind.coe_mul, Coind.coe_mul, mul_smul, ← smul_sub, ← smul_add]⟩

@[simp] theorem h2Primitive_apply (b : U → M) (c : G × G → Coind G U M) (g x : G) :
    (h2Primitive U b c g) x
      = coord U x • b (Shapiro.A 0 G U g (x : G ⧸ U))
        - (c (secC U (x : G ⧸ U), (Shapiro.A 0 G U g (x : G ⧸ U) : G)) : G → M) x
        + (c (g, secC U (g⁻¹ • (x : G ⧸ U))) : G → M) x := rfl

/-- The correction cochain `s_1 c` of the Shapiro homotopy. -/
def s1 (c : G × G → Coind G U M) : G → Coind G U M :=
  fun g => ⟨fun x =>
      - (c (secC U (x : G ⧸ U), (Shapiro.A 0 G U g (x : G ⧸ U) : G)) : G → M) x
      + (c (g, secC U (g⁻¹ • (x : G ⧸ U))) : G → M) x, by
    intro x u
    have hc : (((x * (u : G) : G)) : G ⧸ U) = (x : G ⧸ U) := coset_mul U x u
    show - (c (secC U (((x * (u : G) : G)) : G ⧸ U),
            (Shapiro.A 0 G U g (((x * (u : G) : G)) : G ⧸ U) : G)) : G → M) (x * (u : G))
        + (c (g, secC U (g⁻¹ • (((x * (u : G) : G)) : G ⧸ U))) : G → M) (x * (u : G))
      = u⁻¹ • (- (c (secC U (x : G ⧸ U),
            (Shapiro.A 0 G U g (x : G ⧸ U) : G)) : G → M) x
        + (c (g, secC U (g⁻¹ • (x : G ⧸ U))) : G → M) x)
    rw [hc, Coind.coe_mul, Coind.coe_mul, ← smul_neg, ← smul_add]⟩

@[simp] theorem s1_apply (c : G × G → Coind G U M) (g x : G) :
    (s1 U c g) x
      = - (c (secC U (x : G ⧸ U), (Shapiro.A 0 G U g (x : G ⧸ U) : G)) : G → M) x
        + (c (g, secC U (g⁻¹ • (x : G ⧸ U))) : G → M) x := rfl

/-- `h2Primitive` splits as the Shapiro lift of `b` plus the correction `s1`. -/
theorem h2Primitive_eq (b : U → M) (c : G × G → Coind G U M) :
    h2Primitive U b c = coindCocycle U b + s1 U c := by
  funext g
  apply Subtype.ext
  funext x
  simp only [h2Primitive_apply, s1_apply, coindCocycle_apply, AddSubgroup.coe_add, Pi.add_apply]
  abel

/-- The cocycle condition for `c`, evaluated at a point of `G`. -/
theorem Z2_eval {c : G × G → Coind G U M} (hc : c ∈ Work.AbsoluteKummer.Z2 G (Coind G U M))
    (g h k z : G) :
    (c (g * h, k) : G → M) z + (c (g, h) : G → M) z
      = (c (h, k) : G → M) (g⁻¹ * z) + (c (g, h * k) : G → M) z := by
  have h := ((Work.AbsoluteKummer.mem_Z2_iff c).mp hc).1 g h k
  have h2 := congrArg (fun f : Coind G U M => f z) h
  simpa [AddSubgroup.coe_add, Pi.add_apply, Coind.smul_apply] using h2

/-- The Shapiro lift `coindCocycle U φ` is a chain map. -/
theorem coindCocycle_d1_apply (φ : U → M) (g h x : G) :
    (Work.GroupCohomology.d1 G (Coind G U M) (coindCocycle U φ) (g, h) : G → M) x
      = coord U x • (Work.GroupCohomology.d1 U M φ
          (Shapiro.A 0 G U g (x : G ⧸ U), Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)))) := by
  simp only [Work.GroupCohomology.d1_apply, Coind.smul_apply, coindCocycle_apply,
    AddSubgroup.coe_add, AddSubgroup.coe_sub, Pi.add_apply, Pi.sub_apply,
    coset_smul, coord_smul, A_mul', mul_smul, smul_sub, smul_add]



/-- The correction cochain `s1` satisfies the Shapiro homotopy identity in degree `2`. -/
theorem s1_d1_apply {c : G × G → Coind G U M}
    (hc : c ∈ Work.AbsoluteKummer.Z2 G (Coind G U M)) (g h x : G) :
    (Work.GroupCohomology.d1 G (Coind G U M) (s1 U c) (g, h) : G → M) x
      = (c (g, h) : G → M) x
        - coord U x • ((c (Shapiro.A 0 G U g (x : G ⧸ U),
            Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U))) : G → M) 1) := by
  have hsec : h * secC U (h⁻¹ • g⁻¹ • (x : G ⧸ U)) = secC U (g⁻¹ • (x : G ⧸ U)) * (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G) := secC_mul_A U h (g⁻¹ • (x : G ⧸ U))
  have hsm : secC U (x : G ⧸ U) * (Shapiro.A 0 G U g (x : G ⧸ U) : G) = g * secC U (g⁻¹ • (x : G ⧸ U)) := (secC_mul_A U g (x : G ⧸ U)).symm
  have keyA := Z2_eval U hc g h (secC U (h⁻¹ • g⁻¹ • (x : G ⧸ U))) x
  rw [hsec] at keyA
  have HB : (c (h, secC U (h⁻¹ • g⁻¹ • (x : G ⧸ U))) : G → M) (g⁻¹ * x) = (c (g * h, secC U (h⁻¹ • g⁻¹ • (x : G ⧸ U))) : G → M) x + (c (g, h) : G → M) x - (c (g, secC U (g⁻¹ • (x : G ⧸ U)) * (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G)) : G → M) x := by
    have h2 : (c (g * h, secC U (h⁻¹ • g⁻¹ • (x : G ⧸ U))) : G → M) x + (c (g, h) : G → M) x - (c (g, secC U (g⁻¹ • (x : G ⧸ U)) * (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G)) : G → M) x = (c (h, secC U (h⁻¹ • g⁻¹ • (x : G ⧸ U))) : G → M) (g⁻¹ * x) := by rw [keyA]; abel
    exact h2.symm
  have keyB := Z2_eval U hc (secC U (x : G ⧸ U)) (Shapiro.A 0 G U g (x : G ⧸ U) : G) (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G) (secC U (x : G ⧸ U))
  rw [inv_mul_cancel, ← Subgroup.coe_mul] at keyB
  have HC : (c (secC U (x : G ⧸ U), ((Shapiro.A 0 G U g (x : G ⧸ U) * Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : U) : G)) : G → M) x = (c (secC U (x : G ⧸ U), (Shapiro.A 0 G U g (x : G ⧸ U) : G)) : G → M) x + (c (g * secC U (g⁻¹ • (x : G ⧸ U)), (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G)) : G → M) x - coord U x • ((c (Shapiro.A 0 G U g (x : G ⧸ U), Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U))) : G → M) 1) := by
    have h1 : (c (secC U (x : G ⧸ U), ((Shapiro.A 0 G U g (x : G ⧸ U) * Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : U) : G)) : G → M) (secC U (x : G ⧸ U))
        = (c (secC U (x : G ⧸ U) * (Shapiro.A 0 G U g (x : G ⧸ U) : G), (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G)) : G → M) (secC U (x : G ⧸ U)) + (c (secC U (x : G ⧸ U), (Shapiro.A 0 G U g (x : G ⧸ U) : G)) : G → M) (secC U (x : G ⧸ U)) - (c (Shapiro.A 0 G U g (x : G ⧸ U), Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U))) : G → M) 1 := by
      have h2 : (c (secC U (x : G ⧸ U) * (Shapiro.A 0 G U g (x : G ⧸ U) : G), (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G)) : G → M) (secC U (x : G ⧸ U)) + (c (secC U (x : G ⧸ U), (Shapiro.A 0 G U g (x : G ⧸ U) : G)) : G → M) (secC U (x : G ⧸ U)) - (c (Shapiro.A 0 G U g (x : G ⧸ U), Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U))) : G → M) 1 = (c (secC U (x : G ⧸ U), ((Shapiro.A 0 G U g (x : G ⧸ U) * Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : U) : G)) : G → M) (secC U (x : G ⧸ U)) := by rw [keyB]; abel
      exact h2.symm
    have h3 : coord U x • ((c (secC U (x : G ⧸ U), ((Shapiro.A 0 G U g (x : G ⧸ U) * Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : U) : G)) : G → M) (secC U (x : G ⧸ U)))
        = coord U x • ((c (secC U (x : G ⧸ U) * (Shapiro.A 0 G U g (x : G ⧸ U) : G), (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G)) : G → M) (secC U (x : G ⧸ U))) + coord U x • ((c (secC U (x : G ⧸ U), (Shapiro.A 0 G U g (x : G ⧸ U) : G)) : G → M) (secC U (x : G ⧸ U))) - coord U x • ((c (Shapiro.A 0 G U g (x : G ⧸ U), Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U))) : G → M) 1) := by
      rw [h1]
      simp only [smul_add, smul_sub]
    rw [← Coind.apply_eq, ← Coind.apply_eq, ← Coind.apply_eq] at h3
    rw [hsm] at h3
    rw [h3]
    abel
  have keyC := Z2_eval U hc g (secC U (g⁻¹ • (x : G ⧸ U))) (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G) x
  have HD : (c (g * secC U (g⁻¹ • (x : G ⧸ U)), (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G)) : G → M) x = (c (secC U (g⁻¹ • (x : G ⧸ U)), (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G)) : G → M) (g⁻¹ * x) + (c (g, secC U (g⁻¹ • (x : G ⧸ U)) * (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G)) : G → M) x - (c (g, secC U (g⁻¹ • (x : G ⧸ U))) : G → M) x := by
    have h2 : (c (secC U (g⁻¹ • (x : G ⧸ U)), (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G)) : G → M) (g⁻¹ * x) + (c (g, secC U (g⁻¹ • (x : G ⧸ U)) * (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G)) : G → M) x - (c (g, secC U (g⁻¹ • (x : G ⧸ U))) : G → M) x = (c (g * secC U (g⁻¹ • (x : G ⧸ U)), (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G)) : G → M) x := by rw [← keyC]; abel
    exact h2.symm
  simp only [Work.GroupCohomology.d1_apply, Coind.smul_apply, s1_apply, AddSubgroup.coe_add,
    AddSubgroup.coe_sub, Pi.add_apply, Pi.sub_apply, coset_smul, A_mul', mul_smul, mul_inv_rev]
  rw [HB, HC, HD]
  abel

/-- Evaluation of `d1 (h2Primitive b c)` at a pair `(g,h)` and a point `x`. -/
theorem h2Primitive_d1 {b : U → M} {c : G × G → Coind G U M}
    (hc : c ∈ Work.AbsoluteKummer.Z2 G (Coind G U M))
    (hb : ∀ u v : U, Work.GroupCohomology.d1 U M b (u, v) = (c ((u : G), (v : G)) : G → M) 1) :
    Work.GroupCohomology.d1 G (Coind G U M) (h2Primitive U b c) = c := by
  funext p
  obtain ⟨g, h⟩ := p
  apply Subtype.ext
  funext x
  rw [h2Primitive_eq U b c, map_add]
  show (Work.GroupCohomology.d1 G (Coind G U M) (coindCocycle U b) (g, h) : G → M) x
      + (Work.GroupCohomology.d1 G (Coind G U M) (s1 U c) (g, h) : G → M) x
      = (c (g, h) : G → M) x
  rw [coindCocycle_d1_apply, s1_d1_apply U hc, hb]
  abel

/-- The `H`-coordinate of `g * u` at a coset `C` when `u` fixes `g⁻¹ • C`. -/
lemma A_mul_of_fix (g u : G) (C : G ⧸ U)
    (hfix : u⁻¹ • (g⁻¹ • C) = g⁻¹ • C) :
    (Shapiro.A 0 G U (g * u) C : G)
      = (Shapiro.A 0 G U g C : G)
        * ((secC U (g⁻¹ • C))⁻¹ * u * secC U (g⁻¹ • C)) := by
  have h1 : (g * u)⁻¹ • C = g⁻¹ • C := by rw [mul_inv_rev, mul_smul]; exact hfix
  simp only [Shapiro.coe_A, h1, secC]
  group

/-- The coset `D` is fixed by `u⁻¹` exactly when the `U`-coordinate `(secC U D)⁻¹ * u * secC U D`
lies in `U`. -/
lemma coset_fix_iff {u : G} {D : G ⧸ U} :
    u⁻¹ • D = D ↔ (secC U D)⁻¹ * u * secC U D ∈ U := by
  constructor
  · intro h
    have step : u⁻¹ • ((secC U D : G) : G ⧸ U) = ((secC U D : G) : G ⧸ U) := by
      rw [secC_mk U D]; exact h
    rw [MulAction.Quotient.smul_coe U u⁻¹ (secC U D), smul_eq_mul] at step
    rw [coset_eq_iff U (u⁻¹ * secC U D) (secC U D)] at step
    rwa [show (u⁻¹ * secC U D)⁻¹ * secC U D
        = (secC U D)⁻¹ * u * secC U D from by group] at step
  · intro h
    have step : ((u⁻¹ * secC U D : G) : G ⧸ U) = ((secC U D : G) : G ⧸ U) := by
      rw [coset_eq_iff U (u⁻¹ * secC U D) (secC U D)]
      rwa [show (u⁻¹ * secC U D)⁻¹ * secC U D
        = (secC U D)⁻¹ * u * secC U D from by group]
    rw [← secC_mk U D, MulAction.Quotient.smul_coe U u⁻¹ (secC U D), smul_eq_mul]
    exact step

/-- A coinduced cochain with locally constant coefficients is locally constant. -/
theorem h2Primitive_isLocallyConstant {b : U → M} {c : G × G → Coind G U M}
    (hU : IsOpen (U : Set G))
    (hb : Work.AbsoluteKummer.IsLocallyConstant b)
    (hc : Work.AbsoluteKummer.IsLocallyConstant c) :
    Work.AbsoluteKummer.IsLocallyConstant (h2Primitive U b c) := by
  classical
  haveI hfin : Fintype (G ⧸ U) := Fintype.ofFinite _
  intro g
  -- ### 1.  the coset-stabiliser condition
  have hfix : ∀ u : G, (∀ D : G ⧸ U, (secC U D)⁻¹ * u * (secC U D) ∈ U) →
      ∀ D : G ⧸ U, u⁻¹ • D = D := by
    intro u hu D
    exact (coset_fix_iff (u := u) (D := D)).mpr (hu D)
  -- ### 2.  choice data
  set AD : G ⧸ U → U := fun D => Shapiro.A 0 G U g (g • D) with hAD
  have hΩ : ∀ D : G ⧸ U, ∃ Ω : Set G, IsOpen Ω ∧ (AD D : G) ∈ Ω ∧
      ∀ z : U, (z : G) ∈ Ω → b z = b (AD D) := by
    intro D
    obtain ⟨Ω, hΩo, hAΩ, hconst⟩ := hb (AD D)
    obtain ⟨Ω', hΩ'o, hΩ'eq⟩ := isOpen_induced_iff.mp hΩo
    refine ⟨Ω', hΩ'o, ?_, ?_⟩
    · have h : (AD D) ∈ Subtype.val ⁻¹' Ω' := by rw [hΩ'eq]; exact hAΩ
      simpa using h
    · intro z hz
      exact hconst z (by rw [← hΩ'eq]; exact hz)
  choose Ω hΩo hΩmem hΩc using hΩ
  have hΞ : ∀ D : G ⧸ U, ∃ Ξ : Set (G × G), IsOpen Ξ ∧
      ((secC U (g • D), (AD D : G)) : G × G) ∈ Ξ ∧
      ∀ z ∈ Ξ, c z = c (secC U (g • D), (AD D : G)) := by
    intro D
    obtain ⟨Ξ, hΞo, hΞmem, hΞc⟩ := hc ((secC U (g • D), (AD D : G)) : G × G)
    exact ⟨Ξ, hΞo, hΞmem, hΞc⟩
  choose Ξ hΞo hΞmem hΞc using hΞ
  have hΥ : ∀ D : G ⧸ U, ∃ Υ : Set (G × G), IsOpen Υ ∧
      ((g, secC U D) : G × G) ∈ Υ ∧ ∀ z ∈ Υ, c z = c (g, secC U D) := by
    intro D
    obtain ⟨Υ, hΥo, hΥmem, hΥc⟩ := hc ((g, secC U D) : G × G)
    exact ⟨Υ, hΥo, hΥmem, hΥc⟩
  choose Υ hΥo hΥmem hΥc using hΥ
  -- ### 3.  the neighbourhood
  set W : Set G := ⋂ D : G ⧸ U, {u : G |
      (secC U D)⁻¹ * u * (secC U D) ∈ U ∧
      (AD D : G) * ((secC U D)⁻¹ * u * (secC U D)) ∈ Ω D ∧
      ((secC U (g • D), (AD D : G) * ((secC U D)⁻¹ * u * (secC U D))) : G × G) ∈ Ξ D ∧
      ((g * u, secC U D) : G × G) ∈ Υ D} with hW
  have hWopen : IsOpen W := by
    rw [hW]
    refine isOpen_iInter_of_finite fun D => ?_
    rw [Set.ofPred_and, Set.ofPred_and, Set.ofPred_and]
    have h1 : IsOpen {u : G | (secC U D)⁻¹ * u * (secC U D) ∈ U} :=
      hU.preimage (by continuity)
    have h2 : IsOpen {u : G | (AD D : G) * ((secC U D)⁻¹ * u * (secC U D)) ∈ Ω D} :=
      (hΩo D).preimage (by continuity)
    have h3 : IsOpen {u : G |
        ((secC U (g • D), (AD D : G) * ((secC U D)⁻¹ * u * (secC U D))) : G × G) ∈ Ξ D} :=
      (hΞo D).preimage (by continuity)
    have h4 : IsOpen {u : G | ((g * u, secC U D) : G × G) ∈ Υ D} :=
      (hΥo D).preimage (by continuity)
    exact h1.inter (h2.inter (h3.inter h4))
  have hWmem : (1 : G) ∈ W := by
    rw [hW, Set.mem_iInter]
    intro D
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (secC U D)⁻¹ * 1 * secC U D ∈ U
      simp
    · show (AD D : G) * ((secC U D)⁻¹ * 1 * (secC U D)) ∈ Ω D
      simpa using hΩmem D
    · show ((secC U (g • D), (AD D : G) * ((secC U D)⁻¹ * 1 * (secC U D))) : G × G) ∈ Ξ D
      simpa using hΞmem D
    · show ((g * 1, secC U D) : G × G) ∈ Υ D
      simpa using hΥmem D
  -- ### 4.  the main computation
  have hmain : ∀ u ∈ W, h2Primitive U b c (g * u) = h2Primitive U b c g := by
    intro u hu
    have hWu : ∀ D : G ⧸ U,
        (secC U D)⁻¹ * u * (secC U D) ∈ U ∧
        (AD D : G) * ((secC U D)⁻¹ * u * (secC U D)) ∈ Ω D ∧
        ((secC U (g • D), (AD D : G) * ((secC U D)⁻¹ * u * (secC U D))) : G × G) ∈ Ξ D ∧
        ((g * u, secC U D) : G × G) ∈ Υ D := by
      intro D
      rw [hW] at hu
      exact Set.mem_iInter.mp hu D
    apply Subtype.ext
    funext x
    have hfixx : u⁻¹ • (g⁻¹ • (x : G ⧸ U)) = g⁻¹ • (x : G ⧸ U) :=
      hfix u (fun D => (hWu D).1) (g⁻¹ • (x : G ⧸ U))
    have hxD : g • (g⁻¹ • (x : G ⧸ U)) = (x : G ⧸ U) := smul_inv_smul g (x : G ⧸ U)
    have hADx : AD (g⁻¹ • (x : G ⧸ U)) = Shapiro.A 0 G U g (x : G ⧸ U) := by
      show Shapiro.A 0 G U g (g • (g⁻¹ • (x : G ⧸ U))) = Shapiro.A 0 G U g (x : G ⧸ U)
      rw [hxD]
    have hAx : (Shapiro.A 0 G U (g * u) (x : G ⧸ U) : G)
        = (AD (g⁻¹ • (x : G ⧸ U)) : G)
          * ((secC U (g⁻¹ • (x : G ⧸ U)))⁻¹ * u * secC U (g⁻¹ • (x : G ⧸ U))) := by
      rw [A_mul_of_fix U g u (x : G ⧸ U) hfixx, ← hADx]
    have hb_eq : b (Shapiro.A 0 G U (g * u) (x : G ⧸ U))
        = b (Shapiro.A 0 G U g (x : G ⧸ U)) := by
      calc b (Shapiro.A 0 G U (g * u) (x : G ⧸ U))
          = b (AD (g⁻¹ • (x : G ⧸ U))) := hΩc _ _ (by rw [hAx]; exact (hWu _).2.1)
        _ = b (Shapiro.A 0 G U g (x : G ⧸ U)) :=
            (hΩc _ _ (by rw [← hADx]; exact hΩmem _)).symm
    have hc1_eq : c (secC U (x : G ⧸ U), (Shapiro.A 0 G U (g * u) (x : G ⧸ U) : G))
        = c (secC U (x : G ⧸ U), (Shapiro.A 0 G U g (x : G ⧸ U) : G)) := by
      have hsec : secC U (g • (g⁻¹ • (x : G ⧸ U))) = secC U (x : G ⧸ U) := by rw [hxD]
      calc c (secC U (x : G ⧸ U), (Shapiro.A 0 G U (g * u) (x : G ⧸ U) : G))
          = c (secC U (g • (g⁻¹ • (x : G ⧸ U))),
              (AD (g⁻¹ • (x : G ⧸ U)) : G)
                * ((secC U (g⁻¹ • (x : G ⧸ U)))⁻¹ * u
                    * secC U (g⁻¹ • (x : G ⧸ U)))) := by
            rw [hsec, hAx]
        _ = c (secC U (g • (g⁻¹ • (x : G ⧸ U))), (AD (g⁻¹ • (x : G ⧸ U)) : G)) :=
            hΞc _ _ (hWu _).2.2.1
        _ = c (secC U (x : G ⧸ U), (Shapiro.A 0 G U g (x : G ⧸ U) : G)) := by
            rw [hsec, hADx]
    have hc2_eq : c (g * u, secC U ((g * u)⁻¹ • (x : G ⧸ U)))
        = c (g, secC U (g⁻¹ • (x : G ⧸ U))) := by
      have hsec : (g * u)⁻¹ • (x : G ⧸ U) = g⁻¹ • (x : G ⧸ U) := by
        rw [mul_inv_rev, mul_smul]; exact hfixx
      rw [hsec]
      exact hΥc _ _ (hWu _).2.2.2
    simp only [h2Primitive_apply]
    rw [hb_eq, hc1_eq, hc2_eq]
  -- ### 5.  assemble
  refine ⟨{g' : G | g⁻¹ * g' ∈ W}, ?_, ?_, ?_⟩
  · exact hWopen.preimage (by continuity)
  · show g⁻¹ * g ∈ W
    rw [inv_mul_cancel]
    exact hWmem
  · intro g' hg'
    show h2Primitive U b c g' = h2Primitive U b c g
    have : g' = g * (g⁻¹ * g') := by group
    rw [this]
    exact hmain (g⁻¹ * g') hg'

/-- **Shapiro's lemma, injectivity of the restriction map in degree two.** -/
theorem shapiro_H2_inj {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type*} [AddCommGroup M] [DistribMulAction U M]
    (c : G × G → Work.SSGRoute.PT.Coind G U M)
    (hc : c ∈ Work.AbsoluteKummer.Z2 G (Work.SSGRoute.PT.Coind G U M))
    (hb : ∃ b ∈ Work.AbsoluteKummer.C1c U M,
        Work.GroupCohomology.d1 U M b = fun p : U × U => c ((p.1 : G), (p.2 : G)) 1) :
    ∃ B ∈ Work.AbsoluteKummer.C1c G (Work.SSGRoute.PT.Coind G U M),
      Work.GroupCohomology.d1 G (Work.SSGRoute.PT.Coind G U M) B = c := by
  obtain ⟨b, hbC1c, hbeq⟩ := hb
  have hblc : Work.AbsoluteKummer.IsLocallyConstant b := hbC1c
  have hclc : Work.AbsoluteKummer.IsLocallyConstant c :=
    ((Work.AbsoluteKummer.mem_Z2_iff c).mp hc).2
  exact ⟨h2Primitive U b c, h2Primitive_isLocallyConstant U hU hblc hclc,
    h2Primitive_d1 U hc (fun u v => by simpa using congrFun hbeq (u, v))⟩

end
end Work.SSGRoute.PT
