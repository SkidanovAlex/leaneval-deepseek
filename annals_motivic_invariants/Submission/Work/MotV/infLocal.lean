import Mathlib
import Submission.Work.MotV.PlaceDefs
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.InfAux
import Submission.Work.MotC2.Relations
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The orders of vanishing at the point at infinity

`Work.MotC2.infPlace E` is the local ring of the point at infinity `O` of an elliptic Weierstrass
curve `E` over a field `N`, i.e. the localization of the chart-at-infinity coordinate ring
`infCoordRing E = N[u,w]` (`u = 1/x`, `w = y/x²`) at its maximal ideal `m = (u,w)`.

The main result of this file computes the orders of vanishing of the four standard elements at `O`:

* `ord_O(x) = -2`, `ord_O(1/x) = 2`, `ord_O(y/x²) = 1`, `ord_O(y) = -3`.

The mathematical content is the pair of relations

* `w² = u·h` with `h ∈ infCoordRing E`, `h ∉ m` (so `h` is a unit of the local ring), and
* `y = w·x²` (so `y⁻¹ = w³·(h⁻¹)²`),

combined with the fact that `w` is a uniformizer: every non-unit of the local ring is a multiple
of `w`.  The latter is proved by reducing an element of the local ring to a fraction `r/g`
(`g ∉ m`), showing that it is a unit as soon as `r ∉ m`, and expanding `r` along the two
generators `u, w` of `m`.
-/

set_option maxHeartbeats 1000000

namespace Work.MotV

open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section
set_option autoImplicit false

variable {N : Type*} [Field N]

/-! ## The chart-at-infinity ring and its elements -/

/-- `1/x` as an element of the chart-at-infinity coordinate ring. -/
private def uC (E : WeierstrassCurve N) : ↥(MotC2.infCoordRing E) :=
  ⟨MotC2.infU E, MotC2.InfAux.infU_mem_infCoordRing E⟩

/-- `y/x²` as an element of the chart-at-infinity coordinate ring. -/
private def wC (E : WeierstrassCurve N) : ↥(MotC2.infCoordRing E) :=
  ⟨MotC2.infW E, MotC2.InfAux.infW_mem_infCoordRing E⟩

/-- The chart-ring element `h = 1 + a₂u + a₄u² + a₆u³ - a₁w - a₃uw` with `w² = u·h`. -/
private def hC (E : WeierstrassCurve N) : ↥(MotC2.infCoordRing E) :=
  1 + algebraMap N (↥(MotC2.infCoordRing E)) E.a₂ * uC E
    + algebraMap N (↥(MotC2.infCoordRing E)) E.a₄ * (uC E) ^ 2
    + algebraMap N (↥(MotC2.infCoordRing E)) E.a₆ * (uC E) ^ 3
    - (algebraMap N (↥(MotC2.infCoordRing E)) E.a₁ * wC E
        + algebraMap N (↥(MotC2.infCoordRing E)) E.a₃ * uC E * wC E)

@[simp] private lemma coe_uC (E : WeierstrassCurve N) :
    ((uC E : ↥(MotC2.infCoordRing E)) : MotC2.Func E) = MotC2.infU E := rfl

@[simp] private lemma coe_wC (E : WeierstrassCurve N) :
    ((wC E : ↥(MotC2.infCoordRing E)) : MotC2.Func E) = MotC2.infW E := rfl

private lemma uC_mem (E : WeierstrassCurve N) : uC E ∈ MotC2.InfAux.infIdealR E := by
  rw [MotC2.InfAux.infIdealR_eq_span]
  exact Ideal.subset_span (Set.mem_insert _ _)

private lemma wC_mem (E : WeierstrassCurve N) : wC E ∈ MotC2.InfAux.infIdealR E := by
  rw [MotC2.InfAux.infIdealR_eq_span]
  exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

private lemma coe_hC (E : WeierstrassCurve N) :
    ((hC E : ↥(MotC2.infCoordRing E)) : MotC2.Func E) =
      1 + algebraMap N (MotC2.Func E) E.a₂ * MotC2.infU E
        + algebraMap N (MotC2.Func E) E.a₄ * (MotC2.infU E) ^ 2
        + algebraMap N (MotC2.Func E) E.a₆ * (MotC2.infU E) ^ 3
        - (algebraMap N (MotC2.Func E) E.a₁ * MotC2.infW E
            + algebraMap N (MotC2.Func E) E.a₃ * MotC2.infU E * MotC2.infW E) := by
  simp only [hC, uC, wC, Subalgebra.coe_one, Subalgebra.coe_add, Subalgebra.coe_mul,
    Subalgebra.coe_pow, Subalgebra.coe_sub, Subalgebra.coe_algebraMap]

/-- `h ∉ (u,w)`: the element `h` of the relation `w² = u·h` is a unit of the local ring. -/
private lemma hC_notMem (E : WeierstrassCurve N) : hC E ∉ MotC2.InfAux.infIdealR E := by
  have hu := uC_mem E
  have hw := wC_mem E
  have hu2 : (uC E) ^ 2 ∈ MotC2.InfAux.infIdealR E := by
    rw [pow_two]; exact mul_mem hu hu
  have hu3 : (uC E) ^ 3 ∈ MotC2.InfAux.infIdealR E := by
    have h : (uC E) ^ 3 = (uC E) ^ 2 * uC E := by ring
    rw [h]; exact mul_mem hu2 hu
  have h1 : algebraMap N ↥(MotC2.infCoordRing E) E.a₂ * uC E
      + algebraMap N ↥(MotC2.infCoordRing E) E.a₄ * (uC E) ^ 2
      + algebraMap N ↥(MotC2.infCoordRing E) E.a₆ * (uC E) ^ 3 ∈
        MotC2.InfAux.infIdealR E :=
    add_mem (add_mem (Ideal.mul_mem_left _ _ hu) (Ideal.mul_mem_left _ _ hu2))
      (Ideal.mul_mem_left _ _ hu3)
  have h2 : algebraMap N ↥(MotC2.infCoordRing E) E.a₁ * wC E
      + algebraMap N ↥(MotC2.infCoordRing E) E.a₃ * uC E * wC E ∈
        MotC2.InfAux.infIdealR E :=
    add_mem (Ideal.mul_mem_left _ _ hw)
      (mul_mem (Ideal.mul_mem_left _ _ hu) hw)
  intro hmem
  have hsub : hC E - 1 ∈ MotC2.InfAux.infIdealR E := by
    have heq : hC E - 1 = (algebraMap N ↥(MotC2.infCoordRing E) E.a₂ * uC E
        + algebraMap N ↥(MotC2.infCoordRing E) E.a₄ * (uC E) ^ 2
        + algebraMap N ↥(MotC2.infCoordRing E) E.a₆ * (uC E) ^ 3)
        - (algebraMap N ↥(MotC2.infCoordRing E) E.a₁ * wC E
            + algebraMap N ↥(MotC2.infCoordRing E) E.a₃ * uC E * wC E) := by
      simp only [hC]; ring
    rw [heq]; exact sub_mem h1 h2
  have hone : (1 : ↥(MotC2.infCoordRing E)) ∈ MotC2.InfAux.infIdealR E := by
    have := sub_mem hmem hsub
    convert this using 1
    refl_ring1
  exact MotC2.InfAux.one_notMem_infIdealR E hone

private lemma hC_ne_zero (E : WeierstrassCurve N) : hC E ≠ 0 :=
  fun h => hC_notMem E (by rw [h]; exact (MotC2.InfAux.infIdealR E).zero_mem)

private lemma coe_hC_ne_zero (E : WeierstrassCurve N) :
    ((hC E : ↥(MotC2.infCoordRing E)) : MotC2.Func E) ≠ 0 :=
  fun h => hC_ne_zero E (Subtype.ext (by simpa using h))

/-- The Weierstrass relation in the chart at infinity, solved for `w² = u·h`. -/
private lemma infU_mul_hC (E : WeierstrassCurve N) :
    MotC2.infU E * ((hC E : ↥(MotC2.infCoordRing E)) : MotC2.Func E)
      = (MotC2.infW E) ^ 2 := by
  rw [coe_hC]
  have h := MotC2.infW_sq_relation E
  linear_combination (norm := refl_ring1) -h

private lemma infU_ne_zero (E : WeierstrassCurve N) : MotC2.infU E ≠ 0 := by
  rw [MotC2.infU]; exact inv_ne_zero (MotC2.genX_ne_zero E)

private lemma infW_ne_zero (E : WeierstrassCurve N) : MotC2.infW E ≠ 0 := by
  have h := infU_mul_hC E
  have hu := infU_ne_zero E
  have hh := coe_hC_ne_zero E
  intro hw
  rw [hw, pow_two, mul_zero] at h
  exact (mul_ne_zero hu hh) h

/-! ## The local ring at infinity -/

/-- `w = y/x²` as an element of the local ring at infinity. -/
private def wS (E : WeierstrassCurve N) : ↥(MotC2.infPlace E) :=
  ⟨MotC2.infW E, MotC2.InfAux.mem_infPlace_of_mem E (wC E)⟩

/-- `u = 1/x` as an element of the local ring at infinity. -/
private def uS (E : WeierstrassCurve N) : ↥(MotC2.infPlace E) :=
  ⟨MotC2.infU E, MotC2.InfAux.mem_infPlace_of_mem E (uC E)⟩

/-- `h` as an element of the local ring at infinity (a unit). -/
private def hSp (E : WeierstrassCurve N) : ↥(MotC2.infPlace E) :=
  ⟨((hC E : ↥(MotC2.infCoordRing E)) : MotC2.Func E),
    MotC2.InfAux.mem_infPlace_of_mem E (hC E)⟩

/-- `h⁻¹` as an element of the local ring at infinity. -/
private def hInvS (E : WeierstrassCurve N) : ↥(MotC2.infPlace E) :=
  ⟨(((hC E : ↥(MotC2.infCoordRing E)) : MotC2.Func E))⁻¹,
    MotC2.InfAux.inv_mem_infPlace_of_notMem E (hC_notMem E)⟩

@[simp] private lemma coe_wS (E : WeierstrassCurve N) :
    ((wS E : ↥(MotC2.infPlace E)) : MotC2.Func E) = MotC2.infW E := rfl

@[simp] private lemma coe_uS (E : WeierstrassCurve N) :
    ((uS E : ↥(MotC2.infPlace E)) : MotC2.Func E) = MotC2.infU E := rfl

private lemma infW_mem_infPlace (E : WeierstrassCurve N) :
    MotC2.infW E ∈ MotC2.infPlace E :=
  MotC2.InfAux.mem_infPlace_of_mem E (wC E)

private lemma infU_mem_infPlace (E : WeierstrassCurve N) :
    MotC2.infU E ∈ MotC2.infPlace E :=
  MotC2.InfAux.mem_infPlace_of_mem E (uC E)

private lemma hSp_mul_hInvS (E : WeierstrassCurve N) : hSp E * hInvS E = 1 := by
  have key : ((hC E : ↥(MotC2.infCoordRing E)) : MotC2.Func E)
      * (((hC E : ↥(MotC2.infCoordRing E)) : MotC2.Func E))⁻¹ = 1 :=
    mul_inv_cancel₀ (coe_hC_ne_zero E)
  exact Subtype.ext key

/-- The unit `h⁻¹` of the local ring at infinity. -/
private def hU (E : WeierstrassCurve N) : Units ↥(MotC2.infPlace E) :=
  ⟨hInvS E, hSp E, by rw [mul_comm]; exact hSp_mul_hInvS E, hSp_mul_hInvS E⟩

private lemma hInvS_unit (E : WeierstrassCurve N) : IsUnit (hInvS E) := ⟨hU E, rfl⟩

private lemma hSp_unit (E : WeierstrassCurve N) : IsUnit (hSp E) :=
  isUnit_iff_exists_inv.mpr ⟨hInvS E, hSp_mul_hInvS E⟩

/-- `u = w²·h⁻¹`. -/
private lemma uS_eq (E : WeierstrassCurve N) : uS E = hInvS E * (wS E) ^ 2 := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, Subalgebra.coe_pow]
  show MotC2.infU E =
    ((((hC E : ↥(MotC2.infCoordRing E)) : MotC2.Func E))⁻¹) * (MotC2.infW E) ^ 2
  rw [eq_inv_mul_iff_mul_eq₀ (coe_hC_ne_zero E)]
  rw [mul_comm]
  exact infU_mul_hC E

private lemma uS_eq_hU (E : WeierstrassCurve N) :
    uS E = (↑(hU E) : ↥(MotC2.infPlace E)) * (wS E) ^ 2 := uS_eq E

/-! ## The unit criterion in the local ring at infinity -/

/-- An element `x = r/g` of the local ring at infinity with `g ∉ m` is a unit as soon as
`r ∉ m`. -/
private lemma isUnit_of_notMem (E : WeierstrassCurve N)
    {x : ↥(MotC2.infPlace E)} {r g : ↥(MotC2.infCoordRing E)}
    (hxg : (x : MotC2.Func E) * (g : MotC2.Func E) = (r : MotC2.Func E))
    (hr : r ∉ MotC2.InfAux.infIdealR E) : IsUnit x := by
  have hr0 : r ≠ 0 := fun h => hr (by rw [h]; exact (MotC2.InfAux.infIdealR E).zero_mem)
  have hrK : (r : MotC2.Func E) ≠ 0 := fun h => hr0 (Subtype.ext h)
  have hinv : ((r : MotC2.Func E))⁻¹ ∈ MotC2.infPlace E :=
    MotC2.InfAux.inv_mem_infPlace_of_notMem E hr
  refine isUnit_iff_exists_inv.mpr ⟨⟨(g : MotC2.Func E) * (r : MotC2.Func E)⁻¹,
      mul_mem (MotC2.InfAux.mem_infPlace_of_mem E g) hinv⟩, ?_⟩
  apply Subtype.ext
  show (x : MotC2.Func E) * ((g : MotC2.Func E) * (r : MotC2.Func E)⁻¹) = 1
  calc (x : MotC2.Func E) * ((g : MotC2.Func E) * (r : MotC2.Func E)⁻¹)
      = ((x : MotC2.Func E) * (g : MotC2.Func E)) * (r : MotC2.Func E)⁻¹ := by ring
    _ = (r : MotC2.Func E) * (r : MotC2.Func E)⁻¹ := by rw [hxg]
    _ = 1 := mul_inv_cancel₀ hrK

/-- Conversely, if `x = r/g` (`g ∉ m`) is a unit then `r ∉ m`. -/
private lemma notMem_of_isUnit (E : WeierstrassCurve N)
    {x : ↥(MotC2.infPlace E)} {r g : ↥(MotC2.infCoordRing E)}
    (hg : g ∉ MotC2.InfAux.infIdealR E)
    (hxg : (x : MotC2.Func E) * (g : MotC2.Func E) = (r : MotC2.Func E))
    (hunit : IsUnit x) : r ∉ MotC2.InfAux.infIdealR E := by
  have hx0K : (x : MotC2.Func E) ≠ 0 := fun h0 => hunit.ne_zero (Subtype.ext h0)
  intro hr
  obtain ⟨u, hu⟩ := hunit
  have hxinv : (x : MotC2.Func E)⁻¹ ∈ MotC2.infPlace E := by
    have h2 : (((u⁻¹ : Units ↥(MotC2.infPlace E)) : ↥(MotC2.infPlace E)) : MotC2.Func E)
        = ((x : MotC2.Func E))⁻¹ := by
      rw [MotC2.subalgebra_coe_unit_inv (MotC2.infPlace E) u, hu]
    rw [← h2]
    exact (((u⁻¹ : Units ↥(MotC2.infPlace E)) : ↥(MotC2.infPlace E))).2
  obtain ⟨r', g', hg', hxg'⟩ :=
    (MotC2.InfAux.infPlace_mem_iff E ((x : MotC2.Func E)⁻¹)).mp hxinv
  have hgg' : (g : MotC2.Func E) * (g' : MotC2.Func E)
      = (r : MotC2.Func E) * (r' : MotC2.Func E) := by
    calc (g : MotC2.Func E) * (g' : MotC2.Func E)
        = ((x : MotC2.Func E)⁻¹ * (x : MotC2.Func E))
            * ((g : MotC2.Func E) * (g' : MotC2.Func E)) := by
          rw [inv_mul_cancel₀ hx0K, one_mul]
      _ = ((x : MotC2.Func E) * (g : MotC2.Func E))
            * ((x : MotC2.Func E)⁻¹ * (g' : MotC2.Func E)) := by ring
      _ = (r : MotC2.Func E) * (r' : MotC2.Func E) := by rw [hxg, hxg']
  have hgg'A : g * g' = r * r' := Subtype.ext hgg'
  have hmem : g * g' ∈ MotC2.InfAux.infIdealR E := by
    rw [hgg'A, mul_comm r r']
    exact Ideal.mul_mem_left _ _ hr
  rcases (MotC2.InfAux.instIsPrimeInfIdealR E).mem_or_mem hmem with h | h
  · exact hg h
  · exact hg' h

/-! ## `w = y/x²` is not a unit -/

private lemma not_isUnit_wS (E : WeierstrassCurve N) : ¬ IsUnit (wS E) := by
  intro hunit
  have hmem : wC E ∉ MotC2.InfAux.infIdealR E :=
    notMem_of_isUnit (E := E) (x := wS E) (r := wC E) (g := 1)
      (MotC2.InfAux.one_notMem_infIdealR E) (by simp) hunit
  exact hmem (wC_mem E)

/-! ## Every non-unit is a multiple of `w` -/

private lemma uS_mem_span (E : WeierstrassCurve N) : uS E ∈ Ideal.span {wS E} := by
  have h : (wS E) ^ 2 ∈ Ideal.span {wS E} := by
    rw [pow_two]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_right (wS E) (wS E))
  rw [uS_eq E]
  exact Ideal.mul_mem_left _ _ h

private lemma mem_span_of_not_isUnit (E : WeierstrassCurve N)
    {x : ↥(MotC2.infPlace E)} (hx : ¬ IsUnit x) : x ∈ Ideal.span {wS E} := by
  obtain ⟨r, g, hg, hxg⟩ :=
    (MotC2.InfAux.infPlace_mem_iff E (x : MotC2.Func E)).mp x.2
  have hr : r ∈ MotC2.InfAux.infIdealR E := by
    by_contra hr
    exact hx (isUnit_of_notMem E hxg hr)
  obtain ⟨a, b, hab⟩ := (MotC2.InfAux.mem_infIdealR_iff' E r).mp hr
  have hgS : IsUnit (⟨(g : MotC2.Func E), MotC2.InfAux.mem_infPlace_of_mem E g⟩ :
      ↥(MotC2.infPlace E)) :=
    isUnit_of_notMem (E := E)
      (x := ⟨(g : MotC2.Func E), MotC2.InfAux.mem_infPlace_of_mem E g⟩)
      (r := g) (g := 1) (by simp) hg
  have hxgS : x * ⟨(g : MotC2.Func E), MotC2.InfAux.mem_infPlace_of_mem E g⟩ =
      ⟨(r : MotC2.Func E), MotC2.InfAux.mem_infPlace_of_mem E r⟩ := Subtype.ext hxg
  have hrS : (⟨(r : MotC2.Func E), MotC2.InfAux.mem_infPlace_of_mem E r⟩ :
        ↥(MotC2.infPlace E)) =
      (⟨(a : MotC2.Func E), MotC2.InfAux.mem_infPlace_of_mem E a⟩ : ↥(MotC2.infPlace E))
        * uS E +
      (⟨(b : MotC2.Func E), MotC2.InfAux.mem_infPlace_of_mem E b⟩ : ↥(MotC2.infPlace E))
        * wS E := by
    apply Subtype.ext
    show (r : MotC2.Func E) =
      (a : MotC2.Func E) * MotC2.infU E + (b : MotC2.Func E) * MotC2.infW E
    have h := congrArg (fun z : ↥(MotC2.infCoordRing E) => (z : MotC2.Func E)) hab
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul] at h
    simpa only [coe_uC, coe_wC] using h.symm
  have hmem : (⟨(r : MotC2.Func E), MotC2.InfAux.mem_infPlace_of_mem E r⟩ :
      ↥(MotC2.infPlace E)) ∈ Ideal.span {wS E} := by
    rw [hrS]
    exact add_mem (Ideal.mul_mem_left _ _ (uS_mem_span E))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton (wS E))))
  have hxgS_mem : x * ⟨(g : MotC2.Func E), MotC2.InfAux.mem_infPlace_of_mem E g⟩
      ∈ Ideal.span {wS E} := by rw [hxgS]; exact hmem
  obtain ⟨gsunit, hgsunit⟩ := hgS
  have hxeq : x = (x * ⟨(g : MotC2.Func E), MotC2.InfAux.mem_infPlace_of_mem E g⟩)
      * ↑(gsunit⁻¹) := by
    rw [mul_assoc, ← hgsunit, Units.mul_inv, mul_one]
  have hfinal : (x * ⟨(g : MotC2.Func E), MotC2.InfAux.mem_infPlace_of_mem E g⟩)
      * ↑(gsunit⁻¹) ∈ Ideal.span {wS E} := by
    rw [mul_comm]
    exact Ideal.mul_mem_left _ _ hxgS_mem
  rwa [hxeq]

/-! ## `w` is irreducible -/

private lemma irreducible_wS (E : WeierstrassCurve N) : Irreducible (wS E) := by
  refine ⟨not_isUnit_wS E, ?_⟩
  intro a b hab
  by_contra hcon
  push_neg at hcon
  obtain ⟨a₁, ha₁⟩ := Ideal.mem_span_singleton.mp (mem_span_of_not_isUnit E hcon.1)
  obtain ⟨b₁, hb₁⟩ := Ideal.mem_span_singleton.mp (mem_span_of_not_isUnit E hcon.2)
  have hfac : wS E = (wS E) ^ 2 * (a₁ * b₁) := by
    conv_lhs => rw [hab]
    rw [ha₁, hb₁]
    refl_ring1
  have hK : (MotC2.infW E) = (MotC2.infW E) ^ 2 * ((a₁ * b₁ : ↥(MotC2.infPlace E)) :
      MotC2.Func E) := by
    have h := congrArg (fun z : ↥(MotC2.infPlace E) => (z : MotC2.Func E)) hfac
    simpa only [Subalgebra.coe_mul, Subalgebra.coe_pow, coe_wS] using h
  have hwne : MotC2.infW E ≠ 0 := infW_ne_zero E
  have hzero : (MotC2.infW E)
      * (1 - (MotC2.infW E) * ((a₁ * b₁ : ↥(MotC2.infPlace E)) : MotC2.Func E)) = 0 := by
    linear_combination (norm := refl_ring1) hK
  have hone : (MotC2.infW E) * ((a₁ * b₁ : ↥(MotC2.infPlace E)) : MotC2.Func E) = 1 :=
    (sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hwne)).symm
  have hunit : IsUnit (wS E) := isUnit_iff_exists_inv.mpr ⟨a₁ * b₁, by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_one, coe_wS]
    exact hone⟩
  exact not_isUnit_wS E hunit

/-! ## `x` and `y` do not lie in the local ring at infinity -/

private lemma genX_notMem (E : WeierstrassCurve N) : MotC2.genX E ∉ MotC2.infPlace E := by
  intro hx
  have h1 : (⟨MotC2.genX E, hx⟩ : ↥(MotC2.infPlace E)) * uS E = 1 := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_one, coe_uS]
    show MotC2.genX E * MotC2.infU E = 1
    rw [mul_comm]
    exact MotC2.infU_mul_genX E
  have hunit : IsUnit (uS E) :=
    isUnit_iff_exists_inv.mpr ⟨⟨MotC2.genX E, hx⟩, by rw [mul_comm]; exact h1⟩
  have hsq : uS E * hSp E = (wS E) ^ 2 := by
    rw [uS_eq E]
    calc (hInvS E * (wS E) ^ 2) * hSp E = (hInvS E * hSp E) * (wS E) ^ 2 := by ring
      _ = (wS E) ^ 2 := by
          rw [mul_comm (hInvS E) (hSp E), hSp_mul_hInvS E, one_mul]
  have h2 : IsUnit ((wS E) ^ 2) := by
    rw [← hsq]
    exact IsUnit.mul hunit (hSp_unit E)
  exact not_isUnit_wS E ((isUnit_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h2)

private lemma genY_notMem (E : WeierstrassCurve N) : MotC2.genY E ∉ MotC2.infPlace E := by
  intro hy
  have hyu : (⟨MotC2.genY E, hy⟩ : ↥(MotC2.infPlace E)) * (uS E) ^ 2 = wS E := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow, coe_uS, coe_wS]
    show MotC2.genY E * ((MotC2.genX E)⁻¹) ^ 2 = MotC2.infW E
    rw [MotC2.genY_eq_infW_mul]
    have hx0 : MotC2.genX E ≠ 0 := MotC2.genX_ne_zero E
    field_simp
  have hsq : (uS E) ^ 2 = (hInvS E) ^ 2 * (wS E) ^ 4 := by
    rw [uS_eq E]; ring
  have hw : wS E = (wS E) ^ 4 * ((⟨MotC2.genY E, hy⟩ : ↥(MotC2.infPlace E))
      * (hInvS E) ^ 2) := by
    calc wS E = (⟨MotC2.genY E, hy⟩ : ↥(MotC2.infPlace E)) * (uS E) ^ 2 := hyu.symm
      _ = (⟨MotC2.genY E, hy⟩ : ↥(MotC2.infPlace E))
            * ((hInvS E) ^ 2 * (wS E) ^ 4) := by rw [hsq]
      _ = (wS E) ^ 4 * ((⟨MotC2.genY E, hy⟩ : ↥(MotC2.infPlace E))
            * (hInvS E) ^ 2) := by ring
  have hwne : wS E ≠ 0 := fun h => infW_ne_zero E (by rw [← coe_wS E, h, Subalgebra.coe_zero])
  have hzero : wS E * (1 - (wS E) ^ 3 * ((⟨MotC2.genY E, hy⟩ : ↥(MotC2.infPlace E))
      * (hInvS E) ^ 2)) = 0 := by
    linear_combination (norm := refl_ring1) hw
  have hone : (wS E) ^ 3 * ((⟨MotC2.genY E, hy⟩ : ↥(MotC2.infPlace E)) * (hInvS E) ^ 2)
      = 1 := (sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hwne)).symm
  have h3 : IsUnit ((wS E) ^ 3) := isUnit_iff_exists_inv.mpr ⟨_, hone⟩
  exact not_isUnit_wS E ((isUnit_pow_iff (by norm_num : (3 : ℕ) ≠ 0)).mp h3)

/-! ## `y⁻¹ = w³·(h⁻¹)²` -/

private lemma genY_inv_eq (E : WeierstrassCurve N) :
    (MotC2.genY E)⁻¹ =
      ((((hC E : ↥(MotC2.infCoordRing E)) : MotC2.Func E))⁻¹) ^ 2 * (MotC2.infW E) ^ 3 := by
  have hrel := infU_mul_hC E
  have hu := infU_ne_zero E
  have hw := infW_ne_zero E
  have hh := coe_hC_ne_zero E
  have hh2 : ((hC E : ↥(MotC2.infCoordRing E)) : MotC2.Func E)
      = (MotC2.infW E) ^ 2 * (MotC2.infU E)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hu, mul_comm]
    exact hrel
  have hgen : MotC2.genY E = MotC2.infW E * ((MotC2.infU E)⁻¹) ^ 2 := by
    rw [MotC2.genY_eq_infW_mul]
    congr 1
    rw [show MotC2.genX E = (MotC2.infU E)⁻¹ from by rw [MotC2.infU, inv_inv]]
  rw [hgen, hh2]
  field_simp

private lemma genYInv_eq (E : WeierstrassCurve N)
    {h : (MotC2.genY E)⁻¹ ∈ MotC2.infPlace E} :
    (⟨(MotC2.genY E)⁻¹, h⟩ : ↥(MotC2.infPlace E)) = (hInvS E) ^ 2 * (wS E) ^ 3 := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_pow, coe_wS]
  show (MotC2.genY E)⁻¹ =
    ((((hC E : ↥(MotC2.infCoordRing E)) : MotC2.Func E))⁻¹) ^ 2 * (MotC2.infW E) ^ 3
  exact genY_inv_eq E

/-! ## Reading off `ordOfPlace` -/

private lemma ordOfPlace_eq_of (E : WeierstrassCurve N)
    (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S)
    {f : MotC2.Func E} (hf : f ∈ S) {n : ℕ}
    (h : @IsDiscreteValuationRing.addVal ↥S _ _ hS.1.choose (⟨f, hf⟩ : ↥S) = (n : ℕ∞)) :
    ordOfPlace E S hS f = n := by
  rw [ordOfPlace, dif_pos hf, h]
  exact congrArg (fun m : ℕ => (m : ℤ)) (WithTop.untopD_coe (0 : ℕ) n)

private lemma ordOfPlace_eq_neg_of (E : WeierstrassCurve N)
    (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S)
    {f : MotC2.Func E} (hf : f ∉ S) {n : ℕ}
    (h : @IsDiscreteValuationRing.addVal ↥S _ _ hS.1.choose
      (⟨f⁻¹, (MotC2.mem_or_inv_mem_of_isRatPlace hS f).resolve_left hf⟩ : ↥S) = (n : ℕ∞)) :
    ordOfPlace E S hS f = -(n : ℤ) := by
  rw [ordOfPlace, dif_neg hf, h]
  exact congrArg (fun m : ℤ => -m)
    (congrArg (fun m : ℕ => (m : ℤ)) (WithTop.untopD_coe (0 : ℕ) n))

end

/-! ## The main theorem -/

theorem infLocal {N : Type*} [Field N] (E : WeierstrassCurve N) [E.IsElliptic]
    (hInf : Work.MotC2.IsRatPlace E (Work.MotC2.infPlace E)) :
    Work.MotV.ordOfPlace E (Work.MotC2.infPlace E) hInf (Work.MotC2.genX E) = -2 ∧
    Work.MotV.ordOfPlace E (Work.MotC2.infPlace E) hInf (Work.MotC2.infU E) = 2 ∧
    Work.MotV.ordOfPlace E (Work.MotC2.infPlace E) hInf (Work.MotC2.infW E) = 1 ∧
    Work.MotV.ordOfPlace E (Work.MotC2.infPlace E) hInf (Work.MotC2.genY E) = -3 := by
  letI : IsDiscreteValuationRing ↥(MotC2.infPlace E) := hInf.1.choose
  have hπ : Irreducible (wS E) := irreducible_wS E
  have hvalW : IsDiscreteValuationRing.addVal ↥(MotC2.infPlace E) (wS E) = (1 : ℕ∞) :=
    IsDiscreteValuationRing.addVal_uniformizer hπ
  have hvalU : IsDiscreteValuationRing.addVal ↥(MotC2.infPlace E) (uS E) = (2 : ℕ∞) := by
    rw [uS_eq_hU E]
    exact IsDiscreteValuationRing.addVal_def' (hU E) hπ 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `ord_O(x) = -2`
    have hnot : MotC2.genX E ∉ MotC2.infPlace E := genX_notMem E
    have h2 : IsDiscreteValuationRing.addVal ↥(MotC2.infPlace E)
        (⟨(MotC2.genX E)⁻¹,
          (MotC2.mem_or_inv_mem_of_isRatPlace hInf (MotC2.genX E)).resolve_left hnot⟩ :
            ↥(MotC2.infPlace E)) = (2 : ℕ∞) := by
      rw [show (⟨(MotC2.genX E)⁻¹,
          (MotC2.mem_or_inv_mem_of_isRatPlace hInf (MotC2.genX E)).resolve_left hnot⟩ :
            ↥(MotC2.infPlace E)) = uS E from Subtype.ext rfl]
      exact hvalU
    exact ordOfPlace_eq_neg_of (E := E) (S := MotC2.infPlace E) (hS := hInf) hnot h2
  · -- `ord_O(1/x) = 2`
    have hin : MotC2.infU E ∈ MotC2.infPlace E := infU_mem_infPlace E
    have h2 : IsDiscreteValuationRing.addVal ↥(MotC2.infPlace E)
        (⟨MotC2.infU E, hin⟩ : ↥(MotC2.infPlace E)) = (2 : ℕ∞) := by
      rw [show (⟨MotC2.infU E, hin⟩ : ↥(MotC2.infPlace E)) = uS E from Subtype.ext rfl]
      exact hvalU
    exact ordOfPlace_eq_of (E := E) (S := MotC2.infPlace E) (hS := hInf) hin h2
  · -- `ord_O(y/x²) = 1`
    have hin : MotC2.infW E ∈ MotC2.infPlace E := infW_mem_infPlace E
    have h1 : IsDiscreteValuationRing.addVal ↥(MotC2.infPlace E)
        (⟨MotC2.infW E, hin⟩ : ↥(MotC2.infPlace E)) = (1 : ℕ∞) := by
      rw [show (⟨MotC2.infW E, hin⟩ : ↥(MotC2.infPlace E)) = wS E from Subtype.ext rfl]
      exact hvalW
    exact ordOfPlace_eq_of (E := E) (S := MotC2.infPlace E) (hS := hInf) hin h1
  · -- `ord_O(y) = -3`
    have hnot : MotC2.genY E ∉ MotC2.infPlace E := genY_notMem E
    have h3 : IsDiscreteValuationRing.addVal ↥(MotC2.infPlace E)
        (⟨(MotC2.genY E)⁻¹,
          (MotC2.mem_or_inv_mem_of_isRatPlace hInf (MotC2.genY E)).resolve_left hnot⟩ :
            ↥(MotC2.infPlace E)) = (3 : ℕ∞) := by
      rw [genYInv_eq (E := E)
        (h := (MotC2.mem_or_inv_mem_of_isRatPlace hInf (MotC2.genY E)).resolve_left hnot)]
      rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
        IsDiscreteValuationRing.addVal_eq_zero_iff.mpr (hInvS_unit E),
        Irreducible.addVal_pow hπ 3]
      simp
    exact ordOfPlace_eq_neg_of (E := E) (S := MotC2.infPlace E) (hS := hInf) hnot h3

end Work.MotV
