/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotC2

# The local ring at the point at infinity: setup

This file sets up the vocabulary needed to prove `Work.MotC2.InfPlace`: the subalgebra
`infPlace E ⊆ L(E)` is the localization of the chart-at-infinity coordinate ring
`infCoordRing E = L[1/x, y/x²]` at the maximal ideal `(1/x, y/x²)`.

## Main results

* `Work.MotC2.infIdealR`: the ideal `⟨1/x, y/x²⟩` of the chart ring `infCoordRing E`, and
  `Work.MotC2.mem_infIdealR_iff` relating it to the submodule `infIdeal E`.
* `Work.MotC2.infPlace_mem_iff`: the membership description of `infPlace E` as fractions `r / g`
  with `g ∉ ⟨1/x, y/x²⟩`.
* `Work.MotC2.instIsLocalizationInfPlace`: `↥(infPlace E)` is the localization of `infCoordRing E`
  at that maximal ideal.

## Tags

elliptic curve, function field, local ring, place
-/

import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.recip_poly_degree_le
import Submission.Work.MotC2.exists_aeval_add_mul_infW
import Submission.Work.MotC2.algebraMap_smul_eq_aeval
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- The proofs below (in particular the localization instance) need more than the default number
-- of kernel heartbeats, exactly as in `AffPlaceSetup`.
set_option maxHeartbeats 4000000

open Polynomial WeierstrassCurve.Affine

namespace Work.MotC2.PoleAux

variable {L : Type*} [Field L]

/-! ## The ideal `⟨1/x, y/x²⟩` -/

lemma infU_mem_infCoordRing (E : WeierstrassCurve L) : infU E ∈ infCoordRing E :=
  Algebra.subset_adjoin (by simp)

lemma infW_mem_infCoordRing (E : WeierstrassCurve L) : infW E ∈ infCoordRing E :=
  Algebra.subset_adjoin (by simp)

/-- The maximal ideal `⟨u, w⟩ = ⟨1/x, y/x²⟩` of the chart-at-infinity coordinate ring
`infCoordRing E`, as an ideal of the ring itself. -/
noncomputable def infIdealR (E : WeierstrassCurve L) : Ideal (infCoordRing E) :=
  Ideal.span {⟨infU E, infU_mem_infCoordRing E⟩, ⟨infW E, infW_mem_infCoordRing E⟩}

lemma infIdealR_eq_span (E : WeierstrassCurve L) :
    infIdealR E = Ideal.span {⟨infU E, infU_mem_infCoordRing E⟩,
      ⟨infW E, infW_mem_infCoordRing E⟩} := rfl

/-- Membership in the ideal `⟨u, w⟩` of the chart ring, in terms of generators. -/
lemma mem_infIdealR_iff' (E : WeierstrassCurve L) (r : infCoordRing E) :
    r ∈ infIdealR E ↔ ∃ a b : infCoordRing E,
      a * ⟨infU E, infU_mem_infCoordRing E⟩ + b * ⟨infW E, infW_mem_infCoordRing E⟩ = r := by
  rw [infIdealR_eq_span, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, by simpa using h⟩
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, by simpa using h⟩

/-- The submodule `infIdeal E ⊆ L(E)` and the ideal `infIdealR E` of the chart ring have the same
elements, under the coercion `infCoordRing E → L(E)`. -/
lemma mem_infIdealR_iff (E : WeierstrassCurve L) (r : infCoordRing E) :
    (r : Func E) ∈ infIdeal E ↔ r ∈ infIdealR E := by
  rw [mem_infIdealR_iff', infIdeal, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨a, b, ?_⟩
    apply Subtype.ext
    simpa [Algebra.smul_def] using hab
  · rintro ⟨a, b, hab⟩
    refine ⟨a, b, ?_⟩
    have h := congrArg (fun y : infCoordRing E => (y : Func E)) hab
    simpa [Algebra.smul_def] using h

/-! ## Membership in `infPlace E` -/

lemma mem_infPlace_of_mem (E : WeierstrassCurve L) (r : infCoordRing E) :
    (r : Func E) ∈ infPlace E :=
  Algebra.subset_adjoin (Or.inl r.2)

lemma inv_mem_infPlace_of_notMem (E : WeierstrassCurve L) {r : infCoordRing E}
    (hr : r ∉ infIdealR E) :
    ((r : Func E))⁻¹ ∈ infPlace E :=
  Algebra.subset_adjoin (Or.inr ⟨(r : Func E), ⟨r.2, fun h => hr ((mem_infIdealR_iff E r).mp h)⟩,
    rfl⟩)

/-! ## The ideal is proper: the point at infinity is a genuine point

We prove `1 ∉ ⟨u, w⟩` by a degree argument.  Suppose `a u + b w = 1` with `a, b` in the chart ring.
Write `a = A₀(u) + A₁(u) w` and `b = B₀(u) + B₁(u) w` (`exists_aeval_add_mul_infW`) and let `m` be
the largest degree occurring.  Multiplying the relation `a u + b w = 1` by `x ^ (m+4)` and using
`recip_poly_degree_le` to clear the negative powers of `x`, one gets an identity

`x ^ (m+4) = P₀(x) + (P₁(x) + Q₀(x))·y + Q₁(x)·y²`

with `P₀, P₁, Q₀, Q₁` polynomials of degrees `≤ m+3, m+1, m+2, m`.  Since `y² = W(x) - b(x)·y` and
`{1, y}` is an `L[X]`-basis of `L[x,y]` (`CoordinateRing.smul_basis_eq_zero`), this forces

`P₀ + Q₁·W - X ^ (m+4) = 0`,

whose left hand side has degree `≤ m+3 < m+4`: a contradiction. -/

/-- The Weierstrass cubic `X³ + a₂X² + a₄X + a₆`, as a polynomial used to express `y²` in the chart
at infinity. -/
noncomputable def infY2poly (E : WeierstrassCurve L) : Polynomial L :=
  X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆

/-- The linear polynomial `a₁X + a₃` appearing in the Weierstrass relation. -/
noncomputable def infLinepoly (E : WeierstrassCurve L) : Polynomial L :=
  C E.a₁ * X + C E.a₃

lemma aeval_infY2poly (E : WeierstrassCurve L) :
    aeval (genX E) (infY2poly E) = (genX E) ^ 3 + algebraMap L (Func E) E.a₂ * (genX E) ^ 2 +
      algebraMap L (Func E) E.a₄ * genX E + algebraMap L (Func E) E.a₆ := by
  simp [infY2poly]

lemma aeval_infLinepoly (E : WeierstrassCurve L) :
    aeval (genX E) (infLinepoly E) =
      algebraMap L (Func E) E.a₁ * genX E + algebraMap L (Func E) E.a₃ := by
  simp [infLinepoly]

/-- The Weierstrass relation in the chart at infinity, solved for `y²`. -/
lemma genY_sq_eq_aeval (E : WeierstrassCurve L) :
    (genY E) ^ 2 = aeval (genX E) (infY2poly E) - aeval (genX E) (infLinepoly E) * genY E := by
  have h := genY_sq_relation E
  rw [aeval_infY2poly, aeval_infLinepoly]
  linear_combination (norm := refl_ring1) h

lemma natDegree_infY2poly_le (E : WeierstrassCurve L) : (infY2poly E).natDegree ≤ 3 := by
  have h : infY2poly E = (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆ : Polynomial L) := by
    rw [infY2poly]
  rw [h]
  compute_degree!

/-- **The ideal `⟨1/x, y/x²⟩` of the chart ring is proper.**  Equivalently, the point at infinity
`O` is a genuine point of `E`: there is no relation `1 = 0` at `O`. -/
theorem one_notMem_infIdealR (E : WeierstrassCurve L) : (1 : infCoordRing E) ∉ infIdealR E := by
  intro hmem
  rw [mem_infIdealR_iff'] at hmem
  obtain ⟨a, b, hab⟩ := hmem
  -- the same relation in the function field
  have hK : (a : Func E) * infU E + (b : Func E) * infW E = 1 := by
    have h := congrArg (fun y : infCoordRing E => (y : Func E)) hab
    simpa using h
  have hx : genX E ≠ 0 := genX_ne_zero E
  -- reduce `a` and `b` to the normal form `A(u) + B(u) w`
  obtain ⟨A₀, A₁, ha⟩ := exists_aeval_add_mul_infW L E a
  obtain ⟨B₀, B₁, hb⟩ := exists_aeval_add_mul_infW L E b
  -- the degree bound
  set m : ℕ := max (max A₀.natDegree A₁.natDegree) (max B₀.natDegree B₁.natDegree) with hm
  have hmA₀ : A₀.natDegree ≤ m := by
    rw [hm]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hmA₁ : A₁.natDegree ≤ m := by
    rw [hm]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hmB₀ : B₀.natDegree ≤ m := by
    rw [hm]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hmB₁ : B₁.natDegree ≤ m := by
    rw [hm]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨P₀, hP₀deg, hP₀⟩ :=
    recip_poly_degree_le (genX E) (genX_ne_zero E) A₀ (m + 3) (by omega)
  obtain ⟨P₁, hP₁deg, hP₁⟩ :=
    recip_poly_degree_le (genX E) (genX_ne_zero E) A₁ (m + 1) (by omega)
  obtain ⟨Q₀, hQ₀deg, hQ₀⟩ :=
    recip_poly_degree_le (genX E) (genX_ne_zero E) B₀ (m + 2) (by omega)
  obtain ⟨Q₁, hQ₁deg, hQ₁⟩ :=
    recip_poly_degree_le (genX E) (genX_ne_zero E) B₁ m (by omega)
  -- the key identity
  have key' : (genX E) ^ (m + 4) * ((a : Func E) * infU E + (b : Func E) * infW E) =
      aeval (genX E) P₀ + aeval (genX E) P₁ * genY E + aeval (genX E) Q₀ * genY E +
        aeval (genX E) Q₁ * (genY E) ^ 2 := by
    rw [hP₀, hP₁, hQ₀, hQ₁, ha, hb]
    simp only [infU, infW]
    field_simp
    ring_nf
  have key : (genX E) ^ (m + 4) =
      aeval (genX E) P₀ + aeval (genX E) P₁ * genY E + aeval (genX E) Q₀ * genY E +
        aeval (genX E) Q₁ * (genY E) ^ 2 := by
    rw [← key', hK, mul_one]
  -- assemble the identity with the two polynomials `D` and `E`
  have key2 : aeval (genX E) (P₀ + Q₁ * infY2poly E - X ^ (m + 4)) +
      aeval (genX E) (P₁ + Q₀ - Q₁ * infLinepoly E) * genY E = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_infY2poly, aeval_infLinepoly,
      key, genY_sq_eq_aeval E]
    refl_ring1
  -- transfer to the affine coordinate ring and use the basis `{1, y}`
  obtain ⟨hD1, hD2⟩ := algebraMap_smul_eq_aeval L E (P₀ + Q₁ * infY2poly E - X ^ (m + 4))
  obtain ⟨hE1, hE2⟩ := algebraMap_smul_eq_aeval L E (P₁ + Q₀ - Q₁ * infLinepoly E)
  have hzero : (P₀ + Q₁ * infY2poly E - X ^ (m + 4)) • (1 : Coord E) +
      (P₁ + Q₀ - Q₁ * infLinepoly E) • (CoordinateRing.mk E X) = 0 := by
    apply IsFractionRing.injective (Coord E) (Func E)
    rw [map_add, hD1, hE2, map_zero, key2]
  obtain ⟨hD0, -⟩ := CoordinateRing.smul_basis_eq_zero hzero
  -- degree contradiction
  have hX : (X ^ (m + 4) : Polynomial L) = P₀ + Q₁ * infY2poly E :=
    (sub_eq_zero.mp hD0).symm
  have hdeg : (X ^ (m + 4) : Polynomial L).natDegree ≤ m + 3 := by
    rw [hX]
    refine le_trans (natDegree_add_le _ _) (max_le hP₀deg ?_)
    refine le_trans (natDegree_mul_le) ?_
    have := natDegree_infY2poly_le E
    omega
  rw [natDegree_X_pow] at hdeg
  omega

/-! ## The quotient of the chart ring by the maximal ideal is `L` -/

/-- Every element of the chart ring is a constant plus an element of the maximal ideal `⟨u, w⟩`. -/
theorem exists_algebraMap_sub_mem_infIdealR (E : WeierstrassCurve L) (x : infCoordRing E) :
    ∃ c : L, x - algebraMap L (infCoordRing E) c ∈ infIdealR E := by
  have key : ∀ y ∈ (Algebra.adjoin L ({infU E, infW E} : Set (Func E))),
      ∃ c : L, y - algebraMap L (Func E) c ∈ infIdeal E := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem z hz =>
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · refine ⟨0, ?_⟩
          rw [map_zero, sub_zero]
          exact Submodule.subset_span (Set.mem_insert (infU E) {infW E})
        · refine ⟨0, ?_⟩
          rw [map_zero, sub_zero]
          exact Submodule.subset_span (Set.mem_insert_of_mem (infU E) rfl)
    | algebraMap c => exact ⟨c, by rw [sub_self]; exact (infIdeal E).zero_mem⟩
    | add x y hx hy ihx ihy =>
        obtain ⟨c₁, h₁⟩ := ihx
        obtain ⟨c₂, h₂⟩ := ihy
        refine ⟨c₁ + c₂, ?_⟩
        rw [map_add]
        have : x + y - (algebraMap L (Func E) c₁ + algebraMap L (Func E) c₂) =
            (x - algebraMap L (Func E) c₁) + (y - algebraMap L (Func E) c₂) := by ring
        rw [this]
        exact (infIdeal E).add_mem h₁ h₂
    | mul x y hx hy ihx ihy =>
        obtain ⟨c₁, h₁⟩ := ihx
        obtain ⟨c₂, h₂⟩ := ihy
        refine ⟨c₁ * c₂, ?_⟩
        rw [map_mul]
        have hyle : y ∈ (infCoordRing E : Set (Func E)) := hy
        have hxle : x ∈ (infCoordRing E : Set (Func E)) := hx
        have hs₁ : (x - algebraMap L (Func E) c₁) * y ∈ infIdeal E := by
          have := Submodule.smul_mem (infIdeal E) (⟨y, hyle⟩ : infCoordRing E) h₁
          simpa [Algebra.smul_def, mul_comm] using this
        have hs₂ : algebraMap L (Func E) c₁ * (y - algebraMap L (Func E) c₂) ∈ infIdeal E := by
          have := Submodule.smul_mem (infIdeal E)
            (⟨algebraMap L (Func E) c₁,
              (infCoordRing E).algebraMap_mem c₁⟩ : infCoordRing E) h₂
          simpa [Algebra.smul_def] using this
        have : x * y - algebraMap L (Func E) c₁ * algebraMap L (Func E) c₂ =
            (x - algebraMap L (Func E) c₁) * y +
              algebraMap L (Func E) c₁ * (y - algebraMap L (Func E) c₂) := by ring
        rw [this]
        exact (infIdeal E).add_mem hs₁ hs₂
  obtain ⟨c, hc⟩ := key x.1 x.2
  refine ⟨c, (mem_infIdealR_iff E (x - algebraMap L (infCoordRing E) c)).mp ?_⟩
  simpa using hc

/-- The ideal `⟨u, w⟩` of the chart ring is maximal. -/
theorem isMaximal_infIdealR (E : WeierstrassCurve L) : (infIdealR E).IsMaximal := by
  refine Ideal.isMaximal_iff.mpr ⟨one_notMem_infIdealR E, ?_⟩
  intro J x hle hxI hxJ
  obtain ⟨c, hc⟩ := exists_algebraMap_sub_mem_infIdealR E x
  have hcne : c ≠ 0 := by
    intro h0
    rw [h0, map_zero, sub_zero] at hc
    exact hxI hc
  have hab : algebraMap L (infCoordRing E) c⁻¹ * algebraMap L (infCoordRing E) c = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hcne, map_one]
  have h1 : (1 : infCoordRing E) = algebraMap L (infCoordRing E) c⁻¹ * x -
      algebraMap L (infCoordRing E) c⁻¹ * (x - algebraMap L (infCoordRing E) c) := by
    rw [mul_sub, hab]
    refl_ring1
  rw [h1]
  exact J.sub_mem (J.mul_mem_left _ hxJ) (J.mul_mem_left _ (hle hc))

instance instIsPrimeInfIdealR (E : WeierstrassCurve L) : (infIdealR E).IsPrime :=
  (isMaximal_infIdealR E).isPrime

/-! ## The membership description of `infPlace E` -/

/-- The elements of `infPlace E` are exactly the fractions `a / b` with `a, b` in the chart ring and
`b` outside the maximal ideal `⟨u, w⟩`. -/
theorem infPlace_mem_iff (E : WeierstrassCurve L) (f : Func E) :
    f ∈ infPlace E ↔ ∃ a b : infCoordRing E, b ∉ infIdealR E ∧ f * (b : Func E) = (a : Func E) := by
  have h1I : (1 : infCoordRing E) ∉ infIdealR E := one_notMem_infIdealR E
  have hprime : (infIdealR E).IsPrime := instIsPrimeInfIdealR E
  constructor
  · intro hf
    have key : ∀ x ∈ (Algebra.adjoin L ((infCoordRing E : Set (Func E)) ∪
        ((fun r : Func E => r⁻¹) '' {r : Func E | r ∈ infCoordRing E ∧ r ∉ infIdeal E}))),
        ∃ a b : infCoordRing E, b ∉ infIdealR E ∧ x * (b : Func E) = (a : Func E) := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem y hy =>
          rcases hy with hy | ⟨r, ⟨hr, hrn⟩, rfl⟩
          · exact ⟨⟨y, hy⟩, 1, h1I, by rw [Subalgebra.coe_one, mul_one]⟩
          · refine ⟨1, ⟨r, hr⟩, fun h => hrn ((mem_infIdealR_iff E ⟨r, hr⟩).mpr h), ?_⟩
            rw [Subalgebra.coe_one]
            have hr0 : (r : Func E) ≠ 0 := fun h0 => hrn (by
              show (r : Func E) ∈ infIdeal E
              rw [h0]
              exact Submodule.zero_mem _)
            exact inv_mul_cancel₀ hr0
      | algebraMap c =>
          exact ⟨algebraMap L (infCoordRing E) c, 1, h1I, by
            rw [Subalgebra.coe_one, mul_one]
            exact (IsScalarTower.algebraMap_apply L (infCoordRing E) (Func E) c).symm⟩
      | add x y hx hy ihx ihy =>
          obtain ⟨a₁, b₁, hb₁, h₁⟩ := ihx
          obtain ⟨a₂, b₂, hb₂, h₂⟩ := ihy
          refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, ?_, ?_⟩
          · intro hcon
            rcases hprime.mem_or_mem hcon with hc | hc
            · exact hb₁ hc
            · exact hb₂ hc
          · rw [Subalgebra.coe_mul, Subalgebra.coe_add]
            calc (x + y) * ((b₁ : Func E) * (b₂ : Func E))
                = x * (b₁ : Func E) * (b₂ : Func E) + y * (b₂ : Func E) * (b₁ : Func E) := by
                  refl_ring1
              _ = (a₁ : Func E) * (b₂ : Func E) + (a₂ : Func E) * (b₁ : Func E) := by rw [h₁, h₂]
              _ = ((a₁ * b₂ + a₂ * b₁ : infCoordRing E) : Func E) := by
                  rw [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_mul]
      | mul x y hx hy ihx ihy =>
          obtain ⟨a₁, b₁, hb₁, h₁⟩ := ihx
          obtain ⟨a₂, b₂, hb₂, h₂⟩ := ihy
          refine ⟨a₁ * a₂, b₁ * b₂, ?_, ?_⟩
          · intro hcon
            rcases hprime.mem_or_mem hcon with hc | hc
            · exact hb₁ hc
            · exact hb₂ hc
          · rw [Subalgebra.coe_mul, Subalgebra.coe_mul]
            calc (x * y) * ((b₁ : Func E) * (b₂ : Func E))
                = (x * (b₁ : Func E)) * (y * (b₂ : Func E)) := by ring
              _ = (a₁ : Func E) * (a₂ : Func E) := by rw [h₁, h₂]
              _ = ((a₁ * a₂ : infCoordRing E) : Func E) := by rw [Subalgebra.coe_mul]
    exact key f (by simpa [infPlace] using hf)
  · rintro ⟨a, b, hb, hab⟩
    have hb0 : (b : Func E) ≠ 0 := by
      intro h0
      exact hb ((mem_infIdealR_iff E b).mp (by rw [h0]; exact Submodule.zero_mem _))
    have hf : f = (a : Func E) * ((b : Func E))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hb0, hab]
    rw [hf]
    exact mul_mem (mem_infPlace_of_mem E a) (inv_mem_infPlace_of_notMem E hb)

/-! ## `infPlace E` is the localization of the chart ring at the maximal ideal -/

/-- The `L`-algebra map `L[1/x, y/x²] → ↥(infPlace E)`. -/
noncomputable def infPlaceAlgHom (E : WeierstrassCurve L) :
    infCoordRing E →ₐ[L] ↥(infPlace E) :=
  (IsScalarTower.toAlgHom L (infCoordRing E) (Func E)).codRestrict (infPlace E)
    fun r => mem_infPlace_of_mem E r

/-- The canonical `infCoordRing E`-algebra structure on `↥(infPlace E)`. -/
noncomputable instance instAlgebraInfPlace (E : WeierstrassCurve L) :
    Algebra (infCoordRing E) ↥(infPlace E) :=
  (infPlaceAlgHom E).toRingHom.toAlgebra

lemma infPlace_algebraMap_val (E : WeierstrassCurve L) (r : infCoordRing E) :
    ((algebraMap (infCoordRing E) ↥(infPlace E)) r : Func E) = (r : Func E) := by
  change ((IsScalarTower.toAlgHom L (infCoordRing E) (Func E)) r) = (r : Func E)
  rw [IsScalarTower.toAlgHom_apply]
  exact Subalgebra.algebraMap_apply (infCoordRing E) r

/-- `↥(infPlace E)` is the localization of the chart ring `infCoordRing E` at the maximal ideal
`⟨1/x, y/x²⟩`. -/
noncomputable instance instIsLocalizationInfPlace (E : WeierstrassCurve L) :
    IsLocalization.AtPrime ↥(infPlace E) (infIdealR E) where
  map_units := fun y => by
    obtain ⟨r, hr⟩ := y
    have hmem : ((r : Func E))⁻¹ ∈ infPlace E := inv_mem_infPlace_of_notMem E hr
    refine isUnit_iff_exists_inv.mpr ⟨⟨(r : Func E)⁻¹, hmem⟩, ?_⟩
    apply Subtype.ext
    change (r : Func E) * (r : Func E)⁻¹ = 1
    have hr0 : (r : Func E) ≠ 0 := fun h0 =>
      hr ((mem_infIdealR_iff E r).mp (by
        show (r : Func E) ∈ infIdeal E
        rw [h0]
        exact Submodule.zero_mem _))
    rw [mul_inv_cancel₀ hr0]
  surj := fun z => by
    obtain ⟨a, b, hb, hh⟩ := (infPlace_mem_iff E z.1).mp z.2
    refine ⟨(a, ⟨b, hb⟩), ?_⟩
    apply Subtype.ext
    change (z : Func E) * (b : Func E) = (a : Func E)
    exact hh
  exists_of_eq := fun {x y} hxy => by
    refine ⟨1, ?_⟩
    have hval : (x : Func E) = (y : Func E) := by
      have h := congrArg (fun w : ↥(infPlace E) => (w : Func E)) hxy
      simpa [infPlace_algebraMap_val] using h
    show (1 : infCoordRing E) * x = (1 : infCoordRing E) * y
    rw [one_mul, one_mul]
    exact Subtype.ext hval

end Work.MotC2.PoleAux
