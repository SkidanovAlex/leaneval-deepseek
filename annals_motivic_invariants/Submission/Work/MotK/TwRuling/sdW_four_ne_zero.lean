/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.TwRuling.SdWNdeg
import Submission.Work.MotK.TwRuling.productSpan_eq
import Submission.Work.MotK.TGen.SdualTBrick
import Submission.Work.MotK.TwRule
import Submission.Work.MotK.TwDataMod5
import Submission.Work.MotK.LinkCertGen
import Submission.Work.MotK.TGen.TwCoordGKleinTw
import Submission.Work.MotK.TGen.TwBridge
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

/-!
# Non-degeneracy of the fourth ruling coordinate

The target of this file is `Work.MotK.TwRuling.sdW_four_ne_zero`: for `D : KleinData K` with
`D.Good` and `h ≠ 0`, the fourth coordinate `sdW K D h 4` of the ruling point is nonzero.

The proof has two halves.

* **The core non-degeneracy** (`SdWfour.kleinQuad_ne_zero`, §2).  For a field `R`, a Weierstrass
  curve `E` over `R`, and `κ : Fin 5 → R(E)` whose span is that of `1, x, y, x², xy` and on which
  the five Klein Pfaffians vanish, the quadratic form `2aκ₀² - bκ₁κ₄` is nonzero (`a, b ∈ R`,
  `ab ≠ 0`).  The argument is the "kernel of the multiplication map" computation: the map
  `(Fin 5 × Fin 3 → R) → R(E)`, `c ↦ ∑_q c q • κ_{pfA q} κ_{pfB q}`, over the fifteen unordered
  pairs of `Fin 5`, has range the span of the ten monomials of `L(10·O)` (dimension 10) and hence
  a `5`-dimensional kernel, which is exactly the span of the five Pfaffian coefficient vectors;
  the coefficient vector of `2a X₀² - b X₁X₄` is not in that span.

* **The assembly** (§3).  `sdRuleA K D h 4` and `sdRuleB K D h 4` are the images under
  `algebraMap ↥F₁ (RatFunc ↥F₁)` of explicit elements of the twist field `F₁`, the first of which
  is nonzero by the core lemma; then `sdW 4 = C a₀ + t · C b₀` is nonzero because its constant
  term is (`RatFunc.C_add_X_mul_C_ne_zero`).
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotK.TwRuling

open WeierstrassCurve WeierstrassCurve.Affine

namespace SdWfour

/-! ## §1 Elementary polynomial identities for the twisted ruling vectors -/

/-- The fourth component of the first ruling vector. -/
theorem kleinTwRuleA_four {R : Type*} [CommRing R] (a b h : R) (c : Fin 5 → R) :
    Work.MotK.kleinTwRuleA a b h c 4
      = 2 * a ^ 3 * b * (c 0) ^ 2 - a ^ 2 * b ^ 2 * h * (c 1) * (c 4) := by
  unfold Work.MotK.kleinTwRuleA Work.MotK.kleinTwPolarP Work.MotK.kleinTwP Work.MotK.kleinTwTan
    Work.MotK.kleinTwBilin Work.MotK.kleinTwQ Work.MotK.kleinTwP0 Work.MotK.kleinTwP1
    Work.MotK.kleinTwP2 Work.MotK.kleinTwP3 Work.MotK.kleinTwP4 Work.MotK.kleinE
  simp only [Pi.single_apply, Fin.isValue]
  norm_num
  refl_ring1

/-- The fourth component of the second ruling vector. -/
theorem kleinTwRuleB_four {R : Type*} [CommRing R] (a b h : R) (c : Fin 5 → R) :
    Work.MotK.kleinTwRuleB a b h c 4
      = a ^ 4 * h * (c 1) * (c 3) - 2 * a * b ^ 3 * h * (c 0) * (c 4) := by
  unfold Work.MotK.kleinTwRuleB Work.MotK.kleinTwPolarP Work.MotK.kleinTwP Work.MotK.kleinTwTan
    Work.MotK.kleinTwBilin Work.MotK.kleinTwQ Work.MotK.kleinTwP0 Work.MotK.kleinTwP1
    Work.MotK.kleinTwP2 Work.MotK.kleinTwP3 Work.MotK.kleinTwP4 Work.MotK.kleinE
  simp only [Pi.single_apply, Fin.isValue]
  norm_num
  refl_ring1

/-- Naturality of the fourth component of the first ruling vector. -/
theorem kleinTwRuleA_map_four {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b h : R)
    (c : Fin 5 → R) :
    Work.MotK.kleinTwRuleA (φ a) (φ b) (φ h) (fun i => φ (c i)) 4
      = φ (Work.MotK.kleinTwRuleA a b h c 4) := by
  simp only [kleinTwRuleA_four, map_sub, map_mul, map_pow, map_ofNat]

/-- Naturality of the fourth component of the second ruling vector. -/
theorem kleinTwRuleB_map_four {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b h : R)
    (c : Fin 5 → R) :
    Work.MotK.kleinTwRuleB (φ a) (φ b) (φ h) (fun i => φ (c i)) 4
      = φ (Work.MotK.kleinTwRuleB a b h c 4) := by
  simp only [kleinTwRuleB_four, map_sub, map_mul, map_pow, map_ofNat]

/-- **Transcendence of `RatFunc.X`**: `C a + X * C b` is nonzero as soon as `a ≠ 0`. -/
theorem ratFunc_C_add_X_mul_C_ne_zero {F : Type*} [Field F] {a b : F} (ha : a ≠ 0) :
    RatFunc.C a + RatFunc.X * RatFunc.C b ≠ 0 := by
  intro h0
  have hX : (algebraMap (Polynomial F) (RatFunc F)) Polynomial.X = RatFunc.X :=
    RatFunc.algebraMap_X
  have hCa : (algebraMap (Polynomial F) (RatFunc F)) (Polynomial.C a) = RatFunc.C a := by
    change (algebraMap (Polynomial F) (RatFunc F)) ((algebraMap F (Polynomial F)) a) = RatFunc.C a
    rw [← IsScalarTower.algebraMap_apply F (Polynomial F) (RatFunc F), RatFunc.algebraMap_eq_C]
  have hCb : (algebraMap (Polynomial F) (RatFunc F)) (Polynomial.C b) = RatFunc.C b := by
    change (algebraMap (Polynomial F) (RatFunc F)) ((algebraMap F (Polynomial F)) b) = RatFunc.C b
    rw [← IsScalarTower.algebraMap_apply F (Polynomial F) (RatFunc F), RatFunc.algebraMap_eq_C]
  have h2 : (algebraMap (Polynomial F) (RatFunc F))
      (Polynomial.C a + Polynomial.X * Polynomial.C b) = 0 := by
    rw [map_add, map_mul, hCa, hCb, hX, h0]
  have h3 : Polynomial.C a + Polynomial.X * Polynomial.C b = 0 :=
    IsFractionRing.injective (Polynomial F) (RatFunc F) (by rw [h2, map_zero])
  have h4 : (Polynomial.C a + Polynomial.X * Polynomial.C b).coeff 0 = 0 := by
    rw [h3, Polynomial.coeff_zero]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_mul_zero, add_zero] at h4
  exact ha h4

/-- The zeroth twisted coordinate (in the rational function field of the twist field) is `1`. -/
theorem sdY_zero (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) :
    Work.MotK.TGen.sdY K D h 0 = 1 := by
  have h0 : Work.MotK.twCoordG K D h 0 = 1 := by
    rw [Work.MotK.twCoordG]
    simp only [Fin.val_zero, pow_zero, one_mul]
    exact div_self (hD.coord0_ne (Work.MotK.KbG K))
  have hsub : (⟨Work.MotK.twCoordG K D h 0,
      IntermediateField.subset_adjoin K (Set.range (Work.MotK.twCoordG K D h))
        (Set.mem_range_self 0)⟩ : ↥(Work.MotK.twistFieldTG K D h)) = 1 :=
    Subtype.ext h0
  rw [Work.MotK.TGen.sdY, hsub, map_one]

/-! ## §2 The core non-degeneracy: the multiplication map on the fifteen pairs -/

variable {R : Type} [Field R]

/-- First coordinate of the `q`-th pair of the fifteen unordered pairs of `Fin 5`. -/
def pfA (q : Fin 5 × Fin 3) : Fin 5 :=
  if q.2 = 0 then 2 * q.1 else if q.2 = 1 then 2 * q.1 + 2 else 2 * q.1 + 1

/-- Second coordinate of the `q`-th pair of the fifteen unordered pairs of `Fin 5`. -/
def pfB (q : Fin 5 × Fin 3) : Fin 5 :=
  if q.2 = 0 then 2 * q.1 else if q.2 = 1 then 2 * q.1 + 3 else 2 * q.1 + 4

@[simp] theorem pfA_zero (k : Fin 5) : pfA (k, 0) = 2 * k := by simp [pfA]
@[simp] theorem pfB_zero (k : Fin 5) : pfB (k, 0) = 2 * k := by simp [pfB]
@[simp] theorem pfA_one (k : Fin 5) : pfA (k, 1) = 2 * k + 2 := by simp [pfA]
@[simp] theorem pfB_one (k : Fin 5) : pfB (k, 1) = 2 * k + 3 := by simp [pfB]
@[simp] theorem pfA_two (k : Fin 5) : pfA (k, 2) = 2 * k + 1 := by simp [pfA]
@[simp] theorem pfB_two (k : Fin 5) : pfB (k, 2) = 2 * k + 4 := by simp [pfB]

/-- The fifteen pairs `(pfA q, pfB q)` exhaust the unordered pairs of `Fin 5`. -/
theorem pf_cover : ∀ p : Fin 5 × Fin 5, ∃ q : Fin 5 × Fin 3,
    (pfA q = p.1 ∧ pfB q = p.2) ∨ (pfA q = p.2 ∧ pfB q = p.1) := by decide

section

variable {E : WeierstrassCurve R} (κ : Fin 5 → Affine.FunctionField E)

/-- The multiplication map `c ↦ ∑_q c q • κ_{pfA q} κ_{pfB q}` on the fifteen pairs. -/
noncomputable def Phi : (Fin 5 × Fin 3 → R) →ₗ[R] Affine.FunctionField E where
  toFun c := ∑ q : Fin 5 × Fin 3, c q • (κ (pfA q) * κ (pfB q))
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_assoc, Finset.smul_sum]

theorem Phi_single (q : Fin 5 × Fin 3) (r : R) :
    Phi κ (Pi.single q r : Fin 5 × Fin 3 → R) = r • (κ (pfA q) * κ (pfB q)) := by
  change (∑ q' : Fin 5 × Fin 3, (Pi.single q r : Fin 5 × Fin 3 → R) q'
    • (κ (pfA q') * κ (pfB q'))) = r • (κ (pfA q) * κ (pfB q))
  rw [Finset.sum_eq_single q]
  · rw [Pi.single_eq_same]
  · intro q' _ hq'
    rw [Pi.single_eq_of_ne hq', zero_smul]
  · intro h; exact absurd (Finset.mem_univ q) h

theorem Phi_range_eq_pairs :
    (Phi κ).range = Submodule.span R (Set.range (fun q : Fin 5 × Fin 3 =>
      κ (pfA q) * κ (pfB q))) := by
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨c, hc⟩ := hz
    rw [← hc]
    change (∑ q : Fin 5 × Fin 3, c q • (κ (pfA q) * κ (pfB q)))
      ∈ Submodule.span R (Set.range (fun q : Fin 5 × Fin 3 => κ (pfA q) * κ (pfB q)))
    exact Submodule.sum_mem _ (fun q _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self q)))
  · rw [Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    exact ⟨Pi.single q 1, by rw [Phi_single, one_smul]⟩

theorem span_pairs_eq_span_all :
    Submodule.span R (Set.range (fun q : Fin 5 × Fin 3 => κ (pfA q) * κ (pfB q)))
      = Submodule.span R (Set.range (fun p : Fin 5 × Fin 5 => κ p.1 * κ p.2)) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    exact Submodule.subset_span ⟨(pfA q, pfB q), rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    change κ p.1 * κ p.2 ∈ Submodule.span R (Set.range (fun q : Fin 5 × Fin 3 =>
      κ (pfA q) * κ (pfB q)))
    obtain ⟨q, hq | hq⟩ := pf_cover p
    · rw [← hq.1, ← hq.2]
      exact Submodule.subset_span ⟨q, rfl⟩
    · rw [← hq.1, ← hq.2, mul_comm]
      exact Submodule.subset_span ⟨q, rfl⟩

end

theorem smul_mul_smul (E : WeierstrassCurve R) (c d : R) (x y : Affine.FunctionField E) :
    (c • x) * (d • y) = (c * d) • (x * y) := by
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]; ring

theorem mul_mem_span_mul {E : WeierstrassCurve R} {f : Fin 5 → Affine.FunctionField E}
    {u v : Affine.FunctionField E}
    (hu : u ∈ Submodule.span R (Set.range f)) (hv : v ∈ Submodule.span R (Set.range f)) :
    u * v ∈ Submodule.span R (Set.range (fun p : Fin 5 × Fin 5 => f p.1 * f p.2)) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hu
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hv
  rw [Finset.sum_mul_sum]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  refine Submodule.sum_mem _ (fun j _ => ?_)
  rw [smul_mul_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)

section Core

variable {E : WeierstrassCurve R}

/-- The coefficient vector of the `k`-th Pfaffian relation. -/
noncomputable def cPf (a b : R) (k : Fin 5) : Fin 5 × Fin 3 → R :=
  (-(a * b)) • (Pi.single (k, (0 : Fin 3)) 1 : Fin 5 × Fin 3 → R)
    + a ^ 2 • (Pi.single (k, (1 : Fin 3)) 1 : Fin 5 × Fin 3 → R)
    - b ^ 2 • (Pi.single (k, (2 : Fin 3)) 1 : Fin 5 × Fin 3 → R)

theorem cPf_apply_0 (a b : R) (k : Fin 5) : cPf a b k (k, 0) = -(a * b) := by
  simp [cPf, Pi.single_eq_same, Pi.single_eq_of_ne]

theorem cPf_apply_1 (a b : R) (k : Fin 5) : cPf a b k (k, 1) = a ^ 2 := by
  simp [cPf, Pi.single_eq_same, Pi.single_eq_of_ne]

theorem cPf_apply_2 (a b : R) (k : Fin 5) : cPf a b k (k, 2) = -(b ^ 2) := by
  simp [cPf, Pi.single_eq_same, Pi.single_eq_of_ne]

theorem cPf_apply_ne (a b : R) (k k' : Fin 5) (s : Fin 3) (h : k' ≠ k) :
    cPf a b k (k', s) = 0 := by
  have h0 : (k', s) ≠ (k, (0 : Fin 3)) := fun hh => h (Prod.ext_iff.mp hh).1
  have h1 : (k', s) ≠ (k, (1 : Fin 3)) := fun hh => h (Prod.ext_iff.mp hh).1
  have h2 : (k', s) ≠ (k, (2 : Fin 3)) := fun hh => h (Prod.ext_iff.mp hh).1
  simp only [cPf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne h0,
    Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
  first | refl_ring1 | ring

/-- The coefficient vector of the quadric `2a X₀² - b X₁X₄`. -/
noncomputable def cQ (a b : R) : Fin 5 × Fin 3 → R :=
  (2 * a) • (Pi.single ((0 : Fin 5), (0 : Fin 3)) 1 : Fin 5 × Fin 3 → R)
    - b • (Pi.single ((0 : Fin 5), (2 : Fin 3)) 1 : Fin 5 × Fin 3 → R)

theorem cQ_apply_00 (a b : R) : cQ a b ((0 : Fin 5), (0 : Fin 3)) = 2 * a := by
  simp [cQ, Pi.single_eq_same, Pi.single_eq_of_ne]

theorem cQ_apply_01 (a b : R) : cQ a b ((0 : Fin 5), (1 : Fin 3)) = 0 := by
  simp [cQ, Pi.single_eq_of_ne]

theorem cQ_apply_02 (a b : R) : cQ a b ((0 : Fin 5), (2 : Fin 3)) = -b := by
  simp [cQ, Pi.single_eq_same, Pi.single_eq_of_ne]

theorem Phi_cPf (a b : R) (κ : Fin 5 → Affine.FunctionField E) (k : Fin 5) :
    Phi κ (cPf a b k) = Work.MotK.kleinP (algebraMap R (Affine.FunctionField E) a)
      (algebraMap R (Affine.FunctionField E) b) κ k := by
  rw [cPf, map_sub, map_add, map_smul, map_smul, map_smul, Phi_single, Phi_single, Phi_single]
  simp only [pfA_zero, pfB_zero, pfA_one, pfB_one, pfA_two, pfB_two, Fin.isValue,
    Algebra.smul_def, map_neg, map_mul, map_pow]
  fin_cases k <;>
    · simp only [Work.MotK.kleinP, Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2,
        Work.MotK.kleinP3, Work.MotK.kleinP4, Fin.isValue]
      norm_num
      refl_ring1

theorem span_all_eq_span_bas {E : WeierstrassCurve R} (κ : Fin 5 → Affine.FunctionField E)
    (hκmem : ∀ i, κ i ∈ Submodule.span R (Set.range (sdBas E)))
    (hspans : ∀ m, sdBas E m ∈ Submodule.span R (Set.range κ)) :
    Submodule.span R (Set.range (fun p : Fin 5 × Fin 5 => κ p.1 * κ p.2))
      = Submodule.span R (Set.range (fun p : Fin 5 × Fin 5 => sdBas E p.1 * sdBas E p.2)) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    change κ p.1 * κ p.2 ∈ Submodule.span R (Set.range (fun p : Fin 5 × Fin 5 =>
      sdBas E p.1 * sdBas E p.2))
    exact mul_mem_span_mul (hκmem p.1) (hκmem p.2)
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    change sdBas E p.1 * sdBas E p.2
      ∈ Submodule.span R (Set.range (fun p : Fin 5 × Fin 5 => κ p.1 * κ p.2))
    exact mul_mem_span_mul (hspans p.1) (hspans p.2)

theorem Phi_range_eq_span_sdTen {E : WeierstrassCurve R} (κ : Fin 5 → Affine.FunctionField E)
    (hκmem : ∀ i, κ i ∈ Submodule.span R (Set.range (sdBas E)))
    (hspans : ∀ m, sdBas E m ∈ Submodule.span R (Set.range κ)) :
    (Phi κ).range = Submodule.span R (Set.range (sdTen E)) := by
  rw [Phi_range_eq_pairs, span_pairs_eq_span_all, span_all_eq_span_bas κ hκmem hspans,
    productSpan_eq]

theorem finrank_ker {E : WeierstrassCurve R} (κ : Fin 5 → Affine.FunctionField E)
    (hκmem : ∀ i, κ i ∈ Submodule.span R (Set.range (sdBas E)))
    (hspans : ∀ m, sdBas E m ∈ Submodule.span R (Set.range κ)) :
    Module.finrank R ((Phi κ).ker) = 5 := by
  have h := LinearMap.finrank_range_add_finrank_ker (Phi κ)
  rw [Phi_range_eq_span_sdTen κ hκmem hspans, finrank_span_sdTen,
    Module.finrank_fintype_fun_eq_card] at h
  have hc : Fintype.card (Fin 5 × Fin 3) = 15 := by simp [Fintype.card_prod]
  omega

theorem cPf_mem_ker (a b : R) {E : WeierstrassCurve R} (κ : Fin 5 → Affine.FunctionField E)
    (hκ : ∀ k : Fin 5, Work.MotK.kleinP (algebraMap R (Affine.FunctionField E) a)
      (algebraMap R (Affine.FunctionField E) b) κ k = 0) (k : Fin 5) :
    cPf a b k ∈ (Phi κ).ker := by
  rw [LinearMap.mem_ker, Phi_cPf a b κ k, hκ k]

theorem linearIndependent_cPf (a b : R) (hab : a * b ≠ 0) :
    LinearIndependent R (cPf a b) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  have h := congrFun hc (k, (1 : Fin 3))
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at h
  rw [Finset.sum_eq_single k] at h
  · rw [cPf_apply_1, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_right
      (pow_ne_zero 2 (fun h0 => hab (by rw [h0, zero_mul])))
  · intro k' _ hk'
    rw [cPf_apply_ne a b k' k 1 (Ne.symm hk'), smul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

theorem ker_eq_span_cPf (a b : R) (hab : a * b ≠ 0) {E : WeierstrassCurve R}
    (κ : Fin 5 → Affine.FunctionField E)
    (hκmem : ∀ i, κ i ∈ Submodule.span R (Set.range (sdBas E)))
    (hspans : ∀ m, sdBas E m ∈ Submodule.span R (Set.range κ))
    (hκ : ∀ k : Fin 5, Work.MotK.kleinP (algebraMap R (Affine.FunctionField E) a)
      (algebraMap R (Affine.FunctionField E) b) κ k = 0) :
    (Phi κ).ker = Submodule.span R (Set.range (cPf a b)) := by
  have hle : Submodule.span R (Set.range (cPf a b)) ≤ (Phi κ).ker := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact cPf_mem_ker a b κ hκ k
  have hfin : Module.finrank R ↥(Submodule.span R (Set.range (cPf a b)))
      = Module.finrank R ↥((Phi κ).ker) := by
    rw [finrank_span_eq_card (linearIndependent_cPf a b hab), finrank_ker κ hκmem hspans,
      Fintype.card_fin]
  exact (Submodule.eq_of_le_of_finrank_eq hle hfin).symm

theorem cQ_notMem_ker (a b : R) (hab : a * b ≠ 0) {E : WeierstrassCurve R}
    (κ : Fin 5 → Affine.FunctionField E)
    (hκmem : ∀ i, κ i ∈ Submodule.span R (Set.range (sdBas E)))
    (hspans : ∀ m, sdBas E m ∈ Submodule.span R (Set.range κ))
    (hκ : ∀ k : Fin 5, Work.MotK.kleinP (algebraMap R (Affine.FunctionField E) a)
      (algebraMap R (Affine.FunctionField E) b) κ k = 0) :
    cQ a b ∉ (Phi κ).ker := by
  intro hmem
  rw [ker_eq_span_cPf a b hab κ hκmem hspans hκ] at hmem
  obtain ⟨μ, hμ⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hmem
  have h01 := congrFun hμ ((0 : Fin 5), (1 : Fin 3))
  have h02 := congrFun hμ ((0 : Fin 5), (2 : Fin 3))
  simp only [Finset.sum_apply, Pi.smul_apply] at h01 h02
  rw [Finset.sum_eq_single (0 : Fin 5)] at h01
  · rw [cPf_apply_1, cQ_apply_01, smul_eq_mul] at h01
    have hμ0 : μ 0 = 0 := (mul_eq_zero.mp h01).resolve_right
      (pow_ne_zero 2 (fun h0 => hab (by rw [h0, zero_mul])))
    rw [Finset.sum_eq_single (0 : Fin 5)] at h02
    · rw [cPf_apply_2, cQ_apply_02, smul_eq_mul, hμ0, zero_mul] at h02
      exact hab (by rw [neg_eq_zero.mp h02.symm, mul_zero])
    · intro k' _ hk'
      rw [cPf_apply_ne a b k' 0 2 (Ne.symm hk'), smul_zero]
    · intro h; exact absurd (Finset.mem_univ (0 : Fin 5)) h
  · intro k' _ hk'
    rw [cPf_apply_ne a b k' 0 1 (Ne.symm hk'), smul_zero]
  · intro h; exact absurd (Finset.mem_univ (0 : Fin 5)) h

/-- **The core non-degeneracy.**  For a field `R`, a Weierstrass curve `E` over `R`, `a, b ∈ R`
with `ab ≠ 0`, and `κ` in the function field whose span is that of `1, x, y, x², xy` and on which
the five Klein Pfaffians vanish, the quadratic form `2aκ₀² - bκ₁κ₄` is nonzero. -/
theorem kleinQuad_ne_zero {E : WeierstrassCurve R} (a b : R) (hab : a * b ≠ 0)
    (κ : Fin 5 → Affine.FunctionField E)
    (hκmem : ∀ i, κ i ∈ Submodule.span R (Set.range (sdBas E)))
    (hspans : ∀ m, sdBas E m ∈ Submodule.span R (Set.range κ))
    (hκ : ∀ k : Fin 5, Work.MotK.kleinP (algebraMap R (Affine.FunctionField E) a)
      (algebraMap R (Affine.FunctionField E) b) κ k = 0) :
    2 * algebraMap R (Affine.FunctionField E) a * (κ 0) ^ 2
      - algebraMap R (Affine.FunctionField E) b * (κ 1) * (κ 4) ≠ 0 := by
  intro h0
  refine cQ_notMem_ker a b hab κ hκmem hspans hκ ?_
  rw [LinearMap.mem_ker]
  change Phi κ (cQ a b) = 0
  rw [cQ, map_sub, map_smul, map_smul, Phi_single, Phi_single]
  simp only [pfA_zero, pfB_zero, pfA_two, pfB_two, Fin.isValue, Algebra.smul_def, map_mul,
    map_ofNat, map_neg, map_one, mul_zero, zero_add, one_mul]
  linear_combination (norm := refl_ring1) h0

end Core

end SdWfour

/-! ## §3 The assembly -/

open SdWfour

theorem sdW_four_ne_zero (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good) (h : K)
    (hh : h ≠ 0) : Work.MotK.TGen.sdW K D h 4 ≠ 0 := by
  classical
  set F₁ : IntermediateField K (Work.MotK.OmG K D) := Work.MotK.twistFieldTG K D h with hF₁
  set S := Work.MotK.TGen.sdA K D h with hS
  let yF : Fin 5 → ↥F₁ := fun i => ⟨Work.MotK.twCoordG K D h i,
    IntermediateField.subset_adjoin K (Set.range (Work.MotK.twCoordG K D h)) (Set.mem_range_self i)⟩
  have hyF : ∀ i, algebraMap ↥F₁ S (yF i) = Work.MotK.TGen.sdY K D h i := fun i => rfl
  have hsy : Work.MotK.TGen.sdY K D h = fun i => algebraMap ↥F₁ S (yF i) :=
    funext fun i => (hyF i).symm
  have hyOm : ∀ i, algebraMap ↥F₁ (Work.MotK.OmG K D) (yF i) = Work.MotK.twCoordG K D h i :=
    fun i => rfl
  have hyF0 : yF 0 = 1 := by
    refine (RingHom.injective (algebraMap ↥F₁ S)) ?_
    rw [hyF 0, sdY_zero K D hD h, map_one]
  -- the two ruling vectors, evaluated at `i = 4`, as `C`-images
  have hA : Work.MotK.TGen.sdRuleA K D h 4 = algebraMap ↥F₁ S
      (2 * (algebraMap K ↥F₁ D.a) ^ 3 * (algebraMap K ↥F₁ D.b)
        - (algebraMap K ↥F₁ D.a) ^ 2 * (algebraMap K ↥F₁ D.b) ^ 2 * (algebraMap K ↥F₁ h)
          * yF 1 * yF 4) := by
    rw [Work.MotK.TGen.sdRuleA, hsy, IsScalarTower.algebraMap_apply K ↥F₁ S D.a,
      IsScalarTower.algebraMap_apply K ↥F₁ S D.b, IsScalarTower.algebraMap_apply K ↥F₁ S h,
      kleinTwRuleA_map_four (algebraMap ↥F₁ S) (algebraMap K ↥F₁ D.a) (algebraMap K ↥F₁ D.b)
        (algebraMap K ↥F₁ h) yF,
      kleinTwRuleA_four, hyF0, one_pow, mul_one]
  have hB : Work.MotK.TGen.sdRuleB K D h 4 = algebraMap ↥F₁ S
      ((algebraMap K ↥F₁ D.a) ^ 4 * (algebraMap K ↥F₁ h) * yF 1 * yF 3
        - 2 * (algebraMap K ↥F₁ D.a) * (algebraMap K ↥F₁ D.b) ^ 3 * (algebraMap K ↥F₁ h)
          * yF 0 * yF 4) := by
    rw [Work.MotK.TGen.sdRuleB, hsy, IsScalarTower.algebraMap_apply K ↥F₁ S D.a,
      IsScalarTower.algebraMap_apply K ↥F₁ S D.b, IsScalarTower.algebraMap_apply K ↥F₁ S h,
      kleinTwRuleB_map_four (algebraMap ↥F₁ S) (algebraMap K ↥F₁ D.a) (algebraMap K ↥F₁ D.b)
        (algebraMap K ↥F₁ h) yF,
      kleinTwRuleB_four]
  -- the constant term of `sdRuleA K D h 4` is nonzero
  have hne : algebraMap ↥F₁ S
      (2 * (algebraMap K ↥F₁ D.a) ^ 3 * (algebraMap K ↥F₁ D.b)
        - (algebraMap K ↥F₁ D.a) ^ 2 * (algebraMap K ↥F₁ D.b) ^ 2 * (algebraMap K ↥F₁ h)
          * yF 1 * yF 4) ≠ 0 := by
    intro h0
    have hfac : 2 * (algebraMap K ↥F₁ D.a) ^ 3 * (algebraMap K ↥F₁ D.b)
        - (algebraMap K ↥F₁ D.a) ^ 2 * (algebraMap K ↥F₁ D.b) ^ 2 * (algebraMap K ↥F₁ h)
          * yF 1 * yF 4
        = (algebraMap K ↥F₁ D.a) ^ 2 * (algebraMap K ↥F₁ D.b)
          * (2 * (algebraMap K ↥F₁ D.a)
            - (algebraMap K ↥F₁ D.b) * (algebraMap K ↥F₁ h) * yF 1 * yF 4) := by ring
    rw [hfac, map_mul, map_mul, map_pow] at h0
    have haK : D.a ≠ 0 := fun hda => hD.ab_ne (by rw [hda, zero_mul])
    have hbK : D.b ≠ 0 := fun hdb => hD.ab_ne (by rw [hdb, mul_zero])
    have ha : algebraMap K ↥F₁ D.a ≠ 0 := fun h0 =>
      haK (RingHom.injective (algebraMap K ↥F₁) (by rw [h0, map_zero]))
    have hb : algebraMap K ↥F₁ D.b ≠ 0 := fun h0 =>
      hbK (RingHom.injective (algebraMap K ↥F₁) (by rw [h0, map_zero]))
    have haS : algebraMap ↥F₁ S (algebraMap K ↥F₁ D.a) ≠ 0 := fun h0 =>
      ha (RingHom.injective (algebraMap ↥F₁ S) (by rw [h0, map_zero]))
    have hbS : algebraMap ↥F₁ S (algebraMap K ↥F₁ D.b) ≠ 0 := fun h0 =>
      hb (RingHom.injective (algebraMap ↥F₁ S) (by rw [h0, map_zero]))
    have hz : algebraMap ↥F₁ S (2 * (algebraMap K ↥F₁ D.a)
        - (algebraMap K ↥F₁ D.b) * (algebraMap K ↥F₁ h) * yF 1 * yF 4) = 0 := by
      rcases mul_eq_zero.mp h0 with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact absurd h2 (pow_ne_zero 2 haS)
        · exact absurd h2 hbS
      · exact h1
    have hz' : 2 * (algebraMap K ↥F₁ D.a)
        - (algebraMap K ↥F₁ D.b) * (algebraMap K ↥F₁ h) * yF 1 * yF 4 = 0 :=
      RingHom.injective (algebraMap ↥F₁ S) (by rw [hz, map_zero])
    -- push to the algebraic closure
    have h3 : 2 * algebraMap K (Work.MotK.OmG K D) D.a
        - algebraMap K (Work.MotK.OmG K D) D.b * algebraMap K (Work.MotK.OmG K D) h
          * Work.MotK.twCoordG K D h 1 * Work.MotK.twCoordG K D h 4 = 0 := by
      have h := congrArg (algebraMap ↥F₁ (Work.MotK.OmG K D)) hz'
      simpa only [map_zero, map_sub, map_mul, map_ofNat, hyOm,
        IsScalarTower.algebraMap_apply K ↥F₁ (Work.MotK.OmG K D)] using h
    -- the Kummer coordinate identity
    have hy : algebraMap K (Work.MotK.OmG K D) h * Work.MotK.twCoordG K D h 1
        * Work.MotK.twCoordG K D h 4
        = Work.MotV.kleinCoord D (Work.MotK.KbG K) 1 * Work.MotV.kleinCoord D (Work.MotK.KbG K) 4
          / (Work.MotV.kleinCoord D (Work.MotK.KbG K) 0) ^ 2 := by
      set w := algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h) with hwdef
      have hw5 : w ^ 5 = algebraMap K (Work.MotK.OmG K D) h := by
        rw [hwdef]; exact Work.MotK.TGen.wG_pow_five D h
      have hw1 : w ^ 1 * Work.MotK.twCoordG K D h 1
          = Work.MotV.kleinCoord D (Work.MotK.KbG K) 1
            / Work.MotV.kleinCoord D (Work.MotK.KbG K) 0 := by
        rw [hwdef]; exact Work.MotK.TGen.pow_mul_twCoordG D h hh 1
      have hw4 : w ^ 4 * Work.MotK.twCoordG K D h 4
          = Work.MotV.kleinCoord D (Work.MotK.KbG K) 4
            / Work.MotV.kleinCoord D (Work.MotK.KbG K) 0 := by
        rw [hwdef]; exact Work.MotK.TGen.pow_mul_twCoordG D h hh 4
      have hmain : w ^ 5 * Work.MotK.twCoordG K D h 1 * Work.MotK.twCoordG K D h 4
          = Work.MotV.kleinCoord D (Work.MotK.KbG K) 1
            * Work.MotV.kleinCoord D (Work.MotK.KbG K) 4
            / (Work.MotV.kleinCoord D (Work.MotK.KbG K) 0) ^ 2 := by
        rw [show w ^ 5 = w ^ 1 * w ^ 4 from by ring]
        rw [show w ^ 1 * w ^ 4 * Work.MotK.twCoordG K D h 1 * Work.MotK.twCoordG K D h 4
            = (w ^ 1 * Work.MotK.twCoordG K D h 1)
              * (w ^ 4 * Work.MotK.twCoordG K D h 4) from by ring]
        rw [hw1, hw4]
        first | refl_ring1 | ring
      rw [← hw5]
      exact hmain
    -- contradict the core lemma
    have hcore := kleinQuad_ne_zero (R := Work.MotK.KbG K)
      (E := D.E.baseChange (Work.MotK.KbG K))
      (algebraMap K (Work.MotK.KbG K) D.a) (algebraMap K (Work.MotK.KbG K) D.b)
      (fun h0 => hD.ab_ne (RingHom.injective (algebraMap K (Work.MotK.KbG K))
        (by rw [map_mul, map_zero, h0])))
      (Work.MotV.kleinCoord D (Work.MotK.KbG K)) (by
        intro i
        rw [Work.MotV.kleinCoord_eq_sum]
        refine Submodule.sum_mem _ (fun m _ => ?_)
        rw [← Algebra.smul_def]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩))
      (by
        obtain ⟨e, he⟩ := hD.spans
        intro m
        rw [show sdBas (D.E.baseChange (Work.MotK.KbG K)) m
            = Work.MotV.kleinBas D (Work.MotK.KbG K) m from rfl,
          he (Work.MotK.KbG K) m]
        refine Submodule.sum_mem _ (fun i _ => ?_)
        rw [← Algebra.smul_def]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
      (by intro k; exact hD.klein_eq (Work.MotK.KbG K) k)
    simp only [← IsScalarTower.algebraMap_apply K (Work.MotK.KbG K) (Work.MotK.OmG K D)]
      at hcore
    have hκ0 : (Work.MotV.kleinCoord D (Work.MotK.KbG K) 0) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (hD.coord0_ne (Work.MotK.KbG K))
    have h4 : 2 * algebraMap K (Work.MotK.OmG K D) D.a
        - algebraMap K (Work.MotK.OmG K D) D.b
          * (Work.MotV.kleinCoord D (Work.MotK.KbG K) 1
              * Work.MotV.kleinCoord D (Work.MotK.KbG K) 4
              / (Work.MotV.kleinCoord D (Work.MotK.KbG K) 0) ^ 2) = 0 := by
      linear_combination (norm := refl_ring1) h3 + algebraMap K (Work.MotK.OmG K D) D.b * hy
    have h5 : 2 * algebraMap K (Work.MotK.OmG K D) D.a
            * (Work.MotV.kleinCoord D (Work.MotK.KbG K) 0) ^ 2
          - algebraMap K (Work.MotK.OmG K D) D.b * Work.MotV.kleinCoord D (Work.MotK.KbG K) 1
            * Work.MotV.kleinCoord D (Work.MotK.KbG K) 4 = 0 := by
      have h4' : 2 * algebraMap K (Work.MotK.OmG K D) D.a
          = algebraMap K (Work.MotK.OmG K D) D.b
            * (Work.MotV.kleinCoord D (Work.MotK.KbG K) 1
                * Work.MotV.kleinCoord D (Work.MotK.KbG K) 4
                / (Work.MotV.kleinCoord D (Work.MotK.KbG K) 0) ^ 2) := sub_eq_zero.mp h4
      rw [h4', mul_assoc, div_mul_cancel₀ _ hκ0]
      refl_ring1
    exact hcore h5
  rw [Work.MotK.TGen.sdW, hA, hB, RatFunc.algebraMap_eq_C]
  exact ratFunc_C_add_X_mul_C_ne_zero (fun h0 => hne (by rw [h0, map_zero]))

end Work.MotK.TwRuling
