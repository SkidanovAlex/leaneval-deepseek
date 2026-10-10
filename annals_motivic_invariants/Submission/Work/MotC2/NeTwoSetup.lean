import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.Integral
import Submission.Work.MotC2.Negation
import Submission.Work.MotC2.affRing_eq_adjoin
import Submission.Work.MotC2.algebraMap_smul_eq_aeval
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve.Affine

namespace Work.MotC2

variable {L : Type*} [Field L]

/-- The `L`-algebra map `L[X] → L(E)`, `X ↦ x = genX E`. -/
noncomputable def xPhi (E : WeierstrassCurve L) : Polynomial L →ₐ[L] Func E :=
  Polynomial.aeval (genX E)

lemma xPhi_X (E : WeierstrassCurve L) : xPhi E Polynomial.X = genX E := by
  simp [xPhi]

lemma xPhi_apply (E : WeierstrassCurve L) (p : Polynomial L) :
    xPhi E p = algebraMap (Polynomial L) (Func E) p :=
  (algebraMap_polynomial_eq_aeval_genX E p).symm

lemma algebraMap_poly_func_injective (E : WeierstrassCurve L) :
    Function.Injective (algebraMap (Polynomial L) (Func E)) := by
  intro x y hxy
  have h : algebraMap (Coord E) (Func E) (algebraMap (Polynomial L) (Coord E) x) =
      algebraMap (Coord E) (Func E) (algebraMap (Polynomial L) (Coord E) y) := by
    rw [IsScalarTower.algebraMap_apply (Polynomial L) (Coord E) (Func E)] at hxy
    exact hxy
  exact FaithfulSMul.algebraMap_injective (Polynomial L) (Coord E)
    (IsFractionRing.injective (Coord E) (Func E) h)

lemma xPhi_injective (E : WeierstrassCurve L) : Function.Injective (xPhi E) := by
  intro x y h
  refine algebraMap_poly_func_injective E ?_
  rw [← xPhi_apply E x, ← xPhi_apply E y]
  exact h

/-- `L[x]` as a subalgebra of `L(E)`. -/
noncomputable def Ax (E : WeierstrassCurve L) : Subalgebra L (Func E) :=
  Algebra.adjoin L ({genX E} : Set (Func E))

lemma xPhi_range (E : WeierstrassCurve L) : (xPhi E).range = Ax E := by
  rw [Ax, Algebra.adjoin_singleton_eq_range_aeval]
  rfl

noncomputable def xPsi (E : WeierstrassCurve L) : RatFunc L →ₐ[Polynomial L] Func E :=
  RatFunc.liftAlgHom (Algebra.ofId (Polynomial L) (Func E))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective (Algebra.ofId (Polynomial L) (Func E))
      (fun x y h => algebraMap_poly_func_injective E (by
        simpa only [Algebra.ofId_apply] using h)))

lemma xPsi_apply_algebraMap (E : WeierstrassCurve L) (p : Polynomial L) :
    xPsi E (algebraMap (Polynomial L) (RatFunc L) p) = xPhi E p := by
  have h : algebraMap (Polynomial L) (RatFunc L) p =
      algebraMap (Polynomial L) (RatFunc L) p / algebraMap (Polynomial L) (RatFunc L) 1 := by simp
  rw [xPsi, h, RatFunc.liftAlgHom_apply_div]
  rw [map_one, div_one, Algebra.ofId_apply]
  exact (xPhi_apply E p).symm

lemma xPsi_injective (E : WeierstrassCurve L) : Function.Injective (xPsi E) := by
  have hφ : Function.Injective (Algebra.ofId (Polynomial L) (Func E)) :=
    fun x y h => algebraMap_poly_func_injective E (by simpa only [Algebra.ofId_apply] using h)
  exact RatFunc.liftAlgHom_injective _ hφ

/-- `e = a₁x + a₃` in `L(E)`. -/
noncomputable def eK (E : WeierstrassCurve L) : Func E :=
  algebraMap L (Func E) E.a₁ * genX E + algebraMap L (Func E) E.a₃

/-- `c = x³ + a₂x² + a₄x + a₆` in `L(E)`. -/
noncomputable def cK (E : WeierstrassCurve L) : Func E :=
  genX E ^ 3 + algebraMap L (Func E) E.a₂ * genX E ^ 2 + algebraMap L (Func E) E.a₄ * genX E +
    algebraMap L (Func E) E.a₆

lemma eK_mem (E : WeierstrassCurve L) : eK E ∈ Ax E := by
  have hx : genX E ∈ Ax E := Algebra.subset_adjoin (Set.mem_singleton _)
  exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ E.a₁) hx)
    (Subalgebra.algebraMap_mem _ E.a₃)

lemma cK_mem (E : WeierstrassCurve L) : cK E ∈ Ax E := by
  have hx : genX E ∈ Ax E := Algebra.subset_adjoin (Set.mem_singleton _)
  exact add_mem (add_mem (add_mem (pow_mem hx 3)
    (mul_mem (Subalgebra.algebraMap_mem _ E.a₂) (pow_mem hx 2)))
    (mul_mem (Subalgebra.algebraMap_mem _ E.a₄) hx)) (Subalgebra.algebraMap_mem _ E.a₆)

lemma y_sq (E : WeierstrassCurve L) : genY E ^ 2 + eK E * genY E = cK E := by
  have h := genY_sq_relation E
  rw [eK, cK]
  linear_combination (norm := refl_ring1) h

/-- The conjugation `y ↦ -y - e` fixes `L[x]` pointwise. -/
lemma negAlgEquiv_mem_Ax (E : WeierstrassCurve L) {a : Func E} (ha : a ∈ Ax E) :
    negAlgEquiv E a = a := by
  rw [Ax] at ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact negAlgEquiv_genX E
  | algebraMap c => exact AlgEquiv.commutes (negAlgEquiv E) c
  | add x y hx hy px py => rw [map_add, px, py]
  | mul x y hx hy px py => rw [map_mul, px, py]

/-! ## The coordinate ring as a subalgebra of `L(E)` -/

/-- The structure map `L[X,Y]/(W_E) → L(E)` as an `L`-algebra map onto `affRing E`. -/
noncomputable def coordHomAffRing (E : WeierstrassCurve L) : Coord E →ₐ[L] ↥(affRing E) :=
  (IsScalarTower.toAlgHom L (Coord E) (Func E)).codRestrict (affRing E)
    (fun a => Algebra.subset_adjoin ⟨a, rfl⟩)

lemma coordHomAffRing_coe (E : WeierstrassCurve L) (a : Coord E) :
    ((coordHomAffRing E a : ↥(affRing E)) : Func E) = algebraMap (Coord E) (Func E) a := rfl

lemma coordHomAffRing_injective (E : WeierstrassCurve L) :
    Function.Injective (coordHomAffRing E) := fun a b h =>
  IsFractionRing.injective (Coord E) (Func E) (by
    rw [← coordHomAffRing_coe E a, ← coordHomAffRing_coe E b, h])

lemma coordHomAffRing_surjective (E : WeierstrassCurve L) :
    Function.Surjective (coordHomAffRing E) := by
  rintro ⟨y, hy⟩
  have key : ∃ a : Coord E, algebraMap (Coord E) (Func E) a = y := by
    induction hy using Algebra.adjoin_induction with
    | mem z hz => obtain ⟨a, rfl⟩ := hz; exact ⟨a, rfl⟩
    | algebraMap c => exact ⟨algebraMap L (Coord E) c, by
        rw [← IsScalarTower.algebraMap_apply L (Coord E) (Func E)]⟩
    | add x y hx hy px py =>
        obtain ⟨a, ha⟩ := px; obtain ⟨b, hb⟩ := py
        exact ⟨a + b, by rw [map_add, ha, hb]⟩
    | mul x y hx hy px py =>
        obtain ⟨a, ha⟩ := px; obtain ⟨b, hb⟩ := py
        exact ⟨a * b, by rw [map_mul, ha, hb]⟩
  obtain ⟨a, ha⟩ := key
  exact ⟨a, Subtype.ext (by rw [coordHomAffRing_coe, ha])⟩

/-- The affine coordinate ring `L[X,Y]/(W_E)` is the affine ring `L[x,y] ⊆ L(E)`. -/
noncomputable def coordEquivAffRing (E : WeierstrassCurve L) : Coord E ≃ₐ[L] ↥(affRing E) :=
  AlgEquiv.ofBijective (coordHomAffRing E)
    ⟨coordHomAffRing_injective E, coordHomAffRing_surjective E⟩

lemma coordEquivAffRing_coe (E : WeierstrassCurve L) (a : Coord E) :
    ((coordEquivAffRing E a : ↥(affRing E)) : Func E) = algebraMap (Coord E) (Func E) a := rfl

/-- `L[X] → L[x]` as an `L`-algebra equivalence. -/
noncomputable def xPhiHom (E : WeierstrassCurve L) : Polynomial L →ₐ[L] ↥(Ax E) :=
  (xPhi E).codRestrict (Ax E) (fun p => by
    rw [← xPhi_range]
    exact (AlgHom.mem_range (xPhi E)).mpr ⟨p, rfl⟩)

lemma xPhiHom_coe (E : WeierstrassCurve L) (p : Polynomial L) :
    ((xPhiHom E p : ↥(Ax E)) : Func E) = xPhi E p := rfl

lemma xPhiHom_injective (E : WeierstrassCurve L) : Function.Injective (xPhiHom E) :=
  fun a b h => xPhi_injective E (by rw [← xPhiHom_coe E a, ← xPhiHom_coe E b, h])

lemma xPhiHom_surjective (E : WeierstrassCurve L) : Function.Surjective (xPhiHom E) := by
  rintro ⟨y, hy⟩
  have key : ∃ a : Polynomial L, xPhi E a = y := by
    rw [Ax] at hy
    induction hy using Algebra.adjoin_induction with
    | mem z hz =>
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact ⟨Polynomial.X, xPhi_X E⟩
    | algebraMap c => exact ⟨Polynomial.C c, by simp [xPhi]⟩
    | add x y hx hy px py =>
        obtain ⟨a, ha⟩ := px; obtain ⟨b, hb⟩ := py
        exact ⟨a + b, by rw [map_add, ha, hb]⟩
    | mul x y hx hy px py =>
        obtain ⟨a, ha⟩ := px; obtain ⟨b, hb⟩ := py
        exact ⟨a * b, by rw [map_mul, ha, hb]⟩
  obtain ⟨a, ha⟩ := key
  exact ⟨a, Subtype.ext (by rw [xPhiHom_coe, ha])⟩

/-- `L[X] ≅ L[x] ⊆ L(E)`. -/
noncomputable def xPhiEquiv (E : WeierstrassCurve L) : Polynomial L ≃ₐ[L] ↥(Ax E) :=
  AlgEquiv.ofBijective (xPhiHom E) ⟨xPhiHom_injective E, xPhiHom_surjective E⟩

lemma xPhiEquiv_coe (E : WeierstrassCurve L) (p : Polynomial L) :
    ((xPhiEquiv E p : ↥(Ax E)) : Func E) = xPhi E p := rfl

/-! ## Integrality transfers -/

lemma isIntegral_coord_iff (E : WeierstrassCurve L) {h : Func E} :
    IsIntegral (Coord E) h ↔ IsIntegral ↥(affRing E) h := by
  refine RingEquiv.isIntegral_iff (coordEquivAffRing E).toRingEquiv ?_ h
  refine RingHom.ext (fun a => ?_)
  rw [RingHom.comp_apply]
  exact coordEquivAffRing_coe E a

lemma isIntegral_poly_iff (E : WeierstrassCurve L) {h : Func E} :
    IsIntegral (Polynomial L) h ↔ IsIntegral ↥(Ax E) h := by
  refine RingEquiv.isIntegral_iff (xPhiEquiv E).toRingEquiv ?_ h
  refine RingHom.ext (fun p => ?_)
  rw [RingHom.comp_apply]
  exact (xPhiEquiv_coe E p).trans (xPhi_apply E p)

/-- Integrality over the affine ring implies integrality over `L[x]`. -/
lemma isIntegral_Ax_of_isIntegral_affRing (E : WeierstrassCurve L) {h : Func E}
    (hh : IsIntegral ↥(affRing E) h) : IsIntegral ↥(Ax E) h := by
  have h1 : IsIntegral (Coord E) h := (isIntegral_coord_iff E).mpr hh
  haveI : Algebra.IsIntegral (Polynomial L) (Coord E) :=
    AdjoinRoot.isIntegral_of_monic (WeierstrassCurve.Affine.monic_polynomial (W := E))
  have h2 : IsIntegral (Polynomial L) h :=
    isIntegral_trans (R := Polynomial L) (A := Coord E) (B := Func E) h h1
  exact (isIntegral_poly_iff E).mp h2

/-- `genY` is integral over `L[x]`. -/
lemma isIntegral_genY_Ax (E : WeierstrassCurve L) : IsIntegral ↥(Ax E) (genY E) :=
  (Integral L E).1

/-- An element of `L(x) ⊆ L(E)` (in the sense of lying in the range of `xPsi`) that is integral
over `L[x]` belongs to `L[x]`. -/
lemma mem_Ax_of_isIntegral_of_mem_range_xPsi (E : WeierstrassCurve L) {z : Func E}
    (hz : z ∈ Set.range (xPsi E)) (hzint : IsIntegral ↥(Ax E) z) : z ∈ Ax E := by
  obtain ⟨w, rfl⟩ := hz
  have h1 : IsIntegral (Polynomial L) (xPsi E w) := (isIntegral_poly_iff E).mpr hzint
  have h2 : IsIntegral (Polynomial L) w :=
    (isIntegral_algHom_iff (xPsi E) (xPsi_injective E)).mp h1
  obtain ⟨p, hp⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Polynomial L)
    (K := RatFunc L)).mp h2
  rw [← hp, xPsi_apply_algebraMap, ← xPhi_range]
  exact (AlgHom.mem_range (xPhi E)).mpr ⟨p, rfl⟩

/-- The conjugation fixes `L(x) = range (xPsi E)`. -/
lemma negAlgEquiv_xPsi (E : WeierstrassCurve L) (w : RatFunc L) :
    negAlgEquiv E (xPsi E w) = xPsi E w := by
  obtain ⟨P, Q, hQ, hw⟩ := IsFractionRing.div_surjective (Polynomial L) w
  have hPm : xPhi E P ∈ Ax E := xPhi_range E ▸ (AlgHom.mem_range (xPhi E)).mpr ⟨P, rfl⟩
  have hQm : xPhi E Q ∈ Ax E := xPhi_range E ▸ (AlgHom.mem_range (xPhi E)).mpr ⟨Q, rfl⟩
  have h1 : xPsi E (algebraMap (Polynomial L) (RatFunc L) P /
      algebraMap (Polynomial L) (RatFunc L) Q) = xPhi E P / xPhi E Q := by
    rw [xPsi, RatFunc.liftAlgHom_apply_div]
    simp only [Algebra.ofId_apply, xPhi_apply]
  rw [← hw, h1, map_div₀, negAlgEquiv_mem_Ax E hPm, negAlgEquiv_mem_Ax E hQm]

/-- Every element of `L(x) = range (xPsi E)` is fixed by the conjugation. -/
lemma negAlgEquiv_mem_range_xPsi (E : WeierstrassCurve L) {z : Func E}
    (hz : z ∈ Set.range (xPsi E)) : negAlgEquiv E z = z := by
  obtain ⟨w, rfl⟩ := hz
  exact negAlgEquiv_xPsi E w

/-- A quotient of elements of `L[x]` lies in `L(x) = range (xPsi E)`. -/
lemma mem_range_xPsi_of_mul (E : WeierstrassCurve L) {z u v : Func E} (hu : u ∈ Ax E)
    (hv : v ∈ Ax E) (hv0 : v ≠ 0) (hzv : z * v = u) : z ∈ Set.range (xPsi E) := by
  rw [← xPhi_range] at hu hv
  obtain ⟨P, hP⟩ := hu
  obtain ⟨Q, hQ⟩ := hv
  have hP' : xPhi E P = u := hP
  have hQ' : xPhi E Q = v := hQ
  have hQ0 : xPhi E Q ≠ 0 := fun h => hv0 (hQ'.symm.trans h)
  have hzv' : z * xPhi E Q = xPhi E P := by rw [hQ', hP']; exact hzv
  refine ⟨algebraMap (Polynomial L) (RatFunc L) P / algebraMap (Polynomial L) (RatFunc L) Q, ?_⟩
  rw [xPsi, RatFunc.liftAlgHom_apply_div]
  simp only [Algebra.ofId_apply]
  have hQ0' : algebraMap (Polynomial L) (Func E) Q ≠ 0 := by rw [← xPhi_apply E Q]; exact hQ0
  rw [div_eq_iff hQ0', ← xPhi_apply E P, ← xPhi_apply E Q]
  exact hzv'.symm

/-- The conjugation acts on `y` by `y ↦ -y - eK`. -/
lemma negAlgEquiv_genY' (E : WeierstrassCurve L) :
    negAlgEquiv E (genY E) = - genY E - eK E := by
  rw [negAlgEquiv_genY, eK]
  refl_ring1

/-- The image of `L[X]` under `xPhi` lies in `L(x)`. -/
lemma xPhi_mem_range_xPsi (E : WeierstrassCurve L) (p : Polynomial L) :
    xPhi E p ∈ Set.range (xPsi E) :=
  ⟨algebraMap (Polynomial L) (RatFunc L) p, xPsi_apply_algebraMap E p⟩

lemma Ax_subset_range_xPsi (E : WeierstrassCurve L) :
    (Ax E : Set (Func E)) ⊆ Set.range (xPsi E) := by
  intro a ha
  rw [← xPhi_range] at ha
  obtain ⟨p, rfl⟩ := ha
  exact xPhi_mem_range_xPsi E p

lemma algebraMap_mem_range_xPsi (E : WeierstrassCurve L) (c : L) :
    algebraMap L (Func E) c ∈ Set.range (xPsi E) := by
  refine ⟨algebraMap (Polynomial L) (RatFunc L) (Polynomial.C c), ?_⟩
  rw [xPsi_apply_algebraMap, xPhi_apply, Polynomial.C_eq_algebraMap]
  exact (IsScalarTower.algebraMap_apply L (Polynomial L) (Func E) c).symm

lemma mem_range_xPsi_add (E : WeierstrassCurve L) {a b : Func E}
    (ha : a ∈ Set.range (xPsi E)) (hb : b ∈ Set.range (xPsi E)) :
    a + b ∈ Set.range (xPsi E) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x + y, map_add (xPsi E) x y⟩

lemma mem_range_xPsi_mul (E : WeierstrassCurve L) {a b : Func E}
    (ha : a ∈ Set.range (xPsi E)) (hb : b ∈ Set.range (xPsi E)) :
    a * b ∈ Set.range (xPsi E) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x * y, map_mul (xPsi E) x y⟩

lemma mem_range_xPsi_neg (E : WeierstrassCurve L) {a : Func E}
    (ha : a ∈ Set.range (xPsi E)) : -a ∈ Set.range (xPsi E) := by
  obtain ⟨x, rfl⟩ := ha
  exact ⟨-x, map_neg (xPsi E) x⟩

lemma mem_range_xPsi_sub (E : WeierstrassCurve L) {a b : Func E}
    (ha : a ∈ Set.range (xPsi E)) (hb : b ∈ Set.range (xPsi E)) :
    a - b ∈ Set.range (xPsi E) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x - y, map_sub (xPsi E) x y⟩

lemma mem_range_xPsi_pow (E : WeierstrassCurve L) {a : Func E}
    (ha : a ∈ Set.range (xPsi E)) (n : ℕ) : a ^ n ∈ Set.range (xPsi E) := by
  obtain ⟨x, rfl⟩ := ha
  exact ⟨x ^ n, map_pow (xPsi E) x n⟩

/-- A natural number, viewed in `L(E)`, is the image of a constant of `L`. -/
lemma natCast_eq_algebraMap (E : WeierstrassCurve L) (n : ℕ) :
    (n : Func E) = algebraMap L (Func E) (n : L) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, Nat.cast_succ, map_add, map_one, ih]

/-- `L[x] ⊆ L[x,y]`. -/
lemma Ax_le_affRing (E : WeierstrassCurve L) : Ax E ≤ affRing E := by
  rw [affRing_eq_adjoin L E, Ax]
  refine Algebra.adjoin_mono ?_
  intro a ha
  rw [Set.mem_singleton_iff] at ha
  subst ha
  exact Set.mem_insert _ _

lemma eK_mem_range_xPsi (E : WeierstrassCurve L) : eK E ∈ Set.range (xPsi E) :=
  Ax_subset_range_xPsi E (eK_mem E)

lemma cK_mem_range_xPsi (E : WeierstrassCurve L) : cK E ∈ Set.range (xPsi E) :=
  Ax_subset_range_xPsi E (cK_mem E)

lemma xPhi_linCoef (E : WeierstrassCurve L) : xPhi E (linCoef E) = eK E := by
  rw [xPhi_apply, linCoef, eK]
  simp [IsScalarTower.algebraMap_apply L (Polynomial L) (Func E), algebraMap_X_func]

lemma xPhi_cubCoef (E : WeierstrassCurve L) : xPhi E (cubCoef E) = cK E := by
  rw [xPhi_apply, cubCoef, cK]
  simp [IsScalarTower.algebraMap_apply L (Polynomial L) (Func E), algebraMap_X_func]

/-- `D = e² + 4c` is the image under `xPhi` of `linCoef² + 4 cubCoef`. -/
lemma xPhi_D (E : WeierstrassCurve L) :
    xPhi E (linCoef E ^ 2 + 4 * cubCoef E) = eK E ^ 2 + 4 * cK E := by
  simp only [map_add, map_mul, map_pow, map_ofNat, xPhi_linCoef, xPhi_cubCoef]

end Work.MotC2
