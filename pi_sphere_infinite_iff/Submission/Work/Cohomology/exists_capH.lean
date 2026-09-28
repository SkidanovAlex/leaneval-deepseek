import Mathlib
import Submission.Work.Cohomology.cap_d

/-!
# The cap product pairing `H^n(X) × H_{n+m}(X) → H_m(X)`

This file constructs the descent of the cap product of `Submission/Work/Cohomology/CapProduct.lean`
to homology, using the boundary formula `cap_d`:

* `genElt` — a generator (a simplex) of the singular chains, as an element of the chain module;
* `cap_gen_apply`, `capHom_add`, `capHom_smul`, `cap_zero` — elementary properties;
* `capHom_comp_d_of_cocycle` — for a cocycle, `cap (·) (m+1)` followed by the differential is
  `±` the differential followed by `cap (·) m`;
* `capZHom`, `capZ` — the cap product of a cocycle with a chain, landing on cycles;
* `capZHom_iCycles` — its value, `⟨σ, c⟩ ↦ cap γ c`;
* `capZHom_factor` — the case of a boundary chain, needed to descend to homology;
* `capHomH` — the descent to `H_{n+m} → H_m`, `capHfun` and `capH'` — the descent in the
  cohomological variable, and finally `exists_capH`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R] (X : SSet)

/-- The singular chain complex of `X` with coefficients in `R`. -/
abbrev chainC : ChainComplex (ModuleCat R) ℕ := X.chainComplex (ModuleCat.of R R)

/-- The singular cochain complex of `X` with coefficients in `R`. -/
abbrev cochainC : CochainComplex (ModuleCat R) ℕ := SSetCochainComplex R X

/-! ## Generators of the chain complex and the cap product on them -/

/-- The chain in the singular chain complex determined by a generator (a simplex). -/
def genElt {N : ℕ} (σ : X _⦋N⦌) : ↑((chainC R X).X N) :=
  (X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1

/-- The cap product of a cochain with a generator. -/
theorem cap_gen_apply {n m : ℕ} (α : Cochain R X n) (σ : X _⦋n+m⦌) :
    (capHom R X α m).hom (genElt R X σ) =
      genEval R X α (frontFace X n (n+m) (by omega) σ) • genElt R X (backFace X n m σ) := by
  rw [genElt, genElt, ← frontFace_proof_irrel n (n+m) _ (by omega) σ]
  exact cap_apply R X α σ

/-- The cap product is additive in the cochain. -/
theorem capHom_add {n m : ℕ} (α β : Cochain R X n) :
    capHom R X (α + β) m = capHom R X α m + capHom R X β m := by
  apply SSet.chainComplex_hom_ext
  intro σ
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add, LinearMap.add_apply]
  rw [← genElt]
  rw [cap_gen_apply, cap_gen_apply, cap_gen_apply, genEval_add, add_smul]

/-- The cap product is homogeneous in the cochain. -/
theorem capHom_smul {n m : ℕ} (r : R) (α : Cochain R X n) :
    capHom R X (r • α) m = r • capHom R X α m := by
  apply SSet.chainComplex_hom_ext
  intro σ
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_smul, LinearMap.smul_apply]
  rw [← genElt]
  rw [cap_gen_apply, cap_gen_apply, genEval_smul, smul_assoc]

/-- The cap product with the zero cochain vanishes. -/
theorem capHom_zero {n m : ℕ} : capHom R X (0 : Cochain R X n) m = 0 := by
  have h := capHom_smul R X (n := n) (m := m) (0 : R) (0 : Cochain R X n)
  simpa using h

/-- The cap product with the zero cochain vanishes. -/
theorem cap_zero {n m : ℕ} : cap R X (0 : Cochain R X n) m = 0 := by
  rw [cap, capHom_zero, ModuleCat.hom_zero]

/-! ## The boundary formula for a cocycle -/

/-- **Boundary formula for a cocycle.**  Composing the cap product with a cocycle of degree `n` and
target `m+1` with the differential is, up to the sign `(-1)^n`, the differential followed by the
cap product with target `m`. -/
theorem capHom_comp_d_of_cocycle {n m : ℕ} (γ : Cochain R X n)
    (hγ : cochainDiff R X γ = 0) :
    capHom R X γ (m+1) ≫ (chainC R X).d (m+1) m =
      (-1:R)^n • ((chainC R X).d (n+m+1) (n+m) ≫ capHom R X γ m) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_smul, LinearMap.smul_apply]
  rw [← cap, ← cap]
  rw [cap_d R X γ c, hγ, cap_zero, LinearMap.zero_apply, sub_zero]
  rfl

/-! ## The cap product of a cocycle with boundaries -/

/-- **The cap product of a coboundary with a cycle is a boundary.**  Evaluating the boundary
formula for a cocycle at a cycle. -/
theorem cap_coboundary {p m : ℕ} (β : Cochain R X p) (x : (chainC R X).X (p+(m+1)))
    (hx : ((chainC R X).d (p+(m+1)) (p+m)).hom x = 0) :
    cap R X (cochainDiff R X β) m ((capIdx p m) ▸ x) =
      -((-1:R)^p • ((chainC R X).d (m+1) m).hom (cap R X β (m+1) x)) := by
  have h := cap_d R X β x
  rw [hx] at h
  simp only [map_zero, zero_sub] at h
  rw [h, ← mul_smul, neg_one_pow_mul_self, one_smul, neg_neg]

/-! ## The cap product of a cocycle with a chain, landing on cycles -/

/-- The composite `cap (·) m` kills cycles: the well-definedness statement for `capZHom`. -/
theorem capZHom_d (n m : ℕ) (z : ↑((cochainC R X).cycles n)) :
    ((chainC R X).iCycles (n+m) ≫ capHom R X (((cochainC R X).iCycles n).hom z) m) ≫
      (chainC R X).d m ((ComplexShape.down ℕ).next m) = 0 := by
  cases m with
  | zero =>
    rw [show (ComplexShape.down ℕ).next 0 = 0 from
      ComplexShape.next_eq_self' (ComplexShape.down ℕ) 0 (by
        intro k hk
        have hk' : k + 1 = 0 := hk
        omega)]
    rw [show (chainC R X).d 0 0 = 0 from
      HomologicalComplex.shape (chainC R X) 0 0 (by
        intro h
        have h' : 0 + 1 = 0 := h
        omega)]
    exact comp_zero
  | succ k =>
    rw [show (ComplexShape.down ℕ).next (k+1) = k from
      ComplexShape.next_eq' (ComplexShape.down ℕ) (i := k+1) (j := k) rfl]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
    have hcyc : ((chainC R X).d (n+(k+1)) (n+k)).hom
        (((chainC R X).iCycles (n+(k+1))).hom y) = 0 := by
      have h := congrArg
        (fun (f : (chainC R X).cycles (n+(k+1)) ⟶ (chainC R X).X (n+k)) => f.hom y)
        (HomologicalComplex.iCycles_d (chainC R X) (n+(k+1)) (n+k))
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] using h
    rw [show ((chainC R X).d (k+1) k).hom
        ((capHom R X (((cochainC R X).iCycles n).hom z) (k+1)).hom
          (((chainC R X).iCycles (n+(k+1))).hom y))
        = (-1:R)^n • ((cap R X (((cochainC R X).iCycles n).hom z) k)
              (((chainC R X).d (n+(k+1)) (n+k)).hom
                (((chainC R X).iCycles (n+(k+1))).hom y))
            - (cap R X (cochainDiff R X (((cochainC R X).iCycles n).hom z)) k)
              ((capIdx n k) ▸ (((chainC R X).iCycles (n+(k+1))).hom y)))
        from cap_d R X (((cochainC R X).iCycles n).hom z)
          (((chainC R X).iCycles (n+(k+1))).hom y)]
    rw [hcyc, map_zero, cochainDiff_iCycles R X n z, cap_zero, LinearMap.zero_apply,
      sub_zero, smul_zero]

/-- **The cap product of a cocycle with a chain**, at the cycle level: the linear map
`cycles (n+m) → cycles m` induced by `c ↦ cap γ c`. -/
noncomputable def capZHom (n m : ℕ) (z : ↑((cochainC R X).cycles n)) :
    (chainC R X).cycles (n+m) ⟶ (chainC R X).cycles m :=
  (chainC R X).liftCycles
    ((chainC R X).iCycles (n+m) ≫ capHom R X (((cochainC R X).iCycles n).hom z) m)
    ((ComplexShape.down ℕ).next m) rfl (capZHom_d R X n m z)

/-- The computation rule for `capZHom`: on the underlying chains it is the cap product. -/
theorem capZHom_iCycles (n m : ℕ) (z : ↑((cochainC R X).cycles n)) :
    capZHom R X n m z ≫ (chainC R X).iCycles m =
      (chainC R X).iCycles (n+m) ≫ capHom R X (((cochainC R X).iCycles n).hom z) m := by
  rw [capZHom]
  exact HomologicalComplex.liftCycles_i (chainC R X) _ _ _ _

/-- `capZHom` is additive in the cocycle. -/
theorem capZHom_add (n m : ℕ) (z z' : ↑((cochainC R X).cycles n)) :
    capZHom R X n m (z + z') = capZHom R X n m z + capZHom R X n m z' := by
  apply (cancel_mono ((chainC R X).iCycles m)).mp
  rw [CategoryTheory.Preadditive.add_comp, capZHom_iCycles, capZHom_iCycles, capZHom_iCycles]
  rw [← CategoryTheory.Preadditive.comp_add, ← capHom_add]
  rw [show (((cochainC R X).iCycles n).hom (z + z'))
      = ((cochainC R X).iCycles n).hom z + ((cochainC R X).iCycles n).hom z' from
    map_add _ z z']

/-- `capZHom` is homogeneous in the cocycle. -/
theorem capZHom_smul (n m : ℕ) (r : R) (z : ↑((cochainC R X).cycles n)) :
    capZHom R X n m (r • z) = r • capZHom R X n m z := by
  apply (cancel_mono ((chainC R X).iCycles m)).mp
  calc capZHom R X n m (r • z) ≫ (chainC R X).iCycles m
      = (chainC R X).iCycles (n+m) ≫ capHom R X (((cochainC R X).iCycles n).hom (r • z)) m :=
        capZHom_iCycles R X n m (r • z)
    _ = (chainC R X).iCycles (n+m) ≫ capHom R X (r • ((cochainC R X).iCycles n).hom z) m := by
        rw [map_smul]
    _ = (chainC R X).iCycles (n+m)
          ≫ (r • capHom R X (((cochainC R X).iCycles n).hom z) m) := by
        rw [capHom_smul]
    _ = r • ((chainC R X).iCycles (n+m)
          ≫ capHom R X (((cochainC R X).iCycles n).hom z) m) :=
        CategoryTheory.Linear.comp_smul _ _ _ _ r _
    _ = r • (capZHom R X n m z ≫ (chainC R X).iCycles m) := by
        rw [capZHom_iCycles]
    _ = (r • capZHom R X n m z) ≫ (chainC R X).iCycles m :=
        (CategoryTheory.Linear.smul_comp _ _ _ r _ _).symm

/-- **The cap product of a cocycle with a chain**, as a linear map in the cocycle. -/
noncomputable def capZ (n m : ℕ) :
    ↑((cochainC R X).cycles n) →ₗ[R]
      ((chainC R X).cycles (n+m) →ₗ[R] (chainC R X).cycles m) where
  toFun z := (capZHom R X n m z).hom
  map_add' z z' := by rw [← ModuleCat.hom_add, capZHom_add]
  map_smul' r z := by
    simp only [RingHom.id_apply]
    rw [capZHom_smul, ModuleCat.hom_smul]

/-! ## The descent of the cap product in the homological variable -/

/-- The index identification `prev n = n - 1` for the cohomological shape. -/
theorem prev_up (n : ℕ) : (ComplexShape.up ℕ).prev n = n - 1 := by
  rcases n with _ | k
  · exact ComplexShape.prev_eq_self' (ComplexShape.up ℕ) 0 (by
      intro j hj
      have hj' : j + 1 = 0 := hj
      omega)
  · exact ComplexShape.prev_eq' (ComplexShape.up ℕ) (i := k+1) (j := k) rfl

/-- The index identification `prev n = n + 1` for the homological shape. -/
theorem prev_down (n : ℕ) : (ComplexShape.down ℕ).prev n = n + 1 :=
  ComplexShape.prev_eq' (ComplexShape.down ℕ) (i := n) (j := n+1) rfl

/-- `H_{n+m}` is the cokernel of the boundary map `cycles (n+m)`. -/
noncomputable def homCoker (n m : ℕ) :
    IsColimit (CokernelCofork.ofπ ((chainC R X).homologyπ (n+m))
      (HomologicalComplex.toCycles_comp_homologyπ (chainC R X) (n+m+1) (n+m))) :=
  (chainC R X).homologyIsCokernel (n+m+1) (n+m) (prev_down (n+m))

/-- **A chain which is a boundary is killed by the cap product with a cocycle.** -/
theorem capZHom_factor (n m : ℕ) (z : ↑((cochainC R X).cycles n)) :
    (chainC R X).toCycles (n+m+1) (n+m) ≫ capZHom R X n m z =
      ((-1:R)^n • capHom R X (((cochainC R X).iCycles n).hom z) (m+1)) ≫
        (chainC R X).toCycles (m+1) m := by
  apply (cancel_mono ((chainC R X).iCycles m)).mp
  calc (((chainC R X).toCycles (n+m+1) (n+m)) ≫ capZHom R X n m z) ≫ (chainC R X).iCycles m
      = (chainC R X).toCycles (n+m+1) (n+m)
          ≫ (capZHom R X n m z ≫ (chainC R X).iCycles m) := by rw [Category.assoc]
    _ = (chainC R X).toCycles (n+m+1) (n+m)
          ≫ ((chainC R X).iCycles (n+m)
              ≫ capHom R X (((cochainC R X).iCycles n).hom z) m) := by
        rw [capZHom_iCycles]
    _ = ((chainC R X).toCycles (n+m+1) (n+m) ≫ (chainC R X).iCycles (n+m))
          ≫ capHom R X (((cochainC R X).iCycles n).hom z) m := by rw [Category.assoc]
    _ = ((chainC R X).d (n+m+1) (n+m))
          ≫ capHom R X (((cochainC R X).iCycles n).hom z) m := by
        rw [HomologicalComplex.toCycles_i]
    _ = (-1:R)^n
          • (capHom R X (((cochainC R X).iCycles n).hom z) (m+1)
              ≫ (chainC R X).d (m+1) m) := by
        rw [capHom_comp_d_of_cocycle R X _ (cochainDiff_iCycles R X n z), smul_smul,
          neg_one_pow_mul_self, one_smul]
    _ = ((-1:R)^n • capHom R X (((cochainC R X).iCycles n).hom z) (m+1))
          ≫ (chainC R X).d (m+1) m :=
        (CategoryTheory.Linear.smul_comp _ _ _ _ _ _).symm
    _ = ((-1:R)^n • capHom R X (((cochainC R X).iCycles n).hom z) (m+1))
          ≫ ((chainC R X).toCycles (m+1) m ≫ (chainC R X).iCycles m) := by
        rw [HomologicalComplex.toCycles_i]
    _ = (((-1:R)^n • capHom R X (((cochainC R X).iCycles n).hom z) (m+1))
          ≫ (chainC R X).toCycles (m+1) m) ≫ (chainC R X).iCycles m := by
        rw [Category.assoc]

/-- **The descent of the cap product to homology in the homological variable.** -/
noncomputable def capHomH (n m : ℕ) (z : ↑((cochainC R X).cycles n)) :
    (chainC R X).homology (n+m) ⟶ (chainC R X).homology m :=
  (homCoker R X n m).desc
    (CokernelCofork.ofπ (capZHom R X n m z ≫ (chainC R X).homologyπ m) (by
      rw [← Category.assoc, capZHom_factor, Category.assoc,
        HomologicalComplex.toCycles_comp_homologyπ, comp_zero]))

/-- The computation rule for `capHomH`. -/
theorem homologyπ_comp_capHomH (n m : ℕ) (z : ↑((cochainC R X).cycles n)) :
    (chainC R X).homologyπ (n+m) ≫ capHomH R X n m z =
      capZHom R X n m z ≫ (chainC R X).homologyπ m :=
  Cofork.IsColimit.π_desc (homCoker R X n m)

/-- `capHomH` is additive in the cocycle. -/
theorem capHomH_add (n m : ℕ) (z z' : ↑((cochainC R X).cycles n)) :
    capHomH R X n m (z + z') = capHomH R X n m z + capHomH R X n m z' := by
  apply Cofork.IsColimit.hom_ext (homCoker R X n m)
  show (chainC R X).homologyπ (n+m) ≫ capHomH R X n m (z + z')
      = (chainC R X).homologyπ (n+m) ≫ capHomH R X n m z
        + (chainC R X).homologyπ (n+m) ≫ capHomH R X n m z'
  rw [homologyπ_comp_capHomH, homologyπ_comp_capHomH, homologyπ_comp_capHomH, capZHom_add,
    CategoryTheory.Preadditive.add_comp]

/-- `capHomH` is homogeneous in the cocycle. -/
theorem capHomH_smul (n m : ℕ) (r : R) (z : ↑((cochainC R X).cycles n)) :
    capHomH R X n m (r • z) = r • capHomH R X n m z := by
  apply Cofork.IsColimit.hom_ext (homCoker R X n m)
  show (chainC R X).homologyπ (n+m) ≫ capHomH R X n m (r • z)
      = r • ((chainC R X).homologyπ (n+m) ≫ capHomH R X n m z)
  rw [homologyπ_comp_capHomH, homologyπ_comp_capHomH, capZHom_smul,
    CategoryTheory.Linear.smul_comp]

/-- **The cap product with a cocycle, as a linear map into `H_{n+m} → H_m`.** -/
noncomputable def capHfun (n m : ℕ) :
    ↑((cochainC R X).cycles n) →ₗ[R]
      ((chainC R X).homology (n+m) →ₗ[R] (chainC R X).homology m) where
  toFun z := (capHomH R X n m z).hom
  map_add' z z' := by rw [← ModuleCat.hom_add, capHomH_add]
  map_smul' r z := by
    simp only [RingHom.id_apply]
    rw [capHomH_smul, ModuleCat.hom_smul]

/-! ## The cap product of a coboundary with a cycle -/

/-- A witness that the cap product of a coboundary `dβ` (of degree `p+1`) with a cycle of degree
`(p+1)+m` is a boundary in degree `m`. -/
noncomputable def capCobWitness (p m : ℕ) (β : Cochain R X p) :
    (chainC R X).cycles ((p+1)+m) ⟶ (chainC R X).X (m+1) :=
  (chainC R X).iCycles ((p+1)+m) ≫
    ((chainC R X).XIsoOfEq (capIdx p m).symm).hom ≫
      ((-((-1:R)^p)) • capHom R X β (m+1))

/-- The object transport of the chain complex, as a cast of elements. -/
theorem chain_XIsoOfEq_hom_apply {a b : ℕ} (h : a = b) (w : ↑((chainC R X).X a)) :
    ((chainC R X).XIsoOfEq h).hom.hom w = h ▸ w := by
  cases h; rfl

/-- A cast followed by the inverse cast is the identity. -/
theorem eqRec_self_symm {a b : ℕ} (h : a = b) (w : ↑((chainC R X).X b)) :
    h ▸ (h.symm ▸ w) = w := by
  cases h; rfl

/-- The defining property of `capCobWitness`. -/
theorem capCobWitness_spec (p m : ℕ) (β : Cochain R X p) :
    capCobWitness R X p m β ≫ (chainC R X).d (m+1) m =
      (chainC R X).iCycles ((p+1)+m) ≫ capHom R X (cochainDiff R X β) m := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  set z : ↑((chainC R X).X ((p+1)+m)) := ((chainC R X).iCycles ((p+1)+m)).hom y with hz
  set x : ↑((chainC R X).X (p+(m+1))) :=
    (((chainC R X).XIsoOfEq (capIdx p m).symm).hom).hom z with hx
  have hxz : ((capIdx p m) ▸ x) = z := by
    rw [hx, chain_XIsoOfEq_hom_apply]
    exact eqRec_self_symm R X (capIdx p m) z
  have hzc : ((chainC R X).d ((p+1)+m) (p+m)).hom z = 0 := by
    have h := congrArg
      (fun (f : (chainC R X).cycles ((p+1)+m) ⟶ (chainC R X).X (p+m)) => f.hom y)
      (HomologicalComplex.iCycles_d (chainC R X) ((p+1)+m) (p+m))
    simpa only [hz, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  have hdx : ((chainC R X).d (p+(m+1)) (p+m)).hom x = 0 := by
    have h2 : ((chainC R X).XIsoOfEq (capIdx p m).symm).hom
        ≫ (chainC R X).d (p+(m+1)) (p+m)
        = (chainC R X).d ((p+1)+m) (p+m) :=
      HomologicalComplex.XIsoOfEq_hom_comp_d (chainC R X) (capIdx p m).symm (p+m)
    have h3 := congrArg
      (fun (f : (chainC R X).X ((p+1)+m) ⟶ (chainC R X).X (p+m)) => f.hom z) h2
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h3
    rw [hx, h3, hzc]
  have key : (cap R X (cochainDiff R X β) m) ((capIdx p m) ▸ x)
      = -((-1:R)^p • ((chainC R X).d (m+1) m).hom (cap R X β (m+1) x)) :=
    cap_coboundary R X β x hdx
  rw [hxz] at key
  show ((chainC R X).d (m+1) m).hom ((-((-1:R)^p)) • ((capHom R X β (m+1)).hom x))
      = (cap R X (cochainDiff R X β) m) z
  rw [map_smul, key, neg_smul]
  rfl

/-- **The cap product of a coboundary with a cycle vanishes in homology.** -/
theorem capHomH_eq_zero_of_coboundary (p m : ℕ) (β : ↑((cochainC R X).X p)) :
    capHomH R X (p+1) m ((cochainC R X).toCycles p (p+1) β) = 0 := by
  have hζ : ((cochainC R X).iCycles (p+1)).hom ((cochainC R X).toCycles p (p+1) β)
      = cochainDiff R X β := by
    have h := congrArg (fun (f : (cochainC R X).X p ⟶ (cochainC R X).X (p+1)) => f.hom β)
      (HomologicalComplex.toCycles_i (cochainC R X) p (p+1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [h, SSetCochainComplex_d, ModuleCat.hom_ofHom]
    rfl
  have hΦ : capZHom R X (p+1) m ((cochainC R X).toCycles p (p+1) β)
      = capCobWitness R X p m β ≫ (chainC R X).toCycles (m+1) m := by
    apply (cancel_mono ((chainC R X).iCycles m)).mp
    rw [capZHom_iCycles, Category.assoc, HomologicalComplex.toCycles_i, capCobWitness_spec, hζ]
  have hzero : capZHom R X (p+1) m ((cochainC R X).toCycles p (p+1) β)
      ≫ (chainC R X).homologyπ m = 0 := by
    rw [hΦ, Category.assoc, HomologicalComplex.toCycles_comp_homologyπ, comp_zero]
  apply Cofork.IsColimit.hom_ext (homCoker R X (p+1) m)
  show (chainC R X).homologyπ (p+1+m)
      ≫ capHomH R X (p+1) m ((cochainC R X).toCycles p (p+1) β)
      = (chainC R X).homologyπ (p+1+m) ≫ 0
  rw [homologyπ_comp_capHomH, hzero, comp_zero]

/-- The composite of the boundary map `cycles n` with `capHfun` vanishes. -/
theorem toCycles_comp_capHfun (n m : ℕ) :
    (cochainC R X).toCycles (n-1) n ≫ ModuleCat.ofHom (capHfun R X n m) = 0 := by
  rcases n with _ | k
  · have h0 : (cochainC R X).toCycles (0-1) 0 = 0 := by
      apply (cancel_mono ((cochainC R X).iCycles 0)).mp
      rw [HomologicalComplex.toCycles_i, zero_comp]
      exact HomologicalComplex.shape (cochainC R X) 0 0 (by
        intro h
        have h' : 0 + 1 = 0 := h
        omega)
    rw [h0, zero_comp]
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro β
    show (capHomH R X (k+1) m ((cochainC R X).toCycles k (k+1) β)).hom = 0
    rw [capHomH_eq_zero_of_coboundary R X k m β, ModuleCat.hom_zero]

/-! ## The descent of the cap product in the cohomological variable -/

/-- **The descent of the cap product to cohomology.** -/
noncomputable def capH' (n m : ℕ) :
    (cochainC R X).homology n ⟶
      ModuleCat.of R ((chainC R X).homology (n+m) →ₗ[R] (chainC R X).homology m) :=
  ((cochainC R X).homologyIsCokernel (n-1) n (prev_up n)).desc
    (CokernelCofork.ofπ (ModuleCat.ofHom (capHfun R X n m)) (toCycles_comp_capHfun R X n m))

/-- The computation rule for `capH'`. -/
theorem homologyπ_comp_capH' (n m : ℕ) :
    (cochainC R X).homologyπ n ≫ capH' R X n m = ModuleCat.ofHom (capHfun R X n m) :=
  Cofork.IsColimit.π_desc ((cochainC R X).homologyIsCokernel (n-1) n (prev_up n))

/-- **The cap product pairing `H^n(X) × H_{n+m}(X) → H_m(X)`.** -/
theorem exists_capH (R : Type) [CommRing R] (X : SSet) :
    ∃ (capZ : ∀ n m : ℕ, (Work.Cohomology.SSetCochainComplex R X).cycles n →ₗ[R]
          ((X.chainComplex (ModuleCat.of R R)).cycles (n + m) →ₗ[R]
            (X.chainComplex (ModuleCat.of R R)).cycles m))
      (capH : ∀ n m : ℕ, (Work.Cohomology.SSetCochainComplex R X).homology n →ₗ[R]
          ((X.chainComplex (ModuleCat.of R R)).homology (n + m) →ₗ[R]
            (X.chainComplex (ModuleCat.of R R)).homology m)),
      (∀ (n m : ℕ) (z : (Work.Cohomology.SSetCochainComplex R X).cycles n)
          (c : (X.chainComplex (ModuleCat.of R R)).cycles (n + m)),
          (X.chainComplex (ModuleCat.of R R)).iCycles m (capZ n m z c) =
            Work.Cohomology.cap R X ((Work.Cohomology.SSetCochainComplex R X).iCycles n z) m
              ((X.chainComplex (ModuleCat.of R R)).iCycles (n + m) c))
      ∧ (∀ (n m : ℕ) (z : (Work.Cohomology.SSetCochainComplex R X).cycles n)
          (c : (X.chainComplex (ModuleCat.of R R)).cycles (n + m)),
          capH n m ((Work.Cohomology.SSetCochainComplex R X).homologyπ n z)
            ((X.chainComplex (ModuleCat.of R R)).homologyπ (n + m) c) =
          (X.chainComplex (ModuleCat.of R R)).homologyπ m (capZ n m z c)) := by
  refine ⟨fun n m => capZ R X n m, fun n m => (capH' R X n m).hom, ?_, ?_⟩
  · intro n m z c
    exact congrArg (fun (f : (chainC R X).cycles (n+m) ⟶ (chainC R X).X m) => f.hom c)
      (capZHom_iCycles R X n m z)
  · intro n m z c
    have hπ : (capH' R X n m).hom (((cochainC R X).homologyπ n).hom z)
        = (capHfun R X n m) z := by
      have h := congrArg
        (fun (f : (cochainC R X).cycles n ⟶ ModuleCat.of R
            ((chainC R X).homology (n+m) →ₗ[R] (chainC R X).homology m)) => f.hom z)
        (homologyπ_comp_capH' R X n m)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] using h
    rw [hπ]
    show (capHomH R X n m z).hom (((chainC R X).homologyπ (n+m)).hom c)
        = (((chainC R X).homologyπ m).hom.comp ((capZHom R X n m z).hom)) c
    rw [← ModuleCat.hom_comp, ← homologyπ_comp_capHomH, ModuleCat.hom_comp, LinearMap.comp_apply]


end

end Work.Cohomology
