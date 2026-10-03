/-
# Node N8: the torsion crux (Lemma 5.1′ of Jaikin-Zapirain--Linton)

This file sets up the vocabulary of the torsion case of the coherence theorem: the diagonal
action of a group algebra on a tensor product `V ⊗[K] M`, the abstract interface `TorsionData`
carrying the structural facts about the division closures `D H` of `K[H]` in the ring of
affiliated operators, and the Laurent datum `LaurentBase` attached to a surjection `φ : H ↠ ℤ`.

Main definitions:

* `Work.ORTorsion.gAct`, `diagGroupHom`, `diagRingHom`: the diagonal action, `x • (v ⊗ m)`
  for `x = Σ c_g g` is `Σ c_g ((g • v) ⊗ (g • m))`;
* `Work.ORTorsion.TorsionData`: `G`, `K`, the ambient `K`-algebra `U ⊇ K[G]`, the division
  closures `D H` of `K[H]` in `U`, semisimplicity of `D H`, local indicability of the quotient
  by the normal closure of the root `u`, and the Laurent data;
* `Work.ORTorsion.LaurentBase`: for `H ≤ G` and `φ : H ↠ ℤ` with kernel `N`, the subalgebra
  `R = Σ_{h ∈ H} D(N) h` with its `ℤ`-grading by `u = gen s` and the coordinate maps `coord k`,
  together with the common-denominator property for `D(H)`.

The interface fields are the inputs (I1)--(I4) of the lead's design (`N8_TORSION_LEAD.md` §1)
together with the structural consequences established in node N7: the semisimplicity of the
division closures and the Laurent/Ore decomposition.
-/
import Mathlib
import Submission.Work.ORLinnell.Basic
import Submission.Work.ORLocInd.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped TensorProduct

open Work.ORLocInd

open Subgroup

namespace Work.ORTorsion

variable {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Algebra K U]

/-! ## The diagonal action -/

/-- The group action underlying the `K[G]`-module structure on `V`, as a `K`-linear map. -/
noncomputable def gAct {K : Type*} [Field K] {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module K V] [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (g : G) : V →ₗ[K] V where
  toFun v := MonoidAlgebra.single g (1 : K) • v
  map_add' v w := smul_add _ _ _
  map_smul' k v := by
    show MonoidAlgebra.single g (1 : K) • (k • v) = k • (MonoidAlgebra.single g (1 : K) • v)
    exact (smul_comm k (MonoidAlgebra.single g (1 : K)) v).symm

theorem gAct_mul {K : Type*} [Field K] {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module K V] [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (g h : G) : (gAct (K := K) (g * h) : V →ₗ[K] V) = (gAct (K := K) g).comp (gAct (K := K) h) := by
  ext v
  show MonoidAlgebra.single (g * h) (1 : K) • v
      = MonoidAlgebra.single g (1 : K) • (MonoidAlgebra.single h (1 : K) • v)
  rw [← mul_smul, MonoidAlgebra.single_mul_single, one_mul]

theorem gAct_one {K : Type*} [Field K] {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module K V] [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V] :
    (gAct (K := K) (1 : G) : V →ₗ[K] V) = LinearMap.id := by
  ext v
  change MonoidAlgebra.single (1 : G) (1 : K) • v = v
  rw [show (MonoidAlgebra.single (1 : G) (1 : K) : MonoidAlgebra K G) = 1 from rfl, one_smul]

theorem mulLeft_mul' {K : Type*} [Field K] {M : Type*} [Ring M] [Algebra K M] (a b : M) :
    (LinearMap.mulLeft K (a * b) : M →ₗ[K] M) =
      (LinearMap.mulLeft K a).comp (LinearMap.mulLeft K b) := by
  ext m; simp

theorem mulLeft_one' {K : Type*} [Field K] {M : Type*} [Ring M] [Algebra K M] :
    (LinearMap.mulLeft K (1 : M) : M →ₗ[K] M) = LinearMap.id := by
  ext m; simp

/-- The diagonal action of a single element `h` of a group `H` mapping into `G` (acting on `V`)
and into the `K`-algebra `M`. -/
noncomputable def diagElem {K : Type*} [Field K] {G : Type*} [Group G] {M : Type*} [Ring M]
    [Algebra K M] {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Type*} [Group H] (jG : H →* G) (jM : H →* M) (h : H) : Module.End K (V ⊗[K] M) :=
  TensorProduct.map (gAct (K := K) (jG h)) (LinearMap.mulLeft K (jM h))

theorem diagElem_apply_tmul {K : Type*} [Field K] {G : Type*} [Group G] {M : Type*} [Ring M]
    [Algebra K M] {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Type*} [Group H] (jG : H →* G) (jM : H →* M) (h : H) (v : V) (m : M) :
    diagElem (K := K) (V := V) jG jM h (v ⊗ₜ[K] m) =
      ((MonoidAlgebra.single (jG h) (1 : K) : MonoidAlgebra K G) • v) ⊗ₜ[K] (jM h * m) := rfl

theorem diagElem_one {K : Type*} [Field K] {G : Type*} [Group G] {M : Type*} [Ring M]
    [Algebra K M] {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Type*} [Group H] (jG : H →* G) (jM : H →* M) :
    (diagElem (K := K) (V := V) jG jM (1 : H) : Module.End K (V ⊗[K] M)) = LinearMap.id := by
  rw [diagElem, map_one, map_one, gAct_one, mulLeft_one', TensorProduct.map_id]

theorem diagElem_mul {K : Type*} [Field K] {G : Type*} [Group G] {M : Type*} [Ring M]
    [Algebra K M] {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Type*} [Group H] (jG : H →* G) (jM : H →* M) (h h' : H) :
    (diagElem (K := K) (V := V) jG jM (h * h') : Module.End K (V ⊗[K] M)) =
      (diagElem (K := K) (V := V) jG jM h).comp (diagElem (K := K) (V := V) jG jM h') := by
  rw [diagElem, diagElem, diagElem, map_mul, map_mul, gAct_mul, mulLeft_mul',
    TensorProduct.map_comp]

/-- The diagonal action of the group `H` on `V ⊗[K] M`. -/
noncomputable def diagGroupHom {K : Type*} [Field K] {G : Type*} [Group G] {M : Type*} [Ring M]
    [Algebra K M] {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Type*} [Group H] (jG : H →* G) (jM : H →* M) : H →* Module.End K (V ⊗[K] M) where
  toFun := diagElem jG jM
  map_one' := diagElem_one jG jM
  map_mul' := diagElem_mul jG jM

/-- The diagonal action of `K[H]` on `V ⊗[K] M`. -/
noncomputable def diagRingHom {K : Type*} [Field K] {G : Type*} [Group G] {M : Type*} [Ring M]
    [Algebra K M] {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Type*} [Group H] (jG : H →* G) (jM : H →* M) :
    MonoidAlgebra K H →+* Module.End K (V ⊗[K] M) :=
  (MonoidAlgebra.lift K (Module.End K (V ⊗[K] M)) H (diagGroupHom jG jM)).toRingHom

theorem diagRingHom_single {K : Type*} [Field K] {G : Type*} [Group G] {M : Type*} [Ring M]
    [Algebra K M] {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Type*} [Group H] (jG : H →* G) (jM : H →* M) (h : H) :
    diagRingHom (K := K) (V := V) jG jM (MonoidAlgebra.single h (1 : K) : MonoidAlgebra K H)
      = diagGroupHom (K := K) (V := V) jG jM h := by
  show (MonoidAlgebra.lift K (Module.End K (V ⊗[K] M)) H (diagGroupHom jG jM))
      (MonoidAlgebra.single h (1 : K) : MonoidAlgebra K H) = diagGroupHom jG jM h
  rw [MonoidAlgebra.lift_single, one_smul]

/-- The diagonal action of a general monomial `single h c`: the ring homomorphism `diagRingHom`
sends `single h c` to `c` times the diagonal action of the group element `h`. -/
theorem diagRingHom_single_coeff {K : Type*} [Field K] {G : Type*} [Group G] {M : Type*}
    [Ring M] [Algebra K M] {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Type*} [Group H] (jG : H →* G) (jM : H →* M) (h : H) (c : K) :
    diagRingHom (K := K) (V := V) jG jM (MonoidAlgebra.single h c)
      = c • diagGroupHom (K := K) (V := V) jG jM h := by
  show (MonoidAlgebra.lift K (Module.End K (V ⊗[K] M)) H (diagGroupHom jG jM))
      (MonoidAlgebra.single h c) = c • diagGroupHom jG jM h
  rw [MonoidAlgebra.lift_single]

/-- Evaluation form of `diagRingHom_single_coeff`. -/
theorem diagRingHom_single_coeff_apply {K : Type*} [Field K] {G : Type*} [Group G] {M : Type*}
    [Ring M] [Algebra K M] {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Type*} [Group H] (jG : H →* G) (jM : H →* M) (h : H) (c : K) (m : V ⊗[K] M) :
    diagRingHom (K := K) (V := V) jG jM (MonoidAlgebra.single h c) m
      = c • (diagElem (K := K) (V := V) jG jM h m) := by
  rw [diagRingHom_single_coeff, LinearMap.smul_apply]
  rfl

/-- The monomial `single h c` with `c ≠ 0` acts invertibly (diagonally) on `V ⊗[K] M`, with
explicit inverse given by the action of `single h⁻¹ c⁻¹`. -/
theorem single_inv_diag_single_diag {K : Type*} [Field K] {G : Type*} [Group G] {M : Type*}
    [Ring M] [Algebra K M] {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Type*} [Group H] (jG : H →* G) (jM : H →* M) (h : H) {c : K} (hc : c ≠ 0)
    (m : V ⊗[K] M) :
    diagRingHom (K := K) (V := V) jG jM (MonoidAlgebra.single h⁻¹ c⁻¹)
      (diagRingHom (K := K) (V := V) jG jM (MonoidAlgebra.single h c) m) = m := by
  rw [diagRingHom_single_coeff_apply, diagRingHom_single_coeff_apply, LinearMap.map_smul,
    ← mul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [show diagElem (K := K) (V := V) jG jM h⁻¹ (diagElem (K := K) (V := V) jG jM h m)
      = ((diagElem (K := K) (V := V) jG jM h⁻¹).comp
          (diagElem (K := K) (V := V) jG jM h)) m from rfl,
    ← diagElem_mul, inv_mul_cancel, diagElem_one]
  rfl

/-! ## The interface -/

/-- **The Laurent datum.**  Let `H ≤ G` and let `φ : H →* Multiplicative ℤ` be a surjection with
kernel `N`.  This structure records the subalgebra `R = Σ_{h ∈ H} D(N) h` of `U` together with

* the `ℤ`-grading: right multiplication by the powers of `u = gen s`, where `s ∈ H` generates
  the quotient `H/N ≅ ℤ` (`φ s = ofAdd 1`);
* the coordinate maps `coord k : R → D(N)` extracting the coefficient of `u ^ k`, with the
  shift rule `coord i (y * u ^ k) = coord (i - k) y`, the base rule on `D(N) u ^ k`, and the
  reconstruction `Σ_i (coord i y) u ^ i = y`;
* the common-denominator property: every finite family in `D(H)` has a right common denominator
  which is a unit of `D(H)` and lies in `R` (this is the content of L1+L3 of the design). -/
structure LaurentBase (K : Type*) [Field K] (U : Type*) [Ring U] [Algebra K U]
    (G : Type*) [Group G] (gen : G →* Uˣ) (D : Subgroup G → Subalgebra K U)
    (H : Subgroup G) (φ : H →* Multiplicative ℤ) where
  /-- the kernel of `φ`, as a subgroup of `G` -/
  N : Subgroup G
  /-- `N` is the kernel of `φ : H ↠ ℤ` -/
  hN : N = φ.ker.map H.subtype
  /-- a generator of the infinite cyclic quotient `H/N` -/
  s : H
  /-- the generator is mapped to `1 ∈ ℤ` -/
  hs : φ s = Multiplicative.ofAdd 1
  /-- the powers of the generator have the expected degree -/
  hs_zpow : ∀ k : ℤ, φ (s ^ k) = Multiplicative.ofAdd k
  /-- the Laurent subalgebra `R = Σ_{h ∈ H} D(N) h` -/
  R : Subalgebra K U
  /-- `D(N) ⊆ R` -/
  DN_le_R : D N ≤ R
  /-- `R ⊆ D(H)` -/
  R_le_DH : R ≤ D H
  /-- `R` contains the image of `H` -/
  gen_mem_R : ∀ h : H, (gen (h : G) : U) ∈ R
  /-- right multiplication by the powers of `u = gen s`, as a `K`-linear map on `R` -/
  rightMulU : ℤ → (↥R →ₗ[K] ↥R)
  /-- `rightMulU j` is multiplication by `u ^ j` -/
  rightMulU_coe : ∀ (j : ℤ) (y : ↥R),
    ((rightMulU j y : ↥R) : U) = (y : U) * ((((gen (s : G) : Uˣ)) ^ j : Uˣ) : U)
  /-- `rightMulU (-j)` is a left inverse of `rightMulU j` -/
  rightMulU_neg : ∀ (j : ℤ) (y : ↥R), rightMulU (-j) (rightMulU j y) = y
  /-- the coordinate (degree) maps -/
  coord : ℤ → (↥R →ₗ[K] ↥(D N))
  /-- shifting the degree -/
  coord_shift : ∀ (i k : ℤ) (y : ↥R), coord i (rightMulU k y) = coord (i - k) y
  /-- the base rule: `coord` extracts the coefficient of `u ^ k` -/
  coord_base : ∀ (i k : ℤ) (d : ↥(D N)),
    coord i (rightMulU k ⟨(d : U), DN_le_R d.2⟩) = if i = k then d else 0
  /-- reconstruction of an element of `R` from its coordinates -/
  coord_expand : ∀ y : ↥R, ∃ S : Finset ℤ,
    ∑ i ∈ S, rightMulU i ⟨(coord i y : U), DN_le_R (coord i y).2⟩ = y
  /-- common right denominators in `R`, which are units of `D(H)` -/
  denom : ∀ (n : ℕ) (x : Fin n → ↥(D H)), ∃ t : ↥(D H), t ≠ 0 ∧ IsUnit t ∧
    ∀ k, ((x k * t : ↥(D H)) : U) ∈ R

/-- **The torsion setting for node N8.**  The ambient `K`-algebra `U` is the ring of affiliated
operators `U(G)` of the paper, `gen : G →* Uˣ` is the image of `K[G] ⊆ U`, and `D H` is the
division closure of `K[H]` in `U`.

The fields are the inputs of the design:

* (I1) `independence` — Linnell independence (node N5);
* (I2) `conjugation` — conjugation carries `D H` to `D (gHg⁻¹)`;
* (I3) `quotient_locallyIndicable` — `G ⧸ ⟨⟨u⟩⟩` is locally indicable (node N4) for the root `u`
  of the one-relator presentation `G = ⟨X | u ^ l⟩`;
* (I4)/(N7) `semisimple` — every division closure is semisimple Artinian in characteristic zero;
* (N7) `laurent` — the Laurent/Ore decomposition of `Σ_{h ∈ H} D(N) h` used by Lemma 5.1′. -/
structure TorsionData (K : Type*) [Field K] (G : Type*) [Group G] (U : Type*) [Ring U]
    [Algebra K U] where
  /-- the image of `G` in the units of `U` -/
  gen : G →* Uˣ
  /-- the division closure of `K[H]` in `U` -/
  D : Subgroup G → Subalgebra K U
  /-- `D H` contains the image of `H` -/
  gen_mem : ∀ (H : Subgroup G) (h : H), (gen (h : G) : U) ∈ D H
  /-- `D` is monotone -/
  D_mono : ∀ {H₁ H₂ : Subgroup G}, H₁ ≤ H₂ → D H₁ ≤ D H₂
  /-- `D H` is division closed in `U` -/
  isDivisionClosed : ∀ H : Subgroup G, IsDivisionClosed (D H).toSubring
  /-- `D H` is the smallest division closed subalgebra containing the image of `H` -/
  minimal : ∀ (H : Subgroup G) (A : Subalgebra K U),
    (∀ h : H, (gen (h : G) : U) ∈ A) → IsDivisionClosed A.toSubring → D H ≤ A
  /-- **(I1) Linnell independence**, in the *right*-coset convention: elements of `U` whose group
  parts `gen (g i)` lie in pairwise distinct **right** cosets `H (g i)` of `H` — i.e.
  `(g i) * (g j)⁻¹ ∈ H` implies `i = j` — are linearly independent over `D H` with the
  coefficients on the **left**.  This is the convention of
  `Work.ORLinnell.LinnellDatum.independence`; the previous (left-coset) form was false, see
  `OR_REMAINING_LEAD.md` (V2). -/
  independence : ∀ (H : Subgroup G) (n : ℕ) (g : Fin n → G),
    (∀ i j, (g i) * (g j)⁻¹ ∈ H → i = j) → ∀ a : Fin n → U,
    (∀ i, a i ∈ D H) → (∑ i, a i * (gen (g i) : U)) = 0 → ∀ i, a i = 0
  /-- **(I2) conjugation** -/
  conjugation : ∀ (g : G) (H : Subgroup G) (x : U), x ∈ D H →
    (gen g : U) * x * ↑((gen g)⁻¹) ∈ D (H.map (MulAut.conj g))
  /-- **(N7)** every division closure is semisimple Artinian -/
  semisimple : ∀ H : Subgroup G, IsSemisimpleRing ↥(D H)
  /-- the root `u` of the one-relator presentation `G = ⟨X | u ^ l⟩` -/
  u : G
  /-- **(I3)** the quotient `G ⧸ ⟨⟨u⟩⟩` is locally indicable -/
  quotient_locallyIndicable : Work.ORLocInd.Group.LocallyIndicable (G ⧸ normalClosure {u})
  /-- **(N7)** the Laurent/Ore datum for every `ℤ`-quotient of a subgroup -/
  laurent : ∀ (H : Subgroup G) (φ : H →* Multiplicative ℤ), Function.Surjective φ →
    LaurentBase K U G gen D H φ

/-! ## Basic API for the interface -/

namespace TorsionData

variable {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Algebra K U]
variable (L : TorsionData K G U)

/-- The image of `H` in `↥(D H)`. -/
noncomputable def genD (H : Subgroup G) : H →* ↥(L.D H) where
  toFun h := ⟨(L.gen (h : G) : U), L.gen_mem H h⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

/-- The `K`-algebra map `K[H] →+* ↥(D H)`. -/
noncomputable def algHomD (H : Subgroup G) : MonoidAlgebra K H →ₐ[K] ↥(L.D H) :=
  MonoidAlgebra.lift K ↥(L.D H) H (L.genD H)

@[simp] theorem algHomD_single (H : Subgroup G) (h : H) :
    algHomD L H (MonoidAlgebra.single h (1 : K) : MonoidAlgebra K H) = L.genD H h := by
  rw [algHomD, MonoidAlgebra.lift_single, one_smul]

/-- The `K[H]`-module structure on `↥(D H)` by left multiplication. -/
noncomputable instance instModuleD (H : Subgroup G) : Module (MonoidAlgebra K H) ↥(L.D H) :=
  Module.compHom _ (L.algHomD H).toRingHom

/-- The image of `G` in `↥(D ⊤)`. -/
noncomputable def genTop : G →* ↥(L.D ⊤) where
  toFun g := ⟨(L.gen g : U), L.gen_mem ⊤ ⟨g, trivial⟩⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

/-- The `SMul` underlying the diagonal `K[H]`-action on `V ⊗[K] ↥(D H)`, at high priority so
that it takes precedence over `TensorProduct.leftHasSMul`.  It is definitionally the scalar
multiplication of `instDiagD`. -/
noncomputable instance (priority := 2000) instDiagDSmul (H : Subgroup G) (V : Type*)
    [AddCommGroup V] [Module K V] [Module (MonoidAlgebra K G) V]
    [IsScalarTower K (MonoidAlgebra K G) V] :
    SMul (MonoidAlgebra K H) (V ⊗[K] ↥(L.D H)) where
  smul x m := diagRingHom (K := K) (V := V) H.subtype (L.genD H) x m

@[simp] theorem instDiagDSmul_apply (H : Subgroup G) (V : Type*) [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (x : MonoidAlgebra K H) (m : V ⊗[K] ↥(L.D H)) :
    x • m = diagRingHom (K := K) (V := V) H.subtype (L.genD H) x m := rfl

/-- The `instDiagDSmul` action is multiplicative in the scalar.  Stated separately from the
`Module` instance `instDiagD` because `Module`-level lemmas such as `mul_smul` may resolve to a
different (tensor-product) module structure. -/
theorem instDiagDSmul_mul (H : Subgroup G) (V : Type*) [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (x y : MonoidAlgebra K H) (m : V ⊗[K] ↥(L.D H)) :
    x • (y • m) = (x * y) • m := by
  rw [instDiagDSmul_apply (L := L) H V, instDiagDSmul_apply (L := L) H V,
    instDiagDSmul_apply (L := L) H V, map_mul]
  rfl

/-- The `instDiagDSmul` action of `1` is the identity. -/
theorem instDiagDSmul_one (H : Subgroup G) (V : Type*) [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (m : V ⊗[K] ↥(L.D H)) :
    (1 : MonoidAlgebra K H) • m = m := by
  rw [instDiagDSmul_apply (L := L) H V, map_one]
  rfl

/-- The diagonal `K[H]`-module structure on `V ⊗[K] ↥(D H)`. -/
noncomputable instance instDiagD (H : Subgroup G) (V : Type*) [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V] :
    Module (MonoidAlgebra K H) (V ⊗[K] ↥(L.D H)) := 
  { instDiagDSmul (L := L) H V with
    one_smul := fun m => by rw [instDiagDSmul_apply (L := L) H V, map_one]; rfl
    mul_smul := fun x y m => by rw [instDiagDSmul_apply (L := L) H V, instDiagDSmul_apply (L := L) H V,
      instDiagDSmul_apply (L := L) H V, map_mul]; rfl
    smul_zero := fun x => by rw [instDiagDSmul_apply (L := L) H V, map_zero]
    smul_add := fun x m n => by rw [instDiagDSmul_apply (L := L) H V, instDiagDSmul_apply (L := L) H V,
      instDiagDSmul_apply (L := L) H V, map_add]
    add_smul := fun x y m => by rw [instDiagDSmul_apply (L := L) H V, instDiagDSmul_apply (L := L) H V,
      instDiagDSmul_apply (L := L) H V, map_add]; rfl
    zero_smul := fun m => by rw [instDiagDSmul_apply (L := L) H V, map_zero]; rfl }


/-- The `SMul` underlying the diagonal `K[N]`-action on `V ⊗[K] ↥(D N)`. -/
noncomputable instance (priority := 2000) instDiagDNSmul (N : Subgroup G) (V : Type*)
    [AddCommGroup V] [Module K V] [Module (MonoidAlgebra K G) V]
    [IsScalarTower K (MonoidAlgebra K G) V] :
    SMul (MonoidAlgebra K N) (V ⊗[K] ↥(L.D N)) where
  smul x m := diagRingHom (K := K) (V := V) N.subtype (L.genD N) x m

@[simp] theorem instDiagDNSmul_apply (N : Subgroup G) (V : Type*) [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (x : MonoidAlgebra K N) (m : V ⊗[K] ↥(L.D N)) :
    x • m = diagRingHom (K := K) (V := V) N.subtype (L.genD N) x m := rfl

/-- The `instDiagDNSmul` action is multiplicative in the scalar. -/
theorem instDiagDNSmul_mul (N : Subgroup G) (V : Type*) [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (x y : MonoidAlgebra K N) (m : V ⊗[K] ↥(L.D N)) :
    x • (y • m) = (x * y) • m := by
  rw [instDiagDNSmul_apply (L := L) N V, instDiagDNSmul_apply (L := L) N V,
    instDiagDNSmul_apply (L := L) N V, map_mul]
  rfl

/-- The diagonal `K[N]`-module structure on `V ⊗[K] ↥(D N)`. -/
noncomputable instance instDiagDN (N : Subgroup G) (V : Type*) [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V] :
    Module (MonoidAlgebra K N) (V ⊗[K] ↥(L.D N)) := 
  { instDiagDNSmul (L := L) N V with
    one_smul := fun m => by rw [instDiagDNSmul_apply (L := L) N V, map_one]; rfl
    mul_smul := fun x y m => by rw [instDiagDNSmul_apply (L := L) N V, instDiagDNSmul_apply (L := L) N V,
      instDiagDNSmul_apply (L := L) N V, map_mul]; rfl
    smul_zero := fun x => by rw [instDiagDNSmul_apply (L := L) N V, map_zero]
    smul_add := fun x m n => by rw [instDiagDNSmul_apply (L := L) N V, instDiagDNSmul_apply (L := L) N V,
      instDiagDNSmul_apply (L := L) N V, map_add]
    add_smul := fun x y m => by rw [instDiagDNSmul_apply (L := L) N V, instDiagDNSmul_apply (L := L) N V,
      instDiagDNSmul_apply (L := L) N V, map_add]; rfl
    zero_smul := fun m => by rw [instDiagDNSmul_apply (L := L) N V, map_zero]; rfl }


/-- The `SMul` underlying the diagonal `K[G]`-action on `V ⊗[K] ↥(D ⊤)`, at high priority so
that it takes precedence over `TensorProduct.leftHasSMul`.  It is definitionally the scalar
multiplication of `instDiagTop`. -/
noncomputable instance (priority := 2000) instDiagTopSmul (V : Type*) [AddCommGroup V]
    [Module K V] [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V] :
    SMul (MonoidAlgebra K G) (V ⊗[K] ↥(L.D ⊤)) where
  smul x m := diagRingHom (K := K) (V := V) (MonoidHom.id G) L.genTop x m

@[simp] theorem instDiagTopSmul_apply (V : Type*) [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (x : MonoidAlgebra K G) (m : V ⊗[K] ↥(L.D ⊤)) :
    x • m = diagRingHom (K := K) (V := V) (MonoidHom.id G) L.genTop x m := rfl

/-- The `instDiagTopSmul` action is multiplicative in the scalar.  Stated separately from the
`Module` instance `instDiagTop` because `Module`-level lemmas such as `mul_smul` may resolve to
Mathlib's tensor-product module structure `TensorProduct.leftModule` instead. -/
theorem instDiagTopSmul_mul (V : Type*) [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (x y : MonoidAlgebra K G) (m : V ⊗[K] ↥(L.D ⊤)) :
    x • (y • m) = (x * y) • m := by
  rw [instDiagTopSmul_apply (L := L) V, instDiagTopSmul_apply (L := L) V,
    instDiagTopSmul_apply (L := L) V, map_mul]
  rfl

/-- The `instDiagTopSmul` action of `1` is the identity. -/
theorem instDiagTopSmul_one (V : Type*) [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (m : V ⊗[K] ↥(L.D ⊤)) :
    (1 : MonoidAlgebra K G) • m = m := by
  rw [instDiagTopSmul_apply (L := L) V, map_one]
  rfl

/-- The diagonal `K[G]`-module structure on `V ⊗[K] ↥(D ⊤)`. -/
noncomputable instance instDiagTop (V : Type*) [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V] :
    Module (MonoidAlgebra K G) (V ⊗[K] ↥(L.D ⊤)) := 
  { instDiagTopSmul (L := L) V with
    one_smul := fun m => by rw [instDiagTopSmul_apply (L := L) V, map_one]; rfl
    mul_smul := fun x y m => by rw [instDiagTopSmul_apply (L := L) V, instDiagTopSmul_apply (L := L) V,
      instDiagTopSmul_apply (L := L) V, map_mul]; rfl
    smul_zero := fun x => by rw [instDiagTopSmul_apply (L := L) V, map_zero]
    smul_add := fun x m n => by rw [instDiagTopSmul_apply (L := L) V, instDiagTopSmul_apply (L := L) V,
      instDiagTopSmul_apply (L := L) V, map_add]
    add_smul := fun x y m => by rw [instDiagTopSmul_apply (L := L) V, instDiagTopSmul_apply (L := L) V,
      instDiagTopSmul_apply (L := L) V, map_add]; rfl
    zero_smul := fun m => by rw [instDiagTopSmul_apply (L := L) V, map_zero]; rfl }

end TorsionData

/-! ## Degree data for an element of `K[H]` -/

section Degree

variable {H H' : Subgroup G}

/-- The algebra map `K[H] →ₐ[K] K[G]` induced by the inclusion `H ≤ G`. -/
noncomputable def mapToG (H : Subgroup G) : MonoidAlgebra K H →ₐ[K] MonoidAlgebra K G :=
  MonoidAlgebra.lift K (MonoidAlgebra K G) H
    { toFun := fun h => MonoidAlgebra.single (h : G) (1 : K)
      map_one' := rfl
      map_mul' := by
        intro a b
        rw [MonoidAlgebra.single_mul_single, mul_one]
        rfl }

@[simp] theorem mapToG_single (H : Subgroup G) (h : H) :
    mapToG (K := K) (G := G) H (MonoidAlgebra.single h (1 : K) : MonoidAlgebra K H)
      = MonoidAlgebra.single (h : G) (1 : K) := by
  rw [mapToG, MonoidAlgebra.lift_single, one_smul]
  rfl

@[simp] theorem mapToG_one (H : Subgroup G) : mapToG (K := K) (G := G) H 1 = 1 := map_one _

/-- The algebra map `K[H] →ₐ[K] K[H']` induced by a subgroup inclusion. -/
noncomputable def mapSubAlg (h : H ≤ H') : MonoidAlgebra K H →ₐ[K] MonoidAlgebra K H' :=
  MonoidAlgebra.lift K (MonoidAlgebra K H') H
    { toFun := fun k => MonoidAlgebra.single ⟨(k : G), h k.2⟩ (1 : K)
      map_one' := rfl
      map_mul' := by
        intro a b
        rw [MonoidAlgebra.single_mul_single, mul_one]
        rfl }

/-- The degree of `h : H`, i.e. the integer `b` with `φ h = ofAdd b`. -/
def deg (φ : H →* Multiplicative ℤ) (h : H) : ℤ := Multiplicative.toAdd (φ h)

theorem deg_zpow {φ : H →* Multiplicative ℤ} {s : H}
    (hs : ∀ k : ℤ, φ (s ^ k) = Multiplicative.ofAdd k) (b : ℤ) : deg φ (s ^ b) = b := by
  simp [deg, hs b]

theorem deg_apply (φ : H →* Multiplicative ℤ) (h : H) :
    φ h = Multiplicative.ofAdd (deg φ h) := by
  simp [deg]

/-- The part of `x : K[H]` of degree `b`. -/
noncomputable def degPart (φ : H →* Multiplicative ℤ) (b : ℤ) (x : MonoidAlgebra K H) :
    MonoidAlgebra K H :=
  MonoidAlgebra.ofCoeff (∑ h ∈ x.coeff.support,
    if φ h = Multiplicative.ofAdd b then Finsupp.single h (x.coeff h) else 0)

end Degree

/-! ## The tensor-level grading maps of the Laurent datum -/

namespace LaurentBase

variable {gen : G →* Uˣ} {D : Subgroup G → Subalgebra K U} {H : Subgroup G}
  {φ : H →* Multiplicative ℤ}

/-- An element of `φ.ker` is an element of `Lb.N` (via the field `hN`). -/
theorem mem_N_of_mem_ker (Lb : LaurentBase K U G gen D H φ) {h : H} (hh : h ∈ φ.ker) :
    (h : G) ∈ Lb.N := by
  rw [Lb.hN]
  exact Subgroup.mem_map.mpr ⟨h, hh, rfl⟩

/-- The kernel `N` is contained in `H`. -/
theorem N_le_H (Lb : LaurentBase K U G gen D H φ) : Lb.N ≤ H := by
  intro x hx
  rw [Lb.hN] at hx
  obtain ⟨y, -, hy⟩ := Subgroup.mem_map.mp hx
  exact hy ▸ y.2

theorem mem_ker_mul_zpow (Lb : LaurentBase K U G gen D H φ) {b : ℤ} {h : H}
    (hh : φ h = Multiplicative.ofAdd b) : h * Lb.s ^ (-b) ∈ φ.ker := by
  rw [MonoidHom.mem_ker, map_mul, Lb.hs_zpow, hh, ← ofAdd_add]
  simp

/-- The degree-`b` coefficient of `x : K[H]`, as an element of `K[N]`, `N = ker φ`. -/
noncomputable def degCoeff (Lb : LaurentBase K U G gen D H φ) (b : ℤ)
    (x : MonoidAlgebra K H) : MonoidAlgebra K ↥Lb.N :=
  MonoidAlgebra.ofCoeff (∑ h ∈ x.coeff.support,
    if hh : φ h = Multiplicative.ofAdd b then
      Finsupp.single ⟨(h * Lb.s ^ (-b) : H), Lb.mem_N_of_mem_ker (Lb.mem_ker_mul_zpow hh)⟩
        (x.coeff h)
    else 0)

/-- The image of `H` in `↥R`. -/
noncomputable def genR (Lb : LaurentBase K U G gen D H φ) : H →* ↥Lb.R where
  toFun h := ⟨(gen (h : G) : U), Lb.gen_mem_R h⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

/-- The `K`-algebra map `K[H] →+* ↥R`. -/
noncomputable def algHomR (Lb : LaurentBase K U G gen D H φ) : MonoidAlgebra K H →ₐ[K] ↥Lb.R :=
  MonoidAlgebra.lift K ↥Lb.R H Lb.genR

/-- The `K[H]`-module structure on `↥R` by left multiplication. -/
noncomputable instance instModuleR (Lb : LaurentBase K U G gen D H φ) :
    Module (MonoidAlgebra K H) ↥Lb.R :=
  Module.compHom _ (Lb.algHomR).toRingHom

/-- The `SMul` underlying the diagonal `K[H]`-action on `V ⊗[K] ↥R`, at high priority. -/
noncomputable instance (priority := 2000) instDiagRSmul (Lb : LaurentBase K U G gen D H φ)
    (V : Type*) [AddCommGroup V] [Module K V] [Module (MonoidAlgebra K G) V]
    [IsScalarTower K (MonoidAlgebra K G) V] :
    SMul (MonoidAlgebra K H) (V ⊗[K] ↥Lb.R) where
  smul x m := diagRingHom (K := K) (V := V) H.subtype Lb.genR x m

@[simp] theorem instDiagRSmul_apply (Lb : LaurentBase K U G gen D H φ) (V : Type*)
    [AddCommGroup V] [Module K V] [Module (MonoidAlgebra K G) V]
    [IsScalarTower K (MonoidAlgebra K G) V] (x : MonoidAlgebra K H) (m : V ⊗[K] ↥Lb.R) :
    x • m = diagRingHom (K := K) (V := V) H.subtype Lb.genR x m := rfl

/-- The `instDiagRSmul` action is multiplicative in the scalar. -/
theorem instDiagRSmul_mul (Lb : LaurentBase K U G gen D H φ) (V : Type*) [AddCommGroup V]
    [Module K V] [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (x y : MonoidAlgebra K H) (m : V ⊗[K] ↥Lb.R) :
    x • (y • m) = (x * y) • m := by
  rw [instDiagRSmul_apply (Lb := Lb) V, instDiagRSmul_apply (Lb := Lb) V,
    instDiagRSmul_apply (Lb := Lb) V, map_mul]
  rfl

/-- The diagonal `K[H]`-module structure on `V ⊗[K] ↥R`. -/
noncomputable instance instDiagR (Lb : LaurentBase K U G gen D H φ) (V : Type*) [AddCommGroup V]
    [Module K V] [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V] :
    Module (MonoidAlgebra K H) (V ⊗[K] ↥Lb.R) :=
  Module.compHom _ (diagRingHom (K := K) (V := V) H.subtype Lb.genR)


/-- `rightMulU` is injective. -/
theorem rightMulU_injective (Lb : LaurentBase K U G gen D H φ) (j : ℤ) :
    Function.Injective (Lb.rightMulU j) := by
  intro y y' h
  have h2 := congrArg (Lb.rightMulU (-j)) h
  rwa [Lb.rightMulU_neg, Lb.rightMulU_neg] at h2

/-- The inclusion `V ⊗[K] D(N) → V ⊗[K] R`. -/
noncomputable def inclDN (Lb : LaurentBase K U G gen D H φ) {V : Type*} [AddCommGroup V]
    [Module K V] : V ⊗[K] ↥(D Lb.N) →ₗ[K] V ⊗[K] ↥Lb.R :=
  TensorProduct.map LinearMap.id (Subalgebra.inclusion Lb.DN_le_R).toLinearMap

/-- Right multiplication by `u ^ k` on `V ⊗[K] R`. -/
noncomputable def Tm (Lb : LaurentBase K U G gen D H φ) {V : Type*} [AddCommGroup V]
    [Module K V] (k : ℤ) : V ⊗[K] ↥Lb.R →ₗ[K] V ⊗[K] ↥Lb.R :=
  TensorProduct.map LinearMap.id (Lb.rightMulU k)

/-- The degree-`k` coordinate map `V ⊗[K] R → V ⊗[K] D(N)`. -/
noncomputable def Mk (Lb : LaurentBase K U G gen D H φ) {V : Type*} [AddCommGroup V]
    [Module K V] (k : ℤ) : V ⊗[K] ↥Lb.R →ₗ[K] V ⊗[K] ↥(D Lb.N) :=
  TensorProduct.map LinearMap.id (Lb.coord k)

@[simp] theorem Tm_tmul (Lb : LaurentBase K U G gen D H φ) {V : Type*} [AddCommGroup V]
    [Module K V] (k : ℤ) (v : V) (y : ↥Lb.R) :
    Tm Lb k (v ⊗ₜ[K] y) = v ⊗ₜ[K] (Lb.rightMulU k y) := rfl

@[simp] theorem Mk_tmul (Lb : LaurentBase K U G gen D H φ) {V : Type*} [AddCommGroup V]
    [Module K V] (k : ℤ) (v : V) (y : ↥Lb.R) :
    Mk Lb k (v ⊗ₜ[K] y) = v ⊗ₜ[K] (Lb.coord k y) := rfl

@[simp] theorem inclDN_tmul (Lb : LaurentBase K U G gen D H φ) {V : Type*} [AddCommGroup V]
    [Module K V] (v : V) (d : ↥(D Lb.N)) :
    inclDN Lb (v ⊗ₜ[K] d) = v ⊗ₜ[K] ⟨(d : U), Lb.DN_le_R d.2⟩ := rfl

end LaurentBase

end Work.ORTorsion
