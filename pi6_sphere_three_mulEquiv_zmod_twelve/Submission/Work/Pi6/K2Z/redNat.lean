import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.K2Z.coeffChange
import Submission.Work.Cohomology.KroneckerH
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Reduction of coefficients `ℤ → ℤ/p` for singular (co)homology and the Kronecker pairing

For a simplicial set `X` and a prime `p` this file constructs

* `redHom : Hₙ(X;ℤ) → Hₙ(X;ℤ/p)` on homology, induced by the chain-level reduction `kappa` of
  `Submission/Work/Pi6/K2Z/coeffChange.lean` (via the induced map on cycles and the descent along
  `homologyπ`, whose kernel is the image of `toCycles`), and
* `redCoh : Hⁿ(X;ℤ) → Hⁿ(X;ℤ/p)` on cohomology, induced by the cochain-level reduction `gammaLM`
  of the same file (via the induced map on cocycles and the descent along `homologyπ`),

together with the two compatibility statements needed downstream:

* `redCoh` is multiplicative for the cup product (`gamma_cup_fun` + the computation rules
  `cupH'_apply`), and
* the Kronecker pairing of `redCoh x` with `redHom c` is the reduction of the integral pairing
  (`gammaLM_kappa` + `kronH_apply`).

The main theorem `redNat` is the packaged existence statement.

## Formalisation remarks

The cycles/homology of a complex live in `ModuleCat`, and the carrier of e.g.
`(X.chainComplex (ModuleCat.of (ZMod p) (ZMod p))).cycles n` is a `ℤ/p`-module that is used as a
`ℤ`-module by restriction of scalars; the `ℤ`-linearity of the maps on cycles is therefore proved
by `LinearMap.mk` with the *named* module instances, converting the `ℤ`-action to `zsmul` via
`Subsingleton.elim` on the (subsingleton) type of `Module ℤ` structures and `map_zsmul`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.K2Z

noncomputable section

abbrev chZC (X : SSet) : ChainComplex (ModuleCat ℤ) ℕ := X.chainComplex (ModuleCat.of ℤ ℤ)

abbrev chPC (p : ℕ) (X : SSet) : ChainComplex (ModuleCat (ZMod p)) ℕ :=
  X.chainComplex (ModuleCat.of (ZMod p) (ZMod p))

abbrev coCZC (X : SSet) : CochainComplex (ModuleCat ℤ) ℕ :=
  Work.Cohomology.SSetCochainComplex ℤ X

abbrev coCPC (p : ℕ) (X : SSet) : CochainComplex (ModuleCat (ZMod p)) ℕ :=
  Work.Cohomology.SSetCochainComplex (ZMod p) X

/-- The computation rule for the composite of morphisms of `ℤ`-modules. -/
lemma comp_hom_apply {M N P : ModuleCat ℤ} (f : M ⟶ N) (g : N ⟶ P) (x : ↥M) :
    (f ≫ g).hom x = g.hom (f.hom x) := rfl

/-! ## Elementary lemmas about cycles -/

lemma iCycles_toCycles_apply {R : Type} [CommRing R] {ι : Type} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat R) c) (i j : ι) [K.HasHomology j] (y : ↥(K.X i)) :
    (K.iCycles j).hom ((K.toCycles i j).hom y) = (K.d i j).hom y := by
  have h := congrArg (fun (f : K.X i ⟶ K.X j) => f.hom y)
    (HomologicalComplex.toCycles_i K i j)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

lemma homologyπ_toCycles_apply {R : Type} [CommRing R] {ι : Type} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat R) c) (i j : ι) [K.HasHomology j] (y : ↥(K.X i)) :
    (K.homologyπ j).hom ((K.toCycles i j).hom y) = 0 := by
  have h := congrArg (fun (f : K.X i ⟶ K.homology j) => f.hom y)
    (HomologicalComplex.toCycles_comp_homologyπ K i j)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h

lemma iCycles_injective' {R : Type} [CommRing R] {ι : Type} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat R) c) (i : ι) [K.HasHomology i] :
    Function.Injective ((K.iCycles i).hom) :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

/-! ## Cycles of killed chains -/

lemma toSpanSingleton_d_eq_zero (R : Type) [CommRing R] (K : ChainComplex (ModuleCat R) ℕ)
    (i : ℕ) (y : ↥(K.X i)) (hy : (K.d i ((ComplexShape.down ℕ).next i)).hom y = 0) :
    ModuleCat.ofHom (LinearMap.toSpanSingleton R (↥(K.X i)) y) ≫
      K.d i ((ComplexShape.down ℕ).next i) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  show (K.d i ((ComplexShape.down ℕ).next i)).hom (r • y) = 0
  rw [map_smul, hy, smul_zero]

def mkCycle (R : Type) [CommRing R] (K : ChainComplex (ModuleCat R) ℕ) (i : ℕ)
    (y : ↥(K.X i)) (hy : (K.d i ((ComplexShape.down ℕ).next i)).hom y = 0) : ↥(K.cycles i) :=
  (K.liftCycles (ModuleCat.ofHom (LinearMap.toSpanSingleton R (↥(K.X i)) y))
    ((ComplexShape.down ℕ).next i) rfl (toSpanSingleton_d_eq_zero R K i y hy)).hom 1

lemma iCycles_mkCycle (R : Type) [CommRing R] (K : ChainComplex (ModuleCat R) ℕ) (i : ℕ)
    (y : ↥(K.X i)) (hy : (K.d i ((ComplexShape.down ℕ).next i)).hom y = 0) :
    (K.iCycles i).hom (mkCycle R K i y hy) = y := by
  have h := congrArg (fun (f : ModuleCat.of R R ⟶ K.X i) => f.hom (1 : R))
    (HomologicalComplex.liftCycles_i K (ModuleCat.ofHom (LinearMap.toSpanSingleton R (↥(K.X i)) y))
      ((ComplexShape.down ℕ).next i) rfl (toSpanSingleton_d_eq_zero R K i y hy))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, mkCycle, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] using h

lemma d_iCycles_eq_zero (R : Type) [CommRing R] (K : ChainComplex (ModuleCat R) ℕ) (i : ℕ)
    (z : ↥(K.cycles i)) :
    (K.d i ((ComplexShape.down ℕ).next i)).hom ((K.iCycles i).hom z) = 0 := by
  have h := congrArg (fun (f : K.cycles i ⟶ K.X ((ComplexShape.down ℕ).next i)) => f.hom z)
    (HomologicalComplex.iCycles_d K i ((ComplexShape.down ℕ).next i))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h

lemma mkCycle_add (R : Type) [CommRing R] (K : ChainComplex (ModuleCat R) ℕ) (i : ℕ)
    (y y' : ↥(K.X i)) (hy : (K.d i ((ComplexShape.down ℕ).next i)).hom y = 0)
    (hy' : (K.d i ((ComplexShape.down ℕ).next i)).hom y' = 0) :
    mkCycle R K i (y + y') (by rw [map_add, hy, hy', add_zero]) =
      mkCycle R K i y hy + mkCycle R K i y' hy' := by
  apply iCycles_injective' (K := K) i
  rw [map_add ((K.iCycles i).hom), iCycles_mkCycle, iCycles_mkCycle, iCycles_mkCycle]

lemma mkCycle_smul (R : Type) [CommRing R] (K : ChainComplex (ModuleCat R) ℕ) (i : ℕ)
    (c : R) (y : ↥(K.X i)) (hy : (K.d i ((ComplexShape.down ℕ).next i)).hom y = 0) :
    mkCycle R K i (c • y) (by rw [map_smul, hy, smul_zero]) = c • mkCycle R K i y hy := by
  apply iCycles_injective' (K := K) i
  rw [map_smul ((K.iCycles i).hom), iCycles_mkCycle, iCycles_mkCycle]

/-! ## The chain map property of `kappa` -/

lemma kappa_d (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ) (y : ↥((chZC X).X n)) :
    (kappa p X ((ComplexShape.down ℕ).next n))
        (((chZC X).d n ((ComplexShape.down ℕ).next n)).hom y) =
      ((chPC p X).d n ((ComplexShape.down ℕ).next n)).hom ((kappa p X n) y) := by
  rcases n with _ | k
  · have hnext : (ComplexShape.down ℕ).next 0 = 0 :=
      ComplexShape.next_eq_self (ComplexShape.down ℕ) 0 (by
        intro h
        rw [ComplexShape.down_Rel] at h
        omega)
    have hZ : ((chZC X).d 0 0).hom y = 0 := by
      rw [(chZC X).shape 0 0 (by rw [ComplexShape.down_Rel]; omega)]
      rfl
    have hP : ((chPC p X).d 0 0).hom ((kappa p X 0) y) = 0 := by
      rw [(chPC p X).shape 0 0 (by rw [ComplexShape.down_Rel]; omega)]
      rfl
    rw [hnext, hZ, hP, map_zero]
  · have hnext : (ComplexShape.down ℕ).next (k + 1) = k :=
      ComplexShape.next_eq' (ComplexShape.down ℕ) (i := k + 1) (j := k) rfl
    rw [hnext]
    exact kappa_comm_elem p X k y

/-! ## Reduction on the cycles of the chain complex -/

lemma kappaZ_hy (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ) (z : ↥((chZC X).cycles n)) :
    ((chPC p X).d n ((ComplexShape.down ℕ).next n)).hom
      ((kappa p X n) ((chZC X).iCycles n z)) = 0 := by
  rw [← kappa_d p X n ((chZC X).iCycles n z), d_iCycles_eq_zero, map_zero]

/-- Coefficient reduction on the cycles of the integral chain complex (as a function). -/
def kappaZFun (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ)
    (z : ↥((chZC X).cycles n)) : ↥((chPC p X).cycles n) :=
  mkCycle (ZMod p) (chPC p X) n ((kappa p X n) ((chZC X).iCycles n z)) (kappaZ_hy p X n z)

lemma kappaZFun_zero (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ) :
    kappaZFun p X n 0 = 0 := by
  apply iCycles_injective' (K := chPC p X) n
  simp only [kappaZFun, iCycles_mkCycle, map_zero]

lemma kappaZFun_add (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ)
    (z z' : ↥((chZC X).cycles n)) :
    kappaZFun p X n (z + z') = kappaZFun p X n z + kappaZFun p X n z' := by
  have h : (kappa p X n) ((chZC X).iCycles n (z + z')) =
      (kappa p X n) ((chZC X).iCycles n z) + (kappa p X n) ((chZC X).iCycles n z') := by
    rw [map_add ((chZC X).iCycles n).hom, map_add (kappa p X n)]
  simp only [kappaZFun, h]
  exact mkCycle_add (ZMod p) (chPC p X) n _ _ _ _

def kappaZAdd (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ) :
    ↥((chZC X).cycles n) →+ ↥((chPC p X).cycles n) where
  toFun := kappaZFun p X n
  map_zero' := kappaZFun_zero p X n
  map_add' := kappaZFun_add p X n

/-- Coefficient reduction on the cycles of the integral chain complex. -/
def kappaZ (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ) :
    @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) (↥((chZC X).cycles n)) (↥((chPC p X).cycles n)) _ _
      ((chZC X).cycles n).isModule (AddCommGroup.toIntModule (M := ↥((chPC p X).cycles n))) :=
  @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) _ _ _ _
    ((chZC X).cycles n).isModule (AddCommGroup.toIntModule (M := ↥((chPC p X).cycles n)))
    (kappaZAdd p X n) (by
      intro r z
      have hinst : ((chZC X).cycles n).isModule =
          AddCommGroup.toIntModule (M := ↥((chZC X).cycles n)) := Subsingleton.elim _ _
      rw [hinst]
      simp only [RingHom.id_apply]
      exact AddMonoidHom.map_zsmul (kappaZAdd p X n) r z)

lemma iCycles_kappaZ (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ)
    (z : ↥((chZC X).cycles n)) :
    (chPC p X).iCycles n (kappaZ p X n z) = (kappa p X n) ((chZC X).iCycles n z) :=
  iCycles_mkCycle (ZMod p) (chPC p X) n _ (kappaZ_hy p X n z)

lemma kappaZ_toCycles (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ)
    (y : ↥((chZC X).X (n + 1))) :
    kappaZ p X n ((chZC X).toCycles (n + 1) n y) =
      (chPC p X).toCycles (n + 1) n ((kappa p X (n + 1)) y) := by
  apply iCycles_injective' (K := chPC p X) n
  rw [iCycles_kappaZ, iCycles_toCycles_apply, iCycles_toCycles_apply]
  exact kappa_comm_elem p X n y

lemma kappaZ_homologyπ (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ)
    (y : ↥((chZC X).X (n + 1))) :
    ((chPC p X).homologyπ n) (kappaZ p X n ((chZC X).toCycles (n + 1) n y)) = 0 := by
  rw [kappaZ_toCycles, homologyπ_toCycles_apply]

def kappaComp (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ) :
    (chZC X).cycles n ⟶ ModuleCat.of ℤ ↥((chPC p X).homology n) :=
  ModuleCat.ofHom (kappaZ p X n) ≫
    ModuleCat.ofHom (LinearMap.restrictScalars ℤ ((chPC p X).homologyπ n).hom)

lemma kappaComp_apply (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ)
    (z : ↥((chZC X).cycles n)) :
    (kappaComp p X n).hom z = ((chPC p X).homologyπ n) (kappaZ p X n z) :=
  rfl

lemma kappaComp_eq_zero (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ) :
    (chZC X).toCycles (n + 1) n ≫ kappaComp p X n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  show ((chPC p X).homologyπ n) (kappaZ p X n ((HomologicalComplex.toCycles (chZC X) (n + 1) n) y)) = 0
  exact kappaZ_homologyπ p X n y

noncomputable def redHomM (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ) :
    (chZC X).homology n ⟶ ModuleCat.of ℤ ↥((chPC p X).homology n) :=
  Cofork.IsColimit.desc ((chZC X).homologyIsCokernel (n + 1) n (ChainComplex.prev ℕ n))
    (kappaComp p X n) (by rw [zero_comp]; exact kappaComp_eq_zero p X n)

/-- Coefficient reduction `Hₙ(X;ℤ) → Hₙ(X;ℤ/p)`. -/
noncomputable def redHom (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ) :
    ↥((chZC X).homology n) →ₗ[ℤ] ↥((chPC p X).homology n) :=
  (redHomM p X n).hom

lemma redHom_homologyπ (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ)
    (z : ↥((chZC X).cycles n)) :
    redHom p X n (((chZC X).homologyπ n).hom z) =
      ((chPC p X).homologyπ n) (kappaZ p X n z) := by
  have h := Cofork.IsColimit.π_desc'
    ((chZC X).homologyIsCokernel (n + 1) n (ChainComplex.prev ℕ n))
    (kappaComp p X n) (by rw [zero_comp]; exact kappaComp_eq_zero p X n)
  have h2 := congrArg (fun (f : (chZC X).cycles n ⟶ ModuleCat.of ℤ ↥((chPC p X).homology n)) =>
    f.hom z) h
  simp only [redHomM, Cofork.π_ofπ, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    LinearMap.comp_apply, redHom, LinearMap.restrictScalars_apply] at h2 ⊢
  exact h2

/-! ## The cochain map property of `gamma` -/

lemma genEval_gammaLM (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ)
    (α : Work.Cohomology.Cochain ℤ X n) (σ : X _⦋n⦌) :
    Work.Cohomology.genEval (ZMod p) X (gammaLM p X n α) σ =
      ((Work.Cohomology.genEval ℤ X α σ : ℤ) : ZMod p) :=
  gammaCat_genEval p X n α σ

lemma gammaCat_kappa (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ)
    (α : Work.Cohomology.Cochain ℤ X n) (y : ↥((chZC X).X n)) :
    (gammaCat p X n α).hom ((kappa p X n) y) = ((α y : ℤ) : ZMod p) := by
  have h := congrArg (fun (f : ↥((chZC X).X n) →ₗ[ℤ] ZMod p) => f y)
    (gamma_comp_kappa p X n α)
  simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearMap.toSpanSingleton_apply, zsmul_eq_mul, mul_one] using h

lemma gammaLM_kappa (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ)
    (α : Work.Cohomology.Cochain ℤ X n) (y : ↥((chZC X).X n)) :
    gammaLM p X n α ((kappa p X n) y) = ((α y : ℤ) : ZMod p) := by
  change (gammaCat p X n α).hom ((kappa p X n) y) = ((α y : ℤ) : ZMod p)
  exact gammaCat_kappa p X n α y

lemma gammaComm (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ)
    (α : Work.Cohomology.Cochain ℤ X n) :
    Work.Cohomology.cochainDiff (ZMod p) X (gammaLM p X n α) =
      gammaLM p X (n + 1) (Work.Cohomology.cochainDiff ℤ X α) := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [Work.Cohomology.cochainDiff_apply, genEval_gammaLM p X (n + 1)
    (Work.Cohomology.cochainDiff ℤ X α) σ]
  rw [Work.Cohomology.cochainDiff_apply]
  rw [← kappaCat_gen p X (n + 1) σ]
  rw [← kappa_comm_elem p X n ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1)]
  exact gammaCat_kappa p X n α (((chZC X).d (n + 1) n).hom
    ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1))

lemma gamma_cocycle (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ)
    (α : Work.Cohomology.Cochain ℤ X n) (hα : Work.Cohomology.cochainDiff ℤ X α = 0) :
    Work.Cohomology.cochainDiff (ZMod p) X (gammaLM p X n α) = 0 := by
  rw [gammaComm p X n α, hα, map_zero]

/-! ## Nicely typed bridges for cochains -/

lemma cochainOfCycle_injective' (R : Type) [CommRing R] (X : SSet) (n : ℕ) :
    Function.Injective (Work.Cohomology.cochainOfCycle R X n) :=
  Work.Cohomology.iCycles_injective R X n

lemma cochainDiff_cochainOfCycle' (R : Type) [CommRing R] (X : SSet) (n : ℕ)
    (z : ↥((Work.Cohomology.SSetCochainComplex R X).cycles n)) :
    Work.Cohomology.cochainDiff R X (Work.Cohomology.cochainOfCycle R X n z) = 0 :=
  Work.Cohomology.cochainDiff_iCycles R X n z

lemma cochainOfCycle_toCycles' (R : Type) [CommRing R] (X : SSet) (i j : ℕ)
    (β : Work.Cohomology.Cochain R X i) :
    Work.Cohomology.cochainOfCycle R X j
        ((Work.Cohomology.SSetCochainComplex R X).toCycles i j β) =
      ((Work.Cohomology.SSetCochainComplex R X).d i j).hom β :=
  iCycles_toCycles_apply (Work.Cohomology.SSetCochainComplex R X) i j β

lemma d_apply_cochain (R : Type) [CommRing R] (X : SSet) (k : ℕ)
    (β : Work.Cohomology.Cochain R X k) :
    ((Work.Cohomology.SSetCochainComplex R X).d k (k + 1)).hom β =
      Work.Cohomology.cochainDiff R X β :=
  Work.Cohomology.SSetCochainComplex_d_apply R X k β

lemma cochainOfCycle_zero' (R : Type) [CommRing R] (X : SSet) (n : ℕ) :
    Work.Cohomology.cochainOfCycle R X n 0 = 0 :=
  map_zero ((Work.Cohomology.SSetCochainComplex R X).iCycles n).hom

/-! ## Reduction on the cocycles of the cochain complex -/

lemma gammaZ_killed (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ)
    (z : ↥((coCZC X).cycles n)) :
    Work.Cohomology.cochainDiff (ZMod p) X
      (gammaLM p X n (Work.Cohomology.cochainOfCycle ℤ X n z)) = 0 := by
  rw [gammaComm p X n (Work.Cohomology.cochainOfCycle ℤ X n z),
    cochainDiff_cochainOfCycle', map_zero]

/-- Coefficient reduction on the cocycles of the integral cochain complex (as a function). -/
def gammaZFun (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ)
    (z : ↥((coCZC X).cycles n)) : ↥((coCPC p X).cycles n) :=
  Work.Cohomology.cocycleOf (ZMod p) X
    (gammaLM p X n (Work.Cohomology.cochainOfCycle ℤ X n z)) (gammaZ_killed p X n z)

lemma gammaZFun_zero (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ) :
    gammaZFun p X n 0 = 0 := by
  apply cochainOfCycle_injective' (R := ZMod p) (X := X) n
  simp only [gammaZFun, Work.Cohomology.cochainOfCycle_cocycleOf, cochainOfCycle_zero', map_zero]

lemma gammaZFun_add (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ)
    (z z' : ↥((coCZC X).cycles n)) :
    gammaZFun p X n (z + z') = gammaZFun p X n z + gammaZFun p X n z' := by
  apply cochainOfCycle_injective' (R := ZMod p) (X := X) n
  simp only [gammaZFun, Work.Cohomology.cochainOfCycle_cocycleOf,
    Work.Cohomology.cochainOfCycle_add, map_add (gammaLM p X n)]

def gammaZAdd (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ) :
    ↥((coCZC X).cycles n) →+ ↥((coCPC p X).cycles n) where
  toFun := gammaZFun p X n
  map_zero' := gammaZFun_zero p X n
  map_add' := gammaZFun_add p X n

/-- Coefficient reduction on the cocycles of the integral cochain complex. -/
def gammaZ (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ) :
    @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) (↥((coCZC X).cycles n)) (↥((coCPC p X).cycles n)) _ _
      ((coCZC X).cycles n).isModule (AddCommGroup.toIntModule (M := ↥((coCPC p X).cycles n))) :=
  @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) _ _ _ _
    ((coCZC X).cycles n).isModule (AddCommGroup.toIntModule (M := ↥((coCPC p X).cycles n)))
    (gammaZAdd p X n) (by
      intro r z
      have hinst : ((coCZC X).cycles n).isModule =
          AddCommGroup.toIntModule (M := ↥((coCZC X).cycles n)) := Subsingleton.elim _ _
      rw [hinst]
      simp only [RingHom.id_apply]
      exact AddMonoidHom.map_zsmul (gammaZAdd p X n) r z)

lemma cochainOfCycle_gammaZ (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ)
    (z : ↥((coCZC X).cycles n)) :
    Work.Cohomology.cochainOfCycle (ZMod p) X n (gammaZ p X n z) =
      gammaLM p X n (Work.Cohomology.cochainOfCycle ℤ X n z) :=
  Work.Cohomology.cochainOfCycle_cocycleOf (ZMod p) X n _ (gammaZ_killed p X n z)

lemma gammaZ_toCycles_succ (p : ℕ) [Fact p.Prime] (X : SSet) (k : ℕ)
    (β : Work.Cohomology.Cochain ℤ X k) :
    gammaZ p X (k + 1) ((coCZC X).toCycles k (k + 1) β) =
      (coCPC p X).toCycles k (k + 1) (gammaLM p X k β) := by
  apply cochainOfCycle_injective' (R := ZMod p) (X := X) (k + 1)
  rw [cochainOfCycle_gammaZ, cochainOfCycle_toCycles' ℤ X k (k + 1) β,
    cochainOfCycle_toCycles' (ZMod p) X k (k + 1) (gammaLM p X k β),
    d_apply_cochain, d_apply_cochain, gammaComm]

def gammaComp (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ) :
    (coCZC X).cycles n ⟶ ModuleCat.of ℤ ↥((coCPC p X).homology n) :=
  ModuleCat.ofHom (gammaZ p X n) ≫
    ModuleCat.ofHom (LinearMap.restrictScalars ℤ ((coCPC p X).homologyπ n).hom)

lemma gammaComp_apply (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ)
    (z : ↥((coCZC X).cycles n)) :
    (gammaComp p X n).hom z = ((coCPC p X).homologyπ n) (gammaZ p X n z) :=
  rfl

lemma gammaComp_eq_zero (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ) :
    (coCZC X).toCycles ((ComplexShape.up ℕ).prev n) n ≫ gammaComp p X n = 0 := by
  generalize hpn : (ComplexShape.up ℕ).prev n = pn
  rcases n with _ | k
  · have hpn' : pn = 0 := by rw [← hpn]; simp
    rw [hpn']
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    show ((coCPC p X).homologyπ 0)
      (gammaZ p X 0 ((HomologicalComplex.toCycles (coCZC X) 0 0) y)) = 0
    rw [HomologicalComplex.toCycles_eq_zero _ (by simp [ComplexShape.up_Rel])]
    simp
  · have hpn' : pn = k := by rw [← hpn]; simp
    rw [hpn']
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    have h := gammaZ_toCycles_succ p X k y
    show ((coCPC p X).homologyπ (k + 1))
      (gammaZ p X (k + 1) ((HomologicalComplex.toCycles (coCZC X) k (k + 1)) y)) = 0
    rw [show gammaZ p X (k + 1) ((HomologicalComplex.toCycles (coCZC X) k (k + 1)) y) =
        (HomologicalComplex.toCycles (coCPC p X) k (k + 1)) (gammaLM p X k y) from h]
    exact homologyπ_toCycles_apply (coCPC p X) k (k + 1) (gammaLM p X k y)

noncomputable def redCohM (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ) :
    (coCZC X).homology n ⟶ ModuleCat.of ℤ ↥((coCPC p X).homology n) :=
  Work.Cohomology.descH ℤ X n (gammaComp p X n) (gammaComp_eq_zero p X n)

/-- Coefficient reduction `Hⁿ(X;ℤ) → Hⁿ(X;ℤ/p)`. -/
noncomputable def redCoh (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ) :
    ↥((coCZC X).homology n) →ₗ[ℤ] ↥((coCPC p X).homology n) :=
  (redCohM p X n).hom

lemma redCoh_homologyπ (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ)
    (z : ↥((coCZC X).cycles n)) :
    redCoh p X n (((coCZC X).homologyπ n).hom z) =
      ((coCPC p X).homologyπ n) (gammaZ p X n z) := by
  have h := Work.Cohomology.homologyπ_descH ℤ X n (gammaComp p X n) (gammaComp_eq_zero p X n)
  have h2 := congrArg (fun (f : (coCZC X).cycles n ⟶ ModuleCat.of ℤ ↥((coCPC p X).homology n)) =>
    f.hom z) h
  simp only [redCohM, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, redCoh,
    LinearMap.restrictScalars_apply] at h2 ⊢
  exact h2

lemma redCoh_classOf (p : ℕ) [Fact p.Prime] (X : SSet) (n : ℕ)
    (α : Work.Cohomology.Cochain ℤ X n)
    (hα : Work.Cohomology.cochainDiff ℤ X α = 0)
    (hα' : Work.Cohomology.cochainDiff (ZMod p) X (gammaLM p X n α) = 0) :
    redCoh p X n (Work.Cohomology.cohomologyClassOf ℤ X α hα) =
      Work.Cohomology.cohomologyClassOf (ZMod p) X (gammaLM p X n α) hα' := by
  rw [Work.Cohomology.cohomologyClassOf, redCoh_homologyπ,
    Work.Cohomology.cohomologyClassOf]
  congr 1
  apply cochainOfCycle_injective' (R := ZMod p) (X := X) n
  rw [cochainOfCycle_gammaZ, Work.Cohomology.cochainOfCycle_cocycleOf,
    Work.Cohomology.cochainOfCycle_cocycleOf]

lemma gamma_cup_fun (p : ℕ) [Fact p.Prime] (X : SSet) (n m : ℕ)
    (α : Work.Cohomology.Cochain ℤ X n) (β : Work.Cohomology.Cochain ℤ X m) :
    gammaLM p X (n + m) (Work.Cohomology.cup ℤ X α β) =
      Work.Cohomology.cup (ZMod p) X (gammaLM p X n α) (gammaLM p X m β) := by
  change (gammaCat p X (n + m) (Work.Cohomology.cup ℤ X α β)).hom =
    (Work.Cohomology.cupHom (ZMod p) X (gammaCat p X n α).hom (gammaCat p X m β).hom).hom
  exact congrArg ModuleCat.Hom.hom (gamma_cup p X n m α β)

/-! ## Assembly -/

theorem redNat (p : ℕ) [Fact p.Prime] (X : Type) [TopologicalSpace X] :
    ∃ (redCoh : ∀ n : ℕ, Work.Pi6.Coh ℤ X n →ₗ[ℤ] Work.Pi6.Coh (ZMod p) X n)
      (redHom : ∀ n : ℕ, Work.Pi6.HR ℤ X n →ₗ[ℤ] Work.Pi6.HR (ZMod p) X n),
      (∀ (n m : ℕ) (x : Work.Pi6.Coh ℤ X n) (y : Work.Pi6.Coh ℤ X m),
        redCoh (n + m) ((Work.Pi6.cup ℤ X n m) x y) =
          (Work.Pi6.cup (ZMod p) X n m) (redCoh n x) (redCoh m y)) ∧
      (∀ (n : ℕ) (x : Work.Pi6.Coh ℤ X n) (c : Work.Pi6.HR ℤ X n),
        (Work.Cohomology.kronH (ZMod p) (TopCat.toSSet.obj (TopCat.of X)) n) (redCoh n x)
            (redHom n c) =
          ((Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of X)) n x c : ℤ) : ZMod p)) := by
  refine ⟨fun n => redCoh p (TopCat.toSSet.obj (TopCat.of X)) n,
    fun n => redHom p (TopCat.toSSet.obj (TopCat.of X)) n, ?_, ?_⟩
  · intro n m x y
    change redCoh p (TopCat.toSSet.obj (TopCat.of X)) (n + m)
        (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of X)) n m x y) =
      Work.Cohomology.cupH' (ZMod p) (TopCat.toSSet.obj (TopCat.of X)) n m
        (redCoh p (TopCat.toSSet.obj (TopCat.of X)) n x)
        (redCoh p (TopCat.toSSet.obj (TopCat.of X)) m y)
    obtain ⟨α, hα, hx⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ
      (TopCat.toSSet.obj (TopCat.of X)) n x
    obtain ⟨β, hβ, hy⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ
      (TopCat.toSSet.obj (TopCat.of X)) m y
    rw [← hx, ← hy]
    have hαβ := Work.Cohomology.cochainDiff_cup_of_cocycles ℤ
      (TopCat.toSSet.obj (TopCat.of X)) α β hα hβ
    have hαγ := gamma_cocycle p (TopCat.toSSet.obj (TopCat.of X)) n α hα
    have hβγ := gamma_cocycle p (TopCat.toSSet.obj (TopCat.of X)) m β hβ
    have hγcup := gamma_cup_fun p (TopCat.toSSet.obj (TopCat.of X)) n m α β
    have hα' : Work.Cohomology.cochainDiff (ZMod p) (TopCat.toSSet.obj (TopCat.of X))
        (gammaLM p (TopCat.toSSet.obj (TopCat.of X)) (n + m)
          (Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of X)) α β)) = 0 := by
      rw [hγcup]
      exact Work.Cohomology.cochainDiff_cup_of_cocycles (ZMod p)
        (TopCat.toSSet.obj (TopCat.of X)) _ _ hαγ hβγ
    rw [Work.Cohomology.cupH'_apply ℤ (TopCat.toSSet.obj (TopCat.of X)) α β hα hβ hαβ]
    rw [redCoh_classOf p (TopCat.toSSet.obj (TopCat.of X)) (n + m)
      (Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of X)) α β) hαβ hα']
    rw [redCoh_classOf p (TopCat.toSSet.obj (TopCat.of X)) n α hα hαγ,
      redCoh_classOf p (TopCat.toSSet.obj (TopCat.of X)) m β hβ hβγ]
    rw [Work.Cohomology.cupH'_apply (ZMod p) (TopCat.toSSet.obj (TopCat.of X))
      (gammaLM p (TopCat.toSSet.obj (TopCat.of X)) n α)
      (gammaLM p (TopCat.toSSet.obj (TopCat.of X)) m β) hαγ hβγ (hγcup ▸ hα')]
    exact Work.Cohomology.cohomologyClassOf_congr (ZMod p) (TopCat.toSSet.obj (TopCat.of X))
      hγcup hα' (hγcup ▸ hα')
  · intro n x c
    change (Work.Cohomology.kronH (ZMod p) (TopCat.toSSet.obj (TopCat.of X)) n)
        (redCoh p (TopCat.toSSet.obj (TopCat.of X)) n x)
        (redHom p (TopCat.toSSet.obj (TopCat.of X)) n c) =
      ((Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of X)) n x c : ℤ) : ZMod p)
    obtain ⟨α, hα, hx⟩ := Work.Cohomology.exists_cohomologyClassOf ℤ
      (TopCat.toSSet.obj (TopCat.of X)) n x
    rw [← hx]
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((chZC (TopCat.toSSet.obj (TopCat.of X))).homologyπ n)).mp inferInstance c
    have hαγ := gamma_cocycle p (TopCat.toSSet.obj (TopCat.of X)) n α hα
    rw [redCoh_classOf p (TopCat.toSSet.obj (TopCat.of X)) n α hα hαγ]
    rw [redHom_homologyπ p (TopCat.toSSet.obj (TopCat.of X)) n z]
    rw [Work.Cohomology.kronH_apply (ZMod p) (TopCat.toSSet.obj (TopCat.of X))
      (gammaLM p (TopCat.toSSet.obj (TopCat.of X)) n α) hαγ
      (kappaZ p (TopCat.toSSet.obj (TopCat.of X)) n z)]
    rw [iCycles_kappaZ]
    rw [gammaLM_kappa]
    rw [Work.Cohomology.kronH_apply ℤ (TopCat.toSSet.obj (TopCat.of X)) α hα z]

end

end Work.Pi6.K2Z
