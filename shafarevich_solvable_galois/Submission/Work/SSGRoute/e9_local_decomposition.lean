import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.E9Nodes.e9_basic
import Submission.Work.SSGRoute.E9Nodes.e9_unramified_all_but_finite
import Submission.Work.SSGRoute.E9b.chi_pTor_classLevelLimit
import Submission.Work.SSGRoute.E9b.isUnramifiedClassAt_conj
import Submission.Work.SSGRoute.E9b.locTriv_subset_unram
import Submission.Work.SSGRoute.E9b.pTor_classLevel_card
import Submission.Work.SSGRoute.E9b.unramified_inflHIn
import Submission.Work.SSGRoute.local_duality_ext_extH_finite
import Submission.Work.SSGRoute.phi1_wcolim
set_option synthInstance.maxHeartbeats 400000

open SSGRoute.PTExt CategoryTheory

namespace Work.SSGRoute

noncomputable section

set_option maxHeartbeats 200000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
  [FiniteDimensional k K] [IsGalois k K]


/-! ## 0. The abstract finite-support decomposition -/

/-- An additive subgroup of a module over `ZMod p` is automatically a submodule. -/
private noncomputable def toSubmodule (p : ℕ) [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] (U : AddSubgroup V) : Submodule (ZMod p) V :=
  { carrier := U
    zero_mem' := U.zero_mem'
    add_mem' := fun hx hy => U.add_mem hx hy
    smul_mem' := fun c _x hx => by
      have hc : c • _x = c.val • _x := by
        rw [← Nat.cast_smul_eq_nsmul (ZMod p) c.val _x, ZMod.natCast_zmod_val c]
      rw [hc]
      exact U.nsmul_mem hx c.val }

/-- The linear map picking out the `i`-th coordinate of a product. -/
private noncomputable def piSingle (p : ℕ) [Fact p.Prime] {ι : Type*} [DecidableEq ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod p) (M i)] (i : ι) :
    M i →ₗ[ZMod p] (∀ j, M j) where
  toFun v := Pi.single i v
  map_add' v w := by
    funext j
    rcases eq_or_ne j i with h | h
    · subst h; simp
    · simp only [Pi.add_apply, Pi.single_eq_of_ne h, add_zero]
  map_smul' a v := by
    funext j
    rcases eq_or_ne j i with h | h
    · subst h; simp
    · simp only [Pi.smul_apply, Pi.single_eq_of_ne h, smul_zero]

/-- **Abstract finite-support decomposition of a linear functional.** -/
private theorem exists_finsupp_decomposition_aux (p : ℕ) [Fact p.Prime] {V X : Type*}
    [AddCommGroup V] [AddCommGroup X] [Module (ZMod p) V] [Module (ZMod p) X] {ι : Type*}
    (U : ι → AddSubgroup V) (hfin : ∀ x : V, {i : ι | x ∉ U i}.Finite)
    (ψ : V →ₗ[ZMod p] X) (hker : ∀ x : V, (∀ i, x ∈ U i) → ψ x = 0) :
    ∃ (f : ι → V →+ X),
      (∀ i x, x ∈ U i → f i x = 0) ∧
      (∀ x, {i : ι | f i x ≠ 0}.Finite) ∧
      (∀ x, ψ x = ∑ᶠ i, f i x) := by
  classical
  let Ui : ι → Submodule (ZMod p) V := fun i => toSubmodule p (U i)
  let P := ∀ i, V ⧸ Ui i
  let φ : V →ₗ[ZMod p] P := LinearMap.pi (fun i : ι => Submodule.mkQ (Ui i))
  have hφ : ∀ x i, φ x i = (Ui i).mkQ x := fun x i => rfl
  have hmkQ : ∀ (i : ι) (x : V), x ∈ U i → (Ui i).mkQ x = 0 := by
    intro i x hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hx
  have hkerφ : φ.ker ≤ ψ.ker := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    apply hker x
    intro i
    have h2 : (Ui i).mkQ x = 0 := by
      have h3 : φ x i = 0 := by rw [LinearMap.mem_ker.mp hx]; rfl
      rwa [hφ x i] at h3
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
  let q : V ⧸ φ.ker →ₗ[ZMod p] X := Submodule.liftQ φ.ker ψ hkerφ
  let ψ' : φ.range →ₗ[ZMod p] X :=
    q.comp ((LinearMap.quotKerEquivRange φ).symm : ↥φ.range →ₗ[ZMod p] V ⧸ φ.ker)
  have hψ' : ∀ x, ψ' ⟨φ x, LinearMap.mem_range_self φ x⟩ = ψ x := by
    intro x
    show q ((LinearMap.quotKerEquivRange φ).symm ⟨φ x, _⟩) = ψ x
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    show q ((φ.ker).mkQ x) = ψ x
    rw [Submodule.mkQ_apply]
    exact Submodule.liftQ_apply φ.ker ψ x
  obtain ⟨T, hT⟩ := Submodule.exists_isCompl φ.range
  let proj : P →ₗ[ZMod p] φ.range := φ.range.projectionOnto T hT
  let Ψ : P →ₗ[ZMod p] X := ψ'.comp proj
  have hΨφ : ∀ x, Ψ (φ x) = ψ x := by
    intro x
    have h1 : proj (φ x) = ⟨φ x, LinearMap.mem_range_self φ x⟩ :=
      Submodule.projectionOnto_apply_left hT ⟨φ x, LinearMap.mem_range_self φ x⟩
    show ψ' (proj (φ x)) = ψ x
    rw [h1]
    exact hψ' x
  refine ⟨fun i => (Ψ.comp ((piSingle p i).comp (Submodule.mkQ (Ui i)))).toAddMonoidHom,
    ?_, ?_, ?_⟩
  · intro i x hx
    show Ψ ((piSingle p i) ((Ui i).mkQ x)) = 0
    rw [hmkQ i x hx, map_zero, map_zero]
  · intro x
    apply Set.Finite.subset (hfin x)
    intro i hi
    simp only [Set.mem_setOf_eq] at hi ⊢
    intro hx
    exact hi (by
      show Ψ ((piSingle p i) ((Ui i).mkQ x)) = 0
      rw [hmkQ i x hx, map_zero, map_zero])
  · intro x
    set s : Finset ι := (hfin x).toFinset with hs_def
    have hsub : Function.support (fun i => (piSingle p i) ((Ui i).mkQ x)) ⊆ ↑s := by
      intro i hi
      rw [hs_def]
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      intro hx
      exact (Function.mem_support.mp hi) (by rw [hmkQ i x hx]; exact map_zero _)
    have hsum : (∑ᶠ i, (piSingle p i) ((Ui i).mkQ x)) = φ x := by
      rw [finsum_eq_sum_of_support_subset _ hsub]
      funext j
      rw [Finset.sum_apply]
      change (∑ i ∈ s, Pi.single i ((Ui i).mkQ x) j) = φ x j
      rw [Finset.sum_pi_single]
      split_ifs with hj
      · exact (hφ x j).symm
      · have hxU : x ∈ U j := by
          by_contra hc
          exact hj (by
            rw [hs_def]
            simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
            exact hc)
        rw [hφ x j, hmkQ j x hxU]
    have hsub2 : Function.support (fun i => Ψ ((piSingle p i) ((Ui i).mkQ x))) ⊆ ↑s := by
      intro i hi
      apply hsub
      rw [Function.mem_support] at hi ⊢
      intro h0
      exact hi (by rw [h0, map_zero])
    have h3 : (∑ᶠ i, (fun i => (Ψ.comp ((piSingle p i).comp (Submodule.mkQ (Ui i)))).toAddMonoidHom) i x)
        = ∑ᶠ i, Ψ ((piSingle p i) ((Ui i).mkQ x)) := finsum_congr (fun i => rfl)
    rw [← hΨφ x, ← hsum, finsum_eq_sum_of_support_subset _ hsub, map_sum, h3,
      finsum_eq_sum_of_support_subset _ hsub2]

/-! ## 1. The colimit `V = colim_L H¹(Gal(L/k), M)` over the levels -/

/-- The level system `L ↦ H¹(Gal(L/k), res M)`. -/
abbrev AltLeaf (M : Rep.{0} Coeff (K ≃ₐ[k] K)) (L : Lvl k K Ω) : Type _ :=
  extH (Rep.res (galRes k K L.1) M) 1

/-- The transition map: inflation along `L ≤ L'`. -/
def altMap (M : Rep.{0} Coeff (K ≃ₐ[k] K)) (L L' : Lvl k K Ω) (h : L ≤ L') :
    AltLeaf M L →+ AltLeaf M L' :=
  inflHInHom (k := k) (K := K) M (show L.1 ≤ L'.1 from h) 1

@[simp] theorem altMap_apply (M : Rep.{0} Coeff (K ≃ₐ[k] K)) (L L' : Lvl k K Ω) (h : L ≤ L')
    (y : AltLeaf M L) :
    altMap M L L' h y = inflHIn (k := k) (K := K) (show L.1 ≤ L'.1 from h) y := rfl

theorem altMap_self (M : Rep.{0} Coeff (K ≃ₐ[k] K)) (L : Lvl k K Ω) (y : AltLeaf M L) :
    altMap M L L le_rfl y = y := by
  rw [altMap_apply]
  exact inflHIn_refl (k := k) (K := K) (L := L.1) y

theorem altMap_map (M : Rep.{0} Coeff (K ≃ₐ[k] K)) (L L' L'' : Lvl k K Ω) (h₁ : L ≤ L')
    (h₂ : L' ≤ L'') (y : AltLeaf M L) :
    altMap M L' L'' h₂ (altMap M L L' h₁ y) = altMap M L L'' (h₁.trans h₂) y := by
  rw [altMap_apply, altMap_apply, altMap_apply]
  exact inflHIn_trans (k := k) (K := K) (show L.1 ≤ L'.1 from h₁)
    (show L'.1 ≤ L''.1 from h₂) y

instance altDirectedSystem (M : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    DirectedSystem (fun L : Lvl k K Ω => AltLeaf M L) (fun L L' h => altMap M L L' h) where
  map_self := fun L y => altMap_self M L y
  map_map := fun {kt jt it} (hij : it ≤ jt) (hjk : jt ≤ kt) (y : AltLeaf M it) =>
    altMap_map M it jt kt hij hjk y

/-- The `ZeroHomClass` instance used by `DirectLimit` for the level transition maps, stated
directly (build speed: the generic family search explores unrelated morphism classes). -/
instance altZeroHomClass (M : Rep.{0} Coeff (K ≃ₐ[k] K)) (L L' : Lvl k K Ω) :
    ZeroHomClass (AltLeaf M L →+ AltLeaf M L') (AltLeaf M L) (AltLeaf M L') :=
  AddMonoidHomClass.toZeroHomClass

/-- The `AddHomClass` instance used by `DirectLimit` (see `altZeroHomClass`). -/
instance altAddHomClass (M : Rep.{0} Coeff (K ≃ₐ[k] K)) (L L' : Lvl k K Ω) :
    AddHomClass (AltLeaf M L →+ AltLeaf M L') (AltLeaf M L) (AltLeaf M L') :=
  AddMonoidHomClass.toAddHomClass

/-- **`V = colim_L H¹(Gal(L/k), M)`**. -/
abbrev AltLim (M : Rep.{0} Coeff (K ≃ₐ[k] K)) : Type _ :=
  DirectLimit (fun L : Lvl k K Ω => AltLeaf M L)
    (fun (L L' : Lvl k K Ω) (h : L ≤ L') => altMap M L L' h)

/-- The canonical map of the `L`-th component. -/
def AltLim.of (M : Rep.{0} Coeff (K ≃ₐ[k] K)) (L : Lvl k K Ω) : AltLeaf M L →+ AltLim (Ω := Ω) M where
  toFun y := ⟦⟨L, y⟩⟧
  map_zero' := (DirectLimit.zero_def L).symm
  map_add' x y := (DirectLimit.add_def L x y).symm

@[simp] theorem AltLim.of_zero (M : Rep.{0} Coeff (K ≃ₐ[k] K)) (L : Lvl k K Ω) :
    AltLim.of M L (0 : AltLeaf M L) = 0 := map_zero _

/-- The colimit relation. -/
theorem AltLim.of_altMap (M : Rep.{0} Coeff (K ≃ₐ[k] K)) {L L' : Lvl k K Ω} (h : L ≤ L')
    (y : AltLeaf M L) : AltLim.of M L' (altMap M L L' h y) = AltLim.of M L y :=
  Quotient.sound ⟨L', le_rfl, h, altMap_self M L' (altMap M L L' h y)⟩

/-- Induction on `V`. -/
protected theorem AltLim.induction (M : Rep.{0} Coeff (K ≃ₐ[k] K)) {C : AltLim (Ω := Ω) M → Prop}
    (ih : ∀ (L : Lvl k K Ω) (y : AltLeaf M L), C (AltLim.of M L y))
    (a : AltLim (Ω := Ω) M) : C a :=
  DirectLimit.induction (f := fun (L L' : Lvl k K Ω) (h : L ≤ L') => altMap M L L' h)
    (fun L y => ih L y) a

/-- The universal property of `V`. -/
noncomputable def AltLim.lift (M : Rep.{0} Coeff (K ≃ₐ[k] K)) {X : Type} [AddCommMonoid X]
    (g : ∀ L : Lvl k K Ω, AltLeaf M L →+ X)
    (hg : ∀ (L L' : Lvl k K Ω) (h : L ≤ L') (y : AltLeaf M L),
      g L' (altMap M L L' h y) = g L y) : AltLim (Ω := Ω) M →+ X where
  toFun := DirectLimit.lift (fun (L L' : Lvl k K Ω) (h : L ≤ L') => altMap M L L' h)
    (fun L => g L) (fun L L' h x => (hg L L' h x).symm)
  map_zero' := by
    simpa only using
      DirectLimit.lift_zero (f := fun (L L' : Lvl k K Ω) (h : L ≤ L') => altMap M L L' h)
        (g := fun L => g L)
        (fun L L' h x => (hg L L' h x).symm)
  map_add' x y := by
    simpa only using
      DirectLimit.lift_add (f := fun (L L' : Lvl k K Ω) (h : L ≤ L') => altMap M L L' h)
        (g := fun L => g L)
        (fun L L' h x => (hg L L' h x).symm) x y

@[simp] theorem AltLim.lift_of (M : Rep.{0} Coeff (K ≃ₐ[k] K)) {X : Type} [AddCommMonoid X]
    (g : ∀ L : Lvl k K Ω, AltLeaf M L →+ X)
    (hg : ∀ (L L' : Lvl k K Ω) (h : L ≤ L') (y : AltLeaf M L),
      g L' (altMap M L L' h y) = g L y) (L : Lvl k K Ω) (y : AltLeaf M L) :
    AltLim.lift M g hg (AltLim.of M L y) = g L y := rfl

theorem AltLim.of_inflHIn (M : Rep.{0} Coeff (K ≃ₐ[k] K)) (L L' : Lvl k K Ω)
    (h : L.1 ≤ L'.1) (y : AltLeaf M L) :
    AltLim.of M L' (inflHIn (k := k) (K := K) h y) = AltLim.of M L y :=
  AltLim.of_altMap M (show L ≤ L' from h) y

/-- The canonical map `ClassLevelLimit.of` is compatible with inflation (in the `inflCIn` form). -/
theorem ClassLevelLimit.of_inflCIn {L L' : Lvl k K Ω} (h : L.1 ≤ L'.1)
    (y : ClassLevel (k := k) (K := K) L) :
    ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L' (inflCIn (k := k) h y)
      = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L y :=
  ClassLevelLimit.of_levelMap (k := k) (K := K) (Ω := Ω) (show L ≤ L' from h) y

/-! ## 2. The pairing `ψ = φ¹(x)` on `V` -/

/-- **`ψ = φ¹(x)` on the colimit `V`.** -/
noncomputable def psiInf (M : Rep.{0} Coeff (K ≃ₐ[k] K))
    (x : Abelian.Ext.{0} M (classesK k K) 1) :
    AltLim (Ω := Ω) M →+ ClassLevelLimit (k := k) (K := K) (Ω := Ω) :=
  AltLim.lift M
    (fun L => (ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L).comp
      (phiAtHomRight (k := k) (K := K) (L := L.1) x))
    (by
      intro L L' h y
      show ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L'
          (phiAt (k := k) (K := K) (L := L'.1) x
            (inflHIn (k := k) (K := K) (show L.1 ≤ L'.1 from h) y))
        = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L
            (phiAt (k := k) (K := K) (L := L.1) x y)
      rw [← phiAt_level_infl (k := k) (K := K) (Ω := Ω) (L := L.1) (L' := L'.1)
        (show L.1 ≤ L'.1 from h) M x y]
      exact ClassLevelLimit.of_levelMap (k := k) (K := K) (Ω := Ω)
        (show L.1 ≤ L'.1 from h) _)

@[simp] theorem psiInf_of (M : Rep.{0} Coeff (K ≃ₐ[k] K))
    (x : Abelian.Ext.{0} M (classesK k K) 1) (L : Lvl k K Ω) (y : AltLeaf M L) :
    psiInf (Ω := Ω) M x (AltLim.of M L y)
      = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L
          (phiAt (k := k) (K := K) (L := L.1) x y) := rfl



/-! ## 3. The local submodules -/

/-- The additive map `h ↦ extHRestrict D h`. -/
def extHRestrictHomAdd {G : Type} [Group G] (D : Subgroup G) {A : Rep.{0} Coeff G} (n : ℕ) :
    extH A n →+ extH (Rep.res D.subtype A) n where
  toFun y := extHRestrict D y
  map_zero' := E6Util.extHMap_zero D.subtype (𝟙 (Rep.res D.subtype A))
  map_add' a b := extHRestrict_add D a b

/-- Membership in an intersection of kernels indexed by a subtype (build speed: proved once
for abstract data; `mem_KlLoc` instantiates it). -/
private theorem mem_iInf_ker_subtype_iff {A : Type*} [AddGroup A] {ι : Type*} {B : ι → Type*}
    [∀ i, AddGroup (B i)] (P : ι → Prop) (f : ∀ i, A →+ B i) (x : A) :
    x ∈ ⨅ w : {i // P i}, (f w.1).ker ↔ ∀ i, P i → f i x = 0 := by
  simp only [AddSubgroup.mem_iInf, AddMonoidHom.mem_ker, Subtype.forall]

/-- The doubly indexed version of `mem_iInf_ker_subtype_iff` (for `mem_KlUnram`). -/
private theorem mem_iInf_iInf_ker_subtype_iff {A : Type*} [AddGroup A] {ι κ : Type*}
    {B : κ → Type*} [∀ D, AddGroup (B D)] (P : ι → Prop) (R : ι → κ → Prop)
    (f : ∀ D, A →+ B D) (x : A) :
    x ∈ ⨅ q : {q // P q}, ⨅ D : {D // R q.1 D}, (f D.1).ker ↔
      ∀ q, P q → ∀ D, R q D → f D x = 0 := by
  simp only [AddSubgroup.mem_iInf, AddMonoidHom.mem_ker, Subtype.forall]

section Local

variable (M : Rep.{0} Coeff (K ≃ₐ[k] K))

/-- Local triviality at every place over `v`: the intersection over the places `w` of `L` above
`v` of the kernels of `h ↦ extHRestrict (stab w) h`. -/
noncomputable def KlLoc (v : NK.GlobalCFT.Place K) (L : Lvl k K Ω) :
    AddSubgroup (extH (Rep.res (galRes k K L.1) M) 1) :=
  ⨅ (w : {w : NK.GlobalCFT.Place ↥L.1 // NK.GlobalCFT.Place.LiesOver w v}),
    AddMonoidHom.ker (extHRestrictHomAdd (G := ↥L.1 ≃ₐ[k] ↥L.1)
      (A := Rep.res (galRes k K L.1) M) (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w.1) 1)

theorem mem_KlLoc (v : NK.GlobalCFT.Place K) (L : Lvl k K Ω)
    (h : extH (Rep.res (galRes k K L.1) M) 1) :
    h ∈ KlLoc M v L ↔
      ∀ (w : NK.GlobalCFT.Place ↥L.1), NK.GlobalCFT.Place.LiesOver w v →
        extHRestrict (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w) h = 0 :=
  mem_iInf_ker_subtype_iff (fun w : NK.GlobalCFT.Place ↥L.1 => NK.GlobalCFT.Place.LiesOver w v)
    (fun w => extHRestrictHomAdd (G := ↥L.1 ≃ₐ[k] ↥L.1) (A := Rep.res (galRes k K L.1) M)
      (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w) 1) h

/-- Unramifiedness at every finite place over `v`. -/
noncomputable def KlUnram (v : NK.GlobalCFT.Place K) (L : Lvl k K Ω) :
    AddSubgroup (extH (Rep.res (galRes k K L.1) M) 1) :=
  ⨅ (q : {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L.1) //
      NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q) v}),
    ⨅ (D : {D : Subgroup (↥L.1 ≃ₐ[k] ↥L.1) // ∀ σ ∈ D.1, IsInertiaAt q.1 σ}),
      AddMonoidHom.ker (extHRestrictHomAdd (G := ↥L.1 ≃ₐ[k] ↥L.1)
        (A := Rep.res (galRes k K L.1) M) D.1 1)

theorem mem_KlUnram (v : NK.GlobalCFT.Place K) (L : Lvl k K Ω)
    (h : extH (Rep.res (galRes k K L.1) M) 1) :
    h ∈ KlUnram M v L ↔
      ∀ (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L.1)),
        NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q) v →
        IsUnramifiedClassAt q h :=
  mem_iInf_iInf_ker_subtype_iff
    (fun q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L.1) =>
      NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q) v)
    (fun q (D : Subgroup (↥L.1 ≃ₐ[k] ↥L.1)) => ∀ σ ∈ D, IsInertiaAt q σ)
    (fun D => extHRestrictHomAdd (G := ↥L.1 ≃ₐ[k] ↥L.1) (A := Rep.res (galRes k K L.1) M) D 1) h

/-- **The local submodule at `(v, L)`**: locally trivial at every place over `v` when `v ∈ S`
(so that clause (3) holds), and unramified at every finite place over `v` when `v ∉ S` (so that
clause (4) holds). -/
noncomputable def Kl (S : Finset (NK.GlobalCFT.Place K)) (v : NK.GlobalCFT.Place K)
    (L : Lvl k K Ω) : AddSubgroup (extH (Rep.res (galRes k K L.1) M) 1) := by
  classical
  exact if v ∈ S then KlLoc M v L else KlUnram M v L

theorem mem_Kl (S : Finset (NK.GlobalCFT.Place K)) (v : NK.GlobalCFT.Place K) (L : Lvl k K Ω)
    (h : extH (Rep.res (galRes k K L.1) M) 1) :
    h ∈ Kl M S v L ↔
      (v ∈ S → ∀ (w : NK.GlobalCFT.Place ↥L.1), NK.GlobalCFT.Place.LiesOver w v →
        extHRestrict (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w) h = 0) ∧
      (v ∉ S → ∀ (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L.1)),
        NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q) v →
        IsUnramifiedClassAt q h) := by
  classical
  unfold Kl
  by_cases hv : v ∈ S
  · rw [if_pos hv, mem_KlLoc]
    exact ⟨fun hh => ⟨fun _ => hh, fun hc => absurd hv hc⟩, fun hh => hh.1 hv⟩
  · rw [if_neg hv, mem_KlUnram]
    exact ⟨fun hh => ⟨fun hc => absurd hc hv, fun _ => hh⟩, fun hh => hh.2 hv⟩

/-- **Ascent of the local condition.** -/
theorem Kl_ascent (S : Finset (NK.GlobalCFT.Place K)) (v : NK.GlobalCFT.Place K)
    {L L' : Lvl k K Ω} (hLL : L ≤ L') (h : AltLeaf M L) (hh : h ∈ Kl M S v L) :
    altMap M L L' hLL h ∈ Kl M S v L' := by
  classical
  rw [mem_Kl] at hh ⊢
  refine ⟨?_, ?_⟩
  · intro hv w' hw'
    have key := extHRestrict_inflHIn_eq_zero_of_forall (k := k) (K := K) (Ω := Ω) M L.1 L'.1
      (show L.1 ≤ L'.1 from hLL) v h (fun w hw => hh.1 hv w hw)
    rw [altMap_apply]
    exact key w' hw'
  · intro hv q' hq'
    rw [altMap_apply]
    exact E9b.unramified_inflHIn k K Ω M L.1 L'.1 (show L.1 ≤ L'.1 from hLL) v h
      (fun q hq => hh.2 hv q hq) q' hq'

/-- `LocTriv` transfers along the Galois action on places. -/
theorem extHRestrict_stab_eq_zero_of_smul_eq {M : Rep Coeff (K ≃ₐ[k] K)} {L : Lvl k K Ω}
    {w w' : NK.GlobalCFT.Place ↥L.1} {σ : ↥L.1 ≃ₐ[k] ↥L.1} (hσ : σ • w = w')
    {h : AltLeaf M L}
    (hh : extHRestrict (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w) h = 0) :
    extHRestrict (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w') h = 0 := by
  rw [← hσ, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact extHRestrict_conj_eq_zero _ σ h hh

/-- Unramifiedness transfers along the Galois action on finite places. -/
theorem isUnramifiedAt_smulHeightOneSpectrum_of {M : Rep Coeff (K ≃ₐ[k] K)} {L : Lvl k K Ω}
    {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L.1)}
    {σ : ↥L.1 ≃ₐ[k] ↥L.1} {h : AltLeaf M L} (hh : IsUnramifiedClassAt q h) :
    IsUnramifiedClassAt (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q) h :=
  (E9b.isUnramifiedClassAt_smulHeightOneSpectrum_iff q σ h).mp hh

/-- **The local submodule is Galois-invariant.** -/
theorem Kl_le_smul (S : Finset (NK.GlobalCFT.Place K))
    (hSstab : ∀ v ∈ S, ∀ σ : K ≃ₐ[k] K, σ • v ∈ S)
    (M : Rep Coeff (K ≃ₐ[k] K)) (σ : K ≃ₐ[k] K) (v : NK.GlobalCFT.Place K)
    (L : Lvl k K Ω) : Kl M S v L ≤ Kl M S (σ • v) L := by
  classical
  have hstab : σ • v ∈ S ↔ v ∈ S := by
    constructor
    · intro h
      have := hSstab (σ • v) h σ⁻¹
      rwa [inv_smul_smul] at this
    · intro h; exact hSstab v h σ
  intro h hh
  rw [mem_Kl] at hh ⊢
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) (E := ↥L.1) σ
  refine ⟨fun hvS w hw => ?_, fun hvS q' hq' => ?_⟩
  · -- `τ⁻¹ • w` lies over `v`
    have hlies : NK.GlobalCFT.Place.LiesOver (τ⁻¹ • w) v := by
      have h1 := NK.HassePrinciple.liesOver_smul_of_restrict (K := k) (F := K) (L := ↥L.1) τ⁻¹
        (galRes k K ↥L.1 τ⁻¹) (fun y => AlgEquiv.restrictNormal_commutes τ⁻¹ K y) hw
      have h2 : galRes k K ↥L.1 τ⁻¹ • (σ • v) = v := by
        rw [show galRes k K ↥L.1 τ⁻¹ = σ⁻¹ from by
          rw [← hτ]; simp [map_inv], inv_smul_smul]
      rwa [h2] at h1
    exact extHRestrict_stab_eq_zero_of_smul_eq (σ := τ)
      (by rw [smul_inv_smul]) ((hh.1 (hstab.mp hvS)) _ hlies)
  · -- `τ⁻¹ • q'` lies over `v`
    have hqlies : NK.GlobalCFT.Place.LiesOver
        (NK.GlobalCFT.Place.ofFinite (NK.GlobalCFT.Place.smulHeightOneSpectrum τ⁻¹ q')) v := by
      rw [← NK.GlobalCFT.Place.smul_ofFinite]
      have h1 := NK.HassePrinciple.liesOver_smul_of_restrict (K := k) (F := K) (L := ↥L.1) τ⁻¹
        (galRes k K ↥L.1 τ⁻¹) (fun y => AlgEquiv.restrictNormal_commutes τ⁻¹ K y) hq'
      have h2 : galRes k K ↥L.1 τ⁻¹ • (σ • v) = v := by
        rw [show galRes k K ↥L.1 τ⁻¹ = σ⁻¹ from by
          rw [← hτ]; simp [map_inv], inv_smul_smul]
      rwa [h2] at h1
    have h1 : IsUnramifiedClassAt (NK.GlobalCFT.Place.smulHeightOneSpectrum τ⁻¹ q') h :=
      (hh.2 (fun hc => hvS (hstab.mpr hc))) _ hqlies
    have h2 := isUnramifiedAt_smulHeightOneSpectrum_of (σ := τ) h1
    have hcomp : NK.GlobalCFT.Place.smulHeightOneSpectrum τ
        (NK.GlobalCFT.Place.smulHeightOneSpectrum τ⁻¹ q') = q' := by
      apply NK.GlobalCFT.Place.ofFinite_inj.mp
      rw [← NK.GlobalCFT.Place.smul_ofFinite, ← NK.GlobalCFT.Place.smul_ofFinite, smul_inv_smul]
    rwa [hcomp] at h2

/-- **The upper bound of two levels.** -/
noncomputable def Lvl.sup (L L' : Lvl k K Ω) : Lvl k K Ω :=
  ⟨L.1 ⊔ L'.1, inferInstance, inferInstance, isGalois_sup (L := L.1) (L' := L'.1)⟩

theorem Lvl.le_sup_left (L L' : Lvl k K Ω) : L ≤ Lvl.sup L L' :=
  show L.1 ≤ L.1 ⊔ L'.1 from _root_.le_sup_left

theorem Lvl.le_sup_right (L L' : Lvl k K Ω) : L' ≤ Lvl.sup L L' :=
  show L'.1 ≤ L.1 ⊔ L'.1 from _root_.le_sup_right

theorem Lvl.exists_upper_bound (s : Finset (Lvl k K Ω)) :
    ∃ M : Lvl k K Ω, ∀ L ∈ s, L ≤ M := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary (Lvl k K Ω), by simp⟩
  | insert a s ha ih =>
      obtain ⟨M, hM⟩ := ih
      refine ⟨Lvl.sup a M, ?_⟩
      intro L hL
      rw [Finset.mem_insert] at hL
      rcases hL with rfl | hL
      · exact Lvl.le_sup_left _ _
      · exact (hM L hL).trans (Lvl.le_sup_right _ _)

/-- **The colimit-level local submodule** `U_v = ⋃_L of_L(Kl_v L)`. -/
noncomputable def Uv (S : Finset (NK.GlobalCFT.Place K)) (v : NK.GlobalCFT.Place K) :
    AddSubgroup (AltLim (Ω := Ω) M) :=
  ⨆ (L : Lvl k K Ω), (Kl M S v L).map (AltLim.of M L)

theorem Kl_directed (S : Finset (NK.GlobalCFT.Place K)) (v : NK.GlobalCFT.Place K) :
    Directed (· ≤ ·) (fun L : Lvl k K Ω => (Kl M S v L).map (AltLim.of M L)) := by
  intro L L'
  refine ⟨Lvl.sup L L', ?_, ?_⟩
  · intro x hx
    rw [AddSubgroup.mem_map] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨altMap M L (Lvl.sup L L') (Lvl.le_sup_left L L') y,
      Kl_ascent M S v (Lvl.le_sup_left L L') y hy,
      AltLim.of_altMap M (Lvl.le_sup_left L L') y⟩
  · intro x hx
    rw [AddSubgroup.mem_map] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨altMap M L' (Lvl.sup L L') (Lvl.le_sup_right L L') y,
      Kl_ascent M S v (Lvl.le_sup_right L L') y hy,
      AltLim.of_altMap M (Lvl.le_sup_right L L') y⟩

theorem mem_Uv (S : Finset (NK.GlobalCFT.Place K)) (v : NK.GlobalCFT.Place K)
    (y : AltLim (Ω := Ω) M) :
    y ∈ Uv M S v ↔ ∃ (L : Lvl k K Ω) (x : AltLeaf M L), x ∈ Kl M S v L ∧
      AltLim.of M L x = y := by
  rw [Uv, AddSubgroup.mem_iSup_of_directed (Kl_directed M S v)]
  constructor
  · rintro ⟨L, hL⟩
    rw [AddSubgroup.mem_map] at hL
    obtain ⟨x, hx, hxy⟩ := hL
    exact ⟨L, x, hx, hxy⟩
  · rintro ⟨L, x, hx, rfl⟩
    exact ⟨L, AddSubgroup.mem_map.mpr ⟨x, hx, rfl⟩⟩


/-- **The colimit-level local submodules are Galois-invariant.** -/
theorem Uv_le_smul (S : Finset (NK.GlobalCFT.Place K))
    (hSstab : ∀ v ∈ S, ∀ σ : K ≃ₐ[k] K, σ • v ∈ S)
    (M : Rep Coeff (K ≃ₐ[k] K)) (σ : K ≃ₐ[k] K) (v : NK.GlobalCFT.Place K) :
    Uv (Ω := Ω) M S v ≤ Uv (Ω := Ω) M S (σ • v) := by
  intro y hy
  rw [mem_Uv (Ω := Ω)] at hy ⊢
  obtain ⟨L, x, hx, rfl⟩ := hy
  exact ⟨L, x, Kl_le_smul S hSstab M σ v L hx, rfl⟩

end Local

/-! ## 4. The two inputs of the abstract decomposition -/

/-- **The set of places at which a level class is not locally trivial is finite.**
For `h ∈ H¹(Gal(L/k), M)`, only finitely many places `v` of `K` have `h ∉ Kl M S v L`:
`h` is unramified at all but finitely many finite places of `L` and `S` is finite. -/
theorem Kl_notMem_finite (p : ℕ) [Fact p.Prime] (M : Rep Coeff (K ≃ₐ[k] K))
    (S : Finset (NK.GlobalCFT.Place K)) (L : Lvl k K Ω) (h : AltLeaf M L) :
    {v : NK.GlobalCFT.Place K | h ∉ Kl M S v L}.Finite := by
  classical
  have hram : ({q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L.1) |
      ¬ IsUnramifiedClassAt (M := Rep.res (galRes k K L.1) M) q h} : Set _).Finite :=
    E9Nodes.e9_unramified_all_but_finite k ↥L.1 (Rep.res (galRes k K L.1) M) h
  let pb : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L.1) →
      NK.GlobalCFT.Place K := fun q =>
    Classical.choose (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := ↥L.1)
      (NK.GlobalCFT.Place.ofFinite q))
  have pb_spec : ∀ q, NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q) (pb q) :=
    fun q => Classical.choose_spec _
  refine (S.finite_toSet.union (hram.image pb)).subset ?_
  intro v hv
  rw [Set.mem_setOf_eq] at hv
  by_cases hvS : v ∈ S
  · exact Set.mem_union_left _ hvS
  · refine Set.mem_union_right _ ?_
    have h1 : h ∉ KlUnram M v L := by
      intro hmem
      exact hv ((mem_Kl M S v L h).mpr
        ⟨fun hc => absurd hc hvS, fun _ => (mem_KlUnram M v L h).mp hmem⟩)
    rw [mem_KlUnram] at h1
    push_neg at h1
    obtain ⟨q, hq, hqr⟩ := h1
    refine ⟨q, hqr, ?_⟩
    exact place_liesOver_unique (K := K) (L := ↥L.1) (NK.GlobalCFT.Place.ofFinite q)
      (pb_spec q) hq

/-- **`ψ = φ¹(x)` vanishes on the intersection of the local submodules.**
If a class of the colimit `V` is locally trivial (resp. unramified) at every place in the sense
of the submodules `Uv`, then the whole family of local conditions is satisfied at a single
suffiently large level, where the hypothesis `hS` kills `φ¹(x)`. -/
theorem psiInf_eq_zero_of_mem_iInter (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep Coeff (K ≃ₐ[k] K)) (hM : ∀ m : M, p • m = 0)
    (x : Abelian.Ext M (classesK k K) 1) (S : Finset (NK.GlobalCFT.Place K))
    (hSstab : ∀ v ∈ S, ∀ σ : K ≃ₐ[k] K, σ • v ∈ S)
    (hS : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (h : extH (Rep.res (galRes k K L) M) 1),
        (∀ w' : NK.GlobalCFT.Place L, (∃ v ∈ S, NK.GlobalCFT.Place.LiesOver w' v) →
          extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h = 0) →
        (∀ q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
          IsUnramifiedClassAt q' h) →
        phiAt (k := k) (K := K) (L := L) x h = 0) :
    ∀ y : AltLim (Ω := Ω) M, (∀ v : NK.GlobalCFT.Place K, y ∈ Uv M S v) → psiInf (Ω := Ω) M x y = 0 := by
  classical
  intro y
  refine AltLim.induction M (C := fun y => (∀ v : NK.GlobalCFT.Place K, y ∈ Uv M S v) →
    psiInf (Ω := Ω) M x y = 0) ?_ y
  intro L h hy
  have hbad : ({v : NK.GlobalCFT.Place K | h ∉ Kl M S v L} : Set _).Finite :=
    Kl_notMem_finite p M S L h
  let B : Finset (NK.GlobalCFT.Place K) := hbad.toFinset
  have hBmem : ∀ v, v ∈ B ↔ h ∉ Kl M S v L := by
    intro v
    rw [show B = hbad.toFinset from rfl, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hwit : ∀ v : NK.GlobalCFT.Place K, ∃ w : Sigma (fun Lv : Lvl k K Ω => AltLeaf M Lv),
      w.2 ∈ Kl M S v w.1 ∧ AltLim.of M w.1 w.2 = AltLim.of M L h := by
    intro v
    by_cases hv : v ∈ B
    · obtain ⟨L0, x0, hx0, heq0⟩ := (mem_Uv M S v (AltLim.of M L h)).mp (hy v)
      exact ⟨⟨L0, x0⟩, hx0, heq0⟩
    · refine ⟨⟨L, h⟩, ?_, rfl⟩
      by_contra hc
      exact hv ((hBmem v).mpr hc)
  choose wv hwv using hwit
  have hstep : ∀ v : NK.GlobalCFT.Place K, ∃ Mv : Lvl k K Ω, ∃ (hLMv : L ≤ Mv),
      altMap M L Mv hLMv h ∈ Kl M S v Mv := by
    intro v
    obtain ⟨j, hLvj, hLj, heq'⟩ := Quotient.exact (hwv v).2
    exact ⟨j, hLj, by
      rw [← heq']
      exact Kl_ascent M S v hLvj (wv v).2 (hwv v).1⟩
  choose Mv hLMv hmem using hstep
  have hsup : ∃ M' : Lvl k K Ω, L ≤ M' ∧ ∀ v ∈ B, Mv v ≤ M' := by
    induction B using Finset.induction_on with
    | empty => exact ⟨L, le_rfl, by simp⟩
    | insert a s ha ih =>
        obtain ⟨M0, hLM0, hM0⟩ := ih
        refine ⟨Lvl.sup (Mv a) M0, ?_, ?_⟩
        · exact hLM0.trans (Lvl.le_sup_right _ _)
        · intro v hv
          rw [Finset.mem_insert] at hv
          rcases hv with rfl | hv
          · exact Lvl.le_sup_left _ _
          · exact (hM0 v hv).trans (Lvl.le_sup_right _ _)
  obtain ⟨M', hLM', hM'mem⟩ := hsup
  have hKl : ∀ v : NK.GlobalCFT.Place K, altMap M L M' hLM' h ∈ Kl M S v M' := by
    intro v
    by_cases hv : v ∈ B
    · rw [← show altMap M (Mv v) M' (hM'mem v hv) (altMap M L (Mv v) (hLMv v) h)
          = altMap M L M' hLM' h
          from altMap_map M L (Mv v) M' (hLMv v) (hM'mem v hv) h]
      exact Kl_ascent M S v (hM'mem v hv) (altMap M L (Mv v) (hLMv v) h) (hmem v)
    · have hhL : h ∈ Kl M S v L := by
        by_contra hc
        exact hv ((hBmem v).mpr hc)
      exact Kl_ascent M S v hLM' h hhL
  have hzero : phiAt (k := k) (K := K) (L := ↥M'.1) x (altMap M L M' hLM' h) = 0 := by
    refine hS M'.1 (altMap M L M' hLM' h) ?_ ?_
    · intro w' hw'
      obtain ⟨u, huS, huw'⟩ := hw'
      exact ((mem_Kl M S u M' (altMap M L M' hLM' h)).mp (hKl u)).1 huS w' huw'
    · intro q'
      obtain ⟨u, huq⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := ↥M'.1)
        (NK.GlobalCFT.Place.ofFinite q')
      by_cases huS : u ∈ S
      · have hloc : extHRestrict (MulAction.stabilizer (↥M'.1 ≃ₐ[k] ↥M'.1)
            (NK.GlobalCFT.Place.ofFinite q')) (altMap M L M' hLM' h) = 0 :=
          ((mem_Kl M S u M' (altMap M L M' hLM' h)).mp (hKl u)).1 huS _ huq
        obtain ⟨v, huv⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := k) (L := K) u
        have hq'v : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') v :=
          place_liesOver_trans huq huv
        exact E9b.locTriv_subset_unram (M := Rep.res (galRes k K ↥M'.1) M) v
          (NK.GlobalCFT.Place.ofFinite q') q' hq'v hq'v _ hloc
      · exact ((mem_Kl M S u M' (altMap M L M' hLM' h)).mp (hKl u)).2 huS q' huq
  rw [psiInf_of]
  have h1 : ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L
      (phiAt (k := k) (K := K) (L := L.1) x h) = 0 := by
    rw [← ClassLevelLimit.of_levelMap (k := k) (K := K) (Ω := Ω) hLM'
      (phiAt (k := k) (K := K) (L := L.1) x h)]
    rw [show classLevelMap (k := k) L M' hLM' (phiAt (k := k) (K := K) (L := L.1) x h)
        = inflCIn (k := k) hLM' (phiAt (k := k) (K := K) (L := L.1) x h) from rfl]
    rw [phiAt_level_infl (k := k) (K := K) (Ω := Ω) L.1 M'.1 (show L.1 ≤ M'.1 from hLM')
      M x h]
    rw [show inflHIn (k := k) (K := K) (show L.1 ≤ M'.1 from hLM') h = altMap M L M' hLM' h
        from rfl]
    rw [hzero, ClassLevelLimit.of_zero]
  exact h1

/-! ## 5. The main theorem -/

/-- **E9b (decomposition into local families).** -/
theorem e9_local_decomposition (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (x : Abelian.Ext M (classesK k K) 1) (S : Finset (NK.GlobalCFT.Place K))
    (hSarch : ∀ v : NK.GlobalCFT.Place K,
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        v ≠ NK.GlobalCFT.Place.ofFinite q) → v ∈ S)
    (hSbad : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      NK.GlobalCFT.Place.ofFinite q ∉ S →
        (p : NumberField.RingOfIntegers K) ∉ q.asIdeal ∧
        ∀ σ : K ≃ₐ[k] K, IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m)
    (hSstab : ∀ v ∈ S, ∀ σ : K ≃ₐ[k] K, σ • v ∈ S)
    (hS : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (h : extH (Rep.res (galRes k K L) M) 1),
        (∀ w' : NK.GlobalCFT.Place L, (∃ v ∈ S, NK.GlobalCFT.Place.LiesOver w' v) →
          extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h = 0) →
        (∀ q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
          IsUnramifiedClassAt q' h) →
        phiAt (k := k) (K := K) (L := L) x h = 0) :
    ∃ lam : R → ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L]
        [IsGalois k L], extH (Rep.res (galRes k K L) M) 1 →+ extH (classesK k L) 2,
      (∀ (v : R) (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L]
        [IsGalois k L] (h : extH (Rep.res (galRes k K L) M) 1), p • lam v L h = 0) ∧
      (∀ (v : R) (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L]
        [IsGalois k L] (L' : IntermediateField K Ω) [NumberField L'] [FiniteDimensional k L']
        [IsGalois k L'] (hLL : L ≤ L') (h : extH (Rep.res (galRes k K L) M) 1),
        inflCIn (k := k) hLL (lam v L h) = lam v L' (inflHIn (k := k) hLL h)) ∧
      (∀ (v : R) (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L]
        [IsGalois k L], ∃ w' : NK.GlobalCFT.Place L, NK.GlobalCFT.Place.LiesOver w' v.1 ∧
          ∀ h : extH (Rep.res (galRes k K L) M) 1,
            extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h = 0 → lam v L h = 0) ∧
      (∀ v : R, v.1 ∉ S →
        ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
          (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)),
          NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') v.1 →
          ∀ h : extH (Rep.res (galRes k K L) M) 1, IsUnramifiedClassAt q' h → lam v L h = 0) ∧
      ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (h : extH (Rep.res (galRes k K L) M) 1),
        (Function.support (fun v : R => lam v L h)).Finite ∧
        phiAt (k := k) (K := K) (L := L) x h = ∑ᶠ v : R, lam v L h := by
  classical
  obtain ⟨χ, hχ⟩ := E9b.chi_pTor_classLevelLimit p k K Ω
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hVtor : ∀ y : AltLim (Ω := Ω) M, p • y = 0 := by
    intro y
    exact AltLim.induction M (C := fun y => p • y = 0) (fun L h => by
      show p • AltLim.of M L h = 0
      rw [← map_nsmul (AltLim.of M L) p h,
        E6Util.ext_nsmul_p_torsion (G := (↥L.1 ≃ₐ[k] ↥L.1)) p
          (A := Rep.res (galRes k K L.1) M) (fun a => hM a) h, map_zero]) y
  have hpsi_tor : ∀ y : AltLim (Ω := Ω) M, p • psiInf (Ω := Ω) M x y = 0 := by
    intro y
    rw [← map_nsmul (psiInf (Ω := Ω) M x) p y, hVtor y, map_zero]
  have hfin : ∀ y : AltLim (Ω := Ω) M, {v : R | y ∉ Uv M S v.1}.Finite := by
    intro y
    refine AltLim.induction M (C := fun y => {v : R | y ∉ Uv M S v.1}.Finite) ?_ y
    intro L h
    refine ((Kl_notMem_finite p M S L h).preimage (f := fun v : R => v.1)
      (fun a _ b _ hab => Subtype.ext hab)).subset ?_
    intro v hv
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hv ⊢
    intro hc
    exact hv ((mem_Uv M S v.1 (AltLim.of M L h)).mpr ⟨L, h, hc, rfl⟩)
  have hker : ∀ y : AltLim (Ω := Ω) M, (∀ v : R, y ∈ Uv M S v.1) → psiInf (Ω := Ω) M x y = 0 := by
    intro y hy
    apply psiInf_eq_zero_of_mem_iInter p k K Ω M hM x S hSstab hS y
    intro u
    obtain ⟨v, hv, -⟩ := hR u
    obtain ⟨σ, hσ⟩ := hv
    have hu : u = σ⁻¹ • v.1 := by rw [← hσ, inv_smul_smul]
    rw [hu]
    exact Uv_le_smul S hSstab M σ⁻¹ v.1 (hy v)
  letI : Module (ZMod p) (AltLim (Ω := Ω) M) := AddCommGroup.zmodModule hVtor
  letI : Module (ZMod p) ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω))) :=
    AddCommGroup.zmodModule (fun y => Subtype.ext y.2)
  let ψp : AltLim (Ω := Ω) M →+ ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω))) :=
    { toFun := fun y => ⟨psiInf (Ω := Ω) M x y, by rw [mem_pTor]; exact hpsi_tor y⟩
      map_zero' := by apply Subtype.ext; simp
      map_add' := fun a b => by apply Subtype.ext; simp }
  obtain ⟨f, hfker, hffin, hfsum⟩ :=
    exists_finsupp_decomposition_aux (V := AltLim (Ω := Ω) M)
      (X := ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω)))) (ι := R)
      p (fun v : R => Uv M S v.1) hfin
      (AddMonoidHom.toZModLinearMap p ψp)
      (fun y hy => Subtype.ext (hker y hy))
  let pTorToA : ∀ (L : Lvl k K Ω),
      ↥(pTor p (ClassLevel (k := k) (K := K) L)) →
        ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω))) :=
    fun L y => ⟨ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L y.1, by
      rw [mem_pTor, ← map_nsmul, y.2, map_zero]⟩
  let chiLh : ∀ (L : Lvl k K Ω),
      ↥(pTor p (ClassLevel (k := k) (K := K) L)) →+ ZMod p :=
    fun L =>
      { toFun := fun y => χ (pTorToA L y),
        map_zero' := by
          have h0 : pTorToA L 0 = 0 :=
            Subtype.ext (map_zero (ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L))
          rw [h0, map_zero],
        map_add' := fun a b => by
          have h0 : pTorToA L (a + b) = pTorToA L a + pTorToA L b :=
            Subtype.ext (map_add (ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L)
              (a : ClassLevel (k := k) (K := K) L) (b : ClassLevel (k := k) (K := K) L))
          rw [h0, map_add] }
  have chiL_bij : ∀ (L : Lvl k K Ω) (hp : p ∣ Module.finrank k ↥L.1),
      Function.Bijective ⇑(chiLh L) := by
    intro L hp
    have hinj : Function.Injective ⇑(chiLh L) := by
      intro y₁ y₂ h12
      apply Subtype.ext
      apply ClassLevelLimit.of_injective (k := k) (K := K) (Ω := Ω) L
      exact congrArg Subtype.val (hχ.1 h12)
    refine ⟨hinj, fun z => ?_⟩
    haveI : Finite ↥(pTor p (ClassLevel (k := k) (K := K) L)) :=
      Nat.finite_of_card_ne_zero (by
        rw [E9b.pTor_classLevel_card p k K Ω L hp]
        exact (Fact.out : p.Prime).ne_zero)
    haveI : Fintype ↥(pTor p (ClassLevel (k := k) (K := K) L)) := Fintype.ofFinite _
    have hcard : Fintype.card ↥(pTor p (ClassLevel (k := k) (K := K) L)) =
        Fintype.card (ZMod p) := by
      rw [ZMod.card p, ← Nat.card_eq_fintype_card]
      exact E9b.pTor_classLevel_card p k K Ω L hp
    have hcard' : (Finset.univ.image ⇑(chiLh L)).card = Fintype.card (ZMod p) := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, hcard]
    have hz : z ∈ Finset.univ.image ⇑(chiLh L) := by
      rw [Finset.eq_univ_of_card _ hcard']
      exact Finset.mem_univ z
    obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hz
    exact ⟨y, hy⟩
  let chiLe : ∀ (L : Lvl k K Ω) (hp : p ∣ Module.finrank k ↥L.1),
      ↥(pTor p (ClassLevel (k := k) (K := K) L)) ≃+ ZMod p :=
    fun L hp => AddEquiv.ofBijective (chiLh L) (chiL_bij L hp)
  let lamLvl : R → (L : Lvl k K Ω) → AltLeaf M L →+ ClassLevel (k := k) (K := K) L :=
    fun v L =>
      if hp : p ∣ Module.finrank k ↥L.1 then
        { toFun := fun h => ((chiLe L hp).symm (χ (f v (AltLim.of M L h)))).1,
          map_zero' := by
            show ((chiLe L hp).symm (χ (f v (AltLim.of M L 0)))).1 = 0
            exact (congrArg (fun s => ((chiLe L hp).symm (χ (f v s))).1) (AltLim.of_zero M L)).trans
              ((congrArg (fun s => ((chiLe L hp).symm (χ s)).1) (map_zero (f v))).trans
                ((congrArg (fun s => ((chiLe L hp).symm s).1) (map_zero χ)).trans
                  (congrArg Subtype.val (map_zero (chiLe L hp).symm)))),
          map_add' := fun a b => by
            show ((chiLe L hp).symm (χ (f v (AltLim.of M L (a + b))))).1
                = ((chiLe L hp).symm (χ (f v (AltLim.of M L a)))).1
                  + ((chiLe L hp).symm (χ (f v (AltLim.of M L b)))).1
            exact (congrArg (fun s => ((chiLe L hp).symm (χ (f v s))).1)
                (map_add (AltLim.of M L) a b)).trans
              ((congrArg (fun s => ((chiLe L hp).symm (χ s)).1) (map_add (f v) _ _)).trans
                ((congrArg (fun s => ((chiLe L hp).symm s).1) (map_add χ _ _)).trans
                  (congrArg Subtype.val (map_add (chiLe L hp).symm _ _)))) }
      else 0
  have hkey : ∀ (L : Lvl k K Ω) (h : AltLeaf M L) (v : R),
      ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L (lamLvl v L h)
        = (f v (AltLim.of M L h) : ClassLevelLimit (k := k) (K := K) (Ω := Ω)) := by
    intro L h v
    by_cases hp : p ∣ Module.finrank k ↥L.1
    · have h1 : lamLvl v L h
          = ((chiLe L hp).symm (χ (f v (AltLim.of M L h)))).1 := by
        dsimp only [lamLvl]
        rw [dif_pos hp]
        rfl
      rw [h1]
      have key : pTorToA L ((chiLe L hp).symm (χ (f v (AltLim.of M L h))))
          = f v (AltLim.of M L h) := by
        apply hχ.1
        exact AddEquiv.apply_symm_apply (chiLe L hp) (χ (f v (AltLim.of M L h)))
      exact congrArg Subtype.val key
    · have h1 : lamLvl v L h = 0 := by
        dsimp only [lamLvl]
        rw [dif_neg hp]
        rfl
      rw [h1, ClassLevelLimit.of_zero]
      haveI : Subsingleton (AltLeaf M L) :=
        E9Nodes.e9_bad_level_subsingleton p k K ↥L.1 M (fun a => hM a) hp
      rw [Subsingleton.elim h 0, AltLim.of_zero, map_zero (f v)]
      rfl
  have hcl_ker : ∀ (v : R) (L : Lvl k K Ω) (h : AltLeaf M L), h ∈ Kl M S v.1 L →
      lamLvl v L h = 0 := by
    intro v L h hmem
    apply ClassLevelLimit.of_injective (k := k) (K := K) (Ω := Ω) L
    rw [hkey L h v, ClassLevelLimit.of_zero]
    exact congrArg Subtype.val (hfker v (AltLim.of M L h)
      ((mem_Uv M S v.1 (AltLim.of M L h)).mpr ⟨L, h, hmem, rfl⟩))
  have hcl3 : ∀ (v : R) (L : Lvl k K Ω), ∃ w' : NK.GlobalCFT.Place ↥L.1,
      NK.GlobalCFT.Place.LiesOver w' v.1 ∧
      ∀ h : AltLeaf M L, extHRestrict (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w') h = 0 →
        lamLvl v L h = 0 := by
    intro v L
    obtain ⟨w', hw'⟩ : ∃ w' : NK.GlobalCFT.Place ↥L.1,
        NK.GlobalCFT.Place.LiesOver w' v.1 :=
      NK.GlobalCFT.Inclusion.exists_place_liesOver (K := K) (L := ↥L.1) v.1
    obtain ⟨u, hu⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := k) (L := K) v.1
    have hw'u : NK.GlobalCFT.Place.LiesOver w' u := place_liesOver_trans hw' hu
    refine ⟨w', hw', fun h hh => hcl_ker v L h ?_⟩
    rw [mem_Kl]
    refine ⟨fun hvS w hw => ?_, fun hvS q' hq' => ?_⟩
    · have hwu : NK.GlobalCFT.Place.LiesOver w u := place_liesOver_trans hw hu
      obtain ⟨σ, hσ⟩ :=
        NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver hwu hw'u
      have hσ' : σ⁻¹ • w' = w := by rw [← hσ, inv_smul_smul]
      have hstab : extHRestrict (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w) h = 0 := by
        rw [← hσ', MulAction.stabilizer_smul_eq_stabilizer_map_conj σ⁻¹ w']
        exact extHRestrict_conj_eq_zero (MulAction.stabilizer (↥L.1 ≃ₐ[k] ↥L.1) w') σ⁻¹ h hh
      exact hstab
    · have hqu : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') u :=
        place_liesOver_trans hq' hu
      exact E9b.locTriv_subset_unram (M := Rep.res (galRes k K ↥L.1) M) u w' q' hw'u hqu h hh
  have hcl4 : ∀ (v : R), v.1 ∉ S → ∀ (L : Lvl k K Ω)
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L.1)),
      NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') v.1 →
      ∀ h : AltLeaf M L, IsUnramifiedClassAt q' h → lamLvl v L h = 0 := by
    intro v hv L q' hq' h hunr
    refine hcl_ker v L h ?_
    rw [mem_Kl]
    refine ⟨fun hvS => absurd hvS hv, fun _ q'' hq'' => ?_⟩
    obtain ⟨u, hu⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := k) (L := K) v.1
    exact (E9b.isUnramifiedClassAt_conj (M := Rep.res (galRes k K ↥L.1) M) u q' q''
      (place_liesOver_trans hq' hu) (place_liesOver_trans hq'' hu) h).mp hunr
  have hcl5 : ∀ (L : Lvl k K Ω) (h : AltLeaf M L),
      (Function.support (fun v : R => lamLvl v L h)).Finite ∧
      phiAt (k := k) (K := K) (L := L.1) x h = ∑ᶠ v : R, lamLvl v L h := by
    intro L h
    have hfs : Function.HasFiniteSupport (fun v : R => f v (AltLim.of M L h)) := hffin _
    have hfs' : (Function.support (fun v : R => lamLvl v L h)).Finite := by
      refine hfs.subset (fun v hv => ?_)
      rw [Function.mem_support] at hv ⊢
      exact fun h0 => hv (ClassLevelLimit.of_injective (k := k) (K := K) (Ω := Ω) L
        (by rw [ClassLevelLimit.of_zero, hkey L h v, h0]; rfl))
    refine ⟨hfs', ?_⟩
    apply ClassLevelLimit.of_injective (k := k) (K := K) (Ω := Ω) L
    have h1 : ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L
          (phiAt (k := k) (K := K) (L := L.1) x h)
        = Subtype.val (∑ᶠ v : R, f v (AltLim.of M L h)) := by
      rw [show ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L
            (phiAt (k := k) (K := K) (L := L.1) x h)
          = Subtype.val (ψp (AltLim.of M L h)) from rfl]
      exact congrArg Subtype.val (hfsum (AltLim.of M L h))
    have h2 : Subtype.val (∑ᶠ v : R, f v (AltLim.of M L h))
        = ∑ᶠ v : R, ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L (lamLvl v L h) := by
      change AddSubgroup.subtype (pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω)))
          (∑ᶠ v : R, f v (AltLim.of M L h))
        = ∑ᶠ v : R, ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L (lamLvl v L h)
      rw [map_finsum (AddSubgroup.subtype
        (pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω)))) hfs]
      exact finsum_congr (fun v => (hkey L h v).symm)
    rw [h1, h2]
    exact (map_finsum (ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L) hfs').symm
  refine ⟨fun v L hL1 hL2 hL3 => lamLvl v ⟨L, hL1, hL2, hL3⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro v L hL1 hL2 hL3 h
    by_cases hp : p ∣ Module.finrank k ↥(⟨L, hL1, hL2, hL3⟩ : Lvl k K Ω).1
    · have h1 : lamLvl v ⟨L, hL1, hL2, hL3⟩ h
          = ((chiLe ⟨L, hL1, hL2, hL3⟩ hp).symm
              (χ (f v (AltLim.of M ⟨L, hL1, hL2, hL3⟩ h)))).1 := by
        dsimp only [lamLvl]
        rw [dif_pos hp]
        rfl
      rw [h1]
      exact ((chiLe ⟨L, hL1, hL2, hL3⟩ hp).symm
        (χ (f v (AltLim.of M ⟨L, hL1, hL2, hL3⟩ h)))).2
    · have h1 : lamLvl v ⟨L, hL1, hL2, hL3⟩ h = 0 := by
        dsimp only [lamLvl]
        rw [dif_neg hp]
        rfl
      rw [h1]
      exact nsmul_zero p
  · intro v L hL1 hL2 hL3 L' hL1' hL2' hL3' hLL h
    apply ClassLevelLimit.of_injective (k := k) (K := K) (Ω := Ω) ⟨L', hL1', hL2', hL3'⟩
    rw [ClassLevelLimit.of_inflCIn (L := ⟨L, hL1, hL2, hL3⟩) (L' := ⟨L', hL1', hL2', hL3'⟩)
      (show (⟨L, hL1, hL2, hL3⟩ : Lvl k K Ω).1 ≤ (⟨L', hL1', hL2', hL3'⟩ : Lvl k K Ω).1 from hLL)
      (lamLvl v ⟨L, hL1, hL2, hL3⟩ h)]
    have hdvd : Module.finrank k ↥(⟨L, hL1, hL2, hL3⟩ : Lvl k K Ω).1
        ∣ Module.finrank k ↥(⟨L', hL1', hL2', hL3'⟩ : Lvl k K Ω).1 := by
      letI : Algebra ↥L ↥L' := (IntermediateField.inclusion hLL).toRingHom.toAlgebra
      haveI : IsScalarTower k ↥L ↥L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      exact Module.finrank_dvd_finrank_right k ↥L ↥L'
    by_cases hp : p ∣ Module.finrank k ↥(⟨L, hL1, hL2, hL3⟩ : Lvl k K Ω).1
    · rw [hkey ⟨L, hL1, hL2, hL3⟩ h v]
      by_cases hp' : p ∣ Module.finrank k ↥(⟨L', hL1', hL2', hL3'⟩ : Lvl k K Ω).1
      · rw [hkey ⟨L', hL1', hL2', hL3'⟩ (inflHIn (k := k) (K := K) hLL h) v,
          AltLim.of_inflHIn (M := M) ⟨L, hL1, hL2, hL3⟩ ⟨L', hL1', hL2', hL3'⟩ hLL h]
      · exact absurd (dvd_trans hp hdvd) hp'
    · haveI : Subsingleton (AltLeaf M ⟨L, hL1, hL2, hL3⟩) :=
        E9Nodes.e9_bad_level_subsingleton p k K ↥L M (fun a => hM a) hp
      have h1 : lamLvl v ⟨L, hL1, hL2, hL3⟩ h = 0 := by
        rw [Subsingleton.elim h 0]
        exact map_zero _
      rw [h1, ClassLevelLimit.of_zero]
      have h2 : lamLvl v ⟨L', hL1', hL2', hL3'⟩ (inflHIn (k := k) (K := K) hLL h) = 0 := by
        have h0 : inflHIn (k := k) (K := K) hLL h = 0 := by
          rw [Subsingleton.elim h 0]
          exact map_zero (altMap M ⟨L, hL1, hL2, hL3⟩ ⟨L', hL1', hL2', hL3'⟩ hLL)
        rw [h0]
        exact map_zero _
      rw [h2, ClassLevelLimit.of_zero]
  · intro v L hL1 hL2 hL3
    obtain ⟨w', hw', hloc⟩ := hcl3 v ⟨L, hL1, hL2, hL3⟩
    exact ⟨w', hw', fun h hh => hloc h hh⟩
  · intro v hv L hL1 hL2 hL3 q' hq' h hunr
    exact hcl4 v hv ⟨L, hL1, hL2, hL3⟩ q' hq' h hunr
  · intro L hL1 hL2 hL3 h
    obtain ⟨hfs, hsum⟩ := hcl5 ⟨L, hL1, hL2, hL3⟩ h
    exact ⟨hfs, hsum⟩

end
