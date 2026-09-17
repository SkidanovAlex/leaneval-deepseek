import Mathlib
import Submission.Commons.Algebra.Lie.PBW.pbw_standardMonomial_basis

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Commons.Algebra.Lie.UniversalEnveloping

attribute [local instance 100] LieRing.ofAssociativeRing



universe u v u' v' w u_1 u_2

/-! ## ULift instances -/

instance uliftLieRing (L : Type u) [LieRing L] : LieRing (ULift.{w, u} L) where
  bracket x y := ULift.up ⁅x.down, y.down⁆
  add_lie x y z := ULift.ext _ _ (LieRing.add_lie x.down y.down z.down)
  lie_add x y z := ULift.ext _ _ (LieRing.lie_add x.down y.down z.down)
  lie_self x := ULift.ext _ _ (LieRing.lie_self x.down)
  leibniz_lie x y z := ULift.ext _ _ (LieRing.leibniz_lie x.down y.down z.down)

instance uliftLieAlgebra (K : Type u) (L : Type v) [Field K] [LieRing L] [LieAlgebra K L] :
    LieAlgebra (ULift.{w, u} K) (ULift.{w, v} L) where
  toModule := inferInstance
  lie_smul t x y := ULift.ext _ _ (LieAlgebra.lie_smul t.down x.down y.down)

instance uliftCharZero (K : Type u) [Field K] [CharZero K] : CharZero (ULift.{w, u} K) where
  cast_injective a b h :=
    CharZero.cast_injective (R := K) (by
      simpa using congrArg (ULift.down : ULift.{w, u} K → K) h)

/-! ## Same-universe PBW-based theorem -/

set_option maxHeartbeats 800000 in
theorem lift_incl_injective_sameUniverse {K L : Type u} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    (N : LieSubalgebra K L) :
    Function.Injective (UniversalEnvelopingAlgebra.lift K
      ((UniversalEnvelopingAlgebra.ι K).comp (N.incl : N →ₗ⁅K⁆ L))) := by
  classical
  obtain ⟨⟨I, e⟩⟩ := Module.Free.exists_basis (R := K) (M := N)
  have hlin : LinearIndependent K (fun i : I => (e i : L)) := by
    have hker : LinearMap.ker (Submodule.subtype (N : Submodule K L)) = ⊥ := by
      rw [LinearMap.ker_eq_bot]; exact Subtype.coe_injective
    exact e.linearIndependent.map' (Submodule.subtype (N : Submodule K L)) hker
  set sJ : Set L := Set.range (fun i : I => (e i : L)) with hsJ
  have hs : LinearIndepOn K id sJ := hlin.linearIndepOn_id
  let J : Set L := hs.extend (Set.subset_univ sJ)
  letI : LinearOrder J := linearOrderOfSTO WellOrderingRel
  let g : I → J := fun i => ⟨(e i : L), hs.subset_extend (Set.subset_univ sJ) (Set.mem_range_self i)⟩
  have hg : Function.Injective g := by
    intro i j hij
    exact hlin.injective (congrArg (fun x : J => (x : L)) hij)
  letI : LinearOrder I := LinearOrder.lift' g hg
  let eL : Module.Basis J K L := Module.Basis.extend hs
  have hEL : ∀ j : J, eL j = (j : L) := fun j => Module.Basis.extend_apply_self hs j
  obtain ⟨bN, hbN⟩ := _root_.Commons.Algebra.Lie.PBW.pbw_standardMonomial_basis K N I e
  obtain ⟨bL, hbL⟩ := _root_.Commons.Algebra.Lie.PBW.pbw_standardMonomial_basis K L J eL
  let F : {w : List I // w.Pairwise (fun a b : I => a ≤ b)} →
      {w : List J // w.Pairwise (fun a b : J => a ≤ b)} :=
    fun w => ⟨w.1.map g, by
      rw [List.pairwise_map]
      exact w.2.imp (fun {a b} hab => hab)⟩
  have hF : Function.Injective F := by
    intro w v hwv
    have h1 : w.1.map g = v.1.map g := congrArg Subtype.val hwv
    have h2 : w.1 = v.1 := List.map_injective_iff.mpr hg h1
    exact Subtype.ext h2
  have hcompat : ∀ w, (UniversalEnvelopingAlgebra.lift K
      ((UniversalEnvelopingAlgebra.ι K).comp (N.incl : N →ₗ⁅K⁆ L))) (bN w) = bL (F w) := by
    intro w
    have hFw : (F w).1 = w.1.map g := rfl
    rw [hbN w, hbL (F w), hFw, map_list_prod, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    rw [UniversalEnvelopingAlgebra.lift_ι_apply, hEL (g i)]
    rfl
  have hli : LinearIndependent K (fun w => (UniversalEnvelopingAlgebra.lift K
      ((UniversalEnvelopingAlgebra.ι K).comp (N.incl : N →ₗ⁅K⁆ L))) (bN w)) := by
    have h := bL.linearIndependent.comp F hF
    rwa [show (bL ∘ F) = (fun w => (UniversalEnvelopingAlgebra.lift K
      ((UniversalEnvelopingAlgebra.ι K).comp (N.incl : N →ₗ⁅K⁆ L))) (bN w)) from
        funext (fun w => (hcompat w).symm)] at h
  intro x y hxy
  have hsub : (UniversalEnvelopingAlgebra.lift K
      ((UniversalEnvelopingAlgebra.ι K).comp (N.incl : N →ₗ⁅K⁆ L))) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hkey : Finsupp.linearCombination K
      (fun w => (UniversalEnvelopingAlgebra.lift K
        ((UniversalEnvelopingAlgebra.ι K).comp (N.incl : N →ₗ⁅K⁆ L))) (bN w))
      (bN.repr (x - y)) = 0 := by
    have h := Finsupp.apply_linearCombination K
      (UniversalEnvelopingAlgebra.lift K
        ((UniversalEnvelopingAlgebra.ι K).comp (N.incl : N →ₗ⁅K⁆ L))).toLinearMap
      bN (bN.repr (x - y))
    rw [bN.linearCombination_repr (x - y)] at h
    rw [show (⇑(UniversalEnvelopingAlgebra.lift K
        ((UniversalEnvelopingAlgebra.ι K).comp (N.incl : N →ₗ⁅K⁆ L))).toLinearMap ∘ ⇑bN)
        = (fun w => (UniversalEnvelopingAlgebra.lift K
        ((UniversalEnvelopingAlgebra.ι K).comp (N.incl : N →ₗ⁅K⁆ L))) (bN w)) from rfl] at h
    simp only [AlgHom.toLinearMap_apply] at h
    rw [hsub] at h
    exact h.symm
  have hc0 : bN.repr (x - y) = 0 := by
    apply hli.finsuppLinearCombination_injective
    rw [hkey]
    simp
  have hxy0 : x - y = 0 := by
    rw [← bN.linearCombination_repr (x - y), hc0]
    simp
  exact sub_eq_zero.mp hxy0

/-! ## The semilinear change-of-universe isomorphism -/

theorem uea_ringHom_of_semilinear {R : Type u} {R' : Type u'} {M : Type v} {M' : Type v'}
    [CommRing R] [CommRing R'] [LieRing M] [LieAlgebra R M] [LieRing M'] [LieAlgebra R' M']
    (eR : R ≃+* R') (eM : M ≃ M')
    (hadd : ∀ x y, eM (x + y) = eM x + eM y)
    (hsmul : ∀ (r : R) (x : M), eM (r • x) = eR r • eM x)
    (hlie : ∀ x y, eM ⁅x, y⁆ = ⁅eM x, eM y⁆) :
    ∃ (Φ : UniversalEnvelopingAlgebra R M →+* UniversalEnvelopingAlgebra R' M')
      (Ψ : UniversalEnvelopingAlgebra R' M' →+* UniversalEnvelopingAlgebra R M),
      (∀ z, Ψ (Φ z) = z) ∧
      (∀ x : M, Φ (UniversalEnvelopingAlgebra.ι R x) = UniversalEnvelopingAlgebra.ι R' (eM x)) ∧
      (∀ r : R, Φ (algebraMap R (UniversalEnvelopingAlgebra R M) r) =
        algebraMap R' (UniversalEnvelopingAlgebra R' M') (eR r)) := by
  classical
  letI : Algebra R (UniversalEnvelopingAlgebra R' M') := Algebra.compHom _ eR.toRingHom
  letI : Algebra R' (UniversalEnvelopingAlgebra R M) := Algebra.compHom _ eR.symm.toRingHom
  have hsymm_add : ∀ x y : M', eM.symm (x + y) = eM.symm x + eM.symm y := by
    intro x y
    apply eM.injective
    rw [Equiv.apply_symm_apply, hadd, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hsymm_smul : ∀ (r' : R') (y : M'), eM.symm (r' • y) = eR.symm r' • eM.symm y := by
    intro r' y
    apply eM.injective
    rw [Equiv.apply_symm_apply, hsmul, eR.apply_symm_apply, Equiv.apply_symm_apply]
  have hsymm_lie : ∀ x y : M', eM.symm ⁅x, y⁆ = ⁅eM.symm x, eM.symm y⁆ := by
    intro x y
    apply eM.injective
    rw [Equiv.apply_symm_apply, hlie, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  let g : M →ₗ⁅R⁆ UniversalEnvelopingAlgebra R' M' :=
    { toFun := fun x => UniversalEnvelopingAlgebra.ι R' (eM x)
      map_add' := fun x y => by rw [hadd, map_add]
      map_smul' := fun r x => by rw [hsmul, map_smul]; rfl
      map_lie' := fun {x y} => by
        show (UniversalEnvelopingAlgebra.ι R') (eM ⁅x, y⁆) =
          ⁅(UniversalEnvelopingAlgebra.ι R') (eM x), (UniversalEnvelopingAlgebra.ι R') (eM y)⁆
        rw [hlie]
        exact (UniversalEnvelopingAlgebra.ι R').map_lie (eM x) (eM y) }
  let Φ : UniversalEnvelopingAlgebra R M →ₐ[R] UniversalEnvelopingAlgebra R' M' :=
    UniversalEnvelopingAlgebra.lift R g
  let g' : M' →ₗ⁅R'⁆ UniversalEnvelopingAlgebra R M :=
    { toFun := fun y => UniversalEnvelopingAlgebra.ι R (eM.symm y)
      map_add' := fun x y => by rw [hsymm_add, map_add]
      map_smul' := fun r' y => by rw [hsymm_smul, map_smul]; rfl
      map_lie' := fun {x y} => by
        show (UniversalEnvelopingAlgebra.ι R) (eM.symm ⁅x, y⁆) =
          ⁅(UniversalEnvelopingAlgebra.ι R) (eM.symm x), (UniversalEnvelopingAlgebra.ι R) (eM.symm y)⁆
        rw [hsymm_lie]
        exact (UniversalEnvelopingAlgebra.ι R).map_lie (eM.symm x) (eM.symm y) }
  let Ψ : UniversalEnvelopingAlgebra R' M' →ₐ[R'] UniversalEnvelopingAlgebra R M :=
    UniversalEnvelopingAlgebra.lift R' g'
  refine ⟨Φ, Ψ, ?_, ?_, ?_⟩
  · intro z
    let comp : UniversalEnvelopingAlgebra R M →ₐ[R] UniversalEnvelopingAlgebra R M :=
      { toRingHom := (Ψ : UniversalEnvelopingAlgebra R' M' →+* UniversalEnvelopingAlgebra R M).comp
          (Φ : UniversalEnvelopingAlgebra R M →+* UniversalEnvelopingAlgebra R' M')
        commutes' := by
          intro r
          show Ψ (Φ (algebraMap R (UniversalEnvelopingAlgebra R M) r)) =
            algebraMap R (UniversalEnvelopingAlgebra R M) r
          rw [AlgHom.commutes]
          show Ψ (algebraMap R' (UniversalEnvelopingAlgebra R' M') (eR r)) =
            algebraMap R (UniversalEnvelopingAlgebra R M) r
          rw [AlgHom.commutes]
          show algebraMap R' (UniversalEnvelopingAlgebra R M) (eR r) =
            algebraMap R (UniversalEnvelopingAlgebra R M) r
          rw [show algebraMap R' (UniversalEnvelopingAlgebra R M) (eR r) =
            algebraMap R (UniversalEnvelopingAlgebra R M) (eR.symm (eR r)) from rfl,
            eR.symm_apply_apply] }
    have hcomp : comp = AlgHom.id R (UniversalEnvelopingAlgebra R M) := by
      apply UniversalEnvelopingAlgebra.hom_ext
      ext x
      show Ψ (Φ (UniversalEnvelopingAlgebra.ι R x)) = UniversalEnvelopingAlgebra.ι R x
      rw [show Φ (UniversalEnvelopingAlgebra.ι R x) = g x from
        UniversalEnvelopingAlgebra.lift_ι_apply R g x]
      show Ψ ((UniversalEnvelopingAlgebra.ι R') (eM x)) = UniversalEnvelopingAlgebra.ι R x
      rw [show Ψ ((UniversalEnvelopingAlgebra.ι R') (eM x)) = g' (eM x) from
        UniversalEnvelopingAlgebra.lift_ι_apply R' g' (eM x)]
      show (UniversalEnvelopingAlgebra.ι R) (eM.symm (eM x)) = UniversalEnvelopingAlgebra.ι R x
      rw [Equiv.symm_apply_apply]
    exact AlgHom.congr_fun hcomp z
  · intro x
    exact UniversalEnvelopingAlgebra.lift_ι_apply R g x
  · intro r
    exact (AlgHom.commutes Φ r).trans (by rfl)

theorem lift_incl_injective_twoUniverse (K : Type u_1) (L : Type u_2) [Field K] [CharZero K]
    [LieRing L] [LieAlgebra K L] (N : LieSubalgebra K L) :
    Function.Injective (UniversalEnvelopingAlgebra.lift K
      ((UniversalEnvelopingAlgebra.ι K).comp (N.incl : N →ₗ⁅K⁆ L))) := by
  classical
  let K' : Type (max u_1 u_2) := ULift.{max u_1 u_2, u_1} K
  let L' : Type (max u_1 u_2) := ULift.{max u_1 u_2, u_2} L
  let eR : K ≃+* K' :=
    { toFun := (ULift.up : K → K'), invFun := (ULift.down : K' → K),
      left_inv := fun x => rfl, right_inv := fun x => rfl,
      map_mul' := fun x y => rfl, map_add' := fun x y => rfl }
  let eL : L ≃ L' := (Equiv.ulift : ULift.{max u_1 u_2, u_2} L ≃ L).symm
  have eL_add : ∀ x y : L, eL (x + y) = eL x + eL y := fun x y => rfl
  have eL_smul : ∀ (c : K) (x : L), eL (c • x) = eR c • eL x := fun c x => rfl
  have eL_lie : ∀ x y : L, eL ⁅x, y⁆ = ⁅eL x, eL y⁆ := fun x y => rfl
  let N'' : LieSubalgebra K' L' :=
    { carrier := (ULift.up : L → L') '' (N : Set L)
      zero_mem' := ⟨0, N.zero_mem, rfl⟩
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, N.add_mem ha hb, rfl⟩
      smul_mem' := by
        rintro c _ ⟨a, ha, rfl⟩
        exact ⟨c.down • a, N.smul_mem c.down ha, rfl⟩
      lie_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨⁅a, b⁆, N.lie_mem ha hb, rfl⟩ }
  let toN'' : N → N'' := fun n => ⟨(ULift.up : L → L') (n : L), ⟨(n : L), n.2, rfl⟩⟩
  have hinj : Function.Injective toN'' := by
    intro n m h
    have h1 : (ULift.up : L → L') ((n : N) : L) = (ULift.up : L → L') ((m : N) : L) :=
      congrArg Subtype.val h
    have h2 : ((n : N) : L) = ((m : N) : L) := by
      simpa using congrArg (ULift.down : L' → L) h1
    exact Subtype.ext h2
  have hsurj : Function.Surjective toN'' := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, hay⟩ := hy
    exact ⟨⟨a, ha⟩, Subtype.ext hay⟩
  let eN : N ≃ N'' := Equiv.ofBijective toN'' ⟨hinj, hsurj⟩
  have eN_add : ∀ x y : N, eN (x + y) = eN x + eN y := fun x y => Subtype.ext rfl
  have eN_smul : ∀ (c : K) (x : N), eN (c • x) = eR c • eN x := fun c x => Subtype.ext rfl
  have eN_lie : ∀ x y : N, eN ⁅x, y⁆ = ⁅eN x, eN y⁆ := fun x y => Subtype.ext rfl
  have hmain : Function.Injective (UniversalEnvelopingAlgebra.lift K'
      ((UniversalEnvelopingAlgebra.ι K').comp (N''.incl : N'' →ₗ⁅K'⁆ L'))) :=
    lift_incl_injective_sameUniverse N''
  obtain ⟨ΦL, ΨL, hLid, hLgen, hLalg⟩ := uea_ringHom_of_semilinear eR eL eL_add eL_smul eL_lie
  obtain ⟨ΦN, ΨN, hNid, hNgen, hNalg⟩ := uea_ringHom_of_semilinear eR eN eN_add eN_smul eN_lie
  letI : Algebra K (UniversalEnvelopingAlgebra K' L') := Algebra.compHom _ eR.toRingHom
  have hcomm : ∀ z : UniversalEnvelopingAlgebra K N,
      ΦL ((UniversalEnvelopingAlgebra.lift K ((UniversalEnvelopingAlgebra.ι K).comp (N.incl : N →ₗ⁅K⁆ L))) z)
        = (UniversalEnvelopingAlgebra.lift K'
            ((UniversalEnvelopingAlgebra.ι K').comp (N''.incl : N'' →ₗ⁅K'⁆ L'))) (ΦN z) := by
    let G1 : UniversalEnvelopingAlgebra K N →ₐ[K] UniversalEnvelopingAlgebra K' L' :=
      { toRingHom := ΦL.comp (UniversalEnvelopingAlgebra.lift K ((UniversalEnvelopingAlgebra.ι K).comp (N.incl : N →ₗ⁅K⁆ L)))
        commutes' := by
          intro r
          show ΦL ((UniversalEnvelopingAlgebra.lift K ((UniversalEnvelopingAlgebra.ι K).comp (N.incl : N →ₗ⁅K⁆ L))) (algebraMap K (UniversalEnvelopingAlgebra K N) r)) = algebraMap K (UniversalEnvelopingAlgebra K' L') r
          rw [AlgHom.commutes, hLalg]
          rfl }
    let G2 : UniversalEnvelopingAlgebra K N →ₐ[K] UniversalEnvelopingAlgebra K' L' :=
      { toRingHom := ((UniversalEnvelopingAlgebra.lift K'
            ((UniversalEnvelopingAlgebra.ι K').comp (N''.incl : N'' →ₗ⁅K'⁆ L'))) :
              UniversalEnvelopingAlgebra K' N'' →+* UniversalEnvelopingAlgebra K' L').comp ΦN
        commutes' := by
          intro r
          show (UniversalEnvelopingAlgebra.lift K'
            ((UniversalEnvelopingAlgebra.ι K').comp (N''.incl : N'' →ₗ⁅K'⁆ L'))) (ΦN (algebraMap K (UniversalEnvelopingAlgebra K N) r)) = algebraMap K (UniversalEnvelopingAlgebra K' L') r
          rw [hNalg, AlgHom.commutes]
          rfl }
    have hG : G1 = G2 := by
      apply UniversalEnvelopingAlgebra.hom_ext
      ext x
      show ΦL ((UniversalEnvelopingAlgebra.lift K ((UniversalEnvelopingAlgebra.ι K).comp (N.incl : N →ₗ⁅K⁆ L))) (UniversalEnvelopingAlgebra.ι K x)) =
        (UniversalEnvelopingAlgebra.lift K' ((UniversalEnvelopingAlgebra.ι K').comp (N''.incl : N'' →ₗ⁅K'⁆ L'))) (ΦN (UniversalEnvelopingAlgebra.ι K x))
      rw [hNgen x]
      rw [show (UniversalEnvelopingAlgebra.lift K' ((UniversalEnvelopingAlgebra.ι K').comp (N''.incl : N'' →ₗ⁅K'⁆ L'))) (UniversalEnvelopingAlgebra.ι K' (eN x)) =
        (UniversalEnvelopingAlgebra.ι K') ((N''.incl : N'' →ₗ⁅K'⁆ L') (eN x)) from UniversalEnvelopingAlgebra.lift_ι_apply K' _ (eN x)]
      rw [show (UniversalEnvelopingAlgebra.lift K ((UniversalEnvelopingAlgebra.ι K).comp (N.incl : N →ₗ⁅K⁆ L))) (UniversalEnvelopingAlgebra.ι K x) =
        (UniversalEnvelopingAlgebra.ι K) ((N.incl : N →ₗ⁅K⁆ L) x) from UniversalEnvelopingAlgebra.lift_ι_apply K _ x]
      rw [hLgen ((N.incl : N →ₗ⁅K⁆ L) x)]
      rfl
    intro z
    exact AlgHom.congr_fun hG z
  intro x y hxy
  have h1 : (UniversalEnvelopingAlgebra.lift K'
      ((UniversalEnvelopingAlgebra.ι K').comp (N''.incl : N'' →ₗ⁅K'⁆ L'))) (ΦN x)
      = (UniversalEnvelopingAlgebra.lift K'
      ((UniversalEnvelopingAlgebra.ι K').comp (N''.incl : N'' →ₗ⁅K'⁆ L'))) (ΦN y) := by
    rw [← hcomm x, ← hcomm y, hxy]
  have h2 : ΦN x = ΦN y := hmain h1
  exact (hNid x).symm.trans ((congrArg ΨN h2).trans (hNid y))


/-- For a Lie subalgebra `N ⊆ L` of a Lie algebra over a field `K` of characteristic zero, the
canonical algebra morphism `U(N) → U(L)` induced by the inclusion is injective.

Recommended proof: put `f := (UniversalEnvelopingAlgebra.ι K).comp (N.incl : N →ₗ⁅K⁆ L)` and
`φ := UniversalEnvelopingAlgebra.lift K f`.  Choose a basis `e : ι → N` of `N` (`Module.Free`
holds over a field) and a linear order on `ι`.  By `Commons.Algebra.Lie.PBW.pbw_standardMonomial_basis`
applied to `e`, `U(N)` has the basis `b` indexed by nondecreasing words `w : List ι` with
`b w = (w.map fun i => ι K (e i)).prod`.  Also extend the linearly independent family
`fun i => (e i : L)` to a basis of `L` using `Module.Basis.sumExtend` (indexed by `ι ⊕ _`); order
the index type so that every `Sum.inl i` is below every `Sum.inr j` (e.g. `LinearOrder.lift'`
along an embedding into `Sum.Lex`-ordered indices, or any linear order with `inl < inr`).  PBW
for `L` then gives a basis of `U(L)` indexed by nondecreasing words; a nondecreasing word in `ι`
maps to the corresponding nondecreasing word in `ι ⊕ _`, and distinct words give distinct basis
vectors.  Hence if `Σ w, c w • φ (b w) = 0` then all `c w = 0`, so `φ` is injective
(use `Module.Basis.linearIndependent` on the `U(L)` side and `Fintype.linearIndependent_iff` on
the `U(N)` side).

Implementation note: the argument above is carried out in
`lift_incl_injective_sameUniverse`, which assumes `K` and `L` lie in one universe (as the PBW
theorem `pbw_standardMonomial_basis` does).  The general case is reduced to it by transporting
along the `ULift` isomorphism of enveloping algebras `uea_ringHom_of_semilinear`, which replaces
`K` and `L` by copies in the universe `max u v`; see `lift_incl_injective_twoUniverse`. -/
theorem lift_incl_injective {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    (N : LieSubalgebra K L) :
    Function.Injective (UniversalEnvelopingAlgebra.lift K
      ((UniversalEnvelopingAlgebra.ι K).comp (N.incl : N →ₗ⁅K⁆ L))) := by
  exact lift_incl_injective_twoUniverse K L N

end Commons.Algebra.Lie.UniversalEnveloping
