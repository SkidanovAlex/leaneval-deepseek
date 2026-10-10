import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Submission.Commons.NumberTheory.NumberField.Completion.exists_algEquiv_tensor_adicCompletion_prod
import Submission.NK.GlobalCFT.Norm.globalCFT_normIdeleFun_mul
import Submission.NK.GlobalCFT.Norm.globalCFT_normIdeleFun_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm of a principal idèle

Let `L / K` be a finite extension of number fields and `y ∈ Lˣ`.  The main result of this file is
`NK.GlobalCFT.Norm.globalCFT_normIdeleFun_principalIdele`:

`N_{L/K}((y)) = (N_{L/K} y)`,

i.e. the componentwise norm formula `NK.GlobalCFT.Idele.normIdeleFun` sends the principal idèle
of `y` to the principal idèle of the global norm of `y`.  Componentwise, at a place `v` of `K`
this is the classical product formula

`∏_{w | v} N_{L_w/K_v}(y) = N_{L/K}(y)_v`.

The proof has two halves.

* At a **finite** place `v = Q`, we use the Chinese remainder decomposition
  `L ⊗[K] K_Q ≅ ∏_{q | Q} L_q` (`Commons.…exists_algEquiv_tensor_adicCompletion_prod`, here in the
  explicit form `tensor_adicCompletion_prod_apply`), the base change formula for the norm
  (`norm_tmul_one`) and the multiplicativity of the norm over a product of algebras (`norm_pi`).

* At an **infinite** place, the statement is a product formula for the norm over the
  archimedean places `w | v`.

## Main results

* `norm_tmul_one` : `N_{L ⊗[K] F/F}(y ⊗ 1) = N_{L/K}(y)`.
* `norm_pi` : the norm on a finite product of algebras is the product of the norms.
* `tensor_adicCompletion_prod_apply` : the explicit Chinese remainder decomposition at a
  finite place.
* `globalCFT_normIdeleFun_principalIdele_ofFinite` : the finite places.
* `globalCFT_normIdeleFun_principalIdele` : the statement of this file.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped TensorProduct
open NumberField IsDedekindDomain
open scoped NumberField.LiesOver
open Classical

attribute [local instance] Algebra.TensorProduct.rightAlgebra

noncomputable section

namespace NK.GlobalCFT.Norm

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

/-! ### The norm of a base changed element -/

theorem norm_tmul_one {K L F : Type*} [Field K] [Field L] [Field F]
    [Algebra K L] [Algebra K F] [FiniteDimensional K L] (y : L) :
    Algebra.norm F (y ⊗ₜ[K] (1 : F)) = algebraMap K F (Algebra.norm K y) := by
  rw [Algebra.norm_apply, Algebra.norm_apply]
  have hdet : LinearMap.det (Algebra.lmul F (L ⊗[K] F) (y ⊗ₜ[K] (1 : F))) =
      LinearMap.det ((Algebra.lmul K L y).baseChange F) := by
    let e : (F ⊗[K] L) ≃ₗ[F] (L ⊗[K] F) := (Commons.LinearAlgebra.Dimension.flipRight K L F).symm
    rw [← LinearMap.det_conj ((Algebra.lmul K L y).baseChange F) e]
    congr 1
    refine LinearMap.ext fun a => ?_
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul l g =>
        show ((Algebra.lmul F (L ⊗[K] F)) (y ⊗ₜ[K] (1:F))) (l ⊗ₜ[K] g)
          = (↑e ∘ₗ LinearMap.baseChange F ((Algebra.lmul K L) y) ∘ₗ ↑e.symm) (l ⊗ₜ[K] g)
        rw [show ((Algebra.lmul F (L ⊗[K] F)) (y ⊗ₜ[K] (1:F))) (l ⊗ₜ[K] g)
              = (y * l) ⊗ₜ[K] g from by
              rw [show ((Algebra.lmul F (L ⊗[K] F)) (y ⊗ₜ[K] (1:F))) (l ⊗ₜ[K] g)
                    = (y ⊗ₜ[K] (1:F)) * (l ⊗ₜ[K] g) from rfl,
                  Algebra.TensorProduct.tmul_mul_tmul]
              simp]
        rw [LinearMap.comp_apply, LinearMap.comp_apply]
        have h1 : ((e.symm : (L ⊗[K] F) →ₗ[F] (F ⊗[K] L)) (l ⊗ₜ[K] g)) = g ⊗ₜ[K] l := by
          simp [e, Commons.LinearAlgebra.Dimension.flipRight, Algebra.TensorProduct.comm_tmul]
        rw [h1]
        rw [LinearMap.baseChange_tmul]
        rw [show ((Algebra.lmul K L) y) l = y * l from rfl]
        have h2 : ((e : (F ⊗[K] L) →ₗ[F] (L ⊗[K] F)) (g ⊗ₜ[K] (y * l))) = (y * l) ⊗ₜ[K] g := by
          simp [e, Commons.LinearAlgebra.Dimension.flipRight]
        rw [h2]
    | add x z hx hz =>
        simp only [LinearMap.comp_apply, map_add] at hx hz ⊢
        rw [hx, hz]
  rw [hdet, LinearMap.det_baseChange]

/-! ### The norm on a product of algebras -/

theorem norm_prod {F A B : Type*} [Field F] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] [Module.Free F A] [Module.Finite F A] [Module.Free F B] [Module.Finite F B]
    (x : A × B) : Algebra.norm F x = Algebra.norm F x.1 * Algebra.norm F x.2 := by
  obtain ⟨a, b⟩ := x
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply]
  have h : Algebra.lmul F (A × B) (a, b) =
      LinearMap.prodMap (Algebra.lmul F A a) (Algebra.lmul F B b) := by
    ext y : 1 <;> rfl
  rw [h, LinearMap.det_prodMap]

/-- The product over `Fin (n+1)` splits off the `0` factor. -/
def piFinSuccAlgEquiv (F : Type*) [Field F] {n : ℕ} (A : Fin (n+1) → Type*)
    [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)] :
    ((i : Fin (n+1)) → A i) ≃ₐ[F] (A 0 × ((i : Fin n) → A (i.succ))) :=
  AlgEquiv.ofBijective
    { toFun := fun x => (x 0, fun i => x i.succ)
      map_one' := by ext <;> rfl
      map_mul' := by intro x y; ext <;> rfl
      map_zero' := by ext <;> rfl
      map_add' := by intro x y; ext <;> rfl
      commutes' := by intro f; ext <;> rfl }
    ⟨by intro x y h; funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact congrArg Prod.fst h
        · exact congrArg (fun z => z.2 j) h,
     by intro y; exact ⟨fun i => Fin.cases y.1 y.2 i, by ext <;> rfl⟩⟩

@[simp] theorem piFinSuccAlgEquiv_apply (F : Type*) [Field F] {n : ℕ} (A : Fin (n+1) → Type*)
    [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)] (x : ∀ i, A i) :
    piFinSuccAlgEquiv F A x = (x 0, fun (i : Fin n) => x i.succ) := rfl

theorem norm_pi_fin (F : Type*) [Field F] : ∀ (n : ℕ) (A : Fin n → Type*)
    [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)] [∀ i, Module.Free F (A i)]
    [∀ i, Module.Finite F (A i)] (x : ∀ i, A i),
    Algebra.norm F x = ∏ i, Algebra.norm F (x i) := by
  intro n
  induction n with
  | zero =>
      intro A _ _ _ _ x
      haveI : Subsingleton ((i : Fin 0) → A i) := inferInstance
      rw [Subsingleton.elim x 1, map_one]
      simp
  | succ n ih =>
      intro A _ _ _ _ x
      calc Algebra.norm F x
          = Algebra.norm F (piFinSuccAlgEquiv F A x) :=
            (Algebra.norm_eq_of_algEquiv (piFinSuccAlgEquiv F A) x).symm
        _ = Algebra.norm F (piFinSuccAlgEquiv F A x).1
              * Algebra.norm F (piFinSuccAlgEquiv F A x).2 := norm_prod _
        _ = Algebra.norm F (x 0) * ∏ i : Fin n, Algebra.norm F (x i.succ) := by
            rw [piFinSuccAlgEquiv_apply, ih (fun i : Fin n => A i.succ) (fun i : Fin n => x i.succ)]
        _ = ∏ i : Fin (n+1), Algebra.norm F (x i) :=
            (Fin.prod_univ_succ (fun i : Fin (n+1) => Algebra.norm F (x i))).symm

/-- The norm of an element of a finite product of algebras is the product of the norms of the
components. -/
theorem norm_pi {F : Type*} [Field F] {ι : Type*} [Fintype ι] {A : ι → Type*}
    [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)] [∀ i, Module.Free F (A i)]
    [∀ i, Module.Finite F (A i)] (x : ∀ i, A i) :
    Algebra.norm F x = ∏ i, Algebra.norm F (x i) := by
  let e := Fintype.equivFin ι
  let Φ : ((i : Fin (Fintype.card ι)) → A (e.symm i)) ≃ₐ[F] ((i : ι) → A i) :=
    AlgEquiv.piCongrLeft F A e.symm
  have h1 : Algebra.norm F x = Algebra.norm F (Φ.symm x) :=
    (Algebra.norm_eq_of_algEquiv Φ.symm x).symm
  have h2 : Algebra.norm F (Φ.symm x)
      = ∏ i : Fin (Fintype.card ι), Algebra.norm F ((Φ.symm x) i) :=
    norm_pi_fin F (Fintype.card ι) (fun i => A (e.symm i)) (Φ.symm x)
  have h3 : (∏ i : Fin (Fintype.card ι), Algebra.norm F ((Φ.symm x) i))
      = ∏ i : Fin (Fintype.card ι), Algebra.norm F (x (e.symm i)) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [AlgEquiv.piCongrLeft_symm_apply, Equiv.piCongrLeft_symm_apply]
  have h4 : (∏ i : Fin (Fintype.card ι), Algebra.norm F (x (e.symm i)))
      = ∏ j : ι, Algebra.norm F (x j) :=
    Fintype.prod_equiv e.symm _ _ (fun i => rfl)
  rw [h1, h2, h3, h4]

/-! ### The Chinese remainder decomposition at a finite place, with the canonical formula -/

theorem tensor_adicCompletion_prod_apply (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    letI : ∀ q : {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) //
        q.asIdeal.LiesOver p.asIdeal},
        Algebra (p.adicCompletion K) (q.1.adicCompletion L) :=
      fun q => RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap p q.1 q.2)
    letI : Algebra (p.adicCompletion K) (TensorProduct K L (p.adicCompletion K)) :=
      Algebra.TensorProduct.rightAlgebra
    ∃ e : (TensorProduct K L (p.adicCompletion K)) ≃ₐ[p.adicCompletion K]
      ((q : {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) //
          q.asIdeal.LiesOver p.asIdeal}) → q.1.adicCompletion L),
      ∀ l : L, ∀ q : {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) //
          q.asIdeal.LiesOver p.asIdeal},
        e (l ⊗ₜ[K] (1 : p.adicCompletion K)) q = algebraMap L (q.1.adicCompletion L) l := by
  classical
  let F := p.adicCompletion K
  let A := TensorProduct K L F
  let ι := {q : IsDedekindDomain.HeightOneSpectrum (𝓞 L) // q.asIdeal.LiesOver p.asIdeal}
  haveI : Fintype ι :=
    Fintype.ofEquiv _ (Commons.NumberTheory.NumberField.Completion.primesOverEquiv p).symm
  letI : ∀ q : ι, Algebra F (q.1.adicCompletion L) :=
    fun q => RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap p q.1 q.2)
  letI : ∀ q : ι, Module.Finite F (q.1.adicCompletion L) :=
    fun q => Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion p q.1 q.2
  haveI : Module.Finite F A := by
    haveI : Module.Finite F (F ⊗[K] L) := inferInstance
    exact Module.Finite.equiv (M := F ⊗[K] L) (N := L ⊗[K] F)
      (Commons.LinearAlgebra.Dimension.flipRight K L F).symm
  let φ : ∀ q : ι, A →+* q.1.adicCompletion L := fun q =>
    Classical.choose
      (Commons.RingTheory.Henselian.exists_surjective_ringHom_tensor_completion_canon p q.1 q.2)
  have hφ_formula : ∀ (q : ι) (l : L) (f : F),
      φ q (l ⊗ₜ[K] f) = (algebraMap L (q.1.adicCompletion L) l) *
        (Commons.RingTheory.Henselian.adicCompletionMap p q.1 q.2 f) := fun q =>
    (Classical.choose_spec
      (Commons.RingTheory.Henselian.exists_surjective_ringHom_tensor_completion_canon p q.1 q.2)).2
  have hφ_surj : ∀ q : ι, Function.Surjective (φ q) := fun q =>
    (Classical.choose_spec
      (Commons.RingTheory.Henselian.exists_surjective_ringHom_tensor_completion_canon p q.1 q.2)).1
  have hlin : ∀ q : ι, ∀ (f : F) (x : A), φ q (f • x) = f • (φ q x) := by
    intro q f x
    have h1 : f • x = (1 ⊗ₜ[K] f : A) * x := by
      rw [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply]
    have h2 : φ q (1 ⊗ₜ[K] f) =
        (Commons.RingTheory.Henselian.adicCompletionMap p q.1 q.2) f := by
      rw [hφ_formula q 1 f, map_one, one_mul]
    rw [h1, map_mul, h2, Algebra.smul_def]
    congr 1
  have hcop : Pairwise fun i j : ι => IsCoprime (RingHom.ker (φ i)) (RingHom.ker (φ j)) := by
    intro i j hij
    have hne : i.1.asIdeal ≠ j.1.asIdeal := by
      intro hIJ
      exact hij (Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext hIJ))
    exact Commons.NumberTheory.NumberField.Completion.adicCompletionMap_kernels_coprime
      p i.1 j.1 i.2 j.2 hne
  have hdim : (∑ q : ι, Module.finrank F (q.1.adicCompletion L)) = Module.finrank F A := by
    have hbase : Module.finrank F A = Module.finrank K L :=
      Commons.LinearAlgebra.Dimension.tensor_field_baseChange_finrank (K := K) (L := L) (F := F)
    rw [hbase, ← Commons.NumberTheory.NumberField.Completion.sum_finrank_adicCompletion_eq_finrank
      (K := K) (L := L) p]
    refine Fintype.sum_equiv (Commons.NumberTheory.NumberField.Completion.primesOverEquiv p) _ _ ?_
    intro q
    dsimp only
    congr 1
  -- the canonical product map
  let Φ : A →+* (∀ q : ι, q.1.adicCompletion L) := RingHom.pi φ
  have hΦsurj : Function.Surjective Φ := by
    intro y
    choose a ha using fun i => hφ_surj i (y i)
    obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal (I := fun i => RingHom.ker (φ i)) hcop a
    refine ⟨r, funext fun i => ?_⟩
    have hz : φ i (r - a i) = 0 := by
      have h := hr i
      rwa [RingHom.mem_ker] at h
    have hsub : φ i r - φ i (a i) = 0 := by rw [← map_sub]; exact hz
    have hthis : φ i r = φ i (a i) := sub_eq_zero.mp hsub
    change φ i r = y i
    rw [hthis, ha i]
  have hΦcomm : ∀ f : F, Φ (algebraMap F A f) = algebraMap F (∀ i : ι, i.1.adicCompletion L) f := by
    intro f
    funext i
    have h1 : algebraMap F A f = f • (1 : A) := by rw [Algebra.smul_def, mul_one]
    rw [h1]
    change φ i (f • (1 : A)) = (algebraMap F (i.1.adicCompletion L)) f
    rw [hlin i f 1, map_one, Algebra.smul_def, mul_one]
  let Φa : A →ₐ[F] (∀ q : ι, q.1.adicCompletion L) := AlgHom.mk Φ hΦcomm
  have hsurjA : Function.Surjective (Φa : A →ₗ[F] (∀ q : ι, q.1.adicCompletion L)) := by
    intro y
    obtain ⟨a, ha⟩ := hΦsurj y
    exact ⟨a, ha⟩
  have hfr : Module.finrank F A = Module.finrank F (∀ q : ι, q.1.adicCompletion L) := by
    rw [Module.finrank_pi_fintype F, hdim]
  have hinj : Function.Injective Φa :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mpr hsurjA
  refine ⟨AlgEquiv.ofBijective Φa ⟨hinj, hsurjA⟩, ?_⟩
  intro l q
  change Φ (l ⊗ₜ[K] (1 : F)) q = algebraMap L (q.1.adicCompletion L) l
  rw [show Φ (l ⊗ₜ[K] (1 : F)) q = φ q (l ⊗ₜ[K] (1 : F)) from rfl, hφ_formula q l 1, map_one,
    mul_one]

/-! ### The finite places -/

theorem normIdeleFun_principalIdele_ofFinite {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (y : Lˣ)
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    NK.GlobalCFT.Idele.normIdeleFun K L (NK.GlobalCFT.Idele.principalIdele L y)
        (NK.GlobalCFT.Place.ofFinite Q) =
      NK.GlobalCFT.Idele.principalIdele K (Units.map (Algebra.norm K) y)
        (NK.GlobalCFT.Place.ofFinite Q) := by
  let F := Q.adicCompletion K
  let ι := {q : IsDedekindDomain.HeightOneSpectrum (𝓞 L) // q.asIdeal.LiesOver Q.asIdeal}
  haveI : Fintype ι :=
    Fintype.ofEquiv _ (Commons.NumberTheory.NumberField.Completion.primesOverEquiv Q).symm
  letI : ∀ q : ι, Algebra F (q.1.adicCompletion L) :=
    fun q => RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q.1 q.2)
  haveI : ∀ q : ι, Module.Finite F (q.1.adicCompletion L) :=
    fun q => Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q.1 q.2
  haveI : ∀ q : ι, Module.Free F (q.1.adicCompletion L) := fun q => Module.Free.of_divisionRing F _
  obtain ⟨e, he⟩ := tensor_adicCompletion_prod_apply K L Q
  have key : (∏ q : ι, Algebra.norm F (algebraMap L (q.1.adicCompletion L) (y : L)))
      = algebraMap K F (Algebra.norm K (y : L)) := by
    have h2 : Algebra.norm F (e ((y : L) ⊗ₜ[K] (1 : F))) =
        ∏ q : ι, Algebra.norm F (e ((y : L) ⊗ₜ[K] (1 : F)) q) :=
      norm_pi (ι := ι) (A := fun q : ι => q.1.adicCompletion L)
        (e ((y : L) ⊗ₜ[K] (1 : F)))
    have h3 : (∏ q : ι, Algebra.norm F (e ((y : L) ⊗ₜ[K] (1 : F)) q)) =
        ∏ q : ι, Algebra.norm F (algebraMap L (q.1.adicCompletion L) (y : L)) := by
      refine Finset.prod_congr rfl fun q _ => ?_
      rw [he (y : L) q]
    rw [← h3, ← h2, Algebra.norm_eq_of_algEquiv e ((y : L) ⊗ₜ[K] (1 : F))]
    exact norm_tmul_one (F := F) (y := (y : L))
  have hprod : (∏ x ∈ (NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) Q).attach,
        NK.GlobalCFT.Place.localNormFinite x.1 Q ((NK.GlobalCFT.Place.mem_primesOverFinite
          (K := K) (L := L) (Q := Q) (q := x.1)).mp x.2)
          (NK.GlobalCFT.Idele.principalIdele L y (NK.GlobalCFT.Place.ofFinite x.1)))
      = ∏ q : ι, NK.GlobalCFT.Place.localNormFinite q.1 Q q.2
          (NK.GlobalCFT.Idele.principalIdele L y (NK.GlobalCFT.Place.ofFinite q.1)) := by
    rw [Finset.attach_eq_univ]
    refine Fintype.prod_equiv (Equiv.subtypeEquivRight
      (p := fun q => q ∈ NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) Q)
      (q := fun q => q.asIdeal.LiesOver Q.asIdeal)
      (fun x => NK.GlobalCFT.Place.mem_primesOverFinite)) _ _ (fun x => ?_)
    rfl
  rw [NK.GlobalCFT.Idele.normIdeleFun_ofFinite, NK.GlobalCFT.Idele.principalIdele_apply,
    hprod]
  apply Units.ext
  simp only [Units.coe_prod, Units.coe_map, NK.GlobalCFT.Place.localNormFinite,
    NK.GlobalCFT.Idele.principalIdele_apply]
  exact key

theorem isRamified_iff' {K L : Type*} [Field K] [Field L] [Algebra K L]
    (w : InfinitePlace K) (w' : InfinitePlace L) [hw : w'.LiesOver w] :
    w'.IsRamified K ↔ w'.IsComplex ∧ w.IsReal := by
  rw [InfinitePlace.isRamified_iff, LiesOver.comap_eq w' w]

theorem not_isReal_of_isComplex {K : Type*} [Field K] {w : InfinitePlace K} (h : w.IsComplex) :
    ¬ w.IsReal := (InfinitePlace.not_isReal_iff_isComplex).mpr h

theorem conjugate_conjugate {L : Type*} [Field L] (φ : L →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := by
  ext x
  simp [ComplexEmbedding.conjugate_coe_eq]

/-- If `w` is real then `w'.embedding` lies over `w.embedding` for any `w'` over `w`. -/

theorem liesOver_embedding_of_isReal {K L : Type*} [Field K] [Field L] [Algebra K L]
    {w : InfinitePlace K} {w' : InfinitePlace L} [hw : w'.LiesOver w] (hwR : w.IsReal) :
    ComplexEmbedding.LiesOver w'.embedding w.embedding := by
  have hwRe : ComplexEmbedding.IsReal w.embedding := InfinitePlace.isReal_iff.mp hwR
  have hconj : ∀ x : K, starRingEnd ℂ (w.embedding x) = w.embedding x := by
    intro x
    rw [← ComplexEmbedding.conjugate_coe_eq]
    exact congrArg (fun (f : K →+* ℂ) => f x) (ComplexEmbedding.isReal_iff.mp hwRe)
  rcases LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w' w with h | h
  · exact ⟨h⟩
  · refine ⟨?_⟩
    ext x
    have hx := RingHom.congr_fun h x
    simp only [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq] at hx
    simp only [RingHom.comp_apply]
    rw [← Complex.conj_conj (w'.embedding (algebraMap K L x)), hx, hconj x]

theorem isReal_of_conjugate_eq {K : Type*} [Field K] {w : InfinitePlace K}
    (h : ∀ x : K, starRingEnd ℂ (w.embedding x) = w.embedding x) : w.IsReal :=
  InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr (RingHom.ext fun x => by
    rw [ComplexEmbedding.conjugate_coe_eq]; exact h x))

/-- If `w` is complex, exactly one of `w'.embedding` and its conjugate lies over `w.embedding`. -/

theorem not_liesOver_embedding_of_liesOver_conjugate {K L : Type*} [Field K] [Field L]
    [Algebra K L] {w : InfinitePlace K} {w' : InfinitePlace L} [hw : w'.LiesOver w]
    (hwC : w.IsComplex)
    (h : ComplexEmbedding.LiesOver (ComplexEmbedding.conjugate w'.embedding) w.embedding) :
    ¬ ComplexEmbedding.LiesOver w'.embedding w.embedding := by
  intro h'
  refine not_isReal_of_isComplex hwC (isReal_of_conjugate_eq fun k => ?_)
  have h'k : w'.embedding (algebraMap K L k) = w.embedding k :=
    RingHom.congr_fun h'.over k
  have hk : (ComplexEmbedding.conjugate w'.embedding) (algebraMap K L k) = w.embedding k :=
    RingHom.congr_fun h.over k
  calc starRingEnd ℂ (w.embedding k) = starRingEnd ℂ (w'.embedding (algebraMap K L k)) := by
        rw [h'k]
    _ = (ComplexEmbedding.conjugate w'.embedding) (algebraMap K L k) :=
        ComplexEmbedding.conjugate_coe_eq _ _
    _ = w.embedding k := hk

theorem not_liesOver_conjugate_of_liesOver {K L : Type*} [Field K] [Field L] [Algebra K L]
    {w : InfinitePlace K} {w' : InfinitePlace L} [hw : w'.LiesOver w] (hwC : w.IsComplex)
    (h : ComplexEmbedding.LiesOver w'.embedding w.embedding) :
    ¬ ComplexEmbedding.LiesOver (ComplexEmbedding.conjugate w'.embedding) w.embedding := by
  intro h'
  refine not_isReal_of_isComplex hwC (isReal_of_conjugate_eq fun k => ?_)
  have hk : w'.embedding (algebraMap K L k) = w.embedding k := RingHom.congr_fun h.over k
  have h'k : (ComplexEmbedding.conjugate w'.embedding) (algebraMap K L k) = w.embedding k :=
    RingHom.congr_fun h'.over k
  calc starRingEnd ℂ (w.embedding k) = starRingEnd ℂ (w'.embedding (algebraMap K L k)) := by
        rw [hk]
    _ = (ComplexEmbedding.conjugate w'.embedding) (algebraMap K L k) :=
        ComplexEmbedding.conjugate_coe_eq _ _
    _ = w.embedding k := h'k

/-- The product of `σ y` over the embeddings `σ` lying over a given infinite place `w'`. -/

theorem exists_liesOver_conjugate {K L : Type*} [Field K] [Field L] [Algebra K L]
    {w : InfinitePlace K} {w' : InfinitePlace L} [hw : w'.LiesOver w]
    (h : ¬ ComplexEmbedding.LiesOver w'.embedding w.embedding) :
    ComplexEmbedding.LiesOver (ComplexEmbedding.conjugate w'.embedding) w.embedding := by
  rcases LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w' w with h' | h'
  · exact absurd ⟨h'⟩ h
  · exact ⟨h'⟩

theorem factor_real_real {K L : Type*} [Field K] [Field L] [Algebra K L]
    {w : InfinitePlace K} {w' : InfinitePlace L} [hw : w'.LiesOver w]
    (hwR : w.IsReal) (hw'R : w'.IsReal) (z : w'.Completion) :
    extensionEmbedding w (Algebra.norm w.Completion z) = extensionEmbedding w' z := by
  have hwRe : ComplexEmbedding.IsReal w.embedding := InfinitePlace.isReal_iff.mp hwR
  have hconj : ∀ x : K, starRingEnd ℂ (w.embedding x) = w.embedding x := by
    intro x
    rw [← ComplexEmbedding.conjugate_coe_eq]
    exact congrArg (fun (f : K →+* ℂ) => f x) (ComplexEmbedding.isReal_iff.mp hwRe)
  haveI : ComplexEmbedding.LiesOver w'.embedding w.embedding := by
    rcases LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w' w with h | h
    · exact ⟨h⟩
    · refine ⟨?_⟩
      ext x
      have hx := RingHom.congr_fun h x
      simp only [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq] at hx
      simp only [RingHom.comp_apply]
      rw [← Complex.conj_conj (w'.embedding (algebraMap K L x)), hx, hconj x]
  have hlies := NumberField.InfinitePlace.Completion.liesOver_extensionEmbedding w' w
  have hcomp : ∀ x : w.Completion, extensionEmbedding w' ((algebraMap w.Completion w'.Completion) x)
      = extensionEmbedding w x := fun x => RingHom.congr_fun hlies.over x
  have he : ∀ x : w.Completion,
      (ringEquivRealOfIsReal hwR) x
        = (ringEquivRealOfIsReal hw'R) ((algebraMap w.Completion w'.Completion) x) := by
    intro x
    apply Complex.ofReal_injective
    rw [ringEquivRealOfIsReal_apply, ringEquivRealOfIsReal_apply,
      extensionEmbeddingOfIsReal_apply, extensionEmbeddingOfIsReal_apply, hcomp x]
  have hnorm := Algebra.norm_eq_of_equiv_equiv (ringEquivRealOfIsReal hwR)
    (ringEquivRealOfIsReal hw'R) (RingHom.ext he) z
  have hval : Algebra.norm ℝ ((ringEquivRealOfIsReal hw'R) z) = (ringEquivRealOfIsReal hw'R) z := by
    rw [Algebra.norm_self]; rfl
  have hχ : ∀ x : w.Completion, ((ringEquivRealOfIsReal hwR x : ℝ) : ℂ) = extensionEmbedding w x := by
    intro x; rw [ringEquivRealOfIsReal_apply, extensionEmbeddingOfIsReal_apply]
  have hψ : ∀ u : w'.Completion, ((ringEquivRealOfIsReal hw'R u : ℝ) : ℂ) = extensionEmbedding w' u := by
    intro u; rw [ringEquivRealOfIsReal_apply, extensionEmbeddingOfIsReal_apply]
  rw [← hχ (Algebra.norm w.Completion z), ← hψ z, hnorm, hval, RingEquiv.apply_symm_apply]


/-- If `w` is real and `w'` is complex over `w`, then the norm of the completion extension,
transported by the canonical embeddings, is `z ↦ z * conj z`. -/

theorem factor_real_complex {K L : Type*} [Field K] [Field L] [Algebra K L]
    {w : InfinitePlace K} {w' : InfinitePlace L} [hw : w'.LiesOver w]
    (hwR : w.IsReal) (hw'C : w'.IsComplex) (z : w'.Completion) :
    extensionEmbedding w (Algebra.norm w.Completion z)
      = (Complex.normSq (extensionEmbedding w' z) : ℂ) := by
  have hwRe : ComplexEmbedding.IsReal w.embedding := InfinitePlace.isReal_iff.mp hwR
  have hconj : ∀ x : K, starRingEnd ℂ (w.embedding x) = w.embedding x := by
    intro x
    rw [← ComplexEmbedding.conjugate_coe_eq]
    exact congrArg (fun (f : K →+* ℂ) => f x) (ComplexEmbedding.isReal_iff.mp hwRe)
  haveI : ComplexEmbedding.LiesOver w'.embedding w.embedding := by
    rcases LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w' w with h | h
    · exact ⟨h⟩
    · refine ⟨?_⟩
      ext x
      have hx := RingHom.congr_fun h x
      simp only [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq] at hx
      simp only [RingHom.comp_apply]
      rw [← Complex.conj_conj (w'.embedding (algebraMap K L x)), hx, hconj x]
  have hlies := NumberField.InfinitePlace.Completion.liesOver_extensionEmbedding w' w
  have hcomp : ∀ x : w.Completion, extensionEmbedding w' ((algebraMap w.Completion w'.Completion) x)
      = extensionEmbedding w x := fun x => RingHom.congr_fun hlies.over x
  have he : ∀ x : w.Completion,
      (algebraMap ℝ ℂ) ((ringEquivRealOfIsReal hwR) x)
        = (ringEquivComplexOfIsComplex hw'C) ((algebraMap w.Completion w'.Completion) x) := by
    intro x
    change (((ringEquivRealOfIsReal hwR) x : ℝ) : ℂ) = _
    rw [ringEquivRealOfIsReal_apply, extensionEmbeddingOfIsReal_apply,
      ringEquivComplexOfIsComplex_apply, hcomp x]
  have hnorm := Algebra.norm_eq_of_equiv_equiv (ringEquivRealOfIsReal hwR)
    (ringEquivComplexOfIsComplex hw'C) (RingHom.ext he) z
  have hval : Algebra.norm ℝ ((ringEquivComplexOfIsComplex hw'C) z)
      = Complex.normSq ((ringEquivComplexOfIsComplex hw'C) z) :=
    Algebra.norm_complex_apply _
  have hχ : ∀ x : w.Completion, ((ringEquivRealOfIsReal hwR x : ℝ) : ℂ) = extensionEmbedding w x := by
    intro x; rw [ringEquivRealOfIsReal_apply, extensionEmbeddingOfIsReal_apply]
  have hψ : ∀ u : w'.Completion, (ringEquivComplexOfIsComplex hw'C) u = extensionEmbedding w' u := by
    intro u; rw [ringEquivComplexOfIsComplex_apply]
  rw [← hχ (Algebra.norm w.Completion z), ← hψ z, hnorm, hval, RingEquiv.apply_symm_apply]

/-- If `w` and `w'` are both complex, the norm of the completion extension is (transported to `ℂ`)
the embedding `w'.embedding` if it lies over `w.embedding`, and its conjugate otherwise. -/

theorem factor_complex_complex {K L : Type*} [Field K] [Field L] [Algebra K L]
    {w : InfinitePlace K} {w' : InfinitePlace L} [hw : w'.LiesOver w]
    (hwC : w.IsComplex) (hw'C : w'.IsComplex) (z : w'.Completion) :
    extensionEmbedding w (Algebra.norm w.Completion z)
      = if ComplexEmbedding.LiesOver w'.embedding w.embedding
        then extensionEmbedding w' z else starRingEnd ℂ (extensionEmbedding w' z) := by
  rcases LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w' w with h | h
  · haveI : ComplexEmbedding.LiesOver w'.embedding w.embedding := ⟨h⟩
    have hlies := NumberField.InfinitePlace.Completion.liesOver_extensionEmbedding w' w
    have hcomp : ∀ x : w.Completion,
        extensionEmbedding w' ((algebraMap w.Completion w'.Completion) x) = extensionEmbedding w x :=
      fun x => RingHom.congr_fun hlies.over x
    have he : ∀ x : w.Completion,
        (ringEquivComplexOfIsComplex hwC) x
          = (ringEquivComplexOfIsComplex hw'C) ((algebraMap w.Completion w'.Completion) x) := by
      intro x
      rw [ringEquivComplexOfIsComplex_apply, ringEquivComplexOfIsComplex_apply, hcomp x]
    have hnorm := Algebra.norm_eq_of_equiv_equiv (ringEquivComplexOfIsComplex hwC)
      (ringEquivComplexOfIsComplex hw'C) (RingHom.ext he) z
    have hval : Algebra.norm ℂ ((ringEquivComplexOfIsComplex hw'C) z)
        = (ringEquivComplexOfIsComplex hw'C) z := by
      rw [Algebra.norm_self]; rfl
    have hχ : ∀ x : w.Completion,
        (ringEquivComplexOfIsComplex hwC) x = extensionEmbedding w x := by
      intro x; rw [ringEquivComplexOfIsComplex_apply]
    have hψ : ∀ u : w'.Completion,
        (ringEquivComplexOfIsComplex hw'C) u = extensionEmbedding w' u := by
      intro u; rw [ringEquivComplexOfIsComplex_apply]
    rw [if_pos (show ComplexEmbedding.LiesOver w'.embedding w.embedding from ⟨h⟩),
      ← hχ (Algebra.norm w.Completion z), ← hψ z, hnorm, hval, RingEquiv.apply_symm_apply]
  · haveI : ComplexEmbedding.LiesOver (ComplexEmbedding.conjugate w'.embedding) w.embedding := ⟨h⟩
    have hlies := NumberField.InfinitePlace.Completion.liesOver_conjugate_extensionEmbedding w' w
    -- conj ∘ ψ ∘ ι = χ
    have hcomp : ∀ x : w.Completion,
        starRingEnd ℂ (extensionEmbedding w' ((algebraMap w.Completion w'.Completion) x))
          = extensionEmbedding w x := fun x => RingHom.congr_fun hlies.over x
    have hconj : ∀ x : w.Completion,
        extensionEmbedding w' ((algebraMap w.Completion w'.Completion) x)
          = starRingEnd ℂ (extensionEmbedding w x) := by
      intro x
      rw [← Complex.conj_conj (extensionEmbedding w' ((algebraMap w.Completion w'.Completion) x)),
        hcomp x]
    have he : ∀ x : w.Completion,
        (Complex.conjAe.toRingEquiv) ((ringEquivComplexOfIsComplex hwC) x)
          = (ringEquivComplexOfIsComplex hw'C) ((algebraMap w.Completion w'.Completion) x) := by
      intro x
      rw [ringEquivComplexOfIsComplex_apply, ringEquivComplexOfIsComplex_apply]
      change starRingEnd ℂ (extensionEmbedding w x) = _
      rw [← hconj x]
    have hnorm := Algebra.norm_eq_of_equiv_equiv
      ((ringEquivComplexOfIsComplex hwC).trans Complex.conjAe.toRingEquiv)
      (ringEquivComplexOfIsComplex hw'C) (RingHom.ext he) z
    have hval : Algebra.norm ℂ ((ringEquivComplexOfIsComplex hw'C) z)
        = (ringEquivComplexOfIsComplex hw'C) z := by
      rw [Algebra.norm_self]; rfl
    have hχ : ∀ x : w.Completion,
        (Complex.conjAe.toRingEquiv) ((ringEquivComplexOfIsComplex hwC) x)
          = starRingEnd ℂ (extensionEmbedding w x) := by
      intro x; rw [ringEquivComplexOfIsComplex_apply]; rfl
    have hψ : ∀ u : w'.Completion,
        (ringEquivComplexOfIsComplex hw'C) u = extensionEmbedding w' u := by
      intro u; rw [ringEquivComplexOfIsComplex_apply]
    have hne : ¬ ComplexEmbedding.LiesOver w'.embedding w.embedding := by
      intro hcontra
      have h1 : w'.embedding.comp (algebraMap K L) = w.embedding := hcontra.over
      have h2 : (ComplexEmbedding.conjugate w'.embedding).comp (algebraMap K L)
          = ComplexEmbedding.conjugate w.embedding := by
        rw [← h1]
        ext x
        simp [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply]
      rw [h2] at h
      exact (InfinitePlace.not_isReal_iff_isComplex.mpr hwC)
        (InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h))
    have key : ((ringEquivComplexOfIsComplex hwC).trans Complex.conjAe.toRingEquiv)
          (Algebra.norm w.Completion z)
        = (ringEquivComplexOfIsComplex hw'C) z := by
      rw [hnorm, hval, RingEquiv.apply_symm_apply]
    have key2 : starRingEnd ℂ (extensionEmbedding w (Algebra.norm w.Completion z))
        = extensionEmbedding w' z := by
      rw [← hχ (Algebra.norm w.Completion z)]
      exact key.trans (hψ z)
    rw [if_neg hne,
      ← Complex.conj_conj (extensionEmbedding w (Algebra.norm w.Completion z)), key2]

theorem extensionEmbedding_localNormInfinite {K L : Type*} [Field K] [Field L] [Algebra K L]
    (w : InfinitePlace K) (w' : InfinitePlace L) [hw' : w'.LiesOver w] (y : Lˣ) :
    extensionEmbedding w ((NK.GlobalCFT.Place.localNormInfinite w' w
        (Units.map (algebraMap L w'.Completion) y) : w.Completion))
      = (if w'.IsRamified K then
            (extensionEmbedding w' (algebraMap L w'.Completion (y : L))) *
              starRingEnd ℂ (extensionEmbedding w' (algebraMap L w'.Completion (y : L)))
          else if ComplexEmbedding.LiesOver w'.embedding w.embedding then
            extensionEmbedding w' (algebraMap L w'.Completion (y : L))
          else starRingEnd ℂ (extensionEmbedding w' (algebraMap L w'.Completion (y : L)))) := by
  rw [show (↑(NK.GlobalCFT.Place.localNormInfinite w' w
        (Units.map (algebraMap L w'.Completion) y)) : w.Completion)
      = Algebra.norm w.Completion (algebraMap L w'.Completion (y : L)) from by
    simp [NK.GlobalCFT.Place.localNormInfinite, Units.coe_map]]
  rcases w.isReal_or_isComplex with hwR | hwC
  · rcases w'.isReal_or_isComplex with hw'R | hw'C
    · have hLies : ComplexEmbedding.LiesOver w'.embedding w.embedding :=
        liesOver_embedding_of_isReal hwR
      have hRam : ¬ w'.IsRamified K := by
        rw [isRamified_iff' w w']
        exact fun h => (InfinitePlace.not_isReal_iff_isComplex.mpr h.1) hw'R
      rw [if_neg hRam, if_pos hLies]
      exact factor_real_real hwR hw'R _
    · have hRam : w'.IsRamified K := (isRamified_iff' w w').mpr ⟨hw'C, hwR⟩
      rw [if_pos hRam, factor_real_complex hwR hw'C]
      rw [Complex.normSq_eq_conj_mul_self, mul_comm]
  · rcases w'.isReal_or_isComplex with hw'R | hw'C
    · exact absurd (LiesOver.isReal_of_isReal_over (w := w') hw'R) (not_isReal_of_isComplex hwC)
    · have hRam : ¬ w'.IsRamified K := by
        rw [isRamified_iff' w w']
        exact fun h => (not_isReal_of_isComplex hwC) h.2
      rw [if_neg hRam]
      exact factor_complex_complex hwC hw'C _

theorem fiber_prod {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (w : InfinitePlace K) (w' : InfinitePlace L) [hw' : w'.LiesOver w] (y : L) :
    letI : Algebra K ℂ := RingHom.toAlgebra w.embedding
    (∏ σ ∈ (Finset.univ : Finset (L →ₐ[K] ℂ)).filter
        (fun (σ : L →ₐ[K] ℂ) => InfinitePlace.mk (σ : L →+* ℂ) = w'), σ y)
      = (if w'.IsRamified K then w'.embedding y * starRingEnd ℂ (w'.embedding y)
          else if ComplexEmbedding.LiesOver w'.embedding w.embedding then w'.embedding y
          else starRingEnd ℂ (w'.embedding y)) := by
  classical
  letI : Algebra K ℂ := RingHom.toAlgebra w.embedding
  have hemb : ∀ σ : L →ₐ[K] ℂ, InfinitePlace.mk (σ : L →+* ℂ) = w' →
      (σ : L →+* ℂ) = w'.embedding ∨
        (σ : L →+* ℂ) = ComplexEmbedding.conjugate w'.embedding := by
    intro σ hσ
    have h := InfinitePlace.embedding_mk_eq (σ : L →+* ℂ)
    rw [hσ] at h
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h]; exact (conjugate_conjugate _).symm)
  rcases w.isReal_or_isComplex with hwR | hwC
  · rcases w'.isReal_or_isComplex with hw'R | hw'C
    · -- w real, w' real
      have hLies := liesOver_embedding_of_isReal (w := w) (w' := w') hwR
      have hRam : ¬ w'.IsRamified K := by
        rw [isRamified_iff' w w']
        exact fun h => (not_isReal_of_isComplex h.1) hw'R
      rw [if_neg hRam, if_pos hLies]
      let σ₁ : L →ₐ[K] ℂ := AlgHom.mk w'.embedding (fun k => by
        show w'.embedding (algebraMap K L k) = w.embedding k
        rw [← RingHom.comp_apply]
        exact RingHom.congr_fun hLies.over k)
      have hfiber : (Finset.univ : Finset (L →ₐ[K] ℂ)).filter
          (fun (σ : L →ₐ[K] ℂ) => InfinitePlace.mk (σ : L →+* ℂ) = w') = ({σ₁} : Finset (L →ₐ[K] ℂ)) := by
        refine Finset.ext fun σ => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro h
          rcases hemb σ h with h2 | h2
          · exact AlgHom.coe_ringHom_injective (by simpa [σ₁] using h2)
          · have hreal : ComplexEmbedding.conjugate w'.embedding = w'.embedding :=
              ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hw'R)
            exact AlgHom.coe_ringHom_injective (by simpa [σ₁, h2, hreal])
        · intro h
          rw [h]
          simp only [σ₁, AlgHom.coe_ringHom_mk, InfinitePlace.mk_embedding]
      rw [hfiber, Finset.prod_singleton]
      rfl
    · -- w real, w' complex : ramified
      have hLies := liesOver_embedding_of_isReal (w := w) (w' := w') hwR
      have hconjLies : ComplexEmbedding.LiesOver (ComplexEmbedding.conjugate w'.embedding)
          w.embedding := by
        refine ⟨?_⟩
        rw [ComplexEmbedding.conjugate_comp w'.embedding (algebraMap K L), hLies.over,
          ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hwR)]
      have hRam : w'.IsRamified K := (isRamified_iff' w w').mpr ⟨hw'C, hwR⟩
      rw [if_pos hRam]
      let σ₁ : L →ₐ[K] ℂ := AlgHom.mk w'.embedding (fun k => by
        show w'.embedding (algebraMap K L k) = w.embedding k
        rw [← RingHom.comp_apply]
        exact RingHom.congr_fun hLies.over k)
      let σ₂ : L →ₐ[K] ℂ := AlgHom.mk (ComplexEmbedding.conjugate w'.embedding) (fun k => by
        show (ComplexEmbedding.conjugate w'.embedding) (algebraMap K L k) = w.embedding k
        rw [← RingHom.comp_apply]
        exact RingHom.congr_fun hconjLies.over k)
      have hne : ComplexEmbedding.conjugate w'.embedding ≠ w'.embedding := by
        intro h
        exact (not_isReal_of_isComplex hw'C)
          (InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h))
      have hfiber : (Finset.univ : Finset (L →ₐ[K] ℂ)).filter
          (fun (σ : L →ₐ[K] ℂ) => InfinitePlace.mk (σ : L →+* ℂ) = w') = ({σ₁, σ₂} : Finset (L →ₐ[K] ℂ)) := by
        refine Finset.ext fun σ => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · intro h
          rcases hemb σ h with h2 | h2
          · exact Or.inl (AlgHom.coe_ringHom_injective (by simpa [σ₁] using h2))
          · exact Or.inr (AlgHom.coe_ringHom_injective (by simpa [σ₂] using h2))
        · rintro (h | h)
          · rw [h]; simp only [σ₁, AlgHom.coe_ringHom_mk, InfinitePlace.mk_embedding]
          · rw [h]; simp only [σ₂, AlgHom.coe_ringHom_mk, InfinitePlace.mk_embedding, InfinitePlace.mk_conjugate_eq]
      have hne' : σ₁ ≠ σ₂ := by
        intro h
        exact hne (by
          have h2 := congrArg (fun f : L →ₐ[K] ℂ => (f : L →+* ℂ)) h
          simpa [σ₁, σ₂, AlgHom.coe_ringHom_mk] using h2.symm)
      rw [hfiber, Finset.prod_pair hne']
      rfl
  · rcases w'.isReal_or_isComplex with hw'R | hw'C
    · exact absurd (LiesOver.isReal_of_isReal_over (w := w') hw'R) (not_isReal_of_isComplex hwC)
    · -- w complex, w' complex
      have hRam : ¬ w'.IsRamified K := by
        rw [isRamified_iff' w w']
        exact fun h => (not_isReal_of_isComplex hwC) h.2
      by_cases hLies : ComplexEmbedding.LiesOver w'.embedding w.embedding
      · rw [if_neg hRam, if_pos hLies]
        let σ₁ : L →ₐ[K] ℂ := AlgHom.mk w'.embedding (fun k => by
          show w'.embedding (algebraMap K L k) = w.embedding k
          rw [← RingHom.comp_apply]
          exact RingHom.congr_fun hLies.over k)
        have hfiber : (Finset.univ : Finset (L →ₐ[K] ℂ)).filter
            (fun (σ : L →ₐ[K] ℂ) => InfinitePlace.mk (σ : L →+* ℂ) = w') = ({σ₁} : Finset (L →ₐ[K] ℂ)) := by
          refine Finset.ext fun σ => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro h
            rcases hemb σ h with h2 | h2
            · exact AlgHom.coe_ringHom_injective (by simpa [σ₁] using h2)
            · exfalso
              have hcontra : ComplexEmbedding.LiesOver
                  (ComplexEmbedding.conjugate w'.embedding) w.embedding := by
                rw [← h2]
                exact ⟨by ext k; exact σ.commutes k⟩
              exact (not_liesOver_conjugate_of_liesOver hwC hLies) hcontra
          · intro h
            rw [h]
            simp only [σ₁, AlgHom.coe_ringHom_mk, InfinitePlace.mk_embedding]
        rw [hfiber, Finset.prod_singleton]
        rfl
      · have hconjLies := exists_liesOver_conjugate (w := w) (w' := w') hLies
        rw [if_neg hRam, if_neg hLies]
        let σ₂ : L →ₐ[K] ℂ := AlgHom.mk (ComplexEmbedding.conjugate w'.embedding) (fun k => by
          show (ComplexEmbedding.conjugate w'.embedding) (algebraMap K L k) = w.embedding k
          rw [← RingHom.comp_apply]
          exact RingHom.congr_fun hconjLies.over k)
        have hfiber : (Finset.univ : Finset (L →ₐ[K] ℂ)).filter
            (fun (σ : L →ₐ[K] ℂ) => InfinitePlace.mk (σ : L →+* ℂ) = w') = ({σ₂} : Finset (L →ₐ[K] ℂ)) := by
          refine Finset.ext fun σ => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro h
            rcases hemb σ h with h2 | h2
            · exfalso
              have hcontra : ComplexEmbedding.LiesOver w'.embedding w.embedding := by
                rw [← h2]
                exact ⟨by ext k; exact σ.commutes k⟩
              exact hLies hcontra
            · exact AlgHom.coe_ringHom_injective (by simpa [σ₂] using h2)
          · intro h
            rw [h]
            simp only [σ₂, AlgHom.coe_ringHom_mk, InfinitePlace.mk_embedding, InfinitePlace.mk_conjugate_eq]
        rw [hfiber, Finset.prod_singleton]
        exact (ComplexEmbedding.conjugate_coe_eq _ y).symm
/-- The product over the places above an infinite place of the local norm factors. -/
theorem prod_fiber_eq {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (y : L) (w : InfinitePlace K) :
    (∏ w' : {w' : InfinitePlace L // w'.LiesOver w},
        (if w'.1.IsRamified K then w'.1.embedding y * starRingEnd ℂ (w'.1.embedding y)
          else if ComplexEmbedding.LiesOver w'.1.embedding w.embedding then w'.1.embedding y
          else starRingEnd ℂ (w'.1.embedding y)))
      = w.embedding (Algebra.norm K y) := by
  classical
  letI : Algebra K ℂ := RingHom.toAlgebra w.embedding
  have h1 : (∏ w' : {w' : InfinitePlace L // w'.LiesOver w},
        (if w'.1.IsRamified K then w'.1.embedding y * starRingEnd ℂ (w'.1.embedding y)
          else if ComplexEmbedding.LiesOver w'.1.embedding w.embedding then w'.1.embedding y
          else starRingEnd ℂ (w'.1.embedding y)))
      = ∏ w' : {w' : InfinitePlace L // w'.LiesOver w},
          (∏ σ ∈ (Finset.univ : Finset (L →ₐ[K] ℂ)).filter
            (fun (σ : L →ₐ[K] ℂ) => InfinitePlace.mk (σ : L →+* ℂ) = w'.1), σ y) := by
    refine Finset.prod_congr rfl fun w' _ => ?_
    haveI : w'.1.LiesOver w := w'.2
    exact (fiber_prod w w'.1 y).symm
  rw [h1]
  have hlies : ∀ σ : L →ₐ[K] ℂ, (InfinitePlace.mk (σ : L →+* ℂ)).LiesOver w := by
    intro σ
    haveI : ComplexEmbedding.LiesOver (σ : L →+* ℂ) w.embedding :=
      ⟨by ext k; exact σ.commutes k⟩
    haveI : AbsoluteValue.LiesOver (InfinitePlace.mk (σ : L →+* ℂ)).1
        (InfinitePlace.mk w.embedding).1 := inferInstance
    simpa using this
  let g : (L →ₐ[K] ℂ) → {w' : InfinitePlace L // w'.LiesOver w} :=
    fun σ => ⟨InfinitePlace.mk (σ : L →+* ℂ), hlies σ⟩
  have h2 : (∏ w' : {w' : InfinitePlace L // w'.LiesOver w},
          (∏ σ ∈ (Finset.univ : Finset (L →ₐ[K] ℂ)).filter
            (fun (σ : L →ₐ[K] ℂ) => InfinitePlace.mk (σ : L →+* ℂ) = w'.1), σ y))
      = ∏ σ : L →ₐ[K] ℂ, σ y := by
    rw [← Finset.prod_fiberwise_of_maps_to (s := (Finset.univ : Finset (L →ₐ[K] ℂ)))
      (t := (Finset.univ : Finset {w' : InfinitePlace L // w'.LiesOver w}))
      (g := g) (fun i _ => Finset.mem_univ _) (fun σ => σ y)]
    refine Finset.prod_congr rfl fun j _ => ?_
    refine Finset.prod_congr ?_ (fun σ _ => rfl)
    refine Finset.filter_congr fun σ _ => ?_
    simp only [g, Subtype.ext_iff]
  rw [h2, ← Algebra.norm_eq_prod_embeddings K ℂ y]
  rfl


/-- **The infinite places.** The component at an infinite place of the norm formula applied to a
principal idèle. -/
theorem normIdeleFun_principalIdele_ofInfinite {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (y : Lˣ) (w : InfinitePlace K) :
    NK.GlobalCFT.Idele.normIdeleFun K L (NK.GlobalCFT.Idele.principalIdele L y)
        (NK.GlobalCFT.Place.ofInfinite w) =
      NK.GlobalCFT.Idele.principalIdele K (Units.map (Algebra.norm K) y)
        (NK.GlobalCFT.Place.ofInfinite w) := by
  classical
  let LN : (x : InfinitePlace L) → (x.LiesOver w) → (w.Completion) :=
    fun x hx => ↑(@NK.GlobalCFT.Place.localNormInfinite K _ L _ _ x w hx
      (Units.map (algebraMap L (x.Completion)) y))
  rw [NK.GlobalCFT.Idele.normIdeleFun_ofInfinite, NK.GlobalCFT.Idele.principalIdele_apply]
  apply Units.ext
  apply (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).injective
  rw [Units.coe_prod, Units.coe_map, Units.coe_map, map_prod]
  suffices h : (∏ x ∈ (NK.GlobalCFT.Place.fiberInfinite (K := K) (L := L) w).attach,
        (NumberField.InfinitePlace.Completion.extensionEmbedding w)
          (LN x.1 ((NK.GlobalCFT.Place.mem_fiberInfinite (K := K) (L := L)).mp x.2)))
      = w.embedding (Algebra.norm K (y : L)) by
    exact h.trans (by simp)
  have hcongr : (∏ x ∈ (NK.GlobalCFT.Place.fiberInfinite (K := K) (L := L) w).attach,
        (NumberField.InfinitePlace.Completion.extensionEmbedding w)
          (LN x.1 ((NK.GlobalCFT.Place.mem_fiberInfinite (K := K) (L := L)).mp x.2)))
      = ∏ w' : {w' : InfinitePlace L // w'.LiesOver w},
        (NumberField.InfinitePlace.Completion.extensionEmbedding w) (LN w'.1 w'.2) := by
    rw [Finset.attach_eq_univ]
    refine Fintype.prod_equiv (Equiv.subtypeEquivRight
      (p := fun x => x ∈ NK.GlobalCFT.Place.fiberInfinite (K := K) (L := L) w)
      (q := fun x => x.LiesOver w)
      (fun x => NK.GlobalCFT.Place.mem_fiberInfinite)) _ _ (fun x => ?_)
    rfl
  rw [hcongr]
  have hstep : ∀ w' : {w' : InfinitePlace L // w'.LiesOver w},
      (NumberField.InfinitePlace.Completion.extensionEmbedding w) (LN w'.1 w'.2)
        = (if w'.1.IsRamified K then
              w'.1.embedding (y : L) * starRingEnd ℂ (w'.1.embedding (y : L))
            else if ComplexEmbedding.LiesOver w'.1.embedding w.embedding then
              w'.1.embedding (y : L)
            else starRingEnd ℂ (w'.1.embedding (y : L))) := by
    intro w'
    have := extensionEmbedding_localNormInfinite (w := w) (w' := w'.1) (hw' := w'.2) (y := y)
    simpa [LN] using this
  rw [Finset.prod_congr rfl (fun w' _ => hstep w'), prod_fiber_eq (y : L) w]

/-- **The main result.** The norm of a principal idèle is the principal idèle of the norm. -/
theorem globalCFT_normIdeleFun_principalIdele {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (y : Lˣ)
    (v : NK.GlobalCFT.Place K) :
    NK.GlobalCFT.Idele.normIdeleFun K L (NK.GlobalCFT.Idele.principalIdele L y) v =
      NK.GlobalCFT.Idele.principalIdele K (Units.map (Algebra.norm K) y) v := by
  cases v with
  | inl w => exact normIdeleFun_principalIdele_ofInfinite y w
  | inr Q => exact normIdeleFun_principalIdele_ofFinite y Q

end NK.GlobalCFT.Norm
