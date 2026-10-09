import Mathlib
import Submission.Work.SSGRoute.PT.LeadC8
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT.LeadC8

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
open scoped TensorProduct

/-! ## Elementary API for `toClass`

`toClass` is the class map from all cochains to the local `H¹`; on the locally constant cocycles it
is the quotient map and it is additive and `ZMod p`-homogeneous there.  These are the linearity
statements used in the assembly of `hreal_unr_of_unrCount`. -/

/-- On the locally constant cocycles, `toClass` is the quotient map. -/
theorem toClass_eq_mkQ (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) {f : (Ω ≃ₐ[k] Ω) → X}
    (hf : f ∈ Work.SSGRoute.lcCocycles p k Ω K X H) :
    Work.SSGRoute.toClass p k Ω K X H f = Submodule.mkQ _ ⟨f, hf⟩ := by
  rw [Work.SSGRoute.toClass, dif_pos hf]

/-- `toClass` is `ZMod p`-homogeneous on the locally constant cocycles. -/
theorem toClass_smul_zmod (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (c : ZMod p) {f : (Ω ≃ₐ[k] Ω) → X}
    (hf : f ∈ Work.SSGRoute.lcCocycles p k Ω K X H) :
    Work.SSGRoute.toClass p k Ω K X H (c • f) = c • Work.SSGRoute.toClass p k Ω K X H f := by
  rw [Work.SSGRoute.toClass, dif_pos (Submodule.smul_mem _ c hf), Work.SSGRoute.toClass, dif_pos hf,
    ← map_smul]
  rfl

/-- `toClass 0 = 0`. -/
theorem toClass_zero_zmod (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    Work.SSGRoute.toClass p k Ω K X H (0 : (Ω ≃ₐ[k] Ω) → X) = 0 := by
  rw [Work.SSGRoute.toClass, dif_pos (Submodule.zero_mem _)]
  exact map_zero _

/-- `toClass` is `ZMod p`-additive (subtraction) on the locally constant cocycles. -/
theorem toClass_sub_zmod (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) {f g : (Ω ≃ₐ[k] Ω) → X}
    (hf : f ∈ Work.SSGRoute.lcCocycles p k Ω K X H) (hg : g ∈ Work.SSGRoute.lcCocycles p k Ω K X H) :
    Work.SSGRoute.toClass p k Ω K X H (f - g) =
      Work.SSGRoute.toClass p k Ω K X H f - Work.SSGRoute.toClass p k Ω K X H g := by
  have h := Work.SSGRoute.toClass_add p k Ω K X H (Submodule.sub_mem _ hf hg) hg
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

/-! ## The unramified classes as classes of single cocycles

`unrClasses X A` is by definition the span of the classes of the locally constant cocycles vanishing
on the inertia.  That generating set is closed under the `ZMod p`-module operations (apply
`toClass_add`/`toClass_smul_zmod` to the sum/scalar multiple of witnesses), so the span is the
generating set: an element of `unrClasses X A` is the class of one inertia-vanishing cocycle. -/

theorem mem_unrClasses_iff (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    (A : ValuationSubring Ω)
    (y : Work.SSGRoute.H1loc p k Ω K X (SSGRoute.decomp k A)) :
    y ∈ Work.SSGRoute.LeadC8.unrClasses p k Ω K X A ↔
      ∃ f : (Ω ≃ₐ[k] Ω) → X,
        f ∈ Work.SSGRoute.lcCocycles p k Ω K X (SSGRoute.decomp k A) ∧
        (∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → f σ = 0) ∧
        Work.SSGRoute.toClass p k Ω K X (SSGRoute.decomp k A) f = y := by
  constructor
  · intro hy
    refine Submodule.span_induction (p := fun z (_ : z ∈ Submodule.span (ZMod p) _) =>
      ∃ f, f ∈ Work.SSGRoute.lcCocycles p k Ω K X (SSGRoute.decomp k A) ∧
        (∀ σ, SSGRoute.IsInertia k A σ → f σ = 0) ∧
        Work.SSGRoute.toClass p k Ω K X (SSGRoute.decomp k A) f = z) ?_ ?_ ?_ ?_ hy
    · rintro z ⟨f, hf, hfi, rfl⟩
      exact ⟨f, hf, hfi, rfl⟩
    · refine ⟨0, Submodule.zero_mem _, ?_, ?_⟩
      · intro σ hσ; rfl
      · exact toClass_zero_zmod p k Ω K X _
    · rintro z z' _ _ ⟨f, hf, hfi, hfeq⟩ ⟨g, hg, hgi, hgeq⟩
      refine ⟨f + g, Submodule.add_mem _ hf hg, ?_, ?_⟩
      · intro σ hσ; rw [Pi.add_apply, hfi σ hσ, hgi σ hσ, add_zero]
      · rw [Work.SSGRoute.toClass_add p k Ω K X _ hf hg, hfeq, hgeq]
    · rintro c z _ ⟨f, hf, hfi, hfeq⟩
      refine ⟨c • f, Submodule.smul_mem _ c hf, ?_, ?_⟩
      · intro σ hσ; rw [Pi.smul_apply, hfi σ hσ, smul_zero]
      · rw [toClass_smul_zmod p k Ω K X _ c hf, hfeq]
  · rintro ⟨f, hf, hfi, rfl⟩
    exact Submodule.subset_span ⟨f, hf, hfi, rfl⟩

/-! ## Descending the pairing to `H¹`

The clause bundle (1)–(3) (additivity in each variable, vanishing on a coboundary) turns `pair` on
the locally constant cocycles into a `ZMod p`-bilinear form on
`H¹_loc(D_A, M) × H¹_loc(D_A, M^∨(1))`. -/

theorem descendPairing (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω)
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
      ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hadd_l : ∀ (a a' : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a' →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a' →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      pair (SSGRoute.decomp k A) (a + a') b =
        pair (SSGRoute.decomp k A) a b + pair (SSGRoute.decomp k A) a' b)
    (hadd_r : ∀ (a : (Ω ≃ₐ[k] Ω) → M)
        (b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' →
      pair (SSGRoute.decomp k A) a (b + b') =
        pair (SSGRoute.decomp k A) a b + pair (SSGRoute.decomp k A) a b')
    (hcob : ∀ (a : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      (SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∨
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b) →
      pair (SSGRoute.decomp k A) a b = 0) :
    ∃ P : Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A) →ₗ[ZMod p]
            (Work.SSGRoute.H1loc p k Ω K
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A) →ₗ[ZMod p] ZMod p),
      ∀ (f : ↥(Work.SSGRoute.lcCocycles p k Ω K M (SSGRoute.decomp k A)))
        (g : ↥(Work.SSGRoute.lcCocycles p k Ω K
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A))),
        P (Submodule.mkQ _ f) (Submodule.mkQ _ g) = pair (SSGRoute.decomp k A) f.1 g.1 := by
  classical
  let G := Ω ≃ₐ[k] Ω
  let D : Subgroup G := SSGRoute.decomp k A
  let W := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)
  letI : AddCommGroup W :=
    inferInstanceAs (AddCommGroup (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
  let ZM : Submodule (ZMod p) (G → M) := Work.SSGRoute.lcCocycles p k Ω K M D
  let ZN : Submodule (ZMod p) (G → W) := Work.SSGRoute.lcCocycles p k Ω K W D
  let cobM : Submodule (ZMod p) (G → M) := Work.SSGRoute.coboundaries p k Ω K M D
  let cobN : Submodule (ZMod p) (G → W) := Work.SSGRoute.coboundaries p k Ω K W D
  let DM : Submodule (ZMod p) ↥ZM := Submodule.comap ZM.subtype cobM
  let DN : Submodule (ZMod p) ↥ZN := Submodule.comap ZN.subtype cobN
  have hadd1 : ∀ (f f' : ↥ZM) (g : ↥ZN),
      pair D (f + f').1 g.1 = pair D f.1 g.1 + pair D f'.1 g.1 := by
    intro f f' g
    exact hadd_l f.1 f'.1 g.1 f.2.1 f.2.2 f'.2.1 f'.2.2 g.2.1 g.2.2
  have hadd2 : ∀ (f : ↥ZM) (g g' : ↥ZN),
      pair D f.1 (g + g').1 = pair D f.1 g.1 + pair D f.1 g'.1 := by
    intro f g g'
    exact hadd_r f.1 g.1 g'.1 f.2.1 f.2.2 g.2.1 g.2.2 g'.2.1 g'.2.2
  have hzero1 : ∀ (g : ↥ZN), pair D (0 : G → M) g.1 = 0 := by
    intro g
    have h0 : (0 : G → M) ∈ ZM := Submodule.zero_mem ZM
    have h := hadd_l (0 : G → M) (0 : G → M) g.1 h0.1 h0.2 h0.1 h0.2 g.2.1 g.2.2
    simp only [zero_add] at h
    exact (add_left_cancel (by rw [add_zero]; exact h)).symm
  have hzero2 : ∀ (f : ↥ZM), pair D f.1 (0 : G → W) = 0 := by
    intro f
    have h0 : (0 : G → W) ∈ ZN := Submodule.zero_mem ZN
    have h := hadd_r f.1 (0 : G → W) (0 : G → W) f.2.1 f.2.2 h0.1 h0.2 h0.1 h0.2
    simp only [zero_add] at h
    exact (add_left_cancel (by rw [add_zero]; exact h)).symm
  have hsmul1 : ∀ (c : ZMod p) (f : ↥ZM) (g : ↥ZN),
      pair D (c • f).1 g.1 = c • pair D f.1 g.1 := by
    intro c f g
    let Φg : ↥ZM →+ ZMod p :=
      { toFun := fun x => pair D x.1 g.1
        map_zero' := hzero1 g
        map_add' := fun x y => hadd1 x y g }
    exact ZMod.map_smul Φg c f
  have hsmul2 : ∀ (c : ZMod p) (f : ↥ZM) (g : ↥ZN),
      pair D f.1 (c • g).1 = c • pair D f.1 g.1 := by
    intro c f g
    let Ψf : ↥ZN →+ ZMod p :=
      { toFun := fun y => pair D f.1 y.1
        map_zero' := hzero2 f
        map_add' := fun x y => hadd2 f x y }
    exact ZMod.map_smul Ψf c g
  let PM : ↥ZM →ₗ[ZMod p] (↥ZN →ₗ[ZMod p] ZMod p) :=
    LinearMap.mk₂ (ZMod p) (fun f g => pair D f.1 g.1) hadd1 hsmul1 hadd2 hsmul2
  have PM_apply : ∀ (f : ↥ZM) (g : ↥ZN), PM f g = pair D f.1 g.1 := by
    intro f g; rfl
  have hDN : ∀ (f : ↥ZM), DN ≤ (PM f).ker := by
    intro f g hg
    rw [LinearMap.mem_ker, PM_apply]
    exact hcob f.1 g.1 f.2.1 f.2.2 g.2.1 g.2.2 (Or.inr hg)
  let Q : ↥ZM →ₗ[ZMod p] (↥ZN ⧸ DN →ₗ[ZMod p] ZMod p) :=
    { toFun := fun f => Submodule.liftQ DN (PM f) (hDN f)
      map_add' := by
        intro f f'
        apply LinearMap.ext
        intro w
        obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective DN w
        simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.add_apply]
        rw [map_add]
        rfl
      map_smul' := by
        intro c f
        apply LinearMap.ext
        intro w
        obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective DN w
        simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.smul_apply,
          RingHom.id_apply, LinearMap.map_smul] }
  have hDM : DM ≤ Q.ker := by
    intro f hf
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro w
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective DN w
    simp only [Q, Submodule.mkQ_apply]
    exact hcob f.1 g.1 f.2.1 f.2.2 g.2.1 g.2.2 (Or.inl hf)
  refine ⟨Submodule.liftQ DM Q hDM, ?_⟩
  intro f g
  rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
  simp only [Q, Submodule.mkQ_apply]
  exact PM_apply f g

/-- **R1.**  The `hreal_unr` clause of `finiteS_converse_canonical_v7` at one good place, for an
abstract `pair`, from the local clause bundle (1)-(4), orthogonality on unramified classes (6), and
the dimension count `dim H¹(D_A,M) ≤ dim unrClasses M + dim unrClasses M^∨(1)`.  The realiser `a`
produced is a locally constant `M`-cocycle vanishing on the inertia of `A`. -/
theorem hreal_unr_of_unrCount (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hp : ¬ A.valuation (p : Ω) < 1) (hram : ¬ SSGRoute.IsRamifiedIn k K A)
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
      ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hadd_l : ∀ (a a' : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a' →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a' →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      pair (SSGRoute.decomp k A) (a + a') b =
        pair (SSGRoute.decomp k A) a b + pair (SSGRoute.decomp k A) a' b)
    (hadd_r : ∀ (a : (Ω ≃ₐ[k] Ω) → M)
        (b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' →
      pair (SSGRoute.decomp k A) a (b + b') =
        pair (SSGRoute.decomp k A) a b + pair (SSGRoute.decomp k A) a b')
    (hcob : ∀ (a : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      (SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∨
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b) →
      pair (SSGRoute.decomp k A) a b = 0)
    (hperf_l : ∀ a : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b → pair (SSGRoute.decomp k A) a b = 0) →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) a)
    (hperf_r : ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      (∀ a : (Ω ≃ₐ[k] Ω) → M,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a → pair (SSGRoute.decomp k A) a b = 0) →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (horth : ∀ (a : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) →
      (∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → a σ = 0 ∧ b σ = 0) →
      pair (SSGRoute.decomp k A) a b = 0)
    (hcount : Module.finrank (ZMod p) (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) ≤
      Module.finrank (ZMod p) ↥(Work.SSGRoute.LeadC8.unrClasses p k Ω K M A) +
      Module.finrank (ZMod p) ↥(Work.SSGRoute.LeadC8.unrClasses p k Ω K
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) A)) :
    ∀ lam : ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p,
      (∀ b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
        lam (b + b') = lam b + lam b') →
      (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b → lam b = 0) →
      (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) → lam b = 0) →
      ∃ a : (Ω ≃ₐ[k] Ω) → M,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a ∧
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → a σ = 0) ∧
        ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
          pair (SSGRoute.decomp k A) a b = lam b := by
  classical
  intro lam h1 h2 h3
  let G := Ω ≃ₐ[k] Ω
  let W := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)
  letI : AddCommGroup W :=
    inferInstanceAs (AddCommGroup (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
  let ZM : Submodule (ZMod p) (G → M) := Work.SSGRoute.lcCocycles p k Ω K M (SSGRoute.decomp k A)
  let ZN : Submodule (ZMod p) (G → W) :=
    Work.SSGRoute.lcCocycles p k Ω K W (SSGRoute.decomp k A)
  let DMM : Submodule (ZMod p) ↥ZM :=
    Submodule.comap ZM.subtype (Work.SSGRoute.coboundaries p k Ω K M (SSGRoute.decomp k A))
  let DNN : Submodule (ZMod p) ↥ZN :=
    Submodule.comap ZN.subtype (Work.SSGRoute.coboundaries p k Ω K W (SSGRoute.decomp k A))
  haveI hMTfin : Finite (TensorProduct (ZMod p) M T) := by
    haveI : Module.Finite (ZMod p) (TensorProduct (ZMod p) M T) :=
      Module.Finite.tensorProduct (ZMod p) M T
    exact Module.finite_of_finite (ZMod p)
  haveI hNfin : Finite W :=
    Finite.of_injective
      (fun f : W => (f : TensorProduct (ZMod p) M T → ZMod p))
      (fun f g hfg => LinearMap.ext (fun x => congrFun hfg x))
  obtain ⟨nA, φA, hφA⟩ := Work.SSGRoute.PT.exists_finite_spanning_locCocycles p k Ω K M A hA
  obtain ⟨nB, ψB, hψB⟩ := Work.SSGRoute.PT.exists_finite_spanning_locCocycles p k Ω K W A hA
  obtain ⟨a₀, hac, hal, haeq⟩ :=
    Work.SSGRoute.PT.localPairing_surjective_dual p k Ω K T M A hA pair
      hadd_l hadd_r hcob hperf_l hperf_r ⟨nA, φA, hφA⟩ ⟨nB, ψB, hψB⟩ lam h1 h2
  obtain ⟨P, hP⟩ := descendPairing p k Ω K T M A pair hadd_l hadd_r hcob
  have hPm : ∀ (f : ↥ZM) (g : ↥ZN),
      P (Submodule.mkQ DMM f) (Submodule.mkQ DNN g) = pair (SSGRoute.decomp k A) f.1 g.1 :=
    fun f g => hP f g
  have htoCM : ∀ {f : G → M} (hf : f ∈ ZM),
      Work.SSGRoute.toClass p k Ω K M (SSGRoute.decomp k A) f = Submodule.mkQ DMM ⟨f, hf⟩ := by
    intro f hf
    exact toClass_eq_mkQ p k Ω K M (SSGRoute.decomp k A) hf
  have htoCN : ∀ {f : G → W} (hf : f ∈ ZN),
      Work.SSGRoute.toClass p k Ω K W (SSGRoute.decomp k A) f = Submodule.mkQ DNN ⟨f, hf⟩ := by
    intro f hf
    exact toClass_eq_mkQ p k Ω K W (SSGRoute.decomp k A) hf
  haveI hVfin : Finite (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) :=
    Work.SSGRoute.PT.finite_H1loc p k Ω K M A hA
  haveI hWfin : Finite (Work.SSGRoute.H1loc p k Ω K W (SSGRoute.decomp k A)) :=
    Work.SSGRoute.PT.finite_H1loc p k Ω K W A hA
  haveI hVfd : FiniteDimensional (ZMod p) (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) :=
    Module.Finite.of_finite
  haveI hWfd : FiniteDimensional (ZMod p) (Work.SSGRoute.H1loc p k Ω K W (SSGRoute.decomp k A)) :=
    Module.Finite.of_finite
  -- perfectness on the right: the descended pairing has no kernel in the second variable
  have hr : ∀ w : Work.SSGRoute.H1loc p k Ω K W (SSGRoute.decomp k A),
      (∀ v : Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A), P v w = 0) → w = 0 := by
    intro w hw
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective DNN w
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine hperf_r g.1 g.2.1 g.2.2 ?_
    intro a ha hl
    have h1' : P (Submodule.mkQ DMM ⟨a, ⟨ha, hl⟩⟩) (Submodule.mkQ DNN g) = 0 :=
      hw (Submodule.mkQ DMM ⟨a, ⟨ha, hl⟩⟩)
    rw [hPm ⟨a, ⟨ha, hl⟩⟩ g] at h1'
    exact h1'
  -- orthogonality of the two spans, from the generator-wise hypothesis `horth`
  have horthP : ∀ u ∈ Work.SSGRoute.LeadC8.unrClasses p k Ω K M A,
      ∀ u' ∈ Work.SSGRoute.LeadC8.unrClasses p k Ω K W A, P u u' = 0 := by
    intro u hu u' hu'
    refine Submodule.span_induction (p := fun z (_ : z ∈ Submodule.span (ZMod p) _) => P z u' = 0)
      ?_ ?_ ?_ ?_ hu
    · rintro z ⟨f, hf, hfi, rfl⟩
      refine Submodule.span_induction (p := fun z (_ : z ∈ Submodule.span (ZMod p) _) =>
          P (Work.SSGRoute.toClass p k Ω K M (SSGRoute.decomp k A) f) z = 0) ?_ ?_ ?_ ?_ hu'
      · rintro z ⟨g, hg, hgi, rfl⟩
        rw [htoCM hf, htoCN hg, hPm ⟨f, hf⟩ ⟨g, hg⟩]
        exact horth f g hf hg (fun σ hσ => ⟨hfi σ hσ, hgi σ hσ⟩)
      · exact map_zero _
      · intro z z' _ _ hz hz'
        rw [map_add, hz, hz', add_zero]
      · intro c z _ hz
        rw [map_smul, hz, smul_zero]
    · simp
    · intro z z' _ _ hz hz'
      rw [map_add, LinearMap.add_apply, hz, hz', add_zero]
    · intro c z _ hz
      rw [map_smul, LinearMap.smul_apply, hz, smul_zero]
  -- the class of the realiser is orthogonal to the unramified classes of the second variable
  have hv : ∀ u' ∈ Work.SSGRoute.LeadC8.unrClasses p k Ω K W A,
      P (Work.SSGRoute.toClass p k Ω K M (SSGRoute.decomp k A) a₀) u' = 0 := by
    intro u' hu'
    refine Submodule.span_induction (p := fun z (_ : z ∈ Submodule.span (ZMod p) _) =>
        P (Work.SSGRoute.toClass p k Ω K M (SSGRoute.decomp k A) a₀) z = 0) ?_ ?_ ?_ ?_ hu'
    · rintro z ⟨g, hg, hgi, rfl⟩
      rw [htoCM ⟨hac, hal⟩, htoCN hg, hPm ⟨a₀, ⟨hac, hal⟩⟩ ⟨g, hg⟩, haeq g hg.1 hg.2]
      exact h3 g hg.1 hg.2 hgi
    · exact map_zero _
    · intro z z' _ _ hz hz'
      rw [map_add, hz, hz', add_zero]
    · intro c z _ hz
      rw [map_smul, hz, smul_zero]
  have hmem : Work.SSGRoute.toClass p k Ω K M (SSGRoute.decomp k A) a₀ ∈
      Work.SSGRoute.LeadC8.unrClasses p k Ω K M A :=
    Work.SSGRoute.LeadC8.ann_le_of_finrank (F := ZMod p) P hr
      (Work.SSGRoute.LeadC8.unrClasses p k Ω K M A)
      (Work.SSGRoute.LeadC8.unrClasses p k Ω K W A) horthP hcount
      (Work.SSGRoute.toClass p k Ω K M (SSGRoute.decomp k A) a₀) hv
  -- an unramified class is the class of a single inertia-vanishing cocycle
  obtain ⟨u, huc, hui, hueq⟩ :=
    (mem_unrClasses_iff p k Ω K M A
      (Work.SSGRoute.toClass p k Ω K M (SSGRoute.decomp k A) a₀)).mp hmem
  refine ⟨a₀, hac, hal, ?_, fun b hbc hbl => haeq b hbc hbl⟩
  -- `a₀` is cohomologous to the inertia-vanishing `u`, hence itself inertia-vanishing
  refine Work.SSGRoute.PT.eq_zero_of_isInertia_of_sub_isCoboundary k Ω K A hram hui ?_
  have hcl : a₀ - u ∈ ZM := Submodule.sub_mem _ ⟨hac, hal⟩ huc
  have hz : Work.SSGRoute.toClass p k Ω K M (SSGRoute.decomp k A) (a₀ - u) = 0 := by
    rw [toClass_sub_zmod p k Ω K M (SSGRoute.decomp k A) ⟨hac, hal⟩ huc, hueq, sub_self]
  exact (Work.SSGRoute.toClass_eq_zero_iff p k Ω K M (SSGRoute.decomp k A) hcl).mp hz

end Work.SSGRoute.PT.LeadC8
