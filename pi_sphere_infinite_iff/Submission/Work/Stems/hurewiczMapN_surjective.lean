import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Stems.SphereHomologyInject
import Submission.Work.Bordism.toSSet_coprod_iso
import Submission.Work.Stems.HurewiczNeutral
import Submission.Work.Serre.simpHomExists
import Submission.Work.Serre.simpHomChain
import Submission.Work.Serre.prismHom_chain_identity
import Submission.Work.RatHurewicz.ConnectivityBridge
import Submission.Work.Stems.HurewiczNeutralAgree
import Submission.Work.Stems.HurewiczMap
import Submission.Work.RatHurewicz.Bridge.exists_collapse_simplex
import Submission.Work.RatHurewicz.Bridge.chainBoundary
import Submission.Work.RatHurewicz.Bridge.HomologyAux
import Submission.Work.RatHurewicz.Bridge.SigmaChain
import Submission.Work.RatHurewicz.Bridge.exists_collapse_simplex
import Submission.Work.Serre.simpHomChain
import Submission.Work.Stems.HurewiczNeutralAgree

/-!
# The surjectivity half of the integral Hurewicz result in the first non-vanishing degree

This file reduces the statement to the per-simplex "spherical replacement" statement
`Work.Stems.perSimplexSpherical`.
-/

open CategoryTheory AlgebraicTopology Simplicial
open scoped Topology unitInterval Simplicial

namespace Work.Stems

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The singular chain complex of `X` with `ℤ`-coefficients, in the presentation of area SERRE. -/
abbrev hChain (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat ℤ) ℕ :=
  Work.Serre.singChainC X

/-- The singular simplicial set of `X`, in degree `n`. -/
abbrev hSimplex (X : Type) [TopologicalSpace X] (n : ℕ) : Type :=
  (Work.Serre.singX X).obj (Opposite.op (SimplexCategory.mk n))

/-- The chain carried by a singular `n`-simplex. -/
abbrev simplexChain (n : ℕ) (a : hSimplex X n) : (hChain X).X n :=
  (ModuleCat.Hom.hom ((Work.Serre.singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ) a)) (1 : ℤ)

theorem coords_simplexChain (n : ℕ) (a : hSimplex X n) :
    Work.Cohomology.Crux33.coords (Work.Serre.singX X) n (simplexChain (X := X) n a) =
      Finsupp.single a 1 :=
  Work.Cohomology.Crux33.coords_ι _ _ _

theorem simplexChain_ne_zero (n : ℕ) (a : hSimplex X n) : simplexChain (X := X) n a ≠ 0 := by
  intro h
  have h1 := congrArg (Work.Cohomology.Crux33.coords (Work.Serre.singX X) n) h
  rw [coords_simplexChain, map_zero] at h1
  have h2 := congrArg (fun (f : hSimplex X n →₀ ℤ) => f a) h1
  simpa using h2

/-- The constant singular `n`-simplex at `x₀`. -/
def constSimplex (n : ℕ) (x₀ : X) : hSimplex X n :=
  Work.RatHurewicz.Bridge.simplexOf n (ContinuousMap.const (stdSimplex ℝ (Fin (n + 1))) x₀)

theorem delta_constSimplex (m : ℕ) (x₀ : X) (i : Fin (m + 2)) :
    (Work.Serre.singX X).δ i (constSimplex (X := X) (m + 1) x₀) =
      constSimplex (X := X) m x₀ := by
  apply ((TopCat.of X).toSSetObjEquivT (Opposite.op (SimplexCategory.mk m))).injective
  change ((TopCat.of X).toSSetObjEquivT (Opposite.op ⦋m⦌))
      (((TopCat.toSSet.obj (TopCat.of X)).δ i)
        (Work.RatHurewicz.Bridge.simplexOf (m + 1)
          (ContinuousMap.const (stdSimplex ℝ (Fin (m + 2))) x₀)))
    = ContinuousMap.const (stdSimplex ℝ (Fin (m + 1))) x₀
  exact Work.RatHurewicz.Bridge.toSSetObjEquiv_delta_simplexOf_const (m := m) (y := x₀) i

/-- A finite sum of multiples of a fixed element is the multiple by the sum of the
coefficients.  (Stated here because `Finset.sum_smul` has the opposite orientation of the
`∈`-binder.) -/
theorem finsetSumZsmul_const {M : Type} [AddCommGroup M] (ι : Type)
    (s : Finset ι) (r : ι → ℤ) (c : M) :
    (∑ i ∈ s, r i • c) = (∑ i ∈ s, r i) • c := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, add_zsmul]

/-- The alternating sign `ε n = ∑_{i=0}^{n} (-1)^i ∈ {0,1}`. -/
def epsZ (n : ℕ) : ℤ := ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ)

theorem epsZ_eq (n : ℕ) : epsZ n = if Even n then 1 else 0 := by
  rw [epsZ, Fin.sum_neg_one_pow]
  by_cases hn : Even n
  · rw [if_neg (by rw [Nat.even_add_one]; exact not_not_intro hn), if_pos hn]
  · rw [if_pos (by rwa [Nat.even_add_one]), if_neg hn]

theorem epsZ_sq (n : ℕ) : epsZ n * epsZ n = epsZ n := by
  rw [epsZ_eq]
  by_cases hn : Even n <;> simp [hn]

theorem epsZ_sub (n : ℕ) : epsZ n * (1 - epsZ n) = 0 := by
  rw [epsZ_eq]
  by_cases hn : Even n <;> simp [hn]

/-- The boundary of the chain of the constant `(m+1)`-simplex. -/
theorem d_constSimplexChain (m : ℕ) (x₀ : X) :
    (hChain X).d (m + 1) m (simplexChain (X := X) (m + 1) (constSimplex (X := X) (m + 1) x₀)) =
      epsZ (m + 1) • simplexChain (X := X) m (constSimplex (X := X) m x₀) := by
  rw [Work.RatHurewicz.Bridge.d_ιChainComplex_one]
  have hterm : ∀ i : Fin (m + 2),
      (-1 : ℤ) ^ (i : ℕ) • simplexChain (X := X) m
          ((Work.Serre.singX X).δ i (constSimplex (X := X) (m + 1) x₀))
        = (-1 : ℤ) ^ (i : ℕ) • simplexChain (X := X) m (constSimplex (X := X) m x₀) :=
    fun i => by rw [delta_constSimplex m x₀ i]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  rw [finsetSumZsmul_const (Fin (m + 2)) Finset.univ (fun i => (-1 : ℤ) ^ (i : ℕ))
    (simplexChain (X := X) m (constSimplex (X := X) m x₀))]
  rfl

/-- The compression property of the pair `(X, {x₀})` at level `k` from the vanishing of `π_k`. -/
theorem compressRel_singleton (k : ℕ) (x₀ : X)
    (h : Subsingleton (HomotopyGroup (Fin k) X x₀)) : Work.RatHurewicz.CompressRel X {x₀} k := by
  intro f hf
  let hp : GenLoop (Fin k) X x₀ := ⟨f, fun y hy => hf y hy⟩
  have hrel : GenLoop.Homotopic hp GenLoop.const :=
    Quotient.exact (Subsingleton.elim (α := HomotopyGroup (Fin k) X x₀)
      (Quotient.mk _ hp) (Quotient.mk _ GenLoop.const))
  let G : C((Fin k → unitInterval) × unitInterval, X) :=
    ⟨fun p => hrel.some.toHomotopy.toContinuousMap (p.2, p.1),
      hrel.some.toHomotopy.toContinuousMap.continuous.comp
        (continuous_snd.prodMk continuous_fst)⟩
  have hG : ∀ (a : Fin k → unitInterval) (t : unitInterval),
      G (a, t) = hrel.some.toHomotopy (t, a) := fun _ _ => rfl
  refine ⟨G, ?_, ?_, ?_⟩
  · intro x
    rw [hG]
    exact hrel.some.toHomotopy.apply_zero x
  · intro x hx t
    rw [hG]
    exact hrel.some.eq_fst t hx
  · intro x
    rw [hG, hrel.some.toHomotopy.apply_one]
    rfl

/-- The compression hypothesis in degrees `≤ k`. -/
theorem compressHyp_singleton (k : ℕ) (x₀ : X)
    (h : ∀ i : ℕ, i ≤ k → Subsingleton (HomotopyGroup (Fin i) X x₀)) :
    Work.Serre.CompressHyp X {x₀} k :=
  fun i hi => compressRel_singleton i x₀ (h i hi)

/-- The "top" map of the compression family is the constant `x₀` simplex on every simplex. -/
theorem topChainMap_simplexChain (m : ℕ) {x₀ : X} (H : Work.Serre.SimpHom X {x₀} m)
    (a : hSimplex X m) :
    (ModuleCat.Hom.hom (Work.Serre.topChainMap H m)) (simplexChain (X := X) m a)
      = simplexChain (X := X) m (constSimplex (X := X) m x₀) := by
  rw [Work.Serre.topChainMap_gen]
  change simplexChain (X := X) m (Work.Serre.gSimplex H m a)
    = simplexChain (X := X) m (constSimplex (X := X) m x₀)
  rw [show Work.Serre.gSimplex H m a = constSimplex (X := X) m x₀ from ?_]
  apply ((TopCat.of X).toSSetObjEquivT (Opposite.op (SimplexCategory.mk m))).injective
  rw [Work.Serre.toSSetObjEquiv_gSimplex]
  change Work.Serre.topSimplex H m ((TopCat.of X).toSSetObjEquivT
      (Opposite.op (SimplexCategory.mk m)) a) = ContinuousMap.const _ x₀
  ext z
  rw [Work.Serre.topSimplex_apply]
  exact H.htop m le_rfl _ z

/-- The `n`-th augmentation: the sum of the coefficients of a singular `n`-chain. -/
def aug (n : ℕ) : (hChain X).X n →ₗ[ℤ] ℤ :=
  (Finsupp.linearCombination ℤ fun _ : hSimplex X n => (1 : ℤ)).comp
    (Work.Cohomology.Crux33.coords (Work.Serre.singX X) n)

theorem aug_simplexChain (n : ℕ) (a : hSimplex X n) :
    aug (X := X) n (simplexChain (X := X) n a) = 1 := by
  unfold aug
  rw [LinearMap.comp_apply, coords_simplexChain, Finsupp.linearCombination_single, one_smul]

/-- The chain-level operator whose cycles are the "spherical replacements" of the simplices. -/
def Zeta (j : ℕ) (x₀ : X) (H : Work.Serre.SimpHom X {x₀} (j + 1)) :
    (hChain X).X (j + 2) →ₗ[ℤ] (hChain X).X (j + 2) :=
  LinearMap.id
    - (ModuleCat.Hom.hom (Work.Serre.prismHom H (j + 1))).comp
        (ModuleCat.Hom.hom ((hChain X).d (j + 2) (j + 1)))
    - (LinearMap.toSpanSingleton ℤ ((hChain X).X (j + 2))
        (epsZ (j + 2) • simplexChain (X := X) (j + 2) (constSimplex (X := X) (j + 2) x₀))).comp
        (aug (X := X) (j + 2))

/-- **The crux**: the spherical replacement of a single simplex.

For every singular `(j+2)`-simplex `a`, the chain `Zeta j x₀ H (simplexChain a)` (the chain-level
"pinched" form of `a`) is a cycle whose class is the Hurewicz image of a class in `π_{j+2}(X,x₀)`. -/
def PerSimplexSpherical (j : ℕ) (x₀ : X) (H : Work.Serre.SimpHom X {x₀} (j + 1)) : Prop :=
  ∀ a : hSimplex X (j + 2), ∃ (z : (hChain X).cycles (j + 2)) (p : HomotopyGroup (Fin (j + 2)) X x₀),
    (ModuleCat.Hom.hom ((hChain X).iCycles (j + 2)) z = Zeta j x₀ H (simplexChain (X := X) (j + 2) a))
      ∧ (hurewiczMapN (j + 2) (by omega) x₀ p = (hChain X).homologyπ (j + 2) z)



/-! ## The `Zeta` calculus and the assembly, inlined from the sibling modules

The sibling modules `Submission/Work/Stems/zetaCalculus.lean` and
`Submission/Work/Stems/surjectiveOfPerSimplex.lean` import this file (they are stated in
terms of the definitions above), so their proofs cannot be `import`ed back: they are
inlined verbatim here instead (with `σ` renamed to `s`, since `σ` is a notation token in
the scope opened here). -/

/-!
# The calculus of the operator `Zeta`

`Work.Stems.Zeta j x₀ H` is the chain-level "spherical replacement" operator attached to a
compression family `H : SimpHom X {x₀} (j+1)`.  This file proves the three structural properties
requested of it:

* its value on the chain of a single `(j+2)`-simplex (its definition, unfolded);
* it takes values in the cycles;
* it fixes every cycle.

The two non-formal inputs are the chain-homotopy identity
`Work.Serre.prismHom_chain_identity` (`∂T + T∂ = 𝟙 - τ`) and the fact that the augmentation
`Work.Stems.aug` satisfies `aug ∘ ∂ = ε · aug` with `ε n = ∑_{i ≤ n} (-1)^i ∈ {0,1}` together with
`ε n * ε n = ε n`.
-/

open CategoryTheory



set_option maxHeartbeats 4000000

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The canonical `ℤ`-scalar action on a chain group agrees with the one used by
`LinearMap.toSpanSingleton` (they are the two `ℤ`-module structures on an additive commutative
group, which coincide). -/
theorem toSpanSingleton_eq_smul (n : ℕ) (a : ℤ) (x : ↥((hChain X).X n)) :
    (LinearMap.toSpanSingleton ℤ ((hChain X).X n) x) a = a • x :=
  int_smul_eq_zsmul (inferInstance : Module ℤ ↥((hChain X).X n)) a x

/-- **The augmentation is compatible with the differential**: `aug ∘ ∂ = ε · aug`, where
`ε n = ∑_{i ≤ n} (-1)^i`.  This is what makes the `ε² = ε` cancellation in `zetaCalculus` work. -/
theorem aug_comp_d (n : ℕ) (x : (hChain X).X (n + 1)) :
    aug (X := X) n (ModuleCat.Hom.hom ((hChain X).d (n + 1) n) x)
      = epsZ (n + 1) * aug (X := X) (n + 1) x := by
  have key : ModuleCat.ofHom ((aug (X := X) n).comp
        (ModuleCat.Hom.hom ((hChain X).d (n + 1) n)))
      = ModuleCat.ofHom (epsZ (n + 1) • aug (X := X) (n + 1) :
          (hChain X).X (n + 1) →ₗ[ℤ] ℤ) := by
    apply SSet.chainComplex_hom_ext
    intro s
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    show aug (X := X) n ((ModuleCat.Hom.hom ((hChain X).d (n + 1) n))
        ((ModuleCat.Hom.hom ((Work.Serre.singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s)) 1))
      = (epsZ (n + 1) • aug (X := X) (n + 1))
        ((ModuleCat.Hom.hom ((Work.Serre.singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s)) 1)
    rw [LinearMap.smul_apply, Work.Stems.aug_simplexChain, smul_eq_mul, mul_one]
    have hterm : ∀ i : Fin (n + 2),
        (Work.Stems.aug (X := X) n) ((-1 : ℤ) ^ (i : ℕ) •
          (ModuleCat.Hom.hom ((Work.Serre.singX X).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) ((Work.Serre.singX X).δ i s))) 1)
          = (-1 : ℤ) ^ (i : ℕ) := by
      intro i
      rw [map_zsmul, Work.Stems.aug_simplexChain]
      simp
    rw [Work.RatHurewicz.Bridge.d_ιChainComplex_one, map_sum,
      Finset.sum_congr rfl (fun i _ => hterm i)]
    rfl
  have h := congrArg (fun (g : (hChain X).X (n + 1) ⟶ ModuleCat.of ℤ ℤ) =>
    (ModuleCat.Hom.hom g) x) key
  simpa using h

/-- The top chain map of a compression family ending in `{x₀}` sends every chain to a multiple of
the chain of the constant simplex at `x₀`. -/
theorem topChainMap_eq_smul_constSimplex (n : ℕ) {x₀ : X}
    (H : Work.Serre.SimpHom X {x₀} n) :
    ModuleCat.Hom.hom (Work.Serre.topChainMap H n)
      = (LinearMap.toSpanSingleton ℤ ((hChain X).X n)
          (simplexChain (X := X) n (constSimplex (X := X) n x₀))).comp (aug (X := X) n) := by
  have key : Work.Serre.topChainMap H n
      = ModuleCat.ofHom ((LinearMap.toSpanSingleton ℤ ((hChain X).X n)
          (simplexChain (X := X) n (constSimplex (X := X) n x₀))).comp (aug (X := X) n)) := by
    apply SSet.chainComplex_hom_ext
    intro s
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    show (ModuleCat.Hom.hom (Work.Serre.topChainMap H n))
        ((ModuleCat.Hom.hom ((Work.Serre.singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s)) 1)
      = ((LinearMap.toSpanSingleton ℤ ((hChain X).X n)
          (simplexChain (X := X) n (constSimplex (X := X) n x₀))).comp (aug (X := X) n))
        ((ModuleCat.Hom.hom ((Work.Serre.singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s)) 1)
    rw [LinearMap.comp_apply, aug_simplexChain, LinearMap.toSpanSingleton_apply_one,
      Work.Stems.topChainMap_simplexChain]
  exact congrArg ModuleCat.Hom.hom key

/-- The top chain map applied to a chain. -/
theorem topChainMap_apply (n : ℕ) {x₀ : X} (H : Work.Serre.SimpHom X {x₀} n)
    (c : (hChain X).X n) :
    ModuleCat.Hom.hom (Work.Serre.topChainMap H n) c
      = aug (X := X) n c • simplexChain (X := X) n (constSimplex (X := X) n x₀) := by
  rw [topChainMap_eq_smul_constSimplex n H, LinearMap.comp_apply, toSpanSingleton_eq_smul (X := X)]

/-- The chain homotopy identity `∂T + T∂ = 𝟙 - τ` of `Work.Serre.prismHom_chain_identity`,
evaluated on a chain of degree `j+1`. -/
theorem prism_elementwise (j : ℕ) {x₀ : X} (H : Work.Serre.SimpHom X {x₀} (j + 1))
    (x : (hChain X).X (j + 1)) :
    ModuleCat.Hom.hom ((hChain X).d (j + 2) (j + 1))
        (ModuleCat.Hom.hom (Work.Serre.prismHom H (j + 1)) x)
      = x - ModuleCat.Hom.hom (Work.Serre.topChainMap H (j + 1)) x
          - ModuleCat.Hom.hom (Work.Serre.prismHom H j)
              (ModuleCat.Hom.hom ((hChain X).d (j + 1) j) x) := by
  have h := Work.Serre.prismHom_chain_identity H j le_rfl
  have h2 := congrArg (fun (g : (hChain X).X (j + 1) ⟶ (hChain X).X (j + 1)) =>
    (ModuleCat.Hom.hom g) x) h
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_sub, LinearMap.sub_apply, ModuleCat.hom_id, LinearMap.id_apply] at h2
  rw [eq_sub_iff_add_eq]
  exact h2

/-- The definition of `Zeta` unfolded on a single chain, in the form used below. -/
theorem Zeta_apply (j : ℕ) (x₀ : X) (H : Work.Serre.SimpHom X {x₀} (j + 1))
    (c : (hChain X).X (j + 2)) :
    Zeta j x₀ H c
      = c - ModuleCat.Hom.hom (Work.Serre.prismHom H (j + 1))
            (ModuleCat.Hom.hom ((hChain X).d (j + 2) (j + 1)) c)
          - (aug (X := X) (j + 2) c * epsZ (j + 2)) •
              simplexChain (X := X) (j + 2) (constSimplex (X := X) (j + 2) x₀) := by
  rw [Zeta]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply]
  rw [toSpanSingleton_eq_smul (X := X), smul_smul]

/-- The differential of the chain of the constant `(j+2)`-simplex, with the index `j+2` kept
visible (a restatement of `Work.Stems.d_constSimplexChain`). -/
theorem d_constSimplexChain_two (j : ℕ) (x₀ : X) :
    ModuleCat.Hom.hom ((hChain X).d (j + 2) (j + 1))
        (simplexChain (X := X) (j + 2) (constSimplex (X := X) (j + 2) x₀))
      = epsZ (j + 2) • simplexChain (X := X) (j + 1) (constSimplex (X := X) (j + 1) x₀) := by
  have h := Work.Stems.d_constSimplexChain (X := X) (j + 1) x₀
  simpa using h

theorem zetaCalculus {X : Type} [TopologicalSpace X] (j : ℕ) (x₀ : X)
    (H : Work.Serre.SimpHom X {x₀} (j + 1)) :
    (∀ a : Work.Stems.hSimplex X (j + 2),
        Work.Stems.Zeta j x₀ H (Work.Stems.simplexChain (X := X) (j + 2) a)
          = Work.Stems.simplexChain (X := X) (j + 2) a
            - (ModuleCat.Hom.hom (Work.Serre.prismHom H (j + 1))
                (ModuleCat.Hom.hom ((Work.Stems.hChain X).d (j + 2) (j + 1))
                  (Work.Stems.simplexChain (X := X) (j + 2) a)))
            - Work.Stems.epsZ (j + 2) • Work.Stems.simplexChain (X := X) (j + 2)
                (Work.Stems.constSimplex (X := X) (j + 2) x₀))
      ∧ (∀ c : (Work.Stems.hChain X).X (j + 2),
          (Work.Stems.hChain X).d (j + 2) (j + 1) (Work.Stems.Zeta j x₀ H c) = 0)
      ∧ (∀ c : (Work.Stems.hChain X).X (j + 2),
          (Work.Stems.hChain X).d (j + 2) (j + 1) c = 0 → Work.Stems.Zeta j x₀ H c = c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rw [Zeta]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply]
    rw [aug_simplexChain, LinearMap.toSpanSingleton_apply_one]
  · intro c
    rw [Zeta_apply j x₀ H c, map_sub, map_sub, map_zsmul, d_constSimplexChain_two (X := X) j x₀]
    have hdd : ModuleCat.Hom.hom ((hChain X).d (j + 1) j)
        (ModuleCat.Hom.hom ((hChain X).d (j + 2) (j + 1)) c) = 0 := by
      have h0 : ModuleCat.Hom.hom ((hChain X).d (j + 2) (j + 1) ≫
          (hChain X).d (j + 1) j) = 0 := by
        rw [HomologicalComplex.d_comp_d, ModuleCat.hom_zero]
      change ModuleCat.Hom.hom ((hChain X).d (j + 2) (j + 1) ≫
          (hChain X).d (j + 1) j) c = 0
      rw [h0, LinearMap.zero_apply]
    rw [prism_elementwise j H (ModuleCat.Hom.hom ((hChain X).d (j + 2) (j + 1)) c), hdd,
      map_zero, topChainMap_apply (X := X) (j + 1) H (ModuleCat.Hom.hom ((hChain X).d (j + 2) (j + 1)) c),
      aug_comp_d (X := X) (j + 1) c]
    have hcoef : (aug (X := X) (j + 2) c * epsZ (j + 2)) * epsZ (j + 2)
        = epsZ (j + 2) * aug (X := X) (j + 2) c := by
      rw [mul_assoc, epsZ_sq, mul_comm]
    rw [smul_smul, hcoef, sub_zero, sub_sub]
    simp
  · intro c hc
    rw [Zeta_apply j x₀ H c, hc, map_zero, sub_zero]
    have h1 : epsZ (j + 2) * aug (X := X) (j + 2) c = 0 := by
      rw [← aug_comp_d (X := X) (j + 1) c, hc, map_zero]
    rw [mul_comm (aug (X := X) (j + 2) c) (epsZ (j + 2)), h1, zero_smul]
    simp

end

/-!
# `PerSimplexSpherical` implies the surjectivity of the Hurewicz map

`Work.Stems.PerSimplexSpherical j x₀ H` says that the "spherical replacement"
`Zeta j x₀ H (simplexChain a)` of every singular `(j+2)`-simplex `a` is a cycle whose homology
class is the Hurewicz image of a class of `π_{j+2}(X,x₀)`.

Here we extract the consequence: the Hurewicz map
`Work.Stems.hurewiczMapN (j+2) _ x₀ : π_{j+2}(X,x₀) → H_{j+2}(X;ℤ)` is **surjective**.

The argument is the standard one.

* `homologyπ : Z_{j+2} → H_{j+2}` is surjective, so a class `y` is the class of a cycle `z`.
* Every chain is a finite `ℤ`-linear combination of the chains `simplexChain a` of the simplices
  (`chain_eq_sum_simplexChain`, from the coordinate description `mk ∘ coords = 1` of the
  simplicial chain complex).
* `Zeta` is `ℤ`-linear and fixes cycles (`Work.Stems.zetaCalculus`), so the underlying chain of
  `z` is the corresponding combination of the *replacement chains* `Zeta (simplexChain a)`, each
  of which is the chain of a cycle `zf a` supplied by `PerSimplexSpherical`.
* Hence, in the cycle group, `∑ γ a • zf a = z`, and passing to homology with the `ℤ`-linearity
  of `homologyπ` gives `y = ∑ γ a • homologyπ (zf a) = ∑ γ a • hurewiczMapN (pf a)`.
* The `ℤ`-linearity of the Hurewicz map (through the additive packaging `Work.Stems.hurewiczHom`,
  which computes `hurewiczMapN`) turns the last sum into the Hurewicz image of the single class
  `Additive.toMul (∑ γ a • Additive.ofMul (pf a))`.
-/



noncomputable section

/-- The `ℤ`-linear map `mk` from the free module on the singular `n`-simplices back to the
`n`-chains, expanded as a `Finsupp.sum` along the generators `simplexChain`. -/
theorem mk_eq_sum_simplexChain {X : Type} [TopologicalSpace X] (n : ℕ)
    (γ : hSimplex X n →₀ ℤ) :
    Work.Cohomology.Crux33.mk (Work.Serre.singX X) n γ
      = γ.sum (fun a k => k • simplexChain (X := X) n a) := by
  simp only [Work.Cohomology.Crux33.mk, Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr ?_
  intro a k
  simpa [simplexChain]
    using map_zsmul ((Work.Serre.singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ) a).hom
      (γ a) (1 : ℤ)

/-- **Every singular chain is a finite `ℤ`-linear combination of the chains of simplices.**
This is the coordinate description of the simplicial chain complex: `mk ∘ coords = 1`, together
with the value `mk (single a 1) = simplexChain a` of `mk` on the generators. -/
theorem chain_eq_sum_simplexChain {X : Type} [TopologicalSpace X] (n : ℕ)
    (c : (hChain X).X n) :
    c = (Work.Cohomology.Crux33.coords (Work.Serre.singX X) n c).sum
          (fun a k => k • simplexChain (X := X) n a) := by
  have h1 : Work.Cohomology.Crux33.mk (Work.Serre.singX X) n
      (Work.Cohomology.Crux33.coords (Work.Serre.singX X) n c) = c :=
    LinearMap.congr_fun (Work.Cohomology.Crux33.mk_comp_coords (Work.Serre.singX X) n) c
  rw [← mk_eq_sum_simplexChain (X := X) n
    (Work.Cohomology.Crux33.coords (Work.Serre.singX X) n c)]
  exact h1.symm

/-- **The surjectivity half of the integral Hurewicz theorem in the first non-vanishing degree,
from the per-simplex spherical replacement.** -/
theorem surjectiveOfPerSimplex {X : Type} [TopologicalSpace X] (j : ℕ) (x₀ : X)
    (H : Work.Serre.SimpHom X {x₀} (j + 1)) (h : Work.Stems.PerSimplexSpherical j x₀ H) :
    Function.Surjective (Work.Stems.hurewiczMapN (j + 2) (by omega) x₀) := by
  intro y
  -- every homology class is the class of a cycle
  obtain ⟨z, hz⟩ :=
    (ModuleCat.epi_iff_surjective ((hChain X).homologyπ (j + 2))).mp inferInstance y
  -- the spherical replacements supplied by the hypothesis
  choose zf pf hzf hpf using fun a : hSimplex X (j + 2) => h a
  -- the underlying chain of `z` and its coordinates
  set c := (hChain X).iCycles (j + 2) z with hc
  set γ := Work.Cohomology.Crux33.coords (Work.Serre.singX X) (j + 2) c with hγ
  -- the candidate class: the sum of the `pf a` with the coefficients `γ a`
  refine ⟨Additive.toMul (∑ a ∈ γ.support, (γ a) • Additive.ofMul (pf a)), ?_⟩
  rw [← hurewiczHom_eq_hurewiczMapN (n := j + 1) (x₀ := x₀)]
  -- the Hurewicz class of the sum is the sum of the Hurewicz classes
  have step1 : hurewiczHom (j + 1) x₀ (∑ a ∈ γ.support, (γ a) • Additive.ofMul (pf a))
      = ∑ a ∈ γ.support, (γ a) • (hChain X).homologyπ (j + 2) (zf a) := by
    rw [map_sum (hurewiczHom (j + 1) x₀)]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h1 : hurewiczHom (j + 1) x₀ (Additive.ofMul (pf a))
        = hurewiczMapN (j + 2) (by omega) x₀ (pf a) := rfl
    rw [map_zsmul, h1, hpf a]
    rfl
  rw [step1]
  -- `homologyπ` is `ℤ`-linear
  have hsum : (∑ a ∈ γ.support, (γ a) • (hChain X).homologyπ (j + 2) (zf a))
      = (hChain X).homologyπ (j + 2) (∑ a ∈ γ.support, (γ a) • zf a) := by
    rw [map_sum (ModuleCat.Hom.hom ((hChain X).homologyπ (j + 2)))]
    exact Finset.sum_congr rfl fun a _ => (map_zsmul _ _ _).symm
  rw [hsum]
  -- the chain `c` in coordinates
  have hdecomp : c = ∑ a ∈ γ.support, (γ a) • simplexChain (X := X) (j + 2) a := by
    rw [hγ]
    exact chain_eq_sum_simplexChain (X := X) (j + 2) c
  -- the sum of the replacement cycles is the cycle `z`
  have hzsum : (∑ a ∈ γ.support, (γ a) • zf a) = z := by
    refine (ModuleCat.mono_iff_injective ((hChain X).iCycles (j + 2))).mp inferInstance ?_
    rw [map_sum (ModuleCat.Hom.hom ((hChain X).iCycles (j + 2)))]
    have h1 : ∀ a ∈ γ.support, (hChain X).iCycles (j + 2) ((γ a) • zf a)
        = Zeta j x₀ H ((γ a) • simplexChain (j + 2) a) := by
      intro a _
      rw [map_zsmul, hzf a, map_zsmul]
    rw [Finset.sum_congr rfl h1]
    rw [← map_sum (Zeta j x₀ H)]
    rw [← hdecomp, hc]
    -- `Zeta` fixes cycles
    rw [(zetaCalculus j x₀ H).2.2]
    rw [← CategoryTheory.comp_apply, HomologicalComplex.iCycles_d]
    simp
  rw [hzsum]
  exact hz

end


/-! ## The per-simplex spherical replacement, inlined from `Submission/Work/Stems/PerSimplex/`

The sub-development `Submission/Work/Stems/PerSimplex/*` proves the crux
`Work.Stems.PerSimplex.perSimplexSpherical_of_core`; those modules import this file, so
their proofs cannot be `import`ed back and are inlined verbatim here (with `σ` renamed to
`s`). -/

set_option backward.isDefEq.respectTransparency false

/-!
# The prism chain of a homotopy of simplices

For a continuous map `G : Δ^d × I → X` (a homotopy of a `d`-simplex) we define its **prism chain**
`prismChain d G ∈ C_{d+1}(X)`, the alternating sum of the chains of the `d + 1` simplicial pieces
of the product triangulation of `Δ^d × I`.  This is the chain-level avatar of the prism operator;
the face version of the current file's main theorem (`prismChainBoundary` in the sibling module)
computes its boundary as the difference of the top and bottom chains minus the alternating sum of
the prism chains of the face homotopies.
-/

open CategoryTheory AlgebraicTopology Simplicial
open scoped Topology unitInterval Simplicial BigOperators

namespace Work.Stems.PerSimplex

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The `k`-th simplicial piece of the product triangulation of `Δ^d × I` carries the singular
`(d+1)`-simplex `G ∘ pp d k`.  The **prism chain** is their alternating sum. -/
def prismChain (d : ℕ) (G : C(↥(stdSimplex ℝ (Fin (d+1))) × unitInterval, X)) :
    (Work.Stems.hChain X).X (d+1) :=
  ∑ k : Fin (d+1), (-1:ℤ)^((k:ℕ)+1) •
    Work.Stems.simplexChain (X:=X) (d+1)
      (Work.RatHurewicz.Bridge.simplexOf (d+1) (G.comp (Work.Serre.pp d k)))

@[simp] theorem prismChain_def (d : ℕ)
    (G : C(↥(stdSimplex ℝ (Fin (d+1))) × unitInterval, X)) :
    prismChain (X := X) d G
      = ∑ k : Fin (d+1), (-1:ℤ)^((k:ℕ)+1) •
          Work.Stems.simplexChain (X:=X) (d+1)
            (Work.RatHurewicz.Bridge.simplexOf (d+1) (G.comp (Work.Serre.pp d k))) := rfl

end

end Work.Stems.PerSimplex

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open CategoryTheory Limits AlgebraicTopology Simplicial
open scoped Simplicial BigOperators
open Work.RatHurewicz.Bridge (coface coface_apply)

namespace Work.Stems.PerSimplex

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The singular `(n+2)`-simplex carried by the `x`-th piece of the prism of `F`. -/
def px (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X)) (x : Fin (n+2)) :
    Work.Serre.SSetSimplex X (n+2) :=
  Work.RatHurewicz.Bridge.simplexOf (n+2) (F.comp (Work.Serre.pp (n+1) x))

/-- The singular `(n+1)`-simplex carried by the `y`-th piece of the prism of the `x`-th face
homotopy of `F`. -/
def qf (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X))
    (x : Fin (n+2)) (y : Fin (n+1)) : Work.Serre.SSetSimplex X (n+1) :=
  Work.RatHurewicz.Bridge.simplexOf (n+1)
    ((F.comp ((coface n x).prodMap (ContinuousMap.id unitInterval))).comp (Work.Serre.pp n y))

/-- The bottom simplex of `F`. -/
def pbot (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X)) :
    Work.Serre.SSetSimplex X (n+1) :=
  Work.RatHurewicz.Bridge.simplexOf (n+1) (F.comp (Work.Serre.botIncl (n+1)))

/-- The top simplex of `F`. -/
def ptop (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X)) :
    Work.Serre.SSetSimplex X (n+1) :=
  Work.RatHurewicz.Bridge.simplexOf (n+1) (F.comp (Work.Serre.topIncl (n+1)))

/-- The face of the singular simplex attached to a continuous map is the simplex attached to the
composite with the coface. -/
theorem delta_simplexOf (m : ℕ) (f : Fin (m+2)) (c : C(↥(stdSimplex ℝ (Fin (m+2))), X)) :
    (Work.Serre.singX X).δ f (Work.RatHurewicz.Bridge.simplexOf (m+1) c)
      = Work.RatHurewicz.Bridge.simplexOf m (c.comp (coface m f)) := by
  apply ((TopCat.of X).toSSetObjEquivT (Opposite.op (SimplexCategory.mk m))).injective
  rw [Work.Serre.toSSetObjEquiv_δ, Work.RatHurewicz.Bridge.toSSetObjEquiv_simplexOf,
    Work.RatHurewicz.Bridge.toSSetObjEquiv_simplexOf]

/-- The `0`-th face of the first prism piece is the top simplex. -/
theorem delta_px_zero (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X)) :
    (Work.Serre.singX X).δ 0 (px n F 0) = ptop n F := by
  rw [px, ptop, delta_simplexOf (n+1) 0 (F.comp (Work.Serre.pp (n+1) 0))]
  congr 1
  rw [ContinuousMap.comp_assoc, Work.Serre.pp_coface_zero_zero]

/-- The last face of the last prism piece is the bottom simplex. -/
theorem delta_px_last (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X)) :
    (Work.Serre.singX X).δ (Fin.last (n+2)) (px n F (Fin.last (n+1))) = pbot n F := by
  rw [px, pbot, delta_simplexOf (n+1) (Fin.last (n+2))
    (F.comp (Work.Serre.pp (n+1) (Fin.last (n+1))))]
  congr 1
  rw [ContinuousMap.comp_assoc, Work.Serre.pp_coface_last_last]

/-- The `(k+1)`-st face is shared by the `k`-th and `(k+1)`-st prism piece. -/
theorem delta_px_diag (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X))
    (k : Fin (n+1)) :
    (Work.Serre.singX X).δ k.castSucc.succ (px n F k.castSucc)
      = (Work.Serre.singX X).δ k.castSucc.succ (px n F k.succ) := by
  rw [px, px, delta_simplexOf (n+1) k.castSucc.succ (F.comp (Work.Serre.pp (n+1) k.castSucc)),
    delta_simplexOf (n+1) k.castSucc.succ (F.comp (Work.Serre.pp (n+1) k.succ))]
  congr 1
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, Work.Serre.pp_coface_diag]

/-- For `f < k`, the `f`-th face of the `k`-th prism piece is the prism piece of the `f`-th face. -/
theorem delta_px_lt (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X))
    (f : Fin (n+3)) (k : Fin (n+2)) (hfk : (f:ℕ) < (k:ℕ)) :
    (Work.Serre.singX X).δ f (px n F k)
      = qf n F ⟨(f:ℕ), by omega⟩ ⟨(k:ℕ)-1, by omega⟩ := by
  rw [px, qf, delta_simplexOf (n+1) f (F.comp (Work.Serre.pp (n+1) k))]
  congr 1
  rw [ContinuousMap.comp_assoc, Work.Serre.pp_coface_lt k f hfk]
  exact (ContinuousMap.comp_assoc F _ _).symm

/-- For `f > k+1`, the `f`-th face of the `k`-th prism piece is the prism piece of the
`(f-1)`-st face. -/
theorem delta_px_gt (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X))
    (f : Fin (n+3)) (k : Fin (n+2)) (hfk : (k:ℕ) + 1 < (f:ℕ)) :
    (Work.Serre.singX X).δ f (px n F k)
      = qf n F ⟨(f:ℕ)-1, by omega⟩ ⟨(k:ℕ), by omega⟩ := by
  rw [px, qf, delta_simplexOf (n+1) f (F.comp (Work.Serre.pp (n+1) k))]
  congr 1
  rw [ContinuousMap.comp_assoc, Work.Serre.pp_coface_gt k f hfk]
  exact (ContinuousMap.comp_assoc F _ _).symm

end

end Work.Stems.PerSimplex

namespace Work.Stems.PerSimplex

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The terms of the prism identity: the faces of the prism pieces, the prism pieces of the face
homotopies, and the two boundary terms. -/
def pval (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X)) :
    Work.Serre.PIdx n → (Work.Serre.SSetSimplex X (n+1) →₀ ℤ) := fun z =>
  match z with
  | Sum.inl (k, f) =>
      ((-1:ℤ)^((k:ℕ)+1+(f:ℕ))) • Finsupp.single ((Work.Serre.singX X).δ f (px n F k)) (1:ℤ)
  | Sum.inr (Sum.inl (x, y)) =>
      ((-1:ℤ)^((x:ℕ)+((y:ℕ)+1))) • Finsupp.single (qf n F x y) (1:ℤ)
  | Sum.inr (Sum.inr (Sum.inl _)) => - Finsupp.single (pbot n F) (1:ℤ)
  | Sum.inr (Sum.inr (Sum.inr _)) => Finsupp.single (ptop n F) (1:ℤ)

theorem pval_ne_zero (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X))
    (z : Work.Serre.PIdx n) : pval n F z ≠ 0 := by
  match z with
  | Sum.inl (k, f) =>
      intro h
      have h1 := congrArg (fun (w : Work.Serre.SSetSimplex X (n+1) →₀ ℤ) =>
        w ((Work.Serre.singX X).δ f (px n F k))) h
      simp only [pval, Finsupp.smul_apply, Finsupp.single_eq_same, Finsupp.zero_apply,
        smul_eq_mul, mul_one] at h1
      exact pow_ne_zero _ (by norm_num : (-1:ℤ) ≠ 0) h1
  | Sum.inr (Sum.inl (x, y)) =>
      intro h
      have h1 := congrArg (fun (w : Work.Serre.SSetSimplex X (n+1) →₀ ℤ) =>
        w (qf n F x y)) h
      simp only [pval, Finsupp.smul_apply, Finsupp.single_eq_same, Finsupp.zero_apply,
        smul_eq_mul, mul_one] at h1
      exact pow_ne_zero _ (by norm_num : (-1:ℤ) ≠ 0) h1
  | Sum.inr (Sum.inr (Sum.inl u)) =>
      intro h
      have h1 := congrArg (fun (w : Work.Serre.SSetSimplex X (n+1) →₀ ℤ) => w (pbot n F)) h
      simp only [pval, Finsupp.neg_apply, Finsupp.single_eq_same, Finsupp.zero_apply] at h1
      exact one_ne_zero (neg_eq_zero.mp h1)
  | Sum.inr (Sum.inr (Sum.inr u)) =>
      intro h
      have h1 := congrArg (fun (w : Work.Serre.SSetSimplex X (n+1) →₀ ℤ) => w (ptop n F)) h
      simp only [pval, Finsupp.single_eq_same, Finsupp.zero_apply] at h1
      exact one_ne_zero h1

theorem pval_pinv (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X))
    (z : Work.Serre.PIdx n) : pval n F (Work.Serre.pinv z) = - pval n F z := by
  match z with
  | Sum.inl (k, f) =>
      simp only [Work.Serre.pinv]
      by_cases h1 : (f:ℕ) < (k:ℕ)
      · rw [dif_pos h1]
        simp only [pval]
        rw [delta_px_lt n F f k h1, ← neg_smul]
        congr 1
        rw [show (↑k + 1 + ↑f : ℕ) = (↑f + (↑k - 1 + 1)) + 1 by omega, pow_succ]
        ring
      · rw [dif_neg h1]
        by_cases h2 : (f:ℕ) = (k:ℕ)
        · rw [dif_pos h2]
          by_cases h3 : (k:ℕ) = 0
          · rw [dif_pos h3]
            simp only [pval]
            rw [show (↑k + 1 + ↑f : ℕ) = 1 by omega, pow_one]
            rw [show (f : Fin (n+3)) = 0 from Fin.ext (by simp only [Fin.val_zero]; omega),
              show (k : Fin (n+2)) = 0 from Fin.ext (by simp only [Fin.val_zero]; omega),
              delta_px_zero n F]
            rw [neg_one_smul, neg_neg]
          · rw [dif_neg h3]
            simp only [pval]
            have hfac : (Work.Serre.singX X).δ f
                  (px n F (⟨(k:ℕ)-1, by have hk := k.isLt; omega⟩ : Fin (n+2)))
                = (Work.Serre.singX X).δ f (px n F k) := by
              let j : Fin (n+1) := ⟨(k:ℕ)-1, by have hk := k.isLt; omega⟩
              have hjv : (j:ℕ) = (k:ℕ)-1 := rfl
              have hjc : j.castSucc
                  = (⟨(k:ℕ)-1, by have hk := k.isLt; omega⟩ : Fin (n+2)) := rfl
              rw [← hjc]
              rw [show f = j.castSucc.succ from
                Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)]
              rw [show k = j.succ from Fin.ext (by simp only [Fin.val_succ]; omega)]
              exact delta_px_diag n F j
            rw [hfac, ← neg_smul]
            congr 1
            rw [show (↑k + 1 + ↑f : ℕ) = (↑k - 1 + 1 + ↑f) + 1 by omega, pow_succ]
            ring
        · rw [dif_neg h2]
          by_cases h4 : (f:ℕ) = (k:ℕ)+1
          · rw [dif_pos h4]
            by_cases h5 : (k:ℕ) = n+1
            · rw [dif_pos h5]
              simp only [pval]
              rw [show (↑k + 1 + ↑f : ℕ) = 2 * (n + 2) by omega]
              rw [pow_mul, show ((-1:ℤ)^2) = 1 by norm_num, one_pow, one_smul]
              rw [show (f : Fin (n+3)) = Fin.last (n+2) from
                  Fin.ext (by simp only [Fin.val_last]; omega),
                show (k : Fin (n+2)) = Fin.last (n+1) from
                  Fin.ext (by simp only [Fin.val_last]; omega),
                delta_px_last n F]
            · rw [dif_neg h5]
              simp only [pval]
              have hfac : (Work.Serre.singX X).δ f
                    (px n F (⟨(k:ℕ)+1, by have hk := k.isLt; omega⟩ : Fin (n+2)))
                  = (Work.Serre.singX X).δ f (px n F k) := by
                let j : Fin (n+1) := ⟨(k:ℕ), by have hk := k.isLt; omega⟩
                have hjv : (j:ℕ) = (k:ℕ) := rfl
                have hjs : j.succ
                    = (⟨(k:ℕ)+1, by have hk := k.isLt; omega⟩ : Fin (n+2)) := rfl
                rw [← hjs]
                rw [show f = j.castSucc.succ from
                  Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)]
                rw [show k = j.castSucc from Fin.ext (by simp only [Fin.val_castSucc]; omega)]
                exact (delta_px_diag n F j).symm
              rw [hfac, ← neg_smul]
              congr 1
              rw [show (↑k + 1 + 1 + ↑f : ℕ) = (↑k + 1 + ↑f) + 1 by omega, pow_succ]
              ring
          · rw [dif_neg h4]
            simp only [pval]
            rw [delta_px_gt n F f k (by omega), ← neg_smul]
            congr 1
            rw [show (↑k + 1 + ↑f : ℕ) = (↑f - 1 + (↑k + 1)) + 1 by omega, pow_succ]
            ring
  | Sum.inr (Sum.inl (x, y)) =>
      simp only [Work.Serre.pinv]
      by_cases h1 : (x:ℕ) ≤ (y:ℕ)
      · rw [dif_pos h1]
        simp only [pval]
        rw [delta_px_lt n F (⟨(x:ℕ), by have hx := x.isLt; omega⟩ : Fin (n+3))
          (⟨(y:ℕ)+1, by have hy := y.isLt; omega⟩ : Fin (n+2))
          (by simp only [Fin.val_mk]; omega), ← neg_smul]
        congr 1
        rw [show (↑y + 1 + 1 + ↑x : ℕ) = (↑x + (↑y + 1)) + 1 by omega, pow_succ]
        ring
      · rw [dif_neg h1]
        simp only [pval]
        rw [delta_px_gt n F (⟨(x:ℕ)+1, by have hx := x.isLt; omega⟩ : Fin (n+3))
          (⟨(y:ℕ), by have hy := y.isLt; omega⟩ : Fin (n+2))
          (by simp only [Fin.val_mk]; omega), ← neg_smul]
        congr 1
        rw [show (↑y + 1 + (↑x + 1) : ℕ) = (↑x + (↑y + 1)) + 1 by omega, pow_succ]
        ring
  | Sum.inr (Sum.inr (Sum.inl u)) =>
      cases u
      simp only [Work.Serre.pinv, pval]
      rw [show (↑(Fin.last (n+1)) + 1 + ↑(Fin.last (n+2)) : ℕ) = 2 * (n + 2) by
        simp only [Fin.val_last]; omega]
      rw [pow_mul, show ((-1:ℤ)^2) = 1 by norm_num, one_pow, one_smul]
      simp only [delta_px_last n F, neg_neg]
  | Sum.inr (Sum.inr (Sum.inr u)) =>
      cases u
      simp only [Work.Serre.pinv, pval]
      rw [delta_px_zero n F]
      norm_num

end

end Work.Stems.PerSimplex

namespace Work.Stems.PerSimplex

noncomputable section

variable {X : Type} [TopologicalSpace X]

theorem pinv_ne_self (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X))
    (z : Work.Serre.PIdx n) : Work.Serre.pinv z ≠ z := by
  intro h
  have hpinv : pval n F (Work.Serre.pinv z) = pval n F z := by rw [h]
  rw [pval_pinv n F z] at hpinv
  have h1 : pval n F z + pval n F z = 0 := neg_eq_iff_add_eq_zero.mp hpinv
  have h2 : (2:ℤ) • pval n F z = 0 := by rw [two_smul ℤ (pval n F z)]; exact h1
  exact pval_ne_zero n F z ((smul_eq_zero.mp h2).resolve_left (by norm_num))

/-- The combinatorial content of the prism identity, in the free module on the singular
`(n+1)`-simplices. -/
theorem prismSumIdentityF (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X)) :
    (∑ x : Fin (n+2), ∑ y : Fin (n+3),
        ((-1:ℤ)^((x:ℕ)+1+(y:ℕ))) • Finsupp.single ((Work.Serre.singX X).δ y (px n F x)) (1:ℤ))
      + (∑ x : Fin (n+2), ∑ y : Fin (n+1),
          ((-1:ℤ)^((x:ℕ)+((y:ℕ)+1))) • Finsupp.single (qf n F x y) (1:ℤ))
      = Finsupp.single (pbot n F) (1:ℤ) - Finsupp.single (ptop n F) (1:ℤ) := by
  have hsum : ∑ z : Work.Serre.PIdx n, pval n F z = 0 := by
    have h := Finset.sum_ninvolution (s := (Finset.univ : Finset (Work.Serre.PIdx n)))
      (f := pval n F) (Work.Serre.pinv (m := n))
      (fun a => by rw [pval_pinv n F a]; abel) (fun a _ => pinv_ne_self n F a)
      (fun a => Finset.mem_univ (Work.Serre.pinv a)) (fun a => Work.Serre.pinv_pinv a)
    simpa using h
  have hsplit : ∑ z : Work.Serre.PIdx n, pval n F z
      = (∑ x : Fin (n+2), ∑ y : Fin (n+3),
            ((-1:ℤ)^((x:ℕ)+1+(y:ℕ))) •
              Finsupp.single ((Work.Serre.singX X).δ y (px n F x)) (1:ℤ))
        + ((∑ x : Fin (n+2), ∑ y : Fin (n+1),
              ((-1:ℤ)^((x:ℕ)+((y:ℕ)+1))) • Finsupp.single (qf n F x y) (1:ℤ))
          + (- Finsupp.single (pbot n F) (1:ℤ) + Finsupp.single (ptop n F) (1:ℤ))) := by
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, pval, Finset.univ_unique,
      Finset.sum_singleton]
  rw [hsplit] at hsum
  have hsum' : ((∑ x : Fin (n+2), ∑ y : Fin (n+3),
            ((-1:ℤ)^((x:ℕ)+1+(y:ℕ))) •
              Finsupp.single ((Work.Serre.singX X).δ y (px n F x)) (1:ℤ))
        + (∑ x : Fin (n+2), ∑ y : Fin (n+1),
              ((-1:ℤ)^((x:ℕ)+((y:ℕ)+1))) • Finsupp.single (qf n F x y) (1:ℤ)))
        + (- Finsupp.single (pbot n F) (1:ℤ) + Finsupp.single (ptop n F) (1:ℤ)) = 0 := by
    rw [← hsum]; abel
  have h2 := add_eq_zero_iff_eq_neg.mp hsum'
  rw [neg_add_rev, neg_neg] at h2
  rw [sub_eq_add_neg]
  exact h2.trans (add_comm _ _)

end

end Work.Stems.PerSimplex

namespace Work.Stems.PerSimplex

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- **The boundary of the prism chain.**  For a homotopy `F : Δ^{n+1} × I → X` of an
`(n+1)`-simplex, the boundary of the prism chain of `F` is the difference of the top and bottom
chains minus the alternating sum of the prism chains of the face homotopies. -/
theorem prismChainBoundary (n : ℕ) (F : C(↥(stdSimplex ℝ (Fin (n+2))) × unitInterval, X)) :
    (ModuleCat.Hom.hom ((Work.Stems.hChain X).d (n+2) (n+1)))
        (prismChain (X := X) (n+1) F)
      = Work.Stems.simplexChain (X:=X) (n+1)
          (Work.RatHurewicz.Bridge.simplexOf (n+1) (F.comp (Work.Serre.botIncl (n+1))))
        - Work.Stems.simplexChain (X:=X) (n+1)
            (Work.RatHurewicz.Bridge.simplexOf (n+1) (F.comp (Work.Serre.topIncl (n+1))))
        - ∑ i : Fin (n+2), (-1:ℤ)^(i:ℕ) •
            prismChain (X := X) n
              (F.comp ((Work.RatHurewicz.Bridge.coface n i).prodMap
                (ContinuousMap.id unitInterval))) := by
  have hs : (ModuleCat.Hom.hom ((Work.Stems.hChain X).d (n+2) (n+1)))
        (prismChain (X := X) (n+1) F)
      = ∑ x : Fin (n+2), (-1:ℤ)^((x:ℕ)+1) •
          ∑ f : Fin (n+3), (-1:ℤ)^((f:ℕ)) •
            Work.Stems.simplexChain (X:=X) (n+1) ((Work.Serre.singX X).δ f (px n F x)) := by
    simp only [prismChain_def, px, map_sum, map_zsmul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    congr 1
    rw [Work.RatHurewicz.Bridge.d_ιChainComplex_one]
  have ht : (∑ i : Fin (n+2), (-1:ℤ)^(i:ℕ) •
        prismChain (X := X) n
          (F.comp ((Work.RatHurewicz.Bridge.coface n i).prodMap
            (ContinuousMap.id unitInterval))))
      = ∑ i : Fin (n+2), (-1:ℤ)^(i:ℕ) •
          ∑ y : Fin (n+1), (-1:ℤ)^((y:ℕ)+1) •
            Work.Stems.simplexChain (X:=X) (n+1) (qf n F i y) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [prismChain_def, qf]
  have key : (∑ x : Fin (n+2), ∑ f : Fin (n+3),
        ((-1:ℤ)^((x:ℕ)+1+(f:ℕ))) •
          Finsupp.single ((Work.Serre.singX X).δ f (px n F x)) (1:ℤ))
      = Finsupp.single
            (Work.RatHurewicz.Bridge.simplexOf (n+1) (F.comp (Work.Serre.botIncl (n+1)))) (1:ℤ)
        - Finsupp.single
            (Work.RatHurewicz.Bridge.simplexOf (n+1) (F.comp (Work.Serre.topIncl (n+1)))) (1:ℤ)
        - ∑ x : Fin (n+2), ∑ y : Fin (n+1),
            ((-1:ℤ)^((x:ℕ)+((y:ℕ)+1))) • Finsupp.single (qf n F x y) (1:ℤ) := by
    have h := prismSumIdentityF n F
    simp only [pbot, ptop, sub_eq_add_neg] at h ⊢
    rw [← h]
    abel
  rw [hs, ht]
  apply Work.Cohomology.Crux33.eq_of_coords_eq
  simp only [map_sub, map_sum, map_zsmul, Work.Stems.coords_simplexChain]
  simp_rw [Finset.smul_sum, smul_smul, ← pow_add]
  exact key

end

end Work.Stems.PerSimplex

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open CategoryTheory AlgebraicTopology Simplicial
open scoped Topology unitInterval Simplicial BigOperators

namespace Work.Stems.PerSimplex

open Work.RatHurewicz.Bridge (coface coface_apply)

noncomputable section

/-- The hat-extension lemma, with no compression hypothesis: every continuous map on the hat
`sHat n = (Δⁿ × {0}) ∪ (∂Δⁿ × I)` extends to `Δⁿ × I`.  (It is `Work.Serre.sHatExtend` with
`A = Set.univ`, where the compression hypothesis is satisfied by the constant homotopy.) -/
theorem sHatExtendUncond {X : Type} [TopologicalSpace X] (n : ℕ) (hn : 1 ≤ n)
    (f : C(↥(Work.Serre.sHat n), X)) :
    ∃ F : C(↥(stdSimplex ℝ (Fin (n+1))) × unitInterval, X),
      ∀ q : ↥(Work.Serre.sHat n), F q = f q := by
  have hc : Work.RatHurewicz.CompressRel X Set.univ n := by
    intro g hg
    refine ⟨g.comp ⟨fun p => p.1, continuous_fst⟩, ?_, ?_, ?_⟩
    · intro x; rfl
    · intro x hx t; rfl
    · intro x; trivial
  obtain ⟨F, hF, -⟩ :=
    Work.Serre.sHatExtend (X := X) (A := Set.univ) hn hc f (fun q hq => trivial)
  exact ⟨F, hF⟩

variable {X : Type} [TopologicalSpace X]

/-- The alternating sign satisfies `epsZ (n+1) = 1 - epsZ n`. -/
theorem epsZ_succ (n : ℕ) : Work.Stems.epsZ (n+1) = 1 - Work.Stems.epsZ n := by
  rw [Work.Stems.epsZ, Fin.sum_univ_succ]
  have h : ∀ i : Fin (n+1), (-1:ℤ)^(((i.succ : Fin (n+1+1)) : ℕ)) = -((-1:ℤ)^((i:ℕ))) := by
    intro i
    rw [show ((i.succ : Fin (n+1+1)) : ℕ) = (i:ℕ) + 1 from rfl, pow_succ]
    ring
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_neg_distrib]
  rw [Work.Stems.epsZ]
  simp only [Fin.val_zero, pow_zero]
  abel

/-- **The pinched simplex.** -/
theorem pinchedSimplex (j : ℕ) {X : Type} [TopologicalSpace X] (x₀ : X)
    (H : Work.Serre.SimpHom X {x₀} (j + 1)) (a : Work.Stems.hSimplex X (j + 2)) :
    ∃ sg : C(↥(stdSimplex ℝ (Fin (j + 3))), X),
      (∀ z : ↥(stdSimplex ℝ (Fin (j + 3))), (∃ i : Fin (j + 3), z i = 0) → sg z = x₀) ∧
      ∃ w : (Work.Stems.hChain X).X (j + 3),
        (ModuleCat.Hom.hom ((Work.Stems.hChain X).d (j + 3) (j + 2))) w
          = Work.Stems.Zeta j x₀ H (Work.Stems.simplexChain (X := X) (j + 2) a)
            - (Work.Stems.simplexChain (X := X) (j + 2)
                  (Work.RatHurewicz.Bridge.simplexOf (j + 2) sg)
                - Work.Stems.simplexChain (X := X) (j + 2)
                    (Work.Stems.constSimplex (X := X) (j + 2) x₀)) := by
  classical
  -- the continuous map underlying the simplex `a`
  set ac : C(↥(stdSimplex ℝ (Fin (j+3))), X) :=
    ((TopCat.of X).toSSetObjEquivT (Opposite.op (SimplexCategory.mk (j+2)))) a with hac
  have hac_simplex : Work.RatHurewicz.Bridge.simplexOf (j+2) ac = a := by
    rw [hac]
    exact Equiv.symm_apply_apply _ _
  -- the face homotopies, glued into the hat data
  set Gv : (i : Fin (j+3)) → C(↥(stdSimplex ℝ (Fin (j+2))) × unitInterval, X) :=
    fun i => H.G (j+1) (ac.comp (coface (j+1) i)) with hGv
  have hcomp : ∀ (i i' : Fin (j+3)) (hii' : i < i'),
      (Gv i').comp ((coface j ⟨(i:ℕ), by have := i.isLt; omega⟩).prodMap
          (ContinuousMap.id unitInterval))
        = (Gv i).comp ((coface j ⟨(i':ℕ)-1, by have := i'.isLt; omega⟩).prodMap
            (ContinuousMap.id unitInterval)) := by
    intro i i' hii'
    ext p
    obtain ⟨x, t⟩ := p
    show H.G (j+1) (ac.comp (coface (j+1) i'))
        ((coface j ⟨(i:ℕ), by have := i.isLt; omega⟩) x, t)
      = H.G (j+1) (ac.comp (coface (j+1) i))
        ((coface j ⟨(i':ℕ)-1, by have := i'.isLt; omega⟩) x, t)
    rw [H.hside j (by omega) (ac.comp (coface (j+1) i'))
        ⟨(i:ℕ), by have := i.isLt; omega⟩ x t,
      H.hside j (by omega) (ac.comp (coface (j+1) i))
        ⟨(i':ℕ)-1, by have := i'.isLt; omega⟩ x t]
    congr 2
    rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc,
      Work.Serre.coface_coface i i' hii']
  have h0 : ∀ (i : Fin (j+3)) (x : ↥(stdSimplex ℝ (Fin (j+2)))),
      Gv i (x, 0) = ac ((coface (j+1) i) x) := by
    intro i x
    show H.G (j+1) (ac.comp (coface (j+1) i)) (x, 0) = ac ((coface (j+1) i) x)
    rw [H.ht0 (j+1) le_rfl]
    rfl
  obtain ⟨f, hf0, hfside⟩ := Work.Serre.exists_sHatData (k := j) Gv ac hcomp h0
  obtain ⟨F, hF⟩ := sHatExtendUncond (X := X) (j+2) (by omega) f
  refine ⟨F.comp (Work.Serre.topIncl (j+2)), ?_, ?_⟩
  · -- the boundary-constancy of the pinched simplex
    intro z hz
    obtain ⟨i, hi⟩ := hz
    have hmem : ((z, (1 : unitInterval)) : ↥(stdSimplex ℝ (Fin (j+3))) × unitInterval)
        ∈ Work.Serre.sHat (j+2) := Or.inr ⟨i, hi⟩
    show F (z, 1) = x₀
    rw [hF ⟨(z, 1), hmem⟩]
    rw [hfside i ⟨(z, 1), hmem⟩ hi]
    exact H.htop (j+1) le_rfl (ac.comp (coface (j+1) i)) _
  · -- the chain-level relation
    -- the value of `F` on the bottom face is `ac`
    have hbotF : F.comp (Work.Serre.botIncl (j+2)) = ac := by
      ext z
      have hmem : ((z, (0 : unitInterval)) : ↥(stdSimplex ℝ (Fin (j+3))) × unitInterval)
          ∈ Work.Serre.sHat (j+2) := Or.inl rfl
      show F (z, 0) = ac z
      rw [hF ⟨(z, 0), hmem⟩, hf0 ⟨(z, 0), hmem⟩ rfl]
      rfl
    -- the value of `F` on the lateral faces is the corresponding face homotopy
    have hfaceCM : ∀ i : Fin (j+3),
        F.comp ((coface (j+1) i).prodMap (ContinuousMap.id unitInterval))
          = H.G (j+1) (ac.comp (coface (j+1) i)) := by
      intro i
      ext p
      obtain ⟨x, t⟩ := p
      have hmem : ((((coface (j+1) i) x), t) :
          ↥(stdSimplex ℝ (Fin (j+3))) × unitInterval) ∈ Work.Serre.sHat (j+2) :=
        Or.inr (Work.Serre.coface_mem_simplexBdry i x)
      show F ((coface (j+1) i) x, t) = H.G (j+1) (ac.comp (coface (j+1) i)) (x, t)
      rw [hF ⟨((coface (j+1) i) x, t), hmem⟩,
        hfside i ⟨((coface (j+1) i) x, t), hmem⟩
          (Work.RatHurewicz.Bridge.coface_apply_self (j+1) i x)]
      simp only [hGv]
      refine congrArg (fun w => H.G (j+1) (ac.comp (coface (j+1) i)) (w, t)) ?_
      exact Subtype.ext (Work.Serre.uncoface_coface (j+1) i x)
    -- the face prism chains are the prism values of the face simplices
    have hface : ∀ i : Fin (j+3),
        prismChain (X := X) (j+1) (F.comp ((coface (j+1) i).prodMap
            (ContinuousMap.id unitInterval)))
          = Work.Serre.prismVal H (j+1) ((Work.Serre.singX X).δ i a) := by
      intro i
      have hd : (TopCat.of X).toSSetObjEquivT (Opposite.op (SimplexCategory.mk (j+1)))
            ((Work.Serre.singX X).δ i a)
          = ac.comp (coface (j+1) i) := by
        rw [Work.Serre.toSSetObjEquiv_δ, ← hac]
      rw [hfaceCM i, prismChain_def, Work.Serre.prismVal]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      congr 2
      all_goals first
        | rfl
        | (rw [Work.Serre.hSimplex, hd]; rfl)
        | (simp only [Work.Serre.hSimplex, hd]; rfl)
    -- the sum of the face prism chains is the prism homotopy applied to the boundary of `a`
    have hT : (ModuleCat.Hom.hom (Work.Serre.prismHom H (j+1)))
          (ModuleCat.Hom.hom ((Work.Stems.hChain X).d (j+2) (j+1))
            (Work.Stems.simplexChain (X:=X) (j+2) a))
        = ∑ i : Fin (j+3), (-1:ℤ)^(i:ℕ) •
            Work.Serre.prismVal H (j+1) ((Work.Serre.singX X).δ i a) := by
      rw [Work.RatHurewicz.Bridge.d_ιChainComplex_one, map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_zsmul, Work.Serre.prismHom_gen]
    have hface_sum : (∑ i : Fin (j+3), (-1:ℤ)^(i:ℕ) •
          prismChain (X := X) (j+1) (F.comp ((coface (j+1) i).prodMap
            (ContinuousMap.id unitInterval))))
        = (ModuleCat.Hom.hom (Work.Serre.prismHom H (j+1)))
            (ModuleCat.Hom.hom ((Work.Stems.hChain X).d (j+2) (j+1))
              (Work.Stems.simplexChain (X:=X) (j+2) a)) := by
      rw [hT]
      exact Finset.sum_congr rfl (fun i _ => by rw [hface i])
    -- the power of `-1` relation
    have heps : Work.Stems.epsZ (j+3) = 1 - Work.Stems.epsZ (j+2) :=
      epsZ_succ (j+2)
    refine ⟨prismChain (X := X) (j+2) F
      + Work.Stems.simplexChain (X := X) (j+3) (Work.Stems.constSimplex (X := X) (j+3) x₀), ?_⟩
    have hbot : Work.Stems.simplexChain (X:=X) (j+2)
          (Work.RatHurewicz.Bridge.simplexOf (j+2) (F.comp (Work.Serre.botIncl (j+2))))
        = Work.Stems.simplexChain (X:=X) (j+2) a := by
      congr 1
      rw [hbotF]
      exact hac_simplex
    rw [map_add, prismChainBoundary (X := X) (j+1) F, hbot,
      Work.Stems.d_constSimplexChain (j+2) x₀, hface_sum,
      Work.Stems.Zeta_apply, Work.Stems.aug_simplexChain, one_mul, heps]
    simp only [sub_eq_add_neg, add_zsmul, one_zsmul, neg_zsmul,
      show j + 1 + 1 = j + 2 from rfl]
    abel

end

end Work.Stems.PerSimplex

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-!
# Radial coordinates on the standard simplex

For the standard `n`-simplex `Δⁿ ⊆ ℝⁿ⁺¹` we set up the "homothetic" decomposition from the
barycentre `z₀ = (1/(n+1), …, 1/(n+1))`: every point `z` is `z₀ + r(z)·(d(z) - z₀)` with
`r(z) = 1 - (n+1)·min z ∈ [0,1]` and `d(z) ∈ ∂Δⁿ` the point where the ray from `z₀` through `z`
meets the boundary.  The homothety `hom z t = z₀ + ((1+t)/2)·(z - z₀)` has the radial data used in
the construction of the "pinched" sphere map.
-/

open scoped BigOperators
open Work.RatHurewicz.Bridge (coface coface_apply)

namespace Work.Stems.PerSimplex

noncomputable section

/-- The standard `n`-simplex, as the type of its points. -/
abbrev Simp (n : ℕ) := ↥(stdSimplex ℝ (Fin (n + 1)))

variable {n : ℕ}

/-- The barycentric value `1/(n+1)`. -/
def bv (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem bv_pos (n : ℕ) : 0 < bv n := by rw [bv]; positivity

theorem card_bv (n : ℕ) : ((n : ℝ) + 1) * bv n = 1 := by rw [bv]; field_simp

/-- The barycentre of `Δⁿ`. -/
def bary (n : ℕ) : Simp n :=
  ⟨fun _ => bv n, fun _ => le_of_lt (bv_pos n), by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show ((n + 1 : ℕ) : ℝ) = (n:ℝ)+1 from by simp]
    exact card_bv n⟩

@[simp] theorem bary_apply (n : ℕ) (i : Fin (n + 1)) : ((bary n : Fin (n+1) → ℝ) i) = bv n := rfl

/-- The minimum of the coordinates of a point of the simplex. -/
def mn (z : Simp n) : ℝ := Finset.univ.inf' ⟨⟨0, Nat.succ_pos n⟩, Finset.mem_univ _⟩ z

theorem mn_le (z : Simp n) (i : Fin (n + 1)) : mn z ≤ (z : Fin (n+1) → ℝ) i :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem le_mn (z : Simp n) {a : ℝ} (h : ∀ i : Fin (n + 1), a ≤ (z : Fin (n+1) → ℝ) i) : a ≤ mn z :=
  Finset.le_inf' _ _ fun i _ => h i

theorem mn_nonneg (z : Simp n) : 0 ≤ mn z := le_mn z fun i => z.2.1 i

theorem exists_mn_eq (z : Simp n) : ∃ i : Fin (n + 1), mn z = (z : Fin (n+1) → ℝ) i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf'
    (⟨⟨0, Nat.succ_pos n⟩, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin (n+1))).Nonempty) z
  exact ⟨i, hi⟩

theorem sum_coe (z : Simp n) : ∑ i, (z : Fin (n+1) → ℝ) i = 1 := z.2.2

theorem mn_le_bv (z : Simp n) : mn z ≤ bv n := by
  have h1 : ∑ i, mn z ≤ ∑ i, (z : Fin (n+1) → ℝ) i := Finset.sum_le_sum fun i _ => mn_le z i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sum_coe z] at h1
  rw [show ((n + 1 : ℕ) : ℝ) = (n:ℝ)+1 from by simp] at h1
  have h2 : ((n:ℝ)+1) * mn z ≤ ((n:ℝ)+1) * bv n := by rw [card_bv n]; linarith
  exact (mul_le_mul_iff_of_pos_left (by positivity : (0:ℝ) < (n:ℝ)+1)).mp h2

theorem mn_bary (n : ℕ) : mn (bary n) = bv n := by
  refine le_antisymm ?_ ?_
  · exact Finset.inf'_le _ (Finset.mem_univ (⟨0, Nat.succ_pos n⟩ : Fin (n+1)))
  · exact Finset.le_inf' _ _ fun i _ => le_refl _

theorem eq_bary_of_mn (z : Simp n) (h : mn z = bv n) : z = bary n := by
  refine Subtype.ext (funext fun i => ?_)
  have h1 : mn z ≤ (z : Fin (n+1) → ℝ) i := mn_le z i
  have h3 : ∑ j ∈ Finset.univ.erase i, (z : Fin (n+1) → ℝ) j ≥ ∑ _j ∈ Finset.univ.erase i, mn z :=
    Finset.sum_le_sum fun j _ => mn_le z j
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at h3
  rw [show ((n + 1 - 1 : ℕ) : ℝ) = (n:ℝ) from by simp] at h3
  have h5 : (z : Fin (n+1) → ℝ) i + ∑ j ∈ Finset.univ.erase i, (z : Fin (n+1) → ℝ) j = 1 := by
    rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    exact sum_coe z
  rw [h, bv] at h3
  have hpos : (0:ℝ) < (n:ℝ)+1 := by positivity
  have h2 : (z : Fin (n+1) → ℝ) i ≤ bv n := by
    rw [bv]
    nlinarith [h3, h5, mul_inv_cancel₀ (ne_of_gt hpos)]
  rw [h] at h1
  exact le_antisymm h2 h1

/-- The radial coordinate of a point of the simplex. -/
def rad (z : Simp n) : ℝ := 1 - ((n : ℝ) + 1) * mn z

theorem rad_nonneg (z : Simp n) : 0 ≤ rad z := by
  have h1 : mn z ≤ bv n := mn_le_bv z
  have h3 : ((n:ℝ)+1) * mn z ≤ 1 := by
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ (n:ℝ)+1)
    rwa [card_bv] at this
  rw [rad]; linarith

theorem rad_le_one (z : Simp n) : rad z ≤ 1 := by
  have h := mn_nonneg z
  rw [rad]; nlinarith

theorem rad_eq_zero_iff (z : Simp n) : rad z = 0 ↔ z = bary n := by
  rw [rad]
  constructor
  · intro h
    refine eq_bary_of_mn z ?_
    have h' : ((n:ℝ)+1) * mn z = ((n:ℝ)+1) * bv n := by rw [card_bv]; linarith
    exact mul_left_cancel₀ (by positivity : ((n:ℝ)+1) ≠ 0) h'
  · intro h
    rw [h, mn_bary, card_bv, sub_self]

theorem rad_bary (n : ℕ) : rad (bary n) = 0 := (rad_eq_zero_iff _).mpr rfl

/-- The direction of a point of the simplex: where the ray from the barycentre meets the boundary. -/
def dirv (z : Simp n) : Fin (n + 1) → ℝ :=
  fun i => bv n + ((z : Fin (n+1) → ℝ) i - bv n) / rad z

theorem dirv_nonneg (z : Simp n) (hz : 0 < rad z) (i : Fin (n+1)) : 0 ≤ dirv z i := by
  have h := mn_le z i
  have h4 : -bv n * rad z = mn z - bv n := by
    rw [rad]
    have hb : bv n * ((n:ℝ)+1) = 1 := by rw [mul_comm]; exact card_bv n
    calc -bv n * (1 - ((n:ℝ)+1) * mn z)
        = -bv n + bv n * ((n:ℝ)+1) * mn z := by ring
      _ = -bv n + 1 * mn z := by rw [hb]
      _ = mn z - bv n := by ring
  rw [dirv]
  have key : -bv n ≤ ((z : Fin (n+1) → ℝ) i - bv n) / rad z := by
    rw [le_div_iff₀ hz]
    nlinarith [h4, h]
  linarith

theorem dirv_sum (z : Simp n) : ∑ i, dirv z i = 1 := by
  simp only [dirv, Finset.sum_add_distrib]
  have h1 : ∑ i, ((z : Fin (n+1) → ℝ) i - bv n) = 1 - ((n:ℝ)+1) * bv n := by
    rw [Finset.sum_sub_distrib, sum_coe z, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [show ((n + 1 : ℕ) : ℝ) = (n:ℝ)+1 from by simp]
  have h2 : ∑ _i : Fin (n+1), bv n = ((n:ℝ)+1) * bv n := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show ((n + 1 : ℕ) : ℝ) = (n:ℝ)+1 from by simp]
  rw [h2, ← Finset.sum_div, h1, card_bv, sub_self, zero_div, add_zero]

theorem dirv_eq_zero (z : Simp n) (hz : 0 < rad z) : ∃ i, dirv z i = 0 := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf'
    (⟨⟨0, Nat.succ_pos n⟩, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin (n+1))).Nonempty) z
  refine ⟨i, ?_⟩
  have hmni : mn z = (z : Fin (n+1) → ℝ) i := hi
  simp only [dirv]
  have h2 : mn z = bv n - rad z / ((n:ℝ)+1) := by
    rw [rad, bv]; field_simp; ring
  rw [← hmni, h2, bv]
  field_simp
  ring

theorem dirv_eq_of_rad_eq_one (z : Simp n) (h : rad z = 1) : dirv z = (z : Fin (n+1) → ℝ) := by
  funext i
  simp only [dirv]
  rw [h, div_one]
  ring

/-- The radial direction, as a point of the simplex. -/
def dir (z : Simp n) : Simp n :=
  ⟨dirv z, fun i => by
    rcases eq_or_lt_of_le (rad_nonneg z) with h0 | h0
    · have hz : z = bary n := (rad_eq_zero_iff z).mp h0.symm
      subst hz
      simp only [dirv]
      rw [rad_bary, div_zero, add_zero]
      exact le_of_lt (bv_pos n)
    · exact dirv_nonneg z h0 i, dirv_sum z⟩

@[simp] theorem dir_coe (z : Simp n) : ((dir z : Fin (n+1) → ℝ)) = dirv z := rfl

/-- The homothety `hom z t = z₀ + ((1+t)/2)·(z - z₀)`, written as a convex combination. -/
def homv (z : Simp n) (t : ℝ) : Fin (n + 1) → ℝ :=
  fun i => bv n * (1 - (1 + t) / 2) + ((1 + t) / 2) * (z : Fin (n+1) → ℝ) i

theorem homv_eq (z : Simp n) (t : ℝ) (i : Fin (n+1)) :
    homv z t i = bv n + ((1 + t) / 2) * ((z : Fin (n+1) → ℝ) i - bv n) := by
  simp only [homv]; ring

theorem homv_nonneg (z : Simp n) {t : ℝ} (h1t : -1 ≤ t) (h2t : t ≤ 1) (i : Fin (n+1)) :
    0 ≤ homv z t i := by
  simp only [homv]
  have h1 : 0 ≤ (1 + t) / 2 := by linarith
  have h2 : (1 + t) / 2 ≤ 1 := by linarith
  have hb := le_of_lt (bv_pos n)
  have hz := z.2.1 i
  have h3 : 0 ≤ bv n * (1 - (1 + t) / 2) := mul_nonneg hb (by linarith)
  have h4 : 0 ≤ ((1 + t) / 2) * (z : Fin (n+1) → ℝ) i := mul_nonneg h1 hz
  linarith

theorem homv_sum (z : Simp n) (t : ℝ) : ∑ i, homv z t i = 1 := by
  simp only [homv, Finset.sum_add_distrib]
  have h2 : ∑ _i : Fin (n+1), bv n * (1 - (1 + t) / 2)
      = ((n:ℝ)+1) * (bv n * (1 - (1 + t) / 2)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show ((n + 1 : ℕ) : ℝ) = (n:ℝ)+1 from by simp]
  have h3 : ∑ i, ((1 + t) / 2) * (z : Fin (n+1) → ℝ) i = (1 + t) / 2 := by
    rw [← Finset.mul_sum, sum_coe z, mul_one]
  rw [h2, h3, ← mul_assoc, card_bv]
  ring

/-- The homothety, as a point of the simplex (for `t ≥ -1`). -/
def hom (z : Simp n) (t : ℝ) (h1t : -1 ≤ t) (h2t : t ≤ 1) : Simp n :=
  ⟨homv z t, fun i => homv_nonneg z h1t h2t i, homv_sum z t⟩

@[simp] theorem hom_coe (z : Simp n) (t : ℝ) (h1t : -1 ≤ t) (h2t : t ≤ 1) :
    ((hom z t h1t h2t : Fin (n+1) → ℝ)) = homv z t := rfl

/-- The half-sized copy of the simplex (the "inner" region). -/
def half (z : Simp n) : Simp n := hom z 0 (by norm_num) (by norm_num)

theorem half_eq_hom (z : Simp n) : half z = hom z 0 (by norm_num) (by norm_num) := rfl

/-! ## The radial data of the homothety -/

theorem mn_homv (z : Simp n) {t : ℝ} (h1t : -1 ≤ t) (h2t : t ≤ 1) :
    mn (hom z t h1t h2t) = bv n * (1 - (1 + t) / 2) + ((1 + t) / 2) * mn z := by
  have hc : (0:ℝ) ≤ (1 + t) / 2 := by linarith
  refine le_antisymm ?_ ?_
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf'
      (⟨⟨0, Nat.succ_pos n⟩, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin (n+1))).Nonempty) z
    have hmni : mn z = (z : Fin (n+1) → ℝ) i := hi
    calc mn (hom z t h1t h2t) ≤ (hom z t h1t h2t : Fin (n+1) → ℝ) i := mn_le _ i
      _ = bv n * (1 - (1 + t) / 2) + ((1 + t) / 2) * mn z := by
          rw [hom_coe]
          simp only [homv, hmni]
  · refine le_mn _ fun i => ?_
    rw [hom_coe]
    have h1 : ((1 + t) / 2) * mn z ≤ ((1 + t) / 2) * (z : Fin (n+1) → ℝ) i :=
      mul_le_mul_of_nonneg_left (mn_le z i) hc
    simp only [homv]
    nlinarith [h1]

theorem rad_hom (z : Simp n) {t : ℝ} (h1t : -1 ≤ t) (h2t : t ≤ 1) :
    rad (hom z t h1t h2t) = (1 + t) / 2 * rad z := by
  rw [rad, mn_homv z h1t h2t, rad]
  have hb : ((n:ℝ)+1) * bv n = 1 := card_bv n
  rw [show ((n:ℝ)+1) * (bv n * (1 - (1 + t) / 2) + (1 + t) / 2 * mn z)
      = ((n:ℝ)+1) * bv n * (1 - (1 + t) / 2) + ((n:ℝ)+1) * ((1 + t) / 2) * mn z from by ring]
  rw [hb]
  ring

theorem rad_half (z : Simp n) : rad (half z) = rad z / 2 := by
  rw [half, rad_hom]
  ring

theorem hom_one (z : Simp n) : hom z 1 (by norm_num) (by norm_num) = z := by
  refine Subtype.ext (funext fun i => ?_)
  show homv z 1 i = (z : Fin (n+1) → ℝ) i
  simp only [homv]
  norm_num

theorem rad_hom_one (z : Simp n) : rad (hom z 1 (by norm_num) (by norm_num)) = rad z := by
  rw [hom_one z]

theorem dirv_hom (z : Simp n) {t : ℝ} (h1t : -1 ≤ t) (h2t : t ≤ 1)
    (hc : (0:ℝ) < (1 + t) / 2) (hz : rad z ≠ 0) :
    dirv (hom z t h1t h2t) = dirv z := by
  have hrad : rad (hom z t h1t h2t) = (1 + t) / 2 * rad z := rad_hom z h1t h2t
  funext i
  show bv n + (((hom z t h1t h2t : Fin (n+1) → ℝ)) i - bv n) / rad (hom z t h1t h2t)
      = bv n + ((z : Fin (n+1) → ℝ) i - bv n) / rad z
  rw [hrad, hom_coe]
  simp only [homv]
  rw [show bv n * (1 - (1 + t) / 2) + (1 + t) / 2 * (z : Fin (n+1) → ℝ) i - bv n
      = (1 + t) / 2 * ((z : Fin (n+1) → ℝ) i - bv n) from by ring,
    mul_div_mul_left _ _ (ne_of_gt hc)]

theorem dirv_hom_one (z : Simp n) (hz : rad z ≠ 0) :
    dirv (hom z 1 (by norm_num) (by norm_num)) = dirv z :=
  dirv_hom z (by norm_num) (by norm_num) (by norm_num) hz

/-- A point with a vanishing coordinate has radial coordinate `1`. -/
theorem rad_eq_one_of_coord_zero (u : Simp n) (i : Fin (n+1))
    (hi : (u : Fin (n+1) → ℝ) i = 0) : rad u = 1 := by
  rw [rad]
  have h := mn_le u i
  rw [hi] at h
  have h2 := mn_nonneg u
  have : mn u = 0 := le_antisymm h h2
  rw [this]; ring

end

end Work.Stems.PerSimplex

namespace Work.Stems.PerSimplex

/-- Two cycles of a chain complex of `ℤ`-modules whose difference is a boundary represent the
same homology class in `Hₙ`. -/
theorem homologypi_eq_of_boundary {n : ℕ} (hn : 1 ≤ n) (K : ChainComplex (ModuleCat ℤ) ℕ)
    [∀ i, K.HasHomology i] (x y : K.X n) (w : K.X (n + 1))
    (hx : (ModuleCat.Hom.hom (K.d n (n - 1))) x = 0)
    (hy : (ModuleCat.Hom.hom (K.d n (n - 1))) y = 0)
    (h : x - y = (ModuleCat.Hom.hom (K.d (n + 1) n)) w) :
    K.homologyπ n (Work.RatHurewicz.Bridge.cycleOf K n hn x hx)
      = K.homologyπ n (Work.RatHurewicz.Bridge.cycleOf K n hn y hy) := by
  -- `iCycles n` is injective, so it suffices to compare the underlying chains.
  have hinj : Function.Injective (ModuleCat.Hom.hom (K.iCycles n)) :=
    (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
  -- the underlying chain of the difference of the two cycles is `x - y`
  have h2 : (ModuleCat.Hom.hom (K.iCycles n))
      (Work.RatHurewicz.Bridge.cycleOf K n hn x hx - Work.RatHurewicz.Bridge.cycleOf K n hn y hy)
      = x - y := by
    rw [map_sub, Work.RatHurewicz.Bridge.iCycles_cycleOf, Work.RatHurewicz.Bridge.iCycles_cycleOf]
  -- ... and `x - y` is the underlying chain of the cycle `toCycles (n+1) n w`
  have h1 : (ModuleCat.Hom.hom (K.iCycles n)) (K.toCycles (n + 1) n w) = x - y := by
    have hh := HomologicalComplex.toCycles_i K (n + 1) n
    have hh2 := congrArg (fun (g : K.X (n + 1) ⟶ K.X n) => (ModuleCat.Hom.hom g) w) hh
    rw [ModuleCat.hom_comp] at hh2
    simp only [LinearMap.comp_apply] at hh2
    rw [hh2]
    exact h.symm
  -- hence the difference of the two cycles is the image of `w` under `toCycles (n+1) n`
  have hkey : K.toCycles (n + 1) n w = Work.RatHurewicz.Bridge.cycleOf K n hn x hx
      - Work.RatHurewicz.Bridge.cycleOf K n hn y hy := by
    apply hinj
    rw [h1, h2]
  -- whose homology class is zero because `toCycles` is killed by `homologyπ`
  have hzero : (ModuleCat.Hom.hom (K.homologyπ n)) (K.toCycles (n + 1) n w) = 0 := by
    have hh := HomologicalComplex.toCycles_comp_homologyπ K (n + 1) n
    have hh2 := congrArg (fun (g : K.X (n + 1) ⟶ K.homology n) => (ModuleCat.Hom.hom g) w) hh
    rw [ModuleCat.hom_comp] at hh2
    simp only [LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at hh2
    exact hh2
  -- finally, `homologyπ` is additive
  have hfd : (ModuleCat.Hom.hom (K.homologyπ n))
      (Work.RatHurewicz.Bridge.cycleOf K n hn x hx) - (ModuleCat.Hom.hom (K.homologyπ n))
      (Work.RatHurewicz.Bridge.cycleOf K n hn y hy) = 0 := by
    rw [← map_sub, ← hkey]
    exact hzero
  exact sub_eq_zero.mp hfd

end Work.Stems.PerSimplex

namespace Work.Stems.PerSimplex

open scoped Topology

/-- **The cumulative-coordinate map `H : Iⁿ → Δⁿ` sends the cube boundary into the simplicial
boundary**: if some coordinate of `t` equals `0` or `1`, then some barycentric coordinate of
`H n t` vanishes.

If `t i = 0` then all the partial products `Pnat n t k`, `k > i`, vanish, so the coordinate
`i+1` of `H n t` is `0`; if `t i = 1` then the factor `1 - t i` in the `i`-th coordinate of
`H n t` vanishes. -/
theorem H_mem_simplexBoundary (n : ℕ) (t : Work.Stems.Cubical.IC n)
    (ht : t ∈ Cube.boundary (Fin n)) :
    ∃ j : Fin (n + 1), (Work.RatHurewicz.H n t) j = 0 := by
  obtain ⟨i, hi | hi⟩ := ht
  · refine ⟨⟨i.1 + 1, Nat.lt_succ_of_le (by omega)⟩, ?_⟩
    rw [Work.RatHurewicz.H_apply, Work.RatHurewicz.Hfun]
    have hP : Work.RatHurewicz.Pnat n t (i.1 + 1) = 0 := by
      rw [Work.RatHurewicz.Pnat]
      refine Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.lt_succ_self _)) ?_
      rw [Work.RatHurewicz.tval_of_lt t i.2]
      exact congrArg (fun x : unitInterval => (x : ℝ)) hi
    rw [hP, zero_mul]
  · refine ⟨⟨i.1, Nat.lt_succ_of_le (le_of_lt i.2)⟩, ?_⟩
    rw [Work.RatHurewicz.H_apply, Work.RatHurewicz.Hfun, Work.RatHurewicz.tval_of_lt t i.2]
    rw [congrArg (fun x : unitInterval => (x : ℝ)) hi]
    norm_num

/-- **Descent of a boundary-constant simplex along the collapse `Δ^{j+2} → S^{j+2}`.**

Let `sg : Δ^{j+2} → X` be a continuous map which is constant, with value `x₀`, on the simplicial
boundary `∂Δ^{j+2} = {z | ∃ i, z i = 0}`. Then `sg` descends along the collapse
`s : Δ^{j+2} → S^{j+2}` of `Work.RatHurewicz.Bridge.exists_collapse_simplex` (which sends the
boundary to a point `y`) to a continuous map `τ : S^{j+2} → X` with `τ ∘ s = sg` and `τ y = x₀`.

The descent is the quotient-map lift of `sg` along `s`; the only input needed besides the
collapse is that `sg` is constant on the fibres of `s`. A fibre of `s` is either a singleton
(`s` is injective off the simplex boundary) or consists of boundary points: indeed, writing
`z = H t`, `z' = H t'` with `H : I^{j+2} → Δ^{j+2}` the cumulative-coordinate map, the equality
`s z = s z'` means `collapseMap t = collapseMap t'`, so either `t = t'` or both `t, t'` lie on the
cube boundary, in which case `z, z'` lie on the simplex boundary by `H_mem_simplexBoundary`, and
`sg` takes the constant value `x₀` there. -/
theorem descentSimplex (j : ℕ) {X : Type} [TopologicalSpace X] (x₀ : X)
    (sg : C(↥(stdSimplex ℝ (Fin (j + 3))), X))
    (hbnd : ∀ z : ↥(stdSimplex ℝ (Fin (j + 3))), (∃ i : Fin (j + 3), z i = 0) → sg z = x₀) :
    ∃ τ : C(Work.Stems.sphere (j + 2), X),
      ∃ (s : C(↥(stdSimplex ℝ (Fin (j + 3))), Work.Stems.sphere (j + 2)))
        (y : Work.Stems.sphere (j + 2)),
        τ.comp s = sg ∧
          (∀ z : ↥(stdSimplex ℝ (Fin (j + 3))), (∃ i : Fin (j + 3), z i = 0) → s z = y) ∧
          τ y = x₀ := by
  obtain ⟨s, y, hscomp, hsbnd⟩ :=
    Work.RatHurewicz.Bridge.exists_collapse_simplex (j + 2) (by omega)
  -- `s ∘ H = collapseMap` is a quotient map, and `H` is a quotient map, hence `s` is one.
  have hHq : Topology.IsQuotientMap ⇑(Work.RatHurewicz.H (j + 2)) :=
    Work.RatHurewicz.Bridge.H_isQuotientMap (j + 2)
  have hcompq : Topology.IsQuotientMap (⇑s ∘ ⇑(Work.RatHurewicz.H (j + 2))) := by
    rw [← ContinuousMap.coe_comp, hscomp]
    exact Work.Stems.collapseMap_isQuotientMap (j + 2) (by omega)
  have hquot : Topology.IsQuotientMap ⇑s := hHq.of_comp_isQuotientMap hcompq
  -- `s` composed with `H` is the collapse of the cube.
  have hc : ∀ u : Work.Stems.Cubical.IC (j + 2), s (Work.RatHurewicz.H (j + 2) u)
      = Work.Stems.collapseMap (j + 2) (by omega) u :=
    fun u => congrFun (congrArg DFunLike.coe hscomp) u
  have hfac : Function.FactorsThrough ⇑sg ⇑s := by
    intro a b hab
    obtain ⟨t, rfl⟩ := Work.RatHurewicz.Bridge.H_surjective (j + 2) a
    obtain ⟨t', rfl⟩ := Work.RatHurewicz.Bridge.H_surjective (j + 2) b
    have hcm : Work.Stems.collapseMap (j + 2) (by omega) t
        = Work.Stems.collapseMap (j + 2) (by omega) t' := by
      rw [← hc t, ← hc t']
      exact hab
    rcases Work.Stems.collapseMap_fiber (j + 2) (by omega) hcm with h | ⟨ht, ht'⟩
    · rw [h]
    · obtain ⟨i, hi⟩ := H_mem_simplexBoundary (j + 2) t ht
      obtain ⟨i', hi'⟩ := H_mem_simplexBoundary (j + 2) t' ht'
      rw [hbnd _ ⟨i, hi⟩, hbnd _ ⟨i', hi'⟩]
  let τ : C(Work.Stems.sphere (j + 2), X) := hquot.lift sg hfac
  have hτ : τ.comp s = sg := hquot.lift_comp sg hfac
  -- the collapsed point `y` is the image of the cube corner `0`, where `sg` equals `x₀`.
  have hz₀ : ∃ i : Fin (j + 3),
      (Work.RatHurewicz.H (j + 2) (0 : Work.Stems.Cubical.IC (j + 2))) i = 0 :=
    H_mem_simplexBoundary (j + 2) 0 (Work.Stems.zero_mem_cubeBoundary (j + 2) (by omega))
  have hbar : s (Work.RatHurewicz.H (j + 2) 0) = y := hsbnd _ hz₀
  refine ⟨τ, s, y, hτ, hsbnd, ?_⟩
  have hcomp := congrFun (congrArg DFunLike.coe hτ) (Work.RatHurewicz.H (j + 2) 0)
  rw [← hbar]
  exact hcomp.trans (hbnd _ hz₀)

end Work.Stems.PerSimplex

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-!
# The pinched simplex: the geometric input of the per-simplex spherical replacement

Given a compression family `H : SimpHom X {x₀} (j+1)` and a singular `(j+2)`-simplex `a`, the
"pinched" simplex `s` is the simplex obtained from `a` by pushing its boundary to `x₀` along the
homotopies of the `(j+1)`-faces of `a` (given by `H`).  The lemma below records the two facts
needed by the spherical-replacement argument:

* `s` is constant, with value `x₀`, on the boundary of `Δ^{j+2}`;
* the cycle `simplexChain s - simplexChain (constSimplex x₀)` is homologous to the chain-level
  spherical replacement `Zeta j x₀ H (simplexChain a)`.
-/

open CategoryTheory AlgebraicTopology Simplicial
open scoped Topology unitInterval Simplicial BigOperators

namespace Work.Stems.PerSimplex

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- **The pinched simplex.**  There is a `(j+2)`-simplex `s` which is constant on `∂Δ^{j+2}` and
whose "reduced" chain is homologous to `Zeta j x₀ H (simplexChain a)`. -/
theorem exists_pinchedSimplex (j : ℕ) (x₀ : X) (H : Work.Serre.SimpHom X {x₀} (j + 1))
    (a : Work.Stems.hSimplex X (j + 2)) :
    ∃ sg : C(↥(stdSimplex ℝ (Fin (j + 3))), X),
      (∀ z : ↥(stdSimplex ℝ (Fin (j + 3))), (∃ i : Fin (j + 3), z i = 0) → sg z = x₀) ∧
      ∃ w : (Work.Stems.hChain X).X (j + 3),
        (ModuleCat.Hom.hom ((Work.Stems.hChain X).d (j + 3) (j + 2))) w
          = Work.Stems.Zeta j x₀ H (Work.Stems.simplexChain (X := X) (j + 2) a)
            - (Work.Stems.simplexChain (X := X) (j + 2)
                  (Work.RatHurewicz.Bridge.simplexOf (j + 2) sg)
                - Work.Stems.simplexChain (X := X) (j + 2)
                    (Work.Stems.constSimplex (X := X) (j + 2) x₀)) :=
  Work.Stems.PerSimplex.pinchedSimplex j x₀ H a

end

end Work.Stems.PerSimplex

set_option backward.isDefEq.respectTransparency false

/-!
# The `k`-trick: a spherical realisation of a Hurewicz class

If `γ` is a cycle on the sphere `Sⁿ` and `P` is a based cube such that the push-forward of `γ`
along the descent `cubeLift P` of `P` is a prescribed cycle `z` of `X`, then the homology class of
`z` is the Hurewicz image of an explicit element of `πₙ(X,x₀)` — namely `⟦P⟧^k`, where `k` is the
image of `[γ]` under the chosen identification `Hₙ(Sⁿ;ℤ) ≅ ℤ`.

No knowledge of the *degree* of any collapse map is needed: the exponent `k` is defined inside the
proof from the very cycle `γ` that is used.
-/

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

namespace Work.Stems.PerSimplex

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The `k`-th power of a based cube has Hurewicz image `k •` the Hurewicz image of the cube. -/
theorem exists_zpow_hurewicz {n : ℕ} (hn : 1 ≤ n) (x₀ : X) (P : GenLoop (Fin n) X x₀)
    (k : ℤ) :
    ∃ p : HomotopyGroup (Fin n) X x₀,
      hurewiczMapN n hn x₀ p = k • hurewiczMapN n hn x₀ ⟦P⟧ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  letI : Group (Quotient (GenLoop.Homotopic.setoid (Fin n) x₀)) := HomotopyGroup.group (Fin n)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hmul : ∀ a b : HomotopyGroup (Fin (m + 1)) X x₀,
      hurewiczMapN (m + 1) hn x₀ (a * b)
        = hurewiczMapN (m + 1) hn x₀ a + hurewiczMapN (m + 1) hn x₀ b :=
    fun a b => hurewiczMap_mul m a b
  have hone : hurewiczMapN (m + 1) hn x₀ (1 : HomotopyGroup (Fin (m + 1)) X x₀) = 0 :=
    hurewiczMap_one m
  have hinv : ∀ y : HomotopyGroup (Fin (m + 1)) X x₀,
      hurewiczMapN (m + 1) hn x₀ y⁻¹ = - hurewiczMapN (m + 1) hn x₀ y := by
    intro y
    have h : hurewiczMapN (m + 1) hn x₀ y + hurewiczMapN (m + 1) hn x₀ y⁻¹ = 0 := by
      rw [← hmul, mul_inv_cancel, hone]
    exact eq_neg_of_add_eq_zero_right h
  have hnat : ∀ t : ℕ,
      hurewiczMapN (m + 1) hn x₀ (⟦P⟧ ^ (t : ℤ))
        = (t : ℤ) • hurewiczMapN (m + 1) hn x₀ ⟦P⟧ := by
    intro t
    induction t with
    | zero => rw [Nat.cast_zero, zpow_zero, hone, zero_smul]
    | succ t ih => rw [Nat.cast_succ, zpow_add_one, hmul, ih, add_zsmul, one_zsmul]
  refine ⟨⟦P⟧ ^ k, ?_⟩
  by_cases hk : 0 ≤ k
  · obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    exact hnat t
  · push_neg at hk
    obtain ⟨t, ht⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ -k by omega)
    have hk' : k = -((t : ℤ)) := by omega
    rw [hk', zpow_neg, hinv, hnat t, ← neg_zsmul]

/-- **The `k`-trick.** -/
theorem exists_hurewicz_preimage_of_cycle {n : ℕ} (hn : 1 ≤ n) (x₀ : X)
    (P : GenLoop (Fin n) X x₀) (γ : (chains (TopCat.of (sphere n))).cycles n) :
    ∃ p : HomotopyGroup (Fin n) X x₀,
      hurewiczMapN n hn x₀ p =
        HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (TopCat.of (sphere n)) (TopCat.of X)
            (TopCat.ofHom (cubeLift n hn P))) n
          ((chains (TopCat.of (sphere n))).homologyπ n γ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let ee : (chains (TopCat.of (sphere (m + 1)))).homology (m + 1) ≅
      ModuleCat.of ℤ ℤ := Classical.choice (Work.Cohomology.sphereHomologyTop (m + 1)
        (Nat.succ_le_succ (Nat.zero_le m)))
  let kk : ℤ := ModuleCat.Hom.hom ee.hom
    ((chains (TopCat.of (sphere (m + 1)))).homologyπ (m + 1) γ)
  have hu : ModuleCat.Hom.hom ee.hom
      (Work.Stems.sphereGenerator (m + 1) (Nat.succ_le_succ (Nat.zero_le m))) = 1 := by
    have hgen : Work.Stems.sphereGenerator (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) =
        ModuleCat.Hom.hom ee.inv (1 : ℤ) := rfl
    rw [hgen]
    have h := congrArg ModuleCat.Hom.hom (CategoryTheory.Iso.inv_hom_id ee)
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact LinearMap.congr_fun h (1 : ℤ)
  have h1 : (chains (TopCat.of (sphere (m + 1)))).homologyπ (m + 1) γ
      = kk • Work.Stems.sphereGenerator (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) := by
    apply Work.Cohomology.sphereHomologyTop_hom_injective (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m))
    show ModuleCat.Hom.hom ee.hom
        ((chains (TopCat.of (sphere (m + 1)))).homologyπ (m + 1) γ)
      = ModuleCat.Hom.hom ee.hom
        (kk • Work.Stems.sphereGenerator (m + 1) (Nat.succ_le_succ (Nat.zero_le m)))
    rw [map_zsmul, hu]
    show kk = kk • (1 : ℤ)
    simp
  obtain ⟨p, hp⟩ := exists_zpow_hurewicz (Nat.succ_le_succ (Nat.zero_le m)) x₀ P kk
  have hP : hurewiczMapN (m + 1) hn x₀ ⟦P⟧
      = HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (TopCat.of (sphere (m + 1))) (TopCat.of X)
            (TopCat.ofHom (cubeLift (m + 1) hn P))) (m + 1)
          (Work.Stems.sphereGenerator (m + 1) (Nat.succ_le_succ (Nat.zero_le m))) := rfl
  refine ⟨p, ?_⟩
  rw [hp, hP]
  show kk • HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of (sphere (m + 1))) (TopCat.of X)
          (TopCat.ofHom (cubeLift (m + 1) hn P))) (m + 1)
        (Work.Stems.sphereGenerator (m + 1) (Nat.succ_le_succ (Nat.zero_le m)))
      = HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (TopCat.of (sphere (m + 1))) (TopCat.of X)
            (TopCat.ofHom (cubeLift (m + 1) hn P))) (m + 1)
          ((chains (TopCat.of (sphere (m + 1)))).homologyπ (m + 1) γ)
  rw [← map_zsmul, h1]

end

end Work.Stems.PerSimplex

set_option maxHeartbeats 1600000

/-!
# Assembly of the per-simplex spherical replacement

`Work.Stems.PerSimplexSpherical` is proved from the geometric input
`Work.Stems.PerSimplex.exists_pinchedSimplex` (the "pinched simplex" and its chain-level homology
relation) together with the chain-level bookkeeping proved here, and the `k`-trick
`Work.Stems.PerSimplex.exists_hurewicz_preimage_of_cycle` (which turns any class which is the
push-forward of a cycle on the sphere into a Hurewicz image).
-/

open CategoryTheory AlgebraicTopology Simplicial
open scoped Topology unitInterval Simplicial BigOperators

namespace Work.Stems.PerSimplex

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-! ## The chain-level bookkeeping -/

/-- The generator-level form of `chainMap`: the chain map induced by a continuous map sends the
chain carried by a simplex to the chain carried by its image. -/
theorem chainMap_ιChainComplex' (R : Type) [CommRing R] {Y Z : TopCat} (f : Y ⟶ Z) {n : ℕ}
    (τ : (TopCat.toSSet.obj Y) _⦋n⦌) :
    ((Work.Cohomology.chainMap R Y Z f).f n).hom
        ((SSet.ιChainComplex (TopCat.toSSet.obj Y) (R := ModuleCat.of R R) τ).hom 1) =
      (SSet.ιChainComplex (TopCat.toSSet.obj Z) (R := ModuleCat.of R R)
        ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) τ)).hom 1 := by
  rw [Work.Cohomology.chainMap_f_eq]
  exact congrArg (fun (m : ModuleCat.of R R ⟶
      ((TopCat.toSSet.obj Z).chainComplex (ModuleCat.of R R)).X n) => m.hom (1 : R))
    (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj Y) (TopCat.toSSet.obj Z) (TopCat.toSSet.map f)
      (ModuleCat.of R R) τ)

/-- The singular chain carried by a simplex is the same chain in the `Sing` and in the `Serre`
presentation of the singular chain complex. -/
theorem simpChain_eq_simplexChain (n : ℕ) (c : C(↥(stdSimplex ℝ (Fin (n + 1))), X)) :
    Work.RatHurewicz.Bridge.simpChain n c
      = Work.Stems.simplexChain (X := X) n (Work.RatHurewicz.Bridge.simplexOf n c) := by
  apply Work.Cohomology.Crux33.eq_of_coords_eq
  rw [Work.RatHurewicz.Bridge.coords_simpChain, Work.Stems.coords_simplexChain]

/-- The chain of the constant simplex, in the `bridge` presentation. -/
theorem constSimplex_eq_simpChain (n : ℕ) (x : X) :
    Work.RatHurewicz.Bridge.simpChain n
        (ContinuousMap.const (↥(stdSimplex ℝ (Fin (n + 1)))) x)
      = Work.Stems.simplexChain (X := X) n (Work.Stems.constSimplex (X := X) n x) :=
  simpChain_eq_simplexChain n _

/-- The functoriality of the singular simplices of a continuous map. -/
theorem toSSet_map_simplexOf {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (g : C(A, B)) (n : ℕ) (c : C(↥(stdSimplex ℝ (Fin (n + 1))), A)) :
    (TopCat.toSSet.map (TopCat.ofHom g)).app (Opposite.op (SimplexCategory.mk n))
        (Work.RatHurewicz.Bridge.simplexOf n c)
      = Work.RatHurewicz.Bridge.simplexOf n (g.comp c) := by
  apply ((TopCat.of B).toSSetObjEquivT (Opposite.op (SimplexCategory.mk n))).injective
  rw [Work.Bordism.toSSetObjEquiv_map_apply, Work.RatHurewicz.Bridge.toSSetObjEquiv_simplexOf,
    Work.RatHurewicz.Bridge.toSSetObjEquiv_simplexOf]
  rfl

/-- The push-forward of the chain carried by a simplex along a continuous map. -/
theorem chainMap_simpChain_ofHom {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (g : C(A, B)) (n : ℕ) (c : C(↥(stdSimplex ℝ (Fin (n + 1))), A)) :
    (ModuleCat.Hom.hom ((Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B)
        (TopCat.ofHom g)).f n)) (Work.RatHurewicz.Bridge.simpChain n c)
      = Work.RatHurewicz.Bridge.simpChain n (g.comp c) := by
  have h1 : Work.RatHurewicz.Bridge.simpChain n c
      = (SSet.ιChainComplex (TopCat.toSSet.obj (TopCat.of A)) (R := ModuleCat.of ℤ ℤ)
          (Work.RatHurewicz.Bridge.simplexOf n c)).hom 1 := by
    rw [Work.RatHurewicz.Bridge.simpChain, Work.Cohomology.Crux33.mk_single]
  have h2 : Work.RatHurewicz.Bridge.simpChain n (g.comp c)
      = (SSet.ιChainComplex (TopCat.toSSet.obj (TopCat.of B)) (R := ModuleCat.of ℤ ℤ)
          (Work.RatHurewicz.Bridge.simplexOf n (g.comp c))).hom 1 := by
    rw [Work.RatHurewicz.Bridge.simpChain, Work.Cohomology.Crux33.mk_single]
  rw [h1, h2, chainMap_ιChainComplex']
  exact congrArg (fun (τ : (TopCat.toSSet.obj (TopCat.of B)).obj
      (Opposite.op (SimplexCategory.mk n))) =>
        (SSet.ιChainComplex (TopCat.toSSet.obj (TopCat.of B)) (R := ModuleCat.of ℤ ℤ) τ).hom 1)
    (toSSet_map_simplexOf g n c)

/-! ## The descent of a boundary-constant simplex, with the collapse of the cube -/

/-- The descent data of a simplex `sg` which is constant, with value `x₀`, on the simplicial
boundary: a continuous map `τ` of the sphere with `τ ∘ s = sg` for a collapse `s` of the simplex,
where `s` is tied to the cube collapse of `I^{j+2}` (so that the collapsed point is the base point
of `S^{j+2}` used by `cubeLift`). -/
theorem descentData (j : ℕ) (x₀ : X)
    (sg : C(↥(stdSimplex ℝ (Fin (j + 3))), X))
    (hbnd : ∀ z : ↥(stdSimplex ℝ (Fin (j + 3))), (∃ i : Fin (j + 3), z i = 0) → sg z = x₀) :
    ∃ (τ : C(Work.Stems.sphere (j + 2), X))
      (s : C(↥(stdSimplex ℝ (Fin (j + 3))), Work.Stems.sphere (j + 2)))
      (y : Work.Stems.sphere (j + 2)),
      τ.comp s = sg ∧
        s.comp (Work.RatHurewicz.H (j + 2)) = Work.Stems.collapseMap (j + 2) (by omega) ∧
        (∀ z : ↥(stdSimplex ℝ (Fin (j + 3))), (∃ i : Fin (j + 3), z i = 0) → s z = y) ∧
        τ y = x₀ := by
  obtain ⟨s, y, hscomp, hsbnd⟩ :=
    Work.RatHurewicz.Bridge.exists_collapse_simplex (j + 2) (by omega)
  have hHq : Topology.IsQuotientMap ⇑(Work.RatHurewicz.H (j + 2)) :=
    Work.RatHurewicz.Bridge.H_isQuotientMap (j + 2)
  have hcompq : Topology.IsQuotientMap (⇑s ∘ ⇑(Work.RatHurewicz.H (j + 2))) := by
    rw [← ContinuousMap.coe_comp, hscomp]
    exact Work.Stems.collapseMap_isQuotientMap (j + 2) (by omega)
  have hquot : Topology.IsQuotientMap ⇑s := hHq.of_comp_isQuotientMap hcompq
  have hc : ∀ u : Work.Stems.Cubical.IC (j + 2), s (Work.RatHurewicz.H (j + 2) u)
      = Work.Stems.collapseMap (j + 2) (by omega) u :=
    fun u => congrFun (congrArg DFunLike.coe hscomp) u
  have hfac : Function.FactorsThrough ⇑sg ⇑s := by
    intro a b hab
    obtain ⟨t, rfl⟩ := Work.RatHurewicz.Bridge.H_surjective (j + 2) a
    obtain ⟨t', rfl⟩ := Work.RatHurewicz.Bridge.H_surjective (j + 2) b
    have hcm : Work.Stems.collapseMap (j + 2) (by omega) t
        = Work.Stems.collapseMap (j + 2) (by omega) t' := by
      rw [← hc t, ← hc t']
      exact hab
    rcases Work.Stems.collapseMap_fiber (j + 2) (by omega) hcm with h | ⟨ht, ht'⟩
    · rw [h]
    · obtain ⟨i, hi⟩ := H_mem_simplexBoundary (j + 2) t ht
      obtain ⟨i', hi'⟩ := H_mem_simplexBoundary (j + 2) t' ht'
      rw [hbnd _ ⟨i, hi⟩, hbnd _ ⟨i', hi'⟩]
  let τ : C(Work.Stems.sphere (j + 2), X) := hquot.lift sg hfac
  have hτ : τ.comp s = sg := hquot.lift_comp sg hfac
  have hz₀ : ∃ i : Fin (j + 3),
      (Work.RatHurewicz.H (j + 2) (0 : Work.Stems.Cubical.IC (j + 2))) i = 0 :=
    H_mem_simplexBoundary (j + 2) 0 (Work.Stems.zero_mem_cubeBoundary (j + 2) (by omega))
  have hbar : s (Work.RatHurewicz.H (j + 2) 0) = y := hsbnd _ hz₀
  refine ⟨τ, s, y, hτ, hscomp, hsbnd, ?_⟩
  have hcomp := congrFun (congrArg DFunLike.coe hτ) (Work.RatHurewicz.H (j + 2) 0)
  rw [← hbar]
  exact hcomp.trans (hbnd _ hz₀)

/-! ## The chain-level core -/

/-- **The chain-level core.**  From the pinched simplex `sg`, its descent `τ` and the boundary
relation `w`, one builds a based cube `P`, a cycle `γ` on the sphere and a cycle `z` of `X` with
`z` representing `Zeta j x₀ H (simplexChain a)` and with the push-forward of `γ` along the descent
of `P` representing `z`. -/
theorem chainLevelCore_of_pinched (j : ℕ) (x₀ : X) (H : Work.Serre.SimpHom X {x₀} (j + 1))
    (a : Work.Stems.hSimplex X (j + 2)) (sg : C(↥(stdSimplex ℝ (Fin (j + 3))), X))
    (hbnd : ∀ z : ↥(stdSimplex ℝ (Fin (j + 3))), (∃ i : Fin (j + 3), z i = 0) → sg z = x₀)
    (w : (Work.Stems.hChain X).X (j + 3))
    (hw : (ModuleCat.Hom.hom ((Work.Stems.hChain X).d (j + 3) (j + 2))) w
        = Work.Stems.Zeta j x₀ H (Work.Stems.simplexChain (X := X) (j + 2) a)
          - (Work.Stems.simplexChain (X := X) (j + 2)
                (Work.RatHurewicz.Bridge.simplexOf (j + 2) sg)
              - Work.Stems.simplexChain (X := X) (j + 2)
                  (Work.Stems.constSimplex (X := X) (j + 2) x₀))) :
    ∃ (P : GenLoop (Fin (j + 2)) X x₀)
      (γ : (Work.Stems.chains (TopCat.of (Work.Stems.sphere (j + 2)))).cycles (j + 2))
      (zc : (Work.Stems.hChain X).cycles (j + 2)),
      (ModuleCat.Hom.hom ((Work.Stems.hChain X).iCycles (j + 2)) zc
          = Work.Stems.Zeta j x₀ H (Work.Stems.simplexChain (X := X) (j + 2) a)) ∧
      (HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (TopCat.of (Work.Stems.sphere (j + 2))) (TopCat.of X)
            (TopCat.ofHom (Work.Stems.cubeLift (j + 2) (by omega) P))) (j + 2)
          ((Work.Stems.chains (TopCat.of (Work.Stems.sphere (j + 2)))).homologyπ (j + 2) γ)
        = (Work.Stems.hChain X).homologyπ (j + 2) zc) := by
  have hn : 1 ≤ j + 2 := by omega
  obtain ⟨τ, s, y, hτs, hscomp, hsbnd, hτy⟩ := descentData j x₀ sg hbnd
  -- the collapsed point of the simplex collapse is the base point of the sphere
  have hH0 : ∃ i : Fin (j + 3),
      (Work.RatHurewicz.H (j + 2) (0 : Work.Stems.Cubical.IC (j + 2))) i = 0 :=
    H_mem_simplexBoundary (j + 2) 0 (Work.Stems.zero_mem_cubeBoundary (j + 2) hn)
  have hcm0 : Work.Stems.collapseMap (j + 2) hn (0 : Work.Stems.Cubical.IC (j + 2)) = y := by
    rw [← congrFun (congrArg DFunLike.coe hscomp) 0]
    exact hsbnd _ hH0
  -- the based cube
  let P : GenLoop (Fin (j + 2)) X x₀ :=
    ⟨τ.comp (Work.Stems.collapseMap (j + 2) hn), by
      intro u hu
      rw [ContinuousMap.comp_apply, Work.Stems.collapseMap_boundary (j + 2) hn hu, hcm0, hτy]⟩
  have hlift : Work.Stems.cubeLift (j + 2) (by omega) P = τ := by
    have h1 : (Work.Stems.cubeLift (j + 2) (by omega) P).comp (Work.Stems.collapseMap (j + 2) hn)
        = τ.comp (Work.Stems.collapseMap (j + 2) hn) := by
      rw [Work.Stems.cubeLift_comp (j + 2) (by omega) P]
    ext x
    obtain ⟨u, rfl⟩ := (Work.Stems.collapseMap_isQuotientMap (j + 2) hn).surjective x
    exact congrFun (congrArg DFunLike.coe h1) u
  -- the cycle of the sphere
  let cs : (Work.Stems.chains (TopCat.of (Work.Stems.sphere (j + 2)))).X (j + 2) :=
    Work.RatHurewicz.Bridge.simpChain (j + 2) s
      - Work.RatHurewicz.Bridge.simpChain (j + 2)
          (ContinuousMap.const (↥(stdSimplex ℝ (Fin (j + 3)))) y)
  have hcs : (Work.Stems.chains (TopCat.of (Work.Stems.sphere (j + 2)))).d (j + 2) (j + 2 - 1) cs
      = 0 :=
    Work.RatHurewicz.Bridge.sigmaChain_cycle (j + 2) s y hsbnd
  let γ : (Work.Stems.chains (TopCat.of (Work.Stems.sphere (j + 2)))).cycles (j + 2) :=
    Work.RatHurewicz.Bridge.cycleOf (Work.Stems.chains (TopCat.of (Work.Stems.sphere (j + 2))))
      (j + 2) hn cs hcs
  let cmap := Work.Cohomology.chainMap ℤ (TopCat.of (Work.Stems.sphere (j + 2))) (TopCat.of X)
    (TopCat.ofHom τ)
  have hiγ : (ModuleCat.Hom.hom
        ((Work.Stems.chains (TopCat.of (Work.Stems.sphere (j + 2)))).iCycles (j + 2))) γ = cs :=
    Work.RatHurewicz.Bridge.iCycles_cycleOf _ (j + 2) hn cs hcs
  have hconst : τ.comp (ContinuousMap.const (↥(stdSimplex ℝ (Fin (j + 3)))) y)
      = ContinuousMap.const (↥(stdSimplex ℝ (Fin (j + 3)))) x₀ := by
    ext z
    exact hτy
  set aa : (Work.Stems.hChain X).X (j + 2) :=
    (ModuleCat.Hom.hom (cmap.f (j + 2))) ((ModuleCat.Hom.hom
      ((Work.Stems.chains (TopCat.of (Work.Stems.sphere (j + 2)))).iCycles (j + 2))) γ) with haa
  have hcτ : aa = Work.RatHurewicz.Bridge.simpChain (j + 2) sg
      - Work.RatHurewicz.Bridge.simpChain (j + 2)
          (ContinuousMap.const (↥(stdSimplex ℝ (Fin (j + 3)))) x₀) := by
    rw [haa, hiγ, map_sub, chainMap_simpChain_ofHom, chainMap_simpChain_ofHom, hτs, hconst]
  have hconv : Work.RatHurewicz.Bridge.simpChain (j + 2) sg
      - Work.RatHurewicz.Bridge.simpChain (j + 2)
          (ContinuousMap.const (↥(stdSimplex ℝ (Fin (j + 3)))) x₀)
      = Work.Stems.simplexChain (X := X) (j + 2) (Work.RatHurewicz.Bridge.simplexOf (j + 2) sg)
        - Work.Stems.simplexChain (X := X) (j + 2) (Work.Stems.constSimplex (X := X) (j + 2) x₀) := by
    rw [simpChain_eq_simplexChain, constSimplex_eq_simpChain]
    try rfl
  have hsub : aa = Work.Stems.simplexChain (X := X) (j + 2)
        (Work.RatHurewicz.Bridge.simplexOf (j + 2) sg)
      - Work.Stems.simplexChain (X := X) (j + 2) (Work.Stems.constSimplex (X := X) (j + 2) x₀) :=
    hcτ.trans hconv
  have hxcyc : (ModuleCat.Hom.hom ((Work.Stems.chains (TopCat.of X)).d (j + 2) (j + 1))) aa = 0 := by
    rw [hcτ]
    exact Work.RatHurewicz.Bridge.sigmaChain_cycle (j + 2) sg x₀ hbnd
  -- the cycle representing `Zeta`
  set ZetaC : (Work.Stems.hChain X).X (j + 2) :=
    Work.Stems.Zeta j x₀ H (Work.Stems.simplexChain (X := X) (j + 2) a) with hZetaC
  have hZC : (ModuleCat.Hom.hom ((Work.Stems.chains (TopCat.of X)).d (j + 2) (j + 1))) ZetaC = 0 :=
    (zetaCalculus (X := X) j x₀ H).2.1 (Work.Stems.simplexChain (X := X) (j + 2) a)
  have hwC : (ModuleCat.Hom.hom ((Work.Stems.chains (TopCat.of X)).d (j + 3) (j + 2))) w
      = ZetaC - aa := by
    rw [hsub]
    exact hw
  -- the homology comparison
  have hkey := (Work.Stems.PerSimplex.homologypi_eq_of_boundary hn
    (Work.Stems.chains (TopCat.of X)) ZetaC aa w hZC hxcyc hwC.symm).symm
  let zcC : (Work.Stems.chains (TopCat.of X)).cycles (j + 2) :=
    Work.RatHurewicz.Bridge.cycleOf (Work.Stems.chains (TopCat.of X)) (j + 2) hn ZetaC hZC
  have hinj : Function.Injective
      (ModuleCat.Hom.hom ((Work.Stems.chains (TopCat.of X)).iCycles (j + 2))) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hcycEq : HomologicalComplex.cyclesMap cmap (j + 2) γ
      = Work.RatHurewicz.Bridge.cycleOf (Work.Stems.chains (TopCat.of X)) (j + 2) hn aa hxcyc := by
    apply hinj
    have hL : (ModuleCat.Hom.hom ((Work.Stems.chains (TopCat.of X)).iCycles (j + 2)))
        (HomologicalComplex.cyclesMap cmap (j + 2) γ)
        = (ModuleCat.Hom.hom (cmap.f (j + 2))) ((ModuleCat.Hom.hom
            ((Work.Stems.chains (TopCat.of (Work.Stems.sphere (j + 2)))).iCycles (j + 2))) γ) :=
      Work.RatHurewicz.Bridge.iCycles_cyclesMap cmap (j + 2) γ
    have hR : (ModuleCat.Hom.hom ((Work.Stems.chains (TopCat.of X)).iCycles (j + 2)))
        (Work.RatHurewicz.Bridge.cycleOf (Work.Stems.chains (TopCat.of X)) (j + 2) hn aa hxcyc)
        = aa :=
      Work.RatHurewicz.Bridge.iCycles_cycleOf _ (j + 2) hn aa hxcyc
    rw [hL, hR]
  have hzcC : (ModuleCat.Hom.hom ((Work.Stems.chains (TopCat.of X)).iCycles (j + 2))) zcC = ZetaC :=
    Work.RatHurewicz.Bridge.iCycles_cycleOf _ (j + 2) hn ZetaC hZC
  have hfinalC : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap cmap (j + 2)))
      ((Work.Stems.chains (TopCat.of (Work.Stems.sphere (j + 2)))).homologyπ (j + 2) γ)
      = (ModuleCat.Hom.hom ((Work.Stems.chains (TopCat.of X)).homologyπ (j + 2))) zcC := by
    rw [Work.RatHurewicz.Bridge.homologyMap_homologyπ cmap (j + 2) γ, hcycEq]
    exact hkey
  refine ⟨P, γ, zcC, ?_, ?_⟩
  · exact hzcC
  · rw [hlift]
    exact hfinalC

/-- **The per-simplex spherical replacement**, from the chain-level core. -/
theorem perSimplexSpherical_of_core (j : ℕ) (x₀ : X) (H : Work.Serre.SimpHom X {x₀} (j + 1)) :
    Work.Stems.PerSimplexSpherical j x₀ H := by
  intro a
  obtain ⟨sg, hbnd, w, hw⟩ := exists_pinchedSimplex j x₀ H a
  obtain ⟨P, γ, zc, hz, hclass⟩ := chainLevelCore_of_pinched j x₀ H a sg hbnd w hw
  obtain ⟨p, hp⟩ := exists_hurewicz_preimage_of_cycle (show 1 ≤ j + 2 by omega) x₀ P γ
  exact ⟨zc, p, hz, by rw [hp]; exact hclass⟩

end

end Work.Stems.PerSimplex

/-- **The surjectivity half of the integral Hurewicz result in the first non-vanishing degree.**
For `n ≥ 2` and a space `X` with `πᵢ(X,x₀)` trivial for every `i < n` (`π₀` included, so `X` is
path connected, and for `n = 2` also simply connected), the Hurewicz map
`Work.Stems.hurewiczMapN n _ x₀ : πₙ(X,x₀) → Hₙ(X;ℤ)` is **surjective**.

Combined with the already proved injectivity
(`Work.Stems.Hur2c.hurewiczMapN_eq_const_of_eq_zero`) this gives the bijective form
`Work.Stems.hurewicz_first_degree` (`Submission/Work/Stems/HurewiczFirstDegree.lean`, still a
stub), which SERRE's `S1` route and the `C2` chapter's "`H_{2j}(K(ℤ,2j);ℤ) ≅ ℤ`" clause both use.

Three routes are known; the third is the one the workspace's machinery is closest to.

* *(CW/cellular, Hatcher 4.32.)* Take a CW approximation `W → X` with `W` `(n-1)`-connected and a
  single `0`-cell; then `πₙ(W) → πₙ(X)` is an iso, `Hₙ(W) ≅ Hₙ(X)` (both are unchanged by the
  weak equivalence in this range), and for `W = (∨ Sⁿ) ∪ (n+1)-cells` both `πₙ(W)` and `Hₙ(W)` are
  the cokernel of the same boundary map, given on both sides by degrees of attaching maps
  (`Work.RatHurewicz.attachCells` and the cell machinery of RATHUREWICZ are available).
* *(Cone/relative.)* `Hₙ(X) ≅ H_{n+1}(CX, X)` and `πₙ(X) ≅ π_{n+1}(CX, X)` for the cone `CX`, so
  it suffices to show that the *relative* `(n+1)`-cycles of the pair `(CX, X)` are generated by
  relative spheres — i.e. by maps `(D^{n+1}, Sⁿ) → (CX, X)`.
* *(Spherical replacement.)* For a singular `n`-simplex `σ : Δⁿ → X`, the restriction
  `σ|∂Δⁿ : S^{n-1} → X` is null-homotopic (it is a map out of `S^{n-1}` into an `(n-1)`-connected
  space, unbased — here one uses `π₀` and `π₁` triviality to move the base point), so by the
  homotopy extension property of `(Δⁿ, ∂Δⁿ)` there is a homotopy relative to `∂Δⁿ` from `σ` to a
  simplex `σ'` that is constant on `∂Δⁿ`, hence factors as `τ ∘ s` with `s : Δⁿ → Sⁿ` the collapse
  simplex (`Work.RatHurewicz.Bridge.exists_collapse_simplex`) and `τ : Sⁿ → X`; the prism of the
  homotopy makes `σ' - σ` a boundary modulo degenerate simplices, and the degenerate cycles are
  null-homologous (normalisation of the singular chain complex); finally
  `[σ'] = τ_*(α)`, an (unbased) Hurewicz image, and the base point is moved with
  `Work.RatHurewicz.joined_sphere`-type paths.  This is the route that reuses area STEMS'
  cubical machinery (`Work.RatHurewicz.cubicalBridgeDeg`) and `Bridge/`.-/
theorem hurewiczMapN_surjective {X : Type} [TopologicalSpace X] (n : ℕ) (hn : 2 ≤ n) (x₀ : X)
    (hconn : ∀ i : ℕ, i < n → Subsingleton (HomotopyGroup (Fin i) X x₀)) :
    Function.Surjective (Work.Stems.hurewiczMapN n (by omega) x₀) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  obtain ⟨H⟩ := Work.Serre.simpHom_of_compress (j + 1)
    (Work.Stems.compressHyp_singleton (j + 1) x₀ (fun i hi => hconn i (by omega)))
  exact Work.Stems.surjectiveOfPerSimplex j x₀ H
    (Work.Stems.PerSimplex.perSimplexSpherical_of_core j x₀ H)

end

end Work.Stems
