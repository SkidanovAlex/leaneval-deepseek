import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Separation.Lemmas
import Mathlib.Algebra.Module.StablyFree.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A compact abelian group of prime exponent with all index-`ℓ` subgroups open is finite

**Main result** (`NK.LocalTame.cruxCompactExpPrimeFinite`).  Let `V` be a compact Hausdorff
abelian topological group of exponent a prime `ℓ`, and suppose that every subgroup of `V` of
index `ℓ` is open.  Then `V` is finite.

The proof is the standard one, organised so that only very little topological input is used.
Assume `V` infinite and write `A = Additive V`, an infinite `ZMod ℓ`-module.

* `Crux.toMulHom` converts a `ZMod ℓ`-linear functional on `A` into a group homomorphism
  `V →* Multiplicative (ZMod ℓ)`; if the functional is nonzero its kernel has index `ℓ`, so by
  hypothesis it is open, and `Crux.continuous_of_isOpen_ker` then shows the functional is
  continuous.  Hence *every* linear functional on `A` is continuous.
* `Crux.exists_surjective_prefix_family` produces a sequence `F n` of functionals all of whose
  finite prefix maps are onto (`Crux.prefixStep` adds the next one using that the kernel of the
  previous prefix map is infinite).
* Compactness (`IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`) upgrades the
  finite surjectivity to surjectivity of `Ψ : A → (ℕ → ZMod ℓ)`, and `Ψ` is a quotient map.
* On `ℕ → ZMod ℓ` there is a functional vanishing on the dense submodule of finitely supported
  functions but not on the constant function `1`; it is therefore *not* continuous.  Pulling it
  back along the quotient `Ψ` gives a linear functional on `A` that is not continuous (as a
  composite with the quotient map), contradicting the previous point.

The last two steps are what rules out e.g. infinite products of copies of `ZMod ℓ`.

This file is self-contained (only `Mathlib` is imported).
-/

namespace NK.LocalTame

open Filter

namespace Crux

/-! ## Auxiliary topological and algebraic lemmas -/

/-- A group homomorphism into a discrete group is continuous as soon as its kernel is open. -/
theorem continuous_of_isOpen_ker {G H : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [DiscreteTopology H] (φ : G →* H)
    (h : IsOpen (φ.ker : Set G)) : Continuous φ := by
  rw [continuous_iff_continuousAt]
  intro g
  rw [ContinuousAt, nhds_discrete H, Filter.tendsto_pure]
  have hiso : φ ⁻¹' {φ g} = (fun k : G => g * k) '' (φ.ker : Set G) := by
    ext x
    constructor
    · intro hx
      have hxg : φ x = φ g := Set.mem_singleton_iff.mp (Set.mem_preimage.mp hx)
      refine ⟨g⁻¹ * x, ?_, ?_⟩
      · show φ (g⁻¹ * x) = 1
        rw [map_mul, map_inv, hxg, inv_mul_cancel]
      · group
    · rintro ⟨k, hk, rfl⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      rw [map_mul, MonoidHom.mem_ker.mp hk, mul_one]
  have hmem : φ ⁻¹' {φ g} ∈ nhds g := by
    rw [hiso]
    exact ((Homeomorph.mulLeft g).isOpenMap _ h).mem_nhds ⟨1, φ.ker.one_mem, mul_one g⟩
  exact hmem

section LinearAlgebra

variable {A : Type*} [AddCommGroup A] {ℓ : ℕ} [Module (ZMod ℓ) A]

/-- The "prefix map" `a ↦ (f₀ a, f₁ a, …)`. -/
def piMap {n : ℕ} (f : Fin n → (A →ₗ[ZMod ℓ] ZMod ℓ)) : A →ₗ[ZMod ℓ] (Fin n → ZMod ℓ) where
  toFun a := fun i => f i a
  map_add' a b := by ext i; simp
  map_smul' c a := by ext i; simp

theorem piMap_apply {n : ℕ} (f : Fin n → (A →ₗ[ZMod ℓ] ZMod ℓ)) (a : A) (i : Fin n) :
    piMap f a i = f i a := rfl

theorem ker_piMap_eq {n : ℕ} (f : Fin n → (A →ₗ[ZMod ℓ] ZMod ℓ)) (x : A) :
    x ∈ LinearMap.ker (piMap f) ↔ ∀ i, f i x = 0 := by
  simp [piMap, LinearMap.mem_ker, funext_iff]

/-- **Extension step.**  Given `n` functionals whose prefix map is onto, and an infinite space `A`
in which every nonzero vector is detected by a functional taking the value `1`, one can add one
more functional so that the new prefix map is again onto. -/
theorem prefixStep [NeZero ℓ] {n : ℕ} (prev : Fin n → (A →ₗ[ZMod ℓ] ZMod ℓ))
    (hprev : Function.Surjective (piMap prev)) (hinf : Infinite A)
    (hex : ∀ a : A, a ≠ 0 → ∃ f : A →ₗ[ZMod ℓ] ZMod ℓ, f a = 1) :
    ∃ g : A →ₗ[ZMod ℓ] ZMod ℓ, Function.Surjective (piMap (Fin.snoc prev g)) := by
  have hK : ∃ x : A, x ∈ LinearMap.ker (piMap prev) ∧ x ≠ 0 := by
    by_contra h
    push Not at h
    have hker : LinearMap.ker (piMap prev) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      exact h x hx
    have hinj : Function.Injective (piMap prev) := by
      rw [← LinearMap.ker_eq_bot]; exact hker
    exact hinf.not_finite (Finite.of_injective (piMap prev) hinj)
  obtain ⟨x, hx, hx0⟩ := hK
  obtain ⟨g, hg⟩ := hex x hx0
  have hx0' : ∀ i : Fin n, prev i x = 0 := fun i => (ker_piMap_eq prev x).mp hx i
  refine ⟨g, ?_⟩
  intro y
  obtain ⟨a, ha⟩ : ∃ a : A, piMap prev a = fun i : Fin n => y i.castSucc := hprev _
  refine ⟨a + (y (Fin.last n) - g a) • x, ?_⟩
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [piMap_apply, Fin.snoc_castSucc]
    have h1 : prev j (a + (y (Fin.last n) - g a) • x) = piMap prev a j := by
      rw [map_add, map_smul, hx0' j, smul_zero, add_zero]
      rfl
    rw [h1, congrFun ha j]
  · rw [piMap_apply, Fin.snoc_last, map_add, map_smul, hg]
    ring

/-- Recursively build a family of functionals all of whose finite prefix maps are onto. -/
noncomputable def prefixAux [NeZero ℓ] (hinf : Infinite A)
    (hex : ∀ a : A, a ≠ 0 → ∃ f : A →ₗ[ZMod ℓ] ZMod ℓ, f a = 1) :
    (n : ℕ) → {f : Fin n → (A →ₗ[ZMod ℓ] ZMod ℓ) // Function.Surjective (piMap f)}
  | 0 => ⟨Fin.elim0, by intro y; exact ⟨0, funext fun i => i.elim0⟩⟩
  | n + 1 =>
      ⟨Fin.snoc (prefixAux hinf hex n).1
          (prefixStep (prefixAux hinf hex n).1 (prefixAux hinf hex n).2 hinf hex).choose,
        (prefixStep (prefixAux hinf hex n).1 (prefixAux hinf hex n).2 hinf hex).choose_spec⟩

/-- The `n`-th functional of the recursive family. -/
noncomputable def prefixSeq [NeZero ℓ] (hinf : Infinite A)
    (hex : ∀ a : A, a ≠ 0 → ∃ f : A →ₗ[ZMod ℓ] ZMod ℓ, f a = 1) (n : ℕ) :
    A →ₗ[ZMod ℓ] ZMod ℓ := (prefixAux hinf hex (n + 1)).1 (Fin.last n)

theorem prefixAux_prefixEq [NeZero ℓ] (hinf : Infinite A)
    (hex : ∀ a : A, a ≠ 0 → ∃ f : A →ₗ[ZMod ℓ] ZMod ℓ, f a = 1) :
    ∀ (n : ℕ) (i : Fin n), (prefixAux hinf hex n).1 i = prefixSeq hinf hex i := by
  intro n
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · simp only [prefixAux, Fin.snoc_castSucc]
        rw [ih j]
        simp
      · simp only [prefixAux, prefixSeq, Fin.snoc_last]

/-- **A family of functionals with all prefix maps onto.** -/
theorem exists_surjective_prefix_family [NeZero ℓ] (hinf : Infinite A)
    (hex : ∀ a : A, a ≠ 0 → ∃ f : A →ₗ[ZMod ℓ] ZMod ℓ, f a = 1) :
    ∃ F : ℕ → (A →ₗ[ZMod ℓ] ZMod ℓ), ∀ n, Function.Surjective (piMap (fun i : Fin n => F i)) := by
  refine ⟨prefixSeq hinf hex, fun n => ?_⟩
  have h := (prefixAux hinf hex n).2
  have heq : (prefixAux hinf hex n).1 = fun i : Fin n => prefixSeq hinf hex i :=
    funext (prefixAux_prefixEq hinf hex n)
  rw [heq] at h
  exact h

end LinearAlgebra

section FIP

variable {A : Type*} [AddCommGroup A] [TopologicalSpace A] [CompactSpace A] [T2Space A]
  {ℓ : ℕ} [Module (ZMod ℓ) A]

/-- If all finite "prefix maps" of a sequence of continuous functionals are onto, then the
combined map into the full product is onto. -/
theorem surjective_pi_of_prefix_surjective (F : ℕ → (A →ₗ[ZMod ℓ] ZMod ℓ))
    (hcont : ∀ n, Continuous (F n : A → ZMod ℓ))
    (hF : ∀ n, Function.Surjective (piMap (fun i : Fin n => F i))) :
    Function.Surjective (fun a : A => fun n => F n a) := by
  intro y
  have hclosed : ∀ n, IsClosed {a : A | ∀ i : Fin n, F i a = y i} := by
    intro n
    have heq : {a : A | ∀ i : Fin n, F i a = y i}
        = ⋂ i : Fin n, {a : A | F i a = y i} := by
      ext a; simp
    rw [heq]
    exact isClosed_iInter fun i => isClosed_eq (hcont i) continuous_const
  have hne : ∀ n, ({a : A | ∀ i : Fin n, F i a = y i}).Nonempty := by
    intro n
    obtain ⟨a, ha⟩ := hF n (fun i : Fin n => y i)
    exact ⟨a, fun i => congrFun ha i⟩
  have hanti : ∀ n, {a : A | ∀ i : Fin (n + 1), F i a = y i}
      ⊆ {a : A | ∀ i : Fin n, F i a = y i} := by
    intro n a ha i
    exact ha i.castSucc
  have hcomp : IsCompact {a : A | ∀ i : Fin 0, F i a = y i} := by
    have : {a : A | ∀ i : Fin 0, F i a = y i} = Set.univ := by ext a; simp
    rw [this]; exact isCompact_univ
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => {a : A | ∀ i : Fin n, F i a = y i}) hanti hne hcomp hclosed
  refine ⟨a, ?_⟩
  funext n
  exact (Set.mem_iInter.mp ha (n + 1)) ⟨n, Nat.lt_succ_self n⟩

end FIP

section FinSupp

variable (ℓ : ℕ)

/-- The submodule of finitely supported functions `ℕ → ZMod ℓ`. -/
def finSupp : Submodule (ZMod ℓ) (ℕ → ZMod ℓ) where
  carrier := {x | {n | x n ≠ 0}.Finite}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    refine (hx.union hy).subset ?_
    intro n hn
    simp only [Pi.add_apply, Set.mem_union, Set.mem_setOf_eq] at hn ⊢
    by_contra h
    push Not at h
    exact hn (by simp [h.1, h.2])
  smul_mem' := by
    intro c x hx
    refine hx.subset ?_
    intro n hn
    simp only [Set.mem_setOf_eq, Pi.smul_apply] at hn ⊢
    intro h
    exact hn (by simp [h])

theorem mem_finSupp {x : ℕ → ZMod ℓ} : x ∈ finSupp ℓ ↔ {n | x n ≠ 0}.Finite := Iff.rfl

/-- The finitely supported functions are dense in `ℕ → ZMod ℓ`. -/
theorem dense_finSupp : Dense (finSupp ℓ : Set (ℕ → ZMod ℓ)) := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro x
  rw [mem_closure_iff]
  intro o ho hxo
  obtain ⟨I, u, hu, hIu⟩ := isOpen_pi_iff.mp ho x hxo
  refine ⟨fun n => if n ∈ I then x n else 0, hIu (fun i hi => ?_), ?_⟩
  · rw [Finset.mem_coe] at hi
    rw [if_pos hi]
    exact (hu i hi).2
  · show {n | (if n ∈ I then x n else 0) ≠ 0}.Finite
    refine (I.finite_toSet).subset ?_
    intro n hn
    by_contra h
    rw [Finset.mem_coe] at h
    exact hn (if_neg h)

/-- There is a linear functional on `ℕ → ZMod ℓ` which vanishes on the finitely supported
functions and does not vanish on the constant function `1`. -/
theorem exists_functional_vanishing_finSupp [Fact ℓ.Prime] :
    ∃ g : (ℕ → ZMod ℓ) →ₗ[ZMod ℓ] ZMod ℓ,
      (∀ x ∈ finSupp ℓ, g x = 0) ∧ g (fun _ => 1) ≠ 0 := by
  have hu : (fun _ : ℕ => (1 : ZMod ℓ)) ∉ finSupp ℓ := by
    intro h
    rw [mem_finSupp] at h
    have hEq : {n : ℕ | (fun _ : ℕ => (1 : ZMod ℓ)) n ≠ 0} = Set.univ := by
      ext n; simp
    rw [hEq] at h
    exact h.not_infinite Set.infinite_univ
  obtain ⟨g, hg1, hmap⟩ :=
    Submodule.exists_dual_map_eq_bot_of_notMem (R := ZMod ℓ) (M := ℕ → ZMod ℓ)
      (p := finSupp ℓ) hu inferInstance
  refine ⟨g, fun x hx => ?_, hg1⟩
  have hmem : g x ∈ Submodule.map g (finSupp ℓ) := Submodule.mem_map_of_mem hx
  rw [hmap] at hmem
  simpa using hmem

/-- A linear functional vanishing on the dense submodule of finitely supported functions, and
nonzero on the constant function `1`, is not continuous. -/
theorem not_continuous_of_vanishing_finSupp {ℓ : ℕ} (g : (ℕ → ZMod ℓ) →ₗ[ZMod ℓ] ZMod ℓ)
    (hg : ∀ x ∈ finSupp ℓ, g x = 0) (hg1 : g (fun _ => 1) ≠ 0) :
    ¬ Continuous (g : (ℕ → ZMod ℓ) → ZMod ℓ) := by
  intro hc
  have hcl : IsClosed {x : ℕ → ZMod ℓ | g x = 0} := isClosed_eq hc continuous_const
  have hsub : (finSupp ℓ : Set (ℕ → ZMod ℓ)) ⊆ {x | g x = 0} := fun x hx => hg x hx
  have huniv : (Set.univ : Set (ℕ → ZMod ℓ)) ⊆ {x | g x = 0} := by
    rw [← (dense_finSupp ℓ).closure_eq]
    exact closure_minimal hsub hcl
  have htop : LinearMap.ker g = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    simpa using huniv (Set.mem_univ x)
  have hg0 : g = 0 := LinearMap.ker_eq_top.mp htop
  exact hg1 (by rw [hg0, LinearMap.zero_apply])

end FinSupp

section Conversion

/-- Regard a `ZMod ℓ`-linear functional on `Additive V` as a group homomorphism
`V →* Multiplicative (ZMod ℓ)`. -/
def toMulHom {V : Type*} [CommGroup V] {ℓ : ℕ} [Module (ZMod ℓ) (Additive V)]
    (f : Additive V →ₗ[ZMod ℓ] ZMod ℓ) : V →* Multiplicative (ZMod ℓ) where
  toFun := f
  map_one' := f.map_zero
  map_mul' := f.map_add

theorem toMulHom_ker_index {V : Type*} [CommGroup V] {ℓ : ℕ} [Fact ℓ.Prime]
    [Module (ZMod ℓ) (Additive V)]
    (f : Additive V →ₗ[ZMod ℓ] ZMod ℓ) (hf : f ≠ 0) : (toMulHom f).ker.index = ℓ := by
  have hrange : LinearMap.range f = ⊤ := Module.Dual.range_eq_top_of_ne_zero (f := f) hf
  have hsurj : Function.Surjective (toMulHom f) := by
    intro y
    have : y ∈ LinearMap.range f := by rw [hrange]; trivial
    obtain ⟨a, ha⟩ := this
    exact ⟨a, ha⟩
  rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ hsurj, Subgroup.card_top,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod ℓ) ≃ ZMod ℓ), Nat.card_zmod]

/-- Every `ZMod ℓ`-linear functional on `Additive V` is continuous, provided every subgroup of
`V` of index `ℓ` is open. -/
theorem continuous_toMulHom_of_linear {V : Type*} [CommGroup V] [TopologicalSpace V]
    [IsTopologicalGroup V] {ℓ : ℕ} [Fact ℓ.Prime] [Module (ZMod ℓ) (Additive V)]
    (hopen : ∀ H : Subgroup V, H.index = ℓ → IsOpen (H : Set V))
    (f : Additive V →ₗ[ZMod ℓ] ZMod ℓ) : Continuous (f : Additive V → ZMod ℓ) := by
  rcases eq_or_ne f 0 with h0 | h0
  · rw [h0]
    exact continuous_const
  · have := continuous_of_isOpen_ker (toMulHom f) (hopen _ (toMulHom_ker_index f h0))
    exact this

end Conversion


end Crux

open Crux

/-- **The crux.**  A compact Hausdorff abelian topological group of prime exponent `ℓ` in which
every subgroup of index `ℓ` is open is finite. -/
theorem cruxCompactExpPrimeFinite {V : Type*} [CommGroup V] [TopologicalSpace V]
    [IsTopologicalGroup V] [CompactSpace V] [T2Space V] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hexp : ∀ v : V, v ^ ℓ = 1)
    (hopen : ∀ H : Subgroup V, H.index = ℓ → IsOpen (H : Set V)) : Finite V := by
  classical
  by_contra hfin
  haveI : Infinite V := not_finite_iff_infinite.mp hfin
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  let A := Additive V
  haveI hInfA : Infinite A := ‹Infinite V›
  haveI hCompA : CompactSpace A := ‹CompactSpace V›
  haveI hT2A : T2Space A := ‹T2Space V›
  have hAexp : ∀ a : A, ℓ • a = 0 := by
    intro a
    induction a using Additive.rec with
    | ofMul v => simpa using congrArg Additive.ofMul (hexp v)
  haveI : Module (ZMod ℓ) A := AddCommGroup.zmodModule hAexp
  -- every nonzero vector is detected by a functional with value one
  have hex : ∀ a : A, a ≠ 0 → ∃ f : A →ₗ[ZMod ℓ] ZMod ℓ, f a = 1 := fun a ha =>
    Module.Projective.exists_dual_eq_one (ZMod ℓ) ha
  obtain ⟨F, hF⟩ := exists_surjective_prefix_family (A := A) (ℓ := ℓ) inferInstance hex
  have hcoe : ∀ n, Continuous ((F n) : A → ZMod ℓ) := fun n =>
    continuous_toMulHom_of_linear (V := V) (ℓ := ℓ) hopen (F n)
  have hsurjPsi : Function.Surjective (fun a : A => fun n => F n a) :=
    surjective_pi_of_prefix_surjective F hcoe hF
  have hcontPsi : Continuous (fun a : A => fun n => F n a) := by
    rw [continuous_pi_iff]
    exact hcoe
  have hquot : Topology.IsQuotientMap (fun a : A => fun n => F n a) :=
    Topology.IsQuotientMap.of_surjective_continuous hsurjPsi hcontPsi
  -- a functional on the product which is not continuous
  obtain ⟨g, hg0, hgu⟩ := exists_functional_vanishing_finSupp (ℓ := ℓ)
  have hgnotcont : ¬ Continuous (g : (ℕ → ZMod ℓ) → ZMod ℓ) :=
    not_continuous_of_vanishing_finSupp g hg0 hgu
  -- its pullback along the quotient is linear and surjective
  let φ : A →ₗ[ZMod ℓ] ZMod ℓ :=
    { toFun := fun a => g (fun n => F n a)
      map_add' := by
        intro a b
        have h : (fun n => F n (a + b)) = (fun n => F n a) + (fun n => F n b) := by
          funext n; simp
        rw [h, map_add]
      map_smul' := by
        intro c a
        have h : (fun n => F n (c • a)) = c • (fun n => F n a) := by
          funext n; simp
        show g (fun n => F n (c • a)) = c • g (fun n => F n a)
        rw [h, map_smul] }
  have hg_ne : g ≠ 0 := fun h => hgu (by rw [h, LinearMap.zero_apply])
  have hg_range : LinearMap.range g = ⊤ := Module.Dual.range_eq_top_of_ne_zero (f := g) hg_ne
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : y ∈ LinearMap.range g := by rw [hg_range]; trivial
    obtain ⟨z, hz⟩ := hy
    obtain ⟨a, ha⟩ := hsurjPsi z
    exact ⟨a, by
      show g (fun n => F n a) = y
      rw [show (fun n => F n a) = z from ha]
      exact hz⟩
  have hφne : φ ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := hφsurj 1
    rw [h0, LinearMap.zero_apply] at ha
    exact zero_ne_one ha
  have hφcont : Continuous (φ : A → ZMod ℓ) :=
    continuous_toMulHom_of_linear (V := V) (ℓ := ℓ) hopen φ
  have hgcont : Continuous (g : (ℕ → ZMod ℓ) → ZMod ℓ) := by
    rw [hquot.continuous_iff]
    exact hφcont
  exact hgnotcont hgcont

end NK.LocalTame
