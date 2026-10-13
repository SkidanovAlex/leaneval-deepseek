import Mathlib
import Submission.Work.DSM2p.N7a_flat_adjoin_of_flat_quot

-- `haveI` registers the flatness of a stage as a local instance for the equational criterion;
-- the style linter would suggest `have`, which does not feed instance resolution here.
set_option linter.style.haveILetI false

/-!
# `Work.DSM2p.N7_flat_iSup_adjoin`

Let `A → C → L` be commutative rings with `IsScalarTower A C L`, let `x : ℕ → L` be a sequence
which is *increasing* in the sense that `x j ∈ C[x (j+1)]` for all `j`, and let `f j ∈ C[X]` be such
that the kernel of `Polynomial.aeval (x j) : C[X] → L` is the principal ideal `(f j)`.  If the
"stages" `C[X]/(f j)` (equivalently, the subalgebras `C[x j]`) are flat over `A`, then the union
`⋃ j, C[x j]` is flat over `A`.

This is the flatness lemma of Ma's proof of the direct summand theorem: the union is the
*directed* union of the stages, and a filtered colimit of flat modules is flat.

## Structure of the proof

* `N7a_flat_adjoin_of_flat_quot` (a separate file) identifies each stage `↥(C[x j])` with the
  quotient `C[X] ⧸ (f j)` as an `A`-algebra and transfers flatness along the identification.
* `flat_iSup_subalgebra_of_flat` below is the filtered-union step: it is *not* special to
  polynomial algebras but holds for a monotone family of `C`-subalgebras of `L`, each flat over
  `A`.  Its proof is the equational criterion for flatness: a relation `∑ᵢ fᵢ • xᵢ = 0` involves
  finitely many elements, each of which lies in some stage; the finitely many stages have a common
  upper bound `N` (`ℕ` is a semilattice), the relation becomes a relation in the flat stage
  `↥(S N)`, where it is trivialised, and the trivialisation is transported back along the
  `A`-linear inclusion `↥(S N) ↪ ↥(⨆ i, S i)`.
-/

namespace Work.DSM2p

section UnionHelpers

/-- **Membership in a directed union of subalgebras.**  If `S : ι → Subalgebra R A` is directed and
`ι` is nonempty, then `⨆ i, S i` is the set-theoretic union, so a point lies in the supremum iff it
lies in one of the `S i`.

This is the pointwise form of `Subalgebra.coe_iSup_of_directed`. -/
theorem mem_iSup_subalgebra_of_directed {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {ι : Type*} [Nonempty ι] {S : ι → Subalgebra R A} (hS : Directed (· ≤ ·) S) {x : A} :
    x ∈ ⨆ i, S i ↔ ∃ i, x ∈ S i := by
  rw [← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed hS, Set.mem_iUnion]
  exact exists_congr fun i => SetLike.mem_coe

variable {A C L : Type*} [CommRing A] [CommRing C] [CommRing L]
  [Algebra A C] [Algebra C L] [Algebra A L] [IsScalarTower A C L]

/-- **The inclusion of a `C`-subalgebra is compatible with the `A`-structures.**  The `A`-algebra
structure on a `C`-subalgebra `S ⊆ L` is the one induced from `L` (via `IsScalarTower A C L`), so
the structure map of `S` is the restriction of `algebraMap A L`; equivalently, for `S ≤ T` the
inclusion `↥S ↪ ↥T` is `A`-linear.

This is the compatibility needed to make `Subalgebra.inclusion h` an `A`-linear map. -/
theorem inclusion_algebraMap {S T : Subalgebra C L} (h : S ≤ T) (a : A) :
    Subalgebra.inclusion h (algebraMap A ↥S a) = algebraMap A ↥T a :=
  Subtype.ext (by rw [Subalgebra.coe_inclusion]; rfl)

/-- The `A`-linear form of the previous lemma; in particular the inclusion sends the `A`-scalars of
`↥S` to the corresponding `A`-scalars inside `L`. -/
theorem inclusion_algebraMap_apply {S T : Subalgebra C L} (h : S ≤ T) (a : A) :
    ((Subalgebra.inclusion h (algebraMap A ↥S a) : ↥T) : L) = algebraMap A L a := by
  rw [inclusion_algebraMap h a]
  rfl

/-- The `A`-linear inclusion `↥(S N) ↪ ↥(⨆ i, S i)`; `Subalgebra.inclusion` is only a `C`-algebra
map, so we record the `A`-linear structure explicitly. -/
noncomputable def subalgebraInclLinearMap {ι : Type*} {S : ι → Subalgebra C L} (N : ι)
    (h : S N ≤ ⨆ i, S i) : ↥(S N) →ₗ[A] ↥(⨆ i, S i) where
  toFun := Subalgebra.inclusion h
  map_add' := fun a b => map_add (Subalgebra.inclusion h) a b
  map_smul' := fun a b => by
    show Subalgebra.inclusion h (a • b) = a • Subalgebra.inclusion h b
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, inclusion_algebraMap h a]

@[simp]
theorem subalgebraInclLinearMap_apply {ι : Type*} {S : ι → Subalgebra C L} (N : ι)
    (h : S N ≤ ⨆ i, S i) (y : ↥(S N)) :
    subalgebraInclLinearMap (A := A) (C := C) N h y = Subalgebra.inclusion h y := rfl

end UnionHelpers

section Union

variable {A C L : Type*} [CommRing A] [CommRing C] [CommRing L]
  [Algebra A C] [Algebra C L] [Algebra A L] [IsScalarTower A C L]

/-- **Flatness passes to a directed union of subalgebras.**  Let `A → C → L` be commutative rings
with `IsScalarTower A C L` and let `S : ι → Subalgebra C L` be a monotone family of `C`-subalgebras
of `L`, indexed by a nonempty semilattice.  If every `↥(S i)` is flat as an `A`-module (for the
`A`-module structure induced from `L`), then so is the union `↥(⨆ i, S i)`.

This is the filtered-colimit step of the flatness lemma; the proof is the equational criterion,
each individual relation living at a single stage because the family is directed. -/
theorem flat_iSup_subalgebra_of_flat {ι : Type*} [Nonempty ι] [SemilatticeSup ι]
    {S : ι → Subalgebra C L} (hS : Monotone S)
    (h : ∀ i, Module.Flat A ↥(S i)) : Module.Flat A ↥(⨆ i, S i) := by
  classical
  -- It suffices to make every relation in the union trivial (equational criterion for flatness).
  refine Module.Flat.of_forall_isTrivialRelation ?_
  intro l f x hx
  -- The monotone family is directed, since `ι` is a semilattice.
  have hdir : Directed (· ≤ ·) S := fun i j => ⟨i ⊔ j, hS le_sup_left, hS le_sup_right⟩
  -- Every entry of the relation lies in some stage of the family.
  choose n hn using fun i : Fin l =>
    (mem_iSup_subalgebra_of_directed hdir).mp (x i).2
  -- The finitely many stages have a common upper bound.
  have key : ∀ s : Finset (Fin l), ∃ N : ι, ∀ i ∈ s, n i ≤ N := by
    intro s
    induction s using Finset.induction with
    | empty => exact ⟨Classical.arbitrary ι, by simp⟩
    | insert a s _ ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨M, haM, hNM⟩ := exists_ge_ge (n a) N
      exact ⟨M, fun i hi => by
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact haM
        · exact (hN i hi).trans hNM⟩
  obtain ⟨N, hN⟩ : ∃ N : ι, ∀ i : Fin l, n i ≤ N := by simpa using key Finset.univ
  -- The `i`-th element, viewed in the stage `N`.
  let z : Fin l → ↥(S N) := fun i => ⟨(x i : L), hS (hN i) (hn i)⟩
  -- The (`A`-linear) inclusion of that stage into the union.
  let inclTop : ↥(S N) →ₗ[A] ↥(⨆ i, S i) := subalgebraInclLinearMap (A := A) (C := C) N (le_iSup S N)
  have hinj : Function.Injective inclTop := by
    intro a b hab
    have h : (a : L) = (b : L) := by
      have h' := congrArg (fun t : ↥(⨆ i, S i) => (t : L)) hab
      simpa [inclTop] using h'
    exact Subtype.ext h
  have hzx : ∀ i, inclTop (z i) = x i := fun _ => Subtype.ext rfl
  -- The relation, pushed to the stage `N`, is a relation in the flat module `↥(S N)`.
  have hzw : ∑ i, f i • z i = 0 := by
    apply hinj
    rw [map_zero]
    have h1 : inclTop (∑ i, f i • z i) = ∑ i, f i • x i := by
      simp only [map_sum, map_smul, hzx]
    rw [h1, hx]
  -- It is trivial there.
  haveI : Module.Flat A ↥(S N) := h N
  obtain ⟨k, aa, yy, hdec, hrel⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (f := f) (x := z) hzw
  -- Transport the trivialisation along the inclusion into the union.
  refine ⟨k, aa, fun j => inclTop (yy j), fun i => ?_, hrel⟩
  calc x i = inclTop (z i) := (hzx i).symm
    _ = inclTop (∑ j, aa i j • yy j) := by rw [hdec i]
    _ = ∑ j, aa i j • inclTop (yy j) := by
      simp only [map_sum, map_smul]

end Union

theorem N7_flat_iSup_adjoin {A C L : Type*} [CommRing A] [CommRing C] [CommRing L]
    [Algebra A C] [Algebra C L] [Algebra A L] [IsScalarTower A C L]
    (x : ℕ → L) (hmono : ∀ j, x j ∈ Algebra.adjoin C {x (j + 1)}) (f : ℕ → Polynomial C)
    (hker : ∀ j, RingHom.ker (Polynomial.aeval (R := C) (x j)).toRingHom = Ideal.span {f j})
    (hflat : ∀ j, Module.Flat A (Polynomial C ⧸ Ideal.span {f j})) :
    Module.Flat A ↥(⨆ j, Algebra.adjoin C {x j}) := by
  -- The hypothesis `x j ∈ C[x (j+1)]` says exactly that the family of stages is monotone.
  have hstep : ∀ j, Algebra.adjoin C {x j} ≤ Algebra.adjoin C {x (j + 1)} := fun j =>
    Algebra.adjoin_le (by simpa using hmono j)
  have hS : Monotone fun j => Algebra.adjoin C {x j} := monotone_nat_of_le_succ hstep
  -- Each stage is flat over `A`, being the quotient `C[X] ⧸ (f j)`.
  have hstage : ∀ j, Module.Flat A ↥(Algebra.adjoin C {x j}) := fun j =>
    N7a_flat_adjoin_of_flat_quot (x j) (f j) (hker j) (hflat j)
  exact flat_iSup_subalgebra_of_flat hS hstage

end Work.DSM2p
