import Mathlib
import Submission.Work.Lattice.JoinSubmodularity
import Submission.Commons.LinearAlgebra.FreeModule.basis_extend_of_quotient_free
import Submission.Commons.Data.Fin.split_equiv_image_first

/-!
# (i-b) Aligned ℤ-bases for saturated pairs (the aligned-basis glue)

Roadmap item (i): for a full-rank lattice `Λ ≤ ℝᵈ` and **saturated** subgroups
`V, W ≤ Λ`, produce the aligned ambient families realising the flag of the pair
(`span(range u) = V ⊓ W`, `span(range (u++x)) = V`, `span(range (u++y)) = W`,
`span(range (u++x++y)) = V ⊔ W`) so that the proven engine
`JoinSubmodularity.logCovol_submodularity_aligned` instantiates.

**Route (recorded).**  `N := V ⊓ W` is saturated (`saturated_inf`) and pure in `V`
(`pure_inf_left`), so the quotient `V ⧸ N` is torsion-free over `ℤ`, hence free.
This module performs the V-side construction: view `M := ↥V` with
`N̂ := N.comap V.subtype ≤ ↥V` (≅ `↥N` via `comapSubtypeEquivOfLe`), obtain a `ℤ`-basis
of `↥V` extending the basis of `N̂` by the delegated
`Commons.LinearAlgebra.FreeModule.basis_extend_of_quotient_free`, coercing to the
ambient families at the end.  The `W`-side is symmetric, and the sum-side follows from
the two bases of `V` and `W`.

All declarations are Mathlib + Submission (JoinSubmodularity/IntrinsicIndex/
GraysonLattice/MixedRankSpectrum) + the Commons basis-extension lemma.
-/

noncomputable section

open Set Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Submission.AlignedBases

open Submission.GraysonData
open Submission.GraysonLattice
open Submission.IntrinsicIndex
open Submission.MixedRankSpectrum
open Submission.JoinSubmodularity
open Commons.LinearAlgebra.FreeModule
open Commons.Data.Fin

/-- The submodule of `↥V` corresponding to an ambient subgroup `N ≤ V`: the elements of
`V` whose ambient value lies in `N`. -/
abbrev Nhat {d : ℕ} (V N : Submodule ℤ (E d)) : Submodule ℤ (↥V) :=
  N.comap V.subtype

/-- `↥(N̂)` is linearly equivalent to `↥N` when `N ≤ V` (each is the set of `N`-points). -/
noncomputable def Nhat_equiv {d : ℕ} {V N : Submodule ℤ (E d)} (hNV : N ≤ V) :
    (Nhat V N ≃ₗ[ℤ] N) :=
  Submodule.comapSubtypeEquivOfLe (p := N) (q := V) hNV

/-- The quotient `↥V ⧸ N̂` is torsion-free over `ℤ` when `N` is pure in the ambient `V`
(`Pure V N`): `r • (Quotient.mk x) = r • (Quotient.mk y)` forces `x − y ∈ N̂` by purity,
so `mk x = mk y`.  (Over the domain `ℤ` regular scalars are exactly the nonzero ones.) -/
lemma quotient_torsionFree_of_pure {d : ℕ} (V N : Submodule ℤ (E d))
    (hN : Pure V N) : Module.IsTorsionFree ℤ (↥V ⧸ Nhat V N) := by
  classical
  constructor
  intro r hr
  have hr0 : r ≠ 0 := (isRegular_iff_ne_zero (R := ℤ)).mp hr
  intro a b hsmul
  rcases Submodule.Quotient.mk_surjective (Nhat V N) a with ⟨x, rfl⟩
  rcases Submodule.Quotient.mk_surjective (Nhat V N) b with ⟨y, rfl⟩
  -- a = mk x, b = mk y; hsmul : (r : ℤ) • mk x = (r : ℤ) • mk y
  have hxy' : Submodule.Quotient.mk (p := Nhat V N) (((r : ℤ) • x) : ↥V) =
      Submodule.Quotient.mk (p := Nhat V N) (((r : ℤ) • y) : ↥V) := by
    exact hsmul
  have hmemN : V.subtype ((((r : ℤ) • x : ↥V) - ((r : ℤ) • y : ↥V))) ∈ N :=
    Submodule.mem_comap.mp ((Submodule.Quotient.eq (Nhat V N)).mp hxy')
  -- the ambient value of the ℤ-smul/difference on ↥V is the ambient smul/difference of
  -- the values (V.subtype is ℤ-linear and the coercion is its action)
  have hxV : (((x : ↥V) : E d) ∈ V) := (x : ↥V).2
  have hyV : (((y : ↥V) : E d) ∈ V) := (y : ↥V).2
  have hsubE : (r : ℤ) • (((x : ↥V) : E d) - ((y : ↥V) : E d)) ∈ N := by
    have hval : V.subtype (((r : ℤ) • (x - y)) : ↥V) =
        (r : ℤ) • (((x : ↥V) : E d) - ((y : ↥V) : E d)) := by
      calc
        V.subtype (((r : ℤ) • (x - y)) : ↥V) = (r : ℤ) • V.subtype (x - y) := by rw [map_smul]
        _ = (r : ℤ) • (V.subtype x - V.subtype y) := by rw [map_sub]
        _ = (r : ℤ) • V.subtype x - (r : ℤ) • V.subtype y := by rw [smul_sub]
        _ = (r : ℤ) • (((x : ↥V) : E d)) - (r : ℤ) • (((y : ↥V) : E d)) := by
              rfl
        _ = (r : ℤ) • (((x : ↥V) : E d) - ((y : ↥V) : E d)) := by rw [smul_sub]
    have hval2 : V.subtype (((r : ℤ) • (x - y)) : ↥V) =
        V.subtype ((((r : ℤ) • x : ↥V) - ((r : ℤ) • y : ↥V))) := by
      calc
        V.subtype (((r : ℤ) • (x - y)) : ↥V) = (r : ℤ) • V.subtype (x - y) := by rw [map_smul]
        _ = (r : ℤ) • (V.subtype x - V.subtype y) := by rw [map_sub]
        _ = (r : ℤ) • V.subtype x - (r : ℤ) • V.subtype y := by rw [smul_sub]
        _ = V.subtype (((r : ℤ) • x : ↥V)) - V.subtype (((r : ℤ) • y : ↥V)) := by
              rw [← map_smul, ← map_smul]
        _ = V.subtype ((((r : ℤ) • x : ↥V) - ((r : ℤ) • y : ↥V))) := by rw [← map_sub]
    have hsubN : ((r : ℤ) • (x - y) : ↥V) ∈ Nhat V N := Submodule.mem_comap.mpr (by
      rw [hval2]
      exact hmemN)
    rw [← hval]
    exact Submodule.mem_comap.mp hsubN
  have hxyE : (((x : ↥V) : E d) - ((y : ↥V) : E d)) ∈ N := by
    exact hN.2 (((x : ↥V) : E d) - ((y : ↥V) : E d)) (Submodule.sub_mem V hxV hyV)
      ⟨r, hr0, hsubE⟩
  exact (Submodule.Quotient.eq (Nhat V N)).mpr (Submodule.mem_comap.mpr (by
    simpa using hxyE))

/-- A `ℤ`-basis of `N̂` (the submodule of `↥V` of `N`-points) from a `ℤ`-basis of the
ambient subgroup `N` (`N ≤ V`): map through the equivalence `Nhat_equiv`. -/
noncomputable def Nhat_basis {d : ℕ} {V N : Submodule ℤ (E d)} {ι : Type*} (hNV : N ≤ V)
    (bN : Module.Basis ι ℤ N) : Module.Basis ι ℤ (Nhat V N) :=
  bN.map (Nhat_equiv (V := V) (N := N) hNV).symm

/-- Coercing a basis of `N̂` to ambient gives the same values as coercing the
corresponding basis of `N` (both are the `N`-vectors of `bN`): for the basis produced by
`Nhat_basis`, `((Nhat_basis hNV bN) i : E d) = (bN i : E d)`. -/
lemma Nhat_basis_val {d : ℕ} {V N : Submodule ℤ (E d)} {ι : Type*} (hNV : N ≤ V)
    (bN : Module.Basis ι ℤ N) (i : ι) :
    (((Nhat_basis hNV bN i : Nhat V N) : E d) = (bN i : E d)) := by
  classical
  dsimp [Nhat_basis]
  unfold Nhat_equiv
  rw [Submodule.comapSubtypeEquivOfLe_symm_apply]

/-- **Extension of a GIVEN intersection basis (i-b-1′)**: as
`exists_extended_basis_intersection`, but the `ℤ`-basis `bN` of `N` is supplied by the
caller — so that the `V`-side and the `W`-side of a saturated pair can be built from the
SAME basis of `N = V ⊓ W` (the alignment that makes the two-sided construction work).
Let `Λ` be a full-rank lattice, `N ≤ V ≤ Λ` ambient subgroups with `V ≠ ⊥ ≠ N` and `N`
pure in `V` (`Pure V N`).  Then the given basis `bN : Basis (Fin m) ℤ N` extends to a
`ℤ`-basis `bV` of `↥V`, with the `N`-part as an initial segment:
`(Nhat_basis hNV bN i : ↥V) = bV (e i)`. -/
theorem extend_given_basis_intersection {d m : ℕ} (Λ V N : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    (hVΛ : V ≤ Λ) (hNV : N ≤ V) (hV0 : V ≠ ⊥) (_hN0 : N ≠ ⊥) (hN : Pure V N)
    (bN : Module.Basis (Fin m) ℤ N) :
    ∃ n : ℕ, ∃ bV : Module.Basis (Fin n) ℤ (↥V), ∃ e : Fin m ↪ Fin n,
      ∀ i : Fin m, ((Nhat_basis hNV bN i : Nhat V N) : ↥V) = bV (e i) := by
  classical
  let rV : ℕ := subDim V
  -- a certified ambient ℤ-family of V (only to get the finiteness of `↥V`)
  rcases exists_basis_family_int_of_le_lattice (d := d) Λ hΛfin V hVΛ hV0 with
    ⟨cV, _hliV, hzliV, _hmemVΛ, hVspan⟩
  have hmemV : ∀ i : Fin rV, cV i ∈ V := by
    intro i
    rw [hVspan]
    exact Submodule.subset_span (s := Set.range cV) ⟨i, rfl⟩
  let bV0 : Module.Basis (Fin rV) ℤ (↥V) := basis_of_family (M := V) cV hmemV hzliV hVspan
  -- the basis of the N̂-points of V
  let bNhat : Module.Basis (Fin m) ℤ (Nhat V N) := Nhat_basis hNV bN
  -- ↥V is finite over ℤ (from bV0); so is the quotient ↥V ⧸ N̂
  haveI : Module.Finite ℤ (↥V) := Module.Finite.of_basis bV0
  haveI : Module.Finite ℤ (↥V ⧸ Nhat V N) := inferInstance
  -- the quotient is torsion-free (N pure in V)
  haveI : Module.IsTorsionFree ℤ (↥V ⧸ Nhat V N) := quotient_torsionFree_of_pure V N hN
  rcases (Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := ↥V ⧸ Nhat V N)) with ⟨k, bQ⟩
  -- L84: extend bNhat to a basis bV of ↥V
  rcases basis_extend_of_quotient_free (R := ℤ) (M := ↥V) (N := Nhat V N)
    (ι := Fin m) (bN := bNhat) (κ := Fin k) (bQ := bQ) with ⟨n, bV, e, h⟩
  exact ⟨n, bV, e, h⟩

/-- **V-side extension of the intersection basis (i-b-1)**: let `Λ` be a full-rank
lattice, `N ≤ V ≤ Λ` ambient subgroups with `V ≠ ⊥ ≠ N` and `N` pure in `V` (`Pure V N`,
e.g. `N = V ⊓ W` with `W` saturated — `JoinSubmodularity.pure_inf_left`).  Then there
are `m`, a `ℤ`-basis `bN̂ : Basis (Fin m) ℤ (Nhat V N)` of the `N`-points of `V`, and a
`ℤ`-basis `bV` of `↥V` extending it (`(bN̂ i : ↥V) = bV (e i)` for all `i`). -/
theorem exists_extended_basis_intersection {d : ℕ} (Λ V N : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    (hVΛ : V ≤ Λ) (hNV : N ≤ V) (hV0 : V ≠ ⊥) (hN0 : N ≠ ⊥) (hN : Pure V N) :
    ∃ m : ℕ, ∃ bNhat : Module.Basis (Fin m) ℤ (Nhat V N),
      ∃ n : ℕ, ∃ bV : Module.Basis (Fin n) ℤ (↥V), ∃ e : Fin m ↪ Fin n,
        ∀ i : Fin m, (bNhat i : ↥V) = bV (e i) := by
  classical
  let rN : ℕ := subDim N
  have hNΛ : N ≤ Λ := le_trans hNV hVΛ
  rcases exists_basis_family_int_of_le_lattice (d := d) Λ hΛfin N hNΛ hN0 with
    ⟨cN, _hliN, hzliN, _hmemNΛ, hNspan⟩
  have hmemN : ∀ i : Fin rN, cN i ∈ N := by
    intro i
    rw [hNspan]
    exact Submodule.subset_span (s := Set.range cN) ⟨i, rfl⟩
  let bN : Module.Basis (Fin rN) ℤ N := basis_of_family (M := N) cN hmemN hzliN hNspan
  let bNhat : Module.Basis (Fin rN) ℤ (Nhat V N) := Nhat_basis hNV bN
  rcases extend_given_basis_intersection (d := d) (m := rN) Λ V N hΛfin hVΛ hNV hV0 hN0 hN bN
    with ⟨n, bV, e, h⟩
  exact ⟨rN, bNhat, n, bV, e, h⟩

/-! ## Ambient families from bases of subgroups (i-b-2, part 1)

For a `ℤ`-basis `b : Basis ι ℤ (↥X)` of an ambient subgroup `X ≤ E d`, the coerced
family `i ↦ (b i : E d)` spans `X` over `ℤ` (`span_ambient_of_basis`), is `ℤ`-linearly
independent (`li_ambient_of_basis`), and — when `X ≤ Λ` is a subgroup of the full-rank
lattice — `ℝ`-linearly independent (`li_real_ambient_of_basis`, via the
ℤ-independence + lattice-membership transfer). -/

/-- The ambient coercion of a `ℤ`-basis of `X ≤ E d` spans `X` over `ℤ`. -/
lemma span_ambient_of_basis {d : ℕ} (X : Submodule ℤ (E d)) {ι : Type*} [Fintype ι]
    (bX : Module.Basis ι ℤ (↥X)) :
    Submodule.span ℤ (Set.range (fun i : ι => ((bX i : ↥X) : E d))) = X := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact (bX i : ↥X).2
  · intro x hx
    let xX : ↥X := ⟨x, hx⟩
    have hsum := bX.sum_repr xX
    have hlin : X.subtype (∑ i : ι, bX.repr xX i • (bX i : ↥X)) = x := by
      calc
        X.subtype (∑ i : ι, bX.repr xX i • (bX i : ↥X)) = X.subtype xX := congrArg X.subtype hsum
        _ = x := by rfl
    have hpush : X.subtype (∑ i : ι, bX.repr xX i • (bX i : ↥X)) =
        ∑ i : ι, bX.repr xX i • ((bX i : ↥X) : E d) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul]
      rfl
    have hxsum : (∑ i : ι, (bX.repr xX i) • ((bX i : ↥X) : E d)) = x := by
      exact hpush.symm.trans hlin
    rw [← hxsum]
    exact Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _
      (Submodule.subset_span (s := Set.range (fun i : ι => ((bX i : ↥X) : E d))) ⟨i, rfl⟩))

/-- The ambient coercion of a `ℤ`-basis of `X` is `ℤ`-linearly independent (pull back a
vanishing `ℤ`-combination through the injective subtype inclusion `X.subtype`). -/
lemma li_ambient_of_basis {d : ℕ} (X : Submodule ℤ (E d)) {ι : Type*} [Fintype ι]
    (bX : Module.Basis ι ℤ (↥X)) :
    LinearIndependent ℤ (fun i : ι => ((bX i : ↥X) : E d)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  -- hc : ∑ i, c i • ((bX i : ↥X) : E d) = 0 ; pull back through the injective X.subtype
  have hzero : X.subtype (∑ i : ι, c i • (bX i : ↥X)) = 0 := by
    rw [map_sum]
    calc
      (∑ i : ι, X.subtype (c i • (bX i : ↥X))) = ∑ i : ι, c i • X.subtype (bX i) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [map_smul]
      _ = ∑ i : ι, c i • ((bX i : ↥X) : E d) := by
            apply Finset.sum_congr rfl
            intro i hi
            rfl
      _ = 0 := by simpa using hc
  have hlin : (∑ i : ι, c i • (bX i : ↥X)) = 0 := by
    have hker : (∑ i : ι, c i • (bX i : ↥X)) ∈ LinearMap.ker X.subtype := by
      rw [LinearMap.mem_ker]
      exact hzero
    have hk : LinearMap.ker X.subtype = ⊥ := Submodule.ker_subtype X
    simpa [Submodule.mem_bot] using (by rwa [hk] at hker)
  exact (Fintype.linearIndependent_iff.mp bX.linearIndependent) c hlin i

/-- The ambient coercion of a `ℤ`-basis of a subgroup `X ≤ Λ` of the full-rank lattice
`Λ` is `ℝ`-linearly independent. -/
lemma li_real_ambient_of_basis {d n : ℕ} (Λ X : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (hXΛ : X ≤ Λ)
    (bX : Module.Basis (Fin n) ℤ (↥X)) :
    LinearIndependent ℝ (fun i : Fin n => ((bX i : ↥X) : E d)) := by
  exact linearIndependent_real_of_mem_lattice (d := d) Λ hΛfin
    (fun i : Fin n => ((bX i : ↥X) : E d))
    (by intro i; exact hXΛ (bX i).2)
    (li_ambient_of_basis X bX)

/-- The ambient-coerced family of `Nhat_basis` agrees with the ambient-coerced family of
the underlying basis of `N` pointwise (`Nhat_basis_val` restated for the `↥V`-coerced
values). -/
lemma Nhat_basis_val' {d : ℕ} {V N : Submodule ℤ (E d)} {ι : Type*} (hNV : N ≤ V)
    (bN : Module.Basis ι ℤ N) (i : ι) :
    (((Nhat_basis hNV bN i : Nhat V N) : ↥V) : E d) = (bN i : E d) :=
  Nhat_basis_val hNV bN i

/-- The span of the `u`-family of an extended basis is exactly `N = V ⊓ W`: the initial
segment of the extended basis (the `Nhat`-basis, agreeing ambiently with the `N`-basis)
spans `N`. -/
lemma span_initial_of_extension {d m n : ℕ} (V N : Submodule ℤ (E d))
    (bN : Module.Basis (Fin m) ℤ N) (bV : Module.Basis (Fin n) ℤ (↥V))
    (hNV : N ≤ V) (e : Fin m ↪ Fin n)
    (h : ∀ i : Fin m, ((Nhat_basis hNV bN i : Nhat V N) : ↥V) = bV (e i)) :
    Submodule.span ℤ (Set.range (fun i : Fin m => ((bV (e i) : ↥V) : E d))) = N := by
  classical
  -- the initial-segment ambient values equal the ambient values of the N-basis
  have hval : ∀ i : Fin m, ((bV (e i) : ↥V) : E d) = (bN i : E d) := by
    intro i
    rw [← h i]
    exact Nhat_basis_val hNV bN i
  calc
    Submodule.span ℤ (Set.range (fun i : Fin m => ((bV (e i) : ↥V) : E d)))
        = Submodule.span ℤ (Set.range (fun i : Fin m => ((bV (e i) : ↥V) : E d))) := rfl
    _ = Submodule.span ℤ (Set.range (fun i : Fin m => (bN i : E d))) := by
          congr 1
          ext y
          constructor
          · rintro ⟨i, rfl⟩
            refine ⟨i, ?_⟩
            exact (hval i).symm
          · rintro ⟨i, rfl⟩
            refine ⟨i, ?_⟩
            exact hval i
    _ = N := span_ambient_of_basis N bN

/-- Every element of `Fin (m + a)` is either `Fin.castAdd a i` (`i : Fin m`) or
`Fin.natAdd m k` (`k : Fin a`). -/
lemma fin_eq_castAdd_or_natAdd {m a : ℕ} (j : Fin (m + a)) :
    (∃ i : Fin m, j = Fin.castAdd a i) ∨ (∃ k : Fin a, j = Fin.natAdd m k) := by
  by_cases h : j.val < m
  · left
    refine ⟨⟨j.val, h⟩, ?_⟩
    apply Fin.ext
    simp [Fin.castAdd]
  · right
    have hge : m ≤ j.val := le_of_not_gt h
    have hlt : j.val - m < a := by
      have hj : j.val < m + a := j.isLt
      omega
    refine ⟨⟨j.val - m, hlt⟩, ?_⟩
    apply Fin.ext
    simp [Fin.natAdd]
    omega

/-- **Ambient split family for the V-side (i-b-2)**: from a `ℤ`-basis `bV` of `↥V` and a
`ℤ`-basis `bN` of `N ≤ V` embedded as the initial segment `(bNhat i : ↥V) = bV (e i)`,
produce the ambient families `u` (indexed `Fin m`, spanning `N`) and `x` (indexed
`Fin (n - m)`, completing to a `ℤ`-basis of `V`) such that `Fin.append u x` is the
ambient family of `bV` (up to the split permutation), hence spans `V` and is
`ℤ`-independent (and `ℝ`-independent when `V ≤ Λ`). -/
theorem exists_ambient_split_V {d m n : ℕ} (Λ V N : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    (hVΛ : V ≤ Λ) (bN : Module.Basis (Fin m) ℤ N) (bV : Module.Basis (Fin n) ℤ (↥V))
    (hNV : N ≤ V) (e : Fin m ↪ Fin n)
    (h : ∀ i : Fin m, ((Nhat_basis hNV bN i : Nhat V N) : ↥V) = bV (e i)) :
    ∃ u : Fin m → E d, ∃ x : Fin (n - m) → E d,
      Submodule.span ℤ (Set.range u) = N ∧
      Submodule.span ℤ (Set.range (Fin.append u x)) = V ∧
      LinearIndependent ℤ (Fin.append u x) ∧
      LinearIndependent ℝ (Fin.append u x) := by
  classical
  have hmn : m ≤ n := by
    simpa using (Fintype.card_le_of_injective e e.injective)
  rcases split_equiv_image_first (m := m) (n := n) hmn e with ⟨ρ, hρ1, _hρ2, _hρ3⟩
  let a : ℕ := n - m
  let u : Fin m → E d := fun i => ((bV (e i : Fin n) : ↥V) : E d)
  let x : Fin a → E d := fun k => ((bV (ρ (Fin.natAdd m k) : Fin n) : ↥V) : E d)
  have hspanN : Submodule.span ℤ (Set.range u) = N := by
    dsimp [u]
    exact span_initial_of_extension V N bN bV hNV e h
  have hgeq : Fin.append u x = fun j : Fin (m + a) => ((bV (ρ j : Fin n) : ↥V) : E d) := by
    funext j
    rcases fin_eq_castAdd_or_natAdd (m := m) (a := a) j with ⟨i, rfl⟩ | ⟨k, rfl⟩
    · simp [u, x, Fin.append_left]
      -- goal: (bV (e i) : E d) = (bV (ρ (Fin.castAdd a i)) : E d)
      rw [hρ1]
    · simp [u, x, Fin.append_right]
  have hrange : Set.range (fun j : Fin (m + a) => ((bV (ρ j : Fin n) : ↥V) : E d)) =
      Set.range (fun k : Fin n => ((bV k : ↥V) : E d)) := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨ρ j, rfl⟩
    · rintro ⟨k, rfl⟩
      refine ⟨ρ.symm k, ?_⟩
      change ((bV (ρ (ρ.symm k)) : ↥V) : E d) = ((bV k : ↥V) : E d)
      rw [Equiv.apply_symm_apply ρ k]
  have hspanV : Submodule.span ℤ (Set.range (Fin.append u x)) = V := by
    rw [hgeq, hrange]
    exact span_ambient_of_basis V bV
  have hliZ : LinearIndependent ℤ (Fin.append u x) := by
    have hbase := li_ambient_of_basis V bV
    -- hbase : LI ℤ (fun k : Fin n => ((bV k : ↥V) : E d)); compose with ρ
    have hliρ : LinearIndependent ℤ (fun j : Fin (m + a) => ((bV (ρ j : Fin n) : ↥V) : E d)) :=
      hbase.comp ρ ρ.injective
    simpa [hgeq] using hliρ
  -- ℝ-LI: ℤ-independent members of the lattice Λ are ℝ-independent
  have hmem : ∀ j : Fin (m + (n - m)), (Fin.append u x) j ∈ (Λ : Set (E d)) := by
    intro j
    rcases fin_eq_castAdd_or_natAdd (m := m) (a := n - m) j with ⟨i, rfl⟩ | ⟨k, rfl⟩
    · rw [Fin.append_left]
      dsimp [u]
      exact hVΛ (bV (e i : Fin n)).2
    · rw [Fin.append_right]
      dsimp [x]
      exact hVΛ (bV (ρ (Fin.natAdd m k) : Fin n)).2
  have hliR : LinearIndependent ℝ (Fin.append u x) :=
    linearIndependent_real_of_mem_lattice (d := d) Λ hΛfin (Fin.append u x) hmem hliZ
  exact ⟨u, x, hspanN, hspanV, hliZ, hliR⟩

/-! ## (i-b-3) Alignment and the combined (join) span

The V-side and W-side splits share the SAME ambient family `u` on the intersection part:
both are built from the single `ℤ`-basis `bN` of `N = V ⊓ W` (the embedding condition
`(Nhat_basis hNV bN i : ↥V) = bV (e i)` together with `Nhat_basis_val` force the ambient
values to be `(bN i : E d)` on both sides).  And the combined family
`(u ++ x) ++ y` spans the join `V ⊔ W`. -/

/-- The ambient value of an initial-segment vector of an extended basis equals the
ambient value of the corresponding `N`-basis vector: `(bV (e i) : E d) = (bN i : E d)`.
This is the alignment that makes the `u` of the V-side and W-side splits the SAME
family. -/
lemma initial_val_eq_bN {d m n : ℕ} (V N : Submodule ℤ (E d))
    (bN : Module.Basis (Fin m) ℤ N) (bV : Module.Basis (Fin n) ℤ (↥V))
    (hNV : N ≤ V) (e : Fin m ↪ Fin n)
    (h : ∀ i : Fin m, ((Nhat_basis hNV bN i : Nhat V N) : ↥V) = bV (e i)) (i : Fin m) :
    ((bV (e i : Fin n) : ↥V) : E d) = (bN i : E d) := by
  rw [← h i]
  exact Nhat_basis_val hNV bN i

/-- The ambient family of the whole `Fin.append`-concatenation ranges over the union of
the two ranges (`range (append z w) = range z ∪ range w`). -/
lemma range_append {α : Type*} {m n : ℕ} (z : Fin m → α) (w : Fin n → α) :
    Set.range (Fin.append z w) = Set.range z ∪ Set.range w := by
  ext y
  constructor
  · rintro ⟨j, rfl⟩
    rcases fin_eq_castAdd_or_natAdd (m := m) (a := n) j with ⟨i, rfl⟩ | ⟨k, rfl⟩
    · left; refine ⟨i, ?_⟩; simp
    · right; refine ⟨k, ?_⟩; simp
  · rintro (⟨i, rfl⟩ | ⟨k, rfl⟩)
    · refine ⟨Fin.castAdd n i, ?_⟩; simp
    · refine ⟨Fin.natAdd m k, ?_⟩; simp

/-- **Combined span = join**: if `span(range (u ++ x)) = V` and
`span(range (u ++ y)) = W`, then the combined family `(u ++ x) ++ y` spans `V ⊔ W`
(=`V + W` as `ℤ`-submodules): the join of the spans of two families equals the span of
the union of their generators. -/
lemma span_append_join {d m a b : ℕ} (V W : Submodule ℤ (E d))
    (u : Fin m → E d) (x : Fin a → E d) (y : Fin b → E d)
    (hV : Submodule.span ℤ (Set.range (Fin.append u x)) = V)
    (hW : Submodule.span ℤ (Set.range (Fin.append u y)) = W) :
    Submodule.span ℤ (Set.range (Fin.append (Fin.append u x) y)) = V ⊔ W := by
  classical
  -- range((u++x)++y) = range(u++x) ∪ range y, etc.
  have hr1 : Set.range (Fin.append (Fin.append u x) y) =
      Set.range (Fin.append u x) ∪ Set.range y := range_append (Fin.append u x) y
  have hr2 : Set.range (Fin.append u x) = Set.range u ∪ Set.range x := range_append u x
  have hr3 : Set.range (Fin.append u y) = Set.range u ∪ Set.range y := range_append u y
  -- range(u++x) ∪ range y = range u ∪ (range x ∪ range y): re-associate
  have hA : Set.range (Fin.append u x) ∪ Set.range y =
      Set.range u ∪ (Set.range x ∪ Set.range y) := by
    rw [hr2]
    ext z
    simp only [Set.mem_union]
    tauto
  -- range(u++x) ∪ range(u++y) = range u ∪ (range x ∪ range y): absorb the middle u
  have hC : Set.range (Fin.append u x) ∪ Set.range (Fin.append u y) =
      Set.range u ∪ (Set.range x ∪ Set.range y) := by
    rw [hr2, hr3]
    ext z
    simp only [Set.mem_union]
    tauto
  calc
    Submodule.span ℤ (Set.range (Fin.append (Fin.append u x) y))
        = Submodule.span ℤ (Set.range (Fin.append u x) ∪ Set.range y) := by rw [hr1]
    _ = Submodule.span ℤ (Set.range u ∪ (Set.range x ∪ Set.range y)) := by rw [hA]
    _ = Submodule.span ℤ (Set.range (Fin.append u x) ∪ Set.range (Fin.append u y)) := by
          rw [← hC]
    _ = Submodule.span ℤ (Set.range (Fin.append u x)) ⊔
        Submodule.span ℤ (Set.range (Fin.append u y)) := by rw [Submodule.span_union]
    _ = V ⊔ W := by rw [hV, hW]


/-- **Ambient completion with the canonical shared family (i-b-2/3)**: given a `ℤ`-basis
`bN` of `N ≤ V`, a `ℤ`-basis `bV` of `↥V` extending it (`(Nhat_basis hNV bN i : ↥V) =
bV (e i)`) and `V ≤ Λ` full-rank, the CANONICAL ambient family
`u := fun i => ((bN i : ↥N) : E d)` spans `N`, and there is `x : Fin (n-m) → E d`
completing it so that `span(range (u ++ x)) = V` with `u ++ x` both `ℤ`- and
`ℝ`-independent.

Writing the witness family literally as the canonical `ambient ∘ bN` (rather than
existentially) is what allows the `V`-side and the `W`-side of a pair to use the SAME
`u`: both completions are stated with the same expression, so no transport is needed. -/
theorem exists_ambient_completion {d m n : ℕ} (Λ V N : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    (hVΛ : V ≤ Λ) (bN : Module.Basis (Fin m) ℤ N) (bV : Module.Basis (Fin n) ℤ (↥V))
    (hNV : N ≤ V) (e : Fin m ↪ Fin n)
    (h : ∀ i : Fin m, ((Nhat_basis hNV bN i : Nhat V N) : ↥V) = bV (e i)) :
    ∃ x : Fin (n - m) → E d,
      Submodule.span ℤ (Set.range (fun i : Fin m => ((bN i : ↥N) : E d))) = N ∧
      Submodule.span ℤ (Set.range (Fin.append (fun i : Fin m => ((bN i : ↥N) : E d)) x)) = V ∧
      LinearIndependent ℤ (Fin.append (fun i : Fin m => ((bN i : ↥N) : E d)) x) ∧
      LinearIndependent ℝ (Fin.append (fun i : Fin m => ((bN i : ↥N) : E d)) x) := by
  classical
  have hmn : m ≤ n := by simpa using (Fintype.card_le_of_injective e e.injective)
  rcases split_equiv_image_first (m := m) (n := n) hmn e with ⟨ρ, hρ1, _hρ2, _hρ3⟩
  let a : ℕ := n - m
  let u : Fin m → E d := fun i => ((bN i : ↥N) : E d)
  let x : Fin a → E d := fun k => ((bV (ρ (Fin.natAdd m k) : Fin n) : ↥V) : E d)
  have hspanN : Submodule.span ℤ (Set.range u) = N := by
    dsimp [u]
    exact span_ambient_of_basis N bN
  have hgeq : Fin.append u x = fun j : Fin (m + a) => ((bV (ρ j : Fin n) : ↥V) : E d) := by
    funext j
    rcases fin_eq_castAdd_or_natAdd (m := m) (a := a) j with ⟨i, rfl⟩ | ⟨k, rfl⟩
    · simp only [u, x, Fin.append_left]
      rw [hρ1]
      exact (initial_val_eq_bN V N bN bV hNV e h i).symm
    · simp only [u, x, Fin.append_right]
  have hrange : Set.range (fun j : Fin (m + a) => ((bV (ρ j : Fin n) : ↥V) : E d)) =
      Set.range (fun k : Fin n => ((bV k : ↥V) : E d)) := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨ρ j, rfl⟩
    · rintro ⟨k, rfl⟩
      refine ⟨ρ.symm k, ?_⟩
      change ((bV (ρ (ρ.symm k)) : ↥V) : E d) = ((bV k : ↥V) : E d)
      rw [Equiv.apply_symm_apply ρ k]
  have hspanV : Submodule.span ℤ (Set.range (Fin.append u x)) = V := by
    rw [hgeq, hrange]
    exact span_ambient_of_basis V bV
  have hliZ : LinearIndependent ℤ (Fin.append u x) := by
    have hbase := li_ambient_of_basis V bV
    have hliρ : LinearIndependent ℤ
        (fun j : Fin (m + a) => ((bV (ρ j : Fin n) : ↥V) : E d)) :=
      hbase.comp ρ ρ.injective
    simpa [hgeq] using hliρ
  have hmem : ∀ j : Fin (m + (n - m)), (Fin.append u x) j ∈ (Λ : Set (E d)) := by
    intro j
    rcases fin_eq_castAdd_or_natAdd (m := m) (a := n - m) j with ⟨i, rfl⟩ | ⟨k, rfl⟩
    · rw [Fin.append_left]
      dsimp [u]
      exact hVΛ (hNV (bN i).2)
    · rw [Fin.append_right]
      dsimp [x]
      exact hVΛ (bV (ρ (Fin.natAdd m k) : Fin n)).2
  have hliR : LinearIndependent ℝ (Fin.append u x) :=
    linearIndependent_real_of_mem_lattice (d := d) Λ hΛfin (Fin.append u x) hmem hliZ
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · simpa [u] using hspanN
  · simpa [u] using hspanV
  · simpa [u] using hliZ
  · simpa [u] using hliR


/-- **(i-b-3) `ℤ`-independence of the combined family**: if `u ++ x` and `u ++ y` are
`ℤ`-independent spanning `V` resp. `W`, and `u` spans `N = V ⊓ W`, then the combined
family `(u ++ x) ++ y` is `ℤ`-independent.  Proof (coefficient argument over `ℤ`): a
vanishing combination splits into its `(u++x)`-part `S₁ ∈ V` and its `y`-part
`S₂ ∈ W`; `S₁ + S₂ = 0` gives `S₂ = -S₁ ∈ V`, so `S₂ ∈ V ⊓ W = N = span(range u)` —
`S₂ = Σ dᵢ uᵢ`; the relation `-Σ dᵢ uᵢ + S₂ = 0` on the independent family `u ++ y`
forces the `y`-coefficients (and the `dᵢ`) to vanish, hence `S₁ = 0` and the
`(u++x)`-coefficients vanish by independence of `u ++ x`. -/
lemma zli_append3 {d m a b : ℕ} (u : Fin m → E d) (x : Fin a → E d) (y : Fin b → E d)
    (V W N : Submodule ℤ (E d))
    (hux : LinearIndependent ℤ (Fin.append u x))
    (huy : LinearIndependent ℤ (Fin.append u y))
    (hV : V = Submodule.span ℤ (Set.range (Fin.append u x)))
    (hW : W = Submodule.span ℤ (Set.range (Fin.append u y)))
    (hN : N = Submodule.span ℤ (Set.range u))
    (hI : V ⊓ W = N) :
    LinearIndependent ℤ (Fin.append (Fin.append u x) y) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc t
  let S1 : E d := ∑ i : Fin (m + a), c (Fin.castAdd b i) • (Fin.append u x) i
  let S2 : E d := ∑ k : Fin b, c (Fin.natAdd (m + a) k) • y k
  -- split the total sum into the (u++x)-part and the y-part
  have hsum : S1 + S2 = 0 := by
    dsimp [S1, S2]
    have hc' := Fin.sum_univ_add (a := m + a) (b := b)
      (f := fun s : Fin ((m + a) + b) => c s • (Fin.append (Fin.append u x) y) s)
    rw [hc'] at hc
    simpa [Fin.append_left, Fin.append_right] using hc
  -- S1 ∈ V (each summand is a V-element)
  have hS1V : S1 ∈ V := by
    dsimp [S1]
    rw [hV]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  -- S2 ∈ W
  have hS2W : S2 ∈ W := by
    dsimp [S2]
    rw [hW]
    apply Submodule.sum_mem
    intro k hk
    exact Submodule.smul_mem _ _ (by
      refine Submodule.subset_span ⟨Fin.natAdd m k, ?_⟩
      simp [Fin.append_right])
  -- S2 = -S1 so S2 ∈ V
  have hS2neg : S2 = -S1 := eq_neg_of_add_eq_zero_right hsum
  have hS2V : S2 ∈ V := by
    rw [hS2neg]
    exact Submodule.neg_mem V hS1V
  have hS2N : S2 ∈ N := by
    rw [← hI]
    exact ⟨hS2V, hS2W⟩
  -- S2 ∈ span(range u): get integer coefficients d
  have hS2span : S2 ∈ Submodule.span ℤ (Set.range u) := by
    rw [← hN]
    exact hS2N
  rw [Submodule.mem_span_range_iff_exists_fun] at hS2span
  rcases hS2span with ⟨d, hd⟩
  -- relation on append u y with coefficients (-d) on the u-part and c∘natAdd(m+a) on y
  have hfamLI : LinearIndependent ℤ
      ((Fin.append u y) ∘ (finSumFinEquiv : Sum (Fin m) (Fin b) → Fin (m + b))) :=
    huy.comp (finSumFinEquiv : Sum (Fin m) (Fin b) → Fin (m + b)) finSumFinEquiv.injective
  let g1 : Fin m → ℤ := fun i => -d i
  let g2 : Fin b → ℤ := fun k => c (Fin.natAdd (m + a) k)
  have hrel : (∑ z : Sum (Fin m) (Fin b),
      Sum.elim g1 g2 z • (Fin.append u y (finSumFinEquiv z))) = 0 := by
    rw [Fintype.sum_sum_type
      (f := fun z : Sum (Fin m) (Fin b) =>
        Sum.elim g1 g2 z • (Fin.append u y (finSumFinEquiv z)))]
    have hpart1 : (∑ i : Fin m, (Sum.elim g1 g2 (Sum.inl i)) •
        (Fin.append u y (finSumFinEquiv (Sum.inl i)))) = -S2 := by
      calc
        (∑ i : Fin m, (Sum.elim g1 g2 (Sum.inl i)) •
            (Fin.append u y (finSumFinEquiv (Sum.inl i))))
            = ∑ i : Fin m, (-d i) • u i := by
              apply Finset.sum_congr rfl
              intro i hi
              simp [g1, g2, finSumFinEquiv_apply_left, Fin.append_left]
        _ = -(∑ i : Fin m, d i • u i) := by
              have hsmul : (∑ i : Fin m, (-d i) • u i) = ∑ i : Fin m, -(d i • u i) := by
                apply Finset.sum_congr rfl
                intro i hi
                simp
              rw [hsmul, Finset.sum_neg_distrib]
        _ = -S2 := by rw [hd]
    have hpart2 : (∑ k : Fin b, (Sum.elim g1 g2 (Sum.inr k)) •
        (Fin.append u y (finSumFinEquiv (Sum.inr k)))) = S2 := by
      calc
        (∑ k : Fin b, (Sum.elim g1 g2 (Sum.inr k)) •
            (Fin.append u y (finSumFinEquiv (Sum.inr k))))
            = ∑ k : Fin b, c (Fin.natAdd (m + a) k) • y k := by
              apply Finset.sum_congr rfl
              intro k hk
              simp [g1, g2, finSumFinEquiv_apply_right, Fin.append_right]
        _ = S2 := by dsimp [S2]
    rw [hpart1, hpart2]
    simp
  have hzero := (Fintype.linearIndependent_iff.mp hfamLI) (Sum.elim g1 g2) hrel
  have hc3 : ∀ k : Fin b, c (Fin.natAdd (m + a) k) = 0 := by
    intro k
    have hk := hzero (Sum.inr k)
    simpa [g1, g2] using hk
  -- S2 = 0 and hence S1 = 0
  have hS2zero : S2 = 0 := by
    dsimp [S2]
    simp [hc3]
  have hS1zero : S1 = 0 := by
    have hs := hsum
    rw [hS2zero] at hs
    simpa using hs
  -- S1 = 0 is a ℤ-relation on append u x with coefficients f i := c (castAdd b i)
  let f : Fin (m + a) → ℤ := fun i => c (Fin.castAdd b i)
  have hrel2 : (∑ i : Fin (m + a), f i • (Fin.append u x) i) = 0 := by
    simpa [S1, f] using hS1zero
  have hfzero := (Fintype.linearIndependent_iff.mp hux) f hrel2
  -- now split t : Fin (m+a+b)
  rcases fin_eq_castAdd_or_natAdd (m := m + a) (a := b) t with ⟨i, rfl⟩ | ⟨k, rfl⟩
  · exact hfzero i
  · exact hc3 k


/-- **Two-block ℤ-independence**: if `x` and `y` are `ℤ`-independent spanning `V` resp.
`W` with `V ⊓ W = ⊥`, then `x ++ y` is `ℤ`-independent.  (Coefficient argument: a
vanishing combination splits by `Fin.sum_univ_add` into `Sx ∈ V` and `Sy ∈ W`; from
`Sx + Sy = 0` both `Sx ∈ V ⊓ W = ⊥` and `Sy = -Sx` follow, so `Sx = Sy = 0`, and the
independence of `x` resp. `y` kills the coefficients.) -/
lemma zli_append2 {d a b : ℕ} (x : Fin a → E d) (y : Fin b → E d)
    (V W : Submodule ℤ (E d))
    (hx : LinearIndependent ℤ x) (hy : LinearIndependent ℤ y)
    (hV : V = Submodule.span ℤ (Set.range x)) (hW : W = Submodule.span ℤ (Set.range y))
    (hbot : V ⊓ W = ⊥) :
    LinearIndependent ℤ (Fin.append x y) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc t
  let Sx : E d := ∑ i : Fin a, c (Fin.castAdd b i) • x i
  let Sy : E d := ∑ k : Fin b, c (Fin.natAdd a k) • y k
  have hsum : Sx + Sy = 0 := by
    dsimp [Sx, Sy]
    have hc' := Fin.sum_univ_add (a := a) (b := b)
      (f := fun s : Fin (a + b) => c s • Fin.append x y s)
    rw [hc'] at hc
    simpa [Fin.append_left, Fin.append_right] using hc
  have hSxV : Sx ∈ V := by
    dsimp [Sx]
    rw [hV]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hSyW : Sy ∈ W := by
    dsimp [Sy]
    rw [hW]
    exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  have hSxneg : Sx = -Sy := eq_neg_of_add_eq_zero_left hsum
  have hSxW : Sx ∈ W := by
    rw [hSxneg]
    exact Submodule.neg_mem W hSyW
  have hSxbot : Sx ∈ (⊥ : Submodule ℤ (E d)) := by
    rw [← hbot]
    exact ⟨hSxV, hSxW⟩
  have hSx0 : Sx = 0 := (Submodule.mem_bot (R := ℤ)).mp hSxbot
  have hSy0 : Sy = 0 := by
    rw [hSx0, zero_add] at hsum
    exact hsum
  have hfx : ∀ i : Fin a, c (Fin.castAdd b i) = 0 := by
    have hrel : (∑ i : Fin a, c (Fin.castAdd b i) • x i) = 0 := by simpa [Sx] using hSx0
    exact (Fintype.linearIndependent_iff.mp hx) (fun i => c (Fin.castAdd b i)) hrel
  have hfy : ∀ k : Fin b, c (Fin.natAdd a k) = 0 := by
    have hrel : (∑ k : Fin b, c (Fin.natAdd a k) • y k) = 0 := by simpa [Sy] using hSy0
    exact (Fintype.linearIndependent_iff.mp hy) (fun k => c (Fin.natAdd a k)) hrel
  rcases fin_eq_castAdd_or_natAdd (m := a) (a := b) t with ⟨i, rfl⟩ | ⟨k, rfl⟩
  · exact hfx i
  · exact hfy k

/-- The span of the empty family (`Fin.elim0`) is `⊥`. -/
lemma span_range_elim0 {d : ℕ} :
    Submodule.span ℤ (Set.range (Fin.elim0 : Fin 0 → E d)) = ⊥ := by
  apply le_bot_iff.mp
  rw [Submodule.span_le]
  rintro z ⟨i, -⟩
  exact Fin.elim0 i


/-- Reindexing a family by `Fin.cast (Nat.zero_add a)` does not change its range. -/
lemma range_comp_finCast {α : Type*} {a : ℕ} (f : Fin a → α) :
    Set.range (f ∘ Fin.cast (Nat.zero_add a)) = Set.range f := by
  rw [Set.range_comp,
    Set.range_eq_univ.mpr (fun y => ⟨Fin.cast (Nat.zero_add a).symm y, by simp⟩),
    Set.image_univ]

/-- **The degenerate (`V ⊓ W = ⊥`) case of (i-b-3)**: for saturated nonzero `V, W ≤ Λ`
with trivial meet, the empty family `Fin.elim0` plays the role of `u`: the families `x`,
`y` (certified bases of `V`, `W`) give
`span (range (elim0 ++ x)) = V`, `span (range (elim0 ++ y)) = W`,
`span (range ((elim0 ++ x) ++ y)) = V ⊔ W`, all `ℝ`-independent — the `m = 0` case of the
aligned-family theorem. -/
theorem exists_aligned_ambient_of_saturated_pair_bot {d : ℕ} (Λ V W : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    (hVΛ : V ≤ Λ) (hWΛ : W ≤ Λ) (hV0 : V ≠ ⊥) (hW0 : W ≠ ⊥)
    (hbot : V ⊓ W = ⊥) :
    ∃ a b : ℕ, ∃ x : Fin a → E d, ∃ y : Fin b → E d,
      Submodule.span ℤ (Set.range (Fin.elim0 : Fin 0 → E d)) = V ⊓ W ∧
      Submodule.span ℤ (Set.range (Fin.append (Fin.elim0 : Fin 0 → E d) x)) = V ∧
      Submodule.span ℤ (Set.range (Fin.append (Fin.elim0 : Fin 0 → E d) y)) = W ∧
      Submodule.span ℤ (Set.range (Fin.append (Fin.append (Fin.elim0 : Fin 0 → E d) x) y)) =
        V ⊔ W ∧
      LinearIndependent ℝ (Fin.elim0 : Fin 0 → E d) ∧
      LinearIndependent ℝ (Fin.append (Fin.elim0 : Fin 0 → E d) x) ∧
      LinearIndependent ℝ (Fin.append (Fin.elim0 : Fin 0 → E d) y) ∧
      LinearIndependent ℝ (Fin.append (Fin.append (Fin.elim0 : Fin 0 → E d) x) y) := by
  classical
  rcases exists_basis_family_int_of_le_lattice (d := d) Λ hΛfin V hVΛ hV0 with
    ⟨cV, hliV, hzliV, hmemVΛ, hVspan⟩
  rcases exists_basis_family_int_of_le_lattice (d := d) Λ hΛfin W hWΛ hW0 with
    ⟨cW, hliW, hzliW, hmemWΛ, hWspan⟩
  have hrangeV : Set.range (cV ∘ Fin.cast (Nat.zero_add (subDim V))) = Set.range cV :=
    range_comp_finCast cV
  have hrangeW : Set.range (cW ∘ Fin.cast (Nat.zero_add (subDim W))) = Set.range cW :=
    range_comp_finCast cW
  have hspanV : Submodule.span ℤ (Set.range (Fin.append (Fin.elim0 : Fin 0 → E d) cV)) = V := by
    rw [Fin.elim0_append, hrangeV]
    exact hVspan.symm
  have hspanW : Submodule.span ℤ (Set.range (Fin.append (Fin.elim0 : Fin 0 → E d) cW)) = W := by
    rw [Fin.elim0_append, hrangeW]
    exact hWspan.symm
  have hliRV : LinearIndependent ℝ (Fin.append (Fin.elim0 : Fin 0 → E d) cV) := by
    have h := hliV.comp (Fin.cast (Nat.zero_add (subDim V))) (Fin.cast_injective _)
    simpa [Fin.elim0_append] using h
  have hliRW : LinearIndependent ℝ (Fin.append (Fin.elim0 : Fin 0 → E d) cW) := by
    have h := hliW.comp (Fin.cast (Nat.zero_add (subDim W))) (Fin.cast_injective _)
    simpa [Fin.elim0_append] using h
  have hzliV' : LinearIndependent ℤ (Fin.append (Fin.elim0 : Fin 0 → E d) cV) := by
    have h := hzliV.comp (Fin.cast (Nat.zero_add (subDim V))) (Fin.cast_injective _)
    simpa [Fin.elim0_append] using h
  have hzliComb : LinearIndependent ℤ
      (Fin.append (Fin.append (Fin.elim0 : Fin 0 → E d) cV) cW) :=
    zli_append2 _ _ V W hzliV' hzliW hspanV.symm hWspan hbot
  have hmem : ∀ j : Fin ((0 + subDim V) + subDim W),
      (Fin.append (Fin.append (Fin.elim0 : Fin 0 → E d) cV) cW) j ∈ (Λ : Set (E d)) := by
    intro j
    rcases fin_eq_castAdd_or_natAdd (m := 0 + subDim V) (a := subDim W) j with ⟨i, rfl⟩ | ⟨k, rfl⟩
    · rw [Fin.append_left]
      rw [Fin.elim0_append]
      exact hmemVΛ (Fin.cast (Nat.zero_add (subDim V)) i)
    · rw [Fin.append_right]
      exact hmemWΛ k
  have hliRComb : LinearIndependent ℝ
      (Fin.append (Fin.append (Fin.elim0 : Fin 0 → E d) cV) cW) :=
    linearIndependent_real_of_mem_lattice (d := d) Λ hΛfin _ hmem hzliComb
  have hliU0 : LinearIndependent ℝ (Fin.elim0 : Fin 0 → E d) := by
    rw [Fintype.linearIndependent_iff]
    intro c _ i
    exact Fin.elim0 i
  refine ⟨subDim V, subDim W, cV, cW, ?_, hspanV, hspanW, ?_, hliU0, hliRV, hliRW, ?_⟩
  · rw [span_range_elim0, hbot]
  · exact span_append_join V W (Fin.elim0 : Fin 0 → E d) cV cW hspanV hspanW
  · exact hliRComb

/-- **(i-b-3) The aligned ambient families of a saturated pair.**  Let `Λ ≤ ℝᵈ` be a
full-rank lattice and `V, W ≤ Λ` **saturated** nonzero subgroups with `V ⊓ W ≠ ⊥`.  Then
there are ambient families `u` (of `V ⊓ W`), `x`, `y` realising the whole flag of the
pair:

    `span ℤ (range u) = V ⊓ W`,
    `span ℤ (range (u ++ x)) = V`,
    `span ℤ (range (u ++ y)) = W`,
    `span ℤ (range ((u ++ x) ++ y)) = V ⊔ W`,

with all four families `ℝ`-linearly independent (and `u ++ x`, `u ++ y`,
`(u ++ x) ++ y` even `ℤ`-independent).

Construction: `N := V ⊓ W` is saturated (`saturated_inf`) and pure in `V` and in `W`
(`pure_inf_left`); a certified `ℤ`-basis `bN` of `N` extends to bases `bV`, `bW` of `V`,
`W` (`extend_given_basis_intersection`, the SAME `bN` on both sides); the completions
`exists_ambient_completion` give `x`, `y` with the SAME canonical family
`u = ambient ∘ bN`; the join span is `span_append_join`; `ℤ`-independence of
`(u ++ x) ++ y` is `zli_append3`, upgraded to `ℝ`-independence by lattice membership. -/
theorem exists_aligned_ambient_of_saturated_pair_inf_ne_bot {d : ℕ} (Λ V W : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    (hVΛ : V ≤ Λ) (hWΛ : W ≤ Λ) (hV0 : V ≠ ⊥) (hW0 : W ≠ ⊥)
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W) (hN0 : V ⊓ W ≠ ⊥) :
    ∃ m a b : ℕ, ∃ u : Fin m → E d, ∃ x : Fin a → E d, ∃ y : Fin b → E d,
      Submodule.span ℤ (Set.range u) = V ⊓ W ∧
      Submodule.span ℤ (Set.range (Fin.append u x)) = V ∧
      Submodule.span ℤ (Set.range (Fin.append u y)) = W ∧
      Submodule.span ℤ (Set.range (Fin.append (Fin.append u x) y)) = V ⊔ W ∧
      LinearIndependent ℝ u ∧ LinearIndependent ℝ (Fin.append u x) ∧
      LinearIndependent ℝ (Fin.append u y) ∧
      LinearIndependent ℝ (Fin.append (Fin.append u x) y) := by
  classical
  let N : Submodule ℤ (E d) := V ⊓ W
  have hNV : N ≤ V := inf_le_left
  have hNW : N ≤ W := inf_le_right
  have hNΛ : N ≤ Λ := le_trans hNV hVΛ
  -- purity of the meet in each factor (from saturation of the other factor)
  have hpureV : Pure V N := by
    have h := pure_inf_left Λ V W hVΛ hWsat
    simpa [N] using h
  have hpureW : Pure W N := by
    have h := pure_inf_left Λ W V hWΛ hVsat
    rw [show N = W ⊓ V from by dsimp [N]; rw [inf_comm]]
    exact h
  -- the shared ℤ-basis of N
  rcases exists_basis_family_int_of_le_lattice (d := d) Λ hΛfin N hNΛ (by simpa [N] using hN0) with
    ⟨cN, _hliN, hzliN, _hmemNΛ, hNspan⟩
  have hmemN : ∀ i : Fin (subDim N), cN i ∈ N := by
    intro i
    rw [hNspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  let bN : Module.Basis (Fin (subDim N)) ℤ N := basis_of_family (M := N) cN hmemN hzliN hNspan
  -- extend on both sides from the SAME bN
  rcases extend_given_basis_intersection (d := d) Λ V N hΛfin hVΛ hNV hV0 hN0 hpureV bN with
    ⟨nV, bV, eV, hVemb⟩
  rcases extend_given_basis_intersection (d := d) Λ W N hΛfin hWΛ hNW hW0 hN0 hpureW bN with
    ⟨nW, bW, eW, hWemb⟩
  -- completions (both stated with the same canonical family u)
  rcases exists_ambient_completion (d := d) (m := subDim N) (n := nV) Λ V N hΛfin hVΛ bN bV
      hNV eV hVemb with ⟨x, huN, huxV, hliZux, hliRux⟩
  rcases exists_ambient_completion (d := d) (m := subDim N) (n := nW) Λ W N hΛfin hWΛ bN bW
      hNW eW hWemb with ⟨y, _huN', huyW, hliZuy, hliRuy⟩
  -- the canonical family, as the visible witness
  let u : Fin (subDim N) → E d := fun i => ((bN i : ↥N) : E d)
  -- members of the pieces in the lattice
  have huMem : ∀ i : Fin (subDim N), u i ∈ (N : Set (E d)) := by
    intro i
    have : u i ∈ Submodule.span ℤ (Set.range u) := Submodule.subset_span ⟨i, rfl⟩
    rwa [show Submodule.span ℤ (Set.range u) = N from huN] at this
  have hxMem : ∀ k : Fin (nV - subDim N), x k ∈ (V : Set (E d)) := by
    intro k
    have hspan : Submodule.span ℤ (Set.range (Fin.append u x)) = V := huxV
    have hmem : x k ∈ Submodule.span ℤ (Set.range (Fin.append u x)) :=
      Submodule.subset_span ⟨Fin.natAdd (subDim N) k, by rw [Fin.append_right]⟩
    rwa [hspan] at hmem
  have hyMem : ∀ k : Fin (nW - subDim N), y k ∈ (W : Set (E d)) := by
    intro k
    have hspan : Submodule.span ℤ (Set.range (Fin.append u y)) = W := huyW
    have hmem : y k ∈ Submodule.span ℤ (Set.range (Fin.append u y)) :=
      Submodule.subset_span ⟨Fin.natAdd (subDim N) k, by rw [Fin.append_right]⟩
    rwa [hspan] at hmem
  -- ℤ-independence of the combined family
  have hliZcomb : LinearIndependent ℤ (Fin.append (Fin.append u x) y) :=
    zli_append3 u x y V W N (by simpa [u] using hliZux) (by simpa [u] using hliZuy)
      (by simpa [u] using huxV.symm) (by simpa [u] using huyW.symm)
      (by simpa [u] using huN.symm) rfl
  -- members of the combined family in Λ
  have hcombMem : ∀ j : Fin (subDim N + (nV - subDim N) + (nW - subDim N)),
      (Fin.append (Fin.append u x) y) j ∈ (Λ : Set (E d)) := by
    intro j
    rcases fin_eq_castAdd_or_natAdd (m := subDim N + (nV - subDim N)) (a := nW - subDim N) j
      with ⟨i, rfl⟩ | ⟨k, rfl⟩
    · rw [Fin.append_left]
      rcases fin_eq_castAdd_or_natAdd (m := subDim N) (a := nV - subDim N) i with ⟨i0, rfl⟩ | ⟨k0, rfl⟩
      · rw [Fin.append_left]
        exact hNΛ (huMem i0)
      · rw [Fin.append_right]
        exact hVΛ (hxMem k0)
    · rw [Fin.append_right]
      exact hWΛ (hyMem k)
  have hliRcomb : LinearIndependent ℝ (Fin.append (Fin.append u x) y) :=
    linearIndependent_real_of_mem_lattice (d := d) Λ hΛfin _ hcombMem hliZcomb
  -- LI ℝ of u from LI ℝ (u ++ x) by restriction
  have hliRu : LinearIndependent ℝ u := by
    have h := hliRux.comp (Fin.castAdd (nV - subDim N))
      (Fin.castAdd_injective _ (nV - subDim N))
    have heq : ((Fin.append u x) ∘ (Fin.castAdd (nV - subDim N))) = u := by
      funext i
      rw [Function.comp_apply, Fin.append_left]
    rwa [heq] at h
  refine ⟨subDim N, nV - subDim N, nW - subDim N, u, x, y, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [u] using huN
  · simpa [u] using huxV
  · simpa [u] using huyW
  · exact span_append_join V W u x y huxV huyW
  · exact hliRu
  · simpa [u] using hliRux
  · simpa [u] using hliRuy
  · exact hliRcomb


/-- **(i-b-3) The aligned ambient families of a saturated pair (UNIFIED, both cases).**
Let `Λ ≤ ℝᵈ` be a full-rank lattice and `V, W ≤ Λ` **saturated** nonzero subgroups (NO
hypothesis on `V ⊓ W`: it may be `⊥`, in which case `m = 0`).  Then there are ambient
families `u` (of `V ⊓ W`), `x`, `y` realising the whole flag of the pair:

    `span ℤ (range u) = V ⊓ W`, `span ℤ (range (u ++ x)) = V`,
    `span ℤ (range (u ++ y)) = W`, `span ℤ (range ((u ++ x) ++ y)) = V ⊔ W`,

with all four families `ℝ`-linearly independent. -/
theorem exists_aligned_ambient_of_saturated_pair {d : ℕ} (Λ V W : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    (hVΛ : V ≤ Λ) (hWΛ : W ≤ Λ) (hV0 : V ≠ ⊥) (hW0 : W ≠ ⊥)
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W) :
    ∃ m a b : ℕ, ∃ u : Fin m → E d, ∃ x : Fin a → E d, ∃ y : Fin b → E d,
      Submodule.span ℤ (Set.range u) = V ⊓ W ∧
      Submodule.span ℤ (Set.range (Fin.append u x)) = V ∧
      Submodule.span ℤ (Set.range (Fin.append u y)) = W ∧
      Submodule.span ℤ (Set.range (Fin.append (Fin.append u x) y)) = V ⊔ W ∧
      LinearIndependent ℝ u ∧ LinearIndependent ℝ (Fin.append u x) ∧
      LinearIndependent ℝ (Fin.append u y) ∧
      LinearIndependent ℝ (Fin.append (Fin.append u x) y) := by
  by_cases hN0 : V ⊓ W ≠ ⊥
  · exact exists_aligned_ambient_of_saturated_pair_inf_ne_bot Λ V W hΛfin hVΛ hWΛ hV0 hW0
      hVsat hWsat hN0
  · have hbot : V ⊓ W = ⊥ := not_not.mp hN0
    obtain ⟨a, b, x, y, h1, h2, h3, h4, h5, h6, h7⟩ :=
      exists_aligned_ambient_of_saturated_pair_bot Λ V W hΛfin hVΛ hWΛ hV0 hW0 hbot
    exact ⟨0, a, b, Fin.elim0, x, y, h1, h2, h3, h4, h5, h6, h7⟩


/-! ## (i-b-4) The saturated-pair log-covol submodularity and the join budget

Feeding the aligned families of `exists_aligned_ambient_of_saturated_pair` into the
proven engine `JoinSubmodularity.logCovol_submodularity_aligned` gives the **mixed-rank
log-covol submodularity** for saturated pairs, and its join-budget corollaries (the tool
the greedy HN-flag construction consumes). -/

/-- **(i-b-4) Log-covol submodularity for saturated pairs.**  For saturated nonzero
`V, W ≤ Λ` with `V ⊓ W ≠ ⊥`:

`log covol V + log covol W ≥ log covol (V ⊓ W) + log covol (V ⊔ W)`. -/
theorem logCovol_submodularity_saturated {d : ℕ} (Λ V W : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    (hVΛ : V ≤ Λ) (hWΛ : W ≤ Λ) (hV0 : V ≠ ⊥) (hW0 : W ≠ ⊥)
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W) (hN0 : V ⊓ W ≠ ⊥) :
    Real.log (latticeCovol V) + Real.log (latticeCovol W) ≥
      Real.log (latticeCovol (V ⊓ W)) + Real.log (latticeCovol (V ⊔ W)) := by
  classical
  obtain ⟨m, a, b, u, x, y, huN, huxV, huyW, huxyS, hliRu, hliRux, hliRuy, hliRuxy⟩ :=
    exists_aligned_ambient_of_saturated_pair_inf_ne_bot Λ V W hΛfin hVΛ hWΛ hV0 hW0 hVsat hWsat hN0
  have hm : 0 < m := by
    have h1 : subDim (V ⊓ W) = m := by
      rw [← huN]
      exact subDim_span_range_of_linearIndependent u hliRu
    have h2 : 0 < subDim (V ⊓ W) := Nat.pos_of_ne_zero
      (fun hz => hN0 ((subDim_eq_zero_iff_bot (V ⊓ W)).mp hz))
    omega
  exact logCovol_submodularity_aligned (d := d) hm u x y hliRu hliRux hliRuy hliRuxy V W
    huxV.symm huyW.symm huN.symm huxyS.symm

/-- **The join budget (log form)**: for a saturated pair, the log-covolume of the join is
at most `log covol V + log covol W − log covol (V ⊓ W)`. -/
theorem log_latticeCovol_sup_le {d : ℕ} (Λ V W : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    (hVΛ : V ≤ Λ) (hWΛ : W ≤ Λ) (hV0 : V ≠ ⊥) (hW0 : W ≠ ⊥)
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W) (hN0 : V ⊓ W ≠ ⊥) :
    Real.log (latticeCovol (V ⊔ W)) ≤
      Real.log (latticeCovol V) + Real.log (latticeCovol W) - Real.log (latticeCovol (V ⊓ W)) := by
  have h := logCovol_submodularity_saturated Λ V W hΛfin hVΛ hWΛ hV0 hW0 hVsat hWsat hN0
  linarith

/-- **The join budget (product form)**: for a saturated pair,
`covol (V ⊓ W) · covol (V ⊔ W) ≤ covol V · covol W`. -/
theorem latticeCovol_inf_mul_sup_le {d : ℕ} (Λ V W : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    (hVΛ : V ≤ Λ) (hWΛ : W ≤ Λ) (hV0 : V ≠ ⊥) (hW0 : W ≠ ⊥)
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W) (hN0 : V ⊓ W ≠ ⊥) :
    latticeCovol (V ⊓ W) * latticeCovol (V ⊔ W) ≤ latticeCovol V * latticeCovol W := by
  have hlog := logCovol_submodularity_saturated Λ V W hΛfin hVΛ hWΛ hV0 hW0 hVsat hWsat hN0
  have hInΛ : V ⊓ W ≤ Λ := le_trans inf_le_left hVΛ
  have hSupΛ : V ⊔ W ≤ Λ := sup_le hVΛ hWΛ
  have hSup0 : V ⊔ W ≠ ⊥ := fun hz =>
    hV0 (le_bot_iff.mp (by rw [← hz]; exact le_sup_left))
  have hVpos : 0 < latticeCovol V := latticeCovol_pos (d := d) Λ V hVΛ hV0
  have hWpos : 0 < latticeCovol W := latticeCovol_pos (d := d) Λ W hWΛ hW0
  have hInpos : 0 < latticeCovol (V ⊓ W) := latticeCovol_pos (d := d) Λ (V ⊓ W) hInΛ hN0
  have hSuppos : 0 < latticeCovol (V ⊔ W) := latticeCovol_pos (d := d) Λ (V ⊔ W) hSupΛ hSup0
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_add, Real.exp_add, Real.exp_log hInpos, Real.exp_log hSuppos,
    Real.exp_log hVpos, Real.exp_log hWpos] at hexp
  exact hexp


end Submission.AlignedBases

end
