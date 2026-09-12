import Mathlib

/-!
# Covolume-spectrum discreteness — core: finitely many bounded-index subgroups

Paper §3 (and its Harder–Narasimhan reference [5, §1.3]) uses, for a full-rank lattice
`Λ`, the **discreteness of the covolume spectrum**: among the discrete subgroups
`W ≤ Λ` of a fixed rank with covolume below any given bound there are only finitely
many (Mahler compactness / integer-matrix counting).  This module develops the core of
that statement in its purest group-theoretic form, over an *arbitrary* additive
commutative group `G` that is free and finitely generated as a `ℤ`-module (e.g. `Λ`
itself, or the coordinate group `(Fin d → ℤ)`):

**Theorem (`finite_index_bounded`)** — for every `n : ℕ` only finitely many subgroups
`H ≤ G` have finite index bounded by `n`.

The proof is the classical multiplication-by-`n!` argument:
1. every subgroup `H` with `0 < H.index ≤ n` contains the whole `n!`-scaled subgroup
   `Rₙ := (nsmulAddMonoidHom n!).range` — since `H.index ∣ n!` and
   `H.index • x ∈ H` for every `x` (`AddSubgroup.nsmul_index_mem`);
2. the scaled subgroup has finite index `(n!)^{finrank ℤ G}` in `G`
   (`AddSubgroup.index_range_nsmul`), so the quotient `G ⧸ Rₙ` is finite;
3. subgroups of `G` containing `Rₙ` correspond injectively to the (finitely many)
   subgroups of the finite group `G ⧸ Rₙ` (`AddSubgroup.comap_map_eq_self`).

A real-bound wrapper (`finite_index_bounded_real`) is included for the covolume
applications (`covol ≤ C` bounds the index by `C / covol(Λ)`, a real).

All declarations are Mathlib-only (candidates for promotion to the shared commons once
the downstream §3 modules fix the exact API shape).
-/

open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

namespace Submission.SpectrumDiscreteness

/-! ## Bounded-index subgroups of a free finite-rank `ℤ`-module -/

/-- **The `n!`-scaled subgroup is below every subgroup of index `≤ n`**: if
`H ≤ G` has finite index `H.index ≤ n`, then `(n! • G) = (nsmulAddMonoidHom n!).range`
is contained in `H` (as `H.index ∣ n!` and `H.index • x ∈ H` for all `x`). -/
lemma nsmul_range_factorial_le_of_index_le {G : Type*} [AddCommGroup G] (H : AddSubgroup G)
    {n : ℕ} (hb : H.index ≤ n) (hz : H.index ≠ 0) :
    (nsmulAddMonoidHom (α := G) n.factorial).range ≤ H := by
  have hmpos : 0 < H.index := Nat.pos_of_ne_zero hz
  obtain ⟨k, hk⟩ := Nat.dvd_factorial hmpos hb  -- hk : n.factorial = H.index * k
  haveI : H.Normal := inferInstance
  intro x hx
  rcases (AddMonoidHom.mem_range.mp hx) with ⟨y, hy⟩
  have hmy : H.index • y ∈ H := AddSubgroup.nsmul_index_mem H y
  have hkmy : k • (H.index • y) ∈ H := AddSubgroup.nsmul_mem H hmy k
  -- x = n! • y = (H.index · k) • y = k • (H.index • y)
  have hxy : x = k • (H.index • y) := by
    calc
      x = n.factorial • y := hy.symm
      _ = (H.index * k) • y := by rw [hk]
      _ = k • (H.index • y) := by exact mul_nsmul y H.index k
  rwa [hxy]

/-- **Finitely many subgroups containing a fixed finite-index subgroup**: if
`R ≤ G` has finite index in `G`, then the subgroups of `G` containing `R` are finite —
they correspond injectively to subgroups of the finite group `G ⧸ R`. -/
lemma finite_subgroups_ge_of_finiteIndex {G : Type*} [AddCommGroup G] (R : AddSubgroup G)
    (hR : R.index ≠ 0) : Finite {H : AddSubgroup G // R ≤ H} := by
  classical
  haveI : Fintype (G ⧸ R) := AddSubgroup.fintypeOfIndexNeZero hR
  haveI : Finite (AddSubgroup (G ⧸ R)) := inferInstance
  haveI : R.Normal := inferInstance
  let f : G →+ G ⧸ R := QuotientAddGroup.mk' R
  let φ : {H : AddSubgroup G // R ≤ H} → AddSubgroup (G ⧸ R) :=
    fun H => AddSubgroup.map f H.1
  have hφinj : Function.Injective φ := by
    intro A B hAB
    apply Subtype.ext
    have hk : f.ker = R := QuotientAddGroup.ker_mk' R
    have hA : AddSubgroup.comap f (AddSubgroup.map f A.1) = A.1 :=
      AddSubgroup.comap_map_eq_self (by simpa [hk] using A.2)
    have hB : AddSubgroup.comap f (AddSubgroup.map f B.1) = B.1 :=
      AddSubgroup.comap_map_eq_self (by simpa [hk] using B.2)
    have hm : AddSubgroup.map f A.1 = AddSubgroup.map f B.1 := by simpa [φ] using hAB
    calc
      A.1 = AddSubgroup.comap f (AddSubgroup.map f A.1) := hA.symm
      _ = AddSubgroup.comap f (AddSubgroup.map f B.1) := by rw [hm]
      _ = B.1 := hB
  exact Finite.of_injective φ hφinj

/-- **The `n!`-scaled subgroup of a free finite-rank `ℤ`-module has finite index**:
`((nsmulAddMonoidHom n!).range).index = (n!)^{finrank ℤ G} ≠ 0`. -/
lemma index_ne_zero_range_nsmul_factorial {G : Type*} [AddCommGroup G]
    [Module.Free ℤ G] [Module.Finite ℤ G] (n : ℕ) :
    ((nsmulAddMonoidHom (α := G) n.factorial).range).index ≠ 0 := by
  have h := AddSubgroup.index_range_nsmul (M := G) n.factorial
  rw [h]
  exact pow_ne_zero _ (Nat.factorial_ne_zero n)

/-- **Core theorem (natural bound)**: for a free finite-rank `ℤ`-module `G`, only
finitely many subgroups of `G` have finite index bounded by `n`. -/
theorem finite_index_bounded {G : Type*} [AddCommGroup G] [Module.Free ℤ G]
    [Module.Finite ℤ G] (n : ℕ) :
    Finite {H : AddSubgroup G // H.index ≠ 0 ∧ H.index ≤ n} := by
  classical
  let R : AddSubgroup G := (nsmulAddMonoidHom (α := G) n.factorial).range
  have hR : R.index ≠ 0 := by
    dsimp [R]
    exact index_ne_zero_range_nsmul_factorial (G := G) n
  have hleR : ∀ H : AddSubgroup G, H.index ≠ 0 → H.index ≤ n → R ≤ H := by
    intro H hz hb
    exact nsmul_range_factorial_le_of_index_le H hb hz
  haveI : Finite {H : AddSubgroup G // R ≤ H} :=
    finite_subgroups_ge_of_finiteIndex (G := G) R hR
  refine Finite.of_injective
    (fun H : {H : AddSubgroup G // H.index ≠ 0 ∧ H.index ≤ n} =>
      (⟨H.1, hleR H.1 H.2.1 H.2.2⟩ : {H : AddSubgroup G // R ≤ H})) ?_
  intro A B h
  exact Subtype.ext (by simpa using congrArg Subtype.val h)

/-- **Core theorem (real bound)**: only finitely many subgroups of a free finite-rank
`ℤ`-module `G` have finite index bounded by the real number `B`
(`(H.index : ℝ) ≤ B`).  This is the shape used by the covolume applications: the index
of a full-rank sublattice is its covolume ratio, bounded by `C / covol(Λ)`. -/
theorem finite_index_bounded_real {G : Type*} [AddCommGroup G] [Module.Free ℤ G]
    [Module.Finite ℤ G] (B : ℝ) :
    Finite {H : AddSubgroup G // H.index ≠ 0 ∧ (H.index : ℝ) ≤ B} := by
  classical
  haveI : Finite {H : AddSubgroup G // H.index ≠ 0 ∧ H.index ≤ Nat.ceil B} :=
    finite_index_bounded (G := G) (Nat.ceil B)
  refine Finite.of_injective
    (fun H : {H : AddSubgroup G // H.index ≠ 0 ∧ (H.index : ℝ) ≤ B} =>
      (⟨H.1, H.2.1, ?_⟩ : {H : AddSubgroup G // H.index ≠ 0 ∧ H.index ≤ Nat.ceil B})) ?_
  · exact_mod_cast le_trans H.2.2 (Nat.le_ceil B)
  · intro A B h
    exact Subtype.ext (by simpa using congrArg Subtype.val h)

/-- **Covolume-bound finiteness, abstract form**: for a free finite-rank `ℤ`-module
`G`, a positive real scale `c` and a bound `C`, only finitely many finite-index
subgroups `H ≤ G` satisfy `(H.index : ℝ) · c ≤ C` (i.e. have "covolume ≤ C" when
`c` is the lattice covolume and `H.index · c` is the covolume of the sublattice
represented by `H`). -/
theorem finite_subgroups_covolume_bound {G : Type*} [AddCommGroup G] [Module.Free ℤ G]
    [Module.Finite ℤ G] {c : ℝ} (hc : 0 < c) (C : ℝ) :
    Finite {H : AddSubgroup G // H.index ≠ 0 ∧ (H.index : ℝ) * c ≤ C} := by
  classical
  haveI : Finite {H : AddSubgroup G // H.index ≠ 0 ∧ H.index ≤ Nat.ceil (C / c)} :=
    finite_index_bounded (G := G) (n := Nat.ceil (C / c))
  refine Finite.of_injective
    (fun H : {H : AddSubgroup G // H.index ≠ 0 ∧ (H.index : ℝ) * c ≤ C} =>
      (⟨H.1, H.2.1, ?_⟩ : {H : AddSubgroup G // H.index ≠ 0 ∧ H.index ≤ Nat.ceil (C / c)})) ?_
  · have hdiv := (le_div_iff₀ hc).mpr H.2.2
    exact_mod_cast le_trans hdiv (Nat.le_ceil (C / c))
  · intro A B h
    exact Subtype.ext (by simpa using congrArg Subtype.val h)

/-! ## Full-rank covolume-spectrum discreteness for a lattice

The §3 covolume-spectrum statement attaches to a full-rank lattice `Λ` (a
`ℤ`-submodule of a finite-dimensional Euclidean space with `IsZLattice`) the
discreteness of its covolume spectrum at the top rank: for every bound `C` only
finitely many **full-rank sublattices** of `Λ` have covolume `≤ C`.  Working on the
lattice point group `↥Λ`, a full-rank sublattice is a finite-index additive subgroup
`H ≤ ↥Λ`, and its covolume is the product `(H.index : ℝ) · covolume Λ`
(`ZLattice.covolume_div_covolume_eq_relIndex'`, index = covolume ratio).  Hence the
theorem below is exactly "finitely many full-rank sublattices of covolume ≤ C".

The general-rank version (rank-`r` sublattices, `r < dim`) is the mixed-rank refinement
of this statement (saturation / Plücker coordinates) and is recorded in the ROADMAP. -/

section Lattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Full-rank covolume-spectrum discreteness**: for a full-rank lattice `Λ ≤ E` and a
bound `C : ℝ`, only finitely many full-rank sublattices of `Λ` (finite-index additive
subgroups `H ≤ ↥Λ`) have covolume `(H.index : ℝ) · covolume Λ ≤ C`. -/
theorem finite_fullRank_sublattices_covol_le (Λ : Submodule ℤ E) [DiscreteTopology ↥Λ]
    [IsZLattice ℝ Λ] (C : ℝ) :
    Finite {H : AddSubgroup ↥Λ // H.index ≠ 0 ∧
      (H.index : ℝ) * ZLattice.covolume Λ ≤ C} := by
  haveI : Module.Free ℤ ↥Λ := ZLattice.module_free ℝ Λ
  haveI : Module.Finite ℤ ↥Λ := ZLattice.module_finite ℝ Λ
  exact finite_subgroups_covolume_bound (G := ↥Λ) (c := ZLattice.covolume Λ) (C := C)
    (ZLattice.covolume_pos Λ)

end Lattice

end Submission.SpectrumDiscreteness
