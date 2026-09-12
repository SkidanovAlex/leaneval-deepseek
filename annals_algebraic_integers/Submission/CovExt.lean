import Mathlib
import Mathlib.Algebra.Module.ZLattice.Covolume
import Submission.LatticeDefs

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
open scoped BigOperators RealInnerProductSpace NNReal ENNReal
open Module Submodule MeasureTheory MeasureTheory.Measure Metric Filter

/-!
# Extending a primitive lattice vector to a ℤ-basis

Task for the sub-agent.  Prove `Submission.CovExt.exists_basis_of_pure` below,
replace the placeholder proof by a real proof.  Do NOT change the statement or name.

## Mathematical content
Let `L : Submodule ℤ E` be a full-rank `ℤ`-lattice of a finite-dimensional real vector
space `E` (`DiscreteTopology L`, `IsZLattice ℝ L`), and let `v ∈ L` be nonzero and
*primitive* in the sense

    hpure : ∀ y ∈ L, y ∈ span ℝ ({v} : Set E) → y ∈ span ℤ ({v} : Set E)

(equivalently `L ∩ ℝ·v ⊆ ℤ·v`).  Then `v` extends to a `ℤ`-basis of `L`:

    ∃ (τ : Type*) (b : Basis (Option τ) ℤ L), (b none : E) = v

## Suggested proof route
`L` is a free finite `ℤ`-module (`Module.Free ℤ L`, `Module.Finite ℤ L` — instances
`instModuleFree_of_discrete_submodule`, `instModuleFinite_of_discrete_submodule`).
The purity condition says the cyclic submodule `K := Submodule.span ℤ ({v} : Set L)`
is *pure*: the quotient `L ⧸ K` is torsion-free (if `n • x̄ = 0` in the quotient for
`n : ℕ, 0 < n`, then `n • x ∈ K = ℤ·v`; dividing by `n` over `ℝ` and using `hpure`
gives `x ∈ K`, hence `x̄ = 0`).
1. Show `Module.IsTorsionFree ℤ (L ⧸ K)` (over the PID `ℤ`, torsion-free +
   finitely generated ⇒ free: `Module.free_of_finite_type_torsion_free'`, or
   `Module.free_iff_isTorsionFree`).
2. Get a basis `bq : Basis τ ℤ (L ⧸ K)` of the quotient
   (e.g. `Module.Free.chooseBasis ℤ (L ⧸ K)` with `τ := Free.ChooseBasisIndex ℤ (L ⧸ K)`).
3. Lift: choose arbitrary preimages `lt : L` of `bq t` (choice / `Quotient.out`-style,
   e.g. `Classical.choose` of the `mkQ` surjectivity) for `t : τ`.
4. Construct the combined basis `b : Basis (Option τ) ℤ L` with
   `b none = v` and `b (some t) = lt`.  Prove it is a basis: linear independence and
   spanning: if `c • v + Σ_t c_t • lt = 0`, reduce modulo `K` to get all `c_t = 0`, then
   `c • v = 0` so `c = 0` (v ≠ 0); for spanning, for `x : L` take its class `x̄`,
   express it in `bq`, lift, and adjust the `v`-coefficient (their difference lies in `K`).
   You may build it via `Basis.mk` or as `Basis.ofRepr` from the direct-sum-like structure.
   Helpful: `Submodule.Quotient.mk_eq_zero`, `mkQ` (the quotient map `L →ₗ[ℤ] L ⧸ K`),
   `Submodule.mkQ_apply`, `Submodule.mem_quotient_iff_mem` / `QuotientAddGroup.eq_zero_iff`,
   `LinearMap.ker_mkQ`, `LinearMap.range_mkQ`, `Submodule.range_mkQ`, `mkQ_surjective`.
   Also `Module.Basis.map`, `Basis.mk`, `Basis.ofRepr` (LinearAlgebra/Basis), and lemmas
   about `Option` as an index (`Finset.sum_option`, `Fintype.card_option`,
   `Option.some_injective`, `Option.guard`).  Simpler: use `Basis.mk` with index
   `Option τ` and prove the two conditions.
5. Show `(b none : E) = v` (make sure the coercion from `L` to `E` is unwrapped via
   `Submodule.coe_mk`/`SetLike.coe_mk` as needed).

Useful facts:
  - `ZLattice.module_free`/`module_finite` or the instances
    `instModuleFree_of_discrete_submodule`, `instModuleFinite_of_discrete_submodule`;
  - `Module.Free.chooseBasis`/`Module.Free.ChooseBasisIndex`;
  - PID material in `Mathlib.LinearAlgebra.FreeModule.PID`
    (`Module.free_of_finite_type_torsion_free'`, `Module.free_iff_isTorsionFree`,
    `Submodule.Quotient` torsion-free statements);
  - the pure implication from `ℝ`-span to `ℤ`-span only needs `span ℝ ({v} : Set E)`
    membership: `Submodule.mem_span_singleton`-style facts or
    `mem_span_singleton` (search for it; may be called `mem_span_singleton` or use
    `span_singleton_eq_range`), and division: from `n • x ∈ K ⊆ ℤ·v` with `n : ℤ`,
    `n ≠ 0`, deduce `x ∈ span ℝ {v}` by writing `x = (1/n) • (n • x)`-style smul facts.

The final file must contain no unfinished placeholders or extra axioms; axioms ⊆ {propext, Quot.sound,
Classical.choice}.
-/

namespace Submission.CovExt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A primitive lattice vector can be extended to a ℤ-basis of the lattice. -/
lemma exists_basis_of_pure (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (v : E) (hvL : v ∈ L) (hv0 : v ≠ 0)
    (hpure : ∀ (y : E), y ∈ L → y ∈ span ℝ ({v} : Set E) → y ∈ span ℤ ({v} : Set E)) :
    ∃ (τ : Type*) (b : Basis (Option τ) ℤ L), (b none : E) = v  := by
  classical
  let w : L := ⟨v, hvL⟩
  have hw0 : w ≠ 0 := by
    intro hw
    exact hv0 (by simpa [w] using congrArg (fun z : L => (z : E)) hw)
  let K : Submodule ℤ L := span ℤ ({w} : Set L)
  -- The cyclic submodule K corresponds under L ↪ E to span ℤ {v} ⊆ E.
  have hK_map : K.map L.subtype = span ℤ ({v} : Set E) := by
    rw [show K = span ℤ ({w} : Set L) by rfl, Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa [w] using congrArg Subtype.val ha
    · intro hy
      refine ⟨w, by simp [w], ?_⟩
      rw [hy]
      rfl
  have hK_mem (x : L) : x ∈ K ↔ (x : E) ∈ span ℤ ({v} : Set E) := by
    rw [← hK_map]
    constructor
    · intro hx
      rw [Submodule.mem_map]
      exact ⟨x, hx, rfl⟩
    · intro hx'
      rw [Submodule.mem_map] at hx'
      rcases hx' with ⟨y, hy, hyx⟩
      have hyx' : y = x := by
        apply Subtype.ext
        exact hyx
      simpa [hyx'] using hy
  have hmem0 (z : L) : K.mkQ z = 0 ↔ z ∈ K := by
    constructor
    · intro h
      have hz : z ∈ K.mkQ.ker := (LinearMap.mem_ker (f := K.mkQ) (y := z)).mpr h
      simpa using hz
    · intro hz
      have hz' : z ∈ K.mkQ.ker := by simpa using hz
      exact (LinearMap.mem_ker (f := K.mkQ) (y := z)).mp hz'
  -- purity of K inside L (the quotient L⧸K is torsion free)
  have hpure_K : ∀ (x : L) (n : ℤ), n ≠ 0 → n • x ∈ K → x ∈ K := by
    intro x n hn hnx
    have h1 : ((n • x : L) : E) ∈ span ℤ ({v} : Set E) := (hK_mem (n • x)).mp hnx
    rcases (Submodule.mem_span_singleton.mp h1) with ⟨a, ha⟩
    have hEqY : ((n • x : L) : E) = (n : ℝ) • (x : E) := by
      rw [show ((n • x : L) : E) = n • (x : E) by rfl]
      exact (Int.cast_smul_eq_zsmul ℝ n (x : E)).symm
    have hxspanR : (x : E) ∈ span ℝ ({v} : Set E) := by
      rw [Submodule.mem_span_singleton]
      refine ⟨(n : ℝ)⁻¹ * (a : ℝ), ?_⟩
      calc
        ((n : ℝ)⁻¹ * (a : ℝ)) • (v : E) = (n : ℝ)⁻¹ • ((a : ℝ) • (v : E)) := by
          rw [← smul_smul]
        _ = (n : ℝ)⁻¹ • (a • v) := by rw [Int.cast_smul_eq_zsmul ℝ a]
        _ = (n : ℝ)⁻¹ • ((n • x : L) : E) := by rw [ha]
        _ = (n : ℝ)⁻¹ • ((n : ℝ) • (x : E)) := by rw [hEqY]
        _ = (x : E) := by
          exact inv_smul_smul₀ (by exact_mod_cast hn) (x : E)
    exact (hK_mem x).mpr (hpure (x : E) x.2 hxspanR)
  letI : Module.IsTorsionFree ℤ (L ⧸ K) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro n q hnq
    rcases K.mkQ_surjective q with ⟨x, rfl⟩
    by_cases hn : n = 0
    · exact Or.inl hn
    · right
      have hmk0 : K.mkQ (n • x) = 0 := by
        simpa using hnq
      have hnxK : n • x ∈ K := (hmem0 (n • x)).mp hmk0
      have hxK : x ∈ K := hpure_K x n hn hnxK
      exact (hmem0 x).mpr hxK
  letI : Module.Finite ℤ (L ⧸ K) := inferInstance
  obtain ⟨n, bq⟩ : Σ (n : ℕ), Basis (Fin n) ℤ (L ⧸ K) := Module.basisOfFiniteTypeTorsionFree'
  let lt : Fin n → L := fun i => Classical.choose (K.mkQ_surjective (bq i))
  have hlt : ∀ i : Fin n, K.mkQ (lt i) = bq i := fun i => Classical.choose_spec (K.mkQ_surjective (bq i))
  let e : Option (Fin n) → L := fun j => j.elim w lt
  have hmk_w : K.mkQ w = 0 := (hmem0 w).mpr (Submodule.mem_span_singleton_self w)
  have hsmul_w (c : ℤ) : c • w = 0 → c = 0 := by
    intro h
    have h' : c • (w : E) = (0 : E) := by
      simpa using congrArg (fun z : L => (z : E)) h
    have h'' : (c : ℝ) • (w : E) = 0 := by
      rw [Int.cast_smul_eq_zsmul ℝ c]
      simpa using h'
    by_contra hc
    have hw0E : (w : E) = 0 := (smul_eq_zero.mp h'').resolve_left (by exact_mod_cast hc)
    exact hw0 (Subtype.ext hw0E)
  -- linear independence of the family e
  have hli : LinearIndependent ℤ e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsplit : g none • w + (∑ t : Fin n, g (some t) • lt t) = 0 := by
      simpa [e] using hg
    have hgQ : (∑ t : Fin n, g (some t) • bq t) = 0 := by
      have h1 := congrArg K.mkQ hsplit
      simpa [map_add, _root_.map_sum, map_smul, hmk_w, hlt] using h1
    have hgSome : ∀ t : Fin n, g (some t) = 0 := by
      intro t
      exact (Fintype.linearIndependent_iff.mp bq.linearIndependent (fun t : Fin n => g (some t)) hgQ) t
    have hsum0 : (∑ t : Fin n, g (some t) • lt t) = 0 := by
      simp [hgSome]
    have hgNone : g none = 0 := by
      have hwNone : g none • w = 0 := by
        have h2 := hsplit
        rw [hsum0] at h2
        simpa using h2
      exact hsmul_w (g none) hwNone
    intro i
    cases i with
    | none => exact hgNone
    | some t => exact hgSome t
  -- spanning of the family e
  let s : (L ⧸ K) →ₗ[ℤ] L := bq.constr ℤ lt
  have hsec : K.mkQ.comp s = (LinearMap.id : (L ⧸ K) →ₗ[ℤ] L ⧸ K) := by
    refine bq.ext ?_
    intro t
    simp [s, hlt]
  have hsp : (⊤ : Submodule ℤ L) ≤ span ℤ (Set.range e) := by
    intro x hx
    let y : L := s (K.mkQ x)
    have hmkdiff : K.mkQ (x - y) = 0 := by
      have h1 : K.mkQ (s (K.mkQ x)) = K.mkQ x := by
        have hc := congrArg (fun (f : (L ⧸ K) →ₗ[ℤ] (L ⧸ K)) => f (K.mkQ x)) hsec
        simpa using hc
      rw [map_sub, h1]
      simp
    have hdiffK : x - y ∈ K := (hmem0 (x - y)).mp hmkdiff
    rcases (Submodule.mem_span_singleton.mp hdiffK) with ⟨c, hc⟩
    have hy_span : y ∈ span ℤ (Set.range e) := by
      have hy_range : y ∈ LinearMap.range s := by
        refine ⟨K.mkQ x, ?_⟩
        rfl
      have hy_lt : y ∈ span ℤ (Set.range lt) := by
        rw [← bq.constr_range (S := ℤ) (f := lt)]
        simpa [s] using hy_range
      have hmono : span ℤ (Set.range lt) ≤ span ℤ (Set.range e) := by
        apply Submodule.span_mono
        intro z hz
        rcases hz with ⟨t, rfl⟩
        exact ⟨some t, by simp [e]⟩
      exact hmono hy_lt
    have hc_span : c • w ∈ span ℤ (Set.range e) := by
      apply Submodule.smul_mem
      exact subset_span ⟨none, by simp [e]⟩
    have hx_eq : x = y + c • w := by
      calc
        x = y + (x - y) := by abel
        _ = y + c • w := by rw [← hc]
    have hx_mem : x ∈ span ℤ (Set.range e) := by
      rw [hx_eq]
      exact Submodule.add_mem _ hy_span hc_span
    exact hx_mem
  let bfin : Basis (Option (Fin n)) ℤ L := Basis.mk hli hsp
  refine ⟨ULift (Fin n), bfin.reindex (Equiv.optionCongr Equiv.ulift).symm, ?_⟩
  have hb : bfin none = w := by
    simpa [bfin, e] using (Basis.mk_apply hli hsp (i := none))
  have hb0 : (bfin none : E) = v := by
    rw [hb]
  have hnone : ((Equiv.optionCongr Equiv.ulift).symm.symm none) = (none : Option (Fin n)) := by
    rw [Equiv.symm_symm]
    simp [Equiv.optionCongr_apply]
  rw [Basis.reindex_apply, hnone, hb0]

end Submission.CovExt
