import Mathlib
import Submission.CellContinuity
import Submission.GaussianMeasure
import Submission.VoronoiMeasure
import Submission.StableClosure
import Submission.StableLattices
import Submission.LatticeBasics
import Submission.Filtration
import Submission.Transport
import Submission.Commons.LinearAlgebra.Matrix.det_gram_mul_relative_lower
import Submission.Commons.LinearAlgebra.Matrix.det_gram_mul_relative_lower_all
import Submission.Commons.Analysis.Real.one_sub_pow_ge_one_sub_mul

open Module Real Matrix
open Submission.CellContinuity
open Submission.LatticeParam
open Submission.StableClosure
open Submission.StableCompact
open Submission.QuotientLattice
open Submission.StableLattices
open scoped Real BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Stability is open at determinant-one-free stable points (paper Prop 2.5(iv), interior half)

The interior branch of the rank induction (`gamma_stable_of_two_le`) needs: a *global
γ-minimizer* `ℳ` over the stable family with NO strict determinant-one primitive sublattice
(`hno`) is a local minimum of `γ_{1/t_m}(V(·))` over the determinant-one lattices — i.e. the
stable set contains a whole determinant-one neighbourhood of `ℳ` (then global minimality
over the stable family forces local minimality over the neighbourhood).

This module proves the matrix form of that openness statement:

**`stable_near_stable_no_det_one`** — for an invertible basis matrix `B₀` with
`Stable (latticeOfMatrix B₀)` and no strict det-one primitive sublattice, there is `δ > 0`
such that every determinant-one `A` with all entries within `δ` of `B₀` has
`Stable (latticeOfMatrix A)`.

Proof architecture (the three pieces of the Session-103b design):

* (O2, DONE here) `sqrt_det_gram_relative_lower` — the uniform relative volume bound:
  for `A` entrywise `δ`-close to invertible `B₀`, every coefficient matrix
  `U : Matrix (Fin m) (Fin r) ℤ` satisfies
  `(1 - C·δ)^r · √det(UᵀB₀ᵀB₀U) ≤ √det(UᵀAᵀAU)`.  This is the square-root corollary of
  the commons theorem `Commons.LinearAlgebra.Matrix.det_gram_mul_relative_lower` (child L93).
  In the code's `volColSum` language (`volColSum cs A = √det(Gram(colSum A csₖ))`, whose Gram
  matrix is `UᵀAᵀAU` for `U` the column matrix of `cs`), it says every sublattice
  determinant of `latticeOfMatrix A` is at least `(1-C·δ)^r` times the corresponding
  sublattice determinant of `latticeOfMatrix B₀`.

* (O1, DONE) `margin_of_no_det_one` — the strict uniform margin: `∃ ε₀ ∈ (0,1]`, every
  sublattice of rank `r ∈ [1, m)` of the stable `latticeOfMatrix B₀` has determinant
  `≥ 1 + ε₀`.  Proof: contradiction — a sequence of rank-`[1,m)` sublattices with
  `det < 1 + 1/(n+1)` all lie in the finite multi-rank set `⋃_{r<m} finSet L r`
  (`mem_fin_set_of_det_le` + `union_finSet_finite`); the value function
  `v n := det (L' n) [discreteTopology_of_le]` has finite range, `v n ≥ 1` (stability) and
  `v n < 1 + 1/(n+1)`, so the finite nonempty value set has minimum `1` (Finset.min'
  argument), giving a det-one sublattice of rank `[1,m)` — contradicting
  `no_det_one_of_no_det_one_sublattice` (primitive closure).

* (O3, DONE) `stable_near_stable_no_det_one` (the openness theorem) + the internal-δ
  main-rank lemma `subdet_ge_one_close` are PROVEN: δ chosen internally as
  `ε₀/(C₀·(m:ℝ)·(1+ε₀))` from the margin ε₀ and the rank-uniform relative constant C₀
  (`sqrt_det_gram_relative_lower_all`); rank-1≤r<m sublattices bounded via relative basis
  `cs`, `det ℒ' = √det(UcᵀAᵀAUc)` (gram bridge), `(1-C₀δ)^r·√(B₀-part) ≤ det ℒ'`
  (relative bound at U := csMatℤ cs), B₀-part = det(spanColSum B₀ cs) ≥ 1+ε₀ (margin),
  Bernoulli + margin arithmetic; rank-0 via `eq_bot_of_finrank_zero` + `det_bot`; full-rank
  via `det_le_of_submodule_same_rank` + `det = |det A| = 1`; `finrank_le_of_le` bounds the
  rank.  This completes the whole interior-openness input of the γ-route (matrix form of
  paper Prop 2.5(iv) "interior" half).

NOTE: this module is OFF the Solution import path.  It now has ZERO sorries: the full
openness theorem `stable_near_stable_no_det_one` (O3) is proven.  It is the
interior-branch openness input: feed it through the global γ-minimizer machinery to get
"no strict det-one primitive sublattice ⟹ local minimum over the determinant-one
lattices" for the interior branch of `gamma_stable_of_two_le`.
-/

namespace Submission.StableOpen

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

/-- Square-root (volume) form of the uniform relative Gram bound: for `A` entrywise `δ`-close
to invertible `B₀`, every integer coefficient matrix `U` satisfies
`√det(UᵀAᵀAU) ≥ (1 - C·δ)^r · √det(UᵀB₀ᵀB₀U)`.  (O2: uniform relative volume bound.) -/
theorem sqrt_det_gram_relative_lower {r : ℕ} (B₀ : Matrix (Fin m) (Fin m) ℝ)
    (hB : B₀.det ≠ 0) :
    ∃ (C : ℝ), 0 < C ∧
    ∀ (δ : ℝ), 0 ≤ δ → C * δ ≤ (1 : ℝ) / 2 →
    ∀ (A : Matrix (Fin m) (Fin m) ℝ),
      (∀ j i : Fin m, |A j i - B₀ j i| ≤ δ) →
      ∀ U : Matrix (Fin m) (Fin r) ℤ,
        let Uc : Matrix (Fin m) (Fin r) ℝ := U.map (fun z : ℤ => (z : ℝ))
        (1 - C * δ) ^ r * Real.sqrt ((Uc.transpose * B₀.transpose * B₀ * Uc).det) ≤
          Real.sqrt ((Uc.transpose * A.transpose * A * Uc).det) := by
  classical
  rcases Commons.LinearAlgebra.Matrix.det_gram_mul_relative_lower (m := m) (r := r) B₀ hB with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro δ hδ0 hCδ A hA U
  have hrel := hC δ hδ0 hCδ A hA U
  let dVol : ℝ := ((U.map (fun z : ℤ => (z : ℝ))).transpose * B₀.transpose * B₀ *
    (U.map (fun z : ℤ => (z : ℝ)))).det
  let eVol : ℝ := ((U.map (fun z : ℤ => (z : ℝ))).transpose * A.transpose * A *
    (U.map (fun z : ℤ => (z : ℝ)))).det
  have h1m : 0 ≤ 1 - C * δ := by linarith
  have hpow0 : 0 ≤ (1 - C * δ) ^ r := pow_nonneg h1m r
  have hD0 : 0 ≤ dVol := by
    dsimp [dVol]
    exact Matrix.PosSemidef.det_nonneg
      (by
        have hBpsd : (B₀.transpose * B₀).PosSemidef := by
          have hh := Matrix.posSemidef_conjTranspose_mul_self (R := ℝ) B₀
          simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hh
        have hcong := hBpsd.conjTranspose_mul_mul_same (U.map (fun z : ℤ => (z : ℝ)))
        simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using hcong)
  have hE0 : 0 ≤ eVol := by
    dsimp [eVol]
    exact Matrix.PosSemidef.det_nonneg
      (by
        have hApsd : (A.transpose * A).PosSemidef := by
          have hh := Matrix.posSemidef_conjTranspose_mul_self (R := ℝ) A
          simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hh
        have hcong := hApsd.conjTranspose_mul_mul_same (U.map (fun z : ℤ => (z : ℝ)))
        simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using hcong)
  have hsq : ((1 - C * δ) ^ r * Real.sqrt dVol) ^ 2 ≤ (Real.sqrt eVol) ^ 2 := by
    calc
      ((1 - C * δ) ^ r * Real.sqrt dVol) ^ 2 = (1 - C * δ) ^ (2 * r) * dVol := by
        rw [mul_pow]
        rw [Real.sq_sqrt hD0]
        congr 1
        ring_nf
      _ ≤ eVol := by
        dsimp [dVol, eVol]
        simpa [mul_assoc] using hrel
      _ = (Real.sqrt eVol) ^ 2 := by rw [Real.sq_sqrt hE0]
  have habs := sq_le_sq.mp hsq
  have hleft : 0 ≤ (1 - C * δ) ^ r * Real.sqrt dVol := mul_nonneg hpow0 (Real.sqrt_nonneg dVol)
  have hright : 0 ≤ Real.sqrt eVol := Real.sqrt_nonneg eVol
  simpa [abs_of_nonneg hleft, abs_of_nonneg hright] using habs

/-- The interior-branch `hno` hypothesis: no strict primitive determinant-one sublattice of
rank in `[1, m)`. -/
def NoDetOneSublattice (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] : Prop :=
  ¬ ∃ (ℒ' : Submodule ℤ E) (_hd : DiscreteTopology ℒ'),
      ℒ' ≤ ℒ ∧ Submission.QuotientLattice.Primitive ℒ' ℒ ∧
      ReverseMinkowski.determinant ℒ' = 1 ∧ 1 ≤ Module.finrank ℤ ℒ' ∧ Module.finrank ℤ ℒ' < m


/-! ### Helper machinery (proven) — primitive closures and the hno reduction -/

/-- The primitive closure of `ℒ'` inside `L`: `L ∩ realSpan ℒ'` (as a `ℤ`-submodule). -/
def primClosure {L : Submodule ℤ E} (ℒ' : Submodule ℤ E) : Submodule ℤ E :=
  L ⊓ (realSpan ℒ').restrictScalars ℤ

lemma primClosure_le {L : Submodule ℤ E} (ℒ' : Submodule ℤ E) : primClosure (L := L) ℒ' ≤ L := by
  exact inf_le_left

lemma le_primClosure_of_le {L : Submodule ℤ E} {ℒ' : Submodule ℤ E} (h : ℒ' ≤ L) :
    ℒ' ≤ primClosure (L := L) ℒ' := by
  intro x hx
  exact ⟨h hx, mem_realSpan (ℒ := ℒ') hx⟩

lemma realSpan_primClosure {L : Submodule ℤ E} {ℒ' : Submodule ℤ E} (h : ℒ' ≤ L) :
    realSpan (primClosure (L := L) ℒ') = realSpan ℒ' := by
  apply le_antisymm
  · apply Submodule.span_le.2
    intro x hx
    exact hx.2
  · have hsub : (ℒ' : Set E) ⊆ (primClosure (L := L) ℒ' : Set E) := by
      intro x hx
      exact le_primClosure_of_le h hx
    simpa [realSpan] using (Submodule.span_mono hsub)

lemma primitive_primClosure {L : Submodule ℤ E} {ℒ' : Submodule ℤ E} (h : ℒ' ≤ L) :
    Primitive (primClosure (L := L) ℒ') L := by
  intro x
  rw [realSpan_primClosure h]
  rfl

/-- A det-one sublattice of rank in `[1, m)` of a stable `L` contradicts `hno`: its
primitive closure is a primitive det-one sublattice. -/
lemma no_det_one_of_no_det_one_sublattice {L : Submodule ℤ E} [DiscreteTopology L]
    (hSt : Stable L) (hno : NoDetOneSublattice L) :
    ¬ ∃ (ℒ'' : Submodule ℤ E) (_hd : DiscreteTopology ℒ''),
      ℒ'' ≤ L ∧ ReverseMinkowski.determinant ℒ'' = 1 ∧
      1 ≤ Module.finrank ℤ ℒ'' ∧ Module.finrank ℤ ℒ'' < m := by
  intro h
  rcases h with ⟨ℒ'', hDT, hle, hd1, hr1, hrm⟩
  haveI : DiscreteTopology ℒ'' := hDT
  have hdPC : DiscreteTopology (primClosure (L := L) ℒ'') := by
    exact Submission.LatticeBasics.discreteTopology_of_le (primClosure_le ℒ'')
  haveI : DiscreteTopology (primClosure (L := L) ℒ'') := hdPC
  have hlePC : ℒ'' ≤ primClosure (L := L) ℒ'' := le_primClosure_of_le hle
  have hfinPC : Module.finrank ℤ (primClosure (L := L) ℒ'') = Module.finrank ℤ ℒ'' := by
    rw [← Submission.Transport.realSpan_finrank (ℒ := primClosure (L := L) ℒ'')]
    rw [realSpan_primClosure hle]
    exact Submission.Transport.realSpan_finrank (ℒ := ℒ'')
  have hdetPC_le : ReverseMinkowski.determinant (primClosure (L := L) ℒ'') ≤
      ReverseMinkowski.determinant ℒ'' := by
    exact Submission.Filtration.det_le_of_submodule_same_rank (N := ℒ'') (L := primClosure (L := L) ℒ'')
      hlePC hfinPC.symm
  have hdetPC_ge : (1 : ℝ) ≤ ReverseMinkowski.determinant (primClosure (L := L) ℒ'') := by
    exact hSt.2 (primClosure (L := L) ℒ'') (primClosure_le ℒ'')
  have hdetPC : ReverseMinkowski.determinant (primClosure (L := L) ℒ'') = 1 := by
    apply le_antisymm
    · rw [hd1] at hdetPC_le
      exact hdetPC_le
    · exact hdetPC_ge
  have hprim : Primitive (primClosure (L := L) ℒ'') L := primitive_primClosure hle
  have hfin1 : 1 ≤ Module.finrank ℤ (primClosure (L := L) ℒ'') := by rwa [hfinPC]
  have hfinm : Module.finrank ℤ (primClosure (L := L) ℒ'') < m := by rwa [hfinPC]
  exact hno ⟨primClosure (L := L) ℒ'', hdPC, primClosure_le ℒ'', hprim, hdetPC, hfin1, hfinm⟩


/-- `ReverseMinkowski.determinant` is independent of the discreteness instance (any two
instances on the same submodule give the same value).  This unlocks value-set arguments
over sublattices where the instance is supplied per element. -/
lemma det_indep_instance {M : Submodule ℤ E} (hd₁ hd₂ : DiscreteTopology M) :
    @ReverseMinkowski.determinant m M hd₁ = @ReverseMinkowski.determinant m M hd₂ := by
  exact @Submission.Uncrossing.det_eq_of_eq m M M hd₁ hd₂ rfl


/-- **(O1 step 1)** A rank-`r` sublattice `M ≤ L` with `det M ≤ 2` lies in the commons
finite per-rank set (witness `w` = its finBasis values, `gram(w).det ≤ 4`). -/
lemma mem_fin_set_of_det_le {L M : Submodule ℤ E} [DiscreteTopology L]
    [DiscreteTopology M] (hle : M ≤ L) (r : ℕ) (hr : Module.finrank ℤ M = r)
    (hdet : ReverseMinkowski.determinant M ≤ 2) :
    M ∈ {M' : Submodule ℤ E | M' ≤ L ∧ Module.finrank ℤ M' = r ∧
      (∃ w : Fin r → E,
        (∀ i : Fin r, w i ∈ M') ∧
        (∀ ⦃x⦄, x ∈ M' → x ∈ Submodule.span ℤ (Set.range w)) ∧
        (Matrix.gram ℝ w).det ≤ (2 : ℝ) ^ 2)} := by
  classical
  haveI : Module.Free ℤ M := instModuleFree_of_discrete_submodule M
  haveI : Module.Finite ℤ M := instModuleFinite_of_discrete_submodule M
  let β : Module.Basis (Fin r) ℤ M :=
    (Module.finBasis ℤ M).reindex (Equiv.cast (congrArg Fin hr))
  let w : Fin r → E := fun i => ((β i : M) : E)
  refine ⟨hle, hr, w, ?_, ?_, ?_⟩
  · intro i
    exact (β i).property
  · intro x hx
    have hspan : Submodule.span ℤ (Set.range (fun j : Fin r => ((β j : M) : E))) = M := by
      exact span_values_eq_lattice β
    change x ∈ Submodule.span ℤ (Set.range (fun j : Fin r => ((β j : M) : E)))
    rw [hspan]
    exact hx
  · have hg : ReverseMinkowski.determinant M = Real.sqrt ((Matrix.gram ℝ w).det) := by
      dsimp [w]
      exact Submission.Uncrossing.det_eq_sqrt_gram_any_basis (L := M) (r := r) β
    have hg0 : 0 ≤ (Matrix.gram ℝ w).det := by
      exact (Matrix.posSemidef_gram ℝ w).det_nonneg
    have hle2 : Real.sqrt ((Matrix.gram ℝ w).det) ≤ 2 := by
      rwa [hg] at hdet
    have hsq : (Matrix.gram ℝ w).det ≤ (2 : ℝ) ^ 2 := by
      have hsq0 : 0 ≤ Real.sqrt ((Matrix.gram ℝ w).det) := Real.sqrt_nonneg _
      have hsqb : (Real.sqrt ((Matrix.gram ℝ w).det)) ^ 2 ≤ 2 ^ 2 :=
        pow_le_pow_left₀ hsq0 hle2 2
      calc
        (Matrix.gram ℝ w).det = (Real.sqrt ((Matrix.gram ℝ w).det)) ^ 2 := (Real.sq_sqrt hg0).symm
        _ ≤ 2 ^ 2 := hsqb
        _ = (2 : ℝ) ^ 2 := by norm_num
    exact hsq


/-- Per-rank commons-style finite set (gram-based; no discreteness in the predicate). -/
def finSet (L : Submodule ℤ E) (r : ℕ) : Set (Submodule ℤ E) :=
  {M | M ≤ L ∧ Module.finrank ℤ M = r ∧
    ∃ w : Fin r → E,
      (∀ i : Fin r, w i ∈ M) ∧
      (∀ ⦃x⦄, x ∈ M → x ∈ Submodule.span ℤ (Set.range w)) ∧
      (Matrix.gram ℝ w).det ≤ (2 : ℝ) ^ 2}

lemma finSet_finite {L : Submodule ℤ E} [DiscreteTopology L] (hLz : IsZLattice ℝ L) (r : ℕ) :
    (finSet L r).Finite := by
  simpa [finSet] using
    (Commons.Lattice.Minimizer.finite_sublattices_det_le (n := m) (r := r) (L := L) (C := 2))

/-- **(O1 step 2)** The union over ranks `< m` of the per-rank finite sets is finite. -/
lemma union_finSet_finite {L : Submodule ℤ E} [DiscreteTopology L] (hLz : IsZLattice ℝ L) :
    (⋃ r ∈ (↑(Finset.range m) : Set ℕ), finSet L r).Finite := by
  exact (Finset.range m).finite_toSet.biUnion (fun r _hr => finSet_finite (L := L) hLz r)

/-- **(O1, OPEN — margin).** A stable lattice with no strict det-one primitive sublattice has
a uniform margin `ε₀ > 0` for the determinants of all its strict rank-`r ∈ [1, m)`
sublattices. -/
theorem margin_of_no_det_one (B₀ : Matrix (Fin m) (Fin m) ℝ)
    (hdet₀ : B₀.det ≠ 0)
    (hSt : @Stable m (latticeOfMatrix B₀) (latticeOfMatrix_discrete B₀ hdet₀))
    (hno : @NoDetOneSublattice m (latticeOfMatrix B₀) (latticeOfMatrix_discrete B₀ hdet₀)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧
    ∀ (ℒ' : Submodule ℤ E) (_hd : DiscreteTopology ℒ'),
      ℒ' ≤ latticeOfMatrix B₀ → 1 ≤ Module.finrank ℤ ℒ' → Module.finrank ℤ ℒ' < m →
      (1 : ℝ) + ε₀ ≤ ReverseMinkowski.determinant ℒ' := by
  classical
  let L : Submodule ℤ E := latticeOfMatrix B₀
  haveI : DiscreteTopology L := latticeOfMatrix_discrete B₀ hdet₀
  have hLfin : Module.finrank ℤ L = m := by
    dsimp [L]
    exact finrank_latticeOfMatrix B₀ hdet₀
  have hLz : IsZLattice ℝ L := by
    dsimp [L]
    exact Submission.MainStable.isZLattice_of_finrank (n := m) (latticeOfMatrix B₀) hLfin
  by_cases hm1 : m ≤ 1
  · refine ⟨1, by norm_num, by norm_num, ?_⟩
    intro ℒ' _hd hle hr1 hrm
    omega
  · have hm2 : 2 ≤ m := by omega
    by_contra h
    have hseq : ∀ n : ℕ, ∃ (ℒ' : Submodule ℤ E) (_hd : DiscreteTopology ℒ'),
        ℒ' ≤ L ∧ 1 ≤ Module.finrank ℤ ℒ' ∧ Module.finrank ℤ ℒ' < m ∧
        ReverseMinkowski.determinant ℒ' < 1 + 1 / ((n : ℝ) + 1) := by
      intro n
      let ε : ℝ := 1 / ((n : ℝ) + 1)
      have hε0 : 0 < ε := by dsimp [ε]; positivity
      have hε1 : ε ≤ 1 := by
        dsimp [ε]
        have hpos : 0 < (n : ℝ) + 1 := by positivity
        have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
        rw [div_le_iff₀ hpos]
        nlinarith
      have hnotQ : ¬ ∀ (ℒ'' : Submodule ℤ E) (_hd : DiscreteTopology ℒ''),
          ℒ'' ≤ L → 1 ≤ Module.finrank ℤ ℒ'' → Module.finrank ℤ ℒ'' < m →
          (1 : ℝ) + ε ≤ ReverseMinkowski.determinant ℒ'' := by
        intro hQ
        exact h ⟨ε, hε0, hε1, hQ⟩
      push_neg at hnotQ
      rcases hnotQ with ⟨ℒ', hd, hle, hr1, hrm, hlt⟩
      refine ⟨ℒ', hd, hle, hr1, hrm, ?_⟩
      simpa [ε] using hlt
    let L' : ℕ → Submodule ℤ E := fun n => Classical.choose (hseq n)
    have hspec (n : ℕ) : ∃ (_hd : DiscreteTopology (L' n)),
        L' n ≤ L ∧ 1 ≤ Module.finrank ℤ (L' n) ∧ Module.finrank ℤ (L' n) < m ∧
        ReverseMinkowski.determinant (L' n) < 1 + 1 / ((n : ℝ) + 1) := by
      exact Classical.choose_spec (hseq n)
    let hd : ∀ n : ℕ, DiscreteTopology (L' n) := fun n => Classical.choose (hspec n)
    have hspec2 (n : ℕ) : L' n ≤ L ∧ 1 ≤ Module.finrank ℤ (L' n) ∧
        Module.finrank ℤ (L' n) < m ∧
        ReverseMinkowski.determinant (L' n) < 1 + 1 / ((n : ℝ) + 1) := by
      exact Classical.choose_spec (hspec n)
    have hle (n : ℕ) : L' n ≤ L := (hspec2 n).1
    have hr1 (n : ℕ) : 1 ≤ Module.finrank ℤ (L' n) := (hspec2 n).2.1
    have hrm (n : ℕ) : Module.finrank ℤ (L' n) < m := (hspec2 n).2.2.1
    have hlt (n : ℕ) : ReverseMinkowski.determinant (L' n) < 1 + 1 / ((n : ℝ) + 1) := (hspec2 n).2.2.2
    have hone_div (n : ℕ) : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      rw [div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)]
      nlinarith
    have hlt2 (n : ℕ) : ReverseMinkowski.determinant (L' n) ≤ 2 := by
      exact le_trans (le_of_lt (hlt n)) (by nlinarith [hone_div n])
    have hmem (n : ℕ) : L' n ∈ (⋃ r ∈ (↑(Finset.range m) : Set ℕ), finSet L r) := by
      haveI : DiscreteTopology (L' n) := hd n
      have hmemr := mem_fin_set_of_det_le (L := L) (M := L' n) (hle n)
        (Module.finrank ℤ (L' n)) rfl (hlt2 n)
      rw [Set.mem_iUnion₂]
      refine ⟨Module.finrank ℤ (L' n), ?_, ?_⟩
      · exact Finset.mem_range.mpr (hrm n)
      · simpa [finSet] using hmemr
    -- final contradiction: values in a finite set, min = 1, det-one sublattice
    have hFFfin : (⋃ r ∈ (↑(Finset.range m) : Set ℕ), finSet L r).Finite := by
      exact union_finSet_finite (L := L) hLz
    let v : ℕ → ℝ := fun n => @ReverseMinkowski.determinant m (L' n)
      (Submission.LatticeBasics.discreteTopology_of_le (ℒ := L) (ℒ' := L' n) (hle n))
    have vge1 (n : ℕ) : 1 ≤ v n := by
      dsimp [v]
      exact hSt.2 (L' n) (hle n)
    have hvlt (n : ℕ) : v n < 1 + 1 / ((n : ℝ) + 1) := by
      dsimp [v]
      haveI : DiscreteTopology (L' n) := hd n
      rw [Submission.StableOpen.det_indep_instance (M := L' n) (Submission.LatticeBasics.discreteTopology_of_le (hle n)) (hd n)]
      exact hlt n
    -- finite range of v
    let S : Set (Submodule ℤ E) := ⋃ r ∈ (↑(Finset.range m) : Set ℕ), finSet L r
    have hSfin : S.Finite := by dsimp [S]; exact hFFfin
    have hleS (M : Submodule ℤ E) (hM : M ∈ S) : M ≤ L := by
      rw [Set.mem_iUnion₂] at hM
      rcases hM with ⟨r, _hr, hfin⟩
      exact hfin.1
    let detSub : {M : Submodule ℤ E // M ∈ S} → ℝ := fun x =>
      @ReverseMinkowski.determinant m x.1
        (Submission.LatticeBasics.discreteTopology_of_le (hleS x.1 x.2))
    have hfac (n : ℕ) : v n = detSub ⟨L' n, hmem n⟩ := by
      dsimp [v, detSub]
    have hrangeFin : (Set.range v).Finite := by
      haveI : Finite {M : Submodule ℤ E // M ∈ S} := by
        exact hSfin
      have hdetFin : (Set.range detSub).Finite := Set.finite_range detSub
      refine hdetFin.subset ?_
      rintro r ⟨n, rfl⟩
      exact ⟨⟨L' n, hmem n⟩, (hfac n).symm⟩
    -- min argument
    have hVne : (Set.range v).Nonempty := ⟨v 0, ⟨0, rfl⟩⟩
    let Vf : Finset ℝ := hrangeFin.toFinset
    have hVfn : Vf.Nonempty := by
      refine ⟨v 0, ?_⟩
      exact (hrangeFin.mem_toFinset).2 ⟨0, rfl⟩
    let m₀ : ℝ := Vf.min' hVfn
    have hm₀range : m₀ ∈ Set.range v := by
      exact (hrangeFin.mem_toFinset).1 (Vf.min'_mem hVfn)
    rcases hm₀range with ⟨n₀, hn₀⟩
    have h1le : (1 : ℝ) ≤ m₀ := by
      rw [← hn₀]
      exact vge1 n₀
    have hml1 : m₀ ≤ 1 := by
      refine le_of_forall_pos_le_add ?_
      intro δ hδ
      have hδ0 : 0 < δ := hδ
      rcases exists_nat_gt ((1 : ℝ) / δ) with ⟨N, hN⟩
      have hsmall : (1 : ℝ) / ((N : ℝ) + 1) < δ := by
        rw [div_lt_iff₀ (by positivity : 0 < (N : ℝ) + 1)]
        have hδne : δ ≠ 0 := ne_of_gt hδ0
        have hmul := mul_lt_mul_of_pos_left hN hδ0
        have hδinv : δ * ((1 : ℝ) / δ) = 1 := by field_simp [hδne]
        have h1 : (1 : ℝ) < δ * (N : ℝ) := by nlinarith
        nlinarith
      have hvn : v N < 1 + δ := by
        have hvN : v N < 1 + 1 / ((N : ℝ) + 1) := hvlt N
        linarith
      have hm₀le : m₀ ≤ v N := by
        have hvNV : v N ∈ Vf := (hrangeFin.mem_toFinset).2 ⟨N, rfl⟩
        exact Finset.min'_le Vf (v N) hvNV
      linarith
    have hm₀eq : m₀ = 1 := le_antisymm hml1 h1le
    have hv1 : v n₀ = 1 := by
      rw [hn₀]
      exact hm₀eq
    haveI : DiscreteTopology (L' n₀) := hd n₀
    have hd1 : ReverseMinkowski.determinant (L' n₀) = 1 := by
      have hb : ReverseMinkowski.determinant (L' n₀) = v n₀ := by
        dsimp [v]
      rw [hb, hv1]
    exact no_det_one_of_no_det_one_sublattice hSt hno ⟨L' n₀, hd n₀, hle n₀, hd1, hr1 n₀, hrm n₀⟩


/-! ### Coefficient-matrix bridge helpers (O3) — verified in scratch -/

/-- coefficient matrix (real): column k is the coefficient vector of `cs k` -/
def csMatℝ {r : ℕ} (cs : Fin r → Fin m → ℤ) : Matrix (Fin m) (Fin r) ℝ :=
  fun j k => (cs k j : ℝ)

/-- coefficient matrix (integer) -/
def csMatℤ {r : ℕ} (cs : Fin r → Fin m → ℤ) : Matrix (Fin m) (Fin r) ℤ :=
  fun j k => cs k j

lemma csMatℝ_eq_map {r : ℕ} (cs : Fin r → Fin m → ℤ) :
    csMatℝ cs = (csMatℤ cs).map (fun z : ℤ => (z : ℝ)) := by
  ext j k
  rfl

/-- `colSum A a = A.mulVec a` (coordinatewise). -/
lemma colSum_eq_mulVec (A : Matrix (Fin m) (Fin m) ℝ) (a : Fin m → ℝ) :
    colSum A a = A.mulVec a := by
  ext j
  simp [colSum, cols, Matrix.mulVec, dotProduct, mul_comm]

lemma dotProduct_mulVec_mulVec (A : Matrix (Fin m) (Fin m) ℝ) (u v : Fin m → ℝ) :
    dotProduct (A.mulVec u) (A.mulVec v) = dotProduct u ((A.transpose * A) *ᵥ v) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec]
  rw [← Matrix.dotProduct_mulVec]

lemma inner_colSum_colSum (A : Matrix (Fin m) (Fin m) ℝ) (u v : Fin m → ℝ) :
    inner ℝ (colSum A u) (colSum A v) = dotProduct u ((A.transpose * A) *ᵥ v) := by
  calc
    inner ℝ (colSum A u) (colSum A v) = ∑ j : Fin m, (colSum A u) j * (colSum A v) j := by
      simp [inner]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = dotProduct (A.mulVec u) (A.mulVec v) := by
      rw [colSum_eq_mulVec A u, colSum_eq_mulVec A v]
      rfl
    _ = dotProduct u ((A.transpose * A) *ᵥ v) := by
      exact dotProduct_mulVec_mulVec A u v
lemma dotProduct_col_col {r : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (U : Matrix (Fin m) (Fin r) ℝ)
    (k l : Fin r) :
    dotProduct (fun p : Fin m => U p k) (M *ᵥ fun p : Fin m => U p l) =
      ((U.transpose * M * U) k l) := by
  calc
    dotProduct (fun p : Fin m => U p k) (M *ᵥ fun p : Fin m => U p l)
        = dotProduct ((fun p : Fin m => U p k) ᵥ* M) (fun p : Fin m => U p l) := by
            rw [Matrix.dotProduct_mulVec]
    _ = dotProduct (fun q : Fin m => (U.transpose * M) k q) (fun p : Fin m => U p l) := by
            apply congrArg (fun w : Fin m → ℝ => dotProduct w (fun p : Fin m => U p l))
            ext q
            simp [Matrix.vecMul, Matrix.mul_apply, dotProduct]
    _ = ((U.transpose * M * U) k l) := by
            simp [Matrix.mul_apply, dotProduct]

lemma gram_colSum_csMat (A : Matrix (Fin m) (Fin m) ℝ) {r : ℕ}
    (cs : Fin r → Fin m → ℤ) :
    Matrix.gram ℝ (fun k : Fin r => colSum A (fun i : Fin m => (cs k i : ℝ))) =
      (csMatℝ cs).transpose * A.transpose * A * (csMatℝ cs) := by
  classical
  ext k l
  calc
    (Matrix.gram ℝ (fun kk : Fin r => colSum A (fun i : Fin m => (cs kk i : ℝ)))) k l
        = inner ℝ (colSum A (fun i : Fin m => (cs k i : ℝ)))
            (colSum A (fun i : Fin m => (cs l i : ℝ))) := by
          rfl
    _ = dotProduct (fun i : Fin m => (cs k i : ℝ))
          ((A.transpose * A) *ᵥ (fun i : Fin m => (cs l i : ℝ))) := by
          exact inner_colSum_colSum A (fun i : Fin m => (cs k i : ℝ)) (fun i : Fin m => (cs l i : ℝ))
    _ = (((csMatℝ cs).transpose * A.transpose * A * (csMatℝ cs)) k l) := by
          simpa [csMatℝ, Matrix.mul_assoc] using (dotProduct_col_col (A.transpose * A) (csMatℝ cs) k l)


lemma colSum_add_coeff (B₀ : Matrix (Fin m) (Fin m) ℝ) (u v : Fin m → ℤ) :
    colSum B₀ (fun i : Fin m => (((u + v) i : ℤ) : ℝ)) =
      colSum B₀ (fun i : Fin m => (u i : ℝ)) + colSum B₀ (fun i : Fin m => (v i : ℝ)) := by
  have hc : (fun i : Fin m => (((u + v) i : ℤ) : ℝ)) =
      (fun i : Fin m => (u i : ℝ)) + (fun i : Fin m => (v i : ℝ)) := by
    ext i
    simp
  rw [hc]
  exact colSum_add B₀ (fun i : Fin m => (u i : ℝ)) (fun i : Fin m => (v i : ℝ))

lemma colSum_zsmul_coeff (B₀ : Matrix (Fin m) (Fin m) ℝ) (z : ℤ) (u : Fin m → ℤ) :
    colSum B₀ (fun i : Fin m => (((z • u) i : ℤ) : ℝ)) =
      z • colSum B₀ (fun i : Fin m => (u i : ℝ)) := by
  have hc : (fun i : Fin m => (((z • u) i : ℤ) : ℝ)) =
      (z : ℝ) • (fun i : Fin m => (u i : ℝ)) := by
    ext i
    simp [Pi.smul_apply, Int.cast_mul]
  rw [hc]
  rw [colSum_smul B₀ (z : ℝ) (fun i : Fin m => (u i : ℝ))]
  exact (Int.cast_smul_eq_zsmul ℝ z (colSum B₀ (fun i : Fin m => (u i : ℝ))))

lemma linearIndependent_colSum_of_linearIndependent (B₀ : Matrix (Fin m) (Fin m) ℝ)
    (hdet₀ : B₀.det ≠ 0) {r : ℕ}
    (cs : Fin r → Fin m → ℤ) (hcsZ : LinearIndependent ℤ cs) :
    LinearIndependent ℤ (fun k : Fin r => colSum B₀ (fun i : Fin m => (cs k i : ℝ))) := by
  let f : (Fin m → ℤ) →ₗ[ℤ] E :=
    { toFun := fun u => colSum B₀ (fun i : Fin m => (u i : ℝ))
      map_add' := by
        intro u v
        exact colSum_add_coeff B₀ u v
      map_smul' := by
        intro z u
        exact colSum_zsmul_coeff B₀ z u }
  have hinj : Function.Injective f := by
    intro u v huv
    have hz : f (u - v) = 0 := by
      rw [map_sub, sub_eq_zero.mpr huv]
    have hfu : colSum B₀ (fun i : Fin m => (((u - v) i : ℤ) : ℝ)) = 0 := by
      simpa [f] using hz
    have hc : (∑ i : Fin m, (((u - v) i : ℤ) : ℝ) • (cols B₀ i)) = 0 := by
      simpa [colSum] using hfu
    have hcb : (∑ i : Fin m, (((u - v) i : ℤ) : ℝ) • (colsBasis B₀ hdet₀ i)) = 0 := by
      simpa [colsBasis_apply] using hc
    funext i
    have hz2 : (((u - v) i : ℤ) : ℝ) = 0 := by
      exact (Fintype.linearIndependent_iff.mp (colsBasis B₀ hdet₀).linearIndependent)
        (fun j : Fin m => (((u - v) j : ℤ) : ℝ)) hcb i
    have hz3 : ((u - v) i : ℤ) = 0 := by exact_mod_cast hz2
    have hsub : u i - v i = 0 := by simpa using hz3
    exact (sub_eq_zero.mp hsub)
  have hker : f.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  exact (hcsZ.map' f hker)

/-- Rank-inside version of `sqrt_det_gram_relative_lower`: the relative-bound constant `C`
is uniform over every rank `r` (used by the internal-δ openness lemma). -/
theorem sqrt_det_gram_relative_lower_all (B₀ : Matrix (Fin m) (Fin m) ℝ)
    (hB : B₀.det ≠ 0) :
    ∃ (C : ℝ), 0 < C ∧
    ∀ (δ : ℝ), 0 ≤ δ → C * δ ≤ (1 : ℝ) / 2 →
    ∀ (A : Matrix (Fin m) (Fin m) ℝ),
      (∀ j i : Fin m, |A j i - B₀ j i| ≤ δ) →
      ∀ {r : ℕ}, ∀ U : Matrix (Fin m) (Fin r) ℤ,
        let Uc : Matrix (Fin m) (Fin r) ℝ := U.map (fun z : ℤ => (z : ℝ))
        (1 - C * δ) ^ r * Real.sqrt ((Uc.transpose * B₀.transpose * B₀ * Uc).det) ≤
          Real.sqrt ((Uc.transpose * A.transpose * A * Uc).det) := by
  classical
  rcases Commons.LinearAlgebra.Matrix.det_gram_mul_relative_lower_all B₀ hB with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro δ hδ0 hCδ A hA r U
  have hrel := hC δ hδ0 hCδ A hA U
  let dVol : ℝ := ((U.map (fun z : ℤ => (z : ℝ))).transpose * B₀.transpose * B₀ *
    (U.map (fun z : ℤ => (z : ℝ)))).det
  let eVol : ℝ := ((U.map (fun z : ℤ => (z : ℝ))).transpose * A.transpose * A *
    (U.map (fun z : ℤ => (z : ℝ)))).det
  have h1m : 0 ≤ 1 - C * δ := by linarith
  have hpow0 : 0 ≤ (1 - C * δ) ^ r := pow_nonneg h1m r
  have hD0 : 0 ≤ dVol := by
    dsimp [dVol]
    exact Matrix.PosSemidef.det_nonneg
      (by
        have hBpsd : (B₀.transpose * B₀).PosSemidef := by
          have hh := Matrix.posSemidef_conjTranspose_mul_self (R := ℝ) B₀
          simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hh
        have hcong := hBpsd.conjTranspose_mul_mul_same (U.map (fun z : ℤ => (z : ℝ)))
        simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using hcong)
  have hE0 : 0 ≤ eVol := by
    dsimp [eVol]
    exact Matrix.PosSemidef.det_nonneg
      (by
        have hApsd : (A.transpose * A).PosSemidef := by
          have hh := Matrix.posSemidef_conjTranspose_mul_self (R := ℝ) A
          simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hh
        have hcong := hApsd.conjTranspose_mul_mul_same (U.map (fun z : ℤ => (z : ℝ)))
        simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using hcong)
  have hsq : ((1 - C * δ) ^ r * Real.sqrt dVol) ^ 2 ≤ (Real.sqrt eVol) ^ 2 := by
    calc
      ((1 - C * δ) ^ r * Real.sqrt dVol) ^ 2 = (1 - C * δ) ^ (2 * r) * dVol := by
        rw [mul_pow]
        rw [Real.sq_sqrt hD0]
        congr 1
        ring_nf
      _ ≤ eVol := by
        dsimp [dVol, eVol]
        simpa [mul_assoc] using hrel
      _ = (Real.sqrt eVol) ^ 2 := by rw [Real.sq_sqrt hE0]
  have habs := sq_le_sq.mp hsq
  have hleft : 0 ≤ (1 - C * δ) ^ r * Real.sqrt dVol := mul_nonneg hpow0 (Real.sqrt_nonneg dVol)
  have hright : 0 ≤ Real.sqrt eVol := Real.sqrt_nonneg eVol
  simpa [abs_of_nonneg hleft, abs_of_nonneg hright] using habs

/-- **(O3 main-rank)** For `A` entrywise `≤ δ`-close to the stable det-one-free `B₀`
(δ satisfying `C·δ ≤ 1/2` and the multiplicative margin `(1+ε₀)(1 − (m:ℝ)·C·δ) ≥ 1`, with
`ε₀`/`C` the margin and relative-bound constants), every sublattice `ℒ'` of
`latticeOfMatrix A` of rank `r ∈ [1, m)` has determinant `≥ 1`.

Standalone so the main-rank argument compiles separately from the rank-0/full-rank wrapper.
-/
theorem subdet_ge_one_close (B₀ : Matrix (Fin m) (Fin m) ℝ) (hm : 2 ≤ m)
    (hdet₀ : B₀.det ≠ 0)
    (hSt : @Stable m (latticeOfMatrix B₀) (latticeOfMatrix_discrete B₀ hdet₀))
    (hno : @NoDetOneSublattice m (latticeOfMatrix B₀) (latticeOfMatrix_discrete B₀ hdet₀)) :
    ∃ δ : ℝ, 0 < δ ∧
    ∀ (A : Matrix (Fin m) (Fin m) ℝ) (hdetA : A.det ≠ 0),
      (∀ j i : Fin m, |A j i - B₀ j i| < δ) →
      ∀ (ℒ' : Submodule ℤ E) (_hd : DiscreteTopology ℒ'),
        ℒ' ≤ latticeOfMatrix A → 1 ≤ Module.finrank ℤ ℒ' → Module.finrank ℤ ℒ' < m →
        1 ≤ ReverseMinkowski.determinant ℒ' := by
  classical
  -- internal constants: margin ε₀ and the rank-uniform relative-bound constant C₀
  rcases margin_of_no_det_one B₀ hdet₀ hSt hno with ⟨ε₀, hε₀pos, hε₀le, hε₀prop⟩
  rcases sqrt_det_gram_relative_lower_all B₀ hdet₀ with ⟨C₀, hC₀pos, hC₀⟩
  let δ : ℝ := ε₀ / (C₀ * (m : ℝ) * (1 + ε₀))
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have h1pe : 0 < 1 + ε₀ := by linarith
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hm)
  have hCδ12 : C₀ * δ ≤ (1 : ℝ) / 2 := by
    dsimp [δ]
    field_simp [hC₀pos.ne', hmR.ne', h1pe.ne']
    have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith [hε₀pos, h1pe, hm2]
  have hmarg : (1 + ε₀) * (1 - (m : ℝ) * C₀ * δ) ≥ 1 := by
    dsimp [δ]
    field_simp [hC₀pos.ne', hmR.ne', h1pe.ne']
    nlinarith
  refine ⟨δ, hδpos, ?_⟩
  intro A hdetA hbox
  haveI : DiscreteTopology (latticeOfMatrix A) := latticeOfMatrix_discrete A hdetA
  have hboxle : ∀ j i : Fin m, |A j i - B₀ j i| ≤ δ := by
    intro j i
    exact le_of_lt (hbox j i)
  intro ℒ' hdL hle hr1 hrm
  haveI : DiscreteTopology ℒ' := hdL
  let L : Submodule ℤ E := latticeOfMatrix B₀
  haveI : DiscreteTopology L := latticeOfMatrix_discrete B₀ hdet₀
  -- SECTION 1: relative basis of ℒ' inside latticeOfMatrix A (mem_span_cols_iff)
  haveI : Module.Free ℤ ℒ' := instModuleFree_of_discrete_submodule ℒ'
  haveI : Module.Finite ℤ ℒ' := instModuleFinite_of_discrete_submodule ℒ'
  let r : ℕ := Module.finrank ℤ ℒ'
  let b : Module.Basis (Fin r) ℤ ℒ' := Module.finBasis ℤ ℒ'
  have hmem_j (j : Fin r) : ((b j : ℒ') : E) ∈ latticeOfMatrix A := by
    exact hle (b j).property
  let cs : Fin r → Fin m → ℤ := fun j =>
    Classical.choose ((mem_span_cols_iff A ((b j : ℒ') : E)).mp (hmem_j j))
  have hcs (j : Fin r) : colSum A (fun i : Fin m => (cs j i : ℝ)) = ((b j : ℒ') : E) := by
    dsimp [cs]
    exact Classical.choose_spec ((mem_span_cols_iff A ((b j : ℒ') : E)).mp (hmem_j j))
  -- SECTION 2: ℤ-independence chain
  have hvalℝ : LinearIndependent ℝ (fun j : Fin r => ((b j : ℒ') : E)) := by
    exact Commons.LinearAlgebra.Independence.discrete_basis_values_linIndep (ℒ := ℒ') b
  have hAℝ : LinearIndependent ℝ (fun k : Fin r => colSum A (fun i : Fin m => (cs k i : ℝ))) := by
    have hfam : (fun k : Fin r => colSum A (fun i : Fin m => (cs k i : ℝ))) =
        fun j : Fin r => ((b j : ℒ') : E) := by
      funext j
      exact hcs j
    rwa [← hfam] at hvalℝ
  have hAZ : LinearIndependent ℤ (fun k : Fin r => colSum A (fun i : Fin m => (cs k i : ℝ))) := by
    exact linearIndependent_int_of_real_colSum A cs hAℝ
  have hcsZ : LinearIndependent ℤ cs := by
    exact linearIndependent_coeffs_of_colSum A cs hAZ
  have hB₀Z : LinearIndependent ℤ (fun k : Fin r => colSum B₀ (fun i : Fin m => (cs k i : ℝ))) := by
    exact linearIndependent_colSum_of_linearIndependent B₀ hdet₀ cs hcsZ
  -- SECTION 3: det ℒ' = √det(UcᵀAᵀAUc)
  have hdet3 : ReverseMinkowski.determinant ℒ' =
      Real.sqrt (((csMatℝ cs).transpose * A.transpose * A * (csMatℝ cs)).det) := by
    have hgram : ReverseMinkowski.determinant ℒ' =
        Real.sqrt ((Matrix.gram ℝ (fun j : Fin r => ((b j : ℒ') : E))).det) := by
      exact Submission.Uncrossing.det_eq_sqrt_gram_any_basis (L := ℒ') b
    have hfam : (fun j : Fin r => ((b j : ℒ') : E)) =
        fun j : Fin r => colSum A (fun i : Fin m => (cs j i : ℝ)) := by
      funext j
      exact (hcs j).symm
    have hg3 : (Matrix.gram ℝ (fun j : Fin r => ((b j : ℒ') : E))).det =
        ((csMatℝ cs).transpose * A.transpose * A * (csMatℝ cs)).det := by
      rw [hfam]
      rw [gram_colSum_csMat A cs]
    rw [hgram]
    rw [hg3]
  -- SECTION 4: B₀-side volume (margin on spanColSum B₀ cs) and the relative bound
  have hL''le : spanColSum B₀ cs ≤ L := by
    dsimp [L]
    exact spanColSum_le_latticeOfMatrix B₀ cs
  have hdL'' : DiscreteTopology (spanColSum B₀ cs) := by
    exact Submission.LatticeBasics.discreteTopology_of_le (ℒ := L) (ℒ' := spanColSum B₀ cs) hL''le
  haveI : DiscreteTopology (spanColSum B₀ cs) := hdL''
  have hfin'' : Module.finrank ℤ (spanColSum B₀ cs) = r := by
    simpa using (Module.finrank_eq_card_basis (spanColSum_basis B₀ cs hB₀Z))
  have hvol'' : ReverseMinkowski.determinant (spanColSum B₀ cs) = volColSum (m := m) cs B₀ := by
    exact determinant_spanColSum_eq_vol B₀ cs hB₀Z
  have hdet'' : (1 : ℝ) + ε₀ ≤ ReverseMinkowski.determinant (spanColSum B₀ cs) := by
    have h1 : 1 ≤ Module.finrank ℤ (spanColSum B₀ cs) := by rwa [hfin'']
    have hmm : Module.finrank ℤ (spanColSum B₀ cs) < m := by rwa [hfin'']
    exact hε₀prop (spanColSum B₀ cs) hdL'' hL''le h1 hmm
  have hvolgram : volColSum (m := m) cs B₀ =
      Real.sqrt (((csMatℝ cs).transpose * B₀.transpose * B₀ * (csMatℝ cs)).det) := by
    dsimp [volColSum]
    rw [gram_colSum_csMat B₀ cs]
  have hBvol : (1 : ℝ) + ε₀ ≤
      Real.sqrt ((((csMatℤ cs).map (fun z : ℤ => (z : ℝ))).transpose * B₀.transpose * B₀ *
        ((csMatℤ cs).map (fun z : ℤ => (z : ℝ)))).det) := by
    have hvol2 : volColSum (m := m) cs B₀ =
        Real.sqrt ((((csMatℤ cs).map (fun z : ℤ => (z : ℝ))).transpose * B₀.transpose * B₀ *
          ((csMatℤ cs).map (fun z : ℤ => (z : ℝ)))).det) := by
      rw [csMatℝ_eq_map cs] at hvolgram
      exact hvolgram
    rw [hvol''] at hdet''
    rw [hvol2] at hdet''
    exact hdet''
  have hrelA := hC₀ δ (le_of_lt hδpos) hCδ12 A hboxle (csMatℤ cs)
  have hdet3' : ReverseMinkowski.determinant ℒ' =
      Real.sqrt ((((csMatℤ cs).map (fun z : ℤ => (z : ℝ))).transpose * A.transpose * A *
        ((csMatℤ cs).map (fun z : ℤ => (z : ℝ)))).det) := by
    rw [csMatℝ_eq_map cs] at hdet3
    exact hdet3
  have hle1 : (1 - C₀ * δ) ^ r *
      Real.sqrt ((((csMatℤ cs).map (fun z : ℤ => (z : ℝ))).transpose * B₀.transpose * B₀ *
        ((csMatℤ cs).map (fun z : ℤ => (z : ℝ)))).det) ≤ ReverseMinkowski.determinant ℒ' := by
    rw [hdet3']
    exact hrelA
  have hpow0 : 0 ≤ (1 - C₀ * δ) ^ r := by
    apply pow_nonneg
    linarith [hCδ12]
  have hmain : (1 - C₀ * δ) ^ r * (1 + ε₀) ≤ ReverseMinkowski.determinant ℒ' := by
    calc
      (1 - C₀ * δ) ^ r * (1 + ε₀)
          ≤ (1 - C₀ * δ) ^ r *
              Real.sqrt ((((csMatℤ cs).map (fun z : ℤ => (z : ℝ))).transpose * B₀.transpose *
                B₀ * ((csMatℤ cs).map (fun z : ℤ => (z : ℝ)))).det) := by
                exact mul_le_mul_of_nonneg_left hBvol hpow0
      _ ≤ ReverseMinkowski.determinant ℒ' := hle1
  -- SECTION 5: Bernoulli + multiplicative margin ⟹ ≥ 1
  have hber : 1 - (m : ℝ) * C₀ * δ ≤ (1 - C₀ * δ) ^ r := by
    have hb := Commons.Analysis.Real.one_sub_pow_ge_one_sub_mul (C₀ * δ) r (by positivity)
      (by linarith [hCδ12])
    have hrmR : (r : ℝ) ≤ (m : ℝ) := by exact_mod_cast (le_of_lt hrm)
    have hCδ0 : 0 ≤ C₀ * δ := by positivity
    nlinarith
  have hmarg' : (1 : ℝ) ≤ (1 - (m : ℝ) * C₀ * δ) * (1 + ε₀) := by
    have hc : (1 + ε₀) * (1 - (m : ℝ) * C₀ * δ) = (1 - (m : ℝ) * C₀ * δ) * (1 + ε₀) := by ring
    rwa [hc] at hmarg
  have hmul : (1 - (m : ℝ) * C₀ * δ) * (1 + ε₀) ≤ (1 - C₀ * δ) ^ r * (1 + ε₀) := by
    exact mul_le_mul_of_nonneg_right hber (by linarith : 0 ≤ 1 + ε₀)
  have h1le : (1 : ℝ) ≤ (1 - C₀ * δ) ^ r * (1 + ε₀) := le_trans hmarg' hmul
  exact le_trans h1le hmain

/-- **(O3, OPEN — assembly).** Stability is open at a det-one-free stable point: every
determinant-one matrix `A` entrywise sufficiently close to `B₀` generates a stable lattice. -/
theorem stable_near_stable_no_det_one (B₀ : Matrix (Fin m) (Fin m) ℝ)
    (hm : 2 ≤ m) (hdet₀ : B₀.det ≠ 0)
    (hSt : @Stable m (latticeOfMatrix B₀) (latticeOfMatrix_discrete B₀ hdet₀))
    (hno : @NoDetOneSublattice m (latticeOfMatrix B₀) (latticeOfMatrix_discrete B₀ hdet₀)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Matrix (Fin m) (Fin m) ℝ, A.det ≠ 0 → |A.det| = 1 →
      (∀ j i : Fin m, |A j i - B₀ j i| < δ) →
      ∀ hdA : DiscreteTopology (latticeOfMatrix A), @Stable m (latticeOfMatrix A) hdA := by
  classical
  rcases subdet_ge_one_close B₀ hm hdet₀ hSt hno with ⟨δ, hδpos, hsub⟩
  refine ⟨δ, hδpos, ?_⟩
  intro A hdetA habs hbox hdA
  haveI : DiscreteTopology (latticeOfMatrix A) := hdA
  constructor
  · have hd : ReverseMinkowski.determinant (latticeOfMatrix A) = |A.det| :=
      det_latticeOfMatrix_eq_abs_det A hdetA
    rw [hd, habs]
  · intro ℒ' hle hdL
    haveI : DiscreteTopology ℒ' := hdL
    by_cases h0 : Module.finrank ℤ ℒ' = 0
    · have hbot : ℒ' = ⊥ := Submission.Filtration.eq_bot_of_finrank_zero h0
      have hde : ReverseMinkowski.determinant ℒ' =
          ReverseMinkowski.determinant (⊥ : Submodule ℤ E) := by
        exact Submission.Uncrossing.det_eq_of_eq (L₁ := ℒ') (L₂ := ⊥) hbot
      rw [hde]
      rw [Submission.Filtration.det_bot]
    · by_cases hm' : Module.finrank ℤ ℒ' = m
      · have hfr : Module.finrank ℤ (latticeOfMatrix A) = m := finrank_latticeOfMatrix A hdetA
        have hleA : ReverseMinkowski.determinant (latticeOfMatrix A) ≤
            ReverseMinkowski.determinant ℒ' := by
          exact Submission.Filtration.det_le_of_submodule_same_rank (N := ℒ')
            (L := latticeOfMatrix A) hle (by rw [hm', hfr])
        have hdA1 : ReverseMinkowski.determinant (latticeOfMatrix A) = 1 := by
          have hd : ReverseMinkowski.determinant (latticeOfMatrix A) = |A.det| :=
            det_latticeOfMatrix_eq_abs_det A hdetA
          rw [hd, habs]
        rw [← hdA1]
        exact hleA
      · have hr1 : 1 ≤ Module.finrank ℤ ℒ' := by omega
        have hleRank : Module.finrank ℤ ℒ' ≤ m := by
          haveI : Module.Free ℤ (latticeOfMatrix A) :=
            instModuleFree_of_discrete_submodule (latticeOfMatrix A)
          haveI : Module.Finite ℤ (latticeOfMatrix A) :=
            instModuleFinite_of_discrete_submodule (latticeOfMatrix A)
          haveI : Module.Free ℤ ℒ' := instModuleFree_of_discrete_submodule ℒ'
          haveI : Module.Finite ℤ ℒ' := instModuleFinite_of_discrete_submodule ℒ'
          have hlt : Module.finrank ℤ ℒ' ≤ Module.finrank ℤ (latticeOfMatrix A) :=
            finrank_le_of_le (ℒ' := ℒ') (ℒ := latticeOfMatrix A) hle
          rwa [finrank_latticeOfMatrix A hdetA] at hlt
        have hrm : Module.finrank ℤ ℒ' < m := by omega
        exact hsub A hdetA hbox ℒ' hdL hle hr1 hrm


/-- **(Interior-branch input: hno ⟹ local minimum over the determinant-one lattices).**
A stable full-rank `latticeOfMatrix B₀` with no strict det-one primitive sublattice
(`hno`) has a whole determinant-one neighborhood of *stable* lattices
(`stable_near_stable_no_det_one`); global γ-minimality over the stable family (`hmin`)
then makes every det-one `A` entrywise close to `B₀` a γ-improvement, i.e. `B₀` is a
local minimum of `A ↦ γ_s(V(latticeOfMatrix A))` over the determinant-one matrices.
(No continuity is needed here — only the openness lemma and the global minimum.) -/
theorem local_min_gamma_of_no_det_one (s : ℝ) (hs : 0 < s)
    (B₀ : Matrix (Fin m) (Fin m) ℝ) (hm : 2 ≤ m) (hdet₀ : B₀.det ≠ 0)
    (habs : |B₀.det| = 1)
    (hSt : @Stable m (latticeOfMatrix B₀) (latticeOfMatrix_discrete B₀ hdet₀))
    (hno : @NoDetOneSublattice m (latticeOfMatrix B₀) (latticeOfMatrix_discrete B₀ hdet₀))
    (hmin : ∀ (ℒ₀ : Submodule ℤ E) (_hd : DiscreteTopology ℒ₀),
      @Stable m ℒ₀ _hd → Module.finrank ℤ ℒ₀ = m →
      Submission.GaussianMeasure.gammaMass s (Submission.Voronoi.voronoi (latticeOfMatrix B₀)) ≤
        Submission.GaussianMeasure.gammaMass s (Submission.Voronoi.voronoi ℒ₀)) :
    ∃ δ : ℝ, 0 < δ ∧
    ∀ (A : Matrix (Fin m) (Fin m) ℝ), A.det ≠ 0 → |A.det| = 1 →
      (∀ j i : Fin m, |A j i - B₀ j i| < δ) →
      Submission.GaussianMeasure.gammaMass s (Submission.Voronoi.voronoi (latticeOfMatrix B₀)) ≤
        Submission.GaussianMeasure.gammaMass s (Submission.Voronoi.voronoi (latticeOfMatrix A)) := by
  rcases stable_near_stable_no_det_one B₀ hm hdet₀ hSt hno with ⟨δ, hδpos, hopen⟩
  refine ⟨δ, hδpos, ?_⟩
  intro A hdetA habs hbox
  haveI : DiscreteTopology (latticeOfMatrix A) := latticeOfMatrix_discrete A hdetA
  have hStA : @Stable m (latticeOfMatrix A) (latticeOfMatrix_discrete A hdetA) :=
    hopen A hdetA habs hbox (latticeOfMatrix_discrete A hdetA)
  have hfinA : Module.finrank ℤ (latticeOfMatrix A) = m := finrank_latticeOfMatrix A hdetA
  exact hmin (latticeOfMatrix A) (latticeOfMatrix_discrete A hdetA) hStA hfinA

end Submission.StableOpen
