import Mathlib
import Submission.CellGamma
import Submission.MatrixTopology
import Submission.StableClosure
import Submission.StableCompact
import Submission.StablePrecompact

open Module Real Filter
open scoped Real BigOperators InnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# (B-ii / step iv) the stable-family γ-minimizer

Paper route (arxiv 2203.11866 §1): "the stable lattices form a compact subset of the
determinant-one lattices, so the continuous function ρ_s attains a global maximum over the
stable lattices".  On the γ-side this session's modules provide every ingredient of the
minimizer existence:

* representatives in a compact `K` (`StableCompact.stable_lattices_in_compact_set`),
* the stable closure (`StableClosure.stable_latticeOfMatrix_of_stable_sequence` and its
  in-`K` corollary `stable_latticeOfMatrix_of_seq_in_K` below),
* topological γ-continuity (`CellGamma.continuousAt_gammaMass_of_matrix`) — matrices are
  first countable (`MatrixTopology.instFirstCountableTopologyMatrix`), so compact sets are
  sequentially compact (`IsCompact.tendsto_subseq`).

The minimizer theorem (statement, proof assembled next):
```
∃ (ℳ : Submodule ℤ (EuclideanSpace ℝ (Fin m))) [DiscreteTopology ℳ],
  Stable ℳ ∧ finrank ℤ ℳ = m ∧
  ∀ (ℒ : Submodule ℤ (EuclideanSpace ℝ (Fin m))) [DiscreteTopology ℒ],
    Stable ℒ → finrank ℤ ℒ = m →
    gammaMass s (VC ℳ) ≤ gammaMass s (VC ℒ)
```
for `0 < s`, provided a stable full-rank rank-`m` lattice exists.  DESIGN NOTE: the compact
set must be built explicitly as `K := {A | |A.det| = 1 ∧ ∀ i, ‖cols A i‖ ≤ C}` (replicating
`stable_lattices_in_compact_set`'s construction via
`Commons.Lattice.Minkowski.bounded_basis_covolume_one`) so that elements of `K` have
`|det A| = 1 ≠ 0` — the closure theorem's discreteness hypotheses (`hdetn`, `hDT`) are then
automatic for every element of `K` (opaque `K` from `stable_lattices_in_compact_set` does not
expose `|det A| = 1`).  Minimizing sequence: `β := sInf {γ_s(V(latticeOfMatrix A)) | A ∈ K ∧
Stable (latticeOfMatrix A)}` (bounded below by 0 via `Boundary.gammaMass_nonneg` on the
measurable cells); choose `Aₙ ∈ K` stable with `γ(Aₙ) < β + 1/(n+1)` (`csInf_lt_iff`);
`IsCompact.tendsto_subseq hK (fun n => hAₙK n)` gives a convergent subsequence `A_{φ n} → A₀
∈ K`; the closure corollary gives stability of `latticeOfMatrix A₀`; sequential γ-continuity
(`tendsto_volColSum`-style / `CellGamma` subsequential continuity) gives
`γ(A₀) = lim γ(A_{φ n}) = β`; then for every stable `ℒ` take its representative `A ∈ K`
(`latticeOfMatrix A = ℒ`) and conclude `γ(ℳ) ≤ γ(A) = γ(ℒ)` for `ℳ := latticeOfMatrix A₀`.
-/

noncomputable section
namespace Submission.StableMinimizer

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "VC" => Submission.Voronoi.voronoi

open Submission.CellContinuity
open Submission.StableCompact
open Submission.LatticeParam
open Submission.StableClosure

/-- **(iv) closure in `K`**: a limit (in a det-`≠0` compact set `K`) of a sequence of stable
matrix-lattices is stable.  This is the topological half of "the stable family is compact"
(the other half, that every stable lattice has a representative in `K`, is
`StableCompact.stable_lattices_in_compact_set`). -/
lemma stable_latticeOfMatrix_of_seq_in_K (K : Set (Matrix (Fin m) (Fin m) ℝ))
    (hKd : ∀ A : Matrix (Fin m) (Fin m) ℝ, A ∈ K → A.det ≠ 0)
    (An : ℕ → Matrix (Fin m) (Fin m) ℝ) (hAnK : ∀ n : ℕ, An n ∈ K)
    (hStn : ∀ n : ℕ, @Submission.StableLattices.Stable m (latticeOfMatrix (An n))
      (latticeOfMatrix_discrete (An n) (hKd (An n) (hAnK n))))
    (A₀ : Matrix (Fin m) (Fin m) ℝ) (hA₀K : A₀ ∈ K)
    (hconv : Filter.Tendsto An Filter.atTop (𝓝 A₀)) :
    @Submission.StableLattices.Stable m (latticeOfMatrix A₀)
      (latticeOfMatrix_discrete A₀ (hKd A₀ hA₀K)) := by
  exact stable_latticeOfMatrix_of_stable_sequence A₀ An hconv
    (fun n => hKd (An n) (hAnK n)) (hKd A₀ hA₀K) hStn

/-- The explicit covolume-one compact representative set with the properties the minimizer
needs: every element has `|det A| = 1 ≠ 0` (so `latticeOfMatrix A` is discrete), and every
stable full-rank lattice is `latticeOfMatrix A` for some `A ∈ K`. -/
theorem exists_stable_detOne_compact_set :
    ∃ (C : ℝ) (K : Set (Matrix (Fin m) (Fin m) ℝ)),
      IsCompact K ∧
      (K = {A : Matrix (Fin m) (Fin m) ℝ | |A.det| = 1 ∧ ∀ i : Fin m, ‖cols A i‖ ≤ C}) ∧
      ∀ (ℒ : Submodule ℤ E) [DiscreteTopology ℒ],
        Submission.StableLattices.Stable ℒ → Module.finrank ℤ ℒ = m →
        ∃ A : Matrix (Fin m) (Fin m) ℝ, A ∈ K ∧ latticeOfMatrix A = ℒ := by
  classical
  rcases Commons.Lattice.Minkowski.bounded_basis_covolume_one m with ⟨C, hCprop⟩
  let K : Set (Matrix (Fin m) (Fin m) ℝ) := {A | |A.det| = 1 ∧ ∀ i : Fin m, ‖cols A i‖ ≤ C}
  refine ⟨C, K, ?_, rfl, ?_⟩
  · simpa [K, cols] using (Commons.LinearAlgebra.Matrix.isCompact_det_one_bounded_cols (m := m) (C := C))
  · have hbasis : ∀ (ℒ : Submodule ℤ E) [DiscreteTopology ℒ],
        Submission.StableLattices.Stable ℒ → Module.finrank ℤ ℒ = m →
        ∃ b : Module.Basis (Fin m) ℤ ℒ, ∀ i : Fin m, ‖((b i : ℒ) : E)‖ ≤ C := by
      intro ℒ _hDT hSt hfin
      have hℒ : IsZLattice ℝ ℒ := Submission.MainStable.isZLattice_of_finrank (n := m) ℒ hfin
      exact hCprop ℒ hℒ (Submission.StablePrecompact.stable_meets_delegation_hypotheses (m := m) ℒ hfin hSt).1
        (Submission.StablePrecompact.stable_meets_delegation_hypotheses (m := m) ℒ hfin hSt).2
    intro ℒ _hDT hSt hfin
    rcases Submission.StableCompact.stable_bounded_detOne_representative (C := C) hbasis ℒ hSt hfin with ⟨A, hdet, hcol, hL⟩
    refine ⟨A, ?_, hL⟩
    dsimp [K]
    exact ⟨hdet, hcol⟩

lemma det_ne_zero_of_mem_detOne (C : ℝ) {A : Matrix (Fin m) (Fin m) ℝ}
    (h : |A.det| = 1 ∧ ∀ i : Fin m, ‖cols A i‖ ≤ C) : A.det ≠ 0 := by
  intro hz
  rw [hz] at h
  norm_num at h

/-- The set of `γ_s(V(latticeOfMatrix A))`-values over stable matrices in `K`. -/
def gammaSet (K : Set (Matrix (Fin m) (Fin m) ℝ))
    (hKd : ∀ A : Matrix (Fin m) (Fin m) ℝ, A ∈ K → A.det ≠ 0) (s : ℝ) : Set ℝ :=
  {r | ∃ (A : Matrix (Fin m) (Fin m) ℝ) (hA : A ∈ K),
    @Submission.StableLattices.Stable m (latticeOfMatrix A) (latticeOfMatrix_discrete A (hKd A hA)) ∧
    Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A)) = r}

/-- The γ-value of a stable full-rank lattice lies in `gammaSet` (via its representative). -/
lemma mem_gammaSet_of_rep {K : Set (Matrix (Fin m) (Fin m) ℝ)}
    (hKd : ∀ A : Matrix (Fin m) (Fin m) ℝ, A ∈ K → A.det ≠ 0) (s : ℝ)
    {A₀ : Matrix (Fin m) (Fin m) ℝ} (hA₀K : A₀ ∈ K)
    (hSt₀ : @Submission.StableLattices.Stable m (latticeOfMatrix A₀)
      (latticeOfMatrix_discrete A₀ (hKd A₀ hA₀K))) :
    Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A₀)) ∈ gammaSet K hKd s := by
  refine ⟨A₀, hA₀K, hSt₀, rfl⟩

/-- `gammaSet` is nonempty as soon as some stable full-rank lattice exists (K is a
representative set). -/
lemma gammaSet_nonempty {K : Set (Matrix (Fin m) (Fin m) ℝ)}
    (hKd : ∀ A : Matrix (Fin m) (Fin m) ℝ, A ∈ K → A.det ≠ 0) (s : ℝ)
    (hne : ∃ (ℒ : Submodule ℤ E) (_hDT : DiscreteTopology ℒ),
      @Submission.StableLattices.Stable m ℒ _hDT ∧ Module.finrank ℤ ℒ = m)
    (hKrep : ∀ (ℒ : Submodule ℤ E) [DiscreteTopology ℒ],
      Submission.StableLattices.Stable ℒ → Module.finrank ℤ ℒ = m →
      ∃ A : Matrix (Fin m) (Fin m) ℝ, A ∈ K ∧ latticeOfMatrix A = ℒ) :
    (gammaSet K hKd s).Nonempty := by
  rcases hne with ⟨ℒ₀, hDT₀, hSt₀, hfin₀⟩
  haveI : DiscreteTopology ℒ₀ := hDT₀
  rcases hKrep ℒ₀ hSt₀ hfin₀ with ⟨A₀, hA₀K, hA₀L⟩
  have hStA : @Submission.StableLattices.Stable m (latticeOfMatrix A₀)
      (latticeOfMatrix_discrete A₀ (hKd A₀ hA₀K)) := by
    haveI : DiscreteTopology (latticeOfMatrix A₀) := latticeOfMatrix_discrete A₀ (hKd A₀ hA₀K)
    exact Submission.Filtration.stable_of_submodule_eq (W₁ := latticeOfMatrix A₀) (W₂ := ℒ₀) hA₀L hSt₀
  exact ⟨Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A₀)), mem_gammaSet_of_rep hKd s hA₀K hStA⟩

/-- `gammaSet` is bounded below by `0` (the Gaussian mass of any measurable set is ≥ 0). -/
lemma gammaSet_bddBelow {K : Set (Matrix (Fin m) (Fin m) ℝ)}
    (hKd : ∀ A : Matrix (Fin m) (Fin m) ℝ, A ∈ K → A.det ≠ 0) (s : ℝ) :
    BddBelow (gammaSet K hKd s) := by
  refine ⟨0, ?_⟩
  intro r hr
  rcases hr with ⟨A, hA, hSt, hrγ⟩
  rw [← hrγ]
  exact Submission.Boundary.gammaMass_nonneg s
    (Submission.Voronoi.voronoi_measurable (latticeOfMatrix A))


/-- The minimizing sequence: from the nonempty bounded-below value set, choose for each `n`
a stable matrix `Aₙ ∈ K` with `γ(Aₙ) < β + 1/(n+1)`. -/
lemma exists_gamma_minimizing_seq {K : Set (Matrix (Fin m) (Fin m) ℝ)}
    (hKd : ∀ A : Matrix (Fin m) (Fin m) ℝ, A ∈ K → A.det ≠ 0) (s : ℝ)
    (hSne : (gammaSet K hKd s).Nonempty) (hSbdd : BddBelow (gammaSet K hKd s)) :
    ∃ An : ℕ → Matrix (Fin m) (Fin m) ℝ,
      (∀ n : ℕ, An n ∈ K) ∧
      (∀ n : ℕ, ∃ hA : An n ∈ K,
        @Submission.StableLattices.Stable m (latticeOfMatrix (An n))
          (latticeOfMatrix_discrete (An n) (hKd (An n) hA))) ∧
      (∀ n : ℕ, Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix (An n))) <
        sInf (gammaSet K hKd s) + 1 / ((n : ℝ) + 1)) := by
  classical
  let β : ℝ := sInf (gammaSet K hKd s)
  have hrec (n : ℕ) : ∃ (A : Matrix (Fin m) (Fin m) ℝ) (hA : A ∈ K),
      @Submission.StableLattices.Stable m (latticeOfMatrix A) (latticeOfMatrix_discrete A (hKd A hA)) ∧
      Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A)) < β + 1 / ((n : ℝ) + 1) := by
    have hpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    have hβlt : β < β + (1 : ℝ) / ((n : ℝ) + 1) := by linarith
    have hβlts : β < sInf (gammaSet K hKd s) + (1 : ℝ) / ((n : ℝ) + 1) := by
      dsimp [β] at hβlt ⊢
      exact hβlt
    rcases (csInf_lt_iff (s := gammaSet K hKd s) hSbdd hSne).mp hβlts with ⟨b, hbS, hb⟩
    rcases hbS with ⟨A, hA, hSt, hγ⟩
    refine ⟨A, hA, hSt, ?_⟩
    rwa [← hγ] at hb
  let An : ℕ → Matrix (Fin m) (Fin m) ℝ := fun n => Classical.choose (hrec n)
  refine ⟨An, ?_, ?_, ?_⟩
  · intro n
    rcases (Classical.choose_spec (hrec n)) with ⟨hA, _hSt, _hb⟩
    exact hA
  · intro n
    rcases (Classical.choose_spec (hrec n)) with ⟨hA, hSt, _hb⟩
    exact ⟨hA, hSt⟩
  · intro n
    rcases (Classical.choose_spec (hrec n)) with ⟨_hA, _hSt, hb⟩
    dsimp [An]
    exact hb
/-- **(iv) convergent stable subsequence**: from the minimizing sequence (stable matrices in
the compact set `K`), extract a subsequence converging to `A₀ ∈ K`, which is again a stable
sequence in `K` (so the Session-97/98 closure corollary applies to it). -/
lemma exists_convergent_stable_subseq {K : Set (Matrix (Fin m) (Fin m) ℝ)} (hKc : IsCompact K)
    (hKd : ∀ A : Matrix (Fin m) (Fin m) ℝ, A ∈ K → A.det ≠ 0)
    (An : ℕ → Matrix (Fin m) (Fin m) ℝ) (hAnK : ∀ n : ℕ, An n ∈ K)
    (hAnSt : ∀ n : ℕ, ∃ hA : An n ∈ K,
      @Submission.StableLattices.Stable m (latticeOfMatrix (An n))
        (latticeOfMatrix_discrete (An n) (hKd (An n) hA))) :
    ∃ (A₀ : Matrix (Fin m) (Fin m) ℝ) (hA₀K : A₀ ∈ K) (φ : ℕ → ℕ),
      StrictMono φ ∧ Filter.Tendsto (fun n : ℕ => An (φ n)) Filter.atTop (𝓝 A₀) ∧
      (∀ n : ℕ, ∃ hA : An (φ n) ∈ K,
        @Submission.StableLattices.Stable m (latticeOfMatrix (An (φ n)))
          (latticeOfMatrix_discrete (An (φ n)) (hKd (An (φ n)) hA))) := by
  classical
  rcases IsCompact.tendsto_subseq hKc hAnK with ⟨A₀, hA₀K, φ, hφmono, hconvφ⟩
  refine ⟨A₀, hA₀K, φ, hφmono, ?_, ?_⟩
  · -- hconvφ : Tendsto (An ∘ φ) atTop (𝓝 A₀): rewrite to fun n => An (φ n)
    simpa [Function.comp_def] using hconvφ
  · intro n
    exact hAnSt (φ n)
theorem exists_stable_gamma_minimizer (s : ℝ) (hs : 0 < s)
    (hne : ∃ (ℒ : Submodule ℤ E) (_hDT : DiscreteTopology ℒ),
      @Submission.StableLattices.Stable m ℒ _hDT ∧ Module.finrank ℤ ℒ = m) :
    ∃ (ℳ : Submodule ℤ E) (_hDT : DiscreteTopology ℳ),
      @Submission.StableLattices.Stable m ℳ _hDT ∧ Module.finrank ℤ ℳ = m ∧
      ∀ (ℒ : Submodule ℤ E) (_hDT2 : DiscreteTopology ℒ),
        @Submission.StableLattices.Stable m ℒ _hDT2 → Module.finrank ℤ ℒ = m →
        Submission.GaussianMeasure.gammaMass s (VC ℳ) ≤
          Submission.GaussianMeasure.gammaMass s (VC ℒ) := by
  classical
  rcases exists_stable_detOne_compact_set (m := m) with ⟨C, K, hKc, hKdef, hKrep⟩
  have hKd : ∀ A : Matrix (Fin m) (Fin m) ℝ, A ∈ K → A.det ≠ 0 := by
    intro A hA
    have hA' : |A.det| = 1 ∧ ∀ i : Fin m, ‖cols A i‖ ≤ C := by
      rwa [hKdef] at hA
    exact det_ne_zero_of_mem_detOne C hA'
  let S : Set ℝ := gammaSet K hKd s
  have hSne : S.Nonempty := by
    dsimp [S]
    exact gammaSet_nonempty (m := m) hKd s hne hKrep
  have hSbdd : BddBelow S := by
    dsimp [S]
    exact gammaSet_bddBelow (m := m) hKd s
  rcases exists_gamma_minimizing_seq (m := m) hKd s hSne hSbdd with ⟨An, hAnK, hAnSt, hbound⟩
  rcases exists_convergent_stable_subseq (m := m) hKc hKd An hAnK hAnSt with
    ⟨A₀, hA₀K, φ, hφmono, hconvφ, hsubSt⟩
  -- stability of the limit
  have hStA₀ : @Submission.StableLattices.Stable m (latticeOfMatrix A₀)
      (latticeOfMatrix_discrete A₀ (hKd A₀ hA₀K)) := by
    have hDT₀ : DiscreteTopology (latticeOfMatrix A₀) := latticeOfMatrix_discrete A₀ (hKd A₀ hA₀K)
    exact stable_latticeOfMatrix_of_seq_in_K (m := m) K hKd (fun n => An (φ n))
      (fun n => hAnK (φ n))
      (fun n => by
        rcases hsubSt n with ⟨hA, hSt⟩
        exact hSt)
      A₀ hA₀K hconvφ
  have hfinA₀ : Module.finrank ℤ (latticeOfMatrix A₀) = m := by
    haveI : DiscreteTopology (latticeOfMatrix A₀) := latticeOfMatrix_discrete A₀ (hKd A₀ hA₀K)
    exact finrank_latticeOfMatrix (m := m) A₀ (hKd A₀ hA₀K)
  -- γ-continuity along the subsequence
  let u : ℕ → ℝ := fun n => Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix (An (φ n))))
  have hγlim : Filter.Tendsto u Filter.atTop (𝓝 (Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A₀)))) := by
    dsimp [u]
    exact Submission.CellGamma.gammaMass_tendsto_of_matrix_tendsto (m := m) s hs A₀ (hKd A₀ hA₀K) (fun n => An (φ n)) hconvφ
  let β : ℝ := sInf S
  -- β ≤ γ(A₀)
  have hβle : β ≤ Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A₀)) := by
    dsimp [β]
    refine csInf_le hSbdd ?_
    exact mem_gammaSet_of_rep hKd s hA₀K hStA₀
  -- γ(A₀) ≤ β by contradiction
  have hγleβ : Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A₀)) ≤ β := by
    by_contra hnot
    have hgt : β < Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A₀)) := lt_of_not_ge hnot
    let δ : ℝ := (Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A₀)) - β) / 2
    have hδpos : 0 < δ := by dsimp [δ]; linarith
    -- uₙ → γ(A₀) so eventually uₙ > β + δ
    have hgt1 : ∀ᶠ n in Filter.atTop, β + δ < u n := by
      have hd : ∀ᶠ n in Filter.atTop, |u n - Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A₀))| < δ :=
        (Metric.tendsto_nhds.mp hγlim) δ hδpos
      refine hd.mono ?_
      intro n hn
      dsimp [δ] at hn
      have hz : u n - Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A₀)) > -δ := (abs_lt.mp hn).1
      have hu0 : Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A₀)) - δ < u n := by linarith
      have hcalc : Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A₀)) - δ = β + δ := by dsimp [δ]; ring
      rwa [← hcalc]
    -- bound: uₙ < β + 1/(φn + 1) ; eventually 1/(φn+1)... use φ n ≥ n and archimedean
    have hφge (n : ℕ) : n ≤ φ n := hφmono.id_le n
    have hlt2 : ∀ᶠ n in Filter.atTop, u n < β + δ := by
      -- pick N with 1/(N+1) < δ
      rcases (exists_nat_gt (1 / δ)) with ⟨N, hN⟩
      refine (Filter.eventually_atTop.mpr ⟨N, ?_⟩)
      intro n hn
      have hb := hbound (φ n)
      have hbd : Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix (An (φ n)))) < β + 1 / ((φ n : ℝ) + 1) := by
        simpa [β, S] using hb
      -- 1/(φn+1) ≤ 1/(n+1) ≤ ... < δ? need n ≥ N: φ n ≥ n ≥ N
      have hfrac : 1 / ((φ n : ℝ) + 1) < δ := by
        -- 1/(φn+1) < δ ⟸ 1/δ < φn+1 (all positive)
        have hφn : (1 / δ : ℝ) < (φ n : ℝ) + 1 := by
          have hNle : (N : ℝ) ≤ (φ n : ℝ) + 1 := by
            have hn1 : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            have hφ : (n : ℝ) ≤ (φ n : ℝ) := by exact_mod_cast hφge n
            nlinarith
          exact lt_of_lt_of_le hN hNle
        have hpos1 : 0 < (φ n : ℝ) + 1 := by positivity
        -- 1 < δ·(φn+1) from 1/δ < φn+1
        have h1lt : (1 : ℝ) < δ * ((φ n : ℝ) + 1) := by
          have harg := (div_lt_iff₀ hδpos).mp hφn
          nlinarith
        exact (div_lt_iff₀ hpos1).2 h1lt
      have hu : u n < β + 1 / ((φ n : ℝ) + 1) := by
        dsimp [u]
        exact hbd
      linarith
    -- both eventually hold: get an n with both
    rcases (Filter.Eventually.and hgt1 hlt2).exists with ⟨n, hn1, hn2⟩
    linarith
  have hβeq : Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix A₀)) = β := le_antisymm hγleβ hβle
  -- assemble
  refine ⟨latticeOfMatrix A₀, latticeOfMatrix_discrete A₀ (hKd A₀ hA₀K), hStA₀, hfinA₀, ?_⟩
  intro ℒ _hDT2 hStℒ hfinℒ
  haveI : DiscreteTopology ℒ := _hDT2
  -- γ(A₀) = β ≤ γ(ℒ)
  rcases hKrep ℒ hStℒ hfinℒ with ⟨Aℒ, hAℒK, hAℒL⟩
  have hStAℒ : @Submission.StableLattices.Stable m (latticeOfMatrix Aℒ)
      (latticeOfMatrix_discrete Aℒ (hKd Aℒ hAℒK)) := by
    haveI : DiscreteTopology (latticeOfMatrix Aℒ) := latticeOfMatrix_discrete Aℒ (hKd Aℒ hAℒK)
    exact Submission.Filtration.stable_of_submodule_eq (W₁ := latticeOfMatrix Aℒ) (W₂ := ℒ) hAℒL hStℒ
  have hmem : Submission.GaussianMeasure.gammaMass s (VC ℒ) ∈ S := by
    dsimp [S]
    -- gammaMass s (VC ℒ) = gammaMass s (VC(latticeOfMatrix Aℒ)) via voronoi_congr hAℒL
    have hcell : VC (latticeOfMatrix Aℒ) = VC ℒ := Submission.Intrinsic.voronoi_congr (latticeOfMatrix Aℒ) ℒ hAℒL
    -- membership: mem_gammaSet_of_rep gives gammaMass s (VC(latticeOfMatrix Aℒ)) ∈ gammaSet: value equal to gammaMass s (VC ℒ): rewrite
    have hmem0 : Submission.GaussianMeasure.gammaMass s (VC (latticeOfMatrix Aℒ)) ∈ gammaSet K hKd s :=
      mem_gammaSet_of_rep hKd s hAℒK hStAℒ
    -- rewrite value: gammaMass s (VC (latticeOfMatrix Aℒ)) = gammaMass s (VC ℒ) via hcell: congrArg
    rwa [congrArg (fun T : Set E => Submission.GaussianMeasure.gammaMass s T) hcell] at hmem0
  have hβℒ : β ≤ Submission.GaussianMeasure.gammaMass s (VC ℒ) := by
    dsimp [β]
    exact csInf_le hSbdd hmem
  -- γ(A₀) ≤ β ≤ γ(ℒ): but the goal is gammaMass s (VC (latticeOfMatrix A₀)) ≤ gammaMass s (VC ℒ)
  rw [hβeq]
  exact hβℒ
end Submission.StableMinimizer
