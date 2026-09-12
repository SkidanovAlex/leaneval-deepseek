import Mathlib
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Submission.LatticeDefs
import Submission.CovDual
import Submission.CovShort
import Submission.CovExt

noncomputable section

open scoped BigOperators RealInnerProductSpace NNReal ENNReal
open Module Submodule MeasureTheory MeasureTheory.Measure Metric Filter
open Submission.LatticeDefs
open Submission.CovShort
open Submission.CovExt
open Submission.CovDual

universe u

namespace Submission.CovRec

section FinBasis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A primitive lattice vector can be extended to a ℤ-basis of the lattice indexed by
`Option (Fin n)`. -/
lemma exists_basisFin_of_pure (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (v : E) (hvL : v ∈ L) (hv0 : v ≠ 0)
    (hpure : ∀ (y : E), y ∈ L → y ∈ span ℝ ({v} : Set E) → y ∈ span ℤ ({v} : Set E)) :
    ∃ (n : ℕ) (b : Basis (Option (Fin n)) ℤ L), (b none : E) = v  := by
  classical
  let w : L := ⟨v, hvL⟩
  have hw0 : w ≠ 0 := by
    intro hw
    exact hv0 (by simpa [w] using congrArg (fun z : L => (z : E)) hw)
  let K : Submodule ℤ L := span ℤ ({w} : Set L)
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
  refine ⟨n, bfin, ?_⟩
  have hb : bfin none = w := by
    simpa [bfin, e] using (Basis.mk_apply hli hsp (i := none))
  have hb0 : (bfin none : E) = v := by
    rw [hb]
  exact hb0

end FinBasis

section Recursion

/-- Covering radius bound for any full-rank lattice with dual first minimum ≥ 1 in
dimension `d`: every point is within `d^5+1` of a lattice point. -/
def coverProp (d : ℕ) : Prop :=
  ∀ ⦃E : Type u⦄ [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E],
    ∀ (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L],
      finrank ℝ E = d →
      (∀ ⦃y : E⦄, y ∈ ldual E L → y ≠ 0 → 1 ≤ ‖y‖) →
      ∀ x : E, ∃ m : E, m ∈ L ∧ ‖x - m‖ ≤ (d : ℝ) ^ 5 + 1

/-- Dimension-0 lattices are trivial. -/
lemma coverProp_zero : coverProp 0 := by
  dsimp [coverProp]
  intro E hna hip hfd hms hbr L hdt hzl hfin hmin x
  have hx : x = 0 := (finrank_zero_iff_forall_zero (K := ℝ)).mp hfin x
  refine ⟨0, ?_, ?_⟩
  · exact zero_mem L
  · subst x; simp

/-- For a real `c` there is an integer within distance 1/2. -/
lemma exists_int_close (c : ℝ) : ∃ n : ℤ, |c - (n : ℝ)| ≤ 1 / 2 := by
  let f : ℤ := Int.floor c
  have hf : c = (f : ℝ) + Int.fract c := (Int.floor_add_fract c).symm
  have hfr0 : 0 ≤ Int.fract c := Int.fract_nonneg c
  have hfr1 : Int.fract c < 1 := Int.fract_lt_one c
  by_cases hle : Int.fract c ≤ 1 / 2
  · refine ⟨f, ?_⟩
    have hsub : c - (f : ℝ) = Int.fract c := by linarith
    rw [hsub]
    rw [abs_of_nonneg hfr0]
    exact hle
  · refine ⟨f + 1, ?_⟩
    have hlt : 1 / 2 < Int.fract c := lt_of_not_ge hle
    have hcast1 : ((f + 1 : ℤ) : ℝ) = (f : ℝ) + 1 := by norm_num
    have hsub : c - ((f + 1 : ℤ) : ℝ) = Int.fract c - 1 := by linarith [hcast1]
    rw [hsub]
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- Dimension 1. -/
lemma coverProp_one : coverProp 1 := by
  dsimp [coverProp]
  intro E hna hip hfd hms hbr L hdt hzl hfin hmin x
  have hd1 : 1 ≤ finrank ℝ E := by rw [hfin]
  obtain ⟨vE, hvL, hv0, hvmin, hvb⟩ := shortVector_of_hmin L hmin hd1
  have hspanE : span ℝ ({vE} : Set E) = ⊤ := by
    have hdimv : finrank ℝ (span ℝ ({vE} : Set E)) = 1 := finrank_span_singleton hv0
    exact Submodule.eq_top_of_finrank_eq (hdimv.trans (by simpa using hfin.symm))
  have hxmem : x ∈ span ℝ ({vE} : Set E) := by
    rw [hspanE]
    trivial
  rcases (mem_span_singleton.mp hxmem) with ⟨c, hc⟩
  rcases exists_int_close c with ⟨n, hn⟩
  let m : E := (n : ℤ) • vE
  have hmL : m ∈ L := Submodule.smul_mem L n hvL
  refine ⟨m, hmL, ?_⟩
  have hcE : (n : ℤ) • vE = (n : ℝ) • vE := (Int.cast_smul_eq_zsmul (R := ℝ) n vE).symm
  have hnorm : ‖x - m‖ ≤ 1 / 2 * ‖vE‖ := by
    dsimp [m]
    rw [← hc, hcE]
    rw [← sub_smul]
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hn (norm_nonneg vE)
  have hb : 1 / 2 * ‖vE‖ ≤ 2 := by
    have hv' : ‖vE‖ ≤ 4 := by
      have h : (finrank ℝ E : ℝ) = (1 : ℝ) := by exact_mod_cast hfin
      nlinarith [hvb, h]
    nlinarith
  have hb2 : ‖x - m‖ ≤ 2 := le_trans hnorm hb
  norm_num at hb2 ⊢
  exact hb2

end Recursion

section RecursionStep

/-!
# The recursion step for the covering-radius bound

Task for the sub-agent: prove `Submission.CovRec.coverProp_step` below, REPLACING the placeholder
by a real proof. Do NOT change the statement or name.

## Context
`coverProp d` (defined above) says: in every `d`-dimensional finite-dimensional real inner
product space `E` (with `[MeasurableSpace E] [BorelSpace E]`), every full-rank `ℤ`-lattice
`L : Submodule ℤ E` (with `[DiscreteTopology L] [IsZLattice ℝ L]`) whose *dual lattice*
`ldual E L` has Euclidean first minimum ≥ 1 satisfies: every point `x` lies within
`(d:ℝ)^5 + 1` of a lattice point.  `coverProp_zero` and `coverProp_one` are proved.

## Task
Prove the induction step for `d ≥ 2`:

    coverProp_step (d : ℕ) (hd : 2 ≤ d) (ih : coverProp (d - 1)) : coverProp d

## Available lemmas (import Submission.CovShort etc.)
- `Submission.CovShort.shortVector_of_hmin (L) hmin hd1 : ∃ v ∈ L, v ≠ 0,
  (∀ u ∈ L, u ≠ 0 → ‖v‖ ≤ ‖u‖) ∧ ‖v‖ ≤ 4 * (finrank ℝ E : ℝ)` — a SHORTEST nonzero vector,
  bounded by `4·dim`, under the dual-first-min hypothesis `hmin`.
- `Submission.CovShort.shortest_pure hvL hvmin hv0 : ∀ y ∈ L, y ∈ span ℝ {v} → y ∈ span ℤ {v}`
  (primitivity of a shortest vector).
- `Submission.CovExt.exists_basis_of_pure L v hvL hv0 hpure :
  ∃ (τ : Type*) (bfull : Basis (Option τ) ℤ L), (bfull none : E) = v`
  (extends the primitive vector `v` to a ℤ-basis of `L` whose "0-th" element is `v`).
- `coverProp_zero`, `coverProp_one` in this file.

## Proof route (suggested; you may deviate, but the statement must be proved)
Unfold `coverProp d`; take the ambient `E`, lattice `L`, `hfin : finrank ℝ E = d`,
`hmin`, and a point `x : E`.

1. **Shortest vector.**  `d ≥ 2 ⟹ 1 ≤ finrank ℝ E` (use `hfin`).  Obtain
   `⟨v, hvL, hv0, hvmin, hvb⟩` from `shortVector_of_hmin L hmin hd1`.
   Record the bound `‖v‖ ≤ 4 * (d:ℝ)`.
2. **Basis of L containing v.**  `shortest_pure hvL hvmin hv0` gives the purity condition
   `hpure`; from `exists_basis_of_pure` get `⟨τ, bfull, hbfirst⟩` with
   `bfull : Basis (Option τ) ℤ L` and `(bfull none : E) = v`.
   Let `bzr := bfull.ofZLatticeBasis ℝ : Basis (Option τ) ℝ E` (real extension).
3. **Orthogonal complement space.**  Let `W₀ : Submodule ℝ E := (span ℝ ({v} : Set E))ᗮ`.
   As a *type*, `W₀` carries all needed instances automatically
   (`NormedAddCommGroup`, `InnerProductSpace ℝ`, `FiniteDimensional ℝ`,
   `MeasurableSpace`, `BorelSpace`, `MeasureSpace`, `ProperSpace`), verify by `infer_instance`.
   Let `π : E →ₗ[ℝ] E := W₀.starProjection` (orthogonal projection onto `W₀`; needs
   `W₀.HasOrthogonalProjection` — automatic).  Facts available in Mathlib
   (Analysis/InnerProductSpace/Projection/Basic.lean and Submodule.lean):
   - `Submodule.range_starProjection : W₀.starProjection.range = W₀`
   - `Submodule.ker_starProjection : W₀.starProjection.ker = W₀ᗮ`
   - `Submodule.starProjection_eq_self_iff`, `Submodule.starProjection_apply_mem`,
     `Submodule.sub_starProjection_mem_orthogonal`,
     `Submodule.orthogonal_orthogonal` (with `HasOrthogonalProjection`),
     `norm_starProjection_apply_le`.
   Since `v ≠ 0`, `W₀ᗮ = span ℝ {v}` (double orthogonal complement
   `(span ℝ {v})ᗮᗮ = span ℝ {v}`, use `Submodule.orthogonal_orthogonal` with
   `K := span ℝ {v}`).
4. **Dimension of W₀.**  `finrank ℝ (span ℝ {v}) = 1` (`finrank_span_singleton hv0`);
   `Submodule.finrank_add_finrank_orthogonal K : finrank ℝ K + finrank ℝ Kᗮ = finrank ℝ E`;
   deduce `finrank ℝ W₀ = d - 1`.  (`finrank ℝ W₀` with `W₀` as a *type* is the finrank of
   the submodule-as-type, matching `Submodule.finrank_add_finrank_orthogonal`'s first term.)
5. **The projected lattice.**  `π(bzr j) ∈ W₀` for every `j` (by range equality).  For each
   `j : {j : Option τ // j ≠ none}` let `u j : W₀ := ⟨π (bzr j.1), proof that π (bzr j.1) ∈ W₀⟩`.
   Show `u` is an ℝ-basis of `W₀` (`Basis.mk (hli) (hsp)`, LinearAlgebra/Basis/Basic.lean):
   - linear independence: a real combination `Σ_j c_j • u j = 0` means
     `π (Σ_j c_j • bzr j.1) = 0`, i.e. `Σ_j c_j • bzr j.1 ∈ ker π = span ℝ {v} = ℝ•(bzr none)`;
     extend the coefficients by `c_none` to a combination of the *whole* basis `bzr` equal to 0,
     contradicting `bzr.linearIndependent` unless all `c_j = 0`.
   - spanning: for `w : W₀`, `w = π w` and `w = Σ_j c_j • bzr j` (real, all `j`, since `bzr` is a
     real basis); `π (bzr none) = π v = 0`, so `w = Σ_{j≠none} c_j • u j`.
   Then define `Λ' : Submodule ℤ W₀ := span ℤ (Set.range u)` (u as the Basis value `ub`);
   the instances `[DiscreteTopology Λ']` and `[IsZLattice ℝ Λ']` are automatic from `ub`
   (ZSpan instances: `DiscreteTopology (span ℤ (Set.range ub))` needs `[Finite ι]` — get
   `[Finite (Option τ)]` from `Module.Finite.finite_basis bfull` (L is finite), then
   `[Finite {j // j ≠ none}]`; `IsZLattice` from `instIsZLatticeRealSpan ub`).
6. **The dual condition for the projected lattice.**  Prove
   `hmin' : ∀ ⦃w : W₀⦄, w ∈ ldual W₀ Λ' → w ≠ 0 → 1 ≤ ‖w‖`:
   take `w : W₀` with `w ∈ ldual W₀ Λ'`, i.e. `∀ a ∈ Λ', ∃ z : ℤ, ⟪w, a⟫_W₀ = (z:ℝ)`.
   For `m : L` write `m = Σ_j n_j • bzr j` (`n_j : ℤ`, integer coefficients, since `bfull` is a
   ℤ-basis).  Show `(w : E) ∈ ldual E L` by checking `⟪(w:E), m⟫_E ∈ ℤ`: split the sum into the
   `j ≠ none` part and the `none` part; the former is a ℤ-linear combination of the values
   `⟪w, u j⟫_W₀` (use that for `w ∈ W₀`, `⟪(w:E), π y⟫_E = ⟪(w:E), y⟫_E` because
   `y - π y ∈ span ℝ {v} = W₀ᗮ` is orthogonal to `w`; equivalently use the self-adjointness of
   the orthogonal projection or `Submodule.inner_starProjection`-type lemmas); the `none` term is
   `n_none • ⟪(w:E), v⟫_E = 0` since `w ∈ W₀ = (span ℝ {v})ᗮ` means `⟪(w:E), v⟫ = 0`.
   Conclude with `hmin` that `1 ≤ ‖(w:E)‖ = ‖w‖` (the norm on the subtype `W₀` equals the
   ambient norm, and the inner product on `W₀` is the restriction of `⟪·,·⟫_E`).
7. **Apply the induction hypothesis.**  Invoke `ih` at the ambient `W₀` (a type; all instances
   infer) with lattice `Λ'`, `hfinW : finrank ℝ W₀ = d - 1`, and `hmin'`, obtaining for the point
   `xW : W₀ := ⟨π x, proof π x ∈ W₀⟩` a lattice point `m₁ ∈ Λ'` with
   `‖xW - m₁‖ ≤ (d-1 : ℝ)^5 + 1` (norm in `W₀`).
8. **Lift to L and round the v-component.**  Since `Λ' = span ℤ (range u) ⊆ π(L)` (each `u j` is
   `π (bzr j.1)` with `bzr j.1 ∈ L`), the point `m₁` has the form `π m₀` for some `m₀ ∈ L`
   (`m₁ = ⟨π m₀, _⟩ : W₀`).  Both `x - π x` and `m₀ - π m₀` lie in `span ℝ {v}` (they are in
   `ker π = W₀ᗮ = span ℝ {v}`).  Choose the integer `k` with
   `‖(x - π x) - (m₀ - π m₀) - k • v‖ ≤ ‖v‖ / 2`
   (write `(x - π x) - (m₀ - π m₀) = c • v` with `c : ℝ` — use `Submodule.mem_span_singleton`-type
   facts on `span ℝ {v}` — and pick `k` via an integer within `1/2` of `c`; the ℤ-smul
   `k • v` satisfies `k • v = (k:ℝ) • v` by `Int.cast_smul_eq_zsmul (R := ℝ) k v`).  Then with
   `m := m₀ + k • v ∈ L`:
   `x - m = (xW - m₁) + ((x - πx) - (m₀ - πm₀) - k • v)` (all as elements of `E`, where `xW`
   and `m₁` are coerced from `W₀` to `E`), hence by the triangle inequality and steps 7, 8:
   `‖x - m‖ ≤ (d-1:ℝ)^5 + 1 + ‖v‖/2`.
9. **Final arithmetic.**  With `‖v‖ ≤ 4*d` (step 1) show for `d ≥ 2`:
   `(d-1 : ℝ)^5 + 1 + (4*(d:ℝ))/2 ≤ (d:ℝ)^5 + 1` (i.e. `2*d ≤ d^5 - (d-1)^5`; true for `d ≥ 2`
   since `d^5 - (d-1)^5 ≥ d^4 ≥ 2*d`; prove with real arithmetic, `nlinarith`-friendly facts like
   `(d-1)^4 ≤ d^4`, powers nonneg, or by `nlinarith` on expanded polynomials plus small case splits).
   Conclude `‖x - m‖ ≤ (d:ℝ)^5 + 1`; with `m ∈ L`, done.

## Final bookkeeping
No unfinished placeholders; axioms ⊆ {propext, Quot.sound, Classical.choice}.  You may add any
helper lemmas in this file.  The ambient-typeclass-binders of `coverProp` are ordinary Π-binders:
after `dsimp [coverProp]`, use `intro E hna hip hfd hms hbr L hdt hzl hfin hmin x` (in that exact
order: E; NormedAddCommGroup; InnerProductSpace; FiniteDimensional; MeasurableSpace; BorelSpace;
L; DiscreteTopology; IsZLattice; hfin; hmin; x).
-/
set_option maxHeartbeats 0 in
lemma coverProp_step (d : ℕ) (hd : 2 ≤ d) (ih : coverProp.{u} (d - 1)) : coverProp.{u} d := by
  dsimp [coverProp]
  intro E hna hip hfd hms hbr L hdt hzl hfin hmin x
  have hd1 : 1 ≤ finrank ℝ E := by
    rw [hfin]
    omega
  obtain ⟨v, hvL, hv0, hvmin, hvb⟩ := shortVector_of_hmin (L := L) hmin hd1
  have hpure : ∀ (y : E), y ∈ L → y ∈ span ℝ ({v} : Set E) → y ∈ span ℤ ({v} : Set E) :=
    shortest_pure hvL hvmin hv0
  obtain ⟨n, bfull, hbfirst⟩ := exists_basisFin_of_pure (L := L) v hvL hv0 hpure
  let bzr : Basis (Option (Fin n)) ℝ E := bfull.ofZLatticeBasis ℝ
  have hbzr_none : bzr none = v := by
    rw [Module.Basis.ofZLatticeBasis_apply]
    exact hbfirst
  have hbzr_some (t : Fin n) : bzr (some t) = (bfull (some t) : E) := by
    rw [Module.Basis.ofZLatticeBasis_apply]
  let K₁ : Submodule ℝ E := span ℝ ({v} : Set E)
  let W : Submodule ℝ E := K₁ᗮ
  have hWperp : Wᗮ = K₁ := by
    dsimp [W]
    exact (Submodule.orthogonal_orthogonal (K := K₁))
  let π : E →ₗ[ℝ] W := W.orthogonalProjectionOnto
  let star : E →ₗ[ℝ] E := W.starProjection
  have hπstar (y : E) : (π y : E) = star y := by
    rfl
  have hπv : π v = 0 := by
    dsimp [π]
    have hvker : v ∈ π.ker := by
      rw [Submodule.ker_orthogonalProjectionOnto]
      rw [hWperp]
      dsimp [K₁]
      exact Submodule.mem_span_singleton_self v
    exact (LinearMap.mem_ker (f := π) (y := v)).mp hvker
  have hstar_v_zero : star v = 0 := by
    have hvker : v ∈ star.ker := by
      rw [Submodule.ker_starProjection]
      rw [hWperp]
      dsimp [K₁]
      exact Submodule.mem_span_singleton_self v
    exact (LinearMap.mem_ker (f := star) (y := v)).mp hvker
  have h_inner_pi (w : W) (y : E) : ⟪(w : E), (π y : E)⟫ = ⟪(w : E), y⟫ := by
    rw [hπstar]
    have hz : y - star y ∈ Wᗮ := by
      dsimp [star]
      exact Submodule.sub_starProjection_mem_orthogonal y
    have hz' : ⟪(w : E), y - star y⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (K := W) (u := (w : E)) w.2 hz
    have hmain : ⟪(w : E), y⟫ - ⟪(w : E), star y⟫ = 0 := by
      simpa [inner_sub_right] using hz'
    exact (sub_eq_zero.mp hmain).symm
  have h_inner_v (w : W) : ⟪(w : E), v⟫ = 0 := by
    have hvW : v ∈ Wᗮ := by
      rw [hWperp]
      dsimp [K₁]
      exact Submodule.mem_span_singleton_self v
    exact Submodule.inner_right_of_mem_orthogonal (K := W) (u := (w : E)) w.2 hvW
  let u : Fin n → W := fun t => π (bzr (some t))
  -- linear independence of u
  have hli_u : LinearIndependent ℝ u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hgE : (∑ t : Fin n, g t • (u t : E)) = (0 : E) := by
      have h := congrArg (fun w : W => (w : E)) hg
      simpa [u] using h
    let y : E := ∑ t : Fin n, g t • bzr (some t)
    have hsy : star y = 0 := by
      dsimp [y]
      rw [_root_.map_sum (g := star)]
      simp [u, ← hπstar, ← hgE]
    have hyker : y ∈ star.ker := by
      exact (LinearMap.mem_ker (f := star) (y := y)).mpr hsy
    have hyW : y ∈ Wᗮ := by
      rw [← Submodule.ker_starProjection]
      exact hyker
    have hyK : y ∈ K₁ := by
      rw [hWperp] at hyW
      exact hyW
    rcases (Submodule.mem_span_singleton.mp hyK) with ⟨c, hc⟩
    -- hc : c • v = y
    let f : Option (Fin n) → ℝ := fun j => Option.elim j (-c) g
    have hzero : (∑ j : Option (Fin n), f j • bzr j) = 0 := by
      rw [Fintype.sum_option]
      dsimp [f]
      rw [hbzr_none]
      dsimp [y] at hc
      rw [← hc]
      simp
    have hfzero := (Fintype.linearIndependent_iff.mp bzr.linearIndependent) f hzero
    intro t
    exact hfzero (some t)


  -- spanning of u
  have hsp_u : (⊤ : Submodule ℝ W) ≤ span ℝ (Set.range u) := by
    intro w hw
    let a : Option (Fin n) → ℝ := bzr.repr (w : E)
    have hwE_sum : (w : E) = ∑ j : Option (Fin n), a j • bzr j := by
      simpa [a] using (bzr.sum_repr (w : E)).symm
    have hstar_w : star (w : E) = (w : E) := by
      exact (Submodule.starProjection_eq_self_iff (K := W) (v := (w : E))).mpr w.2
    have h1 : (w : E) = ∑ t : Fin n, a (some t) • (u t : E) := by
      calc
        (w : E) = star (w : E) := hstar_w.symm
        _ = star (∑ j : Option (Fin n), a j • bzr j) := by rw [hwE_sum]
        _ = ∑ j : Option (Fin n), a j • star (bzr j) := by
              rw [_root_.map_sum (g := star)]
              simp
        _ = a none • star (bzr none) + ∑ t : Fin n, a (some t) • star (bzr (some t)) := by
              rw [Fintype.sum_option]
        _ = ∑ t : Fin n, a (some t) • (u t : E) := by
              simp [u, ← hπstar, hbzr_none, hπv]
    have hwW_sum : w = ∑ t : Fin n, a (some t) • u t := by
      apply Subtype.ext
      simpa using h1
    rw [hwW_sum]
    exact Submodule.sum_mem (span ℝ (Set.range u)) (by
      intro t ht
      exact Submodule.smul_mem _ (a (some t)) (Submodule.subset_span ⟨t, rfl⟩))
  let ub : Basis (Fin n) ℝ W := Basis.mk hli_u hsp_u
  have hueq : ∀ t : Fin n, ub t = u t := by
    intro t
    exact Basis.mk_apply hli_u hsp_u t
  have hfinK1 : finrank ℝ (K₁ : Submodule ℝ E) = 1 := by
    dsimp [K₁]
    exact finrank_span_singleton hv0
  have hfinW : finrank ℝ W = d - 1 := by
    have hadd := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (E := E) K₁
    rw [hfin] at hadd
    dsimp [W]
    omega
  let Λ' : Submodule ℤ W := span ℤ (Set.range ub)
  have hΛ'_def : Λ' = span ℤ (Set.range u) := by
    apply congrArg (fun f : Fin n → W => span ℤ (Set.range f))
    funext t
    exact hueq t
  letI : DiscreteTopology Λ' := by
    dsimp [Λ']
    infer_instance
  letI : IsZLattice ℝ Λ' := by
    dsimp [Λ']
    infer_instance

  have hπΛ : ∀ m : E, m ∈ L → π m ∈ Λ' := by
    intro m hmL
    let ml : L := ⟨m, hmL⟩
    let c : Option (Fin n) →₀ ℤ := bfull.repr ml
    have hml_sum : ml = ∑ j : Option (Fin n), c j • bfull j := by
      simpa [c] using (bfull.sum_repr ml)
    have hmE : (m : E) = ∑ j : Option (Fin n), (c j : ℤ) • (bfull j : E) := by
      have h := congrArg (fun z : L => (z : E)) hml_sum
      simpa using h
    have hbzr_apply (j : Option (Fin n)) : bzr j = (bfull j : E) := by
      rw [Module.Basis.ofZLatticeBasis_apply]
    have hmER : (m : E) = ∑ j : Option (Fin n), ((c j : ℤ) : ℝ) • bzr j := by
      calc
        (m : E) = ∑ j : Option (Fin n), (c j : ℤ) • (bfull j : E) := hmE
        _ = ∑ j : Option (Fin n), ((c j : ℤ) : ℝ) • bzr j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hbzr_apply j]
          exact (Int.cast_smul_eq_zsmul ℝ (c j) (bfull j : E)).symm
    have hπm : π m = ∑ j : Option (Fin n), ((c j : ℤ) : ℝ) • π (bzr j) := by
      have h := congrArg (fun z : E => π z) hmER
      simpa using h
    have hπm2 : π m = ∑ t : Fin n, ((c (some t) : ℤ) : ℝ) • u t := by
      calc
        π m = ∑ j : Option (Fin n), ((c j : ℤ) : ℝ) • π (bzr j) := hπm
        _ = ((c none : ℤ) : ℝ) • π (bzr none) + ∑ t : Fin n, ((c (some t) : ℤ) : ℝ) • π (bzr (some t)) := by
              rw [Fintype.sum_option]
        _ = ∑ t : Fin n, ((c (some t) : ℤ) : ℝ) • u t := by
              simp [hbzr_none, hπv, u]
    have hmem_u : π m ∈ span ℤ (Set.range u) := by
      rw [hπm2]
      refine Submodule.sum_mem (span ℤ (Set.range u)) ?_
      intro t ht
      rw [Int.cast_smul_eq_zsmul ℝ (c (some t)) (u t)]
      exact Submodule.smul_mem (span ℤ (Set.range u)) (c (some t)) (Submodule.subset_span ⟨t, rfl⟩)
    rw [hΛ'_def]
    exact hmem_u
  have hmin' : ∀ ⦃w : W⦄, w ∈ ldual W Λ' → w ≠ 0 → 1 ≤ ‖w‖ := by
    intro w hwld hw0
    have hwE_ldual : (w : E) ∈ ldual E L := by
      rw [LatticeDefs.mem_ldual]
      intro m hmL
      have hpm : π m ∈ Λ' := hπΛ m hmL
      rcases (LatticeDefs.mem_ldual.mp hwld) (π m) hpm with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      calc
        ⟪(w : E), m⟫ = ⟪(w : E), (π m : E)⟫ := (h_inner_pi w m).symm
        _ = ⟪w, π m⟫ := rfl
        _ = (z : ℝ) := hz
    have hw0E : (w : E) ≠ 0 := by
      intro h
      apply hw0
      apply Subtype.ext
      exact h
    have h1 : 1 ≤ ‖(w : E)‖ := hmin hwE_ldual hw0E
    simpa using h1

  let xW : W := π x
  obtain ⟨m1, hm1Λ, hdist⟩ := ih (E := W) (L := Λ') hfinW hmin' xW
  let m1' : span ℤ (Set.range ub) := ⟨m1, by simpa using hm1Λ⟩
  let ubr : Basis (Fin n) ℤ (span ℤ (Set.range ub)) := ub.restrictScalars ℤ
  let dcoef : Fin n →₀ ℤ := ubr.repr m1'
  have hm1'_sum : m1' = ∑ i : Fin n, dcoef i • ubr i := by
    simpa [dcoef] using (ubr.sum_repr m1')
  have hm1_sum : m1 = ∑ i : Fin n, dcoef i • ub i := by
    have h := congrArg (fun z : span ℤ (Set.range ub) => (z : W)) hm1'_sum
    simpa [ubr, Module.Basis.restrictScalars_apply] using h
  let m0 : L := ∑ i : Fin n, dcoef i • bfull (some i)
  have hbzr_some' (i : Fin n) : bzr (some i) = (bfull (some i) : E) := hbzr_some i
  have hm0ER : ((m0 : L) : E) = ∑ i : Fin n, ((dcoef i : ℤ) : ℝ) • bzr (some i) := by
    have h0 : ((m0 : L) : E) = ∑ i : Fin n, (dcoef i : ℤ) • (bfull (some i) : E) := by
      dsimp [m0]
      simp
    calc
      ((m0 : L) : E) = ∑ i : Fin n, (dcoef i : ℤ) • (bfull (some i) : E) := h0
      _ = ∑ i : Fin n, ((dcoef i : ℤ) : ℝ) • bzr (some i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hbzr_some' i]
        exact (Int.cast_smul_eq_zsmul ℝ (dcoef i) (bfull (some i) : E)).symm
  have hπm0 : π (m0 : E) = m1 := by
    calc
      π ((m0 : L) : E) = ∑ i : Fin n, ((dcoef i : ℤ) : ℝ) • π (bzr (some i)) := by
        have h := congrArg (fun z : E => π z) hm0ER
        simpa using h
      _ = ∑ i : Fin n, ((dcoef i : ℤ) : ℝ) • u i := by
        simp [u]
      _ = ∑ i : Fin n, (dcoef i : ℤ) • u i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Int.cast_smul_eq_zsmul ℝ (dcoef i) (u i)
      _ = ∑ i : Fin n, (dcoef i : ℤ) • ub i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hueq i]
      _ = m1 := hm1_sum.symm

  have hstar_m0 : star (m0 : E) = (m1 : E) := by
    rw [← hπstar (m0 : E)]
    exact congrArg (fun z : W => (z : E)) hπm0
  have hx_orth : x - star x ∈ Wᗮ := by
    dsimp [star]
    exact Submodule.sub_starProjection_mem_orthogonal x
  have hxstar : x - star x ∈ K₁ := by
    rwa [hWperp] at hx_orth
  have hm0_orth : (m0 : E) - star (m0 : E) ∈ Wᗮ := by
    dsimp [star]
    exact Submodule.sub_starProjection_mem_orthogonal (m0 : E)
  have hm0v : (m0 : E) - (m1 : E) ∈ K₁ := by
    rwa [hWperp, hstar_m0] at hm0_orth
  rcases (Submodule.mem_span_singleton.mp hxstar) with ⟨c1, hc1⟩
  rcases (Submodule.mem_span_singleton.mp hm0v) with ⟨c2, hc2⟩
  rcases exists_int_close (c1 - c2) with ⟨k, hk⟩
  let m : E := (m0 : E) + (k : ℝ) • v
  have hk_smul : (k : ℝ) • v ∈ L := by
    rw [Int.cast_smul_eq_zsmul ℝ k v]
    exact Submodule.smul_mem L k hvL
  have hm_mem : m ∈ L := by
    dsimp [m]
    exact Submodule.add_mem L m0.2 hk_smul
  have hdiff : (x - star x) - ((m0 : E) - (m1 : E)) = (c1 - c2) • v := by
    rw [← hc1, ← hc2]
    rw [← sub_smul]
  have hrv_eq : (x - star x) - ((m0 : E) - (m1 : E)) - (k : ℝ) • v =
      (c1 - c2 - (k : ℝ)) • v := by
    rw [hdiff]
    rw [← sub_smul]
  have hrv_norm : ‖(x - star x) - ((m0 : E) - (m1 : E)) - (k : ℝ) • v‖ ≤ ‖v‖ / 2 := by
    rw [hrv_eq]
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |c1 - c2 - (k : ℝ)| * ‖v‖ ≤ (1 / 2) * ‖v‖ := by
        exact mul_le_mul_of_nonneg_right hk (norm_nonneg v)
      _ = ‖v‖ / 2 := by ring
  have hsplit : x - m = (((π x - m1 : W) : E)) + ((x - star x) - ((m0 : E) - (m1 : E)) - (k : ℝ) • v) := by
    have hterm : (((π x - m1 : W) : E)) = star x - (m1 : E) := by
      change (π x : E) - (m1 : E) = star x - (m1 : E)
      rw [hπstar x]
    rw [hterm]
    dsimp [m]
    abel
  have hdistE : ‖(((π x - m1 : W) : E))‖ ≤ (d - 1 : ℝ)^5 + 1 := by
    dsimp [xW] at hdist
    have hd1n : 1 ≤ d := by omega
    have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub hd1n]
      norm_num
    rw [hcast] at hdist
    simpa using hdist
  have hbd : ‖x - m‖ ≤ (d - 1 : ℝ)^5 + 1 + ‖v‖ / 2 := by
    rw [hsplit]
    calc
      ‖(((π x - m1 : W) : E)) + ((x - star x) - ((m0 : E) - (m1 : E)) - (k : ℝ) • v)‖
          ≤ ‖(((π x - m1 : W) : E))‖ + ‖((x - star x) - ((m0 : E) - (m1 : E)) - (k : ℝ) • v)‖ :=
            norm_add_le _ _
      _ ≤ (d - 1 : ℝ)^5 + 1 + ‖v‖ / 2 := by
            exact add_le_add hdistE hrv_norm
  have hvb' : ‖v‖ ≤ 4 * (d : ℝ) := by
    rw [hfin] at hvb
    exact hvb
  have harith : (d - 1 : ℝ)^5 + 1 + 2 * (d : ℝ) ≤ (d : ℝ)^5 + 1 := by
    let s : ℝ := (d : ℝ) - 2
    have hs : 0 ≤ s := by
      dsimp [s]
      linarith [show (2 : ℝ) ≤ (d : ℝ) by exact_mod_cast hd]
    have hfac : (d : ℝ)^5 - ((d : ℝ) - 1)^5 - 2 * (d : ℝ) =
        27 + 73 * s + 70 * s^2 + 30 * s^3 + 5 * s^4 := by
      dsimp [s]
      ring
    have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
    have hs3 : 0 ≤ s ^ 3 := by positivity
    have hs4 : 0 ≤ s ^ 4 := by positivity
    nlinarith
  have hfinal : ‖x - m‖ ≤ (d : ℝ)^5 + 1 := by
    have hvb2 : ‖v‖ / 2 ≤ 2 * (d : ℝ) := by
      nlinarith [hvb']
    linarith
  exact ⟨m, hm_mem, hfinal⟩

end RecursionStep

end Submission.CovRec
