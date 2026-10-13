/-
  `Work.CoreStep.stratReindex_good_bwd`

  Reindexing the coordinates of an ambient stratum `Stratum 0 N` along a coordinate equivalence
  `e : Fin (0 + N) ≃ Fin (0 + N')` preserves `Stratum.Good` -- the "backward" half of the
  invariance of `Good` under a renaming of the coordinates (the forward half is
  `Work.CoreStep.stratReindex_good_fwd`).

  The three conjuncts of `Good` are transported as follows.

  * *Vanishing of the equations on the set.*  `Stratum.reindex_h_eval` (`StratReindexDefs`) says
    that the reindexed equations at `z` are the original equations at `z ∘ e`, while
    `z ∈ (reindex e S).X.set` is exactly `z ∘ e ∈ S.X.set` (`Stratum.reindex_mem`).

  * *Full rank of the Jacobian.*  Since `p = 0`, *every* coordinate of `Fin (0 + N')` is a "last"
    coordinate, so the Jacobian matrix of the reindexed stratum is the Jacobian matrix of `S` with
    its columns permuted by the equivalence `σ : Fin N' ≃ Fin N`.  Here `σ` is the restriction of
    `e.symm` to the copies of `Fin _` produced by `0 + _`, i.e.
    `σ l = (e.symm (Fin.natAdd 0 l)).cast (Nat.zero_add N)`; the rank is permutation invariant by
    `Matrix.rank_submatrix`.  (This is the only place where `p = 0` is used; for `p > 0` the `Fin q`
    directions are the *last* coordinates and an arbitrary coordinate renaming need not preserve
    them.)  See `StratReindexBwd.reindex_jacMatrix_rank`.

  * *Locality.*  `Good` asks that the zero set of the equations, inside the fibre over
    `projFirst 0 N' z`, be contained in the set locally at `z`.  For `p = 0` the fibre condition is
    vacuous (both sides live in the one-point space `Fin 0 → ℝ`), and the statement is transported
    along the homeomorphism `Work.WilE7.pullHomeo e`, which maps `z` to `z ∘ e` and identifies the
    zero sets of the two families of equations.  See `StratReindexBwd.reindex_good_locality`.
-/
import Mathlib
import Submission.Work.CoreStep.StratReindexDefs

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology

namespace Work.CoreStep

open WilkiesDesign WilkiesDesign.E

/-- The identification `Fin (0 + n) ≃ Fin n` of the two copies of `Fin n` differing by `0 + _`
(the `0 + _` is not definitionally the identity, so it has to be made explicit). -/
def StratReindexBwd.finCastEquiv (n : ℕ) : Fin (0 + n) ≃ Fin n := finCongr (Nat.zero_add n)

/-- `Fin.natAdd 0 : Fin n → Fin (0 + n)` is a retraction of the cast `Fin (0 + n) → Fin n`. -/
theorem StratReindexBwd.natAdd_zero_cast (n : ℕ) (x : Fin (0 + n)) :
    Fin.natAdd 0 (x.cast (Nat.zero_add n)) = x := by
  ext; simp

/-- `Fin.natAdd 0 : Fin n → Fin (0 + n)` is a section of the cast `Fin (0 + n) → Fin n`. -/
theorem StratReindexBwd.cast_natAdd_zero (n : ℕ) (l : Fin n) :
    (Fin.natAdd 0 l).cast (Nat.zero_add n) = l := by
  ext; simp

/-- **Reindexing permutes the columns of the Jacobian matrix**, hence does not change its rank: the
Jacobian matrix of `Stratum.reindex e S` at `z` is the Jacobian matrix of `S` at `z ∘ e` with the
columns permuted by the coordinate equivalence `σ` given by the restriction of `e.symm` across
`0 + _`. -/
theorem StratReindexBwd.reindex_jacMatrix_rank {N N' : ℕ} (e : Fin (0 + N) ≃ Fin (0 + N'))
    (S : WilkiesDesign.E.Stratum 0 N) (z : Fin (0 + N') → ℝ) :
    (Matrix.of fun (a : Fin S.j) (l : Fin N') =>
        eaEval (Stratum.reindex e S).X.c
          (eaD (Stratum.reindex e S).X.c (Fin.natAdd 0 l) ((Stratum.reindex e S).h a)) z).rank =
      (Matrix.of fun (a : Fin S.j) (l : Fin N) =>
        eaEval S.X.c (eaD S.X.c (Fin.natAdd 0 l) (S.h a)) (fun i => z (e i))).rank := by
  set σ : Fin N' ≃ Fin N :=
    (StratReindexBwd.finCastEquiv N').symm.trans (e.symm.trans (StratReindexBwd.finCastEquiv N))
    with hσdef
  have hσcoe : ⇑σ = fun l => (e.symm (Fin.natAdd 0 l)).cast (Nat.zero_add N) := by
    rw [hσdef]; funext l; simp [StratReindexBwd.finCastEquiv, finCongr]
  have hσidx : ∀ l : Fin N', Fin.natAdd 0 (σ l) = e.symm (Fin.natAdd 0 l) := by
    intro l; rw [hσcoe]; ext; simp
  have hmat : (Matrix.of fun (a : Fin S.j) (l : Fin N') =>
        eaEval (Stratum.reindex e S).X.c
          (eaD (Stratum.reindex e S).X.c (Fin.natAdd 0 l) ((Stratum.reindex e S).h a)) z)
      = (Matrix.of fun (a : Fin S.j) (l : Fin N) =>
        eaEval S.X.c (eaD S.X.c (Fin.natAdd 0 l) (S.h a)) (fun i => z (e i))).submatrix
          (⇑(Equiv.refl (Fin S.j))) (⇑σ) := by
    ext a l
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Equiv.refl_apply]
    rw [Stratum.reindex_jac_entry, ← hσidx l]
  rw [hmat, Matrix.rank_submatrix]

/-- **Locality of `Good` transports along a coordinate renaming.**  If the zero set of the
equations of `S` is locally contained in `S.X.set` near `z ∘ e`, then the zero set of the equations
of `Stratum.reindex e S` is locally contained in its own set near `z`: the two conditions correspond
under the homeomorphism `Work.WilE7.pullHomeo e` (`z ↦ z ∘ e`), and for `p = 0` the fibre condition
`projFirst 0 _ z' = projFirst 0 _ z` is automatic. -/
theorem StratReindexBwd.reindex_good_locality {N N' : ℕ} (e : Fin (0 + N) ≃ Fin (0 + N'))
    (S : WilkiesDesign.E.Stratum 0 N) (z : Fin (0 + N') → ℝ)
    (hloc : ∀ᶠ w' in 𝓝 (fun i : Fin (0 + N) => z (e i)),
      WilkiesDesign.E.projFirst 0 N w' = WilkiesDesign.E.projFirst 0 N (fun i => z (e i)) →
      (∀ a, eaEval S.X.c (S.h a) w' = 0) → w' ∈ S.X.set) :
    ∀ᶠ z' in 𝓝 z,
      WilkiesDesign.E.projFirst 0 N' z' = WilkiesDesign.E.projFirst 0 N' z →
      (∀ a, eaEval (Stratum.reindex e S).X.c ((Stratum.reindex e S).h a) z' = 0) →
        z' ∈ (Stratum.reindex e S).X.set := by
  -- For `p = 0` the fibre condition `projFirst 0 N · = projFirst 0 N ·` is vacuous:
  have hproj : ∀ w' : Fin (0 + N) → ℝ,
      WilkiesDesign.E.projFirst 0 N w' = WilkiesDesign.E.projFirst 0 N (fun i => z (e i)) := by
    intro w'; funext i; exact Fin.elim0 i
  have hloc' : ∀ᶠ w' in 𝓝 (fun i => z (e i)),
      (∀ a, eaEval S.X.c (S.h a) w' = 0) → w' ∈ S.X.set :=
    hloc.mono fun w' hp hq => hp (hproj w') hq
  -- Push the statement along the homeomorphism `pullHomeo e`, which sends `z` to `z ∘ e`:
  have hloc'' : ∀ᶠ w' in Filter.map (⇑(Work.WilE7.pullHomeo e)) (𝓝 z),
      (∀ a, eaEval S.X.c (S.h a) w' = 0) → w' ∈ S.X.set := by
    rw [(Work.WilE7.pullHomeo e).map_nhds_eq z]
    exact hloc'
  have h2' : ∀ᶠ z' in 𝓝 z,
      (∀ a, eaEval S.X.c (S.h a) ((Work.WilE7.pullHomeo e) z') = 0) →
        ((Work.WilE7.pullHomeo e) z') ∈ S.X.set := Filter.eventually_map.mp hloc''
  refine h2'.mono fun z' hP _ hz0 => ?_
  have hh : ((Work.WilE7.pullHomeo e) z') ∈ S.X.set := by
    refine hP fun a => ?_
    rw [show (Work.WilE7.pullHomeo e) z' = fun i => z' (e i) from rfl,
      ← Stratum.reindex_h_eval e S z' a]
    exact hz0 a
  exact (Stratum.reindex_mem e S z').mpr hh

theorem stratReindex_good_bwd {N N' : ℕ} (e : Fin (0 + N) ≃ Fin (0 + N'))
    (S : WilkiesDesign.E.Stratum 0 N) :
    WilkiesDesign.E.Stratum.Good S →
      WilkiesDesign.E.Stratum.Good (Work.CoreStep.Stratum.reindex e S) := by
  intro hS z hz
  have hzS : (fun i : Fin (0 + N) => z (e i)) ∈ S.X.set := (Stratum.reindex_mem e S z).mp hz
  obtain ⟨h1, h2, h3⟩ := hS _ hzS
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rw [Stratum.reindex_h_eval e S z a]
    exact h1 a
  · exact (StratReindexBwd.reindex_jacMatrix_rank e S z).trans h2
  · exact StratReindexBwd.reindex_good_locality e S z h3

end Work.CoreStep
