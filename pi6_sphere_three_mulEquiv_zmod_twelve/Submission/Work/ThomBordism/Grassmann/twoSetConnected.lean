import Mathlib
import Submission.Work.ThomBordism.TwoSet.Basic
import Submission.Work.ThomBordism.TwoSet.CompressBasic
import Submission.Work.ThomBordism.TwoSet.Assembly
import Submission.Work.ThomBordism.TwoSet.TraceAux
import Submission.Work.ThomBordism.TwoSet.subsingleton_piZero_of_homeomorph
import Submission.Work.ThomBordism.TwoSet.compressRel_twoSet

/-!
# `twoSetConnected`: the connectivity of a union of two open sets

The theorem is the classical Mayer–Vietoris statement for homotopy groups: if `X = U ∪ V` with
`U`, `V` open and the pairs `(V, U ∩ V)`, `(U, U ∩ V)` are `j`-connected, then the pair `(X, U)` is
`j`-connected, i.e. `π_j(X)` is trivial wherever `π_j(U)` is.

The proof is assembled from

* `Work.ThomBordism.TwoSet.Compress`, the compression property of a pair (tom Dieck (6.7.5));
* `Work.ThomBordism.TwoSet.Compress.ofSubsingleton` / `.ofSubsingletonZero`, which turn the
  connectivity hypotheses of the two pieces into compression properties (via the machinery
  `push_into_Z` of `TwoSet/Push.lean`);
* `Work.ThomBordism.TwoSet.compressRel_twoSet`, the two-set (Mayer–Vietoris) theorem: the
  compressions of `(U, U ∩ V)` and `(V, U ∩ V)` give the compression of `(X, U)`;
* `Work.ThomBordism.TwoSet.Compress.toSubsingleton`, which turns the compression of `(X, U)` on
  the piece containing the base point into the triviality of `π_j(X)` there.

All the ingredients are in the sibling modules of `Submission/Work/ThomBordism/TwoSet/`.
-/

open scoped Topology unitInterval

namespace Work.ThomBordism.Grassmann

open Work.ThomBordism.TwoSet

variable {X : Type*} [TopologicalSpace X]

/-- **Compression of the trace of `U` in `V`.**  If `π_d(V) = 0` for `d ≤ j` and
`π_d(U ∩ V) = 0` for `d + 1 ≤ j`, then every map `(Iᵈ, ∂Iᵈ) → (V, U ∩ V)` (`d ≤ j`) is homotopic,
relative to the boundary, into `U ∩ V`. -/
theorem compress_trace_of_subsingleton {U V : Set X} {j : ℕ}
    (hV : ∀ d, d ≤ j → ∀ v : ↥V, Subsingleton (HomotopyGroup (Fin d) ↥V v))
    (hUV : ∀ d, d + 1 ≤ j → ∀ w : ↥(U ∩ V), Subsingleton (HomotopyGroup (Fin d) ↥(U ∩ V) w))
    (hUVne : (U ∩ V).Nonempty) :
    ∀ d, d ≤ j → Compress ↥V {v : ↥V | (v : X) ∈ U} d := by
  intro d hd
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · subst h0
    refine Compress.ofSubsingletonZero (fun v => hV 0 (by omega) v) ?_
    obtain ⟨z, hz⟩ := hUVne
    exact ⟨(⟨⟨z, hz.2⟩, hz.1⟩ : {v : ↥V | (v : X) ∈ U}), hz.1⟩
  · refine Compress.ofSubsingleton hpos (fun v => hV d hd v) ?_
    intro z
    have hbase : traceHomeo z = (⟨z.1.1, ⟨z.2, z.1.2⟩⟩ : ↥(U ∩ V)) := rfl
    by_cases hd1 : d = 1
    · subst hd1
      exact subsingleton_piZero_of_homeomorph traceHomeo hbase
        (hUV 0 (by omega) ⟨z.1.1, ⟨z.2, z.1.2⟩⟩)
    · haveI : Nonempty (Fin (d - 1)) := ⟨⟨0, by omega⟩⟩
      exact subsingleton_of_homeomorph traceHomeo hbase (Fin (d - 1))
        (hUV (d - 1) (by omega) ⟨z.1.1, ⟨z.2, z.1.2⟩⟩)

/-- The homeomorphism `↥(V ∩ U) ≃ₜ ↥(U ∩ V)` (the two sets have the same elements). -/
def interSwapHomeo {U V : Set X} : ↥(V ∩ U) ≃ₜ ↥(U ∩ V) where
  toFun w := ⟨w.1, ⟨w.2.2, w.2.1⟩⟩
  invFun w := ⟨w.1, ⟨w.2.2, w.2.1⟩⟩
  left_inv w := by ext; rfl
  right_inv w := by ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- **The target.**  If `X = U ∪ V` with `U, V` open, `U ∩ V` nonempty, and the homotopy groups
`πᵢ` of `U`, `V` are trivial for `i < k` while those of `U ∩ V` are trivial for `i + 1 < k`, then
`πⱼ(X)` is trivial for `j < k`. -/
theorem twoSetConnected {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (hne : (U ∩ V).Nonempty) (k : ℕ)
    (hk : 2 ≤ k)
    (hUk : ∀ j, j < k → ∀ x : ↥U, Subsingleton (HomotopyGroup (Fin j) ↥U x))
    (hVk : ∀ j, j < k → ∀ x : ↥V, Subsingleton (HomotopyGroup (Fin j) ↥V x))
    (hUVk : ∀ j, j + 1 < k → ∀ x : ↥(U ∩ V), Subsingleton (HomotopyGroup (Fin j) ↥(U ∩ V) x)) :
    ∀ j, j < k → ∀ x : X, Subsingleton (HomotopyGroup (Fin j) X x) := by
  intro j hj x
  -- the compression of the two pieces
  have hVc : ∀ d, d ≤ j → Compress ↥V {v : ↥V | (v : X) ∈ U} d :=
    compress_trace_of_subsingleton (U := U) (V := V) (j := j)
      (fun d hd v => hVk d (by omega) v)
      (fun d hd w => hUVk d (by omega) w) hne
  have hUc : ∀ d, d ≤ j → Compress ↥U {u : ↥U | (u : X) ∈ V} d :=
    compress_trace_of_subsingleton (U := V) (V := U) (j := j)
      (fun d hd u => hUk d (by omega) u)
      (fun d hd w => by
        have hbase : interSwapHomeo w = (⟨w.1, ⟨w.2.2, w.2.1⟩⟩ : ↥(U ∩ V)) := rfl
        rcases Nat.eq_zero_or_pos d with h0 | hpos
        · subst h0
          exact subsingleton_piZero_of_homeomorph interSwapHomeo hbase
            (hUVk 0 (by omega) ⟨w.1, ⟨w.2.2, w.2.1⟩⟩)
        · haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
          exact subsingleton_of_homeomorph interSwapHomeo hbase (Fin d)
            (hUVk d (by omega) ⟨w.1, ⟨w.2.2, w.2.1⟩⟩))
      (hne.elim fun z hz => ⟨z, ⟨hz.2, hz.1⟩⟩)
  -- the two-set (Mayer–Vietoris) step
  have hXU : Compress X U j := compressRel_twoSet hU hV hcov j hVc hUc
  have hXV : Compress X V j := compressRel_twoSet hV hU (by rw [Set.union_comm]; exact hcov) j hUc hVc
  -- which piece contains the base point
  have hxu : x ∈ U ∨ x ∈ V := by
    have : x ∈ U ∪ V := by rw [hcov]; trivial
    exact this
  rcases hxu with hx | hx
  · exact Compress.toSubsingleton (U := U) hXU hx (hUk j hj ⟨x, hx⟩)
  · exact Compress.toSubsingleton (U := V) hXV hx (hVk j hj ⟨x, hx⟩)

end Work.ThomBordism.Grassmann
