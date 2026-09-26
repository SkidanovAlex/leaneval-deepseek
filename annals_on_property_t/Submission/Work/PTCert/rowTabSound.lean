import Mathlib
import Submission.Work.PTCert.Glue3

/-! Guidance from the project lead (the requester):

Context: `Submission/Work/PTCert/Glue2.lean` (concrete objects of the rank-5 certificate: EI, fE,
actE, actN, repE, nuE, Pmat, …, and the semantic Props ESem/TabSem/NSem/RowSem/GroupSem/OrbLabSem/
ClassSem/KleinSem = plain meanings of the kernel checks) and `Glue3.lean` (the Props of the
mathematical steps). READ BOTH FIRST, and `NOTES_LEAD_glue.md` (workspace root) for the whole chain.
Hypotheses of the form `CodeFacts`, `ConjActFacts`, `ActCSound`, `BitsBridge`, `OrbitDecomp`,
`KleinLevel`, `FourierTransport`, `LdlChainSound`, `WhtSound` are GlueDefs Props proved in parallel by
other agents; `ESem`… are data facts proved by kernel checks. Use them as given; do not re-prove them.
Already-proved theorems you may use directly: `Work.PTCert.avgMatInvariant`, `rowFormula`,
`twistedFourierCriterion`, `psdOfBlock`, `psdSignedPerm`, `labelPrinciple`, `avgPrinciple`, `gramSOS`,
`avgGram`, `ldlScaledPrinciple`, `letterAction`, `modelSound`, `sigmaGroupFacts` (+ namespace
SigmaFacts: signAut_mul, signAut_inv, sigAut_mul, sigAut_inv, mem_SigmaSet_iff, ...), `permCheckKSound`.
NEVER unfold the big data definitions (`eAll`, `eM`, …) or try `decide` on them: all data facts come
through the Sem hypotheses. Do not change Glue*.lean. If the statement is false, `declare_false`
with the concrete reason (and say which hypothesis is missing).
Unfold `rowCheck` (KernelCert.lean) on the singleton [t]: allL [t] p = p t, i.e.
wht 5 vs == unpack32 (rowT.get t) with vs = (List.range 32).map (fun sc => sv (p8 valT (2048 r + ((o >>> (11*sc)) &&& 2047)))),
o = olT.get t. `==` on List ℤ true ⇒ equality (beq_iff_eq / LawfulBEq). WhtSound turns wht 5 vs into
(List.range 32).map (fun S => Σ_{sc<32} chiS5 S sc * vs[sc]). rowVal rowTs r S t = f32 (…get t) S =
(unpack32 (…get t))[S] (unpack32 = map f32 over range 32; List.getElem_map, List.getElem_range).
OrbLabSem rewrites the label field as labE r (actC cmT (ntab sc) (rp t)); keyOf r g = 2048 * r + g.
Note rowTs.getD r (NT.leaf 0) is used both in rowCheck and in rowVal.
-/

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G

namespace RowTabAux

/-- `allL` on a singleton list is the predicate itself. -/
lemma allL_singleton (p : ℕ → Bool) (t : ℕ) : allL [t] p = p t := by
  simp [allL]

/-- **Unfolding `rowCheck` on one rep.**  If the singleton check `rowCheck valT olT rowT r [t]`
passes, then the Walsh–Hadamard transform of the `32` row values equals the packed row `t` of
`rowT`.  The `32` values are `sv (p8 valT (2048 r + label sc))` with `label sc` read from the
orbit-label leaf `olT.get t` (field `sc`, `11` bits). -/
lemma rowCheck_single (valT olT rowT : NT) (r t : ℕ)
    (h : rowCheck valT olT rowT r [t] = true) :
    wht 5 ((List.range 32).map (fun sc =>
        sv (p8 valT (2048 * r + (((olT.get t) >>> (11 * sc)) &&& 2047))))) =
      unpack32 (rowT.get t) := by
  simp only [rowCheck, allL_singleton] at h
  rw [beq_iff_eq] at h
  exact h

/-- `getD` into `(List.range 32).map f` is `f` at the index. -/
lemma getD_map_range32 {f : ℕ → ℤ} {i : ℕ} (h : i < 32) :
    ((List.range 32).map f).getD i 0 = f i := by
  have hlen : i < ((List.range 32).map f).length := by simpa using h
  rw [List.getD_eq_getElem _ _ hlen, List.getElem_map]
  simp

/-- The `S`-th entry of `unpack32 v` is `f32 v S`. -/
lemma unpack32_getD (v i : ℕ) (h : i < 32) : (unpack32 v).getD i 0 = f32 v i := by
  unfold unpack32
  exact getD_map_range32 h

end RowTabAux

open RowTabAux

/-- **(I) Row tables** from the kernel `rowCheck`s.  If for every row `r < 18` and every
N-representative `t < 611` the singleton kernel check holds, then the row table `rowTs` contains
the character sums `Row_S(x₀_r, t) = Σ_{sc < 32} χ_S(sc) · val(r, label of ν_sc · rep_t)`. -/
theorem rowTabSound (hW : WhtSound) (hO : OrbLabSem) : RowTabSound := by
  intro valT rowTs hchk r hr t ht S hS
  -- the singleton kernel check for this row and rep
  have hc := hchk r hr t ht
  have hrow := rowCheck_single valT (olTs.getD r (NT.leaf 0)) (rowTs.getD r (NT.leaf 0)) r t hc
  -- the length hypothesis of `WhtSound`
  have hlen : ((List.range 32).map (fun sc =>
      sv (p8 valT (2048 * r + ((((olTs.getD r (NT.leaf 0)).get t) >>> (11 * sc)) &&& 2047))))).length = 32 := by
    simp
  have hWv := hW _ hlen
  -- `unpack32` of the packed row `t` is the list of character sums
  have hgetD := congrArg (fun l : List ℤ => l.getD S 0) (hrow.symm.trans hWv)
  rw [unpack32_getD _ _ hS, getD_map_range32 hS] at hgetD
  show f32 ((rowTs.getD r (NT.leaf 0)).get t) S = _
  rw [hgetD]
  -- rewrite each value by the orbit-label semantics, then fold `keyOf`
  refine Finset.sum_congr rfl fun sc hsc => ?_
  have hsc' : sc < 32 := Finset.mem_range.mp hsc
  rw [getD_map_range32 (f := fun sc =>
    sv (p8 valT (2048 * r + ((((olTs.getD r (NT.leaf 0)).get t) >>> (11 * sc)) &&& 2047)))) hsc']
  rw [hO r hr t ht sc hsc']
  simp only [keyOf]

end Work.PTCert
