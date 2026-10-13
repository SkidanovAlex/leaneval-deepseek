/-
  WilE9 / Sharp — `sdSet` in the multi-index form of the domain.

  `Main2.lean` indexes the domain condition by the *multi-indices* `μ` with `∑ μ ≤ k` (of which
  there are `binom(n+k,n)`), because `Gen.inter` adds the per-index degree bounds and the
  list-indexed `DomSet` has `Σ_{l≤k} n^l` summands — exponential in `k`.  This file records the
  corresponding form of the identification `Work.WilE9.sdSet_eq`:

      `sdSet f k v = {z | Fin.init z ∈ DomSet2 n k S (graphOf f)} ∩ Eset n S (List.ofFn v)`,

  which is the form the final assembly consumes (the domain is needed in the `DomSet2` shape for
  the polynomial degree bound `DomSet2_gen`).

  The proof is the same bookkeeping as `Sharp/sdSet_eq.lean`, with `DomSet2` in place of `DomSet`,
  so that the axiom closure of the final assembly does not pass through the `SdClean` copy of the
  domain analysis.
-/
import Mathlib
import Submission.Work.WilE9.Sharp.DomSet2_eq
import Submission.Work.WilE9.Deriv.glDeriv_ofFn

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical Topology
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-- The `C^k`-locus of a function is open, hence equal to its own interior. -/
theorem interior_contDiffAt_eq' {n : ℕ} (f : (Fin n → ℝ) → ℝ) (k : ℕ) :
    interior {x : Fin n → ℝ | ContDiffAt ℝ k f x} = {x : Fin n → ℝ | ContDiffAt ℝ k f x} := by
  refine IsOpen.interior_eq ?_
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx' : ContDiffAt ℝ k f x := hx
  exact hx'.eventually (by simp)

/-- **The identification of the sharp-derivative set, multi-index form.**  Under `SecSpec`,
`LimSpec` and order independence of `Eset`, the sharp-derivative set is the `DomSet2`-domain
condition intersected with `Eset n S (List.ofFn v)`. -/
theorem sdSet2_eq {n k : ℕ} {S : List (AEStratum n)} {f : (Fin n → ℝ) → ℝ}
    (hsec : SecSpec n k S f) (hlim : LimSpec n k S f)
    (hperm : ∀ (L L' : List (Fin n)), L.length ≤ k → L'.length ≤ k → List.Perm L L' →
      Eset n S L = Eset n S L')
    (v : Fin k → Fin n) :
    Work.WilE9.sdSet f k v =
      {z : Fin (n + 1) → ℝ | Fin.init z ∈ DomSet2 n k S (WilkiesDesign.graphOf f)} ∩
        Eset n S (List.ofFn v) := by
  -- the domain condition of `DomSet2` is the `C^k`-locus, which is open
  have hDomI : DomSet2 n k S (WilkiesDesign.graphOf f)
      = interior {x : Fin n → ℝ | ContDiffAt ℝ k f x} := by
    rw [DomSet2_eq hsec hlim hperm, interior_contDiffAt_eq']
  have hlen : (List.ofFn v).length ≤ k := by simp
  ext z
  rw [Work.WilE9.sdSet_eq, hDomI]
  constructor
  · rintro ⟨hC, hval⟩
    refine ⟨hC, ?_⟩
    have hzC : ContDiffAt ℝ k f (Fin.init z) := interior_subset hC
    have hzC' : ContDiffAt ℝ ((List.ofFn v).length) f (Fin.init z) := by simpa using hzC
    have hgl := Work.WilE9.Deriv.glDeriv_ofFn f (Fin.init z) v hzC
    have hmem : Fin.snoc (Fin.init z) (z (Fin.last n)) ∈ Eset n S (List.ofFn v) :=
      (hsec (List.ofFn v) hlen (Fin.init z) (z (Fin.last n)) hzC').mpr (by
        rw [hval]
        exact hgl.symm)
    rwa [Fin.snoc_init_self] at hmem
  · rintro ⟨hC, hzE⟩
    refine ⟨hC, ?_⟩
    have hzC : ContDiffAt ℝ k f (Fin.init z) := interior_subset hC
    have hzC' : ContDiffAt ℝ ((List.ofFn v).length) f (Fin.init z) := by simpa using hzC
    have hgl := Work.WilE9.Deriv.glDeriv_ofFn f (Fin.init z) v hzC
    have hE : Fin.snoc (Fin.init z) (z (Fin.last n)) ∈ Eset n S (List.ofFn v) := by
      rwa [Fin.snoc_init_self]
    rw [(hsec (List.ofFn v) hlen (Fin.init z) (z (Fin.last n)) hzC').mp hE]
    exact hgl

end Work.WilE9.Sharp
