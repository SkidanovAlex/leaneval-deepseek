import Mathlib
import Submission.NK.CFTLib.hilbertReciprocityCyclicAux
import Submission.NK.CFTLib.HRclean.transferMainClean

/-! Guidance from the project lead (the requester):

# Guidance: Hilbert reciprocity for cyclic extensions ("a local norm at all places but one is a local norm there too")
RULE: no licensed inputs; build what is missing. Library item used by the existence theorem (unramifiedness of class
fields), the Neukirch containment (support of global Brauer classes) and others.
Equivalent: the cyclic algebra (a, L/K) ∈ Br(L/K) cannot be supported at exactly one place (Σ_v inv_v = 0).
ON DISK: `NK.CFTLib.fundamentalClassElement` (global fundamental class, PROVED), `NK.CFTLib.ARL.artinReciprocity_cyclotomic`
(cyclotomic reciprocity, PROVED), injectivity Br(L/K) ↪ ⊕ Br(L_w/K_v) (`NK.GlobalCFTdeep.hbnUnits`, Hasse norm theorem),
local norm index (`LocalReciprocityLubinTate.NormIndex`), `NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm`.
ROUTE (Milne CFT VII.7/VIII.4; Cassels–Fröhlich VII §9–11): ...
-/

namespace NK.CFTLib

/-- **Hilbert reciprocity for cyclic extensions of number fields** in the "no singleton place of
local-norm failure" form (Milne, *CFT*, VII.8.1(a) / VIII.2 Example 2.2(ii)): an `a ∈ Kˣ` which is
a local norm at every place `v ≠ v₀` is a local norm at `v₀` as well.

This is the arithmetic heart of the deliverable `NK.CFTLib.hilbertReciprocity_cyclic`; the
statement is `HilbertReciprocityOnePlace` of
`Submission/Work/CFTLib/hilbertReciprocityCyclicAux.lean`, unfolded. -/
theorem hilbertReciprocity_onePlace_aux : HilbertReciprocityOnePlace :=
  -- The arithmetic content (Hilbert reciprocity `∑_v inv_v = 0` for cyclic `L/K`, i.e. the cyclic
  -- algebra `(a, L/K)` cannot be supported at exactly one place) is assembled in
  -- `Submission/Work/CFTLib/HRclean/transferMainClean.lean` from
  --   * `NK.CFTLib.HRclean.Transfer.cycClass_eq_zero_of_transfer_main` — the Brauer transfer: the
  --     Hasse–Brauer–Noether theorem at the level `E/M`, the translation identity
  --     `cycClassOf_translation`, the localisation dictionaries at the levels `M/K`, `E/M`, `L/K`,
  --     the injectivity of the local level inflation (`locUnits_inflation_eq_zero_iff`, clean copy
  --     `NK.CFTLib.HRclean.T4`), inflation–restriction exactness (`NK.CFTLib.HRclean.T3`) and
  --     the Hasse principle at `M/K`;
  --   * `NK.CFTLib.HRdescent.localConditionCyclotomicPrimeOdd` — the local condition at `v₀`
  --     (Milne III.3.5/III.3.6), with the cyclotomic level unramified at `v₀`;
  --   * `NK.CFTLib.cyclotomicCruxAt_of_coprime` — Hilbert reciprocity at the cyclotomic level.
  -- (The modules in `Submission/Work/CFTLib/HRclean/` are clean copies of the modules in which
  -- these statements were originally phrased; see the `README.md` there for the import cycle that
  -- forces the copy.)
  NK.CFTLib.HRclean.Transfer.hilbertReciprocityOnePlace_main

/-- **Hilbert reciprocity for cyclic extensions of number fields, "one place omitted" form.**

An idèle `z` supported at a single place `v₀` such that `P(a)·z` is an idèle norm forces `P(a)`
itself to be an idèle norm: equivalently, an element of `Kˣ` which is a local norm at every place
different from `v₀` is a local norm at `v₀`, hence (by Hasse's norm theorem) a global norm.

The reduction to `HilbertReciprocityOnePlace` is proved sorry-free in
`Submission/Work/CFTLib/hilbertReciprocityCyclicAux.lean`
(`NK.CFTLib.hilbertReciprocity_cyclic_of_onePlace`). -/
theorem hilbertReciprocity_cyclic (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (a : Kˣ) (v₀ : NK.GlobalCFT.Place K)
    (h : ∃ z : NK.GlobalCFT.Idele K, (∀ v, v ≠ v₀ → z v = 1) ∧
      NK.GlobalCFT.Idele.principalIdele K a * z ∈ NK.GlobalCFT.Idele.normImage K L) :
    NK.GlobalCFT.Idele.principalIdele K a ∈ NK.GlobalCFT.Idele.normImage K L :=
  hilbertReciprocity_cyclic_of_onePlace hilbertReciprocity_onePlace_aux K L a v₀ h

end NK.CFTLib
