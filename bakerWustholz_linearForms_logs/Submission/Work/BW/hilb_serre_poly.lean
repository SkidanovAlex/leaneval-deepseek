import Mathlib
import Submission.Work.BW.GradedHilbDefs
import Submission.Work.BW.HilbSerreDefs
import Submission.Work.BW.HilbStep
import Submission.Work.BW.finiteDim_vars_zero
import Submission.Work.BW.kFun_zero_eq
import Submission.Work.BW.isGrading_quoPiece
import Submission.Work.BW.isGrading_kerPiece
import Submission.Work.BW.finrank_relation
import Submission.Work.BW.hilb_serre_empty

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Multigraded Hilbert–Serre: for a finitely generated `MR N`-module `M` with a `ℤ^{N+1}`-grading
`piece` compatible with the ring grading (`IsGrading`, in `Submission/Work/BW/GradedHilbDefs.lean`),
such that every variable outside a finite set `V` acts as zero, the dimension of the `u`-th graded
piece is given by the binomial kernel `kFun` of a single polynomial `P`, with multiplicity vector
`β` sending `i` to the number of variables of `V` lying over the `i`-th factor.

Suggested route: induct on `V` (revert `M`, `piece`, the hypotheses first).
For `V = ∅`, `M` is annihilated by all variables, hence finite dimensional over `ℂ`; the grading is
an internal direct sum, so only finitely many pieces are nonzero: take `P` to be the `Finsupp`-sum
of `(dim (piece u)) • X^u` over those `u`, and use `IsGrading.eq_bot_of_neg` for negative degrees.
For the step `V = insert x s` (with `x ∉ s`), put `i` the first coordinate of `x` and `e` the weight
`wZ N x`. Let `C` be `M ⧸ (X x • ⊤)` with pieces the images of `piece u`, and let `K` be the kernel
of multiplication by `X x` on `M(-e)`, i.e. the submodule of `M` of elements killed by `X x`, with
pieces `piece (u - e) ⊓ K`. Both inherit an `IsGrading` with the same `eq_bot_of_neg` property, are
finitely generated, have finite dimensional pieces, and are annihilated by every variable outside
`s` (the variable `x` annihilates `K` and `C` by construction). Apply the induction hypothesis to
both, obtaining `P_C` and `P_K`, and set `P` to be `P_C - P_K`.
Rank-nullity for the multiplication map from `piece (u - e)` to `piece u` (its image is
`piece u ⊓ (X x • ⊤)`, using `DirectSum.IsInternal.submodule_iSupIndep` and the internal
decomposition) gives that the difference of the dimensions of `piece u` and `piece (u - e)` equals
the difference of the dimensions of the pieces of `C` and `K`. With `β'` the vector obtained from
`β` by replacing the `i`-th entry by `β i - 1`, the identity `kFun_diff` in `GradedHilbDefs` gives
that the difference `kFun β P u - kFun β P (u - e)` equals `kFun β' P u`. Hence the function `F`
sending `u` to `dim (piece u) - kFun β P u` satisfies `F u = F (u - e)` for every `u`; iterating
gives `F u = F (u - n • e)`, and for `n` large the `i`-th coordinate of `u - n • e` is negative, so
`F` vanishes by `IsGrading.eq_bot_of_neg` and `kFun_eq_zero_of_neg`. Note `β i ≥ 1` because `x ∈ V`. -/
theorem hilb_serre_poly (N : ℕ) (V : Finset (Fin (N + 1) × Fin 2))
    (M : Type*) [AddCommGroup M] [Module ℂ M] [Module (MR N) M] [IsScalarTower ℂ (MR N) M]
    (piece : (Fin (N + 1) →₀ ℤ) → Submodule ℂ M) (hg : IsGrading N piece)
    (hfin : Module.Finite (MR N) M) (hfd : ∀ u, Module.Finite ℂ ↥(piece u))
    (hV : ∀ v ∉ V, ∀ m : M, (MvPolynomial.X v : MR N) • m = 0) :
    ∃ P : MvPolynomial (Fin (N + 1)) ℚ,
      ∀ u, (Module.finrank ℂ ↥(piece u) : ℚ) =
        kFun N (fun i => (V.filter (fun v => v.1 = i)).card) P u :=
  hilb_serre_step N
    (fun _ _ _ _ _ piece hg hfin hfd h => hilb_serre_empty piece hg hfin hfd h)
    (fun _ _ _ _ _ piece x hg => isGrading_quoPiece piece x hg)
    (fun _ _ _ _ _ piece x hg => isGrading_kerPiece piece x hg)
    (fun _ _ _ _ _ piece x hg hfd u => finrank_relation piece x hg hfd u)
    V M piece hg hfin hfd hV

end Work.BW
