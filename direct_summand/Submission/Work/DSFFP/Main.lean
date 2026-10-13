/-
# DSFFP Main: `DSMap.Mix2.ff_mod_pow_proved`

Subproject DSFFP (curric-46 lead) for the LeanEval problem `direct_summand`: the FFP node of
`Submission/Work/DSMap/Mix2.lean` ("faithful flatness mod `p` ⟹ mod `pᵐ`", needed for the
descent step of the mixed-characteristic route).

The theorem below has the same statement as the frozen `DSMap.Mix2.ff_mod_pow`; the frozen node
is a `sorry`, this one is proved (no `sorry`, no new axiom).

The mathematics is the classical local flatness criterion for a nilpotent ideal (Stacks 10.99.8,
tag `051C`), proved elementarily in this directory:

* `Work.DSFFP.tpure_of_coker_quot` — base case of Step A (`Tor₁ˢ(S/I, T) = 0` from `h1`),
* `Work.DSFFP.tpure_of_flat_quot_top` — `Tor₁ˢ(N, T) = 0` for `S ⧸ I`-modules `N` (from `h2`),
* `Work.DSFFP.tpure_of_iSup` — filtered-union lemma,
* `Work.DSFFP.tpure_of_smul_top_le` — Step A: `Tor₁ˢ(N, T) = 0` for all `N` killed by `I`,
* `Work.DSFFP.flat_of_flat_mod_nilpotent` — the criterion: `I ^ n = ⊥` ⟹ `T` is `S`-flat,
* `Work.DSFFP.idxInj_quot_pow`, `Work.DSFFP.flat_quot_quot_pow`,
  `Work.DSFFP.smul_top_eq_top_imp_eq_top` — the three inputs in the FFP situation.
-/
import Submission.Work.DSMap.Mix2
import Submission.Work.DSFFP.Defs
import Submission.Work.DSFFP.idxInj_quot_pow
import Submission.Work.DSFFP.flat_quot_quot_pow
import Submission.Work.DSFFP.smul_top_eq_top_imp_eq_top
import Submission.Work.DSFFP.flat_of_flat_mod_nilpotent

open TensorProduct

universe a b c

namespace DSMap.Mix2

/-- **FFP, proved**: faithful flatness modulo `p` implies faithful flatness modulo `p ^ m`, for
`p` a non-zero-divisor on both sides.  Same statement as the frozen `DSMap.Mix2.ff_mod_pow`. -/
theorem ff_mod_pow_proved (p : ℕ) {D D' : Type a} [CommRing D] [CommRing D'] [Algebra D D']
    (hD : IsSMulRegular D (p : D)) (hD' : IsSMulRegular D' (p : D'))
    (h : Module.FaithfullyFlat (D ⧸ Ideal.span {(p : D)})
      (D' ⧸ (Ideal.span {(p : D)}).map (algebraMap D D'))) (m : ℕ) :
    Module.FaithfullyFlat (D ⧸ Ideal.span {(p : D) ^ m})
      (D' ⧸ (Ideal.span {(p : D) ^ m}).map (algebraMap D D')) := by
  have hI : (Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : D) ^ m}) (p : D)}) ^ m = ⊥ := by
    rw [Ideal.span_singleton_pow, ← map_pow]
    exact Ideal.span_singleton_eq_bot.mpr
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _))
  have hflat : Module.Flat (D ⧸ Ideal.span {(p : D) ^ m})
      (D' ⧸ (Ideal.span {(p : D) ^ m}).map (algebraMap D D')) :=
    Work.DSFFP.flat_of_flat_mod_nilpotent _ _ m hI
      (Work.DSFFP.idxInj_quot_pow p hD hD' m) (Work.DSFFP.flat_quot_quot_pow p h m)
  refine (Module.FaithfullyFlat.iff_flat_and_proper_ideal (D ⧸ Ideal.span {(p : D) ^ m})
    (D' ⧸ (Ideal.span {(p : D) ^ m}).map (algebraMap D D'))).mpr
    ⟨hflat, fun J hJ hJtop => hJ ?_⟩
  exact Work.DSFFP.smul_top_eq_top_imp_eq_top p h m hJtop

end DSMap.Mix2

namespace Work.DSFFP

/-- `Work.DSFFP` alias of `DSMap.Mix2.ff_mod_pow_proved` (same statement). -/
theorem ff_mod_pow_proved (p : ℕ) {D D' : Type a} [CommRing D] [CommRing D'] [Algebra D D']
    (hD : IsSMulRegular D (p : D)) (hD' : IsSMulRegular D' (p : D'))
    (h : Module.FaithfullyFlat (D ⧸ Ideal.span {(p : D)})
      (D' ⧸ (Ideal.span {(p : D)}).map (algebraMap D D'))) (m : ℕ) :
    Module.FaithfullyFlat (D ⧸ Ideal.span {(p : D) ^ m})
      (D' ⧸ (Ideal.span {(p : D) ^ m}).map (algebraMap D D')) :=
  DSMap.Mix2.ff_mod_pow_proved p hD hD' h m

end Work.DSFFP

/-! ## Sanity check: the deliverable has exactly the frozen statement -/

/-- The frozen statement `DSMap.Mix2.ff_mod_pow` (see `Submission/Work/DSMap/Mix2.lean`),
discharged by `ff_mod_pow_proved`. -/
example (p : ℕ) {D D' : Type a} [CommRing D] [CommRing D'] [Algebra D D']
    (hD : IsSMulRegular D (p : D)) (hD' : IsSMulRegular D' (p : D'))
    (h : Module.FaithfullyFlat (D ⧸ Ideal.span {(p : D)})
      (D' ⧸ (Ideal.span {(p : D)}).map (algebraMap D D'))) (m : ℕ) :
    Module.FaithfullyFlat (D ⧸ Ideal.span {(p : D) ^ m})
      (D' ⧸ (Ideal.span {(p : D) ^ m}).map (algebraMap D D')) :=
  DSMap.Mix2.ff_mod_pow_proved p hD hD' h m
