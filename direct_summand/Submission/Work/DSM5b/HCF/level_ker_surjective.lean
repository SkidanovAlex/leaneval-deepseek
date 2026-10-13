import Mathlib
import Submission.Work.DSM5b.HCF.Complex
import Submission.Work.DSM5b.HCF.surj_cohomology
import Submission.Work.DSM5b.HCF.LksAux
import Submission.Work.DSM5b.HCF.gExtend_block_eq
import Submission.Work.DSM5b.HCF.gsurjD_signSection
import Submission.Work.DSM5b.HCF.htcD_eq_zero_of_blockwise
import Submission.Work.DSM5b.HCF.gExtend_apply_incrTup

namespace Work.DSM5b.HCF

universe u

open Classical Finset

variable {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι] [LinearOrder ι]

/-- **Surjectivity of the comparison map on the top-degree cocycles of the size-`k` graded piece.**
Let `ℰ = Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k` (supported on the subsets of size exactly `k`).
Every cochain `y : Stc ℰ (k-1)` on the increasing tuples of length `k` is the restriction
`Work.DSM5b.toStc ℰ (k-1) z` of some cocycle `z : Htc ℰ (k-1)` (`htcD z = 0`).

Route: an increasing tuple of length `k` is the increasing enumeration of its range `S₀`
(`card S₀ = k`).  The second conjunct of `Work.DSM5b.HCF.surj_cohomology` (proved for
`S₀ : Finset (Fin n)`; you need it for `S₀ : Finset ι` with `[LinearOrder ι]`, e.g. by reindexing
along `S₀.orderIsoOfFin` to `Finset.univ : Finset (Fin k)`, or by transcribing the proof) gives, on
the block of tuples with range `S₀`, a cocycle with prescribed value `y` at the increasing
enumeration, namely `τ ↦ signOfR τ • y(S₀)`; assemble these blockwise into a single cochain
`z : Htc ℰ (k-1)` (tuples whose range has size `≠ k` get value `0`, the coefficient module there
being a subsingleton), check `htcD z = 0` blockwise, and note `signOfR = 1` at the increasing
enumeration (`Work.DSM5b.HCF.signOfR_incTupleE`).

Do NOT use `sorry` and do NOT use any frozen `DSMap`/`area_*` declaration. -/
theorem level_ker_surjective {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι] [LinearOrder ι]
    (𝒜 : Work.DSM5b.CoeffSys R ι) (k : ℕ) :
    Function.Surjective (fun z : ↥(LinearMap.ker (Work.DSM5b.CoeffSys.htcD (𝒜 := Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k) (k - 1))) =>
      Work.DSM5b.toStc (Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k) (k - 1) z.1) := by
  intro y
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `k = 0`: the coefficient system is supported on the empty set, so both complexes vanish
    -- in degree `0 - 1 = 0` (every tuple of length `1` has a non-empty range).
    subst hk0
    have hsub : ∀ τ : Work.DSM5b.IncrTuple (ι := ι) (0 - 1),
        Subsingleton ((Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 0).M (Work.DSM5b.tupRng τ.1)) :=
      fun τ => Work.DSM5b.HCF.subsingleton_coeff_exactlyCoeff 𝒜 0 (by
        have hpos := Finset.card_pos.mpr (Work.DSM5b.tupRng_nonempty τ.1)
        omega)
    haveI : Subsingleton (Work.DSM5b.Stc (Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 0) (0 - 1)) :=
      ⟨fun a b => funext (fun τ => @Subsingleton.elim _ (hsub τ) (a τ) (b τ))⟩
    exact ⟨⟨0, by simp⟩, Subsingleton.elim _ _⟩
  · -- `k ≥ 1`: extend the sorted cochain by the sign section on every `k`-element block.
    have hk : (k - 1) + 1 = k := by omega
    refine ⟨⟨Work.DSM5b.HCF.gExtend 𝒜 k (k - 1) hk y, ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker]
      exact Work.DSM5b.HCF.htcD_eq_zero_of_blockwise 𝒜 k (k - 1) hk _ (fun S₀ hS => by
        rw [Work.DSM5b.HCF.gExtend_block_eq 𝒜 k (k - 1) hk y S₀ hS]
        exact Work.DSM5b.HCF.gsurjD_signSection (k - 1) (hk.trans hS.symm) _)
    · funext τ₀
      exact Work.DSM5b.HCF.gExtend_apply_incrTup 𝒜 k (k - 1) hk y τ₀

end Work.DSM5b.HCF
