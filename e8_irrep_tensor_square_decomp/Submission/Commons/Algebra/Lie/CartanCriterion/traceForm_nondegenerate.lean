import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

attribute [local instance 100] LieRing.ofAssociativeRing

set_option linter.style.haveILetI false

namespace Commons.Algebra.Lie.CartanCriterion

open LieModule

/-- **Engel's theorem**, nilpotent-operator form: a Lie subalgebra of `End K M` all of whose
elements are nilpotent endomorphisms is a nilpotent Lie algebra. -/
private lemma engel_nilpotent_of_isNilpotent {K M : Type*} [Field K] [AddCommGroup M]
    [Module K M] [Module.Finite K M] (𝔞 : LieSubalgebra K (Module.End K M))
    (h : ∀ x : 𝔞, IsNilpotent (x : Module.End K M)) : LieRing.IsNilpotent 𝔞 := by
  rw [LieAlgebra.isNilpotent_iff_forall (R := K)]
  intro x
  exact LieAlgebra.isNilpotent_ad_of_isNilpotent (h x)

/-- **Cartan's criterion for solvability**, representation-theoretic form: if a finite-dimensional
faithful representation `M` of a Lie algebra `L` over a field of characteristic zero has vanishing
trace form, then `L` is solvable.

This is the general form of `LieAlgebra.isSolvable_of_killingForm_apply_lie_eq_zero`; the proof
combines `LieModule.isNilpotent_derivedSeries_of_traceForm_eq_zero` (the hard analytic part, using
Jordan–Chevalley) with Engel's theorem applied to the image of `⁅L, L⁆` in `End M`. -/
private theorem isSolvable_of_traceForm_eq_zero {K L M : Type*} [Field K] [CharZero K]
    [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M] [LieRingModule L M]
    [LieModule K L M] [Module.Finite K M] [LieModule.IsFaithful K L M]
    (h : LieModule.traceForm K L M = 0) : LieAlgebra.IsSolvable L := by
  set H : LieIdeal K L := LieAlgebra.derivedSeries K L 1 with hH
  haveI : LieModule.IsFaithful K H M :=
    inferInstanceAs (LieModule.IsFaithful K (H : LieSubalgebra K L) M)
  have hM : LieModule.IsNilpotent H M := by
    rw [hH]; exact LieModule.isNilpotent_derivedSeries_of_traceForm_eq_zero h
  have hmin : ∀ x : H, IsNilpotent (LieModule.toEnd K H M x) :=
    (LieModule.isNilpotent_iff_forall' (R := K) (L := H) (M := M)).mp hM
  set 𝔞 : LieSubalgebra K (Module.End K M) := (LieModule.toEnd K H M).range with h𝔞
  have ha : ∀ y : 𝔞, IsNilpotent (y : Module.End K M) := by
    rintro ⟨y, hy⟩
    rw [h𝔞] at hy
    obtain ⟨x, rfl⟩ := hy
    simpa using hmin x
  have h𝔞n : LieRing.IsNilpotent 𝔞 := engel_nilpotent_of_isNilpotent 𝔞 ha
  have hinj : Function.Injective (LieModule.toEnd K H M) := IsFaithful.injective_toEnd
  have hHn : LieRing.IsNilpotent H :=
    (LieEquiv.ofInjective (LieModule.toEnd K H M) hinj).nilpotent_iff_equiv_nilpotent.mpr h𝔞n
  have hHs : LieAlgebra.IsSolvable H := by
    haveI : LieModule.IsNilpotent H H := hHn
    exact LieAlgebra.isSolvable_of_isNilpotent H
  obtain ⟨k, hk⟩ := hHs.solvable (R := K)
  rw [LieIdeal.derivedSeries_eq_bot_iff] at hk
  refine LieAlgebra.IsSolvable.mk (R := K) (k := k + 1) ?_
  rw [LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_add]
  rw [show LieAlgebra.derivedSeriesOfIdeal K L 1 ⊤ = H from by
    rw [hH, LieAlgebra.derivedSeries_def]]
  exact hk

/-- If `L` is a Lie algebra with trivial solvable radical and `M` a finite-dimensional faithful
`L`-module, then the trace form of `M` on `L` is non-degenerate.

Indeed, the radical `r` of the trace form is an ideal on which the form vanishes identically; by
Cartan's criterion the restriction of `M` to `r` then forces `r` to be solvable, so `r = 0` by
triviality of the radical. -/
theorem traceForm_nondegenerate {K L M : Type*} [Field K] [CharZero K]
    [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M] [LieRingModule L M]
    [LieModule K L M] [Module.Finite K M] [LieModule.IsFaithful K L M]
    [LieAlgebra.HasTrivialRadical K L] :
    (LieModule.traceForm K L M).Nondegenerate := by
  set r : LieIdeal K L :=
    LieAlgebra.InvariantForm.orthogonal (LieModule.traceForm K L M)
      (LieModule.traceForm_lieInvariant K L M) ⊤ with hr
  have mem_r : ∀ y : L, y ∈ r ↔ ∀ x : L, LieModule.traceForm K L M x y = 0 := by
    intro y
    rw [hr, LieAlgebra.InvariantForm.mem_orthogonal]
    simp
  have hsol : LieAlgebra.IsSolvable r := by
    haveI : LieModule.IsFaithful K r M :=
      inferInstanceAs (LieModule.IsFaithful K (r : LieSubalgebra K L) M)
    refine isSolvable_of_traceForm_eq_zero (K := K) (L := r) (M := M) ?_
    ext x y
    have h0 : LieModule.traceForm K L M (↑x : L) (↑y : L) = 0 :=
      (mem_r ↑y).mp y.2 ↑x
    rw [show (LieModule.traceForm K (↥r) M) x y
        = LieModule.traceForm K L M (↑x : L) (↑y : L) from
      LieModule.traceForm_lieSubalgebra_mk_left K L M (r : LieSubalgebra K L) x.2 y]
    exact h0
  have hrbot : r = ⊥ := by
    haveI : LieAlgebra.IsSolvable r := hsol
    exact LieAlgebra.HasTrivialRadical.eq_bot_of_isSolvable r
  have hker : LinearMap.ker (LieModule.traceForm K L M) = ⊥ := by
    have h1 : LinearMap.ker (LieModule.traceForm K L M) = r.toSubmodule := by
      ext x
      rw [LinearMap.mem_ker, LieSubmodule.mem_toSubmodule, mem_r]
      constructor
      · intro hx z
        rw [LieModule.traceForm_comm]
        exact LinearMap.congr_fun hx z
      · intro hx
        ext z
        rw [LieModule.traceForm_comm]
        exact hx z
    rw [h1, hrbot]
    rfl
  refine (LieModule.traceForm_isSymm K L M).isRefl.nondegenerate_iff_separatingLeft.mpr ?_
  rw [LinearMap.separatingLeft_iff_ker_eq_bot]
  exact hker

end Commons.Algebra.Lie.CartanCriterion