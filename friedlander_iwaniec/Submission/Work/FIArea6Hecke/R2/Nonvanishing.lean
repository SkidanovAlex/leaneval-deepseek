/-
# `Work.FIArea6Hecke.R2.Nonvanishing`

Non-vanishing of the reduced Gauss sum `Gs M chi S 1` for a primitive character `chi` mod `M` with
a nontrivial value on the units.  It is the Parseval identity (`Gs_parseval`) combined with the
duality `Gs a = star (chi a) * Gs 1` on the units (`GsUnitK`) and the vanishing off the units
(`GsNonunitK`):

  `|U| · Gs 1 · conj (Gs 1) = |U| · S.card`,  `U = {a ∈ S : a a unit mod M}`,

so `Gs 1 ≠ 0` because `|U| ≠ 0` (the class of `1` is a unit) and `S ≠ ∅`.  No knowledge of
`S.card` is required.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R2.Defs
import Submission.Work.FIArea6Hecke.R2.GsUnitK
import Submission.Work.FIArea6Hecke.R2.GsNonunitK
import Submission.Work.FIArea6Hecke.R2.GsParseval
import Submission.Work.FIArea6Hecke.CGD.CrsCalculus
import Submission.Work.FIArea6Hecke.CGD.ChiUnits

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6Hecke.R2

open scoped BigOperators
open Work.FIArea6Hecke.R

noncomputable section

/-- `1` is a unit modulo `M`. -/
lemma isUnitMod_one (M : GaussianInt) : IsUnitMod M 1 := ⟨1, by rw [one_mul, sub_self]; exact dvd_zero M⟩

/-- A complete residue system mod `M` is non-empty. -/
lemma card_crs_pos {M : GaussianInt} {S : Finset GaussianInt} (hS : IsCRS M S) : 0 < S.card :=
  Finset.card_pos.mpr ⟨Work.FIArea6Hecke.CGD.crsRep M S hS 0,
    Work.FIArea6Hecke.CGD.crsRep_mem M S hS 0⟩

/-- **Non-vanishing** of the Gauss sum at the trivial frequency. -/
theorem Gs_one_ne_zero (M : GaussianInt) (hM : M ≠ 0) (hg : 2 ≤ Work.FIPlan.gnorm M)
    (S : Finset GaussianInt) (hS : IsCRS M S)
    (chi : GaussianInt → ℂ) (hchi : IsCharModStrict M chi)
    (hprim : IsPrimitiveCharAt M chi)
    (hnt : ∃ z : GaussianInt, IsUnitMod M z ∧ chi z ≠ 1) :
    Gs M chi S 1 ≠ 0 := by
  classical
  set U : Finset GaussianInt := S.filter (fun a => IsUnitMod M a) with hU
  have hUpos : 0 < U.card := by
    refine Finset.card_pos.mpr ⟨Work.FIArea6Hecke.CGD.crsRep M S hS 1, ?_⟩
    rw [hU, Finset.mem_filter]
    refine ⟨Work.FIArea6Hecke.CGD.crsRep_mem M S hS 1, ?_⟩
    refine ⟨1, ?_⟩
    have h := Work.FIArea6Hecke.CGD.crsRep_dvd M S hS 1
    have heq : Work.FIArea6Hecke.CGD.crsRep M S hS 1 * 1 - 1
        = -(1 - Work.FIArea6Hecke.CGD.crsRep M S hS 1) := by ring
    rw [heq]
    exact dvd_neg.mpr h
  have hUc : ((U.card : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hUpos)
  have hunit : ∀ a ∈ U, Gs M chi S a * star (Gs M chi S a)
      = Gs M chi S 1 * star (Gs M chi S 1) := by
    intro a ha
    rw [hU, Finset.mem_filter] at ha
    rw [GsUnitK M hM hg S hS chi hchi a ha.2]
    have h1 : chi a * star (chi a) = 1 :=
      (Work.FIArea6Hecke.CGD.ChiUnits M hg chi hchi hnt S hS).1 a ha.2
    calc (star (chi a) * Gs M chi S 1) * star (star (chi a) * Gs M chi S 1)
        = (star (chi a) * Gs M chi S 1) * (chi a * star (Gs M chi S 1)) := by
          rw [star_mul, star_star]; ring
      _ = (chi a * star (chi a)) * (Gs M chi S 1 * star (Gs M chi S 1)) := by ring
      _ = Gs M chi S 1 * star (Gs M chi S 1) := by rw [h1, one_mul]
  have hnonunit : ∀ a ∈ S.filter (fun a => ¬ IsUnitMod M a),
      Gs M chi S a * star (Gs M chi S a) = 0 := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [GsNonunitK M hM hg S hS chi hchi hprim hnt a ha.2, zero_mul]
  have hL : ∑ a ∈ S, Gs M chi S a * star (Gs M chi S a)
      = ((U.card : ℕ) : ℂ) * (Gs M chi S 1 * star (Gs M chi S 1)) := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun a => IsUnitMod M a)
      (fun a => Gs M chi S a * star (Gs M chi S a))]
    rw [Finset.sum_congr rfl hunit, Finset.sum_eq_zero hnonunit, add_zero,
      Finset.sum_const, nsmul_eq_mul]
  have hR : ∑ s ∈ S, chi s * star (chi s) = ((U.card : ℕ) : ℂ) := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun a => IsUnitMod M a)
      (fun s => chi s * star (chi s))]
    have h1 : ∑ s ∈ S.filter (fun a => IsUnitMod M a), chi s * star (chi s)
        = ((U.card : ℕ) : ℂ) := by
      rw [Finset.sum_congr rfl (fun a ha =>
          (Work.FIArea6Hecke.CGD.ChiUnits M hg chi hchi hnt S hS).1 a
            (Finset.mem_filter.mp ha).2)]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have h2 : ∑ s ∈ S.filter (fun a => ¬ IsUnitMod M a), chi s * star (chi s) = 0 := by
      refine Finset.sum_eq_zero (fun a ha => ?_)
      rw [Finset.mem_filter] at ha
      rw [hchi.2.2.2.2 a ha.2, star_zero, mul_zero]
    rw [h1, h2, add_zero]
  have hp := Gs_parseval M hM S hS chi hchi
  rw [hL, hR] at hp
  have hkey : Gs M chi S 1 * star (Gs M chi S 1) = ((S.card : ℕ) : ℂ) := by
    refine mul_left_cancel₀ hUc ?_
    rw [hp, mul_comm]
  intro hzero
  rw [hzero, zero_mul] at hkey
  have hSc : ((S.card : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp (card_crs_pos hS))
  exact hSc hkey.symm

end

end Work.FIArea6Hecke.R2
