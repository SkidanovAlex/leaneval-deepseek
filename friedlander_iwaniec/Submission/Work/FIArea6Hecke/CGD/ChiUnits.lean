import Mathlib
import Submission.Work.FIArea6Hecke.ConductorGaussSumDefs
import Submission.Work.FIArea6Hecke.CGD.CrsCalculus

namespace Work.FIArea6Hecke.CGD

open scoped BigOperators
open Work.FIArea6Hecke.R

noncomputable section

/-- The Gaussian norm `gnorm` is multiplicative. -/
lemma gnorm_mul_cgd (z w : GaussianInt) :
    Work.FIPlan.gnorm (z * w) = Work.FIPlan.gnorm z * Work.FIPlan.gnorm w := by
  unfold Work.FIPlan.gnorm
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]

/-- `gnorm 1 = 1`. -/
lemma gnorm_one_cgd : Work.FIPlan.gnorm (1 : GaussianInt) = 1 := by
  unfold Work.FIPlan.gnorm
  rw [Zsqrtd.norm_one]; rfl

/-- A unit modulo `M` of modulus `≥ 2` is nonzero (so that multiplication by it is
injective on `ℤ[i]`). -/
lemma unit_ne_zero_of_IsUnitMod (M v : GaussianInt) (hg : 2 ≤ Work.FIPlan.gnorm M)
    (hv : IsUnitMod M v) : v ≠ 0 := by
  intro hv0
  obtain ⟨w, hw⟩ := hv
  have hM1 : M ∣ 1 := by
    rw [hv0, zero_mul, zero_sub] at hw
    exact dvd_neg.mp hw
  obtain ⟨k, hk⟩ := hM1
  have hgn : 1 = Work.FIPlan.gnorm M * Work.FIPlan.gnorm k := by
    have h := congrArg Work.FIPlan.gnorm hk
    rwa [gnorm_mul_cgd, gnorm_one_cgd] at h
  have hk0 : Work.FIPlan.gnorm k ≠ 0 := by
    intro h; rw [h, mul_zero] at hgn; exact one_ne_zero hgn
  have hk1 : 1 ≤ Work.FIPlan.gnorm k := Nat.one_le_iff_ne_zero.mpr hk0
  nlinarith [hg, hk1]

/-- A multiplicative character of `(ℤ[i]/M)^*` with `‖χ‖ ≤ 1` takes values of modulus `1` on
the units modulo `M`. -/
lemma chi_unit_mul_star (M : GaussianInt) (chi : GaussianInt → ℂ)
    (hchi : IsCharModStrict M chi) (u : GaussianInt) (hu : IsUnitMod M u) :
    chi u * star (chi u) = 1 := by
  obtain ⟨h1, hmul, hbound, hper, hsupp⟩ := hchi
  obtain ⟨w, hw⟩ := hu
  have huw : chi (u * w) = 1 := by rw [hper (u*w) 1 hw, h1]
  have hmul' : chi u * chi w = 1 := by rw [← hmul u w, huw]
  have hnorm : ‖chi u‖ = 1 := by
    have hkey : ‖chi u‖ * ‖chi w‖ = 1 := by rw [← norm_mul, hmul', norm_one]
    have hu1 := hbound u
    have hw1 := hbound w
    have hu0 := norm_nonneg (chi u)
    have hw0 := norm_nonneg (chi w)
    nlinarith
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
  norm_num

/-- Vanishing of the sum of a nontrivial multiplicative character over a complete residue
system: `χ` is `M`-periodic and multiplicative, so a unit `v` with `χ v ≠ 1` permutes the CRS
and yields `∑_{s ∈ S} χ s = χ v · ∑_{s ∈ S} χ s`. -/
lemma sum_crs_eq_zero (M : GaussianInt) (hg : 2 ≤ Work.FIPlan.gnorm M)
    (chi : GaussianInt → ℂ) (hchi : IsCharModStrict M chi)
    (hnt : ∃ z : GaussianInt, IsUnitMod M z ∧ chi z ≠ 1)
    (S : Finset GaussianInt) (hS : IsCRS M S) :
    Finset.sum S chi = 0 := by
  obtain ⟨h1, hmul, hbound, hper, hsupp⟩ := hchi
  obtain ⟨v, hv_unit, hv_ne1⟩ := hnt
  have hv0 : v ≠ 0 := unit_ne_zero_of_IsUnitMod M v hg hv_unit
  have hT_CRS : IsCRS M (S.image (fun s => s * v)) :=
    (CrsCalculus M S S hS hS chi hper).2.2.1 v hv_unit hv0
  have h_eq : Finset.sum S chi = Finset.sum (S.image (fun s => s * v)) chi :=
    (CrsCalculus M S (S.image (fun s => s * v)) hS hT_CRS chi hper).1
  have h_dil : Finset.sum (S.image (fun s => s * v)) chi =
      Finset.sum S (fun s => chi (s * v)) :=
    (CrsCalculus M S S hS hS chi hper).2.2.2.2 v hv0
  have h_mul : Finset.sum S (fun s => chi (s * v)) = (Finset.sum S chi) * chi v := by
    have hstep : Finset.sum S (fun s => chi (s * v)) =
        Finset.sum S (fun s => chi s * chi v) := by
      apply Finset.sum_congr rfl
      intro s _
      exact hmul s v
    rw [hstep, Finset.sum_mul]
  have hchain : Finset.sum S chi = (Finset.sum S chi) * chi v :=
    h_eq.trans (h_dil.trans h_mul)
  have hfac : (Finset.sum S chi) * (chi v - 1) = 0 := by
    rw [mul_sub, mul_one, ← hchain, sub_self]
  have hlast : chi v - 1 ≠ 0 := sub_ne_zero.mpr hv_ne1
  rcases mul_eq_zero.mp hfac with h | h
  · exact h
  · exact absurd h hlast

theorem ChiUnits (M : GaussianInt) (hg : 2 ≤ Work.FIPlan.gnorm M)
    (chi : GaussianInt → ℂ) (hchi : Work.FIArea6Hecke.R.IsCharModStrict M chi)
    (hnt : ∃ z : GaussianInt, Work.FIArea6Hecke.R.IsUnitMod M z ∧ chi z ≠ 1)
    (S : Finset GaussianInt) (hS : Work.FIArea6Hecke.R.IsCRS M S) :
    (∀ u : GaussianInt, Work.FIArea6Hecke.R.IsUnitMod M u → chi u * star (chi u) = 1) ∧
    (Finset.sum S chi = 0) :=
  ⟨fun u hu => chi_unit_mul_star M chi hchi u hu,
   sum_crs_eq_zero M hg chi hchi hnt S hS⟩

end

end Work.FIArea6Hecke.CGD
