import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.thm32
import Submission.Work.BG.lemma24
import Submission.Work.BG.centralIntegral
import Submission.Work.BG.glaubValue
import Submission.Work.BG.lemma18LinearIndependent
import Submission.Work.BG.rem31Orth
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.lemma33ShapeA
import Submission.Work.BG.l34ExcNeFourAux
import Submission.Work.BG.l34ne_glauberman_contra
import Submission.Work.BG.l34ne_chi_even
import Submission.Work.BG.l34ne_cong_alpha
import Submission.Work.BG.l34ne_exists_fixing_action
import Submission.Work.BG.l34ne_restrict_shape
import Submission.Work.BG.l34ne_orbit_deg_dvd
import Submission.Work.BG.l34ne_orbit_fiber_card
import Submission.Work.BG.s02_sum_irr_eq_finsum_bset
import Submission.Work.BG.inner_pmIrr_eq_pm_one
import Submission.Work.BG.congContra
import Submission.Work.BG.s02_lemma21
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.CharBridge
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.modTwoIndep
import Submission.Work.BG.hatInjCore
import Submission.Work.BG.glaubCorrDistinct
import Submission.OddOrder.GroupTheory.RepresentationTheory.ZIrr
import Submission.OddOrder.GroupTheory.RepresentationTheory.InducedCharacter

namespace Work.BG

-- NOTE (area BG hygiene): `L34Irr` and `l34ne_inner_restrict_eq_inner_ind` are also declared
-- in `BG/l34ne_deg_mod_four.lean`, which made the two modules (and hence `BG/c3NotThree`,
-- which imports this one) impossible to co-import.  The copies here were renamed.


open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- Shorthand: the irreducible characters of the subgroup `H₀ = C.P.H0`. -/
abbrev L34IrrC {G : Type} [Group G] [Finite G] (C : Sec2Ctx G) : Type _ :=
  IrreducibleCharacter ↥C.P.H0

/-- Frobenius reciprocity in the direction `(Res^G_H χ, θ)_H = (χ, Ind^G_H θ)_G`. -/
theorem c3enc_inner_restrict {H : Subgroup G} [Fintype ↥H]
    [Invertible (Nat.card ↥H : ℂ)] (χ : ClassFunction G ℂ) (θ : ClassFunction ↥H ℂ) :
    ClassFunction.inner (ClassFunction.restrict H χ) θ =
      ClassFunction.inner χ (ClassFunction.induce H θ) := by
  rw [ClassFunction.inner_star_comm, ← ClassFunction.inner_induce_eq_inner_restrict H θ χ,
    ClassFunction.inner_star_comm, star_star]

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem c3enc_deg_crux {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Compat D C → Work.GW2.C16.Sec3Hyp D →
    ∀ f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ, Work.GW2.C16.IsCoherent C f →
    ∀ χ : ClassFunction G ℂ, Work.BG.IsPmIrr χ →
    ∀ ν ∈ Work.GW2.C16.bset C f χ, Work.BG.sconj C ν ≠ ν →
      (Work.BG.sconj C ν ∉ Work.BG.lamOrbit C ν ∨ (Work.BG.lamOrbit C ν).ncard = D.n) →
      (Work.BG.lamOrbit C ν).ncard = 4 →
      Work.BG.sconj C '' Work.BG.lamOrbit C ν = Work.BG.lamOrbit C ν →
      D.n = 4 →
      ∀ ξ ∈ Work.GW2.C16.bset C f χ, ξ ≠ ν → ξ ≠ Work.BG.sconj C ν →
        Work.BG.sconj C ξ = ξ → (Work.BG.lamOrbit C ξ).ncard ≠ 4 →
        Work.GW2.C16.bset C f χ = {ν, Work.BG.sconj C ν, ξ} →
        (∃ m : ℤ, ξ 1 = (2 : ℂ) * (m : ℂ) ∧ Odd m) →
        ∃ k : ℤ, χ 1 = (4 : ℂ) * (k : ℂ) := by
  intro hDC hS3 f hf χ hχ ν hν hne hdisj h4 hstab hn4 ξ hξ hξν hξνs hξs hξ4 hbset hξodd
  classical
  haveI hFintypeH0 : Fintype ↥C.P.H0 := Fintype.ofFinite _
  obtain ⟨hνirr, hνne0⟩ := hν
  obtain ⟨hξirr, hξne0⟩ := hξ
  -- ## basic coherence facts
  have hstruct := bset_orbit_struct C f hf χ hχ
  have hsνmem : sconj C ν ∈ bset C f χ := (hstruct.1 ν ⟨hνirr, hνne0⟩).1
  have hscirr : IsIrreducibleCharacter (sconj C ν) := hsνmem.1
  have hνfix : f (sconj C ν) = f ν := (hstruct.1 ν ⟨hνirr, hνne0⟩).2.1
  have hcoefν : ClassFunction.inner χ (f ν) = 1 ∨ ClassFunction.inner χ (f ν) = -1 :=
    (hstruct.1 ν ⟨hνirr, hνne0⟩).2.2
  have hcoefξ : ClassFunction.inner χ (f ξ) = 1 ∨ ClassFunction.inner χ (f ξ) = -1 :=
    (hstruct.1 ξ ⟨hξirr, hξne0⟩).2.2
  -- ## `ν 1` is an odd integer
  obtain ⟨dν, hdνodd, hdνeq⟩ := l34ne_orbit_deg_dvd D C hDC hS3 ν hνirr
  have hν1 : ν 1 = (dν : ℂ) := by
    have h : ((4 : ℕ) : ℂ) * ν 1 = ((4 : ℕ) : ℂ) * (dν : ℂ) := by
      have hh := hdνeq
      rw [h4, hn4] at hh
      exact hh
    exact mul_left_cancel₀ (by norm_num) h
  -- ## `(ν^s) 1 = ν 1`
  have hsconj1 : (sconj C ν) 1 = ν 1 := by
    show (conjByH C.P C.s ν) (1 : ↥C.P.H0) = ν 1
    rw [conjByH_apply]
    exact congrArg ν (map_one (conjMulEquiv C.P C.s))
  -- ## the Fourier expansion of `χ` on `H₀`
  let a : L34IrrC C → ℂ := fun r =>
    ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) (r : ClassFunction ↥C.P.H0 ℂ)
  have hFourier : ClassFunction.restrict C.P.H0 χ =
      ∑ r : L34IrrC C, a r • (r : ClassFunction ↥C.P.H0 ℂ) :=
    (sum_inner_irreducibleCharacter_smul (ClassFunction.restrict C.P.H0 χ)).symm
  have h1 : χ 1 = ∑ r : L34IrrC C, a r * ((r : ClassFunction ↥C.P.H0 ℂ) 1) := by
    have h := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => φ (1 : ↥C.P.H0)) hFourier
    rw [ClassFunction.restrict_apply] at h
    rw [ClassFunction.sum_apply] at h
    simp only [ClassFunction.smul_apply] at h
    simpa using h
  -- ## the finsum over `𝒮(χ)` equals the sum over all irreducibles
  have h2 : (∑ r : L34IrrC C, ClassFunction.inner χ (f (r : ClassFunction ↥C.P.H0 ℂ)) *
        ((r : ClassFunction ↥C.P.H0 ℂ) 1))
      = ∑ᶠ ν' ∈ bset C f χ, ClassFunction.inner χ (f ν') * ν' 1 := by
    refine s02_sum_irr_eq_finsum_bset C f χ
      (fun ξ' => ClassFunction.inner χ (f ξ') * ξ' 1) ?_
    intro r hr
    have h0 : ClassFunction.inner χ (f (r : ClassFunction ↥C.P.H0 ℂ)) = 0 := by
      by_contra hc
      exact hr ⟨r.2, hc⟩
    rw [h0, zero_mul]
  -- ## the key identity: `a r - a (ρ r) = (χ, f r) - (χ, f (ρ r))`
  have hkey : ∀ r : L34IrrC C,
      a (orbitRep C r) - ClassFunction.inner χ (f (orbitRep C r : ClassFunction ↥C.P.H0 ℂ))
        = a r - ClassFunction.inner χ (f (r : ClassFunction ↥C.P.H0 ℂ)) := by
    intro r
    have hG := (hf.1 (r : ClassFunction ↥C.P.H0 ℂ) r.2)
      (r : ClassFunction ↥C.P.H0 ℂ) (Or.inl (s02c_LamEquiv_refl C _))
      (orbitRep C r : ClassFunction ↥C.P.H0 ℂ) (Or.inl (orbitRep_mem C r)) r.2 (orbitRep C r).2
    have hind : ClassFunction.induce C.P.H0
          ((r : ClassFunction ↥C.P.H0 ℂ) - (orbitRep C r : ClassFunction ↥C.P.H0 ℂ))
        = f (r : ClassFunction ↥C.P.H0 ℂ) - f (orbitRep C r : ClassFunction ↥C.P.H0 ℂ) :=
      hG.2.2.2.1 (orbitRep_mem C r)
    have hfr := c3enc_inner_restrict (H := C.P.H0) χ
      ((r : ClassFunction ↥C.P.H0 ℂ) - (orbitRep C r : ClassFunction ↥C.P.H0 ℂ))
    rw [ClassFunction.inner_sub_right] at hfr
    rw [hind, ClassFunction.inner_sub_right] at hfr
    simp only [a]
    linear_combination -hfr
  -- ## the "correction" sum
  let g : L34IrrC C → ℂ := fun r =>
    (a r - ClassFunction.inner χ (f (r : ClassFunction ↥C.P.H0 ℂ))) *
      ((r : ClassFunction ↥C.P.H0 ℂ) 1)
  have hgeval : ∀ r : L34IrrC C, g (orbitRep C r)
      = (a r - ClassFunction.inner χ (f (r : ClassFunction ↥C.P.H0 ℂ))) *
        ((r : ClassFunction ↥C.P.H0 ℂ) 1) := by
    intro r
    have hdeg : (orbitRep C r : ClassFunction ↥C.P.H0 ℂ) 1
        = (r : ClassFunction ↥C.P.H0 ℂ) 1 := by
      obtain ⟨β, hβ⟩ := orbitRep_mem C r
      have hlam1 : (lamCF C β) (1 : ↥C.P.H0) = 1 :=
        Lambda.apply_eq_one_of_mem_U (P := C.P) (δ := lamCF C β) ⟨β, rfl⟩ (Subgroup.one_mem _)
      rw [hβ, ClassFunction.mul_apply, hlam1, one_mul]
    simp only [g]
    rw [hkey r, hdeg]
  have h3 : (∑ r : L34IrrC C, g (orbitRep C r))
      = (∑ r : L34IrrC C, a r * ((r : ClassFunction ↥C.P.H0 ℂ) 1))
        - ∑ r : L34IrrC C,
            ClassFunction.inner χ (f (r : ClassFunction ↥C.P.H0 ℂ)) *
              ((r : ClassFunction ↥C.P.H0 ℂ) 1) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hgeval r]
    ring
  -- ## grouping the correction sum by orbits
  have hgrp : (∑ r : L34IrrC C, g (orbitRep C r))
      = ∑ q ∈ (Finset.univ : Finset (L34IrrC C)).image (orbitRep C),
          ((Finset.univ.filter (fun r : L34IrrC C => orbitRep C r = q)).card : ℂ) * g q := by
    have hfib := Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (L34IrrC C)))
      (t := (Finset.univ : Finset (L34IrrC C)).image (orbitRep C))
      (g := orbitRep C)
      (fun i _ => Finset.mem_image_of_mem (orbitRep C) (Finset.mem_univ i))
      (fun r => g (orbitRep C r))
    rw [← hfib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show (∑ r ∈ Finset.univ.filter (fun r : L34IrrC C => orbitRep C r = q), g (orbitRep C r))
        = ∑ _r ∈ Finset.univ.filter (fun r : L34IrrC C => orbitRep C r = q), g q from
      Finset.sum_congr rfl fun r hr => by rw [(Finset.mem_filter.mp hr).2]]
    rw [Finset.sum_const, nsmul_eq_mul]
  -- ## each grouped term is a multiple of `D.n`
  have hterm : ∀ q : L34IrrC C, ∃ c : ℤ,
      q ∈ (Finset.univ : Finset (L34IrrC C)).image (orbitRep C) →
      ((Finset.univ.filter (fun r : L34IrrC C => orbitRep C r = q)).card : ℂ) * g q
        = (D.n : ℂ) * (c : ℂ) := by
    intro q
    by_cases hq : q ∈ (Finset.univ : Finset (L34IrrC C)).image (orbitRep C)
    · obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hq
      have hqq : orbitRep C q = q := by
        rw [← hx]
        exact orbitRep_eq_of_lamEquiv (s02c_LamEquiv_symm C (orbitRep_mem C x))
      have hcard : (Finset.univ.filter (fun r : L34IrrC C => orbitRep C r = q)).card
          = (lamOrbit C (q : ClassFunction ↥C.P.H0 ℂ)).ncard :=
        (l34ne_orbit_fiber_card C q hqq).symm
      obtain ⟨aq, haqodd, haqeq⟩ := l34ne_orbit_deg_dvd D C hDC hS3
        (q : ClassFunction ↥C.P.H0 ℂ) q.2
      obtain ⟨ma, hma⟩ := ClassFunction.inner_mem_ZIrr_int
        (ClassFunction.restrict_mem_ZIrr C.P.H0 (mem_ZIrr_of_isPmIrr hχ)) q.2.mem_ZIrr
      obtain ⟨mb, hmb⟩ := ClassFunction.inner_mem_ZIrr_int (mem_ZIrr_of_isPmIrr hχ)
        ((hf.1 (q : ClassFunction ↥C.P.H0 ℂ) q.2) (q : ClassFunction ↥C.P.H0 ℂ)
          (Or.inl (s02c_LamEquiv_refl C _)) (q : ClassFunction ↥C.P.H0 ℂ)
          (Or.inl (s02c_LamEquiv_refl C _)) q.2 q.2).1
      refine ⟨(ma - mb) * aq, fun _ => ?_⟩
      have hrh : a q - ClassFunction.inner χ (f (q : ClassFunction ↥C.P.H0 ℂ))
          = ((ma - mb : ℤ) : ℂ) := by
        simp only [a, hma, hmb, Int.cast_sub]
      have hcardC : ((Finset.univ.filter (fun r : L34IrrC C => orbitRep C r = q)).card : ℂ) *
          ((q : ClassFunction ↥C.P.H0 ℂ) 1) = (D.n : ℂ) * (aq : ℂ) := by
        rw [hcard, haqeq]
      have hgoal : ((Finset.univ.filter (fun r : L34IrrC C => orbitRep C r = q)).card : ℂ) *
          ((a q - ClassFunction.inner χ (f (q : ClassFunction ↥C.P.H0 ℂ))) *
            ((q : ClassFunction ↥C.P.H0 ℂ) 1))
          = (D.n : ℂ) * (((ma - mb) * aq : ℤ) : ℂ) := by
        rw [hrh]
        calc ((Finset.univ.filter (fun r : L34IrrC C => orbitRep C r = q)).card : ℂ) *
              (((ma - mb : ℤ) : ℂ) * ((q : ClassFunction ↥C.P.H0 ℂ) 1))
            = ((ma - mb : ℤ) : ℂ) *
                (((Finset.univ.filter (fun r : L34IrrC C => orbitRep C r = q)).card : ℂ) *
                  ((q : ClassFunction ↥C.P.H0 ℂ) 1)) := by ring
          _ = ((ma - mb : ℤ) : ℂ) * ((D.n : ℂ) * (aq : ℂ)) := by rw [hcardC]
          _ = (D.n : ℂ) * (((ma - mb) * aq : ℤ) : ℂ) := by push_cast; ring
      simpa only [g] using hgoal
    · exact ⟨0, fun h => absurd h hq⟩
  choose cc hcc using hterm
  have hgroupSum : (∑ q ∈ (Finset.univ : Finset (L34IrrC C)).image (orbitRep C),
        ((Finset.univ.filter (fun r : L34IrrC C => orbitRep C r = q)).card : ℂ) * g q)
      = (D.n : ℂ) *
        ((∑ q ∈ (Finset.univ : Finset (L34IrrC C)).image (orbitRep C), cc q : ℤ) : ℂ) := by
    rw [Int.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [hcc q hq]
  -- ## the degree decomposition
  have hdecomp : ∃ K : ℤ, χ 1 =
      (∑ᶠ ν' ∈ bset C f χ, ClassFunction.inner χ (f ν') * ν' 1) + (D.n : ℂ) * (K : ℂ) := by
    refine ⟨∑ q ∈ (Finset.univ : Finset (L34IrrC C)).image (orbitRep C), cc q, ?_⟩
    have hchain : χ 1 - (∑ᶠ ν' ∈ bset C f χ, ClassFunction.inner χ (f ν') * ν' 1)
        = (D.n : ℂ) *
          ((∑ q ∈ (Finset.univ : Finset (L34IrrC C)).image (orbitRep C), cc q : ℤ) : ℂ) := by
      rw [← h2, h1, ← h3, hgrp, hgroupSum]
    linear_combination hchain
  obtain ⟨K, hK⟩ := hdecomp
  -- ## evaluating the finsum on the three-element set
  let i0 : L34IrrC C := ⟨ν, hνirr⟩
  let i1 : L34IrrC C := ⟨sconj C ν, hscirr⟩
  let i2 : L34IrrC C := ⟨ξ, hξirr⟩
  have h01 : i0 ≠ i1 := fun h => hne (congrArg Subtype.val h).symm
  have h02 : i0 ≠ i2 := fun h => hξν (congrArg Subtype.val h).symm
  have h12 : i1 ≠ i2 := fun h => hξνs (congrArg Subtype.val h).symm
  have hfin3 : (∑ᶠ ν' ∈ bset C f χ, ClassFunction.inner χ (f ν') * ν' 1)
      = ClassFunction.inner χ (f ν) * (ν 1)
        + ClassFunction.inner χ (f (sconj C ν)) * ((sconj C ν) 1)
        + ClassFunction.inner χ (f ξ) * (ξ 1) := by
    rw [← s02_sum_irr_eq_finsum_bset C f χ
      (fun ξ' => ClassFunction.inner χ (f ξ') * ξ' 1) ?_]
    · have hzz : ∀ x ∈ (Finset.univ : Finset (L34IrrC C)),
          x ∉ ({i0, i1, i2} : Finset (L34IrrC C)) →
          ClassFunction.inner χ (f (x : ClassFunction ↥C.P.H0 ℂ)) *
            (x : ClassFunction ↥C.P.H0 ℂ) 1 = 0 := by
        intro x _ hx
        have hmem : (x : ClassFunction ↥C.P.H0 ℂ) ∉ bset C f χ := by
          rw [hbset]
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          rintro (h | h | h)
          · exact hx (by
              simp only [Finset.mem_insert, Finset.mem_singleton]; left; exact Subtype.ext h)
          · exact hx (by
              simp only [Finset.mem_insert, Finset.mem_singleton]; right; left; exact Subtype.ext h)
          · exact hx (by
              simp only [Finset.mem_insert, Finset.mem_singleton]; right; right; exact Subtype.ext h)
        have h0 : ClassFunction.inner χ (f (x : ClassFunction ↥C.P.H0 ℂ)) = 0 := by
          by_contra hc
          exact hmem ⟨x.2, hc⟩
        rw [h0, zero_mul]
      rw [← Finset.sum_subset (fun x _ => Finset.mem_univ x) hzz]
      rw [Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton]
            rintro (h | h)
            exacts [h01 h, h02 h]),
          Finset.sum_insert (by
            simp only [Finset.mem_singleton]; exact h12),
          Finset.sum_singleton]
      simp only [i0, i1, i2]
      ring
    · intro r hr
      have h0 : ClassFunction.inner χ (f (r : ClassFunction ↥C.P.H0 ℂ)) = 0 := by
        by_contra hc
        exact hr ⟨r.2, hc⟩
      rw [h0, zero_mul]
  -- ## finish: parity
  rw [hfin3, hνfix, hsconj1, hν1, hn4] at hK
  obtain ⟨m, hm_eq, hm_odd⟩ := hξodd
  rw [hm_eq] at hK
  obtain ⟨b, hb⟩ := hm_odd
  obtain ⟨aa, haa⟩ := hdνodd
  rcases hcoefν with he | he <;> rcases hcoefξ with he' | he'
  · exact ⟨aa + b + 1 + K, by rw [hK, he, he', haa, hb]; push_cast; ring⟩
  · exact ⟨aa - b + K, by rw [hK, he, he', haa, hb]; push_cast; ring⟩
  · exact ⟨b - aa + K, by rw [hK, he, he', haa, hb]; push_cast; ring⟩
  · exact ⟨-(aa + b + 1) + K, by rw [hK, he, he', haa, hb]; push_cast; ring⟩

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **BG Lemma 3.4, the degree count.**  In the exceptional configuration `χ(1)` is divisible
by `4`, derived from `c3enc_deg_crux` by supplying the standing consequences `D.n = 4`,
`bset C f χ = {ν, ν^s, ξ}` and `ξ(1) = 2m` with `m` odd. -/
theorem c3enc_deg4 {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Compat D C → Work.GW2.C16.Sec3Hyp D →
    ∀ f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ, Work.GW2.C16.IsCoherent C f →
    ∀ χ : ClassFunction G ℂ, Work.BG.IsPmIrr χ →
    ∀ ν ∈ Work.GW2.C16.bset C f χ, Work.BG.sconj C ν ≠ ν →
      (Work.BG.sconj C ν ∉ Work.BG.lamOrbit C ν ∨ (Work.BG.lamOrbit C ν).ncard = D.n) →
      (Work.BG.lamOrbit C ν).ncard = 4 →
      Work.BG.sconj C '' Work.BG.lamOrbit C ν = Work.BG.lamOrbit C ν →
      ∀ ξ ∈ Work.GW2.C16.bset C f χ, ξ ≠ ν → ξ ≠ Work.BG.sconj C ν →
      Work.BG.sconj C ξ = ξ → (Work.BG.lamOrbit C ξ).ncard ≠ 4 →
      ∃ k : ℤ, χ 1 = (4 : ℂ) * (k : ℂ) := by
  intro hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv ξ hξ hξν hξνs hξfix hξne4
  haveI : Fintype ↥C.P.U := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥C.P.U : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have huniq : D.n = 4 := l34ExcNeFour_n_eq_four D C hdisj hinv h4
  have hbset : bset C f χ = {ν, sconj C ν, ξ} :=
    l34ExcNeFour_bset_eq D C hDC hS3 f hf χ hχ hν hne hξ hξν hξνs
  obtain ⟨⟨β, hβirr, hνβ, hsνβ⟩, ⟨α₁, α₂, hα₁irr, hα₂irr, hαne, hαdeg, hξshape⟩, hξ2⟩ :=
    l34ne_restrict_shape D C hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv huniq ξ hξ hξν hξνs
      hξfix hξne4
  have hξdeg : ∃ m : ℤ, ξ 1 = (2 : ℂ) * (m : ℂ) ∧ Odd m := by
    obtain ⟨n₁, hn₁odd, hn₁⟩ := exists_odd_nat_degree (odd_card_U_of_compat hDC) hα₁irr
    refine ⟨(n₁ : ℤ), ?_, by exact_mod_cast hn₁odd⟩
    have h1 : restrictU C ξ (1 : ↥C.P.U) = ξ 1 := by
      rw [restrictU_apply]
      exact congrArg ξ (Subtype.ext (by simp))
    have h' : ξ 1 = α₁ 1 + α₂ 1 := by
      rw [← h1, hξshape, ClassFunction.add_apply]
    have hα₂ : α₂ 1 = (n₁ : ℂ) := by rw [← hαdeg]; exact hn₁
    rw [h', hn₁, hα₂]
    push_cast
    ring
  exact c3enc_deg_crux D C hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv huniq ξ hξ hξν hξνs
    hξfix hξne4 hbset hξdeg

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem c3ExcNeFourC {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Compat D C → Work.GW2.C16.Sec3Hyp D →
    ∀ f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ, Work.GW2.C16.IsCoherent C f →
    ∀ χ : ClassFunction G ℂ, Work.BG.IsPmIrr χ →
    ∀ ν ∈ Work.GW2.C16.bset C f χ, Work.BG.sconj C ν ≠ ν →
      (Work.BG.sconj C ν ∉ Work.BG.lamOrbit C ν ∨ (Work.BG.lamOrbit C ν).ncard = D.n) →
      (Work.BG.lamOrbit C ν).ncard = 4 →
      Work.BG.sconj C '' Work.BG.lamOrbit C ν = Work.BG.lamOrbit C ν →
      ∀ ξ ∈ Work.GW2.C16.bset C f χ, ξ ≠ ν → ξ ≠ Work.BG.sconj C ν →
      Work.BG.sconj C ξ = ξ → (Work.BG.lamOrbit C ξ).ncard ≠ 4 → False := by
  intro hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv ξ hξ hξν hξνs hξs hξ4
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype ↥C.P.U := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(C.P.U) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have huniq : D.n = 4 := l34ExcNeFour_n_eq_four D C hdisj hinv h4
  obtain ⟨⟨β, hβirr, hνβ, hsνβ⟩, ⟨α₁, α₂, hα₁irr, hα₂irr, hαne, hαdeg, hξshape⟩, hξ2⟩ :=
    l34ne_restrict_shape D C hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv huniq ξ hξ hξν hξνs
      hξs hξ4
  have h4dvd : ∃ k : ℤ, χ 1 = (4 : ℂ) * (k : ℂ) :=
    c3enc_deg4 D C hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv ξ hξ hξν hξνs hξs hξ4
  obtain ⟨σ, L, hσσ, hLS, hLrel, hinvα₁, hinvα₂, hcent⟩ :=
    l34ne_exists_fixing_action D C hDC hS3 huniq hξ.1 hξs hα₁irr hα₂irr hαne hξshape hξ2
  have hcongU : ∀ u : ↥(C.P.U), AlgIntModTwo (χ (u : G)) (α₁ u + α₂ u) :=
    l34ne_cong_alpha D C hDC hS3 f hf χ hχ hν hξ hne hξν hξνs
      (l34ExcNeFour_bset_eq D C hDC hS3 f hf χ hχ hν hne hξ hξν hξνs) hβirr hνβ hsνβ hξshape
  have hUodd : Odd (Nat.card ↥(C.P.U)) := odd_card_U_of_compat hDC
  haveI : Fintype ↥(fixedSubgroup σ) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(fixedSubgroup σ) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  refine l34ExcNeFour_glauberman_contra hUodd σ hσσ hα₁irr hα₂irr hinvα₁ hinvα₂ hαne ?_
  intro c
  have hc0 : AlgIntModTwo (χ (((c : ↥(C.P.U)) : G))) 0 :=
    l34ne_chi_even (D.S) hχ h4dvd (u := (((c : ↥(C.P.U)) : G)))
      ⟨L, hLS, hLrel, fun l hl => hcent (c : ↥(C.P.U)) c.2 l hl⟩
  exact (hcongU c).symm.trans hc0

end Work.BG
