import Mathlib
import Submission.Work.BG.lemma36Defs
import Submission.Work.BG.degree_ge_sOrbitCount

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.GW2.C16

theorem eqCase_kill {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (hDC : Work.GW2.C16.Compat D C)
    [Fintype ↥C.P.H0] [Fintype ↥(Work.GW2.C16.Uin C)]
    [Invertible (Nat.card ↥(Work.GW2.C16.Uin C) : ℂ)]
    (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (hχ : OddOrder.RepresentationTheory.IsIrreducibleCharacter χ)
    (a : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(Work.GW2.C16.Uin C))
    (hca : OddOrder.RepresentationTheory.ClassFunction.inner
        (OddOrder.RepresentationTheory.ClassFunction.restrict (Work.GW2.C16.Uin C)
          (OddOrder.RepresentationTheory.ClassFunction.restrict C.P.H0 χ))
        (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ) ≠ 0)
    (hOrbit : (Work.BG.sOrbitU D C hDC
        (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ)).ncard *
      (Work.BG.lamOrbitOfU C
        (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ)).ncard = 2 * D.n)
    (hMultA : ∃ c : ℕ, (c : ℂ) = OddOrder.RepresentationTheory.ClassFunction.inner
        (OddOrder.RepresentationTheory.ClassFunction.restrict (Work.GW2.C16.Uin C)
          (OddOrder.RepresentationTheory.ClassFunction.restrict C.P.H0 χ))
        (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ) ∧
      (Work.BG.lamOrbitOfU C
        (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ)).ncard ≤ c)
    (heq : Work.BG.irrDeg ⟨χ, hχ⟩ = 2 * D.n * Work.BG.irrDeg a) :
    (∀ c : ℕ, (c : ℂ) = OddOrder.RepresentationTheory.ClassFunction.inner
        (OddOrder.RepresentationTheory.ClassFunction.restrict (Work.GW2.C16.Uin C)
          (OddOrder.RepresentationTheory.ClassFunction.restrict C.P.H0 χ))
        (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ) →
      c = (Work.BG.lamOrbitOfU C
        (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ)).ncard) ∧
    (∀ b : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(Work.GW2.C16.Uin C),
      OddOrder.RepresentationTheory.ClassFunction.inner
        (OddOrder.RepresentationTheory.ClassFunction.restrict (Work.GW2.C16.Uin C)
          (OddOrder.RepresentationTheory.ClassFunction.restrict C.P.H0 χ))
        (b : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ) ≠ 0 →
      (b : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ) ∈
        Work.BG.sOrbitU D C hDC
          (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ)) := by
  classical
  -- ## Abbreviations for the expressions occurring throughout
  set χU : ClassFunction ↥(Uin C) ℂ :=
    ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ) with hχUdef
  set NS : ℕ := (sOrbitU D C hDC (a : ClassFunction ↥(Uin C) ℂ)).ncard with hNSdef
  set NL : ℕ := (lamOrbitOfU C (a : ClassFunction ↥(Uin C) ℂ)).ncard with hNLdef
  set dG : ℕ := irrDeg ⟨χ, hχ⟩ with hdGdef
  -- ## The decomposition of `χ|_U` into irreducibles
  have hχUchar : IsCharacter χU := by
    rw [hχUdef]
    exact isCharacterRestrict (isCharacterRestrict hχ.isCharacter C.P.H0) (Uin C)
  obtain ⟨m, hsupp, hsum, hcoeff⟩ := hχUchar.exists_natFinsupp_eq_sum
  set cA : ℕ := m (a : ClassFunction ↥(Uin C) ℂ) with hcAdef
  have hcA : (cA : ℂ) = ClassFunction.inner χU (a : ClassFunction ↥(Uin C) ℂ) := by
    rw [hcAdef]; exact hcoeff _ a.isIrreducible
  have hc_ne : cA ≠ 0 := by
    intro h0
    apply hca
    rw [← hcA, h0]; simp
  -- ## Evaluating the decomposition at `1`; `deg χ` is the support sum
  have hval : χU 1 = ∑ b ∈ m.support, (m b : ℂ) * (b 1) := by
    rw [hsum]
    rw [ClassFunction.sum_apply]
    exact Finset.sum_congr rfl fun b _ => ClassFunction.smul_apply _ _ _
  have hχU1 : χU 1 = χ 1 := by
    rw [hχUdef]; simp [ClassFunction.restrict_apply]
  have hdG_eq : χ 1 = (dG : ℂ) := by
    rw [hdGdef]; exact irrDeg_spec ⟨χ, hχ⟩
  have hsum_re : ∑ b ∈ m.support, (m b : ℝ) * (b 1).re = (dG : ℝ) := by
    have h2 : (∑ b ∈ m.support, (m b : ℂ) * (b 1)) = (dG : ℂ) := by
      rw [← hval]; exact hχU1.trans hdG_eq
    have h3 : (∑ b ∈ m.support, ((m b : ℂ) * (b 1)).re) = (dG : ℝ) := by
      have := congrArg Complex.re h2
      simpa [Complex.re_sum, Complex.natCast_re] using this
    have hterm : ∀ b, ((m b : ℂ) * (b 1)).re = (m b : ℝ) * (b 1).re := by
      intro b
      rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    have h4 : ∑ b ∈ m.support, ((m b : ℂ) * (b 1)).re
        = ∑ b ∈ m.support, (m b : ℝ) * (b 1).re :=
      Finset.sum_congr rfl fun b _ => hterm b
    rw [← h4]; exact h3
  -- ## The `S`-orbit of `a`, as a finset
  set T : Finset (ClassFunction ↥(Uin C) ℂ) :=
    (Finset.univ : Finset ↥(D.S)).image
      (fun s : ↥(D.S) => ClassFunction.compHom (L33D.phiS D C hDC s).toMonoidHom
        (a : ClassFunction ↥(Uin C) ℂ)) with hTdef
  have hTcoe : (T : Set (ClassFunction ↥(Uin C) ℂ)) =
      sOrbitU D C hDC (a : ClassFunction ↥(Uin C) ℂ) := by
    rw [hTdef]
    ext b
    constructor
    · intro hb
      rw [Finset.mem_coe, Finset.mem_image] at hb
      obtain ⟨s, -, hs⟩ := hb
      change ∃ s : ↥(D.S), b = ClassFunction.compHom (L33D.phiS D C hDC s).toMonoidHom
        (a : ClassFunction ↥(Uin C) ℂ)
      exact ⟨s, hs.symm⟩
    · intro hb
      change ∃ s : ↥(D.S), b = ClassFunction.compHom (L33D.phiS D C hDC s).toMonoidHom
        (a : ClassFunction ↥(Uin C) ℂ) at hb
      obtain ⟨s, hs⟩ := hb
      rw [Finset.mem_coe, Finset.mem_image]
      exact ⟨s, Finset.mem_univ s, hs.symm⟩
  have hNcard : NS = T.card := by
    rw [hNSdef, ← hTcoe]
    exact Set.ncard_coe_finset T
  -- ## Every element of the orbit has multiplicity `cA` and degree `a(1)`
  have hmem : ∀ b ∈ T, m b = cA ∧ b 1 = ((irrDeg a : ℕ) : ℂ) := by
    intro b hb
    rw [hTdef, Finset.mem_image] at hb
    obtain ⟨s, -, rfl⟩ := hb
    have hb_irr : IsIrreducibleCharacter (ClassFunction.compHom
        (L33D.phiS D C hDC s).toMonoidHom (a : ClassFunction ↥(Uin C) ℂ)) :=
      a.isIrreducible.compHom_of_surjective (L33D.phiS D C hDC s).surjective
    refine ⟨?_, ?_⟩
    · have hcast : (m (ClassFunction.compHom
          (L33D.phiS D C hDC s).toMonoidHom (a : ClassFunction ↥(Uin C) ℂ)) : ℂ) = (cA : ℂ) := by
        rw [hcoeff _ hb_irr]
        rw [inner_phiS_eq D C hDC s χ (a : ClassFunction ↥(Uin C) ℂ), ← hχUdef]
        exact hcA.symm
      exact Nat.cast_injective hcast
    · rw [ClassFunction.compHom_apply, map_one]
      exact irrDeg_spec a
  -- ## Positivity of the orbit cardinality, from the orbit product
  have hNS_pos : 0 < NS := by
    have hDn : 0 < D.n := lt_of_lt_of_le (by norm_num) D.two_le
    have h : NS * NL ≠ 0 := by
      rw [hOrbit]
      exact mul_ne_zero (by norm_num) hDn.ne'
    exact Nat.pos_of_ne_zero (left_ne_zero_of_mul h)
  -- ## The counting inequality, giving `cA ≤ NL`
  obtain ⟨c', dχ', hc', hdχ', hineq⟩ := degree_ge_sOrbitCount D C hDC χ hχ a hca
  have hc'cA : c' = cA := Nat.cast_injective (by rw [hc', hcA, hχUdef])
  have hdχ'dG : dχ' = dG := Nat.cast_injective (by rw [← hdχ']; exact hdG_eq)
  have hineq' : NS * cA ≤ 2 * D.n := by
    have h1 : NS * cA * irrDeg a ≤ 2 * D.n * irrDeg a := by
      rw [hNSdef, ← hc'cA, ← heq, ← hdχ'dG]
      exact hineq
    exact Nat.le_of_mul_le_mul_right h1 (irrDeg_pos a)
  have hcA_le_NL : cA ≤ NL := by
    refine Nat.le_of_mul_le_mul_left ?_ hNS_pos
    exact hineq'.trans (le_of_eq hOrbit.symm)
  -- ## The lower bound `NL ≤ cA` supplied by the hypothesis
  obtain ⟨cM, hcM, hleM⟩ := hMultA
  have hcMcA : cM = cA := Nat.cast_injective (by rw [hcM, hcA])
  have hNL_le_cA : NL ≤ cA := by rw [hcMcA] at hleM; exact hleM
  have hcA_eq : cA = NL := le_antisymm hcA_le_NL hNL_le_cA
  refine ⟨?_, ?_⟩
  -- ## Part 1: the multiplicity of `a` in `χ|_U` equals `|Λ(a)|`
  · intro c hc
    rw [← hcA_eq]
    exact Nat.cast_injective (by rw [hc, hcA, hχUdef])
  -- ## Part 2: the support of `χ|_U` is contained in the `S`-orbit of `a`
  · intro b hb
    have hsumT_re : ∑ b' ∈ T, (m b' : ℝ) * (b' 1).re
        = (NS : ℝ) * (cA : ℝ) * (irrDeg a : ℝ) := by
      have hterm : ∀ b' ∈ T, (m b' : ℝ) * (b' 1).re = (cA : ℝ) * (irrDeg a : ℝ) := by
        intro b' hb'
        obtain ⟨hmb, hb1⟩ := hmem b' hb'
        rw [hmb, hb1, Complex.natCast_re]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, ← hNcard]
      ring
    have hsat : (dG : ℝ) = (NS : ℝ) * (cA : ℝ) * (irrDeg a : ℝ) := by
      have hnat : dG = NS * cA * irrDeg a := by
        rw [hcA_eq, hOrbit]
        exact heq
      rw [hnat]; push_cast; ring
    have hsum_eq : ∑ b' ∈ m.support, (m b' : ℝ) * (b' 1).re
        = ∑ b' ∈ T, (m b' : ℝ) * (b' 1).re := hsum_re.trans (hsat.trans hsumT_re.symm)
    have hnonneg : ∀ b' ∈ m.support, 0 ≤ (m b' : ℝ) * (b' 1).re := by
      intro b' hb'
      have hb'irr : IsIrreducibleCharacter b' := hsupp (Finset.mem_coe.mpr hb')
      have hb'1 : 0 ≤ (b' 1).re := by
        rw [irrDeg_spec ⟨b', hb'irr⟩, Complex.natCast_re]; exact Nat.cast_nonneg _
      exact mul_nonneg (Nat.cast_nonneg _) hb'1
    have hTsub : T ⊆ m.support := by
      intro b' hb'
      rw [Finsupp.mem_support_iff, (hmem b' hb').1]
      exact hc_ne
    have hssub : m.support ⊆ T := by
      by_contra hcon
      obtain ⟨x, hxsupp, hxT⟩ := Finset.not_subset.mp hcon
      have hx_pos : 0 < (m x : ℝ) * (x 1).re := by
        have hmx : 0 < m x := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hxsupp)
        have hx1 : 0 < (x 1).re := by
          have hxirr : IsIrreducibleCharacter x := hsupp (Finset.mem_coe.mpr hxsupp)
          rw [irrDeg_spec ⟨x, hxirr⟩, Complex.natCast_re]
          exact_mod_cast (irrDeg_pos ⟨x, hxirr⟩)
        exact mul_pos (by exact_mod_cast hmx) hx1
      have hsum0 : ∑ b' ∈ m.support \ T, (m b' : ℝ) * (b' 1).re = 0 := by
        have hs := Finset.sum_sdiff (f := fun b' => (m b' : ℝ) * (b' 1).re) hTsub
        linarith [hs, hsum_eq]
      have hmem' : x ∈ m.support \ T := Finset.mem_sdiff.mpr ⟨hxsupp, hxT⟩
      have hle := Finset.single_le_sum (s := m.support \ T)
        (f := fun b' => (m b' : ℝ) * (b' 1).re)
        (fun i hi => hnonneg i (Finset.mem_sdiff.mp hi).1) hmem'
      linarith [hle, hsum0, hx_pos]
    have hbsupp : (b : ClassFunction ↥(Uin C) ℂ) ∈ m.support := by
      rw [Finsupp.mem_support_iff]
      intro h0
      apply hb
      rw [← hcoeff _ b.isIrreducible, h0]; simp
    have hbT : (b : ClassFunction ↥(Uin C) ℂ) ∈ T := hssub hbsupp
    have hmem_set : (b : ClassFunction ↥(Uin C) ℂ) ∈ (T : Set (ClassFunction ↥(Uin C) ℂ)) :=
      Finset.mem_coe.mpr hbT
    rw [hTcoe] at hmem_set
    exact hmem_set

end Work.BG
