import Mathlib
import Submission.Work.BG.degreeGeSOrbit
import Submission.Work.BG.lemma36Defs
import Submission.Work.BG.isCharacterRestrict

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

/-- **Step 1 of BG Lemma 3.6 (the count).**  If `a ∈ Irr(U)` is a constituent of `χ|_U` with
multiplicity `c = ⟨χ|_U, a⟩` for an irreducible character `χ` of `G`, then the `S`-orbit of `a`
contributes `|S·a| · c · a(1)` to `χ(1)`.

Route (all ingredients are in the workspace): `isCharacterRestrict` makes `χ|_U` a genuine
character of `U`, so `IsCharacter.exists_natFinsupp_eq_sum` writes
`χ|_U = ∑_{b ∈ Irr U} m_b·b` with `m_b = ⟨χ|_U, b⟩ ∈ ℕ` and `χ(1) = ∑_b m_b·b(1)`.  For each
`s : ↥(D.S)` and `b_s := compHom (phiS s) a`: `b_s` is irreducible, `m_{b_s} = c` by
`Work.BG.inner_phiS_eq`, and `b_s 1 = a 1 = irrDeg a` since `(phiS s) 1 = 1`.  Hence the orbit's
`ncard` distinct elements each contribute `c * irrDeg a`, a sub-sum of `χ(1)`. -/
theorem degree_ge_sOrbitCount {G : Type} [Group G] [Finite G] [Fintype G]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (hDC : Work.GW2.C16.Compat D C)
    [Fintype ↥(Work.GW2.C16.Uin C)] [Invertible (Nat.card ↥(Work.GW2.C16.Uin C) : ℂ)]
    [Invertible (Nat.card G : ℂ)]
    (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (hχ : OddOrder.RepresentationTheory.IsIrreducibleCharacter χ)
    (a : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(Work.GW2.C16.Uin C))
    (hca : OddOrder.RepresentationTheory.ClassFunction.inner
        (OddOrder.RepresentationTheory.ClassFunction.restrict (Work.GW2.C16.Uin C)
          (OddOrder.RepresentationTheory.ClassFunction.restrict C.P.H0 χ))
        (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ) ≠ 0) :
    ∃ c dχ : ℕ, (c : ℂ) = OddOrder.RepresentationTheory.ClassFunction.inner
        (OddOrder.RepresentationTheory.ClassFunction.restrict (Work.GW2.C16.Uin C)
          (OddOrder.RepresentationTheory.ClassFunction.restrict C.P.H0 χ))
        (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ) ∧
      χ 1 = (dχ : ℂ) ∧
      (Work.BG.sOrbitU D C hDC (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ)).ncard *
        c * Work.BG.irrDeg a ≤ dχ := by
  classical
  -- `χ|_U` is a genuine character of `U = ↥(Uin C)`
  have hχUchar : IsCharacter
      (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ)) :=
    isCharacterRestrict (isCharacterRestrict hχ.isCharacter C.P.H0) (Uin C)
  -- its non-negative-integer decomposition into irreducibles
  obtain ⟨m, hsupp, hsum, hcoeff⟩ := hχUchar.exists_natFinsupp_eq_sum
  -- the multiplicity `c` and the degree `dχ` of `χ`
  set c : ℕ := m (a : ClassFunction ↥(Uin C) ℂ) with hcdef
  have hc : (c : ℂ) = ClassFunction.inner
      (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ))
      (a : ClassFunction ↥(Uin C) ℂ) := by
    rw [hcdef]
    exact hcoeff (a : ClassFunction ↥(Uin C) ℂ) a.isIrreducible
  set dχ : ℕ := irrDeg (⟨χ, hχ⟩ : IrreducibleCharacter G) with hddef
  have hdχ : χ 1 = (dχ : ℂ) := by
    rw [hddef]
    exact irrDeg_spec (⟨χ, hχ⟩ : IrreducibleCharacter G)
  -- evaluation of a finite sum of class functions at `1`
  have hsum_apply : ∀ (t : Finset (ClassFunction ↥(Uin C) ℂ))
      (F : ClassFunction ↥(Uin C) ℂ → ClassFunction ↥(Uin C) ℂ),
      (∑ b ∈ t, F b) 1 = ∑ b ∈ t, (F b) 1 := by
    intro t F
    induction t using Finset.cons_induction with
    | empty => simp
    | cons b t hb ih => rw [Finset.sum_cons, Finset.sum_cons, ClassFunction.add_apply, ih]
  have hχU1eq : ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ) 1 = χ 1 := by
    simp [ClassFunction.restrict_apply]
  have hval : ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ) 1
      = ∑ b ∈ m.support, (m b : ℂ) * (b 1) := by
    rw [hsum, hsum_apply (m.support) (fun b => (m b : ℂ) • b)]
    exact Finset.sum_congr rfl fun b _ => ClassFunction.smul_apply _ _ _
  have hχ1re : (χ 1).re = ∑ b ∈ m.support, (m b : ℝ) * (b 1).re := by
    have h : χ 1 = ∑ b ∈ m.support, (m b : ℂ) * (b 1) := hχU1eq.symm.trans hval
    rw [h, Complex.re_sum]
    exact Finset.sum_congr rfl fun b _ => by
      rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  have hdχre : (dχ : ℝ) = ∑ b ∈ m.support, (m b : ℝ) * (b 1).re := by
    have hdre : (χ 1).re = (dχ : ℝ) := by
      have h := congrArg Complex.re hdχ
      rwa [Complex.natCast_re] at h
    exact hdre.symm.trans hχ1re
  -- each irreducible degree is non-negative (for the monotonicity of the sum)
  have hterm_nonneg : ∀ b ∈ m.support, (0 : ℝ) ≤ (m b : ℝ) * (b 1).re := by
    intro b hb
    have hb_irr : IsIrreducibleCharacter b := hsupp (Finset.mem_coe.mpr hb)
    have hdeg : (0 : ℝ) ≤ (b 1).re := by
      obtain ⟨d, _, hd1⟩ :=
        irreducibleCharacter_apply_one_eq_pos_natCast (⟨b, hb_irr⟩ : IrreducibleCharacter ↥(Uin C))
      rw [hd1, Complex.natCast_re]
      exact Nat.cast_nonneg d
    exact mul_nonneg (Nat.cast_nonneg _) hdeg
  -- the `S`-orbit of `a` as a finset
  set T : Finset (ClassFunction ↥(Uin C) ℂ) :=
    Finset.image (fun s : ↥(D.S) => ClassFunction.compHom (L33D.phiS D C hDC s).toMonoidHom
      (a : ClassFunction ↥(Uin C) ℂ)) Finset.univ with hTdef
  have hTcoe : (T : Set (ClassFunction ↥(Uin C) ℂ)) =
      sOrbitU D C hDC (a : ClassFunction ↥(Uin C) ℂ) := by
    rw [hTdef]
    ext b
    simp only [sOrbitU, Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor <;> rintro ⟨s, h⟩ <;> exact ⟨s, h.symm⟩
  have hNcard : (sOrbitU D C hDC (a : ClassFunction ↥(Uin C) ℂ)).ncard = T.card := by
    rw [← hTcoe]
    exact Set.ncard_coe_finset T
  -- each element of the orbit is an irreducible constituent with multiplicity `c` and degree
  -- `irrDeg a`
  have hmem : ∀ b ∈ T, m b = c ∧ b 1 = (irrDeg a : ℂ) := by
    intro b hb
    rw [hTdef, Finset.mem_image] at hb
    obtain ⟨s, -, rfl⟩ := hb
    have hb_irr : IsIrreducibleCharacter
        (ClassFunction.compHom (L33D.phiS D C hDC s).toMonoidHom
          (a : ClassFunction ↥(Uin C) ℂ)) :=
      a.isIrreducible.compHom_of_surjective (L33D.phiS D C hDC s).surjective
    refine ⟨?_, ?_⟩
    · have hmbC : (m (ClassFunction.compHom (L33D.phiS D C hDC s).toMonoidHom
          (a : ClassFunction ↥(Uin C) ℂ)) : ℂ) = (c : ℂ) := by
        rw [hcoeff _ hb_irr,
          inner_phiS_eq D C hDC s χ (a : ClassFunction ↥(Uin C) ℂ), ← hc]
      exact Nat.cast_injective hmbC
    · rw [ClassFunction.compHom_apply]
      have h1 : (MulEquiv.toMonoidHom ((L33D.phiS D C hDC) s)) (1 : ↥(Uin C)) = 1 := map_one _
      rw [h1]
      exact irrDeg_spec a
  have horbit_val : ∀ b ∈ T, (m b : ℝ) * (b 1).re = (c : ℝ) * (irrDeg a : ℝ) := by
    intro b hb
    obtain ⟨hmb, hb1⟩ := hmem b hb
    rw [hmb, hb1, Complex.natCast_re]
  -- the orbit is contained in the support (its multiplicities are `c ≠ 0`)
  have hc_ne : c ≠ 0 := by
    intro h0
    exact hca (by rw [← hc, h0]; simp)
  have hTsub : T ⊆ m.support := by
    intro b hb
    rw [Finsupp.mem_support_iff]
    rw [(hmem b hb).1]
    exact hc_ne
  -- the displayed inequality
  have hTsum : ∑ b ∈ T, (m b : ℝ) * (b 1).re
      = (T.card : ℝ) * (c : ℝ) * (irrDeg a : ℝ) := by
    rw [Finset.sum_congr rfl fun b hb => horbit_val b hb]
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  have hmain : ∑ b ∈ T, (m b : ℝ) * (b 1).re ≤ (dχ : ℝ) := by
    rw [hdχre]
    exact Finset.sum_le_sum_of_subset_of_nonneg hTsub (fun b hb _ => hterm_nonneg b hb)
  have hcast : ((T.card * c * irrDeg a : ℕ) : ℝ)
      = (T.card : ℝ) * (c : ℝ) * (irrDeg a : ℝ) := by
    push_cast
    ring
  have hfinal : ((T.card * c * irrDeg a : ℕ) : ℝ) ≤ (dχ : ℝ) := by
    rw [hcast, ← hTsum]
    exact hmain
  have hnat : T.card * c * irrDeg a ≤ dχ := by
    exact_mod_cast hfinal
  refine ⟨c, dχ, hc, hdχ, ?_⟩
  rw [hNcard]
  exact hnat

end Work.BG
