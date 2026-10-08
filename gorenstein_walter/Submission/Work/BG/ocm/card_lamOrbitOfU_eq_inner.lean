import Mathlib
import Submission.Work.BG.orbitCardAux
import Submission.Work.BG.glauberman_two
import Submission.Work.BG.lamOrbitOfU_inner_eq_zero_or_one
import Submission.OddOrder.GroupTheory.RepresentationTheory.CharacterCompleteness
import Submission.OddOrder.GroupTheory.RepresentationTheory.ZIrrFourier

namespace Work.BG.ocm

open OddOrder.RepresentationTheory

set_option maxHeartbeats 1600000

theorem card_lamOrbitOfU_eq_inner {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype ↥C.P.H0] [Fintype ↥(Work.GW2.C16.Uin C)]
    (hDC : Work.GW2.C16.Compat D C) (hS3 : Work.GW2.C16.Sec3Hyp D)
    (a : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(Work.GW2.C16.Uin C)) :
    ((Work.BG.lamOrbitOfU C (a : OddOrder.RepresentationTheory.ClassFunction
        ↥(Work.GW2.C16.Uin C) ℂ)).ncard : ℂ)
      = OddOrder.RepresentationTheory.ClassFunction.inner
          (OddOrder.RepresentationTheory.ClassFunction.induce (Work.GW2.C16.Uin C)
            (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ))
          (OddOrder.RepresentationTheory.ClassFunction.induce (Work.GW2.C16.Uin C)
            (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ)) := by
  classical
  haveI : Finite ↥C.P.H0 := Finite.of_fintype _
  haveI : Fintype (IrreducibleCharacter ↥C.P.H0) := Fintype.ofFinite _
  -- name the induced class function and its Fourier coefficients
  set θ : ClassFunction ↥(Work.GW2.C16.Uin C) ℂ :=
    (a : ClassFunction ↥(Work.GW2.C16.Uin C) ℂ) with hθ
  -- **Frobenius reciprocity + multiplicity one**: `⟨Ind θ, b⟩ = ⟨Res b, θ⟩ ∈ {0,1}`.
  have hcoe : ∀ b : IrreducibleCharacter ↥C.P.H0,
      ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
          (b : ClassFunction ↥C.P.H0 ℂ)
        = ClassFunction.inner
            (ClassFunction.restrict (Work.GW2.C16.Uin C) (b : ClassFunction ↥C.P.H0 ℂ)) θ := by
    intro b
    rw [ClassFunction.inner_induce_eq_inner_restrict, ClassFunction.inner_star_comm]
    rcases Work.BG.lamOrbitOfU_inner_eq_zero_or_one D C hDC hS3
      (ν := (b : ClassFunction ↥C.P.H0 ℂ)) b.isIrreducible (a := θ) a.isIrreducible with h | h
    · rw [h, star_zero]
    · rw [h, star_one]
  have hmb01 : ∀ b : IrreducibleCharacter ↥C.P.H0,
      ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
          (b : ClassFunction ↥C.P.H0 ℂ) = 0 ∨
      ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
          (b : ClassFunction ↥C.P.H0 ℂ) = 1 := by
    intro b
    rw [hcoe b]
    exact Work.BG.lamOrbitOfU_inner_eq_zero_or_one D C hDC hS3 b.isIrreducible a.isIrreducible
  have hprod : ∀ b : IrreducibleCharacter ↥C.P.H0,
      ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
          (b : ClassFunction ↥C.P.H0 ℂ)
        * star (ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
          (b : ClassFunction ↥C.P.H0 ℂ))
      = (if ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
            (b : ClassFunction ↥C.P.H0 ℂ) = 0 then (0:ℂ) else 1) := by
    intro b
    rcases hmb01 b with h | h <;> rw [h] <;> simp
  -- **Parseval**: `⟨Ind θ, Ind θ⟩ = Σ_b |⟨Ind θ, b⟩|²`.
  have hparse : ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
        (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
      = ∑ b : IrreducibleCharacter ↥C.P.H0,
          ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
              (b : ClassFunction ↥C.P.H0 ℂ)
            * star (ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
              (b : ClassFunction ↥C.P.H0 ℂ)) := by
    have hfour := sum_inner_irreducibleCharacter_smul (G := ↥C.P.H0)
      (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
    calc ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
          (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
        = ClassFunction.inner
            (∑ b : IrreducibleCharacter ↥C.P.H0,
              ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
                (b : ClassFunction ↥C.P.H0 ℂ) • (b : ClassFunction ↥C.P.H0 ℂ))
            (ClassFunction.induce (Work.GW2.C16.Uin C) θ) := by rw [hfour]
      _ = ∑ b : IrreducibleCharacter ↥C.P.H0,
            ClassFunction.inner
              (ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
                (b : ClassFunction ↥C.P.H0 ℂ) • (b : ClassFunction ↥C.P.H0 ℂ))
              (ClassFunction.induce (Work.GW2.C16.Uin C) θ) := by
            rw [inner_sum_left]
      _ = _ := by
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [ClassFunction.inner_smul_left, ClassFunction.inner_star_comm, star_star]
  -- the sum of the multiplicities is the number of nonzero Fourier coefficients
  have hsum : (∑ b : IrreducibleCharacter ↥C.P.H0,
        (if ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
            (b : ClassFunction ↥C.P.H0 ℂ) = 0 then (0:ℂ) else 1))
      = ((Finset.univ.filter (fun b : IrreducibleCharacter ↥C.P.H0 =>
          ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
            (b : ClassFunction ↥C.P.H0 ℂ) ≠ 0)).card : ℂ) := by
    have hcong : (∑ b : IrreducibleCharacter ↥C.P.H0,
        (if ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
            (b : ClassFunction ↥C.P.H0 ℂ) = 0 then (0:ℂ) else 1))
      = ∑ b : IrreducibleCharacter ↥C.P.H0,
        (if ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
            (b : ClassFunction ↥C.P.H0 ℂ) ≠ 0 then (1:ℂ) else 0) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases h : ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
          (b : ClassFunction ↥C.P.H0 ℂ) = 0 <;> simp [h]
    rw [hcong, Finset.sum_boole]
  -- the `Λ`-orbit of `θ` is the image of the nonzero-coefficient irreducible characters
  have hlamEq : Work.BG.lamOrbitOfU C θ
      = ↑((Finset.univ.filter (fun b : IrreducibleCharacter ↥C.P.H0 =>
          ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
            (b : ClassFunction ↥C.P.H0 ℂ) ≠ 0)).image
            (fun b : IrreducibleCharacter ↥C.P.H0 => (b : ClassFunction ↥C.P.H0 ℂ))) := by
    ext ν
    constructor
    · intro hν
      obtain ⟨hνirr, hνne⟩ := hν
      refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨ν, hνirr⟩, ?_, rfl⟩)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rwa [hcoe]⟩
    · intro hν
      rw [Finset.mem_coe, Finset.mem_image] at hν
      obtain ⟨b, hb, rfl⟩ := hν
      rw [Finset.mem_filter] at hb
      exact ⟨b.isIrreducible, by rw [← hcoe b]; exact hb.2⟩
  have hScard : (Work.BG.lamOrbitOfU C θ).ncard
      = (Finset.univ.filter (fun b : IrreducibleCharacter ↥C.P.H0 =>
          ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
            (b : ClassFunction ↥C.P.H0 ℂ) ≠ 0)).card := by
    rw [hlamEq, Set.ncard_coe_finset,
      Finset.card_image_of_injective _ (fun _ _ hxy => Subtype.ext hxy)]
  -- assembly
  calc ((Work.BG.lamOrbitOfU C θ).ncard : ℂ)
      = ((Finset.univ.filter (fun b : IrreducibleCharacter ↥C.P.H0 =>
          ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
            (b : ClassFunction ↥C.P.H0 ℂ) ≠ 0)).card : ℂ) := by rw [hScard]
    _ = (∑ b : IrreducibleCharacter ↥C.P.H0,
        (if ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
            (b : ClassFunction ↥C.P.H0 ℂ) = 0 then (0:ℂ) else 1)) := hsum.symm
    _ = (∑ b : IrreducibleCharacter ↥C.P.H0,
          ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
              (b : ClassFunction ↥C.P.H0 ℂ)
            * star (ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
              (b : ClassFunction ↥C.P.H0 ℂ))) := by
          refine Finset.sum_congr rfl fun b _ => (hprod b).symm
    _ = ClassFunction.inner (ClassFunction.induce (Work.GW2.C16.Uin C) θ)
          (ClassFunction.induce (Work.GW2.C16.Uin C) θ) := hparse.symm

end Work.BG.ocm
