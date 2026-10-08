import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.l34ne_orbit_fiber_card

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

/-- `Λ`-equivalent class functions of `H₀` have the same degree. -/
theorem chiDegOrbitLamEquivOne (C : Sec2Ctx G) {μ ν : ClassFunction ↥C.P.H0 ℂ}
    (h : LamEquiv C μ ν) : ν 1 = μ 1 := by
  obtain ⟨β, rfl⟩ := h
  rw [ClassFunction.mul_apply]
  have h1 : lamCF C β 1 = 1 := by simp [lamCF]
  rw [h1, one_mul]

/-- The `Λ`-orbit representative is idempotent. -/
theorem chiDegOrbitRepIdem (C : Sec2Ctx G) (ν : IrreducibleCharacter ↥C.P.H0) :
    orbitRep C (orbitRep C ν) = orbitRep C ν :=
  (orbitRep_eq_of_lamEquiv (C := C) (orbitRep_mem C ν)).symm

/-- The sum of `d θ * θ(1)` over the `Λ`-orbit of an orbit representative `r` is divisible
by `4`. -/
theorem chiDegOrbitFiberSum {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype (IrreducibleCharacter ↥C.P.H0)] [DecidableEq (IrreducibleCharacter ↥C.P.H0)]
    (d : IrreducibleCharacter ↥C.P.H0 → ℂ)
    (hd_inv : ∀ μ ν : IrreducibleCharacter ↥C.P.H0,
      LamEquiv C (μ : ClassFunction ↥C.P.H0 ℂ) (ν : ClassFunction ↥C.P.H0 ℂ) → d μ = d ν)
    (hd_int : ∀ θ : IrreducibleCharacter ↥C.P.H0, ∃ m : ℤ, d θ = (m : ℂ))
    (horb : ∀ θ : IrreducibleCharacter ↥C.P.H0,
      ∃ z : ℤ, ((lamOrbit C (θ : ClassFunction ↥C.P.H0 ℂ)).ncard : ℂ) *
        ((θ : ClassFunction ↥C.P.H0 ℂ) 1) = 4 * (z : ℂ))
    (r : IrreducibleCharacter ↥C.P.H0) (hr : orbitRep C r = r) :
    ∃ Z : ℤ, (∑ θ ∈ Finset.univ.filter (fun θ : IrreducibleCharacter ↥C.P.H0 =>
        orbitRep C θ = r), d θ * ((θ : ClassFunction ↥C.P.H0 ℂ) 1)) = 4 * (Z : ℂ) := by
  classical
  obtain ⟨m, hm⟩ := hd_int r
  obtain ⟨z, hz⟩ := horb r
  refine ⟨m * z, ?_⟩
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  have hcard : (Finset.univ.filter (fun θ : IrreducibleCharacter ↥C.P.H0 =>
      orbitRep C θ = r)).card = (lamOrbit C (r : ClassFunction ↥C.P.H0 ℂ)).ncard := by
    convert (l34ne_orbit_fiber_card C r hr).symm
  have hconst : ∀ θ ∈ Finset.univ.filter (fun θ : IrreducibleCharacter ↥C.P.H0 =>
        orbitRep C θ = r),
      d θ * ((θ : ClassFunction ↥C.P.H0 ℂ) 1) = d r * ((r : ClassFunction ↥C.P.H0 ℂ) 1) := by
    intro θ hθ
    rw [Finset.mem_filter] at hθ
    obtain ⟨-, hθr⟩ := hθ
    have hL : LamEquiv C (θ : ClassFunction ↥C.P.H0 ℂ) (r : ClassFunction ↥C.P.H0 ℂ) := by
      have h := orbitRep_mem C θ
      rwa [hθr] at h
    rw [hd_inv θ r hL, ← chiDegOrbitLamEquivOne C hL]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, hcard, hm, nsmul_eq_mul]
  push_cast
  linear_combination (m : ℂ) * hz

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem chiDegOrbitConstantSum {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype (IrreducibleCharacter ↥C.P.H0)]
    (d : IrreducibleCharacter ↥C.P.H0 → ℂ)
    (hd_inv : ∀ μ ν : IrreducibleCharacter ↥C.P.H0,
      Work.BG.LamEquiv C (μ : ClassFunction ↥C.P.H0 ℂ) (ν : ClassFunction ↥C.P.H0 ℂ) → d μ = d ν)
    (hd_int : ∀ θ : IrreducibleCharacter ↥C.P.H0, ∃ m : ℤ, d θ = (m : ℂ))
    (horb : ∀ θ : IrreducibleCharacter ↥C.P.H0,
      ∃ z : ℤ, ((Work.BG.lamOrbit C (θ : ClassFunction ↥C.P.H0 ℂ)).ncard : ℂ) *
        ((θ : ClassFunction ↥C.P.H0 ℂ) 1) = 4 * (z : ℂ)) :
    ∃ z : ℤ,
      (∑ θ : IrreducibleCharacter ↥C.P.H0, d θ * ((θ : ClassFunction ↥C.P.H0 ℂ) 1))
        = 4 * (z : ℂ) := by
  classical
  set R : Finset (IrreducibleCharacter ↥C.P.H0) := Finset.univ.image (orbitRep C) with hR
  have hfib : ∀ r ∈ R, ∃ Z : ℤ,
      (∑ θ ∈ Finset.univ.filter (fun θ : IrreducibleCharacter ↥C.P.H0 => orbitRep C θ = r),
        d θ * ((θ : ClassFunction ↥C.P.H0 ℂ) 1)) = 4 * (Z : ℂ) := by
    intro r hr
    have hr' : orbitRep C r = r := by
      obtain ⟨θ, -, hθ⟩ := Finset.mem_image.mp (by rwa [hR] at hr)
      rw [← hθ, chiDegOrbitRepIdem C θ]
    exact chiDegOrbitFiberSum C d hd_inv hd_int horb r hr'
  choose Zfun hZfun using hfib
  let Zf : IrreducibleCharacter ↥C.P.H0 → ℤ := fun r => if hr : r ∈ R then Zfun r hr else 0
  refine ⟨∑ r ∈ R, Zf r, ?_⟩
  have hZfeq : ∀ r ∈ R,
      (∑ θ ∈ Finset.univ.filter (fun θ : IrreducibleCharacter ↥C.P.H0 => orbitRep C θ = r),
        d θ * ((θ : ClassFunction ↥C.P.H0 ℂ) 1)) = 4 * ((Zf r : ℤ) : ℂ) := by
    intro r hr
    rw [hZfun r hr]
    simp only [Zf, dif_pos hr]
  have hS : (∑ θ : IrreducibleCharacter ↥C.P.H0, d θ * ((θ : ClassFunction ↥C.P.H0 ℂ) 1))
      = ∑ r ∈ R, ∑ θ ∈ Finset.univ.filter (fun θ : IrreducibleCharacter ↥C.P.H0 =>
          orbitRep C θ = r), d θ * ((θ : ClassFunction ↥C.P.H0 ℂ) 1) := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (IrreducibleCharacter ↥C.P.H0)))
      (t := R) (g := fun θ => orbitRep C θ)
      (f := fun θ => d θ * ((θ : ClassFunction ↥C.P.H0 ℂ) 1))
      (fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x))]
  rw [hS, Finset.sum_congr rfl hZfeq, ← Finset.mul_sum]
  congr 1
  exact (map_sum (Int.castRingHom ℂ) Zf R).symm

end Work.BG
