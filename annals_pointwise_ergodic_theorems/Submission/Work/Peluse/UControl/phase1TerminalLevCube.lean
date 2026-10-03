import Mathlib
import Submission.Work.Peluse.UControl.levCubeDefs
import Submission.Work.Peluse.UControl.atomInjective

/-!
# The phase-1 terminal state is a level state of the PET level chain

The input of the level chain (`PetLevelChain`, hence `Work.Peluse.UControl.petChapter5Holds`) is a
`Phase1Terminal d n lc Y` state: its live slots are the `(P, h)` with `h : Fin n → Bool`, `h ≠ 0`,
all of degree `d - 1`, with leading coefficient `C d * C lc * shift h`.

This file identifies it with a `LevCube`-state of the level chain: `A` is *all* the parameters
(`Finset.univ`), the frozen vector is the empty history, and the atoms are
`atoms₁ s = C ((d : ℤ) * lc) * X s`, so that `atomSum univ atoms₁ h = C d * C lc * shift h`.  The
`LevIndep` hypothesis of `LevRound` (distinct histories have distinct atom sums) holds because
`lc ≠ 0` (the leading coefficient of the nonzero polynomial `Y.Q (P,h)`) and `MvPolynomial` over `ℤ`
is a domain.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

attribute [local instance] Classical.propDecidable

/-- The atoms of the phase-1 terminal state: `C (d * lc) * X s`. -/
def levInitAtoms (d n : ℕ) (lc : ℤ) :
    {s // s ∈ (Finset.univ : Finset (Fin n))} → MvPolynomial (Fin n) ℤ :=
  fun s => MvPolynomial.C ((d : ℤ) * lc) * MvPolynomial.X s.1

lemma levInitAtoms_atomSum {d n : ℕ} (lc : ℤ) (h : Fin n → Bool) :
    atomSum (Finset.univ : Finset (Fin n)) (levInitAtoms d n lc) h
      = MvPolynomial.C (d : ℤ) * MvPolynomial.C lc * HistData.shift h := by
  classical
  have hshift : MvPolynomial.C (d : ℤ) * MvPolynomial.C lc * HistData.shift h
      = ∑ s ∈ (Finset.univ : Finset (Fin n)),
          (if h s then MvPolynomial.C (d : ℤ) * MvPolynomial.C lc * MvPolynomial.X s else 0) := by
    simp only [HistData.shift, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    by_cases hs : h s <;> simp [hs]
  rw [hshift, atomSum]
  rw [← Finset.sum_attach (s := (Finset.univ : Finset (Fin n)))
      (f := fun s : Fin n =>
        if h s then MvPolynomial.C (d : ℤ) * MvPolynomial.C lc * MvPolynomial.X s else 0)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  by_cases hs : h s
  · simp only [hs, if_true, levInitAtoms]
    rw [map_mul]
  · simp [hs]

lemma cubeSet_univ (n : ℕ) (f₀ : Fin n → Bool) :
    cubeSet n (Finset.univ : Finset (Fin n)) f₀ = Finset.univ := by
  ext h
  simp [cubeSet]

/-- The live slots of the level state with all parameters current and the empty history frozen are
exactly the `P`-tagged nonempty histories. -/
lemma LevH_univ (d n : ℕ) :
    LevH d n (Finset.univ : Finset (Fin n)) 0
      = Finset.univ.filter (fun x : InitIdx d × (Fin n → Bool) =>
          x.1 = (Sum.inr 0 : InitIdx d) ∧ x.2 ≠ 0) := by
  ext x
  rw [mem_LevH, cubeSet_univ]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- **The phase-1 terminal state is a level state of degree `d - 1` with all parameters current and
atoms `C (d * lc) * X s`.** -/
theorem phase1Terminal_levCube {d n : ℕ} {lc : ℤ} {Y : HistData d n}
    (hT : Phase1Terminal d n lc Y) :
    LevCube d (d - 1) n (Finset.univ : Finset (Fin n)) 0 (levInitAtoms d n lc) Y := by
  classical
  refine ⟨?_, ?_⟩
  · rw [LevH_univ]
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      obtain ⟨hx1, hx2, -, -⟩ := hT.1 x hx
      exact ⟨hx1, hx2⟩
    · rintro ⟨hx1, hx2⟩
      have hmem := hT.2 x.2 hx2
      have h2 : ((Sum.inr 0 : InitIdx d), x.2) = x := by rw [← hx1]
      rwa [h2] at hmem
  · intro h _ hne
    have hmem : ((Sum.inr 0 : InitIdx d), h) ∈ Y.H := hT.2 h hne
    obtain ⟨-, -, hdeg, hlc⟩ := hT.1 _ hmem
    exact ⟨hdeg, by rw [hlc, levInitAtoms_atomSum]⟩

/-- **The atoms of the phase-1 terminal state are independent** (so that `LevRound` applies), given
that `C ((d : ℤ) * lc) ≠ 0` — which holds in the situation of `PetChapter5`, where `d ≥ 2` and
`lc = P.leadingCoeff ≠ 0`. -/
theorem phase1Terminal_levIndep {d n : ℕ} {lc : ℤ}
    (hlc : MvPolynomial.C ((d : ℤ) * lc) ≠ (0 : MvPolynomial (Fin n) ℤ)) :
    LevIndep n (Finset.univ : Finset (Fin n)) (levInitAtoms d n lc) := by
  classical
  intro h g _ _ hsum
  have h1 : MvPolynomial.C (d : ℤ) * MvPolynomial.C lc * HistData.shift h
      = MvPolynomial.C (d : ℤ) * MvPolynomial.C lc * HistData.shift g := by
    rw [← levInitAtoms_atomSum (d := d) (n := n) lc h,
      ← levInitAtoms_atomSum (d := d) (n := n) lc g, hsum]
  have hC : (MvPolynomial.C (d : ℤ) * MvPolynomial.C lc : MvPolynomial (Fin n) ℤ)
      = MvPolynomial.C ((d : ℤ) * lc) := (map_mul _ _ _).symm
  rw [hC] at h1
  exact histShift_injective (mul_left_cancel₀ hlc h1)

end

end Work.Peluse.UControl
