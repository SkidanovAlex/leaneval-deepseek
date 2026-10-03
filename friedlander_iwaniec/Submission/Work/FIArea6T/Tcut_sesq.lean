/-
# `Submission.Work.FIArea6T.Tcut_sesq` — T1: the sesquilinear expansion of the (10.13) form

`Work.FIArea6T.TcutBil` (`Submission.Work.FIArea6T.Defs`) is the sesquilinear form underlying
`Work.FITop4.Tcut` (`Tcut Rz cut β = TcutBil Rz cut β β`, definitionally).  Here we record that it
is additive in the first argument and conjugate-linear in the second, in the expanded form used by
the τ-removal: with `δ = Work.FIArea6T.tauCompl Pa β` the (5.9)-complement of a clean coefficient
and `Work.FIArea6T.tauCut_eq_sub_tauCompl`, the diagonal case gives

  `Tcut (tauCut Pa β) = TcutBil β β − TcutBil β δ − TcutBil δ β + TcutBil δ δ`,

which is the starting point of the Rankin-plus-Schur removal of *FI* (10.4)
(`FIArea6/AREA6_CONTRACT_LEAD.md` §3.3, T1).
-/
import Mathlib
import Submission.Work.FIArea6T.Defs

set_option autoImplicit false

namespace Work.FIArea6T

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- `TcutBil` is additive in its first argument. -/
private lemma TcutBil_sub_left (Rz : ℤ) (cut : GaussianInt → GaussianInt → ℕ → ℝ)
    (a b v : GaussianInt → ℂ) :
    TcutBil Rz cut (a - b) v = TcutBil Rz cut a v - TcutBil Rz cut b v := by
  have hpt : ∀ z1 z2 : GaussianInt,
      (if Work.FIPlan.GaussCoprime z1 z2 then
        ((a - b) z1 * star (v z2)) *
          ((∑ d ∈ Work.FITop4.Sset z1 z2,
            ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
              * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℂ)
       else 0)
      = (if Work.FIPlan.GaussCoprime z1 z2 then
          (a z1 * star (v z2)) *
            ((∑ d ∈ Work.FITop4.Sset z1 z2,
              ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
                * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℂ)
         else 0)
        - (if Work.FIPlan.GaussCoprime z1 z2 then
            (b z1 * star (v z2)) *
              ((∑ d ∈ Work.FITop4.Sset z1 z2,
                ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
                  * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℂ)
           else 0) := by
    intro z1 z2
    by_cases hc : Work.FIPlan.GaussCoprime z1 z2
    · rw [if_pos hc, if_pos hc, if_pos hc, Pi.sub_apply, sub_mul, sub_mul]
    · rw [if_neg hc, if_neg hc, if_neg hc]; ring
  have hsum : (∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
        (if Work.FIPlan.GaussCoprime z1 z2 then
          ((a - b) z1 * star (v z2)) *
            ((∑ d ∈ Work.FITop4.Sset z1 z2,
              ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
                * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℂ)
         else 0))
      = (∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
          (if Work.FIPlan.GaussCoprime z1 z2 then
            (a z1 * star (v z2)) *
              ((∑ d ∈ Work.FITop4.Sset z1 z2,
                ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
                  * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℂ)
           else 0))
        - (∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
          (if Work.FIPlan.GaussCoprime z1 z2 then
            (b z1 * star (v z2)) *
              ((∑ d ∈ Work.FITop4.Sset z1 z2,
                ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
                  * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℂ)
           else 0)) := by
    rw [Finset.sum_congr rfl (fun z1 _ => Finset.sum_congr rfl (fun z2 _ => hpt z1 z2))]
    simp only [Finset.sum_sub_distrib]
  simp only [TcutBil]
  rw [hsum]; ring

/-- `TcutBil` is conjugate-linear in its second argument. -/
private lemma TcutBil_sub_right (Rz : ℤ) (cut : GaussianInt → GaussianInt → ℕ → ℝ)
    (u a b : GaussianInt → ℂ) :
    TcutBil Rz cut u (a - b) = TcutBil Rz cut u a - TcutBil Rz cut u b := by
  have hpt : ∀ z1 z2 : GaussianInt,
      (if Work.FIPlan.GaussCoprime z1 z2 then
        (u z1 * star ((a - b) z2)) *
          ((∑ d ∈ Work.FITop4.Sset z1 z2,
            ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
              * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℂ)
       else 0)
      = (if Work.FIPlan.GaussCoprime z1 z2 then
          (u z1 * star (a z2)) *
            ((∑ d ∈ Work.FITop4.Sset z1 z2,
              ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
                * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℂ)
         else 0)
        - (if Work.FIPlan.GaussCoprime z1 z2 then
            (u z1 * star (b z2)) *
              ((∑ d ∈ Work.FITop4.Sset z1 z2,
                ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
                  * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℂ)
           else 0) := by
    intro z1 z2
    by_cases hc : Work.FIPlan.GaussCoprime z1 z2
    · rw [if_pos hc, if_pos hc, if_pos hc, Pi.sub_apply, star_sub, mul_sub, sub_mul]
    · rw [if_neg hc, if_neg hc, if_neg hc]; ring
  have hsum : (∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
        (if Work.FIPlan.GaussCoprime z1 z2 then
          (u z1 * star ((a - b) z2)) *
            ((∑ d ∈ Work.FITop4.Sset z1 z2,
              ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
                * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℂ)
         else 0))
      = (∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
          (if Work.FIPlan.GaussCoprime z1 z2 then
            (u z1 * star (a z2)) *
              ((∑ d ∈ Work.FITop4.Sset z1 z2,
                ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
                  * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℂ)
           else 0))
        - (∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
          (if Work.FIPlan.GaussCoprime z1 z2 then
            (u z1 * star (b z2)) *
              ((∑ d ∈ Work.FITop4.Sset z1 z2,
                ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
                  * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℂ)
           else 0)) := by
    rw [Finset.sum_congr rfl (fun z1 _ => Finset.sum_congr rfl (fun z2 _ => hpt z1 z2))]
    simp only [Finset.sum_sub_distrib]
  simp only [TcutBil]
  rw [hsum]; ring

/-- **T1 — the sesquilinear expansion of the (10.13) form.** -/
theorem Tcut_sesq (Rz : ℤ) (cut : GaussianInt → GaussianInt → ℕ → ℝ)
    (u₁ u₂ v₁ v₂ : GaussianInt → ℂ) :
    Work.FIArea6T.TcutBil Rz cut (fun z => u₁ z - u₂ z) (fun z => v₁ z - v₂ z)
      = Work.FIArea6T.TcutBil Rz cut u₁ v₁ - Work.FIArea6T.TcutBil Rz cut u₁ v₂
        - Work.FIArea6T.TcutBil Rz cut u₂ v₁ + Work.FIArea6T.TcutBil Rz cut u₂ v₂ := by
  change TcutBil Rz cut (u₁ - u₂) (v₁ - v₂) = _
  rw [TcutBil_sub_left, TcutBil_sub_right, TcutBil_sub_right]
  ring

end

end Work.FIArea6T
