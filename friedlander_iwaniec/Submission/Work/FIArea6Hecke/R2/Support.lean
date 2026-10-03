/-
# `Work.FIArea6Hecke.R2.Support`

The **off-support vanishing** of the conductor Gauss sum: `condGaussSum M chi ξ = 0` whenever
`M ∤ ξ`.  This is the first half of the duality; it uses only the `M`-periodicity of `chi` and the
action of the translations by multiples of `M` on the box `[0,N)²`.

Proof.  The weight `f s = chi s · ekern M ξ s` is `N`-periodic (`N = gnorm M`), so the sum over the
box is the sum over any translated box: for `M ∣ w` the map `s ↦ s + w` carries the box to a
complete residue system mod `N` and
`∑_{box} f = ∑_{box} f (· + w) = (∑_{box} f) · ekern M ξ w`.
Taking `w = M` and `w = -i M` and using `LambdaArith` (`¬ M ∣ ξ` makes one of the two character
values `≠ 1`) gives `∑_{box} f = 0`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R2.Defs
import Submission.Work.FIArea6Hecke.CGD.BoxCRS
import Submission.Work.FIArea6Hecke.CGD.CrsCalculus
import Submission.Work.FIArea6Hecke.CGD.LambdaArith
import Submission.Work.FIArea6Hecke.CGD.EkernOne
import Submission.Work.FIArea6Hecke.CGD.Reindex

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6Hecke.R2

open scoped BigOperators
open Work.FIArea6Hecke.R

noncomputable section

/-- The weight `s ↦ chi s · ekern M ξ s` is invariant under translation by multiples of `N`. -/
lemma weight_periodic_norm (M ξ : GaussianInt) (chi : GaussianInt → ℂ)
    (hchi : IsCharModStrict M chi) (hM : M ≠ 0) (x y : GaussianInt)
    (h : ((Work.FIPlan.gnorm M : ℕ) : GaussianInt) ∣ (x - y)) :
    chi x * ekern M ξ x = chi y * ekern M ξ y := by
  obtain ⟨c, hc⟩ := h
  have hx : x = y + ((Work.FIPlan.gnorm M : ℕ) : GaussianInt) * c := by
    have h := sub_eq_iff_eq_add.mp hc
    rw [h]; ring
  rw [hx, chi_add_gnorm M chi hchi c y, ekern_add_intCast M ξ c y hM]

/-- **Off-support vanishing**: if `M ∤ ξ` then the conductor Gauss sum vanishes. -/
theorem condGaussSum_eq_zero_of_not_dvd (M ξ : GaussianInt) (hM : M ≠ 0)
    (chi : GaussianInt → ℂ) (hchi : IsCharModStrict M chi) (hξ : ¬ M ∣ ξ) :
    condGaussSum M chi ξ = 0 := by
  classical
  have hN0 : Work.FIPlan.gnorm M ≠ 0 := gnorm_ne_zero hM
  obtain ⟨hbox, _hboxcard⟩ := Work.FIArea6Hecke.CGD.BoxCRS (Work.FIPlan.gnorm M) hN0
  set f : GaussianInt → ℂ := fun s => chi s * ekern M ξ s with hf
  have hfper : ∀ z w : GaussianInt,
      ((Work.FIPlan.gnorm M : ℕ) : GaussianInt) ∣ (z - w) → f z = f w := by
    intro z w h
    simp only [hf]
    exact weight_periodic_norm M ξ chi hchi hM z w h
  have hbase : condGaussSum M chi ξ = Finset.sum (gbox (Work.FIPlan.gnorm M)) f := by
    rw [Work.FIArea6Hecke.CGD.Reindex]
    rfl
  -- translation by a multiple `w` of `M` multiplies the box sum by `ekern M ξ w`
  have hshift : ∀ w : GaussianInt, M ∣ w →
      Finset.sum (gbox (Work.FIPlan.gnorm M)) f
        = Finset.sum (gbox (Work.FIPlan.gnorm M)) f * ekern M ξ w := by
    intro w hw
    have hCC := Work.FIArea6Hecke.CGD.CrsCalculus ((Work.FIPlan.gnorm M : ℕ) : GaussianInt)
      (gbox (Work.FIPlan.gnorm M)) (gbox (Work.FIPlan.gnorm M)) hbox hbox f hfper
    have hwCRS : IsCRS ((Work.FIPlan.gnorm M : ℕ) : GaussianInt)
        ((gbox (Work.FIPlan.gnorm M)).image (fun s => s + w)) := hCC.2.1 w
    have hsumimg : Finset.sum ((gbox (Work.FIPlan.gnorm M)).image (fun s => s + w)) f
        = Finset.sum (gbox (Work.FIPlan.gnorm M)) (fun s => f (s + w)) := hCC.2.2.2.1 w
    have hCC2 := Work.FIArea6Hecke.CGD.CrsCalculus ((Work.FIPlan.gnorm M : ℕ) : GaussianInt)
      (gbox (Work.FIPlan.gnorm M)) ((gbox (Work.FIPlan.gnorm M)).image (fun s => s + w))
      hbox hwCRS f hfper
    have hswap : Finset.sum (gbox (Work.FIPlan.gnorm M)) f
        = Finset.sum ((gbox (Work.FIPlan.gnorm M)).image (fun s => s + w)) f := hCC2.1
    have hterm : ∀ s : GaussianInt, f (s + w) = f s * ekern M ξ w := by
      intro s
      simp only [hf]
      rw [chi_add_of_dvd M chi hchi hw, ekern_add_right]
      ring
    have hstep : Finset.sum (gbox (Work.FIPlan.gnorm M)) (fun s => f (s + w))
        = Finset.sum (gbox (Work.FIPlan.gnorm M)) f * ekern M ξ w := by
      rw [Finset.sum_congr rfl (fun s _ => hterm s), Finset.sum_mul]
    calc Finset.sum (gbox (Work.FIPlan.gnorm M)) f
        = Finset.sum ((gbox (Work.FIPlan.gnorm M)).image (fun s => s + w)) f := hswap
      _ = Finset.sum (gbox (Work.FIPlan.gnorm M)) (fun s => f (s + w)) := hsumimg
      _ = Finset.sum (gbox (Work.FIPlan.gnorm M)) f * ekern M ξ w := hstep
  have hM1 : M ∣ M := dvd_rfl
  have hM2 : M ∣ star (⟨0, 1⟩ : GaussianInt) * M := dvd_mul_left M _
  have hsum1 := hshift M hM1
  have hsum2 := hshift (star (⟨0, 1⟩ : GaussianInt) * M) hM2
  have hkey : ekern M ξ M ≠ 1 ∨ ekern M ξ (star (⟨0, 1⟩ : GaussianInt) * M) ≠ 1 := by
    rcases Work.FIArea6Hecke.CGD.LambdaArith M ξ hM hξ with h | h
    · left
      intro hc
      exact h ((Work.FIArea6Hecke.CGD.EkernOne M hM ξ M).mp hc)
    · right
      intro hc
      exact h ((Work.FIArea6Hecke.CGD.EkernOne M hM ξ
        (star (⟨0, 1⟩ : GaussianInt) * M)).mp hc)
  have hzero : Finset.sum (gbox (Work.FIPlan.gnorm M)) f = 0 := by
    rcases hkey with hkey | hkey
    · have h1 : Finset.sum (gbox (Work.FIPlan.gnorm M)) f * (1 - ekern M ξ M) = 0 := by
        rw [mul_sub, mul_one, ← hsum1, sub_self]
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h (sub_ne_zero.mpr (Ne.symm hkey))
    · have h1 : Finset.sum (gbox (Work.FIPlan.gnorm M)) f
          * (1 - ekern M ξ (star (⟨0, 1⟩ : GaussianInt) * M)) = 0 := by
        rw [mul_sub, mul_one, ← hsum2, sub_self]
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h (sub_ne_zero.mpr (Ne.symm hkey))
  rw [hbase, hzero]

end

end Work.FIArea6Hecke.R2
