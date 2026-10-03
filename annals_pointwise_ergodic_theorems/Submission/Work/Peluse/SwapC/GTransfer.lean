/-
The transfer layer between the multiset cube sum `Work.Peluse.SwapC.mCubeSum` and the general box
form `Work.Peluse.SwapC.gWinForm`.

`mCubeSum d X ν S F` is
`(1/|S|) (1/|X|)^{2d} ∑_{h,h'} ∑'_x ∏_ω C^{|ω|} F_ω (x + cornerShift (ν ∘ h) (ν ∘ h') ω)`,
and `gWinForm d (fun _ => X) ν W F` is the same inner sum with the `tsum` over `ℤ` replaced by a
sum over the finite window `W`.  For finitely supported `F` the two agree once `W` contains the
support of the cube term, which is what this file proves: the cube term vanishes off
`gWindow N M`, where `N` bounds the support of every `F ω` and `M = dirMass ν` bounds the
`ℓ¹`-size of the directions.

## Main results

* `Work.Peluse.SwapC.mCubeSum_eq_gWinForm`
-/
import Mathlib
import Submission.Work.Peluse.SwapC.GDefs
import Submission.Work.Peluse.SwapC.Basic

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse

/-- The `ℓ¹`-size of a finite direction family `ν`: the sum over the coordinates of the sum of the
absolute values of the directions actually taken. -/
def dirMass {d : ℕ} {X : Type} [Fintype X] (ν : Fin d → X → ℤ) : ℕ :=
  ∑ i, (Finset.univ.image (ν i)).sum (fun a => a.natAbs)

/-- The window containing the support of the cube term of `mCubeSum` with support bound `N` and
direction mass `M`: `[-N-M, N+M]`. -/
def gWindow (N M : ℕ) : Finset ℤ :=
  Finset.Icc (-(((N + M : ℕ) : ℤ))) (((N + M : ℕ) : ℤ))

lemma gtotal_natAbs_le {d : ℕ} {X : Type} [Fintype X] (ν : Fin d → X → ℤ) (h : Fin d → X) :
    (gtotal ν h).natAbs ≤ dirMass ν := by
  rw [gtotal, dirMass]
  refine le_trans (Work.Peluse.BoxNorm.natAbs_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  exact Finset.single_le_sum (fun a _ => Nat.zero_le _)
    (Finset.mem_image.mpr ⟨h i, Finset.mem_univ _, rfl⟩)

lemma weight_zero_bool {d : ℕ} : weight (0 : Fin d → Bool) = 0 := by
  rw [weight]
  simp

lemma gcorner_zero {d : ℕ} {X : Type} (z z' : Fin d → X) :
    gcorner z z' (0 : Fin d → Bool) = z' := by
  funext i
  simp [gcorner]

/-- The cube term of `mCubeSum` vanishes off the window `gWindow N (dirMass ν)` when `N` bounds the
support of every `F ω`. -/
lemma cubeTerm_mCubeSum_eq_zero {d : ℕ} {X : Type} [Fintype X] (ν : Fin d → X → ℤ)
    {F : (Fin d → Bool) → ℤ → ℂ} {N : ℕ} (hN : ∀ ω, SupportIn (F ω) N)
    (z z' : Fin d → X) {x : ℤ} (hx : x ∉ gWindow N (dirMass ν)) :
    (∏ ω : Fin d → Bool,
        (star^[weight ω])
          (F ω (x + cornerShift (fun k => ν k (z k)) (fun k => ν k (z' k)) ω))) = 0 := by
  have hconv : (∏ ω : Fin d → Bool,
        (star^[weight ω])
          (F ω (x + cornerShift (fun k => ν k (z k)) (fun k => ν k (z' k)) ω)))
      = ∏ ω : Fin d → Bool, (star^[weight ω]) (F ω (x + gtotal ν (gcorner z z' ω))) :=
    Finset.prod_congr rfl (fun ω _ => by rw [gtotal_gcorner])
  rw [hconv]
  refine Finset.prod_eq_zero (Finset.mem_univ (0 : Fin d → Bool)) ?_
  have hz : gcorner z z' (0 : Fin d → Bool) = z' := gcorner_zero z z'
  have hM : (gtotal ν z').natAbs ≤ dirMass ν := gtotal_natAbs_le ν z'
  have hxbig : N + dirMass ν < x.natAbs := by
    rw [gWindow, Finset.mem_Icc, not_and_or, not_le, not_le] at hx
    have hcast : ((N + dirMass ν : ℕ) : ℤ) < (x.natAbs : ℤ) := by
      rcases hx with h | h
      · have h2 := Int.le_natAbs (a := -x)
        rw [Int.natAbs_neg] at h2
        omega
      · exact lt_of_lt_of_le h (Int.le_natAbs (a := x))
    omega
  have htri : x.natAbs ≤ (x + gtotal ν z').natAbs + (gtotal ν z').natAbs := by
    have h := Int.natAbs_add_le (x + gtotal ν z') (-(gtotal ν z'))
    simpa using h
  have hlt : N < (x + gtotal ν z').natAbs := by omega
  rw [hz, weight_zero_bool, Function.iterate_zero_apply]
  exact hN (0 : Fin d → Bool) _ hlt

/-- `gWinForm` with the total shift written as a `cornerShift` (the form in which `mCubeSum` is
stated). -/
lemma gWinForm_eq_cornerShift (d : ℕ) (X : Type) [Fintype X] (ν : Fin d → X → ℤ) (W : Finset ℤ)
    (F : (Fin d → Bool) → ℤ → ℂ) :
    gWinForm d (fun _ : Fin d => X) ν W F
      = ∑ h : Fin d → X, ∑ h' : Fin d → X, ∑ x ∈ W,
          ∏ ω : Fin d → Bool,
            (star^[weight ω])
              (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω)) := by
  simp only [gWinForm]
  refine Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ =>
    Finset.sum_congr rfl (fun x _ => ?_)))
  exact Finset.prod_congr rfl (fun ω _ => by rw [gtotal_gcorner])

/-- **The multiset cube sum is the general box form**, up to the normalisation constant `c` and with
the `tsum` over `ℤ` replaced by the sum over the window `gWindow N (dirMass ν)`. -/
lemma mCubeSum_eq_gWinForm (d : ℕ) (X : Type) [Fintype X] (ν : Fin d → X → ℤ) (S : Finset ℤ)
    (F : (Fin d → Bool) → ℤ → ℂ) {N : ℕ} (hN : ∀ ω, SupportIn (F ω) N) :
    mCubeSum d X ν S F
      = (((S.card : ℂ))⁻¹ * (((Fintype.card X : ℂ))⁻¹) ^ (2 * d)) *
          gWinForm d (fun _ : Fin d => X) ν (gWindow N (dirMass ν)) F := by
  rw [gWinForm_eq_cornerShift]
  simp only [mCubeSum]
  congr 1
  refine Finset.sum_congr rfl (fun h _ => ?_)
  refine Finset.sum_congr rfl (fun h' _ => ?_)
  exact tsum_eq_sum (s := gWindow N (dirMass ν))
    (fun x hx => cubeTerm_mCubeSum_eq_zero ν hN h h' hx)

/-- The norm form of `mCubeSum_eq_gWinForm`. -/
lemma norm_mCubeSum_eq (d : ℕ) (X : Type) [Fintype X] (ν : Fin d → X → ℤ) (S : Finset ℤ)
    (F : (Fin d → Bool) → ℤ → ℂ) {N : ℕ} (hN : ∀ ω, SupportIn (F ω) N) :
    ‖mCubeSum d X ν S F‖
      = (((S.card : ℝ))⁻¹ * (((Fintype.card X : ℝ))⁻¹) ^ (2 * d)) *
          ‖gWinForm d (fun _ : Fin d => X) ν (gWindow N (dirMass ν)) F‖ := by
  rw [mCubeSum_eq_gWinForm d X ν S F hN, norm_mul, norm_mul, norm_pow, norm_inv, norm_inv,
    Complex.norm_natCast, Complex.norm_natCast]

end

end Work.Peluse.SwapC
