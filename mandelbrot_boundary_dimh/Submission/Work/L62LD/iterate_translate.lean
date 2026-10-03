import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.l62c_basic

/-!
# L62LD — the iterate of `ĥ = d.E - β` commutes with integral translations on `Bl`

`d.E` is `T`-equivariant on the lower horn component `hd.Bl` (`Work.L62.E_add_one_Bl`), hence so
is `ĥ = d.E - β`.  Consequently, as long as the forward orbit of `y` stays inside a set
`S ⊆ hd.Bl`, the `n`-th iterate of `ĥ` satisfies `ĥ^[n] (y + k) = ĥ^[n] y + k` for every `k : ℤ`.

This is exactly the `ℤ`-equivariance used when the `L62` chain of discs is built in the lift.
-/

namespace Work.L62LD

noncomputable section

open MandelDim

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-- `d.E` commutes with an arbitrary integral translation on `hd.Bl`. -/
theorem E_add_int_bl (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d)
    {w : ℂ} (hw : w ∈ hd.Bl) (k : ℤ) :
    d.E (w + (k : ℂ)) = d.E w + (k : ℂ) :=
  Work.Horn.MandelDim.E_add_int hd.Bl_T
    (fun _ hw _ => Work.L62.E_add_one_Bl d hd hw) hw k

/-- **Adding an integer to the starting point.**  If the orbit of `y` up to time `n` stays in a
subset of the `T`-invariant lower horn component `hd.Bl`, then the `n`-th iterate of
`ĥ = d.E - β` commutes with translation by any integer. -/
theorem iterate_translate {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {β : ℂ} {S : Set ℂ} (hS : S ⊆ hd.Bl)
    {y : ℂ} {n : ℕ} (hy : ∀ m, m ≤ n → ((fun w => d.E w - β)^[m]) y ∈ S) (k : ℤ) :
    ((fun w => d.E w - β)^[n]) (y + (k : ℂ)) = ((fun w => d.E w - β)^[n]) y + (k : ℂ) := by
  -- one step of the shift, valid at every point of `hd.Bl`
  have hstep : ∀ w ∈ hd.Bl,
      (fun z : ℂ => d.E z - β) (w + (k : ℂ)) = (fun z : ℂ => d.E z - β) w + (k : ℂ) := by
    intro w hw
    simp only
    rw [E_add_int_bl d hd hw k]
    ring
  have key : ∀ (m : ℕ) (y : ℂ),
      (∀ i, i ≤ m → ((fun w => d.E w - β)^[i]) y ∈ hd.Bl) →
      ((fun w => d.E w - β)^[m]) (y + (k : ℂ))
        = ((fun w => d.E w - β)^[m]) y + (k : ℂ) := by
    intro m
    induction m with
    | zero => intro y _; simp
    | succ p ih =>
        intro y hy'
        have hmem : ((fun w => d.E w - β)^[p]) y ∈ hd.Bl := hy' p (Nat.le_succ p)
        have hrec : ((fun w => d.E w - β)^[p]) (y + (k : ℂ))
            = ((fun w => d.E w - β)^[p]) y + (k : ℂ) :=
          ih y (fun i hi => hy' i (le_trans hi (Nat.le_succ p)))
        calc (fun w => d.E w - β)^[p + 1] (y + (k : ℂ))
            = (fun w => d.E w - β) (((fun w => d.E w - β)^[p]) (y + (k : ℂ))) :=
              Function.iterate_succ_apply' _ _ _
          _ = (fun w => d.E w - β) (((fun w => d.E w - β)^[p]) y + (k : ℂ)) := by rw [hrec]
          _ = (fun w => d.E w - β) (((fun w => d.E w - β)^[p]) y) + (k : ℂ) := hstep _ hmem
          _ = ((fun w => d.E w - β)^[p + 1]) y + (k : ℂ) :=
              congrArg (· + (k : ℂ))
                (Function.iterate_succ_apply' (fun w => d.E w - β) p y).symm
  exact key n y (fun i hi => hS (hy i hi))

end

end Work.L62LD
