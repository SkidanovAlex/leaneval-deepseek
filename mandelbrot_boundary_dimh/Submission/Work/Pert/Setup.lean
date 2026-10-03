import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Basic

/-!
# PERT · `Work.Pert.Setup`: the gates, the lifted coordinate and the maximal domain `Dφ`

Language layer for the assembly of `PertData` (Shishikura §4.2, see `NOTES_PERT_assembly.md`).

For a perturbation `f` with normal-form data `(σ, u, α)` let `F = liftF u σ α` be the lift of `f`
on the cylinder and `Q` one of the two gate regions of §4.2 (`Qm ξ` resp. `Qp ξ`), on which `F`
is a near-translation (`Work.Pert.gate` / `gate_scale`).  `Φ` is a Fatou coordinate of `F` on `Q`
(`MandelDim.IsFatouCoordOn F Φ Q`, plus the surjectivity of `MandelDim.FatouExists`).

A point `w` of the maximal domain lies at *level* `n` when `w - n = Φ ζ` for some `ζ ∈ Q` whose
first `n` iterates under `F` still lie in `Q`; the iterated Abel equation then gives
`Φ (F^[n] ζ) = w`, so `φ_f w` should be `τ_f (F^[n] ζ)`.  The two facts proved here are

* `level_point_eq`: two legal levels of the same `w` end at the **same** point of `Q`
  (injectivity of `Φ` plus the Abel equation), so the value `τ (F^[n] ζ)` is well defined;
* `level_value_abel`: for a legal level `(ζ, n)` of `w` and a legal level `(ζ', n')` of `w + 1`,
  `τ (F^[n'] ζ') = f (τ (F^[n] ζ))` — the Abel equation `φ_f (w+1) = f (φ_f w)` of (4.2.1),
  together with the well-definedness of `φ_f`.
-/

namespace Work.Pert

open MandelDim Complex Set

noncomputable section

/-- The "lower" gate region of §4.2: `Qreg (ξ - 1/α) (-ξ)`. -/
def Qm (ξ : ℝ) (α : ℂ) : Set ℂ := MandelDim.Qreg (some ((ξ : ℂ) - 1 / α)) (some (-(ξ : ℂ)))

/-- The "upper" gate region of §4.2: `Qreg ξ (-ξ + 1/α)`. -/
def Qp (ξ : ℝ) (α : ℂ) : Set ℂ := MandelDim.Qreg (some (ξ : ℂ)) (some (-(ξ : ℂ) + 1 / α))

/-- The maximal domain of `φ_f`: the forward extension of the gate image along legal `F`-walks. -/
def Dphi (F Φ : ℂ → ℂ) (Q : Set ℂ) : Set ℂ :=
  {w | ∃ (n : ℕ) (ζ : ℂ), ζ ∈ Q ∧ Φ ζ = w - (n : ℂ) ∧ ∀ j : ℕ, j ≤ n → F^[j] ζ ∈ Q}

/-- The iterated Abel equation along a legal walk. -/
theorem abel_iter {F Φ : ℂ → ℂ} {Q : Set ℂ} {n : ℕ} {ζ : ℂ}
    (hwalk : ∀ j : ℕ, j ≤ n → F^[j] ζ ∈ Q)
    (hΦ : ∀ z ∈ Q, F z ∈ Q → Φ (F z) = Φ z + 1) :
    Φ (F^[n] ζ) = Φ ζ + (n : ℂ) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : ∀ j : ℕ, j ≤ k → F^[j] ζ ∈ Q := fun j hj => hwalk j (by omega)
    have h2 : Φ (F^[k] ζ) = Φ ζ + (k : ℂ) := ih h1
    have hk : F^[k] ζ ∈ Q := hwalk k (by omega)
    have hk1 : F (F^[k] ζ) ∈ Q := by
      have he : F^[(k + 1)] ζ = F (F^[k] ζ) := by rw [Function.iterate_succ_apply']
      rw [← he]; exact hwalk (k + 1) (by omega)
    have h3 : Φ (F (F^[k] ζ)) = Φ (F^[k] ζ) + 1 := hΦ (F^[k] ζ) hk hk1
    rw [Function.iterate_succ_apply' F k ζ, h3, h2]
    push_cast; ring

/-- **Well-definedness of the level**: two legal levels of the same point `w` end at the same point
of `Q` (so the value `τ (F^[n] ζ)` depends only on `w`). -/
theorem level_point_eq {F Φ : ℂ → ℂ} {Q : Set ℂ} (hinj : Set.InjOn Φ Q)
    (hΦ : ∀ z ∈ Q, F z ∈ Q → Φ (F z) = Φ z + 1)
    {w : ℂ} {n : ℕ} {ζ : ℂ} (hζQ : ζ ∈ Q) (hΦζ : Φ ζ = w - (n : ℂ))
    (hwalk : ∀ j : ℕ, j ≤ n → F^[j] ζ ∈ Q)
    {n' : ℕ} {ζ' : ℂ} (hζ'Q : ζ' ∈ Q) (hΦζ' : Φ ζ' = w - (n' : ℂ))
    (hwalk' : ∀ j : ℕ, j ≤ n' → F^[j] ζ' ∈ Q) :
    F^[n] ζ = F^[n'] ζ' := by
  have h1 : Φ (F^[n] ζ) = Φ ζ + (n : ℂ) := abel_iter hwalk hΦ
  have h2 : Φ (F^[n'] ζ') = Φ ζ' + (n' : ℂ) := abel_iter hwalk' hΦ
  have hmem1 : F^[n] ζ ∈ Q := hwalk n le_rfl
  have hmem2 : F^[n'] ζ' ∈ Q := hwalk' n' le_rfl
  have hkey : Φ (F^[n] ζ) = Φ (F^[n'] ζ') := by
    rw [h1, h2, hΦζ, hΦζ']; push_cast; ring
  exact hinj hmem1 hmem2 hkey

/-- A legal level of `w` truncated at a smaller height is a legal level of the corresponding
point: if `ζ ∈ Q` witnesses level `n` of `w` and `m ≤ n`, then `ζ` witnesses level `m` of
`w - (n - m)`. -/
theorem IsLevel_trunc {F Φ : ℂ → ℂ} {Q : Set ℂ} {w : ℂ} {n m : ℕ} {ζ : ℂ}
    (hmn : m ≤ n) (hζQ : ζ ∈ Q) (hΦζ : Φ ζ = w - (n : ℂ))
    (hwalk : ∀ j : ℕ, j ≤ n → F^[j] ζ ∈ Q) :
    Φ ζ = (w - ((n - m : ℕ) : ℂ)) - (m : ℂ) ∧ ∀ j : ℕ, j ≤ m → F^[j] ζ ∈ Q := by
  refine ⟨?_, fun j hj => hwalk j (by omega)⟩
  rw [hΦζ]
  have hcast : ((n : ℂ)) = ((n - m : ℕ) : ℂ) + (m : ℂ) := by
    rw [Nat.cast_sub hmn]; push_cast; ring
  rw [hcast]; ring

/-- **The Abel equation of `φ_f` (4.2.1), with well-definedness**: for a legal level `(ζ, n)` of
`w` and a legal level `(ζ', n')` of `w + 1`, the values `τ (F^[n] ζ)`, `τ (F^[n'] ζ')` satisfy
`τ (F^[n'] ζ') = f (τ (F^[n] ζ))`.  (`hOrb` is `MandelDim.FatouOrbit` for `(F, Φ, Q)`; it is the
only place where the walk is used beyond the last level.  `hτ` is `Work.Pert.abel`.) -/
theorem level_value_abel {F f τ Φ : ℂ → ℂ} {Q : Set ℂ} (hinj : Set.InjOn Φ Q)
    (hΦ : ∀ z ∈ Q, F z ∈ Q → Φ (F z) = Φ z + 1)
    (hτ : ∀ z : ℂ, τ (F z) = f (τ z))
    (hOrb : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℕ, Φ z' = Φ z + (k : ℂ) →
      ((∀ j : ℕ, j ≤ k → F^[j] z ∈ Q) ∧ F^[k] z = z'))
    {w : ℂ} {n : ℕ} {ζ : ℂ} (hζQ : ζ ∈ Q) (hΦζ : Φ ζ = w - (n : ℂ))
    (hwalk : ∀ j : ℕ, j ≤ n → F^[j] ζ ∈ Q)
    {n' : ℕ} {ζ' : ℂ} (hζ'Q : ζ' ∈ Q) (hΦζ' : Φ ζ' = (w + 1) - (n' : ℂ))
    (hwalk' : ∀ j : ℕ, j ≤ n' → F^[j] ζ' ∈ Q) :
    τ (F^[n'] ζ') = f (τ (F^[n] ζ)) := by
  rcases Nat.eq_zero_or_pos n' with h0 | hpos
  · -- `n' = 0`: `FatouOrbit` extends the walk of `ζ` by one step
    subst h0
    have hkey : Φ ζ' = Φ ζ + ((n + 1 : ℕ) : ℂ) := by
      rw [hΦζ', hΦζ]; push_cast; ring
    obtain ⟨hwalk2, hfin⟩ := hOrb ζ hζQ ζ' hζ'Q (n + 1) hkey
    have hsplit : F^[(n + 1)] ζ = F (F^[n] ζ) := Function.iterate_succ_apply' F n ζ
    have hsame : F (F^[n] ζ) = ζ' := by rw [← hsplit]; exact hfin
    show τ ζ' = f (τ (F^[n] ζ))
    rw [← hsame]
    exact hτ (F^[n] ζ)
  · -- `n' ≥ 1`: truncate the legal level of `w + 1` to a legal level of `w`
    obtain ⟨hΦtr, hwalktr⟩ := IsLevel_trunc (F := F) (Φ := Φ) (Q := Q) (w := w + 1)
      (n := n') (m := n' - 1) (by omega) hζ'Q hΦζ' hwalk'
    have hone : n' - (n' - 1) = 1 := by omega
    rw [hone] at hΦtr
    have hΦtr' : Φ ζ' = w - ((n' - 1 : ℕ) : ℂ) := by simpa using hΦtr
    have hsame : F^[n] ζ = F^[(n' - 1)] ζ' :=
      level_point_eq hinj hΦ hζQ hΦζ hwalk hζ'Q hΦtr' hwalktr
    have hstep : F^[n'] ζ' = F (F^[(n' - 1)] ζ') := by
      have hne : n' = (n' - 1) + 1 := by omega
      conv_lhs => rw [hne]
      rw [Function.iterate_succ_apply']
    rw [hstep, ← hsame]
    exact hτ (F^[n] ζ)

end

end Work.Pert
