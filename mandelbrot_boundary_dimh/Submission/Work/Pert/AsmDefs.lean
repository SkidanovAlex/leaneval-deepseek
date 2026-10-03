import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.tools

/-!
# PERT · `Work.Pert.AsmDefs`: the level-defined coordinate `φ_f` and the lifted return map

Language layer for the assembly of `PertData` (Shishikura §4.2).  Given a perturbed germ, its
normal-form data `(σ, u, α)`, the lift `F = liftF u σ α`, a Fatou coordinate `Φ` of `F` on a gate
region `Q` (`MandelDim.IsFatouCoordOn F Φ Q`) and the covering coordinate `τ = tauC σ α`, we define

* `invOn Φ Q w` — a point of `Q` mapping to `w` under `Φ` (junk value `0` if there is none);
* `phiOf F τ Φ Q w` — **`φ_f(w)`**: the value `τ (F^[n] ζ)` at a legal level `(n, ζ)` of `w`
  (well defined thanks to `Work.Pert.level_point_eq`); it is the extension of `τ ∘ Φ⁻¹` to the
  maximal domain `Work.Pert.Dphi F Φ Q` (Shishikura (4.2.1));
* `retOf Φ Q α w` — the lifted return map `R̃_f = Φ ∘ T_f ∘ Φ⁻¹` on `Φ '' Q`, defined through the
  chosen preimage `invOn Φ Q w` and the deck translation `Tt α`.
-/

namespace Work.Pert

open MandelDim Complex Set

noncomputable section

/-! ## A chosen preimage -/

/-- A point of `Q` mapping to `w` under `Φ`; junk value `0` when there is none. -/
def invOn (Φ : ℂ → ℂ) (Q : Set ℂ) (w : ℂ) : ℂ := by
  classical
  exact if h : ∃ ζ ∈ Q, Φ ζ = w then h.choose else 0

theorem invOn_mem {Φ : ℂ → ℂ} {Q : Set ℂ} {w : ℂ} (h : ∃ ζ ∈ Q, Φ ζ = w) :
    invOn Φ Q w ∈ Q := by
  classical
  have h1 : invOn Φ Q w = h.choose := by
    unfold invOn
    rw [dite_eq_left h]
  rw [h1]
  exact h.choose_spec.1

theorem invOn_spec {Φ : ℂ → ℂ} {Q : Set ℂ} {w : ℂ} (h : ∃ ζ ∈ Q, Φ ζ = w) :
    Φ (invOn Φ Q w) = w := by
  classical
  unfold invOn
  rw [dite_eq_left h]
  exact h.choose_spec.2

theorem invOn_eq {Φ : ℂ → ℂ} {Q : Set ℂ} {w ζ : ℂ} (hinj : InjOn Φ Q)
    (h : ∃ ζ ∈ Q, Φ ζ = w) (hζ : ζ ∈ Q) (hΦ : Φ ζ = w) : invOn Φ Q w = ζ :=
  hinj (invOn_mem h) hζ (by rw [invOn_spec h, hΦ])

/-! ## The level-defined coordinate `φ_f` -/

/-- **The coordinate `φ_f` attached to a Fatou coordinate `Φ` of `F` on `Q`**: at a point `w` with a
legal level `(n, ζ)` — `ζ ∈ Q`, `Φ ζ = w - n` and the walk `F^[j] ζ ∈ Q` for `j ≤ n` — the value is
`τ (F^[n] ζ)`.  It is the extension of `τ ∘ Φ⁻¹` to the maximal domain `Dphi F Φ Q`. -/
def phiOf (F τ Φ : ℂ → ℂ) (Q : Set ℂ) (w : ℂ) : ℂ := by
  classical
  exact if h : ∃ (n : ℕ) (ζ : ℂ), ζ ∈ Q ∧ Φ ζ = w - (n : ℂ) ∧
      ∀ j : ℕ, j ≤ n → F^[j] ζ ∈ Q
    then τ (F^[h.choose] h.choose_spec.choose) else 0

/-- **Well-definedness of `φ_f`**: the value at any legal level `(n, ζ)` of `w` is `τ (F^[n] ζ)`. -/
theorem phiOf_eq {F τ Φ : ℂ → ℂ} {Q : Set ℂ} {w : ℂ} {n : ℕ} {ζ : ℂ}
    (hinj : InjOn Φ Q) (hab : ∀ z ∈ Q, F z ∈ Q → Φ (F z) = Φ z + 1)
    (hζ : ζ ∈ Q) (hΦ : Φ ζ = w - (n : ℂ)) (hwalk : ∀ j : ℕ, j ≤ n → F^[j] ζ ∈ Q) :
    phiOf F τ Φ Q w = τ (F^[n] ζ) := by
  classical
  have hex : ∃ (n : ℕ) (ζ : ℂ), ζ ∈ Q ∧ Φ ζ = w - (n : ℂ) ∧ ∀ j : ℕ, j ≤ n → F^[j] ζ ∈ Q :=
    ⟨n, ζ, hζ, hΦ, hwalk⟩
  have hrew : phiOf F τ Φ Q w = τ (F^[hex.choose] hex.choose_spec.choose) := by
    unfold phiOf
    rw [dite_eq_left hex]
  rw [hrew]
  have h2 := hex.choose_spec
  have hsame := level_point_eq hinj hab hζ hΦ hwalk h2.choose_spec.1 h2.choose_spec.2.1
    h2.choose_spec.2.2
  rw [hsame]

/-- The membership form: `w` lies in the maximal domain iff it has a legal level. -/
theorem mem_Dphi_iff {F Φ : ℂ → ℂ} {Q : Set ℂ} {w : ℂ} :
    w ∈ Dphi F Φ Q ↔ ∃ (n : ℕ) (ζ : ℂ), ζ ∈ Q ∧ Φ ζ = w - (n : ℂ) ∧
      ∀ j : ℕ, j ≤ n → F^[j] ζ ∈ Q := Iff.rfl

/-- `phiOf` is the value of `τ ∘ Φ⁻¹` where the latter makes sense. -/
theorem phiOf_eq_level {F τ Φ : ℂ → ℂ} {Q : Set ℂ} {ζ : ℂ} (hinj : InjOn Φ Q)
    (hab : ∀ z ∈ Q, F z ∈ Q → Φ (F z) = Φ z + 1) (hζ : ζ ∈ Q) :
    phiOf F τ Φ Q (Φ ζ) = τ ζ := by
  have h0 := phiOf_eq (F := F) (τ := τ) (Φ := Φ) (Q := Q) (w := Φ ζ) (n := 0) (ζ := ζ)
    hinj hab hζ (by simp) (fun j hj => by
      have hj0 : j = 0 := Nat.le_zero.mp hj
      subst hj0; simpa using hζ)
  simpa using h0

/-! ## The lifted return map `R̃_f` -/

/-- The lifted return map `R̃_f = Φ ∘ T_f ∘ Φ⁻¹` attached to a Fatou coordinate `Φ` of `F` on the
gate `Q` and the deck translation `T_f = Tt α`. -/
def retOf (Φ : ℂ → ℂ) (Q : Set ℂ) (α w : ℂ) : ℂ := Φ (Tt α (invOn Φ Q w))

/-- On `Φ '' Q` the return map is the conjugate of the deck translation. -/
theorem retOf_eq {Φ : ℂ → ℂ} {Q : Set ℂ} {α w ζ : ℂ} (hinj : InjOn Φ Q)
    (h : ∃ z ∈ Q, Φ z = w) (hζ : ζ ∈ Q) (hΦ : Φ ζ = w) :
    retOf Φ Q α w = Φ (Tt α ζ) := by
  simp only [retOf, invOn_eq hinj h hζ hΦ]

end

end Work.Pert
