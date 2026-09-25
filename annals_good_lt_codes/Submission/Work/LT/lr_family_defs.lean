import Mathlib
import Submission.Work.LT.Defs

/-! # Building blocks for `Work.LT.lr_expander_family`

The expander family produced by `lr_expander_family` is built from the lazy symmetric generating
list of `SL₃(ℤ/p)` together with all words of a fixed length `k`.  This file collects the
definitions shared by `lr_expander_family` and the helper lemmas delegated for it.
-/

namespace Work.LT.RF

/-- Squared `ℓ²` norm of a real function on a finite type. -/
noncomputable def l2 {X : Type*} [Fintype X] (f : X → ℝ) : ℝ := ∑ x, f x ^ 2

/-- Left-averaging walk operator of a list `α : ι → G`. -/
noncomputable def lOp {G : Type*} [Group G] [Fintype G] {ι : Type*} [Fintype ι] (α : ι → G)
    (f : G → ℝ) : G → ℝ :=
  fun x => (∑ a, f (α a * x)) / (Fintype.card ι : ℝ)

/-- Right-averaging walk operator of a list `α : ι → G`. -/
noncomputable def rOp {G : Type*} [Group G] [Fintype G] {ι : Type*} [Fintype ι] (α : ι → G)
    (f : G → ℝ) : G → ℝ :=
  fun x => (∑ a, f (x * α a)) / (Fintype.card ι : ℝ)

/-- The lazy symmetric 48-letter alphabet on 12 generators: two copies of each `g i`, two copies
of each `(g i)⁻¹` and two copies of `1`.  (The identities are what make the walk lazy, hence
positive.) -/
noncomputable def alpha {G : Type*} [Group G] (g : Fin 12 → G) (a : Fin 12 × Bool × Bool) : G :=
  if a.2.1 then (if a.2.2 then g a.1 else (g a.1)⁻¹) else 1

/-- The involution of the alphabet index set that turns every letter into its inverse. -/
noncomputable def eta : (Fin 12 × Bool × Bool) ≃ (Fin 12 × Bool × Bool) :=
  Equiv.prodCongr (Equiv.refl (Fin 12))
    (Equiv.prodCongr (Equiv.refl Bool) (Equiv.swap true false))

/-- `alpha` is inverted by `eta`: the alphabet is closed under taking inverses. -/
lemma alpha_eta {G : Type*} [Group G] (g : Fin 12 → G) (a : Fin 12 × Bool × Bool) :
    alpha g (eta a) = (alpha g a)⁻¹ := by
  obtain ⟨i, b1, b2⟩ := a
  cases b1 <;> cases b2 <;> simp [alpha, eta, Equiv.swap_apply_left, Equiv.swap_apply_right]

/-- Index type of words of length `k` over the alphabet. -/
abbrev wIdx (k : ℕ) : Type := Fin k → Fin 12 × Bool × Bool

/-- Product of the letters of a word, multiplied in reading order. -/
noncomputable def word {G : Type*} [Group G] (g : Fin 12 → G) (k : ℕ) (w : wIdx k) : G :=
  ((List.ofFn w).map (alpha g)).prod

end Work.LT.RF
