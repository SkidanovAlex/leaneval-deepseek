import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.ValMinAbs
import Submission.Work.BoseB7AK.LatBox.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7AK.LatBox.kmom_rows` — the concrete box's momentum map, proved

The four rows stated in `Submission/Work/BoseB7AK/LatBox/Defs.lean` for the
concrete truncated dual-lattice box `Mode = Fin 3 → ZMod n` (`n` odd) with
`kmom i = ℓ⁻¹ • (2π · (i μ).valMinAbs)_μ`:

* `kmom (-i) = -kmom i`;
* `kmom` is injective;
* `Work.BoseK15.OnDualLattice ℓ kmom`;
* additivity (no wrap) of `kmom` at a pair `(i,j)` whose representatives satisfy
  `((i μ).valMinAbs - (j μ).valMinAbs) * 2 ∈ Ioc (-n) n`, and its clean
  sufficient form `2 (C₁ + C₂) ≤ n` from `|(i μ).valMinAbs| ≤ C₁`,
  `|(j μ).valMinAbs| ≤ C₂`.

Everything is coordinatewise: `ZMod.valMinAbs` is a section of `ℤ → ZMod n` with
`valMinAbs_spec` (`x.valMinAbs = y ↔ x = ↑y ∧ y * 2 ∈ Ioc (-n) n`), and the
oddness of `n` enters exactly twice — to make `2 * a.val ≠ n` (so that negation
commutes with `valMinAbs`) and to rule out the boundary value `-n` in the
no-wrap condition.
-/

namespace Work.BoseB7AK.LatBox

/-- **Negation commutes with `ZMod.valMinAbs` for odd `n`.**  The element `a` is
its own negative only if `2 * a.val = n`, which is impossible for odd `n`; hence
`-a.valMinAbs` is the smallest-absolute-value representative of `-a`
(`ZMod.valMinAbs_spec`, whose `Ioc` condition is the negative of the one for
`a.valMinAbs`). -/
lemma valMinAbs_neg_of_odd {n : ℕ} [NeZero n] (hn : Odd n) (a : ZMod n) :
    (-a).valMinAbs = -a.valMinAbs := by
  rw [ZMod.valMinAbs_spec]
  refine ⟨by push_cast; ring, ?_⟩
  obtain ⟨k, hk⟩ := hn
  have h := a.valMinAbs_mem_Ioc
  simp only [Set.mem_Ioc] at h ⊢
  constructor <;> omega

/-- **`valMinAbs` is additive when the representatives do not wrap**:
`(a - b).valMinAbs = a.valMinAbs - b.valMinAbs` as soon as the difference of the
representatives lies in the fundamental domain `(-n, n]`
(immediate from `ZMod.valMinAbs_spec`: both `a - b` and `↑(a.valMinAbs - b.valMinAbs)`
are `a - b` in `ZMod n`). -/
lemma valMinAbs_sub_of_mem {n : ℕ} [NeZero n] {a b : ZMod n}
    (h : (a.valMinAbs - b.valMinAbs) * 2 ∈ Set.Ioc (-(n : ℤ)) n) :
    (a - b).valMinAbs = a.valMinAbs - b.valMinAbs := by
  rw [ZMod.valMinAbs_spec]
  refine ⟨?_, h⟩
  push_cast
  ring

/-- **The no-wrap condition from explicit bounds on the representatives.**  If
`|a| ≤ C₁`, `|b| ≤ C₂` and `2 (C₁ + C₂) ≤ n`, then `2 (a - b) ∈ (-n, n]`: the
upper bound and the weak lower bound are the triangle inequality, and the strict
lower bound uses that `2 (a - b)` is even while `n` (hence `-n`) is odd. -/
lemma mem_Ioc_of_abs_le {n : ℕ} (hn : Odd n) {a b : ℤ} {C₁ C₂ : ℝ}
    (h₁ : |((a : ℤ) : ℝ)| ≤ C₁) (h₂ : |((b : ℤ) : ℝ)| ≤ C₂)
    (hC : 2 * (C₁ + C₂) ≤ (n : ℝ)) :
    (a - b) * 2 ∈ Set.Ioc (-(n : ℤ)) n := by
  have h1 := abs_le.mp h₁
  have h2 := abs_le.mp h₂
  rw [Set.mem_Ioc]
  refine ⟨?_, ?_⟩
  · have hle : -(n : ℤ) ≤ (a - b) * 2 := by
      have : (-(n : ℝ)) ≤ (((a - b) * 2 : ℤ) : ℝ) := by
        push_cast
        nlinarith [h1.1, h2.2, hC]
      exact_mod_cast this
    have hne : (a - b) * 2 ≠ -(n : ℤ) := by
      intro heq
      obtain ⟨k, hk⟩ := hn
      omega
    omega
  · have : (((a - b) * 2 : ℤ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      nlinarith [h1.2, h2.1, hC]
    exact_mod_cast this

/-- **`kmom` is injective**: the coordinates determine the representatives
`(i μ).valMinAbs`, and `ZMod.valMinAbs` is injective. -/
lemma kmom_injective {n : ℕ} [NeZero n] {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Function.Injective (kmom n ℓ) := by
  intro i j hij
  funext μ
  have h1 : (kmom n ℓ i).ofLp μ = (kmom n ℓ j).ofLp μ := by rw [hij]
  rw [kmom_apply, kmom_apply] at h1
  have hℓne : ℓ⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hℓ)
  have h2 : 2 * Real.pi * ((i μ).valMinAbs : ℝ) = 2 * Real.pi * ((j μ).valMinAbs : ℝ) :=
    mul_left_cancel₀ hℓne h1
  have h3 : ((i μ).valMinAbs : ℝ) = ((j μ).valMinAbs : ℝ) :=
    mul_left_cancel₀ (by positivity : (2 : ℝ) * Real.pi ≠ 0) h2
  exact ZMod.injective_valMinAbs (Int.cast_injective h3)

theorem kmom_rows {n : ℕ} [NeZero n] (hn : Odd n) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∀ i : Fin 3 → ZMod n, Work.BoseB7AK.LatBox.kmom n ℓ (-i) = -Work.BoseB7AK.LatBox.kmom n ℓ i)
    ∧ Function.Injective (Work.BoseB7AK.LatBox.kmom n ℓ)
    ∧ Work.BoseK15.OnDualLattice ℓ (Work.BoseB7AK.LatBox.kmom n ℓ)
    ∧ (∀ i j : Fin 3 → ZMod n,
        (∀ μ : Fin 3, (((i μ).valMinAbs - (j μ).valMinAbs) * 2 ∈ Set.Ioc (-(n : ℤ)) n)) →
        Work.BoseB7AK.LatBox.kmom n ℓ (i - j)
          = Work.BoseB7AK.LatBox.kmom n ℓ i - Work.BoseB7AK.LatBox.kmom n ℓ j)
    ∧ (∀ (C₁ C₂ : ℝ) (i j : Fin 3 → ZMod n),
        (∀ μ : Fin 3, |((((i μ).valMinAbs : ℤ) : ℝ))| ≤ C₁) →
        (∀ μ : Fin 3, |((((j μ).valMinAbs : ℤ) : ℝ))| ≤ C₂) →
        2 * (C₁ + C₂) ≤ (n : ℝ) →
        Work.BoseB7AK.LatBox.kmom n ℓ (i - j)
          = Work.BoseB7AK.LatBox.kmom n ℓ i - Work.BoseB7AK.LatBox.kmom n ℓ j) := by
  -- the coordinatewise additivity: the whole content of the two additivity rows
  have hD : ∀ {i j : Fin 3 → ZMod n},
      (∀ μ : Fin 3, ((i μ).valMinAbs - (j μ).valMinAbs) * 2 ∈ Set.Ioc (-(n : ℤ)) n) →
      kmom n ℓ (i - j) = kmom n ℓ i - kmom n ℓ j := by
    intro i j h
    ext μ
    rw [WithLp.ofLp_sub, Pi.sub_apply]
    rw [kmom_apply, kmom_apply, kmom_apply]
    rw [Pi.sub_apply, valMinAbs_sub_of_mem (h μ)]
    push_cast
    ring
  refine ⟨?_, kmom_injective hℓ, ?_, fun i j h => hD h, ?_⟩
  · intro i
    ext μ
    rw [WithLp.ofLp_neg, kmom_apply, Pi.neg_apply, Pi.neg_apply, kmom_apply,
      valMinAbs_neg_of_odd hn]
    push_cast
    ring
  · refine ⟨kmom_injective hℓ, fun i => ⟨fun μ => (i μ).valMinAbs, ?_⟩⟩
    ext μ
    simp [kmom, Work.BoseB4.vec]
  · intro C₁ C₂ i j h₁ h₂ hC
    exact hD fun μ => mem_Ioc_of_abs_le hn (h₁ μ) (h₂ μ) hC

end Work.BoseB7AK.LatBox
