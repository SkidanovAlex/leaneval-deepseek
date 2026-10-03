import Mathlib

namespace Work.Pert

/-!
# A geometric sum over a separated (downward) family

`Work.Pert.lc_geom_inj_sum`.

Let `s : Finset ℕ` be a finite set of indices, `u : ℕ → ℝ` a sequence, and let `a γ : ℝ`
with `γ > 0`.  Assume

* `u j > a` for every `j ∈ s`, and
* `u` decreases by at least `γ` when the index increases: `j < j'` in `s` forces
  `u j ≥ u j' + γ`.

Then `∑_{j ∈ s} exp (-2π (u j - a)) ≤ 1 + 1/(2πγ)`.

The proof writes `f j = exp (-2π (u j - a))` and `r = exp (-2πγ) ∈ (0,1)`.  The separation
hypothesis in this form is exactly `f j ≤ r · f j'` whenever `j < j'` in `s`.  The key
observation is the strengthened induction on the (finite) index set: with `m = max s`,

  `∑_{j ∈ s} f j ≤ f m / (1 - r)`,

because deleting the *largest* index `c` of `s` leaves a smaller set `t` whose maximum `M`
satisfies `M < c`, hence `f M ≤ r · f c`, while the induction hypothesis bounds `∑_{j ∈ t} f j`
by `f M/(1-r)`; the two combine as `f c + r·f c/(1-r) = f c/(1-r)`.  The max-deletion step is
`Finset.induction_on_max`, which inserts the new element strictly above all others.

Finally `f m ≤ 1` (as `u m > a`) and `1/(1-r) ≤ 1 + 1/(2πγ)`, the latter being the elementary
inequality `(x+1) e^{-x} ≤ 1 ⇔ x + 1 ≤ e^x` for `x = 2πγ > 0`.
-/

theorem lc_geom_inj_sum {u : ℕ → ℝ} {a γ : ℝ} (hγ : 0 < γ) {s : Finset ℕ}
    (hb : ∀ j ∈ s, a < u j)
    (hsep : ∀ j ∈ s, ∀ j' ∈ s, j < j' → u j ≥ u j' + γ) :
    ∑ j ∈ s, Real.exp (-(2 * Real.pi * (u j - a))) ≤ 1 + 1 / (2 * Real.pi * γ) := by
  classical
  -- Abbreviations: the summand `f` and the geometric ratio `r`.
  set f : ℕ → ℝ := fun j => Real.exp (-(2 * Real.pi * (u j - a))) with hf
  set r : ℝ := Real.exp (-(2 * Real.pi * γ)) with hr
  have hrpos : 0 < r := by rw [hr]; exact Real.exp_pos _
  have hrlt : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    have : 0 < 2 * Real.pi * γ := by positivity
    linarith
  have h1r : 0 < 1 - r := by linarith
  have hfpos : ∀ j, 0 < f j := by intro j; rw [hf]; exact Real.exp_pos _
  -- The separation hypothesis is exactly contraction by the ratio `r`.
  have hstep : ∀ j j' : ℕ, u j ≥ u j' + γ → f j ≤ r * f j' := by
    intro j j' h
    simp only [hf, hr]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [h, Real.pi_pos]
  -- Strengthened induction on the index set, deleting its maximum.
  have key : ∀ t : Finset ℕ,
      (∀ j ∈ t, a < u j) → (∀ j ∈ t, ∀ j' ∈ t, j < j' → u j ≥ u j' + γ) →
      ∀ m ∈ t, (∀ j ∈ t, j ≤ m) → ∑ j ∈ t, f j ≤ f m / (1 - r) := by
    intro t
    induction t using Finset.induction_on_max with
    | empty =>
      intro _ _ m hm _
      simp at hm
    | insert c t hlt ih =>
      intro hb' hsep' m hm hmax
      -- `c` is strictly larger than everything in `t`, and is an upper bound of `t`;
      -- since `m` is an upper bound too and `m ∈ insert c t`, necessarily `m = c`.
      have hcm : c ≤ m := hmax c (Finset.mem_insert_self c t)
      have hm_eq : m = c := by
        rcases Finset.mem_insert.mp hm with h | h
        · exact h
        · exact absurd (hlt m h) (not_lt.mpr hcm)
      rw [hm_eq]
      have hct : c ∉ t := fun hc => absurd (hlt c hc) (lt_irrefl c)
      rw [Finset.sum_insert hct]
      rcases t.eq_empty_or_nonempty with ht | ht
      · -- `t = ∅`: only the `f c` term remains, and `1/(1-r) ≥ 1`.
        subst ht
        rw [Finset.sum_empty, add_zero]
        rw [le_div_iff₀ h1r]
        nlinarith [hfpos c, hrpos]
      · -- `t ≠ ∅`: apply the induction hypothesis at `M = max t < c`.
        have hMem : t.max' ht ∈ t := t.max'_mem ht
        have hMc : t.max' ht < c := hlt _ hMem
        have ihM := ih (fun j hj => hb' j (Finset.mem_insert.mpr (Or.inr hj)))
          (fun j hj j' hj' hjj' =>
            hsep' j (Finset.mem_insert.mpr (Or.inr hj)) j' (Finset.mem_insert.mpr (Or.inr hj')) hjj')
          (t.max' ht) hMem (fun j hj => Finset.le_max' t j hj)
        have huj : u (t.max' ht) ≥ u c + γ :=
          hsep' (t.max' ht) (Finset.mem_insert.mpr (Or.inr hMem)) c (Finset.mem_insert_self c t) hMc
        have hstepM : f (t.max' ht) ≤ r * f c := hstep _ _ huj
        calc f c + ∑ j ∈ t, f j
            ≤ f c + f (t.max' ht) / (1 - r) := add_le_add (le_refl _) ihM
          _ ≤ f c + r * f c / (1 - r) :=
              add_le_add (le_refl _) (div_le_div_of_nonneg_right hstepM h1r.le)
          _ = f c / (1 - r) := by
              field_simp
              ring
  rcases s.eq_empty_or_nonempty with hs | hs
  · -- `s = ∅` is trivial.
    subst hs
    simp only [Finset.sum_empty]
    positivity
  · -- Otherwise bound by `f (max s) / (1 - r) ≤ 1/(1-r)` and close with the elementary estimate.
    have hkey := key s hb hsep (s.max' hs) (s.max'_mem hs) (fun j hj => Finset.le_max' s j hj)
    have hfmax : f (s.max' hs) ≤ 1 := by
      rw [hf, Real.exp_le_one_iff]
      have hp := Real.pi_pos
      have hu := hb (s.max' hs) (s.max'_mem hs)
      nlinarith
    have hnum : 1 / (1 - r) ≤ 1 + 1 / (2 * Real.pi * γ) := by
      rw [hr]
      have hx : 0 < 2 * Real.pi * γ := by positivity
      have hrlt' : Real.exp (-(2 * Real.pi * γ)) < 1 := by
        rw [Real.exp_lt_one_iff]
        linarith
      have h1r' : 0 < 1 - Real.exp (-(2 * Real.pi * γ)) := by linarith
      -- `(x + 1) e^{-x} ≤ 1`, from `x + 1 ≤ e^x`.
      have hbnd : (2 * Real.pi * γ + 1) * Real.exp (-(2 * Real.pi * γ)) ≤ 1 := by
        calc (2 * Real.pi * γ + 1) * Real.exp (-(2 * Real.pi * γ))
            ≤ Real.exp (2 * Real.pi * γ) * Real.exp (-(2 * Real.pi * γ)) :=
              mul_le_mul_of_nonneg_right (Real.add_one_le_exp _) (Real.exp_pos _).le
          _ = Real.exp (2 * Real.pi * γ + -(2 * Real.pi * γ)) := by rw [Real.exp_add]
          _ = 1 := by simp
      rw [div_le_iff₀ h1r']
      have hxne : (2 * Real.pi * γ) ≠ 0 := ne_of_gt hx
      have hsplit : (1 + 1 / (2 * Real.pi * γ)) * (1 - Real.exp (-(2 * Real.pi * γ)))
          = ((2 * Real.pi * γ + 1) * (1 - Real.exp (-(2 * Real.pi * γ)))) / (2 * Real.pi * γ) := by
        rw [one_add_div (a := 1) (b := 2 * Real.pi * γ) hxne, div_mul_eq_mul_div]
      rw [hsplit, le_div_iff₀ hx]
      nlinarith [hbnd]
    calc ∑ j ∈ s, Real.exp (-(2 * Real.pi * (u j - a)))
        = ∑ j ∈ s, f j := by simp only [hf]
      _ ≤ f (s.max' hs) / (1 - r) := hkey
      _ ≤ 1 / (1 - r) := div_le_div_of_nonneg_right hfmax h1r.le
      _ ≤ 1 + 1 / (2 * Real.pi * γ) := hnum

end Work.Pert
