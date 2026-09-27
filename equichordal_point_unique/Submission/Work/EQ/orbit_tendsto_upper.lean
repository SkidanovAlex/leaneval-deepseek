import Mathlib

namespace Work.EQ

/-- **Monotone orbit of a fixed-point-free interval map tends to the upper endpoint.**

Let `τ : ℝ → ℝ` be continuous and strictly increasing with fixed points `a < b` and no fixed
point in the open interval `(a,b)`.  If `a < θ < b` and `θ < τ θ`, then the orbit
`n ↦ τ^[n] θ` increases to `b`.

Indeed, strict monotonicity together with `θ < τ θ` makes the orbit strictly increasing
(each step applies `τ` to the previous inequality), and since `τ b = b` the orbit stays below
`b`.  Being increasing and bounded above it converges to its supremum `L ≤ b`; continuity gives
`τ L = L`, and `L > a` because `L ≥ θ > a`, so `L` cannot lie strictly below `b` — that would be
a fixed point in `(a,b)`.  Hence `L = b`. -/
theorem orbit_tendsto_upper {τ : ℝ → ℝ} (hcont : Continuous τ) (hmono : StrictMono τ)
    {a b : ℝ} (hab : a < b) (ha : τ a = a) (hb : τ b = b)
    (hfix : ∀ x, a < x → x < b → τ x ≠ x)
    {θ : ℝ} (hθa : a < θ) (hθb : θ < b) (hθ : θ < τ θ) :
    Filter.Tendsto (fun n : ℕ => τ^[n] θ) Filter.atTop (nhds b) := by
  -- The orbit is strictly increasing: `τ^[n]θ < τ^[n+1]θ`.
  have hinc : ∀ n : ℕ, τ^[n] θ < τ^[n+1] θ := fun n => by
    have h := (hmono.iterate n) hθ
    simpa [Function.iterate_succ_apply] using h
  -- The orbit stays below the fixed point `b`.
  have hbdd : ∀ n : ℕ, τ^[n] θ ≤ b := by
    intro n
    induction n with
    | zero => simpa using le_of_lt hθb
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        calc τ (τ^[k] θ) ≤ τ b := hmono.monotone ih
          _ = b := hb
  have hmono_u : Monotone (fun n : ℕ => τ^[n] θ) := (strictMono_nat_of_lt_succ hinc).monotone
  have hBdd : BddAbove (Set.range fun n : ℕ => τ^[n] θ) :=
    ⟨b, by rintro _ ⟨n, rfl⟩; exact hbdd n⟩
  -- The orbit converges to its supremum `L`.
  let L : ℝ := ⨆ n : ℕ, τ^[n] θ
  have hL : Filter.Tendsto (fun n : ℕ => τ^[n] θ) Filter.atTop (nhds L) :=
    tendsto_atTop_ciSup hmono_u hBdd
  have hLb : L ≤ b := ciSup_le (fun n => hbdd n)
  have hθL : θ ≤ L := by
    have := le_ciSup (f := fun n : ℕ => τ^[n] θ) hBdd 0
    simpa using this
  -- Continuity turns the limit into a fixed point: `τ L = L`.
  have hτL : τ L = L := by
    have h1 : Filter.Tendsto (fun n : ℕ => τ (τ^[n] θ)) Filter.atTop (nhds (τ L)) :=
      (hcont.tendsto L).comp hL
    have h1' : Filter.Tendsto (fun n : ℕ => τ^[n+1] θ) Filter.atTop (nhds (τ L)) := by
      have heq : (fun n : ℕ => τ (τ^[n] θ)) = (fun n : ℕ => τ^[n+1] θ) := by
        funext n; rw [Function.iterate_succ_apply']
      rwa [heq] at h1
    have h2 : Filter.Tendsto (fun n : ℕ => τ^[n+1] θ) Filter.atTop (nhds L) := by
      have := hL.comp (Filter.tendsto_add_atTop_nat 1)
      simpa [Function.comp_def] using this
    exact tendsto_nhds_unique h1' h2
  -- `L` cannot lie strictly below `b`, since it is `> a` and `(a,b)` has no fixed points.
  have hLnotlt : ¬ L < b := by
    intro hLtb
    exact (hfix L (lt_of_lt_of_le hθa hθL) hLtb) hτL
  have hLb' : L = b := le_antisymm hLb (le_of_not_gt hLnotlt)
  rw [hLb'] at hL
  exact hL

end Work.EQ
