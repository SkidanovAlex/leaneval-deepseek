import Mathlib

namespace Work.EQ

/-- For a strictly increasing continuous `τ` with fixed points `a < b` and no fixed point
strictly between them, the orbit of any `θ ∈ (a,b)` with `τ θ < θ` decreases to `a`. -/
theorem orbit_tendsto_lower {τ : ℝ → ℝ} (hcont : Continuous τ) (hmono : StrictMono τ)
    {a b : ℝ} (hab : a < b) (ha : τ a = a) (hb : τ b = b)
    (hfix : ∀ x, a < x → x < b → τ x ≠ x)
    {θ : ℝ} (hθa : a < θ) (hθb : θ < b) (hθ : τ θ < θ) :
    Filter.Tendsto (fun n : ℕ => τ^[n] θ) Filter.atTop (nhds a) := by
  have _ := hab
  -- The orbit stays in `(a,b)` and strictly decreases.
  have hmain : ∀ n : ℕ, a < τ^[n] θ ∧ τ^[n] θ < b ∧ τ^[n+1] θ < τ^[n] θ := by
    intro n
    induction n with
    | zero =>
      refine ⟨hθa, hθb, ?_⟩
      simpa using hθ
    | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · calc a = τ a := ha.symm
          _ < τ (τ^[n] θ) := hmono h1
          _ = τ^[n+1] θ := (Function.iterate_succ_apply' τ n θ).symm
      · calc τ^[n+1] θ = τ (τ^[n] θ) := Function.iterate_succ_apply' τ n θ
          _ < τ b := hmono h2
          _ = b := hb
      · calc τ^[n+2] θ = τ (τ^[n+1] θ) := Function.iterate_succ_apply' τ (n+1) θ
          _ < τ (τ^[n] θ) := hmono h3
          _ = τ^[n+1] θ := (Function.iterate_succ_apply' τ n θ).symm
  -- Hence an antitone sequence bounded below by `a`, whose infimum `L` is its limit.
  have hanti : Antitone (fun n : ℕ => τ^[n] θ) :=
    antitone_nat_of_succ_le (fun n => le_of_lt (hmain n).2.2)
  have hbdd : BddBelow (Set.range (fun n : ℕ => τ^[n] θ)) :=
    ⟨a, by rintro x ⟨n, rfl⟩; exact le_of_lt (hmain n).1⟩
  set L : ℝ := ⨅ n, τ^[n] θ with hL
  have hlim : Filter.Tendsto (fun n : ℕ => τ^[n] θ) Filter.atTop (nhds L) :=
    tendsto_atTop_ciInf hanti hbdd
  -- Continuity turns the limit relation `u (n+1) = τ (u n)` into `L = τ L`.
  have hshift : Filter.Tendsto (fun n : ℕ => τ^[n+1] θ) Filter.atTop (nhds L) :=
    (Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => τ^[n] θ) 1).mpr hlim
  have hcontlim : Filter.Tendsto (fun n : ℕ => τ (τ^[n] θ)) Filter.atTop (nhds (τ L)) :=
    (hcont.tendsto L).comp hlim
  have hcontlim' : Filter.Tendsto (fun n : ℕ => τ^[n+1] θ) Filter.atTop (nhds (τ L)) := by
    simpa only [Function.iterate_succ_apply'] using hcontlim
  have hτL : L = τ L := tendsto_nhds_unique hshift hcontlim'
  -- `a ≤ L ≤ θ < b`, and `hfix` forces `L = a`.
  have hLa : a ≤ L := le_ciInf (fun n => le_of_lt (hmain n).1)
  have hLθ : L ≤ θ := by simpa using ciInf_le hbdd 0
  have hLb : L < b := lt_of_le_of_lt hLθ hθb
  have hnot : ¬ a < L := fun h => hfix L h hLb hτL.symm
  have hLeq : L = a := le_antisymm (le_of_not_gt hnot) hLa
  simpa [hLeq] using hlim

end Work.EQ
