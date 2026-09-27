import Mathlib

namespace Work.EQ

theorem norm_apply_zero_le_of_seq_eq {f g : ℂ → ℂ} {t : ℕ → ℂ} {C : ℝ}
    (hg : AnalyticAt ℂ g 0) (hfg : f =ᶠ[nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ] g)
    (ht0 : ∀ n, t n ≠ 0) (ht : Filter.Tendsto t Filter.atTop (nhds (0 : ℂ)))
    (hle : ∀ n, ‖f (t n)‖ ≤ C) : ‖g 0‖ ≤ C := by
  have ht' : Filter.Tendsto t Filter.atTop (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨ht, Filter.Eventually.of_forall (fun n => ht0 n)⟩
  have heq : (f ∘ t) =ᶠ[Filter.atTop] (g ∘ t) := hfg.comp_tendsto ht'
  have hC : ∀ᶠ n in Filter.atTop, ‖g (t n)‖ ≤ C :=
    heq.mono fun n hn => by
      rw [Function.comp_apply, Function.comp_apply] at hn
      rw [← hn]
      exact hle n
  have hlim : Filter.Tendsto (fun n => ‖g (t n)‖) Filter.atTop (nhds ‖g 0‖) :=
    hg.continuousAt.tendsto.norm.comp ht
  exact le_of_tendsto hlim hC

end Work.EQ
