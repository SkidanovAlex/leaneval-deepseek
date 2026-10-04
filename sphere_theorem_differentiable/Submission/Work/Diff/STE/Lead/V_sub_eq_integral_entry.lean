import Mathlib
import Submission.Work.Diff.STE.Lead.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter MeasureTheory
open scoped Interval Topology

namespace Work.Diff.STE.Lead

/-- **Newton–Leibniz for one entry of the matrix-valued ODE.**  If each slice `s ↦ V s y`
(`y ∈ Ω` fixed) has (one-sided, within `Ico 0 τ`) derivative `Φ (y, jetM (V t) y)` and the right
hand side `(σ, y) ↦ Φ (y, jetM (V σ) y)` is continuous on `Ico 0 τ ×ˢ Ω`, then for each entry
`(a,b)` and all `s, t ∈ Ico 0 τ`

`V s y a b - V t y a b = ∫ σ in t..s, Φ (y, jetM (V σ) y) a b`.

This is the entrywise form of `Work.Diff.STE.Lead.V_sub_eq_integral`. -/
theorem V_sub_eq_integral_entry {n : ℕ} {τ : ℝ} {Ω : Set (Fin n → ℝ)}
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (V : ℝ → (Fin n → ℝ) → Work.Diff.STE.Flat.MatC n)
    (heq : ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ y ∈ Ω,
        HasDerivWithinAt (fun s : ℝ => V s y) (Φ (y, Work.Diff.STE.Flat.jetM (V t) y))
          (Set.Ico (0 : ℝ) τ) t)
    (hcont : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => Φ (p.2, Work.Diff.STE.Flat.jetM (V p.1) p.2))
      (Set.Ico (0 : ℝ) τ ×ˢ Ω))
    (a b : Fin n) {s t : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) τ) (ht : t ∈ Set.Ico (0 : ℝ) τ)
    {y : Fin n → ℝ} (hy : y ∈ Ω) :
    V s y a b - V t y a b = ∫ σ in t..s, Φ (y, Work.Diff.STE.Flat.jetM (V σ) y) a b := by
  -- The continuous linear projection onto the `(a,b)`-entry of a matrix.
  let P : Work.Diff.STE.Flat.MatC n →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) b).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => (Fin n → ℂ)) a)
  -- The entrywise derivative, obtained by composing the matrix derivative with `P`.
  have hentry : ∀ x ∈ Set.Ico (0 : ℝ) τ,
      HasDerivWithinAt (fun σ : ℝ => V σ y a b) (Φ (y, Work.Diff.STE.Flat.jetM (V x) y) a b)
        (Set.Ico (0 : ℝ) τ) x := by
    intro x hx
    exact P.hasFDerivAt.hasFDerivWithinAt.comp_hasDerivWithinAt x (heq x hx y hy)
      (Set.mapsTo_univ _ _)
  -- Continuity of the entrywise right hand side, from the joint continuity hypothesis.
  have hGcont : ContinuousOn (fun σ : ℝ => Φ (y, Work.Diff.STE.Flat.jetM (V σ) y) a b)
      (Set.Ico (0 : ℝ) τ) := by
    have h1 : ContinuousOn (fun σ : ℝ => Φ (y, Work.Diff.STE.Flat.jetM (V σ) y))
        (Set.Ico (0 : ℝ) τ) :=
      hcont.comp (continuousOn_id.prodMk continuousOn_const) (fun σ hσ => ⟨hσ, hy⟩)
    exact P.continuous.comp_continuousOn h1
  -- Newton–Leibniz on `[u, v] ⊆ Ico 0 τ`.
  have key : ∀ u v : ℝ, u ∈ Set.Ico (0 : ℝ) τ → v ∈ Set.Ico (0 : ℝ) τ → u ≤ v →
      V v y a b - V u y a b =
        ∫ σ in u..v, Φ (y, Work.Diff.STE.Flat.jetM (V σ) y) a b := by
    intro u v hu hv huv
    have hsub : Set.Icc u v ⊆ Set.Ico (0 : ℝ) τ := fun x hx =>
      ⟨le_trans hu.1 hx.1, lt_of_le_of_lt hx.2 hv.2⟩
    have hcont' : ContinuousOn (fun σ : ℝ => Φ (y, Work.Diff.STE.Flat.jetM (V σ) y) a b)
        (Set.uIcc u v) := by
      rw [Set.uIcc_of_le huv]
      exact hGcont.mono hsub
    have hFV : ContinuousOn (fun σ : ℝ => V σ y a b) (Set.Icc u v) := by
      have hd : DifferentiableOn ℝ (fun σ : ℝ => V σ y a b) (Set.Ico (0 : ℝ) τ) := fun x hx =>
        (hentry x hx).differentiableWithinAt
      exact hd.continuousOn.mono hsub
    -- On the interior of `[u, v]` the point is interior to `Ico 0 τ`, so the derivative within
    -- `Ico 0 τ` is an honest two-sided derivative.
    have hderiv : ∀ x ∈ Set.Ioo u v,
        HasDerivAt (fun σ : ℝ => V σ y a b) (Φ (y, Work.Diff.STE.Flat.jetM (V x) y) a b) x := by
      intro x hx
      have hxJ : x ∈ Set.Ico (0 : ℝ) τ := ⟨le_trans hu.1 (le_of_lt hx.1), lt_trans hx.2 hv.2⟩
      have hnb : Set.Ico (0 : ℝ) τ ∈ 𝓝 x := Filter.mem_of_superset
        (Ioo_mem_nhds (lt_of_le_of_lt hu.1 hx.1) (lt_trans hx.2 hv.2))
        (fun z hz => ⟨le_of_lt hz.1, hz.2⟩)
      exact (hentry x hxJ).hasDerivAt hnb
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv hFV hderiv
      hcont'.intervalIntegrable).symm
  rcases le_total t s with hts | hst
  · exact key t s ht hs hts
  · have h := key s t hs ht hst
    rw [intervalIntegral.integral_symm] at h
    have h2 : V s y a b - V t y a b = -(V t y a b - V s y a b) := by ring
    rw [h2, h, neg_neg]

end Work.Diff.STE.Lead
