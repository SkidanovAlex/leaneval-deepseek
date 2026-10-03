import Mathlib
import Submission.Work.Repel.V10.chain_v9_setup
import Submission.Work.Repel.V10.chain_v9_src
import Submission.Work.Repel.V10.chain_v9_walk
import Submission.Work.Repel.V10.chain_v9_isl
import Submission.Work.Repel.V10.chainV9_cells
import Submission.Work.Repel.V10.Isl_sub_halfball
import Submission.Work.Repel.V10.SrcC_sub_Dflat

/-!
# `Work.Repel.chain_v9_final` : the §6 assembly

From the hypothesis package `Work.Repel.V10` (which is literally the hypothesis list of
`Work.Repel.chain_returns_v9`) we build the `ReturnData` of Shishikura's §6, Step 6:

* `Work.Repel.chainV9_cells` supplies the finite set `S` of cells `(j,k,n)` with
  `|S| ≥ N₀ = η η₁²/(320(C₀+1))`, `W j + k ⊆ Sm1`, `|n| ≤ η/10 + 1` and `1 ≤ j`;
* `Work.Repel.SrcC_uniform_iterate` gives, for each cell, a single iterate `N_q ≥ 1` with
  `f^{N_q} ∘ φ₀ = φ₀ ∘ wOfCell q` on the whole source region `SrcC q`;
* `Work.Repel.Isl_surj`, `Isl_sub_halfball`, `Isl_ball_data`, `Isl_injOn_cell` and `Isl_deriv`
  supply the `hsurj`, `hΩhalf`, `hΩsub`/`hdisj`, `hinj` and `hderiv` fields;
* the `Fin S.card`-indexed family is obtained from `Finset.equivFin`.
-/

set_option linter.style.haveILetI false

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

/-- `N₀` is at least `2`, so the cell set has at least two elements. -/
theorem V10.two_le_N₀ (V : V10) : 2 ≤ V.N₀ := by
  rw [V10.N₀]
  have h1 : (64 : ℝ) * (V.C₀ + 1) ≤ V.η₁ := V.hsize
  have h2 : (0 : ℝ) < V.C₀ + 1 := by linarith [V.hC₀]
  have h3 : (0 : ℝ) < 320 * (V.C₀ + 1) := by positivity
  have hC : (1 : ℝ) ≤ V.C₀ + 1 := by linarith [V.hC₀]
  have hkey : 100 * (64 * (V.C₀ + 1)) ^ 2 ≤ V.η * V.η₁ ^ 2 := by
    nlinarith [V.hη, h1, V.hC₀]
  have h640 : 2 * (320 * (V.C₀ + 1)) ≤ 100 * (64 * (V.C₀ + 1)) ^ 2 := by
    nlinarith [hC, sq_nonneg (V.C₀ + 1)]
  rw [le_div_iff₀ h3]
  linarith

/-- **The §6 assembly, modulo the geometry.**

This is the assembly step of `chain_returns_v9`: given the cell set `S` (`chainV9_cells`), a
uniform iterate `Nf q` of each cell (`SrcC_uniform_iterate`), and the island data

* `hInj q` : injectivity of `f^[Nf q]` on the image of the source region of `q` — the
  conclusion of the missing `Isl_injOn_cell` (see `NOTES_chain_returns_v9_session2.md` §3);
* `u, δ, hδpos, hIsl_ball, hball_cell, hdisjS` — the conclusion of `Isl_ball_data`;
* `hhalf` — `Isl_sub_halfball`;
* `hder` — `Isl_deriv`,

we build the `ReturnData` of Shishikura's §6, Step 6. -/
theorem chain_returns_v9_assembly (V : V10) (S : Finset (ℕ × ℤ × ℤ))
    (Nf : ℕ × ℤ × ℤ → ℕ)
    (hScard : V.N₀ ≤ (S.card : ℝ))
    (hSmS : ∀ q ∈ S, V.fib q.1 q.2.1 ⊆ V.Sm1)
    (hj : ∀ q ∈ S, 1 ≤ q.1)
    (hiter : ∀ q ∈ S, 1 ≤ Nf q ∧ ∀ w ∈ V.SrcC q.1 q.2.1 q.2.2,
      V.f ^[Nf q] (V.P₀.φ w) = V.P₀.φ (V.wOfCell (q.1, q.2.1, q.2.2) w))
    (hInj : ∀ q ∈ S, Set.InjOn (V.f ^[Nf q]) (V.P₀.φ '' V.SrcC q.1 q.2.1 q.2.2))
    (u : ℕ × ℤ × ℤ → ℂ) (δ : ℕ × ℤ × ℤ → ℝ)
    (hδpos : ∀ q ∈ S, 0 < δ q)
    (hIsl_ball : ∀ q ∈ S, V.Isl q.1 q.2.1 q.2.2 ⊆ Metric.ball (u q) (δ q))
    (hball_cell : ∀ q ∈ S, Metric.ball (u q) (δ q) ⊆ V.P₀.φ '' V.SrcC q.1 q.2.1 q.2.2)
    (hdisjS : ∀ q ∈ S, ∀ q' ∈ S, q ≠ q' →
      Disjoint (Metric.ball (u q) (δ q)) (Metric.ball (u q') (δ q')))
    (hhalf : ∀ q ∈ S, V.Isl q.1 q.2.1 q.2.2 ⊆ Metric.ball V.p (V.r / 2))
    (hder : ∀ q ∈ S, ∀ z ∈ V.Isl q.1 q.2.1 q.2.2,
      ‖deriv (V.f ^[Nf q]) z‖ ≤ V.Kmax) :
    ∃ (p : ℂ) (r Kc : ℝ), 0 < r ∧
      (p = 1.05 * Complex.I / V.η ∨ p = -1.05 * Complex.I / V.η) ∧
      ∃ RD : Work.Repel.ReturnData V.f p r Kc, V.N₀ ≤ (RD.N : ℝ) ∧ Kc ≤ V.Kmax := by
  classical
  -- index the cells by `Fin S.card`
  let e : ↥S ≃ Fin S.card := S.equivFin
  let qf : Fin S.card → ℕ × ℤ × ℤ := fun i => (e.symm i : ℕ × ℤ × ℤ)
  have hqf : ∀ i, qf i ∈ S := fun i => (e.symm i).2
  have hqf_inj : Function.Injective qf := fun i j hij => e.symm.injective (Subtype.ext hij)
  let RD : Work.Repel.ReturnData V.f V.p V.r V.Kmax :=
    { N := S.card
      n := fun i => Nf (qf i)
      Ω := fun i => V.Isl (qf i).1 (qf i).2.1 (qf i).2.2
      u := fun i => u (qf i)
      δ := fun i => δ (qf i)
      hN := by
        have h : (2 : ℝ) ≤ (S.card : ℝ) := le_trans (V.two_le_N₀) hScard
        exact_mod_cast h
      hn := fun i => (hiter (qf i) (hqf i)).1
      hδ := fun i => hδpos (qf i) (hqf i)
      hΩsub := fun i => hIsl_ball (qf i) (hqf i)
      hΩhalf := fun i => hhalf (qf i) (hqf i)
      hdisj := fun i j hij =>
        hdisjS (qf i) (hqf i) (qf j) (hqf j) (fun h => hij (hqf_inj h))
      hdiff := fun i => (V.hfdiff.iterate (Nf (qf i))).differentiableOn
      hinj := fun i => (hInj (qf i) (hqf i)).mono (hball_cell (qf i) (hqf i))
      hsurj := fun i =>
        V10.Isl_surj V (hj (qf i) (hqf i)) (hSmS (qf i) (hqf i)) (hiter (qf i) (hqf i)).2
      hderiv := fun i z hz => hder (qf i) (hqf i) z hz }
  exact ⟨V.p, V.r, V.Kmax, V.r_pos, Or.inl rfl, RD, hScard, le_refl _⟩

end

end Work.Repel
