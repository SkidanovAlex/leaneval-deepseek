import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic

/-! # L62 assembly layer: the chain predicate of Shishikura's Lemma 6.2

`Work.L62.IsChain` bundles the concluding conjunction of `L62Statement`, so that the
construction of the discs `W j` (the paper's §6, Step 2) can be split into lemmas about a
chain.  See `Submission/Work/L62/NOTES_L62.md` for the plan and the refereeing analysis.
-/

namespace Work.L62

open MandelDim Set Metric Filter Topology

open Work.Horn.MandelDim


open Work.Horn.MandelDim

noncomputable section

/-- The chain data of Lemma 6.2's conclusion: discs `W j` pulled back by `ĥ = R - β`.

This is exactly the concluding conjunction of `L62Statement`, bundled so that the construction
can be split into lemmas about a chain. -/
structure IsChain (R : ℂ → ℂ) (β : ℂ) (DR : Set ℂ) (ζa ζb : ℂ) (ρ : ℝ) (s : ℝ)
    (C₀ C₁ C₁' : ℝ) (W : ℕ → Set ℂ) : Prop where
  sign : s = 1 ∨ s = -1
  base : W 0 = ball ζa ρ ∨ W 0 = ball ζb ρ
  open_conn : ∀ j, IsOpen (W j) ∧ IsConnected (W j)
  chain : ∀ j, W (j + 1) ⊆ DR ∧ InjOn (fun w => R w - β) (W (j + 1)) ∧
    (fun w => R w - β) '' W (j + 1) = W j
  disjoint : ∀ i j, i ≠ j → Disjoint (piExp '' W i) (piExp '' W j)
  marching : ∀ M : ℝ, ∃ J : ℕ, ∀ j, J ≤ j → ∀ w ∈ W j, M < s * w.im
  bounded : ∀ j, Bornology.IsBounded (W j) ∧ Metric.diam (W j) < 1 / 2
  close : ∀ j, ∃ u ∈ W j, ∃ u' ∈ W (j + 1), ‖u - u'‖ < C₀
  deriv_bd : ∀ j, ∀ w ∈ W j, C₁ < ‖deriv ((fun u => R u - β)^[j]) w‖ ∧
    ‖deriv ((fun u => R u - β)^[j]) w‖ < C₁'

/-- `ĥ = R - β` is `T`-equivariant whenever `R` is. -/
theorem isTEquivariantOn_sub {R : ℂ → ℂ} {DR : Set ℂ} {β : ℂ} (h : IsTEquivariantOn R DR) :
    IsTEquivariantOn (fun w => R w - β) DR :=
  ⟨h.1, fun w hw => by
    have hw' : R (w + 1) = R w + 1 := h.2 w hw
    show R (w + 1) - β = R w - β + 1
    rw [hw']
    ring⟩

/-- The perturbed map `ĥ = R - β` pushes down to `e^{-2πiβ}` times the pushdown of `R`. -/
theorem pushdown_sub (R : ℂ → ℂ) (β ζ : ℂ) :
    pushdown (fun w => R w - β) ζ = piExp (-β) * pushdown R ζ := by
  rcases eq_or_ne ζ 0 with rfl | hζ
  · simp [pushdown_zero]
  · rw [pushdown_of_ne _ hζ, pushdown_of_ne _ hζ]
    simp only [piExp]
    rw [← Complex.exp_add]
    congr 1
    ring

/-- The maps `ĥ^[j]` map `W j` onto `W 0`. -/
theorem IsChain.image_iterate {R : ℂ → ℂ} {β : ℂ} {DR : Set ℂ} {ζa ζb : ℂ} {ρ s C₀ C₁ C₁' : ℝ}
    {W : ℕ → Set ℂ} (h : IsChain R β DR ζa ζb ρ s C₀ C₁ C₁' W) (j : ℕ) :
    (fun u => R u - β)^[j] '' W j = W 0 := by
  induction j with
  | zero => simp
  | succ n ih =>
      have hstep : (fun u => R u - β) '' W (n + 1) = W n := (h.chain n).2.2
      have h1 : (fun u => R u - β)^[n + 1] '' W (n + 1)
          = (fun u => R u - β)^[n] '' W n := by
        rw [Function.iterate_succ, Set.image_comp, hstep]
      rw [h1, ih]

/-- The maps `ĥ^[j]` are injective on `W j`. -/
theorem IsChain.injOn_iterate {R : ℂ → ℂ} {β : ℂ} {DR : Set ℂ} {ζa ζb : ℂ} {ρ s C₀ C₁ C₁' : ℝ}
    {W : ℕ → Set ℂ} (h : IsChain R β DR ζa ζb ρ s C₀ C₁ C₁' W) (j : ℕ) :
    InjOn (fun u => R u - β)^[j] (W j) := by
  induction j with
  | zero => exact injOn_id _
  | succ n ih =>
      have hstep : InjOn (fun u => R u - β) (W (n + 1)) := (h.chain n).2.1
      have hmap : MapsTo (fun u => R u - β) (W (n + 1)) (W n) := by
        intro w hw
        rw [← (h.chain n).2.2]
        exact mem_image_of_mem _ hw
      have hcomp : InjOn ((fun u => R u - β)^[n] ∘ (fun u => R u - β)) (W (n + 1)) :=
        ih.comp hstep hmap
      simpa [Function.iterate_succ] using hcomp

/-- The members of `W (j+1)` lie in the domain `DR` of `ĥ`. -/
theorem IsChain.W_succ_subset_DR {R : ℂ → ℂ} {β : ℂ} {DR : Set ℂ} {ζa ζb : ℂ} {ρ s C₀ C₁ C₁' : ℝ}
    {W : ℕ → Set ℂ} (h : IsChain R β DR ζa ζb ρ s C₀ C₁ C₁' W) (j : ℕ) :
    W (j + 1) ⊆ DR := (h.chain j).1

/-- For `j ≥ 1` all discs lie in `DR`. -/
theorem IsChain.W_subset_DR {R : ℂ → ℂ} {β : ℂ} {DR : Set ℂ} {ζa ζb : ℂ} {ρ s C₀ C₁ C₁' : ℝ}
    {W : ℕ → Set ℂ} (h : IsChain R β DR ζa ζb ρ s C₀ C₁ C₁' W) {j : ℕ} (hj : 1 ≤ j) :
    W j ⊆ DR := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  exact h.W_succ_subset_DR k

/-- `ĥ^[j]` maps `W j` into `W 0` (the forward form of `image_iterate`). -/
theorem IsChain.iterate_mem {R : ℂ → ℂ} {β : ℂ} {DR : Set ℂ} {ζa ζb : ℂ} {ρ s C₀ C₁ C₁' : ℝ}
    {W : ℕ → Set ℂ} (h : IsChain R β DR ζa ζb ρ s C₀ C₁ C₁' W) {j : ℕ} {w : ℂ}
    (hw : w ∈ W j) : (fun u => R u - β)^[j] w ∈ W 0 := by
  rw [← h.image_iterate j]
  exact mem_image_of_mem _ hw

/-- The images `W j` are `π`-disjoint from `W 0` for `j ≥ 1` when `W 0` misses the
`π`-image of the tail: the statement form used in the disjointness step. -/
theorem IsChain.disjoint_zero {R : ℂ → ℂ} {β : ℂ} {DR : Set ℂ} {ζa ζb : ℂ} {ρ s C₀ C₁ C₁' : ℝ}
    {W : ℕ → Set ℂ} (h : IsChain R β DR ζa ζb ρ s C₀ C₁ C₁' W) {j : ℕ} (hj : j ≠ 0) :
    Disjoint (piExp '' W 0) (piExp '' W j) :=
  h.disjoint 0 j (fun h0 => hj h0.symm)

end

end Work.L62
