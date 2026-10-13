import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilE7.cells
import Submission.Work.WilE7.band_preconn
import Submission.Work.WilE7.singleton_cylDecomp
import Submission.Work.WilE7.PCDefs
import Submission.Work.WilE7.isLocPC_band

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesDesign WilkiesDesign.E

/-!
## Cylindrical cells are locally preconnected

A cell of the frozen decomposition `WilkiesDesign.IsCell` is `ℝ⁰`, a graph over a cell, or a
band between two continuous `EReal`-valued functions over a cell.  Reading the three
constructors top down, `A ⊆ ℝⁿ` is obtained from a base cell `C ⊆ ℝⁿ⁻¹` by either taking a
graph (a homeomorphic copy of `C`) or a band (the region between two graphs).  Around a point
`c ∈ A`, with base point `x₀ = Fin.init c`, that description makes `A` look like the product
of a small piece of `C` with an interval in the last coordinate, and this persists inside any
prescribed open neighbourhood `W ∋ c` because the boundary functions are continuous on `C`.

This is exactly the induction below.  The base case `ℝ⁰` is a subsingleton; the graph step
`isLocPC_graph` pulls a neighbourhood of `x₀` in `C` back along `x ↦ Fin.snoc x (f x)`; and
the band step `Work.WilE7.isLocPC_band` (proved in `Submission/Work/WilE7/isLocPC_band.lean`)
cuts a finite vertical window `(t₀ - δ, t₀ + δ)` out of the (possibly unbounded) fibre, using
the two elementary facts about the extended reals `exists_lt_coe_sub` and `exists_coe_add_lt`
from `PCDefs`.
-/

/-- The zeroth-dimensional cell `ℝ⁰` is locally preconnected: it is a subsingleton, so every
subset is preconnected. -/
theorem isLocPC_univ : IsLocPC (Set.univ : Set (Fin 0 → ℝ)) := by
  intro c hc W hW hcW
  refine ⟨W, hW, hcW, subset_rfl, ?_⟩
  exact Set.Subsingleton.isPreconnected (fun a _ b _ => funext (fun i => Fin.elim0 i))

/-- The graph step: if the base cell `C` is locally preconnected then so is the graph of a
function continuous on `C`.  Concretely, given a point `c = Fin.snoc x₀ (f x₀)` and an open
`W ∋ c`, continuity of `x ↦ Fin.snoc x (f x)` on `C` produces an open `V₀ ∋ x₀` with
`V₀ ∩ C ⊆ Φ ⁻¹' W`; applying `IsLocPC C` inside `V₀` gives an open `V₁ ∋ x₀` with
`V₁ ∩ C` preconnected, and then `V := {z | Fin.init z ∈ V₁} ∩ ball c ε` is open, contains
`c`, lies in `W`, and satisfies `V ∩ A = Φ '' (V₁ ∩ C)`, a continuous image of a
preconnected set. -/
theorem isLocPC_graph {n : ℕ} {C : Set (Fin n → ℝ)} (hC : IsLocPC C)
    (f : (Fin n → ℝ) → ℝ) (hf : ContinuousOn f C) :
    IsLocPC {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)} := by
  intro c hc W hW hcW
  obtain ⟨hx₀C, hlast⟩ := hc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW c hcW
  set Φ : (Fin n → ℝ) → (Fin (n + 1) → ℝ) := fun x => Fin.snoc x (f x) with hΦdef
  have hΦ : ContinuousOn Φ C := by
    rw [hΦdef]
    exact ContinuousOn.finSnoc (X := fun _ => ℝ) continuousOn_id hf
  have hΦc : Φ (Fin.init c) = c := by
    rw [hΦdef]
    show Fin.snoc (Fin.init c) (f (Fin.init c)) = c
    rw [← hlast]
    exact Fin.snoc_init_self c
  have hpre : Φ ⁻¹' Metric.ball c ε ∈ nhdsWithin (Fin.init c) C :=
    (hΦ.continuousWithinAt hx₀C).preimage_mem_nhdsWithin
      (by rw [hΦc]; exact Metric.ball_mem_nhds c hε)
  obtain ⟨u, hu, huc⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre
  obtain ⟨ε', hε', hball'⟩ := Metric.mem_nhds_iff.mp hu
  obtain ⟨V₁, hV₁open, hx₀V₁, hV₁sub, hV₁pc⟩ :=
    hC (Fin.init c) hx₀C (Metric.ball (Fin.init c) ε') Metric.isOpen_ball (Metric.mem_ball_self hε')
  refine ⟨{z : Fin (n + 1) → ℝ | Fin.init z ∈ V₁} ∩ Metric.ball c ε, ?_, ?_, ?_, ?_⟩
  · exact (hV₁open.preimage (Continuous.finInit continuous_id)).inter Metric.isOpen_ball
  · exact ⟨by simpa using hx₀V₁, Metric.mem_ball_self hε⟩
  · intro z hz
    exact hball hz.2
  · have himg : ({z : Fin (n + 1) → ℝ | Fin.init z ∈ V₁} ∩ Metric.ball c ε) ∩
        {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)}
        = Φ '' (V₁ ∩ C) := by
      ext z
      constructor
      · rintro ⟨⟨hz1, hz2⟩, hzC, hzlast⟩
        refine ⟨Fin.init z, ⟨by simpa using hz1, hzC⟩, ?_⟩
        rw [hΦdef]
        show Fin.snoc (Fin.init z) (f (Fin.init z)) = z
        rw [← hzlast]
        exact Fin.snoc_init_self z
      · rintro ⟨x, ⟨hxV₁, hxC⟩, hxz⟩
        have hxV₀ : x ∈ Metric.ball (Fin.init c) ε' := hV₁sub hxV₁
        have hxU : x ∈ u := hball' hxV₀
        have hballz : Φ x ∈ Metric.ball c ε := huc ⟨hxU, hxC⟩
        have hinit : Fin.init (Φ x) = x := by
          rw [hΦdef]
          simp
        have hlastz : (Φ x) (Fin.last n) = f (Fin.init (Φ x)) := by
          rw [hinit, hΦdef]
          simp
        rw [← hxz]
        exact ⟨⟨by show Fin.init (Φ x) ∈ V₁; rw [hinit]; exact hxV₁, hballz⟩,
          by show Fin.init (Φ x) ∈ C; rw [hinit]; exact hxC, hlastz⟩
    rw [himg]
    exact hV₁pc.image Φ (hΦ.mono Set.inter_subset_right)

/-- Every cylindrical cell is locally preconnected at each of its points: it is a subsingleton
in dimension `0`, a graph in the graph case, and a band in the band case. -/
theorem isCell_localPreconnected {n : ℕ} {A : Set (Fin n → ℝ)} (hA : WilkiesDesign.IsCell n A) :
    ∀ c ∈ A, ∀ W : Set (Fin n → ℝ), IsOpen W → c ∈ W →
      ∃ V : Set (Fin n → ℝ), IsOpen V ∧ c ∈ V ∧ V ⊆ W ∧ IsPreconnected (V ∩ A) := by
  show IsLocPC A
  induction hA with
  | zero => exact isLocPC_univ
  | graph hC f hf ih => exact isLocPC_graph ih f hf
  | band hC a b ha hb hab ih => exact isLocPC_band ih a b ha hb

end Work.WilE7
