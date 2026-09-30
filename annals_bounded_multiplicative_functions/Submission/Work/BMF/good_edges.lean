import Mathlib
import Submission.Work.BMF.adi_edge_dec
import Submission.Work.BMF.adi_all_defs
import Submission.Work.BMF.walk_closure
import Submission.Work.BMF.degen_closedWalkAll_le
import Submission.Work.BMF.bikeSetAll_bridge
import Submission.Work.BMF.good_bike_aux
import Submission.Work.BMF.adi_graph_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Good edges

The counting step "the good bicycles over a single arc are few": a bicycle is an arc of the
quadruple graph together with one closed walk through each of its endpoints, so the good bicycles
are contained in the disjoint union, over the arcs `e` that actually occur, of the products of the
two sets of closed walks through the endpoints of `e`.  Since the number of closed walks of the
`q`-subgraph through a point is `≪ π₀(P₁)^{2ℓ}/(X/L)` (`Work.BMF.closedWalkVal_card_le`), each
fibre contributes at most `≪ π₀(P₁)^{4ℓ}/(X/L)²`, and the total is at most the number of *distinct*
arcs occurring times that bound.
-/

namespace Work.BMF

open Finset Real

theorem good_edges (k : ℕ) (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    ∃ C P₀ : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ) (c Cq X L P₁ P₂ c₅ δ : ℝ)
      (D : Work.BMF.QuadData k f c Cq X L P₁ P₂) (q : ℕ),
      P₀ ≤ P₁ → 0 < P₁ → 0 < L → 8000 * P₁ ^ 2 < X / L → 3 ≤ X / L →
      X / L ≤ P₁ ^ (ℓ - 1) →
      ((Work.BMF.goodBikeSet D q ℓ (X / L) c₅ δ).card : ℝ) ≤
        C * (((Work.BMF.goodBikeSet D q ℓ (X / L) c₅ δ).image (fun t => t.1)).card : ℝ) *
          Work.BMF.pi0 P₁ ^ (4 * ℓ) / (X / L) ^ 2 := by
  classical
  obtain ⟨Cv, Pv, hCv, hPv, hval⟩ := closedWalkVal_card_le k ℓ hℓ
  refine ⟨Cv * Cv, Pv, by positivity, ?_⟩
  intro f c Cq X L P₁ P₂ c₅ δ D q hP₀ hP₁ hL hbig hN3 hNle
  have hNpos : 0 < X / L := lt_of_lt_of_le (by positivity) hbig.le
  have hX : 0 < X := (div_pos_iff_of_pos_right hL).mp hNpos
  set N0 : ℝ := X / L with hN0
  set s := goodBikeSet D q ℓ (X / L) c₅ δ with hs
  -- the fibre of a bicycle over its arc: the product of the two walk sets at the endpoints
  set F : Edge → Finset ((Fin (ℓ + 1) → GVert D) × (Fin (ℓ + 1) → GVert D)) :=
    fun e => (closedWalkVal D q ℓ e.x₁).product (closedWalkVal D q ℓ e.x₂) with hF
  have hval' : ∀ x : ℝ, ((closedWalkVal D q ℓ x).card : ℝ) ≤ Cv * pi0 P₁ ^ (2 * ℓ) / N0 := by
    intro x
    have h := hval f c Cq X L P₁ P₂ D q x hP₀ hP₁ hL hX hN3 hNle
    rwa [hN0]
  have hKnn : 0 ≤ Cv * pi0 P₁ ^ (2 * ℓ) / N0 := by
    have h0 := hval' 0
    have h00 : (0 : ℝ) ≤ ((closedWalkVal D q ℓ (0 : ℝ)).card : ℝ) := Nat.cast_nonneg _
    linarith
  -- each fibre of the sigma decomposition contributes at most the square of the walk bound
  have hFe : ∀ e : Edge, ((F e).card : ℝ) ≤
      (Cv * pi0 P₁ ^ (2 * ℓ) / N0) * (Cv * pi0 P₁ ^ (2 * ℓ) / N0) := by
    intro e
    have hc : (F e).card =
        (closedWalkVal D q ℓ e.x₁).card * (closedWalkVal D q ℓ e.x₂).card := by
      rw [hF]
      simp only []
      rw [show (closedWalkVal D q ℓ e.x₁).product (closedWalkVal D q ℓ e.x₂)
          = (closedWalkVal D q ℓ e.x₁) ×ˢ (closedWalkVal D q ℓ e.x₂) from rfl,
        Finset.card_product]
    rw [hc, Nat.cast_mul]
    exact mul_le_mul (hval' e.x₁) (hval' e.x₂) (Nat.cast_nonneg _) hKnn
  -- the good bicycles sit inside the sigma over the arcs that actually occur
  have hsub : s ⊆ (s.image (fun t => t.1)).sigma F := by
    rintro ⟨e, W₁, W₂⟩ ht
    have hbike : (⟨e, W₁, W₂⟩ :
        (_ : Edge) × (Fin (ℓ + 1) → GVert D) × (Fin (ℓ + 1) → GVert D)) ∈ bikeSet D q ℓ := by
      have h1 : (⟨e, W₁, W₂⟩ :
          (_ : Edge) × (Fin (ℓ + 1) → GVert D) × (Fin (ℓ + 1) → GVert D)) ∈
          goodBikeSet D q ℓ (X / L) c₅ δ := by rwa [← hs]
      rw [goodBikeSet] at h1
      exact Finset.mem_of_mem_filter _ h1
    rw [bikeSet, Finset.mem_sigma] at hbike
    obtain ⟨-, hW⟩ := hbike
    rw [Finset.mem_sigma]
    exact ⟨Finset.mem_image_of_mem _ ht, by simpa only [hF] using hW⟩
  have hcard : ((s.card : ℝ)) ≤ ∑ e ∈ s.image (fun t => t.1), ((F e).card : ℝ) := by
    calc ((s.card : ℝ)) ≤ (((s.image (fun t => t.1)).sigma F).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ = ∑ e ∈ s.image (fun t => t.1), ((F e).card : ℝ) := by
          rw [Finset.card_sigma, Nat.cast_sum]
  have hpow : (pi0 P₁ ^ (2 * ℓ) : ℝ) ^ 2 = pi0 P₁ ^ (4 * ℓ) := by
    rw [← pow_mul]; congr 1; ring
  have hKK : (Cv * pi0 P₁ ^ (2 * ℓ) / N0) * (Cv * pi0 P₁ ^ (2 * ℓ) / N0)
      = Cv ^ 2 * pi0 P₁ ^ (4 * ℓ) / N0 ^ 2 := by
    rw [div_mul_div_comm, ← pow_two (Cv * pi0 P₁ ^ (2 * ℓ)), mul_pow, hpow, ← pow_two N0]
  calc ((s.card : ℝ))
      ≤ ∑ e ∈ s.image (fun t => t.1), ((F e).card : ℝ) := hcard
    _ ≤ ∑ _e ∈ s.image (fun t => t.1),
          (Cv * pi0 P₁ ^ (2 * ℓ) / N0) * (Cv * pi0 P₁ ^ (2 * ℓ) / N0) :=
        Finset.sum_le_sum (fun e _ => hFe e)
    _ = ((s.image (fun t => t.1)).card : ℝ) *
          ((Cv * pi0 P₁ ^ (2 * ℓ) / N0) * (Cv * pi0 P₁ ^ (2 * ℓ) / N0)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (Cv * Cv) * ((s.image (fun t => t.1)).card : ℝ) * pi0 P₁ ^ (4 * ℓ) / N0 ^ 2 := by
        rw [hKK]; ring

end Work.BMF
