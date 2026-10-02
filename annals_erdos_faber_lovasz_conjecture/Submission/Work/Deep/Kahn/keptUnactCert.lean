import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.roundKeptUnactDefs

/-!
# `Work.Deep.Kahn.keptUnactCert`

The certificate condition of the Bruhn--Joos concentration inequality for the statistic
`keptUnactCount ω x γ` (the paper's `keptUnactColsRV`).

For every `ω` the certificate set is `certSetK ω x γ = colThru x γ ∪ pickBlock ω x γ '' colThru x γ`
of size at most `2 · #(colThru x γ)`.  If `ω'` agrees with `ω` on all but fewer than
`u/(C+2)` of its coordinates, then `keptUnactCount ω' x γ < keptUnactCount ω x γ + u`:

an edge counted by `ω'` but not by `ω` either was activated at `ω` (so its own coordinate
changed) or was blocked at `ω` (so the coordinate of its chosen blocker changed); linearity
bounds the multiplicity of a blocker by `C`.  Unlike the `uncolActCount` certificate no
exceptional set is needed, since a blocker never contains `x`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

namespace Round

theorem keptUnactCert {n c C K : ℕ} [NeZero K]
    {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗] {L : 𝓗 → Finset (Fin c)}
    (hlin : ErdosFaberLovaszConjecture.Hypergraph.IsLinear 𝓗)
    (hsize : ∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C)
    (x : Fin n) (γ : Fin c) :
    ∀ (u : ℝ), 0 < u → ∀ ω : Space K 𝓗 L,
      ∃ I : Finset 𝓗, I.card ≤ 2 * (colThru (L := L) x γ).card ∧
        ∀ ω' : Space K 𝓗 L,
          ((I.filter (fun i : 𝓗 => ω i ≠ ω' i)).card : ℝ) < u / ((C : ℝ) + 2) →
            (keptUnactCount ω' x γ : ℝ) < (keptUnactCount ω x γ : ℝ) + u := by
  classical
  intro u hu ω
  refine ⟨certSetK (K := K) ω x γ, certSetK_card_le (K := K) ω x γ, ?_⟩
  intro ω' hJcard
  set J : Finset 𝓗 := (certSetK (K := K) ω x γ).filter (fun i : 𝓗 => ω i ≠ ω' i) with hJdef
  set S : Finset 𝓗 := (colThru (L := L) x γ).filter
    (fun e : 𝓗 => ¬ counted (K := K) ω x γ e ∧ counted (K := K) ω' x γ e) with hSdef
  -- every edge counted at `ω'` but not at `ω` lies in `S`
  have hsub : keptUnactSet (K := K) ω' x γ ⊆ keptUnactSet (K := K) ω x γ ∪ S := by
    intro e he
    obtain ⟨heC, hcnt⟩ := mem_keptUnactSet.mp he
    by_cases h : counted (K := K) ω x γ e
    · exact Finset.mem_union_left _ (mem_keptUnactSet.mpr ⟨heC, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heC, h, hcnt⟩)
  -- `S` is contained in `S₁ ∪ S₂`
  have hSsub : S ⊆ (colThru (L := L) x γ).filter (fun e : 𝓗 => ω e ≠ ω' e) ∪
      (colThru (L := L) x γ).filter (fun e : 𝓗 => ¬ active ω e ∧ IsBlocked ω x γ e ∧
        pickBlock (K := K) ω x γ e ∈ J) := by
    intro e he
    obtain ⟨heC, hnc, hc'⟩ := Finset.mem_filter.mp (by rw [← hSdef]; exact he)
    rw [Finset.mem_union]
    by_cases heq : ω e = ω' e
    · by_cases hact : active ω e
      · exact absurd ((active_congr (K := K) heq).mp hact) hc'.1
      · have hb : IsBlocked ω x γ e := (not_counted_iff (K := K)).mp hnc |>.resolve_left hact
        by_cases hJ : pickBlock (K := K) ω x γ e ∈ J
        · exact Or.inr (Finset.mem_filter.mpr ⟨heC, hact, hb, hJ⟩)
        · exfalso
          have hpick : ω (pickBlock (K := K) ω x γ e) = ω' (pickBlock (K := K) ω x γ e) := by
            by_contra hne
            exact hJ (Finset.mem_filter.mpr
              ⟨mem_certSetK_pickBlock (K := K) heC, hne⟩)
          exact (not_counted_of_not_counted (K := K) heC heq hpick hnc) hc'
    · exact Or.inl (Finset.mem_filter.mpr ⟨heC, heq⟩)
  -- `S₁ ⊆ J`
  have hS1 : ((colThru (L := L) x γ).filter (fun e : 𝓗 => ω e ≠ ω' e)).card ≤ J.card := by
    refine Finset.card_le_card ?_
    intro e he
    exact Finset.mem_filter.mpr
      ⟨mem_certSetK_of_mem_colThru (K := K) (Finset.mem_filter.mp he).1,
        (Finset.mem_filter.mp he).2⟩
  -- `S₂` has at most `C · #J` elements
  have hS2 : ((colThru (L := L) x γ).filter (fun e : 𝓗 => ¬ active ω e ∧
      IsBlocked ω x γ e ∧ pickBlock (K := K) ω x γ e ∈ J)).card ≤ C * J.card := by
    have hsub2 : ((colThru (L := L) x γ).filter (fun e : 𝓗 => ¬ active ω e ∧
        IsBlocked ω x γ e ∧ pickBlock (K := K) ω x γ e ∈ J)) ⊆
        J.biUnion (fun w : 𝓗 => (colThru (L := L) x γ).filter (fun e : 𝓗 => ¬ active ω e ∧
          IsBlocked ω x γ e ∧ pickBlock (K := K) ω x γ e = w)) := by
      intro e he
      obtain ⟨heC, hna, hb, hpe⟩ := Finset.mem_filter.mp he
      rw [Finset.mem_biUnion]
      exact ⟨pickBlock (K := K) ω x γ e, hpe,
        Finset.mem_filter.mpr ⟨heC, hna, hb, rfl⟩⟩
    refine le_trans (Finset.card_le_card hsub2) ?_
    refine le_trans Finset.card_biUnion_le ?_
    have hfib : ∀ w ∈ J, ((colThru (L := L) x γ).filter (fun e : 𝓗 => ¬ active ω e ∧
        IsBlocked ω x γ e ∧ pickBlock (K := K) ω x γ e = w)).card ≤ C :=
      fun w _ => pickBlock_fiber_card_le (K := K) hlin hsize ω x γ w
    calc (∑ w ∈ J, ((colThru (L := L) x γ).filter (fun e : 𝓗 => ¬ active ω e ∧
            IsBlocked ω x γ e ∧ pickBlock (K := K) ω x γ e = w)).card)
        ≤ ∑ _w ∈ J, C := Finset.sum_le_sum hfib
      _ = C * J.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- hence `S.card ≤ (C+1) * J.card`
  have hScard : S.card ≤ (C + 1) * J.card := by
    have h2 : S.card ≤ ((colThru (L := L) x γ).filter (fun e : 𝓗 => ω e ≠ ω' e)).card
        + ((colThru (L := L) x γ).filter (fun e : 𝓗 => ¬ active ω e ∧ IsBlocked ω x γ e ∧
            pickBlock (K := K) ω x γ e ∈ J)).card :=
      le_trans (Finset.card_le_card hSsub) (Finset.card_union_le _ _)
    have h3 : (C + 1) * J.card = J.card + C * J.card := by ring
    omega
  -- the count increases by at most `S.card`
  have hfinal : keptUnactCount ω' x γ ≤ keptUnactCount ω x γ + (C + 1) * J.card := by
    rw [keptUnactCount_eq_card (K := K) ω' x γ, keptUnactCount_eq_card (K := K) ω x γ]
    calc (keptUnactSet (K := K) ω' x γ).card
        ≤ (keptUnactSet (K := K) ω x γ ∪ S).card := Finset.card_le_card hsub
      _ ≤ (keptUnactSet (K := K) ω x γ).card + S.card := Finset.card_union_le _ _
      _ ≤ (keptUnactSet (K := K) ω x γ).card + (C + 1) * J.card := by omega
  -- the arithmetic
  have hJsmall : ((C : ℝ) + 1) * (J.card : ℝ) < u := by
    have h3 : (0 : ℝ) ≤ (J.card : ℝ) := by positivity
    have h4 : ((C : ℝ) + 1) * (J.card : ℝ) ≤ ((C : ℝ) + 2) * (J.card : ℝ) := by nlinarith
    have h5 : ((C : ℝ) + 2) * (J.card : ℝ) < ((C : ℝ) + 2) * (u / ((C : ℝ) + 2)) :=
      mul_lt_mul_of_pos_left hJcard (by linarith : (0 : ℝ) < (C : ℝ) + 2)
    have h6 : ((C : ℝ) + 2) * (u / ((C : ℝ) + 2)) = u := by
      field_simp
    linarith
  have hcast : (keptUnactCount ω' x γ : ℝ)
      ≤ (keptUnactCount ω x γ : ℝ) + ((C : ℝ) + 1) * (J.card : ℝ) := by
    have h6 : ((keptUnactCount ω' x γ : ℕ) : ℝ)
        ≤ ((keptUnactCount ω x γ + (C + 1) * J.card : ℕ) : ℝ) := by exact_mod_cast hfinal
    push_cast at h6
    linarith
  linarith [hcast, hJsmall]

end Round

end

end Work.Deep.Kahn
