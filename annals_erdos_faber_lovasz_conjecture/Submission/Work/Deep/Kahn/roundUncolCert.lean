import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.roundUncolDefs

/-!
# `Work.Deep.Kahn.Round.uncolAct_cert`

The **certificate condition** of the Bruhn--Joos concentration inequality for the statistic
`uncolActCount ω x γ` (the paper's `uncolActivatedNbrsRV`).

Off the exceptional set `excSet x γ ℓ`, for every level `u > 0` the certificate set

  `certSet ω x γ = uncolActSet ω x γ ∪ blockerOf ω x γ '' uncolActSet ω x γ`

of the at most `2 D` counted edges and their chosen blockers has the property that an outcome
`ω'` agreeing with `ω` on all but fewer than `u / (C + ℓ + 2)` of its coordinates counts all
but fewer than `u` of the edges counted by `ω`:

  `uncolActCount ω' x γ > uncolActCount ω x γ - u`.

The two structural inputs (proved in `roundUncolDefs`) are

* linearity: a blocker not containing `x` meets the counted edge in a vertex `≠ x`, and at most
  one edge contains both that vertex and `x`, so it is the chosen blocker of at most `C` edges;
* the exceptional set: a blocker containing `x` is an activated `γ`-edge through `x` of a fixed
  colour `δ`, of which there are fewer than `ℓ` off `excSet x γ ℓ`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

namespace Round

variable {n c : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗]
  {L : 𝓗 → Finset (Fin c)} {K C : ℕ}

/-- The set of coordinates of the certificate set on which `ω` and `ω'` disagree. -/
def diffSet [NeZero K] (ω ω' : Space K 𝓗 L) (x : Fin n) (γ : Fin c) : Finset 𝓗 :=
  (certSet (K := K) ω x γ).filter (fun i : 𝓗 => ω i ≠ ω' i)

lemma mem_diffSet [NeZero K] {ω ω' : Space K 𝓗 L} {x : Fin n} {γ : Fin c} {i : 𝓗} :
    i ∈ diffSet (K := K) ω ω' x γ ↔ i ∈ certSet (K := K) ω x γ ∧ ω i ≠ ω' i := by
  classical
  rw [diffSet, Finset.mem_filter]

/-- The counted edges whose blocker is one of the changed coordinates. -/
def killedSet [NeZero K] (ω ω' : Space K 𝓗 L) (x : Fin n) (γ : Fin c) : Finset 𝓗 :=
  (uncolActSet (K := K) ω x γ).filter
    (fun e : 𝓗 => e ∈ diffSet (K := K) ω ω' x γ ∨
      blockerOf (K := K) ω x γ e ∈ diffSet (K := K) ω ω' x γ)

lemma mem_killedSet [NeZero K] {ω ω' : Space K 𝓗 L} {x : Fin n} {γ : Fin c} {e : 𝓗} :
    e ∈ killedSet (K := K) ω ω' x γ ↔ e ∈ uncolActSet (K := K) ω x γ ∧
      (e ∈ diffSet (K := K) ω ω' x γ ∨
        blockerOf (K := K) ω x γ e ∈ diffSet (K := K) ω ω' x γ) := by
  classical
  rw [killedSet, Finset.mem_filter]

/-- **The surviving counted edges.**  An edge counted at `ω` whose own coordinate and whose
chosen blocker are unchanged is still counted at `ω'`. -/
lemma filter_survivors_subset [NeZero K] (ω ω' : Space K 𝓗 L) (x : Fin n) (γ : Fin c) :
    (uncolActSet (K := K) ω x γ).filter
        (fun e : 𝓗 => ω e = ω' e ∧
          ω (blockerOf (K := K) ω x γ e) = ω' (blockerOf (K := K) ω x γ e))
      ⊆ uncolActSet (K := K) ω' x γ := by
  classical
  intro e he
  rw [Finset.mem_filter] at he
  obtain ⟨heU, hee, heb⟩ := he
  obtain ⟨h1, h2, hact, hkept⟩ := mem_uncolActSet.mp heU
  have hspec := blockerOf_spec (K := K) (x := x) (γ := γ) heU
  obtain ⟨hne, hmeet, hactb, hcolb⟩ := hspec
  refine mem_uncolActSet.mpr ⟨h1, h2, (active_congr hee).mp hact, ?_⟩
  · intro hkept'
    rw [kept] at hkept'
    obtain ⟨-, hno⟩ := hkept'
    have hgact : active ω' (blockerOf (K := K) ω x γ e) := (active_congr heb).mp hactb
    have hgcol : colour ω' (blockerOf (K := K) ω x γ e) = colour ω' e := by
      rw [← colour_congr heb, ← colour_congr hee, hcolb]
    exact hno _ hne hmeet hgact hgcol

private lemma killedSet_subset [NeZero K] (ω ω' : Space K 𝓗 L) (x : Fin n) (γ : Fin c) :
    killedSet (K := K) ω ω' x γ ⊆
      ((uncolActSet (K := K) ω x γ).filter (fun e : 𝓗 => e ∈ diffSet (K := K) ω ω' x γ))
        ∪ (diffSet (K := K) ω ω' x γ).biUnion (fun w => blkFib (K := K) ω x γ w) := by
  classical
  intro e he
  obtain ⟨heU, hcase⟩ := mem_killedSet.mp he
  rw [Finset.mem_union]
  rcases hcase with hcase | hcase
  · exact Or.inl (Finset.mem_filter.mpr ⟨heU, hcase⟩)
  · refine Or.inr ?_
    rw [Finset.mem_biUnion]
    exact ⟨blockerOf (K := K) ω x γ e, hcase, mem_blkFib.mpr ⟨heU, rfl⟩⟩

/-- **The killed count.**  At most `(C + ℓ + 1) · #(changed certificate coordinates)` counted
edges are lost. -/
lemma killedSet_card_le [NeZero K] (hlin : 𝓗.IsLinear)
    (hsize : ∀ e : 𝓗, edgeSize (e : Set (Fin n)) = C)
    {ω ω' : Space K 𝓗 L} {x : Fin n} {γ : Fin c} {ℓ : ℕ}
    (hω : ω ∉ excSet (L := L) x γ ℓ) :
    (killedSet (K := K) ω ω' x γ).card ≤
      (C + ℓ + 1) * (diffSet (K := K) ω ω' x γ).card := by
  classical
  set A := (diffSet (K := K) ω ω' x γ).card with hA
  refine le_trans (Finset.card_le_card (killedSet_subset ω ω' x γ)) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  have h1 : ((uncolActSet (K := K) ω x γ).filter
      (fun e : 𝓗 => e ∈ diffSet (K := K) ω ω' x γ)).card ≤ A := by
    rw [hA]
    refine Finset.card_le_card ?_
    intro e he
    exact (Finset.mem_filter.mp he).2
  have h2 : ((diffSet (K := K) ω ω' x γ).biUnion
      (fun w => blkFib (K := K) ω x γ w)).card ≤ (C + ℓ) * A := by
    refine le_trans Finset.card_biUnion_le ?_
    have hfib : ∀ w ∈ diffSet (K := K) ω ω' x γ,
        (blkFib (K := K) ω x γ w).card ≤ C + ℓ := by
      intro w _hw
      by_cases hxw : x ∈ (w : Set (Fin n))
      · have hle := blkFib_le_of_mem_x (K := K) (L := L) (ω := ω) (x := x) (γ := γ) hω hxw
        omega
      · have hle := blkFib_le_of_not_mem_x (K := K) (L := L) (ω := ω) (x := x) (γ := γ) hlin hxw
        rw [hsize w] at hle
        omega
    calc (∑ w ∈ diffSet (K := K) ω ω' x γ, (blkFib (K := K) ω x γ w).card)
        ≤ ∑ _w ∈ diffSet (K := K) ω ω' x γ, (C + ℓ) := Finset.sum_le_sum hfib
      _ = (C + ℓ) * (diffSet (K := K) ω ω' x γ).card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ = (C + ℓ) * A := by rw [hA]
  have htot : ((uncolActSet (K := K) ω x γ).filter
        (fun e : 𝓗 => e ∈ diffSet (K := K) ω ω' x γ)).card
      + ((diffSet (K := K) ω ω' x γ).biUnion (fun w => blkFib (K := K) ω x γ w)).card
      ≤ (C + ℓ + 1) * A := by
    have hadd := Nat.add_le_add h1 h2
    have heq : (C + ℓ + 1) * A = A + (C + ℓ) * A := by ring
    omega
  exact htot

/-- **The certificate property of `uncolActCount`.** -/
theorem uncolAct_cert [NeZero K] (hlin : 𝓗.IsLinear)
    (hsize : ∀ e : 𝓗, edgeSize (e : Set (Fin n)) = C)
    (ℓ : ℕ) (x : Fin n) (γ : Fin c) :
    ∀ (u : ℝ), 0 < u → ∀ ω : Space K 𝓗 L, ω ∉ excSet (L := L) x γ ℓ →
      ∃ I : Finset 𝓗, I.card ≤ 2 * (colThru (L := L) x γ).card ∧
        ∀ ω' : Space K 𝓗 L, ω' ∉ excSet (L := L) x γ ℓ →
          ((I.filter (fun i : 𝓗 => ω i ≠ ω' i)).card : ℝ) <
              u / ((C : ℝ) + (ℓ : ℝ) + 2) →
            (uncolActCount (K := K) (L := L) ω x γ : ℝ) - u <
              (uncolActCount (K := K) (L := L) ω' x γ : ℝ) := by
  classical
  intro u hu ω hω
  refine ⟨certSet (K := K) ω x γ, ?_, ?_⟩
  · refine le_trans (certSet_card_le (K := K) ω x γ) ?_
    have hsub : (uncolActSet (K := K) ω x γ).card ≤ (colThru (L := L) x γ).card :=
      Finset.card_le_card (uncolActSet_subset_colThru ω x γ)
    omega
  · intro ω' hω' hS
    set surv := (uncolActSet (K := K) ω x γ).filter
      (fun e : 𝓗 => ω e = ω' e ∧
        ω (blockerOf (K := K) ω x γ e) = ω' (blockerOf (K := K) ω x γ e)) with hsurvdef
    set killed := killedSet (K := K) ω ω' x γ with hkilleddef
    set S := diffSet (K := K) ω ω' x γ with hSdef
    -- the survivors are counted at `ω'`
    have hcard_surv : surv.card ≤ uncolActCount (K := K) (L := L) ω' x γ := by
      rw [← uncolActSet_card (K := K) (L := L) ω' x γ]
      exact Finset.card_le_card (filter_survivors_subset (K := K) (L := L) ω ω' x γ)
    -- at most `(C+ℓ)` counted edges per changed certificate coordinate are killed
    have hkilled : killed.card ≤ (C + ℓ + 1) * S.card := by
      rw [hkilleddef, hSdef]
      exact killedSet_card_le (K := K) (L := L) hlin hsize (ℓ := ℓ) (ω' := ω') hω
    -- the counted edges split into survivors and killed
    have hsplit : (uncolActSet (K := K) ω x γ).card = surv.card + killed.card := by
      have hpart := Finset.card_filter_add_card_filter_not
        (s := uncolActSet (K := K) ω x γ)
        (fun e : 𝓗 => ω e = ω' e ∧
          ω (blockerOf (K := K) ω x γ e) = ω' (blockerOf (K := K) ω x γ e))
      have heq : (uncolActSet (K := K) ω x γ).filter
          (fun e : 𝓗 => ¬ (ω e = ω' e ∧
            ω (blockerOf (K := K) ω x γ e) = ω' (blockerOf (K := K) ω x γ e)))
          = killed := by
        rw [hkilleddef]
        ext e
        rw [Finset.mem_filter, mem_killedSet, ← hSdef]
        constructor
        · rintro ⟨heU, hne⟩
          refine ⟨heU, ?_⟩
          by_cases hee : ω e = ω' e
          · right
            rw [mem_diffSet]
            refine ⟨mem_certSet.mpr (Or.inr ⟨e, heU, rfl⟩), ?_⟩
            by_contra hcon
            exact hne ⟨hee, hcon⟩
          · left
            rw [mem_diffSet]
            exact ⟨mem_certSet.mpr (Or.inl heU), hee⟩
        · rintro ⟨heU, hcase⟩
          refine ⟨heU, ?_⟩
          rintro ⟨hee, heb⟩
          rcases hcase with hcase | hcase
          · exact (mem_diffSet.mp hcase).2 hee
          · exact (mem_diffSet.mp hcase).2 heb
      rw [hsurvdef]
      rw [heq] at hpart
      exact hpart.symm
    -- arithmetic
    have hsurvR : (surv.card : ℝ) ≤ (uncolActCount (K := K) (L := L) ω' x γ : ℝ) := by
      exact_mod_cast hcard_surv
    have hkilledR : (killed.card : ℝ) ≤ ((C : ℝ) + (ℓ : ℝ) + 1) * (S.card : ℝ) := by
      have := hkilled
      push_cast
      exact_mod_cast this
    have hcount : (uncolActCount (K := K) (L := L) ω x γ : ℝ)
        = (surv.card : ℝ) + (killed.card : ℝ) := by
      rw [← uncolActSet_card (K := K) (L := L) ω x γ, hsplit]
      push_cast
      ring
    have hkey : (killed.card : ℝ) < u := by
      refine lt_of_le_of_lt hkilledR ?_
      calc ((C : ℝ) + (ℓ : ℝ) + 1) * (S.card : ℝ)
          < ((C : ℝ) + (ℓ : ℝ) + 1) * (u / ((C : ℝ) + (ℓ : ℝ) + 2)) := by
            apply mul_lt_mul_of_pos_left hS
            positivity
        _ = u * (((C : ℝ) + (ℓ : ℝ) + 1) / ((C : ℝ) + (ℓ : ℝ) + 2)) := by ring
        _ < u * 1 := by
            apply mul_lt_mul_of_pos_left _ hu
            rw [div_lt_one (by positivity)]
            linarith
        _ = u := by ring
    linarith [hcount, hsurvR, hkey]

end Round

end

end Work.Deep.Kahn
