import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.KahnPartition
import Submission.Work.Deep.Prob.Colouring.card_weighted_dev_le
import Submission.Work.Deep.Nibble.PiCount.card_pi_biUnion_comp
import Submission.Work.Deep.Nibble.PiCount.blockFacts
import Submission.Work.Deep.Nibble.PiCount.degInPart_blockSum

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Classical

namespace Work.Deep.Nibble

noncomputable section

/-- The edges of `𝓗` through `v`. -/
abbrev edgeIdx {n : ℕ} (𝓗 : HG n) (v : Fin n) : Type := {e : 𝓗 // v ∈ (e : Set (Fin n))}

/-- The block `e ∖ {v}` of an edge `e` through `v`. -/
def blkF {n : ℕ} {𝓗 : HG n} (v : Fin n) (e : edgeIdx 𝓗 v) : Finset (Fin n) :=
  (ErdosFaberLovaszConjecture.verts (e.1 : Set (Fin n))).erase v

/-- The `Bool` pattern recording, for every edge through `v`, whether its block is all in part `i`. -/
def patOf {n p : ℕ} {𝓗 : HG n} (v : Fin n) (i : Fin p) (c : Fin n → Fin p)
    (e : edgeIdx 𝓗 v) : Bool :=
  decide (∀ x : ↑(blkF v e), c x = i)

/-- The mean of the induced degree of `v`. -/
def muOf {n : ℕ} (𝓗 : HG n) (v : Fin n) (r p : ℕ) : ℝ :=
  ((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ) / (p : ℝ) ^ (r - 1)

/-- The deviation event for a pattern `σ`. -/
def devOf {n : ℕ} {𝓗 : HG n} (v : Fin n) (r p : ℕ) (τ : ℝ) (σ : edgeIdx 𝓗 v → Bool) : Prop :=
  τ ≤ |(∑ e : edgeIdx 𝓗 v, (if σ e then (1 : ℝ) else 0)) - muOf 𝓗 v r p|

/-- If a property of colourings of a finite type depends only on the coordinates away from `v`,
then pinning the colour of `v` divides the number of colourings satisfying it by `p`. -/
theorem card_filter_pin_indep {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}
    (v : α) (i : Fin p) (Q : (α → Fin p) → Prop) [DecidablePred Q]
    (hQ : ∀ c c' : α → Fin p, (∀ x, x ≠ v → c x = c' x) → (Q c ↔ Q c')) :
    ((Finset.univ.filter (fun c : α → Fin p => c v = i ∧ Q c)).card : ℝ) * (p : ℝ)
      = ((Finset.univ.filter Q).card : ℝ) := by
  classical
  have haux : ∀ (c : α → Fin p) (j : Fin p), Q (Function.update c v j) ↔ Q c := by
    intro c j
    have h : ∀ x, x ≠ v → c x = Function.update c v j x :=
      fun x hx => (Function.update_of_ne hx j c).symm
    exact (hQ c (Function.update c v j) h).symm
  have hcard : ∀ j : Fin p,
      ((Finset.univ.filter (fun c : α → Fin p => c v = j ∧ Q c)).card : ℕ)
        = ((Finset.univ.filter (fun c : α → Fin p => c v = i ∧ Q c)).card : ℕ) := by
    intro j
    refine Finset.card_bij (fun c _ => Function.update c v i) ?_ ?_ ?_
    · intro c hc
      rw [Finset.mem_filter] at hc ⊢
      exact ⟨Finset.mem_univ _, Function.update_self v i c, (haux c i).mpr hc.2.2⟩
    · intro c₁ hc₁ c₂ hc₂ heq
      funext x
      by_cases hx : x = v
      · subst hx
        rw [show c₁ x = j from (Finset.mem_filter.mp hc₁).2.1,
          show c₂ x = j from (Finset.mem_filter.mp hc₂).2.1]
      · have h2 := congrFun heq x
        rw [Function.update_of_ne hx i c₁, Function.update_of_ne hx i c₂] at h2
        exact h2
    · intro c hc
      rw [Finset.mem_filter] at hc
      refine ⟨Function.update c v j, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, Function.update_self v j c, (haux c j).mpr hc.2.2⟩
      · funext x
        by_cases hx : x = v
        · subst hx
          rw [Function.update_self]
          exact hc.2.1.symm
        · rw [Function.update_of_ne hx i (Function.update c v j), Function.update_of_ne hx j c]
  have hsum : (Finset.univ.filter Q).card
      = ∑ j : Fin p, (Finset.univ.filter (fun c : α → Fin p => c v = j ∧ Q c)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter Q)
      (t := (Finset.univ : Finset (Fin p))) (f := fun c : α → Fin p => c v)
      (fun c _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    rw [show (Finset.univ.filter Q).filter (fun c : α → Fin p => c v = j)
        = Finset.univ.filter (fun c : α → Fin p => Q c ∧ c v = j) from by
      rw [Finset.filter_filter]]
    apply Finset.filter_congr
    intro c _
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hfin : (Finset.univ.filter Q).card
      = p * ((Finset.univ.filter (fun c : α → Fin p => c v = i ∧ Q c)).card) := by
    rw [hsum]
    rw [Finset.sum_congr rfl (fun j _ => hcard j)]
    rw [Finset.sum_const_nat (s := Finset.univ)
      (f := fun _ : Fin p => (Finset.univ.filter (fun c : α → Fin p => c v = i ∧ Q c)).card)
      (m := (Finset.univ.filter (fun c : α → Fin p => c v = i ∧ Q c)).card) (fun j _ => rfl)]
    rw [Finset.card_univ, Fintype.card_fin]
  have hcast := congrArg (fun m : ℕ => (m : ℝ)) hfin
  push_cast at hcast
  rw [hcast]
  ring

/-- **The pinned block-pattern count.**  Among the colourings of `Fin n` with `π v = i`, the
number whose pattern on the blocks equals a prescribed `σ` is `p` to the number of free
coordinates times the product of the local counts. -/
theorem card_pat_eq {n : ℕ} {𝓗 : HG n} (v : Fin n) {r p : ℕ} (hr : 2 ≤ r)
    (hlin : ErdosFaberLovaszConjecture.Hypergraph.IsLinear 𝓗)
    (hrsize : ∀ e ∈ 𝓗, v ∈ e → e.ncard = r) (i : Fin p) (σ : edgeIdx 𝓗 v → Bool) :
    ((Finset.univ.filter (fun c : Fin n → Fin p => c v = i ∧ patOf (𝓗 := 𝓗) v i c = σ)).card : ℝ)
      = (p : ℝ) ^ (n - (Finset.univ.biUnion (blkF (𝓗 := 𝓗) v)).card - 1) *
          ∏ e : edgeIdx 𝓗 v, (if σ e then (1 : ℝ) else (p : ℝ) ^ (r - 1) - 1) := by
  classical
  have hbf := PiCount.blockFacts v hr hlin hrsize
  have hcardBlk : ∀ e : edgeIdx 𝓗 v, (blkF v e).card = r - 1 := fun e => hbf.1 e
  have hdisjBlk : ∀ e₁ e₂ : edgeIdx 𝓗 v, e₁ ≠ e₂ →
      Disjoint (blkF v e₁) (blkF v e₂) := fun e₁ e₂ h => hbf.2.1 e₁ e₂ h
  have hvW : v ∉ Finset.univ.biUnion (blkF (𝓗 := 𝓗) v) := hbf.2.2
  have hWle : (Finset.univ.biUnion (blkF (𝓗 := 𝓗) v)).card + 1 ≤ n := by
    have h1 : (insert v (Finset.univ.biUnion (blkF (𝓗 := 𝓗) v))).card
        = (Finset.univ.biUnion (blkF (𝓗 := 𝓗) v)).card + 1 :=
      Finset.card_insert_of_notMem hvW
    have h2 : (insert v (Finset.univ.biUnion (blkF (𝓗 := 𝓗) v))).card ≤ n := by
      calc (insert v (Finset.univ.biUnion (blkF (𝓗 := 𝓗) v))).card
            ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
        _ = n := by simp
    omega
  have hp0 : 0 < p := by have := i.isLt; omega
  -- (a) the property only depends on the coordinates different from `v`
  have hQ : ∀ c c' : Fin n → Fin p, (∀ x, x ≠ v → c x = c' x) →
      ((∀ e : edgeIdx 𝓗 v, ((∀ x : ↑(blkF v e), c x = i) ↔ σ e = true)) ↔
       (∀ e : edgeIdx 𝓗 v, ((∀ x : ↑(blkF v e), c' x = i) ↔ σ e = true))) := by
    intro c c' h
    refine forall_congr' (fun e => ?_)
    have h1 : (∀ x : ↑(blkF v e), c x = i) ↔ (∀ x : ↑(blkF v e), c' x = i) := by
      refine forall_congr' (fun x => ?_)
      have hmem : x.1 ∈ Finset.univ.biUnion (blkF (𝓗 := 𝓗) v) :=
        Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ e, x.2⟩
      have hxv : x.1 ≠ v := by
        intro h
        rw [h] at hmem
        exact hvW hmem
      rw [h x.1 hxv]
    rw [h1]
  -- (b) the target filter is the "Prop form" filter
  have hf_eq : (Finset.univ.filter (fun c : Fin n → Fin p =>
        c v = i ∧ patOf (𝓗 := 𝓗) v i c = σ))
      = Finset.univ.filter (fun c : Fin n → Fin p => c v = i ∧
          ∀ e : edgeIdx 𝓗 v, ((∀ x : ↑(blkF v e), c x = i) ↔ σ e = true)) := by
    apply Finset.filter_congr
    intro c _
    have hiff : (patOf (𝓗 := 𝓗) v i c = σ) ↔
        (∀ e : edgeIdx 𝓗 v, ((∀ x : ↑(blkF v e), c x = i) ↔ σ e = true)) := by
      rw [funext_iff]
      refine forall_congr' (fun e => ?_)
      rw [Bool.eq_iff_iff, patOf, decide_eq_true_iff]
    rw [hiff]
  -- (c) pinning the coordinate `v`
  have hpin := card_filter_pin_indep (v := v) i
    (fun c : Fin n → Fin p =>
      ∀ e : edgeIdx 𝓗 v, ((∀ x : ↑(blkF v e), c x = i) ↔ σ e = true)) hQ
  -- (d) the master block count
  have hmaster := PiCount.card_pi_biUnion_comp (α := Fin n) (p := p) (blkF (𝓗 := 𝓗) v) hdisjBlk
    (fun e g => ((∀ x : ↑(blkF v e), g x = i) ↔ σ e = true))
  rw [Fintype.card_fin] at hmaster
  -- (e) the local counts
  have hloc : ∀ e : edgeIdx 𝓗 v,
      ((Finset.univ.filter (fun g : ↑(blkF v e) → Fin p =>
        ((∀ x : ↑(blkF v e), g x = i) ↔ σ e = true))).card : ℝ)
        = (if σ e then (1 : ℝ) else (p : ℝ) ^ (r - 1) - 1) := by
    intro e
    by_cases hb : σ e = true
    · rw [if_pos hb]
      have hset : (Finset.univ.filter (fun g : ↑(blkF v e) → Fin p =>
          ((∀ x : ↑(blkF v e), g x = i) ↔ σ e = true)))
          = {(fun _ : ↑(blkF v e) => i)} := by
        ext g
        rw [hb]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, iff_true]
        constructor
        · intro h; funext x; exact h x
        · intro h x; rw [h]
      rw [hset, Finset.card_singleton]
      norm_num
    · rw [if_neg hb]
      have hbfalse : σ e = false := by cases h : σ e <;> simp_all
      have hset : (Finset.univ.filter (fun g : ↑(blkF v e) → Fin p =>
          ((∀ x : ↑(blkF v e), g x = i) ↔ σ e = true)))
          = (Finset.univ : Finset (↑(blkF v e) → Fin p)).erase (fun _ => i) := by
        ext g
        rw [hbfalse]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_true,
          Finset.mem_erase, Bool.false_eq_true, iff_false]
        constructor
        · intro h hg; exact h (by rw [hg]; intro x; rfl)
        · intro h hcon; exact h (funext (fun x => hcon x))
      rw [hset, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, hcardBlk e,
        Nat.cast_sub (Nat.one_le_pow _ p hp0), Nat.cast_pow, Nat.cast_one]
  -- (f) assemble
  have hA : ((Finset.univ.filter (fun c : Fin n → Fin p => c v = i ∧
        ∀ e : edgeIdx 𝓗 v, ((∀ x : ↑(blkF v e), c x = i) ↔ σ e = true))).card : ℝ) * (p : ℝ)
      = (p : ℝ) ^ (n - (Finset.univ.biUnion (blkF (𝓗 := 𝓗) v)).card) *
          ∏ e : edgeIdx 𝓗 v, (if σ e then (1 : ℝ) else (p : ℝ) ^ (r - 1) - 1) := by
    rw [hpin, hmaster]
    rw [Finset.prod_congr rfl (fun e _ => hloc e)]
  rw [hf_eq]
  have hpR : (p : ℝ) ≠ 0 := by positivity
  have hkey : (p : ℝ) ^ (n - (Finset.univ.biUnion (blkF (𝓗 := 𝓗) v)).card - 1) * (p : ℝ)
      = (p : ℝ) ^ (n - (Finset.univ.biUnion (blkF (𝓗 := 𝓗) v)).card) := by
    rw [← pow_succ]
    congr 1
    omega
  refine mul_right_cancel₀ hpR ?_
  rw [hA, ← hkey]
  ring


-- ===== the assembly =====

/-- **Chernoff count for the induced degree of a random part.**  Let `𝓗` be a linear hypergraph on `Fin n` whose edges through `v` all have `r` vertices, let `p ≥ 2` and assign every vertex of `Fin n` a part in `Fin p`; fix a part `i` and condition on `π v = i`.  Then the induced degree `degInPart 𝓗 π v i` (the number of edges of `𝓗` through `v` all of whose vertices lie in part `i`) is a sum of `d_𝓗(v)` independent Bernoulli`(p^{-(r-1)})` variables (the events "`e ∖ {v} ⊆` part `i`" are independent because `𝓗` is linear, and each has probability `p^{-(r-1)}`), so the weighted Bernstein/Chernoff bound in counting form gives the displayed estimate: the number of `π` with `π v = i` on which the deviation from the mean `d_𝓗(v)/p^{r-1}` is at least `τ ≥ 0` is at most `p^{n-1} · 2 exp(-τ²/(2(μ + τ/3)))` with `μ = d_𝓗(v)/p^{r-1}`.  The template for the counting part is `Work.Deep.Prob.Colouring.card_weighted_dev_le` (fibre count of a Boolean pattern under a uniform colouring); the analytic input is `Work.Deep.Prob.Colouring.card_weighted_dev_le`'s engine `Commons.Probability.Chernoff.chernoff_two_sided_finite_weighted` (both already in the workspace). -/
theorem partDegCount {n : ℕ} {𝓗 : HG n} (v : Fin n) {r p : ℕ} (hr : 2 ≤ r) (hp : 2 ≤ p)
    (hlin : ErdosFaberLovaszConjecture.Hypergraph.IsLinear 𝓗)
    (hrsize : ∀ e ∈ 𝓗, v ∈ e → e.ncard = r) (i : Fin p) {τ : ℝ} (hτ : 0 ≤ τ) :
    ((Finset.univ.filter (fun π : Fin n → Fin p =>
        π v = i ∧ τ ≤ |((degInPart 𝓗 π v i : ℕ) : ℝ)
          - ((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ)
              / (p : ℝ) ^ (r - 1)|)).card : ℝ)
      ≤ (p : ℝ) ^ (n - 1) *
          (2 * Real.exp (-(τ ^ 2) / (2 * (1 *
            (((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ)
              / (p : ℝ) ^ (r - 1)) + τ / 3)))) := by
  classical
  have hbf := PiCount.blockFacts v hr hlin hrsize
  have hcardBlk : ∀ e : edgeIdx 𝓗 v, (blkF v e).card = r - 1 := fun e => hbf.1 e
  have hdisjBlk : ∀ e₁ e₂ : edgeIdx 𝓗 v, e₁ ≠ e₂ →
      Disjoint (blkF v e₁) (blkF v e₂) := fun e₁ e₂ h => hbf.2.1 e₁ e₂ h
  have hvW : v ∉ Finset.univ.biUnion (blkF (𝓗 := 𝓗) v) := hbf.2.2
  have hWcard : (Finset.univ.biUnion (blkF (𝓗 := 𝓗) v)).card
      = (r - 1) * Fintype.card (edgeIdx 𝓗 v) := by
    rw [Finset.card_biUnion (fun j _ k _ hjk => hdisjBlk j k hjk)]
    rw [Finset.sum_congr rfl (fun e _ => hcardBlk e)]
    rw [Finset.sum_const, Finset.card_univ]
    exact Nat.mul_comm _ _
  have hWle : (Finset.univ.biUnion (blkF (𝓗 := 𝓗) v)).card + 1 ≤ n := by
    have h1 : (insert v (Finset.univ.biUnion (blkF (𝓗 := 𝓗) v))).card
        = (Finset.univ.biUnion (blkF (𝓗 := 𝓗) v)).card + 1 :=
      Finset.card_insert_of_notMem hvW
    have h2 : (insert v (Finset.univ.biUnion (blkF (𝓗 := 𝓗) v))).card ≤ n := by
      calc (insert v (Finset.univ.biUnion (blkF (𝓗 := 𝓗) v))).card
            ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
        _ = n := by simp
    omega
  have hdeg : (ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v) = Fintype.card (edgeIdx 𝓗 v) := by
    show Nat.card (edgeIdx 𝓗 v) = Fintype.card (edgeIdx 𝓗 v)
    exact Nat.card_eq_fintype_card
  have hKr1 : (1 : ℝ) ≤ (p : ℝ) ^ (r - 1) :=
    one_le_pow₀ (by exact_mod_cast (le_trans (by norm_num : (1:ℕ) ≤ 2) hp))
  have hsumID : ∀ c : Fin n → Fin p, c v = i →
      (degInPart 𝓗 c v i : ℝ) = ∑ e : edgeIdx 𝓗 v, (if patOf (𝓗 := 𝓗) v i c e then (1:ℝ) else 0) := by
    intro c hcv
    rw [PiCount.degInPart_blockSum v c i hcv]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hP : (∀ x ∈ (ErdosFaberLovaszConjecture.verts (e.1 : Set (Fin n))).erase v, c x = i)
    · have hpat : patOf (𝓗 := 𝓗) v i c e = true := by
        rw [patOf, decide_eq_true_iff]
        intro x
        exact hP x.1 x.2
      rw [if_pos hP, if_pos hpat]
    · have hpat : patOf (𝓗 := 𝓗) v i c e = false := by
        rw [patOf]
        exact decide_eq_false_iff_not.mpr (fun h => hP (fun x hx => h ⟨x, hx⟩))
      rw [if_neg hP, if_neg (by rw [hpat]; exact Bool.false_ne_true)]
  have hstep1 : (Finset.univ.filter (fun π : Fin n → Fin p =>
        π v = i ∧ τ ≤ |((degInPart 𝓗 π v i : ℕ) : ℝ)
          - ((ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ)
              / (p : ℝ) ^ (r - 1)|))
      = Finset.univ.filter (fun c : Fin n → Fin p =>
          c v = i ∧ devOf (𝓗 := 𝓗) v r p τ (patOf (𝓗 := 𝓗) v i c)) := by
    apply Finset.filter_congr
    intro c _
    by_cases hcv : c v = i
    · constructor
      · intro h
        exact ⟨h.1, by rw [hsumID c hcv] at h; exact h.2⟩
      · intro h
        exact ⟨h.1, by rw [hsumID c hcv]; exact h.2⟩
    · constructor
      · intro h; exact absurd h.1 hcv
      · intro h; exact absurd h.1 hcv
  have hinner : ∀ σ : edgeIdx 𝓗 v → Bool,
      (∑ c ∈ (Finset.univ.filter (fun c : Fin n → Fin p => c v = i)).filter
            (fun c => patOf (𝓗 := 𝓗) v i c = σ),
          (if devOf (𝓗 := 𝓗) v r p τ (patOf (𝓗 := 𝓗) v i c) then (1 : ℝ) else 0))
        = ((Finset.univ.filter (fun c : Fin n → Fin p =>
              c v = i ∧ patOf (𝓗 := 𝓗) v i c = σ)).card : ℝ)
            * (if devOf (𝓗 := 𝓗) v r p τ σ then (1 : ℝ) else 0) := by
    intro σ
    rw [show (Finset.univ.filter (fun c : Fin n → Fin p => c v = i)).filter
          (fun c => patOf (𝓗 := 𝓗) v i c = σ)
        = Finset.univ.filter (fun c : Fin n → Fin p =>
            c v = i ∧ patOf (𝓗 := 𝓗) v i c = σ) from by rw [Finset.filter_filter]]
    rw [Finset.sum_congr rfl (fun c hc => by
      have h2 : patOf (𝓗 := 𝓗) v i c = σ := (Finset.mem_filter.mp hc).2.2
      rw [h2])]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hX : ((Finset.univ.filter (fun c : Fin n → Fin p =>
        c v = i ∧ devOf (𝓗 := 𝓗) v r p τ (patOf (𝓗 := 𝓗) v i c))).card : ℝ)
      = ∑ σ : edgeIdx 𝓗 v → Bool,
          (((Finset.univ.filter (fun c : Fin n → Fin p =>
              c v = i ∧ patOf (𝓗 := 𝓗) v i c = σ)).card : ℝ)
            * (if devOf (𝓗 := 𝓗) v r p τ σ then (1:ℝ) else 0)) := by
    have h1 : (Finset.univ.filter (fun c : Fin n → Fin p =>
          c v = i ∧ devOf (𝓗 := 𝓗) v r p τ (patOf (𝓗 := 𝓗) v i c)))
        = (Finset.univ.filter (fun c : Fin n → Fin p => c v = i)).filter
            (fun c => devOf (𝓗 := 𝓗) v r p τ (patOf (𝓗 := 𝓗) v i c)) :=
      (Finset.filter_filter (p := fun c : Fin n → Fin p => c v = i)
        (q := fun c : Fin n → Fin p => devOf (𝓗 := 𝓗) v r p τ (patOf (𝓗 := 𝓗) v i c))
        (s := Finset.univ)).symm
    rw [h1, Finset.card_filter]
    push_cast
    rw [← Finset.sum_fiberwise_of_maps_to
          (s := Finset.univ.filter (fun c : Fin n → Fin p => c v = i))
          (t := (Finset.univ : Finset (edgeIdx 𝓗 v → Bool)))
          (g := fun c : Fin n → Fin p => patOf (𝓗 := 𝓗) v i c)
          (f := fun c : Fin n → Fin p =>
            (if devOf (𝓗 := 𝓗) v r p τ (patOf (𝓗 := 𝓗) v i c) then (1:ℝ) else 0))
          (fun c _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro σ _
    exact hinner σ
  have hmean : (∑ _e : edgeIdx 𝓗 v, (1 : ℝ) / (p : ℝ) ^ (r - 1) * 1) = muOf 𝓗 v r p := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, muOf, hdeg,
      one_div, div_eq_mul_inv]
  have hcher := Commons.Probability.Chernoff.chernoff_two_sided_finite_weighted
    (ι := edgeIdx 𝓗 v) (p := fun _ : edgeIdx 𝓗 v => (1 : ℝ) / (p : ℝ) ^ (r - 1))
    (fun _ => by positivity)
    (fun _ => by rw [div_le_one (by positivity)]; exact hKr1)
    (X := fun _ : edgeIdx 𝓗 v => (1 : ℝ)) (fun _ => by norm_num)
    (C := 1) (by norm_num) (fun _ => by norm_num) (t := τ) hτ
  have hcher2 : (∑ σ : edgeIdx 𝓗 v → Bool,
        (∏ e : edgeIdx 𝓗 v, (if σ e then (1 : ℝ) / (p : ℝ) ^ (r - 1)
            else 1 - 1 / (p : ℝ) ^ (r - 1)))
          * (if devOf (𝓗 := 𝓗) v r p τ σ then (1 : ℝ) else 0))
      ≤ 2 * Real.exp (-(τ ^ 2) / (2 * (1 * muOf 𝓗 v r p + τ / 3))) := by
    rw [hmean] at hcher
    simpa [devOf] using hcher
  have hprod : ∀ σ : edgeIdx 𝓗 v → Bool,
      (∏ e : edgeIdx 𝓗 v, (if σ e then (1 : ℝ) else (p : ℝ) ^ (r - 1) - 1))
        = ((p : ℝ) ^ (r - 1)) ^ (Fintype.card (edgeIdx 𝓗 v))
          * ∏ e : edgeIdx 𝓗 v, (if σ e then (1 : ℝ) / (p : ℝ) ^ (r - 1)
              else 1 - 1 / (p : ℝ) ^ (r - 1)) := by
    intro σ
    have h := Work.Deep.Prob.Colouring.prod_fibre_eq_pow_mul (ι := edgeIdx 𝓗 v)
      (K := p ^ (r - 1)) (Nat.one_le_pow (r - 1) p (le_trans (by norm_num) hp)) σ
    simpa [Nat.cast_pow] using h
  have hbig : (∑ σ : edgeIdx 𝓗 v → Bool,
        (∏ e : edgeIdx 𝓗 v, (if σ e then (1 : ℝ) else (p : ℝ) ^ (r - 1) - 1))
          * (if devOf (𝓗 := 𝓗) v r p τ σ then (1 : ℝ) else 0))
      ≤ ((p : ℝ) ^ (r - 1)) ^ (Fintype.card (edgeIdx 𝓗 v))
          * (2 * Real.exp (-(τ ^ 2) / (2 * (1 * muOf 𝓗 v r p + τ / 3)))) := by
    calc (∑ σ : edgeIdx 𝓗 v → Bool,
          (∏ e : edgeIdx 𝓗 v, (if σ e then (1 : ℝ) else (p : ℝ) ^ (r - 1) - 1))
            * (if devOf (𝓗 := 𝓗) v r p τ σ then (1 : ℝ) else 0))
        = ∑ σ : edgeIdx 𝓗 v → Bool, ((((p : ℝ) ^ (r - 1)) ^ (Fintype.card (edgeIdx 𝓗 v)))
            * ∏ e : edgeIdx 𝓗 v, (if σ e then (1 : ℝ) / (p : ℝ) ^ (r - 1)
                else 1 - 1 / (p : ℝ) ^ (r - 1)))
            * (if devOf (𝓗 := 𝓗) v r p τ σ then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro σ _
          rw [hprod σ]
      _ = ((p : ℝ) ^ (r - 1)) ^ (Fintype.card (edgeIdx 𝓗 v))
            * ∑ σ : edgeIdx 𝓗 v → Bool,
              (∏ e : edgeIdx 𝓗 v, (if σ e then (1 : ℝ) / (p : ℝ) ^ (r - 1)
                else 1 - 1 / (p : ℝ) ^ (r - 1))) * (if devOf (𝓗 := 𝓗) v r p τ σ then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro σ _
          ring
      _ ≤ ((p : ℝ) ^ (r - 1)) ^ (Fintype.card (edgeIdx 𝓗 v))
            * (2 * Real.exp (-(τ ^ 2) / (2 * (1 * muOf 𝓗 v r p + τ / 3)))) :=
          mul_le_mul_of_nonneg_left hcher2 (by positivity)
  have hfinal : ((Finset.univ.filter (fun c : Fin n → Fin p =>
        c v = i ∧ devOf (𝓗 := 𝓗) v r p τ (patOf (𝓗 := 𝓗) v i c))).card : ℝ)
      ≤ (p : ℝ) ^ (n - 1) * (2 * Real.exp (-(τ ^ 2) / (2 * (1 * muOf 𝓗 v r p + τ / 3)))) := by
    rw [hX]
    calc (∑ σ : edgeIdx 𝓗 v → Bool,
          (((Finset.univ.filter (fun c : Fin n → Fin p =>
              c v = i ∧ patOf (𝓗 := 𝓗) v i c = σ)).card : ℝ)
            * (if devOf (𝓗 := 𝓗) v r p τ σ then (1:ℝ) else 0)))
        = (p : ℝ) ^ (n - (Finset.univ.biUnion (blkF (𝓗 := 𝓗) v)).card - 1)
            * (∑ σ : edgeIdx 𝓗 v → Bool,
              (∏ e : edgeIdx 𝓗 v, (if σ e then (1 : ℝ) else (p : ℝ) ^ (r - 1) - 1))
                * (if devOf (𝓗 := 𝓗) v r p τ σ then (1 : ℝ) else 0)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro σ _
          rw [card_pat_eq v hr hlin hrsize i σ]
          ring
      _ ≤ (p : ℝ) ^ (n - (Finset.univ.biUnion (blkF (𝓗 := 𝓗) v)).card - 1)
            * (((p : ℝ) ^ (r - 1)) ^ (Fintype.card (edgeIdx 𝓗 v))
              * (2 * Real.exp (-(τ ^ 2) / (2 * (1 * muOf 𝓗 v r p + τ / 3))))) :=
          mul_le_mul_of_nonneg_left hbig (by positivity)
      _ = (p : ℝ) ^ (n - 1) * (2 * Real.exp (-(τ ^ 2) / (2 * (1 * muOf 𝓗 v r p + τ / 3)))) := by
          rw [show ((p : ℝ) ^ (r - 1)) ^ (Fintype.card (edgeIdx 𝓗 v))
              = (p : ℝ) ^ ((Finset.univ.biUnion (blkF (𝓗 := 𝓗) v)).card) from by
                rw [← pow_mul, hWcard]]
          rw [← mul_assoc, ← pow_add]
          rw [show n - (Finset.univ.biUnion (blkF (𝓗 := 𝓗) v)).card - 1
                + (Finset.univ.biUnion (blkF (𝓗 := 𝓗) v)).card = n - 1 from by omega]
  rw [hstep1]
  exact hfinal

end

end Work.Deep.Nibble
