import Mathlib
import Submission.Work.Peluse.SwapC.cgenSlotsEndpoints
import Submission.Work.Peluse.SwapC.cprocBookkeeping
import Submission.Work.Peluse.SwapC.cgenSlotsLength
import Submission.Work.Peluse.SwapC.cStep
import Submission.Work.Peluse.SwapC.concatStep
import Submission.Work.Peluse.SwapC.cStZeroIdent
import Submission.Work.Peluse.SwapC.cStFinalIdent

/-! # `Work.Peluse.SwapC.concatAll`: the assembly of KKL Proposition 6.2

The state `cSt I q M N f (genuineSlots (cproc s k))` is compared along the `2^s - 1` splits of the
process (`cprocBookkeeping`), each split costing a power of `δ` (`cStep`, the analytic increment
built on `concatStep`).  On the way through we use the two ends (`cgenSlotsEndpoints`): the state at
`k = 0` is the hypothesis of `concatAll` and the state at `k = 2^s - 1` is its conclusion. -/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap
open CC

/-- Splitting off a single coordinate of a function space. -/
private def piSingleEquiv {α I : Type} [DecidableEq α] (a : α) :
    (α → I) ≃ I × ({x : α // x ≠ a} → I) where
  toFun f := (f a, fun x => f x.1)
  invFun p := fun x => if h : x = a then p.1 else p.2 ⟨x, h⟩
  left_inv f := by
    funext x
    by_cases h : x = a
    · subst h; simp
    · simp [h]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · simp
    · funext x; simp [x.2]

/-- **The average over a function space of a function of one coordinate is the average over that
coordinate** (`α` finite). -/
private lemma avg_pi_single {α I : Type} [Fintype α] [DecidableEq α] [Fintype I] [Nonempty I]
    (a : α) (F : I → ℝ) : avg (fun f : α → I => F (f a)) = avg F := by
  classical
  have h1 : (∑ f : α → I, F (f a))
      = ∑ p : I × ({x : α // x ≠ a} → I), F p.1 := by
    refine Fintype.sum_equiv (piSingleEquiv a) _ _ ?_
    intro f; rfl
  have hcard : Fintype.card (α → I)
      = Fintype.card I * Fintype.card ({x : α // x ≠ a} → I) := by
    rw [Fintype.card_congr (piSingleEquiv a), Fintype.card_prod]
  have h2 : (∑ i : I, ∑ _r : ({x : α // x ≠ a} → I), F i)
      = ((Fintype.card ({x : α // x ≠ a} → I) : ℝ)) * ∑ i : I, F i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [avg, avg, h1, Fintype.sum_prod_type, h2, hcard]
  push_cast
  field_simp

/-! ## Elementary list facts used by the assembly -/

variable {s : ℕ}

private lemma find?_exists {α : Type*} (p : α → Bool) :
    ∀ {l : List α}, (∃ a ∈ l, p a = true) → ∃ a, l.find? p = some a := by
  intro l
  induction l with
  | nil => intro h; obtain ⟨a, ha, _⟩ := h; exact absurd ha (by simp)
  | cons b t ih =>
    intro h
    by_cases hb : p b = true
    · exact ⟨b, List.find?_cons_of_pos hb⟩
    · obtain ⟨a, ha, hpa⟩ := h
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact absurd hpa hb
      · obtain ⟨c, hc⟩ := ih ⟨a, ha', hpa⟩
        exact ⟨c, by rw [List.find?_cons_of_neg hb]; exact hc⟩

private lemma find?_mem {α : Type*} {p : α → Bool} :
    ∀ {l : List α} {a : α}, l.find? p = some a → a ∈ l := by
  intro l
  induction l with
  | nil => intro a h; exact absurd h (by simp)
  | cons b t ih =>
    intro a h
    by_cases hb : p b = true
    · rw [List.find?_cons_of_pos hb] at h
      exact List.mem_cons.mpr (Or.inl (Option.some.inj h).symm)
    · rw [List.find?_cons_of_neg hb] at h
      exact List.mem_cons_of_mem _ (ih h)

private lemma csplitFirst_eq_self {Λ : List (CLeaf s)} (h : ∀ l ∈ Λ, ¬ (l.dep < s)) :
    csplitFirst Λ = Λ := by
  induction Λ with
  | nil => rfl
  | cons a t ih =>
    have ha : ¬ (a.dep < s) := h a (List.mem_cons_self ..)
    rw [csplitFirst, dif_neg ha]
    rw [ih (fun l hl => h l (List.mem_cons_of_mem _ hl))]

private lemma exists_splittable {Λ : List (CLeaf s)} (h : csplitFirst Λ ≠ Λ) :
    ∃ l ∈ Λ, l.dep < s := by
  by_contra hcon
  push_neg at hcon
  exact h (csplitFirst_eq_self (fun l hl => by have := hcon l hl; omega))

/-- **KKL Proposition 6.2 (full concatenation)**, verbatim from
`Submission/Work/Peluse/P2P3_STATEMENTS.lean.txt`.  All `s` raw slots are concatenated: slot `k` of
the output is `q (ι ε) j − q (ι ε') j` for `(j, ε, ε') = slotAt s k`, i.e. the slot set
`slotSet s` of `Holds/SwapDefs.lean`.

The proof is KKL's `s`-stage iteration of `concatStep`: at stage `r` each current leaf's raw slot
`s−r` is concatenated, the other leaves' raw slots being frozen into the function via `pbox_peel`,
followed by Jensen's inequality (convexity of `x ↦ x^e`, available as
`Work.Peluse.Holds.ExpPET.pow_mean_avg_le`).  `concatStep` may be assumed as a hypothesis. -/
theorem concatAll : ∀ s : ℕ, 1 ≤ s → ∃ C : ℝ, 0 < C ∧ ∃ e : ℕ, 1 ≤ e ∧
    ∀ (I : Type) [Fintype I] [Nonempty I] (q : I → Fin s → ℤ) (M N : ℕ) (δ : ℝ) (f : ℤ → ℂ),
      1 ≤ M → Work.Peluse.SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) → 0 < δ →
      δ ≤ Work.Peluse.LadderP.Swap.avg (fun i : I =>
            Work.Peluse.LadderP.Swap.pbox s (q i) (fun _ => 0) M (Work.Peluse.symIcc N) f) →
      C * δ ^ e ≤ Work.Peluse.LadderP.Swap.avg (fun ι : (Fin s → Bool) → I =>
        Work.Peluse.LadderP.Swap.pbox (Work.Peluse.LadderP.Swap.slotCard s)
          (fun k => q (ι (Work.Peluse.LadderP.Swap.slotAt s k).2.1)
            (Work.Peluse.LadderP.Swap.slotAt s k).1)
          (fun k => q (ι (Work.Peluse.LadderP.Swap.slotAt s k).2.2)
            (Work.Peluse.LadderP.Swap.slotAt s k).1) M (Work.Peluse.symIcc N) f) := by
  intro s hs
  -- the process facts
  obtain ⟨hsub, hlen, hfin, hsplit⟩ := cprocBookkeeping s
  obtain ⟨hend0, hendf⟩ := cgenSlotsEndpoints s
  have hnod : ∀ k : ℕ, (cproc s k).Nodup := cprocNodup s hsub
  -- the uniform constants of the step lemma, at a bound valid for every state
  obtain ⟨C₀, hC₀, e₀, he₀, hstep⟩ := cStep Work.Peluse.SwapC.concatStep (s * 2 ^ s + s * 4 ^ s)
  -- the iterated constants
  set F : ℝ → ℝ := fun x => C₀ * x ^ e₀ with hF
  set A : ℕ → ℝ := fun k => (F^[k]) 1 with hA
  set E : ℕ → ℕ := fun k => e₀ ^ k with hE
  have hA0 : A 0 = 1 := by rw [hA]; rfl
  have hAsucc : ∀ k, A (k + 1) = C₀ * (A k) ^ e₀ := by
    intro k
    rw [hA]
    show F^[k + 1] 1 = C₀ * F^[k] 1 ^ e₀
    rw [Function.iterate_succ_apply', hF]
  have hApos : ∀ k, 0 < A k := by
    intro k
    induction k with
    | zero => rw [hA0]; norm_num
    | succ k ih => rw [hAsucc]; positivity
  have hE0 : E 0 = 1 := by rw [hE]; rfl
  have hEsucc : ∀ k, E (k + 1) = e₀ * E k := by
    intro k
    rw [hE]
    show e₀ ^ (k + 1) = e₀ * e₀ ^ k
    rw [pow_succ]
    ring
  have hE1 : ∀ k, 1 ≤ E k := by
    intro k
    induction k with
    | zero => rw [hE0]
    | succ k ih => rw [hEsucc k]; nlinarith [Nat.one_le_pow k e₀ he₀]
  -- the length bound of the states
  have hlenD : ∀ k ≤ 2 ^ s - 1, (genuineSlots (cproc s k)).length ≤ s * 2 ^ s + s * 4 ^ s := by
    intro k hk
    have h1 := cgenSlotsLength (cproc s k)
    have h2 : (cproc s k).length = k + 1 := hlen k hk
    have h3 : k + 1 ≤ 2 ^ s := by
      have : 0 < 2 ^ s := by positivity
      omega
    have h4 : (cproc s k).length * (cproc s k).length ≤ 2 ^ s * 2 ^ s := by
      rw [h2]; exact Nat.mul_le_mul h3 h3
    have h5 : 2 ^ s * 2 ^ s = 4 ^ s := by rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
    rw [h5] at h4
    have h6 : s * (cproc s k).length ≤ s * 2 ^ s := Nat.mul_le_mul_left s (by rw [h2]; exact h3)
    have h7 : s * (cproc s k).length * (cproc s k).length ≤ s * 4 ^ s := by
      calc s * (cproc s k).length * (cproc s k).length
          = s * ((cproc s k).length * (cproc s k).length) := by ring
        _ ≤ s * 4 ^ s := Nat.mul_le_mul_left s h4
    omega
  refine ⟨A (2 ^ s - 1), hApos _, E (2 ^ s - 1), hE1 _, ?_⟩
  intro I _ _ q M N δ f hM hsupp hb hδ hhyp
  -- the chain along the process
  have key : ∀ k, k ≤ 2 ^ s - 1 →
      A k * δ ^ (E k) ≤ cSt I q M N f (genuineSlots (cproc s k)) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [hA0, hE0, pow_one, one_mul]
      rw [cStZeroIdent I s q M N f hend0]
      exact hhyp
    | succ k ih =>
      intro hk
      have hk' : k ≤ 2 ^ s - 1 := by omega
      have hih : A k * δ ^ (E k) ≤ cSt I q M N f (genuineSlots (cproc s k)) := ih hk'
      -- the process moved: `csplitFirst` did change the list
      have hne : csplitFirst (cproc s k) ≠ cproc s k := by
        intro hcon
        have h1 : (cproc s (k + 1)).length = k + 2 := by
          have := hlen (k + 1) (by omega)
          omega
        have h2 : (cproc s (k + 1)).length = (cproc s k).length := by
          rw [show cproc s (k + 1) = csplitFirst (cproc s k) from rfl, hcon]
        rw [hlen k hk'] at h2
        omega
      obtain ⟨l₀, hl₀mem, hl₀d⟩ := exists_splittable hne
      obtain ⟨l, hl⟩ : ∃ l : CLeaf s, cnextLeaf (cproc s k) = some l := by
        refine find?_exists (fun l : CLeaf s => decide (l.dep < s)) ⟨l₀, hl₀mem, ?_⟩
        simp [hl₀d]
      have hlmem : l ∈ cproc s k := find?_mem hl
      have hld : l.dep < s := by
        have := List.find?_some hl
        simpa using this
      have hsplitk : csplitFirst (cproc s k) = refine (cproc s k) l :=
        hsplit (cproc s k) l hld (hnod k) hl
      have hstepk := hstep I s q M N f (cproc s k) l (A k * δ ^ (E k))
        (hsub k) (hnod k) hlmem hld (hlenD k hk') hM hsupp hb (mul_pos (hApos k) (pow_pos hδ _)) hih
      have hck : cproc s (k + 1) = refine (cproc s k) l := by
        rw [show cproc s (k + 1) = csplitFirst (cproc s k) from rfl, hsplitk]
      have harith : C₀ * (A k * δ ^ (E k)) ^ e₀ = A (k + 1) * δ ^ (E (k + 1)) := by
        rw [hAsucc, hEsucc k, mul_pow, ← pow_mul, mul_comm (E k) e₀]
        ring
      rw [hck, ← harith]
      exact hstepk
  have hfin_key := key (2 ^ s - 1) (le_refl _)
  rw [cStFinalIdent I s hs q M N f (hendf hs hfin)] at hfin_key
  exact hfin_key

end

end Work.Peluse.SwapC
