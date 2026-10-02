import Submission.Work.Deep.Nibble.FamWTAux

/-!
# The weighted kept count `Z`, and the elementary bounds on `badSum`

`Zsum 𝓖 ω S = ∑_e |e ∩ S| · 1[ω e]` is the (linear in `θ`) weighted count of the
kept edges meeting `S`.  It is the statistic whose deviation controls the *size of
the Bruhn--Joos certificate* of the per-set waste (`r2_Wfam_tail`): on the event
`Z ≤ 4θ|S|` the certificate (all bad kept edges meeting `S`, plus one kept witness
each) has at most `8θ|S|` coordinates.

The elementary bounds recorded here are

* `badSum_le_Zsum` — the waste is dominated by `Z`;
* `Zsum_le_sum_hd` — `Z` is dominated by the degree sum over `S`;
* `badSum_le_two_mul_D` — hence `badSum ≤ 2D|S|` under `(1±ε)`-regularity with
  `ε ≤ 1` (the bound `M` of `bj_talagrand`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The weighted kept count through `S`: `∑_e |e ∩ S| · 1[ω e]`. -/
noncomputable def Zsum (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) : ℕ :=
  ∑ e : 𝓖, if ω e then ((e : Set V) ∩ (S : Set V)).ncard else 0

/-- The edge-charged waste is dominated by the weighted kept count. -/
lemma badSum_le_Zsum' (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) :
    badSum 𝓖 ω S ≤ Zsum 𝓖 ω S :=
  badSum_le_Zsum 𝓖 ω S

/-- `Z` is dominated by the degree sum over `S`. -/
lemma Zsum_le_sum_hd (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) :
    Zsum 𝓖 ω S ≤ ∑ v ∈ S, hd 𝓖 v := by
  classical
  have h3 : (∑ e : 𝓖, (((e : Set V) ∩ (S : Set V)).ncard : ℕ)) = ∑ v ∈ S, hd 𝓖 v := by
    exact_mod_cast sum_ncard_inter_eq_sum_hd 𝓖 S
  calc Zsum 𝓖 ω S
      ≤ ∑ e : 𝓖, ((e : Set V) ∩ (S : Set V)).ncard := by
        refine Finset.sum_le_sum fun e _ => ?_
        split_ifs <;> omega
    _ = ∑ v ∈ S, hd 𝓖 v := h3

/-- Under `(1±ε)`-regularity with `ε ≤ 1`, the waste inside `S` is at most
`2 D |S|`. -/
lemma badSum_le_two_mul_D {𝓖 : Set (Set V)} {ε : ℝ} (hε1 : ε ≤ 1) {D : ℕ}
    (hdeg : ∀ v : V, |((hd 𝓖 v : ℝ)) - (D : ℝ)| ≤ ε * (D : ℝ))
    (ω : 𝓖 → Bool) (S : Finset V) :
    badSum 𝓖 ω S ≤ 2 * D * S.card := by
  classical
  have hDnn : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
  have hbound : ∀ v : V, hd 𝓖 v ≤ 2 * D := by
    intro v
    have h := hdeg v
    rw [abs_le] at h
    have hεD : ε * (D : ℝ) ≤ (D : ℝ) := by
      have := mul_le_mul_of_nonneg_right hε1 hDnn
      simpa using this
    have this : (hd 𝓖 v : ℝ) ≤ 2 * (D : ℝ) := by linarith [h.2, hεD]
    exact_mod_cast this
  calc badSum 𝓖 ω S ≤ ∑ v ∈ S, hd 𝓖 v := badSum_le_sum_hd 𝓖 ω S
    _ ≤ ∑ _v ∈ S, 2 * D := Finset.sum_le_sum fun v _ => hbound v
    _ = 2 * D * S.card := by rw [Finset.sum_const, smul_eq_mul]; ring

end Work.Deep.Nibble
