import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.charValDefs
import Submission.Work.EQ.fan_base
import Submission.Work.EQ.charVal_aux
import Submission.Work.EQ.walk_count_defs
import Submission.Work.EQ.walk_gamma_params

namespace Work.EQ

/-! ### The endpoint correction `wtRho` and the main induction

The proof uses the correction factor `wtRho` of `Work.EQ.walk_count_defs`: the weight of a word
`l` that runs from the state `n` to the state `m` is bounded by `γ ^ (l.count false) * wtRho a γ n m`.
Since `wtRho a γ n n = 1`, this gives the theorem for closed walks at any state. -/

/-- `wtRho` at `n = m` is `1` (empty product). -/
lemma wc_rho_self (a γ : ℝ) (n : ℕ) : wtRho a γ n n = 1 := by
  simp only [wtRho, if_pos (le_refl n), Finset.Ico_self, Finset.prod_empty]

/-- After an up-step `n → n+1` towards a target at level `≥ n+1`, the correction `wtRho` gains
exactly the factor `upW a n / γ`. -/
lemma wc_rho_up {a γ : ℝ} {n m : ℕ} (h : n + 1 ≤ m) :
    wtRho a γ n m = upW a n / γ * wtRho a γ (n + 1) m := by
  have hnm : n ≤ m := by omega
  have hlt : n < m := by omega
  simp only [wtRho, if_pos hnm, if_pos h]
  rw [← Finset.insert_Ico_add_one_left_eq_Ico hlt,
    Finset.prod_insert (by simp only [Finset.mem_Ico]; omega)]

/-- After a down-step `n+1 → n` towards a target at level `≤ n`, the correction `wtRho` gains
exactly the factor `dnW a (n+1)`. -/
lemma wc_rho_dn {a γ : ℝ} {n m : ℕ} (h : m ≤ n) :
    wtRho a γ (n + 1) m = wtRho a γ n m * dnW a (n + 1) := by
  rcases lt_or_eq_of_le h with hlt | heq
  · have h1 : ¬ n + 1 ≤ m := by omega
    have h2 : ¬ n ≤ m := by omega
    simp only [wtRho, if_neg h1, if_neg h2]
    rw [← Finset.insert_Ico_right_eq_Ico_add_one (by omega : m ≤ n),
      Finset.prod_insert (by simp only [Finset.mem_Ico]; omega)]
    exact mul_comm _ _
  · rw [heq]
    have h1 : ¬ n + 1 ≤ n := by omega
    simp only [wtRho, if_neg h1, if_pos (le_refl n)]
    rw [Finset.Ico_self, Finset.prod_empty, one_mul,
      ← Finset.insert_Ico_right_eq_Ico_add_one (le_refl n),
      Finset.prod_insert (by simp only [Finset.mem_Ico]; omega)]
    simp

/-- The correction `wtRho` is positive whenever `γ > 0`, the up weights are positive and the
down weights are positive from state `1` on. -/
lemma wc_rho_pos (a γ : ℝ) (hγ : 0 < γ) (hup : ∀ n : ℕ, 0 < upW a n)
    (hdn : ∀ n : ℕ, 1 ≤ n → 0 < dnW a n) (n m : ℕ) : 0 < wtRho a γ n m := by
  simp only [wtRho]
  split_ifs with h
  · exact Finset.prod_pos fun j _ => div_pos (hup j) hγ
  · exact Finset.prod_pos fun j hj => hdn (j + 1) (by
      have := (Finset.mem_Ico.mp hj).1
      omega)

/-- **The main induction.** For every word `l` running from the state `n` to the state `m`, its
weight product is at most `γ ^ (l.count false) * wtRho a γ n m`, provided `γ > 0` is at least the
extreme product `upW a j * dnW a (j+1)` for every `j`. The induction is on the word: each up-step
pays one factor `γ` (its `upW` is compensated by the matching down-step, via `γ ≥ c j`), while
the down-steps and the stationary step at `A₁` are absorbed by the correction `wtRho`. -/
private lemma wc_aux (a γ : ℝ) (hγ : 0 < γ) (hup : ∀ n : ℕ, 0 < upW a n)
    (hdn : ∀ n : ℕ, 1 ≤ n → 0 < dnW a n) (hc : ∀ n : ℕ, upW a n * dnW a (n + 1) ≤ γ)
    (h0 : stW a true 0 = 1) :
    ∀ l : List Bool, ∀ n m : ℕ, stAux l n = m →
      wtAux a l n ≤ γ ^ (l.count false) * wtRho a γ n m := by
  intro l
  induction l with
  | nil =>
    intro n m h
    simp only [stAux_nil] at h
    subst h
    simp [wtRho]
  | cons c l ih =>
    intro n m hst
    cases c with
    | false =>
      have hst' : stAux l (n + 1) = m := by simpa [stp] using hst
      have ih' := ih (n + 1) m hst'
      have hw : stW a false n = upW a n := rfl
      have hkey : upW a n * wtRho a γ (n + 1) m ≤ γ * wtRho a γ n m := by
        by_cases hle : n + 1 ≤ m
        · rw [wc_rho_up hle]
          have heq : γ * (upW a n / γ * wtRho a γ (n + 1) m)
              = upW a n * wtRho a γ (n + 1) m := by
            field_simp
          rw [heq]
        · have hm : m ≤ n := by omega
          rw [wc_rho_dn hm]
          have heq : upW a n * (wtRho a γ n m * dnW a (n + 1))
              = upW a n * dnW a (n + 1) * wtRho a γ n m := by ring
          rw [heq]
          exact mul_le_mul_of_nonneg_right (hc n) (le_of_lt (wc_rho_pos a γ hγ hup hdn n m))
      calc wtAux a (false :: l) n
          = upW a n * wtAux a l (n + 1) := by rw [wtAux_cons, stp_false, hw]
        _ ≤ upW a n * (γ ^ (l.count false) * wtRho a γ (n + 1) m) :=
            mul_le_mul_of_nonneg_left ih' (le_of_lt (hup n))
        _ = γ ^ (l.count false) * (upW a n * wtRho a γ (n + 1) m) := by ring
        _ ≤ γ ^ (l.count false) * (γ * wtRho a γ n m) :=
            mul_le_mul_of_nonneg_left hkey (pow_nonneg (le_of_lt hγ) _)
        _ = γ ^ ((false :: l).count false) * wtRho a γ n m := by
            rw [count_false_false_cons, pow_succ]; ring
    | true =>
      rcases eq_or_ne n 0 with hn | hn
      · subst hn
        have hst' : stAux l 0 = m := by simpa [stp] using hst
        have ih' := ih 0 m hst'
        calc wtAux a (true :: l) 0
            = wtAux a l 0 := by rw [wtAux_cons, stp_true_zero, h0, one_mul]
          _ ≤ γ ^ (l.count false) * wtRho a γ 0 m := ih'
          _ = γ ^ ((true :: l).count false) * wtRho a γ 0 m := by
              rw [count_false_true_cons]
      · obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        subst hk
        have hst' : stAux l k = m := by simpa [stp_true_succ] using hst
        have ih' := ih k m hst'
        have hnk : 1 ≤ k + 1 := by omega
        have hw : stW a true (k + 1) = dnW a (k + 1) := by
          simp [stW, abs_of_pos (hdn (k + 1) hnk)]
        have hkey : dnW a (k + 1) * wtRho a γ k m ≤ wtRho a γ (k + 1) m := by
          by_cases hle : k + 1 ≤ m
          · rw [wc_rho_up hle]
            have heq : dnW a (k + 1) * (upW a k / γ * wtRho a γ (k + 1) m)
                = (dnW a (k + 1) * upW a k / γ) * wtRho a γ (k + 1) m := by ring
            rw [heq]
            have h3 : dnW a (k + 1) * upW a k / γ ≤ 1 := by
              rw [div_le_one hγ]
              calc dnW a (k + 1) * upW a k = upW a k * dnW a (k + 1) := by ring
                _ ≤ γ := hc k
            simpa using mul_le_mul_of_nonneg_right h3
              (le_of_lt (wc_rho_pos a γ hγ hup hdn (k + 1) m))
          · have hm : m ≤ k := by omega
            exact le_of_eq (by rw [wc_rho_dn hm]; ring)
        calc wtAux a (true :: l) (k + 1)
            = dnW a (k + 1) * wtAux a l k := by rw [wtAux_cons, stp_true_succ, hw]
          _ ≤ dnW a (k + 1) * (γ ^ (l.count false) * wtRho a γ k m) :=
              mul_le_mul_of_nonneg_left ih' (le_of_lt (hdn (k + 1) hnk))
          _ = γ ^ (l.count false) * (dnW a (k + 1) * wtRho a γ k m) := by ring
          _ ≤ γ ^ (l.count false) * wtRho a γ (k + 1) m :=
              mul_le_mul_of_nonneg_left hkey (pow_nonneg (le_of_lt hγ) _)
          _ = γ ^ ((true :: l).count false) * wtRho a γ (k + 1) m := by
              rw [count_false_true_cons]

/-- **Exponentially few non-principal letters in a returning word (Rychlik Lemma 13).**

With `charValDefs.lean`'s walk: `stAux l 0 = 0` says the word `l`, read in chronological order,
returns to the centre `A₁`, and `wtAux a l 0` is the modulus of the corresponding weight product
(the characteristic value). `l.count false` is the number of non-principal letters, i.e. of
up-steps of the walk (a `false` letter always moves the state from `n` to `n+1`).

The claim: there is a *uniform* `γ < 1` (depending only on `a`) such that every returning word's
weight product is at most `γ ^ (l.count false)`. Consequently only `O(log (1/η))` non-principal
letters can occur in a returning word whose value is at least `η`.

Route (the only place where the equichordal numbers enter): put
`c n = upW a n * dnW a (n+1)`; each `c n` is `< 1` and `c n → λ² < 1`, so
`γ := max {c 0, c 1, λ²(1 + 1/stQ a 2)(1 - 1/stQ a 3)} < 1` is a uniform bound. A *closed* walk at
level `n` (staying `≥ n`) is a concatenation of excursions: `false` (up to `n+1`), a closed walk
at level `n+1`, `true` (down to `n`). Exactly one up-step per excursion, so each excursion
contributes `c n` times the (inductively bounded) factor of its inner walk; a `true` letter at
level `0` is stationary (weight `1`). This gives `wtAux a l 0 ≤ γ ^ (l.count false)` by strong
induction on the word. Note `l.count false = 0` forces all letters to be stationary, where the
product is `1 = γ ^ 0`, consistent with the statement. -/
theorem walk_count {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧
      ∀ l : List Bool, stAux l 0 = 0 → wtAux a l 0 ≤ γ ^ (l.count false) := by
  obtain ⟨hγpos, hγlt, hup, hdn, _, hc⟩ := walk_gamma_params ha0 ha1
  refine ⟨upW a 0 * dnW a 1, hγpos, hγlt, fun l hl => ?_⟩
  have h0 : stW a true 0 = 1 := stW_true_zero ha0 ha1
  have h := wc_aux a (upW a 0 * dnW a 1) hγpos hup hdn hc h0 l 0 0 hl
  rw [wc_rho_self] at h
  simpa using h

end Work.EQ
