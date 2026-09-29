import Mathlib

/-!
# The scale schedule for the finite rational tower (`rat_tower_lower`)
-/

namespace Work.TMComp.C7Aux

noncomputable section

/-- The largest index `i ≤ k` with `A * Q i ≤ N` (the largest usable approximant at scale `N`).
Returns `0` if no index is usable. -/
def rtlIdx (A : ℝ) (Q : ℕ → ℕ) (k : ℕ) (N : ℕ) : ℕ :=
  Nat.findGreatest (fun i => A * (Q i : ℝ) ≤ (N : ℝ)) k

/-- The multiplier attached to the index `i`. -/
def rtlMM (cκ : ℝ) (Q : ℕ → ℕ) (i : ℕ) : ℕ :=
  Q i * max 1 (Nat.floor (Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ))))

/-- The `(scale, index)` recursion of the tower. -/
def rtlU (A cκ : ℝ) (Q : ℕ → ℕ) (k N₀ : ℕ) : ℕ → ℕ × ℕ
  | 0 => (N₀, rtlIdx A Q k N₀)
  | (s+1) => (rtlMM cκ Q (rtlU A cκ Q k N₀ s).2 * (rtlU A cκ Q k N₀ s).1,
              rtlIdx A Q k (rtlMM cκ Q (rtlU A cκ Q k N₀ s).2 * (rtlU A cκ Q k N₀ s).1))

def rtlN (A cκ : ℝ) (Q : ℕ → ℕ) (k N₀ : ℕ) (s : ℕ) : ℕ := (rtlU A cκ Q k N₀ s).1
def rtli (A cκ : ℝ) (Q : ℕ → ℕ) (k N₀ : ℕ) (s : ℕ) : ℕ := (rtlU A cκ Q k N₀ s).2

@[simp] theorem rtlN_zero (A cκ : ℝ) (Q : ℕ → ℕ) (k N₀ : ℕ) : rtlN A cκ Q k N₀ 0 = N₀ := rfl

theorem rtlN_succ (A cκ : ℝ) (Q : ℕ → ℕ) (k N₀ : ℕ) (s : ℕ) :
    rtlN A cκ Q k N₀ (s+1) = rtlMM cκ Q (rtli A cκ Q k N₀ s) * rtlN A cκ Q k N₀ s := rfl

theorem rtli_eq_idx (A cκ : ℝ) (Q : ℕ → ℕ) (k N₀ : ℕ) (s : ℕ) :
    rtli A cκ Q k N₀ s = rtlIdx A Q k (rtlN A cκ Q k N₀ s) := by
  induction s with
  | zero => rfl
  | succ s ih =>
      show (rtlU A cκ Q k N₀ (s+1)).2 = rtlIdx A Q k (rtlU A cκ Q k N₀ (s+1)).1
      rfl

theorem rtlIdx_le (A : ℝ) (Q : ℕ → ℕ) (k N : ℕ) : rtlIdx A Q k N ≤ k := Nat.findGreatest_le k

theorem rtlIdx_spec {A : ℝ} {Q : ℕ → ℕ} {k N : ℕ} (h : A * (Q 0 : ℝ) ≤ (N : ℝ)) :
    A * (Q (rtlIdx A Q k N) : ℝ) ≤ (N : ℝ) :=
  Nat.findGreatest_spec (P := fun i => A * (Q i : ℝ) ≤ (N : ℝ)) (Nat.zero_le k) h

theorem rtlIdx_greatest {A : ℝ} {Q : ℕ → ℕ} {k N i : ℕ} (h : rtlIdx A Q k N = i) (hik : i < k) :
    ¬ (A * (Q (i+1) : ℝ) ≤ (N : ℝ)) := by
  have h' := (Nat.findGreatest_eq_iff (P := fun j => A * (Q j : ℝ) ≤ (N : ℝ))).mp h
  exact h'.2.2 (n := i+1) (Nat.lt_succ_self i) (by omega)

theorem rtlIdx_mono {A : ℝ} {Q : ℕ → ℕ} {k : ℕ} {N N' : ℕ} (hNN' : N ≤ N')
    (h : A * (Q 0 : ℝ) ≤ (N : ℝ)) : rtlIdx A Q k N ≤ rtlIdx A Q k N' := by
  have hm := rtlIdx_spec (k := k) h
  have hm' : A * (Q (rtlIdx A Q k N) : ℝ) ≤ (N' : ℝ) := le_trans hm (by exact_mod_cast hNN')
  exact Nat.le_findGreatest (rtlIdx_le A Q k N) hm'

theorem rtli_le (A cκ : ℝ) (Q : ℕ → ℕ) (k N₀ s : ℕ) : rtli A cκ Q k N₀ s ≤ k := by
  rw [rtli_eq_idx]; exact rtlIdx_le _ _ _ _

theorem rtli_spec {A cκ : ℝ} {Q : ℕ → ℕ} {k N₀ : ℕ} {s : ℕ}
    (h : A * (Q 0 : ℝ) ≤ (rtlN A cκ Q k N₀ s : ℝ)) :
    A * (Q (rtli A cκ Q k N₀ s) : ℝ) ≤ (rtlN A cκ Q k N₀ s : ℝ) := by
  rw [rtli_eq_idx]; exact rtlIdx_spec h

theorem rtli_greatest {A cκ : ℝ} {Q : ℕ → ℕ} {k N₀ s : ℕ}
    (h : rtli A cκ Q k N₀ s < k) :
    ¬ (A * (Q (rtli A cκ Q k N₀ s + 1) : ℝ) ≤ (rtlN A cκ Q k N₀ s : ℝ)) := by
  rw [rtli_eq_idx] at h ⊢
  exact rtlIdx_greatest rfl h

theorem rtlMM_pos (cκ : ℝ) (Q : ℕ → ℕ) {i : ℕ} (hi : 1 ≤ Q i) : 1 ≤ rtlMM cκ Q i := by
  unfold rtlMM
  calc (1 : ℕ) = 1 * 1 := by ring
    _ ≤ Q i * max 1 (Nat.floor (Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ)))) :=
        Nat.mul_le_mul hi (le_max_left 1 _)

theorem rtlMM_three_le (cκ : ℝ) (Q : ℕ → ℕ) {i : ℕ} (hi : 3 ≤ Q i) : 3 ≤ rtlMM cκ Q i := by
  unfold rtlMM
  calc (3 : ℕ) = 3 * 1 := by ring
    _ ≤ Q i * max 1 (Nat.floor (Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ)))) :=
        Nat.mul_le_mul hi (le_max_left 1 _)

theorem rtlMM_dvd (cκ : ℝ) (Q : ℕ → ℕ) (i : ℕ) : Q i ∣ rtlMM cκ Q i := ⟨_, rfl⟩

theorem rtlMM_le (cκ : ℝ) (Q : ℕ → ℕ) (i : ℕ)
    (h : 1 ≤ Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ))) :
    (rtlMM cκ Q i : ℝ) ≤ Real.exp (cκ * (Q i : ℝ) / 2) / 5 := by
  have hf : 1 ≤ Nat.floor (Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ))) := by
    have := Nat.floor_pos.mpr h; omega
  have hmax : max 1 (Nat.floor (Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ))))
      = Nat.floor (Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ))) := max_eq_right hf
  have hfle : (Nat.floor (Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ))) : ℝ)
      ≤ Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ)) := Nat.floor_le (by positivity)
  have hQi : ((Q i : ℝ)) ≠ 0 := by
    intro h0; rw [h0] at h; norm_num at h
  have hmul : ((Q i : ℝ)) * (Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ)))
      = Real.exp (cκ * (Q i : ℝ) / 2) / 5 := by field_simp
  calc (rtlMM cκ Q i : ℝ)
      = (Q i : ℝ) * (Nat.floor (Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ))) : ℝ) := by
        unfold rtlMM; rw [hmax, Nat.cast_mul]
    _ ≤ (Q i : ℝ) * (Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ))) :=
        mul_le_mul_of_nonneg_left hfle (Nat.cast_nonneg _)
    _ = Real.exp (cκ * (Q i : ℝ) / 2) / 5 := hmul

theorem rtlMM_ge (cκ : ℝ) (Q : ℕ → ℕ) (i : ℕ)
    (h : 2 ≤ Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ))) :
    Real.exp (cκ * (Q i : ℝ) / 2) / 10 ≤ (rtlMM cκ Q i : ℝ) := by
  have hQi : 0 < Q i := by
    rcases Nat.eq_zero_or_pos (Q i) with h0 | h0
    · rw [h0] at h; norm_num at h
    · exact h0
  have hf : Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ)) / 2
      ≤ (Nat.floor (Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ))) : ℝ) := by
    have h2 := Nat.floor_le (show (0:ℝ) ≤ _ by positivity)
    have h3 := Nat.lt_floor_add_one (Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ)))
    linarith
  have hle : Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ)) / 2
      ≤ ((max 1 (Nat.floor (Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ))))) : ℕ) := by
    have h4 : (Nat.floor (Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ))) : ℝ)
        ≤ ((max 1 (Nat.floor (Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ))))) : ℕ) := by
      exact_mod_cast (le_max_right 1 (Nat.floor (Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ)))))
    linarith
  have hfirst : Real.exp (cκ * (Q i : ℝ) / 2) / 10
      = (Q i : ℝ) * (Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ)) / 2) := by
    field_simp; ring
  calc Real.exp (cκ * (Q i : ℝ) / 2) / 10
      = (Q i : ℝ) * (Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ)) / 2) := hfirst
    _ ≤ (Q i : ℝ) * ((max 1 (Nat.floor
          (Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ))))) : ℕ) :=
        mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)
    _ = (rtlMM cκ Q i : ℝ) := by unfold rtlMM; rw [Nat.cast_mul]

theorem rtlN_mono (A cκ : ℝ) (Q : ℕ → ℕ) (k N₀ : ℕ) (hQ : ∀ i ≤ k, 1 ≤ Q i) :
    Monotone (rtlN A cκ Q k N₀) := by
  apply monotone_nat_of_le_succ
  intro s
  rw [rtlN_succ]
  have h1 : 1 ≤ rtlMM cκ Q (rtli A cκ Q k N₀ s) :=
    rtlMM_pos cκ Q (hQ _ (rtli_le A cκ Q k N₀ s))
  exact Nat.le_mul_of_pos_left _ (by omega)

theorem N₀_le_rtlN (A cκ : ℝ) (Q : ℕ → ℕ) (k N₀ : ℕ) (hQ : ∀ i ≤ k, 1 ≤ Q i) (s : ℕ) :
    N₀ ≤ rtlN A cκ Q k N₀ s := by
  have h := (rtlN_mono A cκ Q k N₀ hQ) (Nat.zero_le s)
  rwa [rtlN_zero] at h


theorem rtli_mono (A cκ : ℝ) (Q : ℕ → ℕ) (k N₀ : ℕ) (hQ : ∀ i ≤ k, 1 ≤ Q i)
    (hA0 : A * (Q 0 : ℝ) ≤ (N₀ : ℝ)) :
    Monotone (rtli A cκ Q k N₀) := by
  intro s t hst
  rw [rtli_eq_idx, rtli_eq_idx]
  refine rtlIdx_mono ((rtlN_mono A cκ Q k N₀ hQ) hst) ?_
  exact le_trans hA0 (by exact_mod_cast N₀_le_rtlN A cκ Q k N₀ hQ s)

/-- Along a run of constant index `i`, the scales are exactly the successive multiples by
`rtlMM cκ Q i`. -/
theorem rtlN_eq_pow (A cκ : ℝ) (Q : ℕ → ℕ) (k N₀ : ℕ) (i t1 : ℕ) :
    ∀ n : ℕ, (∀ u, t1 ≤ u → u < t1 + n → rtli A cκ Q k N₀ u = i) →
      rtlN A cκ Q k N₀ (t1 + n) = (rtlMM cκ Q i)^n * rtlN A cκ Q k N₀ t1 := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
      intro h
      have h1 : rtli A cκ Q k N₀ (t1 + n) = i := h _ (by omega) (by omega)
      have h2 : ∀ u, t1 ≤ u → u < t1 + n → rtli A cκ Q k N₀ u = i :=
        fun u hu hu' => h u hu (by omega)
      rw [show t1 + (n+1) = (t1 + n) + 1 by omega, rtlN_succ, h1, ih h2]
      ring

end
end Work.TMComp.C7Aux
