/-
  `slot_aux` : elementary helpers for the slot lemma `Work.WilC4.slot_bound`.

  Nothing here is specific to the slot argument: deepness of a point of a `B`-free interval,
  continuity and constant sign of the fibre on such an interval, the telescoping product identity,
  the `4 |u-1|` bound for `|logb 2 u|`, and `(c/k)^{-e} = k^e c^{-e}`.
-/
import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.chain_arith

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC4

open Work.WilC4.Route (Gr InD valY ratioY eq_valY valY_mem)

variable {k : ℕ}

/-- Deepness at scale `M` of a point `t` of an interval `(a,b)` free of `B`, as soon as `t` is at
multiplicative distance `M` from the endpoints. -/
lemma isDeepR_of_free {B : Set (Fin (k + 1) → ℝ)} {c : Fin k → ℝ} {a b t M : ℝ}
    (hM : 0 < M) (ht : 0 < t) (hfree : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B)
    (htI : t ∈ Set.Ioo a b) (hlo : a < t / (2 * M)) (hhi : 2 * M * t < b) :
    IsDeepR B c M t := by
  intro b' hb' hcon
  rcases lt_or_ge a b' with h | h
  · have hb'ge : b ≤ b' := by
      by_contra hlt
      exact hfree b' ⟨h, lt_of_not_ge hlt⟩ hb'
    exact absurd hcon.2 (not_le.mpr (lt_of_lt_of_le hhi hb'ge))
  · exact absurd hcon.1 (not_le.mpr (lt_of_le_of_lt h hlo))

/-- On an interval free of `B₀`, `GoodFibre` makes `valY` continuous. -/
lemma valY_continuousOn_free {Y : Set (Fin (k + 2) → ℝ)}
    {B₀ : Set (Fin (k + 1) → ℝ)} {c : Fin k → ℝ} {a b : ℝ}
    (hgood : GoodFibre Y B₀) (hab : a < b)
    (hfree : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B₀) :
    ContinuousOn (fun z => valY Y c z) (Set.Ioo a b) := by
  obtain ⟨hu, hnz, hcont⟩ := hgood c a b hab hfree
  rw [Metric.continuousOn_iff]
  intro z hz ε hε
  obtain ⟨δ, hδ0, hδ⟩ := hcont z hz ε hε
  refine ⟨δ, hδ0, fun z' hz' hdist => ?_⟩
  have hInDz : InD Y c z := ((hu z hz).exists).imp fun y hy => hy
  have hInDz' : InD Y c z' := ((hu z' hz').exists).imp fun y hy => hy
  have h := hδ z' hz' _ _ (by simpa [Real.dist_eq] using hdist)
    (valY_mem Y c z hInDz) (valY_mem Y c z' hInDz')
  simpa [Real.dist_eq] using h

/-- On an interval free of `B₀`, `valY` has constant sign. -/
lemma valY_sign {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    {c : Fin k → ℝ} {a b : ℝ} (hgood : GoodFibre Y B₀) (hab : a < b)
    (hfree : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B₀) :
    (∀ z ∈ Set.Ioo a b, 0 < valY Y c z) ∨ (∀ z ∈ Set.Ioo a b, valY Y c z < 0) := by
  have hcont : ContinuousOn (fun z => valY Y c z) (Set.Ioo a b) :=
    valY_continuousOn_free hgood hab hfree
  obtain ⟨hu, hnz, -⟩ := hgood c a b hab hfree
  have hne : ∀ z ∈ Set.Ioo a b, valY Y c z ≠ 0 := fun z hz =>
    hnz z hz _ (valY_mem Y c z (((hu z hz).exists).imp fun y hy => hy))
  have hmem : ∀ z ∈ Set.Ioo a b, valY Y c z ∈ (fun z => valY Y c z) '' Set.Ioo a b :=
    fun z hz => ⟨z, hz, rfl⟩
  have hOC := (isPreconnected_Ioo.image _ hcont).ordConnected
  by_cases h : ∃ z ∈ Set.Ioo a b, 0 < valY Y c z
  · left
    obtain ⟨z₀, hz₀, hz₀pos⟩ := h
    intro z hz
    rcases lt_trichotomy (valY Y c z) 0 with hlt | heq | hgt
    · obtain ⟨w, hw, hw0⟩ := hOC.out (hmem z hz) (hmem z₀ hz₀) ⟨hlt.le, hz₀pos.le⟩
      exact absurd hw0 (hne w hw)
    · exact absurd heq (hne z hz)
    · exact hgt
  · right
    push Not at h
    intro z hz
    exact lt_of_le_of_ne (h z hz) (hne z hz)

/-- The fibre of `Y` at a point of an interval free of `B₀` is a genuine nonzero value. -/
lemma valY_gr_ne {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    {c : Fin k → ℝ} {a b : ℝ} (hgood : GoodFibre Y B₀) (hab : a < b)
    (hfree : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B₀) {x : ℝ} (hx : x ∈ Set.Ioo a b) :
    Gr Y c x (valY Y c x) ∧ valY Y c x ≠ 0 := by
  obtain ⟨hu, hnz, -⟩ := hgood c a b hab hfree
  have hInD : InD Y c x := ((hu x hx).exists).imp fun y hy => hy
  exact ⟨valY_mem Y c x hInD, hnz x hx _ (valY_mem Y c x hInD)⟩

/-- The telescoping identity for a product of consecutive quotients. -/
lemma prod_range_div_real (f : ℕ → ℝ) : ∀ K : ℕ, (∀ k ≤ K, f k ≠ 0) →
    ∏ k ∈ Finset.range K, (f (k + 1) / f k) = f K / f 0 := by
  intro K
  induction K with
  | zero => intro hne; rw [Finset.prod_range_zero, div_self (hne 0 (Nat.zero_le 0))]
  | succ n ih =>
    intro hne
    rw [Finset.prod_range_succ]
    rw [ih (fun k hk => hne k (le_trans hk (Nat.le_succ n)))]
    have h0 : f 0 ≠ 0 := hne 0 (Nat.zero_le _)
    have hn : f n ≠ 0 := hne n (Nat.le_succ n)
    have hn1 : f (n + 1) ≠ 0 := hne (n + 1) (Nat.le_refl _)
    field_simp

/-- `|logb 2 u| ≤ 4 |u - 1|` for `u ≥ 1/2`. -/
lemma abs_logb_two_le {u : ℝ} (hu : 1/2 ≤ u) :
    |Real.logb 2 u| ≤ 4 * |u - 1| := by
  have hlog : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogpos : (0:ℝ) < Real.log 2 := by linarith
  have h := abs_log_le_two_mul_abs_sub_one hu
  rw [Real.logb, abs_div, abs_of_pos hlogpos, div_le_iff₀ hlogpos]
  nlinarith [h, abs_nonneg (u - 1), hlog]

/-- `(c/k)^{-e} = k^e * c^{-e}` for `c, k > 0`. -/
lemma div_rpow_neg {c : ℝ} (hc : 0 < c) {kk : ℝ} (hk : 0 < kk) (e : ℝ) :
    (c / kk) ^ (-e) = kk ^ e * c ^ (-e) := by
  rw [div_eq_mul_inv, Real.mul_rpow hc.le (by positivity : (0:ℝ) ≤ kk⁻¹),
    Real.inv_rpow hk.le]
  rw [Real.rpow_neg hk.le, inv_inv]
  ring

/-- The chain points `t_j = x₁ 2^j` of the slot argument. -/
def SlotPt (x₁ : ℝ) (j : ℕ) : ℝ := x₁ * (2:ℝ)^j

/-- The scale `M_j` attached to the `j`-th chain point: the depth of `x₁ 2^j` inside `(a,b)`.
The interval `(x₁ 2^j/(4M_j), 4M_j x₁ 2^j)` of `M_j`-deepness misses the boundary. -/
def SlotM (N : ℕ) (x₁ b : ℝ) (j : ℕ) : ℝ :=
  min (SlotPt x₁ j / (x₁ / (2 * (N:ℝ)))) (b / SlotPt x₁ j) / 4

lemma SlotPt_pos {x₁ : ℝ} (hx₁ : 0 < x₁) (j : ℕ) : 0 < SlotPt x₁ j :=
  mul_pos hx₁ (pow_pos (by norm_num) j)

lemma SlotPt_ge {x₁ : ℝ} (hx₁ : 0 < x₁) (j : ℕ) : x₁ ≤ SlotPt x₁ j :=
  le_mul_of_one_le_right hx₁.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := j))

lemma SlotPt_mono {x₁ : ℝ} (hx₁ : 0 < x₁) : Monotone (SlotPt x₁) := fun i j hij =>
  mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hij) hx₁.le

lemma SlotPt_succ (x₁ : ℝ) (j : ℕ) : SlotPt x₁ (j+1) = 2 * SlotPt x₁ j := by
  simp only [SlotPt, pow_succ]; ring

/-- `(N/8 ≤ SlotM)` whenever the chain point lies in `(x₁, 2x₂)`: the two arguments of the `min`
defining `SlotM` are bounded below by `N/2`. -/
lemma SlotM_ge {N : ℕ} {x₁ x₂ b : ℝ} (hx₁ : 0 < x₁) (hNpos : 0 < (N:ℝ))
    (hb : 0 < b) (hNxb : (N:ℝ) * x₂ < b) {j : ℕ}
    (hge : x₁ ≤ SlotPt x₁ j) (hlt : SlotPt x₁ j < 2 * x₂) :
    (N:ℝ)/8 ≤ SlotM N x₁ b j := by
  have ht : 0 < SlotPt x₁ j := lt_of_lt_of_le hx₁ hge
  show (N:ℝ)/8 ≤ min (SlotPt x₁ j / (x₁ / (2 * (N:ℝ)))) (b / SlotPt x₁ j) / 4
  have h1 : (N:ℝ)/2 ≤ SlotPt x₁ j / (x₁ / (2 * (N:ℝ))) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < x₁ / (2 * (N:ℝ)))]
    have heq : (N:ℝ)/2 * (x₁ / (2 * (N:ℝ))) = x₁/4 := by field_simp; ring
    rw [heq]; nlinarith [hge, hx₁]
  have h2 : (N:ℝ)/2 ≤ b / SlotPt x₁ j := by
    rw [le_div_iff₀ ht]; nlinarith [hNxb, hlt, hNpos]
  have h3 : (N:ℝ)/2 ≤ min (SlotPt x₁ j / (x₁ / (2 * (N:ℝ)))) (b / SlotPt x₁ j) := le_min h1 h2
  linarith

/-- The chain point `x₁ (K-1)` is still below `x₂`, where `K = ⌈log₂ (x₂/x₁)⌉`. -/
lemma SlotPt_pre_lt {x₁ x₂ : ℝ} {K : ℕ} (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hK1 : 1 ≤ K)
    (hKlt : (K:ℝ) < Real.logb 2 (x₂ / x₁) + 1) : SlotPt x₁ (K-1) < x₂ := by
  have hx2div : 0 < x₂ / x₁ := div_pos hx₂ hx₁
  have hcast : ((K-1 : ℕ) : ℝ) = (K:ℝ) - 1 := by rw [Nat.cast_sub hK1]; norm_num
  have hltlog : ((K-1 : ℕ) : ℝ) < Real.logb 2 (x₂ / x₁) := by rw [hcast]; linarith
  have h : (2:ℝ)^((K-1:ℕ) : ℝ) < x₂ / x₁ :=
    (Real.lt_logb_iff_rpow_lt (by norm_num) hx2div).mp hltlog
  rw [Real.rpow_natCast] at h
  have h2 := mul_lt_mul_of_pos_left h hx₁
  rw [mul_div_cancel₀ _ hx₁.ne'] at h2
  simpa [SlotPt] using h2

/-- A chain point `t = x₁ 2^j` lying in the slot `(a,b)` with `Na < x₁` is `SlotM N x₁ b j`-deep
relative to `B`. -/
lemma isDeepR_SlotM {B : Set (Fin (k + 1) → ℝ)} {c : Fin k → ℝ} {a b x₁ : ℝ} {N j : ℕ}
    (hfree : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B)
    (hx₁ : 0 < x₁) (hNpos : 0 < (N:ℝ)) (hb : 0 < b)
    (hNax : (N:ℝ) * a < x₁) (ha : a < SlotPt x₁ j) (htb : SlotPt x₁ j < b) :
    IsDeepR B c (SlotM N x₁ b j) (SlotPt x₁ j) := by
  have ht : 0 < SlotPt x₁ j := SlotPt_pos hx₁ j
  have haapos : 0 < x₁ / (2 * (N:ℝ)) := by positivity
  have ha_2aa : a < 2 * (x₁ / (2 * (N:ℝ))) := by
    rcases lt_or_ge a 0 with h | h
    · nlinarith [haapos]
    · have h2 : (N:ℝ) * (x₁ / (2 * (N:ℝ))) = x₁/2 := by field_simp
      nlinarith [hNax, h2]
  have hMpos : 0 < SlotM N x₁ b j := by
    show 0 < min (SlotPt x₁ j / (x₁ / (2 * (N:ℝ)))) (b / SlotPt x₁ j) / 4
    exact div_pos (lt_min (div_pos ht haapos) (div_pos hb ht)) (by norm_num)
  refine isDeepR_of_free hMpos ht hfree ⟨ha, htb⟩ ?_ ?_
  · -- `a < t/(2M)`: `M ≤ t/(4aa)` and `a < 2aa`
    have h1 : SlotM N x₁ b j ≤ SlotPt x₁ j / (4 * (x₁ / (2 * (N:ℝ)))) := by
      show min (SlotPt x₁ j / (x₁ / (2 * (N:ℝ)))) (b / SlotPt x₁ j) / 4
          ≤ SlotPt x₁ j / (4 * (x₁ / (2 * (N:ℝ))))
      have h2 : min (SlotPt x₁ j / (x₁ / (2 * (N:ℝ)))) (b / SlotPt x₁ j) / 4
          ≤ (SlotPt x₁ j / (x₁ / (2 * (N:ℝ)))) / 4 :=
        div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      have h3 : (SlotPt x₁ j / (x₁ / (2 * (N:ℝ)))) / 4
          = SlotPt x₁ j / (4 * (x₁ / (2 * (N:ℝ)))) := by ring
      linarith
    have h4 : 2 * (x₁ / (2 * (N:ℝ))) ≤ SlotPt x₁ j / (2 * SlotM N x₁ b j) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * SlotM N x₁ b j)]
      have h5 : SlotM N x₁ b j * (4 * (x₁ / (2 * (N:ℝ)))) ≤ SlotPt x₁ j := by
        have h6 := h1
        rw [le_div_iff₀ (by positivity : (0:ℝ) < 4 * (x₁ / (2 * (N:ℝ))))] at h6
        linarith [h6]
      nlinarith [h5]
    linarith
  · -- `2 M t < b`: `M ≤ b/(4t)`
    have h2 : SlotM N x₁ b j ≤ b / (4 * SlotPt x₁ j) := by
      show min (SlotPt x₁ j / (x₁ / (2 * (N:ℝ)))) (b / SlotPt x₁ j) / 4
          ≤ b / (4 * SlotPt x₁ j)
      have h3 : min (SlotPt x₁ j / (x₁ / (2 * (N:ℝ)))) (b / SlotPt x₁ j) / 4
          ≤ (b / SlotPt x₁ j) / 4 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      have h4 : (b / SlotPt x₁ j) / 4 = b / (4 * SlotPt x₁ j) := by ring
      linarith
    have h5 : SlotM N x₁ b j * SlotPt x₁ j ≤ b/4 := by
      have h6 := mul_le_mul_of_nonneg_right h2 (le_of_lt ht)
      have h7 : (b / (4 * SlotPt x₁ j)) * SlotPt x₁ j = b/4 := by field_simp
      linarith [h6, h7]
    nlinarith [h5]

lemma SlotM_pos {N : ℕ} {x₁ b : ℝ} (hx₁ : 0 < x₁) (hNpos : 0 < (N:ℝ)) (hb : 0 < b) (j : ℕ) :
    0 < SlotM N x₁ b j := by
  show 0 < min (SlotPt x₁ j / (x₁ / (2 * (N:ℝ)))) (b / SlotPt x₁ j) / 4
  exact div_pos (lt_min (div_pos (SlotPt_pos hx₁ j) (by positivity))
    (div_pos hb (SlotPt_pos hx₁ j))) (by norm_num)

/-- The chain point `x₁ K` is below `2x₂`, where `K = ⌈log₂ (x₂/x₁)⌉`. -/
lemma SlotPt_K_lt {x₁ x₂ : ℝ} {K : ℕ} (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (hKlt : (K:ℝ) < Real.logb 2 (x₂ / x₁) + 1) : SlotPt x₁ K < 2 * x₂ := by
  have hx2div : 0 < x₂ / x₁ := div_pos hx₂ hx₁
  have hltlog : (K:ℝ) - 1 < Real.logb 2 (x₂ / x₁) := by linarith
  have h : (2:ℝ)^((K:ℝ) - 1) < x₂ / x₁ :=
    (Real.lt_logb_iff_rpow_lt (by norm_num) hx2div).mp hltlog
  have h2 : (2:ℝ)^((K:ℝ) - 1) = (2:ℝ)^K / 2 := by
    rw [Real.rpow_sub (by norm_num : (0:ℝ) < 2), Real.rpow_one, Real.rpow_natCast]
  rw [h2] at h
  have h3 : (2:ℝ)^K < 2 * (x₂ / x₁) := by nlinarith [h]
  have h4 := mul_lt_mul_of_pos_left h3 hx₁
  have heq2 : x₁ * (2 * (x₂ / x₁)) = 2 * x₂ := by field_simp
  rw [heq2] at h4
  simpa [SlotPt] using h4

end Work.WilC4
