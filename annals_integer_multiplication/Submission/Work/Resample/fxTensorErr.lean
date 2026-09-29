import Mathlib
import Submission.Work.Resample.fx
import Submission.Work.Resample.axis

/-!
# Error of an iterated fixed-point tensor computation (paper Lemma 2.11 / Corollary 2.8)

`fxTensorRec` applies a family of fixed-point slice maps `Fh i : (Fin sᵢ → ℤ×ℤ) → (Fin tᵢ → ℤ×ℤ)`
successively along the axes of a flat lexicographic array, and `tensorMapRec` does the same for
the corresponding family of true maps `A i`.  Here we prove that if every `A i` is additive and
contractive in the sup norm, and every `Fh i` keeps `C̃◦` invariant and approximates `A i` with
error `εᵢ` (in the fixed-point norm `2^p‖·‖`), then the whole iteration approximates the tensor of
the `A i` with error `δ` (error of the input) plus `Σᵢ εᵢ`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ## Elementary fixed-point facts -/

lemma fxTE_zget_of_lt {n : ℕ} (u : Fin n → ℤ × ℤ) {i : ℕ} (h : i < n) :
    zget u i = u ⟨i, h⟩ := by
  simp [zget, h]

lemma fxTE_vget_of_lt {n : ℕ} (u : Fin n → ℂ) {i : ℕ} (h : i < n) :
    vget u i = u ⟨i, h⟩ := by
  simp [vget, h]

lemma fxTE_vget_sub {n : ℕ} (u v : Fin n → ℂ) (i : ℕ) :
    vget (u - v) i = vget u i - vget v i := by
  by_cases h : i < n <;> simp [vget, h, Pi.sub_apply]

@[simp] lemma fxTE_fxC_zero (p : ℕ) : fxC p (0, 0) = 0 := by
  simp [fxC]

@[simp] lemma fxTE_inDisc_zero (p : ℕ) : inDisc p (0, 0) := by
  rw [inDisc]
  have h : ((0 : ℤ)) ^ 2 + ((0 : ℤ)) ^ 2 = 0 := by norm_num
  rw [h]
  exact pow_nonneg (by norm_num : (0 : ℤ) ≤ 4) p

lemma fxTE_fxC_zget {n : ℕ} (p : ℕ) (u : Fin n → ℤ × ℤ) (i : ℕ) :
    fxC p (zget u i) = vget (fun j => fxC p (u j)) i := by
  by_cases h : i < n
  · rw [fxTE_zget_of_lt u h, fxTE_vget_of_lt _ h]
  · simp only [zget, vget, dite_eq_right h, fxTE_fxC_zero]

/-- Sup-norm bound: it suffices to bound every value (also valid for the empty index type). -/
lemma fxTE_norm_pi_le {n : ℕ} {x : Fin n → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ j, ‖x j‖ ≤ c) : ‖x‖ ≤ c := by
  have key : (Finset.univ.sup fun j : Fin n => ‖x j‖₊) ≤ (⟨c, hc⟩ : NNReal) :=
    Finset.sup_le fun j _ => by exact_mod_cast h j
  calc ‖x‖ = ((Finset.univ.sup fun j : Fin n => ‖x j‖₊ : NNReal) : ℝ) := Pi.norm_def x
    _ ≤ ((⟨c, hc⟩ : NNReal) : ℝ) := NNReal.coe_le_coe.mpr key
    _ = c := rfl

/-! ## Sums over `List.range` -/

lemma fxTE_norm_apply_le {n : ℕ} (x : Fin n → ℂ) (j : Fin n) : ‖x j‖ ≤ ‖x‖ :=
  norm_le_pi_norm x j

lemma fxTE_list_sum_range_map (f : ℕ → ℝ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  rw [← List.sum_toFinset f List.nodup_range, List.toFinset_range]

lemma fxTE_sum_range_succ (f : ℕ → ℝ) (n : ℕ) :
    ((List.range (n + 1)).map f).sum = f 0 + ((List.range n).map (fun i => f (i + 1))).sum := by
  rw [fxTE_list_sum_range_map f (n + 1), fxTE_list_sum_range_map (fun i => f (i + 1)) n,
    Finset.sum_range_succ']
  ring

/-! ## Turning additivity into subtraction -/

noncomputable def fxTE_addHom {n m : ℕ} (A : (Fin n → ℂ) → (Fin m → ℂ))
    (hAdd : ∀ x y : Fin n → ℂ, A (x + y) = A x + A y) : (Fin n → ℂ) →+ (Fin m → ℂ) where
  toFun := A
  map_zero' := by
    have h : A 0 + 0 = A 0 + A 0 := by rw [add_zero]; simpa using hAdd 0 0
    exact (add_left_cancel h).symm
  map_add' := hAdd

lemma fxTE_sub_of_add {n m : ℕ} (A : (Fin n → ℂ) → (Fin m → ℂ))
    (hAdd : ∀ x y : Fin n → ℂ, A (x + y) = A x + A y) (x y : Fin n → ℂ) :
    A (x - y) = A x - A y :=
  (fxTE_addHom A hAdd).map_sub x y

/-! ## Unfolding the fixed-point / complex axis recursion -/

lemma fxTE_axisFx1Gen_apply {s t B : ℕ} (hB : 0 < B)
    (Φ : (Fin s → ℤ × ℤ) → (Fin t → ℤ × ℤ)) (u : Fin (s * B) → ℤ × ℤ)
    (idx : Fin (t * B)) :
    axisFx1Gen s t B Φ u idx =
      Φ (fun j : Fin s => zget u ((j : ℕ) * B + (idx : ℕ) % B))
        ⟨(idx : ℕ) / B, (Nat.div_lt_iff_lt_mul hB).mpr idx.isLt⟩ := by
  simp only [axisFx1Gen]
  rw [dite_eq_left ((Nat.div_lt_iff_lt_mul hB).mpr idx.isLt)]

lemma fxTE_axisApply1Gen_apply {s t B : ℕ} (Φ : (Fin s → ℂ) → (Fin t → ℂ))
    (u : Fin (s * B) → ℂ) (idx : Fin (t * B)) (h : (idx : ℕ) / B < t) :
    axisApply1Gen s t B Φ u idx =
      Φ (fun j : Fin s => vget u ((j : ℕ) * B + (idx : ℕ) % B)) ⟨(idx : ℕ) / B, h⟩ := by
  simp only [axisApply1Gen]
  rw [fxTE_vget_of_lt _ h]

lemma fxTE_fxBlockwise_apply {t N N' : ℕ} (hN' : 0 < N')
    (Φ : (Fin N → ℤ × ℤ) → (Fin N' → ℤ × ℤ)) (u : Fin (t * N) → ℤ × ℤ)
    (idx : Fin (t * N')) :
    fxBlockwise t N N' Φ u idx =
      Φ (fun K' : Fin N => zget u ((idx : ℕ) / N' * N + (K' : ℕ)))
        ⟨(idx : ℕ) % N', Nat.mod_lt _ hN'⟩ := by
  simp only [fxBlockwise]
  rw [dite_eq_left (Nat.mod_lt _ hN')]

lemma fxTE_blockwise_apply {t N N' : ℕ} (hN' : 0 < N')
    (Ψ : (Fin N → ℂ) → (Fin N' → ℂ)) (v : Fin (t * N) → ℂ) (idx : Fin (t * N')) :
    blockwise t N N' Ψ v idx =
      Ψ (fun K' : Fin N => vget v ((idx : ℕ) / N' * N + (K' : ℕ)))
        ⟨(idx : ℕ) % N', Nat.mod_lt _ hN'⟩ := by
  simp only [blockwise]
  rw [fxTE_vget_of_lt _ (Nat.mod_lt _ hN')]

/-! ## Index arithmetic -/

lemma fxTE_idx_in_range {t N N' : ℕ} (_hN : 0 < N) (hN' : 0 < N') (idx : Fin (t * N'))
    (K' : Fin N) : (idx : ℕ) / N' * N + (K' : ℕ) < t * N := by
  have h1 : (idx : ℕ) / N' < t := (Nat.div_lt_iff_lt_mul hN').mpr idx.isLt
  have h2 : ((idx : ℕ) / N' + 1) * N ≤ t * N :=
    Nat.mul_le_mul_right N (Nat.succ_le_of_lt h1)
  have h3 : (idx : ℕ) / N' * N + (K' : ℕ) < ((idx : ℕ) / N' + 1) * N := by
    rw [Nat.add_mul]; omega
  omega

lemma fxTE_idx_in_range_axis {s B : ℕ} (_hB : 0 < B) (j : Fin s) (K : Fin B) :
    (j : ℕ) * B + (K : ℕ) < s * B := by
  have h1 : ((j : ℕ) + 1) * B ≤ s * B := Nat.mul_le_mul_right B (Nat.succ_le_of_lt j.isLt)
  have h2 : (j : ℕ) * B + (K : ℕ) < ((j : ℕ) + 1) * B := by rw [Nat.add_mul]; omega
  omega

lemma fxTE_pos_right {t B : ℕ} (h : 0 < t * B) : 0 < B := by
  rcases Nat.eq_zero_or_pos B with hz | hp
  · rw [hz, Nat.mul_zero] at h
    exact absurd h (Nat.lt_irrefl 0)
  · exact hp

lemma fxTE_pos_left {t B : ℕ} (h : 0 < t * B) : 0 < t := by
  rcases Nat.eq_zero_or_pos t with hz | hp
  · rw [hz, Nat.zero_mul] at h
    exact absurd h (Nat.lt_irrefl 0)
  · exact hp

/-! ## Additivity of the axis application -/

lemma fxTE_axisApply1Gen_sub {s t B : ℕ} (Φ : (Fin s → ℂ) → (Fin t → ℂ))
    (hΦ : ∀ x y : Fin s → ℂ, Φ (x + y) = Φ x + Φ y) (u v : Fin (s * B) → ℂ) :
    axisApply1Gen s t B Φ (u - v) = axisApply1Gen s t B Φ u - axisApply1Gen s t B Φ v := by
  funext idx
  have h1 : (fun j : Fin s => vget (u - v) ((j : ℕ) * B + (idx : ℕ) % B))
      = (fun j : Fin s => vget u ((j : ℕ) * B + (idx : ℕ) % B))
        - (fun j : Fin s => vget v ((j : ℕ) * B + (idx : ℕ) % B)) := by
    funext j
    rw [Pi.sub_apply, fxTE_vget_sub]
  show vget (Φ (fun j : Fin s => vget (u - v) ((j : ℕ) * B + (idx : ℕ) % B))) ((idx : ℕ) / B)
    = vget (Φ (fun j : Fin s => vget u ((j : ℕ) * B + (idx : ℕ) % B))) ((idx : ℕ) / B)
      - vget (Φ (fun j : Fin s => vget v ((j : ℕ) * B + (idx : ℕ) % B))) ((idx : ℕ) / B)
  rw [h1, fxTE_sub_of_add Φ hΦ]
  exact fxTE_vget_sub _ _ _

/-! ## One axis step -/

theorem fxTE_axis {s t B p : ℕ} (A0 : (Fin s → ℂ) → (Fin t → ℂ))
    (F0 : (Fin s → ℤ × ℤ) → (Fin t → ℤ × ℤ)) (ε0 δ : ℝ) (hδ : 0 ≤ δ)
    (hAdd : ∀ x y : Fin s → ℂ, A0 (x + y) = A0 x + A0 y)
    (hNorm : ∀ z : Fin s → ℂ, ‖A0 z‖ ≤ ‖z‖)
    (hDisc : ∀ w : Fin s → ℤ × ℤ, (∀ j, inDisc p (w j)) → ∀ k : Fin t, inDisc p (F0 w k))
    (hErr : ∀ w : Fin s → ℤ × ℤ, (∀ j, inDisc p (w j)) → ∀ k : Fin t,
      ‖fxC p (F0 w k) - A0 (fun j => fxC p (w j)) k‖ * (2 : ℝ) ^ p ≤ ε0)
    (u : Fin (s * B) → ℤ × ℤ) (v : Fin (s * B) → ℂ)
    (hu : ∀ j, inDisc p (u j))
    (hv : ∀ j, ‖fxC p (u j) - v j‖ * (2 : ℝ) ^ p ≤ δ) :
    (∀ idx : Fin (t * B), inDisc p (axisFx1Gen s t B F0 u idx)) ∧
    (∀ idx : Fin (t * B),
      ‖fxC p (axisFx1Gen s t B F0 u idx) - axisApply1Gen s t B A0 v idx‖ * (2 : ℝ) ^ p
        ≤ δ + ε0) := by
  have h2p : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have hB_of : ∀ idx : Fin (t * B), 0 < B := fun idx => fxTE_pos_right (Fin.pos idx)
  have hdiv_of : ∀ idx : Fin (t * B), (idx : ℕ) / B < t :=
    fun idx => (Nat.div_lt_iff_lt_mul (hB_of idx)).mpr idx.isLt
  constructor
  · intro idx
    rw [fxTE_axisFx1Gen_apply (hB_of idx)]
    exact hDisc _ (fun j => by
      have hlt := fxTE_idx_in_range_axis (hB_of idx) j ⟨(idx : ℕ) % B, Nat.mod_lt _ (hB_of idx)⟩
      rw [fxTE_zget_of_lt _ hlt]
      exact hu ⟨_, hlt⟩) _
  · intro idx
    have hB := hB_of idx
    have hd := hdiv_of idx
    have ha : ‖fxC p (axisFx1Gen s t B F0 u idx)
        - axisApply1Gen s t B A0 (fun m : Fin (s * B) => fxC p (u m)) idx‖ * (2 : ℝ) ^ p ≤ ε0 := by
      rw [fxTE_axisFx1Gen_apply hB,
        fxTE_axisApply1Gen_apply A0 (fun m : Fin (s * B) => fxC p (u m)) idx hd]
      have hfun : (fun j : Fin s => fxC p (zget u ((j : ℕ) * B + (idx : ℕ) % B)))
          = (fun j : Fin s => vget (fun m : Fin (s * B) => fxC p (u m))
              ((j : ℕ) * B + (idx : ℕ) % B)) := by
        funext j
        exact fxTE_fxC_zget p u _
      have hdisc : ∀ j : Fin s,
          inDisc p ((fun j : Fin s => zget u ((j : ℕ) * B + (idx : ℕ) % B)) j) := by
        intro j
        have hlt := fxTE_idx_in_range_axis hB j ⟨(idx : ℕ) % B, Nat.mod_lt _ hB⟩
        show inDisc p (zget u ((j : ℕ) * B + (idx : ℕ) % B))
        rw [fxTE_zget_of_lt _ hlt]
        exact hu ⟨_, hlt⟩
      have he := hErr (fun j : Fin s => zget u ((j : ℕ) * B + (idx : ℕ) % B)) hdisc
        ⟨(idx : ℕ) / B, hd⟩
      rw [← hfun]
      exact he
    have hsubpt : axisApply1Gen s t B A0 ((fun m : Fin (s * B) => fxC p (u m)) - v) idx
        = axisApply1Gen s t B A0 (fun m : Fin (s * B) => fxC p (u m)) idx
          - axisApply1Gen s t B A0 v idx :=
      congrFun (fxTE_axisApply1Gen_sub A0 hAdd (fun m : Fin (s * B) => fxC p (u m)) v) idx
    have hb : ‖axisApply1Gen s t B A0 (fun m : Fin (s * B) => fxC p (u m)) idx
        - axisApply1Gen s t B A0 v idx‖ * (2 : ℝ) ^ p ≤ δ := by
      rw [← hsubpt,
        fxTE_axisApply1Gen_apply A0 ((fun m : Fin (s * B) => fxC p (u m)) - v) idx hd]
      have hpw : ∀ j : Fin s,
          ‖vget ((fun m : Fin (s * B) => fxC p (u m)) - v) ((j : ℕ) * B + (idx : ℕ) % B)‖
            ≤ δ / (2 : ℝ) ^ p := by
        intro j
        have hlt := fxTE_idx_in_range_axis hB j ⟨(idx : ℕ) % B, Nat.mod_lt _ hB⟩
        have hvv : vget ((fun m : Fin (s * B) => fxC p (u m)) - v)
            ((j : ℕ) * B + (idx : ℕ) % B) = fxC p (u ⟨_, hlt⟩) - v ⟨_, hlt⟩ := by
          rw [fxTE_vget_of_lt _ hlt, Pi.sub_apply]
        rw [hvv, le_div_iff₀ h2p]
        exact hv ⟨_, hlt⟩
      calc ‖(A0 (fun j : Fin s => vget ((fun m : Fin (s * B) => fxC p (u m)) - v)
              ((j : ℕ) * B + (idx : ℕ) % B))) ⟨(idx : ℕ) / B, hd⟩‖ * (2 : ℝ) ^ p
          ≤ ‖A0 (fun j : Fin s => vget ((fun m : Fin (s * B) => fxC p (u m)) - v)
              ((j : ℕ) * B + (idx : ℕ) % B))‖ * (2 : ℝ) ^ p :=
            mul_le_mul_of_nonneg_right
              (fxTE_norm_apply_le _ ⟨(idx : ℕ) / B, hd⟩) (by positivity)
        _ ≤ ‖(fun j : Fin s => vget ((fun m : Fin (s * B) => fxC p (u m)) - v)
              ((j : ℕ) * B + (idx : ℕ) % B))‖ * (2 : ℝ) ^ p :=
            mul_le_mul_of_nonneg_right (hNorm _) (by positivity)
        _ ≤ (δ / (2 : ℝ) ^ p) * (2 : ℝ) ^ p :=
            mul_le_mul_of_nonneg_right
              (fxTE_norm_pi_le (div_nonneg hδ (le_of_lt h2p)) hpw) (by positivity)
        _ = δ := div_mul_cancel₀ δ (ne_of_gt h2p)
    have htri : ‖fxC p (axisFx1Gen s t B F0 u idx) - axisApply1Gen s t B A0 v idx‖
        ≤ ‖fxC p (axisFx1Gen s t B F0 u idx)
            - axisApply1Gen s t B A0 (fun m : Fin (s * B) => fxC p (u m)) idx‖
          + ‖axisApply1Gen s t B A0 (fun m : Fin (s * B) => fxC p (u m)) idx
            - axisApply1Gen s t B A0 v idx‖ := by
      have h := dist_triangle (fxC p (axisFx1Gen s t B F0 u idx))
        (axisApply1Gen s t B A0 (fun m : Fin (s * B) => fxC p (u m)) idx)
        (axisApply1Gen s t B A0 v idx)
      simpa only [dist_eq_norm] using h
    calc ‖fxC p (axisFx1Gen s t B F0 u idx) - axisApply1Gen s t B A0 v idx‖ * (2 : ℝ) ^ p
        ≤ (‖fxC p (axisFx1Gen s t B F0 u idx)
              - axisApply1Gen s t B A0 (fun m : Fin (s * B) => fxC p (u m)) idx‖
            + ‖axisApply1Gen s t B A0 (fun m : Fin (s * B) => fxC p (u m)) idx
              - axisApply1Gen s t B A0 v idx‖) * (2 : ℝ) ^ p :=
          mul_le_mul_of_nonneg_right htri (by positivity)
      _ = ‖fxC p (axisFx1Gen s t B F0 u idx)
              - axisApply1Gen s t B A0 (fun m : Fin (s * B) => fxC p (u m)) idx‖ * (2 : ℝ) ^ p
            + ‖axisApply1Gen s t B A0 (fun m : Fin (s * B) => fxC p (u m)) idx
              - axisApply1Gen s t B A0 v idx‖ * (2 : ℝ) ^ p := by ring
      _ ≤ ε0 + δ := add_le_add ha hb
      _ = δ + ε0 := by ring

/-! ## The blockwise step -/

theorem fxTE_block (t N N' p : ℕ) (Φ : (Fin N → ℤ × ℤ) → (Fin N' → ℤ × ℤ))
    (Ψ : (Fin N → ℂ) → (Fin N' → ℂ)) (b δ' : ℝ)
    (h : ∀ (w : Fin N → ℤ × ℤ) (w' : Fin N → ℂ),
      (∀ j, inDisc p (w j)) → (∀ j, ‖fxC p (w j) - w' j‖ * (2 : ℝ) ^ p ≤ δ') →
      ∀ k : Fin N', ‖fxC p (Φ w k) - Ψ w' k‖ * (2 : ℝ) ^ p ≤ b)
    (u : Fin (t * N) → ℤ × ℤ) (v : Fin (t * N) → ℂ)
    (hu : ∀ j, inDisc p (u j))
    (hv : ∀ j, ‖fxC p (u j) - v j‖ * (2 : ℝ) ^ p ≤ δ') :
    ∀ idx : Fin (t * N'),
      ‖fxC p (fxBlockwise t N N' Φ u idx) - blockwise t N N' Ψ v idx‖ * (2 : ℝ) ^ p ≤ b := by
  intro idx
  rcases Nat.eq_zero_or_pos N' with hN' | hN'pos
  · have hpos := Fin.pos idx
    rw [hN'] at hpos
    simp at hpos
  rw [fxTE_fxBlockwise_apply hN'pos, fxTE_blockwise_apply hN'pos]
  refine h (fun K' : Fin N => zget u ((idx : ℕ) / N' * N + (K' : ℕ)))
    (fun K' : Fin N => vget v ((idx : ℕ) / N' * N + (K' : ℕ))) ?_ ?_
    ⟨(idx : ℕ) % N', Nat.mod_lt _ hN'pos⟩
  · intro j
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; exact Fin.elim0 j
    · have hlt := fxTE_idx_in_range hN hN'pos idx j
      rw [fxTE_zget_of_lt _ hlt]
      exact hu ⟨_, hlt⟩
  · intro j
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; exact Fin.elim0 j
    · have hlt := fxTE_idx_in_range hN hN'pos idx j
      rw [fxTE_zget_of_lt _ hlt, fxTE_vget_of_lt _ hlt]
      exact hv ⟨_, hlt⟩

/-! ## The iterated estimate -/

theorem fxTE_aux (ss : List ℕ) : ∀ (ts : List ℕ), ts.length = ss.length → ∀ (p : ℕ)
    (A : (i : ℕ) → (Fin (ss.getD i 0) → ℂ) → (Fin (ts.getD i 0) → ℂ))
    (Fh : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ))
    (ε : ℕ → ℝ) (δ : ℝ), 0 ≤ δ →
    (∀ i < ss.length, ∀ x y : Fin (ss.getD i 0) → ℂ, A i (x + y) = A i x + A i y) →
    (∀ i < ss.length, ∀ z : Fin (ss.getD i 0) → ℂ, ‖A i z‖ ≤ ‖z‖) →
    (∀ i < ss.length, ∀ w : Fin (ss.getD i 0) → ℤ × ℤ,
      (∀ j, inDisc p (w j)) → ∀ k : Fin (ts.getD i 0), inDisc p (Fh i w k)) →
    (∀ i < ss.length, ∀ w : Fin (ss.getD i 0) → ℤ × ℤ,
      (∀ j, inDisc p (w j)) → ∀ k : Fin (ts.getD i 0),
      ‖fxC p (Fh i w k) - A i (fun j => fxC p (w j)) k‖ * (2 : ℝ) ^ p ≤ ε i) →
    ∀ (u : Fin ss.prod → ℤ × ℤ), (∀ j, inDisc p (u j)) → ∀ (v : Fin ss.prod → ℂ),
      (∀ j, ‖fxC p (u j) - v j‖ * (2 : ℝ) ^ p ≤ δ) → ∀ J : Fin ts.prod,
      ‖fxC p (fxTensorRec ss ts Fh u J) - tensorMapRec ss ts A v J‖ * (2 : ℝ) ^ p
        ≤ δ + ((List.range ss.length).map ε).sum := by
  induction ss with
  | nil =>
    intro ts hl p A Fh ε δ hδ hAdd hNorm hDisc hErr u hu v hv J
    have hts : ts = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    subst hts
    have h1 : fxTensorRec [] [] Fh u J = u J := rfl
    have h2 : tensorMapRec [] [] A v J = v J := rfl
    simpa only [h1, h2, List.length_nil, List.range_zero, List.map_nil, List.sum_nil,
      add_zero] using hv J
  | cons s ss' ih =>
    intro ts hl p A Fh ε δ hδ hAdd hNorm hDisc hErr u hu v hv J
    cases ts with
    | nil =>
      simp only [List.length_nil, List.length_cons] at hl
      omega
    | cons t ts' =>
      have hTS : ts'.length = ss'.length := by
        simp only [List.length_cons] at hl
        omega
      have hpos : 0 < t * ts'.prod := by simpa only [List.prod_cons] using Fin.pos J
      have ht : 0 < t := fxTE_pos_left hpos
      have h0len : 0 < (s :: ss').length := by simp only [List.length_cons]; exact Nat.zero_lt_succ _
      -- `ε 0 ≥ 0`, forced by the error hypothesis at the zero fixed-point vector
      have hε0 : 0 ≤ ε 0 := by
        have he := hErr 0 h0len (fun _ : Fin s => (0, 0)) (fun _ => fxTE_inDisc_zero p) ⟨0, ht⟩
        have hnn : (0 : ℝ) ≤ ‖fxC p (Fh 0 (fun _ : Fin s => (0, 0)) ⟨0, ht⟩)
            - A 0 (fun j : Fin s => fxC p ((fun _ : Fin s => (0, 0)) j)) ⟨0, ht⟩‖ * (2 : ℝ) ^ p :=
          mul_nonneg (norm_nonneg _) (by positivity)
        exact le_trans hnn he
      -- hypotheses for the tail
      have hAdd' : ∀ i < ss'.length, ∀ x y : Fin (ss'.getD i 0) → ℂ,
          A (i + 1) (x + y) = A (i + 1) x + A (i + 1) y :=
        fun i hi x y => hAdd (i + 1) (by simp only [List.length_cons]; omega) x y
      have hNorm' : ∀ i < ss'.length, ∀ z : Fin (ss'.getD i 0) → ℂ, ‖A (i + 1) z‖ ≤ ‖z‖ :=
        fun i hi z => hNorm (i + 1) (by simp only [List.length_cons]; omega) z
      have hDisc' : ∀ i < ss'.length, ∀ w : Fin (ss'.getD i 0) → ℤ × ℤ,
          (∀ j, inDisc p (w j)) → ∀ k : Fin (ts'.getD i 0), inDisc p (Fh (i + 1) w k) :=
        fun i hi w hw k => hDisc (i + 1) (by simp only [List.length_cons]; omega) w hw k
      have hErr' : ∀ i < ss'.length, ∀ w : Fin (ss'.getD i 0) → ℤ × ℤ,
          (∀ j, inDisc p (w j)) → ∀ k : Fin (ts'.getD i 0),
          ‖fxC p (Fh (i + 1) w k) - A (i + 1) (fun j => fxC p (w j)) k‖ * (2 : ℝ) ^ p
            ≤ ε (i + 1) :=
        fun i hi w hw k => hErr (i + 1) (by simp only [List.length_cons]; omega) w hw k
      have hδ' : 0 ≤ δ + ε 0 := add_nonneg hδ hε0
      have hIH := ih ts' hTS p (fun i => A (i + 1)) (fun i => Fh (i + 1)) (fun i => ε (i + 1))
        (δ + ε 0) hδ' hAdd' hNorm' hDisc' hErr'
      have haxis := fxTE_axis (s := s) (t := t) (B := ss'.prod) (p := p) (A0 := A 0) (F0 := Fh 0)
        (ε0 := ε 0) (δ := δ) hδ
        (fun x y => hAdd 0 h0len x y) (fun z => hNorm 0 h0len z)
        (fun w hw k => hDisc 0 h0len w hw k) (fun w hw k => hErr 0 h0len w hw k) u v hu hv
      have hblock := fxTE_block t ss'.prod ts'.prod p
        (fxTensorRec ss' ts' (fun i => Fh (i + 1))) (tensorMapRec ss' ts' (fun i => A (i + 1)))
        ((δ + ε 0) + ((List.range ss'.length).map (fun i => ε (i + 1))).sum) (δ + ε 0)
        (fun w w' hw hw' k => hIH w hw w' hw' k)
        (axisFx1Gen s t ss'.prod (Fh 0) u) (axisApply1Gen s t ss'.prod (A 0) v) haxis.1 haxis.2
      have hsum : ((List.range (s :: ss').length).map ε).sum
          = ε 0 + ((List.range ss'.length).map (fun i => ε (i + 1))).sum := by
        simp only [List.length_cons]
        exact fxTE_sum_range_succ ε ss'.length
      rw [hsum, ← add_assoc]
      exact hblock J

theorem fxTensorErr (ss ts : List ℕ) (hl : ts.length = ss.length) (p : ℕ)
    (A : (i : ℕ) → (Fin (ss.getD i 0) → ℂ) → (Fin (ts.getD i 0) → ℂ))
    (Fh : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ))
    (ε : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hAdd : ∀ i < ss.length, ∀ x y : Fin (ss.getD i 0) → ℂ, A i (x + y) = A i x + A i y)
    (hNorm : ∀ i < ss.length, ∀ z : Fin (ss.getD i 0) → ℂ, ‖A i z‖ ≤ ‖z‖)
    (hDisc : ∀ i < ss.length, ∀ w : Fin (ss.getD i 0) → ℤ × ℤ,
      (∀ j, HvdH.inDisc p (w j)) → ∀ k : Fin (ts.getD i 0), HvdH.inDisc p (Fh i w k))
    (hErr : ∀ i < ss.length, ∀ w : Fin (ss.getD i 0) → ℤ × ℤ,
      (∀ j, HvdH.inDisc p (w j)) → ∀ k : Fin (ts.getD i 0),
      ‖HvdH.fxC p (Fh i w k) - A i (fun j => HvdH.fxC p (w j)) k‖ * (2 : ℝ) ^ p ≤ ε i)
    (u : Fin ss.prod → ℤ × ℤ) (hu : ∀ j, HvdH.inDisc p (u j))
    (v : Fin ss.prod → ℂ) (hv : ∀ j, ‖HvdH.fxC p (u j) - v j‖ * (2 : ℝ) ^ p ≤ δ)
    (J : Fin ts.prod) :
    ‖HvdH.fxC p (Work.Resample.fxTensorRec ss ts Fh u J) -
      (Work.Resample.tensorMapRec ss ts A v) J‖ * (2 : ℝ) ^ p ≤ δ + ((List.range ss.length).map ε).sum :=
  fxTE_aux ss ts hl p A Fh ε δ hδ hAdd hNorm hDisc hErr u hu v hv J

end Work.Resample
