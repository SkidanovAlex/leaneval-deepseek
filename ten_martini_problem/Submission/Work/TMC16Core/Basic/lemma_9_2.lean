import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Basic

open Work.TMC16Core

lemma l92_sum_shift_up {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) (p : ℕ) :
    (∑ t : Fin n, (if ((p : ℤ) + 1 = ((t : ℕ) : ℤ)) then B t j else 0))
      = (if h : p + 1 < n then B ⟨p + 1, h⟩ j else 0) := by
  by_cases h : p + 1 < n
  · rw [dif_pos h]
    have hh : ∀ t : Fin n, (if ((p : ℤ) + 1 = ((t : ℕ) : ℤ)) then B t j else 0)
        = if t = (⟨p + 1, h⟩ : Fin n) then B t j else 0 := by
      intro t
      by_cases ht : t = ⟨p + 1, h⟩
      · subst ht; simp
      · rw [if_neg, if_neg ht]
        intro hc
        have hc' : (((t : ℕ)) : ℤ) = (((p + 1 : ℕ)) : ℤ) := by push_cast; omega
        exact ht (Fin.ext (by exact_mod_cast hc'))
    simp_rw [hh]
    rw [Finset.sum_ite_eq']
    simp
  · rw [dif_neg h]
    refine Finset.sum_eq_zero ?_
    intro t _
    rw [if_neg]
    intro hc
    have : (t:ℕ) = p + 1 := by
      have hc' : ((t:ℕ):ℤ) = (((p+1:ℕ)):ℤ) := by push_cast; omega
      exact_mod_cast hc'
    omega

lemma l92_sum_shift_down {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) {p : ℕ} (hp : p < n) :
    (∑ t : Fin n, (if ((t : ℕ) : ℤ) + 1 = ((p : ℤ)) then B t j else 0))
      = (if h : 0 < p then B ⟨p - 1, by omega⟩ j else 0) := by
  by_cases h : 0 < p
  · rw [dif_pos h]
    have hh : ∀ t : Fin n, (if ((t : ℕ) : ℤ) + 1 = ((p : ℤ)) then B t j else 0)
        = if t = (⟨p - 1, by omega⟩ : Fin n) then B t j else 0 := by
      intro t
      by_cases ht : t = ⟨p - 1, by omega⟩
      · subst ht
        have hcond : (((p - 1 : ℕ)) : ℤ) + 1 = ((p : ℕ) : ℤ) := by omega
        rw [Fin.val_mk, if_pos hcond, if_pos (Fin.ext rfl)]
      · rw [if_neg, if_neg ht]
        intro hc
        have hc' : (((t : ℕ)) : ℤ) = (((p - 1 : ℕ)) : ℤ) := by push_cast; omega
        exact ht (Fin.ext (by exact_mod_cast hc'))
    simp_rw [hh]
    rw [Finset.sum_ite_eq']
    simp
  · rw [dif_neg h]
    refine Finset.sum_eq_zero ?_
    intro t _
    rw [if_neg]
    intro hc
    omega

theorem l92_dirMat_mul_apply (α lam : ℝ) (θ : ℝ) (E : ℂ) (n : ℕ)
    (B : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (dirMat α lam θ E n * B) i j =
      (((amoPot α lam θ ((i:ℕ):ℤ) : ℝ) : ℂ) - E) * B i j
      + (if h : (i:ℕ) + 1 < n then B ⟨(i:ℕ)+1, h⟩ j else 0)
      + (if h : 0 < (i:ℕ) then B ⟨(i:ℕ)-1, by omega⟩ j else 0) := by
  rw [Matrix.mul_apply]
  have hsplit : ∀ t : Fin n, (dirMat α lam θ E n) i t * B t j =
      (if i = t then (((amoPot α lam θ ((i:ℕ):ℤ) : ℝ) : ℂ) - E) * B t j else 0)
      + (if ((i:ℕ):ℤ)+1 = ((t:ℕ):ℤ) then B t j else 0)
      + (if ((t:ℕ):ℤ)+1 = ((i:ℕ):ℤ) then B t j else 0) := by
    intro t
    simp only [dirMat, ite_mul, zero_mul, add_mul, one_mul]
  have h1 : (∑ t : Fin n, (if i = t then (((amoPot α lam θ ((i:ℕ):ℤ) : ℝ) : ℂ) - E) * B t j else 0))
      = (((amoPot α lam θ ((i:ℕ):ℤ) : ℝ) : ℂ) - E) * B i j := by
    rw [Finset.sum_ite_eq (M := ℂ)]
    simp
  have h2 := l92_sum_shift_up (n := n) B j (i:ℕ)
  have h3 := l92_sum_shift_down (n := n) B j (p := (i:ℕ)) i.isLt
  rw [Finset.sum_congr rfl (fun t _ => hsplit t)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h2, h3]

end Work.TMC16Core.Basic

namespace Work.TMC16Core.Basic

open Work.TMC16Core

theorem l92_pd_rec (α lam : ℝ) (φ : ℝ) (E : ℂ) (L : ℕ) :
    pd α lam φ E (L + 2) =
      (E - ((amoPot α lam φ (L : ℤ) : ℝ) : ℂ)) * pd α lam φ E (L + 1) - pd α lam φ E L := by
  simp [pd]

theorem l92_pd_shift (α lam : ℝ) (θ : ℝ) (E : ℂ) (n m : ℕ) :
    pd α lam θ E (n + m + 1) =
      pd α lam (θ + (n : ℝ) * α) E (m + 1) * pd α lam θ E (n + 1) -
      pd α lam (θ + ((n : ℝ) + 1) * α) E m * pd α lam θ E n := by
  have hsh : ∀ k : ℕ, amoPot α lam θ ((n + k : ℕ) : ℤ) = amoPot α lam (θ + (n : ℝ) * α) (k : ℤ) := by
    intro k; simp only [amoPot]; push_cast; ring_nf
  have hsh2 : ∀ k : ℕ, amoPot α lam θ ((n + 1 + k : ℕ) : ℤ) = amoPot α lam (θ + ((n : ℝ) + 1) * α) (k : ℤ) := by
    intro k; simp only [amoPot]; push_cast; ring_nf
  have hsh0 : amoPot α lam θ ((n : ℕ) : ℤ) = amoPot α lam (θ + (n : ℝ) * α) (0 : ℤ) := by
    simp only [amoPot]; push_cast; ring_nf
  induction m using Nat.twoStepInduction with
  | zero => simp [pd]
  | one =>
    rw [l92_pd_rec α lam θ E n]
    rw [show (1:ℕ) + 1 = 0 + 2 by omega, l92_pd_rec α lam (θ + (n:ℝ)*α) E 0, hsh0]
    simp [pd]
  | more m ih1 ih2 =>
    rw [show n + (m + 2) + 1 = (n + m + 1) + 2 by omega, l92_pd_rec α lam θ E (n + m + 1)]
    rw [show (n + m + 1) + 1 = n + (m + 1) + 1 by omega]
    rw [ih2, ih1]
    rw [show n + m + 1 = n + (m + 1) by omega]
    rw [hsh (m + 1)]
    rw [l92_pd_rec α lam (θ + (n:ℝ)*α) E (m + 1)]
    rw [l92_pd_rec α lam (θ + ((n:ℝ)+1)*α) E m]
    rw [← hsh2 m]
    rw [show n + 1 + m = n + (m + 1) by omega]
    rw [hsh (m + 1)]
    ring

noncomputable def l92_adjF (α lam : ℝ) (θ : ℝ) (E : ℂ) (n : ℕ) (p q : ℕ) : ℂ :=
  (-1 : ℂ) ^ (n - 1) * pd α lam θ E (min p q + 1) *
    pd α lam (θ + (((max p q) + 1 : ℕ) : ℝ) * α) E (n - max p q)

noncomputable def l92_adjM (α lam : ℝ) (θ : ℝ) (E : ℂ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => l92_adjF α lam θ E n i.val j.val

lemma l92_adjF_le {α lam : ℝ} {θ : ℝ} {E : ℂ} {n p q : ℕ} (h : p ≤ q) :
    l92_adjF α lam θ E n p q = (-1 : ℂ) ^ (n - 1) * pd α lam θ E (p + 1) *
      pd α lam (θ + (((q + 1 : ℕ)) : ℝ) * α) E (n - q) := by
  simp only [l92_adjF, min_eq_left h, max_eq_right h]

lemma l92_adjF_ge {α lam : ℝ} {θ : ℝ} {E : ℂ} {n p q : ℕ} (h : q ≤ p) :
    l92_adjF α lam θ E n p q = (-1 : ℂ) ^ (n - 1) * pd α lam θ E (q + 1) *
      pd α lam (θ + (((p + 1 : ℕ)) : ℝ) * α) E (n - p) := by
  simp only [l92_adjF, min_eq_right h, max_eq_left h]

lemma l92_adjF_eq_zero {α lam : ℝ} {θ : ℝ} {E : ℂ} {n p q : ℕ} (h : n ≤ p) :
    l92_adjF α lam θ E n p q = 0 := by
  have hmax : n ≤ max p q := le_trans h (le_max_left p q)
  have hsub : n - max p q = 0 := Nat.sub_eq_zero_of_le hmax
  rw [l92_adjF, hsub]
  simp [pd]

end Work.TMC16Core.Basic

namespace Work.TMC16Core.Basic

open Work.TMC16Core

set_option maxHeartbeats 1000000 in
theorem l92_dirMat_mul_adjM (α lam : ℝ) (θ : ℝ) (E : ℂ) (n : ℕ) :
    dirMat α lam θ E n * l92_adjM α lam θ E n = ((-1 : ℂ)^n * pd α lam θ E (n+1)) • 1 := by
  ext i j
  rw [l92_dirMat_mul_apply]
  simp only [l92_adjM, Matrix.smul_apply, Matrix.one_apply, Fin.val_mk, smul_eq_mul]
  rcases lt_trichotomy (i:ℕ) (j:ℕ) with hlt | heq | hgt
  · have hij : i ≠ j := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
    have hIJ : (i:ℕ) ≤ (j:ℕ) := le_of_lt hlt
    have hI1n : (i:ℕ) + 1 < n := by omega
    have hI1J : (i:ℕ) + 1 ≤ (j:ℕ) := by omega
    have hT1 : (amoPot α lam θ ((i:ℕ):ℤ) - (E:ℂ)) * l92_adjF α lam θ E n (i:ℕ) (j:ℕ)
        = (amoPot α lam θ ((i:ℕ):ℤ) - (E:ℂ)) * ((-1:ℂ)^(n-1) * pd α lam θ E ((i:ℕ)+1)
            * pd α lam (θ + (((j:ℕ)+1:ℕ):ℝ)*α) E (n - (j:ℕ))) := by
      rw [l92_adjF_le (α:=α) (lam:=lam) (θ:=θ) (E:=E) (n:=n) hIJ]
    have hT2 : (if h : (i:ℕ)+1 < n then l92_adjF α lam θ E n ((i:ℕ)+1) (j:ℕ) else 0)
        = (-1:ℂ)^(n-1) * pd α lam θ E ((i:ℕ)+2)
            * pd α lam (θ + (((j:ℕ)+1:ℕ):ℝ)*α) E (n - (j:ℕ)) := by
      rw [dif_pos hI1n, l92_adjF_le (α:=α) (lam:=lam) (θ:=θ) (E:=E) (n:=n) hI1J]
    have hT3 : (if h : 0 < (i:ℕ) then l92_adjF α lam θ E n ((i:ℕ)-1) (j:ℕ) else 0)
        = (-1:ℂ)^(n-1) * pd α lam θ E (i:ℕ)
            * pd α lam (θ + (((j:ℕ)+1:ℕ):ℝ)*α) E (n - (j:ℕ)) := by
      by_cases h0 : 0 < (i:ℕ)
      · rw [dif_pos h0, l92_adjF_le (α:=α) (lam:=lam) (θ:=θ) (E:=E) (n:=n) (show (i:ℕ)-1 ≤ (j:ℕ) by omega)]
        rw [show (i:ℕ) - 1 + 1 = (i:ℕ) by omega]
      · rw [dif_neg h0]
        have hpz : pd α lam θ E (i:ℕ) = 0 := by rw [show (i:ℕ) = 0 by omega]; rfl
        rw [hpz]; ring
    rw [hT1, hT2, hT3, if_neg hij, mul_zero]
    have hbr : (amoPot α lam θ ((i:ℕ):ℤ) - (E:ℂ)) * pd α lam θ E ((i:ℕ)+1)
        + pd α lam θ E ((i:ℕ)+2) + pd α lam θ E (i:ℕ) = 0 := by
      rw [l92_pd_rec α lam θ E (i:ℕ)]; ring
    linear_combination ((-1:ℂ)^(n-1) * pd α lam (θ + (((j:ℕ)+1:ℕ):ℝ)*α) E (n - (j:ℕ))) * hbr
  · have hij : i = j := Fin.ext heq
    subst hij
    have hT1 : (amoPot α lam θ ((i:ℕ):ℤ) - (E:ℂ)) * l92_adjF α lam θ E n (i:ℕ) (i:ℕ)
        = (amoPot α lam θ ((i:ℕ):ℤ) - (E:ℂ)) * ((-1:ℂ)^(n-1) * pd α lam θ E ((i:ℕ)+1)
            * pd α lam (θ + (((i:ℕ)+1:ℕ):ℝ)*α) E (n - (i:ℕ))) := by
      rw [l92_adjF_le (α:=α) (lam:=lam) (θ:=θ) (E:=E) (n:=n) (le_refl _)]
    have hT2 : (if h : (i:ℕ)+1 < n then l92_adjF α lam θ E n ((i:ℕ)+1) (i:ℕ) else 0)
        = (-1:ℂ)^(n-1) * pd α lam θ E ((i:ℕ)+1)
            * pd α lam (θ + (((i:ℕ)+2:ℕ):ℝ)*α) E (n - ((i:ℕ)+1)) := by
      by_cases h : (i:ℕ)+1 < n
      · rw [dif_pos h, l92_adjF_ge (α:=α) (lam:=lam) (θ:=θ) (E:=E) (n:=n) (by omega)]
      · rw [dif_neg h]
        have hz : n - ((i:ℕ)+1) = 0 := by omega
        rw [hz]; simp [pd]
    have hT3 : (if h : 0 < (i:ℕ) then l92_adjF α lam θ E n ((i:ℕ)-1) (i:ℕ) else 0)
        = (-1:ℂ)^(n-1) * pd α lam θ E (i:ℕ)
            * pd α lam (θ + (((i:ℕ)+1:ℕ):ℝ)*α) E (n - (i:ℕ)) := by
      by_cases h0 : 0 < (i:ℕ)
      · rw [dif_pos h0, l92_adjF_le (α:=α) (lam:=lam) (θ:=θ) (E:=E) (n:=n) (by omega)]
        rw [show (i:ℕ) - 1 + 1 = (i:ℕ) by omega]
      · rw [dif_neg h0]
        have hpz : pd α lam θ E (i:ℕ) = 0 := by rw [show (i:ℕ) = 0 by omega]; rfl
        rw [hpz]; ring
    have hnpos : 0 < n := by omega
    have hsign : (-1:ℂ)^(n-1) = -(-1:ℂ)^n := by
      conv_rhs => rw [show n = (n-1) + 1 by omega, pow_succ]
      ring
    rw [hT1, hT2, hT3, if_pos rfl, mul_one, hsign]
    have e1 : pd α lam θ E (i:ℕ) + (amoPot α lam θ ((i:ℕ):ℤ) - (E:ℂ)) * pd α lam θ E ((i:ℕ)+1)
        = - pd α lam θ E ((i:ℕ)+2) := by
      rw [l92_pd_rec α lam θ E (i:ℕ)]; ring
    have e2 : pd α lam θ E (n+1)
        = pd α lam (θ + (((i:ℕ)+1:ℕ):ℝ)*α) E (n - (i:ℕ)) * pd α lam θ E ((i:ℕ)+2)
          - pd α lam (θ + (((i:ℕ)+2:ℕ):ℝ)*α) E (n - ((i:ℕ)+1)) * pd α lam θ E ((i:ℕ)+1) := by
      have h := l92_pd_shift α lam θ E ((i:ℕ)+1) (n - ((i:ℕ)+1))
      rw [show ((i:ℕ)+1) + (n - ((i:ℕ)+1)) + 1 = n+1 by omega] at h
      rw [show n - ((i:ℕ)+1) + 1 = n - (i:ℕ) by omega] at h
      rw [show θ + (((((i:ℕ) + 1 : ℕ)) : ℝ) + 1) * α = θ + ((((i:ℕ) + 2 : ℕ)) : ℝ) * α by
        push_cast; ring] at h
      exact h
    linear_combination (-((-1:ℂ)^n) * pd α lam (θ + (((i:ℕ)+1:ℕ):ℝ)*α) E (n - (i:ℕ))) * e1
      + (-((-1:ℂ)^n)) * e2
  · have hij : i ≠ j := fun h => by rw [h] at hgt; exact lt_irrefl _ hgt
    have hJI : (j:ℕ) ≤ (i:ℕ) := le_of_lt hgt
    have hT1 : (amoPot α lam θ ((i:ℕ):ℤ) - (E:ℂ)) * l92_adjF α lam θ E n (i:ℕ) (j:ℕ)
        = (amoPot α lam θ ((i:ℕ):ℤ) - (E:ℂ)) * ((-1:ℂ)^(n-1) * pd α lam θ E ((j:ℕ)+1)
            * pd α lam (θ + (((i:ℕ)+1:ℕ):ℝ)*α) E (n - (i:ℕ))) := by
      rw [l92_adjF_ge (α:=α) (lam:=lam) (θ:=θ) (E:=E) (n:=n) hJI]
    have hT2 : (if h : (i:ℕ)+1 < n then l92_adjF α lam θ E n ((i:ℕ)+1) (j:ℕ) else 0)
        = (-1:ℂ)^(n-1) * pd α lam θ E ((j:ℕ)+1)
            * pd α lam (θ + (((i:ℕ)+2:ℕ):ℝ)*α) E (n - ((i:ℕ)+1)) := by
      by_cases h : (i:ℕ)+1 < n
      · rw [dif_pos h, l92_adjF_ge (α:=α) (lam:=lam) (θ:=θ) (E:=E) (n:=n) (by omega)]
      · rw [dif_neg h]
        have hz : n - ((i:ℕ)+1) = 0 := by omega
        rw [hz]; simp [pd]
    have hT3 : (if h : 0 < (i:ℕ) then l92_adjF α lam θ E n ((i:ℕ)-1) (j:ℕ) else 0)
        = (-1:ℂ)^(n-1) * pd α lam θ E ((j:ℕ)+1)
            * pd α lam (θ + ((i:ℕ):ℝ)*α) E (n - ((i:ℕ)-1)) := by
      rw [dif_pos (by omega : 0 < (i:ℕ)),
        l92_adjF_ge (α:=α) (lam:=lam) (θ:=θ) (E:=E) (n:=n) (show (j:ℕ) ≤ (i:ℕ)-1 by omega)]
      rw [show (i:ℕ)-1+1 = (i:ℕ) by omega]
    rw [hT1, hT2, hT3, if_neg hij, mul_zero]
    have e3 : pd α lam (θ + ((i:ℕ):ℝ)*α) E (n - (i:ℕ) + 1)
        = (E - ((amoPot α lam θ ((i:ℕ):ℤ) : ℝ) : ℂ)) * pd α lam (θ + (((i:ℕ)+1:ℕ):ℝ)*α) E (n - (i:ℕ))
          - pd α lam (θ + (((i:ℕ)+2:ℕ):ℝ)*α) E (n - ((i:ℕ)+1)) := by
      have h := l92_pd_shift α lam (θ + ((i:ℕ):ℝ)*α) E 1 (n - ((i:ℕ)+1))
      simp only [Nat.cast_one] at h
      rw [show (1:ℕ) + (n - ((i:ℕ)+1)) + 1 = n - (i:ℕ) + 1 by omega] at h
      rw [show n - ((i:ℕ)+1) + 1 = n - (i:ℕ) by omega] at h
      rw [show (θ + ((i:ℕ):ℝ)*α) + 1 * α = θ + ((((i:ℕ)+1:ℕ)):ℝ)*α by push_cast; ring] at h
      rw [show (θ + ((i:ℕ):ℝ)*α) + (1 + 1) * α = θ + ((((i:ℕ)+2:ℕ)):ℝ)*α by push_cast; ring] at h
      rw [h]
      rw [l92_pd_rec α lam (θ + ((i:ℕ):ℝ)*α) E 0]
      rw [show amoPot α lam (θ + ((i:ℕ):ℝ)*α) (((0:ℕ)):ℤ) = amoPot α lam θ ((i:ℕ):ℤ) by
        simp only [amoPot]; push_cast; ring_nf]
      rw [show pd α lam (θ + ((i:ℕ):ℝ)*α) E 1 = 1 from rfl,
          show pd α lam (θ + ((i:ℕ):ℝ)*α) E 0 = 0 from rfl]
      ring
    rw [show n - ((i:ℕ)-1) = n - (i:ℕ) + 1 by omega]
    have hbr : (amoPot α lam θ ((i:ℕ):ℤ) - (E:ℂ)) * pd α lam (θ + (((i:ℕ)+1:ℕ):ℝ)*α) E (n - (i:ℕ))
        + pd α lam (θ + (((i:ℕ)+2:ℕ):ℝ)*α) E (n - ((i:ℕ)+1))
        + pd α lam (θ + ((i:ℕ):ℝ)*α) E (n - (i:ℕ) + 1) = 0 := by
      rw [e3]; ring
    linear_combination ((-1:ℂ)^(n-1) * pd α lam θ E ((j:ℕ)+1)) * hbr

end Work.TMC16Core.Basic

namespace Work.TMC16Core.Basic

open Work.TMC16Core

lemma l92_dirMat_inv_eq (α lam : ℝ) (φ : ℝ) (E : ℂ) (n : ℕ)
    (hR : ((-1:ℂ)^n * pd α lam φ E (n+1)) ≠ 0) :
    (dirMat α lam φ E n)⁻¹ = ((-1:ℂ)^n * pd α lam φ E (n+1))⁻¹ • l92_adjM α lam φ E n := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_smul, l92_dirMat_mul_adjM, smul_smul, inv_mul_cancel₀ hR, one_smul]

lemma l92_dirMat_det_ne_zero (α lam : ℝ) (φ : ℝ) (E : ℂ) (n : ℕ)
    (hR : ((-1:ℂ)^n * pd α lam φ E (n+1)) ≠ 0) : (dirMat α lam φ E n).det ≠ 0 := by
  have h1 : dirMat α lam φ E n * (((-1:ℂ)^n * pd α lam φ E (n+1))⁻¹ • l92_adjM α lam φ E n) = 1 := by
    rw [Matrix.mul_smul, l92_dirMat_mul_adjM, smul_smul, inv_mul_cancel₀ hR, one_smul]
  exact Matrix.det_ne_zero_of_right_inverse h1

lemma l92_dirMat_inv_entry (α lam : ℝ) (φ : ℝ) (E : ℂ) (n : ℕ)
    (hR : ((-1:ℂ)^n * pd α lam φ E (n+1)) ≠ 0) (i j : Fin n) :
    (dirMat α lam φ E n)⁻¹ i j = ((-1:ℂ)^n * pd α lam φ E (n+1))⁻¹ * l92_adjM α lam φ E n i j := by
  rw [l92_dirMat_inv_eq α lam φ E n hR, Matrix.smul_apply, smul_eq_mul]

lemma l92_greenEntry_eq (α lam : ℝ) (φ : ℝ) (E : ℂ) (k : ℕ)
    (hR : ((-1:ℂ)^k * pd α lam φ E (k+1)) ≠ 0) (i j : ℕ) :
    greenEntry α lam φ E k i j =
      (if h : i < k ∧ j < k then
        ((-1:ℂ)^k * pd α lam φ E (k+1))⁻¹ * l92_adjF α lam φ E k i j else 0) := by
  rw [greenEntry]
  split_ifs with h
  · rw [l92_dirMat_inv_entry α lam φ E k hR ⟨i,h.1⟩ ⟨j,h.2⟩]
    rfl
  · rfl

lemma l92_G_eq (α lam : ℝ) (θ : ℝ) (E : ℂ) (k : ℕ) (x₁ x₂ : ℤ)
    (hk : (x₂ - x₁ + 1).toNat = k)
    (hR : ((-1:ℂ)^k * pd α lam (θ + (x₁:ℝ)*α) E (k+1)) ≠ 0) (x y : ℤ) :
    G α lam θ E x₁ x₂ x y =
      (if h : (x-x₁).toNat < k ∧ (y-x₁).toNat < k then
        ((-1:ℂ)^k * pd α lam (θ+(x₁:ℝ)*α) E (k+1))⁻¹
          * l92_adjF α lam (θ+(x₁:ℝ)*α) E k ((x-x₁).toNat) ((y-x₁).toNat) else 0) := by
  rw [G, hk]
  exact l92_greenEntry_eq α lam (θ+(x₁:ℝ)*α) E k hR _ _

end Work.TMC16Core.Basic

namespace Work.TMC16Core.Basic

open Work.TMC16Core

set_option maxHeartbeats 1000000 in
theorem l92_green_bound_notA {α lam : ℝ} {E : ℂ} {θ r L ε₁ : ℝ} {k : ℕ} {x₁ x₂ y : ℤ}
    (hbd : ∀ n : ℕ, n ≤ k → ∀ ζ : ℝ, ‖pd α lam ζ E (n + 1)‖ ≤ Real.exp ((n : ℝ) * (L + ε₁)))
    (hx : x₂ = x₁ + (k : ℤ) - 1) (h1 : x₁ ≤ y) (h2 : y ≤ x₂)
    (hnot : Real.exp (((k : ℝ) + 1) * r) < ‖pd α lam (θ + (x₁ : ℝ) * α) E (k + 1)‖) :
    ‖G α lam θ E x₁ x₂ y x₁‖ < Real.exp ((L + ε₁) * ((x₂ - y : ℤ) : ℝ) - ((k : ℝ) + 1) * r) ∧
    ‖G α lam θ E x₁ x₂ y x₂‖ < Real.exp ((L + ε₁) * ((y - x₁ : ℤ) : ℝ) - ((k : ℝ) + 1) * r) := by
  have hk1 : (x₂ - x₁ + 1).toNat = k := by
    have h : x₂ - x₁ + 1 = (k:ℤ) := by omega
    rw [h]; exact Int.toNat_natCast k
  have hane : 0 ≤ y - x₁ := by omega
  have hbne : 0 ≤ x₂ - y := by omega
  have hkpos : 0 < k := by omega
  have hpdne : pd α lam (θ + (x₁:ℝ)*α) E (k+1) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnot
    exact absurd (Real.exp_pos _) (not_lt.mpr hnot.le)
  have hR : ((-1:ℂ)^k * pd α lam (θ + (x₁:ℝ)*α) E (k+1)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) hpdne
  have hcast_a : (((y-x₁).toNat : ℕ) : ℝ) = (y:ℝ) - (x₁:ℝ) := by
    have h : (((y-x₁).toNat : ℕ) : ℤ) = y - x₁ := Int.toNat_of_nonneg hane
    exact_mod_cast h
  have hcast_b : (((x₂-y).toNat : ℕ) : ℝ) = (x₂:ℝ) - (y:ℝ) := by
    have h : (((x₂-y).toNat : ℕ) : ℤ) = x₂ - y := Int.toNat_of_nonneg hbne
    exact_mod_cast h
  have hka : k - (y-x₁).toNat = (x₂-y).toNat + 1 := by
    have ha : ((y-x₁).toNat : ℤ) = y - x₁ := Int.toNat_of_nonneg hane
    have hb : ((x₂-y).toNat : ℤ) = x₂ - y := Int.toNat_of_nonneg hbne
    omega
  have hyx_lt : (y-x₁).toNat < k := (Int.toNat_lt hane).mpr (by omega)
  have hxx : (x₁-x₁).toNat < k := by
    rw [show x₁ - x₁ = (0:ℤ) by ring]; exact hkpos
  have hxx2 : (x₂-x₁).toNat < k := by
    rw [hx, show x₁ + (k:ℤ) - 1 - x₁ = (k:ℤ) - 1 by ring]
    have h : ((k:ℤ)-1).toNat = k - 1 := by
      have h' : ((((k:ℤ)-1).toNat : ℕ) : ℤ) = (k:ℤ) - 1 := Int.toNat_of_nonneg (by omega)
      omega
    rw [h]; omega
  -- first Green entry
  have hEq1 : G α lam θ E x₁ x₂ y x₁
      = ((-1:ℂ)^k * pd α lam (θ+(x₁:ℝ)*α) E (k+1))⁻¹ * l92_adjF α lam (θ+(x₁:ℝ)*α) E k ((y-x₁).toNat) 0 := by
    rw [l92_G_eq α lam θ E k x₁ x₂ hk1 hR y x₁, dif_pos ⟨hyx_lt, hxx⟩]
    rw [show (x₁-x₁).toNat = 0 by rw [show x₁ - x₁ = (0:ℤ) by ring]; rfl]
  have hadj1 : l92_adjF α lam (θ+(x₁:ℝ)*α) E k ((y-x₁).toNat) 0
      = (-1:ℂ)^(k-1) * pd α lam (θ + ((y:ℝ)+1)*α) E (k - (y-x₁).toNat) := by
    rw [l92_adjF_ge (α:=α) (lam:=lam) (θ:=θ+(x₁:ℝ)*α) (E:=E) (n:=k) (p:=(y-x₁).toNat) (q:=0) (by omega)]
    rw [show (0:ℕ) + 1 = 1 from rfl, show pd α lam (θ + (x₁:ℝ)*α) E 1 = 1 from rfl, mul_one]
    congr 1
    rw [show (θ + (x₁:ℝ)*α) + ((((y-x₁).toNat) + 1 : ℕ) : ℝ) * α = θ + ((y:ℝ)+1)*α by
      push_cast; rw [hcast_a]; ring]
  have hnorm1 : ‖pd α lam (θ + ((y:ℝ)+1)*α) E (k - (y-x₁).toNat)‖
      ≤ Real.exp (((x₂-y:ℤ):ℝ) * (L + ε₁)) := by
    have h := hbd (k - (y-x₁).toNat - 1) (by omega) (θ + ((y:ℝ)+1)*α)
    rw [show k - (y-x₁).toNat - 1 + 1 = k - (y-x₁).toNat by omega] at h
    have hN : ((k - (y-x₁).toNat - 1 : ℕ) : ℝ) = ((x₂-y:ℤ):ℝ) := by
      rw [show k - (y-x₁).toNat - 1 = (x₂-y).toNat by omega]
      have h2' : (((x₂-y).toNat : ℕ) : ℤ) = x₂ - y := Int.toNat_of_nonneg hbne
      exact_mod_cast h2'
    rwa [hN] at h
  have hinv : (‖pd α lam (θ + (x₁:ℝ)*α) E (k+1)‖)⁻¹ < Real.exp (-(((k:ℝ)+1) * r)) := by
    have h := one_div_lt_one_div_of_lt (Real.exp_pos (((k:ℝ)+1) * r)) hnot
    rw [one_div, one_div, ← Real.exp_neg] at h
    exact h
  have hG1b : ‖G α lam θ E x₁ x₂ y x₁‖
      < Real.exp ((L + ε₁) * ((x₂ - y : ℤ) : ℝ) - ((k : ℝ) + 1) * r) := by
    rw [hEq1, hadj1]
    simp only [norm_mul, norm_inv, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have hpos : (0:ℝ) < Real.exp (((x₂-y:ℤ):ℝ) * (L + ε₁)) := Real.exp_pos _
    calc (‖pd α lam (θ + (x₁:ℝ)*α) E (k+1)‖)⁻¹ * ‖pd α lam (θ + ((y:ℝ)+1)*α) E (k - (y-x₁).toNat)‖
        ≤ (‖pd α lam (θ + (x₁:ℝ)*α) E (k+1)‖)⁻¹ * Real.exp (((x₂-y:ℤ):ℝ) * (L + ε₁)) :=
          mul_le_mul_of_nonneg_left hnorm1 (by positivity)
      _ < Real.exp (-(((k:ℝ)+1) * r)) * Real.exp (((x₂-y:ℤ):ℝ) * (L + ε₁)) :=
          mul_lt_mul_of_pos_right hinv hpos
      _ = Real.exp ((L + ε₁) * ((x₂-y:ℤ):ℝ) - ((k:ℝ)+1) * r) := by
          rw [← Real.exp_add]; congr 1; ring
  -- second Green entry
  have hEq2 : G α lam θ E x₁ x₂ y x₂
      = ((-1:ℂ)^k * pd α lam (θ+(x₁:ℝ)*α) E (k+1))⁻¹
          * l92_adjF α lam (θ+(x₁:ℝ)*α) E k ((y-x₁).toNat) ((x₂-x₁).toNat) := by
    rw [l92_G_eq α lam θ E k x₁ x₂ hk1 hR y x₂, dif_pos ⟨hyx_lt, hxx2⟩]
  have hx2n : (x₂-x₁).toNat = k - 1 := by
    rw [hx, show x₁ + (k:ℤ) - 1 - x₁ = (k:ℤ) - 1 by ring]
    have h' : ((((k:ℤ)-1).toNat : ℕ) : ℤ) = (k:ℤ) - 1 := Int.toNat_of_nonneg (by omega)
    omega
  have hadj2 : l92_adjF α lam (θ+(x₁:ℝ)*α) E k ((y-x₁).toNat) ((x₂-x₁).toNat)
      = (-1:ℂ)^(k-1) * pd α lam (θ + (x₁:ℝ)*α) E ((y-x₁).toNat + 1) := by
    rw [hx2n,
      l92_adjF_le (α:=α) (lam:=lam) (θ:=θ+(x₁:ℝ)*α) (E:=E) (n:=k) (p:=(y-x₁).toNat) (q:=k-1) (by omega)]
    rw [show k - (k-1) = 1 by omega]
    rw [show pd α lam (θ + (x₁:ℝ)*α + (((k-1:ℕ)+1 : ℕ) : ℝ) * α) E 1 = 1 from rfl, mul_one]
  have hnorm2 : ‖pd α lam (θ + (x₁:ℝ)*α) E ((y-x₁).toNat + 1)‖
      ≤ Real.exp (((y-x₁:ℤ):ℝ) * (L + ε₁)) := by
    have h := hbd ((y-x₁).toNat) (by omega) (θ + (x₁:ℝ)*α)
    rw [show (((y-x₁).toNat : ℕ) : ℝ) = ((y-x₁:ℤ):ℝ) by
      have h' : (((y-x₁).toNat : ℕ) : ℤ) = y - x₁ := Int.toNat_of_nonneg hane
      exact_mod_cast h'] at h
    exact h
  have hG2b : ‖G α lam θ E x₁ x₂ y x₂‖
      < Real.exp ((L + ε₁) * ((y - x₁ : ℤ) : ℝ) - ((k : ℝ) + 1) * r) := by
    rw [hEq2, hadj2]
    simp only [norm_mul, norm_inv, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have hpos : (0:ℝ) < Real.exp (((y-x₁:ℤ):ℝ) * (L + ε₁)) := Real.exp_pos _
    calc (‖pd α lam (θ + (x₁:ℝ)*α) E (k+1)‖)⁻¹ * ‖pd α lam (θ + (x₁:ℝ)*α) E ((y-x₁).toNat + 1)‖
        ≤ (‖pd α lam (θ + (x₁:ℝ)*α) E (k+1)‖)⁻¹ * Real.exp (((y-x₁:ℤ):ℝ) * (L + ε₁)) :=
          mul_le_mul_of_nonneg_left hnorm2 (by positivity)
      _ < Real.exp (-(((k:ℝ)+1) * r)) * Real.exp (((y-x₁:ℤ):ℝ) * (L + ε₁)) :=
          mul_lt_mul_of_pos_right hinv hpos
      _ = Real.exp ((L + ε₁) * ((y-x₁:ℤ):ℝ) - ((k:ℝ)+1) * r) := by
          rw [← Real.exp_add]; congr 1; ring
  exact ⟨hG1b, hG2b⟩


/-- Arithmetic core of AJ Lemma 9.2: the two exponent inequalities turning the two
Green's-function estimates into decay at rate `L - ε` on the two sides of the interval. -/
theorem l92_exp_bound {k : ℕ} {L ε ε₁ δ a b : ℝ}
    (hL : 0 ≤ L) (hε : 0 < ε) (hεL : ε ≤ L) (hε₁ : 0 < ε₁)
    (hδ1 : 1 / 40 ≤ δ) (hδ2 : δ ≤ 1 / 2)
    (ha : δ * (k : ℝ) ≤ a) (hb : δ * (k : ℝ) - 1 ≤ b) (hab : a + b = (k : ℝ) - 1) :
    (L - ε) * a + b * (L + ε₁) ≤ ((k : ℝ) + 1) * (L - ε * δ + ε₁) ∧
    (L - ε) * b + a * (L + ε₁) ≤ ((k : ℝ) + 1) * (L - ε * δ + ε₁) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hδ0 : (0 : ℝ) < δ := by linarith
  have hεε₁ : (0 : ℝ) < ε + ε₁ := by linarith
  constructor
  · have hb' : b = ((k : ℝ) - 1) - a := by linarith
    have hA : δ * (k : ℝ) * (ε + ε₁) ≤ a * (ε + ε₁) :=
      mul_le_mul_of_nonneg_right ha (le_of_lt hεε₁)
    have h2L : ε * δ ≤ 2 * L := by
      nlinarith [mul_le_mul_of_nonneg_right hεL (le_of_lt hδ0), hδ2, hL]
    have hB : (0 : ℝ) ≤ 2 * L - ε * δ + 2 * ε₁ + δ * (k : ℝ) * ε₁ := by
      nlinarith [h2L, hε₁, mul_nonneg (le_of_lt hδ0) hk0]
    rw [hb']
    nlinarith [hA, hB]
  · have ha' : a = ((k : ℝ) - 1) - b := by linarith
    have hA : (δ * (k : ℝ) - 1) * (ε + ε₁) ≤ b * (ε + ε₁) :=
      mul_le_mul_of_nonneg_right hb (le_of_lt hεε₁)
    have h2L : ε * (1 + δ) ≤ 2 * L := by
      nlinarith [mul_le_mul_of_nonneg_right hεL (by linarith : (0 : ℝ) ≤ 1 + δ), hδ2, hL]
    have hB : (0 : ℝ) ≤ 2 * L - ε * (1 + δ) + ε₁ * (1 + δ * (k : ℝ)) := by
      nlinarith [h2L, hε₁, mul_nonneg (le_of_lt hδ0) hk0]
    rw [ha']
    nlinarith [hA, hB]

/-- **AJ Lemma 9.2** (arXiv v1 `\ref{prop}`; published Lemma 9.2): a `(L-ε,k)`-singular
point forces a whole stretch of the rotation orbit into `A_{k,L-εδ+ε₁}`. -/
theorem lemma_9_2 {α lam : ℝ} {E : ℂ} {θ L ε ε₁ δ : ℝ} {k : ℕ} {y : ℤ}
    (hL : 0 ≤ L) (hεL : ε ≤ L) (hε : 0 < ε) (hε₁ : 0 < ε₁)
    (hδ1 : 1 / 40 ≤ δ) (hδ2 : δ ≤ 1 / 2) (hk40 : 40 ≤ k)
    (hkδ : 1 ≤ (k : ℝ) * (δ - 1 / 40))
    (hbd : ∀ n : ℕ, n ≤ k → ∀ ζ : ℝ,
        ‖Work.TMC16Core.pd α lam ζ E (n + 1)‖ ≤ Real.exp ((n : ℝ) * (L + ε₁)))
    (hs : Work.TMC16Core.IsSingular α lam θ E (L - ε) k y)
    (x : ℤ) (hx1 : y - (1 - δ) * (k : ℝ) ≤ (x : ℝ)) (hx2 : (x : ℝ) ≤ y - δ * (k : ℝ)) :
    θ + ((x : ℝ) + (((k : ℝ) - 1) / 2)) * α ∈ Work.TMC16Core.AkSet α lam E k (L - ε * δ + ε₁) := by
  rw [Work.TMC16Core.mem_AkSet_iff_shift]
  by_contra hcon
  push Not at hcon
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hδ0 : (0 : ℝ) < δ := by linarith
  have hdk : (1 : ℝ) ≤ (k : ℝ) * δ := by nlinarith [hkδ, hkpos]
  have hxy : (x : ℝ) ≤ (y : ℝ) := by nlinarith [hx2, hδ0, hkpos]
  have hyx : (y : ℝ) ≤ (x : ℝ) + (k : ℝ) - 1 := by nlinarith [hx1, hdk]
  have hxyZ : x ≤ y := by exact_mod_cast hxy
  have hyxZ : y ≤ x + (k : ℤ) - 1 := by exact_mod_cast hyx
  have hcast1 : (((y - x : ℤ) : ℝ)) = (y : ℝ) - (x : ℝ) := by push_cast; ring
  have hcast2 : (((x + (k : ℤ) - 1) - y : ℤ) : ℝ) = (x : ℝ) + (k : ℝ) - 1 - (y : ℝ) := by
    push_cast; ring
  have hdist1 : (k : ℤ) ≤ 40 * (y - x) := by
    have hreal : ((k : ℤ) : ℝ) ≤ ((40 * (y - x) : ℤ) : ℝ) := by
      push_cast
      have h1 : δ * (k : ℝ) ≤ (y : ℝ) - (x : ℝ) := by linarith [hx2]
      nlinarith [h1, mul_nonneg (sub_nonneg.mpr hδ1) hkpos.le]
    exact_mod_cast hreal
  have hdist2 : (k : ℤ) ≤ 40 * ((x + (k : ℤ) - 1) - y) := by
    have hreal : ((k : ℤ) : ℝ) ≤ ((40 * ((x + (k : ℤ) - 1) - y) : ℤ) : ℝ) := by
      push_cast
      have h1 : δ * (k : ℝ) - 1 ≤ (x : ℝ) + (k : ℝ) - 1 - (y : ℝ) := by linarith [hx1]
      nlinarith [h1, hkδ, hkpos]
    exact_mod_cast hreal
  have hpdne : Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (k + 1) ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hcon
    exact absurd (Real.exp_pos _) (not_lt.mpr hcon.le)
  have hdet : (Work.TMC16Core.dirMat α lam (θ + (x : ℝ) * α) E k).det ≠ 0 :=
    l92_dirMat_det_ne_zero α lam (θ + (x : ℝ) * α) E k
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) hpdne)
  have ha' : δ * (k : ℝ) ≤ ((y - x : ℤ) : ℝ) := by rw [hcast1]; linarith [hx2]
  have hb' : δ * (k : ℝ) - 1 ≤ (((x + (k : ℤ) - 1) - y : ℤ) : ℝ) := by rw [hcast2]; linarith [hx1]
  have hab' : ((y - x : ℤ) : ℝ) + (((x + (k : ℤ) - 1) - y : ℤ) : ℝ) = (k : ℝ) - 1 := by
    rw [hcast1, hcast2]; ring
  have hbnd := l92_exp_bound (k := k) (L := L) (ε := ε) (ε₁ := ε₁) (δ := δ)
    (a := ((y - x : ℤ) : ℝ)) (b := (((x + (k : ℤ) - 1) - y : ℤ) : ℝ))
    hL hε hεL hε₁ hδ1 hδ2 ha' hb' hab'
  have hgb := l92_green_bound_notA (α := α) (lam := lam) (E := E) (θ := θ)
    (r := L - ε * δ + ε₁) (L := L) (ε₁ := ε₁) (k := k)
    (x₁ := x) (x₂ := x + (k : ℤ) - 1) (y := y) hbd rfl hxyZ hyxZ hcon
  have hnonneg1 : (0 : ℝ) ≤ ((y - x : ℤ) : ℝ) := by rw [hcast1]; linarith [hxy]
  have hnonneg2 : (0 : ℝ) ≤ (((x + (k : ℤ) - 1) - y : ℤ) : ℝ) := by rw [hcast2]; linarith [hyx]
  have hG1 : ‖Work.TMC16Core.G α lam θ E x (x + (k : ℤ) - 1) y x‖ <
      Real.exp (-((L - ε) * |((y - x : ℤ) : ℝ)|)) := by
    refine lt_of_lt_of_le hgb.1 ?_
    rw [Real.exp_le_exp, abs_of_nonneg hnonneg1]
    linarith [hbnd.1]
  have hG2 : ‖Work.TMC16Core.G α lam θ E x (x + (k : ℤ) - 1) y (x + (k : ℤ) - 1)‖ <
      Real.exp (-((L - ε) * |((y - (x + (k : ℤ) - 1) : ℤ) : ℝ)|)) := by
    refine lt_of_lt_of_le hgb.2 ?_
    rw [Real.exp_le_exp]
    have habs : |((y - (x + (k : ℤ) - 1) : ℤ) : ℝ)| = (((x + (k : ℤ) - 1) - y : ℤ) : ℝ) := by
      rw [abs_of_nonpos]
      · push_cast; ring
      · push_cast; linarith [hyx]
    rw [habs]
    linarith [hbnd.2]
  exact hs ⟨x, x + (k : ℤ) - 1, rfl, hxyZ, hyxZ, hdist1, hdist2, hdet, hG1, hG2⟩

end Work.TMC16Core.Basic
