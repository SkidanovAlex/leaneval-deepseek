import Mathlib
import Submission.Work.PARIMPL2.Direct.oidAux
import Submission.Work.PARIMPL2.Direct.orbitCrossBound
import Submission.Work.PARIMPL2.Direct.oidDefs
import Submission.Work.PARIMPL2.Direct.oidArcNeg
import Submission.Work.PARIMPL2.Direct.oidArcPos
import Submission.Work.PARIMPL2.Direct.oidCf_abs_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-!
## The "cross" estimate on the positive side

We bound the weighted sum `∑_j ocA_j · ∏_{i∈(j,n)} (1 + oidCf_i)` by
`(∏_{i<n} (1 + oidCf_i))·(8(1+log R) + 14(exp(12 cr/R) - 1))`.

The backward products are factored at the index `j0` where `λ x_j` crosses `π/2`: the
coefficients `ocA_j` are `≤ 0` for `j < j0` and `≥ 0` for `j0 ≤ j < n`, so with
`\bar Q = ∏_{i∈(j0,n)}(1 + oidCf_i)` one has
`∑_j A_j Q_j = \bar Q·(S_n - P - Q)`, where `P, Q ≥ 0` are the two arc corrections, bounded by
`8δ` (`oidArcNeg`) and `6δ` (`oidArcPos`), with `δ = exp(12 cr/R) - 1`.
-/

/-! ### Elementary facts about `oidCf` and products of `1 + oidCf` -/

/-- Product monotonicity for nonnegative real factors.  (`ℝ` has no `MulLeftMono` instance, so
Mathlib's `Finset.prod_le_prod` is unavailable for `ℝ`.) -/
theorem oidc_prod_le_prod {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  revert hf h
  refine Finset.induction_on s ?_ ?_
  · intro _ _; simp
  · intro a s ha ih hf h
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact mul_le_mul (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => h i (Finset.mem_insert_of_mem hi)))
      (Finset.prod_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
      (le_trans (hf a (Finset.mem_insert_self a s)) (h a (Finset.mem_insert_self a s)))

/-- `1 ≤ ∏ f i` for real factors `f i ≥ 1`. -/
theorem oidc_one_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h : ∀ i ∈ s, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _; simp
  · intro a s ha ih h
    rw [Finset.prod_insert ha]
    have h1 : 1 ≤ ∏ i ∈ s, f i := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have h2 : 1 ≤ f a := h a (Finset.mem_insert_self a s)
    have h3 : 0 ≤ ∏ i ∈ s, f i := le_trans zero_le_one h1
    nlinarith [h1, h2, h3]

/-- Subset monotonicity of products: factors `≥ 1` outside `s`, `≥ 0` inside `s`. -/
theorem oidc_prod_le_prod_of_subset_of_one_le {ι : Type*} (s t : Finset ι) (f : ι → ℝ)
    (hst : s ⊆ t) (h1 : ∀ i ∈ t, i ∉ s → 1 ≤ f i) (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  classical
  rw [← Finset.prod_sdiff hst]
  have h2 : 1 ≤ ∏ i ∈ t \ s, f i :=
    oidc_one_le_prod _ _
      (fun i hi => h1 i (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hi).2)
  have h3 : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg hf
  nlinarith [h2, h3]

/-- Splitting an `Ico`-product at an intermediate index. -/
theorem oidc_prod_Ico_split (f : ℕ → ℝ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    (∏ i ∈ Finset.Ico a b, f i) * (∏ i ∈ Finset.Ico b c, f i) = ∏ i ∈ Finset.Ico a c, f i := by
  have h1 : Finset.Ico a c = Finset.Ico a b ∪ Finset.Ico b c := by
    ext i; simp only [Finset.mem_Ico, Finset.mem_union]; omega
  rw [h1, Finset.prod_union]
  exact Finset.disjoint_left.mpr (fun i hi1 hi2 => by
    simp only [Finset.mem_Ico] at hi1 hi2; omega)

/-- `1 - exp (-X) ≤ exp X - 1` for `X ≥ 0`. -/
theorem oidc_one_sub_exp_neg_le (X : ℝ) (hX : 0 ≤ X) :
    1 - Real.exp (-X) ≤ Real.exp X - 1 := by
  have h1 := Real.add_one_le_exp X
  have h2 := Real.add_one_le_exp (-X)
  linarith

/-- `oidCf lam cr x y j = cr·λ·sinh(λy)·cosh(λy)/(D_j·y)` is nonnegative when `cr ≥ 0`. -/
theorem oidc_oidCf_nonneg (lam cr : ℝ) (hlam : 0 < lam) (hcr : 0 ≤ cr) (x y : ℕ → ℝ) (j : ℕ)
    (hD : 0 < ocDen lam x y j) : 0 ≤ oidCf lam cr x y j := by
  by_cases hy : y j = 0
  · rw [oidCf, oidZeta_im_zero_of lam x y j hy, hy, mul_zero, zero_div]
  · have hsy : 0 ≤ Real.sinh (lam * y j) * (lam * y j) := by
      rcases le_total 0 (lam * y j) with h | h
      · have h1 : 0 ≤ Real.sinh (lam * y j) := by
          have h2 := Real.sinh_le_sinh.mpr h
          rwa [Real.sinh_zero] at h2
        positivity
      · have h1 : Real.sinh (lam * y j) ≤ 0 := by
          have h2 := Real.sinh_le_sinh.mpr h
          rwa [Real.sinh_zero] at h2
        nlinarith [h]
    rw [oidCf, oidZeta_im]
    have hcosh : 0 < Real.cosh (lam * y j) := Real.cosh_pos _
    have hnum : 0 ≤ cr * (Real.sinh (lam * y j) * (lam * y j) * Real.cosh (lam * y j)) :=
      mul_nonneg hcr (mul_nonneg hsy hcosh.le)
    have hden : 0 ≤ ocDen lam x y j * (y j) ^ 2 := mul_nonneg hD.le (sq_nonneg _)
    rw [show -cr * (-(lam * Real.sinh (lam * y j) * Real.cosh (lam * y j)) / ocDen lam x y j)
          / y j
        = cr * (Real.sinh (lam * y j) * (lam * y j) * Real.cosh (lam * y j))
            / (ocDen lam x y j * (y j)^2) by
      field_simp]
    exact div_nonneg hnum hden

/-- `1 + oidCf ≤ exp (oidCg)`. -/
theorem oidc_one_add_oidCf_le_exp (lam cr : ℝ) (hlam : 0 < lam) (hcr : 0 ≤ cr)
    (x y : ℕ → ℝ) (j : ℕ) (hD : 0 < ocDen lam x y j) :
    1 + oidCf lam cr x y j ≤ Real.exp (oidCg lam cr x y j) := by
  have h1 : oidCf lam cr x y j ≤ oidCg lam cr x y j := by
    have h := oidCf_abs_le lam cr hlam x y j
    rw [abs_of_nonneg hcr] at h
    exact le_trans (le_abs_self _) h
  have h2 := Real.add_one_le_exp (oidCg lam cr x y j)
  linarith

/-- `∏_{i∈Ico a b} (1 + oidCf_i) ≤ exp (∑_{i∈Ico a b} oidCg_i)`, for indices `≤ n`. -/
theorem oidc_prod_one_add_le_exp_sum (lam cr : ℝ) (hlam : 0 < lam) (hcr : 0 ≤ cr)
    (x y : ℕ → ℝ) (n a b : ℕ) (hDpos : ∀ j ≤ n, 0 < ocDen lam x y j)
    (hb : ∀ i ∈ Finset.Ico a b, i ≤ n) :
    (∏ i ∈ Finset.Ico a b, (1 + oidCf lam cr x y i))
      ≤ Real.exp (∑ i ∈ Finset.Ico a b, oidCg lam cr x y i) := by
  calc (∏ i ∈ Finset.Ico a b, (1 + oidCf lam cr x y i))
      ≤ ∏ i ∈ Finset.Ico a b, Real.exp (oidCg lam cr x y i) :=
        oidc_prod_le_prod _ _ _
          (fun i hi => by
            have h1 := oidc_oidCf_nonneg lam cr hlam hcr x y i (hDpos i (hb i hi))
            linarith)
          (fun i hi => oidc_one_add_oidCf_le_exp lam cr hlam hcr x y i (hDpos i (hb i hi)))
    _ = Real.exp (∑ i ∈ Finset.Ico a b, oidCg lam cr x y i) := (Real.exp_sum _ _).symm

/-- The crossing index of `λ x` through `π/2`. -/
theorem oidc_exists_cross (lam : ℝ) (hlam : 0 < lam) (n : ℕ) (x : ℕ → ℝ)
    (hdec : ∀ j < n, x (j + 1) ≤ x j - 1 / 3) :
    ∃ j0 : ℕ, j0 ≤ n ∧ (∀ j < j0, Real.pi / 2 < lam * x j)
      ∧ (∀ j, j0 ≤ j → j < n → lam * x j ≤ Real.pi / 2) := by
  have hxanti : ∀ b, b ≤ n → ∀ a, a ≤ b → x b ≤ x a := by
    intro b
    induction b with
    | zero => intro _ a ha; simp only [Nat.le_zero] at ha; subst ha; exact le_rfl
    | succ b ih =>
      intro hb a ha
      rcases Nat.eq_or_lt_of_le ha with h | h
      · subst h; exact le_rfl
      · have hab : a ≤ b := by omega
        have hbn : b ≤ n := by omega
        have ih' := ih hbn a hab
        have hd : x (b+1) ≤ x b := by
          have := hdec b (Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hb); linarith
        linarith
  classical
  by_cases hex : ∃ j, j ≤ n ∧ lam * x j ≤ Real.pi / 2
  · refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_, ?_⟩
    · intro j hj
      have h1 := Nat.find_min hex hj
      have hjn : j ≤ n := le_trans (le_of_lt hj) (Nat.find_spec hex).1
      by_contra hcon
      exact h1 ⟨hjn, not_lt.mp hcon⟩
    · intro j hj hjn
      have hle : lam * x j ≤ lam * x (Nat.find hex) :=
        mul_le_mul_of_nonneg_left (hxanti j (le_of_lt hjn) (Nat.find hex) hj) hlam.le
      have h2 : lam * x (Nat.find hex) ≤ Real.pi / 2 := (Nat.find_spec hex).2
      linarith
  · refine ⟨n, le_rfl, ?_, ?_⟩
    · intro j hj
      by_contra hcon
      exact hex ⟨j, le_of_lt hj, not_lt.mp hcon⟩
    · intro j hj hjn; omega

theorem oidCrossPos (lam R cr : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (hcr : 0 ≤ cr) (hcpR : cr ≤ 3 * R / 16)
    (n : ℕ) (x y : ℕ → ℝ)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ x j) (hx2 : ∀ j ≤ n, x j ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, x (j + 1) ≤ x j - 1 / 3)
    (hDpos : ∀ j ≤ n, 0 < Work.PARIMPL2.Direct.ocDen lam x y j)
    (hSn : |∑ j ∈ Finset.range n, Work.PARIMPL2.Direct.ocA lam x y j| ≤ 8 * (1 + Real.log R)) :
    |∑ j ∈ Finset.range n, Work.PARIMPL2.Direct.ocA lam x y j
        * ∏ i ∈ Finset.Ico (j + 1) n, (1 + Work.PARIMPL2.Direct.oidCf lam cr x y i)|
      ≤ (∏ i ∈ Finset.range n, (1 + Work.PARIMPL2.Direct.oidCf lam cr x y i))
        * (8 * (1 + Real.log R) + 14 * (Real.exp (12 * cr / R) - 1)) := by
  classical
  have hRpos : (0:ℝ) < R := by linarith
  -- ## basic window facts
  have hxpos : ∀ j ≤ n, 0 < x j := fun j hj => by linarith [hx1 j hj, hRpos]
  have htxpos : ∀ j ≤ n, 0 < lam * x j := fun j hj => mul_pos hlam (hxpos j hj)
  have htxltpi : ∀ j ≤ n, lam * x j < Real.pi := by
    intro j hj
    have h := mul_le_mul_of_nonneg_left (hx2 j hj) hlam.le
    have he : lam * (Real.pi / lam - R / 4) = Real.pi - lam * R / 4 := by field_simp
    rw [he] at h
    have h2 : 0 < lam * R / 4 := by positivity
    linarith
  have hsinpos : ∀ j ≤ n, 0 < Real.sin (lam * x j) := fun j hj =>
    Real.sin_pos_of_pos_of_lt_pi (htxpos j hj) (htxltpi j hj)
  -- ## the crossing index
  obtain ⟨j0, hj0le, hnegArc, hposArc⟩ := oidc_exists_cross lam hlam n x hdec
  -- ## the signs of `ocA`
  have hAle : ∀ j < j0, ocA lam x y j ≤ 0 := by
    intro j hj
    have hjn : j ≤ n := le_trans (le_of_lt hj) hj0le
    have hcos : Real.cos (lam * x j) < 0 := by
      have h2 : lam * x j < Real.pi := htxltpi j hjn
      have hp := Real.cos_pos_of_mem_Ioo (x := Real.pi - lam * x j)
        ⟨by linarith [Real.pi_pos], by linarith [hnegArc j hj]⟩
      rw [Real.cos_pi_sub] at hp
      linarith [hp]
    rw [ocA]
    have hD := hDpos j hjn
    have hs := hsinpos j hjn
    have hnum : lam * Real.sin (lam * x j) * Real.cos (lam * x j) ≤ 0 := by
      have h1 : 0 < lam * Real.sin (lam * x j) := mul_pos hlam hs
      nlinarith [h1, hcos]
    exact div_nonpos_of_nonpos_of_nonneg hnum hD.le
  have hAge : ∀ j, j0 ≤ j → j < n → 0 ≤ ocA lam x y j := by
    intro j hj hjn
    have hjn' : j ≤ n := le_of_lt hjn
    have hcos : 0 ≤ Real.cos (lam * x j) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [htxpos j hjn', Real.pi_pos], hposArc j hj hjn⟩
    rw [ocA]
    have hD := hDpos j hjn'
    have hs := hsinpos j hjn'
    exact div_nonneg (mul_nonneg (mul_nonneg hlam.le hs.le) hcos) hD.le
  -- ## the factors `1 + oidCf` are `≥ 1 > 0`
  have hCnn : ∀ i ≤ n, 0 ≤ oidCf lam cr x y i :=
    fun i hi => oidc_oidCf_nonneg lam cr hlam hcr x y i (hDpos i hi)
  have hC1 : ∀ i ≤ n, 1 ≤ 1 + oidCf lam cr x y i := fun i hi => by linarith [hCnn i hi]
  have hC0 : ∀ i ≤ n, 0 < 1 + oidCf lam cr x y i := fun i hi => by linarith [hCnn i hi]
  -- ## abbreviations
  set Qf : ℕ → ℝ := fun j => ∏ i ∈ Finset.Ico (j+1) n, (1 + oidCf lam cr x y i) with hQf
  set Qbar : ℝ := ∏ i ∈ Finset.Ico (j0+1) n, (1 + oidCf lam cr x y i) with hQbar
  set Pf : ℝ := ∏ i ∈ Finset.range n, (1 + oidCf lam cr x y i) with hPf
  set E : ℝ := Real.exp (12 * cr / R) - 1 with hE
  have hQbarnn : 0 ≤ Qbar := by
    rw [hQbar]
    exact Finset.prod_nonneg (fun i hi => by
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
      exact le_of_lt (hC0 i (le_of_lt h2)))
  have hPfnn : 0 ≤ Pf := by
    rw [hPf]
    exact Finset.prod_nonneg (fun i hi => by
      have h2 := Finset.mem_range.mp hi
      exact le_of_lt (hC0 i (le_of_lt h2)))
  have hEnn : 0 ≤ E := by
    rw [hE]
    have h : 0 ≤ 12 * cr / R := by positivity
    linarith [Real.one_le_exp h]
  have hQbar_le_Pf : Qbar ≤ Pf := by
    rw [hQbar, hPf]
    exact oidc_prod_le_prod_of_subset_of_one_le _ _ _
      (fun i hi => by
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
        exact Finset.mem_range.mpr h2)
      (fun i hi _ => by
        have h2 := Finset.mem_range.mp hi
        exact hC1 i (le_of_lt h2))
      (fun i hi => by
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
        exact le_of_lt (hC0 i (le_of_lt h2)))
  -- ## the product comparisons
  have hQf_ns : ∀ j < j0, Qbar ≤ Qf j := by
    intro j hj
    rw [hQbar, hQf]
    exact oidc_prod_le_prod_of_subset_of_one_le _ _ _
      (fun i hi => by simp only [Finset.mem_Ico] at hi ⊢; omega)
      (fun i hi _ => by
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
        exact hC1 i (le_of_lt h2))
      (fun i hi => by
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
        exact le_of_lt (hC0 i (le_of_lt h2)))
  have hQf_nl : ∀ j < j0, Qf j ≤ Qbar * (∏ i ∈ Finset.Ico (j+1) (j0+1),
      (1 + oidCf lam cr x y i)) := by
    intro j hj
    have hsub : Finset.Ico (j+1) n ⊆ Finset.Ico (j+1) (j0+1) ∪ Finset.Ico (j0+1) n := by
      intro i hi; simp only [Finset.mem_Ico, Finset.mem_union] at hi ⊢; omega
    have hdisj : Disjoint (Finset.Ico (j+1) (j0+1)) (Finset.Ico (j0+1) n) :=
      Finset.disjoint_left.mpr (fun i hi1 hi2 => by
        simp only [Finset.mem_Ico] at hi1 hi2; omega)
    rw [hQf, hQbar]
    calc (∏ i ∈ Finset.Ico (j+1) n, (1 + oidCf lam cr x y i))
        ≤ ∏ i ∈ Finset.Ico (j+1) (j0+1) ∪ Finset.Ico (j0+1) n,
            (1 + oidCf lam cr x y i) :=
          oidc_prod_le_prod_of_subset_of_one_le _ _ _ hsub
            (fun i hi _ => hC1 i (by
              rcases Finset.mem_union.mp hi with h' | h'
              · obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp h'
                omega
              · obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp h'
                omega))
            (fun i hi => by
              obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
              exact le_of_lt (hC0 i (le_of_lt h2)))
      _ = (∏ i ∈ Finset.Ico (j+1) (j0+1), (1 + oidCf lam cr x y i))
            * (∏ i ∈ Finset.Ico (j0+1) n, (1 + oidCf lam cr x y i)) :=
          Finset.prod_union hdisj
      _ = (∏ i ∈ Finset.Ico (j0+1) n, (1 + oidCf lam cr x y i))
            * (∏ i ∈ Finset.Ico (j+1) (j0+1), (1 + oidCf lam cr x y i)) := by ring
  have hQf_ps : ∀ j, j0 ≤ j → j < n → Qf j ≤ Qbar := by
    intro j hj hjn
    rw [hQf, hQbar]
    exact oidc_prod_le_prod_of_subset_of_one_le _ _ _
      (fun i hi => by simp only [Finset.mem_Ico] at hi ⊢; omega)
      (fun i hi _ => by
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
        exact hC1 i (le_of_lt h2))
      (fun i hi => by
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
        exact le_of_lt (hC0 i (le_of_lt h2)))
  have hQf_pg : ∀ j, j0 ≤ j → j < n →
      Qbar * Real.exp (-(∑ i ∈ Finset.Ico (j0+1) (j+1), oidCg lam cr x y i)) ≤ Qf j := by
    intro j hj hjn
    have hsplit := oidc_prod_Ico_split (fun i => (1 + oidCf lam cr x y i))
      (show j0+1 ≤ j+1 by omega) (show j+1 ≤ n by omega)
    have hqj_le : (∏ i ∈ Finset.Ico (j0+1) (j+1), (1 + oidCf lam cr x y i))
        ≤ Real.exp (∑ i ∈ Finset.Ico (j0+1) (j+1), oidCg lam cr x y i) :=
      oidc_prod_one_add_le_exp_sum lam cr hlam hcr x y n (j0+1) (j+1) hDpos
        (fun i hi => by
          obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
          omega)
    have hqjpos : 0 < ∏ i ∈ Finset.Ico (j0+1) (j+1), (1 + oidCf lam cr x y i) :=
      Finset.prod_pos (fun i hi => by
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
        exact hC0 i (by omega))
    have hle1 : Real.exp (-(∑ i ∈ Finset.Ico (j0+1) (j+1), oidCg lam cr x y i))
        ≤ 1 / (∏ i ∈ Finset.Ico (j0+1) (j+1), (1 + oidCf lam cr x y i)) := by
      simpa only [Real.exp_neg, one_div] using one_div_le_one_div_of_le hqjpos hqj_le
    have hQbar_eq : Qbar
        = (∏ i ∈ Finset.Ico (j0+1) (j+1), (1 + oidCf lam cr x y i)) * Qf j := by
      rw [hQbar, hQf, ← hsplit]
    have hQfj : Qf j = Qbar / (∏ i ∈ Finset.Ico (j0+1) (j+1), (1 + oidCf lam cr x y i)) := by
      rw [hQbar_eq]
      rw [eq_div_iff (ne_of_gt hqjpos)]
      ring
    calc Qbar * Real.exp (-(∑ i ∈ Finset.Ico (j0+1) (j+1), oidCg lam cr x y i))
        ≤ Qbar * (1 / (∏ i ∈ Finset.Ico (j0+1) (j+1), (1 + oidCf lam cr x y i))) :=
          mul_le_mul_of_nonneg_left hle1 hQbarnn
      _ = Qf j := by rw [hQfj]; ring
  -- ## the two arc estimates
  have hArcNeg := oidArcNeg lam R cr hlam hR hlamR hcr hcpR n j0 x y hj0le hnegArc
    hx1 hx2 hdec hDpos hSn
  have hArcPos := oidArcPos lam R cr hlam hR hlamR hcr n j0 x y hj0le hposArc
    hx1 hx2 hdec hDpos hSn
  -- ## the split of the sum
  have hsum_split : (∑ j ∈ Finset.range n, ocA lam x y j * Qf j)
      = (∑ j ∈ Finset.range j0, ocA lam x y j * Qf j)
        + ∑ j ∈ Finset.Ico j0 n, ocA lam x y j * Qf j := by
    simp only [Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive (fun j => ocA lam x y j * Qf j) (Nat.zero_le j0) hj0le).symm
  -- ### negative arc
  have hYnn : ∀ j, 0 ≤ ∑ i ∈ Finset.Ico (j+1) (j0+1), oidCg lam cr x y i := by
    intro j
    apply Finset.sum_nonneg
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
    exact oidCg_nonneg lam cr x y hcr i (hDpos i (by omega))
  have hneg_low : Qbar * ((∑ j ∈ Finset.range j0, ocA lam x y j)
        - ∑ j ∈ Finset.range j0, |ocA lam x y j|
            * (Real.exp (∑ i ∈ Finset.Ico (j+1) (j0+1), oidCg lam cr x y i) - 1))
      ≤ ∑ j ∈ Finset.range j0, ocA lam x y j * Qf j := by
    have hpt : ∀ j ∈ Finset.range j0, Qbar * (ocA lam x y j - |ocA lam x y j|
          * (Real.exp (∑ i ∈ Finset.Ico (j+1) (j0+1), oidCg lam cr x y i) - 1))
        ≤ ocA lam x y j * Qf j := by
      intro j hj
      have hjlt := Finset.mem_range.mp hj
      have hA := hAle j hjlt
      have hq_le : (∏ i ∈ Finset.Ico (j+1) (j0+1), (1 + oidCf lam cr x y i))
          ≤ Real.exp (∑ i ∈ Finset.Ico (j+1) (j0+1), oidCg lam cr x y i) :=
        oidc_prod_one_add_le_exp_sum lam cr hlam hcr x y n (j+1) (j0+1) hDpos
          (fun i hi => by
            obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
            omega)
      have hstepA : ocA lam x y j
            * (Qbar * (∏ i ∈ Finset.Ico (j+1) (j0+1), (1 + oidCf lam cr x y i)))
          ≤ ocA lam x y j * Qf j := mul_le_mul_of_nonpos_left (hQf_nl j hjlt) hA
      have hstepB : ocA lam x y j
            * (Qbar * Real.exp (∑ i ∈ Finset.Ico (j+1) (j0+1), oidCg lam cr x y i))
          ≤ ocA lam x y j
            * (Qbar * (∏ i ∈ Finset.Ico (j+1) (j0+1), (1 + oidCf lam cr x y i))) :=
        mul_le_mul_of_nonpos_left (mul_le_mul_of_nonneg_left hq_le hQbarnn) hA
      have hstepC : Qbar * (ocA lam x y j - |ocA lam x y j|
            * (Real.exp (∑ i ∈ Finset.Ico (j+1) (j0+1), oidCg lam cr x y i) - 1))
          = ocA lam x y j
            * (Qbar * Real.exp (∑ i ∈ Finset.Ico (j+1) (j0+1), oidCg lam cr x y i)) := by
        rw [abs_of_nonpos hA]; ring
      linarith [hstepA, hstepB, hstepC.le, hstepC.ge]
    calc Qbar * ((∑ j ∈ Finset.range j0, ocA lam x y j)
          - ∑ j ∈ Finset.range j0, |ocA lam x y j|
              * (Real.exp (∑ i ∈ Finset.Ico (j+1) (j0+1), oidCg lam cr x y i) - 1))
        = ∑ j ∈ Finset.range j0, Qbar * (ocA lam x y j - |ocA lam x y j|
              * (Real.exp (∑ i ∈ Finset.Ico (j+1) (j0+1), oidCg lam cr x y i) - 1)) := by
          rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j hj; ring
      _ ≤ ∑ j ∈ Finset.range j0, ocA lam x y j * Qf j := Finset.sum_le_sum hpt
  have hneg_up : (∑ j ∈ Finset.range j0, ocA lam x y j * Qf j)
      ≤ Qbar * (∑ j ∈ Finset.range j0, ocA lam x y j) := by
    calc (∑ j ∈ Finset.range j0, ocA lam x y j * Qf j)
        ≤ ∑ j ∈ Finset.range j0, ocA lam x y j * Qbar := by
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonpos_left (hQf_ns j (Finset.mem_range.mp hj))
            (hAle j (Finset.mem_range.mp hj))
      _ = Qbar * (∑ j ∈ Finset.range j0, ocA lam x y j) := by
          rw [← Finset.sum_mul]; ring
  have hneg_fin : Qbar * ((∑ j ∈ Finset.range j0, ocA lam x y j) - 8 * E)
      ≤ ∑ j ∈ Finset.range j0, ocA lam x y j * Qf j := by
    have h1 := hArcNeg
    rw [← hE] at h1
    have h2 : Qbar * (∑ j ∈ Finset.range j0, |ocA lam x y j|
          * (Real.exp (∑ i ∈ Finset.Ico (j+1) (j0+1), oidCg lam cr x y i) - 1))
        ≤ Qbar * (8 * E) := mul_le_mul_of_nonneg_left h1 hQbarnn
    linarith [hneg_low, h2]
  -- ### positive arc
  have hXnn : ∀ j, j < n → 0 ≤ ∑ i ∈ Finset.Ico (j0+1) (j+1), oidCg lam cr x y i := by
    intro j hjn
    apply Finset.sum_nonneg
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
    exact oidCg_nonneg lam cr x y hcr i (hDpos i (le_of_lt (lt_of_lt_of_le h2 hjn)))
  have hpos_low : Qbar * ((∑ j ∈ Finset.Ico j0 n, ocA lam x y j)
        - ∑ j ∈ Finset.Ico j0 n, ocA lam x y j
            * (Real.exp (∑ i ∈ Finset.Ico (j0+1) (j+1), oidCg lam cr x y i) - 1))
      ≤ ∑ j ∈ Finset.Ico j0 n, ocA lam x y j * Qf j := by
    have hpt : ∀ j ∈ Finset.Ico j0 n, Qbar * (ocA lam x y j - ocA lam x y j
          * (Real.exp (∑ i ∈ Finset.Ico (j0+1) (j+1), oidCg lam cr x y i) - 1))
        ≤ ocA lam x y j * Qf j := by
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
      have hA := hAge j hj1 hj2
      have hstepA : ocA lam x y j
            * (Qbar * Real.exp (-(∑ i ∈ Finset.Ico (j0+1) (j+1), oidCg lam cr x y i)))
          ≤ ocA lam x y j * Qf j := mul_le_mul_of_nonneg_left (hQf_pg j hj1 hj2) hA
      have hstepB : ocA lam x y j * (Qbar * (2 - Real.exp (∑ i ∈ Finset.Ico (j0+1) (j+1),
              oidCg lam cr x y i)))
          ≤ ocA lam x y j
            * (Qbar * Real.exp (-(∑ i ∈ Finset.Ico (j0+1) (j+1), oidCg lam cr x y i))) := by
        apply mul_le_mul_of_nonneg_left _ hA
        apply mul_le_mul_of_nonneg_left _ hQbarnn
        have h := oidc_one_sub_exp_neg_le (∑ i ∈ Finset.Ico (j0+1) (j+1), oidCg lam cr x y i)
          (hXnn j hj2)
        linarith
      have hstepC : Qbar * (ocA lam x y j - ocA lam x y j
            * (Real.exp (∑ i ∈ Finset.Ico (j0+1) (j+1), oidCg lam cr x y i) - 1))
          = ocA lam x y j * (Qbar * (2 - Real.exp (∑ i ∈ Finset.Ico (j0+1) (j+1),
              oidCg lam cr x y i))) := by ring
      linarith [hstepA, hstepB, hstepC.le, hstepC.ge]
    calc Qbar * ((∑ j ∈ Finset.Ico j0 n, ocA lam x y j)
          - ∑ j ∈ Finset.Ico j0 n, ocA lam x y j
              * (Real.exp (∑ i ∈ Finset.Ico (j0+1) (j+1), oidCg lam cr x y i) - 1))
        = ∑ j ∈ Finset.Ico j0 n, Qbar * (ocA lam x y j - ocA lam x y j
              * (Real.exp (∑ i ∈ Finset.Ico (j0+1) (j+1), oidCg lam cr x y i) - 1)) := by
          rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j hj; ring
      _ ≤ ∑ j ∈ Finset.Ico j0 n, ocA lam x y j * Qf j := Finset.sum_le_sum hpt
  have hpos_up : (∑ j ∈ Finset.Ico j0 n, ocA lam x y j * Qf j)
      ≤ Qbar * (∑ j ∈ Finset.Ico j0 n, ocA lam x y j) := by
    calc (∑ j ∈ Finset.Ico j0 n, ocA lam x y j * Qf j)
        ≤ ∑ j ∈ Finset.Ico j0 n, ocA lam x y j * Qbar := by
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left (hQf_ps j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2)
            (hAge j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2)
      _ = Qbar * (∑ j ∈ Finset.Ico j0 n, ocA lam x y j) := by
          rw [← Finset.sum_mul]; ring
  have hpos_fin : Qbar * ((∑ j ∈ Finset.Ico j0 n, ocA lam x y j) - 6 * E)
      ≤ ∑ j ∈ Finset.Ico j0 n, ocA lam x y j * Qf j := by
    have h1 := hArcPos
    rw [← hE] at h1
    have h2 : Qbar * (∑ j ∈ Finset.Ico j0 n, ocA lam x y j
          * (Real.exp (∑ i ∈ Finset.Ico (j0+1) (j+1), oidCg lam cr x y i) - 1))
        ≤ Qbar * (6 * E) := mul_le_mul_of_nonneg_left h1 hQbarnn
    linarith [hpos_low, h2]
  -- ## the total `∑_j ocA j` and its split
  have hmnegnn : 0 ≤ ∑ j ∈ Finset.range j0, -(ocA lam x y j) :=
    Finset.sum_nonneg (fun j hj => by
      have := hAle j (Finset.mem_range.mp hj); linarith)
  have hmposnn : 0 ≤ ∑ j ∈ Finset.Ico j0 n, ocA lam x y j :=
    Finset.sum_nonneg (fun j hj =>
      hAge j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2)
  have hSnsplit : (∑ j ∈ Finset.range n, ocA lam x y j)
      = (∑ j ∈ Finset.Ico j0 n, ocA lam x y j) - ∑ j ∈ Finset.range j0, -(ocA lam x y j) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    have hsp := Finset.sum_Ico_consecutive (fun j => ocA lam x y j) (Nat.zero_le j0) hj0le
    have h1 : (∑ j ∈ Finset.Ico 0 j0, ocA lam x y j)
        = -(∑ j ∈ Finset.Ico 0 j0, -(ocA lam x y j)) := by
      rw [Finset.sum_neg_distrib]; ring
    linarith [hsp, h1]
  set Sn : ℝ := (∑ j ∈ Finset.Ico j0 n, ocA lam x y j) - ∑ j ∈ Finset.range j0, -(ocA lam x y j)
    with hSnDef
  have hSigma_le : (∑ j ∈ Finset.range n, ocA lam x y j * Qf j) ≤ Qbar * Sn := by
    rw [hsum_split]
    have h1 : -(∑ j ∈ Finset.range j0, -(ocA lam x y j))
        = ∑ j ∈ Finset.range j0, ocA lam x y j := by
      rw [Finset.sum_neg_distrib]; ring
    have h2 : Qbar * Sn = Qbar * (∑ j ∈ Finset.Ico j0 n, ocA lam x y j)
        + Qbar * (∑ j ∈ Finset.range j0, ocA lam x y j) := by
      rw [hSnDef, ← h1]; ring
    rw [h2]
    linarith [hneg_up, hpos_up]
  have hSigma_ge : Qbar * (Sn - 14 * E) ≤ ∑ j ∈ Finset.range n, ocA lam x y j * Qf j := by
    rw [hsum_split]
    have h1 : -(∑ j ∈ Finset.range j0, -(ocA lam x y j))
        = ∑ j ∈ Finset.range j0, ocA lam x y j := by
      rw [Finset.sum_neg_distrib]; ring
    have h2 : Qbar * (Sn - 14 * E)
        = Qbar * ((∑ j ∈ Finset.Ico j0 n, ocA lam x y j) - 6 * E)
          + Qbar * ((∑ j ∈ Finset.range j0, ocA lam x y j) - 8 * E) := by
      rw [hSnDef, ← h1]; ring
    rw [h2]
    linarith [hneg_fin, hpos_fin]
  -- ## absolute value bound
  have hAbs : |∑ j ∈ Finset.range n, ocA lam x y j * Qf j| ≤ Qbar * (|Sn| + 14 * E) := by
    rw [abs_le']
    constructor
    · calc (∑ j ∈ Finset.range n, ocA lam x y j * Qf j) ≤ Qbar * Sn := hSigma_le
        _ ≤ Qbar * (|Sn| + 14 * E) := by
            apply mul_le_mul_of_nonneg_left _ hQbarnn
            linarith [le_abs_self Sn, hEnn]
    · have h2 : -(Qbar * (Sn - 14 * E)) = Qbar * (14 * E - Sn) := by ring
      calc -(∑ j ∈ Finset.range n, ocA lam x y j * Qf j) ≤ -(Qbar * (Sn - 14 * E)) := by
            linarith [hSigma_ge]
        _ = Qbar * (14 * E - Sn) := h2
        _ ≤ Qbar * (|Sn| + 14 * E) := by
            apply mul_le_mul_of_nonneg_left _ hQbarnn
            linarith [neg_le_abs Sn, hEnn]
  -- ## final assembly
  have hSabs : |Sn| ≤ 8 * (1 + Real.log R) := by
    have h := hSn
    rw [hSnsplit] at h
    exact h
  calc |∑ j ∈ Finset.range n, ocA lam x y j * Qf j|
      ≤ Qbar * (|Sn| + 14 * E) := hAbs
    _ ≤ Pf * (|Sn| + 14 * E) := by
        apply mul_le_mul_of_nonneg_right hQbar_le_Pf
        linarith [abs_nonneg Sn, hEnn]
    _ ≤ Pf * (8 * (1 + Real.log R) + 14 * E) := by
        apply mul_le_mul_of_nonneg_left _ hPfnn
        linarith [hSabs]
    _ = (∏ i ∈ Finset.range n, (1 + oidCf lam cr x y i))
        * (8 * (1 + Real.log R) + 14 * (Real.exp (12 * cr / R) - 1)) := by
        rw [hPf, hE]

end Work.PARIMPL2.Direct
