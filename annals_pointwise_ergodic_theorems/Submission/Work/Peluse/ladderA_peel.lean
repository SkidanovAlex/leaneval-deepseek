import Mathlib
import Submission.Work.Peluse.LadderA.sum_paramBox_split
import Submission.Work.Peluse.LadderA.markov_density
import Submission.Work.Peluse.LadderA.boxNormPow_level_raise
import Submission.Work.Peluse.LadderA.branch1_nondegeneracy
import Submission.Work.Peluse.LadderA.branch2_impossible
import Submission.Work.Peluse.LadderA.QAfin_update_eq
import Submission.Work.Peluse.LadderA.concatFixed_symm
import Submission.Work.Peluse.LadderA.aShift_bound
import Submission.Work.Peluse.LadderA.iterDelta_bounds
import Submission.Work.Peluse.LadderA.boxNorm_symIcc_ge
import Submission.Work.Peluse.UControl.uNormPow_arithIcc_shrink_ambient

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators

namespace Work.Peluse.LadderA

noncomputable section

open Work.Peluse Work.Peluse.UControl Work.Peluse.Ulower

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The shift attached to the `i`-th direction of the `A`-part. -/
def aShift (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ)
    (a : Fin n → ℤ) (a'' : Slot ι k → ℤ) (s₀ : Slot ι k)
    (i : Fin (Fintype.card (AIdx k kω s₀))) : ℤ :=
  ∑ s ∈ (((Fintype.equivFin (AIdx k kω s₀)).symm i).1.1.1.erase s₀), p s.1 a * a'' s

/-- **The per-shift bound.**  For a good shift tuple `sh`, the conclusion's box-norm power of `f`
at the long direction is bounded below. -/
theorem perShBound (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (D : ℕ)
    (s₀ : Slot ι k) (m : ℕ) (hm : Fintype.card (FamIdx kω) = m)
    (hs1 : 1 ≤ Fintype.card (AIdx k kω s₀))
    (tbig : ℕ) (s' : ℕ) (hs' : 1 ≤ s') (C' A : ℝ) (hC' : 0 < C') (hA : 1 ≤ A)
    (Khc : ℕ) (hKhc : 1 ≤ Khc) (ht : s' + 1 ≤ tbig)
    (hconc : ∀ (c : ℤ), 0 < c → ∀ (Nw M₁ M₂ : ℕ) (d : Fin (Fintype.card (AIdx k kω s₀)) → ℤ)
        (δ δ' : ℝ) (f : ℤ → ℂ),
        1 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ Nw → (M₁ : ℝ) * (M₂ : ℝ) ≤ (Nw : ℝ) / (c : ℝ) →
        (∀ i : Fin (Fintype.card (AIdx k kω s₀)),
            |d i| ≤ (((Fintype.card (Slot ι k)) * D + 3 : ℕ) : ℤ) * (Nw : ℤ) / (M₁ : ℤ)) →
        SupportIn f Nw → (∀ x : ℤ, ‖f x‖ ≤ 1) →
        0 < δ → δ ≤ 1 → 0 < δ' → A * δ' ≤ δ ^ Khc → A ≤ (M₂ : ℝ) * (δ * δ') ^ Khc →
        δ ≤ (((Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)).card : ℝ))⁻¹ *
              ∑ a ∈ Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ),
                boxNorm (Fintype.card (AIdx k kω s₀))
                  (fun i : Fin (Fintype.card (AIdx k kω s₀)) =>
                    arithIcc (c * a + d i) M₁) (symIcc Nw) f →
        C' * (δ * δ') ^ Khc ≤
          uNorm s' (arithIcc c (⌊δ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) (symIcc Nw) f)
    (Kbig : ℕ) (Cbig : ℝ) (c₁ : ℝ) (Kh : ℕ) (hKhc_le : Khc ≤ Kh)
    (hKbig : 2 ^ (m + 1) * Kh + 1 ≤ Kbig) (hCbig : A / c₁ ^ Khc ≤ Cbig) (hc₁ : 0 < c₁)
    (hCbig1 : 1 ≤ Cbig)
    (M₁ M₂ N : ℕ) (γ γ' δ₀ : ℝ) (a : Fin n → ℤ) (a'' : Slot ι k → ℤ) (ft : ℤ → ℂ)
    (hL1 : 1 ≤ ⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋)
    (hM₂pos : 1 ≤ M₂) (hM₂M₁ : M₂ ≤ M₁) (hM₁pos : 1 ≤ M₁) (hN : 1 ≤ N) (hNM : M₁ ≤ N)
    (hMc : p s₀.1 a * (M₁ : ℤ) * (M₂ : ℤ) ≤ (N : ℤ))
    (hp : ∀ i : ι, |p i a| * (M₁ : ℤ) * (M₂ : ℤ) ≤ (D : ℤ) * (N : ℤ))
    (hcpos : 0 < p s₀.1 a)
    (ha'' : a'' ∈ (paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0))
    (hfsupp : SupportIn ft N)
    (hfb : ∀ x : ℤ, ‖ft x‖ ≤ 1)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hγ'0 : 0 < γ') (hγ'1 : γ' ≤ Cbig⁻¹)
    (hCγ' : Cbig * γ' ≤ γ ^ Kbig)
    (hnondeg : Cbig * (γ * γ') ^ (-(Kbig : ℤ)) ≤ (M₂ : ℝ))
    (hδ₀pos : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1) (hδ₀ge : c₁ * γ ^ (2 ^ m) ≤ δ₀)
    (sh : (j : Fin (Fintype.card (BIdx k kω s₀))) →
        ↥(QBfin k kω p M₁ a a'' s₀ j) × ↥(QBfin k kω p M₁ a a'' s₀ j))
    (hδ : δ₀ ≤ (((Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)).card : ℝ))⁻¹ *
        ∑ a₀ ∈ Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ),
          boxNorm (Fintype.card (AIdx k kω s₀))
            (fun i : Fin (Fintype.card (AIdx k kω s₀)) =>
              QAfin k kω p M₁ a (Function.update a'' s₀ a₀) s₀ i)
            (symIcc ((m * (Fintype.card (Slot ι k) * D + 1) + 1) * N))
            (iterDelta (Fintype.card (BIdx k kω s₀))
              (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) ft)) :
    ((1 : ℝ) / 2) ^ (2 ^ (tbig - s') - 1) *
        (C' * (δ₀ * γ') ^ Khc) ^ (2 ^ tbig)
      ≤ boxNormPow tbig (fun _ : Fin tbig =>
            arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
          (symIcc ((m * (Fintype.card (Slot ι k) * D + 1) + 1) * N))
          (iterDelta (Fintype.card (BIdx k kω s₀))
            (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) ft) := by
  -- elementary consequences of the hypotheses
  have hbox : ∀ s : Slot ι k, |a'' s| < (M₂ : ℤ) := by
    intro s
    have h1 : a'' ∈ paramBox (k := k) M₂ := (Finset.mem_filter.mp ha'').1
    have h2 : a'' s ∈ Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ) := by
      have h3 : a'' ∈ Fintype.piFinset (fun _ : Slot ι k => Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)) := by
        simpa only [paramBox] using h1
      exact (Fintype.mem_piFinset.mp h3) s
    rw [Finset.mem_Ioo] at h2
    rw [abs_lt]
    exact h2
  -- the support/behaviour of the difference function
  have hgf : SupportIn (iterDelta (Fintype.card (BIdx k kω s₀))
      (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) ft)
      ((m * (Fintype.card (Slot ι k) * D + 1) + 1) * N) := by
    simpa only using (iterDelta_bounds k kω p a'' s₀ hm ft hfsupp hfb hM₁pos hM₂pos hNM hbox hp sh).1
  have hgn : ∀ x : ℤ, ‖iterDelta (Fintype.card (BIdx k kω s₀))
      (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) ft x‖ ≤ 1 :=
    (iterDelta_bounds k kω p a'' s₀ hm ft hfsupp hfb hM₁pos hM₂pos hNM hbox hp sh).2
  -- the window `Nb` dominates `N`
  have hNle : N ≤ (m * (Fintype.card (Slot ι k) * D + 1) + 1) * N := by
    have h1 : 1 ≤ m * (Fintype.card (Slot ι k) * D + 1) + 1 := by omega
    calc N = 1 * N := (one_mul N).symm
      _ ≤ (m * (Fintype.card (Slot ι k) * D + 1) + 1) * N := Nat.mul_le_mul_right N h1
  -- the shift bound for the `A`-family
  have hshift : ∀ i : Fin (Fintype.card (AIdx k kω s₀)),
      |aShift k kω p a a'' s₀ i| ≤
        (((Fintype.card (Slot ι k)) * D + 3 : ℕ) : ℤ) *
          (((m * (Fintype.card (Slot ι k) * D + 1) + 1) * N : ℕ) : ℤ) / (M₁ : ℤ) := by
    intro i
    have hb := aShift_bound k p a'' (((Fintype.equivFin (AIdx k kω s₀)).symm i).1.1.1.erase s₀)
      (Nw := (m * (Fintype.card (Slot ι k) * D + 1) + 1) * N)
      hM₁pos hM₂pos hNM hNle (fun s _ => hbox s) hp
    simpa only [aShift] using hb
  -- the two arithmetic conditions of the concatenation theorem
  have hKc : 2 ^ m * Khc + 1 ≤ Kbig := by
    have h3 : 2 ^ m * Khc ≤ 2 ^ m * Kh := Nat.mul_le_mul_left _ hKhc_le
    have h4 : 2 ^ m * Kh ≤ 2 ^ (m + 1) * Kh := by
      have h5 : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ m)
      exact Nat.mul_le_mul_right _ h5
    omega
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  have hK₁ : 2 ^ m * Khc ≤ Kbig := Nat.le_of_succ_le hKc
  have hK₂ : Khc ≤ Kbig := by
    have h1 : Khc ≤ 2 ^ m * Khc := by
      have h2 : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
      calc Khc = 1 * Khc := (one_mul _).symm
        _ ≤ 2 ^ m * Khc := Nat.mul_le_mul_right _ h2
    exact le_trans h1 hK₁
  have hAγ' : A * γ' ≤ δ₀ ^ Khc := by
    have h1 : γ' ≤ c₁ ^ Khc * γ ^ (2 ^ m * Khc) / A :=
      branch2_impossible hγ0 hγ1 hγ'0 hCbig1 hc₁ hApos hKc hCγ' hCbig
    have h2 : A * γ' ≤ A * (c₁ ^ Khc * γ ^ (2 ^ m * Khc) / A) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hApos)
    have h3 : A * (c₁ ^ Khc * γ ^ (2 ^ m * Khc) / A) = (c₁ * γ ^ (2 ^ m)) ^ Khc := by
      field_simp
      rw [mul_pow, pow_mul]
    have h4 : (c₁ * γ ^ (2 ^ m)) ^ Khc ≤ δ₀ ^ Khc :=
      pow_le_pow_left₀ (by positivity) hδ₀ge Khc
    linarith [h3 ▸ h2]
  have hγ'1' : γ' ≤ 1 := le_trans hγ'1 (inv_le_one_of_one_le₀ hCbig1)
  have hnondeg' : Cbig ≤ (M₂ : ℝ) * (γ * γ') ^ Kbig := by
    have hx : (0 : ℝ) < (γ * γ') ^ Kbig := by positivity
    have h1 : (γ * γ') ^ (-(Kbig : ℤ)) = ((γ * γ') ^ Kbig)⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    rw [h1] at hnondeg
    calc Cbig = Cbig * ((γ * γ') ^ Kbig)⁻¹ * (γ * γ') ^ Kbig := by field_simp
      _ ≤ (M₂ : ℝ) * (γ * γ') ^ Kbig := mul_le_mul_of_nonneg_right hnondeg (le_of_lt hx)
  have hAnd : A ≤ (M₂ : ℝ) * (δ₀ * γ') ^ Khc := by
    have h1 : A ≤ (M₂ : ℝ) * (c₁ * γ ^ (2 ^ m) * γ') ^ Khc :=
      branch1_nondegeneracy hγ0 hγ1 hγ'0 hγ'1' hCbig1 hc₁ hApos hK₁ hK₂ hnondeg' hCbig
    have h2 : (c₁ * γ ^ (2 ^ m) * γ') ^ Khc ≤ (δ₀ * γ') ^ Khc :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hδ₀ge (le_of_lt hγ'0)) Khc
    have h3 : (M₂ : ℝ) * (c₁ * γ ^ (2 ^ m) * γ') ^ Khc ≤ (M₂ : ℝ) * (δ₀ * γ') ^ Khc :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  -- the identification of the `A`-family with the concatenation's family
  have hfam : ∀ a₀ : ℤ, (fun i : Fin (Fintype.card (AIdx k kω s₀)) =>
        QAfin k kω p M₁ a (Function.update a'' s₀ a₀) s₀ i)
      = fun i => arithIcc (p s₀.1 a * a₀ + aShift k kω p a a'' s₀ i) M₁ := by
    intro a₀
    funext i
    rw [QAfin_update_eq k kω p M₁ a a'' s₀ a₀ i]
    rfl
  have hM₁₂' : (M₁ : ℝ) * (M₂ : ℝ) ≤
      ((((m * (Fintype.card (Slot ι k) * D + 1) + 1) * N) : ℕ) : ℝ) / (p s₀.1 a : ℝ) := by
    have h1 : (p s₀.1 a : ℝ) * (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMc
    have h2 : (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (p s₀.1 a : ℝ) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h3 : (N : ℝ) ≤ ((((m * (Fintype.card (Slot ι k) * D + 1) + 1) * N) : ℕ) : ℝ) := by
      exact_mod_cast hNle
    calc (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (p s₀.1 a : ℝ) := h2
      _ ≤ _ := div_le_div_of_nonneg_right h3 (by positivity)
  have hδavg : δ₀ ≤ (((Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)).card : ℝ))⁻¹ *
      ∑ a₀ ∈ Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ),
        boxNorm (Fintype.card (AIdx k kω s₀))
          (fun i : Fin (Fintype.card (AIdx k kω s₀)) =>
            arithIcc (p s₀.1 a * a₀ + aShift k kω p a a'' s₀ i) M₁)
          (symIcc ((m * (Fintype.card (Slot ι k) * D + 1) + 1) * N))
          (iterDelta (Fintype.card (BIdx k kω s₀))
            (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) ft) := by
    have heq : (∑ a₀ ∈ Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ),
        boxNorm (Fintype.card (AIdx k kω s₀))
          (fun i : Fin (Fintype.card (AIdx k kω s₀)) =>
            QAfin k kω p M₁ a (Function.update a'' s₀ a₀) s₀ i)
          (symIcc ((m * (Fintype.card (Slot ι k) * D + 1) + 1) * N))
          (iterDelta (Fintype.card (BIdx k kω s₀))
            (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) ft))
        = (∑ a₀ ∈ Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ),
        boxNorm (Fintype.card (AIdx k kω s₀))
          (fun i : Fin (Fintype.card (AIdx k kω s₀)) =>
            arithIcc (p s₀.1 a * a₀ + aShift k kω p a a'' s₀ i) M₁)
          (symIcc ((m * (Fintype.card (Slot ι k) * D + 1) + 1) * N))
          (iterDelta (Fintype.card (BIdx k kω s₀))
            (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) ft)) :=
      Finset.sum_congr rfl (fun a₀ _ => by rw [hfam a₀])
    calc δ₀ ≤ (((Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)).card : ℝ))⁻¹ *
          (∑ a₀ ∈ Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ),
            boxNorm (Fintype.card (AIdx k kω s₀))
              (fun i : Fin (Fintype.card (AIdx k kω s₀)) =>
                QAfin k kω p M₁ a (Function.update a'' s₀ a₀) s₀ i)
              (symIcc ((m * (Fintype.card (Slot ι k) * D + 1) + 1) * N))
              (iterDelta (Fintype.card (BIdx k kω s₀))
                (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) ft)) := hδ
      _ = _ := by rw [heq]
  -- the concatenation theorem
  have hconcat : C' * (δ₀ * γ') ^ Khc ≤
      boxNorm s' (fun _ : Fin s' => arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
        (symIcc ((m * (Fintype.card (Slot ι k) * D + 1) + 1) * N))
        (iterDelta (Fintype.card (BIdx k kω s₀))
          (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) ft) :=
    hconc (p s₀.1 a) hcpos (((m * (Fintype.card (Slot ι k) * D + 1) + 1) * N)) M₁ M₂
      (aShift k kω p a a'' s₀) δ₀ γ'
      (iterDelta (Fintype.card (BIdx k kω s₀))
        (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) ft)
      hM₂pos hM₂M₁ (by omega) hM₁₂' hshift hgf hgn hδ₀pos hδ₀1 hγ'0 hAγ' hAnd hδavg
  -- raise the box-norm power
  have hpow : (C' * (δ₀ * γ') ^ Khc) ^ (2 ^ s') ≤
      boxNormPow s' (fun _ : Fin s' => arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
        (symIcc ((m * (Fintype.card (Slot ι k) * D + 1) + 1) * N))
        (iterDelta (Fintype.card (BIdx k kω s₀))
          (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) ft) := by
    have h1 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ C' * (δ₀ * γ') ^ Khc) hconcat (2 ^ s')
    rwa [BoxNorm.boxNorm_pow] at h1
  -- the level raising
  have hLpos : 1 ≤ (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat := by omega
  have hne : ∀ i : Fin s', ((fun _ : Fin s' => arithIcc (p s₀.1 a)
      (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) i).Nonempty := by
    intro i
    exact ⟨p s₀.1 a * 1, Finset.mem_image.mpr ⟨1, by simp [hLpos], by ring⟩⟩
  have hne2 : ∀ i : Fin (tbig - s'), ((fun _ : Fin (tbig - s') => arithIcc (p s₀.1 a)
      (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) i).Nonempty := by
    intro i
    exact ⟨p s₀.1 a * 1, Finset.mem_image.mpr ⟨1, by simp [hLpos], by ring⟩⟩
  have hconst : (Fin.append (fun _ : Fin s' => arithIcc (p s₀.1 a)
        (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
      (fun _ : Fin (tbig - s') => arithIcc (p s₀.1 a)
        (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat))
      = fun _ : Fin (s' + (tbig - s')) => arithIcc (p s₀.1 a)
        (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat := by
    funext i
    refine Fin.addCases
      (motive := fun i : Fin (s' + (tbig - s')) => Fin.append _ _ i = _) (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
    · rw [Fin.append_right]
  have hbnd : ∀ i : Fin (s' + (tbig - s')), ∀ z : ℤ,
      z ∈ Fin.append (fun _ : Fin s' => arithIcc (p s₀.1 a)
          (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
        (fun _ : Fin (tbig - s') => arithIcc (p s₀.1 a)
          (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) i →
      |z| ≤ (((m * (Fintype.card (Slot ι k) * D + 1) + 1) * N : ℕ) : ℤ) := by
    intro i z hz
    rw [hconst] at hz
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
    rw [Finset.mem_Icc] at hn
    have hcz : (0:ℤ) < p s₀.1 a := hcpos
    have hLle : ((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℤ) ≤ ⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋ := by
      rw [Int.toNat_of_nonneg (Int.floor_nonneg.mpr (by positivity))]
    have hfl : (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋ : ℝ) ≤ γ' * (M₁ : ℝ) * (M₂ : ℝ) := Int.floor_le _
    have hstep : (n : ℤ) * p s₀.1 a ≤ (M₁ : ℤ) * (M₂ : ℤ) * p s₀.1 a := by
      have h1 : (n : ℤ) ≤ ((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℤ) := by exact_mod_cast hn.2
      have h2 : ((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℝ) ≤ γ' * (M₁ : ℝ) * (M₂ : ℝ) :=
        le_trans (by exact_mod_cast hLle) hfl
      have h3 : (n : ℝ) ≤ γ' * (M₁ : ℝ) * (M₂ : ℝ) := le_trans (by exact_mod_cast h1) h2
      have h4 : (n : ℝ) * (p s₀.1 a : ℝ) ≤ γ' * (M₁ : ℝ) * (M₂ : ℝ) * (p s₀.1 a : ℝ) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
      have h5 : γ' * (M₁ : ℝ) * (M₂ : ℝ) * (p s₀.1 a : ℝ) ≤ (M₁ : ℝ) * (M₂ : ℝ) * (p s₀.1 a : ℝ) := by
        have : γ' * ((M₁ : ℝ) * (M₂ : ℝ) * (p s₀.1 a : ℝ)) ≤ 1 * ((M₁:ℝ) * (M₂:ℝ) * (p s₀.1 a : ℝ)) :=
          mul_le_mul_of_nonneg_right hγ'1' (by positivity)
        linarith
      have h6 : (n : ℝ) * (p s₀.1 a : ℝ) ≤ (M₁ : ℝ) * (M₂ : ℝ) * (p s₀.1 a : ℝ) := le_trans h4 h5
      exact_mod_cast h6
    have h7 : (M₁ : ℤ) * (M₂ : ℤ) * p s₀.1 a ≤ (N : ℤ) := by
      have := hMc
      linarith [mul_comm (p s₀.1 a) (M₁ : ℤ)]
    have h8 : (n : ℤ) * p s₀.1 a ≤ (N : ℤ) := le_trans hstep h7
    have h9 : |(n : ℤ) * p s₀.1 a| ≤ (N : ℤ) := by
      rw [abs_of_nonneg (by positivity)]
      exact h8
    have h10 : (N : ℤ) ≤ (((m * (Fintype.card (Slot ι k) * D + 1) + 1) * N : ℕ) : ℤ) := by
      exact_mod_cast hNle
    rw [mul_comm]
    exact le_trans h9 h10
  -- the level raising
  have hlr := boxNormPow_level_raise (a := s') (b := tbig - s') (by omega) (by omega)
    (fun _ : Fin s' => arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
    (fun _ : Fin (tbig - s') => arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
    (iterDelta (Fintype.card (BIdx k kω s₀)) (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) ft)
    hne hne2 hbnd hgf hgn
  -- combine with the power bound
  have hcomb : ((1 : ℝ) / 2) ^ (2 ^ (tbig - s') - 1) *
        (C' * (δ₀ * γ') ^ Khc) ^ (2 ^ tbig) ≤
      boxNormPow (s' + (tbig - s'))
        (Fin.append (fun _ : Fin s' => arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
          (fun _ : Fin (tbig - s') => arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat))
        (symIcc ((m * (Fintype.card (Slot ι k) * D + 1) + 1) * N))
        (iterDelta (Fintype.card (BIdx k kω s₀)) (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) ft) := by
    have hexp : (2:ℕ) ^ tbig = 2 ^ s' * 2 ^ (tbig - s') := by
      rw [← pow_add, Nat.add_sub_cancel' (by omega)]
    have hpoweq : (C' * (δ₀ * γ') ^ Khc) ^ (2 ^ tbig) =
        ((C' * (δ₀ * γ') ^ Khc) ^ (2 ^ s')) ^ (2 ^ (tbig - s')) := by
      calc (C' * (δ₀ * γ') ^ Khc) ^ (2 ^ tbig)
          = (C' * (δ₀ * γ') ^ Khc) ^ (2 ^ s' * 2 ^ (tbig - s')) := by rw [hexp]
        _ = ((C' * (δ₀ * γ') ^ Khc) ^ (2 ^ s')) ^ (2 ^ (tbig - s')) :=
            (pow_mul _ (2 ^ s') (2 ^ (tbig - s')))
    rw [hpoweq]
    exact le_trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hpow (2 ^ (tbig - s'))) (by positivity)) hlr
  -- reindex to level `tbig`
  have hcast := Concat.boxNormPow_cast (Nat.add_sub_cancel' (by omega) :
    s' + (tbig - s') = tbig)
    (Fin.append (fun _ : Fin s' => arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
      (fun _ : Fin (tbig - s') => arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat))
    (symIcc ((m * (Fintype.card (Slot ι k) * D + 1) + 1) * N))
    (iterDelta (Fintype.card (BIdx k kω s₀)) (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) ft)
  rw [hcast] at hcomb
  have hfinal : (fun j : Fin tbig => Fin.append
      (fun _ : Fin s' => arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
      (fun _ : Fin (tbig - s') => arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
      (Fin.cast (Nat.add_sub_cancel' (by omega) : s' + (tbig - s') = tbig).symm j))
      = fun _ : Fin tbig => arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat := by
    funext j
    simp only [hconst]
  rw [show (fun _ : Fin tbig => arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
      = (fun j : Fin tbig => Fin.append
          (fun _ : Fin s' => arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
          (fun _ : Fin (tbig - s') => arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
          (Fin.cast (Nat.add_sub_cancel' (by omega) : s' + (tbig - s') = tbig).symm j))
      from hfinal.symm]
  exact hcomb




end
end Work.Peluse.LadderA
