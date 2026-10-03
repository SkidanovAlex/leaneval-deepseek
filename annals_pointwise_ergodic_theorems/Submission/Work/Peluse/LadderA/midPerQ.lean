import Mathlib
import Submission.Work.Peluse.LadderA.peel_split_pair
import Submission.Work.Peluse.LadderA.L_ge_one
import Submission.Work.Peluse.LadderA.midPerQDefs
import Submission.Work.Peluse.LadderA.avgPowLeFinset
import Submission.Work.Peluse.LadderA.perQArith
import Submission.Work.Peluse.LadderA.markovConst

namespace Work.Peluse.LadderA

open Work.Peluse Work.Peluse.UControl Work.Peluse.Ulower
open scoped BigOperators

set_option maxHeartbeats 4000000

theorem midPerQ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ) (kω : Work.Peluse.UControl.SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (D : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι k) (m : ℕ) (hm : Fintype.card (Work.Peluse.UControl.FamIdx kω) = m)
    (hs1 : 1 ≤ Fintype.card (Work.Peluse.LadderA.AIdx k kω s₀))
    (tbig : ℕ) (s' : ℕ) (hs' : 1 ≤ s') (C' A : ℝ) (hC' : 0 < C') (hA : 1 ≤ A)
    (Khc : ℕ) (hKhc : 1 ≤ Khc) (ht : s' + 1 ≤ tbig) (htm : m ≤ tbig)
    (hconc : ∀ (c : ℤ), 0 < c → ∀ (Nw M₁ M₂ : ℕ) (d : Fin (Fintype.card (Work.Peluse.LadderA.AIdx k kω s₀)) → ℤ)
        (δ δ' : ℝ) (f : ℤ → ℂ),
        1 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ Nw → (M₁ : ℝ) * (M₂ : ℝ) ≤ (Nw : ℝ) / (c : ℝ) →
        (∀ i : Fin (Fintype.card (Work.Peluse.LadderA.AIdx k kω s₀)),
            |d i| ≤ (((Fintype.card (Work.Peluse.UControl.Slot ι k)) * D + 3 : ℕ) : ℤ) * (Nw : ℤ) / (M₁ : ℤ)) →
        Work.Peluse.SupportIn f Nw → (∀ x : ℤ, ‖f x‖ ≤ 1) →
        0 < δ → δ ≤ 1 → 0 < δ' → A * δ' ≤ δ ^ Khc → A ≤ (M₂ : ℝ) * (δ * δ') ^ Khc →
        δ ≤ (((Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)).card : ℝ))⁻¹ *
              ∑ a ∈ Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ),
                Work.Peluse.boxNorm (Fintype.card (Work.Peluse.LadderA.AIdx k kω s₀))
                  (fun i : Fin (Fintype.card (Work.Peluse.LadderA.AIdx k kω s₀)) =>
                    Work.Peluse.arithIcc (c * a + d i) M₁) (Work.Peluse.symIcc Nw) f →
        C' * (δ * δ') ^ Khc ≤
          Work.Peluse.uNorm s' (Work.Peluse.arithIcc c (⌊δ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) (Work.Peluse.symIcc Nw) f)
    (Kbig : ℕ) (Cbig : ℝ) (c₁ : ℝ) (Kh : ℕ) (hKhc_le : Khc ≤ Kh)
    (hKbig : 2 ^ (m + 1) * Kh + 1 ≤ Kbig) (hCbig : A / c₁ ^ Khc ≤ Cbig) (hc₁ : 0 < c₁)
    (hCbig2 : 2 ≤ Cbig)
    (M₁ M₂ N : ℕ) (γ γ' : ℝ) (a : Fin n → ℤ) (a'' : Work.Peluse.UControl.Slot ι k → ℤ) (gt : ℤ → ℂ)
    (hM₂pos : 1 ≤ M₂) (hM₂M₁ : M₂ ≤ M₁) (hN : 1 ≤ N)
    (hM₁₂ : (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ))
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hγ'0 : 0 < γ') (hCγ' : Cbig * γ' ≤ γ ^ Kbig)
    (hnondeg : Cbig * (γ * γ') ^ (-(Kbig : ℤ)) ≤ (M₂ : ℝ))
    (hcpos : 0 < p s₀.1 a)
    (hMc : p s₀.1 a * (M₁ : ℤ) * (M₂ : ℤ) ≤ (N : ℤ))
    (hp : ∀ i : ι, |p i a| * (M₁ : ℤ) * (M₂ : ℤ) ≤ (D : ℤ) * (N : ℤ))
    (hfsupp : Work.Peluse.SupportIn gt N) (hfb : ∀ x : ℤ, ‖gt x‖ ≤ 1)
    (ha'' : a'' ∈ (Work.Peluse.UControl.paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0))
    (hδ₀ge : c₁ * γ ^ (2 ^ m) ≤
      ((γ / ((((m * (Fintype.card (Work.Peluse.UControl.Slot ι k) * D + 1) + 1 : ℕ) : ℝ) + 1)) / 2) ^ (2 ^ m) / 2))
    (hL1 : 1 ≤ γ' * (M₁ : ℝ) * (M₂ : ℝ))
    (hgood : γ / ((((m * (Fintype.card (Work.Peluse.UControl.Slot ι k) * D + 1) + 1 : ℕ) : ℝ) + 1) * 2) ≤
      (((Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)).card : ℝ))⁻¹ *
        ∑ a₀ ∈ Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ),
          Work.Peluse.boxNorm (Fintype.card (Work.Peluse.UControl.FamIdx kω))
            (fun j => Work.Peluse.UControl.pDirFam p M₁ a (Function.update a'' s₀ a₀)
              ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω)).symm j))
            (Work.Peluse.symIcc (((m * (Fintype.card (Work.Peluse.UControl.Slot ι k) * D + 1) + 1) * N))) gt)
    (b₀ : ℤ) :
    (c₁ * γ ^ (2 ^ m)) ^ (1 / (2 : ℝ) ^ (Fintype.card (Work.Peluse.UControl.ConclIdx s₀ kω tbig))) *
        ((1 : ℝ) / 2) ^ (2 ^ tbig) *
        (C') ^ ((2 : ℝ) ^ tbig / (2 : ℝ) ^ (Fintype.card (Work.Peluse.UControl.ConclIdx s₀ kω tbig))) *
        ((c₁ * γ ^ (2 ^ m)) * γ') ^
          (Khc * (2 : ℝ) ^ tbig / (2 : ℝ) ^ (Fintype.card (Work.Peluse.UControl.ConclIdx s₀ kω tbig)))
      ≤ Work.Peluse.boxNorm (Fintype.card (Work.Peluse.UControl.ConclIdx s₀ kω tbig))
          (fun j => Work.Peluse.UControl.conclDir p M₁ M₂ γ' s₀ tbig a (Function.update a'' s₀ b₀)
            ((Fintype.equivFin (Work.Peluse.UControl.ConclIdx s₀ kω tbig)).symm j)) (Work.Peluse.symIcc N) gt := by
  classical
  -- ## 0. elementary consequences of the hypotheses
  have hM₁pos : 1 ≤ M₁ := le_trans hM₂pos hM₂M₁
  have htb : 1 ≤ tbig := by omega
  have hCbigpos : (0:ℝ) < Cbig := by linarith
  have hγ'1C : γ' ≤ Cbig⁻¹ := by
    have h1 : γ' * Cbig ≤ 1 := by
      calc γ' * Cbig = Cbig * γ' := by ring
        _ ≤ γ ^ Kbig := hCγ'
        _ ≤ 1 := pow_le_one₀ (le_of_lt hγ0) hγ1
    have h2 : γ' ≤ 1 / Cbig := (le_div_iff₀ hCbigpos).mpr h1
    simpa [one_div] using h2
  have hγ'1 : γ' ≤ 1 := by
    have h : Cbig⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith : (1:ℝ) ≤ Cbig)
    linarith
  have hL1floor : 1 ≤ ⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋ := by
    rw [Int.le_floor]
    simpa using hL1
  have hM₁N : M₁ ≤ N := by
    have h : (M₁:ℝ) ≤ (N:ℝ) := by
      have h2 : (1:ℝ) ≤ (M₂:ℝ) := by exact_mod_cast hM₂pos
      nlinarith [hM₁₂]
    exact_mod_cast h
  have hNleNw : N ≤ Win k D m N := by
    unfold Win Kbv
    calc N = 1 * N := (one_mul N).symm
      _ ≤ _ := Nat.mul_le_mul_right N (by omega)
  have hM₁Nw : M₁ ≤ Win k D m N := le_trans hM₁N hNleNw
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
  have hIoo_ne : (IooV M₂).Nonempty := by
    refine ⟨0, ?_⟩
    rw [IooV, Finset.mem_Ioo]
    have h : (0:ℤ) < (M₂:ℤ) := by exact_mod_cast hM₂pos
    omega
  have hc₀pos : 0 < Cz k D m γ := by
    unfold Cz
    positivity
  have hc₀1 : Cz k D m γ ≤ 1 := by
    unfold Cz
    rw [div_le_one (by positivity)]
    have h : (0:ℝ) ≤ ((Kbv k D m : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hcz_eq : Cz k D m γ = (γ / (((Kbv k D m : ℕ) : ℝ) + 1)) / 2 := by
    unfold Cz
    rw [div_mul_eq_div_div]
  have hδ₀ge' : Dtv c₁ γ m ≤ (Cz k D m γ) ^ (2^m) / 2 := by
    rw [hcz_eq]
    exact hδ₀ge
  have hdtpos : 0 < Dtv c₁ γ m := by
    unfold Dtv
    positivity
  have hδ₀1 : Dtv c₁ γ m ≤ 1 := by
    have h : (Cz k D m γ) ^ (2^m) ≤ 1 := pow_le_one₀ (le_of_lt hc₀pos) hc₀1
    linarith
  have h2δ : 2 * Dtv c₁ γ m ≤ (Cz k D m γ) ^ (2^m) := by linarith
  -- ## 1. the shifted functions
  have hshsupp : ∀ sh : ShiftTuple k kω p M₁ a a'' s₀,
      Work.Peluse.SupportIn (shiftId k kω p M₁ a a'' s₀ sh gt) (Win k D m N) := by
    intro sh
    have h := (iterDelta_bounds k kω p a'' s₀ hm gt hfsupp hfb hM₁pos hM₂pos hM₁N hbox hp sh).1
    exact h
  have hshnorm : ∀ sh : ShiftTuple k kω p M₁ a a'' s₀, ∀ x : ℤ,
      ‖shiftId k kω p M₁ a a'' s₀ sh gt x‖ ≤ 1 := by
    intro sh
    exact (iterDelta_bounds k kω p a'' s₀ hm gt hfsupp hfb hM₁pos hM₂pos hM₁N hbox hp sh).2
  -- ## 2. the peel of the hypothesis family
  have hpeel : ∀ a₀ : ℤ,
      boxNormPow (Fintype.card (FamIdx kω))
        (fun j => pDirFam p M₁ a (Function.update a'' s₀ a₀)
          ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc (Win k D m N)) gt
      = peelWeight k kω p M₁ a a'' s₀ *
        ∑ sh : ShiftTuple k kω p M₁ a a'' s₀,
          ANorm k kω p M₁ a a'' s₀ (Win k D m N) a₀ sh gt := fun a₀ =>
    (peel_split_pair k kω p M₁ M₂ a a'' s₀ tbig γ' htb hs1 (symIcc (Win k D m N)) gt
      (FinSuppZ.of_supportIn hfsupp) a₀ b₀).1
  -- ## 3. the hypothesis, peeled and averaged (Jensen)
  have hgood1 : Cz k D m γ ≤ ((IooV M₂).card : ℝ)⁻¹ * ∑ a₀ ∈ IooV M₂,
      (peelWeight k kω p M₁ a a'' s₀ *
        ∑ sh : ShiftTuple k kω p M₁ a a'' s₀,
          ANorm k kω p M₁ a a'' s₀ (Win k D m N) a₀ sh gt) ^ (1/(2:ℝ)^m) := by
    have hgh : Cz k D m γ ≤ ((IooV M₂).card : ℝ)⁻¹ * ∑ a₀ ∈ IooV M₂,
        boxNorm (Fintype.card (FamIdx kω))
          (fun j => pDirFam p M₁ a (Function.update a'' s₀ a₀)
            ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc (Win k D m N)) gt := hgood
    have hsum : (∑ a₀ ∈ IooV M₂, boxNorm (Fintype.card (FamIdx kω))
          (fun j => pDirFam p M₁ a (Function.update a'' s₀ a₀)
            ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc (Win k D m N)) gt)
        = ∑ a₀ ∈ IooV M₂, (peelWeight k kω p M₁ a a'' s₀ *
            ∑ sh : ShiftTuple k kω p M₁ a a'' s₀,
              ANorm k kω p M₁ a a'' s₀ (Win k D m N) a₀ sh gt) ^ (1/(2:ℝ)^m) := by
      refine Finset.sum_congr rfl (fun a₀ _ => ?_)
      rw [boxNorm, hpeel a₀, hm]
    rw [hsum] at hgh
    exact hgh
  have hjensen : (Cz k D m γ) ^ (2^m) ≤ ((IooV M₂).card : ℝ)⁻¹ * ∑ a₀ ∈ IooV M₂,
      (peelWeight k kω p M₁ a a'' s₀ *
        ∑ sh : ShiftTuple k kω p M₁ a a'' s₀,
          ANorm k kω p M₁ a a'' s₀ (Win k D m N) a₀ sh gt) := by
    have hX0 : ∀ a₀ : ℤ, 0 ≤ (peelWeight k kω p M₁ a a'' s₀ *
        ∑ sh : ShiftTuple k kω p M₁ a a'' s₀,
          ANorm k kω p M₁ a a'' s₀ (Win k D m N) a₀ sh gt) ^ (1/(2:ℝ)^m) := by
      intro a₀
      exact Real.rpow_nonneg (mul_nonneg (peelWeight_nonneg k kω p M₁ a a'' s₀)
        (Finset.sum_nonneg (fun sh _ =>
          ANorm_nonneg k kω p M₁ a a'' s₀ (Win k D m N) a₀ sh gt))) _
    have hj := avgPowLeFinset (IooV M₂) (fun a₀ : ℤ => (peelWeight k kω p M₁ a a'' s₀ *
        ∑ sh : ShiftTuple k kω p M₁ a a'' s₀,
          ANorm k kω p M₁ a a'' s₀ (Win k D m N) a₀ sh gt) ^ (1/(2:ℝ)^m)) hX0 hIoo_ne
      (Nat.one_le_two_pow : 1 ≤ 2^m)
    have h1 : (Cz k D m γ) ^ (2^m) ≤ (((IooV M₂).card : ℝ)⁻¹ * ∑ a₀ ∈ IooV M₂,
        (peelWeight k kω p M₁ a a'' s₀ *
          ∑ sh : ShiftTuple k kω p M₁ a a'' s₀,
            ANorm k kω p M₁ a a'' s₀ (Win k D m N) a₀ sh gt) ^ (1/(2:ℝ)^m)) ^ (2^m) :=
      pow_le_pow_left₀ (le_of_lt hc₀pos) hgood1 _
    refine le_trans h1 (le_trans hj ?_)
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a₀ _ => ?_)) (by positivity)
    refine le_of_eq ?_
    have hnn : 0 ≤ peelWeight k kω p M₁ a a'' s₀ *
        ∑ sh : ShiftTuple k kω p M₁ a a'' s₀,
          ANorm k kω p M₁ a a'' s₀ (Win k D m N) a₀ sh gt :=
      mul_nonneg (peelWeight_nonneg k kω p M₁ a a'' s₀)
        (Finset.sum_nonneg (fun sh _ => ANorm_nonneg k kω p M₁ a a'' s₀ (Win k D m N) a₀ sh gt))
    rw [show (1 : ℝ) / (2:ℝ)^m = (((2^m : ℕ)) : ℝ)⁻¹ by
      rw [Nat.cast_pow, Nat.cast_ofNat, one_div]]
    exact Real.rpow_inv_natCast_pow hnn (by positivity)
  have hEA : 2 * Dtv c₁ γ m ≤ ((IooV M₂).card : ℝ)⁻¹ * ∑ a₀ ∈ IooV M₂,
      (peelWeight k kω p M₁ a a'' s₀ *
        ∑ sh : ShiftTuple k kω p M₁ a a'' s₀,
          ANorm k kω p M₁ a a'' s₀ (Win k D m N) a₀ sh gt) := le_trans h2δ hjensen
  -- ## 4. the per-shift line averages
  have hdsh0 : ∀ sh : ShiftTuple k kω p M₁ a a'' s₀,
      0 ≤ DSh k kω p M₁ a a'' s₀ M₂ (Win k D m N) sh gt := by
    intro sh
    unfold DSh
    refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun a₀ _ => ?_))
    unfold ABox
    exact Real.rpow_nonneg (norm_nonneg _) _
  have hdsh1 : ∀ sh : ShiftTuple k kω p M₁ a a'' s₀,
      DSh k kω p M₁ a a'' s₀ M₂ (Win k D m N) sh gt ≤ 1 := by
    intro sh
    have h1 : ∀ a₀ ∈ IooV M₂, ABox k kω p M₁ a a'' s₀ (Win k D m N) a₀ sh gt ≤ 1 := by
      intro a₀ _
      have hp1 : boxNormPow (Fintype.card (AIdx k kω s₀)) (AFam k kω p M₁ a a'' s₀ a₀)
          (symIcc (Win k D m N)) (shiftId k kω p M₁ a a'' s₀ sh gt) ≤ 1 :=
        ANorm_le_one k kω p M₁ a a'' s₀ (Win k D m N) a₀ sh gt (hshsupp sh) (hshnorm sh)
      unfold ABox
      calc (boxNormPow (Fintype.card (AIdx k kω s₀)) (AFam k kω p M₁ a a'' s₀ a₀)
              (symIcc (Win k D m N)) (shiftId k kω p M₁ a a'' s₀ sh gt)) ^
              (1 / (2:ℝ) ^ (Fintype.card (AIdx k kω s₀)))
          ≤ (1:ℝ) ^ (1 / (2:ℝ) ^ (Fintype.card (AIdx k kω s₀))) :=
            Real.rpow_le_rpow (norm_nonneg _) hp1 (by positivity)
        _ = 1 := Real.one_rpow _
    unfold DSh
    calc ((IooV M₂).card : ℝ)⁻¹ * ∑ a₀ ∈ IooV M₂,
            ABox k kω p M₁ a a'' s₀ (Win k D m N) a₀ sh gt
        ≤ ((IooV M₂).card : ℝ)⁻¹ * ∑ a₀ ∈ IooV M₂, (1:ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum h1) (by positivity)
      _ = 1 := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          exact inv_mul_cancel₀ (by
            have h := Finset.card_ne_zero.mpr hIoo_ne
            exact_mod_cast h)
  have hdsh_ge : 2 * Dtv c₁ γ m ≤ peelWeight k kω p M₁ a a'' s₀ *
      ∑ sh : ShiftTuple k kω p M₁ a a'' s₀, DSh k kω p M₁ a a'' s₀ M₂ (Win k D m N) sh gt := by
    have hstep1 : ((IooV M₂).card : ℝ)⁻¹ * ∑ a₀ ∈ IooV M₂,
        (peelWeight k kω p M₁ a a'' s₀ *
          ∑ sh : ShiftTuple k kω p M₁ a a'' s₀,
            ANorm k kω p M₁ a a'' s₀ (Win k D m N) a₀ sh gt)
        ≤ ((IooV M₂).card : ℝ)⁻¹ * ∑ a₀ ∈ IooV M₂,
        (peelWeight k kω p M₁ a a'' s₀ *
          ∑ sh : ShiftTuple k kω p M₁ a a'' s₀,
            ABox k kω p M₁ a a'' s₀ (Win k D m N) a₀ sh gt) := by
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a₀ _ => ?_)) (by positivity)
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun sh _ => ?_))
        (peelWeight_nonneg k kω p M₁ a a'' s₀)
      exact ANorm_le_ABox k kω p M₁ a a'' s₀ (Win k D m N) a₀ sh gt (hshsupp sh) (hshnorm sh)
    have hstep2 : ((IooV M₂).card : ℝ)⁻¹ * ∑ a₀ ∈ IooV M₂,
        (peelWeight k kω p M₁ a a'' s₀ *
          ∑ sh : ShiftTuple k kω p M₁ a a'' s₀,
            ABox k kω p M₁ a a'' s₀ (Win k D m N) a₀ sh gt)
        = peelWeight k kω p M₁ a a'' s₀ *
          ∑ sh : ShiftTuple k kω p M₁ a a'' s₀, DSh k kω p M₁ a a'' s₀ M₂ (Win k D m N) sh gt := by
      rw [← Finset.mul_sum]
      rw [Finset.sum_comm]
      rw [show ((IooV M₂).card : ℝ)⁻¹ * (peelWeight k kω p M₁ a a'' s₀ *
            ∑ sh : ShiftTuple k kω p M₁ a a'' s₀, ∑ a₀ ∈ IooV M₂,
              ABox k kω p M₁ a a'' s₀ (Win k D m N) a₀ sh gt)
          = peelWeight k kω p M₁ a a'' s₀ * (((IooV M₂).card : ℝ)⁻¹ *
            ∑ sh : ShiftTuple k kω p M₁ a a'' s₀, ∑ a₀ ∈ IooV M₂,
              ABox k kω p M₁ a a'' s₀ (Win k D m N) a₀ sh gt) from by ring]
      rw [Finset.mul_sum]
    linarith [hEA, hstep1, hstep2]
  -- ## 5. the good shifts (Markov)
  have hmarkov : Dtv c₁ γ m ≤ peelWeight k kω p M₁ a a'' s₀ *
      (((Finset.univ.filter (fun sh : ShiftTuple k kω p M₁ a a'' s₀ =>
        Dtv c₁ γ m ≤ DSh k kω p M₁ a a'' s₀ M₂ (Win k D m N) sh gt)).card : ℝ)) :=
    markovConst (peelWeight_nonneg k kω p M₁ a a'' s₀)
      (peelWeight_mul_card k kω p M₁ a a'' s₀ hM₁pos)
      (fun sh => DSh k kω p M₁ a a'' s₀ M₂ (Win k D m N) sh gt) hdsh0 hdsh1
      (le_of_lt hdtpos) hδ₀1 hdsh_ge
  -- ## 6. the per-shift bound (the concatenation theorem + level raising)
  have hper : ∀ sh : ShiftTuple k kω p M₁ a a'' s₀,
      Dtv c₁ γ m ≤ DSh k kω p M₁ a a'' s₀ M₂ (Win k D m N) sh gt →
      ((1:ℝ)/2)^(2^(tbig - s') - 1) * (C' * (Dtv c₁ γ m * γ')^Khc)^(2^tbig)
        ≤ LNorm k kω p M₁ a a'' s₀ tbig M₂ (Win k D m N) γ' sh gt := by
    intro sh hδsh
    exact perShBound k kω p D s₀ m hm hs1 tbig s' hs' C' A hC' hA Khc hKhc ht hconc
      Kbig Cbig c₁ Kh hKhc_le hKbig hCbig hc₁ (by linarith : (1:ℝ) ≤ Cbig)
      M₁ M₂ N γ γ' (Dtv c₁ γ m) a a'' gt hL1floor hM₂pos hM₂M₁ hM₁pos hN hM₁N hMc hp hcpos
      ha'' hfsupp hfb hγ0 hγ1 hγ'0 hγ'1C hCγ' hnondeg hdtpos hδ₀1 le_rfl sh hδsh
  -- ## 7. summing over the good shifts
  have hgoodmem : ∀ sh ∈ Finset.univ.filter (fun sh : ShiftTuple k kω p M₁ a a'' s₀ =>
        Dtv c₁ γ m ≤ DSh k kω p M₁ a a'' s₀ M₂ (Win k D m N) sh gt),
      Dtv c₁ γ m ≤ DSh k kω p M₁ a a'' s₀ M₂ (Win k D m N) sh gt :=
    fun sh hsh => (Finset.mem_filter.mp hsh).2
  have hsumgood : (((Finset.univ.filter (fun sh : ShiftTuple k kω p M₁ a a'' s₀ =>
        Dtv c₁ γ m ≤ DSh k kω p M₁ a a'' s₀ M₂ (Win k D m N) sh gt)).card : ℝ)) *
        (((1:ℝ)/2)^(2^(tbig - s') - 1) * (C' * (Dtv c₁ γ m * γ')^Khc)^(2^tbig))
      ≤ ∑ sh ∈ Finset.univ.filter (fun sh : ShiftTuple k kω p M₁ a a'' s₀ =>
        Dtv c₁ γ m ≤ DSh k kω p M₁ a a'' s₀ M₂ (Win k D m N) sh gt),
        LNorm k kω p M₁ a a'' s₀ tbig M₂ (Win k D m N) γ' sh gt := by
    have h1 : (∑ sh ∈ Finset.univ.filter (fun sh : ShiftTuple k kω p M₁ a a'' s₀ =>
          Dtv c₁ γ m ≤ DSh k kω p M₁ a a'' s₀ M₂ (Win k D m N) sh gt),
          (((1:ℝ)/2)^(2^(tbig - s') - 1) * (C' * (Dtv c₁ γ m * γ')^Khc)^(2^tbig)))
        = (((Finset.univ.filter (fun sh : ShiftTuple k kω p M₁ a a'' s₀ =>
            Dtv c₁ γ m ≤ DSh k kω p M₁ a a'' s₀ M₂ (Win k D m N) sh gt)).card : ℝ)) *
          (((1:ℝ)/2)^(2^(tbig - s') - 1) * (C' * (Dtv c₁ γ m * γ')^Khc)^(2^tbig)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [← h1]
    exact Finset.sum_le_sum (fun sh hsh => hper sh (hgoodmem sh hsh))
  have hβsum : Dtv c₁ γ m * (((1:ℝ)/2)^(2^(tbig - s') - 1) * (C' * (Dtv c₁ γ m * γ')^Khc)^(2^tbig))
      ≤ peelWeight k kω p M₁ a a'' s₀ *
        ∑ sh : ShiftTuple k kω p M₁ a a'' s₀,
          LNorm k kω p M₁ a a'' s₀ tbig M₂ (Win k D m N) γ' sh gt := by
    have hK0 : 0 ≤ ((1:ℝ)/2)^(2^(tbig - s') - 1) * (C' * (Dtv c₁ γ m * γ')^Khc)^(2^tbig) := by
      positivity
    have e4 : (∑ sh ∈ Finset.univ.filter (fun sh : ShiftTuple k kω p M₁ a a'' s₀ =>
          Dtv c₁ γ m ≤ DSh k kω p M₁ a a'' s₀ M₂ (Win k D m N) sh gt),
          LNorm k kω p M₁ a a'' s₀ tbig M₂ (Win k D m N) γ' sh gt)
        ≤ ∑ sh : ShiftTuple k kω p M₁ a a'' s₀,
          LNorm k kω p M₁ a a'' s₀ tbig M₂ (Win k D m N) γ' sh gt :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun sh _ _ => by unfold LNorm; exact norm_nonneg _)
    have e4' := mul_le_mul_of_nonneg_left e4 (peelWeight_nonneg k kω p M₁ a a'' s₀)
    calc Dtv c₁ γ m * (((1:ℝ)/2)^(2^(tbig - s') - 1) * (C' * (Dtv c₁ γ m * γ')^Khc)^(2^tbig))
        ≤ (peelWeight k kω p M₁ a a'' s₀ *
            (((Finset.univ.filter (fun sh : ShiftTuple k kω p M₁ a a'' s₀ =>
              Dtv c₁ γ m ≤ DSh k kω p M₁ a a'' s₀ M₂ (Win k D m N) sh gt)).card : ℝ))) *
            (((1:ℝ)/2)^(2^(tbig - s') - 1) * (C' * (Dtv c₁ γ m * γ')^Khc)^(2^tbig)) :=
          mul_le_mul_of_nonneg_right hmarkov hK0
      _ = peelWeight k kω p M₁ a a'' s₀ *
            ((((Finset.univ.filter (fun sh : ShiftTuple k kω p M₁ a a'' s₀ =>
              Dtv c₁ γ m ≤ DSh k kω p M₁ a a'' s₀ M₂ (Win k D m N) sh gt)).card : ℝ)) *
            (((1:ℝ)/2)^(2^(tbig - s') - 1) * (C' * (Dtv c₁ γ m * γ')^Khc)^(2^tbig))) := by ring
      _ ≤ peelWeight k kω p M₁ a a'' s₀ *
            (∑ sh ∈ Finset.univ.filter (fun sh : ShiftTuple k kω p M₁ a a'' s₀ =>
              Dtv c₁ γ m ≤ DSh k kω p M₁ a a'' s₀ M₂ (Win k D m N) sh gt),
              LNorm k kω p M₁ a a'' s₀ tbig M₂ (Win k D m N) γ' sh gt) :=
          mul_le_mul_of_nonneg_left hsumgood (peelWeight_nonneg k kω p M₁ a a'' s₀)
      _ ≤ peelWeight k kω p M₁ a a'' s₀ *
            ∑ sh : ShiftTuple k kω p M₁ a a'' s₀,
              LNorm k kω p M₁ a a'' s₀ tbig M₂ (Win k D m N) γ' sh gt := e4'
  -- ## 8. the peel of the conclusion's family
  have hconcl_peel : boxNormPow (Fintype.card (ConclIdx s₀ kω tbig))
        (fun j => conclDir p M₁ M₂ γ' s₀ tbig a (Function.update a'' s₀ b₀)
          ((Fintype.equivFin (ConclIdx s₀ kω tbig)).symm j)) (symIcc (Win k D m N)) gt
      = peelWeight k kω p M₁ a a'' s₀ *
        ∑ sh : ShiftTuple k kω p M₁ a a'' s₀,
          LNorm k kω p M₁ a a'' s₀ tbig M₂ (Win k D m N) γ' sh gt :=
    peel_concl_conj k kω p M₁ M₂ a a'' s₀ tbig γ' htb (symIcc (Win k D m N)) gt
      (FinSuppZ.of_supportIn hfsupp) b₀
  -- ## 9. the final assembly
  have hZ : Dtv c₁ γ m * ((1:ℝ)/2)^(2^(tbig - s') - 1) * (C' * (Dtv c₁ γ m * γ')^Khc)^(2^tbig)
      ≤ boxNormPow (Fintype.card (ConclIdx s₀ kω tbig))
          (fun j => conclDir p M₁ M₂ γ' s₀ tbig a (Function.update a'' s₀ b₀)
            ((Fintype.equivFin (ConclIdx s₀ kω tbig)).symm j)) (symIcc N) gt := by
    refine le_trans ?_ (boxNormPow_mono_symIcc hNleNw _)
    rw [hconcl_peel, mul_assoc]
    exact hβsum
  have hC1 : 1 ≤ Fintype.card (ConclIdx s₀ kω tbig) := by
    rw [← card_conclIdx k kω s₀ tbig]
    omega
  have hmain := perQArith (C := Fintype.card (ConclIdx s₀ kω tbig)) (tbig := tbig) (s' := s')
      hC1 ht (δ := Dtv c₁ γ m) (X := C' * (Dtv c₁ γ m * γ')^Khc)
      (Z := boxNormPow (Fintype.card (ConclIdx s₀ kω tbig))
          (fun j => conclDir p M₁ M₂ γ' s₀ tbig a (Function.update a'' s₀ b₀)
            ((Fintype.equivFin (ConclIdx s₀ kω tbig)).symm j)) (symIcc N) gt)
      (le_of_lt hdtpos) (by positivity) hZ
  have hgoal : (c₁ * γ ^ (2 ^ m)) ^ (1 / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig))) *
        ((1 : ℝ) / 2) ^ (2 ^ tbig) *
        (C') ^ ((2 : ℝ) ^ tbig / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig))) *
        ((c₁ * γ ^ (2 ^ m)) * γ') ^
          (Khc * (2 : ℝ) ^ tbig / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig)))
      = (Dtv c₁ γ m) ^ (1 / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig))) *
        ((1 : ℝ) / 2) ^ (2 ^ tbig) *
        (C' * (Dtv c₁ γ m * γ') ^ Khc) ^
          ((2 : ℝ) ^ tbig / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig))) := by
    have hAid : (C') ^ ((2 : ℝ) ^ tbig / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig))) *
        ((c₁ * γ ^ (2 ^ m)) * γ') ^
          (Khc * (2 : ℝ) ^ tbig / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig)))
        = (C' * ((c₁ * γ ^ (2 ^ m)) * γ') ^ Khc) ^
          ((2 : ℝ) ^ tbig / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig))) := by
      have hbase : (0:ℝ) ≤ (c₁ * γ ^ (2 ^ m)) * γ' := by positivity
      rw [mul_div_assoc]
      rw [Real.rpow_mul hbase (Khc:ℝ)
        ((2 : ℝ) ^ tbig / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig)))]
      rw [Real.rpow_natCast]
      rw [← Real.mul_rpow (le_of_lt hC')
        (by positivity : (0:ℝ) ≤ ((c₁ * γ ^ (2 ^ m)) * γ') ^ Khc)]
    calc (c₁ * γ ^ (2 ^ m)) ^ (1 / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig))) *
          ((1 : ℝ) / 2) ^ (2 ^ tbig) *
          (C') ^ ((2 : ℝ) ^ tbig / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig))) *
          ((c₁ * γ ^ (2 ^ m)) * γ') ^
            (Khc * (2 : ℝ) ^ tbig / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig)))
        = (c₁ * γ ^ (2 ^ m)) ^ (1 / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig))) *
          ((1 : ℝ) / 2) ^ (2 ^ tbig) *
          ((C') ^ ((2 : ℝ) ^ tbig / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig))) *
          ((c₁ * γ ^ (2 ^ m)) * γ') ^
            (Khc * (2 : ℝ) ^ tbig / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig)))) := by ring
      _ = (c₁ * γ ^ (2 ^ m)) ^ (1 / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig))) *
          ((1 : ℝ) / 2) ^ (2 ^ tbig) *
          (C' * ((c₁ * γ ^ (2 ^ m)) * γ') ^ Khc) ^
            ((2 : ℝ) ^ tbig / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig))) := by rw [hAid]
      _ = (Dtv c₁ γ m) ^ (1 / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig))) *
          ((1 : ℝ) / 2) ^ (2 ^ tbig) *
          (C' * (Dtv c₁ γ m * γ') ^ Khc) ^
            ((2 : ℝ) ^ tbig / (2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω tbig))) := rfl
  rw [hgoal, boxNorm]
  exact hmain

end Work.Peluse.LadderA
