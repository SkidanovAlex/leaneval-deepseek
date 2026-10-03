import Mathlib
import Submission.Work.Peluse.Prop36SW.LStateAbs
import Submission.Work.Peluse.Prop36SW.lstateStepTwo

set_option maxHeartbeats 4000000

open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

theorem lstatePeelAbs {ι : Type} [Fintype ι] [DecidableEq ι]
    (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ)
    {P : Type} [DecidableEq P] (p : ι → P → ℤ)
    (M₁ M₂ N D : ℕ) (A : Finset P) (g : P → ℤ → ℂ) (γ γ' γ'' : ℝ) (t' : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1))
    (st : Work.Peluse.Prop36SW.LStateAbs kω p M₁ M₂ N D A g γ)
    (hγ' : 0 < γ') (hγ'' : 0 < γ'') (ht' : 1 ≤ t')
    (hL : 1 ≤ (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
    (hB : 1 ≤ Fintype.card (Work.Peluse.Prop36SW.ShortIdx (k := fun _ : ι => 1) kω s₀))
    (hconcl : γ'' ≤ (A.card : ℝ)⁻¹ *
        ((Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
        ∑ a ∈ A, ∑ b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂,
          Work.Peluse.boxNorm (Fintype.card (Work.Peluse.UControl.ConclIdx s₀ kω t'))
            (fun i => Work.Peluse.Prop36SW.conclDirG p M₁ M₂ γ' s₀ t' a b
              ((Fintype.equivFin (Work.Peluse.UControl.ConclIdx s₀ kω t')).symm i))
            (Work.Peluse.symIcc N) (g a)) :
    Work.Peluse.Prop36SW.LStateAbs (Work.Peluse.Prop36SW.peelKω kω s₀)
      (Work.Peluse.Prop36SW.peelP p M₁ M₂ A γ' t' s₀) M₁ M₂
      (Work.Peluse.Prop36SW.peelN N D t' γ') D
      (Finset.univ : Finset (Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀))
      (Work.Peluse.Prop36SW.peelG p M₁ M₂ A γ' t' s₀ g)
      (min ((((Work.Peluse.symIcc N).card : ℝ) /
              ((Work.Peluse.symIcc (Work.Peluse.Prop36SW.peelN N D t' γ')).card : ℝ)) ^
              (1 / (2 : ℝ) ^ (Fintype.card (Work.Peluse.Prop36SW.ShortIdx (k := fun _ : ι => 1) kω s₀))) *
            γ'' ^ (2 ^ Fintype.card (Work.Peluse.UControl.ConclIdx s₀ kω t'))) 1) := by
  classical
  obtain ⟨hγ0, hγ1, hM2a, hM2b, hN1, hM1M2N, hp_ne, hp_le, hp_abs, hg1, hg2, hγfam⟩ := st
  have hM1 : 1 ≤ M₁ := le_trans hM2a hM2b
  have hboundAbs : ∀ a ∈ A, p s₀.1 a * (M₁ : ℤ) * (M₂ : ℤ) ≤ (N : ℤ) := by
    intro a ha
    have h := hp_le s₀.1 a ha
    have h1 : p s₀.1 a * (M₁ : ℤ) ≤ |p s₀.1 a| * (M₁ : ℤ) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    exact le_trans (mul_le_mul_of_nonneg_right h1 (by positivity)) h
  -- ## 0. preliminary facts
  have hpeelN_ge : N ≤ peelN N D t' γ' := by
    have h1 : 1 ≤ 1 + t' * ⌈γ' * (D : ℝ)⌉₊ := by omega
    rw [peelN]
    calc N = N * 1 := (mul_one N).symm
      _ ≤ N * (1 + t' * ⌈γ' * (D : ℝ)⌉₊) := Nat.mul_le_mul_left N h1
  have hpeelN1 : 1 ≤ peelN N D t' γ' := le_trans hN1 hpeelN_ge
  have hSNne : (Work.Peluse.symIcc N).Nonempty := ⟨0, by simp [Work.Peluse.symIcc]⟩
  have hSPne : (Work.Peluse.symIcc (peelN N D t' γ')).Nonempty :=
    ⟨0, by simp [Work.Peluse.symIcc]⟩
  have hcardle : (Work.Peluse.symIcc N).card
      ≤ (Work.Peluse.symIcc (peelN N D t' γ')).card := by
    apply Finset.card_le_card
    intro x hx
    simp only [Work.Peluse.symIcc, Finset.mem_Icc] at hx ⊢
    obtain ⟨h1, h2⟩ := hx
    constructor <;> omega
  have hb1ne : (paramBox (k := fun _ : ι => 1) M₂).Nonempty := by
    refine ⟨fun _ => 0, ?_⟩
    rw [paramBox, Fintype.mem_piFinset]
    intro s
    rw [Finset.mem_Ioo]
    constructor <;> omega
  have hEc_eq : Fintype.card (ConclIdx s₀ kω t')
      = t' + Fintype.card (ShortIdx (k := fun _ : ι => 1) kω s₀) := by
    show Fintype.card (Sum (Fin t')
      (Σ ω : {s : Finset (Slot ι (fun _ => 1)) // s.Nonempty ∧ s₀ ∉ s},
        Fin (kω ⟨ω.1, ω.2.1⟩))) = _
    rw [Fintype.card_sum, Fintype.card_fin]
  have hBcardF : Fintype.card (FamIdx (peelKω kω s₀))
      = Fintype.card (ShortIdx (k := fun _ : ι => 1) kω s₀) :=
    (Fintype.card_congr (peelIdxSymm kω s₀)).symm
  have hEc1 : 1 ≤ Fintype.card (ConclIdx s₀ kω t') := by rw [hEc_eq]; omega
  have hbase : 0 < ((Work.Peluse.symIcc N).card : ℝ) /
      ((Work.Peluse.symIcc (peelN N D t' γ')).card : ℝ) := by
    apply div_pos
    · exact_mod_cast Finset.card_pos.mpr hSNne
    · exact_mod_cast Finset.card_pos.mpr hSPne
  -- ## the scalars and the four sums
  let ρpow : ℝ := (((Work.Peluse.symIcc N).card : ℝ) /
      ((Work.Peluse.symIcc (peelN N D t' γ')).card : ℝ)) ^
      (1 / (2 : ℝ) ^ Fintype.card (FamIdx (peelKω kω s₀)))
  let DD : ℝ := (Fintype.card (PeelParam p M₁ M₂ A γ' t' s₀) : ℝ)⁻¹ *
      ((paramBox (k := fun _ : PeelSlot s₀ => 1) M₂).card : ℝ)⁻¹
  let CC : ℝ := (A.card : ℝ)⁻¹ * ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
      (((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℝ))⁻¹ ^ (2 * t')
  let PowSum : ℝ := ∑ q : PeelParam p M₁ M₂ A γ' t' s₀,
      ∑ a' ∈ paramBox (k := fun _ : PeelSlot s₀ => 1) M₂,
        Work.Peluse.boxNormPow (Fintype.card (FamIdx (peelKω kω s₀)))
          (peelFam kω p M₁ M₂ A γ' t' s₀ q a') (Work.Peluse.symIcc N)
          (peelG p M₁ M₂ A γ' t' s₀ g q)
  let BoxSum : ℝ := ∑ q : PeelParam p M₁ M₂ A γ' t' s₀,
      ∑ a' ∈ paramBox (k := fun _ : PeelSlot s₀ => 1) M₂,
        famNorm kω p M₁ M₂ N D A γ' t' s₀ g q a'
  let AGG : ℝ := ∑ a ∈ A, ∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
      ∑ sh : (j : Fin t') → PeelShift p M₁ M₂ γ' s₀ a × PeelShift p M₁ M₂ γ' s₀ a,
        shortPow kω p M₁ M₂ N γ' t' s₀ g a b sh
  -- ## 1. Jensen
  have hJensen : γ'' ^ (2 ^ Fintype.card (ConclIdx s₀ kω t')) ≤
      (A.card : ℝ)⁻¹ * ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
        ∑ a ∈ A, ∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
          Work.Peluse.boxNormPow (Fintype.card (ConclIdx s₀ kω t'))
            (conclFam p M₁ M₂ γ' s₀ t' kω a b) (Work.Peluse.symIcc N) (g a) := by
    have hpair : (((A ×ˢ paramBox (k := fun _ : ι => 1) M₂).card : ℝ))⁻¹ *
          ∑ pr ∈ A ×ˢ paramBox (k := fun _ : ι => 1) M₂,
            Work.Peluse.boxNorm (Fintype.card (ConclIdx s₀ kω t'))
              (fun i => conclDirG p M₁ M₂ γ' s₀ t' pr.1 pr.2
                ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i))
              (Work.Peluse.symIcc N) (g pr.1)
        = (A.card : ℝ)⁻¹ * ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
          ∑ a ∈ A, ∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
            Work.Peluse.boxNorm (Fintype.card (ConclIdx s₀ kω t'))
              (fun i => conclDirG p M₁ M₂ γ' s₀ t' a b
                ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i))
              (Work.Peluse.symIcc N) (g a) := by
      rw [Finset.sum_product, Finset.card_product, Nat.cast_mul, mul_inv_rev]
      ring
    have hpairP : (((A ×ˢ paramBox (k := fun _ : ι => 1) M₂).card : ℝ))⁻¹ *
          ∑ pr ∈ A ×ˢ paramBox (k := fun _ : ι => 1) M₂,
            Work.Peluse.boxNormPow (Fintype.card (ConclIdx s₀ kω t'))
              (fun i => conclDirG p M₁ M₂ γ' s₀ t' pr.1 pr.2
                ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i))
              (Work.Peluse.symIcc N) (g pr.1)
        = (A.card : ℝ)⁻¹ * ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
          ∑ a ∈ A, ∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
            Work.Peluse.boxNormPow (Fintype.card (ConclIdx s₀ kω t'))
              (fun i => conclDirG p M₁ M₂ γ' s₀ t' a b
                ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i))
              (Work.Peluse.symIcc N) (g a) := by
      rw [Finset.sum_product, Finset.card_product, Nat.cast_mul, mul_inv_rev]
      ring
    have hJ0 := boxNorm_average_pow_varying (t := Fintype.card (ConclIdx s₀ kω t'))
      (s := A ×ˢ paramBox (k := fun _ : ι => 1) M₂)
      (Q := fun pr : P × (Slot ι (fun _ => 1) → ℤ) => fun i => conclDirG p M₁ M₂ γ' s₀ t'
        pr.1 pr.2 ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i))
      (S := Work.Peluse.symIcc N) (F := fun pr : P × (Slot ι (fun _ => 1) → ℤ) => g pr.1)
    have hconcl' := hconcl
    rw [← hpair] at hconcl'
    have h1 := pow_le_pow_left₀ (le_of_lt hγ'') hconcl'
      (2 ^ Fintype.card (ConclIdx s₀ kω t'))
    rw [hpairP] at hJ0
    exact le_trans h1 hJ0
  -- ## 2. the peel identity, per (a, b)
  have hpeel : ∀ a ∈ A, ∀ b ∈ paramBox (k := fun _ : ι => 1) M₂,
      Work.Peluse.boxNormPow (Fintype.card (ConclIdx s₀ kω t'))
        (conclFam p M₁ M₂ γ' s₀ t' kω a b) (Work.Peluse.symIcc N) (g a)
      = (((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℝ))⁻¹ ^ (2 * t') *
        ∑ sh : (j : Fin t') → PeelShift p M₁ M₂ γ' s₀ a × PeelShift p M₁ M₂ γ' s₀ a,
          shortPow kω p M₁ M₂ N γ' t' s₀ g a b sh := by
    intro a ha b hb
    have h := conclPeelAvgShort kω p M₁ M₂ N γ' t' s₀ ht' hB hL a
      (hp_ne s₀.1 a ha) b (g a) ⟨N, hg2 a ha⟩
    exact h
  -- ## 3. assembling steps 1 and 2
  have hStep12 : γ'' ^ (2 ^ Fintype.card (ConclIdx s₀ kω t')) ≤ CC * AGG := by
    have h3a : γ'' ^ (2 ^ Fintype.card (ConclIdx s₀ kω t')) ≤
        (A.card : ℝ)⁻¹ * ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
          ∑ a ∈ A, ∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
            (((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℝ))⁻¹ ^ (2 * t') *
              ∑ sh : (j : Fin t') → PeelShift p M₁ M₂ γ' s₀ a × PeelShift p M₁ M₂ γ' s₀ a,
                shortPow kω p M₁ M₂ N γ' t' s₀ g a b sh := by
      refine le_trans hJensen (le_of_eq ?_)
      congr 1
      refine Finset.sum_congr rfl (fun a ha => ?_)
      refine Finset.sum_congr rfl (fun b hb => ?_)
      exact hpeel a ha b hb
    have hsplit : (((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℝ))⁻¹ ^ (2 * t') * AGG
        = ∑ a ∈ A, ∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
            (((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℝ))⁻¹ ^ (2 * t') *
              ∑ sh : (j : Fin t') → PeelShift p M₁ M₂ γ' s₀ a × PeelShift p M₁ M₂ γ' s₀ a,
                shortPow kω p M₁ M₂ N γ' t' s₀ g a b sh := by
      dsimp only [AGG]
      conv_lhs => rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a ha => ?_)
      conv_lhs => rw [Finset.mul_sum]
    have h3 : γ'' ^ (2 ^ Fintype.card (ConclIdx s₀ kω t')) ≤
        (A.card : ℝ)⁻¹ * ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
          ((((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℝ))⁻¹ ^ (2 * t') * AGG) := by
      rw [hsplit]
      exact h3a
    have hCC : CC * AGG = (A.card : ℝ)⁻¹ * ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
        ((((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℝ))⁻¹ ^ (2 * t') * AGG) := by
      dsimp only [CC]
      ring
    rw [hCC]
    exact h3
  -- ## 4. the middle identity between the two sums
  have hmid : DD * PowSum = CC * AGG := by
    have h := peelPowSum_eq_shortSum kω p M₁ M₂ N A γ' t' s₀ g hM2a
      (fun a ha => hp_ne s₀.1 a ha)
    exact h
  -- ## 5. the pointwise comparison at the enlarged ambient
  have hpt : ∀ (q : PeelParam p M₁ M₂ A γ' t' s₀)
      (a' : Slot (PeelSlot s₀) (fun _ => 1) → ℤ),
      (((Work.Peluse.symIcc N).card : ℝ) /
          ((Work.Peluse.symIcc (peelN N D t' γ')).card : ℝ)) ^
          (1 / (2 : ℝ) ^ Fintype.card (FamIdx (peelKω kω s₀))) *
        Work.Peluse.boxNormPow (Fintype.card (FamIdx (peelKω kω s₀)))
          (peelFam kω p M₁ M₂ A γ' t' s₀ q a') (Work.Peluse.symIcc N)
          (peelG p M₁ M₂ A γ' t' s₀ g q)
      ≤ famNorm kω p M₁ M₂ N D A γ' t' s₀ g q a' := by
    intro q a'
    have hZ : Work.Peluse.boxNormPow (Fintype.card (FamIdx (peelKω kω s₀)))
        (peelFam kω p M₁ M₂ A γ' t' s₀ q a') (Work.Peluse.symIcc N)
        (peelG p M₁ M₂ A γ' t' s₀ g q) ≤ 1 := by
      rw [famNorm_eq_famPow_peel kω p M₁ M₂ N A γ' t' s₀ g q a']
      exact boxNormPow_le_one_of_support_sub_image
        (fun x => Ulower.norm_iterDelta_le_one t'
          (fun j => (((q.2 j).1 : ℤ), ((q.2 j).2 : ℤ))) (g q.1.1.1)
          (hg1 q.1.1.1 q.1.1.2) x)
        (fun x hx => iterDelta_support_sub_image t'
          (fun j => (((q.2 j).1 : ℤ), ((q.2 j).2 : ℤ)))
          (hg2 q.1.1.1 q.1.1.2) x (by simpa only [sub_eq_add_neg] using hx))
    rw [famNorm]
    exact boxNorm_ge_ratio_mul_boxNormPow hSNne hSPne hcardle hZ
  -- ## 6. summing the pointwise comparison
  have hsumPt : ρpow * PowSum ≤ BoxSum := by
    dsimp only [PowSum, BoxSum]
    have h1 : ρpow * (∑ q : PeelParam p M₁ M₂ A γ' t' s₀,
          ∑ a' ∈ paramBox (k := fun _ : PeelSlot s₀ => 1) M₂,
            Work.Peluse.boxNormPow (Fintype.card (FamIdx (peelKω kω s₀)))
              (peelFam kω p M₁ M₂ A γ' t' s₀ q a') (Work.Peluse.symIcc N)
              (peelG p M₁ M₂ A γ' t' s₀ g q))
        = ∑ q : PeelParam p M₁ M₂ A γ' t' s₀,
          ∑ a' ∈ paramBox (k := fun _ : PeelSlot s₀ => 1) M₂,
            ρpow * Work.Peluse.boxNormPow (Fintype.card (FamIdx (peelKω kω s₀)))
              (peelFam kω p M₁ M₂ A γ' t' s₀ q a') (Work.Peluse.symIcc N)
              (peelG p M₁ M₂ A γ' t' s₀ g q) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [Finset.mul_sum]
    rw [h1]
    refine Finset.sum_le_sum (fun q _ => Finset.sum_le_sum (fun a' _ => ?_))
    exact hpt q a'
  -- ## 7. the final inequality
  have hfin : ρpow * γ'' ^ (2 ^ Fintype.card (ConclIdx s₀ kω t')) ≤ DD * BoxSum := by
    have hρnn : 0 ≤ ρpow := by dsimp only [ρpow]; exact Real.rpow_nonneg (le_of_lt hbase) _
    have hDDnn : 0 ≤ DD := by dsimp only [DD]; positivity
    calc ρpow * γ'' ^ (2 ^ Fintype.card (ConclIdx s₀ kω t'))
        ≤ ρpow * (CC * AGG) := mul_le_mul_of_nonneg_left hStep12 hρnn
      _ = ρpow * (DD * PowSum) := by rw [← hmid]
      _ = DD * (ρpow * PowSum) := by ring
      _ ≤ DD * BoxSum := mul_le_mul_of_nonneg_left hsumPt hDDnn
  have hmain : min ((((Work.Peluse.symIcc N).card : ℝ) /
          ((Work.Peluse.symIcc (peelN N D t' γ')).card : ℝ)) ^
          (1 / (2 : ℝ) ^ (Fintype.card (ShortIdx (k := fun _ : ι => 1) kω s₀))) *
        γ'' ^ (2 ^ Fintype.card (ConclIdx s₀ kω t'))) 1 ≤ DD * BoxSum := by
    refine le_trans (min_le_left _ _) ?_
    have hρ : (((Work.Peluse.symIcc N).card : ℝ) /
          ((Work.Peluse.symIcc (peelN N D t' γ')).card : ℝ)) ^
          (1 / (2 : ℝ) ^ (Fintype.card (ShortIdx (k := fun _ : ι => 1) kω s₀))) = ρpow := by
      dsimp only [ρpow]
      rw [hBcardF]
    rw [hρ]
    exact hfin
  -- ## 8. the new state
  refine ⟨?_, ?_, hM2a, hM2b, hpeelN1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_min (mul_pos (Real.rpow_pos_of_pos hbase _) (pow_pos hγ'' _)) one_pos
  · exact min_le_right _ _
  · exact le_trans hM1M2N (by exact_mod_cast hpeelN_ge)
  · intro i a _
    exact hp_ne i.1.1 a.1.1.1 a.1.1.2
  · intro i a _
    have h := hp_le i.1.1 a.1.1.1 a.1.1.2
    have h2 : (N : ℤ) ≤ (peelN N D t' γ' : ℤ) := by exact_mod_cast hpeelN_ge
    exact le_trans h h2
  · intro i a _
    have h := hp_abs i.1.1 a.1.1.1 a.1.1.2
    have h2 : (D : ℤ) * (N : ℤ) ≤ (D : ℤ) * (peelN N D t' γ' : ℤ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hpeelN_ge) (by positivity)
    exact le_trans h h2
  · intro a _ x
    exact Ulower.norm_iterDelta_le_one t' (fun j => (((a.2 j).1 : ℤ), ((a.2 j).2 : ℤ)))
      (g a.1.1.1) (hg1 a.1.1.1 a.1.1.2) x
  · intro a _
    exact supportInPeelG p M₁ M₂ N D A γ' t' s₀ g hγ'
      hboundAbs (fun a ha => hp_abs s₀.1 a ha) hg2 a
  · exact hmain


end

end Work.Peluse.Prop36SW
