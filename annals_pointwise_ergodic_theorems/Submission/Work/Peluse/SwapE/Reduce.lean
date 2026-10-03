import Submission.Work.Peluse.SwapE.Assembly

/-!
# `SwapE` — the second reduction: `MassToCube` + `WindowShrink` give `UniformFromMass`

This module closes the gap between the two finer pieces of the endgame
(`SwapE/Defs.lean`, design §3.6 steps 4–5 and step 6) and the single `UniformFromMass` piece used
by `SwapE/Assembly.lean`.

* `massToCube` (delegated) turns the average of the cube mass over the slot box into a box-norm
  power at the slot window `arithIcc 1 (4HM+1)` — a translate of `symIcc (2HM)` of the same size;
* `windowShrink` (delegated, a three-line corollary of the proved
  `Work.Peluse.Prop36SW.boxNormPow_arithIcc_shrink`) trims that window down to `arithIcc 1 D`
  because `D ≤ H*M < 4HM+1`, at the cost of a constant only;
* the root `uNorm = uNormPow^{1/2^{s'}}` (`Basic.lean`) then costs only the constant power
  `(C₂C₁)^{1/2^{s'}}`, and since `θ ≤ 1` the exponent `e/2^{s'}` may be weakened back to the
  integer exponent `e` (`Real.rpow_le_rpow_of_exponent_ge`).
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapE

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap

/-- `D ≤ massBoxCard H M` whenever `D ≤ H * M`. -/
theorem le_massBoxCard {D H M : ℕ} (h : D ≤ H * M) : D ≤ massBoxCard H M := by
  have h1 : H * M ≤ 4 * (H * M) := Nat.le_mul_of_pos_left _ (by norm_num)
  have h2 : 4 * (H * M) + 1 = massBoxCard H M := by unfold massBoxCard; ring
  omega

/-- `θ^e ≤ (θ^e)^(1/2^{s'})` for `0 < θ ≤ 1`: for a base in `(0,1]` the real power is
antitone in the exponent. -/
theorem pow_le_pow_root (θ : ℝ) (e s' : ℕ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    θ ^ e ≤ (θ ^ e) ^ (1 / (2 : ℝ) ^ s') := by
  have ha0 : (0 : ℝ) < θ ^ e := pow_pos hθ e
  have ha1 : θ ^ e ≤ 1 := pow_le_one₀ hθ.le hθ1
  have ht1 : (1 : ℝ) / (2 : ℝ) ^ s' ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ s')]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  simpa using Real.rpow_le_rpow_of_exponent_ge ha0 ha1
    (y := (1 : ℝ)) (z := (1 : ℝ) / (2 : ℝ) ^ s') ht1

/-- `#(massBox d H M) = (massBoxCard H M)^d`: the slot box has the cardinality its normalising
constant announces. -/
theorem massBox_card (d H M : ℕ) : (massBox d H M).card = (massBoxCard H M) ^ d := by
  have hfac : (Finset.Icc (-(massHalf H M)) (massHalf H M)).card = massBoxCard H M := by
    rw [Int.card_Icc]
    unfold massHalf massBoxCard
    have h : 2 * ((H * M : ℕ) : ℤ) + 1 - -(2 * ((H * M : ℕ) : ℤ))
        = ((4 * H * M + 1 : ℕ) : ℤ) := by
      push_cast; ring
    rw [h, Int.toNat_natCast]
  unfold massBox
  rw [Fintype.card_piFinset]
  simp only [hfac]
  simp

/-- Cauchy–Schwarz for a finite average: the square of the mean is at most the mean of the
squares. -/
private lemma finset_mean_sq_le {ι : Type} (s : Finset ι) (g : ι → ℝ)
    (hc : (s.card : ℝ) ≠ 0) :
    ((∑ i ∈ s, g i) / (s.card : ℝ)) ^ 2 ≤ (∑ i ∈ s, g i ^ 2) / (s.card : ℝ) := by
  have hpos : (0 : ℝ) < (s.card : ℝ) := lt_of_le_of_ne (by positivity) (Ne.symm hc)
  have hCS := sq_sum_le_card_mul_sum_sq (s := s) (f := g)
  rw [div_pow]
  have hT : (∑ i ∈ s, g i ^ 2) / (s.card : ℝ)
      = (∑ i ∈ s, g i ^ 2) * (s.card : ℝ) / (s.card : ℝ) ^ 2 := by
    field_simp
  rw [hT, div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < (s.card : ℝ) ^ 2)]
  linarith [hCS]

/-- The Cauchy–Schwarz step of the endgame: the square of the average of the cube mass is at most
the average of its square. -/
theorem massAvg_sq_le (d H M N : ℕ) (f : ℤ → ℂ) :
    (massAvg d H M N f) ^ 2 ≤ massSq d H M N f := by
  have hcard : (((massBox d H M).card : ℕ) : ℝ) = ((massBoxCard H M : ℝ)) ^ d := by
    rw [massBox_card]
    push_cast
    ring
  have hc : (((massBox d H M).card : ℕ) : ℝ) ≠ 0 := by
    have h1 : (0 : ℝ) < ((massBox d H M).card : ℝ) := by
      rw [hcard]
      have hbase : (0 : ℝ) < (massBoxCard H M : ℝ) := by unfold massBoxCard; positivity
      exact pow_pos hbase d
    exact h1.ne'
  rw [massAvg, massSq, ← hcard]
  exact finset_mean_sq_le (massBox d H M) (fun n => ‖boxMass d (symIcc N) f n‖) hc

/-- **`SqToCube` implies `MassToCube`**: the passage from the average of the cube mass to its mean
square is Cauchy–Schwarz (`massAvg_sq_le`). -/
theorem massToCube_of_sq (h : SqToCube) : MassToCube := by
  intro d hd
  obtain ⟨e, he, s', hs', C, hC, hb⟩ := h d hd
  refine ⟨2 * e, by omega, s', hs', C, hC, ?_⟩
  intro H M N θ f hH hM hf hf1 hθ hθ1 hmass
  have hsq : θ ^ 2 ≤ massSq d H M N f :=
    le_trans (pow_le_pow_left₀ hθ.le hmass 2) (massAvg_sq_le d H M N f)
  have h2 := hb H M N (θ ^ 2) f hH hM hf hf1 (by positivity) hsq
  simpa [pow_mul] using h2

/-- **The endgame reduction**: `MassToCube` (Cauchy–Schwarz/Fejér, design step 4–5) and
`WindowShrink` (the window trim, design step 6) together give `UniformFromMass`. -/
theorem uniformFromMass_of_cube (hMC : MassToCube) (hWS : WindowShrink) : UniformFromMass := by
  intro d hd
  obtain ⟨e, he, s', hs', C₁, hC₁, hcube⟩ := hMC d hd
  obtain ⟨C₂, hC₂, hshr⟩ := hWS s' hs'
  refine ⟨e, he, s', hs', (C₂ * C₁) ^ (1 / (2 : ℝ) ^ s'), by positivity, ?_⟩
  intro H M D N θ f hH hM hD1 hDM hDN hf hf1 hθ hθ1 hmass
  have hDL : D ≤ massBoxCard H M := le_massBoxCard hDM
  have hcube' : C₁ * θ ^ e
      ≤ boxNormPow s' (fun _ => arithIcc 1 (massBoxCard H M)) (symIcc N) f :=
    hcube H M N θ f hH hM hf hf1 hθ hθ1 hmass
  have hshr' : C₂ * boxNormPow s' (fun _ => arithIcc 1 (massBoxCard H M)) (symIcc N) f
      ≤ uNormPow s' (arithIcc 1 D) (symIcc N) f := hshr (massBoxCard H M) D N f hD1 hDL hf
  have h1 : (C₂ * C₁) * θ ^ e ≤ uNormPow s' (arithIcc 1 D) (symIcc N) f := by
    have h2 : C₂ * (C₁ * θ ^ e)
        ≤ C₂ * boxNormPow s' (fun _ => arithIcc 1 (massBoxCard H M)) (symIcc N) f :=
      mul_le_mul_of_nonneg_left hcube' hC₂.le
    have h3 : C₂ * (C₁ * θ ^ e) = (C₂ * C₁) * θ ^ e := by ring
    linarith [h2, hshr']
  have hroot : ((C₂ * C₁) * θ ^ e) ^ (1 / (2 : ℝ) ^ s')
      ≤ uNorm s' (arithIcc 1 D) (symIcc N) f := by
    rw [uNorm]
    exact Real.rpow_le_rpow (by positivity) h1 (by positivity)
  have hfac : (C₂ * C₁) ^ (1 / (2 : ℝ) ^ s') * θ ^ e
      ≤ ((C₂ * C₁) * θ ^ e) ^ (1 / (2 : ℝ) ^ s') := by
    have hmul : ((C₂ * C₁) * θ ^ e) ^ (1 / (2 : ℝ) ^ s')
        = (C₂ * C₁) ^ (1 / (2 : ℝ) ^ s') * (θ ^ e) ^ (1 / (2 : ℝ) ^ s') :=
      Real.mul_rpow (by positivity) (by positivity)
    rw [hmul]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_root θ e s' hθ hθ1) (by positivity)
  linarith [hroot, hfac]

/-- **The endgame from the five pieces.** -/
theorem denseEndgame_of_cube (hP : PboxLeOne) (hMa : MassAvgLeOne)
    (hSL : SlotMassLower) (hMC : MassToCube) (hWS : WindowShrink) : DenseEndgame :=
  denseEndgame_of_pieces hP hMa hSL (uniformFromMass_of_cube hMC hWS)

end

end Work.Peluse.SwapE
