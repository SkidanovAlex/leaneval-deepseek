import Submission.Work.Peluse.SwapE.Defs

/-!
# `SwapE` — the assembly of the dense endgame

This module reduces the node `DenseEndgame` (`Submission/Work/Peluse/P2P3_LEAD.md` §3.6, node END)
to the named pieces of `Submission/Work/Peluse/SwapE/Defs.lean`:

* `LinearInLaw`     — the box sum is linear in the joint law of the slot values;
* `SlotDensity`     — KKL Corollary 7.2 at `ℓ = 2`: the slot law has the density of the uniform
  distribution on `[−2HM, 2HM]`, up to `K₀ = endgameK0 η H M`;
* `PboxLeOne`       — the box sum is at most one (so bad slots contribute at most `δ/2`);
* `MassAvgLeOne`    — the cube mass is at most one;
* `SlotMassLower`   — the endgame hypotheses imply `C δ / K₀^d ≤ massAvg`;
* `UniformFromMass` — the average cube mass controls a Gowers uniformity norm at window `[D]`,
  `D ≤ HM`.

The whole content of the regime factor `M/(M+H)` is the single arithmetic fact
`endgameK0 η H M ≤ 32 (M+H)/(η²M)`: the slot density is `1/K₀ ≳ η²M/(M+H)`, and the endgame's
exponent `d·e` collects the `d` slot dimensions.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapE

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap

/-! ## 1. The regime factor -/

/-- The single arithmetic input of the whole chapter: `K₀ = 24/η² + 8H/M ≤ 32(M+H)/(η²M)`. -/
theorem endgameK0_le (η : ℝ) (H M : ℕ) (hη : 0 < η) (hη1 : η ≤ 1) (hM : 1 ≤ M) :
    endgameK0 η H M ≤ 32 * ((M : ℝ) + (H : ℝ)) / (η ^ 2 * (M : ℝ)) := by
  have hη2pos : 0 < η ^ 2 := by positivity
  have hη2le1 : η ^ 2 ≤ 1 := by nlinarith
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hHnn : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  rw [endgameK0,
    show (32 : ℝ) * ((M : ℝ) + (H : ℝ)) / (η ^ 2 * (M : ℝ))
        = 32 / η ^ 2 + 32 * (H : ℝ) / (η ^ 2 * (M : ℝ)) by
      field_simp
      try ring]
  have h1 : 24 / η ^ 2 ≤ 32 / η ^ 2 := by
    rw [div_le_div_iff_of_pos_right hη2pos]; norm_num
  have h2 : 8 * (H : ℝ) / (M : ℝ) ≤ 32 * (H : ℝ) / (η ^ 2 * (M : ℝ)) := by
    rw [show 8 * (H : ℝ) / (M : ℝ) = 8 * (H : ℝ) * η ^ 2 / (η ^ 2 * (M : ℝ)) by
      field_simp
      try ring]
    rw [div_le_div_iff_of_pos_right (by positivity)]
    nlinarith [hη2le1, hHnn]
  linarith

/-! ## 2. Two elementary bounds -/

/-- The uniform average of a family bounded by `1` is at most `1`. -/
theorem avg_le_one {ι : Type} [Fintype ι] [Nonempty ι] (F : ι → ℝ) (h : ∀ i, F i ≤ 1) :
    avg F ≤ 1 := by
  have hc : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty ι›)
  have hsum : ∑ i, F i ≤ ((Fintype.card ι : ℝ)) := by
    have hle := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)
    rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hle
  have hmul := mul_le_mul_of_nonneg_left hsum
    (show (0 : ℝ) ≤ ((Fintype.card ι : ℝ))⁻¹ by positivity)
  rw [avg]
  have h3 : ((Fintype.card ι : ℝ))⁻¹ * ((Fintype.card ι : ℝ)) = 1 :=
    inv_mul_cancel₀ (ne_of_gt hc)
  rwa [h3] at hmul

/-- The arithmetic core of the endgame: the comparison of the density bound `C₁ δ/K₀^d` with the
regime factor `(δ η² M/(M+H))^d`, raised to the endgame exponent `e`. -/
theorem endgame_arith (η δ : ℝ) (H M : ℕ) (d e : ℕ) (C₁ C₂ : ℝ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : 1 ≤ M) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hd : 1 ≤ d) :
    C₂ * (C₁ / (32 : ℝ) ^ d) ^ e * (δ * η ^ 2 * (M : ℝ) / ((M : ℝ) + (H : ℝ))) ^ (d * e)
      ≤ C₂ * (C₁ * δ / (endgameK0 η H M) ^ d) ^ e := by
  set X : ℝ := δ * η ^ 2 * (M : ℝ) / ((M : ℝ) + (H : ℝ)) with hXdef
  set κ : ℝ := endgameK0 η H M with hκdef
  have hκpos : 0 < κ := by rw [hκdef]; unfold endgameK0; positivity
  have hXnn : 0 ≤ X := by rw [hXdef]; positivity
  have hδd : δ ^ d ≤ δ := by
    simpa using pow_le_pow_of_le_one hδ.le hδ1 (m := 1) (n := d) (by omega : 1 ≤ d)
  -- the key regime estimate `X κ ≤ 32 δ`
  have hXκ : X * κ ≤ 32 * δ := by
    have hκ := endgameK0_le η H M hη hη1 hM
    rw [hκdef, hXdef]
    have hXeq : δ * η ^ 2 * (M : ℝ) / ((M : ℝ) + (H : ℝ))
        = δ * (η ^ 2 * (M : ℝ) / ((M : ℝ) + (H : ℝ))) := by ring
    rw [hXeq]
    calc δ * (η ^ 2 * (M : ℝ) / ((M : ℝ) + (H : ℝ))) * endgameK0 η H M
        ≤ δ * (η ^ 2 * (M : ℝ) / ((M : ℝ) + (H : ℝ))) *
            (32 * ((M : ℝ) + (H : ℝ)) / (η ^ 2 * (M : ℝ))) := by gcongr
      _ = 32 * δ := by field_simp; try ring
  have hXκd : X ^ d * κ ^ d ≤ δ * (32 : ℝ) ^ d := by
    have h1 : (X * κ) ^ d ≤ (32 * δ) ^ d := pow_le_pow_left₀ (by positivity) hXκ d
    have h2 : (32 : ℝ) ^ d * δ ^ d ≤ (32 : ℝ) ^ d * δ :=
      mul_le_mul_of_nonneg_left hδd (by positivity)
    calc X ^ d * κ ^ d = (X * κ) ^ d := by rw [mul_pow]
      _ ≤ (32 * δ) ^ d := h1
      _ = (32 : ℝ) ^ d * δ ^ d := by rw [mul_pow]
      _ ≤ (32 : ℝ) ^ d * δ := h2
      _ = δ * (32 : ℝ) ^ d := by ring
  have hbase : C₁ * X ^ d / (32 : ℝ) ^ d ≤ C₁ * δ / κ ^ d := by
    have hκdpos : (0 : ℝ) < κ ^ d := by positivity
    have h32pos : (0 : ℝ) < (32 : ℝ) ^ d := by positivity
    rw [← sub_nonneg]
    have hsplit : C₁ * δ / κ ^ d - C₁ * X ^ d / (32 : ℝ) ^ d
        = (C₁ * δ * (32 : ℝ) ^ d - C₁ * X ^ d * κ ^ d) / ((32 : ℝ) ^ d * κ ^ d) := by
      field_simp
      try ring
    rw [hsplit]
    refine div_nonneg ?_ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hXκd hC₁.le, hC₁, hδ]
  have hpow : (C₁ / (32 : ℝ) ^ d) ^ e * X ^ (d * e) ≤ (C₁ * δ / κ ^ d) ^ e := by
    have h1 : (C₁ / (32 : ℝ) ^ d) ^ e * X ^ (d * e)
        = ((C₁ / (32 : ℝ) ^ d) * X ^ d) ^ e := by rw [pow_mul, mul_pow]
    have h2 : (C₁ / (32 : ℝ) ^ d) * X ^ d = C₁ * X ^ d / (32 : ℝ) ^ d := by ring
    rw [h1, h2]
    exact pow_le_pow_left₀ (by positivity) hbase e
  calc C₂ * (C₁ / (32 : ℝ) ^ d) ^ e * X ^ (d * e)
      = C₂ * ((C₁ / (32 : ℝ) ^ d) ^ e * X ^ (d * e)) := by ring
    _ ≤ C₂ * (C₁ * δ / κ ^ d) ^ e := mul_le_mul_of_nonneg_left hpow hC₂.le

/-! ## 3. The assembly -/

/-- **The assembly of the dense endgame**: the node `DenseEndgame` follows from the three
mathematical pieces (`LinearInLaw`, `SlotDensity`, `UniformFromMass`) and the two boundedness
bricks (`PboxLeOne`, `MassAvgLeOne`). -/
theorem denseEndgame_of_pieces
    (hP : PboxLeOne) (hMa : MassAvgLeOne)
    (hSL : SlotMassLower) (hU : UniformFromMass) : DenseEndgame := by
  intro d hd
  obtain ⟨C₁, hC₁pos, hSL'⟩ := hSL d hd
  obtain ⟨e, he1, s', hs'2, C₂, hC₂pos, hU'⟩ := hU d hd
  have hde : 1 ≤ d * e := by
    have := Nat.mul_pos (by omega : 0 < d) (by omega : 0 < e)
    omega
  refine ⟨d * e, hde, s', hs'2, C₂ * (C₁ / (32 : ℝ) ^ d) ^ e, by positivity, ?_⟩
  intro Ω _ _ q₁ q₂ G H M D N η δ f hH hM hD1 hDM hDN hf hf1 hη hη1 hδ hb hg hbad hmain
  have hmass : C₁ * δ / (endgameK0 η H M) ^ d ≤ massAvg d H M N f :=
    hSL' Ω q₁ q₂ G H M N η δ f hH hM hη hη1 hδ hf hf1 hb hg hbad hmain
  have havg : avg (fun ω : Ω => pbox d (q₁ ω) (q₂ ω) M (symIcc N) f) ≤ 1 :=
    avg_le_one _ (fun ω => hP d (q₁ ω) (q₂ ω) M N f hM hf hf1)
  have hδ1 : δ ≤ 1 := le_trans hmain havg
  have hθle1 : C₁ * δ / (endgameK0 η H M) ^ d ≤ 1 :=
    le_trans hmass (hMa d H M N f hf hf1)
  have hκpos : 0 < endgameK0 η H M := by unfold endgameK0; positivity
  have hθpos : 0 < C₁ * δ / (endgameK0 η H M) ^ d :=
    div_pos (by positivity) (pow_pos hκpos d)
  have hUres : C₂ * (C₁ * δ / (endgameK0 η H M) ^ d) ^ e
      ≤ uNorm s' (arithIcc 1 D) (symIcc N) f :=
    hU' H M D N (C₁ * δ / (endgameK0 η H M) ^ d) f
      hH hM hD1 hDM hDN hf hf1 hθpos hθle1 hmass
  exact le_trans (endgame_arith η δ H M d e C₁ C₂ hη hη1 hδ hδ1 hM hC₁pos hC₂pos hd) hUres

end

end Work.Peluse.SwapE
