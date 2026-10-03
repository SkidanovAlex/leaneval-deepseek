import Mathlib
import Submission.Work.Peluse.Holds.Corrected
import Submission.Work.Peluse.ExpA.petStepPerPairG
import Submission.Work.Peluse.ExpA.avgExtraction
import Submission.Work.Peluse.ExpA.markovPowMean
import Submission.Work.Peluse.ExpA.boxAvgEqPairSum
import Submission.Work.Peluse.ExpA.expCubeTsumLe

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators

namespace Work.Peluse

/-- A function supported in `[-N,N]` vanishes off `symIcc N`. -/
lemma supportIn_symIcc {f : ℤ → ℂ} {N : ℕ} (h : SupportIn f N) :
    ∀ x : ℤ, x ∉ symIcc N → f x = 0 := by
  intro x hx
  apply h
  rw [symIcc, Finset.mem_Icc] at hx
  by_cases h1 : (-(N : ℤ) ≤ x)
  · have h2 : (N : ℤ) < x := lt_of_not_ge (not_and.mp hx h1)
    rw [← Nat.cast_lt (α := ℤ), Int.natCast_natAbs, abs_of_pos (by omega)]
    exact h2
  · push_neg at h1
    rw [← Nat.cast_lt (α := ℤ), Int.natCast_natAbs, abs_of_neg (by omega)]
    omega

open Work.Peluse.ExpA
open Work.Peluse.Holds.ExpPET (expCube)

/-- **The first half of Peluse's Theorem 3.5 at the short direction scale**, in the corrected form
`C46.ExpansionPETShortA` (existential gauge constant `A`).

The proof assembles the bricks of `Work.Peluse.ExpA`:

* `Jensen` (`Holds.ExpPET.pow_le_avg_of_le_avg_rpow`): the hypothesis on the average of the box
  *norms* gives `δ^{2^s} ≤ M₂⁻¹ ∑_a ‖f‖^{2^s}_{□^s(Q(a))}`;
* `ExpA.avgExtraction`: the expansion + Fubini + nonnegativity of the box sum turns that into a
  lower bound for the *average over the label pairs* `(k,k')` of the normalised multilinear
  averages `x_p = ‖(winN·M₂)⁻¹ Λ_p‖`, namely `δ^{2^s}·|S| ≤ M₁^{-2s} ∑_p x_p/W`;
* `ExpA.markovPowMean`: on the good set `{x_p ≥ η}` (a positive proportion, by Markov, of the
  `M₁^{2s}` pairs) the power mean gives `(t/2)^{2K} ≤ (M₁^{-2s})∑_{good} x_p^{2K}`, where
  `t := δ^{2^s}|S|/W` and `η := (CL·δ')^{1/(2K)}`;
* `ExpA.petStepPerPairG`: Peluse's Lemma 4.10 (`PetLinear.linear_boxnorm_control_paper`) applied to
  each *good* pair — the existential gauge constant `A` of the statement is what makes the gauge
  `CL·δ' ≤ γ^{K}` of Lemma 4.10 hold on the good set (`δ' ≤ δ^{K}/A ≤ 1/A`, with
  `A ≥ CL·(s(C₀+1)+3)^{2K}`);
* `ExpA.boxAvgEqPairSum`: `Concat.boxAvg` is the average over the same label pairs of exactly the
  box-norm powers that Lemma 4.10 produces, with the enumeration `ωOfA`.

All losses are powers of `δ` with datum-independent constants, so the conclusion
`C·δ^K ≤ boxAvg s M₁ c (ωOfA s) ⌊δ'M₂⌋ N f` follows for `K ≥ K₀ := 2^{s+1}·KL` and
`C := min 1 (1/((s(C₀+1)+3)^{2KL}·CL^{KL}))`. -/
theorem expansionPETShortA : Work.Peluse.C46.ExpansionPETShortA := by
  intro s hs C₀
  obtain ⟨KL, hKL1, CL, hCL0, hPET⟩ := ExpA.petStepPerPairG (s := s) hs
  set lam : ℕ := s * (C₀ + 1) + 3 with hlamdef
  have hlampos : 0 < lam := by rw [hlamdef]; omega
  have hlamR : (0 : ℝ) < (lam : ℝ) := by exact_mod_cast hlampos
  set Cc : ℝ := min 1 (1 / ((lam : ℝ) ^ (2 * KL) * CL ^ KL)) with hCc
  set AA : ℝ := max 1 (CL * (lam : ℝ) ^ (2 * KL)) with hAA
  set K0 : ℕ := 2 ^ (s + 1) * KL with hK0
  have hCpos : 0 < Cc := by
    rw [hCc]
    refine lt_min one_pos ?_
    exact one_div_pos.mpr (mul_pos (pow_pos hlamR _) (pow_pos hCL0 _))
  have hCle : Cc ≤ 1 / ((lam : ℝ) ^ (2 * KL) * CL ^ KL) := by
    rw [hCc]; exact min_le_right _ _
  have hA1 : 1 ≤ AA := by rw [hAA]; exact le_max_left _ _
  have hAlam : CL * (lam : ℝ) ^ (2 * KL) ≤ AA := by rw [hAA]; exact le_max_right _ _
  have hK01 : 1 ≤ K0 := by
    rw [hK0]
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  refine ⟨Cc, hCpos, AA, hA1, K0, hK01, ?_⟩
  intro c hc K hK N M₁ M₂ b δ δ' f hM2 hM21 hN hNM hb hsup hbd hδ0 hδ1 hδ'0 hAδ' hAM hbox
  -- ## basic facts
  have hM1 : 1 ≤ M₁ := le_trans hM2 hM21
  have hfin : FinSuppZ f := FinSuppZ.of_supportIn hsup
  have hA0 : (0 : ℝ) < AA := lt_of_lt_of_le one_pos hA1
  have hδ'1 : δ' ≤ 1 := by
    have h1 : AA * δ' ≤ 1 := le_trans hAδ' (pow_le_one₀ hδ0.le hδ1)
    nlinarith [hA1, hδ'0, h1]
  have hδδ'0 : 0 < δ * δ' := mul_pos hδ0 hδ'0
  have hδδ'1 : δ * δ' ≤ 1 := by nlinarith [hδ0, hδ1, hδ'0, hδ'1]
  have hK1 : 1 ≤ K := le_trans hK01 hK
  have hM2dd : 1 ≤ (M₂ : ℝ) * (δ * δ') ^ K := le_trans hA1 hAM
  have hM2dd1 : 1 ≤ (M₂ : ℝ) * (δ * δ') := by
    have h2 : (δ * δ') ^ K ≤ (δ * δ') ^ 1 :=
      pow_le_pow_of_le_one (le_of_lt hδδ'0) hδδ'1 hK1
    have h3 : (δ * δ') ^ 1 = δ * δ' := pow_one _
    nlinarith [hM2dd, h2]
  have hδ'M2 : 1 ≤ δ' * (M₂ : ℝ) := by
    have h3 : (M₂ : ℝ) * δ' * δ = (M₂ : ℝ) * (δ * δ') := by ring
    have h4 : 1 / δ ≤ (M₂ : ℝ) * δ' := by
      rw [div_le_iff₀ hδ0]
      rw [h3]
      linarith [hM2dd1]
    have h5 : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
    linarith [h4, h5]
  -- ## the Jensen step
  have hcardIcc : (((Finset.Icc 1 M₂).card : ℕ) : ℝ) = (M₂ : ℝ) := by
    rw [Nat.card_Icc]; simp
  have h2spow : (2 : ℝ) ^ s = ((2 ^ s : ℕ) : ℝ) := by push_cast; ring
  have hJ : δ ^ (2 ^ s) ≤ ((M₂ : ℝ))⁻¹ * ∑ a ∈ Finset.Icc 1 M₂,
      boxNormPow s (fun i : Fin s => arithIcc (c * (a : ℤ) + b i) M₁) (symIcc N) f := by
    have h2s : (1 : ℝ) ≤ (2 : ℝ) ^ s := one_le_pow₀ (by norm_num)
    have hne : (Finset.Icc 1 M₂).Nonempty := ⟨1, by simp [Finset.mem_Icc, hM2]⟩
    have hmain := Holds.ExpPET.pow_le_avg_of_le_avg_rpow (s := Finset.Icc 1 M₂) hne
      (p := (2 : ℝ) ^ s) h2s (le_of_lt hδ0)
      (fun a => boxNormPow s (fun i : Fin s => arithIcc (c * (a : ℤ) + b i) M₁) (symIcc N) f)
      (fun a _ => norm_nonneg _) (by rw [hcardIcc]; exact hbox)
    rw [hcardIcc] at hmain
    rw [h2spow] at hmain
    simpa only [Real.rpow_natCast] using hmain
  -- ## the expansion + Fubini + nonnegativity step
  have hAX := ExpA.avgExtraction (s := s) (M₁ := M₁) (M₂ := M₂) hs hM1 hM2 c b (symIcc N) f hδ0 hfin hJ
  -- ## the pair index type and the extracted averages
  let P : Type := (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁}
  let Λ : P × P → ℂ := fun p => ∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
      expCube (fun i : Fin s => c * (a : ℤ) + b i) (fun i => ((p.1 i).1 : ℤ))
        (fun i => ((p.2 i).1 : ℤ)) f x
  let x : P × P → ℝ := fun p => ‖((winN s C₀ N : ℂ) * (M₂ : ℂ))⁻¹ * Λ p‖
  let t : ℝ := δ ^ (2 ^ s) * ((symIcc N).card : ℝ) / ((winN s C₀ N : ℝ))
  let η : ℝ := (CL * δ') ^ (((2 * KL : ℕ) : ℝ))⁻¹
  have hWpos : (0 : ℝ) < (winN s C₀ N : ℝ) := by
    have h : 1 ≤ winN s C₀ N := le_trans hN (le_winN s C₀ N)
    exact_mod_cast h
  have hcardP : (Finset.univ : Finset P).card = M₁ ^ s := Holds.ExpPET.card_labels s M₁
  have hcP : Fintype.card P = M₁ ^ s := by rw [← Finset.card_univ, hcardP]
  have hcardPP : (Finset.univ : Finset (P × P)).card = M₁ ^ s * M₁ ^ s := by
    rw [Finset.card_univ, Fintype.card_prod, hcP]
  have hcardPP' : (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ) = (((M₁ : ℝ) ^ s) ^ 2) := by
    rw [hcardPP]; push_cast; ring
  haveI : Nonempty (P × P) :=
    ⟨(fun _ => ⟨1, by simp [Finset.mem_Icc, hM1]⟩, fun _ => ⟨1, by simp [Finset.mem_Icc, hM1]⟩)⟩
  have hη0 : 0 ≤ η := Real.rpow_nonneg (by positivity) _
  have hηpow : η ^ (2 * KL) = CL * δ' := by
    simp only [η]
    exact Real.rpow_inv_natCast_pow (by positivity) (by omega)
  have hηpos : 0 < η := Real.rpow_pos_of_pos (by positivity) _
  -- ## x is bounded by 1
  have hx0 : ∀ p : P × P, 0 ≤ x p := fun p => norm_nonneg _
  have hx1 : ∀ p : P × P, x p ≤ 1 := by
    intro p
    have hΛ : ‖Λ p‖ ≤ (M₂ : ℝ) * ((symIcc N).card : ℝ) := by
      simp only [Λ]
      calc ‖∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ, expCube (fun i : Fin s => c * (a : ℤ) + b i)
              (fun i => ((p.1 i).1 : ℤ)) (fun i => ((p.2 i).1 : ℤ)) f x‖
          ≤ ∑ a ∈ Finset.Icc 1 M₂,
              ‖∑' x : ℤ, expCube (fun i : Fin s => c * (a : ℤ) + b i)
                (fun i => ((p.1 i).1 : ℤ)) (fun i => ((p.2 i).1 : ℤ)) f x‖ := norm_sum_le _ _
        _ ≤ ∑ _a ∈ Finset.Icc 1 M₂, ((symIcc N).card : ℝ) := by
            refine Finset.sum_le_sum fun a _ => ?_
            exact ExpA.expCubeTsumLe _ _ _ hbd (supportIn_symIcc hsup)
        _ = ((Finset.Icc 1 M₂).card : ℝ) * ((symIcc N).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = (M₂ : ℝ) * ((symIcc N).card : ℝ) := by rw [hcardIcc]
    have hxeq : x p = ((winN s C₀ N : ℝ) * (M₂ : ℝ))⁻¹ * ‖Λ p‖ := by
      simp only [x, norm_mul, norm_inv, Complex.norm_natCast]
    rw [hxeq]
    have hM2r : (0 : ℝ) < (M₂ : ℝ) := by exact_mod_cast hM2
    have h1 : ((winN s C₀ N : ℝ) * (M₂ : ℝ))⁻¹ * ‖Λ p‖
        ≤ ((winN s C₀ N : ℝ) * (M₂ : ℝ))⁻¹ * ((M₂ : ℝ) * ((symIcc N).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hΛ (by positivity)
    have h2 : ((winN s C₀ N : ℝ) * (M₂ : ℝ))⁻¹ * ((M₂ : ℝ) * ((symIcc N).card : ℝ))
        = ((symIcc N).card : ℝ) / (winN s C₀ N : ℝ) := by
      field_simp
    rw [h2] at h1
    have h3 : ((symIcc N).card : ℝ) / (winN s C₀ N : ℝ) ≤ 1 := by
      rw [div_le_one hWpos]
      exact_mod_cast card_symIcc_le_winN (s := s) (C₀ := C₀) hN
    linarith
  -- ## the lower bound for the average of x
  have hsumsplit : ∑ p : P × P, x p
      = ((winN s C₀ N : ℝ))⁻¹ * ∑ p : P × P, ‖((M₂ : ℂ))⁻¹ * Λ p‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [x, norm_mul, norm_inv, Complex.norm_natCast, mul_inv]
    ring
  have hAX' : δ ^ (2 ^ s) * ((symIcc N).card : ℝ)
      ≤ (∑ p : P × P, ‖((M₂ : ℂ))⁻¹ * Λ p‖) / (((M₁ : ℝ) ^ s) ^ 2) := by
    rw [div_eq_inv_mul]
    have h := hAX
    change δ ^ (2 ^ s) * ((symIcc N).card : ℝ)
      ≤ (((M₁ : ℝ) ^ s) ^ 2)⁻¹ * ∑ k : P, ∑ k' : P, ‖((M₂ : ℂ))⁻¹ * Λ (k, k')‖ at h
    have hp : (∑ k : P, ∑ k' : P, ‖((M₂ : ℂ))⁻¹ * Λ (k, k')‖) = ∑ p : P × P, ‖((M₂ : ℂ))⁻¹ * Λ p‖ :=
      (Fintype.sum_prod_type (fun p : P × P => ‖((M₂ : ℂ))⁻¹ * Λ p‖)).symm
    rw [hp] at h
    exact h
  have ht : t ≤ (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ * ∑ p : P × P, x p := by
    have hBpos : (0 : ℝ) < (((M₁ : ℝ) ^ s) ^ 2) := by positivity
    have hS : δ ^ (2 ^ s) * ((symIcc N).card : ℝ) * (((M₁ : ℝ) ^ s) ^ 2)
        ≤ ∑ p : P × P, ‖((M₂ : ℂ))⁻¹ * Λ p‖ := (le_div_iff₀ hBpos).mp hAX'
    have key : t * (((M₁ : ℝ) ^ s) ^ 2)
        ≤ ((winN s C₀ N : ℝ))⁻¹ * ∑ p : P × P, ‖((M₂ : ℂ))⁻¹ * Λ p‖ := by
      have h1 : (0 : ℝ) < ((winN s C₀ N : ℝ))⁻¹ := by positivity
      calc t * (((M₁ : ℝ) ^ s) ^ 2)
          = (δ ^ (2 ^ s) * ((symIcc N).card : ℝ) * (((M₁ : ℝ) ^ s) ^ 2))
              / ((winN s C₀ N : ℝ)) := by
            simp only [t]; ring
        _ ≤ (∑ p : P × P, ‖((M₂ : ℂ))⁻¹ * Λ p‖) / ((winN s C₀ N : ℝ)) :=
            div_le_div_of_nonneg_right hS (by positivity)
        _ = ((winN s C₀ N : ℝ))⁻¹ * ∑ p : P × P, ‖((M₂ : ℂ))⁻¹ * Λ p‖ := by
            rw [div_eq_inv_mul]
    rw [hcardPP', hsumsplit, ← div_eq_inv_mul]
    exact (le_div_iff₀ hBpos).mpr key
  -- ## η ≤ t/2
  have hηt : η ≤ t / 2 := by
    have hδ'le : δ' ≤ δ ^ K0 / AA := by
      have h1 : δ' ≤ δ ^ K / AA := by
        rw [le_div_iff₀ hA0, mul_comm]
        exact hAδ'
      have h2 : δ ^ K / AA ≤ δ ^ K0 / AA :=
        div_le_div_of_nonneg_right (pow_le_pow_of_le_one hδ0.le hδ1 hK) hA0.le
      linarith
    -- CL * δ' ≤ (δ ^ (2^s) / lam)^(2*KL)
    have hK0' : 2 ^ s * (2 * KL) = K0 := by rw [hK0]; ring
    have hpow : (δ ^ (2 ^ s) / (lam : ℝ)) ^ (2 * KL) = δ ^ K0 / (lam : ℝ) ^ (2 * KL) := by
      rw [div_pow, ← pow_mul, hK0']
    have hbase : CL * δ' ≤ (δ ^ (2 ^ s) / (lam : ℝ)) ^ (2 * KL) := by
      have h2 : CL * δ' ≤ CL * (δ ^ K0 / AA) :=
        mul_le_mul_of_nonneg_left hδ'le hCL0.le
      have h3 : CL * (δ ^ K0 / AA) ≤ δ ^ K0 / (lam : ℝ) ^ (2 * KL) := by
        have hcl : CL * δ ^ K0 / AA ≤ δ ^ K0 / (lam : ℝ) ^ (2 * KL) := by
          rw [div_le_div_iff₀ hA0 (by positivity)]
          nlinarith [hAlam, hCL0, pow_nonneg hδ0.le K0]
        rwa [mul_div_assoc] at hcl
      rw [hpow]
      linarith
    have hrpow : ∀ x : ℝ, 0 ≤ x → (x ^ (2 * KL)) ^ (((2 * KL : ℕ) : ℝ))⁻¹ = x := by
      intro x hx
      rw [← Real.rpow_natCast (x := x) (n := 2 * KL), ← Real.rpow_mul hx,
        mul_inv_cancel₀ (by positivity : (((2 * KL : ℕ) : ℝ)) ≠ 0), Real.rpow_one]
    have hηle : η ≤ δ ^ (2 ^ s) / (lam : ℝ) := by
      dsimp only [η]
      calc (CL * δ') ^ (((2 * KL : ℕ) : ℝ))⁻¹
          ≤ ((δ ^ (2 ^ s) / (lam : ℝ)) ^ (2 * KL)) ^ (((2 * KL : ℕ) : ℝ))⁻¹ :=
            Real.rpow_le_rpow (by positivity) hbase (by positivity)
        _ = δ ^ (2 ^ s) / (lam : ℝ) := hrpow _ (by positivity)
    have htge : δ ^ (2 ^ s) / (lam : ℝ) ≤ t / 2 := by
      have hcard : ((symIcc N).card : ℝ) = 2 * N + 1 := by
        have hcardZ : (symIcc N).card = 2 * N + 1 := by
          rw [symIcc, Int.card_Icc]
          have h1 : (N : ℤ) + 1 - (-(N : ℤ)) = (((2 * N + 1 : ℕ)) : ℤ) := by push_cast; ring
          rw [h1, Int.toNat_natCast]
        rw [hcardZ]; push_cast; ring
      have hWN : (winN s C₀ N : ℝ) = (lam : ℝ) * N := by
        rw [winN, hlamdef]; push_cast; ring
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have ht2 : t / 2 = δ ^ (2 ^ s) * (2 * N + 1) / (2 * ((lam : ℝ) * N)) := by
        dsimp only [t]
        rw [hcard, hWN]; ring
      rw [ht2, div_le_div_iff₀ hlamR (by positivity)]
      have hd : (0:ℝ) < δ ^ (2 ^ s) := pow_pos hδ0 _
      nlinarith [hNr, hd, hlamR]
    linarith
  -- ## the Markov / power-mean step
  have hMarkov := ExpA.markovPowMean (ι := P × P) (x := x) (η := η) (t := t) (p := KL)
    hKL1 hx0 hx1 hη0 hηt ht
  -- ## the per-pair PET step
  let Good : Finset (P × P) := Finset.univ.filter (fun p => η ≤ x p)
  have hGoodsub : Good ⊆ Finset.univ := Finset.filter_subset _ _
  have hpair : ∀ p ∈ Good, (x p ^ 2 / CL) ^ KL ≤ boxNormPow (2 ^ s - 1)
      (fun i : Fin (2 ^ s - 1) => arithIcc (c * dotU (ωOfA s i)
        (fun j => ((p.1 j).1 : ℤ) - ((p.2 j).1 : ℤ))) (⌊δ' * (M₂ : ℝ)⌋).toNat)
      (symIcc N) f := by
    intro p hp
    have hηp : η ≤ x p := (Finset.mem_filter.mp hp).2
    have hxpos : 0 < x p := lt_of_lt_of_le hηpos hηp
    have hγ1 : x p ^ 2 ≤ 1 := by
      calc x p ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (hx0 p) (hx1 p) 2
        _ = 1 := by norm_num
    have hgauge : CL * δ' ≤ (x p ^ 2) ^ KL := by
      have h1 : η ^ (2 * KL) ≤ (x p) ^ (2 * KL) := pow_le_pow_left₀ hηpos.le hηp _
      rw [hηpow] at h1
      have h2 : (x p ^ 2) ^ KL = (x p) ^ (2 * KL) := by rw [pow_mul]
      rw [h2]
      exact h1
    have hγ : x p ^ 2
        ≤ ‖((winN s C₀ N : ℂ) * (M₂ : ℂ))⁻¹ * Λ p‖ ^ 2 := le_of_eq rfl
    exact hPET c C₀ N M₁ M₂ b f p.1 p.2 hc hN hM1 hM2 hNM hb hsup hbd hδ'0 hδ'M2
      (pow_pos hxpos 2) hγ1 hgauge hγ
  -- ## boxAvg is the average of the pair box-norm powers
  have hboxAvg := ExpA.boxAvgEqPairSum (s := s) M₁ hM1 c (⌊δ' * (M₂ : ℝ)⌋).toNat N f
  have hboxAvg' : Concat.boxAvg s M₁ c (ωOfA s) (⌊δ' * (M₂ : ℝ)⌋).toNat N f
      = (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ *
        ∑ p : P × P, boxNormPow (2 ^ s - 1)
          (fun i : Fin (2 ^ s - 1) => arithIcc (c * dotU (ωOfA s i)
            (fun j => ((p.1 j).1 : ℤ) - ((p.2 j).1 : ℤ))) (⌊δ' * (M₂ : ℝ)⌋).toNat)
          (symIcc N) f := by
    rw [hboxAvg, hcardPP', Fintype.sum_prod_type]
  have hstep1 : (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ *
        ∑ p ∈ Good, (x p ^ 2 / CL) ^ KL
      ≤ (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ *
        ∑ p : P × P, boxNormPow (2 ^ s - 1)
          (fun i : Fin (2 ^ s - 1) => arithIcc (c * dotU (ωOfA s i)
            (fun j => ((p.1 j).1 : ℤ) - ((p.2 j).1 : ℤ))) (⌊δ' * (M₂ : ℝ)⌋).toNat)
          (symIcc N) f := by
    have hcpos : (0 : ℝ) < (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hcpos.le
    refine le_trans (Finset.sum_le_sum fun p hp => hpair p hp) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg hGoodsub (fun p _ _ => norm_nonneg _)
  have hstep2 : (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ *
        ∑ p ∈ Good, (x p ^ 2 / CL) ^ KL
      = (1 / CL ^ KL) * ((((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ *
        ∑ p ∈ Good, x p ^ (2 * KL)) := by
    have h2 : ∀ p, (x p ^ 2 / CL) ^ KL = x p ^ (2 * KL) * (1 / CL ^ KL) := by
      intro p
      rw [show (x p ^ 2 / CL) ^ KL = x p ^ (2 * KL) / CL ^ KL by rw [div_pow, ← pow_mul]]
      ring
    calc (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ * ∑ p ∈ Good, (x p ^ 2 / CL) ^ KL
        = (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ *
            ∑ p ∈ Good, x p ^ (2 * KL) * (1 / CL ^ KL) := by
          rw [Finset.sum_congr rfl (fun p _ => h2 p)]
      _ = (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ *
            ((∑ p ∈ Good, x p ^ (2 * KL)) * (1 / CL ^ KL)) := by
          rw [Finset.sum_mul]
      _ = (1 / CL ^ KL) * ((((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ *
            ∑ p ∈ Good, x p ^ (2 * KL)) := by ring
  have hstep3 : (1 / CL ^ KL) * (t ^ (2 * KL) / 2 ^ (2 * KL))
      ≤ (1 / CL ^ KL) * ((((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ *
        ∑ p ∈ Good, x p ^ (2 * KL)) := by
    have hG : (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ * ∑ p ∈ Good, x p ^ (2 * KL)
        = (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ *
          ∑ i ∈ Finset.univ.filter (fun i => η ≤ x i), (x i) ^ (2 * KL) := by
      simp only [Good]
    rw [hG]
    exact mul_le_mul_of_nonneg_left hMarkov (by positivity)
  have htlow : δ ^ (2 ^ s) * 2 / (lam : ℝ) ≤ t := by
    have hcard : ((symIcc N).card : ℝ) = 2 * N + 1 := by
      have hcardZ : (symIcc N).card = 2 * N + 1 := by
        rw [symIcc, Int.card_Icc]
        have h1 : (N : ℤ) + 1 - (-(N : ℤ)) = (((2 * N + 1 : ℕ)) : ℤ) := by push_cast; ring
        rw [h1, Int.toNat_natCast]
      rw [hcardZ]; push_cast; ring
    have hWN : (winN s C₀ N : ℝ) = (lam : ℝ) * N := by
      rw [winN, hlamdef]; push_cast; ring
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have ht2 : t = δ ^ (2 ^ s) * (2 * N + 1) / ((lam : ℝ) * N) := by
      dsimp only [t]
      rw [hcard, hWN]
    rw [ht2, div_le_div_iff₀ hlamR (by positivity)]
    have hd : (0 : ℝ) < δ ^ (2 ^ s) := pow_pos hδ0 _
    nlinarith [hNr, hd, hlamR]
  have hK0' : 2 ^ s * (2 * KL) = K0 := by rw [hK0, pow_succ]; ring
  have hstep4 : δ ^ K0 / ((lam : ℝ) ^ (2 * KL) * CL ^ KL)
      ≤ (1 / CL ^ KL) * (t ^ (2 * KL) / 2 ^ (2 * KL)) := by
    have h1 : (δ ^ (2 ^ s) * 2 / (lam : ℝ)) ^ (2 * KL) ≤ t ^ (2 * KL) :=
      pow_le_pow_left₀ (by positivity) htlow _
    have h2 : (δ ^ (2 ^ s) * 2 / (lam : ℝ)) ^ (2 * KL)
        = δ ^ K0 * 2 ^ (2 * KL) / (lam : ℝ) ^ (2 * KL) := by
      rw [div_pow, mul_pow, ← pow_mul, hK0']
    rw [h2] at h1
    have h3 : δ ^ K0 * 2 ^ (2 * KL) / (lam : ℝ) ^ (2 * KL) / 2 ^ (2 * KL)
        ≤ t ^ (2 * KL) / 2 ^ (2 * KL) :=
      div_le_div_of_nonneg_right h1 (by positivity)
    have h5 : δ ^ K0 / ((lam : ℝ) ^ (2 * KL) * CL ^ KL)
        = δ ^ K0 * 2 ^ (2 * KL) / (lam : ℝ) ^ (2 * KL) / 2 ^ (2 * KL) * (1 / CL ^ KL) := by
      field_simp
    calc δ ^ K0 / ((lam : ℝ) ^ (2 * KL) * CL ^ KL)
        = δ ^ K0 * 2 ^ (2 * KL) / (lam : ℝ) ^ (2 * KL) / 2 ^ (2 * KL) * (1 / CL ^ KL) := h5
      _ ≤ (t ^ (2 * KL) / 2 ^ (2 * KL)) * (1 / CL ^ KL) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = (1 / CL ^ KL) * (t ^ (2 * KL) / 2 ^ (2 * KL)) := by ring
    
  refine ⟨ωOfA s, ωOfA_injective s, ωOfA_ne_zero s, ?_⟩
  have hfin1 : Cc * δ ^ K ≤ δ ^ K0 / ((lam : ℝ) ^ (2 * KL) * CL ^ KL) := by
    have h1 : δ ^ K ≤ δ ^ K0 := pow_le_pow_of_le_one hδ0.le hδ1 hK
    calc Cc * δ ^ K ≤ (1 / ((lam : ℝ) ^ (2 * KL) * CL ^ KL)) * δ ^ K :=
          mul_le_mul_of_nonneg_right hCle (pow_nonneg hδ0.le K)
      _ ≤ (1 / ((lam : ℝ) ^ (2 * KL) * CL ^ KL)) * δ ^ K0 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = δ ^ K0 / ((lam : ℝ) ^ (2 * KL) * CL ^ KL) := by ring
  have hfin2 : δ ^ K0 / ((lam : ℝ) ^ (2 * KL) * CL ^ KL)
      ≤ Concat.boxAvg s M₁ c (ωOfA s) (⌊δ' * (M₂ : ℝ)⌋).toNat N f := by
    rw [hboxAvg']
    exact le_trans hstep4 (le_trans (le_trans hstep3 (le_of_eq hstep2.symm)) hstep1)
  exact le_trans hfin1 hfin2
