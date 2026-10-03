import Mathlib
import Submission.Work.Peluse.Holds.SwapDefs
import Submission.Work.Peluse.ExpA.petStepPerPairG
import Submission.Work.Peluse.ExpA.avgExtraction
import Submission.Work.Peluse.ExpA.markovPowMean
import Submission.Work.Peluse.ExpA.boxAvgEqPairSum
import Submission.Work.Peluse.ExpA.expCubeTsumLe

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace Work.Peluse.SwapA

noncomputable section

open Work.Peluse

/-! ## Auxiliary: support and the relabelling of the sign patterns -/

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

/-- Every everywhere-nonzero injection `Fin (2^t - 1) → (Fin t → Bool)` enumerates the nonzero
sign patterns, so it differs from the canonical enumeration `Holds.omegaOf t` by a permutation of
the index set. -/
lemma exists_perm_comp_of_injective {t : ℕ} (ω₁ ω₂ : Fin (2 ^ t - 1) → (Fin t → Bool))
    (h₁ : Function.Injective ω₁) (n₁ : ∀ i, ω₁ i ≠ 0)
    (h₂ : Function.Injective ω₂) (n₂ : ∀ i, ω₂ i ≠ 0) :
    ∃ σ : Fin (2 ^ t - 1) ≃ Fin (2 ^ t - 1), ∀ i, ω₁ i = ω₂ (σ i) := by
  classical
  have hcard : (Finset.univ.image ω₂).card = 2 ^ t - 1 := by
    rw [Finset.card_image_of_injective _ h₂, Finset.card_univ, Fintype.card_fin]
  have himg : Finset.univ.image ω₂ = Finset.univ.erase (0 : Fin t → Bool) := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · rw [Finset.mem_image] at hx
      obtain ⟨i, -, rfl⟩ := hx
      exact Finset.mem_erase.mpr ⟨n₂ i, Finset.mem_univ _⟩
    · rw [hcard, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hmem : ∀ i, ω₁ i ∈ Finset.univ.image ω₂ := by
    intro i
    rw [himg]
    exact Finset.mem_erase.mpr ⟨n₁ i, Finset.mem_univ _⟩
  let σ : Fin (2 ^ t - 1) → Fin (2 ^ t - 1) := fun i => (Finset.mem_image.mp (hmem i)).choose
  have hσ : ∀ i, ω₂ (σ i) = ω₁ i := fun i => (Finset.mem_image.mp (hmem i)).choose_spec.2
  have hinj : Function.Injective σ := by
    intro i j hij
    refine h₁ ?_
    rw [← hσ i, ← hσ j, hij]
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.mp hinj
  refine ⟨Equiv.ofBijective σ hbij, fun i => ?_⟩
  rw [Equiv.ofBijective_apply, ← hσ i]

/-- The box-sum power is unchanged when the nonzero sign patterns are relabelled by another
everywhere-nonzero injection. -/
lemma boxSumPow_relabel {t : ℕ} (ωOf : Fin (2 ^ t - 1) → (Fin t → Bool))
    (hω : Function.Injective ωOf) (hω0 : ∀ i, ωOf i ≠ 0)
    (g : (Fin t → Bool) → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    boxSumPow (2 ^ t - 1) (fun i => g (ωOf i)) S f
      = boxSumPow (2 ^ t - 1) (fun i => g (Holds.omegaOf t i)) S f := by
  obtain ⟨σ, hσ⟩ := exists_perm_comp_of_injective ωOf (Holds.omegaOf t) hω hω0
    (Holds.omegaOf_injective t) (Holds.omegaOf_ne_zero t)
  have hfun : (fun i => g (ωOf i))
      = (fun i => (fun j => g (Holds.omegaOf t j)) (σ i)) := by
    funext i
    rw [hσ i]
  rw [hfun]
  exact Track.boxSumPow_comp_bij_proved (fun j => g (Holds.omegaOf t j)) S f σ σ.bijective

/-- The box-norm power is unchanged when the nonzero sign patterns are relabelled. -/
lemma boxNormPow_relabel {t : ℕ} (ωOf : Fin (2 ^ t - 1) → (Fin t → Bool))
    (hω : Function.Injective ωOf) (hω0 : ∀ i, ωOf i ≠ 0)
    (g : (Fin t → Bool) → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    boxNormPow (2 ^ t - 1) (fun i => g (ωOf i)) S f
      = boxNormPow (2 ^ t - 1) (fun i => g (Holds.omegaOf t i)) S f := by
  rw [boxNormPow, boxNormPow, boxSumPow_relabel ωOf hω hω0 g S f]

/-- The dense average of the regime swap is the concatenation average along the enumeration
`ExpA.ωOfA` of the nonzero sign patterns. -/
lemma boxAvg_omegaOfA_eq_denseAvg (t M D N : ℕ) (f : ℤ → ℂ) :
    Concat.boxAvg t M 1 (ExpA.ωOfA t) D N f = LadderP.Swap.denseAvg t M D (symIcc N) f := by
  rw [Concat.boxAvg, LadderP.Swap.denseAvg]
  congr 1
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => ?_
  simp only [one_mul]
  refine boxNormPow_relabel (ExpA.ωOfA t) (ExpA.ωOfA_injective t) (ExpA.ωOfA_ne_zero t)
    (fun ω => arithIcc (Concat.dotZ ω (Concat.tupSub h h')) D) (symIcc N) f

/-- **(R) Regime swap.** The sparse level-`t` average (slopes `a+bᵢ`, `a ∈ [M₁]`, windows `[M₂]`) controls the dense average with slopes `ω·(h−h')` (`h,h' ∈ [M₂]^t`) and windows `[M']`, `M' ≥ Cγ^K M₁`. Proof: expand, shift `x`, and apply the PROVED linear generalized von Neumann `PetLinear.linear_boxnorm_control_paper` to the pattern `x + a·(ω·u)` (`ω ∈ {0,1}^t`) for each `u = h − h'`; Hölder over `u`. -/
theorem sparseToDense : ∀ t : ℕ, 1 ≤ t → ∀ B₀ : ℕ, ∃ K : ℕ, 1 ≤ K ∧
    ∃ C : ℝ, 0 < C ∧ C ≤ 1 ∧
    ∀ (M₁ M₂ N : ℕ) (b : Fin t → ℤ) (γ : ℝ) (f : ℤ → ℂ),
      1 ≤ M₂ → M₂ ≤ M₁ → (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) →
      Work.Peluse.SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
      (∀ i : Fin t, |b i| ≤ (B₀ : ℤ) * (M₁ : ℤ)) →
      0 < γ → γ ≤ 1 → 1 ≤ C * γ ^ K * (M₁ : ℝ) →
      γ ≤ Work.Peluse.LadderP.p3BoxAvg t M₁ M₂ b (Work.Peluse.symIcc N) f →
      ∃ M' : ℕ, 1 ≤ M' ∧ M' ≤ M₁ ∧ C * γ ^ K * (M₁ : ℝ) ≤ (M' : ℝ) ∧
        C * γ ^ K ≤ Work.Peluse.LadderP.Swap.denseAvg t M₂ M' (Work.Peluse.symIcc N) f := by
  intro t ht B₀
  -- ## the constants of the per-pair PET step
  obtain ⟨KL, hKL1, CL, hCL0, hPET⟩ := ExpA.petStepPerPairG (s := t) ht
  set lam : ℕ := t * (B₀ + 1) + 3 with hlamdef
  have hlampos : 0 < lam := by rw [hlamdef]; omega
  have hlamR : (0 : ℝ) < (lam : ℝ) := by exact_mod_cast hlampos
  set AA : ℝ := max 1 (CL * (lam : ℝ) ^ (2 * KL)) with hAA
  have hA1 : 1 ≤ AA := by rw [hAA]; exact le_max_left _ _
  have hAA0 : 0 < AA := lt_of_lt_of_le one_pos hA1
  have hAlam : CL * (lam : ℝ) ^ (2 * KL) ≤ AA := by rw [hAA]; exact le_max_right _ _
  set K : ℕ := 2 ^ (t + 1) * KL with hKdef
  have hK1 : 1 ≤ K := by
    rw [hKdef]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) (by omega))
  set Cc : ℝ := min (1 / 2) (min (1 / (2 * AA)) (1 / ((lam : ℝ) ^ (2 * KL) * CL ^ KL)))
    with hCc
  have hCcpos : 0 < Cc := by
    rw [hCc]
    exact lt_min (by norm_num) (lt_min (div_pos one_pos (by positivity))
      (div_pos one_pos (by positivity)))
  have hCcle1 : Cc ≤ 1 := by
    rw [hCc]
    exact le_trans (min_le_left _ _) (by norm_num)
  have hCcAA : Cc ≤ 1 / (2 * AA) := by
    rw [hCc]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hCcCL : Cc ≤ 1 / ((lam : ℝ) ^ (2 * KL) * CL ^ KL) := by
    rw [hCc]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨K, hK1, Cc, hCcpos, hCcle1, ?_⟩
  intro M₁ M₂ N b γ f hM2 hM21 hNM hsup hbd hb hγ0 hγ1 hCM hbox
  -- ## elementary facts
  have hM1 : 1 ≤ M₁ := le_trans hM2 hM21
  have hfin : FinSuppZ f := FinSuppZ.of_supportIn hsup
  have hN : 1 ≤ N := by
    have h1r : (1 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hM1
    have h2r : (1 : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast hM2
    have h : (1 : ℝ) ≤ (M₁ : ℝ) * (M₂ : ℝ) := by
      have := mul_le_mul h1r h2r (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ (M₁:ℝ))
      simpa using this
    have h3 : (1 : ℝ) ≤ (N : ℝ) := le_trans h hNM
    exact_mod_cast h3
  have hcardS : ((symIcc N).card : ℝ) = 2 * (N : ℝ) + 1 := by
    have hcardZ : (symIcc N).card = 2 * N + 1 := by
      rw [symIcc, Int.card_Icc]
      have h1 : (N : ℤ) + 1 - (-(N : ℤ)) = (((2 * N + 1 : ℕ)) : ℤ) := by push_cast; ring
      rw [h1, Int.toNat_natCast]
    rw [hcardZ]; push_cast; ring
  have hWN : (ExpA.winN t B₀ N : ℝ) = (lam : ℝ) * N := by
    rw [ExpA.winN, hlamdef]; push_cast; ring
  -- ## the shift `δ'` and the window `M'`
  set δ' : ℝ := γ ^ K / AA with hδ'def
  have hδ'0 : 0 < δ' := div_pos (pow_pos hγ0 K) hAA0
  have hδ'1 : δ' ≤ 1 := by
    rw [hδ'def, div_le_one hAA0]
    exact le_trans (pow_le_one₀ hγ0.le hγ1) hA1
  -- ## non-degeneracy from the hypothesis `1 ≤ C γ^K M₁`
  have hM1ge : 2 * AA ≤ γ ^ K * (M₁ : ℝ) := by
    have h1 : 1 / Cc ≤ γ ^ K * (M₁ : ℝ) := by
      rw [div_le_iff₀ hCcpos]
      nlinarith [hCM]
    have h2 : 2 * AA ≤ 1 / Cc := by
      rw [le_div_iff₀ hCcpos]
      have hCA : Cc * (2 * AA) ≤ 1 :=
        (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * AA)).mp hCcAA
      nlinarith [hCA]
    linarith
  have hδ'M1 : 2 ≤ δ' * (M₁ : ℝ) := by
    rw [hδ'def, div_mul_eq_mul_div, le_div_iff₀ hAA0]
    linarith [hM1ge]
  have hδ'M1ge1 : 1 ≤ δ' * (M₁ : ℝ) := le_trans one_le_two hδ'M1
  have hδ'M1nn : 0 ≤ δ' * (M₁ : ℝ) := le_trans (by norm_num) hδ'M1ge1
  set M' : ℕ := (⌊δ' * (M₁ : ℝ)⌋).toNat with hM'def
  have hfloor0 : 0 ≤ ⌊δ' * (M₁ : ℝ)⌋ := Int.floor_nonneg.mpr hδ'M1nn
  have hM'cast : (M' : ℝ) = (⌊δ' * (M₁ : ℝ)⌋ : ℝ) := by
    rw [hM'def]
    exact_mod_cast Int.toNat_of_nonneg hfloor0
  have hM'posR : (1 : ℝ) ≤ (M' : ℝ) := by
    have h1 : (1 : ℤ) ≤ ⌊δ' * (M₁ : ℝ)⌋ :=
      Int.le_floor.mpr (by push_cast; linarith [hδ'M1ge1])
    rw [hM'cast]
    exact_mod_cast h1
  have hM'pos : 1 ≤ M' := by exact_mod_cast hM'posR
  have hM'le : M' ≤ M₁ := by
    have h1 : (⌊δ' * (M₁ : ℝ)⌋ : ℝ) ≤ δ' * (M₁ : ℝ) := Int.floor_le _
    have h2 : δ' * (M₁ : ℝ) ≤ 1 * (M₁ : ℝ) := mul_le_mul_of_nonneg_right hδ'1 (by positivity)
    have h3 : (M' : ℝ) ≤ (M₁ : ℝ) := by rw [hM'cast]; linarith
    exact_mod_cast h3
  have hM'ge : Cc * γ ^ K * (M₁ : ℝ) ≤ (M' : ℝ) := by
    have h2AA : Cc * (γ ^ K * (M₁ : ℝ)) ≤ γ ^ K * (M₁ : ℝ) / (2 * AA) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * AA)]
      have hCA : Cc * (2 * AA) ≤ 1 :=
        (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * AA)).mp hCcAA
      have hγM : (0 : ℝ) ≤ γ ^ K * (M₁ : ℝ) := by positivity
      nlinarith [hCA, hγM]
    have hhalf : (δ' * (M₁ : ℝ)) / 2 = γ ^ K * (M₁ : ℝ) / (2 * AA) := by
      rw [hδ'def]; field_simp
    have hfloor : (δ' * (M₁ : ℝ)) / 2 ≤ (⌊δ' * (M₁ : ℝ)⌋ : ℝ) := by
      have h2 := Int.lt_floor_add_one (δ' * (M₁ : ℝ))
      have h3 : ((⌊δ' * (M₁ : ℝ)⌋ : ℤ) : ℝ) ≤ δ' * (M₁ : ℝ) := Int.floor_le _
      linarith [h2, h3, hδ'M1]
    rw [hM'cast]
    calc Cc * γ ^ K * (M₁ : ℝ) = Cc * (γ ^ K * (M₁ : ℝ)) := by ring
      _ ≤ γ ^ K * (M₁ : ℝ) / (2 * AA) := h2AA
      _ = (δ' * (M₁ : ℝ)) / 2 := hhalf.symm
      _ ≤ (⌊δ' * (M₁ : ℝ)⌋ : ℝ) := hfloor
  -- ## the Jensen step
  have hcardIcc : (((Finset.Icc 1 M₁).card : ℕ) : ℝ) = (M₁ : ℝ) := by
    rw [Nat.card_Icc]; simp
  have h2tpow : (2 : ℝ) ^ t = ((2 ^ t : ℕ) : ℝ) := by push_cast; ring
  have hJ : γ ^ (2 ^ t) ≤ ((M₁ : ℝ))⁻¹ * ∑ a ∈ Finset.Icc 1 M₁,
      boxNormPow t (fun i : Fin t => arithIcc ((a : ℤ) + b i) M₂) (symIcc N) f := by
    have h2t : (1 : ℝ) ≤ (2 : ℝ) ^ t := one_le_pow₀ (by norm_num)
    have hne : (Finset.Icc 1 M₁).Nonempty := ⟨1, by simp [Finset.mem_Icc, hM1]⟩
    have harg : γ ≤ ((Finset.Icc 1 M₁).card : ℝ)⁻¹ * ∑ a ∈ Finset.Icc 1 M₁,
        (boxNormPow t (fun i : Fin t => arithIcc ((a : ℤ) + b i) M₂) (symIcc N) f)
          ^ (1 / (2 : ℝ) ^ t) := by
      have heq : ((Finset.Icc 1 M₁).card : ℝ)⁻¹ * ∑ a ∈ Finset.Icc 1 M₁,
          (boxNormPow t (fun i : Fin t => arithIcc ((a : ℤ) + b i) M₂) (symIcc N) f)
            ^ (1 / (2 : ℝ) ^ t) = LadderP.p3BoxAvg t M₁ M₂ b (symIcc N) f := by
        simp only [LadderP.p3BoxAvg, boxNorm, hcardIcc]
      rw [heq]; exact hbox
    have hmain := Holds.ExpPET.pow_le_avg_of_le_avg_rpow (s := Finset.Icc 1 M₁) hne
      (p := (2 : ℝ) ^ t) h2t (le_of_lt hγ0)
      (fun a => boxNormPow t (fun i : Fin t => arithIcc ((a : ℤ) + b i) M₂) (symIcc N) f)
      (fun a _ => norm_nonneg _) harg
    rw [hcardIcc] at hmain
    rw [h2tpow] at hmain
    simpa only [Real.rpow_natCast] using hmain
  -- ## the expansion + Fubini + nonnegativity step
  have hAX := ExpA.avgExtraction (s := t) (hs := ht) (M₁ := M₂) (hM₁ := hM2) (M₂ := M₁)
    (hM₂ := hM1) 1 b (symIcc N) f hγ0 hfin (by simpa only [one_mul] using hJ)
  -- ## the pair index type and the extracted averages
  let P : Type := (i : Fin t) → {n : ℕ // n ∈ Finset.Icc 1 M₂}
  let Λ : P × P → ℂ := fun p => ∑ a ∈ Finset.Icc 1 M₁, ∑' x : ℤ,
      Holds.ExpPET.expCube (fun i : Fin t => 1 * (a : ℤ) + b i)
        (fun i => ((p.1 i).1 : ℤ)) (fun i => ((p.2 i).1 : ℤ)) f x
  let xx : P × P → ℝ := fun p => ‖((ExpA.winN t B₀ N : ℂ) * (M₁ : ℂ))⁻¹ * Λ p‖
  let tt : ℝ := γ ^ (2 ^ t) * ((symIcc N).card : ℝ) / (ExpA.winN t B₀ N : ℝ)
  let η : ℝ := (CL * δ') ^ (((2 * KL : ℕ) : ℝ))⁻¹
  have hWpos : (0 : ℝ) < (ExpA.winN t B₀ N : ℝ) := by
    rw [hWN]; positivity
  have hcardP : (Finset.univ : Finset P).card = M₂ ^ t := Holds.ExpPET.card_labels t M₂
  have hcP : Fintype.card P = M₂ ^ t := by rw [← Finset.card_univ, hcardP]
  have hcardPP : (Finset.univ : Finset (P × P)).card = M₂ ^ t * M₂ ^ t := by
    rw [Finset.card_univ, Fintype.card_prod, hcP]
  have hcardPP' : (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ) = (((M₂ : ℝ) ^ t) ^ 2) := by
    rw [hcardPP]; push_cast; ring
  haveI : Nonempty (P × P) :=
    ⟨(fun _ => ⟨1, by simp [Finset.mem_Icc, hM2]⟩, fun _ => ⟨1, by simp [Finset.mem_Icc, hM2]⟩)⟩
  have hη0 : 0 ≤ η := Real.rpow_nonneg (by positivity) _
  have hηpow : η ^ (2 * KL) = CL * δ' := by
    simp only [η]
    exact Real.rpow_inv_natCast_pow (by positivity) (by omega)
  have hηpos : 0 < η := Real.rpow_pos_of_pos (by positivity) _
  -- ## `xx` is bounded by `1`
  have hx0 : ∀ p : P × P, 0 ≤ xx p := fun p => norm_nonneg _
  have hx1 : ∀ p : P × P, xx p ≤ 1 := by
    intro p
    have hΛ : ‖Λ p‖ ≤ (M₁ : ℝ) * ((symIcc N).card : ℝ) := by
      simp only [Λ]
      calc ‖∑ a ∈ Finset.Icc 1 M₁, ∑' x : ℤ, Holds.ExpPET.expCube (fun i : Fin t => 1 * (a : ℤ) + b i)
              (fun i => ((p.1 i).1 : ℤ)) (fun i => ((p.2 i).1 : ℤ)) f x‖
          ≤ ∑ a ∈ Finset.Icc 1 M₁,
              ‖∑' x : ℤ, Holds.ExpPET.expCube (fun i : Fin t => 1 * (a : ℤ) + b i)
                (fun i => ((p.1 i).1 : ℤ)) (fun i => ((p.2 i).1 : ℤ)) f x‖ := norm_sum_le _ _
        _ ≤ ∑ _a ∈ Finset.Icc 1 M₁, ((symIcc N).card : ℝ) := by
            refine Finset.sum_le_sum fun a _ => ?_
            exact ExpA.expCubeTsumLe _ _ _ hbd (supportIn_symIcc hsup)
        _ = ((Finset.Icc 1 M₁).card : ℝ) * ((symIcc N).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = (M₁ : ℝ) * ((symIcc N).card : ℝ) := by rw [hcardIcc]
    have hxeq : xx p = ((ExpA.winN t B₀ N : ℝ) * (M₁ : ℝ))⁻¹ * ‖Λ p‖ := by
      simp only [xx, norm_mul, norm_inv, Complex.norm_natCast]
    rw [hxeq]
    have hM1r : (0 : ℝ) < (M₁ : ℝ) := by exact_mod_cast hM1
    have h1 : ((ExpA.winN t B₀ N : ℝ) * (M₁ : ℝ))⁻¹ * ‖Λ p‖
        ≤ ((ExpA.winN t B₀ N : ℝ) * (M₁ : ℝ))⁻¹ * ((M₁ : ℝ) * ((symIcc N).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hΛ (by positivity)
    have h2 : ((ExpA.winN t B₀ N : ℝ) * (M₁ : ℝ))⁻¹ * ((M₁ : ℝ) * ((symIcc N).card : ℝ))
        = ((symIcc N).card : ℝ) / (ExpA.winN t B₀ N : ℝ) := by
      field_simp
    rw [h2] at h1
    have h3 : ((symIcc N).card : ℝ) / (ExpA.winN t B₀ N : ℝ) ≤ 1 := by
      rw [div_le_one hWpos]
      exact_mod_cast ExpA.card_symIcc_le_winN (s := t) (C₀ := B₀) hN
    linarith
  -- ## the lower bound for the average of `xx`
  have hsumsplit : ∑ p : P × P, xx p
      = ((ExpA.winN t B₀ N : ℝ))⁻¹ * ∑ p : P × P, ‖((M₁ : ℂ))⁻¹ * Λ p‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [xx, norm_mul, norm_inv, Complex.norm_natCast, mul_inv]
    ring
  have hAX'' : γ ^ (2 ^ t) * ((symIcc N).card : ℝ)
      ≤ (∑ k : P, ∑ k' : P, ‖((M₁ : ℂ))⁻¹ * Λ (k, k')‖) / (((M₂ : ℝ) ^ t) ^ 2) := by
    have h := hAX
    dsimp only [P, Λ] at h ⊢
    rw [div_eq_inv_mul]
    exact h
  have hAX' : γ ^ (2 ^ t) * ((symIcc N).card : ℝ)
      ≤ (∑ p : P × P, ‖((M₁ : ℂ))⁻¹ * Λ p‖) / (((M₂ : ℝ) ^ t) ^ 2) := by
    rw [Fintype.sum_prod_type]
    exact hAX''
  have ht : tt ≤ (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ * ∑ p : P × P, xx p := by
    have hBpos : (0 : ℝ) < (((M₂ : ℝ) ^ t) ^ 2) := by positivity
    have hS : γ ^ (2 ^ t) * ((symIcc N).card : ℝ) * (((M₂ : ℝ) ^ t) ^ 2)
        ≤ ∑ p : P × P, ‖((M₁ : ℂ))⁻¹ * Λ p‖ := (le_div_iff₀ hBpos).mp hAX'
    have key : tt * (((M₂ : ℝ) ^ t) ^ 2)
        ≤ ((ExpA.winN t B₀ N : ℝ))⁻¹ * ∑ p : P × P, ‖((M₁ : ℂ))⁻¹ * Λ p‖ := by
      calc tt * (((M₂ : ℝ) ^ t) ^ 2)
          = (γ ^ (2 ^ t) * ((symIcc N).card : ℝ) * (((M₂ : ℝ) ^ t) ^ 2))
              / ((ExpA.winN t B₀ N : ℝ)) := by
            simp only [tt]; ring
        _ ≤ (∑ p : P × P, ‖((M₁ : ℂ))⁻¹ * Λ p‖) / ((ExpA.winN t B₀ N : ℝ)) :=
            div_le_div_of_nonneg_right hS (by positivity)
        _ = ((ExpA.winN t B₀ N : ℝ))⁻¹ * ∑ p : P × P, ‖((M₁ : ℂ))⁻¹ * Λ p‖ := by
            rw [div_eq_inv_mul]
    rw [hcardPP', hsumsplit, ← div_eq_inv_mul]
    exact (le_div_iff₀ hBpos).mpr key
  -- ## `η ≤ tt / 2`
  have hrpow : ∀ x : ℝ, 0 ≤ x → (x ^ (2 * KL)) ^ (((2 * KL : ℕ) : ℝ))⁻¹ = x := by
    intro x hx
    rw [← Real.rpow_natCast (x := x) (n := 2 * KL), ← Real.rpow_mul hx,
      mul_inv_cancel₀ (by positivity : (((2 * KL : ℕ) : ℝ)) ≠ 0), Real.rpow_one]
  have h2tKL : 2 ^ t * (2 * KL) = K := by rw [hKdef]; ring
  have hbase : CL * δ' ≤ (γ ^ (2 ^ t) / (lam : ℝ)) ^ (2 * KL) := by
    have h3 : CL * (γ ^ K / AA) ≤ γ ^ K / (lam : ℝ) ^ (2 * KL) := by
      rw [← mul_div_assoc, div_le_div_iff₀ hAA0 (by positivity)]
      nlinarith [hAlam, hCL0, pow_nonneg hγ0.le K]
    calc CL * δ' = CL * (γ ^ K / AA) := by rw [hδ'def]
      _ ≤ γ ^ K / (lam : ℝ) ^ (2 * KL) := h3
      _ = (γ ^ (2 ^ t) / (lam : ℝ)) ^ (2 * KL) := by
            rw [div_pow, ← pow_mul, h2tKL]
  have hηle : η ≤ γ ^ (2 ^ t) / (lam : ℝ) := by
    simp only [η]
    calc (CL * δ') ^ (((2 * KL : ℕ) : ℝ))⁻¹
        ≤ ((γ ^ (2 ^ t) / (lam : ℝ)) ^ (2 * KL)) ^ (((2 * KL : ℕ) : ℝ))⁻¹ :=
          Real.rpow_le_rpow (by positivity) hbase (by positivity)
      _ = γ ^ (2 ^ t) / (lam : ℝ) := hrpow _ (by positivity)
  have htge : γ ^ (2 ^ t) / (lam : ℝ) ≤ tt / 2 := by
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have ht2 : tt / 2 = γ ^ (2 ^ t) * (2 * (N : ℝ) + 1) / (2 * ((lam : ℝ) * (N : ℝ))) := by
      simp only [tt]
      rw [hcardS, hWN]
      ring
    rw [ht2, div_le_div_iff₀ hlamR (by positivity)]
    have hd : (0 : ℝ) < γ ^ (2 ^ t) := pow_pos hγ0 _
    nlinarith [hNr, hd, hlamR]
  have hηt : η ≤ tt / 2 := le_trans hηle htge
  -- ## the Markov / power-mean step
  have hMarkov := ExpA.markovPowMean (ι := P × P) (x := xx) (η := η) (t := tt) (p := KL)
    hKL1 hx0 hx1 hη0 hηt ht
  -- ## the per-pair PET step
  have hb' : ∀ i : Fin t, |b i| ≤ (B₀ : ℤ) * (N : ℤ) / (M₂ : ℤ) := by
    intro i
    have hM2pos : (0 : ℤ) < (M₂ : ℤ) := by exact_mod_cast hM2
    have h1 : (B₀ : ℤ) * (M₁ : ℤ) * (M₂ : ℤ) ≤ (B₀ : ℤ) * (N : ℤ) := by
      have hb1 : (B₀ : ℤ) * ((M₁ : ℤ) * (M₂ : ℤ)) ≤ (B₀ : ℤ) * (N : ℤ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hNM) (by exact_mod_cast Nat.zero_le B₀)
      linarith [hb1]
    have h2 : |b i| * (M₂ : ℤ) ≤ (B₀ : ℤ) * (N : ℤ) :=
      le_trans (mul_le_mul_of_nonneg_right (hb i) (by positivity : (0 : ℤ) ≤ (M₂ : ℤ))) h1
    exact (Int.le_ediv_iff_mul_le hM2pos).mpr h2
  let Good : Finset (P × P) := Finset.univ.filter (fun p => η ≤ xx p)
  have hGoodsub : Good ⊆ Finset.univ := Finset.filter_subset _ _
  have hNM' : (M₂ : ℝ) * (M₁ : ℝ) ≤ (N : ℝ) / ((1 : ℤ) : ℝ) := by
    rw [Int.cast_one, div_one]; linarith [hNM]
  have hpair : ∀ p ∈ Good, (xx p ^ 2 / CL) ^ KL ≤ boxNormPow (2 ^ t - 1)
      (fun i : Fin (2 ^ t - 1) => arithIcc (1 * ExpA.dotU (ExpA.ωOfA t i)
        (fun j => ((p.1 j).1 : ℤ) - ((p.2 j).1 : ℤ))) M') (symIcc N) f := by
    intro p hp
    have hηp : η ≤ xx p := (Finset.mem_filter.mp hp).2
    have hxpos : 0 < xx p := lt_of_lt_of_le hηpos hηp
    have hxle1 : xx p ^ 2 ≤ 1 := by
      calc xx p ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (hx0 p) (hx1 p) 2
        _ = 1 := by norm_num
    have hgauge : CL * δ' ≤ (xx p ^ 2) ^ KL := by
      have h1 : η ^ (2 * KL) ≤ (xx p) ^ (2 * KL) := pow_le_pow_left₀ hηpos.le hηp _
      rw [hηpow] at h1
      have h2 : (xx p ^ 2) ^ KL = (xx p) ^ (2 * KL) := by rw [pow_mul]
      rw [h2]; exact h1
    have hγ2 : xx p ^ 2 ≤ ‖((ExpA.winN t B₀ N : ℂ) * (M₁ : ℂ))⁻¹ * Λ p‖ ^ 2 := le_of_eq rfl
    exact hPET 1 B₀ N M₂ M₁ b f p.1 p.2 (by norm_num) hN hM2 hM1 hNM' hb' hsup hbd hδ'0 hδ'M1ge1
      (pow_pos hxpos 2) hxle1 hgauge hγ2
  -- ## the dense average is the average of the pair box-norm powers
  have hboxAvg := ExpA.boxAvgEqPairSum (s := t) M₂ hM2 1 M' N f
  have hboxAvg' : Concat.boxAvg t M₂ 1 (ExpA.ωOfA t) M' N f
      = (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ *
        ∑ p : P × P, boxNormPow (2 ^ t - 1)
          (fun i : Fin (2 ^ t - 1) => arithIcc (1 * ExpA.dotU (ExpA.ωOfA t i)
            (fun j => ((p.1 j).1 : ℤ) - ((p.2 j).1 : ℤ))) M') (symIcc N) f := by
    rw [hboxAvg, hcardPP', Fintype.sum_prod_type]
  have hstep1 : (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ *
        ∑ p ∈ Good, (xx p ^ 2 / CL) ^ KL
      ≤ (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ *
        ∑ p : P × P, boxNormPow (2 ^ t - 1)
          (fun i : Fin (2 ^ t - 1) => arithIcc (1 * ExpA.dotU (ExpA.ωOfA t i)
            (fun j => ((p.1 j).1 : ℤ) - ((p.2 j).1 : ℤ))) M') (symIcc N) f := by
    have hcpos : (0 : ℝ) < (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hcpos.le
    refine le_trans (Finset.sum_le_sum fun p hp => hpair p hp) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg hGoodsub (fun p _ _ => norm_nonneg _)
  have hstep2 : (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ *
        ∑ p ∈ Good, (xx p ^ 2 / CL) ^ KL
      = (1 / CL ^ KL) * ((((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ *
        ∑ p ∈ Good, xx p ^ (2 * KL)) := by
    have h2 : ∀ p, (xx p ^ 2 / CL) ^ KL = xx p ^ (2 * KL) * (1 / CL ^ KL) := by
      intro p
      rw [show (xx p ^ 2 / CL) ^ KL = xx p ^ (2 * KL) / CL ^ KL by rw [div_pow, ← pow_mul]]
      ring
    calc (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ * ∑ p ∈ Good, (xx p ^ 2 / CL) ^ KL
        = (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ *
            ∑ p ∈ Good, xx p ^ (2 * KL) * (1 / CL ^ KL) := by
          rw [Finset.sum_congr rfl (fun p _ => h2 p)]
      _ = (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ *
            ((∑ p ∈ Good, xx p ^ (2 * KL)) * (1 / CL ^ KL)) := by
          rw [Finset.sum_mul]
      _ = (1 / CL ^ KL) * ((((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ *
            ∑ p ∈ Good, xx p ^ (2 * KL)) := by ring
  have hstep3 : (1 / CL ^ KL) * (tt ^ (2 * KL) / 2 ^ (2 * KL))
      ≤ (1 / CL ^ KL) * ((((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ *
        ∑ p ∈ Good, xx p ^ (2 * KL)) := by
    have hG : (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ * ∑ p ∈ Good, xx p ^ (2 * KL)
        = (((Finset.univ : Finset (P × P)).card : ℕ) : ℝ)⁻¹ *
          ∑ i ∈ Finset.univ.filter (fun i => η ≤ xx i), (xx i) ^ (2 * KL) := by
      simp only [Good]
    rw [hG]
    exact mul_le_mul_of_nonneg_left hMarkov (by positivity)
  have htlow : γ ^ (2 ^ t) * 2 / (lam : ℝ) ≤ tt := by
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have ht2 : tt = γ ^ (2 ^ t) * (2 * (N : ℝ) + 1) / ((lam : ℝ) * (N : ℝ)) := by
      simp only [tt]
      rw [hcardS, hWN]
    rw [ht2, div_le_div_iff₀ hlamR (by positivity)]
    have hd : (0 : ℝ) < γ ^ (2 ^ t) := pow_pos hγ0 _
    nlinarith [hNr, hd, hlamR]
  have hstep4 : γ ^ K / ((lam : ℝ) ^ (2 * KL) * CL ^ KL)
      ≤ (1 / CL ^ KL) * (tt ^ (2 * KL) / 2 ^ (2 * KL)) := by
    have h1 : (γ ^ (2 ^ t) * 2 / (lam : ℝ)) ^ (2 * KL) ≤ tt ^ (2 * KL) :=
      pow_le_pow_left₀ (by positivity) htlow _
    have h2 : (γ ^ (2 ^ t) * 2 / (lam : ℝ)) ^ (2 * KL)
        = γ ^ K * 2 ^ (2 * KL) / (lam : ℝ) ^ (2 * KL) := by
      rw [div_pow, mul_pow, ← pow_mul, h2tKL]
    rw [h2] at h1
    have h3 : γ ^ K * 2 ^ (2 * KL) / (lam : ℝ) ^ (2 * KL) / 2 ^ (2 * KL)
        ≤ tt ^ (2 * KL) / 2 ^ (2 * KL) :=
      div_le_div_of_nonneg_right h1 (by positivity)
    have h5 : γ ^ K / ((lam : ℝ) ^ (2 * KL) * CL ^ KL)
        = γ ^ K * 2 ^ (2 * KL) / (lam : ℝ) ^ (2 * KL) / 2 ^ (2 * KL) * (1 / CL ^ KL) := by
      field_simp
    calc γ ^ K / ((lam : ℝ) ^ (2 * KL) * CL ^ KL)
        = γ ^ K * 2 ^ (2 * KL) / (lam : ℝ) ^ (2 * KL) / 2 ^ (2 * KL) * (1 / CL ^ KL) := h5
      _ ≤ (tt ^ (2 * KL) / 2 ^ (2 * KL)) * (1 / CL ^ KL) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = (1 / CL ^ KL) * (tt ^ (2 * KL) / 2 ^ (2 * KL)) := by ring
  -- ## conclusion
  have hfinal : Cc * γ ^ K ≤ Concat.boxAvg t M₂ 1 (ExpA.ωOfA t) M' N f := by
    have hfin1 : Cc * γ ^ K ≤ γ ^ K / ((lam : ℝ) ^ (2 * KL) * CL ^ KL) := by
      calc Cc * γ ^ K ≤ (1 / ((lam : ℝ) ^ (2 * KL) * CL ^ KL)) * γ ^ K :=
            mul_le_mul_of_nonneg_right hCcCL (pow_nonneg hγ0.le K)
        _ = γ ^ K / ((lam : ℝ) ^ (2 * KL) * CL ^ KL) := by ring
    exact le_trans hfin1 (le_trans hstep4 (le_trans hstep3 (le_trans (le_of_eq hstep2.symm)
      (le_trans hstep1 (le_of_eq hboxAvg'.symm)))))
  exact ⟨M', hM'pos, hM'le, hM'ge, by
    rw [← boxAvg_omegaOfA_eq_denseAvg t M₂ M' N f]; exact hfinal⟩

end

end Work.Peluse.SwapA
