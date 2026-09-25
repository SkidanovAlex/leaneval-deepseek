import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.norm_continuousMultilinearMap_le_of_diagonal
import Submission.Work.NN.Core.oneDim_finitediff_interp
import Submission.Work.NN.Core.iteratedFDeriv_comp_perm_of_contDiffAt

namespace Work.NN.Core

open scoped NNReal ENNReal
open Set

/-- The `j`-th derivative of the one-variable slice `t ↦ f (z + t • v)` at `t` is the `j`-th
iterated derivative of `f` at `z + t • v` evaluated on the constant tuple `v`. -/
theorem iteratedDeriv_slice_gen {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ} {f : E → F} (hf : ContDiff ℝ n f)
    (z v : E) (t : ℝ) :
    iteratedDeriv n (fun s : ℝ => f (z + s • v)) t
      = iteratedFDeriv ℝ n f (z + t • v) (fun _ => v) := by
  rw [iteratedDeriv_eq_iteratedFDeriv]
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  have hLv : L 1 = v := by simp [L]
  have hLt : L t = t • v := by simp [L]
  have hf' : ContDiff ℝ n (fun w : E => f (z + w)) := hf.comp (by fun_prop)
  have hfun : (fun s : ℝ => f (z + s • v)) = (fun w : E => f (z + w)) ∘ ⇑L := by
    funext s; simp [L]
  rw [hfun]
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (𝕜 := ℝ) L hf' t (i := n) (le_refl _)]
  rw [hLt, iteratedFDeriv_comp_add_left (𝕜 := ℝ) n z (t • v)]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp [hLv]

/-- The polydisc is convex. -/
theorem convex_polydisc_interp {n : ℕ} (c : Fin n → ℂ) (r : Fin n → ℝ) :
    Convex ℝ (Work.CR.Flat.polydisc c r) := by
  intro x hx y hy a b ha hb hab
  simp only [Work.CR.Flat.mem_polydisc] at hx hy ⊢
  intro j
  have hx' : ‖x j - c j‖ < r j := hx j
  have hy' : ‖y j - c j‖ < r j := hy j
  have hkey : (a • x + b • y) j - c j = a • (x j - c j) + b • (y j - c j) := by
    have h1 : (a • x + b • y) j = a • x j + b • y j := rfl
    have hc : a • c j + b • c j = c j := by rw [← add_smul, hab, one_smul]
    rw [h1, smul_sub, smul_sub]
    linear_combination hc
  rw [hkey]
  have hbnd : ‖a • (x j - c j) + b • (y j - c j)‖ ≤ a * ‖x j - c j‖ + b * ‖y j - c j‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  refine hbnd.trans_lt ?_
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · subst ha0
    have hb1 : b = 1 := by linarith
    subst hb1
    simp only [zero_mul, zero_add, one_mul]
    exact hy'
  · refine (add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx' hapos)
      (mul_le_mul_of_nonneg_left (le_of_lt hy') hb)).trans_eq ?_
    rw [← add_mul, hab, one_mul]

set_option maxHeartbeats 8000000 in
theorem holderNorm_interp_le {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ ρ' : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hρ' : ∀ j, 0 < ρ' j) (hlt : ∀ j, ρ' j < ρ j)
    {m k : ℕ} (hmk : m < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : (Fin n → ℂ) → ℂ, ContDiff ℝ k w →
      Work.CR.Flat.holderNorm k α w (Work.CR.Flat.polydisc 0 ρ) < ⊤ →
      Work.CR.Flat.holderNorm m α w (Work.CR.Flat.polydisc 0 ρ')
        ≤ ENNReal.ofReal ε * Work.CR.Flat.holderNorm k α w (Work.CR.Flat.polydisc 0 ρ)
          + ENNReal.ofReal C * Work.CR.Flat.holderNorm 0 α w (Work.CR.Flat.polydisc 0 ρ) := by
  have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le m) hmk
  have hα1' : 0 < 1 - α := by linarith
  have hmargin_exists : ∃ d : ℝ, 0 < d ∧ ∀ j, d ≤ ρ j - ρ' j := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      exact ⟨1, one_pos, fun j => j.elim0⟩
    · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      refine ⟨Finset.univ.inf' Finset.univ_nonempty (fun j => ρ j - ρ' j), ?_, ?_⟩
      · rw [Finset.lt_inf'_iff]
        intro j _
        exact sub_pos.mpr (hlt j)
      · intro j
        exact Finset.inf'_le _ (Finset.mem_univ j)
  obtain ⟨d, hd0, hdle⟩ := hmargin_exists
  have h1D : ∀ j : ℕ, ∃ A D : ℝ, j ≤ k → 0 ≤ A ∧ 0 ≤ D ∧
      (∀ (ψ : ℝ → ℂ) (h : ℝ), 0 < h → ContDiff ℝ k ψ →
        ∀ (S0 Sk : ℝ), 0 ≤ S0 → 0 ≤ Sk →
          (∀ t ∈ Set.Icc 0 ((k : ℝ) * h), ‖ψ t‖ ≤ S0) →
          (∀ t ∈ Set.Icc 0 ((k : ℝ) * h), ‖iteratedDeriv k ψ t‖ ≤ Sk) →
          ‖iteratedDeriv j ψ 0‖ ≤ A / h ^ j * S0 + D * h ^ (k - j) * Sk) := by
    intro j
    by_cases hj : j ≤ k
    · obtain ⟨A, D, hA, hD, hb⟩ := oneDim_finitediff_interp (k := k) (j := j) hj
      exact ⟨A, D, fun _ => ⟨hA, hD, hb⟩⟩
    · exact ⟨1, 1, fun hjk => absurd hjk hj⟩
  choose AA DD hAD using h1D
  let Kfac : ℕ → ℝ := fun j => (j : ℝ) ^ j / (j.factorial : ℝ)
  have hKfac_nn : ∀ j, 0 ≤ Kfac j := fun j =>
    div_nonneg (pow_nonneg (Nat.cast_nonneg j) j) (Nat.cast_nonneg _)
  let M : ℝ := 1 + ∑ j ∈ Finset.range (k + 1), (Kfac j * DD j + Kfac j * AA j)
  have hsum_nn : 0 ≤ ∑ j ∈ Finset.range (k + 1), (Kfac j * DD j + Kfac j * AA j) :=
    Finset.sum_nonneg (fun j hj => by
      have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      exact add_nonneg (mul_nonneg (hKfac_nn j) (hAD j hj').2.1)
        (mul_nonneg (hKfac_nn j) (hAD j hj').1))
  have hMpos : 0 < M := by simp only [M]; linarith
  have hsummand_nn : ∀ j, j ≤ k → 0 ≤ Kfac j * DD j + Kfac j * AA j := fun j hj =>
    add_nonneg (mul_nonneg (hKfac_nn j) (hAD j hj).2.1) (mul_nonneg (hKfac_nn j) (hAD j hj).1)
  have hMge : ∀ j, j ≤ k → Kfac j * DD j ≤ M := by
    intro j hj
    have hmem : j ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
    have hnn : ∀ i ∈ Finset.range (k + 1), 0 ≤ Kfac i * DD i + Kfac i * AA i := fun i hi =>
      hsummand_nn i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    have h3 := Finset.single_le_sum hnn hmem
    have h4 : 0 ≤ Kfac j * AA j := mul_nonneg (hKfac_nn j) (hAD j hj).1
    have h2 : Kfac j * DD j ≤ ∑ i ∈ Finset.range (k + 1), (Kfac i * DD i + Kfac i * AA i) := by
      linarith
    simp only [M]; linarith
  have hMgeA : ∀ j, j ≤ k → Kfac j * AA j ≤ M := by
    intro j hj
    have hmem : j ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
    have hnn : ∀ i ∈ Finset.range (k + 1), 0 ≤ Kfac i * DD i + Kfac i * AA i := fun i hi =>
      hsummand_nn i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    have h3 := Finset.single_le_sum hnn hmem
    have h4 : 0 ≤ Kfac j * DD j := mul_nonneg (hKfac_nn j) (hAD j hj).2.1
    have h2 : Kfac j * AA j ≤ ∑ i ∈ Finset.range (k + 1), (Kfac i * DD i + Kfac i * AA i) := by
      linarith
    simp only [M]; linarith
  let target : ℝ := ε / (16 * ((m : ℝ) + 1) * M)
  have hm1pos : 0 < (m : ℝ) + 1 := by positivity
  have htarget_pos : 0 < target := by
    simp only [target]; exact div_pos hε (by positivity)
  let hh : ℝ := min 1 (min (d / ((k : ℝ) + 1)) (target ^ (1 / (1 - α))))
  have hden : 0 < (k : ℝ) + 1 := by positivity
  have hhpos : 0 < hh := by
    simp only [hh]
    exact lt_min one_pos (lt_min (div_pos hd0 hden) (Real.rpow_pos_of_pos htarget_pos _))
  have hhle1 : hh ≤ 1 := by simp only [hh]; exact min_le_left _ _
  have hhled : (k : ℝ) * hh ≤ d := by
    have h1 : hh ≤ d / ((k : ℝ) + 1) := by
      simp only [hh]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have h2 : (k : ℝ) * (d / ((k : ℝ) + 1)) ≤ d := by
      rw [mul_div_assoc', div_le_iff₀ hden]
      nlinarith [hd0]
    exact le_trans (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg k)) h2
  have hhrpow : hh ^ (1 - α) ≤ target := by
    have h1 : hh ≤ target ^ (1 / (1 - α)) := by
      simp only [hh]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    have h2 : hh ^ (1 - α) ≤ (target ^ (1 / (1 - α))) ^ (1 - α) :=
      Real.rpow_le_rpow (le_of_lt hhpos) h1 hα1'.le
    have h3 : (target ^ (1 / (1 - α))) ^ (1 - α) = target := by
      rw [← Real.rpow_mul (le_of_lt htarget_pos)]
      have h4 : 1 / (1 - α) * (1 - α) = 1 := by field_simp
      rw [h4, Real.rpow_one]
    rwa [h3] at h2
  let δ : ℕ → ℝ := fun j => Kfac j * DD j * hh ^ ((k - j : ℕ) : ℝ)
  let c : ℕ → ℝ := fun j => Kfac j * AA j / hh ^ j
  have hδnn : ∀ j, j ≤ k → 0 ≤ δ j := fun j hj => by
    simp only [δ]
    exact mul_nonneg (mul_nonneg (hKfac_nn j) (hAD j hj).2.1)
      (Real.rpow_nonneg (le_of_lt hhpos) _)
  have hcnn : ∀ j, j ≤ k → 0 ≤ c j := fun j hj => by
    simp only [c]
    exact div_nonneg (mul_nonneg (hKfac_nn j) (hAD j hj).1) (pow_nonneg (le_of_lt hhpos) j)
  let Cbig : ℝ := 1 + ∑ j ∈ Finset.range (k + 1),
    (Kfac j * AA j / hh ^ j) * (1 + hh ^ (1 - α) + 2 / hh ^ α)
  let Cfin : ℝ := 3 * ((m : ℝ) + 1) * Cbig + 1
  have hsummand2_nn : ∀ j, j ≤ k →
      0 ≤ (Kfac j * AA j / hh ^ j) * (1 + hh ^ (1 - α) + 2 / hh ^ α) := by
    intro j hj
    refine mul_nonneg (div_nonneg (mul_nonneg (hKfac_nn j) (hAD j hj).1)
      (pow_nonneg (le_of_lt hhpos) j)) ?_
    have h2 : 0 ≤ hh ^ (1 - α) := Real.rpow_nonneg (le_of_lt hhpos) _
    have h3 : 0 ≤ 2 / hh ^ α := div_nonneg (by norm_num) (Real.rpow_nonneg (le_of_lt hhpos) _)
    linarith
  have hCbig_single : ∀ j, j ≤ k →
      (Kfac j * AA j / hh ^ j) * (1 + hh ^ (1 - α) + 2 / hh ^ α) ≤ Cbig := by
    intro j hj
    have hmem : j ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
    have hnn : ∀ i ∈ Finset.range (k + 1),
        0 ≤ (Kfac i * AA i / hh ^ i) * (1 + hh ^ (1 - α) + 2 / hh ^ α) := fun i hi =>
      hsummand2_nn i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    have h3 := Finset.single_le_sum hnn hmem
    simp only [Cbig]; linarith
  have hKfacAA : ∀ j, j ≤ k → Kfac j * AA j / hh ^ j ≤ Cbig := by
    intro j hj
    have h4 : 0 ≤ Kfac j * AA j / hh ^ j :=
      div_nonneg (mul_nonneg (hKfac_nn j) (hAD j hj).1) (pow_nonneg (le_of_lt hhpos) j)
    have h3 : 1 ≤ 1 + hh ^ (1 - α) + 2 / hh ^ α := by
      have h1 : 0 ≤ hh ^ (1 - α) := Real.rpow_nonneg (le_of_lt hhpos) _
      have h2 : 0 ≤ 2 / hh ^ α := div_nonneg (by norm_num) (Real.rpow_nonneg (le_of_lt hhpos) _)
      linarith
    have h5 : Kfac j * AA j / hh ^ j ≤ (Kfac j * AA j / hh ^ j) * (1 + hh ^ (1 - α) + 2 / hh ^ α) := by
      nlinarith [h4, h3]
    exact le_trans h5 (hCbig_single j hj)
  have hCbig_nn : 0 ≤ Cbig := by
    simp only [Cbig]
    have h1 : 0 ≤ ∑ i ∈ Finset.range (k + 1),
        (Kfac i * AA i / hh ^ i) * (1 + hh ^ (1 - α) + 2 / hh ^ α) :=
      Finset.sum_nonneg fun i hi =>
        hsummand2_nn i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    linarith
  have hCfin_pos : 0 < Cfin := by
    simp only [Cfin]; nlinarith [hm1pos, hCbig_nn]
  have hδ_M : ∀ j, j ≤ k → δ j ≤ M := by
    intro j hj
    have h1 : Kfac j * DD j ≤ M := hMge j hj
    have h2 : hh ^ ((k - j : ℕ) : ℝ) ≤ 1 :=
      Real.rpow_le_one (le_of_lt hhpos) hhle1 (Nat.cast_nonneg _)
    simp only [δ]
    calc Kfac j * DD j * hh ^ ((k - j : ℕ) : ℝ) ≤ (Kfac j * DD j) * 1 :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (hKfac_nn j) (hAD j hj).2.1)
      _ = Kfac j * DD j := mul_one _
      _ ≤ M := h1
  have hδ_le_t : ∀ j, j + 1 ≤ k → δ j ≤ M * target := by
    intro j hj
    have hjk : j ≤ k := by omega
    have h1 : Kfac j * DD j ≤ M := hMge j hjk
    have h2 : hh ^ ((k - j : ℕ) : ℝ) ≤ hh ^ (1 - α) := by
      refine Real.rpow_le_rpow_of_exponent_ge hhpos hhle1 ?_
      have h3 : (1 : ℝ) ≤ ((k - j : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ k - j by omega)
      linarith
    simp only [δ]
    calc Kfac j * DD j * hh ^ ((k - j : ℕ) : ℝ) ≤ M * hh ^ (1 - α) :=
          mul_le_mul h1 h2 (Real.rpow_nonneg (le_of_lt hhpos) _) (le_of_lt hMpos)
      _ ≤ M * target := mul_le_mul_of_nonneg_left hhrpow (le_of_lt hMpos)
  have hδ_div : ∀ j, j + 1 ≤ k → δ j / hh ^ α ≤ M * target := by
    intro j hj
    have hjk : j ≤ k := by omega
    have h1 : Kfac j * DD j ≤ M := hMge j hjk
    have h2 : hh ^ (((k - j : ℕ) : ℝ) - α) ≤ hh ^ (1 - α) := by
      refine Real.rpow_le_rpow_of_exponent_ge hhpos hhle1 ?_
      have h3 : (1 : ℝ) ≤ ((k - j : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ k - j by omega)
      linarith
    have hsplit : hh ^ ((k - j : ℕ) : ℝ) / hh ^ α = hh ^ (((k - j : ℕ) : ℝ) - α) := by
      rw [← Real.rpow_sub hhpos]
    simp only [δ]
    calc Kfac j * DD j * hh ^ ((k - j : ℕ) : ℝ) / hh ^ α
        = (Kfac j * DD j) * (hh ^ ((k - j : ℕ) : ℝ) / hh ^ α) := by ring
      _ = (Kfac j * DD j) * hh ^ (((k - j : ℕ) : ℝ) - α) := by rw [hsplit]
      _ ≤ M * target := by
          refine le_trans (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (le_of_lt hhpos) _)) ?_
          exact mul_le_mul_of_nonneg_left (le_trans h2 hhrpow) (le_of_lt hMpos)
  have hδ_next : ∀ j, j + 1 ≤ k → δ (j + 1) * hh ^ (1 - α) ≤ M * target := by
    intro j hj
    have h1 : δ (j + 1) ≤ M := hδ_M (j + 1) (by omega)
    exact mul_le_mul h1 hhrpow (Real.rpow_nonneg (le_of_lt hhpos) _) (le_of_lt hMpos)
  refine ⟨Cfin, hCfin_pos, ?_⟩
  intro w hw hfin
  set Ω : Set (Fin n → ℂ) := Work.CR.Flat.polydisc (0 : Fin n → ℂ) ρ with hΩdef
  set Ω' : Set (Fin n → ℂ) := Work.CR.Flat.polydisc (0 : Fin n → ℂ) ρ' with hΩ'def
  have hΩopen : IsOpen Ω := by rw [hΩdef]; exact Work.CR.Flat.isOpen_polydisc 0 ρ
  have hΩ'open : IsOpen Ω' := by rw [hΩ'def]; exact Work.CR.Flat.isOpen_polydisc 0 ρ'
  have hcvx : Convex ℝ Ω' := by rw [hΩ'def]; exact convex_polydisc_interp 0 ρ'
  have hfin' : Work.CR.Flat.holderNorm k α w Ω < ⊤ := by rw [hΩdef]; exact hfin
  have hNk_fin : Work.CR.Flat.iterDerivNorm k w Ω ≠ ⊤ :=
    ne_top_of_le_ne_top hfin'.ne (Work.CR.Flat.iterDerivNorm_le_holderNorm k α w Ω (le_refl k))
  have hN0_fin : Work.CR.Flat.iterDerivNorm 0 w Ω ≠ ⊤ :=
    ne_top_of_le_ne_top hfin'.ne (Work.CR.Flat.iterDerivNorm_le_holderNorm k α w Ω (Nat.zero_le k))
  set S0 : ℝ := (Work.CR.Flat.iterDerivNorm 0 w Ω).toReal with hS0def
  set Sk : ℝ := (Work.CR.Flat.iterDerivNorm k w Ω).toReal with hSkdef
  have hS0eq : ENNReal.ofReal S0 = Work.CR.Flat.iterDerivNorm 0 w Ω := by
    rw [hS0def]; exact ENNReal.ofReal_toReal hN0_fin
  have hSkeq : ENNReal.ofReal Sk = Work.CR.Flat.iterDerivNorm k w Ω := by
    rw [hSkdef]; exact ENNReal.ofReal_toReal hNk_fin
  have hS0nn : 0 ≤ S0 := by rw [hS0def]; exact ENNReal.toReal_nonneg
  have hSnn : 0 ≤ Sk := by rw [hSkdef]; exact ENNReal.toReal_nonneg
  have hS0b : ∀ y ∈ Ω, ‖w y‖ ≤ S0 := by
    intro y hy
    have h1 : ENNReal.ofReal ‖w y‖ ≤ Work.CR.Flat.iterDerivNorm 0 w Ω := by
      rw [Work.CR.Flat.iterDerivNorm_zero]
      exact le_iSup₂_of_le y hy le_rfl
    rw [← hS0eq] at h1
    exact (ENNReal.ofReal_le_ofReal_iff hS0nn).mp h1
  have hSkb : ∀ y ∈ Ω, ‖iteratedFDeriv ℝ k w y‖ ≤ Sk := by
    intro y hy
    have h1 : ENNReal.ofReal ‖iteratedFDerivWithin ℝ k w Ω y‖ ≤ Work.CR.Flat.iterDerivNorm k w Ω :=
      Work.CR.Flat.le_iterDerivNorm k w Ω hy
    have h2 : iteratedFDerivWithin ℝ k w Ω y = iteratedFDeriv ℝ k w y :=
      (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := w) (s := Ω) k hΩopen) hy
    rw [h2, ← hSkeq] at h1
    exact (ENNReal.ofReal_le_ofReal_iff hSnn).mp h1
  have hseg : ∀ (x v : Fin n → ℂ) (t : ℝ), x ∈ Ω' → ‖v‖ ≤ 1 → 0 ≤ t → t ≤ (k : ℝ) * hh →
      x + t • v ∈ Ω := by
    intro x v t hx hv ht0 htle
    rw [hΩ'def, Work.CR.Flat.mem_polydisc] at hx
    rw [hΩdef, Work.CR.Flat.mem_polydisc]
    intro i
    have hxi : ‖x i - (0 : Fin n → ℂ) i‖ < ρ' i := hx i
    have hvi : ‖v i‖ ≤ ‖v‖ := norm_le_pi_norm v i
    have htv : t * ‖v i‖ ≤ (k : ℝ) * hh := by nlinarith [ht0, htle, hvi, norm_nonneg (v i)]
    have hmem : t * ‖v i‖ ≤ ρ i - ρ' i := le_trans htv (le_trans hhled (hdle i))
    have hgoal : ‖x i + t • v i‖ < ρ i := by
      calc ‖x i + t • v i‖ ≤ ‖x i‖ + ‖t • v i‖ := norm_add_le _ _
        _ = ‖x i‖ + t * ‖v i‖ := by rw [norm_smul, Real.norm_of_nonneg ht0]
        _ < ρ i := by
            have : ‖x i‖ < ρ' i := by simpa using hxi
            linarith
    simpa only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, sub_zero] using hgoal
  have hdiffF : ∀ j, j < k → ∀ z : Fin n → ℂ,
      DifferentiableAt ℝ (fun y => iteratedFDeriv ℝ j w y) z := fun j hj z =>
    (hw.differentiable_iteratedFDeriv (m := j) (by exact_mod_cast hj)).differentiableAt
  have hpoint : ∀ j, j ≤ k → ∀ x, x ∈ Ω' →
      ‖iteratedFDeriv ℝ j w x‖ ≤ δ j * Sk + c j * S0 := by
    intro j hj x hx
    have hsym : ∀ (σ : Equiv.Perm (Fin j)) (v : Fin j → (Fin n → ℂ)),
        iteratedFDeriv ℝ j w x (v ∘ σ) = iteratedFDeriv ℝ j w x v :=
      fun σ v => iteratedFDeriv_comp_perm_of_contDiffAt (hw.contDiffAt) hj v σ
    have hdiag : ∀ v : Fin n → ℂ, ‖v‖ ≤ 1 →
        ‖iteratedFDeriv ℝ j w x (fun _ => v)‖ ≤ AA j / hh ^ j * S0 + DD j * hh ^ (k - j) * Sk := by
      intro v hv
      have hb1 : ∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) * hh), ‖w (x + t • v)‖ ≤ S0 := by
        intro t ht
        exact hS0b _ (hseg x v t hx hv ht.1 ht.2)
      have hb2 : ∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) * hh),
          ‖iteratedDeriv k (fun s : ℝ => w (x + s • v)) t‖ ≤ Sk := by
        intro t ht
        rw [iteratedDeriv_slice_gen (n := k) hw x v t]
        have hmem : x + t • v ∈ Ω := hseg x v t hx hv ht.1 ht.2
        calc ‖iteratedFDeriv ℝ k w (x + t • v) (fun _ => v)‖
            ≤ ‖iteratedFDeriv ℝ k w (x + t • v)‖ := by
              refine le_trans (ContinuousMultilinearMap.le_opNorm _ _) ?_
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
              calc ‖iteratedFDeriv ℝ k w (x + t • v)‖ * ‖v‖ ^ k
                  ≤ ‖iteratedFDeriv ℝ k w (x + t • v)‖ * 1 := by
                    gcongr
                    exact pow_le_one₀ (norm_nonneg v) hv
                _ = ‖iteratedFDeriv ℝ k w (x + t • v)‖ := mul_one _
          _ ≤ Sk := hSkb _ hmem
      have hslice : iteratedDeriv j (fun s : ℝ => w (x + s • v)) 0
          = iteratedFDeriv ℝ j w x (fun _ => v) := by
        simpa using iteratedDeriv_slice_gen (n := j) (hw.of_le (by exact_mod_cast hj)) x v 0
      rw [← hslice]
      exact (hAD j hj).2.2 (fun s : ℝ => w (x + s • v)) hh hhpos (hw.comp (by fun_prop))
        S0 Sk hS0nn hSnn hb1 hb2
    refine le_trans (Work.CR.Flat.Cauchy.norm_continuousMultilinearMap_le_of_diagonal
      (iteratedFDeriv ℝ j w x) hsym (D := AA j / hh ^ j * S0 + DD j * hh ^ (k - j) * Sk) hdiag) ?_
    have hconv : (j : ℝ) ^ j / (j.factorial : ℝ) * (AA j / hh ^ j * S0 + DD j * hh ^ (k - j) * Sk)
        = δ j * Sk + c j * S0 := by
      simp only [δ, c, Kfac]
      rw [← Real.rpow_natCast hh (k - j)]
      ring
    exact le_of_eq hconv
  set Nk : ℝ≥0∞ := Work.CR.Flat.holderNorm k α w Ω with hNkdef
  set N0 : ℝ≥0∞ := Work.CR.Flat.holderNorm 0 α w Ω with hN0def
  have hNk_le : Work.CR.Flat.iterDerivNorm k w Ω ≤ Nk := by
    rw [hNkdef]; exact Work.CR.Flat.iterDerivNorm_le_holderNorm k α w Ω (le_refl k)
  have hN0_le : Work.CR.Flat.iterDerivNorm 0 w Ω ≤ N0 := by
    rw [hN0def]; exact Work.CR.Flat.iterDerivNorm_le_holderNorm 0 α w Ω (le_refl 0)
  have hN : ∀ j, j ≤ m → Work.CR.Flat.iterDerivNorm j w Ω'
      ≤ ENNReal.ofReal (δ j) * Nk + ENNReal.ofReal (c j) * N0 := by
    intro j hj
    have hjk : j ≤ k := le_trans hj (le_of_lt hmk)
    rw [Work.CR.Flat.iterDerivNorm]
    refine iSup₂_le fun x hx => ?_
    have hid : iteratedFDerivWithin ℝ j w Ω' x = iteratedFDeriv ℝ j w x :=
      (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := w) (s := Ω') j hΩ'open) hx
    rw [hid]
    calc ENNReal.ofReal ‖iteratedFDeriv ℝ j w x‖
        ≤ ENNReal.ofReal (δ j * Sk + c j * S0) := ENNReal.ofReal_le_ofReal (hpoint j hjk x hx)
      _ = ENNReal.ofReal (δ j) * ENNReal.ofReal Sk + ENNReal.ofReal (c j) * ENNReal.ofReal S0 := by
          rw [ENNReal.ofReal_add (mul_nonneg (hδnn j hjk) hSnn) (mul_nonneg (hcnn j hjk) hS0nn),
            ENNReal.ofReal_mul (hδnn j hjk), ENNReal.ofReal_mul (hcnn j hjk)]
      _ = ENNReal.ofReal (δ j) * Work.CR.Flat.iterDerivNorm k w Ω
            + ENNReal.ofReal (c j) * Work.CR.Flat.iterDerivNorm 0 w Ω := by
          rw [hSkeq, hS0eq]
      _ ≤ ENNReal.ofReal (δ j) * Nk + ENNReal.ofReal (c j) * N0 := by
          gcongr <;> assumption
  have hcoefk_nn : ∀ j, j + 1 ≤ k → 0 ≤ δ (j + 1) * hh ^ (1 - α) + 2 * δ j / hh ^ α := by
    intro j hjk
    have h1 : 0 ≤ δ (j+1) * hh ^ (1-α) :=
      mul_nonneg (hδnn (j+1) hjk) (Real.rpow_nonneg (le_of_lt hhpos) _)
    have h2 : 0 ≤ 2 * δ j / hh ^ α :=
      div_nonneg (mul_nonneg (by norm_num) (hδnn j (by omega))) (Real.rpow_nonneg (le_of_lt hhpos) _)
    linarith
  have hcoef0_nn : ∀ j, j + 1 ≤ k → 0 ≤ c (j + 1) * hh ^ (1 - α) + 2 * c j / hh ^ α := by
    intro j hjk
    have h1 : 0 ≤ c (j+1) * hh ^ (1-α) :=
      mul_nonneg (hcnn (j+1) hjk) (Real.rpow_nonneg (le_of_lt hhpos) _)
    have h2 : 0 ≤ 2 * c j / hh ^ α :=
      div_nonneg (mul_nonneg (by norm_num) (hcnn j (by omega))) (Real.rpow_nonneg (le_of_lt hhpos) _)
    linarith
  have hH : ∀ j, j ≤ m → Work.CR.Flat.holderSeminorm j α w Ω'
      ≤ ENNReal.ofReal (δ (j+1) * hh ^ (1-α) + 2 * δ j / hh ^ α) * Nk
        + ENNReal.ofReal (c (j+1) * hh ^ (1-α) + 2 * c j / hh ^ α) * N0 := by
    intro j hj
    have hjk : j ≤ k := le_trans hj (le_of_lt hmk)
    have hj1k : j + 1 ≤ k := by omega
    rw [Work.CR.Flat.holderSeminorm]
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    have hx' : x ∈ Ω' := hx
    have hy' : y ∈ Ω' := hy
    have hxid : iteratedFDerivWithin ℝ j w Ω' x = iteratedFDeriv ℝ j w x :=
      (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := w) (s := Ω') j hΩ'open) hx
    have hyid : iteratedFDerivWithin ℝ j w Ω' y = iteratedFDeriv ℝ j w y :=
      (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := w) (s := Ω') j hΩ'open) hy
    rw [hxid, hyid]
    have hreal : ‖iteratedFDeriv ℝ j w x - iteratedFDeriv ℝ j w y‖ / ‖x - y‖ ^ α
        ≤ (δ (j+1) * hh ^ (1-α) + 2 * δ j / hh ^ α) * Sk
          + (c (j+1) * hh ^ (1-α) + 2 * c j / hh ^ α) * S0 := by
      have hxi : ‖iteratedFDeriv ℝ j w x‖ ≤ δ j * Sk + c j * S0 := hpoint j hjk x hx'
      have hyi : ‖iteratedFDeriv ℝ j w y‖ ≤ δ j * Sk + c j * S0 := hpoint j hjk y hy'
      have hzi : ∀ z ∈ Ω', ‖iteratedFDeriv ℝ (j+1) w z‖ ≤ δ (j+1) * Sk + c (j+1) * S0 :=
        fun z hz => hpoint (j+1) hj1k z hz
      have hxyn : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      by_cases hc : ‖x - y‖ ≤ hh
      · have hlip := hcvx.norm_image_sub_le_of_norm_fderiv_le
            (f := fun z => iteratedFDeriv ℝ j w z) (C := δ (j+1) * Sk + c (j+1) * S0)
            (fun z _ => hdiffF j (by omega) z)
            (fun z hz => by rw [norm_fderiv_iteratedFDeriv]; exact hzi z hz) hx' hy'
        have hpow : ‖x - y‖ / ‖x - y‖ ^ α = ‖x - y‖ ^ (1 - α) := by
          have h := Real.rpow_sub hxyn (1 : ℝ) α
          rw [Real.rpow_one] at h
          exact h.symm
        have hmono : ‖x - y‖ ^ (1 - α) ≤ hh ^ (1 - α) :=
          Real.rpow_le_rpow (norm_nonneg _) hc hα1'.le
        have hCnn : 0 ≤ δ (j+1) * Sk + c (j+1) * S0 := by
          have h1 := hδnn (j+1) hj1k; have h2 := hcnn (j+1) hj1k
          nlinarith [hSnn, hS0nn]
        calc ‖iteratedFDeriv ℝ j w x - iteratedFDeriv ℝ j w y‖ / ‖x - y‖ ^ α
            = ‖iteratedFDeriv ℝ j w y - iteratedFDeriv ℝ j w x‖ / ‖x - y‖ ^ α := by
              rw [norm_sub_rev (iteratedFDeriv ℝ j w x) (iteratedFDeriv ℝ j w y)]
          _ ≤ ((δ (j+1) * Sk + c (j+1) * S0) * ‖y - x‖) / ‖x - y‖ ^ α :=
              div_le_div_of_nonneg_right hlip (Real.rpow_nonneg (norm_nonneg _) _)
          _ = (δ (j+1) * Sk + c (j+1) * S0) * (‖x - y‖ / ‖x - y‖ ^ α) := by
              rw [norm_sub_rev y x]; ring
          _ = (δ (j+1) * Sk + c (j+1) * S0) * ‖x - y‖ ^ (1 - α) := by rw [hpow]
          _ ≤ (δ (j+1) * Sk + c (j+1) * S0) * hh ^ (1 - α) :=
              mul_le_mul_of_nonneg_left hmono hCnn
          _ ≤ (δ (j+1) * hh ^ (1-α) + 2 * δ j / hh ^ α) * Sk
              + (c (j+1) * hh ^ (1-α) + 2 * c j / hh ^ α) * S0 := by
              have h1 : 0 ≤ δ j / hh ^ α :=
                div_nonneg (hδnn j hjk) (Real.rpow_nonneg (le_of_lt hhpos) _)
              have h2 : 0 ≤ c j / hh ^ α :=
                div_nonneg (hcnn j hjk) (Real.rpow_nonneg (le_of_lt hhpos) _)
              have h3 : 0 ≤ δ (j+1) * hh ^ (1-α) :=
                mul_nonneg (hδnn (j+1) hj1k) (Real.rpow_nonneg (le_of_lt hhpos) _)
              have h4 : 0 ≤ c (j+1) * hh ^ (1-α) :=
                mul_nonneg (hcnn (j+1) hj1k) (Real.rpow_nonneg (le_of_lt hhpos) _)
              have h5 : 0 ≤ (2 * δ j / hh ^ α) * Sk :=
                mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (hδnn j hjk))
                  (Real.rpow_nonneg (le_of_lt hhpos) _)) hSnn
              have h6 : 0 ≤ (2 * c j / hh ^ α) * S0 :=
                mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (hcnn j hjk))
                  (Real.rpow_nonneg (le_of_lt hhpos) _)) hS0nn
              nlinarith [h3, h4, h5, h6]
      · push_neg at hc
        have hpow : hh ^ α < ‖x - y‖ ^ α := Real.rpow_lt_rpow (le_of_lt hhpos) hc hα0
        have hpos : 0 < hh ^ α := Real.rpow_pos_of_pos hhpos _
        have h2 : ‖iteratedFDeriv ℝ j w x - iteratedFDeriv ℝ j w y‖ ≤ 2 * (δ j * Sk + c j * S0) := by
          have h := norm_sub_le (iteratedFDeriv ℝ j w x) (iteratedFDeriv ℝ j w y)
          linarith
        have heq : (2 * (δ j * Sk + c j * S0)) / hh ^ α
            = (2 * δ j / hh ^ α) * Sk + (2 * c j / hh ^ α) * S0 := by ring
        have h2nn : 0 ≤ 2 * (δ j * Sk + c j * S0) := by
          have h1 := hδnn j hjk; have h3 := hcnn j hjk
          nlinarith [hSnn, hS0nn]
        calc ‖iteratedFDeriv ℝ j w x - iteratedFDeriv ℝ j w y‖ / ‖x - y‖ ^ α
            ≤ (2 * (δ j * Sk + c j * S0)) / ‖x - y‖ ^ α :=
              div_le_div_of_nonneg_right h2 (Real.rpow_nonneg (norm_nonneg _) _)
          _ ≤ (2 * (δ j * Sk + c j * S0)) / hh ^ α :=
              div_le_div_of_nonneg_left h2nn hpos hpow.le
          _ = (2 * δ j / hh ^ α) * Sk + (2 * c j / hh ^ α) * S0 := heq
          _ ≤ (δ (j+1) * hh ^ (1-α) + 2 * δ j / hh ^ α) * Sk
              + (c (j+1) * hh ^ (1-α) + 2 * c j / hh ^ α) * S0 := by
              have h1 : 0 ≤ δ (j+1) * hh ^ (1-α) :=
                mul_nonneg (hδnn (j+1) hj1k) (Real.rpow_nonneg (le_of_lt hhpos) _)
              have h2 : 0 ≤ c (j+1) * hh ^ (1-α) :=
                mul_nonneg (hcnn (j+1) hj1k) (Real.rpow_nonneg (le_of_lt hhpos) _)
              nlinarith [hSnn, hS0nn, h1, h2]
    refine le_trans (ENNReal.ofReal_le_ofReal hreal) ?_
    have h1 : ENNReal.ofReal ((δ (j+1) * hh ^ (1-α) + 2 * δ j / hh ^ α) * Sk
        + (c (j+1) * hh ^ (1-α) + 2 * c j / hh ^ α) * S0)
        = ENNReal.ofReal (δ (j+1) * hh ^ (1-α) + 2 * δ j / hh ^ α) * ENNReal.ofReal Sk
          + ENNReal.ofReal (c (j+1) * hh ^ (1-α) + 2 * c j / hh ^ α) * ENNReal.ofReal S0 := by
      rw [ENNReal.ofReal_add (mul_nonneg (hcoefk_nn j hj1k) hSnn)
            (mul_nonneg (hcoef0_nn j hj1k) hS0nn),
          ENNReal.ofReal_mul (hcoefk_nn j hj1k), ENNReal.ofReal_mul (hcoef0_nn j hj1k)]
    rw [h1, hSkeq, hS0eq]
    gcongr <;> assumption
  have hDk_le : ∀ j, j ≤ m → δ j + (δ (j+1) * hh ^ (1-α) + 2 * δ j / hh ^ α) ≤ 4 * (M * target) := by
    intro j hj
    have hj1k : j + 1 ≤ k := by omega
    have h1 := hδ_le_t j hj1k
    have h2 := hδ_next j hj1k
    have h3 := hδ_div j hj1k
    have h4 : 2 * δ j / hh ^ α ≤ 2 * (M * target) := by
      rw [show 2 * δ j / hh ^ α = 2 * (δ j / hh ^ α) by ring]
      exact mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 2)
    calc δ j + (δ (j+1) * hh ^ (1-α) + 2 * δ j / hh ^ α)
        ≤ M * target + (M * target + 2 * (M * target)) := by linarith [h1, h2, h4]
      _ = 4 * (M * target) := by ring
  have hDk_sum : ∑ j ∈ Finset.range (m+1),
      (δ j + (δ (j+1) * hh ^ (1-α) + 2 * δ j / hh ^ α)) ≤ ε := by
    have h1 : ∑ j ∈ Finset.range (m+1), (δ j + (δ (j+1) * hh ^ (1-α) + 2 * δ j / hh ^ α))
        ≤ ∑ _j ∈ Finset.range (m+1), (4 * (M * target)) :=
      Finset.sum_le_sum (fun j hj => hDk_le j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
    have h2 : ∑ _j ∈ Finset.range (m+1), (4 * (M * target)) = ((m : ℝ) + 1) * (4 * (M * target)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    have h3 : ((m : ℝ) + 1) * (4 * (M * target)) = ε / 4 := by
      have hMne : M ≠ 0 := ne_of_gt hMpos
      have hmne : (m : ℝ) + 1 ≠ 0 := ne_of_gt hm1pos
      simp only [target]
      field_simp
      ring
    rw [h2, h3] at h1
    linarith [hε]
  have hD0_le : ∀ j, j ≤ m → c j + (c (j+1) * hh ^ (1-α) + 2 * c j / hh ^ α) ≤ 3 * Cbig := by
    intro j hj
    have hjk : j ≤ k := le_trans hj (le_of_lt hmk)
    have hj1k : j + 1 ≤ k := by omega
    have h1 : c j ≤ Cbig := hKfacAA j hjk
    have h2 : c (j+1) * hh ^ (1-α) ≤ Cbig := by
      have hnn : 0 ≤ Kfac (j+1) * AA (j+1) / hh ^ (j+1) :=
        div_nonneg (mul_nonneg (hKfac_nn (j+1)) (hAD (j+1) hj1k).1)
          (pow_nonneg (le_of_lt hhpos) (j+1))
      have hle : hh ^ (1-α) ≤ 1 + hh ^ (1-α) + 2 / hh ^ α := by
        have h2 : 0 ≤ hh ^ (1 - α) := Real.rpow_nonneg (le_of_lt hhpos) _
        have h3 : 0 ≤ 2 / hh ^ α := div_nonneg (by norm_num) (Real.rpow_nonneg (le_of_lt hhpos) _)
        linarith
      simp only [c]
      calc Kfac (j+1) * AA (j+1) / hh ^ (j+1) * hh ^ (1-α)
          = (Kfac (j+1) * AA (j+1) / hh ^ (j+1)) * hh ^ (1-α) := by ring
        _ ≤ (Kfac (j+1) * AA (j+1) / hh ^ (j+1)) * (1 + hh ^ (1-α) + 2 / hh ^ α) :=
            mul_le_mul_of_nonneg_left hle hnn
        _ ≤ Cbig := hCbig_single (j+1) hj1k
    have h3 : 2 * c j / hh ^ α ≤ Cbig := by
      have hnn : 0 ≤ Kfac j * AA j / hh ^ j :=
        div_nonneg (mul_nonneg (hKfac_nn j) (hAD j hjk).1) (pow_nonneg (le_of_lt hhpos) j)
      have hle : 2 / hh ^ α ≤ 1 + hh ^ (1-α) + 2 / hh ^ α := by
        have h2 : 0 ≤ hh ^ (1 - α) := Real.rpow_nonneg (le_of_lt hhpos) _
        linarith
      simp only [c]
      calc 2 * (Kfac j * AA j / hh ^ j) / hh ^ α
          = (Kfac j * AA j / hh ^ j) * (2 / hh ^ α) := by ring
        _ ≤ (Kfac j * AA j / hh ^ j) * (1 + hh ^ (1-α) + 2 / hh ^ α) :=
            mul_le_mul_of_nonneg_left hle hnn
        _ ≤ Cbig := hCbig_single j hjk
    linarith
  have hD0_sum : ∑ j ∈ Finset.range (m+1),
      (c j + (c (j+1) * hh ^ (1-α) + 2 * c j / hh ^ α)) ≤ Cfin := by
    have h1 : ∑ j ∈ Finset.range (m+1), (c j + (c (j+1) * hh ^ (1-α) + 2 * c j / hh ^ α))
        ≤ ∑ _j ∈ Finset.range (m+1), (3 * Cbig) :=
      Finset.sum_le_sum (fun j hj => hD0_le j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
    have h2 : ∑ _j ∈ Finset.range (m+1), (3 * Cbig) = ((m : ℝ) + 1) * (3 * Cbig) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    have h3 : ((m : ℝ) + 1) * (3 * Cbig) ≤ Cfin := by
      simp only [Cfin]; nlinarith [hCbig_nn]
    linarith
  have hDk_nn : ∀ j, j + 1 ≤ k → 0 ≤ δ j + (δ (j+1) * hh ^ (1-α) + 2 * δ j / hh ^ α) := by
    intro j hj1k
    have h1 : 0 ≤ δ (j+1) * hh ^ (1-α) :=
      mul_nonneg (hδnn (j+1) hj1k) (Real.rpow_nonneg (le_of_lt hhpos) _)
    have h2 : 0 ≤ 2 * δ j / hh ^ α :=
      div_nonneg (mul_nonneg (by norm_num) (hδnn j (by omega))) (Real.rpow_nonneg (le_of_lt hhpos) _)
    have h3 : 0 ≤ δ j := hδnn j (by omega)
    linarith
  have hD0_nn : ∀ j, j + 1 ≤ k → 0 ≤ c j + (c (j+1) * hh ^ (1-α) + 2 * c j / hh ^ α) := by
    intro j hj1k
    have h1 : 0 ≤ c (j+1) * hh ^ (1-α) :=
      mul_nonneg (hcnn (j+1) hj1k) (Real.rpow_nonneg (le_of_lt hhpos) _)
    have h2 : 0 ≤ 2 * c j / hh ^ α :=
      div_nonneg (mul_nonneg (by norm_num) (hcnn j (by omega))) (Real.rpow_nonneg (le_of_lt hhpos) _)
    have h3 : 0 ≤ c j := hcnn j (by omega)
    linarith
  have hfinal : ∑ j ∈ Finset.range (m+1),
      (Work.CR.Flat.iterDerivNorm j w Ω' + Work.CR.Flat.holderSeminorm j α w Ω')
      ≤ ENNReal.ofReal ε * Nk + ENNReal.ofReal Cfin * N0 := by
    have hstep1 : ∑ j ∈ Finset.range (m+1),
        (Work.CR.Flat.iterDerivNorm j w Ω' + Work.CR.Flat.holderSeminorm j α w Ω')
        ≤ ∑ j ∈ Finset.range (m+1),
            (ENNReal.ofReal (δ j + (δ (j+1) * hh ^ (1-α) + 2 * δ j / hh ^ α)) * Nk
              + ENNReal.ofReal (c j + (c (j+1) * hh ^ (1-α) + 2 * c j / hh ^ α)) * N0) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hjk : j ≤ k := le_trans hjm (le_of_lt hmk)
      have hj1k : j + 1 ≤ k := by omega
      calc Work.CR.Flat.iterDerivNorm j w Ω' + Work.CR.Flat.holderSeminorm j α w Ω'
          ≤ (ENNReal.ofReal (δ j) * Nk + ENNReal.ofReal (c j) * N0)
            + (ENNReal.ofReal (δ (j+1) * hh ^ (1-α) + 2 * δ j / hh ^ α) * Nk
               + ENNReal.ofReal (c (j+1) * hh ^ (1-α) + 2 * c j / hh ^ α) * N0) :=
            add_le_add (hN j hjm) (hH j hjm)
        _ = ENNReal.ofReal (δ j + (δ (j+1) * hh ^ (1-α) + 2 * δ j / hh ^ α)) * Nk
            + ENNReal.ofReal (c j + (c (j+1) * hh ^ (1-α) + 2 * c j / hh ^ α)) * N0 := by
            rw [ENNReal.ofReal_add (hδnn j hjk) (hcoefk_nn j hj1k),
              ENNReal.ofReal_add (hcnn j hjk) (hcoef0_nn j hj1k)]
            ring
    have hstep2 : ∑ j ∈ Finset.range (m+1),
            (ENNReal.ofReal (δ j + (δ (j+1) * hh ^ (1-α) + 2 * δ j / hh ^ α)) * Nk
              + ENNReal.ofReal (c j + (c (j+1) * hh ^ (1-α) + 2 * c j / hh ^ α)) * N0)
        = (∑ j ∈ Finset.range (m+1),
              ENNReal.ofReal (δ j + (δ (j+1) * hh ^ (1-α) + 2 * δ j / hh ^ α))) * Nk
          + (∑ j ∈ Finset.range (m+1),
              ENNReal.ofReal (c j + (c (j+1) * hh ^ (1-α) + 2 * c j / hh ^ α))) * N0 := by
      rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
    refine le_trans hstep1 (le_trans (le_of_eq hstep2) ?_)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j hj => hDk_nn j (by
          have := Finset.mem_range.mp hj; omega)),
        ← ENNReal.ofReal_sum_of_nonneg (fun j hj => hD0_nn j (by
          have := Finset.mem_range.mp hj; omega))]
    refine add_le_add ?_ ?_ <;> gcongr
  rw [Work.CR.Flat.holderNorm]
  exact hfinal

end Work.NN.Core
