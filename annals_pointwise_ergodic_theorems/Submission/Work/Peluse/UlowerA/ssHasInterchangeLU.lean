import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.interchangeLDefs
import Submission.Work.Peluse.UlowerA.Defs
import Submission.Work.Peluse.Ulower.StepLe.hypoMass_sl
import Submission.Work.Peluse.Ulower.StepLe.concMass_sl
import Submission.Work.Peluse.Ulower.thetaSet_card_ge

set_option maxHeartbeats 1600000

namespace Work.Peluse.Ulower.StepLe

noncomputable section

open scoped BigOperators
open Work.Peluse

/-- `x ∉ symIcc L ↔ L < x.natAbs`. -/
private lemma notMem_symIcc_iff_ss {L : ℕ} {x : ℤ} :
    x ∉ Work.Peluse.symIcc L ↔ L < x.natAbs := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    exact h ⟨by omega, by omega⟩
  · rintro h ⟨h1, h2⟩
    have h3 : |x| ≤ (L : ℤ) := abs_le.mpr ⟨h1, h2⟩
    rw [Int.abs_eq_natAbs] at h3
    have h4 : x.natAbs ≤ L := by exact_mod_cast h3
    omega

/-- Markov/level-set extraction. -/
private theorem filter_card_ge_of_sum_sq {α : Type*} [DecidableEq α] (Θ : Finset α) (X : α → ℝ)
    {A S θ : ℝ} (hX0 : ∀ k, 0 ≤ X k) (hA0 : 0 ≤ A) (hS1 : 1 ≤ S) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hSum : A ≤ ∑ k ∈ Θ, (X k) ^ 2) (hUni : ∀ k ∈ Θ, X k ≤ S)
    (hKey : θ * (Θ.card : ℝ) ≤ A / (2 * S ^ 2)) :
    A / (2 * S ^ 2) ≤ ((Θ.filter (fun k => θ ≤ X k)).card : ℝ) := by
  classical
  set H₂ : Finset α := Θ.filter (fun k => θ ≤ X k) with hH₂
  have hSpos : (0:ℝ) < S := lt_of_lt_of_le zero_lt_one hS1
  have hS2pos : (0:ℝ) < S ^ 2 := by positivity
  have h2S2pos : (0:ℝ) < 2 * S ^ 2 := by positivity
  have hH₂sub : H₂ ⊆ Θ := by rw [hH₂]; exact Finset.filter_subset _ _
  have hsplit : (∑ k ∈ Θ, (X k) ^ 2) = (∑ k ∈ H₂, (X k) ^ 2) + (∑ k ∈ Θ \ H₂, (X k) ^ 2) := by
    rw [← Finset.sum_sdiff hH₂sub, add_comm]
  have hle1 : (∑ k ∈ H₂, (X k) ^ 2) ≤ (H₂.card : ℝ) * S ^ 2 := by
    calc (∑ k ∈ H₂, (X k) ^ 2) ≤ ∑ _k ∈ H₂, S ^ 2 := by
          refine Finset.sum_le_sum fun k hk => ?_
          exact pow_le_pow_left₀ (hX0 k) (hUni k (hH₂sub hk)) 2
      _ = (H₂.card : ℝ) * S ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hle2 : (∑ k ∈ Θ \ H₂, (X k) ^ 2) ≤ (Θ.card : ℝ) * θ ^ 2 := by
    calc (∑ k ∈ Θ \ H₂, (X k) ^ 2) ≤ ∑ _k ∈ Θ \ H₂, θ ^ 2 := by
          refine Finset.sum_le_sum fun k hk => ?_
          obtain ⟨hkΘ, hkH⟩ := Finset.mem_sdiff.mp hk
          have hlt : X k < θ := by
            by_contra hc
            exact hkH (by rw [hH₂]; exact Finset.mem_filter.mpr ⟨hkΘ, not_lt.mp hc⟩)
          nlinarith [hX0 k, hlt, hθ0]
      _ = ((Θ \ H₂).card : ℝ) * θ ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Θ.card : ℝ) * θ ^ 2 := by
          have hle : ((Θ \ H₂).card : ℝ) ≤ (Θ.card : ℝ) := by
            exact_mod_cast Finset.card_le_card Finset.sdiff_subset
          exact mul_le_mul_of_nonneg_right hle (by positivity)
  have hbound : A ≤ (H₂.card : ℝ) * S ^ 2 + (Θ.card : ℝ) * θ ^ 2 :=
    le_trans hSum (le_trans (le_of_eq hsplit) (add_le_add hle1 hle2))
  have hθcard : (Θ.card : ℝ) * θ ^ 2 ≤ A / 2 := by
    have h1 : (Θ.card : ℝ) * θ ^ 2 = θ * (θ * (Θ.card : ℝ)) := by ring
    rw [h1]
    calc θ * (θ * (Θ.card : ℝ)) ≤ θ * (A / (2 * S ^ 2)) := mul_le_mul_of_nonneg_left hKey hθ0
      _ ≤ 1 * (A / (2 * S ^ 2)) := mul_le_mul_of_nonneg_right hθ1 (by positivity)
      _ = A / (2 * S ^ 2) := one_mul _
      _ ≤ A / 2 := by
          apply div_le_div_of_nonneg_left hA0 (by norm_num)
          nlinarith [hS1]
  have hfinal : A / 2 ≤ (H₂.card : ℝ) * S ^ 2 := by linarith
  rw [div_le_iff₀ h2S2pos]
  nlinarith [hfinal]

/-- The uniform bound on the terms of the conclusion of `HasInterchangeL`. -/
private theorem conclTerm_le_of_mem_ThetaSet {σ N D B : ℕ} (hB : 1 ≤ B) (hN : 1 ≤ N) (hD : 1 ≤ D)
    (hDB : D ≤ B) (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ)
    (hb0 : ∀ x : ℤ, ‖f₀ x‖ ≤ 1) (hb1 : ∀ x : ℤ, ‖f₁ x‖ ≤ 1)
    (hs0 : Work.Peluse.SupportIn f₀ B) (hs1 : Work.Peluse.SupportIn f₁ B)
    (H₁ : Finset ((Fin σ → ℤ) × (Fin σ → ℤ))) (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ)
    (k : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ))
    (hk : k ∈ Work.Peluse.Ulower.ThetaSet σ D H₁) :
    ‖((B : ℂ))⁻¹ * ∑' x : ℤ,
        sliceDual σ N P f₀ f₁ (fun i => (k.2.1 i, k.2.2 i)) x *
          Complex.exp (2 * Real.pi * Complex.I * (mixedPhase β k : ℂ) * (x : ℂ))‖
      ≤ 3 + 4 * (σ : ℝ) := by
  have hmem : k ∈ (Fintype.piFinset (fun _ : Fin σ => Finset.Icc (1:ℤ) (D:ℤ))).product
      ((Fintype.piFinset (fun _ : Fin σ => Finset.Icc (1:ℤ) (D:ℤ))).product
        (Fintype.piFinset (fun _ : Fin σ => Finset.Icc (1:ℤ) (D:ℤ)))) :=
    (Finset.mem_filter.mp hk).1
  have h23 := (Finset.mem_product.mp hmem).2
  have hk2 : k.2.1 ∈ Work.Peluse.Ulower.thetaBox σ D := (Finset.mem_product.mp h23).1
  have hk3 : k.2.2 ∈ Work.Peluse.Ulower.thetaBox σ D := (Finset.mem_product.mp h23).2
  have hk2' : ∀ i : Fin σ, k.2.1 i ∈ Finset.Icc (1:ℤ) (D:ℤ) := by
    rw [Work.Peluse.Ulower.mem_thetaBox] at hk2; exact hk2
  have hk3' : ∀ i : Fin σ, k.2.2 i ∈ Finset.Icc (1:ℤ) (D:ℤ) := by
    rw [Work.Peluse.Ulower.mem_thetaBox] at hk3; exact hk3
  have hsh : ∀ i : Fin σ, |(k.2.1 i)| ≤ (D : ℤ) ∧ |(k.2.2 i)| ≤ (D : ℤ) := by
    intro i
    have h1 := Finset.mem_Icc.mp (hk2' i)
    have h2 := Finset.mem_Icc.mp (hk3' i)
    exact ⟨by rw [abs_of_nonneg (by omega : (0:ℤ) ≤ k.2.1 i)]; exact h1.2,
           by rw [abs_of_nonneg (by omega : (0:ℤ) ≤ k.2.2 i)]; exact h2.2⟩
  have hs0' : ∀ x : ℤ, x ∉ Work.Peluse.symIcc B → f₀ x = 0 :=
    fun x hx => hs0 x (notMem_symIcc_iff_ss.mp hx)
  have hs1' : ∀ x : ℤ, x ∉ Work.Peluse.symIcc B → f₁ x = 0 :=
    fun x hx => hs1 x (notMem_symIcc_iff_ss.mp hx)
  have h := Work.Peluse.Ulower.conclTerm_uniform_bound (σ := σ) (M := N) (L := B) (D := D)
    hB hN hDB P f₀ f₁ hb0 hb1 hs0' hs1' (fun i : Fin σ => (k.2.1 i, k.2.2 i)) hsh
    (mixedPhase β k)
  simpa [sliceDual] using h

/-
**The mass-form route to the target's interchange interface.**

`Work.Peluse.Ulower.StepLe.SharpMassDDI σ` is the *mass* form of Peluse's Lemma 7.4.  Its
induction (`d_σ = σ(2^{σ+1}-3)`) is the cleanest known route to the crux `ss74.ddiCore`, so this
file turns it into the lossy pointwise interface `HasInterchangeL` that `StepLe.blindConvertK2`
consumes.

Route: the slice family `G z = sl P f₀ f₁ (z+1)` over `Z = Fin N` has `E_z G z = dualFn N P f₀ f₁`
(`hypoMass_sl`) and `E_z ct(k.2.1,k.2.2)(G z) = sliceDual σ N P f₀ f₁ (k.2.1,k.2.2)` (`concMass_sl`),
so `SharpMassDDI` reads `C⁻¹ (hypoMass)^{2^σ}/D^{d_σ} ≤ concMass`, with
`hypoMass ≥ η² γ D^{2σ}` and `concMass = ∑_{k∈Θ} ‖·‖²`.  Markov on `Θ_σ(H₁)` with the uniform bound
`‖B⁻¹Σ_x sliceDual·e‖ ≤ 3 + 4σ` extracts `H₂ ⊆ Θ_σ(H₁)` with density and level `c(ηγD/B)^{Ki}`,
`Ki = 2^{σ+1}`: the `D`-powers cancel exactly (`2σ·2^σ - d_σ - 3σ = 0`) and the remaining
comparison `(ηγ)^{2^{σ+1}} ≥ (η²γ)^{2^σ}` uses `γ ≤ 1`.
-/
theorem hasInterchangeLU_int {P : Polynomial ℤ}
    (h : ∀ σ : ℕ, 1 ≤ σ → Work.Peluse.Ulower.StepLe.SharpMassDDI σ) :
    ∀ C₀ : ℕ, 1 ≤ C₀ → Work.Peluse.UlowerA.HasInterchangeLU P C₀ := by
  intro C₀ hC₀
  classical
  intro σ hσ K₀ hK₀
  obtain ⟨C, hCpos, hC⟩ := h σ hσ
  let Ki : ℕ := 2 ^ (σ + 1)
  let S : ℝ := 3 + 4 * (σ : ℝ)
  let c : ℝ := min 1 (C⁻¹ / (2 * S ^ 2 * K₀ ^ Ki))
  have hCp : 0 < C⁻¹ := inv_pos.mpr hCpos
  have hS1 : (1:ℝ) ≤ S := by
    show (1:ℝ) ≤ 3 + 4 * (σ : ℝ)
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) σ]
  have hK0pow : 0 < K₀ ^ Ki := pow_pos (by linarith) _
  have hcpos : 0 < c := by
    change 0 < min 1 (C⁻¹ / (2 * S ^ 2 * K₀ ^ Ki))
    exact lt_min zero_lt_one (div_pos hCp (by positivity))
  have hcle1 : c ≤ 1 := by
    change min 1 (C⁻¹ / (2 * S ^ 2 * K₀ ^ Ki)) ≤ 1
    exact min_le_left _ _
  have hKi : 1 ≤ Ki := by
    show 1 ≤ 2 ^ (σ + 1)
    exact Nat.one_le_two_pow
  refine ⟨c, hcpos, Ki, hKi, ?_⟩
  intro B Ns N D f₀ f₁ β H₁ γ η hN hNs hSc hNNs hD hDK hs0 hs1 hb0 hb1 hBd hγ0 hη0 hη1
    hHsub hdens hpt
  have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hdSup_ge : Ns ≤ Work.Peluse.dSup P Ns N := by rw [Work.Peluse.dSup]; omega
  have hdSup_le_B : Work.Peluse.dSup P Ns N ≤ B := by omega
  have hB1 : 1 ≤ B := le_trans hNs (le_trans hdSup_ge hdSup_le_B)
  have hNsB : Ns ≤ B := le_trans hdSup_ge hdSup_le_B
  have hBpos : (0:ℝ) < (B:ℝ) := by exact_mod_cast (by omega : 0 < B)
  have hDB : D ≤ B := by
    have h3 : D ≤ 2 * σ * D := by
      have h := Nat.mul_le_mul_right D (show 1 ≤ 2 * σ by omega)
      simpa using h
    have h4 : 2 * σ * D ≤ Work.Peluse.dSup P Ns N + 2 * σ * D := by omega
    omega
  have hLsD : Ns + σ * D ≤ B := by
    have h2 : σ * D ≤ 2 * σ * D := by
      calc σ * D = 1 * (σ * D) := (one_mul _).symm
        _ ≤ 2 * (σ * D) := Nat.mul_le_mul_right _ (by norm_num)
        _ = 2 * σ * D := by ring
    omega
  have hbox : ∀ p ∈ H₁, ∀ i : Fin σ, p.1 i ∈ Finset.Icc (1:ℤ) (D:ℤ) ∧
      p.2 i ∈ Finset.Icc (1:ℤ) (D:ℤ) := by
    intro p hp i
    obtain ⟨hu, hv⟩ := mem_pairBox (hHsub hp)
    rw [Work.Peluse.Ulower.arithIcc_one_eq D] at hu hv
    exact ⟨hu i, hv i⟩
  have hcard : (H₁.card : ℝ) ≤ (D:ℝ) ^ (2 * σ) := by
    have h1 : H₁.card ≤ (pairBox σ D).card := Finset.card_le_card hHsub
    have h2 : ((pairBox σ D).card : ℝ) = (D:ℝ) ^ (2 * σ) := by
      rw [pairBox_card, Work.Peluse.Ulower.card_piFinset_arithIcc]
      push_cast
      rw [← pow_mul]
      congr 1
      ring
    rw [← h2]
    exact_mod_cast h1
  have hγ1 : γ ≤ 1 := by
    have h3 : γ * (D:ℝ) ^ (2 * σ) ≤ 1 * (D:ℝ) ^ (2 * σ) := by
      rw [one_mul]
      exact le_trans hdens hcard
    exact le_of_mul_le_mul_right h3 (pow_pos hDpos _)
  have hs0Ns : ∀ x : ℤ, x ∉ Work.Peluse.symIcc Ns → f₀ x = 0 :=
    fun x hx => hs0 x (notMem_symIcc_iff_ss.mp hx)
  have hG1 : ∀ (z : Fin N) (x : ℤ), ‖Work.Peluse.Ulower.sl P f₀ f₁ (z.1 + 1) x‖ ≤ 1 :=
    fun z x => Work.Peluse.Ulower.ss74.sl_norm_le_one hb0 hb1 (z.1 + 1) x
  have hGsupp : ∀ z : Fin N, ∃ c₀ : ℤ, ∀ x : ℤ, x ∉ Work.Peluse.symIcc Ns →
      Work.Peluse.Ulower.sl P f₀ f₁ (z.1 + 1) (x + c₀) = 0 := fun z =>
    ⟨P.eval (((z.1 + 1 : ℕ) : ℤ)),
      fun x hx => Work.Peluse.Ulower.ss74.sl_translate_support (L := Ns) hs0Ns (z.1 + 1) x hx⟩
  have hbound := hC (L := Ns) (D := D) (B := B) hNs hD hLsD
    (fun z : Fin N => Work.Peluse.Ulower.sl P f₀ f₁ (z.1 + 1)) hG1 hGsupp H₁ β hbox
  rw [hypoMass_sl (σ := σ) hN P f₀ f₁ H₁ β,
      concMass_sl (σ := σ) (D := D) (B := B) hN P f₀ f₁ H₁ β] at hbound
  set Θ : Finset ((Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ)) :=
    Work.Peluse.Ulower.ThetaSet σ D H₁ with hΘdef
  let Hyp : ℝ := ∑ p ∈ H₁, (cubeAmp B (Work.Peluse.dualFn N P f₀ f₁) β p.1 p.2) ^ 2
  have hHyp : η ^ 2 * γ * (D:ℝ) ^ (2 * σ) ≤ Hyp := by
    have hsum : ∑ p ∈ H₁, η ^ 2 ≤ Hyp := by
      refine Finset.sum_le_sum fun p hp => ?_
      exact pow_le_pow_left₀ (le_of_lt hη0) (hpt p hp) 2
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    calc η ^ 2 * γ * (D:ℝ) ^ (2 * σ) = η ^ 2 * (γ * (D:ℝ) ^ (2 * σ)) := by ring
      _ ≤ η ^ 2 * (H₁.card : ℝ) := mul_le_mul_of_nonneg_left hdens (sq_nonneg η)
      _ = (H₁.card : ℝ) * η ^ 2 := by ring
      _ ≤ Hyp := hsum
  let A' : ℝ := C⁻¹ * (η ^ 2 * γ) ^ (2 ^ σ) * (D:ℝ) ^ (3 * σ)
  have hA'eq : A' = C⁻¹ * (η ^ 2 * γ) ^ (2 ^ σ) * (D:ℝ) ^ (3 * σ) := rfl
  have hpowid : 2 * σ * 2 ^ σ = σ * (2 ^ (σ + 1) - 3) + 3 * σ := by
    have h3 : 3 ≤ 2 ^ (σ + 1) := by
      calc 3 ≤ 4 := by norm_num
        _ = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (σ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.mul_comm 3 σ, ← Nat.mul_add, Nat.sub_add_cancel h3]
    rw [show (2:ℕ) ^ (σ + 1) = 2 * 2 ^ σ by rw [pow_succ]; ring]
    ring
  have hAeq : A' = C⁻¹ * (η ^ 2 * γ * (D:ℝ) ^ (2 * σ)) ^ (2 ^ σ)
      / (D:ℝ) ^ (σ * (2 ^ (σ + 1) - 3)) := by
    have h1 : (η ^ 2 * γ * (D:ℝ) ^ (2 * σ)) ^ (2 ^ σ)
        = (η ^ 2 * γ) ^ (2 ^ σ) * (D:ℝ) ^ (2 * σ * 2 ^ σ) := by
      rw [mul_pow, ← pow_mul]
    have h2 : (η ^ 2 * γ) ^ (2 ^ σ) * (D:ℝ) ^ (2 * σ * 2 ^ σ)
          / (D:ℝ) ^ (σ * (2 ^ (σ + 1) - 3))
        = (η ^ 2 * γ) ^ (2 ^ σ) * (D:ℝ) ^ (3 * σ) := by
      have hDp : (D:ℝ) ^ (2 * σ * 2 ^ σ)
          = (D:ℝ) ^ (σ * (2 ^ (σ + 1) - 3)) * (D:ℝ) ^ (3 * σ) := by
        rw [← pow_add, hpowid]
      rw [hDp]
      field_simp
    calc A' = C⁻¹ * ((η ^ 2 * γ) ^ (2 ^ σ) * (D:ℝ) ^ (3 * σ)) := by
          rw [hA'eq]; ring
      _ = C⁻¹ * ((η ^ 2 * γ) ^ (2 ^ σ) * (D:ℝ) ^ (2 * σ * 2 ^ σ)
            / (D:ℝ) ^ (σ * (2 ^ (σ + 1) - 3))) := by rw [h2]
      _ = C⁻¹ * (η ^ 2 * γ * (D:ℝ) ^ (2 * σ)) ^ (2 ^ σ)
            / (D:ℝ) ^ (σ * (2 ^ (σ + 1) - 3)) := by rw [h1]; ring
  have hSum : A' ≤ ∑ k ∈ Θ, (‖((B : ℂ))⁻¹ * ∑' x : ℤ,
        sliceDual σ N P f₀ f₁ (fun i => (k.2.1 i, k.2.2 i)) x *
          Complex.exp (2 * Real.pi * Complex.I * (mixedPhase β k : ℂ) * (x : ℂ))‖) ^ 2 := by
    have hpow : (η ^ 2 * γ * (D:ℝ) ^ (2 * σ)) ^ (2 ^ σ) ≤ Hyp ^ (2 ^ σ) :=
      pow_le_pow_left₀ (by positivity) hHyp (2 ^ σ)
    have hDd : (0:ℝ) < (D:ℝ) ^ (σ * (2 ^ (σ + 1) - 3)) := pow_pos hDpos _
    have hmono : C⁻¹ * (η ^ 2 * γ * (D:ℝ) ^ (2 * σ)) ^ (2 ^ σ)
          / (D:ℝ) ^ (σ * (2 ^ (σ + 1) - 3))
        ≤ C⁻¹ * Hyp ^ (2 ^ σ) / (D:ℝ) ^ (σ * (2 ^ (σ + 1) - 3)) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hDd)
      exact mul_le_mul_of_nonneg_left hpow (le_of_lt hCp)
    rw [hAeq]
    exact le_trans hmono hbound
  have hUni : ∀ k ∈ Θ, ‖((B : ℂ))⁻¹ * ∑' x : ℤ,
        sliceDual σ N P f₀ f₁ (fun i => (k.2.1 i, k.2.2 i)) x *
          Complex.exp (2 * Real.pi * Complex.I * (mixedPhase β k : ℂ) * (x : ℂ))‖ ≤ S := by
    intro k hk
    have hkB : k ∈ Work.Peluse.Ulower.ThetaSet σ D H₁ := hΘdef ▸ hk
    exact conclTerm_le_of_mem_ThetaSet hB1 hN hD hDB P f₀ f₁ hb0 hb1
      (hs0.mono hNsB) (hs1.mono hNsB) H₁ β k hkB
  have hΘcard : (Θ.card : ℝ) ≤ (D:ℝ) ^ (3 * σ) := by
    have hsub : Θ ⊆ Work.Peluse.Ulower.thetaBox σ D ×ˢ
        (Work.Peluse.Ulower.thetaBox σ D ×ˢ Work.Peluse.Ulower.thetaBox σ D) := by
      intro k hk
      rw [hΘdef] at hk
      exact (Finset.mem_filter.mp hk).1
    have h1 : Θ.card ≤ (Work.Peluse.Ulower.thetaBox σ D ×ˢ
        (Work.Peluse.Ulower.thetaBox σ D ×ˢ Work.Peluse.Ulower.thetaBox σ D)).card :=
      Finset.card_le_card hsub
    have h3 : ((Work.Peluse.Ulower.thetaBox σ D ×ˢ
        (Work.Peluse.Ulower.thetaBox σ D ×ˢ Work.Peluse.Ulower.thetaBox σ D)).card : ℝ)
        = (D:ℝ) ^ (3 * σ) := by
      have hc : (Work.Peluse.Ulower.thetaBox σ D ×ˢ
          (Work.Peluse.Ulower.thetaBox σ D ×ˢ Work.Peluse.Ulower.thetaBox σ D)).card
          = D ^ σ * (D ^ σ * D ^ σ) := by
        simp only [Finset.card_product, Work.Peluse.Ulower.thetaBox_card]
      rw [hc]
      push_cast
      rw [← pow_add, ← pow_add]
      congr 1
      ring
    calc (Θ.card : ℝ) ≤ ((Work.Peluse.Ulower.thetaBox σ D ×ˢ
          (Work.Peluse.Ulower.thetaBox σ D ×ˢ Work.Peluse.Ulower.thetaBox σ D)).card : ℝ) := by
          exact_mod_cast h1
      _ = (D:ℝ) ^ (3 * σ) := h3
  set θ : ℝ := c * (η * γ * ((D:ℝ) / (B:ℝ))) ^ Ki with hθdef
  have hDBK : (D:ℝ) / (B:ℝ) ≤ K₀ := by
    have h1 : (D:ℝ) ≤ K₀ * (Ns:ℝ) := hDK
    rw [div_le_iff₀ hBpos]
    calc (D:ℝ) ≤ K₀ * (Ns:ℝ) := h1
      _ ≤ K₀ * (B:ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hNsB) (by linarith)
  have hDB1 : (D:ℝ) / (B:ℝ) ≤ 1 := by
    rw [div_le_one hBpos]
    exact_mod_cast hDB
  have hbase1 : η * γ * ((D:ℝ) / (B:ℝ)) ≤ 1 := by
    have hηγ : η * γ ≤ 1 * 1 := mul_le_mul hη1 hγ1 (le_of_lt hγ0) (by norm_num)
    calc η * γ * ((D:ℝ) / (B:ℝ)) ≤ 1 * 1 * 1 :=
          mul_le_mul hηγ hDB1 (by positivity) (by norm_num)
      _ = 1 := by ring
  have hθ0 : 0 ≤ θ := by rw [hθdef]; positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθdef]
    have h2 : (η * γ * ((D:ℝ) / (B:ℝ))) ^ Ki ≤ 1 := pow_le_one₀ (by positivity) hbase1
    calc c * (η * γ * ((D:ℝ) / (B:ℝ))) ^ Ki ≤ 1 * 1 :=
          mul_le_mul hcle1 h2 (by positivity) (by norm_num)
      _ = 1 := by ring
  have hpow_DB : ((D:ℝ) / (B:ℝ)) ^ Ki ≤ K₀ ^ Ki :=
    pow_le_pow_left₀ (by positivity) hDBK Ki
  have hpow_ηγ : (η * γ) ^ Ki ≤ (η ^ 2 * γ) ^ (2 ^ σ) := by
    have h1 : (η * γ) ^ Ki = ((η * γ) ^ 2) ^ (2 ^ σ) := by
      change (η * γ) ^ (2 ^ (σ + 1)) = ((η * γ) ^ 2) ^ (2 ^ σ)
      rw [← pow_mul]
      congr 1
      rw [pow_succ]; ring
    have h2 : (η * γ) ^ 2 ≤ η ^ 2 * γ := by
      have h3 : γ ^ 2 ≤ γ := by nlinarith [hγ0, hγ1]
      have h4 : (η * γ) ^ 2 = η ^ 2 * γ ^ 2 := by ring
      rw [h4]
      exact mul_le_mul_of_nonneg_left h3 (sq_nonneg η)
    rw [h1]
    exact pow_le_pow_left₀ (by positivity) h2 (2 ^ σ)
  have hcK0 : c * K₀ ^ Ki ≤ C⁻¹ / (2 * S ^ 2) := by
    have h := mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) (C⁻¹ / (2 * S ^ 2 * K₀ ^ Ki)))
      (le_of_lt hK0pow)
    have h' : C⁻¹ / (2 * S ^ 2 * K₀ ^ Ki) * K₀ ^ Ki = C⁻¹ / (2 * S ^ 2) := by
      field_simp
    rw [h'] at h
    change min 1 (C⁻¹ / (2 * S ^ 2 * K₀ ^ Ki)) * K₀ ^ Ki ≤ C⁻¹ / (2 * S ^ 2)
    exact h
  have hKey : θ * (Θ.card : ℝ) ≤ A' / (2 * S ^ 2) := by
    calc θ * (Θ.card : ℝ)
        = c * (η * γ) ^ Ki * ((D:ℝ) / (B:ℝ)) ^ Ki * (Θ.card : ℝ) := by
          rw [hθdef, mul_pow]; ring
      _ ≤ c * (η * γ) ^ Ki * K₀ ^ Ki * (D:ℝ) ^ (3 * σ) := by
          have h2 : c * (η * γ) ^ Ki * ((D:ℝ) / (B:ℝ)) ^ Ki ≤ c * (η * γ) ^ Ki * K₀ ^ Ki :=
            mul_le_mul_of_nonneg_left hpow_DB (by positivity)
          have h3 : (Θ.card : ℝ) ≤ (D:ℝ) ^ (3 * σ) := hΘcard
          calc c * (η * γ) ^ Ki * ((D:ℝ) / (B:ℝ)) ^ Ki * (Θ.card : ℝ)
              = (c * (η * γ) ^ Ki * ((D:ℝ) / (B:ℝ)) ^ Ki) * (Θ.card : ℝ) := by ring
            _ ≤ (c * (η * γ) ^ Ki * K₀ ^ Ki) * (D:ℝ) ^ (3 * σ) :=
                mul_le_mul h2 h3 (by positivity) (by positivity)
            _ = c * (η * γ) ^ Ki * K₀ ^ Ki * (D:ℝ) ^ (3 * σ) := by ring
      _ = (c * K₀ ^ Ki) * (η * γ) ^ Ki * (D:ℝ) ^ (3 * σ) := by ring
      _ ≤ (C⁻¹ / (2 * S ^ 2)) * (η ^ 2 * γ) ^ (2 ^ σ) * (D:ℝ) ^ (3 * σ) := by
          have h1 : (c * K₀ ^ Ki) * (η * γ) ^ Ki
              ≤ (C⁻¹ / (2 * S ^ 2)) * (η ^ 2 * γ) ^ (2 ^ σ) :=
            mul_le_mul hcK0 hpow_ηγ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = A' / (2 * S ^ 2) := by rw [hA'eq]; ring
  have hA'0 : 0 ≤ A' := by
    rw [hA'eq]
    exact mul_nonneg (mul_nonneg (le_of_lt hCp) (by positivity)) (by positivity)
  have hmarkov : A' / (2 * S ^ 2) ≤ ((Θ.filter (fun k => θ ≤ ‖((B : ℂ))⁻¹ * ∑' x : ℤ,
        sliceDual σ N P f₀ f₁ (fun i => (k.2.1 i, k.2.2 i)) x *
          Complex.exp (2 * Real.pi * Complex.I * (mixedPhase β k : ℂ) * (x : ℂ))‖)).card : ℝ) :=
    filter_card_ge_of_sum_sq Θ _ (fun k => norm_nonneg _) hA'0 hS1 hθ0 hθ1 hSum hUni hKey
  refine ⟨Θ.filter (fun k => θ ≤ ‖((B : ℂ))⁻¹ * ∑' x : ℤ,
      sliceDual σ N P f₀ f₁ (fun i => (k.2.1 i, k.2.2 i)) x *
        Complex.exp (2 * Real.pi * Complex.I * (mixedPhase β k : ℂ) * (x : ℂ))‖), ?_, ?_, ?_⟩
  · exact Finset.filter_subset _ _
  · calc c * (η * γ * ((D:ℝ) / (B:ℝ))) ^ Ki *
          ((Work.Peluse.Ulower.ThetaSet σ D H₁).card : ℝ)
        = θ * (Θ.card : ℝ) := by rw [hθdef, hΘdef]
      _ ≤ A' / (2 * S ^ 2) := hKey
      _ ≤ _ := hmarkov
  · intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    rw [hθdef] at hk'
    exact hk'

end

end Work.Peluse.Ulower.StepLe


namespace Work.Peluse.UlowerA

/-- **The lossy interchange with the unbalanced scale relation.**

Same statement as `Work.Peluse.Ulower.StepLe.hasInterchangeL_of_sharpMass`, with the balanced
hypothesis `Scaled Ns N P.natDegree` replaced by `UnbalScale P C Ns N`.  The proof is the proof of
the balanced version verbatim: the scale hypothesis is never used there. -/
theorem hasInterchangeLU {P : Polynomial ℤ}
    (h : ∀ σ : ℕ, 1 ≤ σ → Work.Peluse.Ulower.StepLe.SharpMassDDI σ) :
    ∀ C : ℕ, 1 ≤ C → Work.Peluse.UlowerA.HasInterchangeLU P C :=
  Work.Peluse.Ulower.StepLe.hasInterchangeLU_int h

end Work.Peluse.UlowerA
