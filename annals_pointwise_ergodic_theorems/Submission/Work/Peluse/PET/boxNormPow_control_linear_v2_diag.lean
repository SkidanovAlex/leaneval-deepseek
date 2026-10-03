import Mathlib
import Submission.Work.Peluse.Peel.boxNormPow_diag_peel
import Submission.Work.Peluse.PET.absSq_window_control_pow
import Submission.Work.Peluse.PET.boxNormPow_one_arithIcc_shrink

/-!
# The `diag` route to Peluse's Lemma 4.10 (zero constant term)

Target: `Work.Peluse.PET.boxNormPow_control_linear_v2_diag`, a *strengthening* of
`Work.Peluse.PET.boxNormPow_control_linear_v2` in which the exponent is
`2 ^ (m - 1) + K'` and `K'` is a *parameter* constrained by the hypothesis

`(γ M / (1000 (m+1))) ^ m ≤ (1/4) (1000/γ)^K'`.

With `H = ⌊γ' M⌋` (so that `H ≤ γ' M ≤ γ M / (1000 (m+1))`, hence `H ^ m ≤ (1/4) (1000/γ)^K'`,
i.e. `H ^ (-m) ≥ 4 (γ/1000)^K'`), the target follows from three pieces:

* **(A)** the level-one window control at the scale `M` with the *exact* exponent `2 ^ (m-1)`:
  `(γ/1000)^(2^(m-1)) ≤ ‖|F_m|^{2^(m-1)}‖²_{□¹_{c_m[M]}([-N,N])}`
  (`Work.Peluse.WindowControl.absSq_window_control` produces this with an existential exponent;
  `Work.Peluse.PET.absSq_window_control_pow` is the same statement made explicit);
* **(B)** the `M → H` transfer at level one for the nonnegative function `|F_m|^{2^(m-1)}`
  (`Work.Peluse.PET.boxNormPow_one_arithIcc_shrink`), which loses only the factor `4`;
* the **diagonal of the peel** (`Work.Peluse.Peel.boxNormPow_diag_peel`):
  `(∏ i, |Q i|⁻¹) ‖g‖²_{□¹_{Q 0}([-N,N])} ≤ ‖F_m‖^{2^m}_{□^m_Q([-N,N])}` for
  `Q i = (c_m - c_i)[H]`.

The two constants match: `(1/4)` from (B) cancels the `4` from `H^{-m}`.  Since `|Q i| ≤ H` for every
`i`, the product `∏_{i : Fin m} |Q i|⁻¹` dominates `H^{-m}` (the extra factor `|Q 0|⁻¹ ≤ 1` in the
statement of `boxNormPow_diag_peel` is harmless).

## Main results

* `Work.Peluse.PET.boxNormPow_control_linear_v2_diag`
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Peluse.PET

noncomputable section

/-- The assembly of the `diag` route, with the two ingredients (A) and (B) as hypotheses. -/
private lemma diag_core {m : ℕ} (hm : 2 ≤ m) (K' H : ℕ) (c : Fin (m + 1) → ℤ) (hc0 : c 0 = 0)
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (F : Fin (m + 1) → ℤ → ℂ) {γ γ' : ℝ}
    (hγ : 0 < γ) (hγ'le : γ' ≤ γ / (1000 * ((m : ℝ) + 1)))
    (hHge : 1 ≤ H) (hHle : (H : ℝ) ≤ γ' * (M : ℝ))
    (hFsup : Work.Peluse.SupportIn (F ⟨m, Nat.lt_succ_self m⟩) N)
    (hK'hyp : (γ * (M : ℝ) / (1000 * ((m : ℝ) + 1))) ^ m ≤ (1 / 4) * (1000 / γ) ^ K')
    (hA : (γ / 1000) ^ (2 ^ (m - 1)) ≤ Work.Peluse.boxNormPow 1
      (fun _ : Fin 1 => Work.Peluse.arithIcc (c ⟨m, Nat.lt_succ_self m⟩) M)
      (Work.Peluse.symIcc N)
      (fun x => ((‖F ⟨m, Nat.lt_succ_self m⟩ x‖ ^ (2 ^ (m - 1)) : ℝ) : ℂ)))
    (hB : Work.Peluse.boxNormPow 1
      (fun _ : Fin 1 => Work.Peluse.arithIcc (c ⟨m, Nat.lt_succ_self m⟩) M)
      (Work.Peluse.symIcc N)
      (fun x => ((‖F ⟨m, Nat.lt_succ_self m⟩ x‖ ^ (2 ^ (m - 1)) : ℝ) : ℂ))
      ≤ 4 * Work.Peluse.boxNormPow 1
      (fun _ : Fin 1 => Work.Peluse.arithIcc (c ⟨m, Nat.lt_succ_self m⟩) H)
      (Work.Peluse.symIcc N)
      (fun x => ((‖F ⟨m, Nat.lt_succ_self m⟩ x‖ ^ (2 ^ (m - 1)) : ℝ) : ℂ))) :
    (γ / 1000) ^ (2 ^ (m - 1) + K') ≤ Work.Peluse.boxNormPow m
      (fun i : Fin m => Work.Peluse.arithIcc (c ⟨m, Nat.lt_succ_self m⟩ - c i.castSucc) H)
      (Work.Peluse.symIcc N) (F ⟨m, Nat.lt_succ_self m⟩) := by
  classical
  set Fm : ℤ → ℂ := F ⟨m, Nat.lt_succ_self m⟩ with hFm
  set Q : Fin m → Finset ℤ :=
    fun i => Work.Peluse.arithIcc (c ⟨m, Nat.lt_succ_self m⟩ - c i.castSucc) H with hQdef
  -- the direction sets are nonempty and have at most `H` elements
  have hQmem : ∀ i, (Q i).Nonempty := by
    intro i
    refine ⟨c ⟨m, Nat.lt_succ_self m⟩ - c i.castSucc, ?_⟩
    rw [hQdef]
    exact Finset.mem_image.mpr ⟨1, by rw [Finset.mem_Icc]; exact ⟨le_rfl, hHge⟩, by simp⟩
  have hQ0 : Q ⟨0, by omega⟩ = Work.Peluse.arithIcc (c ⟨m, Nat.lt_succ_self m⟩) H := by
    have hcs : ((⟨0, by omega⟩ : Fin m).castSucc : Fin (m + 1)) = 0 := Fin.ext rfl
    simp only [hQdef, hcs, hc0, sub_zero]
  have hcard_le : ∀ i, (Q i).card ≤ H := by
    intro i
    rw [hQdef]
    calc (Work.Peluse.arithIcc (c ⟨m, Nat.lt_succ_self m⟩ - c i.castSucc) H).card
        ≤ (Finset.Icc 1 H).card := Finset.card_image_le
      _ = H := by rw [Nat.card_Icc]; omega
  -- the two ingredients, in the `Fm`-shape
  have hA' : (γ / 1000) ^ (2 ^ (m - 1)) ≤ Work.Peluse.boxNormPow 1
      (fun _ : Fin 1 => Work.Peluse.arithIcc (c ⟨m, Nat.lt_succ_self m⟩) M)
      (Work.Peluse.symIcc N) (fun x => ((‖Fm x‖ ^ (2 ^ (m - 1)) : ℝ) : ℂ)) := by
    rw [hFm]; exact hA
  have hB' : Work.Peluse.boxNormPow 1
      (fun _ : Fin 1 => Work.Peluse.arithIcc (c ⟨m, Nat.lt_succ_self m⟩) M)
      (Work.Peluse.symIcc N) (fun x => ((‖Fm x‖ ^ (2 ^ (m - 1)) : ℝ) : ℂ))
      ≤ 4 * Work.Peluse.boxNormPow 1
      (fun _ : Fin 1 => Work.Peluse.arithIcc (c ⟨m, Nat.lt_succ_self m⟩) H)
      (Work.Peluse.symIcc N) (fun x => ((‖Fm x‖ ^ (2 ^ (m - 1)) : ℝ) : ℂ)) := by
    rw [hFm]; exact hB
  -- (1) the level-one bound at the scale `H`
  have hB1 : (1 / 4) * (γ / 1000) ^ (2 ^ (m - 1)) ≤ Work.Peluse.boxNormPow 1
      (fun _ : Fin 1 => Q ⟨0, by omega⟩) (Work.Peluse.symIcc N)
      (fun x => ((‖Fm x‖ ^ (2 ^ (m - 1)) : ℝ) : ℂ)) := by
    have h2 := hB'
    rw [← hQ0] at h2
    linarith
  -- (2) the exponent arithmetic: `H^m ≤ (1/4)(1000/γ)^{K'}`
  have hHle2 : (H : ℝ) ≤ γ * (M : ℝ) / (1000 * ((m : ℝ) + 1)) := by
    calc (H : ℝ) ≤ γ' * (M : ℝ) := hHle
      _ ≤ (γ / (1000 * ((m : ℝ) + 1))) * (M : ℝ) :=
          mul_le_mul_of_nonneg_right hγ'le (by positivity)
      _ = γ * (M : ℝ) / (1000 * ((m : ℝ) + 1)) := by ring
  have hHpow : (H : ℝ) ^ m ≤ (1 / 4) * (1000 / γ) ^ K' :=
    le_trans (pow_le_pow_left₀ (by positivity) hHle2 m) hK'hyp
  have hHpos : (0 : ℝ) < H := by
    have h : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hHge
    linarith
  have hHmpowpos : (0 : ℝ) < (H : ℝ) ^ m := pow_pos hHpos m
  have h4pos : (0 : ℝ) < (1 / 4) * (1000 / γ) ^ K' := by positivity
  have hHinv : 4 * (γ / 1000) ^ K' ≤ ((H : ℝ) ^ m)⁻¹ := by
    have h1 : (((1 / 4) * (1000 / γ) ^ K')⁻¹) ≤ ((H : ℝ) ^ m)⁻¹ :=
      (inv_le_inv₀ h4pos hHmpowpos).mpr hHpow
    have h2 : (((1 / 4) * (1000 / γ) ^ K')⁻¹) = 4 * (γ / 1000) ^ K' := by
      rw [mul_inv, ← inv_pow, inv_div]
      norm_num
    rwa [h2] at h1
  -- (3) the product of the reciprocal cardinalities dominates `H^{-m}`
  have hprod_le : ∏ i : Fin m, ((Q i).card : ℝ) ≤ (H : ℝ) ^ m := by
    calc ∏ i : Fin m, ((Q i).card : ℝ) ≤ ∏ _i : Fin m, (H : ℝ) :=
          Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => by exact_mod_cast hcard_le i)
      _ = (H : ℝ) ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hprodpos : (0 : ℝ) < ∏ i : Fin m, ((Q i).card : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast (Finset.card_pos.mpr (hQmem i)))
  have hprod : ((H : ℝ) ^ m)⁻¹ ≤ ∏ i : Fin m, ((Q i).card : ℝ)⁻¹ := by
    rw [Finset.prod_inv_distrib]
    exact (inv_le_inv₀ hHmpowpos hprodpos).mpr hprod_le
  -- (4) the diagonal of the peel
  have hdiag := Work.Peluse.Peel.boxNormPow_diag_peel hm hN Fm hFsup Q hQmem
  -- (5) assembly
  have hprodnn : (0 : ℝ) ≤ ∏ i : Fin m, ((Q i).card : ℝ)⁻¹ :=
    Finset.prod_nonneg (fun i _ => by positivity)
  have hfinal : (γ / 1000) ^ (2 ^ (m - 1) + K') ≤
      Work.Peluse.boxNormPow m Q (Work.Peluse.symIcc N) Fm := by
    calc (γ / 1000) ^ (2 ^ (m - 1) + K')
        = (γ / 1000) ^ K' * (γ / 1000) ^ (2 ^ (m - 1)) := by rw [pow_add]; ring
      _ = (4 * (γ / 1000) ^ K') * ((1 / 4) * (γ / 1000) ^ (2 ^ (m - 1))) := by ring
      _ ≤ ((H : ℝ) ^ m)⁻¹ * ((1 / 4) * (γ / 1000) ^ (2 ^ (m - 1))) :=
          mul_le_mul_of_nonneg_right hHinv (by positivity)
      _ ≤ (∏ i : Fin m, ((Q i).card : ℝ)⁻¹) *
          Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => Q ⟨0, by omega⟩) (Work.Peluse.symIcc N)
            (fun x => ((‖Fm x‖ ^ (2 ^ (m - 1)) : ℝ) : ℂ)) :=
          mul_le_mul hprod hB1 (by positivity) hprodnn
      _ ≤ Work.Peluse.boxNormPow m Q (Work.Peluse.symIcc N) Fm := hdiag
  simpa only [hQdef, hFm] using hfinal

/-- **Peluse's Lemma 4.10 with zero constant term, `diag` form.** -/
theorem boxNormPow_control_linear_v2_diag {m : ℕ} (hm : 2 ≤ m) (K' : ℕ) :
    ∀ (c : Fin (m + 1) → ℤ), c 0 = 0 → ∀ {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
      (F : Fin (m + 1) → ℤ → ℂ) {γ γ' : ℝ}, 0 < γ → 0 < γ' → γ ≤ 1 →
      (∀ i x, ‖F i x‖ ≤ 1) → (∀ i, Work.Peluse.SupportIn (F i) N) →
      (∀ y ∈ Finset.Icc 1 M, ∀ i : Fin (m + 1), |c i * (y : ℤ)| ≤ (N : ℤ)) →
      γ' ≤ γ / (1000 * (m + 1)) → 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat →
      γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 0 x *
          ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ ^ 2 →
      (γ * (M : ℝ) / (1000 * ((m : ℝ) + 1))) ^ m ≤ (1 / 4) * (1000 / γ) ^ K' →
      (γ / 1000) ^ (2 ^ (m - 1) + K') ≤ Work.Peluse.boxNormPow m
        (fun i : Fin m => Work.Peluse.arithIcc (c ⟨m, Nat.lt_succ_self m⟩ - c i.castSucc)
          (⌊γ' * (M : ℝ)⌋).toNat) (Work.Peluse.symIcc N) (F ⟨m, Nat.lt_succ_self m⟩) := by
  intro c hc0 N M hN hM F γ γ' hγ hγ' hγ1 hFb hFs hcy hγ'le hHge hLam hK'hyp
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hHle : ((⌊γ' * (M : ℝ)⌋).toNat : ℝ) ≤ γ' * (M : ℝ) := by
    rw [Int.floor_toNat]
    exact Nat.floor_le (le_of_lt (mul_pos hγ' hMpos))
  have hγ'1 : γ' ≤ 1 := by
    have h1 : γ / (1000 * ((m : ℝ) + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      nlinarith [hγ1]
    linarith
  have hHM : ⌊γ' * (M : ℝ)⌋.toNat ≤ M := by
    have h : ((⌊γ' * (M : ℝ)⌋).toNat : ℝ) ≤ (M : ℝ) := by
      calc ((⌊γ' * (M : ℝ)⌋).toNat : ℝ) ≤ γ' * (M : ℝ) := hHle
        _ ≤ 1 * (M : ℝ) := mul_le_mul_of_nonneg_right hγ'1 (by positivity)
        _ = (M : ℝ) := one_mul _
    exact_mod_cast h
  refine diag_core hm K' (⌊γ' * (M : ℝ)⌋.toNat) c hc0 hN hM F hγ hγ'le hHge hHle
    (hFs ⟨m, Nat.lt_succ_self m⟩) hK'hyp ?_ ?_
  · exact absSq_window_control_pow (m := m) (by omega) c hc0 hN hM F hγ hγ' hγ1 hFb hFs hcy
      hγ'le hHge hLam
  · exact boxNormPow_one_arithIcc_shrink hHge hHM (c ⟨m, Nat.lt_succ_self m⟩)
      (fun x => pow_nonneg (norm_nonneg _) _)
      (fun x hx => by
        rw [hFs ⟨m, Nat.lt_succ_self m⟩ x hx, norm_zero,
          zero_pow (by positivity : 2 ^ (m - 1) ≠ 0)])

end

end Work.Peluse.PET
