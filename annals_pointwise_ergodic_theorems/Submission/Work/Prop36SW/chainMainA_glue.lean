import Mathlib
import Submission.Work.Prop36SW.chainRun
import Submission.Work.Prop36SW.lastStep

/-!
# The §5 chain, glued: `Work.Prop36SW.chainMainA_glue`

From the entry (`Reach D d c (d-2)`), the state-to-state step-down (`Reach (m+1) → Reach m`)
and the endgame (`LastStep D d c Λ kω`), produce the data-independent level `S` and, for every
`A₀ ≥ 1`, the constants `C, c₀, e₀, M₀, Cs` and the uniformity-norm-power conclusion at the
coefficient `d!·c`.

This is the version of `Work.Prop36SW.chainMain` (`chainMain.lean`, proved) for the
**re-factored** interface `Work.Prop36SW.Reach` of `chainRun.lean`, in which `Λ, kω` are
quantified *before* `A₀` (so that the level `S` is `A₀`-free) while `c₀, e₀, M₀, Cs` may depend
on `A₀`.  The argument is the one of `chainMain`: descend the chain to slot level `0`, take the
endgame constants there, replace the state's strength by the explicit `γt := c₀' η^{e₀'}` (the
state is antitone in the strength), enlarge the régime once and for all to supply the endgame's
density and threshold hypotheses, and read off the output constants.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators

namespace Work.Prop36SW

noncomputable section

open Work.Peluse
open Work.Peluse.UControl
open Work.Peluse.Prop36SW

/-- **`pFlat` at slot level `0`.**  There the direction is the base direction `c`, so the
coefficient is the constant `(Λ·d)·c`. -/
private lemma pFlat_zero (D : IdxDatum) (d : ℕ) (c : ℤ) (Λ : ℕ) (s : D.S 1)
    (x : Fin (nD D 1) → ℤ) : pFlat D d c 0 Λ s x = ((Λ * d : ℕ) : ℤ) * c := by
  simp only [pFlat, IdxDatum.dir]
  push_cast
  ring

/-- **The endgame's threshold from the régime.**  If `Cn·(4/(3c₀))^{Mn} ≤ η^{M₀}H` and
`c₀·η^{e₀} ≤ γ` with `e₀·Mn ≤ M₀` and `0 < η ≤ 1`, then `Cn·(3γ/4)^{-Mn} ≤ H`.

(`(3γ/4)^{-Mn} = ((4/3)/γ)^{Mn}` grows as `γ` shrinks; the régime forces `η` — hence `γ` — to be
large enough relative to `H`.) -/
private lemma thresholdLe {Cn c₀ γ η H : ℝ} {e₀ Mn M₀ : ℕ}
    (hCn : 0 < Cn) (hc₀ : 0 < c₀) (hη0 : 0 < η) (hη1 : η ≤ 1) (hγ0 : 0 < γ)
    (hmon : c₀ * η ^ e₀ ≤ γ) (hk : e₀ * Mn ≤ M₀)
    (h : Cn * (4 / (3 * c₀)) ^ Mn ≤ η ^ M₀ * H) :
    Cn * (3 * γ / 4) ^ (-(Mn : ℤ)) ≤ H := by
  have hηe0 : (0 : ℝ) < η ^ e₀ := pow_pos hη0 _
  have hγnn : (0 : ℝ) ≤ γ := le_trans (mul_nonneg hc₀.le hηe0.le) hmon
  have hLHSp : 0 < Cn * (4 / (3 * c₀)) ^ Mn :=
    mul_pos hCn (pow_pos (div_pos (by norm_num) (by positivity)) _)
  have hηM0 : (0 : ℝ) < η ^ M₀ := pow_pos hη0 _
  have hH0 : 0 ≤ H := by
    have h' : 0 ≤ η ^ M₀ * H := le_trans hLHSp.le h
    exact (mul_nonneg_iff_of_pos_left hηM0).mp h'
  -- `c₀^{Mn}·η^{M₀} ≤ γ^{Mn}`
  have hsplit1 : η ^ M₀ = η ^ (e₀ * Mn) * η ^ (M₀ - e₀ * Mn) := by
    rw [← pow_add]
    congr 1
    omega
  have hsplit2 : (c₀ * η ^ e₀) ^ Mn = c₀ ^ Mn * η ^ (e₀ * Mn) := by
    rw [mul_pow, ← pow_mul]
  have hsplit : c₀ ^ Mn * η ^ M₀ = (c₀ * η ^ e₀) ^ Mn * η ^ (M₀ - e₀ * Mn) := by
    rw [hsplit1, hsplit2]; ring
  have hpow : (c₀ * η ^ e₀) ^ Mn ≤ γ ^ Mn :=
    pow_le_pow_left₀ (mul_nonneg hc₀.le hηe0.le) hmon Mn
  have heta : η ^ (M₀ - e₀ * Mn) ≤ 1 := pow_le_one₀ hη0.le hη1
  have hc0Mn : c₀ ^ Mn * η ^ M₀ ≤ γ ^ Mn := by
    rw [hsplit]
    calc (c₀ * η ^ e₀) ^ Mn * η ^ (M₀ - e₀ * Mn)
        ≤ γ ^ Mn * 1 :=
          mul_le_mul hpow heta (pow_nonneg hη0.le _) (pow_nonneg hγnn _)
      _ = γ ^ Mn := mul_one _
  -- `Cn·(4/3)^{Mn} ≤ γ^{Mn}·H`
  have hA : Cn * (4 / (3 * c₀)) ^ Mn * c₀ ^ Mn = Cn * (4 / 3) ^ Mn := by
    rw [mul_assoc, ← mul_pow]
    congr 1
    field_simp
  have hCn34 : Cn * (4 / 3) ^ Mn ≤ γ ^ Mn * H := by
    have h1 := mul_le_mul_of_nonneg_right h (pow_nonneg hc₀.le Mn)
    rw [hA] at h1
    have h2 : (η ^ M₀ * H) * c₀ ^ Mn = c₀ ^ Mn * η ^ M₀ * H := by ring
    rw [h2] at h1
    have h3 : c₀ ^ Mn * η ^ M₀ * H ≤ γ ^ Mn * H :=
      mul_le_mul_of_nonneg_right hc0Mn hH0
    linarith
  -- the `zpow` identity
  have hkey : (3 * γ / 4) ^ (-(Mn : ℤ)) = (4 / 3) ^ Mn * γ ^ (-(Mn : ℤ)) := by
    have hγne : γ ≠ 0 := ne_of_gt hγ0
    have h1 : (3 * γ / 4) ^ (-(Mn : ℤ)) = ((3 * γ / 4) ^ Mn)⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    have h2 : γ ^ (-(Mn : ℤ)) = (γ ^ Mn)⁻¹ := by rw [zpow_neg, zpow_natCast]
    rw [h1, h2]
    rw [show (3 * γ / 4) ^ Mn = (3 * γ) ^ Mn / 4 ^ Mn by rw [div_pow]]
    rw [show (4 / 3 : ℝ) ^ Mn = 4 ^ Mn / 3 ^ Mn by rw [div_pow]]
    rw [inv_div]
    field_simp
    ring
  have hgg : γ ^ Mn * γ ^ (-(Mn : ℤ)) = 1 := by
    have h1 : γ ^ Mn = γ ^ ((Mn : ℤ)) := by rw [zpow_natCast]
    rw [h1, ← zpow_add₀ (ne_of_gt hγ0), add_neg_cancel, zpow_zero]
  rw [hkey]
  calc Cn * ((4 / 3) ^ Mn * γ ^ (-(Mn : ℤ)))
      = Cn * (4 / 3) ^ Mn * γ ^ (-(Mn : ℤ)) := by ring
    _ ≤ (γ ^ Mn * H) * γ ^ (-(Mn : ℤ)) :=
          mul_le_mul_of_nonneg_right hCn34 (by positivity)
    _ = H * (γ ^ Mn * γ ^ (-(Mn : ℤ))) := by ring
    _ = H := by rw [hgg, mul_one]

theorem chainMainA_glue (D : Work.Peluse.UControl.IdxDatum) (d : ℕ) (c : ℤ)
    (hd : 2 ≤ d) (hc : c ≠ 0)
    (hEntry : Work.Prop36SW.Reach D d c (d - 2))
    (hStep : ∀ m : ℕ, m + 1 ≤ d - 2 → Work.Prop36SW.Reach D d c (m + 1) →
      Work.Prop36SW.Reach D d c m)
    (hLast : ∀ (Λ : ℕ) (kω : Work.Peluse.UControl.SlotSet (D.S 1) (fun _ => 1) → ℕ),
      Work.Prop36SW.LastStep D d c Λ kω)
    (hI : 2 ≤ Fintype.card (D.I (d - 1))) :
    ∃ (S : ℕ), 2 ≤ S ∧
      ∀ (A₀ : ℝ), 1 ≤ A₀ →
        ∃ (C : ℝ) (E : ℕ) (c₀ : ℝ) (e₀ : ℕ) (M₀ : ℕ) (Cs : ℝ),
          0 < C ∧ 0 < c₀ ∧ 1 ≤ e₀ ∧ 1 ≤ M₀ ∧ 1 ≤ Cs ∧
          ∀ (N H : ℕ) (f : ℤ → ℂ) (η : ℝ),
            1 ≤ N → 2 ≤ H → (∀ x : ℤ, ‖f x‖ ≤ 1) → Work.Peluse.SupportIn f N →
            0 < η → η ≤ 1 → Cs ≤ η ^ M₀ * (H : ℝ) →
            ((H : ℝ) + 1) ^ d ≤ A₀ * N → η ≤ D.famAvg d H c N f →
            ∃ (Lw₀ N' : ℕ),
              N ≤ N' ∧ c₀ * η ^ e₀ * ((H : ℝ) + 1) ^ d ≤ (Lw₀ : ℝ) ∧
              C * η ^ E ≤ Work.Peluse.uNormPow S
                (Work.Peluse.arithIcc ((Nat.factorial d) * c) Lw₀) (Work.Peluse.symIcc N') f := by
  classical
  -- ## 1. descend the chain to slot level `0`
  have hR0 : Reach D d c 0 := by
    have hdesc : ∀ j, j ≤ d - 2 → Reach D d c (d - 2 - j) := by
      intro j
      induction j with
      | zero => intro _; simpa using hEntry
      | succ j ih =>
        intro hj
        have hj' : j ≤ d - 2 := by omega
        have hprev : Reach D d c (d - 2 - j) := ih hj'
        have hm : (d - 2 - j - 1) + 1 ≤ d - 2 := by omega
        have hnext : Reach D d c (d - 2 - j - 1) :=
          hStep (d - 2 - j - 1) hm (by
            have he : d - 2 - j - 1 + 1 = d - 2 - j := by omega
            rw [he]; exact hprev)
        have he : d - 2 - (j + 1) = d - 2 - j - 1 := by omega
        rwa [he]
    have h := hdesc (d - 2) (le_refl _)
    simpa using h
  obtain ⟨Λ', kω', hΛ'eq, hreachA⟩ := hR0
  have hΛ' : Λ' = Nat.factorial (d - 1) := by simpa using hΛ'eq
  -- ## 2. the endgame constants (the level `S_L` is `A₀`-free)
  obtain ⟨C_L, E_L, S_L, Cn, Mn, hC_Lpos, hS_L, hCnpos, hMn1, hlast⟩ := hLast Λ' kω'
  refine ⟨S_L, hS_L, ?_⟩
  intro A₀ hA₀
  -- ## 3. the level-`0` constants at this `A₀`
  obtain ⟨c₀', e₀', M₀', Cs', hc₀'pos, he₀'1, hM₀'1, hCs'1, hreach⟩ := hreachA A₀ hA₀
  obtain ⟨c₀L, e₀L, hc₀Lpos, he₀L1, hlast2⟩ := hlast 1 e₀' (by norm_num) he₀'1
  -- ## the régime is enlarged once and for all
  set M₀ : ℕ := max M₀' (e₀' * Mn) with hM₀def
  set Cs : ℝ := max 1 (max Cs' (Cn * (4 / (3 * c₀')) ^ Mn)) with hCsdef
  refine ⟨C_L * c₀' ^ E_L, e₀' * E_L, c₀L * c₀' ^ e₀L, e₀' * e₀L, M₀, Cs,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_pos hC_Lpos (pow_pos hc₀'pos E_L)
  · exact mul_pos hc₀Lpos (pow_pos hc₀'pos e₀L)
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  · rw [hM₀def]; exact le_trans hM₀'1 (le_max_left _ _)
  · rw [hCsdef]; exact le_max_left _ _
  · -- ## the datum-level statement
    intro N H f η hN hH2 hf hsup hη0 hη1 hCsle hscale hfam
    have hM₀'le : M₀' ≤ M₀ := by rw [hM₀def]; exact le_max_left _ _
    have hCs'le : Cs' ≤ Cs := by
      rw [hCsdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hCsCn : Cn * (4 / (3 * c₀')) ^ Mn ≤ Cs := by
      rw [hCsdef]; exact le_trans (le_max_right Cs' _) (le_max_right _ _)
    have hM₀ge : e₀' * Mn ≤ M₀ := by rw [hM₀def]; exact le_max_right _ _
    have hCs'e : Cs' ≤ η ^ M₀' * (H : ℝ) := by
      have h1 : η ^ M₀ * (H : ℝ) ≤ η ^ M₀' * (H : ℝ) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hη0.le hη1 hM₀'le)
          (Nat.cast_nonneg H)
      linarith [hCsle, hCs'le, h1]
    -- ## the state at slot level `0`
    obtain ⟨M₁, N₁, γ, hLS, hγlb, hM₁hi, hM₁lo, hamb, hNN₁⟩ :=
      hreach N H f η hN hH2 hf hsup hη0 hη1 hCs'e hscale hI hfam
    have hγ0 : 0 < γ := hLS.1
    have hγ1 : γ ≤ 1 := hLS.2.1
    -- replace the strength by `γt := c₀' η^{e₀'}` (the state is antitone in the strength)
    set γt : ℝ := c₀' * η ^ e₀' with hγtdef
    have hγtpos : 0 < γt := by rw [hγtdef]; exact mul_pos hc₀'pos (pow_pos hη0 e₀')
    have hγtle : γt ≤ γ := by rw [hγtdef]; exact hγlb
    have hγtle1 : γt ≤ 1 := le_trans hγtle hγ1
    have hLS' : LStateBox kω' (pFlat D d c 0 Λ') M₁ (H + 1) N₁ 1 (Abox D 1 H) (fun _ => f) γt :=
      LStateBox_mono hLS hγtle hγtpos
    -- ### the window hypothesis of the last round
    have hH1 : 1 ≤ H := by omega
    have hM₁hi' : (M₁ : ℝ) ≤ ((H : ℝ) + 1) ^ (d - 1) := by simpa using hM₁hi
    have hM₁lo' : c₀' * η ^ e₀' * ((H : ℝ) + 1) ^ (d - 1) ≤ (M₁ : ℝ) := by simpa using hM₁lo
    have hpow_gt : γt ^ e₀' ≤ γt := by
      have h := pow_le_pow_of_le_one hγtpos.le hγtle1 he₀'1
      simpa using h
    have hch : (1 : ℝ) * γt ^ e₀' * ((H : ℝ) + 1) ^ (d - 1) ≤ (M₁ : ℝ) := by
      calc (1 : ℝ) * γt ^ e₀' * ((H : ℝ) + 1) ^ (d - 1)
          = γt ^ e₀' * ((H : ℝ) + 1) ^ (d - 1) := by ring
        _ ≤ γt * ((H : ℝ) + 1) ^ (d - 1) :=
            mul_le_mul_of_nonneg_right hpow_gt (by positivity)
        _ = c₀' * η ^ e₀' * ((H : ℝ) + 1) ^ (d - 1) := by rw [hγtdef]
        _ ≤ (M₁ : ℝ) := hM₁lo'
    -- ### the density hypothesis of the last round: the bad set is empty
    have hpf_ne : ∀ (i : D.S 1) (a : Fin (nD D 1) → ℤ), pFlat D d c 0 Λ' i a ≠ 0 := by
      intro i a
      rw [pFlat_zero]
      have h1 : ((Λ' * d : ℕ) : ℤ) ≠ 0 := by
        have hpos : 0 < Λ' * d :=
          Nat.mul_pos (by rw [hΛ']; exact Nat.factorial_pos _) (by omega)
        exact_mod_cast ne_of_gt hpos
      exact mul_ne_zero h1 hc
    have hfilter : (Abox D 1 H).filter (fun a => ∃ i, pFlat D d c 0 Λ' i a = 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro a - ⟨i, hi⟩
      exact hpf_ne i a hi
    have hdensity : 4 * (((Abox D 1 H).filter
        (fun a => ∃ i, pFlat D d c 0 Λ' i a = 0)).card : ℝ)
        ≤ γt * ((Abox D 1 H).card : ℝ) := by
      rw [hfilter, Finset.card_empty, Nat.cast_zero, mul_zero]
      exact mul_nonneg hγtpos.le (Nat.cast_nonneg _)
    -- ### the threshold hypothesis of the last round
    have hthr : Cn * (3 * γt / 4) ^ (-(Mn : ℤ)) ≤ ((H : ℝ) + 1) := by
      have hcore : Cn * (4 / (3 * c₀')) ^ Mn ≤ η ^ M₀ * (H : ℝ) := le_trans hCsCn hCsle
      have hres := thresholdLe hCnpos hc₀'pos hη0 hη1 hγtpos (le_of_eq hγtdef.symm) hM₀ge hcore
      linarith
    -- ## 4. the last round
    obtain ⟨Lw₀, N', hN₁N', hLw, hnorm⟩ :=
      hlast2 H hH1 M₁ N₁ f γt hLS' hM₁hi' hch hamb hdensity hthr
    refine ⟨Lw₀, N', le_trans hNN₁ hN₁N', ?_, ?_⟩
    · -- the output window
      have h := hLw
      rw [hγtdef, mul_pow, ← pow_mul] at h
      calc (c₀L * c₀' ^ e₀L) * η ^ (e₀' * e₀L) * ((H : ℝ) + 1) ^ d
          = c₀L * (c₀' ^ e₀L * η ^ (e₀' * e₀L)) * ((H : ℝ) + 1) ^ d := by ring
        _ ≤ (Lw₀ : ℝ) := h
    · -- the output uniformity norm
      have hfac : Nat.factorial d = d * Nat.factorial (d - 1) := by
        conv_lhs => rw [show d = (d - 1) + 1 by omega]
        rw [Nat.factorial_succ, show (d - 1) + 1 = d by omega]
      have hcoef : ((Λ' * d : ℕ) : ℤ) = ((Nat.factorial d : ℕ) : ℤ) := by
        rw [Nat.cast_mul, hΛ', hfac]
        push_cast
        ring
      have harith : arithIcc (Λ' * d * c) Lw₀
          = arithIcc ((Nat.factorial d) * c) Lw₀ := by
        congr 1
        rw [show (Λ' * d * c : ℤ) = ((Λ' * d : ℕ) : ℤ) * c from rfl, hcoef]
      have heq : C_L * γt ^ E_L = (C_L * c₀' ^ E_L) * η ^ (e₀' * E_L) := by
        rw [hγtdef, mul_pow, ← pow_mul]
        ring
      rw [heq, harith] at hnorm
      exact hnorm

end

end Work.Prop36SW
