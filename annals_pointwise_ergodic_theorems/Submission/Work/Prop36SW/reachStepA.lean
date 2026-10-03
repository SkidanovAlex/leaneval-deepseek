import Mathlib
import Submission.Work.Prop36SW.chainRun
import Submission.Work.Prop36SW.reachStepAuxPow
import Submission.Work.Prop36SW.reachStepAuxThreshold
import Submission.Work.Prop36SW.reachStepAuxWindow

/-!
# The step of the §5 chain for the `A₀`-free interface (`Work.Prop36SW.reachStepA`)

`Work.Prop36SW.reachStepA` is the state-to-state step of the chain `Reach` of
`Submission/Work/Prop36SW/chainRun.lean`, i.e. the port of `Work.Prop36SW.reachStep` to the
interface in which `Reach` quantifies the scale `A₀` **inside** its constant bundle (so that `Λ` and
`kω` --- hence the level produced by `Work.Prop36SW.chainMain` --- are `A₀`-free; this is the form
consumed by `Work.Peluse.prop36SW_of_ladderA`).

From `Reach D d c (m+1)` and the round hypothesis `RoundAll D d c`, produce `Reach D d c m`.

The round at slot level `m+1 → m` is `Work.Prop36SW.RoundStep D d c m Λ' kω'`, which consumes the
state `LStateBox kω' (pFlat D d c (m+1) Λ') M₁ (H+1) N₁ 1 (Abox D (m+2) H) (fun _ => f) γ` and
produces `LStateBox (regroupKω D (m+1) (fun _ => T')) (pFlat D d c m (Λ'·(d-(m+1)))) M₁' (H+1) N' 1
(Abox D (m+1) H) (fun _ => f) γ'`, together with the window bounds `M₁' ≤ M₁(H+1)`,
`c₁γ^{e₁}M₁(H+1) ≤ M₁'`, the ambient `N₁ ≤ N'` and the strength `C_rγ^{E_r} ≤ γ'`.

The only bookkeeping is to derive the round's *density* hypothesis and its *threshold* hypothesis
from the régime `Cs ≤ η^{M₀}H`, with the constants
`Cs := max Cs' (max (Cd/c₀') (Cn_r·(4/(3c₀'))^{Mn_r}))`, `M₀ := max M₀' (e₀'·Mn_r+1)`,
`c₀ := min (c₁·c₀'^{e₁+1}) (C_r·c₀'^{E_r})`, `e₀ := e₀'·(e₁+1) + e₀'·E_r`.

The three elementary pieces of the bookkeeping are the proved lemmas
`Work.Prop36SW.reachStepAuxPow` (the monomial transfer `c₀'η^{e₀'} ≤ γ ⟹ c₀'^{E_r}η^{e₀} ≤ γ^{E_r}`),
`Work.Prop36SW.reachStepAuxThreshold` (the round's threshold from the régime) and
`Work.Prop36SW.reachStepAuxWindow` (the composition of the two window bounds with the strength and
window invariants).
-/

namespace Work.Prop36SW

noncomputable section

open Work.Peluse.UControl
open Work.Peluse.Prop36SW

theorem reachStepA (D : Work.Peluse.UControl.IdxDatum) (d : ℕ) (c : ℤ)
    (hd : 2 ≤ d) (hc : c ≠ 0) (hR : Work.Prop36SW.RoundAll D d c) :
    ∀ m : ℕ, m + 1 ≤ d - 2 → Work.Prop36SW.Reach D d c (m + 1) →
      Work.Prop36SW.Reach D d c m := by
  intro m hm hreach
  classical
  obtain ⟨Λ', kω', hΛ'eq, hreach_out⟩ := hreach
  have hm2 : m + 2 ≤ d := by omega
  have hjm : m + 2 ≤ d - 1 := by omega
  have hΛ'fact : Λ' ≤ Nat.factorial (d - 1) := by
    rw [hΛ'eq]; exact Nat.factorial_le (by omega)
  -- the new coefficient numerator
  have hΛeq : Λ' * (d - (m + 1)) = Nat.factorial (d - 1 - m) := by
    rw [hΛ'eq]
    have h1 : Nat.factorial (d - 1 - m)
        = (d - 1 - m) * Nat.factorial (d - 1 - (m + 1)) := by
      have hA : d - 1 - (m + 1) = d - 2 - m := by omega
      have hB : d - 1 - m = (d - 2 - m) + 1 := by omega
      rw [hB, Nat.factorial_succ, hA]
    rw [h1]
    have h2 : d - (m + 1) = d - 1 - m := by omega
    rw [h2, Nat.mul_comm]
  by_cases hk : 1 ≤ Fintype.card (D.S (m + 2))
  · -- ## the non-degenerate case: the round is available
    obtain ⟨C_r, E_r, Cn_r, Mn_r, T', c₁, e₁, hC_r, hCn_r, hMn_r, hT', hc₁, he₁, hround⟩ :=
      hR m Λ' kω' hk hm2 hΛ'fact
    refine ⟨Λ' * (d - (m + 1)), regroupKω D (m + 1) (fun _ => T'), hΛeq, ?_⟩
    intro A₀ hA₀
    obtain ⟨c₀', e₀', M₀', Cs', hc₀'pos, he₀'1, hM₀'1, hCs'1, hreachA⟩ := hreach_out A₀ hA₀
    -- ## the new constants
    set Cd : ℝ := 4 * ((Fintype.card (D.S (m + 2)) * (m + 1) : ℕ) : ℝ) + 1 with hCddef
    set c₀ : ℝ := min (c₁ * c₀' ^ (e₁ + 1)) (C_r * c₀' ^ E_r) with hc₀def
    set e₀ : ℕ := e₀' * (e₁ + 1) + e₀' * E_r with he₀def
    set M₀ : ℕ := max M₀' (e₀' * Mn_r + 1) with hM₀def
    set Cs : ℝ := max Cs' (max (Cd / c₀') (Cn_r * (4 / (3 * c₀')) ^ Mn_r)) with hCsdef
    refine ⟨c₀, e₀, M₀, Cs, ?_, ?_, ?_, ?_, ?_⟩
    · -- `0 < c₀`
      rw [hc₀def]
      exact lt_min (mul_pos hc₁ (pow_pos hc₀'pos _)) (mul_pos hC_r (pow_pos hc₀'pos _))
    · -- `1 ≤ e₀`
      rw [he₀def]
      have h1 : 1 ≤ e₀' * (e₁ + 1) := by
        have : 0 < e₀' * (e₁ + 1) := Nat.mul_pos (by omega) (by omega)
        omega
      omega
    · -- `1 ≤ M₀`
      rw [hM₀def]; omega
    · -- `1 ≤ Cs`
      rw [hCsdef]; exact le_trans hCs'1 (le_max_left _ _)
    · -- ## the datum-level step
      intro N H f η hN hH hf hsupp hη0 hη1 hCs hA₀N hI hfam
      have hM₀'le : M₀' ≤ M₀ := by rw [hM₀def]; exact le_max_left _ _
      have hCs'le : Cs' ≤ Cs := by rw [hCsdef]; exact le_max_left _ _
      have hCs' : Cs' ≤ η ^ M₀' * (H : ℝ) := by
        have h1 : η ^ M₀ * (H : ℝ) ≤ η ^ M₀' * (H : ℝ) :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_of_le_one hη0.le hη1 hM₀'le) (Nat.cast_nonneg H)
        linarith [hCs, hCs'le, h1]
      -- ### the `Reach (m+1)` state
      obtain ⟨M₁, N₁, γ, hst, hγ_low, hM₁hi, hM₁lo, hamb, hNN₁⟩ :=
        hreachA N H f η hN hH hf hsupp hη0 hη1 hCs' hA₀N hI hfam
      have hγ0 : 0 < γ := hst.1
      -- ### the density hypothesis of the round
      have hCd_le : Cd ≤ γ * (H : ℝ) := by
        have hdiv : Cd / c₀' ≤ η ^ M₀ * (H : ℝ) := by
          have h2 : Cd / c₀' ≤ Cs := by
            rw [hCsdef]
            exact le_trans (le_max_left (Cd / c₀') _) (le_max_right Cs' _)
          linarith [hCs, h2]
        have h3 : Cd ≤ (η ^ M₀ * (H : ℝ)) * c₀' := (div_le_iff₀ hc₀'pos).mp hdiv
        have he' : e₀' ≤ M₀ := by
          rw [hM₀def]
          have h2 : e₀' * 1 ≤ e₀' * Mn_r := Nat.mul_le_mul_left _ hMn_r
          have h4 : e₀' ≤ e₀' * Mn_r := by simpa using h2
          exact le_trans (Nat.le_succ_of_le h4) (le_max_right _ _)
        have hηle : η ^ M₀ ≤ η ^ e₀' := pow_le_pow_of_le_one hη0.le hη1 he'
        have h4 : c₀' * η ^ M₀ ≤ γ :=
          calc c₀' * η ^ M₀ ≤ c₀' * η ^ e₀' := mul_le_mul_of_nonneg_left hηle hc₀'pos.le
            _ ≤ γ := hγ_low
        calc Cd ≤ (η ^ M₀ * (H : ℝ)) * c₀' := h3
          _ = (c₀' * η ^ M₀) * H := by ring
          _ ≤ γ * H := mul_le_mul_of_nonneg_right h4 (by positivity)
      have hdens_core : 4 * ((Fintype.card (D.S (m + 2)) * (m + 1) : ℕ) : ℝ)
          ≤ γ * (2 * (H : ℝ) + 1) := by
        rw [hCddef] at hCd_le
        nlinarith [hCd_le, hγ0.le, Nat.cast_nonneg (α := ℝ) H]
      have hΛ'ne : Λ' ≠ 0 := by rw [hΛ'eq]; exact Nat.factorial_ne_zero _
      have hdens := badSetDensity D d (m + 1) Λ' H c γ hc hΛ'ne (by omega) (by omega) hdens_core
      -- ### the threshold hypothesis of the round
      have hthr_core : Cn_r * (4 / (3 * c₀')) ^ Mn_r ≤ η ^ M₀ * (H : ℝ) := by
        have h2 : Cn_r * (4 / (3 * c₀')) ^ Mn_r ≤ Cs := by
          rw [hCsdef]
          exact le_trans (le_max_right (Cd / c₀') _) (le_max_right Cs' _)
        linarith [hCs, h2]
      have hthr : Cn_r * (3 * γ / 4) ^ (-(Mn_r : ℤ)) ≤ (H : ℝ) + 1 := by
        have hk' : e₀' * Mn_r ≤ M₀ := by
          rw [hM₀def]
          exact le_trans (Nat.le_succ _) (le_max_right _ _)
        have h' := reachStepAuxThreshold hCn_r hc₀'pos hη0 hη1 hγ0 hγ_low hk' hthr_core
        linarith
      -- ### the round
      obtain ⟨M₁', N', γ', hγ'0, hγ'1, hM₁'hi, hM₁'lo, _, hNN', hγ'str, hst'⟩ :=
        hround H (by omega) M₁ N₁ f γ hst hM₁hi hamb hdens hthr
      refine ⟨M₁', N', γ', hst', ?_, ?_, ?_, ?_, ?_⟩
      · -- strength: `c₀ η^{e₀} ≤ γ'`
        have hc₀_le : c₀ ≤ C_r * c₀' ^ E_r := by rw [hc₀def]; exact min_le_right _ _
        have he₀_ge : e₀' * E_r ≤ e₀ := by rw [he₀def]; omega
        have hme := reachStepAuxPow hc₀'pos.le hη0 hη1 hγ_low he₀_ge
        calc c₀ * η ^ e₀ ≤ (C_r * c₀' ^ E_r) * η ^ e₀ :=
              mul_le_mul_of_nonneg_right hc₀_le (pow_nonneg hη0.le _)
          _ = C_r * (c₀' ^ E_r * η ^ e₀) := by ring
          _ ≤ C_r * γ ^ E_r := mul_le_mul_of_nonneg_left hme hC_r.le
          _ ≤ γ' := hγ'str
      · -- window upper bound
        have hpow : ((H : ℝ) + 1) ^ (d - 1 - (m + 1)) * ((H : ℝ) + 1)
            = ((H : ℝ) + 1) ^ (d - 1 - m) := by
          rw [← pow_succ]
          congr 1
          omega
        calc (M₁' : ℝ) ≤ (M₁ : ℝ) * ((H : ℝ) + 1) := hM₁'hi
          _ ≤ ((H : ℝ) + 1) ^ (d - 1 - (m + 1)) * ((H : ℝ) + 1) :=
                mul_le_mul_of_nonneg_right hM₁hi (by positivity)
          _ = ((H : ℝ) + 1) ^ (d - 1 - m) := hpow
      · -- window lower bound
        have hee : d - 1 - (m + 1) = d - 2 - m := by omega
        have hee2 : d - 1 - m = (d - 2 - m) + 1 := by omega
        have hX0 : (0 : ℝ) ≤ (H : ℝ) + 1 := by positivity
        have hXm0 : (0 : ℝ) ≤ ((H : ℝ) + 1) ^ (d - 2 - m) := pow_nonneg hX0 _
        have hc₀_le : c₀ ≤ c₁ * c₀' ^ (e₁ + 1) := by rw [hc₀def]; exact min_le_left _ _
        have he₀_ge : e₀' * (e₁ + 1) ≤ e₀ := by rw [he₀def]; omega
        have hstep3 : c₀' * η ^ e₀' * ((H : ℝ) + 1) ^ (d - 2 - m) ≤ (M₁ : ℝ) := by
          simpa only [hee] using hM₁lo
        have hY : ((H : ℝ) + 1) ^ (d - 1 - m)
            = ((H : ℝ) + 1) ^ (d - 2 - m) * ((H : ℝ) + 1) := by
          rw [hee2, pow_succ]
        rw [hY]
        exact reachStepAuxWindow hc₁.le hc₀'pos hη0 hη1 hγ0.le hXm0 hX0 hc₀_le he₀_ge
          hγ_low hstep3 hM₁'lo
      · -- ambient
        exact le_trans hamb (by exact_mod_cast hNN')
      · -- `N ≤ N'`
        exact le_trans hNN₁ hNN'
  · -- ## the degenerate case: the slot type is empty, no round is needed
    refine ⟨Λ' * (d - (m + 1)), regroupKω D (m + 1) (fun _ => 1), hΛeq, ?_⟩
    intro A₀ hA₀
    refine ⟨1, 1, 1, 1, ?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · intro N H f η hN hH hf hsupp hη0 hη1 hCs hA₀N hI hfam
      have hcon : 1 ≤ Fintype.card (D.S (m + 2)) := card_S_pos_of_card_I D d hI hjm
      exact absurd hcon hk

end

end Work.Prop36SW
