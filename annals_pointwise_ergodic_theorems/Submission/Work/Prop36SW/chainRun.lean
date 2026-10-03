import Mathlib
import Submission.Work.Prop36SW.chainDefs
import Submission.Work.Prop36SW.chainEntry
import Submission.Work.Prop36SW.LStateBoxMonoAmbient
import Submission.Work.Prop36SW.LStateBoxAbsIff
import Submission.Work.Prop36SW.pFlat_dirBound
import Submission.Work.Peluse.Prop36SW.roundUnpeel

/-!
# `Reach`: the state-reachability predicate of the §5 chain

`Work.Prop36SW.Reach D d c A₀ m` says: the chain has reached slot level `m`, with data-independent
constants `Λ, kω, c₀, e₀, M₀, Cs`, and, for every datum `(N, H, f, η)` satisfying the entry
conditions and the régime `Cs ≤ η^{M₀}·H`, produces a state at slot level `m` whose

* window satisfies `c₀ η^{e₀} (H+1)^{d-1-m} ≤ M₁ ≤ (H+1)^{d-1-m}`,
* ambient satisfies `ambK D d c · (H+1)^d ≤ N₁`,
* strength satisfies `c₀ η^{e₀} ≤ γ`,
* coefficient is `pFlat D d c m Λ` with `Λ = (d - 1 - m)!`,

with `m + 1` the slot level's parameter type and `H+1` the box window `M₂ = H+1`
(`Abox D (m+1) H = Icc(-H,H)^{S 0..m}` is the ladder's box `paramBox M₂`).

The régime `Cs ≤ η^{M₀}H` is what makes every subsequent round's *density* hypothesis
(`Work.Prop36SW.badSetDensity`) and *threshold* hypothesis hold, with `M₀` and `Cs` enlarged once
and for all as the chain descends.  It is supplied at the top by the régime `x > 1` of the target
(see `NOTES_prop36SW_of_ladderA_SESSION11.md` §3(c)).

## The entry `reachEntry`

**Do not use `Work.Prop36SW.chainEntry`.**  Its coefficient hypothesis
`|slotCoeff D d c (d-2) s (D.pad (d-1) a)| ≤ 2|c|·d!·(card (D.S (d-1))+1)^{d-2}·(H+1)^{d-2}` is
*false* for some legitimate `IdxDatum`: the correct bound involves the *sum* `sSup D d` of the slot
counts (the direction polynomial at level `d-2` reads all the levels `0 ≤ j ≤ d-2`), e.g.
`|S 1| = 7, |S 2| = 3, |S 3| = 2` with `d = 4` gives `|slotCoeff| = 504|c|H² > 432|c|(H+1)²`
against the stated right-hand side.

Instead re-derive the entry from the *proved* ingredients directly:

1. `Work.Prop36SW.initialStateBox D (d-2) c N H f η` (`chainEntry.lean`), whose coefficient
   hypothesis `hbound` is the *absolute* bound `|slotCoeff|·(H+1)² ≤ N` — satisfiable at an inflated
   ambient `N₀ := (Ccoef + 1) * N` with `Ccoef := 2·|c|·d!·(sSup D d + 1)^{d-2}·A₀`, since
   `|slotCoeff|·(H+1)² ≤ 2|c|d!(sSup+1)^{d-2}(H+1)^d ≤ Ccoef·N` by `Work.Prop36SW.pFlat_dirBound`
   and `(H+1)^d ≤ A₀N`;
2. `Work.Prop36SW.famAvg_window_ratio_le` (or `Work.Prop36SW.exists_windowBound`) to transport the
   family average `η ≤ D.famAvg d H c N f` to the window `N₀`, at the cost of a data-independent
   factor: `η/Ce ≤ D.famAvg d H c N₀ f` with `Ce := 2·Ccoef + 3`;
3. `Work.Prop36SW.LStateBoxAbsIff` to replace the absolute-value coefficient
   `|slotCoeff D d c (d-2) s (D.pad (d-1) (D.decD D (d-1) x))|` by `pFlat D d c (d-2) 1 s x`
   (`pFlat_one`);
4. `Work.Prop36SW.LStateBoxMonoAmbient` to inflate `N₀ → N₂ := max N₀ ⌈ambK D d c · (H+1)^d⌉`
   (`Nat.le_ceil`), whose ratio is data-independent because `N₀ ≥ N ≥ (H+1)^d/A₀` and
   `ambK·(H+1)^d ≤ ambK·A₀·N`.

The régime `Cs ≤ η^{M₀}H` (`M₀ = 1`) supplies the *density* hypothesis of `initialStateBox`
through `Work.Prop36SW.badSetDensity`, and `hI : 2 ≤ card (D.I (d-1))` supplies the positive slot
counts `1 ≤ card (D.S j)` for all `j ≤ d-1` (`Work.Prop36SW.card_S_pos_of_card_I`).  The output is
`⟨1, fun _ => 1, c₀, 1, 1, Cs⟩` with `c₀` the product of the three data-independent conversion
factors (times `2^{-(1+2·card (D.I (d-1)))}`) and `Cs` chosen so that `c₀·Cs ≥ 32·(sSup D d +
1)·(d+1) ≥ 4·card (D.S (d-1))·(d-2)`.

## The step `reachStep`

From `Reach D d c A₀ (m+1)` (constants `Λ', kω', c₀', e₀', M₀', Cs'`) to `Reach D d c A₀ m`, given
`RoundAll D d c` and `m + 1 ≤ d - 2`:

* `RoundAll D d c` at `(m, Λ', kω')` (with `hk := card_S_pos_of_card_I`, `hm : m+2 ≤ d`,
  `hΛ' : Λ' ≤ (d-1)!`) gives `RoundStep D d c m Λ' kω'` with data-independent
  `C_r E_r Cn_r Mn_r T' c₁ e₁`;
* the new constants are `Λ := Λ'*(d-(m+1))` (so `Λ = (d-1-m)!`), `kω := regroupKω D (m+1)
  (fun _ => T')`, `e₀ := e₀'*(e₁+1) + e₀'*E_r`, `c₀ := min (c₁*c₀'^(e₁+1)) (C_r*c₀'^E_r)`,
  `M₀ := max M₀' (e₀'*Mn_r + 1)` and `Cs := max Cs' (max (Cd/c₀') (Cn_r*(4/3)^Mn_r/c₀'))`
  with `Cd := 4*((card (D.S (m+1))*(m+1) : ℕ) : ℝ) + 1`;
* `Cs ≤ η^{M₀}H` gives `Cs' ≤ η^{M₀'}H` (as `M₀ ≥ M₀'`, `η ≤ 1`), the *density*
  `4*card (D.S (m+1))*(m+1) ≤ γ*(2H+1)` (via `γ ≥ c₀'η^{e₀'}` and `M₀ ≥ e₀'`) and the *threshold*
  `Cn_r*(3γ/4)^{-Mn_r} ≤ H+1` (via `γ ≥ c₀'η^{e₀'}` and `M₀ ≥ e₀'*Mn_r`);
* the invariants transfer: the window upper bound by `M₁' ≤ M₁(H+1) ≤ (H+1)^{d-1-m}`, the window
  lower bound by `M₁' ≥ c₁γ^{e₁}M₁(H+1) ≥ c₁(c₀'η^{e₀'})^{e₁+1}(H+1)^{d-1-m}`, the ambient by
  `ambK(H+1)^d ≤ N₁ ≤ N₁'`, and the strength by `γ' ≥ C_rγ^{E_r} ≥ C_r(c₀'η^{e₀'})^{E_r}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
open scoped BigOperators

namespace Work.Prop36SW

noncomputable section

open Work.Peluse
open Work.Peluse.UControl
open Work.Peluse.Prop36SW

/-- **The state-reachability predicate of the §5 chain.**

The constants `Λ` (the state's coefficient numerator, `= (d-1-m)!`) and `kω` (the multiplicity
function of the state's direction family) are quantified **before** `A₀`: the target
`Work.Peluse.C46.Prop36SW` chooses its level `s` *before* `A₀`, and the chain's level is
`max ((card (D.S 1)) * T') 2` with `T'` coming from `Work.Prop36SW.RoundAll` at the (fixed)
multiplicity functions `kω`, so it must be `A₀`-free.  The remaining constants `c₀, e₀, M₀, Cs`
(which absorb the `A₀`-dependent ambient inflations) may depend on `A₀`. -/
def Reach (D : IdxDatum) (d : ℕ) (c : ℤ) (m : ℕ) : Prop :=
  ∃ (Λ : ℕ) (kω : SlotSet (D.S (m + 1)) (fun _ => 1) → ℕ),
    Λ = Nat.factorial (d - 1 - m) ∧
    ∀ (A₀ : ℝ), 1 ≤ A₀ → ∃ (c₀ : ℝ) (e₀ : ℕ) (M₀ : ℕ) (Cs : ℝ),
      0 < c₀ ∧ 1 ≤ e₀ ∧ 1 ≤ M₀ ∧ 1 ≤ Cs ∧
      ∀ (N H : ℕ) (f : ℤ → ℂ) (η : ℝ),
        1 ≤ N → 2 ≤ H → (∀ x : ℤ, ‖f x‖ ≤ 1) → SupportIn f N →
        0 < η → η ≤ 1 → Cs ≤ η ^ M₀ * (H : ℝ) →
        ((H : ℝ) + 1) ^ d ≤ A₀ * N →
        2 ≤ Fintype.card (D.I (d - 1)) →
        η ≤ D.famAvg d H c N f →
        ∃ (M₁ N₁ : ℕ) (γ : ℝ),
          LStateBox kω (pFlat D d c m Λ) M₁ (H + 1) N₁ 1 (Abox D (m + 1) H) (fun _ => f) γ ∧
          c₀ * η ^ e₀ ≤ γ ∧
          (M₁ : ℝ) ≤ ((H : ℝ) + 1) ^ (d - 1 - m) ∧
          c₀ * η ^ e₀ * ((H : ℝ) + 1) ^ (d - 1 - m) ≤ (M₁ : ℝ) ∧
          ambK D d c * ((H : ℝ) + 1) ^ d ≤ (N₁ : ℝ) ∧ N ≤ N₁

theorem card_S_pos_of_card_I (D : IdxDatum) (d : ℕ) (hI : 2 ≤ Fintype.card (D.I (d - 1)))
    {j : ℕ} (hj : j ≤ d - 1) : 1 ≤ Fintype.card (D.S j) := by
  classical
  have hstep : ∀ j, Nonempty (D.S (j + 1)) → Nonempty (D.S j) := by
    intro j ⟨s⟩
    obtain ⟨t, _⟩ := (D.par j s).2
    exact ⟨t⟩
  have htop : Nonempty (D.S (d - 1)) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have hIe : IsEmpty (D.I (d - 1)) :=
      ⟨fun T => (h : IsEmpty (D.S (d - 1))).false (T.2.choose)⟩
    have hc : Fintype.card (D.I (d - 1)) = 0 := Fintype.card_eq_zero_iff.mpr hIe
    omega
  have hdesc : ∀ k, k ≤ d - 1 → Nonempty (D.S (d - 1 - k)) := by
    intro k
    induction k with
    | zero => intro _; simpa using htop
    | succ k ih =>
      intro hk
      have hk' : k ≤ d - 1 := by omega
      have h1 : Nonempty (D.S (d - 1 - k)) := ih hk'
      have h2 : d - 1 - k = (d - 2 - k) + 1 := by omega
      rw [h2] at h1
      have h3 : d - 1 - (k + 1) = d - 2 - k := by omega
      rw [h3]
      exact hstep _ h1
  have hne : Nonempty (D.S j) := by
    have hk : d - 1 - j ≤ d - 1 := by omega
    have h := hdesc (d - 1 - j) hk
    rwa [Nat.sub_sub_self hj] at h
  exact Fintype.card_pos_iff.mpr hne

/-- **The chain**: from the entry (`Reach D d c A₀ (d-2)`) and the step-down and endgame
interfaces, produce the data-independent constants `S, C, E, c₀, e₀, M₀, Cs` of the §5 chain and
the uniformity-norm-power conclusion at the coefficient `d!·c`. -/
theorem chainMain_wip (D : IdxDatum) (d : ℕ) (c : ℤ) (hd : 2 ≤ d)
    (hc : c ≠ 0)
    (hEntry : Reach D d c (d - 2))
    (hStep : ∀ m : ℕ, m + 1 ≤ d - 2 → Reach D d c (m + 1) → Reach D d c m)
    (hLast : ∀ (Λ : ℕ) (kω : SlotSet (D.S 1) (fun _ => 1) → ℕ), LastStep D d c Λ kω)
    (hI : 2 ≤ Fintype.card (D.I (d - 1))) :
    ∃ (S : ℕ),
      2 ≤ S ∧
      ∀ (A₀ : ℝ), 1 ≤ A₀ →
        ∃ (C : ℝ) (E : ℕ) (c₀ : ℝ) (e₀ : ℕ) (M₀ : ℕ) (Cs : ℝ),
          0 < C ∧ 0 < c₀ ∧ 1 ≤ e₀ ∧ 1 ≤ M₀ ∧ 1 ≤ Cs ∧
          ∀ (N H : ℕ) (f : ℤ → ℂ) (η : ℝ),
            1 ≤ N → 2 ≤ H → (∀ x : ℤ, ‖f x‖ ≤ 1) → SupportIn f N →
            0 < η → η ≤ 1 → Cs ≤ η ^ M₀ * (H : ℝ) →
            ((H : ℝ) + 1) ^ d ≤ A₀ * N → η ≤ D.famAvg d H c N f →
            ∃ (Lw₀ N' : ℕ),
              N ≤ N' ∧ c₀ * η ^ e₀ * ((H : ℝ) + 1) ^ d ≤ (Lw₀ : ℝ) ∧
              C * η ^ E ≤ uNormPow S (arithIcc ((Nat.factorial d) * c) Lw₀) (symIcc N') f := by
  sorry

end

end Work.Prop36SW
