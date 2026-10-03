/-
# The periodised-window facts for the modified `f`-side bump `varphiNtj`

This module proves `Work.KMTPlan.A6.varphiNtjPeriodize_aux`, the `1 ≤ N` version of the frozen
statement `Work.KMTPlan.A6.VarphiNtjPeriodize` (`KMTPlan/A6/VarphiNtjPeriodize.lean`).  It is the
band half of the model-input statement `MdlSliceFband`, i.e. it supplies simultaneously

* the pointwise bound of `periodize (varphiNtj N k j t)` (the symbol bound `TleMemLp`/`TleBand`
  want), with the explicit witness `M = (Finset.Icc (-(⌊g⌋+2)) (⌊g⌋+1)).card * 8`,
  `g = 2^{k − logN N}` — the `card` being the number of integers `k'` with `|x_θ + k'| ≤ g`;
* `MemLp (periodize (varphiNtj N k j t)) ⊤ circleMeasure`;
* the arc: `periodize (varphiNtj N k j t) θ ≠ 0 → θ ∈ arcSet 0 g`.

## Why `1 ≤ N`

Every consumer has `N = ⌊a n⌋ ≥ 1`.  For `N = 0` the weight `2^{−k}·0·ξ` vanishes, so
`varphiNtj 0 k j t` is identically zero for `j ≠ 0` and equals `varphiNt 0 k t` for `j = 0`
(where `logN 0 = Nat.log 2 (max 0 2) = 1`); both cases are trivial against
`A7Hi.varphiNt_support_le_all` and `‖varphiNt‖ ≤ 1`.

## The proof, and two traps (both cost a REPL round trip)

* All three conjuncts come from **three** sorry-free facts: `MdlPktMemLp.varphiNtj_support_le_pkt`
  (support radius `g`, *no* `j ≠ −1` condition), `lowModSymbFAux.norm_varphiNtj_le_eight`
  (`‖varphiNtj N k j t x‖ ≤ 8` uniformly in `t, x`; its hypothesis `k ≠ 0 ∨ 0 ≤ j` is exactly what
  `hj` + `hk` give), and `IonescuWainger.memLp_periodize`, whose hypotheses are only *measurable*,
  *supported in `[-R,R]`* and *bounded by `C`* — **no smoothness, no integrability, hence no
  `t ∈ [1/2,1]` restriction** (`varphiNtj_bounds`/`periodizeMemLpTop` are *not* needed, and the
  `t`-dependence never has to be touched: the modulation has modulus `1`).
* The counting is the content: `periodize φ θ = ∑'_m φ (x_θ + m)` and every `k'` outside
  `Finset.Icc (-(⌊g⌋+2)) (⌊g⌋+1)` has a vanishing term because `x_θ ∈ [0,1)` forces
  `|x_θ + k'| > g` (`Int.floor_le`, `Int.lt_floor_add_one`); `tsum_eq_sum` turns the `tsum` into
  that finite sum, and `norm_sum_le` + the `8`-bound give `card · 8`.  The arc conjunct is the
  contrapositive: if every term vanished the `tsum` would be `0`; otherwise `|x_θ + k'| ≤ g` and
  `θ = ((x_θ + k' : ℝ) : Circle)` is the `arcSet 0 g` witness.
* **Trap 1:** `push_neg` turns `¬(a ≤ k' ∧ k' ≤ b)` into the *implication* `a ≤ k' → b < k'`,
  not a disjunction — so the case split must be `by_cases hle : a ≤ k'` followed by `hk'mem hle`
  (resp. `not_le.mp hle`), not `rcases`.
* **Trap 2:** `linarith` does not close the `k'` large comparison even with every cast fact in
  scope; it must be the explicit chain
  `g < ↑⌊g⌋ + 1 ≤ ↑⌊g⌋ + 2 ≤ ↑k' ≤ ↑x_θ + ↑k'` (with the casts carried through `exact_mod_cast`
  and `push_cast`).

## How to use this lemma: the recipe for `TleBandVarphiNtj`

This module is a `depends_on` of `Work.KMTPlan.A6.TleBandVarphiNtj`, whose statement is
`TleBand` instantiated at the model window `φ := varphiNtj N k j t`, `γ := 2^{k − logN N}`.
**Its proof is the body of `A7HiRep/incFamBandLimitedL2.exists_hasFreqSupport_kmtProj`
(`A7HiRep/incFamBandLimitedL2.lean:118–162`) copied verbatim** under three substitutions

* `kmtProj ρ l k f ↝ Tle ρ l (varphiNtj N k j t) F`,
* `periodize (etaCut kmtEta k) ↝ periodize (varphiNtj N k j t)`,
* `incArc ρ l k ↝ ⋃ α ∈ iwArithFreqs ρ l, arcSet α γ`, `γ := 2^{k − logN N}`,

with every generic link shared unchanged: `hsym` from `memLp_iwSymbolSet A` applied to **this
module's second conjunct** (`MemLp (periodize (varphiNtj N k j t)) ⊤ circleMeasure`);
`hconvOp : ⇑(iwOpSet A Ψ hsym) F₀ = Tle ρ l (varphiNtj N k j t) F` by
`rw [← iwConvEqIwOpSetMemlp hsym F₀]; rfl` (the `rfl` fires because `Tle = iwConv A Ψ`);
`hconv` by `simpa only [iwOpSet, multiplierOf, hσ] using hconvOp`; the 15-line
`ftLp_opMul`/`fourierZ_multiplier`/`fourierZ.injective` block for `hopEq`, unchanged; and the
final `exists_hasFreqSupport_congr (hopEq.trans hconv) ⟨opMul_memℓp …, hasFreqSupport_opMul … hΦ⟩`
— which **also yields the `Memℓp` witness**, so no separate `TleMemLp` step is needed (do *not*
import `KMTPlan/A6/TleBand` or `KMTPlan/A6/TleMemLp`: they still carry `sorry` and importing
them imports `sorryAx`).

**The only new step is `hΦ`** (the `etaCut` analogue is the lemma
`iwSymbolSet_etaCut_support_incArc`, which does not exist for a general `φ` — hence inline):

```lean
have hΦ : ∀ᵐ ξ ∂circleMeasure,
    ξ ∉ ⋃ α ∈ iwArithFreqs ρ l, arcSet α γ → ((hsym.toLp σ : Circ → ℂ)) ξ = 0 := by
  filter_upwards [MeasureTheory.MemLp.coeFn_toLp hsym] with ξ hξ hmem
  rw [hξ]; by_contra hne
  rw [hσ, hA, hΨ] at hne
  -- `hne : iwSymbolSet A Ψ ξ ≠ 0`, i.e. `∑ α ∈ A, Ψ (ξ - α) ≠ 0`
  obtain ⟨α, hαA, hαne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  -- `(hφsupp (ξ - α)) hαne : ξ - α ∈ arcSet 0 γ`; transfer to `ξ ∈ arcSet α γ` by unfolding
  -- `arcSet α γ = {ξ | ∃ θ, |θ| ≤ γ ∧ ξ = α + θ}` with the same witness `θ`.
  exact hmem ⟨α, hαA, hφsupp (ξ - α) hαne⟩
```

where `hφsupp` is **this module's third conjunct** (stated in the `arcSet 0 γ` form).  The
`arcSet` transfer is definitional: `ξ - α ∈ arcSet 0 γ` gives `θ` with `|θ| ≤ γ` and `ξ - α = θ`,
hence `ξ = α + θ`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlPktMemLp
import Submission.Work.KMTAreas.A7Hi.windowEnvelopesHasFreqSupport

namespace Work.KMTPlan.A6

theorem varphiNtjPeriodize_aux (N k : ℕ) (j : ℤ) (t : ℝ)
    (hj : j ∈ ({-1, 0, 1} : Finset ℤ)) (hk : k = 0 → j ≠ -1) (hN : 1 ≤ N) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ θ : Work.Analysis.IonescuWainger.Circle,
        ‖Work.Analysis.IonescuWainger.periodize (varphiNtj N k j t) θ‖ ≤ M) ∧
      MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize (varphiNtj N k j t))
        ⊤ Work.Analysis.IonescuWainger.circleMeasure ∧
      (∀ θ : Work.Analysis.IonescuWainger.Circle,
        Work.Analysis.IonescuWainger.periodize (varphiNtj N k j t) θ ≠ 0 →
        θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0
          ((2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) := by
  classical
  have hk' : k ≠ 0 ∨ 0 ≤ j := by
    by_cases h0 : k = 0
    · right
      have hj' : j = -1 ∨ j = 0 ∨ j = 1 := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hj
      rcases hj' with h | h | h
      · exact absurd h (hk h0)
      · omega
      · omega
    · exact Or.inl h0
  set g : ℝ := (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) with hg
  have hg0 : 0 ≤ g := by rw [hg]; positivity
  have hgf : (0 : ℝ) ≤ ((⌊g⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.floor_nonneg.mpr hg0
  have hlt : ((⌊g⌋ : ℤ) : ℝ) ≤ g := Int.floor_le g
  have hgt : g < ((⌊g⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one g
  have hsupp : ∀ ξ : ℝ, varphiNtj N k j t ξ ≠ 0 → |ξ| ≤ g := by
    intro ξ hξ; rw [hg]; exact Work.KMTPlan.A6.varphiNtj_support_le_pkt N k j t ξ hξ
  have hφ0 : ∀ ξ : ℝ, g < |ξ| → varphiNtj N k j t ξ = 0 := by
    intro ξ hξ; by_contra hne; exact absurd (hsupp ξ hne) (not_le.mpr hξ)
  have hb8 : ∀ x : ℝ, ‖varphiNtj N k j t x‖ ≤ 8 :=
    fun x => Work.KMTPlan.A6.norm_varphiNtj_le_eight N k j hj hk' hN t x
  set S : Finset ℤ := Finset.Icc (-(⌊g⌋ + 2)) (⌊g⌋ + 1) with hS
  have hkey : ∀ θ : Work.Analysis.IonescuWainger.Circle,
      Work.Analysis.IonescuWainger.periodize (varphiNtj N k j t) θ
        = ∑ k' ∈ S, varphiNtj N k j t
            ((AddCircle.equivIco (1 : ℝ) 0 θ).val + (k' : ℝ)) := by
    intro θ
    change (∑' k' : ℤ, varphiNtj N k j t
      ((AddCircle.equivIco (1 : ℝ) 0 θ).val + (k' : ℝ))) = _
    refine tsum_eq_sum (s := S) (fun k' hk'mem => ?_)
    refine hφ0 _ ?_
    have hval : ((AddCircle.equivIco (1 : ℝ) 0 θ).val : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
      simpa using (AddCircle.equivIco (1 : ℝ) 0 θ).2
    rw [hS, Finset.mem_Icc] at hk'mem
    push_neg at hk'mem
    by_cases hle : -(⌊g⌋ + 2) ≤ k'
    · have h1 : (⌊g⌋ + 2 : ℤ) ≤ k' := by have := hk'mem hle; omega
      have hcast : ((⌊g⌋ : ℤ) : ℝ) + 2 ≤ (k' : ℝ) := by
        have h2 : (((⌊g⌋ + 2 : ℤ)) : ℝ) ≤ ((k' : ℤ) : ℝ) := by exact_mod_cast h1
        push_cast at h2
        linarith
      rw [abs_of_pos (by linarith [hval.1, hcast, hgf])]
      calc g < ((⌊g⌋ : ℤ) : ℝ) + 1 := hgt
        _ ≤ ((⌊g⌋ : ℤ) : ℝ) + 2 := by linarith
        _ ≤ (k' : ℝ) := hcast
        _ ≤ ((AddCircle.equivIco (1 : ℝ) 0 θ).val : ℝ) + (k' : ℝ) := by linarith [hval.1]
    · have h1 : k' ≤ -(⌊g⌋ + 2) - 1 := by have := not_le.mp hle; omega
      have hcast : (k' : ℝ) ≤ -(((⌊g⌋ : ℤ)) : ℝ) - 3 := by
        have h2 : ((k' : ℤ) : ℝ) ≤ ((-(⌊g⌋ + 2) - 1 : ℤ) : ℝ) := by exact_mod_cast h1
        push_cast at h2
        linarith
      rw [abs_of_neg (by linarith [hval.1, hval.2, hcast, hgf])]
      linarith [hval.2]
  refine ⟨((S.card : ℕ) : ℝ) * 8, by positivity, ?_, ?_, ?_⟩
  · intro θ
    rw [hkey θ]
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun k' _ => hb8 _)) ?_
    simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  · exact Work.Analysis.IonescuWainger.memLp_periodize
      (Work.KMTPlan.A6.measurable_varphiNtj' N k j t) hg0 hφ0 hb8
  · intro θ hθ
    by_contra hmem
    have hzero : ∀ k' : ℤ, varphiNtj N k j t
        ((AddCircle.equivIco (1 : ℝ) 0 θ).val + (k' : ℝ)) = 0 := by
      intro k'
      by_contra hne
      exact hmem ⟨(AddCircle.equivIco (1 : ℝ) 0 θ).val + (k' : ℝ), hsupp _ hne, by
        rw [add_comm]
        simpa using (AddCircle.equivIco (1 : ℝ) 0 θ).2.1⟩
    refine hθ ?_
    change (∑' k' : ℤ, varphiNtj N k j t
      ((AddCircle.equivIco (1 : ℝ) 0 θ).val + (k' : ℝ))) = 0
    rw [tsum_congr hzero, tsum_zero]

end Work.KMTPlan.A6
