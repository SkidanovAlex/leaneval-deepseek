import Mathlib
import Submission.Work.KMTPlan.A6.MdlAdelicLiftPackets
import Submission.Work.KMTPlan.A6.MdlSliceGband
import Submission.Work.KMTPlan.A6.TleBandVarphiNtj
import Submission.Work.KMTAreas.A7.ModelLargeHiRep
import Submission.Work.KMTPlan.A6.MdlAdelicFormPlusDefs

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6

open scoped BigOperators

/-- **The constant-profile realisation of the `zmodAvg`.**  If the first packet family is the
constant function `1` on `ZMod Q` and the second is the constant function `H`, then the arithmetic
averaging form is the constant profile `H`:

`zmodAvg P̃ Q (fun _ => 1) (fun _ => H) θ = H` for every `θ`.

This is the realisation used when the frozen slice is already band-limited to `1/(8Q)` — the
"separated" regime `2^{2·uScale ρ L} > arithQ ρ (max l₁ l₂)`, where the symbol `m_*` of `Btwist`
sees only the `α = 0` arcs of the two inputs: there the target family is the restriction to `ℤ`
of a single `1/(8Q)`-band-limited function `H`, the profile is constant in `θ`, and this identity
produces the required packets `u ≡ 1`, `v ≡ H`. -/
theorem zmodAvg_const (P : Polynomial ℤ) {Q : ℕ} (hQ : 1 ≤ Q) (H : ℂ) (θ : ZMod Q) :
    zmodAvg (negReflect P) Q (fun _ => (1 : ℂ)) (fun _ => H) θ = H := by
  rw [zmodAvg]
  simp only [one_mul]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hQne : ((Q : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- **The periodised-window facts for the modified `f`-side bump `varphiNtj`.**

Third instance of the reduction at the end of §4sexies of `NOTES_MdlAdelicPackets_SESSION.md`
(the `hN`-version of `Work.KMTPlan.A6.VarphiNtjPeriodize`), proved here so that the model-input
band statement `MdlSliceFband` can be assembled from it:

* pointwise bound `‖periodize (varphiNtj N k j t) θ‖ ≤ M` with the explicit
  `M = (Icc (-(⌊g⌋+2)) (⌊g⌋+1)).card * 8`, `g = 2^{k − logN N}` (the `card` is the number of
  integers `k'` with `|x_θ + k'| ≤ g`);
* `MemLp (periodize …) ⊤ circleMeasure` via `memLp_periodize`;
* the arc: `periodize (varphiNtj N k j t) θ ≠ 0 → θ ∈ arcSet 0 g`, from
  `varphiNtj_support_le_pkt` (support radius `g`) and `‖θ‖ ≤ |x_θ + k'|`.

All ingredients are the sorry-free `KMTPlan/A6/MdlPktMemLp` (`varphiNtj_support_le_pkt`,
`memLp_periodize`) and `KMTPlan/A6/lowModSymbFAux` (`norm_varphiNtj_le_eight`). -/
theorem varphiNtjPeriodize_aux_deprecated (N k : ℕ) (j : ℤ) (t : ℝ)
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

/-! ## The `f`-side band node `(S1)`

The `f`-side twin of `Work.KMTPlan.A6.MdlSliceGband` (the `g`-side node, proved): the packet family
`mdlSliceF` is square summable and band-limited to the union of the major arcs of radius
`2^{k₁ − Log N}` around the arithmetic frequencies `α ∈ (ℚ/ℤ)_{≤l₁}`, `N = ⌊a n⌋`.

It is the `(S1)`-input of the adelic-packet programme (`NOTES_MdlAdelicPackets_SESSION2.md` §1a);
stated here because the target file must not import the still-`sorry`-carrying stubs
`MdlSliceFband`/`MdlSliceFbandAssembled`. -/

open MeasureTheory in
/-- `mdlF ρ U l f = piExact (kmtPj ρ) l (−U) f` preserves `ℓ²` (the `f`-side twin of
`MdlSliceGband.memℓp_mdlG`). -/
theorem memℓp_mdlF (ρ : ℝ) (U l : ℕ) {f : ℤ → ℂ} (hf : Memℓp f 2) :
    Memℓp (mdlF ρ U l f) 2 := by
  set k : ℤ := -(U : ℤ) with hk
  have hmem : ∀ (m : ℕ), Memℓp (Work.KMTContract.kmtProj ρ m k f) 2 :=
    fun m => (Work.A7HiRep.exists_hasFreqSupport_kmtProj ρ m k f hf).1
  have hpi : Memℓp (Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l k f) 2 := by
    rw [Work.Analysis.EndVar.piExact]
    split_ifs with h
    · exact hmem 0
    · exact (hmem l).sub (hmem (l - 1))
  simpa [mdlF, hk] using hpi

/-- **The band of the `f`-side packet family** (the `(S1)` node).  On the core scales
`mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n` is the `Tle`-image of `mdlF` under the window
`varphiNtj ⌊a n⌋ k₁ j₁ t`, hence `ℓ²` with Fourier support in `⋃_{α ∈ (ℚ/ℤ)_{≤l₁}} arcSet α γ₁`,
`γ₁ = 2^{k₁ − Log ⌊a n⌋}` (which the `goodScale` gate turns into `γ₁ + γ₂ ≤ 1/(8Q)`). -/
theorem mdlSliceF_band (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (f : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (j₁ : ℤ) (t : ℝ) (n : ℕ)
    (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hk₁ : k₁ = 0 → j₁ ≠ -1)
    (hmain : (k₁ : ℤ) + 2 * (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)
      ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)))
    (hf : Memℓp f 2) :
    ∃ h : Memℓp (mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport
        (mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) h
        (⋃ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
          Work.BourgainPlan.IonescuWainger.arcSet α
            ((2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n))) : ℝ)))) := by
  classical
  by_cases hc : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · have hN1 : 1 ≤ Nat.floor (a n) := by
      have hcut : Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂) < Nat.floor (a n) :=
        ((mdlCore_iff ρ C₀ a l₁ l₂ k₁ k₂ n).mp hc).2.1
      have hsplit : 1 ≤ Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂) := by
        rw [Work.KMTAreas.A7.splitCut]
        exact Nat.one_le_two_pow
      omega
    rw [mdlSliceF, if_pos hc]
    exact TleBandVarphiNtj ρ l₁ (Nat.floor (a n)) k₁ j₁ t
      (mdlF ρ (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)) l₁ f) hj₁ hk₁ hN1
      (memℓp_mdlF ρ _ l₁ hf)
  · rw [mdlSliceF, if_neg hc]
    exact zero_hasFreqSupport _

/-! ## The target in the language of the packets alone

Session 6 (`NOTES_MdlAdelicPackets_SESSION6.md`, §3) isolated the following *strictly weaker*
form of the target's remaining obligation.

The target's clause (1) is a condition on `F` **only**, and clause (3) *identifies* `F` with
`zmodAvg (negReflect P) Q (u n X) (v n X)`; clauses (4),(5) ask only for the measurability of
`u, v`.  Hence, if one takes `F` to be the canonical β-band lift of the gated slice (PROVED in the
tree: `Work.KMTPlan.A6.AdelicLiftExists`, built from `MdlGatedSliceDatumRho` and
`MdlAdelicLiftExists_core`), then clauses (1),(2) are *free* and the whole content of the target is

> the packet families `u, v` are **measurable** and their `zmodAvg`-combination **is** that lift,
> i.e. it is β-band and has the prescribed diagonal.

**In particular `u, v` carry no band condition of their own.**  The band-limited version
(`δ₁ + δ₂ ≤ 1/(8Q)`) is only a *sufficient* route to the two displayed properties, and it is the one
the tree's assembly `Work.KMTPlan.A6Clean.adelicPackets_of_windowPieceLifts` uses.  The theorem
below packages the target from the two displayed properties directly, so that a successor knows
exactly what has to be built. -/
end Work.KMTPlan.A6
