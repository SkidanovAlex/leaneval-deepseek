import Mathlib
import Submission.Commons.Analysis.ODE.exists_confined_smooth_flow
import Submission.Commons.Analysis.ODE.eqOn_of_hasDerivAt_of_locallyLipschitz

namespace Commons.Analysis.ODE

open Set Filter Metric
open scoped Topology NNReal ContDiff

set_option autoImplicit false
set_option maxHeartbeats 800000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A point of an open set on which a field is `C^∞` admits a neighbourhood on which the field is
Lipschitz. -/
lemma ufco_locallyLipschitz {F : E → E} {U : Set E} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U) {z : E} (hz : z ∈ U) :
    ∃ K : NNReal, ∃ U' ∈ nhds z, LipschitzOnWith K F U' := by
  have h1 : ContDiffAt ℝ (1 : WithTop ℕ∞) F z :=
    (hF.contDiffAt (hU.mem_nhds hz)).of_le (WithTop.coe_le_coe.mpr le_top)
  exact h1.exists_lipschitzOnWith

/-- **Uniqueness of solutions of `x' = F x`** when `F` is `C^∞` on an open set `U` and the first
solution stays in `U`; the two solutions agree on the whole interval whenever they agree at one
point of it. -/
lemma ufco_eqOn_of_hasDerivAt {F : E → E} {U : Set E} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U)
    {u v : ℝ → E} {a b t₀ : ℝ} (hat₀ : a ≤ t₀) (ht₀b : t₀ ≤ b)
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (F (u t)) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (F (v t)) t)
    (huU : ∀ t ∈ Icc a b, u t ∈ U)
    (h0 : u t₀ = v t₀) : Set.EqOn u v (Icc a b) := by
  have hloc : ∀ t ∈ Icc a b, ∃ K : NNReal, ∃ U' ∈ nhds (u t), LipschitzOnWith K F U' :=
    fun t ht => ufco_locallyLipschitz hU hF (huU t ht)
  have hright : Set.EqOn u v (Icc t₀ b) :=
    eqOn_of_hasDerivAt_of_locallyLipschitz ht₀b
      (fun t ht => hu t ⟨le_trans hat₀ ht.1, ht.2⟩)
      (fun t ht => hv t ⟨le_trans hat₀ ht.1, ht.2⟩)
      (fun t ht => hloc t ⟨le_trans hat₀ ht.1, ht.2⟩) h0
  have hleft : Set.EqOn u v (Icc a t₀) := by
    have hFneg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => -F z) U := hF.neg
    have hlocn : ∀ t ∈ Icc a t₀,
        ∃ K : NNReal, ∃ U' ∈ nhds (u t), LipschitzOnWith K (fun z => -F z) U' :=
      fun t ht => ufco_locallyLipschitz hU hFneg (huU t ⟨ht.1, le_trans ht.2 ht₀b⟩)
    set c : ℝ := t₀ - a with hc
    have hc0 : 0 ≤ c := by rw [hc]; linarith
    have hu' : ∀ t ∈ Icc (0:ℝ) c,
        HasDerivAt (fun r => u (t₀ - r)) ((fun z => -F z) ((fun r => u (t₀ - r)) t)) t := by
      intro t ht
      have hmem : t₀ - t ∈ Icc a b := ⟨by rw [hc] at ht; linarith [ht.2], by linarith [ht.1]⟩
      have hder : HasDerivAt (fun r : ℝ => t₀ - r) (-1) t := (hasDerivAt_id t).const_sub t₀
      have hcomp := (hu (t₀ - t) hmem).hasFDerivAt.comp_hasDerivAt t hder
      simpa [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply, neg_one_smul]
        using hcomp
    have hv' : ∀ t ∈ Icc (0:ℝ) c,
        HasDerivAt (fun r => v (t₀ - r)) ((fun z => -F z) ((fun r => v (t₀ - r)) t)) t := by
      intro t ht
      have hmem : t₀ - t ∈ Icc a b := ⟨by rw [hc] at ht; linarith [ht.2], by linarith [ht.1]⟩
      have hder : HasDerivAt (fun r : ℝ => t₀ - r) (-1) t := (hasDerivAt_id t).const_sub t₀
      have hcomp := (hv (t₀ - t) hmem).hasFDerivAt.comp_hasDerivAt t hder
      simpa [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply, neg_one_smul]
        using hcomp
    have hloc' : ∀ t ∈ Icc (0:ℝ) c,
        ∃ K : NNReal, ∃ U' ∈ nhds ((fun r => u (t₀ - r)) t),
          LipschitzOnWith K (fun z => -F z) U' :=
      fun t ht => hlocn (t₀ - t) ⟨by rw [hc] at ht; linarith [ht.2], by linarith [ht.1]⟩
    have h0' : (fun r => u (t₀ - r)) 0 = (fun r => v (t₀ - r)) 0 := by
      simpa using h0
    have hrs := eqOn_of_hasDerivAt_of_locallyLipschitz (f := fun z => -F z) hc0 hu' hv' hloc' h0'
    intro t ht
    have ht' : t₀ - t ∈ Icc (0:ℝ) c := ⟨by linarith [ht.2], by rw [hc]; linarith [ht.1]⟩
    have := hrs ht'
    simpa only [sub_sub_cancel] using this
  intro t ht
  rcases le_total t t₀ with h | h
  · exact hleft ⟨ht.1, h⟩
  · exact hright ⟨h, ht.2⟩

/-- **Local flow of a `C^∞` field on an open set, uniform on a compact set.**

This is the statement `uniform_flow_compact_of_contDiffOn` together with the *confinement* of the
flow lines to the open set `W`, which is what makes the uniqueness of the flow available. -/
theorem uniform_flow_compact_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E} {U : Set E} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ α : E → ℝ → E,
      (∀ p ∈ K, α p 0 = p) ∧
      (∀ p ∈ K, ∀ t : ℝ, |t| ≤ ρ → HasDerivAt (α p) (F (α p t)) t) ∧
      (∀ p ∈ K, ∀ t : ℝ, |t| ≤ ρ →
        ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : E => α q t) p)
      ∧ (∀ p ∈ K, ∀ β : ℝ → E, (∀ t : ℝ, |t| ≤ ρ → HasDerivAt β (F (β t)) t) → β 0 = p →
          ∀ t : ℝ, |t| ≤ ρ → β t = α p t) := by
  obtain ⟨ρ, hρpos, α, h0, hder, hmem, hsmooth⟩ :=
    exists_confined_smooth_flow hU hF hK hKU
  refine ⟨ρ, hρpos, α, h0, hder, hsmooth, ?_⟩
  intro p hp β hβ hβ0 t ht
  have htIcc : t ∈ Icc (-ρ) ρ :=
    ⟨by linarith [(abs_le.mp ht).1], by linarith [(abs_le.mp ht).2]⟩
  have hαd : ∀ s ∈ Icc (-ρ) ρ, HasDerivAt (α p) (F (α p s)) s := fun s hs =>
    hder p hp s (by rw [abs_le]; exact ⟨hs.1, hs.2⟩)
  have hαU : ∀ s ∈ Icc (-ρ) ρ, α p s ∈ U := fun s hs =>
    hmem p hp s (by rw [abs_le]; exact ⟨hs.1, hs.2⟩)
  have hβd : ∀ s ∈ Icc (-ρ) ρ, HasDerivAt β (F (β s)) s := fun s hs =>
    hβ s (by rw [abs_le]; exact ⟨hs.1, hs.2⟩)
  have h0x : α p 0 = β 0 := by rw [h0 p hp, hβ0]
  have heq := ufco_eqOn_of_hasDerivAt hU hF (u := α p) (v := β) (a := -ρ) (b := ρ) (t₀ := 0)
    (by linarith) (by linarith) hαd hβd hαU h0x
  exact (heq htIcc).symm

end Commons.Analysis.ODE
