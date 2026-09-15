import Mathlib
import Submission.Commons.Combinatorics.Transference.bohr_sigma_Omega
import Submission.Commons.Combinatorics.Transference.dual_corr_lower
import Submission.Commons.Combinatorics.Transference.energy_increment_exceptional

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- Sum over a union is bounded by the sum of the sums, for a nonnegative summand. -/
private lemma sum_union_le_of_nonneg {X : Type*} [DecidableEq X] (s t : Finset X) (g : X → ℝ)
    (hg : ∀ x, 0 ≤ g x) : ∑ x ∈ s ∪ t, g x ≤ ∑ x ∈ s, g x + ∑ x ∈ t, g x := by
  have h1 : s ∪ t = s ∪ (t \ s) := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  rw [h1, Finset.sum_union Finset.disjoint_sdiff]
  have h2 : ∑ x ∈ t \ s, g x ≤ ∑ x ∈ t, g x :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun i _ _ => hg i)
  linarith

/-- Average of a summand bounded in absolute value by `M` over a nonempty finite set. -/
private lemma abs_inv_card_mul_sum_le {X : Type*} (s : Finset X) (hs : s.Nonempty) (g : X → ℝ)
    {M : ℝ} (hM : ∀ x, |g x| ≤ M) : |(s.card : ℝ)⁻¹ * ∑ x ∈ s, g x| ≤ M := by
  have hc : 0 < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  rw [abs_mul, abs_of_pos (inv_pos.mpr hc)]
  calc (s.card : ℝ)⁻¹ * |∑ x ∈ s, g x|
      ≤ (s.card : ℝ)⁻¹ * ∑ x ∈ s, |g x| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs g s) (inv_nonneg.mpr hc.le)
    _ ≤ (s.card : ℝ)⁻¹ * ∑ x ∈ s, M :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => hM x)) (inv_nonneg.mpr hc.le)
    _ = M := by
        rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]

theorem energy_step_core {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d)
    (P Q : ZMod p → Finset (ZMod p)) (hPmem : ∀ x, x ∈ P x)
    (hPeq : ∀ x y : ZMod p, y ∈ P x → P y = P x) (hQmem : ∀ x, x ∈ Q x)
    (hQeq : ∀ x y : ZMod p, y ∈ Q x → Q y = Q x) (href : ∀ x, Q x ⊆ P x)
    (Ω : Finset (ZMod p)) (hΩsat : ∀ x ∈ Ω, P x ⊆ Ω)
    (ν : ZMod p → ℝ) (hν : ∀ x, 0 ≤ ν x)
    (f : ZMod p → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    (Fnew : ZMod p → ℝ) (hFnew_0 : ∀ x ∈ Ω, Fnew x = 0)
    (hFnew_out : ∀ x, x ∉ Ω → Fnew x = f x - ((P x).card : ℝ)⁻¹ * (∑ y ∈ P x, f y))
    {Mraw εraw : ℝ} (hMpos : 0 < Mraw) (hεraw : 0 < εraw)
    (hMb : ∀ x, |davg d Fnew x| ≤ Mraw)
    (hQcl : ∀ x y : ZMod p, y ∈ Q x → |davg d Fnew y - davg d Fnew x| ≤ εraw)
    {θ δ B γ₀ ρ : ℝ} (hθ : 0 < θ) (hδ0 : 0 ≤ δ) (hB0 : 0 ≤ B) (hγ0 : 0 ≤ γ₀)
    (hδθ : δ < (Fintype.card (ZMod p) : ℝ) * θ)
    (hAtom : ∀ x, |∑ y ∈ Q x, (ν y - 1)| ≤ δ)
    (hAbound : ∀ x, x ∉ Ω → |((P x).card : ℝ)⁻¹ * (∑ y ∈ P x, f y)| ≤ B)
    (hUb : γ₀ ≤ Unorm d Fnew ^ (2 ^ d))
    (hmass : ∑ x ∈ Ω, (ν x + 1) ≤ ρ)
    (hγpos : Mraw * ((1 + B) * ((Fintype.card (ZMod p) : ℝ) * θ *
          ((Finset.univ.image Q).card : ℝ) + ρ))
        + εraw * (∑ x, |Fnew x|) ≤ (Fintype.card (ZMod p) : ℝ) * γ₀ / 2) :
    ∃ Ω' : Finset (ZMod p), Ω ⊆ Ω' ∧
      (∀ x ∈ Ω', Q x ⊆ Ω') ∧
      (∑ x ∈ Ω', (ν x + 1) ≤ (Fintype.card (ZMod p) : ℝ) * θ *
          ((Finset.univ.image Q).card : ℝ) + ρ) ∧
      (∀ x : ZMod p, x ∉ Ω' → |((Q x).card : ℝ)⁻¹ * (∑ y ∈ Q x, (ν y - 1))|
          ≤ 2 * δ / ((Fintype.card (ZMod p) : ℝ) * θ - δ)) ∧
      (∑ x ∈ Finset.univ \ Ω, (((P x).card : ℝ)⁻¹ * (∑ y ∈ P x, f y)) ^ 2
          + ((Fintype.card (ZMod p) : ℝ) * γ₀ / 2) ^ 2 /
              ((Fintype.card (ZMod p) : ℝ) * Mraw ^ 2)
        ≤ ∑ x ∈ Finset.univ \ Ω', (((Q x).card : ℝ)⁻¹ * (∑ y ∈ Q x, f y)) ^ 2
          + B ^ 2 * (((Ω' \ Ω).card : ℝ)) + 2 * B * ((1 + B) *
              ((Fintype.card (ZMod p) : ℝ) * θ *
                ((Finset.univ.image Q).card : ℝ) + ρ))) := by
  classical
  -- The exceptional set coming from Green–Tao Proposition 6.6 applied to the σ-algebra `Q`.
  obtain ⟨ΩQ, hΩQmass, hΩQsat, hΩQout⟩ :=
    bohr_sigma_Omega Q hQmem hQeq ν hν hθ hδ0 hδθ hAtom
  -- `ρ` is nonnegative since it dominates `∑_{Ω}(ν+1) ≥ 0`.
  have hρ : 0 ≤ ρ :=
    le_trans (Finset.sum_nonneg (fun x _ => by linarith [hν x])) hmass
  have hNnonneg : 0 ≤ (Fintype.card (ZMod p) : ℝ) := by positivity
  -- ## Basic properties of the enlarged exceptional set `Ω ∪ ΩQ`.
  have hΩ'sat : ∀ x ∈ Ω ∪ ΩQ, Q x ⊆ Ω ∪ ΩQ := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · intro z hz
      exact Finset.subset_union_left (s₁ := Ω) (s₂ := ΩQ) (hΩsat x hx (href x hz))
    · intro z hz
      exact Finset.subset_union_right (s₁ := Ω) (s₂ := ΩQ) (hΩQsat x hx hz)
  have hFex : ∀ x, x ∉ Ω ∪ ΩQ → Fnew x = f x - ((P x).card : ℝ)⁻¹ * (∑ y ∈ P x, f y) :=
    fun x hx => hFnew_out x (fun h => hx (Finset.mem_union_left ΩQ h))
  -- ## Residual mass bound on `ΩQ \ Ω`.
  have hres : ∑ x ∈ ΩQ \ Ω, |Fnew x|
      ≤ (1 + B) * ((Fintype.card (ZMod p) : ℝ) * θ * ((Finset.univ.image Q).card : ℝ) + ρ) := by
    have hpt : ∀ x ∈ ΩQ \ Ω, |Fnew x| ≤ (1 + B) * (ν x + 1) := by
      intro x hx
      have hxnotΩ : x ∉ Ω := (Finset.mem_sdiff.mp hx).2
      have h1 : |Fnew x|
          ≤ |f x| + |((P x).card : ℝ)⁻¹ * (∑ y ∈ P x, f y)| := by
        rw [hFnew_out x hxnotΩ]; exact abs_sub _ _
      have h2 : |f x| ≤ ν x := by rw [abs_of_nonneg (hf0 x)]; exact hfν x
      have h3 : |((P x).card : ℝ)⁻¹ * (∑ y ∈ P x, f y)| ≤ B := hAbound x hxnotΩ
      have h4 : ν x + B ≤ (1 + B) * (ν x + 1) := by nlinarith [hν x, hB0]
      linarith
    calc ∑ x ∈ ΩQ \ Ω, |Fnew x| ≤ ∑ x ∈ ΩQ \ Ω, (1 + B) * (ν x + 1) :=
          Finset.sum_le_sum hpt
      _ = (1 + B) * ∑ x ∈ ΩQ \ Ω, (ν x + 1) := by rw [Finset.mul_sum]
      _ ≤ (1 + B) * ∑ x ∈ ΩQ, (ν x + 1) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
              (fun i _ _ => by linarith [hν i])) (by linarith)
      _ ≤ (1 + B) * ((Fintype.card (ZMod p) : ℝ) * θ *
            ((Finset.univ.image Q).card : ℝ) + ρ) :=
          mul_le_mul_of_nonneg_left (by linarith [hΩQmass, hρ]) (by linarith)
  have hFmass : ∑ x ∈ Ω ∪ ΩQ, |Fnew x|
      ≤ (1 + B) * ((Fintype.card (ZMod p) : ℝ) * θ * ((Finset.univ.image Q).card : ℝ) + ρ) := by
    have hsim : ∑ x ∈ Ω ∪ ΩQ, |Fnew x| = ∑ x ∈ ΩQ \ Ω, |Fnew x| := by
      have h1 : Ω ∪ ΩQ = (ΩQ \ Ω) ∪ Ω := by
        rw [Finset.sdiff_union_self_eq_union]; exact Finset.union_comm _ _
      rw [h1, Finset.sum_union Finset.disjoint_sdiff.symm]
      have h0 : ∑ x ∈ Ω, |Fnew x| = 0 :=
        Finset.sum_eq_zero (fun x hx => by rw [hFnew_0 x hx, abs_zero])
      rw [h0, add_zero]
    rw [hsim]; exact hres
  -- ## The `Q`-measurable test function `Φ = 𝔼(𝒟F | Q)` and its bound.
  have hΦM : ∀ x, |((Q x).card : ℝ)⁻¹ * (∑ z ∈ Q x, davg d Fnew z)| ≤ Mraw :=
    fun x => abs_inv_card_mul_sum_le (Q x) ⟨x, hQmem x⟩
      (fun z => davg d Fnew z) (fun z => hMb z)
  have hΦconst : ∀ x y : ZMod p, y ∈ Q x →
      ((Q y).card : ℝ)⁻¹ * (∑ z ∈ Q y, davg d Fnew z)
        = ((Q x).card : ℝ)⁻¹ * (∑ z ∈ Q x, davg d Fnew z) :=
    fun x y hy => by rw [hQeq x y hy]
  -- ## The dual correlation lower bound.
  have hcorr : (Fintype.card (ZMod p) : ℝ) * γ₀ / 2 ≤
      |∑ x ∈ Finset.univ \ (Ω ∪ ΩQ), (f x - ((P x).card : ℝ)⁻¹ * (∑ y ∈ P x, f y)) *
        (((Q x).card : ℝ)⁻¹ * (∑ z ∈ Q x, davg d Fnew z))| := by
    have hdual := dual_corr_lower hd P Q hQmem Ω (Ω ∪ ΩQ) Finset.subset_union_left hΩ'sat
      Fnew f hFnew_0 hFex (le_of_lt hMpos) hεraw hMb hQcl (γ := γ₀) hUb
    have hcost : Mraw * (∑ x ∈ Ω ∪ ΩQ, |Fnew x|) + εraw * (∑ x, |Fnew x|)
        ≤ (Fintype.card (ZMod p) : ℝ) * γ₀ / 2 := by
      have h1 := mul_le_mul_of_nonneg_left hFmass (le_of_lt hMpos)
      linarith [h1, hγpos]
    linarith [hdual, hcost]
  -- ## The annulus residual mass bound.
  have hEbound : ∑ x ∈ (Ω ∪ ΩQ) \ Ω,
        |f x - ((P x).card : ℝ)⁻¹ * (∑ y ∈ P x, f y)|
      ≤ (1 + B) * ((Fintype.card (ZMod p) : ℝ) * θ * ((Finset.univ.image Q).card : ℝ) + ρ) := by
    have hsdiff : (Ω ∪ ΩQ) \ Ω = ΩQ \ Ω := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
    have hpt : ∀ x ∈ ΩQ \ Ω,
        |f x - ((P x).card : ℝ)⁻¹ * (∑ y ∈ P x, f y)| = |Fnew x| := by
      intro x hx
      rw [← hFnew_out x (Finset.mem_sdiff.mp hx).2]
    rw [hsdiff, Finset.sum_congr rfl hpt]; exact hres
  have hγ0' : 0 ≤ (Fintype.card (ZMod p) : ℝ) * γ₀ / 2 := by positivity
  refine ⟨Ω ∪ ΩQ, Finset.subset_union_left, hΩ'sat, ?_, ?_, ?_⟩
  · calc ∑ x ∈ Ω ∪ ΩQ, (ν x + 1)
        ≤ ∑ x ∈ Ω, (ν x + 1) + ∑ x ∈ ΩQ, (ν x + 1) :=
          sum_union_le_of_nonneg Ω ΩQ _ (fun x => by linarith [hν x])
      _ ≤ ρ + (Fintype.card (ZMod p) : ℝ) * θ * ((Finset.univ.image Q).card : ℝ) := by
          linarith [hmass, hΩQmass]
      _ = (Fintype.card (ZMod p) : ℝ) * θ * ((Finset.univ.image Q).card : ℝ) + ρ := by ring
  · intro x hx
    exact hΩQout x (fun h => hx (Finset.mem_union_right Ω h))
  · exact energy_increment_exceptional P Q hPmem hPeq hQmem hQeq href
      Finset.subset_union_left hΩsat hΩ'sat f
      (fun x => ((Q x).card : ℝ)⁻¹ * (∑ z ∈ Q x, davg d Fnew z))
      hΦconst hMpos hγ0' hB0 hAbound hΦM hcorr hEbound

end Commons.Combinatorics.Transference
