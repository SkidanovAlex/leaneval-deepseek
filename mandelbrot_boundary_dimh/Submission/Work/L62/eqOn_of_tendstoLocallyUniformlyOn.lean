import Mathlib
import Submission.Work.L62.branch_unique

/-!
# L62 — uniqueness of a holomorphic branch from a locally uniform limit

This is the "continuity/uniqueness in `β`" step of Lemma 6.2: the holomorphic self-map `H β : Ω → Ω`
of the cylinder model is determined by its multiplier relation `g (H β ζ) = c β * ζ`, so a locally
uniform limit along any subsequence of parameters `βseq (φ n) → β₀` must be `H β₀`.

The proof is the classical one:

* the locally uniform limit `H'` of holomorphic functions is holomorphic on the open set `Ω`
  (`TendstoLocallyUniformlyOn.differentiableOn`), and it is the pointwise limit at each point of `Ω`;
* `g` is holomorphic on `Ω` with `deriv g 0 ≠ 0`, hence injective on a neighbourhood `B` of `0`;
* for `ζ` in a neighbourhood of `0` where `H' ζ` and `H β₀ ζ` both lie in `B ∩ Ω`, taking limits in
  `g (H (βseq (φ n)) ζ) = c (βseq (φ n)) * ζ` gives `g (H' ζ) = c β₀ * ζ = g (H β₀ ζ)`, and injectivity
  of `g` on `B` gives `H' ζ = H β₀ ζ`;
* the difference `H' - H β₀` is holomorphic on the open preconnected set `Ω` and vanishes on a
  neighbourhood of `0 ∈ Ω`, so it vanishes everywhere (identity theorem).
-/

namespace Work.L62

open Set Filter
open scoped Topology

/-- **Uniqueness of a holomorphic branch on a preconnected domain, from a locally uniform limit.**

Let `Ω ∋ 0` be open and preconnected, `g` holomorphic on `Ω` with `deriv g 0 ≠ 0`, and let
`H β : Ω → ℂ` be holomorphic with `H β 0 = 0` and `g (H β ζ) = c β * ζ`.  If a subsequence
`H (βseq (φ n))` of parameters `βseq (φ n) → β₀ ∈ Λ` converges locally uniformly on `Ω` to `H'`,
then `H' = H β₀` on `Ω`. -/
theorem eqOn_of_tendstoLocallyUniformlyOn {Ω Λ : Set ℂ} {g c : ℂ → ℂ} {H : ℂ → ℂ → ℂ} {H' : ℂ → ℂ}
    (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω) (h0 : (0 : ℂ) ∈ Ω)
    (hg : DifferentiableOn ℂ g Ω) (hgd : deriv g 0 ≠ 0)
    (hc : ContinuousOn c Λ)
    (hHdiff : ∀ β ∈ Λ, DifferentiableOn ℂ (H β) Ω)
    (hHfix : ∀ β ∈ Λ, H β 0 = 0)
    (heq : ∀ β ∈ Λ, ∀ ζ ∈ Ω, g (H β ζ) = c β * ζ)
    {βseq : ℕ → ℂ} (hβΛ : ∀ n, βseq n ∈ Λ) {β₀ : ℂ} (hβ₀ : β₀ ∈ Λ)
    (hβtend : Filter.Tendsto βseq Filter.atTop (nhds β₀))
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hlim : TendstoLocallyUniformlyOn (fun n => H (βseq (φ n))) H' Filter.atTop Ω) :
    Set.EqOn H' (H β₀) Ω := by
  have hβΛ' : ∀ n, βseq (φ n) ∈ Λ := fun n => hβΛ (φ n)
  -- `H'` is holomorphic on `Ω`: it is a locally uniform limit of holomorphic functions
  have hH'diff : DifferentiableOn ℂ H' Ω :=
    hlim.differentiableOn (Eventually.of_forall fun n => hHdiff _ (hβΛ' n)) hΩo
  have hHβ₀diff : DifferentiableOn ℂ (H β₀) Ω := hHdiff β₀ hβ₀
  have hH'0d : DifferentiableAt ℂ H' 0 := hH'diff.differentiableAt (hΩo.mem_nhds h0)
  have hHβ₀0d : DifferentiableAt ℂ (H β₀) 0 := hHβ₀diff.differentiableAt (hΩo.mem_nhds h0)
  -- `H' 0 = 0`
  have hH'0 : H' 0 = 0 := by
    have h := hlim.tendsto_at h0
    have h' : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (H' 0)) := by
      simpa only [hHfix _ (hβΛ' _)] using h
    exact tendsto_nhds_unique h' tendsto_const_nhds
  -- `g` is injective on a neighbourhood `B` of `0`
  have hgan : AnalyticAt ℂ g 0 := (hg.analyticOnNhd hΩo) 0 h0
  obtain ⟨B, hBmem, hBinj⟩ := injOn_nhds_of_analyticAt_deriv_ne_zero hgan hgd
  -- `c` tends to `c β₀` along the subsequence
  have hctend : Tendsto (fun n => c (βseq (φ n))) atTop (𝓝 (c β₀)) := by
    have h1 : Tendsto (fun n => βseq (φ n)) atTop (𝓝[Λ] β₀) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hβtend.comp hφ.tendsto_atTop, Eventually.of_forall hβΛ'⟩
    exact Filter.Tendsto.comp (hc β₀ hβ₀) h1
  -- a neighbourhood `W` of `0` on which both `H'` and `H β₀` land in `B ∩ Ω`
  have hA : B ∩ Ω ∈ 𝓝 (0 : ℂ) := inter_mem hBmem (hΩo.mem_nhds h0)
  have hpre₁ : H' ⁻¹' (B ∩ Ω) ∈ 𝓝 (0 : ℂ) := hH'0d.continuousAt.preimage_mem_nhds (by simpa only [hH'0] using hA)
  have hpre₂ : (H β₀) ⁻¹' (B ∩ Ω) ∈ 𝓝 (0 : ℂ) :=
    hHβ₀0d.continuousAt.preimage_mem_nhds (by simpa only [hHfix β₀ hβ₀] using hA)
  have hW : Ω ∩ H' ⁻¹' (B ∩ Ω) ∩ (H β₀) ⁻¹' (B ∩ Ω) ∈ 𝓝 (0 : ℂ) :=
    inter_mem (inter_mem (hΩo.mem_nhds h0) hpre₁) hpre₂
  -- on `W`, the two functions agree
  have hkey : ∀ ζ ∈ Ω ∩ H' ⁻¹' (B ∩ Ω) ∩ (H β₀) ⁻¹' (B ∩ Ω), H' ζ = H β₀ ζ := by
    intro ζ hz
    obtain ⟨⟨hζΩ, hH'z⟩, hHz⟩ := hz
    obtain ⟨hH'B, hH'Ω⟩ := hH'z
    obtain ⟨hHB, hHΩ⟩ := hHz
    -- the limit of `g (H (βseq (φ n)) ζ)` is `g (H' ζ)`
    have hgcont : ContinuousAt g (H' ζ) := (hg.differentiableAt (hΩo.mem_nhds hH'Ω)).continuousAt
    have hL₁ : Tendsto (fun n => g (H (βseq (φ n)) ζ)) atTop (𝓝 (g (H' ζ))) :=
      hgcont.tendsto.comp (hlim.tendsto_at hζΩ)
    -- ... and it is also `c β₀ * ζ`
    have hL₂ : Tendsto (fun n => g (H (βseq (φ n)) ζ)) atTop (𝓝 (c β₀ * ζ)) :=
      (hctend.mul_const ζ).congr' (Eventually.of_forall fun n =>
        (heq (βseq (φ n)) (hβΛ' n) ζ hζΩ).symm)
    have hval : g (H' ζ) = c β₀ * ζ := tendsto_nhds_unique hL₁ hL₂
    have hval' : g (H β₀ ζ) = c β₀ * ζ := heq β₀ hβ₀ ζ hζΩ
    exact hBinj hH'B hHB (by rw [hval, hval'])
  -- identity theorem on the open preconnected set `Ω`
  have hev : (fun ζ => H' ζ - H β₀ ζ) =ᶠ[𝓝 (0 : ℂ)] (fun _ => 0) :=
    eventually_of_mem hW fun ζ hz => sub_eq_zero.mpr (hkey ζ hz)
  have hAna : AnalyticOnNhd ℂ (fun ζ => H' ζ - H β₀ ζ) Ω :=
    (hH'diff.analyticOnNhd hΩo).sub (hHβ₀diff.analyticOnNhd hΩo)
  have hEq := hAna.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hΩc h0 hev
  intro ζ hζ
  exact sub_eq_zero.mp (hEq hζ)

end Work.L62
