import Mathlib
import Submission.Work.EQ.H0_structure
import Submission.Work.Analysis.Complex.punctured_ball_connected
import Submission.Work.EQ.EquiLocalDefs

namespace Work.EQ.Chart

open Filter _root_.Topology

/-- **The stabiliser of a continuous family of chains is determined by a single point.**

Let `F` be a continuous family of chains of `⁰H` over the punctured disc `0 < ‖t‖ < ρ`, with
`ψ₁ (F t) = z₀ + tᵏ`. If `ω` is a `k`-th root of unity and `F (ω t₀) = F t₀` for one point `t₀` of
the punctured disc, then `F (ω t) = F t` for every `t` in the punctured disc.

The agreement set `A = {t : F (ω t) = F t}` is closed (chain data is Hausdorff and `F` is
continuous) and open: at `t ∈ A`, both `F (ω s)` and `F s` have the same `ψ₁ = z₀ + sᵏ` for `s`
near `t`, and `ψ₁` is locally injective on `⁰H` (`Work.EQ.H0_structure`, clause 1), so they agree.
The punctured disc is (pre)connected (`Work.Analysis.Complex.isConnected_punctured_ball_at`), so
`A` is empty or everything; it is nonempty by hypothesis. -/
theorem stab_invariance_of_one_point {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {z₀ : ℂ} {k : ℕ} (hk : 1 ≤ k) {ρ : ℝ} (hρ : 0 < ρ)
    {F : ℂ → ChainData}
    (hcont : ContinuousOn F {t : ℂ | 0 < ‖t‖ ∧ ‖t‖ < ρ})
    (hmem : ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ → F t ∈ H0 a h)
    (hpsi : ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ → (F t).2.1 = z₀ + t ^ k)
    {ω : ℂ} (hω : ω ^ k = 1) {t₀ : ℂ} (ht₀ : 0 < ‖t₀‖) (ht₀ρ : ‖t₀‖ < ρ)
    (hfix : F (ω * t₀) = F t₀) :
    ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ → F (ω * t) = F t := by
  have hk0 : k ≠ 0 := by omega
  -- `ω` is a unit complex number, so multiplication by `ω` preserves the punctured disc.
  have hωnorm : ‖ω‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hω hk0
  let D : Set ℂ := {t : ℂ | 0 < ‖t‖ ∧ ‖t‖ < ρ}
  have hDω : ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ → 0 < ‖ω * t‖ ∧ ‖ω * t‖ < ρ := by
    intro t h1 h2
    rw [norm_mul, hωnorm, one_mul]
    exact ⟨h1, h2⟩
  -- the punctured disc is connected
  have hconn : IsConnected D := by
    show IsConnected {t : ℂ | 0 < ‖t‖ ∧ ‖t‖ < ρ}
    simpa only [sub_zero] using
      Work.Analysis.Complex.isConnected_punctured_ball_at (0 : ℂ) hρ
  have hconnI : ConnectedSpace D := isConnected_iff_connectedSpace.mp hconn
  -- the two `⁰H`-valued maps `t ↦ F t` and `t ↦ F (ω t)` on the punctured disc
  let Φ : D → H0 a h := fun x => ⟨F x.1, hmem x.1 x.2.1 x.2.2⟩
  let Ψ : D → H0 a h :=
    fun x => ⟨F (ω * x.1), hmem (ω * x.1) (hDω x.1 x.2.1 x.2.2).1 (hDω x.1 x.2.1 x.2.2).2⟩
  let A : Set D := {x | (Φ x : ChainData) = (Ψ x : ChainData)}
  have hΦcont : Continuous Φ :=
    Continuous.subtype_mk hcont.domRestrict (fun x => hmem x.1 x.2.1 x.2.2)
  have hχ : Continuous (fun x : D => (⟨ω * x.1, hDω x.1 x.2.1 x.2.2⟩ : D)) :=
    Continuous.subtype_mk (continuous_const.mul continuous_subtype_val)
      (fun x => hDω x.1 x.2.1 x.2.2)
  have hΨcont : Continuous Ψ :=
    Continuous.subtype_mk (hcont.domRestrict.comp hχ)
      (fun x => hmem (ω * x.1) (hDω x.1 x.2.1 x.2.2).1 (hDω x.1 x.2.1 x.2.2).2)
  -- `A` is closed: chain data is Hausdorff
  have hAclosed : IsClosed A := by
    have h1 : Continuous (fun x : D => (Φ x : ChainData)) :=
      continuous_subtype_val.comp hΦcont
    have h2 : Continuous (fun x : D => (Ψ x : ChainData)) :=
      continuous_subtype_val.comp hΨcont
    exact isClosed_eq h1 h2
  -- `A` is nonempty, by hypothesis
  have hAne : A.Nonempty := by
    refine ⟨⟨t₀, ht₀, ht₀ρ⟩, ?_⟩
    show F t₀ = F (ω * t₀)
    exact hfix.symm
  -- `A` is open: locally, `ψ₁` separates points of `⁰H`
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨U, hUopen, hxU, hinj⟩ :=
      localInj_of_localHomeomorph (H0_structure ha0 ha1 hh).1 (F x.1) (hmem x.1 x.2.1 x.2.2)
    let U' : Set (H0 a h) := {q | (q : ChainData) ∈ U}
    have hU'open : IsOpen U' := hUopen.preimage continuous_subtype_val
    have hxU'Φ : Φ x ∈ U' := hxU
    have hxU'Ψ : Ψ x ∈ U' := by
      show (Ψ x : ChainData) ∈ U
      rw [← hx]
      exact hxU
    have hW : (Φ ⁻¹' U') ∩ (Ψ ⁻¹' U') ∈ 𝓝 x :=
      Filter.inter_mem
        (hΦcont.continuousAt.preimage_mem_nhds (hU'open.mem_nhds hxU'Φ))
        (hΨcont.continuousAt.preimage_mem_nhds (hU'open.mem_nhds hxU'Ψ))
    refine Filter.mem_of_superset hW ?_
    intro y hy
    have h1 : (Φ y : ChainData) ∈ U := hy.1
    have h2 : (Ψ y : ChainData) ∈ U := hy.2
    have hψ : (Φ y : ChainData).2.1 = (Ψ y : ChainData).2.1 := by
      have hy1 : (Φ y : ChainData).2.1 = z₀ + (y : ℂ) ^ k := hpsi y.1 y.2.1 y.2.2
      have hy2 : (Ψ y : ChainData).2.1 = z₀ + (y : ℂ) ^ k := by
        show (F (ω * y.1)).2.1 = z₀ + (y : ℂ) ^ k
        rw [hpsi (ω * y.1) (hDω y.1 y.2.1 y.2.2).1 (hDω y.1 y.2.1 y.2.2).2,
          mul_pow, hω, one_mul]
      rw [hy1, hy2]
    exact hinj (Φ y) h1 (Φ y).2 (Ψ y) h2 (Ψ y).2 hψ
  -- a nonempty clopen subset of the connected punctured disc is everything
  have hAuniv : A = Set.univ := IsClopen.eq_univ ⟨hAclosed, hAopen⟩ hAne
  intro t ht1 ht2
  have hx : (⟨t, ht1, ht2⟩ : D) ∈ A := by
    rw [hAuniv]
    exact Set.mem_univ _
  exact hx.symm

end Work.EQ.Chart
