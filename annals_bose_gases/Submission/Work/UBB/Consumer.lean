import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.UBBtoGc
import Submission.Work.UBB.Assembly
import Submission.Work.UBB.Hamiltonian
import Submission.Work.UBB.wordInf_eq_eB_div
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.UBB.Consumer` — the end-to-end interfaces

`Submission.STATUS.md` records that the single remaining gap of
`theorem_1_2` is the pressure-level FS `thm:LHY-Background` `hpres`, and that
`hpres` follows from **UBB** through the CLOSED chain
`Submission.UBBtoGc.hpres_of_UBB` + `Submission.GCBoxBound.hpres_of_gcTwoTerm`.
This module makes that chain *directly callable* on this area's statement
`Work.UBB.UBB`:

* `hbox_of_UBB` — `UBB` ⟹ the joint-filter box hypothesis `hbox`
  (`Submission.UniformBox.hbox_of_uniform_box`), i.e. the shape
  `Submission.Endgame`/`Submission.Completeness` consume;
* `hpres_of_UBB` — `UBB` ⟹ the pressure-level `hpres` of
  `Submission.theorem_1_2`;
* `hpres_of_named_inputs` — the same with `UBB` supplied by this area's
  assembly (`uniformBoxBound`), so the *whole* residual is visible as the
  named hypotheses of one theorem.

Also here: the dictionary between the bridge in its `wordInf` form
(`Defs.WordBridge`) and the sibling's own `eB` language (`Defs.WordBridgeE`),
and the elementary shrinking lemma used to manufacture the universal
domination `C·t^{η₀−η} ≤ K` from a bare `∃ε₀`.
-/

noncomputable section

open _root_.BoseGases
open Submission.BoseGases
set_option autoImplicit false
set_option linter.dupNamespace false

namespace Work.UBB

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

/-! ## 1. The two bridges agree -/

/-- The bridge in the sibling's own `eB` language, per box. -/
theorem wordBridge_eB {v : ℝ³ → ℝ} {h : ScatSol v} (hBR : WordBridge v h)
    {N : ℕ} {L : ℝ} (hL : 1 ≤ L)
    (hbd : BddBelow (Set.range (fun Φ : CSBox N L =>
      (sboxE N L (dens N L) (wPairC L v) (wPairC L (g0 v h)) (Φ : X N → ℝ)) /
        (∫ x in abox N L, ((Φ : X N → ℝ) x) ^ 2)))) :
    eB N L (dens N L) v h / L ^ 3
      ≤ boxEnergy N L v / L ^ 3 - 8 * π * (a v) * (dens N L) ^ 2 := by
  rw [← wordInf_eq_eB_div (h := h) (hL := lt_of_lt_of_le one_pos hL) hbd]
  exact hBR L hL N

/-- The bridge in the sibling's own `eB` language, with the boundedness
discharged from the corpus (`Submission.Work.SboxEB.eB_quot_bddBelow`). -/
theorem wordBridge_eB_of_corpus {v : ℝ³ → ℝ} {h : ScatSol v} {R : ℝ}
    (hBR : WordBridge v h) (hR : 0 < R) (hv : 0 ≤ v) (hvrad : IsRadial v)
    (hv1 : MemLp v 1) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hRchi : R ≤ chiR0) {N : ℕ} {L : ℝ} (hL : 1 ≤ L) (hμ : 0 ≤ 0) :
    eB N L (dens N L) v h / L ^ 3
      ≤ boxEnergy N L v / L ^ 3 - 8 * π * (a v) * (dens N L) ^ 2 := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hRs : R ≤ L * chiR0 := by
    have hc : 0 ≤ chiR0 := by
      have := hR.le
      nlinarith [hRchi]
    nlinarith [hLpos.le]
  refine wordBridge_eB hBR hL (eB_quot_bddBelow (N := N) (s := L) (μ := dens N L)
    (v := v) hR hv hvrad hv1 hv_supp h hLpos hRs ?_)
  exact dens_nonneg N hLpos.le

/-- **`UBB` is trivial when the scattering length vanishes** (`lhyRhs 0 · · ρ = 0`
and `boxEnergy ≥ 0` for `v ≥ 0`).  So the `a v = 0` branch of the endgame is
covered by this area's statement, not only by the separate
`Submission.UBBtoGc.hpres_of_av_zero`. -/
theorem UBB_of_av_zero {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hav : a v = 0) (η₀ : ℝ) :
    UBB v η₀ := by
  refine ⟨1, one_pos, 0, le_rfl, ?_⟩
  intro L hL N _hN
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have h0 : 0 ≤ boxEnergy N L v := boxEnergy_nonneg hLpos hv
  have h3 : 0 < L ^ 3 := pow_pos hLpos 3
  have hrhs : lhyRhs (a v) 0 (1 / 2 + η₀) (dens N L) = 0 := by
    rw [hav]
    exact lhyRhs_eq_zero_of_A_eq_zero 0 (1 / 2 + η₀) (dens N L)
  rw [hrhs]
  exact div_nonneg h0 h3.le

/-! ## 2. Manufacturing the universal domination -/

/-- Shrinking `ε₀` manufactures the universal domination
`C·t^{η₀−η} ≤ K` of `Submission.UniformBox.hbox_of_uniform_box` from a bare
`∃ε₀ > 0`: since `η < η₀`, for `t ≤ ε₁` one has `t^{η₀−η} ≤ ε₁^{η₀−η}`. -/
theorem exists_small_dom {C K ε₀ η₀ η : ℝ} (hC : 0 ≤ C) (hK : 0 < K) (hε₀ : 0 < ε₀)
    (hη : η < η₀) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ ε₀ ∧ ∀ t : ℝ, 0 ≤ t → t ≤ ε₁ → C * t ^ (η₀ - η) ≤ K := by
  by_cases hC0 : C = 0
  · refine ⟨ε₀, hε₀, le_rfl, ?_⟩
    intro t _ _
    simp [hC0, hK.le]
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    have hδ : 0 < η₀ - η := sub_pos.mpr hη
    have hy : 0 < K / C := div_pos hK hCpos
    refine ⟨min ε₀ ((K / C) ^ (1 / (η₀ - η))), ?_, min_le_left _ _, ?_⟩
    · exact lt_min hε₀ (Real.rpow_pos_of_pos hy _)
    · intro t ht0 ht
      have ht1 : t ≤ (K / C) ^ (1 / (η₀ - η)) := le_trans ht (min_le_right _ _)
      have hone : (1 / (η₀ - η)) * (η₀ - η) = 1 := by
        field_simp
      have hpow : t ^ (η₀ - η) ≤ K / C := by
        calc t ^ (η₀ - η)
            ≤ ((K / C) ^ (1 / (η₀ - η))) ^ (η₀ - η) :=
              Real.rpow_le_rpow ht0 ht1 hδ.le
          _ = (K / C) ^ ((1 / (η₀ - η)) * (η₀ - η)) :=
              (Real.rpow_mul (le_of_lt hy) (1 / (η₀ - η)) (η₀ - η)).symm
          _ = K / C := by rw [hone, Real.rpow_one]
      have := mul_le_mul_of_nonneg_left hpow hC
      rwa [mul_div_cancel₀ K (ne_of_gt hCpos)] at this

/-! ## 3. The consumer interfaces -/

/-- **`UBB` ⟹ the joint-filter box hypothesis `hbox`** (the shape consumed by
`Submission.Endgame` / the thermodynamic-limit argument): this is
`Submission.UniformBox.hbox_of_uniform_box` called on this area's statement. -/
theorem hbox_of_UBB {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hav : 0 < a v)
    {η₀ η : ℝ} (hη₀ : 0 < η₀) (hη : 0 < η) (hηlt : η < η₀)
    {K : ℝ} (hK : 0 < K) (hUBB : UBB v η₀) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ᶠ p in jointFilter ρ,
      lhyRhs (a v) K (1 / 2 + η) ((p.2 : ℝ) / p.1 ^ 3) ≤ boxDensity v p := by
  rcases hUBB with ⟨ε₀, hε₀, C, hC, hb⟩
  rcases exists_small_dom (C := C) (K := K) hC hK hε₀ hηlt with ⟨ε₁, hε₁, hε₁le, hdom⟩
  refine Submission.BoseGases.hbox_of_uniform_box (v := v) (R := R) hR hv_supp (A := a v) hav
    (η₀ := η₀) hη₀ (η := η) hη hηlt (K := K) ⟨ε₁, hε₁, C, hC, hdom, ?_⟩
  intro L hL N hN
  exact hb L hL N (le_trans hN hε₁le)

/-- **`UBB` ⟹ the pressure-level `hpres`** (FS `thm:LHY-Background`), i.e. the
single remaining gap of `Submission.theorem_1_2`.  This is the CLOSED chain
`Submission.UBBtoGc.hpres_of_UBB` applied to this area's statement. -/
theorem hpres_of_UBB {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {R : ℝ}
    (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {η₀ η K : ℝ} (hav : 0 < a v) (hη₀ : 0 < η₀) (hη₀le : η₀ ≤ 1 / 2)
    (hη : 0 < η) (hηlt : η < η₀) (hK : 0 < K) (hUBB : UBB v η₀) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ
        ≤ gcPressure v ρmax (8 * π * (a v) * ρ) + 8 * π * (a v) * ρ * ρ := by
  rcases hUBB with ⟨ε₀, hε₀, C, hC, hb⟩
  exact Submission.BoseGases.hpres_of_UBB (v := v) (hv := hv) (hv1 := hv1) (R := R) (hR := hR)
    (hv_supp := hv_supp) (A := a v) (η₀ := η₀) (η := η) (K := K) (C := C)
    hav hC hη₀ hη₀le hη hηlt hK ⟨ε₀, hε₀, fun L hL N hN => hb L hL N hN⟩

/-- **The area's headline, primary form**: the pressure-level `hpres` of
`Submission.theorem_1_2` from the *single* named input `SpectralInputH` (no word
dictionary, no `WordBridge`). -/
theorem hpres_of_spectralH {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {R : ℝ}
    (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {J ε₀ η₀ η K : ℝ} (hav : 0 < a v) (hε₀ : 0 < ε₀) (hJ : lhyC ≤ J)
    (hη₀ : 0 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hη : 0 < η) (hηlt : η < η₀) (hK : 0 < K)
    (hspec : SpectralInputH v J ε₀ η₀) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ
        ≤ gcPressure v ρmax (8 * π * (a v) * ρ) + 8 * π * (a v) * ρ * ρ :=
  hpres_of_UBB hv hv1 hR hv_supp hav hη₀ hη₀le hη hηlt hK
    (UBB_of_spectralH hv hav.le hε₀ hJ hspec)

/-- **The area's headline, end to end**: the pressure-level `hpres` from the
named sibling inputs (the a-priori window chapter, the Bogoliubov chapter, the
kinetic/word dictionary and the parameter arithmetic of this area). -/
theorem hpres_of_named_inputs {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {R : ℝ}
    (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {h : ScatSol v} {J ε₀ η₀ η K : ℝ} {W : ℕ → ℝ → ℝ}
    (hav : 0 < a v) (ha : 0 ≤ a v) (hJ : lhyC ≤ J)
    (hε₀ : 0 < ε₀) (hη₀ : 0 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hη : 0 < η) (hηlt : η < η₀)
    (hK : 0 < K) (hbridge : WordBridge v h)
    (ha1 : AprioriNPlus v h J W ε₀)
    (ha2 : BogoliubovLow v h J W ε₀ η₀) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ
        ≤ gcPressure v ρmax (8 * π * (a v) * ρ) + 8 * π * (a v) * ρ * ρ :=
  hpres_of_UBB hv hv1 hR hv_supp hav hη₀ hη₀le hη hηlt hK
    (uniformBoxBound hε₀ ha hJ hbridge ha1 ha2)

end Work.UBB
