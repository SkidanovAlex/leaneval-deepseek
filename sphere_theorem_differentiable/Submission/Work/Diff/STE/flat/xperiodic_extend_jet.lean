import Mathlib
import Submission.Work.Diff.STE.flat.TowerDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Globalising a smooth `x`-periodic `Jet n`-valued nonlinearity off a compact jet region

`Work.Diff.STE.flat.xperiodic_extend_jet` is the `Jet n`-valued form of the "cut off and forget"
step `Work.Diff.STE.flat.exists_xperiodic_extend`: the flat DeTurck nonlinearity is known to be
smooth only on `univ ×ˢ V` for an *open* set `V` of the jet variable (the jets on which the metric
matrix is nondegenerate), while the Moser composition estimate
(`Work.Diff.STE.flat.CSq_comp_xperiodic_le`) needs a function that is smooth on *all* of
`(Fin n → ℝ) × Jet n`, is still `x`-periodic (period `1` in every coordinate direction) and agrees
with `Φ` near a prescribed compact `Kc ⊆ V`.

The remedy is the standard one, and it is proved here in the general form actually needed — an
arbitrary finite-dimensional real normed space of *arguments* `E` and an arbitrary real normed
space of *values* `F` (the target has `E = Jet n = MatC n × (Fin n → MatC n) × …` and
`F = MatC n`):

* pick `ε > 0` with `cthickening ε Kc ⊆ V` (compactness of `Kc` and openness of `V`), and a smooth
  cutoff `f : E → ℝ` with `support f = thickening (ε/2) Kc` and `f = 1` on the closed thickening
  `cthickening (ε/4) Kc` (Mathlib's `exists_contDiff_support_eq_eq_one_iff`);
* put `Φ' (x, w) := f w • Φ (x, w)`.  Where `w ∈ tsupport f` (and `tsupport f ⊆ V`) the point lies
  in the *open* set `univ ×ˢ V` on which `Φ` is smooth and `Φ'` is a product of smooth maps; where
  `w ∉ tsupport f` the factor `f` vanishes on a whole neighbourhood, so `Φ'` is locally the
  constant `0`.  Smoothness is local, hence `Φ'` is `C^∞`;
* the cutoff does not depend on `x`, so `Φ'` is still `x`-periodic: for `w ∈ V` this is `hper`, and
  for `w ∉ V` the factor `f w` vanishes because `support f ⊆ tsupport f ⊆ V`, so both sides are `0`;
* on the open set `W' := thickening (ε/4) Kc ∋ Kc` the cutoff equals `1`, so `Φ' = Φ` there; and
  `W' ⊆ cthickening (ε/4) Kc ⊆ thickening (ε/2) Kc ⊆ cthickening ε Kc ⊆ V`.
-/

open Set Filter

namespace Work.Diff.STE.flat

/-- **The general form of the globalization of an `x`-periodic function off a compact set.**

For `Φ : (Fin n → ℝ) × E → F` smooth on `univ ×ˢ V` (`V` open) and periodic in the `n` coordinate
directions on `V`, and for a compact `Kc ⊆ V`, there is a globally smooth, periodic `Φ'` agreeing
with `Φ` on an open `W'` with `Kc ⊆ W' ⊆ V`.

The only additional input (compared with `Work.Diff.STE.flat.exists_xperiodic_extend`, which is the
case `E = Fin m → ℂ`, `F = ℂ`) is that the periodicity of `Φ` is only assumed on `V`; the conclusion
`W' ⊆ V` is what makes that harmless. -/
theorem exists_xperiodic_extend_general {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F]
    (Φ : (Fin n → ℝ) × E → F) (V : Set E) (hV : IsOpen V)
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ (Set.univ ×ˢ V))
    (hper : ∀ (x : Fin n → ℝ) (w : E) (i : Fin n),
      w ∈ V → Φ (x + Pi.single i 1, w) = Φ (x, w))
    (Kc : Set E) (hKcc : IsCompact Kc) (hKcV : Kc ⊆ V) :
    ∃ Φ' : (Fin n → ℝ) × E → F,
      ContDiff ℝ (⊤ : ℕ∞) Φ' ∧
      (∀ (x : Fin n → ℝ) (w : E) (i : Fin n),
        Φ' (x + Pi.single i 1, w) = Φ' (x, w)) ∧
      (∃ W' : Set E, IsOpen W' ∧ Kc ⊆ W' ∧ W' ⊆ V ∧
        ∀ (x : Fin n → ℝ) (w : E), w ∈ W' → Φ' (x, w) = Φ (x, w)) := by
  -- A positive radius whose closed thickening around `Kc` still lies in `V`.
  obtain ⟨ε, hεpos, hε⟩ := hKcc.exists_cthickening_subset_open hV hKcV
  -- The cutoff is supported in `thickening (ε/2) Kc`, whose closure lies in `V`.
  have hcl : closure (Metric.thickening (ε / 2) Kc) ⊆ V :=
    (Metric.closure_thickening_subset_cthickening (ε / 2) Kc).trans
      ((Metric.cthickening_mono (by linarith) Kc).trans hε)
  have hts : Metric.cthickening (ε / 4) Kc ⊆ Metric.thickening (ε / 2) Kc :=
    Metric.cthickening_subset_thickening' (by linarith) (by linarith) Kc
  obtain ⟨f, hf, _hfrange, hfsupp, hfone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (E := E) (n := ⊤)
      (s := Metric.thickening (ε / 2) Kc) (t := Metric.cthickening (ε / 4) Kc)
      Metric.isOpen_thickening Metric.isClosed_cthickening hts
  have htsuppV : tsupport f ⊆ V := by rw [tsupport, hfsupp]; exact hcl
  refine ⟨fun p => f p.2 • Φ p, ?_, ?_, ?_⟩
  · -- `Φ'` is smooth: on `univ ×ˢ V` it is a product of smooth maps, outside `tsupport f` it
    -- vanishes identically on a neighbourhood.  Smoothness is local, so check it pointwise.
    have hχc : ContDiff ℝ (⊤ : ℕ∞) (fun p : (Fin n → ℝ) × E => f p.2) :=
      hf.comp (ContinuousLinearMap.snd ℝ (Fin n → ℝ) E).contDiff
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p.2 ∈ tsupport f
    · -- here `p` lies in the open set on which `Φ` is smooth
      have hpV : p.2 ∈ V := htsuppV hp
      have hmem : Set.univ ×ˢ V ∈ nhds p :=
        (IsOpen.prod isOpen_univ hV).mem_nhds ⟨trivial, hpV⟩
      exact hχc.contDiffAt.smul (hΦ.contDiffAt hmem)
    · -- here `f` vanishes on a whole neighbourhood, so `Φ'` is locally the constant `0`
      have hev : (fun _ : (Fin n → ℝ) × E => (0 : F)) =ᶠ[nhds p]
          (fun q => f q.2 • Φ q) := by
        have hmemU : Set.univ ×ˢ (tsupport f)ᶜ ∈ nhds p :=
          (IsOpen.prod isOpen_univ (isClosed_tsupport f).isOpen_compl).mem_nhds
            ⟨trivial, hp⟩
        refine Filter.eventually_of_mem hmemU ?_
        intro q hq
        have hz : f q.2 = 0 :=
          Function.notMem_support.mp (fun h => hq.2 (subset_closure h))
        simp [hz]
      exact (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq hev.symm
  · -- periodicity: the cutoff does not depend on `x`
    intro x w i
    show f w • Φ (x + Pi.single i 1, w) = f w • Φ (x, w)
    by_cases hw : w ∈ V
    · rw [hper x w i hw]
    · have hfw : f w = 0 := by
        by_contra hne
        exact hw (htsuppV (subset_closure (Function.mem_support.mpr hne)))
      rw [hfw, zero_smul, zero_smul]
  · -- on the open thickening `W'` of `Kc` the cutoff equals `1`, so `Φ' = Φ`
    refine ⟨Metric.thickening (ε / 4) Kc, Metric.isOpen_thickening, ?_, ?_, ?_⟩
    · exact Metric.self_subset_thickening (by linarith) Kc
    · exact (Metric.thickening_subset_cthickening (ε / 4) Kc).trans
        (hts.trans ((subset_closure : Metric.thickening (ε / 2) Kc ⊆
          closure (Metric.thickening (ε / 2) Kc)).trans hcl))
    · intro x w hw
      have hw1 : f w = 1 :=
        (hfone w).mp ((Metric.thickening_subset_cthickening (ε / 4) Kc) hw)
      simp [hw1]

theorem xperiodic_extend_jet {n : ℕ}
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (V : Set (Work.Diff.STE.Flat.Jet n)) (hV : IsOpen V)
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ (Set.univ ×ˢ V))
    (hper : ∀ (x : Fin n → ℝ) (w : Work.Diff.STE.Flat.Jet n) (i : Fin n),
      w ∈ V → Φ (x + Pi.single i 1, w) = Φ (x, w))
    (Kc : Set (Work.Diff.STE.Flat.Jet n)) (hKcc : IsCompact Kc) (hKcV : Kc ⊆ V) :
    ∃ Φ' : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n,
      ContDiff ℝ (⊤ : ℕ∞) Φ' ∧
      (∀ (x : Fin n → ℝ) (w : Work.Diff.STE.Flat.Jet n) (i : Fin n),
        Φ' (x + Pi.single i 1, w) = Φ' (x, w)) ∧
      (∃ W' : Set (Work.Diff.STE.Flat.Jet n), IsOpen W' ∧ Kc ⊆ W' ∧ W' ⊆ V ∧
        ∀ (x : Fin n → ℝ) (w : Work.Diff.STE.Flat.Jet n), w ∈ W' → Φ' (x, w) = Φ (x, w)) := by
  exact exists_xperiodic_extend_general Φ V hV hΦ hper Kc hKcc hKcV

end Work.Diff.STE.flat
