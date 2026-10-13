/-
Copyright: work module for the Elgindi finite-time singularity project.

# The level-5 extraction rounds

For each of the six level-5 slots `D_z^j D_θ^i` (`j + i = 5`) we produce, from the uniform
convergence of the level-`≤ 4` slots and the uniform `H⁶` bound, a further strictly increasing
subsequence along which the slot converges almost everywhere on every exhaustion box `eBox m`.

* the `z`-slots (`j ≥ 1`): the slot `(j' + 1, i)` is `z · ∂_z (D_z^{j'} D_θ^i)`, so `ae_extract_z`
  applies to the level-4 family `D_z^{j'}D_θ^i`, with the `L¹`-Cauchy input `l1_cauchy_pz` (that
  one needs `SmoothOpen` on the open quadrant, which holds here because the data box `eBoxZ m`
  lies inside the quadrant);
* the `θ`-slot `(0, 5)`: it is `sin 2θ · ∂_θ (D_θ^4)`, so `ae_extract_theta` applies, with the
  `L¹`-Cauchy input `cauchy_theta_of_z_gen` — the transposed form of the *box-local* engine
  `l1_cauchy_pz_gen`.  The transposition matters: the data box `eBoxT m` has unbounded `z`, so
  the quadrant-based engine is not applicable to the transposed family, while the box-local one
  is (its hypotheses are exactly the derivative/continuity/L² facts on the box, which all hold
  on `eBoxT m`).
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.LocUnif.D5.ae_extract_z
import Submission.Work.FTS.StrongEps.LocUnif.D5.l1_cauchy_pz
import Submission.Work.FTS.StrongEps.LocUnif.D5.l1_cauchy_pz_gen
import Submission.Work.FTS.StrongEps.LocUnif.D5.exists_diag_extract
import Submission.Work.FTS.StrongEps.LocUnif.D5.deriv_slot_lintegral_bounds
import Submission.Work.FTS.StrongEps.LocUnif.D5.eBoxes

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif.D5

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary facts -/

/-- The exhaustion boxes are measurable. -/
theorem measurableSet_eBox (m : ℕ) : MeasurableSet (eBox m) :=
  measurableSet_Icc.prod measurableSet_Icc

/-- `1 ≤ smoothOrder`: `C^∞` on the open quadrant gives `C¹` on any subset. -/
theorem one_le_smoothOrder : (1 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
  rw [Work.Stability.smoothOrder]
  exact WithTop.coe_le_coe.mpr le_top

/-- `D_z^{j+1}D_θ^i = z ∂_z (D_z^j D_θ^i)`. -/
theorem mixed_succ_apply (j i : ℕ) (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed (j + 1) i X z θ = z * Work.Spaces.pz (Work.Spaces.mixed j i X) z θ := rfl

/-- `D_θ^5 = sin 2θ · ∂_θ (D_θ^4)`. -/
theorem mixed_zero_five_apply (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 0 5 X z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.mixed 0 4 X) z θ := rfl

/-! ## Transport along `Prod.swap` -/

/-- Uniform convergence is preserved by exchanging the two coordinates. -/
theorem tendstoUniformlyOn_swap_box {F : ℕ → ℝ → ℝ → ℝ} {g : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (h : TendstoUniformlyOn (fun n (p : ℝ × ℝ) => F n p.1 p.2) (fun p => g p.1 p.2)
      Filter.atTop (Set.Icc a b ×ˢ Set.Icc c d)) :
    TendstoUniformlyOn (fun n (p : ℝ × ℝ) => F n p.2 p.1) (fun p => g p.2 p.1)
      Filter.atTop (Set.Icc c d ×ˢ Set.Icc a b) := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with n hn p hp
  exact hn (Prod.swap p) ⟨hp.2, hp.1⟩

/-- Joint continuity is preserved by exchanging the two coordinates. -/
theorem continuousOn_swap_box {F : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (h : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d)) :
    ContinuousOn (fun p : ℝ × ℝ => F p.2 p.1) (Set.Icc c d ×ˢ Set.Icc a b) :=
  h.comp continuous_swap.continuousOn (fun q hq => ⟨hq.2, hq.1⟩)

/-- The `θ`-derivative of the `θ`-slice, on the open quadrant. -/
theorem hasDerivAt_slice_theta {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ' => F z θ') (Work.Spaces.pth F z θ) θ := by
  have hd : DifferentiableAt ℝ (fun θ' => F z θ') θ :=
    ((hF.curry_θ hz).differentiableOn (by rw [Work.Stability.smoothOrder]; simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  exact hd.hasDerivAt

/-- The `θ`-direction `L¹`-Cauchy bound, obtained from the box-local `z`-direction engine
`l1_cauchy_pz_gen` by transposing the two coordinates.  All the hypotheses are box-local, so the
transposition is legitimate even when the box is not contained in the open quadrant. -/
theorem cauchy_theta_of_z_gen {a b c c₀ d d₀ M : ℝ} (ha : 0 < a) (hab : a < b)
    (hc₀ : 0 < c₀) (hc₀c : c₀ < c) (hcd : c < d) (hdd₀ : d < d₀) (hM : 0 ≤ M)
    {L : ℕ → ℝ → ℝ → ℝ} {Llim : ℝ → ℝ → ℝ}
    (hconv : TendstoUniformlyOn (fun n (p : ℝ × ℝ) => L n p.1 p.2) (fun p => Llim p.1 p.2)
      Filter.atTop (Set.Icc a b ×ˢ Set.Icc c₀ d₀))
    (hder : ∀ n : ℕ, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c₀ d₀,
      HasDerivAt (fun θ' => L n z θ') (Work.Spaces.pth (L n) z θ) θ)
    (hder2 : ∀ n : ℕ, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c₀ d₀,
      HasDerivAt (fun θ' => Work.Spaces.pth (L n) z θ')
        (Work.Spaces.pth (Work.Spaces.pth (L n)) z θ) θ)
    (hcont : ∀ n : ℕ, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth (L n) p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c₀ d₀))
    (hcont2 : ∀ n : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pth (L n)) p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c₀ d₀))
    (h1 : ∀ n : ℕ, ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c₀ d₀,
        ENNReal.ofReal ((Work.Spaces.pth (L n) p.1 p.2) ^ 2) ≤ ENNReal.ofReal M)
    (h2 : ∀ n : ℕ, ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c₀ d₀,
        ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pth (L n)) p.1 p.2) ^ 2)
          ≤ ENNReal.ofReal M) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal |Work.Spaces.pth (L n) p.1 p.2 - Work.Spaces.pth (L m) p.1 p.2|
          ≤ ENNReal.ofReal ε := by
  intro ε hε
  have hconvS : TendstoUniformlyOn (fun n (p : ℝ × ℝ) => L n p.2 p.1) (fun p => Llim p.2 p.1)
      Filter.atTop (Set.Icc c₀ d₀ ×ˢ Set.Icc a b) := tendstoUniformlyOn_swap_box hconv
  have hcontS : ∀ n : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pth (L n) p.2 p.1) (Set.Icc c₀ d₀ ×ˢ Set.Icc a b) :=
    fun n => continuousOn_swap_box (hcont n)
  have hcont2S : ∀ n : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pth (L n)) p.2 p.1)
      (Set.Icc c₀ d₀ ×ˢ Set.Icc a b) :=
    fun n => continuousOn_swap_box (hcont2 n)
  have h1S : ∀ n : ℕ, ∫⁻ p in Set.Icc c₀ d₀ ×ˢ Set.Icc a b,
      ENNReal.ofReal ((Work.Spaces.pth (L n) p.2 p.1) ^ 2) ≤ ENNReal.ofReal M := by
    intro n
    have hgoal : ∫⁻ p in Set.Icc c₀ d₀ ×ˢ Set.Icc a b,
        (fun q : ℝ × ℝ => ENNReal.ofReal ((Work.Spaces.pth (L n) q.1 q.2) ^ 2))
          (Prod.swap p) ≤ ENNReal.ofReal M := by
      rw [← lintegral_swap_box (a := a) (b := b) (c := c₀) (d := d₀)
        (f := fun q : ℝ × ℝ => ENNReal.ofReal ((Work.Spaces.pth (L n) q.1 q.2) ^ 2))]
      exact h1 n
    exact hgoal
  have h2S : ∀ n : ℕ, ∫⁻ p in Set.Icc c₀ d₀ ×ˢ Set.Icc a b,
      ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pth (L n)) p.2 p.1) ^ 2)
        ≤ ENNReal.ofReal M := by
    intro n
    have hgoal : ∫⁻ p in Set.Icc c₀ d₀ ×ˢ Set.Icc a b,
        (fun q : ℝ × ℝ =>
          ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pth (L n)) q.1 q.2) ^ 2))
          (Prod.swap p) ≤ ENNReal.ofReal M := by
      rw [← lintegral_swap_box (a := a) (b := b) (c := c₀) (d := d₀)
        (f := fun q : ℝ × ℝ =>
          ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pth (L n)) q.1 q.2) ^ 2))]
      exact h2 n
    exact hgoal
  obtain ⟨N, hN⟩ := l1_cauchy_pz_gen (a := c) (b := d) (a₀ := c₀) (b₀ := d₀) (c := a) (d := b)
    (M := M) (L := fun n x y => L n y x) (Llim := fun x y => Llim y x)
    hc₀ hc₀c hcd hdd₀ hab hM hconvS hder hder2 hcontS hcont2S h1S h2S ε hε
  refine ⟨N, fun n m hn hm => ?_⟩
  have hgoal : ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
      (fun q : ℝ × ℝ => ENNReal.ofReal
        |Work.Spaces.pth (L n) q.1 q.2 - Work.Spaces.pth (L m) q.1 q.2|) p
      ≤ ENNReal.ofReal ε := by
    rw [lintegral_swap_box (a := a) (b := b) (c := c) (d := d)
      (f := fun q : ℝ × ℝ => ENNReal.ofReal
        |Work.Spaces.pth (L n) q.1 q.2 - Work.Spaces.pth (L m) q.1 q.2|)]
    exact hN n m hn hm
  exact hgoal

/-! ## The `z`-slot round -/

/-- The `z`-direction round: the slot `(j' + 1, i)` converges a.e. on `eBox m` along a
subsequence. -/
theorem round_z {α B : ℝ} (hα : 0 < α) {G : ℕ → ℝ → ℝ → ℝ} {φ : ℕ → ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n))
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 6 (G n) ≤ B)
    (hconv4 : ∀ (j i : ℕ), j + i ≤ 4 → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ Work.FTS.EllipticEst.Q0 →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => Work.Spaces.mixed j i (G (φ n)) p.1 p.2)
        (fun p => Work.Spaces.mixed j i f p.1 p.2) Filter.atTop K)
    {j' i : ℕ} (hji : j' + i ≤ 4) {τ : ℕ → ℕ} (hτ : StrictMono τ) (m : ℕ) :
    ∃ ν : ℕ → ℕ, StrictMono ν ∧
      ∀ᵐ p ∂(volume.restrict (eBox m)),
        Filter.Tendsto (fun n => Work.Spaces.mixed (j' + 1) i (G (φ (τ (ν n)))) p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.mixed (j' + 1) i f p.1 p.2)) := by
  classical
  obtain ⟨M, hM, hM1, hM2, -, -⟩ :=
    deriv_slot_lintegral_bounds (α := α) (B := B) hα (F := fun n => G (φ (τ n)))
      (fun n => hsm (φ (τ n))) (fun n => hmem (φ (τ n))) (fun n => hb (φ (τ n)))
      (ea₀_pos m) (((ea₀_lt_ea m).le.trans (ea_lt_eb m).le).trans (eb_lt_eb₀ m).le)
      (ec_pos m) (ed_lt_pi m) j' i hji
  have hsub : eBoxZ m ⊆ Work.FTS.EllipticEst.Q0 := eBoxZ_subset_Q0 m
  have hcompact : IsCompact (eBoxZ m) := by
    simpa only [eBoxZ] using
      (isCompact_Icc.prod isCompact_Icc :
        IsCompact (Set.Icc (ea₀ m) (eb₀ m) ×ˢ Set.Icc (ec m) (ed m)))
  have hconv : TendstoUniformlyOn
      (fun n (p : ℝ × ℝ) => Work.Spaces.mixed j' i (G (φ (τ n))) p.1 p.2)
      (fun p => Work.Spaces.mixed j' i f p.1 p.2) Filter.atTop (eBoxZ m) :=
    tendstoUniformlyOn_subseq hτ (hconv4 j' i hji (eBoxZ m) hcompact hsub)
  have hcont : ∀ n : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.mixed j' i (G (φ (τ n))) p.1 p.2) (eBoxZ m) :=
    fun n => ((hsm (φ (τ n))).mixed j' i).continuousOn.mono hsub
  have hcontdz : ∀ n : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.mixed j' i (G (φ (τ n)))) p.1 p.2)
      (eBoxZ m) :=
    fun n => (((hsm (φ (τ n))).mixed j' i).pz).continuousOn.mono hsub
  have hslice : ∀ n : ℕ, ∀ θ ∈ Set.Icc (ec m) (ed m),
      ContDiffOn ℝ 1 (fun z => Work.Spaces.mixed j' i (G (φ (τ n))) z θ)
        (Set.Ioo (ea₀ m) (eb₀ m)) := by
    intro n θ hθ
    have hθ' : θ ∈ Set.Ioo (0 : ℝ) (π / 2) :=
      ⟨lt_of_lt_of_le (ec_pos m) hθ.1, lt_of_le_of_lt hθ.2 (ed_lt_pi m)⟩
    exact ((((hsm (φ (τ n))).mixed j' i).curry_z hθ').of_le one_le_smoothOrder).mono
      (fun z hz => lt_of_lt_of_le (ea₀_pos m) hz.1.le)
  obtain ⟨ν, hν, hνae⟩ :=
    ae_extract_z (M := M) (ha₀ := ea₀_pos m) (ha₀a := ea₀_lt_ea m) (hab := ea_lt_eb m)
      (hbb₀ := eb_lt_eb₀ m) (hc := ec_pos m) (hcd := ec_lt_ed m) (hM := hM)
      hcont hcontdz hslice hconv
      (l1_cauchy_pz (M := M) (ha₀ := ea₀_pos m) (ha₀a := ea₀_lt_ea m) (hab := ea_lt_eb m)
        (hbb₀ := eb_lt_eb₀ m) (hc := ec_pos m) (hcd := ec_lt_ed m) (hd := ed_lt_pi m)
        (hM := hM) (fun n => (hsm (φ (τ n))).mixed j' i) hconv hM1 hM2)
      hM1
  refine ⟨ν, hν, ?_⟩
  filter_upwards [hνae] with p hp
  simpa only [mixed_succ_apply] using hp.const_mul p.1

/-! ## The `θ`-slot round -/

/-- The `θ`-direction round: the slot `(0, 5)` converges a.e. on `eBox m` along a subsequence. -/
theorem round_theta {α B : ℝ} (hα : 0 < α) {G : ℕ → ℝ → ℝ → ℝ} {φ : ℕ → ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n))
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 6 (G n) ≤ B)
    (hconv4 : ∀ (j i : ℕ), j + i ≤ 4 → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ Work.FTS.EllipticEst.Q0 →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => Work.Spaces.mixed j i (G (φ n)) p.1 p.2)
        (fun p => Work.Spaces.mixed j i f p.1 p.2) Filter.atTop K)
    {τ : ℕ → ℕ} (hτ : StrictMono τ) (m : ℕ) :
    ∃ ν : ℕ → ℕ, StrictMono ν ∧
      ∀ᵐ p ∂(volume.restrict (eBox m)),
        Filter.Tendsto (fun n => Work.Spaces.mixed 0 5 (G (φ (τ (ν n)))) p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.mixed 0 5 f p.1 p.2)) := by
  classical
  obtain ⟨M, hM, -, -, hM3, hM4⟩ :=
    deriv_slot_lintegral_bounds (α := α) (B := B) hα (F := fun n => G (φ (τ n)))
      (fun n => hsm (φ (τ n))) (fun n => hmem (φ (τ n))) (fun n => hb (φ (τ n)))
      (ea_pos m) (ea_lt_eb m).le (ec₀_pos m) (ed₀_lt_pi m) 0 4 (by norm_num)
  have hsubT : eBoxT m ⊆ Work.FTS.EllipticEst.Q0 := eBoxT_subset_Q0 m
  have hcompactT : IsCompact (eBoxT m) := by
    simpa only [eBoxT] using
      (isCompact_Icc.prod isCompact_Icc :
        IsCompact (Set.Icc (ea m) (eb m) ×ˢ Set.Icc (ec₀ m) (ed₀ m)))
  have hconvT : TendstoUniformlyOn
      (fun n (p : ℝ × ℝ) => Work.Spaces.mixed 0 4 (G (φ (τ n))) p.1 p.2)
      (fun p => Work.Spaces.mixed 0 4 f p.1 p.2) Filter.atTop (eBoxT m) :=
    tendstoUniformlyOn_subseq hτ (hconv4 0 4 (by norm_num) (eBoxT m) hcompactT hsubT)
  have hcontT : ∀ n : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.mixed 0 4 (G (φ (τ n))) p.1 p.2) (eBoxT m) :=
    fun n => ((hsm (φ (τ n))).mixed 0 4).continuousOn.mono hsubT
  have hthcontT : ∀ n : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.mixed 0 4 (G (φ (τ n)))) p.1 p.2)
      (eBoxT m) :=
    fun n => (((hsm (φ (τ n))).mixed 0 4).pth).continuousOn.mono hsubT
  have hth2contT : ∀ n : ℕ, ContinuousOn
      (fun p : ℝ × ℝ =>
        Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed 0 4 (G (φ (τ n))))) p.1 p.2)
      (eBoxT m) :=
    fun n => ((((hsm (φ (τ n))).mixed 0 4).pth).pth).continuousOn.mono hsubT
  have hsliceT : ∀ n : ℕ, ∀ z ∈ Set.Icc (ea m) (eb m),
      ContDiffOn ℝ 1 (fun θ => Work.Spaces.mixed 0 4 (G (φ (τ n))) z θ)
        (Set.Ioo (ec₀ m) (ed₀ m)) := by
    intro n z hz
    have hz' : 0 < z := lt_of_lt_of_le (ea_pos m) hz.1
    exact ((((hsm (φ (τ n))).mixed 0 4).curry_θ hz').of_le one_le_smoothOrder).mono
      (Set.Ioo_subset_Ioo (ec₀_pos m).le (ed₀_lt_pi m).le)
  have hderT : ∀ n : ℕ, ∀ z ∈ Set.Icc (ea m) (eb m), ∀ θ ∈ Set.Icc (ec₀ m) (ed₀ m),
      HasDerivAt (fun θ' => Work.Spaces.mixed 0 4 (G (φ (τ n))) z θ')
        (Work.Spaces.pth (Work.Spaces.mixed 0 4 (G (φ (τ n)))) z θ) θ := by
    intro n z hz θ hθ
    have hz' : 0 < z := lt_of_lt_of_le (ea_pos m) hz.1
    have hθ' : θ ∈ Set.Ioo (0 : ℝ) (π / 2) :=
      ⟨lt_of_lt_of_le (ec₀_pos m) hθ.1, lt_of_le_of_lt hθ.2 (ed₀_lt_pi m)⟩
    exact hasDerivAt_slice_theta ((hsm (φ (τ n))).mixed 0 4) hz' hθ'
  have hder2T : ∀ n : ℕ, ∀ z ∈ Set.Icc (ea m) (eb m), ∀ θ ∈ Set.Icc (ec₀ m) (ed₀ m),
      HasDerivAt (fun θ' => Work.Spaces.pth (Work.Spaces.mixed 0 4 (G (φ (τ n)))) z θ')
        (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed 0 4 (G (φ (τ n))))) z θ) θ := by
    intro n z hz θ hθ
    have hz' : 0 < z := lt_of_lt_of_le (ea_pos m) hz.1
    have hθ' : θ ∈ Set.Ioo (0 : ℝ) (π / 2) :=
      ⟨lt_of_lt_of_le (ec₀_pos m) hθ.1, lt_of_le_of_lt hθ.2 (ed₀_lt_pi m)⟩
    exact hasDerivAt_slice_theta (((hsm (φ (τ n))).mixed 0 4).pth) hz' hθ'
  have hcauchy := cauchy_theta_of_z_gen (a := ea m) (b := eb m) (c := ec m) (c₀ := ec₀ m)
    (d := ed m) (d₀ := ed₀ m) (M := M) (ea_pos m) (ea_lt_eb m) (ec₀_pos m) (ec₀_lt_ec m)
    (ec_lt_ed m) (ed_lt_ed₀ m) hM hconvT hderT hder2T hthcontT hth2contT hM3 hM4
  obtain ⟨ν, hν, hνae⟩ :=
    ae_extract_theta (M := M) (a := ea m) (b := eb m) (c := ec m) (c₀ := ec₀ m) (d := ed m)
      (d₀ := ed₀ m) (ea_pos m) (ea_lt_eb m) (ec₀_pos m) (ec₀_lt_ec m) (ec_lt_ed m)
      (ed_lt_ed₀ m) hM hcontT hthcontT hsliceT hconvT hcauchy hM3
  refine ⟨ν, hν, ?_⟩
  filter_upwards [hνae] with p hp
  simpa only [mixed_zero_five_apply] using hp.const_mul (Real.sin (2 * p.2))

/-! ## The diagonal round for one slot -/

/-- One diagonal-extraction round: for the fixed slot `(j, i)` with `j + i = 5` and the current
base `φ ∘ τ`, there is a further strictly increasing `Φ` such that the slot converges a.e. on each
exhaustion box along `G (φ (τ (Φ n)))`. -/
theorem round_slot {α B : ℝ} (hα : 0 < α) {G : ℕ → ℝ → ℝ → ℝ} {φ : ℕ → ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n))
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 6 (G n) ≤ B)
    (hconv4 : ∀ (j i : ℕ), j + i ≤ 4 → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ Work.FTS.EllipticEst.Q0 →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => Work.Spaces.mixed j i (G (φ n)) p.1 p.2)
        (fun p => Work.Spaces.mixed j i f p.1 p.2) Filter.atTop K)
    {j i : ℕ} (hji : j + i = 5) {τ : ℕ → ℕ} (hτ : StrictMono τ) :
    ∃ Φ : ℕ → ℕ, StrictMono Φ ∧
      ∀ m : ℕ, ∀ᵐ p ∂(volume.restrict Work.FTS.EllipticEst.Q0), p ∈ eBox m →
        Filter.Tendsto (fun n => Work.Spaces.mixed j i (G (φ (τ (Φ n)))) p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.mixed j i f p.1 p.2)) := by
  classical
  have hrow : ∀ m : ℕ, ∀ σ : ℕ → ℕ, StrictMono σ →
      ∃ ν : ℕ → ℕ, StrictMono ν ∧
        ∀ᵐ p ∂(volume.restrict (eBox m)),
          Filter.Tendsto (fun n => Work.Spaces.mixed j i (G (φ (τ (σ (ν n))))) p.1 p.2)
            Filter.atTop (nhds (Work.Spaces.mixed j i f p.1 p.2)) := by
    intro m σ hσ
    rcases j with _ | j'
    · have hi : i = 5 := by omega
      subst hi
      exact round_theta (α := α) (B := B) hα hsm hmem hb hconv4 (τ := fun n => τ (σ n))
        (hτ.comp hσ) m
    · have hji' : j' + i ≤ 4 := by omega
      exact round_z (α := α) (B := B) hα hsm hmem hb hconv4 hji' (τ := fun n => τ (σ n))
        (hτ.comp hσ) m
  obtain ⟨Φ, hΦ, hdiag⟩ := exists_diag_extract
    (μ := volume.restrict Work.FTS.EllipticEst.Q0)
    (F := fun k n p => if p ∈ eBox k then Work.Spaces.mixed j i (G (φ (τ n))) p.1 p.2 else 0)
    (G := fun k p => if p ∈ eBox k then Work.Spaces.mixed j i f p.1 p.2 else 0)
    (fun k σ hσ => by
      obtain ⟨ν, hν, hνae⟩ := hrow k σ hσ
      refine ⟨ν, hν, ?_⟩
      have hmemk : ∀ᵐ p ∂(volume.restrict Work.FTS.EllipticEst.Q0), p ∈ eBox k →
          Filter.Tendsto
            (fun n => Work.Spaces.mixed j i (G (φ (τ (σ (ν n))))) p.1 p.2)
            Filter.atTop (nhds (Work.Spaces.mixed j i f p.1 p.2)) := by
        rw [MeasureTheory.ae_restrict_iff' (μ := volume) (s := eBox k) (measurableSet_eBox k)]
          at hνae
        rw [MeasureTheory.ae_restrict_iff' (μ := volume) (s := Work.FTS.EllipticEst.Q0)
          Work.FTS.EllipticEst.isOpen_Q0.measurableSet]
        filter_upwards [hνae] with p hp _
        exact hp
      filter_upwards [hmemk] with p hp
      by_cases h : p ∈ eBox k
      · simpa [h] using hp h
      · simp only [h, if_false]
        exact tendsto_const_nhds)
  refine ⟨Φ, hΦ, fun m => ?_⟩
  filter_upwards [hdiag m] with p hp hpm
  simpa only [hpm, if_true] using hp

end Work.FTS.StrongEps.LocUnif.D5
