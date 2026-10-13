/-
Copyright: work module for the Elgindi finite-time singularity project.

# `T2S`: Elgindi's `Transport2` in the true form (design `ELL_H2_LEAD.md` §B2)

The frozen statement (verbatim from `Submission/Work/FTS/ELL_H2_STATEMENTS.lean.txt`):

```
theorem T2S : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    SmoothOpen f → HkMem α 4 f → CoefThMem 1 f →
    RegQ α 4 g → HkMem α 5 g → DecayAll 4 g →
    |H4Pair α (fun z θ => f z θ * Dz g z θ) g|
      ≤ C / √(gam α - 1) * (Xn α f + CoefTh 1 f) * Xn α g ^ 2
```

This module states it as `T2S_of_pieces` together with the *five* mathematical inputs it is
reduced to.  The reduction is the bookkeeping of `Work.FTS.H2.T2Qaux.assembly` with the
`f`-pointwise data `Mf` replaced by `C₁·(|f|_{ℋ⁴} + CoefTh 1 f)`; the analytic content sits
in the five `Prop`s below.

## The five inputs

* `T2SupF` — the pointwise sup bounds of order `≤ 2` for the **coefficient** `f`, from the
  frozen hypotheses `SmoothOpen f`, `HkMem α 4 f`, `CoefThMem 1 f` alone (no decay!).
  Its `a ≥ 1` half is the σ-gain `flat_mixed_le` (`D_θ^a f` carries a factor `sin 2θ`), its
  `a = 0` half is `sup_dz_le_hk`.  This is *the* place where the design's claim
  "`L^∞` from `ℋ⁴`" has to be made precise: the frozen `T2S` does **not** assume
  `DecayAll 4 f`, so the pointwise bounds must come from the `ℋ⁴`-membership itself.
* `T2SupG` — the same for the test function `g`; **proved** below from the proved
  `T2Qaux.supQ_T2Q` (Elgindi's `SecondDerivativesBounded`) since `RegQ α 4 g` supplies
  `SmoothQuad g`, `HkMem α 4 g` and the frozen hypotheses supply `DecayAll 4 g`.
* `T2Slice` — the `θ`-slice integrability of `Heasy` (the `SmoothOpen`/`CoefThMem` analogue of
  the *false* `Work.FTS.H2.T2SliceEasyQuad`; the extra `CoefThMem 1 f` makes it true).
* `T2Easy` — the bound on the "easy" part (at least one derivative on `f`).
* `T2Hard` — the bound on the five order-five "hard" terms (`f·D_z^5g·D_z^4g·Whz²` and
  `f·D_z(mixed j i g)·mixed j i g·Wm²`), by radial integration by parts.
* `T2Aesm` — the a.e. strong measurability bookkeeping of the two radial marginals.

All five are stated for exactly the frozen hypothesis set, so `T2S_of_pieces` gives the frozen
statement verbatim once they land.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.H2.T2Defs
import Submission.Work.FTS.H2.T2Qaux.SupQ
import Submission.Work.FTS.H2.AesmSlicesQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The hypothesis bundles -/

/-- The frozen `f`-side hypotheses of `T2S`: interior `C^∞`, honesty of `ℋ⁴`, and the flat
angular coefficient norm.  (No decay of `f`: the pointwise bounds come from `T2SupF`.) -/
def T2SF (α : ℝ) (f : Fn) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen f ∧ Work.Spaces.HkMem α 4 f ∧ Work.FTS.VocabO.CoefThMem 1 f

/-- The frozen `g`-side hypotheses of `T2S`. -/
def T2SG (α : ℝ) (g : Fn) : Prop :=
  Work.FTS.Nonlin.RegQ α 4 g ∧ Work.Spaces.HkMem α 5 g ∧ Work.Spaces.DecayAll 4 g

theorem T2SF.smoothOpen {α : ℝ} {f : Fn} (h : T2SF α f) :
    Work.FTS.EllipticEst.SmoothOpen f := h.1
theorem T2SF.hk {α : ℝ} {f : Fn} (h : T2SF α f) : Work.Spaces.HkMem α 4 f := h.2.1
theorem T2SF.coef {α : ℝ} {f : Fn} (h : T2SF α f) : Work.FTS.VocabO.CoefThMem 1 f := h.2.2
theorem T2SG.reg {α : ℝ} {g : Fn} (h : T2SG α g) : Work.FTS.Nonlin.RegQ α 4 g := h.1
theorem T2SG.hk4 {α : ℝ} {g : Fn} (h : T2SG α g) : Work.Spaces.HkMem α 4 g := h.1.2.1
theorem T2SG.hk5 {α : ℝ} {g : Fn} (h : T2SG α g) : Work.Spaces.HkMem α 5 g := h.2.1
theorem T2SG.decay {α : ℝ} {g : Fn} (h : T2SG α g) : Work.Spaces.DecayAll 4 g := h.2.2

/-! ## The five inputs -/

/-- **Input 1**: the pointwise sup bounds of order `≤ 2` for the coefficient `f`, from the
frozen hypotheses of `T2S` alone, with a constant **uniform in `α`**.

This uniformity is forced by the frozen statement of `T2S`, whose right-hand side carries only
one factor `1/√(γ-1)`; a bound `C/√(γ-1)·(…)` for `Mf` would produce a `1/(γ-1)` on the right
and would not be absorbable.

Route.  Write `Q := Xn α f`, `K := CoefTh 1 f`.

* `a ≥ 1`: the σ-gain `flat_mixed_le 1` with the sup data `K` gives
  `|D_z^bD_θ^a f| ≤ C₁·sin(2θ)·K ≤ C₁·K` for `1 ≤ a`, `a + b ≤ 2`.
* `a = 0`: (i) the *radial* Hardy inequality for the weight `w` is `α`-free:
  `sup_z|g(z)|² ≤ (1/3)∫_0^∞ (D_zg(z))² w(z)² dz` (from `g(0) = g(∞) = 0`, the constant being
  `∫_0^∞ z²/(1+z)^4 = 1/3`); applied to the θ-slice at `θ = π/4` (where `sin 2θ = 1`) it gives
  `|f(z,π/4)| ≤ C Q` uniformly in `z` and `α` — here `f(0⁺,·) = 0` and `f(∞,·) = 0` are
  *derived* from `HkMem α 4 f` (the slots `(D_zf)²w²σ^{-η}` and `f²w²σ^{-η}` force both ends to
  vanish: `∫_0^1 f²z^{-4} < ∞` kills the value at `0⁺`, and `∫_0^∞ f² < ∞` plus the existence of
  the limit at `∞` kills it there);
  (ii) `|f(z,θ)| ≤ |f(z,π/4)| + (π/4)·sup|∂_θf| ≤ C Q + (π/4) K`, because
  `CoefThMem 1 f` bounds `∂_θf` by `K = CoefTh 1 f` (`supAbsO_le_coefTh`);
  (iii) the same two steps for the finitely many `D_z^b f`, `b ≤ 2`, using the slots
  `D_z^{b+1}f` and `D_z^{b+1}D_θf` (all of order `≤ 4`, hence in `ℋ⁴`). -/


def T2SupF : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Fn), 0 < α → α ≤ 1 → T2SF α f →
    ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a f z θ|
        ≤ C * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)

/-- **Input 2**: the pointwise sup bounds of order `≤ 2` for the test function `g`. -/
def T2SupG : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : Fn), 0 < α → α ≤ 1 → T2SG α g →
    ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a g z θ|
        ≤ C / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α g

/-- **Input 3**: the `θ`-slice integrability of the easy part `Heasy`. -/
def T2Slice : Prop :=
  ∀ (α : ℝ) (f g : Fn), 0 < α → α ≤ 1 → T2SF α f → T2SG α g →
    ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => Work.FTS.H2.Heasy α f g z θ) Work.Spaces.Iθ

/-- **Input 4**: the bound on the easy part of the pairing, with the pointwise data `Mf`, `Mg`
as parameters (exactly the shape of `Work.FTS.H2.EasyQ_T2Q`). -/
def T2Easy : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : Fn) (Mf Mg : ℝ),
    0 < α → α ≤ 1 → 0 ≤ Mf → 0 ≤ Mg → T2SF α f → T2SG α g →
    (∀ (b a : ℕ), a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a f z θ| ≤ Mf) →
    (∀ (b a : ℕ), a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a g z θ| ≤ Mg) →
    MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.H2.Heasy α f g z θ) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz,
          |∫ θ in Work.Spaces.Iθ, Work.FTS.H2.Heasy α f g z θ|)
        ≤ C * (Mf * Work.Spaces.HkNorm α 4 g ^ 2
            + Mg * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g)

/-- **Input 5**: the bound on the five order-five terms `Hhard`, by radial integration by
parts (exactly the shape of `Work.FTS.H2.HardQ_T2Q`). -/
def T2Hard : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : Fn) (Mf : ℝ),
    0 < α → α ≤ 1 → 0 ≤ Mf → T2SF α f → T2SG α g →
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf) →
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |Work.Spaces.Dz f z θ| ≤ Mf) →
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.FTS.H2.Hhard α f g z θ|
      ≤ C * Mf * Work.Spaces.HkSq α 4 g

/-- **Input 6**: the a.e. strong measurability of the two radial marginals (the
`SmoothOpen`/`CoefThMem` analogue of `Work.FTS.H2.AesmSlicesQ`). -/
def T2Aesm : Prop :=
  ∀ (α : ℝ) (f g : Fn), 0 < α → T2SF α f → T2SG α g →
    MeasureTheory.AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.H2.Hhard α f g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
      MeasureTheory.AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz)

/-! ## `T2SupG` is proved (from the proved `SecondDerivativesBounded` of `T2Qaux`) -/

/-- The `g`-side pointwise bounds of order `≤ 2` follow from the proved
`Work.FTS.H2.T2Qaux.supQ_T2Q` (Elgindi's `SecondDerivativesBounded` in the interior class)
because `RegQ α 4 g` supplies `SmoothQuad g` and the frozen hypotheses supply
`DecayAll 4 g`. -/
theorem T2SupG_proof : T2SupG := by
  obtain ⟨C, hC, hsup⟩ := Work.FTS.H2.T2Qaux.supQ_T2Q
  refine ⟨C, hC, ?_⟩
  intro α g hα hα1 hg b a hab z θ hz hθ hθ'
  exact hsup α g b a hα hα1 hab hg.reg.1 hg.decay hg.hk4 z hz θ ⟨hθ, hθ'⟩

/-! ## The assembly -/

/-- **`T2S` from its five inputs.**  The proof is the bookkeeping of
`Work.FTS.H2.T2Qaux.assembly`, with `Mf := C₁(|f|_{ℋ⁴} + CoefTh 1 f)` supplied by `T2SupF`
and `Mg := C₂/√(γ-1)|g|_{ℋ⁴}` supplied by `T2SupG`. -/
theorem T2S_of_pieces (hF : T2SupF) (hG : T2SupG) (hSlice : T2Slice)
    (hEasy : T2Easy) (hHard : T2Hard) (hAesm : T2Aesm) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : Fn), 0 < α → α ≤ 1 → T2SF α f → T2SG α g →
      |Work.FTS.H2.H4Pair α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
        ≤ C / Real.sqrt (Work.Spaces.gam α - 1)
            * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
            * Work.FTS.Nonlin.Xn α g ^ 2 := by
  obtain ⟨C1, hC1pos, hF⟩ := hF
  obtain ⟨C2, hC2pos, hG⟩ := hG
  obtain ⟨C3, hC3pos, hEasy⟩ := hEasy
  obtain ⟨C4, hC4pos, hHard⟩ := hHard
  refine ⟨C1 * C3 + C2 * C3 + C1 * C4, by positivity, ?_⟩
  intro α f g hα hα1 hsf hsg
  have hγ : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγs : 0 < Real.sqrt (Work.Spaces.gam α - 1) := Real.sqrt_pos.mpr hγ
  have hγle : Real.sqrt (Work.Spaces.gam α - 1) ≤ 1 := by
    rw [Real.sqrt_le_one, Work.Spaces.gam_sub_one]; linarith
  have hXf : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hCb : 0 ≤ Work.FTS.VocabO.CoefTh 1 f := coefTh_nonneg 1 f
  set W : ℝ := Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f with hW
  have hWnn : 0 ≤ W := by rw [hW]; linarith
  have hXfW : Work.Spaces.HkNorm α 4 f ≤ W := by rw [hW, Work.FTS.Nonlin.Xn]; linarith
  -- the pointwise data
  have hbf : ∀ (b a : ℕ), a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a f z θ| ≤ C1 * W := by
    intro b a hab z θ hz hθ hθ'
    rw [hW]; exact hF α f hα hα1 hsf b a hab z θ hz hθ hθ'
  have hbg : ∀ (b a : ℕ), a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a g z θ| ≤ C2 / Real.sqrt (Work.Spaces.gam α - 1)
        * Work.FTS.Nonlin.Xn α g :=
    fun b a hab z θ hz hθ hθ' => hG α g hα hα1 hsg b a hab z θ hz hθ hθ'
  have hSlinteg := hSlice α f g hα hα1 hsf hsg
  have hE := hEasy α f g (C1 * W)
    (C2 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α g)
    hα hα1 (by positivity) (by positivity) hsf hsg hbf hbg
  have hH := hHard α f g (C1 * W) hα hα1 (by positivity) hsf hsg
    (fun z θ hz hθ hθ' => by
      have h := hbf 0 0 (by norm_num) z θ hz hθ hθ'
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero,
        Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero] using h)
    (fun z θ hz hθ hθ' => by
      have h := hbf 1 0 (by norm_num) z θ hz hθ hθ'
      simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_succ,
        Work.Spaces.DzIter_zero] using h)
  obtain ⟨hAesmH, hAesmF⟩ := hAesm α f g hα hsf hsg
  -- from here on the bookkeeping is verbatim `T2Qaux.assembly`
  set ψE : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.H2.Heasy α f g z θ with hψE
  set ψH : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.H2.Hhard α f g z θ with hψH
  set Ff : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g z θ with hFf
  set A : Set ℝ := {z | MeasureTheory.IntegrableOn
    (fun θ => Work.FTS.H2.Hhard α f g z θ) Work.Spaces.Iθ} with hA
  have hIθm : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hIzm : MeasurableSet Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]; exact measurableSet_Ici
  have hident : ∀ z ∈ Work.Spaces.Iz, Ff z = A.indicator ψE z + ψH z := by
    intro z hz
    by_cases hzA : z ∈ A
    · have hHe : MeasureTheory.IntegrableOn (fun θ => Work.FTS.H2.Heasy α f g z θ)
          Work.Spaces.Iθ := hSlinteg z hz
      have hHh : MeasureTheory.IntegrableOn (fun θ => Work.FTS.H2.Hhard α f g z θ)
          Work.Spaces.Iθ := by rw [hA] at hzA; exact hzA
      have hsum : Ff z = ψE z + ψH z := by
        change (∫ θ in Work.Spaces.Iθ,
              Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g z θ)
            = (∫ θ in Work.Spaces.Iθ, Work.FTS.H2.Heasy α f g z θ)
              + (∫ θ in Work.Spaces.Iθ, Work.FTS.H2.Hhard α f g z θ)
        rw [show (fun θ => Work.FTS.H2.H4PairInt α
              (fun z θ => f z θ * Work.Spaces.Dz g z θ) g z θ)
            = fun θ => Work.FTS.H2.Heasy α f g z θ + Work.FTS.H2.Hhard α f g z θ from
          funext fun θ => Work.FTS.H2.H4PairInt_eq_easy_add_hard α f g z θ]
        exact MeasureTheory.integral_add hHe hHh
      rw [hsum, Set.indicator_of_mem hzA]
    · have hHe : MeasureTheory.IntegrableOn (fun θ => Work.FTS.H2.Heasy α f g z θ)
          Work.Spaces.Iθ := hSlinteg z hz
      have hnotint : ¬ MeasureTheory.Integrable
          (fun θ => Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dz g z θ)
            g z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        intro hcon
        have hh : MeasureTheory.IntegrableOn (fun θ => Work.FTS.H2.Hhard α f g z θ)
            Work.Spaces.Iθ := by
          have hsub : (fun θ => Work.FTS.H2.Hhard α f g z θ)
              = fun θ => Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dz g z θ)
                  g z θ - Work.FTS.H2.Heasy α f g z θ := by
            funext θ
            rw [Work.FTS.H2.H4PairInt_eq_easy_add_hard α f g z θ]; ring
          rw [hsub]
          exact hcon.sub hHe
        exact hzA (by rw [hA]; exact hh)
      have hF0 : Ff z = 0 := by rw [hFf]; exact MeasureTheory.integral_undef hnotint
      have hψH0 : ψH z = 0 := by
        rw [hψH]
        exact MeasureTheory.integral_undef (by rw [hA] at hzA; exact hzA)
      rw [hF0, Set.indicator_of_notMem hzA, hψH0]
      ring
  have h1Aint : MeasureTheory.Integrable (A.indicator ψE)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have haesm : MeasureTheory.AEStronglyMeasurable (A.indicator ψE)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have h : (fun z => Ff z - ψH z) =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
          A.indicator ψE := by
        filter_upwards [MeasureTheory.ae_restrict_mem hIzm] with z hz
        rw [hident z hz]; simp
      exact (hAesmF.sub hAesmH).congr h
    refine (hE.1.abs).mono' haesm ?_
    filter_upwards with z
    by_cases hz : z ∈ A
    · rw [Set.indicator_of_mem hz, Real.norm_eq_abs]
    · rw [Set.indicator_of_notMem hz, norm_zero]
      exact abs_nonneg _
  have hbd1A : |∫ z in Work.Spaces.Iz, A.indicator ψE z| ≤ ∫ z in Work.Spaces.Iz, |ψE z| := by
    calc |∫ z in Work.Spaces.Iz, A.indicator ψE z|
        ≤ ∫ z in Work.Spaces.Iz, |A.indicator ψE z| := MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ z in Work.Spaces.Iz, |ψE z| := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun z => abs_nonneg _) hE.1.abs ?_
          filter_upwards with z
          by_cases hz : z ∈ A
          · rw [Set.indicator_of_mem hz]
          · rw [Set.indicator_of_notMem hz, abs_zero]; exact abs_nonneg _
  -- the final bound, with `Mf = C1 * W` and `Mg = C2/s * Xg`
  have hMg2 : (C2 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α g)
      * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g
      ≤ (C2 / Real.sqrt (Work.Spaces.gam α - 1)) * W * Work.Spaces.HkNorm α 4 g ^ 2 := by
    have h1 : Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g
        ≤ W * Work.Spaces.HkNorm α 4 g := mul_le_mul_of_nonneg_right hXfW hXg
    have h2 : Work.Spaces.HkNorm α 4 g * Work.Spaces.HkNorm α 4 g
        = Work.Spaces.HkNorm α 4 g ^ 2 := by ring
    calc (C2 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α g)
          * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g
        = (C2 / Real.sqrt (Work.Spaces.gam α - 1))
          * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g)
          * Work.Spaces.HkNorm α 4 g := by
          rw [Work.FTS.Nonlin.Xn]; ring
      _ ≤ (C2 / Real.sqrt (Work.Spaces.gam α - 1)) * (W * Work.Spaces.HkNorm α 4 g)
          * Work.Spaces.HkNorm α 4 g := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h1 (by positivity)) hXg
      _ = (C2 / Real.sqrt (Work.Spaces.gam α - 1)) * W * Work.Spaces.HkNorm α 4 g ^ 2 := by
          rw [← h2]; ring
  have hcase : |Work.FTS.H2.H4Pair α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
      ≤ (C1 * C3 + C2 * C3 + C1 * C4) / Real.sqrt (Work.Spaces.gam α - 1)
        * W * Work.FTS.Nonlin.Xn α g ^ 2 := by
    by_cases hHint : MeasureTheory.Integrable ψH (MeasureTheory.volume.restrict Work.Spaces.Iz)
    · have hae : Ff =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
          fun z => A.indicator ψE z + ψH z := by
        filter_upwards [MeasureTheory.ae_restrict_mem hIzm] with z hz
        exact hident z hz
      have hadd : ∫ z in Work.Spaces.Iz, Ff z
          = (∫ z in Work.Spaces.Iz, A.indicator ψE z) + ∫ z in Work.Spaces.Iz, ψH z := by
        rw [MeasureTheory.integral_congr_ae hae]
        exact MeasureTheory.integral_add h1Aint hHint
      have hbound : |Work.FTS.H2.H4Pair α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
          ≤ C3 * ((C1 * W) * Work.Spaces.HkNorm α 4 g ^ 2
                + (C2 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α g)
                  * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g)
            + C4 * (C1 * W) * Work.Spaces.HkSq α 4 g := by
        calc |Work.FTS.H2.H4Pair α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
            = |∫ z in Work.Spaces.Iz, Ff z| := rfl
          _ = |(∫ z in Work.Spaces.Iz, A.indicator ψE z)
                + ∫ z in Work.Spaces.Iz, ψH z| := by rw [hadd]
          _ ≤ |∫ z in Work.Spaces.Iz, A.indicator ψE z| + |∫ z in Work.Spaces.Iz, ψH z| :=
              abs_add_le _ _
          _ ≤ (∫ z in Work.Spaces.Iz, |ψE z|) + C4 * (C1 * W) * Work.Spaces.HkSq α 4 g :=
              add_le_add hbd1A hH
          _ ≤ C3 * ((C1 * W) * Work.Spaces.HkNorm α 4 g ^ 2
                + (C2 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α g)
                  * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g)
              + C4 * (C1 * W) * Work.Spaces.HkSq α 4 g := add_le_add hE.2 le_rfl
      refine le_trans hbound ?_
      rw [← Work.FTS.H2.HkNorm_sq α g]
      -- `1 ≤ 1/√(γ-1)`, and `0 ≤ C2/√(γ-1)`
      have hinv : (1 : ℝ) ≤ 1 / Real.sqrt (Work.Spaces.gam α - 1) := by
        rw [one_le_div hγs]; exact hγle
      have hM := hMg2
      have h1 : C3 * ((C1 * W) * Work.Spaces.HkNorm α 4 g ^ 2)
          ≤ (1 / Real.sqrt (Work.Spaces.gam α - 1))
            * (C3 * ((C1 * W) * Work.Spaces.HkNorm α 4 g ^ 2)) := by
        calc C3 * ((C1 * W) * Work.Spaces.HkNorm α 4 g ^ 2)
            = 1 * (C3 * ((C1 * W) * Work.Spaces.HkNorm α 4 g ^ 2)) := by ring
          _ ≤ (1 / Real.sqrt (Work.Spaces.gam α - 1))
              * (C3 * ((C1 * W) * Work.Spaces.HkNorm α 4 g ^ 2)) :=
              mul_le_mul_of_nonneg_right hinv (by positivity)
      have h2 : C3 * ((C2 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α g)
            * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g)
          ≤ C3 * ((C2 / Real.sqrt (Work.Spaces.gam α - 1)) * W
              * Work.Spaces.HkNorm α 4 g ^ 2) :=
        mul_le_mul_of_nonneg_left hM (le_of_lt hC3pos)
      have h3 : C4 * (C1 * W) * Work.Spaces.HkNorm α 4 g ^ 2
          ≤ (1 / Real.sqrt (Work.Spaces.gam α - 1))
            * (C4 * (C1 * W) * Work.Spaces.HkNorm α 4 g ^ 2) := by
        calc C4 * (C1 * W) * Work.Spaces.HkNorm α 4 g ^ 2
            = 1 * (C4 * (C1 * W) * Work.Spaces.HkNorm α 4 g ^ 2) := by ring
          _ ≤ (1 / Real.sqrt (Work.Spaces.gam α - 1))
              * (C4 * (C1 * W) * Work.Spaces.HkNorm α 4 g ^ 2) :=
              mul_le_mul_of_nonneg_right hinv (by positivity)
      calc C3 * ((C1 * W) * Work.Spaces.HkNorm α 4 g ^ 2
              + (C2 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α g)
                * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g)
            + C4 * (C1 * W) * Work.Spaces.HkNorm α 4 g ^ 2
          = (C3 * ((C1 * W) * Work.Spaces.HkNorm α 4 g ^ 2)
              + C3 * ((C2 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α g)
                * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g))
            + C4 * (C1 * W) * Work.Spaces.HkNorm α 4 g ^ 2 := by ring
        _ ≤ ((1 / Real.sqrt (Work.Spaces.gam α - 1))
                * (C3 * ((C1 * W) * Work.Spaces.HkNorm α 4 g ^ 2))
              + C3 * ((C2 / Real.sqrt (Work.Spaces.gam α - 1)) * W
                * Work.Spaces.HkNorm α 4 g ^ 2))
            + (1 / Real.sqrt (Work.Spaces.gam α - 1))
                * (C4 * (C1 * W) * Work.Spaces.HkNorm α 4 g ^ 2) := by
            exact add_le_add (add_le_add h1 h2) h3
        _ = (C1 * C3 + C2 * C3 + C1 * C4) / Real.sqrt (Work.Spaces.gam α - 1)
              * W * Work.Spaces.HkNorm α 4 g ^ 2 := by
            rw [div_eq_mul_inv]
            ring
    · have hnotint : ¬ MeasureTheory.Integrable Ff
          (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
        intro hcon
        refine hHint ?_
        have hcong : ψH =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
            fun z => Ff z - A.indicator ψE z := by
          filter_upwards [MeasureTheory.ae_restrict_mem hIzm] with z hz
          rw [hident z hz]; ring
        exact (hcon.sub h1Aint).congr hcong.symm
      have hzero : |Work.FTS.H2.H4Pair α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g| = 0 := by
        rw [show Work.FTS.H2.H4Pair α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g
            = ∫ z in Work.Spaces.Iz, Ff z from rfl,
          MeasureTheory.integral_undef hnotint, abs_zero]
      rw [hzero]
      exact mul_nonneg (mul_nonneg (by positivity) hWnn) (sq_nonneg _)
  simpa only [hW] using hcase

end Work.FTS.TransportS
