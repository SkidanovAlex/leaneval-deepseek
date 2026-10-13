/-
# `OpenPkg/Basic` — the basic API of the open-quadrant interfaces

The lemmas of this module are the ones a consumer of `Submission/Work/FTS/OpenPkg/Defs.lean`
needs before it can state anything: the relations between the classes
(`RegQ`/`HQo`, `SmoothQuad`/`SmoothOpen`, `HkMem α k` for different `k`), the elementary
properties of the flat norm `CoefTh` and of the `D`-sup norms `WDp`/`WDMem`, and the side
conditions that `GalClass` supplies.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.H2.RegQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  DenseSpan WeakDetermines IsDynWeakOn ProfileBdd EquicontSpace EquicontTau profileFam RegPkg prof)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The classes -/

/-- `SmoothQuad` (genuine `C^∞` on `z > -1`, `0 < θ < π/2`) implies `SmoothOpen` (the same on the
smaller open quadrant `(0,∞) × (0,π/2)`). -/
theorem smoothOpen_of_smoothQuad {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) :
    Work.FTS.EllipticEst.SmoothOpen f := by
  refine hf.mono ?_
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  exact ⟨Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hp1]), hp2⟩

/-- **`RegQ` refines `HQo`**: the interior class of the frozen vocabulary only adds the boundary
traces to the open-quadrant class of `VocabO`. -/
theorem HQo_of_RegQ {α : ℝ} {k : ℕ} {f : Fn} (h : RegQ α k f) : HQo α k f :=
  ⟨smoothOpen_of_smoothQuad h.1, h.2.1⟩

/-- The `ℋ^k`-integrand is monotone in the order. -/
theorem HkIntegrand_mono_le (α : ℝ) {l k : ℕ} (hkl : l ≤ k) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α l f z θ ≤ Work.Spaces.HkIntegrand α k f z θ := by
  induction k, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact le_trans ih (Work.Spaces.HkIntegrand_mono α n f z θ)

/-- **`HkMem` is monotone in the order, in the open-quadrant class**: the `ℋ^k`-integrand is
dominated by the `ℋ^l`-integrand for `k ≤ l`, and the honesty of the larger one is exactly the
integrability certificate the smaller one needs. -/
theorem HkMem_mono_open {α : ℝ} {k : ℕ} {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ l : ℕ, l ≤ k → Work.Spaces.HkMem α k f → Work.Spaces.HkMem α l f :=
  fun l hlk h =>
    Work.FTS.LocData.HkMem_of_majorant α l (hf.continuousOn_HkIntegrand α l)
      h.1 h.2 (fun z _ θ _ => HkIntegrand_mono_le α hlk f z θ)

/-- `HQo` is monotone in the order. -/
theorem HQo.mono {α : ℝ} {k l : ℕ} {f : Fn} (h : HQo α k f) (hkl : l ≤ k) : HQo α l f :=
  ⟨h.1, HkMem_mono_open h.1 l hkl h.2⟩

/-- `HkMem` descends from `ℋ^5` to `ℋ^4` for functions smooth on the open quadrant. -/
theorem HkMem_four_of_five {α : ℝ} {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (h : Work.Spaces.HkMem α 5 f) : Work.Spaces.HkMem α 4 f :=
  HkMem_mono_open hf 4 (by norm_num) h

/-! ## The `GalClass` side conditions -/

theorem galClass_HkMem5 {α : ℝ} {g : Fn} (h : GalClass α g) : Work.Spaces.HkMem α 5 g :=
  HkMem_mono_open (HQo_of_RegQ h.reg).1 5 (by norm_num) h.reg.2.1

theorem galClass_HkMem4 {α : ℝ} {g : Fn} (h : GalClass α g) : Work.Spaces.HkMem α 4 g :=
  HkMem_mono_open (HQo_of_RegQ h.reg).1 4 (by norm_num) h.reg.2.1

theorem galClass_DecayAll4 {α : ℝ} {g : Fn} (h : GalClass α g) : Work.Spaces.DecayAll 4 g :=
  ⟨fun j i hij θ hθ => h.decay.1 j i (le_trans hij (by norm_num)) θ hθ,
    fun a b hab θ hθ => h.decay.2 a b (le_trans hab (by norm_num)) θ hθ⟩

theorem galClass_VanishTheta {α : ℝ} {g : Fn} (h : GalClass α g) : Work.Spaces.VanishTheta g :=
  h.vanish

theorem galClass_l12 {α : ℝ} {g : Fn} (h : GalClass α g) : Work.Construction.L12 g 0 = 0 :=
  h.l12

theorem galClass_HQo4 {α : ℝ} {g : Fn} (h : GalClass α g) : HQo α 4 g :=
  ⟨smoothOpen_of_smoothQuad h.reg.1, galClass_HkMem4 h⟩

/-- **The `T2Clause` side conditions that `GalClass` supplies**: the `g`-side of the primed
transport clauses. -/
theorem galClass_T2_side {α : ℝ} {g : Fn} (h : GalClass α g) :
    RegQ α 4 g ∧ Work.Spaces.HkMem α 5 g ∧ Work.Spaces.DecayAll 4 g :=
  ⟨Work.FTS.Nonlin.galClass_regQ4 h, galClass_HkMem5 h, galClass_DecayAll4 h⟩

/-! ## The flat angular norm `CoefTh` -/

theorem CoefThMem_mono {l l' : ℕ} {f : Fn} (h : CoefThMem l f) (hll : l' ≤ l) : CoefThMem l' f :=
  fun b i hbi => h b i (le_trans hbi hll)

/-- `supAbsO` is nonnegative. -/
theorem supAbsO_nonneg (g : ℝ → ℝ → ℝ) : 0 ≤ Work.FTS.H2.supAbsO g := by
  rw [Work.FTS.H2.supAbsO]
  by_cases h : BddAbove {y : ℝ | ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, 0 < θ ∧ θ < π / 2 ∧ y = |g z θ|}
  · exact le_trans (abs_nonneg _) (le_csSup h ⟨1, one_pos, 1, one_pos,
      by linarith [Real.pi_gt_three], rfl⟩)
  · rw [csSup_of_not_bddAbove h, Real.sSup_empty]

/-- `supAbsO` is monotone in the function, on the honest class (boundedness of the larger
function; without it `supAbsO` is Lean's junk value `0`). -/
theorem supAbsO_mono {f g : ℝ → ℝ → ℝ}
    (hb : BddAbove {y : ℝ | ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, 0 < θ ∧ θ < π / 2 ∧ y = |g z θ|})
    (hle : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ |g z θ|) :
    Work.FTS.H2.supAbsO f ≤ Work.FTS.H2.supAbsO g := by
  rw [Work.FTS.H2.supAbsO, Work.FTS.H2.supAbsO]
  refine csSup_le ⟨|f 1 1|, 1, one_pos, 1, one_pos, by linarith [Real.pi_gt_three], rfl⟩ ?_
  rintro y ⟨z, hz, θ, hθ, hθ', rfl⟩
  exact le_trans (hle z θ hz hθ hθ') (le_csSup hb ⟨z, hz, θ, hθ, hθ', rfl⟩)

/-- The boundedness of `supAbsO`'s defining set, from a uniform pointwise bound. -/
theorem bddAbove_supAbsO {g : ℝ → ℝ → ℝ} {C : ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |g z θ| ≤ C) :
    BddAbove {y : ℝ | ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, 0 < θ ∧ θ < π / 2 ∧ y = |g z θ|} :=
  ⟨C, by rintro y ⟨z, hz, θ, hθ, hθ', rfl⟩; exact h z θ hz hθ hθ'⟩

/-- `CoefTh` is a sum of `supAbsO`s, hence nonnegative. -/
theorem CoefTh_nonneg (l : ℕ) (f : Fn) : 0 ≤ CoefTh l f := by
  classical
  rw [CoefTh]
  refine Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun i _ => ?_
  split_ifs with hbi
  · exact supAbsO_nonneg _
  · exact le_rfl

/-! ## The `D`-sup norms `WDp`/`WDMem` -/

theorem WDMem_mono {l l' : ℕ} {f : Fn} (h : WDMem l f) (hll : l' ≤ l) : WDMem l' f :=
  fun b j hbj => h b j (le_trans hbj hll)

/-- `WDp l f` is nonnegative. -/
theorem WDp_nonneg (l : ℕ) (f : Fn) : 0 ≤ WDp l f := by
  classical
  rw [WDp]
  refine Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun j _ => ?_
  split_ifs with hbj
  · exact supAbsO_nonneg _
  · exact le_rfl

/-- `WDp` is monotone in the function, under the honesty of both. -/
theorem WDp_mono {l : ℕ} {f g : Fn} (hf : WDMem l f) (hg : WDMem l g)
    (hle : ∀ b j : ℕ, b + j ≤ l → ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b j f z θ| ≤ |Work.Spaces.mixed b j g z θ|) :
    WDp l f ≤ WDp l g := by
  classical
  rw [WDp, WDp]
  refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun j _ => ?_
  split_ifs with hbj
  · refine supAbsO_mono ?_ (fun z θ hz hθ hθ' => hle b j hbj z θ hz hθ hθ')
    obtain ⟨K, hK⟩ := hg b j hbj
    exact bddAbove_supAbsO (fun z θ hz hθ hθ' => hK z θ hz hθ hθ')
  · exact le_rfl

/-- A `WDp`-bound is a `WDMem`-bound, on the honest class (the direction the interfaces use). -/
theorem WDMem_of_WDp_le {l : ℕ} {f : Fn} {C : ℝ} (hf : WDMem l f) (h : WDp l f ≤ C) :
    ∀ b j : ℕ, b + j ≤ l → ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b j f z θ| ≤ C := by
  classical
  intro b j hbj z θ hz hθ0 hθ1
  obtain ⟨K, hK⟩ := hf b j hbj
  have hbdd : BddAbove {y : ℝ | ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, 0 < θ ∧ θ < π / 2
      ∧ y = |Work.Spaces.mixed b j f z θ|} :=
    ⟨K, by rintro y ⟨z', hz', θ', hθ', hθ'', rfl⟩; exact hK z' θ' hz' hθ' hθ''⟩
  have h1 : |Work.Spaces.mixed b j f z θ| ≤ Work.FTS.H2.supAbsO (Work.Spaces.mixed b j f) :=
    le_csSup hbdd ⟨z, hz, θ, hθ0, hθ1, rfl⟩
  have h2 : Work.FTS.H2.supAbsO (Work.Spaces.mixed b j f) ≤ WDp l f := by
    have hb' : b ∈ Finset.range (l + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (by omega))
    have hj' : j ∈ Finset.range (l + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (by omega))
    have hnn : ∀ a c : ℕ, 0 ≤ (if a + c ≤ l then
        Work.FTS.H2.supAbsO (Work.Spaces.mixed a c f) else 0) := fun a c => by
      split_ifs with h
      · exact supAbsO_nonneg _
      · exact le_rfl
    have hinner : (if b + j ≤ l then Work.FTS.H2.supAbsO (Work.Spaces.mixed b j f) else 0)
        ≤ ∑ j' ∈ Finset.range (l + 1),
            (if b + j' ≤ l then Work.FTS.H2.supAbsO (Work.Spaces.mixed b j' f) else 0) :=
      Finset.single_le_sum (f := fun j' => if b + j' ≤ l then
        Work.FTS.H2.supAbsO (Work.Spaces.mixed b j' f) else 0) (fun j' _ => hnn b j') hj'
    have houter : (∑ j' ∈ Finset.range (l + 1),
          (if b + j' ≤ l then Work.FTS.H2.supAbsO (Work.Spaces.mixed b j' f) else 0))
        ≤ ∑ b' ∈ Finset.range (l + 1), ∑ j' ∈ Finset.range (l + 1),
            (if b' + j' ≤ l then Work.FTS.H2.supAbsO (Work.Spaces.mixed b' j' f) else 0) :=
      Finset.single_le_sum (f := fun b' => ∑ j' ∈ Finset.range (l + 1),
          (if b' + j' ≤ l then Work.FTS.H2.supAbsO (Work.Spaces.mixed b' j' f) else 0))
        (fun b' _ => Finset.sum_nonneg fun j' _ => hnn b' j') hb'
    have h := le_trans hinner houter
    rw [ite_eq_left hbj] at h
    simpa only [WDp] using h
  linarith

end Work.FTS.OpenPkg
