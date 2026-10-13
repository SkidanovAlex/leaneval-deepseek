/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS.StrongPersist.L3Rhs.L3MulDthAux.ZslotPt`

The pure `D_z`-slots of the `ℋ³`-integrand of `h · D_θ f`, priced by `|h|²_{𝒲^{4,∞}}`:

```
∃ C > 0, ∀ α ∈ (0,1], SmoothOpen h → WlInfMem α 4 h → SmoothOpen f → HkMem α 4 f →
  ∀ i ≤ 3, ∀ z > 0, ∀ θ ∈ (0,π/2),
    (D_z^i (h·D_θ f)(z,θ) · w(z)/sin(2θ)^{η/2})²
      ≤ C · |h|²_{𝒲^{4,∞}} · HkIntegrand α 4 f z θ
```

Route: the open-quadrant Leibniz rule `leibniz_open_Dz` expands
`D_z^i(h·D_θ f) = Σ_{b≤i} C(i,b) D_z^b h · D_z^{i-b}(D_θ f)`, and
`D_z^{i-b}(D_θ f) = D_z^{i-b}D_θ f` (definitionally) is a mixed slot of `f` of total order
`(i-b)+1 ≤ 4`.  Cauchy–Schwarz on the `i+1` terms, `|D_z^b h| ≤ 100|h|_𝒲`
(`DzIter_le_WlInf_open`), the binomial bound `C(i,b)² ≤ 256` (`choose_sq_le_256`) and the
weight comparison `(w/sin(2θ)^{η/2})² ≤ W²` (`H_le_Wt`) with `sq_le_HkIntegrand_mixed`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.DzIter_le_WlInf_open
import Submission.Work.Spaces.H_le_Wt
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary identifications of iterated `D_θ` -/

/-- `D_θ^n (D_θ f) = D_θ^{n+1} f`. -/
theorem DthIter_Dth (n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter n (Work.Spaces.Dth f) = Work.Spaces.DthIter (n + 1) f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ n (Work.Spaces.Dth f), ih]
      rfl

/-- `D_z^j (D_θ f) = D_z^jD_θ f` (definitional). -/
theorem DzIter_Dth_eq (j : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (Work.Spaces.Dth f) = Work.Spaces.mixed j 1 f := rfl

/-- `D_z^jD_θ^i (D_θ f) = D_z^jD_θ^{i+1} f`. -/
theorem mixed_Dth_shift (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (Work.Spaces.Dth f) = Work.Spaces.mixed j (i + 1) f :=
  congrArg (fun g => Work.Spaces.DzIter j g) (DthIter_Dth i f)

/-! ## The `D_z`-slot bound -/

/-- **The pure `D_z`-slots.**  For `i ≤ 3` the `i`-th radial slot of the `ℋ³`-integrand of
`h·D_θ f` (weighted as in `HkIntegrand`) is dominated by `|h|²_𝒲 · HkIntegrand α 4 f`. -/
theorem zslot_le_pt : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (h f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ i : ℕ, i ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.DzIter i (fun z θ => h z θ * Work.Spaces.Dth f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ C * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
  refine ⟨10 ^ 8, by norm_num, ?_⟩
  intro α h f hα hα1 hh hhm hf _hfm i hi z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hW : 0 ≤ Work.Spaces.WlInf α 4 h := Work.Spaces.WlInf_nonneg α 4 h hhm
  have hHInn : 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  set Hv : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hHv
  have heq := Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz i h (Work.Spaces.Dth f) hh hf.Dth
    z θ hz hθ0 hθ1
  have hsplit : (Work.Spaces.DzIter i (fun z θ => h z θ * Work.Spaces.Dth f z θ) z θ * Hv) ^ 2
      = (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * Work.Spaces.DzIter b h z θ)
            * (Work.Spaces.mixed (i - b) 1 f z θ * Hv)) ^ 2 := by
    rw [heq, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [DzIter_Dth_eq]
    ring
  rw [hsplit]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
    (f := fun b => ((i.choose b : ℝ) * Work.Spaces.DzIter b h z θ)
      * (Work.Spaces.mixed (i - b) 1 f z θ * Hv))
  have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hper : ∀ b ∈ Finset.range (i + 1),
      (((i.choose b : ℝ) * Work.Spaces.DzIter b h z θ)
          * (Work.Spaces.mixed (i - b) 1 f z θ * Hv)) ^ 2
        ≤ 2560000 * (Work.Spaces.WlInf α 4 h) ^ 2
          * (Work.Spaces.mixed (i - b) 1 f z θ * Hv) ^ 2 := by
    intro b hb
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hDh : |Work.Spaces.DzIter b h z θ| ≤ 100 * Work.Spaces.WlInf α 4 h :=
      Work.FTS.OpenPkg.DzIter_le_WlInf_open hh hhm (by omega) hz hθ
    have hx : (Work.Spaces.DzIter b h z θ) ^ 2
        ≤ (100 * Work.Spaces.WlInf α 4 h) ^ 2 := by
      have hB : (0 : ℝ) ≤ 100 * Work.Spaces.WlInf α 4 h := mul_nonneg (by norm_num) hW
      have h1 := (abs_le.mp hDh).1
      have h2 := (abs_le.mp hDh).2
      nlinarith [hB, h1, h2]
    have hch : ((i.choose b : ℝ)) ^ 2 ≤ 256 := Work.Spaces.choose_sq_le_256 i b hbi (by omega)
    calc (((i.choose b : ℝ) * Work.Spaces.DzIter b h z θ)
          * (Work.Spaces.mixed (i - b) 1 f z θ * Hv)) ^ 2
        = ((i.choose b : ℝ)) ^ 2 * (Work.Spaces.DzIter b h z θ) ^ 2
            * (Work.Spaces.mixed (i - b) 1 f z θ * Hv) ^ 2 := by ring
      _ ≤ 256 * (100 * Work.Spaces.WlInf α 4 h) ^ 2
            * (Work.Spaces.mixed (i - b) 1 f z θ * Hv) ^ 2 := by
          refine mul_le_mul (mul_le_mul hch hx (sq_nonneg _) (by norm_num)) le_rfl
            (sq_nonneg _) (by positivity)
      _ = 2560000 * (Work.Spaces.WlInf α 4 h) ^ 2
            * (Work.Spaces.mixed (i - b) 1 f z θ * Hv) ^ 2 := by ring
  have hHvWt : Hv ^ 2 ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
    rw [hHv]; exact Work.Spaces.H_le_Wt α hα z θ hzI hθI
  have hsumsq : ∑ b ∈ Finset.range (i + 1), (Work.Spaces.mixed (i - b) 1 f z θ * Hv) ^ 2
      ≤ ((i : ℝ) + 1) * Work.Spaces.HkIntegrand α 4 f z θ := by
    calc ∑ b ∈ Finset.range (i + 1), (Work.Spaces.mixed (i - b) 1 f z θ * Hv) ^ 2
        ≤ ∑ _b ∈ Finset.range (i + 1), Work.Spaces.HkIntegrand α 4 f z θ := by
          refine Finset.sum_le_sum fun b hb => ?_
          have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
          have hmix : (Work.Spaces.mixed (i - b) 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
              ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
            Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ 1 (i - b) (by norm_num) (by omega)
          calc (Work.Spaces.mixed (i - b) 1 f z θ * Hv) ^ 2
              = (Work.Spaces.mixed (i - b) 1 f z θ) ^ 2 * Hv ^ 2 := by ring
            _ ≤ (Work.Spaces.mixed (i - b) 1 f z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 :=
                mul_le_mul_of_nonneg_left hHvWt (sq_nonneg _)
            _ = (Work.Spaces.mixed (i - b) 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
            _ ≤ Work.Spaces.HkIntegrand α 4 f z θ := hmix
      _ = ((i : ℝ) + 1) * Work.Spaces.HkIntegrand α 4 f z θ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; ring
  calc (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * Work.Spaces.DzIter b h z θ)
            * (Work.Spaces.mixed (i - b) 1 f z θ * Hv)) ^ 2
      ≤ (((Finset.range (i + 1)).card : ℕ) : ℝ) * ∑ b ∈ Finset.range (i + 1),
          (((i.choose b : ℝ) * Work.Spaces.DzIter b h z θ)
            * (Work.Spaces.mixed (i - b) 1 f z θ * Hv)) ^ 2 := hcs
    _ ≤ ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1),
          (2560000 * (Work.Spaces.WlInf α 4 h) ^ 2
            * (Work.Spaces.mixed (i - b) 1 f z θ * Hv) ^ 2) := by
        rw [hcard]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (by positivity)
    _ = 2560000 * (Work.Spaces.WlInf α 4 h) ^ 2 * (((i : ℝ) + 1)
          * ∑ b ∈ Finset.range (i + 1), (Work.Spaces.mixed (i - b) 1 f z θ * Hv) ^ 2) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ 2560000 * (Work.Spaces.WlInf α 4 h) ^ 2
          * (((i : ℝ) + 1) * (((i : ℝ) + 1) * Work.Spaces.HkIntegrand α 4 f z θ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hsumsq (by positivity)
    _ ≤ 10 ^ 8 * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
        have hi16 : ((i : ℝ) + 1) ^ 2 ≤ 16 := by
          have hi3 : (i : ℝ) ≤ 3 := by exact_mod_cast hi
          nlinarith
        have h2nn : 0 ≤ (Work.Spaces.WlInf α 4 h) ^ 2 := sq_nonneg _
        have hkey : 2560000 * (Work.Spaces.WlInf α 4 h) ^ 2
            * (((i : ℝ) + 1) * (((i : ℝ) + 1) * Work.Spaces.HkIntegrand α 4 f z θ))
            = (2560000 * ((i : ℝ) + 1) ^ 2)
              * ((Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by ring
        have hkey2 : (10 : ℝ) ^ 8 * (Work.Spaces.WlInf α 4 h) ^ 2
              * Work.Spaces.HkIntegrand α 4 f z θ
            = 10 ^ 8 * ((Work.Spaces.WlInf α 4 h) ^ 2
                * Work.Spaces.HkIntegrand α 4 f z θ) := by ring
        rw [hkey, hkey2]
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg h2nn hHInn)
        nlinarith [hi16]

end Work.FTS.StrongPersist.L3Rhs
