/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS.StrongPersist.L3Rhs.L3MulDthAux.MslotPt`

The mixed slots of the `ℋ³`-integrand of `h · D_θ f`, priced by `|h|²_{𝒲^{4,∞}}`:

```
∃ C > 0, ∀ α ∈ (0,1], SmoothOpen h → WlInfMem α 4 h → SmoothOpen f → HkMem α 4 f →
  ∀ i, j, 1 ≤ i → i + j ≤ 3, ∀ z > 0, ∀ θ ∈ (0,π/2),
    (D_z^jD_θ^i (h·D_θ f)(z,θ) · W(z,θ))² ≤ C · |h|²_{𝒲^{4,∞}} · HkIntegrand α 4 f z θ
```

Route: the open-quadrant two-operator Leibniz rule `leibniz_open_mixed` expands the slot as
`Σ_{a≤i, b≤j} C(i,a)C(j,b) · D_z^bD_θ^a h · D_z^{j-b}D_θ^i(D_θ f)`, and
`D_z^{j-b}D_θ^i(D_θ f) = D_z^{j-b}D_θ^{i-a+1} f` (`mixed_Dth_shift`) is a mixed slot of `f` of
total order `(i-a+1)+(j-b) ≤ i+j+1 ≤ 4`, with `θ`-order `i-a+1 ≥ 1`.  Cauchy–Schwarz twice, the
binomial bounds `choose_sq_le_256`, the coefficient bound `|D_z^bD_θ^a h| ≤ 200|h|_𝒲`
(`abs_mixed_le_WlInf_open`) and `sq_le_HkIntegrand_mixed`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.OpenPkg.Mixed_le_WlInf_open
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.FTS.TransportS.GoodOpenBase
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.L3Rhs.L3MulDthAux.ZslotPt

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

/-- **The mixed slots.**  For `1 ≤ i`, `i + j ≤ 3` the `(j,i)`-slot of the `ℋ³`-integrand of
`h·D_θ f` is dominated by `|h|²_𝒲 · HkIntegrand α 4 f`. -/
theorem mslot_le_pt : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (h f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ i j : ℕ, 1 ≤ i → i + j ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.mixed j i (fun z θ => h z θ * Work.Spaces.Dth f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2
          ≤ C * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
  refine ⟨10 ^ 12, by norm_num, ?_⟩
  intro α h f hα hα1 hh hhm hf _hfm i j hi hij z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hW : 0 ≤ Work.Spaces.WlInf α 4 h := Work.Spaces.WlInf_nonneg α 4 h hhm
  have hHInn : 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have hjk : j ≤ 3 := by omega
  have heq := Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed j i h (Work.Spaces.Dth f) hh hf.Dth
    z θ hz hθ0 hθ1
  have hexp : Work.Spaces.mixed j i (fun z θ => h z θ * Work.Spaces.Dth f z θ) z θ
      = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a h z θ
              * Work.Spaces.mixed (j - b) (i - a + 1) f z θ) := by
    rw [heq]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mixed_Dth_shift]
  have hsplit : (Work.Spaces.mixed j i (fun z θ => h z θ * Work.Spaces.Dth f z θ) z θ
        * Work.Spaces.Wt α z θ) ^ 2
      = (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a h z θ
              * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ * Work.Spaces.Wt α z θ))) ^ 2 := by
    rw [hexp, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hsplit]
  have hterm : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
      (((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a h z θ
              * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ * Work.Spaces.Wt α z θ))) ^ 2
        ≤ 2621440000 * ((Work.Spaces.WlInf α 4 h) ^ 2
            * Work.Spaces.HkIntegrand α 4 f z θ) := by
    intro a ha b hb
    have hai : a ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hch1 : ((i.choose a : ℝ)) ^ 2 ≤ 256 := Work.Spaces.choose_sq_le_256 i a hai (by omega)
    have hch2 : ((j.choose b : ℝ)) ^ 2 ≤ 256 := Work.Spaces.choose_sq_le_256 j b hbj (by omega)
    have hab4 : a + b ≤ 4 := by omega
    have hDh : |Work.Spaces.mixed b a h z θ| ≤ 200 * Work.Spaces.WlInf α 4 h :=
      Work.FTS.TransportS.abs_mixed_le_WlInf_open hα hα1 hh hhm hab4 hz hθ
    have hx : (Work.Spaces.mixed b a h z θ) ^ 2
        ≤ (200 * Work.Spaces.WlInf α 4 h) ^ 2 := by
      have hB : (0 : ℝ) ≤ 200 * Work.Spaces.WlInf α 4 h := mul_nonneg (by norm_num) hW
      have h1 := (abs_le.mp hDh).1
      have h2 := (abs_le.mp hDh).2
      nlinarith [hB, h1, h2]
    have hmix : (Work.Spaces.mixed (j - b) (i - a + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ (i - a + 1) (j - b) (by omega) (by omega)
    calc (((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Work.Spaces.mixed b a h z θ
            * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ * Work.Spaces.Wt α z θ))) ^ 2
        = ((i.choose a : ℝ)) ^ 2 * ((j.choose b : ℝ)) ^ 2
            * (Work.Spaces.mixed b a h z θ) ^ 2
            * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          ring
      _ ≤ 256 * 256 * (200 * Work.Spaces.WlInf α 4 h) ^ 2
            * Work.Spaces.HkIntegrand α 4 f z θ := by
          gcongr
      _ = 2621440000 * ((Work.Spaces.WlInf α 4 h) ^ 2
            * Work.Spaces.HkIntegrand α 4 f z θ) := by ring
  have hinner : ∀ a ∈ Finset.range (i + 1),
      (∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a h z θ
              * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ
                * Work.Spaces.Wt α z θ))) ^ 2
        ≤ ((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1),
            (((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a h z θ
                * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ
                  * Work.Spaces.Wt α z θ))) ^ 2 := by
    intro a _
    have hs := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1))
      (f := fun b => ((i.choose a : ℝ) * (j.choose b : ℝ))
        * (Work.Spaces.mixed b a h z θ
          * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ * Work.Spaces.Wt α z θ)))
    have hc : (((Finset.range (j + 1)).card : ℕ) : ℝ) = (j : ℝ) + 1 := by
      rw [Finset.card_range]; push_cast; ring
    rwa [hc] at hs
  have hbnd : ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        (((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Work.Spaces.mixed b a h z θ
            * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ * Work.Spaces.Wt α z θ))) ^ 2
      ≤ ((i : ℝ) + 1) * ((j : ℝ) + 1)
          * (2621440000 * ((Work.Spaces.WlInf α 4 h) ^ 2
              * Work.Spaces.HkIntegrand α 4 f z θ)) := by
    calc ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          (((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a h z θ
              * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ * Work.Spaces.Wt α z θ))) ^ 2
        ≤ ∑ _a ∈ Finset.range (i + 1), ∑ _b ∈ Finset.range (j + 1),
            (2621440000 * ((Work.Spaces.WlInf α 4 h) ^ 2
              * Work.Spaces.HkIntegrand α 4 f z θ)) :=
          Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hterm a ha b hb
      _ = ((i : ℝ) + 1) * ((j : ℝ) + 1)
            * (2621440000 * ((Work.Spaces.WlInf α 4 h) ^ 2
                * Work.Spaces.HkIntegrand α 4 f z θ)) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; ring
  calc (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a h z θ
              * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ * Work.Spaces.Wt α z θ))) ^ 2
      ≤ ((i : ℝ) + 1) * ∑ a ∈ Finset.range (i + 1),
          (∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a h z θ
                * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ
                  * Work.Spaces.Wt α z θ))) ^ 2 := by
        have hs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
          (f := fun a => ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a h z θ
                * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ
                  * Work.Spaces.Wt α z θ)))
        have hc : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
          rw [Finset.card_range]; push_cast; ring
        rwa [hc] at hs
    _ ≤ ((i : ℝ) + 1) * ∑ a ∈ Finset.range (i + 1),
          (((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1),
            (((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a h z θ
                * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ
                  * Work.Spaces.Wt α z θ))) ^ 2) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a ha => hinner a ha)
          (by positivity)
    _ = ((i : ℝ) + 1) * ((j : ℝ) + 1)
          * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a h z θ
                * (Work.Spaces.mixed (j - b) (i - a + 1) f z θ
                  * Work.Spaces.Wt α z θ))) ^ 2 := by
        rw [← Finset.mul_sum]; ring
    _ ≤ ((i : ℝ) + 1) * ((j : ℝ) + 1)
          * (((i : ℝ) + 1) * ((j : ℝ) + 1)
              * (2621440000 * ((Work.Spaces.WlInf α 4 h) ^ 2
                  * Work.Spaces.HkIntegrand α 4 f z θ))) :=
        mul_le_mul_of_nonneg_left hbnd (by positivity)
    _ ≤ 10 ^ 12 * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
        have htarget : (10 : ℝ) ^ 12 * (Work.Spaces.WlInf α 4 h) ^ 2
              * Work.Spaces.HkIntegrand α 4 f z θ
            = 10 ^ 12 * ((Work.Spaces.WlInf α 4 h) ^ 2
                * Work.Spaces.HkIntegrand α 4 f z θ) := by ring
        rw [htarget]
        have hxnn : (0 : ℝ) ≤ ((i : ℝ) + 1) * ((j : ℝ) + 1) := by positivity
        have h16 : ((i : ℝ) + 1) * ((j : ℝ) + 1) ≤ 16 := by
          have h1 : i + 1 ≤ 4 := by omega
          have h2 : j + 1 ≤ 4 := by omega
          have hnat : (i + 1) * (j + 1) ≤ 16 :=
            calc (i + 1) * (j + 1) ≤ 4 * 4 := Nat.mul_le_mul h1 h2
              _ = 16 := by norm_num
          have hcast : (((i + 1) * (j + 1) : ℕ) : ℝ) ≤ 16 := by exact_mod_cast hnat
          have h := hcast
          push_cast at h
          exact h
        have hsq256 : (((i : ℝ) + 1) * ((j : ℝ) + 1)) ^ 2 ≤ 256 := by
          have h := pow_le_pow_left₀ hxnn h16 2
          norm_num at h
          exact h
        have hbase : 0 ≤ (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ :=
          mul_nonneg (sq_nonneg _) hHInn
        have hkey : ((i : ℝ) + 1) * ((j : ℝ) + 1)
              * (((i : ℝ) + 1) * ((j : ℝ) + 1)
                * (2621440000 * ((Work.Spaces.WlInf α 4 h) ^ 2
                    * Work.Spaces.HkIntegrand α 4 f z θ)))
            = (2621440000 * (((i : ℝ) + 1) * ((j : ℝ) + 1)) ^ 2)
              * ((Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by ring
        rw [hkey]
        refine mul_le_mul_of_nonneg_right ?_ hbase
        calc 2621440000 * (((i : ℝ) + 1) * ((j : ℝ) + 1)) ^ 2
            ≤ 2621440000 * 256 := mul_le_mul_of_nonneg_left hsq256 (by norm_num)
          _ ≤ 10 ^ 12 := by norm_num

end Work.FTS.StrongPersist.L3Rhs
