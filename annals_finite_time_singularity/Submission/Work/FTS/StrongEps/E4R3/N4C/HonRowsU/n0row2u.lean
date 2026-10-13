import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.E4R3.N4C.Defs
import Submission.Work.FTS.NonlinRows.NRow2
import Submission.Work.FTS.StrongEps.E4R3.NRow2_honest_Aux
import Submission.Work.FTS.StrongEps.E4R3.L12_sq_le_growth_honest
import Submission.Work.FTS.StrongEps.E4R3.L12_dzdIter_moment_honest
import Submission.Work.FTS.StrongEps.E4R3.Qang_sq_le_const_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- Uniform-in-`Cs`, `Ce` restatement of `Work.FTS.StrongEps.E4R3.N4C.HonRows.n0row2`.
-- The two binders `Cs`, `Ce` are moved from the theorem's argument list into the inner
-- `forall`, so that the constant `K` does not depend on them (the target `rowsN0T`
-- quantifies `{Cs Ce}` *after* the `exists K`).  The proof script is unchanged.

namespace Work.FTS.StrongEps.E4R3.N4C.HonRowsU

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open MeasureTheory

/-- **Honest row 2 of the §8 table.**  `N₀₃ = (1/α)L₁₂(g)·g` is `ℋ⁴`-honest and
`Xn α (N₀₃) ≤ K α^{-1} (Xn α g)²`, in the *honest* (open-quadrant) class of the route:
`SmoothOpen g`, `HkMem α 4 g`, `HkMem α 5 g`, `L₁₂(g)(0) = 0`, `DecayAll 4 g`.

This is the open-quadrant port of `Work.FTS.NonlinRows.NRow2`: the growth and moment bounds on
`L₁₂(g)` come from the honest lemmas `L12_sq_le_growth_honest` / `L12_dzdIter_moment_honest`,
the angular-moment bound from `Qang_sq_le_const_open`, and the radial Leibniz rule from
`radial_leibniz_open`. -/
theorem n0row2u (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Cs Ce α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      Work.Spaces.HkMem α 5 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.DecayAll 4 g →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N03g α g) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N03g α g)
          ≤ K * (α ^ (-(1 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
  set K1 : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 with hK1def
  set Kc : ℝ := max (K1 / 3) K1 + 1 with hKcdef
  have hK1nn : 0 ≤ K1 := by
    rw [hK1def]; exact MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  have hKcpos : 0 < Kc := by rw [hKcdef]; positivity
  refine ⟨Real.sqrt (200000 * Kc) + 1, by positivity, ?_⟩
  intro Cs Ce α g Φs Φg hα hα1 hαα₂ hsm hmem hmem5 h0 hdecay hs hell
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hhqo : Work.FTS.VocabO.HQo α 4 g := ⟨hsm, hmem⟩
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hHk : Work.Spaces.HkSq α 4 g = (Work.FTS.Nonlin.Xn α g) ^ 2 :=
    (Real.sq_sqrt (Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 g)).symm
  obtain ⟨hmom, hdiff⟩ :=
    Work.FTS.StrongEps.E4R3.L12_dzdIter_moment_honest α hα hα1 hsm hmem h0
  -- the uniform bound on the iterates of `L₁₂(g)`
  have hgrowth := Work.FTS.StrongEps.E4R3.L12_sq_le_growth_honest α hα hα1 hsm hmem h0
  have hCg1 : ∀ z : ℝ, 0 < z → (Work.Construction.L12 g z) ^ 2
      ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 * z ^ 3 := by
    intro z hz
    have h := hgrowth.1 z hz
    rw [show (max ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) / 3)
          (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1) = Kc from by
      rw [hKcdef, hK1def]] at h
    exact h
  have hCg2 : ∀ z : ℝ, 0 < z → (Work.Construction.L12 g z) ^ 2
      ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 / z := by
    intro z hz
    have h := hgrowth.2 z hz
    rw [show (max ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) / 3)
          (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1) = Kc from by
      rw [hKcdef, hK1def]] at h
    exact h
  have hb1 : ∀ b : ℕ, 1 ≤ b → b ≤ 4 → ∀ z : ℝ, 0 < z →
      (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z) ^ 2
        ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
    intro b hb1 hb4 z hz
    have hq := Work.FTS.StrongEps.E4R3.Qang_sq_le_const_open hα hα1 hsm hmem
      (i := b - 1) (by omega) hz
    have h1 : Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z
        = - Work.Elliptic.Qang g (b - 1) z := by
      have h := hmom (b - 1) (by omega) z hz
      rwa [show b - 1 + 1 = b from by omega] at h
    rw [h1, neg_sq]
    calc (Work.Elliptic.Qang g (b - 1) z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkSq α 4 g := hq
      _ = K1 * (Work.FTS.Nonlin.Xn α g) ^ 2 := by rw [← hK1def, hHk]
      _ ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 :=
          mul_le_mul_of_nonneg_right (by
            rw [hKcdef]
            exact le_trans (le_max_right _ _) (le_add_of_nonneg_right zero_le_one))
            (sq_nonneg _)
  have hb0 : ∀ z : ℝ, 0 < z → (Work.Construction.L12 g z) ^ 2
      ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
    intro z hz
    have hKX : 0 ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 :=
      mul_nonneg hKcpos.le (sq_nonneg _)
    by_cases h1 : z ≤ 1
    · refine (hCg1 z hz).trans ?_
      have hz3 : z ^ 3 ≤ 1 := by
        calc z ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ hz.le h1 3
          _ = 1 := by norm_num
      calc Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 * z ^ 3
          ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hz3 hKX
        _ = Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
    · refine (hCg2 z hz).trans ?_
      have hz1 : 1 / z ≤ 1 := by
        rw [div_le_one hz]
        linarith
      have h2 : Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 / z
          = (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * (1 / z) := by
        rw [div_eq_mul_one_div]
      calc Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 / z
          = (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * (1 / z) := h2
        _ ≤ (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left hz1 hKX
        _ = Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
  have hx : ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 < z →
      (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z) ^ 2
        ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
    intro b hb z hz
    rcases Nat.eq_zero_or_pos b with h | h
    · subst h
      rw [Work.Elliptic.DzdIter_zero]
      exact hb0 z hz
    · exact hb1 b h (by omega) z hz
  -- the pointwise Leibniz rules
  have hleib : ∀ i : ℕ, i ≤ 4 → ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.DzIter i (fun z θ => Work.Construction.L12 g z * g z θ) z θ
        = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z
              * Work.Spaces.DzIter (i - b) g z θ) := by
    intro i hi z θ hz hθ
    rw [← Work.Spaces.mixed_zero_right i
      (fun z θ => Work.Construction.L12 g z * g z θ)]
    exact Work.FTS.StrongEps.E4R3.radial_leibniz_open (fun z => Work.Construction.L12 g z) g
      i 0 (by omega) hz hθ hsm
      (fun b hb z' hz' => hdiff b (by omega) z' hz')
  have hleibm : ∀ j i : ℕ, i ≤ 4 → j ≤ 4 → ∀ z θ : ℝ, 0 < z →
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.mixed j i (fun z θ => Work.Construction.L12 g z * g z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z
              * Work.Spaces.mixed (j - b) i g z θ) :=
    fun j i _ hj z θ hz hθ =>
      Work.FTS.StrongEps.E4R3.radial_leibniz_open (fun z => Work.Construction.L12 g z) g
        j i hj hz hθ hsm (fun b hb z' hz' => hdiff b (by omega) z' hz')
  -- the pointwise bound on the `ℋ⁴`-integrand
  have hbin : ∀ i ≤ 4, ∀ b ∈ Finset.range (i + 1), ((i.choose b : ℕ) : ℝ) ≤ 16 :=
    fun i hi b _ => Work.FTS.Nonlinear.RadialProd.choose_le_sixteen hi
  have hpt : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 4 (fun z θ => Work.Construction.L12 g z * g z θ) z θ
        ≤ 200000 * Kc * (Work.FTS.Nonlin.Xn α g) ^ 2
          * Work.Spaces.HkIntegrand α 4 g z θ := by
    intro z θ hz hθ
    have hX2 : 0 ≤ (Work.FTS.Nonlin.Xn α g) ^ 2 := sq_nonneg _
    have hK2nn : 0 ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := mul_nonneg hKcpos.le hX2
    set B : ℝ := Work.Spaces.HkIntegrand α 4 g z θ with hBdef
    have hBnn : 0 ≤ B := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
    have hpure : ∀ i ∈ Finset.range 5,
        (Work.Spaces.DzIter i (fun z θ => Work.Construction.L12 g z * g z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ 6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B := by
      intro i hi
      have hi4 : i ≤ 4 := by have := Finset.mem_range.mp hi; omega
      rw [hleib i hi4 z θ hz hθ,
        show (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
              * (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z
                * Work.Spaces.DzIter (i - b) g z θ))
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
          = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
              * (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z
                * (Work.Spaces.DzIter (i - b) g z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) from by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun b _ => by ring]
      have hCS := Work.FTS.StrongEps.E4R3.slot_sum_sq_le (Finset.range (i + 1))
        (fun b => (i.choose b : ℝ))
        (fun b => Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z)
        (fun b => Work.Spaces.DzIter (i - b) g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
        (Kc := Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) hK2nn
        (fun b hb => by
          rw [abs_of_nonneg (Nat.cast_nonneg _)]
          exact hbin i hi4 b hb)
        (fun b hb => hx b (by have := Finset.mem_range.mp hb; omega) z hz)
      have hy : ∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 ≤ 5 * B := by
        have h1 : ∀ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 ≤ B := by
          intro b hb
          have hb4 : i - b ≤ 4 := by have := Finset.mem_range.mp hb; omega
          exact Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ (i - b) hb4
        calc ∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            ≤ ∑ _b ∈ Finset.range (i + 1), B := Finset.sum_le_sum h1
          _ = ((i + 1 : ℕ) : ℝ) * B := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          _ ≤ 5 * B := by
              have hi5 : i + 1 ≤ 5 := by have := Finset.mem_range.mp hi; omega
              have hc : ((i + 1 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast hi5
              exact mul_le_mul_of_nonneg_right hc hBnn
      have hcard : ((Finset.range (i + 1)).card : ℝ) ≤ 5 := by
        rw [Finset.card_range]
        have hi5 : i + 1 ≤ 5 := by have := Finset.mem_range.mp hi; omega
        exact_mod_cast hi5
      have hA : 256 * ((Finset.range (i + 1)).card : ℝ) ≤ 256 * 5 :=
        mul_le_mul_of_nonneg_left hcard (by norm_num)
      have hC : (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
            * (∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * (5 * B) :=
        mul_le_mul_of_nonneg_left hy hK2nn
      have hS0 : 0 ≤ ∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
        Finset.sum_nonneg fun b _ => sq_nonneg _
      refine hCS.trans ?_
      have h1 := mul_le_mul hA hC (mul_nonneg hK2nn hS0) (by norm_num : (0 : ℝ) ≤ 256 * 5)
      have h2 : (256 * ((Finset.range (i + 1)).card : ℝ))
            * ((Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
              * (∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
          = 256 * ((Finset.range (i + 1)).card : ℝ) * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
            * (∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by ring
      have h3 : (256 * 5) * ((Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * (5 * B))
          = 6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B := by ring
      rw [h2, h3] at h1
      exact h1
    have hmix : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => Work.Construction.L12 g z * g z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ 6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B := by
      intro i hi j hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ 4
      · rw [if_pos hc]
        have hj4 : j ≤ 4 := by have := Finset.mem_range.mp hj; omega
        rw [hleibm j i (by omega) hj4 z θ hz hθ,
          show (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
                * (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z
                  * Work.Spaces.mixed (j - b) i g z θ)) * Work.Spaces.Wt α z θ
            = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
                * (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z
                  * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ)) from by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun b _ => by ring]
        have hCS := Work.FTS.StrongEps.E4R3.slot_sum_sq_le (Finset.range (j + 1))
          (fun b => (j.choose b : ℝ))
          (fun b => Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z)
          (fun b => Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ)
          (Kc := Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) hK2nn
          (fun b hb => by
            rw [abs_of_nonneg (Nat.cast_nonneg _)]
            exact hbin j hj4 b hb)
          (fun b hb => hx b (by have := Finset.mem_range.mp hb; omega) z hz)
        have hy : ∑ b ∈ Finset.range (j + 1), (Work.Spaces.mixed (j - b) i g z θ
              * Work.Spaces.Wt α z θ) ^ 2 ≤ 5 * B := by
          have h1 : ∀ b ∈ Finset.range (j + 1), (Work.Spaces.mixed (j - b) i g z θ
                * Work.Spaces.Wt α z θ) ^ 2 ≤ B := by
            intro b hb
            have hb4 : i + (j - b) ≤ 4 := by have := Finset.mem_range.mp hb; omega
            exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ i (j - b) hc.1 hb4
          calc ∑ b ∈ Finset.range (j + 1), (Work.Spaces.mixed (j - b) i g z θ
                * Work.Spaces.Wt α z θ) ^ 2
              ≤ ∑ _b ∈ Finset.range (j + 1), B := Finset.sum_le_sum h1
            _ = ((j + 1 : ℕ) : ℝ) * B := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            _ ≤ 5 * B := by
                have hj5 : j + 1 ≤ 5 := by have := Finset.mem_range.mp hj; omega
                have hc5 : ((j + 1 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast hj5
                exact mul_le_mul_of_nonneg_right hc5 hBnn
        have hcard : ((Finset.range (j + 1)).card : ℝ) ≤ 5 := by
          rw [Finset.card_range]
          have hj5 : j + 1 ≤ 5 := by have := Finset.mem_range.mp hj; omega
          exact_mod_cast hj5
        have hA : 256 * ((Finset.range (j + 1)).card : ℝ) ≤ 256 * 5 :=
          mul_le_mul_of_nonneg_left hcard (by norm_num)
        have hC : (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
              * (∑ b ∈ Finset.range (j + 1), (Work.Spaces.mixed (j - b) i g z θ
                * Work.Spaces.Wt α z θ) ^ 2)
            ≤ (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * (5 * B) :=
          mul_le_mul_of_nonneg_left hy hK2nn
        have hS0 : 0 ≤ ∑ b ∈ Finset.range (j + 1), (Work.Spaces.mixed (j - b) i g z θ
              * Work.Spaces.Wt α z θ) ^ 2 := Finset.sum_nonneg fun b _ => sq_nonneg _
        refine hCS.trans ?_
        have h1 := mul_le_mul hA hC (mul_nonneg hK2nn hS0) (by norm_num : (0 : ℝ) ≤ 256 * 5)
        have h2 : (256 * ((Finset.range (j + 1)).card : ℝ))
              * ((Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
                * (∑ b ∈ Finset.range (j + 1), (Work.Spaces.mixed (j - b) i g z θ
                  * Work.Spaces.Wt α z θ) ^ 2))
            = 256 * ((Finset.range (j + 1)).card : ℝ) * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
              * (∑ b ∈ Finset.range (j + 1), (Work.Spaces.mixed (j - b) i g z θ
                * Work.Spaces.Wt α z θ) ^ 2) := by ring
        have h3 : (256 * 5) * ((Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * (5 * B))
            = 6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B := by ring
        rw [h2, h3] at h1
        exact h1
      · rw [if_neg hc]
        exact mul_nonneg (by positivity) hBnn
    rw [Work.Spaces.HkIntegrand]
    have hsum1 : (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i
          (fun z θ => Work.Construction.L12 g z * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ 5 * (6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B) := by
      calc (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i
            (fun z θ => Work.Construction.L12 g z * g z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ ∑ _i ∈ Finset.range 5, 6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B :=
            Finset.sum_le_sum fun i hi => hpure i hi
        _ = 5 * (6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            norm_num
    have hsum2 : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => Work.Construction.L12 g z * g z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ 25 * (6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B) := by
      calc (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (fun z θ => Work.Construction.L12 g z * g z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ ∑ _i ∈ Finset.range 5, ∑ _j ∈ Finset.range 5,
              6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B :=
            Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hmix i hi j hj
        _ = 25 * (6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
    refine (add_le_add hsum1 hsum2).trans ?_
    have h3 : 5 * (6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B)
        + 25 * (6400 * (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * B)
        ≤ 200000 * Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 * B := by
      nlinarith [hBnn, hK2nn]
    exact h3
  -- integration
  have hptint : Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.L12 g z * g z θ)
      ≤ (200000 * Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * Work.Spaces.HkSq α 4 g := by
    rw [Work.Spaces.HkSq]
    have hEq : (∫ z in Work.Spaces.Iz, (200000 * Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))
        = (200000 * Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * Work.Spaces.HkSq α 4 g := by
      rw [MeasureTheory.integral_const_mul]
      rfl
    rw [← hEq]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z =>
        MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)
      (hmem.2.const_mul _) ?_
    have hmeas : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
        = MeasureTheory.volume.restrict Work.Spaces.Iz :=
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))
    rw [← hmeas]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    change (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 (fun z θ => Work.Construction.L12 g z * g z θ) z θ)
        ≤ (200000 * Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
          * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ
    rw [show (200000 * Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        = ∫ θ in Work.Spaces.Iθ, (200000 * Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
            * Work.Spaces.HkIntegrand α 4 g z θ from
      (MeasureTheory.integral_const_mul _ _).symm]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)
      ((hmem.1 z (by simp only [Work.Spaces.Iz, Set.mem_Ici]; exact le_of_lt hz)).const_mul _) ?_
    filter_upwards [Work.H2.T1Q.ae_mem_Ioo_Iθ] with θ hθ
    exact (hpt z θ hz hθ).trans (le_of_eq (by ring))
  have hXn : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z * g z θ)
      ≤ Real.sqrt (200000 * Kc) * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
    have h := hptint
    rw [hHk] at h
    calc Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z * g z θ)
        = Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.L12 g z * g z θ)) := rfl
      _ ≤ Real.sqrt ((200000 * Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
            * (Work.FTS.Nonlin.Xn α g) ^ 2) := Real.sqrt_le_sqrt h
      _ = Real.sqrt (200000 * Kc) * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
          have h1 : (200000 * Kc * (Work.FTS.Nonlin.Xn α g) ^ 2)
                * (Work.FTS.Nonlin.Xn α g) ^ 2
              = (200000 * Kc) * ((Work.FTS.Nonlin.Xn α g) ^ 2
                  * (Work.FTS.Nonlin.Xn α g) ^ 2) := by ring
          rw [h1, Real.sqrt_mul (by positivity)]
          congr 1
          rw [show (Work.FTS.Nonlin.Xn α g) ^ 2 * (Work.FTS.Nonlin.Xn α g) ^ 2
              = ((Work.FTS.Nonlin.Xn α g) ^ 2) ^ 2 from by ring,
            Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hfun : Work.FTS.Nonlin.N03g α g
      = fun z θ => (1 / α) * (Work.Construction.L12 g z * g z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N03g, Work.Construction.N03]
    ring
  -- the `ℋ⁴`-honesty of `N₀₃`: the primed product rule applied to the radial factor `L₁₂(g)`
  -- and `g`, then the constant `1/α` pulled out.
  have hL12pkg := hN.l12H α hIoc g hhqo h0
  have hL12sm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 g z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα hell.smooth hell.V.1.1
  have hprod := hN.prod α hIoc (fun z _ => Work.Construction.L12 g z) g
    ⟨hL12sm, hL12pkg.1⟩ hhqo
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (1 / α) hprod.1
  · rw [hfun, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / α)]
    calc (1 / α) * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z * g z θ)
        ≤ (1 / α) * (Real.sqrt (200000 * Kc) * (Work.FTS.Nonlin.Xn α g) ^ 2) :=
          mul_le_mul_of_nonneg_left hXn (by positivity)
      _ ≤ (Real.sqrt (200000 * Kc) + 1)
            * (α ^ (-(1 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
          rw [Real.rpow_neg_one, inv_eq_one_div]
          have h1 : (0 : ℝ) ≤ (1 / α) * (Work.FTS.Nonlin.Xn α g) ^ 2 := by positivity
          have h2 : Real.sqrt (200000 * Kc) ≤ Real.sqrt (200000 * Kc) + 1 := by linarith
          nlinarith [mul_le_mul_of_nonneg_right h2 h1]

end Work.FTS.StrongEps.E4R3.N4C.HonRowsU
