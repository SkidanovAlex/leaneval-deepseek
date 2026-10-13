/-
Copyright: work module for the Elgindi finite-time singularity project.

# Pointwise level-`6` product bound for `A · D_θ f`

The pointwise master bound behind the level-`6` *shift-product* estimate of the `N`-block:
the level-`6` weighted integrand of `A · D_θ f` is dominated, at every point of the open
quadrant, by

  `K MA² · HkIntegrand α 7 f + K (1 + (γ-1)⁻¹ (HkSq α 6 A + HkSq α 6 f)) · (HkIntegrand α 6 A
   + HkIntegrand α 6 f) + K · (D_z⁵A · D_θ²f · W)²`

with `K` universal.  The proof is a finite Leibniz/Cauchy–Schwarz analysis of the slots of
`HkIntegrand α 6`; the key point is that in every summand of a Leibniz expansion of
`D_z^jD_θ^i(A · D_θ f)` the *total* number of derivatives is at most `7`, so one of the two
factors always has order `≤ 4` and can be priced pointwise by `PwAny6`
(`(D_z^bD_θ^a g)² ≤ CP (γ-1)⁻¹ |g|²_{ℋ⁶}`), while the other one is kept as a slot of the
pointwise integrand; the single term that is priceable neither way is the exceptional pair
`D_z⁵A · D_θ²f`, which is carried symbolically in the RHS (as it must be: it is
functionally independent of the other five budget terms).

The vocabulary (`ptdBud`, `CP`, `ptdK2`) and the two per-summand pricing lemmas live in
`Tools/PtDthDefs.lean` and `Tools/PtDthAux/`.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.StrongEps.H5.LevelShift
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtDthDefs
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtDthAux.summandZ_bound
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtDthAux.summandM_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Nblock6.Tools

open Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

def ptdC1 : ℝ := 2401 * 4096 * ptdK2

theorem ptdC1_pos : 0 < ptdC1 := by
  have h := ptdK2_pos
  rw [ptdC1]; positivity

theorem ptdC1_nonneg : 0 ≤ ptdC1 := le_of_lt ptdC1_pos

/-- `(∑_{a∈s} ∑_{b∈t} G a b)² ≤ s.card · t.card · ∑_{a∈s} ∑_{b∈t} (G a b)²`. -/
theorem sq_sum_sq_le {ι : Type*} (s t : Finset ι) (G : ι → ι → ℝ) :
    (∑ a ∈ s, ∑ b ∈ t, G a b) ^ 2
      ≤ (s.card : ℝ) * (t.card : ℝ) * ∑ a ∈ s, ∑ b ∈ t, (G a b) ^ 2 := by
  have h1 := sq_sum_le_card_mul_sum_sq s (fun a => ∑ b ∈ t, G a b)
  have h2 : ∀ a ∈ s, (∑ b ∈ t, G a b) ^ 2 ≤ (t.card : ℝ) * ∑ b ∈ t, (G a b) ^ 2 :=
    fun a _ => sq_sum_le_card_mul_sum_sq t (fun b => G a b)
  have h3 : ∑ a ∈ s, (∑ b ∈ t, G a b) ^ 2
      ≤ (t.card : ℝ) * ∑ a ∈ s, ∑ b ∈ t, (G a b) ^ 2 := by
    calc ∑ a ∈ s, (∑ b ∈ t, G a b) ^ 2
        ≤ ∑ a ∈ s, ((t.card : ℝ) * ∑ b ∈ t, (G a b) ^ 2) := Finset.sum_le_sum h2
      _ = (t.card : ℝ) * ∑ a ∈ s, ∑ b ∈ t, (G a b) ^ 2 := by rw [Finset.mul_sum]
  calc (∑ a ∈ s, ∑ b ∈ t, G a b) ^ 2
      ≤ (s.card : ℝ) * ∑ a ∈ s, (∑ b ∈ t, G a b) ^ 2 := h1
    _ ≤ (s.card : ℝ) * ((t.card : ℝ) * ∑ a ∈ s, ∑ b ∈ t, (G a b) ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (s.card : ℝ) * (t.card : ℝ) * ∑ a ∈ s, ∑ b ∈ t, (G a b) ^ 2 := by ring

/-- A single binomial coefficient of the Leibniz rule at level `≤ 6`. -/
theorem choose_le_64 (j b : ℕ) (hj : j ≤ 6) : (j.choose b : ℝ) ≤ 64 := by
  have h1 : j.choose b ≤ 2 ^ j := Nat.choose_le_two_pow j b
  have h3 : (2 : ℕ) ^ j ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hj
  have h5 : j.choose b ≤ 64 := le_trans h1 h3
  exact_mod_cast h5

/-- The product of the two binomial coefficients of a mixed Leibniz summand at level `≤ 6`. -/
theorem choose_mul_choose_le_64 (i j a b : ℕ) (hij : i + j ≤ 6) :
    (i.choose a : ℝ) * (j.choose b : ℝ) ≤ 64 := by
  have h1 : i.choose a ≤ 2 ^ i := Nat.choose_le_two_pow i a
  have h2 : j.choose b ≤ 2 ^ j := Nat.choose_le_two_pow j b
  have h3 : (2 : ℕ) ^ (i + j) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hij
  have h4 : (2 : ℕ) ^ i * 2 ^ j ≤ 64 := by
    rw [← Nat.pow_add]; simpa using h3
  have h5 : i.choose a * j.choose b ≤ 64 := le_trans (Nat.mul_le_mul h1 h2) h4
  exact_mod_cast h5

/-- `D_z^k (D_θ f) = D_z^k D_θ^1 f`, definitionally. -/
theorem mixed_one_eq_DzIter_Dth (k : ℕ) (f : ℝ → ℝ → ℝ) :
    mixed k 1 f = DzIter k (Dth f) := rfl

/-! ## The two slot bounds -/

/-- The mixed slots of `HkIntegrand α 6 (A · D_θ f)` are bounded by `ptdC1 · ptdBud`. -/
theorem slotM_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {A f : ℝ → ℝ → ℝ} {MA : ℝ} (hA : Work.FTS.EllipticEst.SmoothOpen A)
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hmA : Work.Spaces.HkMem α 6 A) (hmf : Work.Spaces.HkMem α 6 f)
    (hMA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 6) :
    (mixed j i (fun z θ => A z θ * Dth f z θ) z θ * Wt α z θ) ^ 2
      ≤ ptdC1 * ptdBud α A f MA z θ := by
  have hDth : Work.FTS.EllipticEst.SmoothOpen (Dth f) := hf.Dth
  have hpoint : mixed j i (fun z θ => A z θ * Dth f z θ) z θ * Wt α z θ
      = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ) := by
    rw [Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed j i A (Dth f) hA hDth z θ hz hθ0 hθ1]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [Work.FTS.StrongEps.H5.mixed_Dth_eq]
    ring
  rw [hpoint]
  have hbud0 : 0 ≤ ptdBud α A f MA z θ := ptdBud_nonneg hα A f MA z θ
  have hK2 : 0 ≤ ptdK2 := le_of_lt ptdK2_pos
  have h4096 : (0:ℝ) ≤ 4096 * (ptdK2 * ptdBud α A f MA z θ) :=
    mul_nonneg (by norm_num) (mul_nonneg hK2 hbud0)
  -- the per-summand bound, with the binomial coefficient absorbed
  have hterm : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
      (((i.choose a : ℝ) * (j.choose b : ℝ))
          * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ)) ^ 2
        ≤ 4096 * (ptdK2 * ptdBud α A f MA z θ) := by
    intro a ha b hb
    have ha' : a ≤ i := by
      have := Finset.mem_range.mp ha; omega
    have hb' : b ≤ j := by
      have := Finset.mem_range.mp hb; omega
    have hbase := PtDthAux.summandM_bound α hα hα1 hA hf hmA hmf hMA hz hθ0 hθ1 hi hij ha' hb'
    have hc := choose_mul_choose_le_64 i j a b hij
    have hc0 : 0 ≤ (i.choose a : ℝ) * (j.choose b : ℝ) := by positivity
    have hc2 : ((i.choose a : ℝ) * (j.choose b : ℝ)) ^ 2 ≤ 4096 := by nlinarith
    have hsq : (((i.choose a : ℝ) * (j.choose b : ℝ))
          * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ)) ^ 2
        = ((i.choose a : ℝ) * (j.choose b : ℝ)) ^ 2
          * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ) ^ 2 := by
      ring
    rw [hsq]
    calc ((i.choose a : ℝ) * (j.choose b : ℝ)) ^ 2
            * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ) ^ 2
        ≤ 4096 * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right hc2 (sq_nonneg _)
      _ ≤ 4096 * (ptdK2 * ptdBud α A f MA z θ) :=
          mul_le_mul_of_nonneg_left hbase (by norm_num)
  -- the two Cauchy–Schwarz steps
  have hinner : ∀ a ∈ Finset.range (i + 1),
      ∑ b ∈ Finset.range (j + 1),
          (((i.choose a : ℝ) * (j.choose b : ℝ))
            * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ)) ^ 2
        ≤ ((j : ℝ) + 1) * (4096 * (ptdK2 * ptdBud α A f MA z θ)) := by
    intro a ha
    have h := Finset.sum_le_card_nsmul (Finset.range (j + 1))
      (fun b => (((i.choose a : ℝ) * (j.choose b : ℝ))
            * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ)) ^ 2)
      (4096 * (ptdK2 * ptdBud α A f MA z θ)) (fun b hb => hterm a ha b hb)
    simpa [Finset.card_range, nsmul_eq_mul] using h
  have hsum : ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        (((i.choose a : ℝ) * (j.choose b : ℝ))
            * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ)) ^ 2
      ≤ ((i : ℝ) + 1) * (((j : ℝ) + 1) * (4096 * (ptdK2 * ptdBud α A f MA z θ))) := by
    have h := Finset.sum_le_card_nsmul (Finset.range (i + 1))
      (fun a => ∑ b ∈ Finset.range (j + 1),
          (((i.choose a : ℝ) * (j.choose b : ℝ))
            * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ)) ^ 2)
      (((j : ℝ) + 1) * (4096 * (ptdK2 * ptdBud α A f MA z θ))) (fun a ha => hinner a ha)
    simpa [Finset.card_range, nsmul_eq_mul] using h
  have hCS := sq_sum_sq_le (Finset.range (i + 1)) (Finset.range (j + 1))
    (fun a b => ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ))
  have hCS' : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ)) ^ 2
      ≤ ((i : ℝ) + 1) * ((j : ℝ) + 1)
        * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (((i.choose a : ℝ) * (j.choose b : ℝ))
              * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ)) ^ 2 := by
    simpa [Finset.card_range] using hCS
  have hi7 : ((i : ℝ) + 1) ≤ 7 := by
    have : (i : ℝ) ≤ 6 := by exact_mod_cast (by omega : i ≤ 6)
    linarith
  have hj7 : ((j : ℝ) + 1) ≤ 7 := by
    have : (j : ℝ) ≤ 6 := by exact_mod_cast (by omega : j ≤ 6)
    linarith
  have hi0 : (0 : ℝ) ≤ (i : ℝ) + 1 := by positivity
  have hj0 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  calc (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ)) ^ 2
      ≤ ((i : ℝ) + 1) * ((j : ℝ) + 1)
        * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (((i.choose a : ℝ) * (j.choose b : ℝ))
              * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ)) ^ 2 := hCS'
    _ ≤ ((i : ℝ) + 1) * ((j : ℝ) + 1)
        * (((i : ℝ) + 1) * (((j : ℝ) + 1) * (4096 * (ptdK2 * ptdBud α A f MA z θ)))) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg hi0 hj0)
    _ = (((i : ℝ) + 1) * ((j : ℝ) + 1) * (((i : ℝ) + 1) * ((j : ℝ) + 1)))
          * (4096 * (ptdK2 * ptdBud α A f MA z θ)) := by ring
    _ ≤ 2401 * (4096 * (ptdK2 * ptdBud α A f MA z θ)) := by
          have hab : ((i : ℝ) + 1) * ((j : ℝ) + 1) ≤ 49 := by nlinarith
          have hab0 : 0 ≤ ((i : ℝ) + 1) * ((j : ℝ) + 1) := mul_nonneg hi0 hj0
          refine mul_le_mul_of_nonneg_right ?_ h4096
          nlinarith [hab, hab0]
    _ ≤ ptdC1 * ptdBud α A f MA z θ := by
          rw [ptdC1]
          have h1 : (2401:ℝ) * (4096 * (ptdK2 * ptdBud α A f MA z θ))
              = 2401 * 4096 * ptdK2 * ptdBud α A f MA z θ := by ring
          rw [h1]

/-- The pure `D_z`-slots of `HkIntegrand α 6 (A · D_θ f)` are bounded by `ptdC1 · ptdBud`. -/
theorem slotZ_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {A f : ℝ → ℝ → ℝ} {MA : ℝ} (hA : Work.FTS.EllipticEst.SmoothOpen A)
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hmA : Work.Spaces.HkMem α 6 A) (hmf : Work.Spaces.HkMem α 6 f)
    (hMA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    {j : ℕ} (hj : j ≤ 6) :
    (DzIter j (fun z θ => A z θ * Dth f z θ) z θ
        * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
      ≤ ptdC1 * ptdBud α A f MA z θ := by
  have hDth : Work.FTS.EllipticEst.SmoothOpen (Dth f) := hf.Dth
  have hpoint : DzIter j (fun z θ => A z θ * Dth f z θ) z θ
        * (w z / Real.sin (2 * θ) ^ (eta / 2))
      = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
          * (DzIter b A z θ * mixed (j - b) 1 f z θ
              * (w z / Real.sin (2 * θ) ^ (eta / 2))) := by
    rw [← Work.Spaces.mixed_zero_right j (fun z θ => A z θ * Dth f z θ)]
    rw [Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed j 0 A (Dth f) hA hDth z θ hz hθ0 hθ1]
    rw [show Finset.range (0 + 1) = Finset.range 1 from rfl]
    simp only [Finset.sum_range_one]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, mixed_zero_right]
    rw [← mixed_one_eq_DzIter_Dth]
    ring
  rw [hpoint]
  have hbud0 : 0 ≤ ptdBud α A f MA z θ := ptdBud_nonneg hα A f MA z θ
  have hK2 : 0 ≤ ptdK2 := le_of_lt ptdK2_pos
  have h4096 : (0:ℝ) ≤ 4096 * (ptdK2 * ptdBud α A f MA z θ) :=
    mul_nonneg (by norm_num) (mul_nonneg hK2 hbud0)
  have hterm : ∀ b ∈ Finset.range (j + 1),
      ((j.choose b : ℝ) * (DzIter b A z θ * mixed (j - b) 1 f z θ
              * (w z / Real.sin (2 * θ) ^ (eta / 2)))) ^ 2
        ≤ 4096 * (ptdK2 * ptdBud α A f MA z θ) := by
    intro b hb
    have hb' : b ≤ j := by
      have := Finset.mem_range.mp hb; omega
    have hbase := PtDthAux.summandZ_bound α hα hα1 hA hf hmA hmf hMA hz hθ0 hθ1 hj hb'
    have hc := choose_le_64 j b hj
    have hc0 : 0 ≤ (j.choose b : ℝ) := by positivity
    have hc2 : (j.choose b : ℝ) ^ 2 ≤ 4096 := by nlinarith
    have hsq : ((j.choose b : ℝ) * (DzIter b A z θ * mixed (j - b) 1 f z θ
              * (w z / Real.sin (2 * θ) ^ (eta / 2)))) ^ 2
        = (j.choose b : ℝ) ^ 2 * (DzIter b A z θ * mixed (j - b) 1 f z θ
              * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2 := by ring
    rw [hsq]
    calc (j.choose b : ℝ) ^ 2 * (DzIter b A z θ * mixed (j - b) 1 f z θ
              * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
        ≤ 4096 * (DzIter b A z θ * mixed (j - b) 1 f z θ
              * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2 :=
          mul_le_mul_of_nonneg_right hc2 (sq_nonneg _)
      _ ≤ 4096 * (ptdK2 * ptdBud α A f MA z θ) :=
          mul_le_mul_of_nonneg_left hbase (by norm_num)
  have hCS := sq_sum_le_card_mul_sum_sq (Finset.range (j + 1))
    (fun b => (j.choose b : ℝ) * (DzIter b A z θ * mixed (j - b) 1 f z θ
              * (w z / Real.sin (2 * θ) ^ (eta / 2))))
  have hCS' : (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
        * (DzIter b A z θ * mixed (j - b) 1 f z θ
            * (w z / Real.sin (2 * θ) ^ (eta / 2)))) ^ 2
      ≤ ((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1),
          ((j.choose b : ℝ) * (DzIter b A z θ * mixed (j - b) 1 f z θ
              * (w z / Real.sin (2 * θ) ^ (eta / 2)))) ^ 2 := by
    simpa [Finset.card_range] using hCS
  have hsum : ∑ b ∈ Finset.range (j + 1),
        ((j.choose b : ℝ) * (DzIter b A z θ * mixed (j - b) 1 f z θ
              * (w z / Real.sin (2 * θ) ^ (eta / 2)))) ^ 2
      ≤ ((j : ℝ) + 1) * (4096 * (ptdK2 * ptdBud α A f MA z θ)) := by
    have h := Finset.sum_le_card_nsmul (Finset.range (j + 1))
      (fun b => ((j.choose b : ℝ) * (DzIter b A z θ * mixed (j - b) 1 f z θ
              * (w z / Real.sin (2 * θ) ^ (eta / 2)))) ^ 2)
      (4096 * (ptdK2 * ptdBud α A f MA z θ)) (fun b hb => hterm b hb)
    simpa [Finset.card_range, nsmul_eq_mul] using h
  have hj7 : ((j : ℝ) + 1) ≤ 7 := by
    have : (j : ℝ) ≤ 6 := by exact_mod_cast (by omega : j ≤ 6)
    linarith
  have hj0 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  calc (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
        * (DzIter b A z θ * mixed (j - b) 1 f z θ
            * (w z / Real.sin (2 * θ) ^ (eta / 2)))) ^ 2
      ≤ ((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1),
          ((j.choose b : ℝ) * (DzIter b A z θ * mixed (j - b) 1 f z θ
              * (w z / Real.sin (2 * θ) ^ (eta / 2)))) ^ 2 := hCS'
    _ ≤ ((j : ℝ) + 1) * (((j : ℝ) + 1) * (4096 * (ptdK2 * ptdBud α A f MA z θ))) :=
          mul_le_mul_of_nonneg_left hsum hj0
    _ = (((j : ℝ) + 1) * ((j : ℝ) + 1)) * (4096 * (ptdK2 * ptdBud α A f MA z θ)) := by ring
    _ ≤ 49 * (4096 * (ptdK2 * ptdBud α A f MA z θ)) := by
          have hab : ((j : ℝ) + 1) * ((j : ℝ) + 1) ≤ 49 := by nlinarith
          have hab0 : 0 ≤ ((j : ℝ) + 1) * ((j : ℝ) + 1) := mul_nonneg hj0 hj0
          refine mul_le_mul_of_nonneg_right ?_ h4096
          nlinarith [hab, hab0]
    _ ≤ ptdC1 * ptdBud α A f MA z θ := by
          rw [ptdC1]
          have h1 : (49:ℝ) * (4096 * (ptdK2 * ptdBud α A f MA z θ))
              ≤ 2401 * (4096 * (ptdK2 * ptdBud α A f MA z θ)) := by
            refine mul_le_mul_of_nonneg_right ?_ h4096
            norm_num
          calc (49:ℝ) * (4096 * (ptdK2 * ptdBud α A f MA z θ))
              ≤ 2401 * (4096 * (ptdK2 * ptdBud α A f MA z θ)) := h1
            _ = 2401 * 4096 * ptdK2 * ptdBud α A f MA z θ := by ring

/-! ## The assembly -/

/-- The two energy-priced budget terms are dominated by the middle part of the target RHS. -/
theorem inv_pair_le_mid {α : ℝ} (hα : 0 < α) {hA6 hf6 X6A X6f : ℝ}
    (hA6n : 0 ≤ hA6) (hf6n : 0 ≤ hf6) (hXAn : 0 ≤ X6A) (hXfn : 0 ≤ X6f) :
    (gam α - 1)⁻¹ * hA6 * X6f + (gam α - 1)⁻¹ * hf6 * X6A
      ≤ (1 + (gam α - 1)⁻¹ * (hA6 + hf6)) * (X6A + X6f) := by
  have hI : 0 ≤ (gam α - 1)⁻¹ :=
    inv_nonneg.mpr (le_of_lt (by rw [gam_sub_one]; linarith))
  have hS : 0 ≤ X6A + X6f := by linarith
  have hkey : (gam α - 1)⁻¹ * (hA6 + hf6) * (X6A + X6f)
        - ((gam α - 1)⁻¹ * hA6 * X6f + (gam α - 1)⁻¹ * hf6 * X6A)
      = (gam α - 1)⁻¹ * (hA6 * X6A + hf6 * X6f) := by ring
  have hnn : 0 ≤ (gam α - 1)⁻¹ * (hA6 * X6A + hf6 * X6f) :=
    mul_nonneg hI (by linarith [mul_nonneg hA6n hXAn, mul_nonneg hf6n hXfn])
  have hstep : (gam α - 1)⁻¹ * hA6 * X6f + (gam α - 1)⁻¹ * hf6 * X6A
      ≤ (gam α - 1)⁻¹ * (hA6 + hf6) * (X6A + X6f) := by linarith [hkey, hnn]
  have hmono : (gam α - 1)⁻¹ * (hA6 + hf6) * (X6A + X6f)
      ≤ (1 + (gam α - 1)⁻¹ * (hA6 + hf6)) * (X6A + X6f) :=
    mul_le_mul_of_nonneg_right (by linarith) hS
  linarith [hstep, hmono]

theorem ptBoundDth (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A f : ℝ → ℝ → ℝ) (MA : ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f → Work.Spaces.HkMem α 7 f →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA) →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.HkIntegrand α 6 (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ
          ≤ K * MA ^ 2 * Work.Spaces.HkIntegrand α 7 f z θ
            + K * (1 + (Work.Spaces.gam α - 1)⁻¹
                * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
              * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)
            + K * (Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ
                * Work.Spaces.Wt α z θ) ^ 2 := by
  have hKpos : 0 < 10 ^ 14 * (CP + 1) + 1 := by
    have := CP_pos; positivity
  refine ⟨10 ^ 14 * (CP + 1) + 1, hKpos, ?_⟩
  intro A f MA hA hf hmA hmf hm7f hMA z θ hz hθ0 hθ1
  set RHS : ℝ := MA ^ 2 * HkIntegrand α 7 f z θ
      + (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f))
        * (HkIntegrand α 6 A z θ + HkIntegrand α 6 f z θ)
      + (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ) ^ 2 with hRHS
  have hbud0 : 0 ≤ ptdBud α A f MA z θ := ptdBud_nonneg hα A f MA z θ
  -- the budget is dominated by `RHS`
  have hbud_le : ptdBud α A f MA z θ ≤ RHS := by
    have hI : 0 ≤ (gam α - 1)⁻¹ :=
      inv_nonneg.mpr (le_of_lt (by rw [gam_sub_one]; linarith))
    have h2 := HkSq_nonneg α 6 A
    have h3 := HkSq_nonneg α 6 f
    have h4 := HkIntegrand_nonneg α 6 A z θ
    have h5 := HkIntegrand_nonneg α 6 f z θ
    have h1 := HkIntegrand_nonneg α 7 f z θ
    have e2 := inv_pair_le_mid (α := α) hα h2 h3 h4 h5
    rw [ptdBud, hRHS]
    linarith [e2]
  -- the level-six integrand is bounded by `56 · ptdC1 · ptdBud`
  have hLHS : HkIntegrand α 6 (fun z θ => A z θ * Dth f z θ) z θ
      ≤ 56 * ptdC1 * ptdBud α A f MA z θ := by
    have hZ : ∑ i ∈ Finset.range 7,
        (DzIter i (fun z θ => A z θ * Dth f z θ) z θ
          * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
        ≤ 7 * (ptdC1 * ptdBud α A f MA z θ) := by
      have h := Finset.sum_le_card_nsmul (Finset.range 7)
        (fun i => (DzIter i (fun z θ => A z θ * Dth f z θ) z θ
          * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2)
        (ptdC1 * ptdBud α A f MA z θ)
        (fun i hi => slotZ_bound α hα hα1 hA hf hmA hmf hMA hz hθ0 hθ1
          (by have := Finset.mem_range.mp hi; omega))
      simpa [Finset.card_range, nsmul_eq_mul] using h
    have hM : ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
        (if 1 ≤ i ∧ i + j ≤ 6
          then (mixed j i (fun z θ => A z θ * Dth f z θ) z θ * Wt α z θ) ^ 2 else 0)
        ≤ 49 * (ptdC1 * ptdBud α A f MA z θ) := by
      have hinner : ∀ i ∈ Finset.range 7,
          ∑ j ∈ Finset.range 7,
            (if 1 ≤ i ∧ i + j ≤ 6
              then (mixed j i (fun z θ => A z θ * Dth f z θ) z θ * Wt α z θ) ^ 2 else 0)
          ≤ 7 * (ptdC1 * ptdBud α A f MA z θ) := by
        intro i hi
        have h := Finset.sum_le_card_nsmul (Finset.range 7)
          (fun j => (if 1 ≤ i ∧ i + j ≤ 6
              then (mixed j i (fun z θ => A z θ * Dth f z θ) z θ * Wt α z θ) ^ 2 else 0))
          (ptdC1 * ptdBud α A f MA z θ) (fun j hj => by
            by_cases hic : 1 ≤ i ∧ i + j ≤ 6
            · rw [if_pos hic]
              exact slotM_bound α hα hα1 hA hf hmA hmf hMA hz hθ0 hθ1 hic.1 hic.2
            · rw [if_neg hic]
              exact mul_nonneg ptdC1_nonneg hbud0)
        simpa [Finset.card_range, nsmul_eq_mul] using h
      have h := Finset.sum_le_card_nsmul (Finset.range 7) _
        (7 * (ptdC1 * ptdBud α A f MA z θ)) hinner
      have h2 : (7:ℝ) * (7 * (ptdC1 * ptdBud α A f MA z θ))
          = 49 * (ptdC1 * ptdBud α A f MA z θ) := by ring
      simpa [Finset.card_range, nsmul_eq_mul, h2] using h
    rw [HkIntegrand]
    calc _ ≤ 7 * (ptdC1 * ptdBud α A f MA z θ) + 49 * (ptdC1 * ptdBud α A f MA z θ) :=
          add_le_add hZ hM
      _ = 56 * ptdC1 * ptdBud α A f MA z θ := by ring
  have h56 : 56 * ptdC1 ≤ 10 ^ 14 * (CP + 1) + 1 := by
    have h1 := CP_pos
    rw [ptdC1, ptdK2]
    nlinarith
  calc HkIntegrand α 6 (fun z θ => A z θ * Dth f z θ) z θ
      ≤ 56 * ptdC1 * ptdBud α A f MA z θ := hLHS
    _ ≤ (10 ^ 14 * (CP + 1) + 1) * ptdBud α A f MA z θ :=
        mul_le_mul_of_nonneg_right h56 hbud0
    _ ≤ (10 ^ 14 * (CP + 1) + 1) * RHS :=
        mul_le_mul_of_nonneg_left hbud_le hKpos.le
    _ = (10 ^ 14 * (CP + 1) + 1) * MA ^ 2 * HkIntegrand α 7 f z θ
          + (10 ^ 14 * (CP + 1) + 1) * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f))
            * (HkIntegrand α 6 A z θ + HkIntegrand α 6 f z θ)
          + (10 ^ 14 * (CP + 1) + 1) * (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ) ^ 2 := by
        rw [hRHS]; ring


end Work.FTS.StrongEps.E4R3.Nblock6.Tools
