import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.t3SlotGuarded

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2Sup

set_option autoImplicit false

open Work.FTS.TransportS.SlotT2
/-! ## The parts of the Leibniz sum -/

/-- The Leibniz sum of the transport pairing with the slot `(a,b)`, in the index order of
`mixed_mul_Dz_open`. -/
def Ssum (f g : ℝ → ℝ → ℝ) (a b : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
    ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
      * (Work.Spaces.mixed b1 a1 f z θ * Work.Spaces.mixed (b + 1 - b1) (a - a1) g z θ)

/-- The `(a1,b1) = (0,0)` summand. -/
def SmainSum (f g : ℝ → ℝ → ℝ) (a b : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
    (if a1 = 0 ∧ b1 = 0 then
      ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
        * (Work.Spaces.mixed b1 a1 f z θ * Work.Spaces.mixed (b + 1 - b1) (a - a1) g z θ)
    else 0)

/-- The `(a1,b1) = (0,3)` summand. -/
def SdelSum (f g : ℝ → ℝ → ℝ) (a b : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
    (if a1 = 0 ∧ b1 = 3 then
      ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
        * (Work.Spaces.mixed b1 a1 f z θ * Work.Spaces.mixed (b + 1 - b1) (a - a1) g z θ)
    else 0)

/-- All the remaining summands. -/
def Srest (f g : ℝ → ℝ → ℝ) (a b : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
    (if (a1 = 0 ∧ b1 = 0) ∨ (a1 = 0 ∧ b1 = 3) then (0 : ℝ)
      else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
        * (Work.Spaces.mixed b1 a1 f z θ * Work.Spaces.mixed (b + 1 - b1) (a - a1) g z θ))

/-- The main summand in closed form: `f · D_z(mixed b a g)`. -/
def Smain (f g : ℝ → ℝ → ℝ) (a b : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => f z θ * Work.Spaces.mixed (b + 1) a g z θ

/-- The `(0,3)` summand in closed form. -/
def Sdel (f g : ℝ → ℝ → ℝ) (a b : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => (b.choose 3 : ℝ)
    * (Work.Spaces.mixed 3 0 f z θ * Work.Spaces.mixed (b - 2) a g z θ)

/-- The majorant of a single non-delicate summand. -/
def Maj1 (α : ℝ) (f g : ℝ → ℝ → ℝ) (Mf MK Mg : ℝ) (z θ : ℝ) : ℝ :=
  (Mf + MK) * Work.Spaces.HkIntegrand α 4 g z θ
    + Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
        * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ))

theorem Maj1_nonneg {α Mf MK Mg : ℝ} {f g : ℝ → ℝ → ℝ}
    (hM : 0 ≤ Mf + MK) (hMg : 0 ≤ Mg) (z θ : ℝ) : 0 ≤ Maj1 α f g Mf MK Mg z θ :=
  add_nonneg (mul_nonneg hM (Work.Spaces.HkIntegrand_nonneg α 4 g z θ))
    (mul_nonneg hMg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))

/-! ## Elementary Finset lemmas -/

private theorem sum_range_ite_at {n k : ℕ} (hk : k < n) (G : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, (if i = k then G i else 0)) = G k := by
  rw [Finset.sum_eq_single k]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb]
  · intro h
    exact absurd (Finset.mem_range.mpr hk) h

private theorem sum_range_ite_off {n k : ℕ} (hk : ¬ k < n) (G : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, (if i = k then G i else 0)) = 0 := by
  refine Finset.sum_eq_zero fun b hb => ?_
  rw [if_neg]
  intro h
  exact hk (h ▸ Finset.mem_range.mp hb)

private theorem split_pointwise {F : ℝ} {h1 h2 : Prop} [Decidable h1] [Decidable h2]
    (hd : ¬ (h1 ∧ h2)) :
    F = (if h1 then F else 0) + ((if h1 ∨ h2 then 0 else F) + (if h2 then F else 0)) := by
  by_cases hh1 : h1
  · have hh2 : ¬ h2 := fun h => hd ⟨hh1, h⟩
    simp only [if_pos hh1, if_pos (show h1 ∨ h2 from Or.inl hh1), if_neg hh2]
    ring
  · by_cases hh2 : h2
    · simp only [if_neg hh1, if_pos (show h1 ∨ h2 from Or.inr hh2), if_pos hh2]
      ring
    · simp only [if_neg hh1, if_neg (show ¬ (h1 ∨ h2) from not_or.mpr ⟨hh1, hh2⟩), if_neg hh2]
      ring

private theorem split_sum (n : ℕ) (F : ℕ → ℝ) (h1 h2 : ℕ → Prop) [DecidablePred h1]
    [DecidablePred h2] (hd : ∀ b, ¬ (h1 b ∧ h2 b)) :
    (∑ b1 ∈ Finset.range n, F b1)
      = (∑ b1 ∈ Finset.range n, (if h1 b1 then F b1 else (0 : ℝ)))
        + ((∑ b1 ∈ Finset.range n, (if h1 b1 ∨ h2 b1 then (0 : ℝ) else F b1))
          + (∑ b1 ∈ Finset.range n, (if h2 b1 then F b1 else (0 : ℝ)))) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b1 _ => ?_
  exact split_pointwise (hd b1)

private theorem sum_add_add {ι : Type*} (s : Finset ι) (f g h : ι → ℝ) :
    (∑ i ∈ s, (f i + (g i + h i))) = (∑ i ∈ s, f i) + ((∑ i ∈ s, g i) + (∑ i ∈ s, h i)) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

private theorem sum_sum_mul (s t : Finset ℕ) (g : ℕ → ℕ → ℝ) (a : ℝ) :
    (∑ i ∈ s, ∑ j ∈ t, g i j) * a = ∑ i ∈ s, ∑ j ∈ t, g i j * a := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]

private theorem not_both_zero_three (a1 b1 : ℕ) :
    ¬ ((a1 = 0 ∧ b1 = 0) ∧ (a1 = 0 ∧ b1 = 3)) := by
  rintro ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
  omega

/-! ## The Leibniz identity and the split -/

/-- The Leibniz expansion of the transport pairing, in the notation of this file. -/
theorem Ssum_eq_leibniz (b a : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ = Ssum f g a b z θ := by
  intro z θ hz hθ hθ2
  rw [Work.FTS.TransportS.mixed_mul_Dz_open b a f g hf hg z θ hz hθ hθ2]
  refine Finset.sum_congr rfl fun a1 _ => Finset.sum_congr rfl fun b1 hb1 => ?_
  have hb1' : b1 ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb1)
  rw [show b - b1 + 1 = b + 1 - b1 by omega]

/-- The three-way split of the Leibniz sum. -/
theorem Ssum_eq_parts (f g : ℝ → ℝ → ℝ) (a b : ℕ) :
    Ssum f g a b = fun z θ =>
      SmainSum f g a b z θ + (Srest f g a b z θ + SdelSum f g a b z θ) := by
  funext z θ
  simp only [Ssum, SmainSum, Srest, SdelSum]
  refine (Finset.sum_congr rfl (fun a1 _ => ?_)).trans (sum_add_add _ _ _ _)
  exact split_sum (b + 1) (fun b1 => ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
    * (Work.Spaces.mixed b1 a1 f z θ * Work.Spaces.mixed (b + 1 - b1) (a - a1) g z θ))
    (fun b1 => a1 = 0 ∧ b1 = 0) (fun b1 => a1 = 0 ∧ b1 = 3)
    (fun b1 => not_both_zero_three a1 b1)

/-- The `(0,0)` part of the Leibniz sum is the single summand. -/
theorem SmainSum_eq (f g : ℝ → ℝ → ℝ) (a b : ℕ) (z θ : ℝ) :
    SmainSum f g a b z θ = f z θ * Work.Spaces.mixed (b + 1) a g z θ := by
  have hmem : (0 : ℕ) ∈ Finset.range (a + 1) := Finset.mem_range.mpr (Nat.succ_pos a)
  simp only [SmainSum]
  rw [Finset.sum_eq_single 0 (fun a1 _ ha1 => by
        refine Finset.sum_eq_zero fun b1 _ => ?_
        rw [if_neg]
        rintro ⟨h, -⟩
        exact ha1 h)
      (fun h => absurd hmem h)]
  rw [show (∑ b1 ∈ Finset.range (b + 1),
        (if (0 : ℕ) = 0 ∧ b1 = 0 then
          ((a.choose 0 : ℝ) * (b.choose b1 : ℝ))
            * (Work.Spaces.mixed b1 0 f z θ * Work.Spaces.mixed (b + 1 - b1) (a - 0) g z θ)
        else 0))
      = (∑ b1 ∈ Finset.range (b + 1),
        (if b1 = 0 then
          ((a.choose 0 : ℝ) * (b.choose b1 : ℝ))
            * (Work.Spaces.mixed b1 0 f z θ * Work.Spaces.mixed (b + 1 - b1) (a - 0) g z θ)
        else 0)) from Finset.sum_congr rfl fun b1 _ => by simp]
  rw [sum_range_ite_at (Nat.succ_pos b) (fun b1 => ((a.choose 0 : ℝ) * (b.choose b1 : ℝ))
      * (Work.Spaces.mixed b1 0 f z θ * Work.Spaces.mixed (b + 1 - b1) (a - 0) g z θ))]
  simp [Nat.sub_zero]

/-- The `(0,3)` part of the Leibniz sum is the single summand. -/
theorem SdelSum_eq (f g : ℝ → ℝ → ℝ) (a b : ℕ) (z θ : ℝ) :
    SdelSum f g a b z θ
      = (b.choose 3 : ℝ) * (Work.Spaces.mixed 3 0 f z θ * Work.Spaces.mixed (b - 2) a g z θ) := by
  have hmem : (0 : ℕ) ∈ Finset.range (a + 1) := Finset.mem_range.mpr (Nat.succ_pos a)
  simp only [SdelSum]
  rw [Finset.sum_eq_single 0 (fun a1 _ ha1 => by
        refine Finset.sum_eq_zero fun b1 _ => ?_
        rw [if_neg]
        rintro ⟨h, -⟩
        exact ha1 h)
      (fun h => absurd hmem h)]
  rw [show (∑ b1 ∈ Finset.range (b + 1),
        (if (0 : ℕ) = 0 ∧ b1 = 3 then
          ((a.choose 0 : ℝ) * (b.choose b1 : ℝ))
            * (Work.Spaces.mixed b1 0 f z θ * Work.Spaces.mixed (b + 1 - b1) (a - 0) g z θ)
        else 0))
      = (∑ b1 ∈ Finset.range (b + 1),
        (if b1 = 3 then
          ((a.choose 0 : ℝ) * (b.choose b1 : ℝ))
            * (Work.Spaces.mixed b1 0 f z θ * Work.Spaces.mixed (b + 1 - b1) (a - 0) g z θ)
        else 0)) from Finset.sum_congr rfl fun b1 _ => by simp]
  by_cases hb : 3 < b + 1
  · rw [sum_range_ite_at hb (fun b1 => ((a.choose 0 : ℝ) * (b.choose b1 : ℝ))
      * (Work.Spaces.mixed b1 0 f z θ * Work.Spaces.mixed (b + 1 - b1) (a - 0) g z θ))]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
    rw [show b + 1 - 3 = b - 2 by omega]
  · rw [sum_range_ite_off (by omega) (fun b1 => ((a.choose 0 : ℝ) * (b.choose b1 : ℝ))
      * (Work.Spaces.mixed b1 0 f z θ * Work.Spaces.mixed (b + 1 - b1) (a - 0) g z θ))]
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]

/-- The three-way split, with the two exceptional sums in closed form. -/
theorem Ssum_eq_Smain_Srest_Sdel (f g : ℝ → ℝ → ℝ) (a b : ℕ) (z θ : ℝ) :
    Ssum f g a b z θ
      = Smain f g a b z θ + (Srest f g a b z θ + Sdel f g a b z θ) := by
  rw [congrFun (congrFun (Ssum_eq_parts f g a b) z) θ, SmainSum_eq, SdelSum_eq]
  rfl

/-! ## The pointwise bound on the remainder -/

/-- **The pointwise bound on the remainder of the Leibniz sum.**  Every summand of `Srest` has
an `f`-slot of order `≥ 1`, so either the σ-gain or a sup bound on the middle `g`-slot applies
(`termPair_nd'`), and the binomial coefficients sum to at most `6400`. -/
theorem canonW_mul_Srest_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f g : ℝ → ℝ → ℝ} {a b : ℕ} {q Mf MK Mg : ℝ}
    (hMf : 0 ≤ Mf) (hMK : 0 ≤ MK) (hMg : 0 ≤ Mg) (hqnn : 0 ≤ q) (hab : a + b ≤ 4)
    (hq0 : a = 0 → q ≤ Work.Spaces.eta) (hqγ : q ≤ Work.Spaces.gam α)
    (hqcase : q ≤ Work.Spaces.eta ∨ q = Work.Spaces.gam α)
    (hFsup : ∀ j : ℕ, j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.DzIter j f z θ| ≤ Mf)
    (hFσ : ∀ j i : ℕ, 1 ≤ i → i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i f z θ| ≤ MK * Real.sin (2 * θ))
    (hGsup : ∀ j i : ℕ, i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i g z θ| ≤ Mg) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * |Srest f g a b z θ| * |Work.Spaces.mixed b a g z θ|
        ≤ 6400 * Maj1 α f g Mf MK Mg z θ := by
  intro z θ hz hθ hθ2
  have hMaj : 0 ≤ Maj1 α f g Mf MK Mg z θ := Maj1_nonneg (by linarith) hMg z θ
  have hC : 0 ≤ canonW q z θ * |Work.Spaces.mixed b a g z θ| :=
    mul_nonneg (canonW_nonneg ⟨le_of_lt hθ, le_of_lt hθ2⟩) (abs_nonneg _)
  -- Step 1: the absolute value of the remainder sum
  have h1 : |Srest f g a b z θ| ≤ ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
      (if (a1 = 0 ∧ b1 = 0) ∨ (a1 = 0 ∧ b1 = 3) then (0 : ℝ)
        else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
          * |Work.Spaces.mixed b1 a1 f z θ * Work.Spaces.mixed (b + 1 - b1) (a - a1) g z θ|) := by
    simp only [Srest]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun a1 _ => ?_)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun b1 _ => ?_)
    by_cases hc : (a1 = 0 ∧ b1 = 0) ∨ (a1 = 0 ∧ b1 = 3)
    · rw [if_pos hc, if_pos hc, abs_zero]
    · rw [if_neg hc, if_neg hc, abs_mul,
        abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  -- Step 2: multiply by the nonnegative weight
  have h2 : canonW q z θ * |Work.Spaces.mixed b a g z θ| * |Srest f g a b z θ|
      ≤ canonW q z θ * |Work.Spaces.mixed b a g z θ|
        * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
            (if (a1 = 0 ∧ b1 = 0) ∨ (a1 = 0 ∧ b1 = 3) then (0 : ℝ)
              else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
                * |Work.Spaces.mixed b1 a1 f z θ
                    * Work.Spaces.mixed (b + 1 - b1) (a - a1) g z θ|)) :=
    mul_le_mul_of_nonneg_left h1 hC
  -- Step 3: distribute the weight into the sum
  have h3 : canonW q z θ * |Work.Spaces.mixed b a g z θ|
        * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
            (if (a1 = 0 ∧ b1 = 0) ∨ (a1 = 0 ∧ b1 = 3) then (0 : ℝ)
              else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
                * |Work.Spaces.mixed b1 a1 f z θ
                    * Work.Spaces.mixed (b + 1 - b1) (a - a1) g z θ|))
      = ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          (canonW q z θ * |Work.Spaces.mixed b a g z θ|)
            * (if (a1 = 0 ∧ b1 = 0) ∨ (a1 = 0 ∧ b1 = 3) then (0 : ℝ)
              else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
                * |Work.Spaces.mixed b1 a1 f z θ
                    * Work.Spaces.mixed (b + 1 - b1) (a - a1) g z θ|) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a1 _ => ?_
    rw [Finset.mul_sum]
  -- Step 4: each summand is bounded by `coef * Maj1`
  have h4 : ∀ a1 b1 : ℕ, a1 ≤ a → b1 ≤ b →
      (canonW q z θ * |Work.Spaces.mixed b a g z θ|)
          * (if (a1 = 0 ∧ b1 = 0) ∨ (a1 = 0 ∧ b1 = 3) then (0 : ℝ)
            else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
              * |Work.Spaces.mixed b1 a1 f z θ
                  * Work.Spaces.mixed (b + 1 - b1) (a - a1) g z θ|)
        ≤ ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)) * Maj1 α f g Mf MK Mg z θ := by
    intro a1 b1 ha1 hb1
    by_cases hc : (a1 = 0 ∧ b1 = 0) ∨ (a1 = 0 ∧ b1 = 3)
    · rw [if_pos hc, mul_zero]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hMaj
    · rw [if_neg hc]
      have hp1 : 1 ≤ a1 + b1 := by
        rcases Nat.eq_zero_or_pos a1 with h | h
        · rcases Nat.eq_zero_or_pos b1 with h' | h'
          · exact absurd (Or.inl ⟨h, h'⟩) hc
          · omega
        · omega
      have hnd : ¬ (a1 = 0 ∧ b1 = 3 ∧ q = Work.Spaces.gam α) := by
        rintro ⟨h1, h2, -⟩
        exact hc (Or.inr ⟨h1, h2⟩)
      have hp := termPair_nd' hα hα1 hMf hMK hMg hqnn hab ha1 hb1 hp1 hq0 hqγ hqcase
        hnd hFsup hFσ hGsup z θ hz hθ hθ2
      have hkey : canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
            * |Work.Spaces.mixed (b + 1 - b1) (a - a1) g z θ|
            * |Work.Spaces.mixed b a g z θ| ≤ Maj1 α f g Mf MK Mg z θ := by
        simpa only [Maj1] using hp
      rw [abs_mul]
      calc (canonW q z θ * |Work.Spaces.mixed b a g z θ|)
            * (((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
              * (|Work.Spaces.mixed b1 a1 f z θ|
                  * |Work.Spaces.mixed (b + 1 - b1) (a - a1) g z θ|))
          = ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
            * (canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
                * |Work.Spaces.mixed (b + 1 - b1) (a - a1) g z θ|
                * |Work.Spaces.mixed b a g z θ|) := by ring
        _ ≤ ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)) * Maj1 α f g Mf MK Mg z θ :=
            mul_le_mul_of_nonneg_left hkey
              (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  -- Step 5: sum up
  have h5 : (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
        ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)) * Maj1 α f g Mf MK Mg z θ)
      ≤ 6400 * Maj1 α f g Mf MK Mg z θ := by
    have hcard : (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
        ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))) ≤ 6400 := by
      have hinner : ∀ a1 : ℕ,
          (∑ b1 ∈ Finset.range (b + 1), (a.choose a1 : ℝ) * (b.choose b1 : ℝ))
            ≤ (((b + 1 : ℕ)) : ℝ) * 256 := by
        intro a1
        calc (∑ b1 ∈ Finset.range (b + 1), (a.choose a1 : ℝ) * (b.choose b1 : ℝ))
            ≤ (Finset.range (b + 1)).card • (256 : ℝ) :=
              Finset.sum_le_card_nsmul _ _ _ (fun b1 _ => choose_mul_le (by omega) (by omega))
          _ = (((b + 1 : ℕ)) : ℝ) * 256 := by
              rw [Finset.card_range, nsmul_eq_mul]
      calc (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
            ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
          ≤ (Finset.range (a + 1)).card • ((((b + 1 : ℕ)) : ℝ) * 256) :=
            Finset.sum_le_card_nsmul _ _ _ (fun a1 _ => hinner a1)
        _ = (((a + 1 : ℕ)) : ℝ) * ((((b + 1 : ℕ)) : ℝ) * 256) := by
            rw [Finset.card_range, nsmul_eq_mul]
        _ ≤ 6400 := by
            have ha : (((a + 1 : ℕ)) : ℝ) ≤ 5 := by
              exact_mod_cast (by omega : a + 1 ≤ 5)
            have hb : (((b + 1 : ℕ)) : ℝ) ≤ 5 := by
              exact_mod_cast (by omega : b + 1 ≤ 5)
            nlinarith
    calc (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)) * Maj1 α f g Mf MK Mg z θ)
        = (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
            ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))) * Maj1 α f g Mf MK Mg z θ :=
          (sum_sum_mul _ _ _ _).symm
      _ ≤ 6400 * Maj1 α f g Mf MK Mg z θ := mul_le_mul_of_nonneg_right hcard hMaj
  calc canonW q z θ * |Srest f g a b z θ| * |Work.Spaces.mixed b a g z θ|
      = canonW q z θ * |Work.Spaces.mixed b a g z θ| * |Srest f g a b z θ| := by ring
    _ ≤ ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          (canonW q z θ * |Work.Spaces.mixed b a g z θ|)
            * (if (a1 = 0 ∧ b1 = 0) ∨ (a1 = 0 ∧ b1 = 3) then (0 : ℝ)
              else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
                * |Work.Spaces.mixed b1 a1 f z θ
                    * Work.Spaces.mixed (b + 1 - b1) (a - a1) g z θ|) :=
        le_trans h2 (le_of_eq h3)
    _ ≤ ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)) * Maj1 α f g Mf MK Mg z θ :=
        Finset.sum_le_sum fun a1 ha1 => Finset.sum_le_sum fun b1 hb1 =>
          h4 a1 b1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha1))
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb1))
    _ ≤ 6400 * Maj1 α f g Mf MK Mg z θ := h5

end Work.FTS.TransportS.T2Sup
