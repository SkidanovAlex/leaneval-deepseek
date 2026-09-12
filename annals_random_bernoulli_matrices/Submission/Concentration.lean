/-
Generic facts about the Lévy concentration function
(`Submission.Helpers.levyConcentration`) needed by later layers
(eq-aux branch 2, the threshold lemma, the averaging machinery):

  · adding an independent summand decreases the concentration function;
  · scaling the variable scales the radius;
  · the probability that the variable lands in a fixed interval is at most
    the concentration function (already in `Helpers.le_levyConcentration`).
-/
import Mathlib
import Submission.Helpers

set_option autoImplicit false

namespace Submission.Concentration

noncomputable section

open MeasureTheory ProbabilityTheory Measure Filter
open scoped ENNReal BigOperators

/-- `P{|ξ| ≤ t} ≤ cf(ξ, t)`: taking `l = 0` in the sup defining the
concentration function. -/
theorem levyConcentration_mem_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : Ω → ℝ) (t : ℝ) :
    P {x : Ω | |ξ x| ≤ t} ≤ Submission.Helpers.levyConcentration P ξ t := by
  simpa using (Submission.Helpers.le_levyConcentration P ξ t (0 : ℝ))

/-- The family of interval masses appearing in the sup defining the
concentration function is bounded above by `1` on a probability space. -/
lemma bddAbove_cf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (ξ : Ω → ℝ) (t : ℝ) :
    BddAbove {c : ENNReal | ∃ l' : ℝ, c = P {x : Ω | |ξ x - l'| ≤ t}} := by
  refine ⟨(1 : ENNReal), ?_⟩
  intro c hc
  rcases hc with ⟨l', rfl⟩
  calc
    P {x : Ω | |ξ x - l'| ≤ t} ≤ P Set.univ := measure_mono (by intro x hx; trivial)
    _ = 1 := measure_univ

/-- Adding an independent random variable can only decrease the Lévy
concentration function: `cf(ξ + ζ, t) ≤ cf(ξ, t)` for `ξ, ζ` independent. -/
theorem levyConcentration_add_le_left {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] {ξ ζ : Ω → ℝ} (hξ : AEMeasurable ξ P)
    (hζ : AEMeasurable ζ P) (hind : ProbabilityTheory.IndepFun ξ ζ P) (t : ℝ) :
    Submission.Helpers.levyConcentration P (fun ω => ξ ω + ζ ω) t ≤
      Submission.Helpers.levyConcentration P ξ t := by
  classical
  unfold Submission.Helpers.levyConcentration
  rw [sSup_le_iff]
  intro a ha
  rcases ha with ⟨l, rfl⟩
  let B : Set (ℝ × ℝ) := {z : ℝ × ℝ | |z.2 + z.1 - l| ≤ t}
  have hBm : MeasurableSet B := by
    have hg : Continuous (fun z : ℝ × ℝ => |z.2 + z.1 - l|) := by
      refine continuous_abs.comp ?_
      refine Continuous.sub ?_ continuous_const
      exact continuous_snd.add continuous_fst
    have hset : B = (fun z : ℝ × ℝ => |z.2 + z.1 - l|) ⁻¹' Set.Iic t := by
      ext z
      simp [B, Set.mem_Iic]
    rw [hset]
    exact (isClosed_Iic.measurableSet : MeasurableSet (Set.Iic t)).preimage hg.measurable
  have hE : {x : Ω | |ξ x + ζ x - l| ≤ t} = (fun ω => (ζ ω, ξ ω)) ⁻¹' B := by
    ext ω
    simp [B]
  haveI : MeasureTheory.IsProbabilityMeasure (P.map ξ) := Measure.isProbabilityMeasure_map hξ
  haveI : MeasureTheory.IsProbabilityMeasure (P.map ζ) := Measure.isProbabilityMeasure_map hζ
  have hPair : AEMeasurable (fun ω => (ζ ω, ξ ω)) P := hζ.prodMk hξ
  have hsym : ProbabilityTheory.IndepFun ζ ξ P := hind.symm
  have hjoint : P.map (fun ω => (ζ ω, ξ ω)) = (P.map ζ).prod (P.map ξ) :=
    (indepFun_iff_map_prod_eq_prod_map_map (f := ζ) (g := ξ) hζ hξ).1 hsym
  calc
    P {x : Ω | |ξ x + ζ x - l| ≤ t}
        = P ((fun ω => (ζ ω, ξ ω)) ⁻¹' B) := by rw [hE]
    _ = (P.map (fun ω => (ζ ω, ξ ω))) B :=
          (Measure.map_apply_of_aemeasurable hPair hBm).symm
    _ = ((P.map ζ).prod (P.map ξ)) B := by rw [hjoint]
    _ = ∫⁻ y : ℝ, (P.map ξ) (Prod.mk y ⁻¹' B) ∂(P.map ζ) := by
          exact Measure.prod_apply (μ := P.map ζ) (ν := P.map ξ) hBm
    _ ≤ ∫⁻ _ : ℝ, Submission.Helpers.levyConcentration P ξ t ∂(P.map ζ) := by
          exact lintegral_mono (fun y => by
            have hSmeas : MeasurableSet {x : ℝ | |x + y - l| ≤ t} := by
              have hg : Continuous (fun x : ℝ => |x + y - l|) := by
                refine continuous_abs.comp ?_
                refine Continuous.sub ?_ continuous_const
                exact continuous_id.add continuous_const
              have hset2 : {x : ℝ | |x + y - l| ≤ t} =
                  (fun x : ℝ => |x + y - l|) ⁻¹' Set.Iic t := by
                ext z
                simp [Set.mem_Iic]
              rw [hset2]
              exact (isClosed_Iic.measurableSet : MeasurableSet (Set.Iic t)).preimage hg.measurable
            have hfiber : (P.map ξ) (Prod.mk y ⁻¹' B) ≤
                Submission.Helpers.levyConcentration P ξ t := by
              calc
                (P.map ξ) (Prod.mk y ⁻¹' B) = (P.map ξ) {x : ℝ | |x + y - l| ≤ t} := by
                      have hset : Prod.mk y ⁻¹' B = {x : ℝ | |x + y - l| ≤ t} := by
                        ext z
                        simp [B]
                      rw [hset]
                _ = P {ω : Ω | |ξ ω + y - l| ≤ t} := by
                      rw [Measure.map_apply_of_aemeasurable hξ hSmeas]
                      simp
                _ ≤ Submission.Helpers.levyConcentration P ξ t := by
                      have hmem := Submission.Helpers.le_levyConcentration P ξ t (l - y)
                      -- |ξ ω + y - l| = |ξ ω - (l - y)|
                      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmem
            exact hfiber)
    _ = Submission.Helpers.levyConcentration P ξ t * (P.map ζ) Set.univ := lintegral_const _
    _ = Submission.Helpers.levyConcentration P ξ t := by simp

/-- For `0 < a`, `|a·b − l| ≤ a·t` is equivalent to `|b − l/a| ≤ t`. -/
lemma abs_mul_sub_le_iff_div {a b l t : ℝ} (ha : 0 < a) :
    |a * b - l| ≤ a * t ↔ |b - l / a| ≤ t := by
  have hmul : |a * b - l| = a * |b - l / a| := by
    rw [show a * b - l = a * (b - l / a) by
          rw [mul_sub]
          congr 1
          rw [mul_div_cancel₀]
          exact ha.ne']
    rw [abs_mul, abs_of_pos ha]
  rw [hmul]
  exact mul_le_mul_iff_of_pos_left ha

/-- Scaling a random variable scales the concentration radius:
`cf(a·ξ, a·t) = cf(ξ, t)` for `a > 0`. -/
theorem levyConcentration_scale_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (ξ : Ω → ℝ) {a t : ℝ} (ha : 0 < a) :
    Submission.Helpers.levyConcentration P (fun ω => a * ξ ω) (a * t) =
      Submission.Helpers.levyConcentration P ξ t := by
  classical
  unfold Submission.Helpers.levyConcentration
  apply le_antisymm
  · rw [sSup_le_iff]
    intro b hb
    rcases hb with ⟨l, rfl⟩
    have hset : {x : Ω | |a * ξ x - l| ≤ a * t} =
        {x : Ω | |ξ x - l / a| ≤ t} := by
      ext x
      exact abs_mul_sub_le_iff_div (a := a) (b := ξ x) (l := l) (t := t) ha
    rw [hset]
    exact le_csSup (bddAbove_cf P ξ t) ⟨l / a, rfl⟩
  · rw [sSup_le_iff]
    intro b hb
    rcases hb with ⟨l, rfl⟩
    have hset : {x : Ω | |ξ x - l| ≤ t} =
        {x : Ω | |a * ξ x - a * l| ≤ a * t} := by
      ext x
      change |ξ x - l| ≤ t ↔ |a * ξ x - a * l| ≤ a * t
      rw [abs_mul_sub_le_iff_div (a := a) (b := ξ x) (l := a * l) (t := t) ha]
      rw [show (a * l) / a = l by field_simp [ha.ne']]
    rw [hset]
    exact le_csSup (bddAbove_cf P (fun ω => a * ξ ω) (a * t)) ⟨a * l, rfl⟩

end

end Submission.Concentration
