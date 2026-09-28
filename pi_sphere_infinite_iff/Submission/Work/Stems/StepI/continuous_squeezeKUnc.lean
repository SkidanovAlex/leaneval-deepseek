import Submission.Work.Stems.StepI.SqueezeDefs

/-!
# Joint continuity of the second squeeze homotopy

`Work.Stems.StepI.squeezeK` squeezes the nested concatenation `(δ * sg_w) * rev sg_w` onto `δ`.  As
for `squeezeH`, the two branch expressions `t * ((s - hA t)/(hB t - hA t))` and
`t * (1 - (s - hB t)/(1 - hB t))` are not continuous at `t = 0` (their denominators `t/4` and `t/2`
vanish), although they are only ever used in the region `t > 0`.  On that region they are the
polynomials `4s - 4 + 3t` and `2 - 2s`, and replacing them gives the everywhere continuous
`squeezeKClean` (`squeezeK_eq_squeezeKClean`).  The hypothesis `sg (w, 0) = d₀` is what makes the
two branches agree at the junction `s = hA t`, where the first branch is `δ 1 = d₀`.
-/

open scoped Topology unitInterval
open Work.StemsB

namespace Work.Stems.StepI

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {W : Set X} {d₀ : X}

/-- `squeezeK` with its two non-continuous branch expressions replaced by the polynomials they agree
with on the region where those branches are taken. -/
def squeezeKClean (sg : C(↥W × I, X)) (w : ↥W) (δ : C(I, X)) (t s : ℝ) : X :=
  if s ≤ hA t then δ (clampI (s / hA t))
  else if s ≤ hB t then sg (w, clampI (4 * s - 4 + 3 * t))
  else sg (w, clampI (2 - 2 * s))

theorem squeezeK_eq_squeezeKClean (sg : C(↥W × I, X)) (w : ↥W) (δ : C(I, X))
    {t s : ℝ} (ht : t ∈ Set.Icc 0 1) (hs : s ∈ Set.Icc 0 1) :
    squeezeK sg w δ t s = squeezeKClean sg w δ t s := by
  unfold squeezeK squeezeKClean
  by_cases h1 : s ≤ hA t
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    have htpos : 0 < t := by
      rcases eq_or_lt_of_le ht.1 with h | h
      · exfalso
        rw [← h, hA_zero] at h1
        linarith [not_le.mp h1, hs.2]
      · exact h
    by_cases h2 : s ≤ hB t
    · rw [if_pos h2, if_pos h2]
      have harg : t * ((s - hA t) / (hB t - hA t)) = 4 * s - 4 + 3 * t := by
        rw [hB_sub_hA]
        have htne : t ≠ 0 := ne_of_gt htpos
        field_simp
        unfold hA
        ring
      rw [harg]
    · rw [if_neg h2, if_neg h2]
      have harg : t * (1 - ((s - hB t) / (1 - hB t))) = 2 - 2 * s := by
        have hsub : 1 - hB t = t / 2 := by unfold hB; ring
        have htne : t ≠ 0 := ne_of_gt htpos
        rw [hsub]
        field_simp
        unfold hB
        ring
      rw [harg]

theorem continuous_squeezeKClean_comp {α : Type} [TopologicalSpace α]
    (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    {Wf : α → ↥W} (hW : Continuous Wf) {Δ : α → C(I, X)} (hΔ : Continuous Δ)
    (hΔ1 : ∀ a, (Δ a) 1 = d₀) {T S : α → I} (hT : Continuous T) (hS : Continuous S) :
    Continuous fun a => squeezeKClean sg (Wf a) (Δ a) (T a : ℝ) (S a : ℝ) := by
  have hF : Continuous fun p : C(I, X) × I => p.1 p.2 := continuous_eval
  have ht : Continuous fun a : α => (T a : ℝ) := continuous_subtype_val.comp hT
  have hs : Continuous fun a : α => (S a : ℝ) := continuous_subtype_val.comp hS
  have hAc : Continuous fun a : α => Δ a (clampI ((S a : ℝ) / hA (T a : ℝ))) := by
    refine hF.comp (Continuous.prodMk hΔ ?_)
    exact continuous_clampI.comp (Continuous.div hs (continuous_hA.comp ht)
      (fun a => ne_of_gt (hA_pos (T a).2.2)))
  have hBc : Continuous fun a : α =>
      sg (Wf a, clampI (4 * (S a : ℝ) - 4 + 3 * (T a : ℝ))) := by
    refine sg.continuous.comp (Continuous.prodMk hW ?_)
    exact continuous_clampI.comp (by fun_prop)
  have hCc : Continuous fun a : α => sg (Wf a, clampI (2 - 2 * (S a : ℝ))) := by
    refine sg.continuous.comp (Continuous.prodMk hW ?_)
    exact continuous_clampI.comp (by fun_prop)
  have hBC : Continuous fun a : α =>
      if (S a : ℝ) ≤ hB (T a : ℝ) then
        sg (Wf a, clampI (4 * (S a : ℝ) - 4 + 3 * (T a : ℝ)))
      else sg (Wf a, clampI (2 - 2 * (S a : ℝ))) := by
    refine Continuous.if_le hBc hCc hs (continuous_hB.comp ht) ?_
    intro a ha
    have harg : 4 * (S a : ℝ) - 4 + 3 * (T a : ℝ) = 2 - 2 * (S a : ℝ) := by
      rw [ha]; unfold hB; ring
    rw [harg]
  show Continuous fun a : α =>
      if (S a : ℝ) ≤ hA (T a : ℝ) then Δ a (clampI ((S a : ℝ) / hA (T a : ℝ)))
      else if (S a : ℝ) ≤ hB (T a : ℝ) then
        sg (Wf a, clampI (4 * (S a : ℝ) - 4 + 3 * (T a : ℝ)))
      else sg (Wf a, clampI (2 - 2 * (S a : ℝ)))
  refine Continuous.if_le hAc hBC hs (continuous_hA.comp ht) ?_
  intro a ha
  have hle : (S a : ℝ) ≤ hB (T a : ℝ) := by rw [ha]; exact hA_le_hB (T a).2.1
  rw [if_pos hle]
  have hne : hA (T a : ℝ) ≠ 0 := ne_of_gt (hA_pos (T a).2.2)
  have h1 : (S a : ℝ) / hA (T a : ℝ) = 1 := by rw [ha, div_self hne]
  have h2 : 4 * (S a : ℝ) - 4 + 3 * (T a : ℝ) = 0 := by rw [ha]; unfold hA; ring
  rw [h1, h2, clampI_one, clampI_zero, hΔ1 a, hsg0 (Wf a)]

theorem continuous_squeezeKUnc {X : Type} [TopologicalSpace X] {x₀ : X} {W : Set X} {d₀ : X}
    (sg : ContinuousMap (↥W × unitInterval) X)
    (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀) :
    Continuous (Work.Stems.StepI.squeezeKUnc (x₀ := x₀) (d₀ := d₀) sg) := by
  have hcomp := continuous_squeezeKClean_comp sg hsg0
    (α := ((↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) × I) × I)
    (Wf := fun a => a.1.1.1) (continuous_fst.fst.fst)
    (Δ := fun a => fibCM (x₀ := x₀) (d₀ := d₀) a.1.1.2)
    ((continuous_fibCM (x₀ := x₀) (d₀ := d₀)).comp (by fun_prop))
    (fun a => fibCM_one (x₀ := x₀) (d₀ := d₀) a.1.1.2)
    (T := fun a => a.1.2) (S := fun a => a.2) (by fun_prop) (by fun_prop)
  have heq : (fun q : ((↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) × I) × I =>
        squeezeKUnc (x₀ := x₀) (d₀ := d₀) sg q) =
      fun q => squeezeKClean sg q.1.1.1 (fibCM q.1.1.2) (q.1.2 : ℝ) (q.2 : ℝ) := by
    funext q
    exact squeezeK_eq_squeezeKClean sg q.1.1.1 (fibCM q.1.1.2) q.1.2.2 q.2.2
  show Continuous fun q : ((↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) × I) × I =>
    squeezeKUnc (x₀ := x₀) (d₀ := d₀) sg q
  rw [heq]
  exact hcomp

end

end Work.Stems.StepI
