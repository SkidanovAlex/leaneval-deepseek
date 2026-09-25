/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The crescent estimate for the Bochner–Martinelli potential

Replacing the annulus `2η ≤ ‖u‖ < b` centred at the origin by the annulus
`2η ≤ ‖u - h‖ < b` centred at a point `h` of Euclidean norm `η` changes the integral of a
kernel-type function `ψ` with `‖ψ u‖ ≤ B‖u - h‖^{α-2n}` by at most `C B η^α`.

The proof splits the symmetric difference of the two annuli into the part where
`‖u - h‖ < 4η` — estimated by the ball integral of `|u - h|^{α-2n}` — and the part where
`‖u - h‖ ≥ 4η`, which is contained in the annulus `b - η ≤ ‖u - h‖ < b + η` and is estimated
by `(b + η)^α - (b - η)^α ≤ (2η)^α ≤ 2^α η^α` (subadditivity of `t ↦ t^α`).
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmCz.czAux
import Submission.Work.CR.Flat.Cauchy.bmCz.eucShell_rpow_integral

namespace Work.CR.Flat.Cauchy.bmCz

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

variable {n : ℕ}

/-! ### Translation of radial integrals -/

/-- The integral of `eucNorm (u - c) ^ s` over the ball of radius `ρ` centred at `c`. -/
lemma czCrescent_sub_ball_integral (c : Fin n → ℂ) (s ρ : ℝ) :
    ∫ u in {u : Fin n → ℂ | eucNorm (u - c) < ρ}, eucNorm (u - c) ^ s
      = ∫ w in eucBall (n := n) ρ, eucNorm w ^ s := by
  have himg : (fun x : Fin n → ℂ => x + c) '' eucBall (n := n) ρ
      = {u : Fin n → ℂ | eucNorm (u - c) < ρ} := by
    ext u
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [add_sub_cancel_right] using hw
    · intro hu
      exact ⟨u - c, hu, sub_add_cancel u c⟩
  rw [← himg]
  have h := Work.CR.Flat.Cauchy.setIntegral_translate_euc c
    (fun u : Fin n → ℂ => eucNorm (u - c) ^ s) (eucBall (n := n) ρ)
  simpa only [add_sub_cancel_right] using h.symm

/-- The integral of `eucNorm (u - c) ^ s` over the annulus `a ≤ ‖u - c‖ < b` centred at `c`. -/
lemma czCrescent_sub_shell_integral (c : Fin n → ℂ) (s a b : ℝ) :
    ∫ u in {u : Fin n → ℂ | a ≤ eucNorm (u - c) ∧ eucNorm (u - c) < b}, eucNorm (u - c) ^ s
      = ∫ w in eucShell (n := n) a b, eucNorm w ^ s := by
  have himg : (fun x : Fin n → ℂ => x + c) '' eucShell (n := n) a b
      = {u : Fin n → ℂ | a ≤ eucNorm (u - c) ∧ eucNorm (u - c) < b} := by
    ext u
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [add_sub_cancel_right] using hw
    · intro hu
      exact ⟨u - c, hu, sub_add_cancel u c⟩
  rw [← himg]
  have h := Work.CR.Flat.Cauchy.setIntegral_translate_euc c
    (fun u : Fin n → ℂ => eucNorm (u - c) ^ s) (eucShell (n := n) a b)
  simpa only [add_sub_cancel_right] using h.symm

/-- Integrability of `u ↦ eucNorm (u - c) ^ s` on a ball centred at `c`, when `s > -2n`. -/
lemma czCrescent_sub_ball_integrable (hn : 0 < n) {s : ℝ} (hs : -(2 * (n : ℝ)) < s)
    (c : Fin n → ℂ) {ρ : ℝ} (_hρ : 0 < ρ) :
    IntegrableOn (fun u : Fin n → ℂ => eucNorm (u - c) ^ s)
      {u : Fin n → ℂ | eucNorm (u - c) < ρ} volume := by
  have hmp := MeasureTheory.measurePreserving_add_right (volume : Measure (Fin n → ℂ)) c
  have hkey := hmp.integrableOn_comp_preimage (Homeomorph.addRight c).measurableEmbedding
    (f := fun u : Fin n → ℂ => eucNorm (u - c) ^ s)
    (s := {u : Fin n → ℂ | eucNorm (u - c) < ρ})
  have hpre : (fun x : Fin n → ℂ => x + c) ⁻¹' {u : Fin n → ℂ | eucNorm (u - c) < ρ}
      = eucBall (n := n) ρ := by
    ext w
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, mem_eucBall, add_sub_cancel_right]
  have hcomp : ((fun u : Fin n → ℂ => eucNorm (u - c) ^ s) ∘ (fun x : Fin n → ℂ => x + c))
      = fun w : Fin n → ℂ => eucNorm w ^ s := by
    funext w
    simp only [Function.comp_apply, add_sub_cancel_right]
  rw [hpre, hcomp] at hkey
  exact hkey.mp (Work.CR.Flat.Cauchy.integrableOn_eucNorm_rpow_ball hn hs ρ)

/-- Integrability of `u ↦ eucNorm (u - c) ^ s` on an annulus centred at `c` with inner
radius `a > 0`. -/
lemma czCrescent_sub_shell_integrable (c : Fin n → ℂ) {s a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun u : Fin n → ℂ => eucNorm (u - c) ^ s)
      {u : Fin n → ℂ | a ≤ eucNorm (u - c) ∧ eucNorm (u - c) < b} volume := by
  have hmp := MeasureTheory.measurePreserving_add_right (volume : Measure (Fin n → ℂ)) c
  have hkey := hmp.integrableOn_comp_preimage (Homeomorph.addRight c).measurableEmbedding
    (f := fun u : Fin n → ℂ => eucNorm (u - c) ^ s)
    (s := {u : Fin n → ℂ | a ≤ eucNorm (u - c) ∧ eucNorm (u - c) < b})
  have hpre : (fun x : Fin n → ℂ => x + c) ⁻¹'
        {u : Fin n → ℂ | a ≤ eucNorm (u - c) ∧ eucNorm (u - c) < b}
      = eucShell (n := n) a b := by
    ext w
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, mem_eucShell, add_sub_cancel_right]
  have hcomp : ((fun u : Fin n → ℂ => eucNorm (u - c) ^ s) ∘ (fun x : Fin n → ℂ => x + c))
      = fun w : Fin n → ℂ => eucNorm w ^ s := by
    funext w
    simp only [Function.comp_apply, add_sub_cancel_right]
  rw [hpre, hcomp] at hkey
  exact hkey.mp (Work.CR.Flat.Cauchy.integrableOn_eucNorm_rpow_shell ha hab)

/-! ### The crescent estimate -/

theorem czCrescent {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {B η b : ℝ}, 0 ≤ B → 0 < η → 2 * η ≤ b →
      ∀ {h : Fin n → ℂ}, Work.CR.Flat.Cauchy.eucNorm h = η → ∀ {ψ : (Fin n → ℂ) → ℂ},
      MeasureTheory.AEStronglyMeasurable ψ MeasureTheory.volume →
      (∀ u : Fin n → ℂ,
          ‖ψ u‖ ≤ B * (Work.CR.Flat.Cauchy.eucNorm (u - h)) ^ (α - 2 * (n : ℝ))) →
      ‖(∫ u in Work.CR.Flat.Cauchy.eucShell (2 * η) b, ψ u)
         - (∫ u in {u : Fin n → ℂ | 2 * η ≤ Work.CR.Flat.Cauchy.eucNorm (u - h)
             ∧ Work.CR.Flat.Cauchy.eucNorm (u - h) < b}, ψ u)‖
        ≤ C * B * η ^ α := by
  classical
  let s : ℝ := α - 2 * (n : ℝ)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsneg : s < 0 := by simp only [s]; linarith
  have hsgt : -(2 * (n : ℝ)) < s := by simp only [s]; linarith
  have hsne : s ≠ -(2 * (n : ℝ)) := by
    intro hcon
    have h0 : α = 0 := by simp only [s] at hcon; linarith
    exact absurd h0 hα.ne'
  have hsadd : s + 2 * (n : ℝ) = α := by simp only [s]; ring
  obtain ⟨Crad, hCradpos, hCrad⟩ := eucRadialBound hn s hsgt
  obtain ⟨Csh, hCshpos, hCsh⟩ := eucShell_rpow_integral (n := n) hn
  refine ⟨Crad * 4 ^ α + Csh * 2 ^ α / α, by positivity, ?_⟩
  intro B η b hB hη h2ηb h hh ψ hψm hψbd
  have hηpos : 0 < η := hη
  have h4ηpos : 0 < 4 * η := by linarith
  have hbηpos : 0 < b - η := by linarith
  have hbηle : b - η ≤ b + η := by linarith
  let A0 : Set (Fin n → ℂ) := eucShell (2 * η) b
  let A1 : Set (Fin n → ℂ) := {u : Fin n → ℂ | 2 * η ≤ eucNorm (u - h) ∧ eucNorm (u - h) < b}
  let Inn : Set (Fin n → ℂ) := {u : Fin n → ℂ | eucNorm (u - h) < 4 * η}
  let Out : Set (Fin n → ℂ) := {u : Fin n → ℂ | 4 * η ≤ eucNorm (u - h)}
  let Ann : Set (Fin n → ℂ) :=
    {u : Fin n → ℂ | b - η ≤ eucNorm (u - h) ∧ eucNorm (u - h) < b + η}
  let S : Set (Fin n → ℂ) := (A0 \ A1) ∪ (A1 \ A0)
  let Λ : (Fin n → ℂ) → ℝ := fun u => B * eucNorm (u - h) ^ s
  have hψpt : ∀ u : Fin n → ℂ, ‖ψ u‖ ≤ B * eucNorm (u - h) ^ s := fun u => hψbd u
  -- measurability
  have hA0m : MeasurableSet A0 := measurableSet_eucShell _ _
  have hA1m : MeasurableSet A1 := by
    have heq : A1 = (fun u : Fin n → ℂ => u - h) ⁻¹' eucShell (n := n) (2 * η) b := by
      ext u
      simp [A1, mem_eucShell]
    rw [heq]
    exact (measurableSet_eucShell (n := n) (2 * η) b).preimage
      ((continuous_id.sub continuous_const).measurable)
  have hInnm : MeasurableSet Inn :=
    (isOpen_lt (continuous_eucNorm.comp (continuous_id.sub continuous_const))
      continuous_const).measurableSet
  have hOutm : MeasurableSet Out :=
    (isClosed_le continuous_const (continuous_eucNorm.comp (continuous_id.sub continuous_const))
      ).measurableSet
  have hAnnm : MeasurableSet Ann :=
    ((isClosed_le continuous_const (continuous_eucNorm.comp (continuous_id.sub continuous_const))
        ).measurableSet).inter
      ((isOpen_lt (continuous_eucNorm.comp (continuous_id.sub continuous_const))
        continuous_const).measurableSet)
  have hSm : MeasurableSet S := (hA0m.diff hA1m).union (hA1m.diff hA0m)
  -- finite volume
  have hA0fin : volume A0 < ⊤ :=
    Work.CR.Flat.Cauchy.volume_lt_top_of_subset_eucNorm (M := b) (fun x hx => le_of_lt hx.2)
  have hA1fin : volume A1 < ⊤ := by
    refine Work.CR.Flat.Cauchy.volume_lt_top_of_subset_eucNorm (M := b + η) (fun x hx => ?_)
    have h1 : eucNorm x ≤ eucNorm (x - h) + eucNorm h := by
      have := eucNorm_add_le (x - h) h
      simpa only [sub_add_cancel] using this
    rw [hh] at h1
    linarith [h1, hx.2]
  -- integrability of ψ on the two annuli
  have hψA0 : IntegrableOn ψ A0 volume := by
    refine Work.CR.Flat.Cauchy.integrableOn_of_norm_le_const_aux hA0m hA0fin
      (hψm.mono_measure Measure.restrict_le_self) (M := B * η ^ s) (fun x hx => ?_)
    have hxge : η ≤ eucNorm (x - h) := by
      have h1 := abs_eucNorm_sub_le x h
      rw [hh] at h1
      have h2 : η ≤ eucNorm x := by linarith [hx.1]
      have h3 : |eucNorm x - η| = eucNorm x - η := abs_of_nonneg (by linarith)
      linarith [h1, h2, h3, hx.1]
    calc ‖ψ x‖ ≤ B * eucNorm (x - h) ^ s := hψpt x
      _ ≤ B * η ^ s := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hηpos hxge hsneg.le) hB
  have hψA1 : IntegrableOn ψ A1 volume := by
    refine Work.CR.Flat.Cauchy.integrableOn_of_norm_le_const_aux hA1m hA1fin
      (hψm.mono_measure Measure.restrict_le_self) (M := B * (2 * η) ^ s) (fun x hx => ?_)
    have h2ηpos : 0 < 2 * η := by linarith
    calc ‖ψ x‖ ≤ B * eucNorm (x - h) ^ s := hψpt x
      _ ≤ B * (2 * η) ^ s := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos h2ηpos hx.1 hsneg.le) hB
  have hψA0' : IntegrableOn ψ (A0 \ A1) volume := hψA0.mono_set Set.sdiff_subset
  have hψA1' : IntegrableOn ψ (A1 \ A0) volume := hψA1.mono_set Set.sdiff_subset
  -- the difference of the two integrals is the integral over the symmetric difference
  have hsplit1 := setIntegral_sdiff (f := ψ) (s := A0) (t := A1 ∩ A0)
    (hA1m.inter hA0m) hψA0 Set.inter_subset_right
  rw [Set.sdiff_inter_self_eq_sdiff] at hsplit1
  have hsplit2 := setIntegral_sdiff (f := ψ) (s := A1) (t := A0 ∩ A1)
    (hA0m.inter hA1m) hψA1 Set.inter_subset_right
  rw [Set.sdiff_inter_self_eq_sdiff] at hsplit2
  have hdiff : (∫ u in A0, ψ u) - (∫ u in A1, ψ u)
      = (∫ u in A0 \ A1, ψ u) - (∫ u in A1 \ A0, ψ u) := by
    rw [hsplit1, hsplit2, Set.inter_comm A1 A0]
    abel
  -- symmetrise the two differences
  have htri : ‖(∫ u in A0 \ A1, ψ u) - (∫ u in A1 \ A0, ψ u)‖
      ≤ (∫ u in A0 \ A1, ‖ψ u‖) + (∫ u in A1 \ A0, ‖ψ u‖) := by
    have h1 : ‖∫ u in A0 \ A1, ψ u‖ ≤ ∫ u in A0 \ A1, ‖ψ u‖ :=
      Work.CR.Flat.Cauchy.norm_setIntegral_le_of_norm_le' (hA0m.diff hA1m)
        hψA0'.norm (fun u _ => le_rfl)
    have h2 : ‖∫ u in A1 \ A0, ψ u‖ ≤ ∫ u in A1 \ A0, ‖ψ u‖ :=
      Work.CR.Flat.Cauchy.norm_setIntegral_le_of_norm_le' (hA1m.diff hA0m)
        hψA1'.norm (fun u _ => le_rfl)
    linarith [norm_sub_le (∫ u in A0 \ A1, ψ u) (∫ u in A1 \ A0, ψ u), h1, h2]
  have hSdisj : Disjoint (A0 \ A1) (A1 \ A0) := by
    rw [Set.disjoint_left]
    intro u hu hu'
    exact hu.2 hu'.1
  have hSunion : (∫ u in S, ‖ψ u‖)
      = (∫ u in A0 \ A1, ‖ψ u‖) + (∫ u in A1 \ A0, ‖ψ u‖) :=
    setIntegral_union hSdisj (hA1m.diff hA0m) hψA0'.norm hψA1'.norm
  -- the majorant and its integrability
  have hΛnn : ∀ u : Fin n → ℂ, 0 ≤ Λ u :=
    fun u => mul_nonneg hB (Real.rpow_nonneg (eucNorm_nonneg _) _)
  have hΛmeas : AEStronglyMeasurable Λ volume :=
    (((measurable_eucNorm_rpow s).comp (measurable_id.sub_const h)).const_mul B).aestronglyMeasurable
  have hΛInn : IntegrableOn Λ Inn volume :=
    (czCrescent_sub_ball_integrable hn hsgt h h4ηpos).const_mul B
  have hΛAnn : IntegrableOn Λ Ann volume :=
    (czCrescent_sub_shell_integrable h hbηpos hbηle).const_mul B
  -- the splitting of the symmetric difference
  have hInnOut : Inn ∪ Out = Set.univ := by
    ext u
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    rcases lt_or_ge (eucNorm (u - h)) (4 * η) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hSsplit : S = (S ∩ Inn) ∪ (S ∩ Out) := by
    ext u
    constructor
    · intro hu
      rcases lt_or_ge (eucNorm (u - h)) (4 * η) with h | h
      · exact Or.inl ⟨hu, h⟩
      · exact Or.inr ⟨hu, h⟩
    · rintro (⟨hu, _⟩ | ⟨hu, _⟩) <;> exact hu
  have hSdisjIO : Disjoint (S ∩ Inn) (S ∩ Out) := by
    rw [Set.disjoint_left]
    intro u hu hu'
    have h1 : eucNorm (u - h) < 4 * η := hu.2
    have h2 : 4 * η ≤ eucNorm (u - h) := hu'.2
    linarith
  -- outer inclusion
  have hSOut : S ∩ Out ⊆ Ann := by
    rintro u ⟨huS, huO⟩
    change u ∈ (A0 \ A1) ∪ (A1 \ A0) at huS
    rw [Set.mem_union] at huS
    have huO' : 4 * η ≤ eucNorm (u - h) := huO
    rcases huS with huS | huS
    · obtain ⟨huA0, huA1⟩ := huS
      have h2ηh : 2 * η ≤ eucNorm (u - h) := by linarith
      have hge : b ≤ eucNorm (u - h) := by
        by_contra hlt
        rw [not_le] at hlt
        exact huA1 ⟨h2ηh, hlt⟩
      have hle : eucNorm (u - h) ≤ eucNorm u + eucNorm h := eucNorm_sub_le u h
      rw [hh] at hle
      exact ⟨by linarith, by linarith [huA0.2]⟩
    · obtain ⟨huA1, huA0⟩ := huS
      have htri1 : eucNorm u ≤ eucNorm (u - h) + eucNorm h := by
        have := eucNorm_add_le (u - h) h
        simpa only [sub_add_cancel] using this
      have htri2 : eucNorm (u - h) ≤ eucNorm u + eucNorm h := eucNorm_sub_le u h
      rw [hh] at htri1 htri2
      have hge : b ≤ eucNorm u := by
        by_contra hlt
        rw [not_le] at hlt
        exact huA0 ⟨by linarith, hlt⟩
      exact ⟨by linarith, by linarith [huA1.2]⟩
  have hΛSInn : IntegrableOn Λ (S ∩ Inn) volume := hΛInn.mono_set Set.inter_subset_right
  have hΛSOut : IntegrableOn Λ (S ∩ Out) volume := hΛAnn.mono_set hSOut
  have hΛS : IntegrableOn Λ S volume := by
    rw [hSsplit]
    exact hΛSInn.union hΛSOut
  have hψnS : IntegrableOn (fun u : Fin n → ℂ => ‖ψ u‖) S volume := by
    refine Integrable.mono' hΛS (hψm.norm.mono_measure Measure.restrict_le_self) ?_
    filter_upwards with u
    simpa only [Real.norm_of_nonneg (norm_nonneg (ψ u))] using hψpt u
  have hLeS : (∫ u in S, ‖ψ u‖) ≤ ∫ u in S, Λ u :=
    setIntegral_mono_on hψnS hΛS hSm (fun u _ => hψpt u)
  have hΛSsplit : (∫ u in S, Λ u) = (∫ u in S ∩ Inn, Λ u) + (∫ u in S ∩ Out, Λ u) := by
    have h := setIntegral_union (f := Λ) hSdisjIO (hSm.inter hOutm) hΛSInn hΛSOut
    rwa [← hSsplit] at h
  have hmonoInn : (∫ u in S ∩ Inn, Λ u) ≤ ∫ u in Inn, Λ u :=
    setIntegral_mono_set hΛInn (Filter.Eventually.of_forall hΛnn)
      (Filter.Eventually.of_forall (fun u hu => hu.2))
  have hmonoOut : (∫ u in S ∩ Out, Λ u) ≤ ∫ u in Ann, Λ u :=
    setIntegral_mono_set hΛAnn (Filter.Eventually.of_forall hΛnn)
      (Filter.Eventually.of_forall hSOut)
  -- the two numerical bounds
  have hInnBound : ∫ u in Inn, Λ u ≤ B * Crad * (4 * η) ^ α := by
    have heq : ∫ u in Inn, Λ u = B * ∫ w in eucBall (n := n) (4 * η), eucNorm w ^ s := by
      change ∫ u in {u : Fin n → ℂ | eucNorm (u - h) < 4 * η}, B * eucNorm (u - h) ^ s
          = B * ∫ w in eucBall (n := n) (4 * η), eucNorm w ^ s
      rw [MeasureTheory.integral_const_mul, czCrescent_sub_ball_integral h s (4 * η)]
    rw [heq]
    have h4 := hCrad (4 * η) h4ηpos
    rw [hsadd] at h4
    calc B * ∫ w in eucBall (n := n) (4 * η), eucNorm w ^ s
        ≤ B * (Crad * (4 * η) ^ α) := mul_le_mul_of_nonneg_left h4 hB
      _ = B * Crad * (4 * η) ^ α := by ring
  have hAnnBound : ∫ u in Ann, Λ u ≤ B * (Csh * 2 ^ α * η ^ α / α) := by
    have heq : ∫ u in Ann, Λ u
        = B * ∫ w in eucShell (n := n) (b - η) (b + η), eucNorm w ^ s := by
      change ∫ u in {u : Fin n → ℂ | b - η ≤ eucNorm (u - h) ∧ eucNorm (u - h) < b + η},
            B * eucNorm (u - h) ^ s
          = B * ∫ w in eucShell (n := n) (b - η) (b + η), eucNorm w ^ s
      rw [MeasureTheory.integral_const_mul, czCrescent_sub_shell_integral h s (b - η) (b + η)]
    rw [heq]
    have hshell := hCsh (s := s) hsne (a := b - η) (b := b + η) hbηpos hbηle
    rw [hsadd] at hshell
    rw [hshell]
    have hbnd : (b + η) ^ α - (b - η) ^ α ≤ 2 ^ α * η ^ α := by
      have h1 := Real.rpow_add_le_add_rpow (p := α) (a := b - η) (b := 2 * η)
        (by linarith) (by linarith) hα.le hα1.le
      rw [show b - η + 2 * η = b + η from by ring] at h1
      have h2 : (2 * η) ^ α = 2 ^ α * η ^ α := Real.mul_rpow (by norm_num) hη.le
      rw [h2] at h1
      linarith
    calc B * (Csh * (((b + η) ^ α - (b - η) ^ α) / α))
        ≤ B * (Csh * ((2 ^ α * η ^ α) / α)) := by
          refine mul_le_mul_of_nonneg_left ?_ hB
          exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hbnd hα.le) hCshpos.le
      _ = B * (Csh * 2 ^ α * η ^ α / α) := by ring
  -- assembly
  show ‖(∫ u in A0, ψ u) - (∫ u in A1, ψ u)‖
      ≤ (Crad * 4 ^ α + Csh * 2 ^ α / α) * B * η ^ α
  calc ‖(∫ u in A0, ψ u) - (∫ u in A1, ψ u)‖
      = ‖(∫ u in A0 \ A1, ψ u) - (∫ u in A1 \ A0, ψ u)‖ := by rw [hdiff]
    _ ≤ (∫ u in A0 \ A1, ‖ψ u‖) + (∫ u in A1 \ A0, ‖ψ u‖) := htri
    _ = ∫ u in S, ‖ψ u‖ := hSunion.symm
    _ ≤ ∫ u in S, Λ u := hLeS
    _ = (∫ u in S ∩ Inn, Λ u) + (∫ u in S ∩ Out, Λ u) := hΛSsplit
    _ ≤ (∫ u in Inn, Λ u) + (∫ u in Ann, Λ u) := add_le_add hmonoInn hmonoOut
    _ ≤ B * Crad * (4 * η) ^ α + B * (Csh * 2 ^ α * η ^ α / α) :=
        add_le_add hInnBound hAnnBound
    _ = (Crad * 4 ^ α + Csh * 2 ^ α / α) * B * η ^ α := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hη.le]
        field_simp

end

end Work.CR.Flat.Cauchy.bmCz
