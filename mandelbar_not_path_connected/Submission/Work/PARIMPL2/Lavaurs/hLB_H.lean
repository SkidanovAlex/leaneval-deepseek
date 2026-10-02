import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.FlowerGlue2.Defs
import Submission.Work.FlowerGlue2.AttrNorm
import Submission.Work.FlowerGlue2.box_deep_of_transient_bound
import Submission.Work.PARIMPL2.Lavaurs.psi_w0_re_le
import Submission.Work.PARIMPL2.Lavaurs.deep_tail_subset_pa
import Submission.Work.PARIMPL2.Lavaurs.deep_tail_preimage_shift
import Submission.Work.PARIMPL2.Lavaurs.orbit_enters_deep
import Submission.Work.PARIMPL2.Lavaurs.deep_level_bound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Lavaurs

/-- **The deep tail is contained in the petal** (auxiliary form): the `cover` field, the
`Ψ_ends` field and the chart asymptotics of the repelling coordinate force the whole deep
half-plane `{M₀ < Re (w0 P ·)}` into `Pa`. -/
private theorem deep_tail_subset_pa_aux {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (P : Work.PARIMPL.ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁)
    {Re : ℝ} (hRe : ∀ w : ℂ, w.re < -Re → Re < |w.im| → fl.Ψ w ∈ fl.Pa)
    {Rψ Cψ : ℝ} (hCψ0 : 0 ≤ Cψ)
    (hψ : ∀ w : ℂ, w.re < -Rψ → |w.im| ≤ Re →
      (Work.PARIMPL2.w0 P (fl.Ψ w)).re ≤ w.re + Cψ * (1 + Real.log (2 + ‖w‖))) :
    ∃ M₀ : ℝ, ∀ z : ℂ, M₀ < (Work.PARIMPL2.w0 P z).re → z ∈ fl.Pa := by
  obtain ⟨Rc, hRcψ, hRcRe, hRcbig, hRcbig2, hRc1⟩ : ∃ Rc : ℝ,
      Rψ ≤ Rc ∧ Re + 1 ≤ Rc ∧ 16 * Cψ ^ 2 + Re + 4 ≤ Rc ∧ 2 * Cψ + Re + 4 ≤ Rc ∧
        1 ≤ Rc := by
    refine ⟨max (max Rψ (Re + 1))
      (max (max (16 * Cψ ^ 2 + Re + 4) (2 * Cψ + Re + 4)) 1), ?_, ?_, ?_, ?_, ?_⟩
    · exact le_trans (le_max_left Rψ (Re + 1)) (le_max_left _ _)
    · exact le_trans (le_max_right Rψ (Re + 1)) (le_max_left _ _)
    · exact le_trans (le_trans (le_max_left (16 * Cψ ^ 2 + Re + 4) (2 * Cψ + Re + 4))
        (le_max_left _ _)) (le_max_right _ _)
    · exact le_trans (le_trans (le_max_right (16 * Cψ ^ 2 + Re + 4) (2 * Cψ + Re + 4))
        (le_max_left _ _)) (le_max_right _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hRcpos : 0 < Rc := lt_of_lt_of_le one_pos hRc1
  obtain ⟨r, hr0, hcov⟩ := fl.cover Rc
  have hspos : 0 < ‖P.s c₀‖ := norm_pos_iff.mpr (P.s_ne c₀ (Metric.mem_ball_self P.hρ₀))
  have hclaim : ∀ w : ℂ, w.re < -Rc → |w.im| ≤ Re →
      (Work.PARIMPL2.w0 P (fl.Ψ w)).re ≤ 0 := by
    intro w hw1 hw2
    have hRe0 : 0 ≤ Re := le_trans (abs_nonneg w.im) hw2
    have h1 : (Work.PARIMPL2.w0 P (fl.Ψ w)).re ≤ w.re + Cψ * (1 + Real.log (2 + ‖w‖)) :=
      hψ w (by linarith [hw1, hRcψ]) hw2
    have h3 := Complex.norm_le_abs_re_add_abs_im w
    have h4 : |w.re| = -w.re := abs_of_neg (by linarith [hw1, hRcpos])
    have h2 : ‖w‖ ≤ -w.re + Re := by linarith [h3, h4, hw2]
    have h5 : Real.log (2 + ‖w‖) ≤ Real.log (2 + (-w.re + Re)) :=
      Real.log_le_log (by linarith [norm_nonneg w]) (by linarith [h2])
    have h6 : Cψ * Real.log (2 + (-w.re + Re)) ≤ -w.re - Cψ := by
      have hL1 : 1 ≤ 2 + (-w.re + Re) := by linarith [hw1, hRcRe, hRe0]
      have hL2 : 16 * Cψ ^ 2 ≤ 2 + (-w.re + Re) := by linarith [hw1, hRcbig]
      have h7 := Work.FlowerGlue2.bdtb_const_mul_log_le_half (a := Cψ)
        (L := 2 + (-w.re + Re)) hCψ0 hL1 hL2
      have h8 : (2 + (-w.re + Re)) / 2 ≤ -w.re - Cψ := by linarith [hw1, hRcbig2]
      linarith
    have h9 : Cψ * Real.log (2 + ‖w‖) ≤ Cψ * Real.log (2 + (-w.re + Re)) :=
      mul_le_mul_of_nonneg_left h5 hCψ0
    linarith [h1, h6, h9]
  refine ⟨max (‖P.s c₀‖ / r + 1) 1, ?_⟩
  intro z hz
  have hz_ne : z ≠ d.z₁ := by
    intro h
    rw [h] at hz
    simp [Work.PARIMPL2.w0] at hz
    linarith
  have hstrong : ‖P.s c₀‖ / r + 1 < (Work.PARIMPL2.w0 P z).re :=
    lt_of_le_of_lt (le_max_left _ _) hz
  have hdist : ‖z - d.z₁‖ = ‖P.s c₀‖ / ‖Work.PARIMPL2.w0 P z‖ := by
    have h1 : z = d.z₁ - P.s c₀ / Work.PARIMPL2.w0 P z :=
      Work.FlowerGlue2.chart_recovery (P := P) hz_ne
    have h2 : z - d.z₁ = -(P.s c₀ / Work.PARIMPL2.w0 P z) := by
      conv_lhs => rw [h1]
      ring
    rw [h2, norm_neg, norm_div]
  have hbig : ‖P.s c₀‖ / r < ‖Work.PARIMPL2.w0 P z‖ := by
    have h3 : ‖P.s c₀‖ / r < (Work.PARIMPL2.w0 P z).re := by linarith
    linarith [Complex.re_le_norm (Work.PARIMPL2.w0 P z)]
  have hlt : ‖z - d.z₁‖ < r := by
    have hw0pos : 0 < ‖Work.PARIMPL2.w0 P z‖ :=
      norm_pos_iff.mpr (Work.FlowerGlue2.w0_ne_zero hz_ne)
    rw [hdist, div_lt_iff₀ hw0pos]
    have h4 : r * (‖P.s c₀‖ / r) = ‖P.s c₀‖ := by field_simp
    have h5 : r * (‖P.s c₀‖ / r) < r * ‖Work.PARIMPL2.w0 P z‖ :=
      mul_lt_mul_of_pos_left hbig hr0
    linarith
  have hne : 0 < ‖z - d.z₁‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz_ne)
  rcases hcov z hne hlt with hzPa | ⟨w, hw, hwz⟩
  · exact hzPa
  · by_cases him : |w.im| ≤ Re
    · have h2 := hclaim w hw him
      rw [hwz] at h2
      have h3 : (1 : ℝ) ≤ (Work.PARIMPL2.w0 P z).re := le_trans (le_max_right _ _) hz.le
      linarith
    · push_neg at him
      have h2 : fl.Ψ w ∈ fl.Pa := hRe w (by linarith [hw, hRcRe]) him
      rw [hwz] at h2
      exact h2

/-- **The `|Im φa| ≤ H`-restricted uniform transient bound** (`NOTES_LEAD_mandelbar_wire.md` §A.4
R1, item (1) of the lead's directive): for an **arbitrary** flower (in particular SatFree's wide,
saturating one — so nothing here may assume `Re κ₀ > 0`), the *shallow* part of the petal carries
bounded `φa`-level, provided the height `|Im φa|` is bounded.

The unrestricted form (`Re (w0 P z) ≤ M → Re (φa z) ≤ M'`, no height restriction) is **false** on a
wide petal when `κ₀ < 0`; the height restriction is exactly what the deepening
(`Work.PARIMPL2.Lavaurs.box_deep_H`) preserves along the orbit, since `φa (F z) = φa z + 1` shifts
only the real part.

Proof route (the lead's): from `AttrCompare.asymp`,
`φa z = w0 z - κ₀ log (w0 z) + sa + O(1/Re w0 z)`, so a bounded `|Im φa z|` forces
`|Im (w0 P z)| ≲ H + C log |w0 P z|`; with `Re (w0 P z) ≤ M` this bounds `|w0 P z|` (a
self-referential logarithmic bound) and hence bounds `Re (φa z)` above.

**Caveat raised in review (check this first).**  The `AttrCompare`/`ParabolicFlowerFix` fields do
*not* by themselves exclude the following family: a point `z ∈ fl.Pa` at bounded distance from a
*preimage* `z_* ≠ z₁` of `z₁` (so `Re (w0 P z)` is bounded) whose image `F z` is very deep (so
`Re (φa z) = Re (φa (F z)) - 1` is large), while `Im φa` is orbit-invariant and hence still bounded.
If such a configuration is consistent with the fields of `ParabolicFlowerFix` and `AttrCompare`,
this statement is **false** and must be restated with a smallness hypothesis on the shallow part of
`Pa` (e.g. `Pa` avoids a neighbourhood of the preimages of `z₁`).  Please settle this first; if it
is false, write `Lavaurs/NOTES_FALSE_hLB_H.md` with the counterexample, as for
`transit_model`/`transit_exit`. -/
theorem hLB_H {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁)
    (A : Work.FlowerGlue2.AttrCompare P fl.Pa fl.φa) :
    ∀ H : ℝ, ∃ M M' : ℝ, A.N ≤ M ∧ ∀ z ∈ fl.Pa,
      (Work.PARIMPL2.w0 P z).re ≤ M → |(fl.φa z).im| ≤ H → (fl.φa z).re ≤ M' := by
  intro H
  -- the repelling coordinate pins the deep tail of the petal (`cover` + the chart asymptotics)
  obtain ⟨Re, hRe⟩ := fl.Ψ_ends
  obtain ⟨Rψ, Cψ, hCψ0, hψ⟩ := psi_w0_re_le P fl Re
  obtain ⟨M₀, hM₀⟩ := deep_tail_subset_pa_aux P fl hRe hCψ0 hψ
  -- the deep tail is forward-deepening: a deep enough point has a preimage at any prescribed depth
  obtain ⟨M₁, C, hC0, hpre'⟩ := deep_tail_preimage_shift P
  -- the (deep) case of the transient bound
  obtain ⟨Mlev, hlev⟩ := deep_level_bound P fl A (max (max M₀ (M₁ + C)) (A.N + 1) + C) H
  classical
  set T : ℝ := max (max M₀ (M₁ + C)) (A.N + 1) with hT
  have hT₀ : M₀ ≤ T := le_trans (le_max_left _ _) (le_max_left _ _)
  have hT₁ : M₁ + C ≤ T := le_trans (le_max_right _ _) (le_max_left _ _)
  have hTN : A.N + 1 ≤ T := le_max_right _ _
  have hdeep : ∀ z ∈ fl.Pa, A.N < (Work.PARIMPL2.w0 P z).re → (Work.PARIMPL2.w0 P z).re ≤ T + C →
      |(fl.φa z).im| ≤ H → (fl.φa z).re ≤ Mlev := hlev
  refine ⟨T, Mlev, by linarith, ?_⟩
  intro z hz hle hHφ
  have hmaps : ∀ k : ℕ, ((Work.PARIMPL.Ft c₀)^[k] z) ∈ fl.Pa := fun k =>
    Work.FatouCoord.mapsTo_iterate_of_mapsTo fl.mapsTo_Pa k hz
  have hinj : ∀ a ∈ fl.Pa, ∀ b ∈ fl.Pa, Work.PARIMPL.Ft c₀ a = Work.PARIMPL.Ft c₀ b → a = b := by
    intro a ha b hb hab
    apply A.φa_inj ha hb
    have h1 : fl.φa (Work.PARIMPL.Ft c₀ a) = fl.φa (Work.PARIMPL.Ft c₀ b) := by rw [hab]
    rw [A.φa_shift a ha, A.φa_shift b hb] at h1
    linear_combination h1
  by_cases hd : A.N < (Work.PARIMPL2.w0 P z).re
  · exact hdeep z hz hd (by linarith) hHφ
  · push_neg at hd
    -- the first time the chart coordinate crosses `T`
    obtain ⟨n, hn⟩ := orbit_enters_deep P fl z hz T
    set p : ℕ → Prop := fun k => T < (Work.PARIMPL2.w0 P ((Work.PARIMPL.Ft c₀)^[k] z)).re with hpdef
    have hp : ∃ k, p k := ⟨n, hn⟩
    set n₀ : ℕ := Nat.find hp with hn₀
    have hspec : T < (Work.PARIMPL2.w0 P ((Work.PARIMPL.Ft c₀)^[n₀] z)).re := Nat.find_spec hp
    have hmin : ∀ m < n₀, (Work.PARIMPL2.w0 P ((Work.PARIMPL.Ft c₀)^[m] z)).re ≤ T := by
      intro m hm
      by_contra hcon
      push_neg at hcon
      exact Nat.find_min hp hm hcon
    have hn₀pos : 0 < n₀ := by
      rcases Nat.eq_zero_or_pos n₀ with h0 | h0
      · exfalso
        rw [h0] at hspec
        simp only [Function.iterate_zero, id_eq] at hspec
        linarith
      · exact h0
    -- the crossing cannot jump over the (already deep) threshold
    have hjump : (Work.PARIMPL2.w0 P ((Work.PARIMPL.Ft c₀)^[n₀] z)).re ≤ T + C := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨y, hy1, hy2, hyF⟩ := hpre' ((Work.PARIMPL.Ft c₀)^[n₀] z) (by linarith [hspec, hT₁])
      have hyT : T < (Work.PARIMPL2.w0 P y).re := by linarith
      have hyPa : y ∈ fl.Pa := hM₀ y (by linarith [hyT, hT₀])
      have hzPa : ((Work.PARIMPL.Ft c₀)^[n₀ - 1] z) ∈ fl.Pa := hmaps (n₀ - 1)
      have hlast : Work.PARIMPL.Ft c₀ ((Work.PARIMPL.Ft c₀)^[n₀ - 1] z)
          = ((Work.PARIMPL.Ft c₀)^[n₀] z) := by
        have hsucc : (n₀ - 1).succ = n₀ := by omega
        rw [← Function.iterate_succ_apply' (Work.PARIMPL.Ft c₀) (n₀ - 1) z, hsucc]
      have heq : y = ((Work.PARIMPL.Ft c₀)^[n₀ - 1] z) := hinj y hyPa _ hzPa (by rw [hyF, hlast])
      have hmin' : (Work.PARIMPL2.w0 P ((Work.PARIMPL.Ft c₀)^[n₀ - 1] z)).re ≤ T :=
        hmin (n₀ - 1) (Nat.sub_lt hn₀pos (by norm_num))
      rw [heq] at hyT
      linarith
    -- the deep estimate at the crossing point, transported back along the orbit
    have hzPa : ((Work.PARIMPL.Ft c₀)^[n₀] z) ∈ fl.Pa := hmaps n₀
    have hdeepn : A.N < (Work.PARIMPL2.w0 P ((Work.PARIMPL.Ft c₀)^[n₀] z)).re := by
      linarith [hspec, hTN]
    have hheight : |(fl.φa ((Work.PARIMPL.Ft c₀)^[n₀] z)).im| ≤ H := by
      have hshift := fl.φa_shift_iterate hz n₀
      rw [hshift]; simp [hHφ]
    have hlevel : (fl.φa ((Work.PARIMPL.Ft c₀)^[n₀] z)).re ≤ Mlev :=
      hdeep _ hzPa hdeepn hjump hheight
    have hshift := fl.φa_shift_iterate hz n₀
    have hre : (fl.φa z).re + (n₀ : ℝ) = (fl.φa ((Work.PARIMPL.Ft c₀)^[n₀] z)).re := by
      rw [hshift]; simp [Complex.add_re]
    linarith

end Work.PARIMPL2.Lavaurs
