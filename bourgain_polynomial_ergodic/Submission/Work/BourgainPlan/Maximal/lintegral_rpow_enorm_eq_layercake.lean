import Mathlib

open MeasureTheory

namespace Work.BourgainPlan.Maximal

/-- Layer cake for the truncations: the supremum of `(g ⊓ n)^p` over `n` is `g^p`. -/
private lemma trunc_rpow_iSup {p : ℝ} (hp : 0 < p) (a : ENNReal) :
    (⨆ n : ℕ, ENNReal.rpow (a ⊓ (n:ENNReal)) p) = ENNReal.rpow a p := by
  have key : (⨆ n : ℕ, ENNReal.rpow (n : ENNReal) p) = ⊤ := by
    apply iSup_eq_top.mpr
    intro b hb
    obtain ⟨n, hn⟩ := exists_nat_gt (b.toReal ^ (1/p))
    refine ⟨n, ?_⟩
    rw [show b = ENNReal.ofReal b.toReal from (ENNReal.ofReal_toReal hb.ne).symm]
    have h1 : ENNReal.rpow (ENNReal.ofReal (n:ℝ)) p = ENNReal.ofReal ((n:ℝ)^p) :=
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le
    rw [← ENNReal.ofReal_natCast n, h1,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg]
    calc b.toReal = (b.toReal ^ (1/p)) ^ p := by
          rw [← Real.rpow_mul ENNReal.toReal_nonneg, one_div_mul_cancel hp.ne', Real.rpow_one]
      _ < (n:ℝ) ^ p := Real.rpow_lt_rpow (Real.rpow_nonneg ENNReal.toReal_nonneg _) hn hp
  by_cases htop : a = ⊤
  · subst htop
    simp only [top_inf_eq]
    rw [show (⊤ : ENNReal).rpow p = ⊤ from ENNReal.top_rpow_of_pos hp]
    exact key
  · apply le_antisymm
    · apply iSup_le; intro n
      exact ENNReal.rpow_le_rpow inf_le_left hp.le
    · obtain ⟨n, hn⟩ := exists_nat_ge a.toReal
      have hle : a ≤ (n:ENNReal) := by
        have h2 : a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal htop).symm
        rw [h2, ← ENNReal.ofReal_natCast n]
        exact ENNReal.ofReal_le_ofReal hn
      have h3 : a ⊓ (n:ENNReal) = a := inf_eq_left.mpr hle
      have h4 : ENNReal.rpow (a ⊓ (n:ENNReal)) p ≤
          ⨆ m : ℕ, ENNReal.rpow (a ⊓ (m:ENNReal)) p :=
        le_iSup (fun m : ℕ => ENNReal.rpow (a ⊓ (m:ENNReal)) p) n
      rw [h3] at h4
      exact h4

/-- Layer cake for the truncations: the level sets `{t < g}` are the increasing union
of the level sets `{t < g ⊓ n}`. -/
private lemma trunc_meas_iSup {β : Type*} [MeasurableSpace β] {ν : MeasureTheory.Measure β}
    {g : β → ENNReal} (t : ℝ) (a : ENNReal) :
    (⨆ n : ℕ, ν {x : β | ENNReal.ofReal t < g x ⊓ (n:ENNReal)} * a)
      = ν {x : β | ENNReal.ofReal t < g x} * a := by
  have hmono : Monotone (fun n : ℕ => {x : β | ENNReal.ofReal t < g x ⊓ (n:ENNReal)}) := by
    intro i j hij x hx
    exact lt_of_lt_of_le hx (inf_le_inf_left (g x) (Nat.cast_le.mpr hij))
  have hunion : (⋃ n : ℕ, {x : β | ENNReal.ofReal t < g x ⊓ (n:ENNReal)})
      = {x : β | ENNReal.ofReal t < g x} := by
    ext x
    rw [Set.mem_iUnion]
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩; exact lt_of_lt_of_le hn inf_le_left
    · intro hx
      by_cases htop : g x = ⊤
      · obtain ⟨n, hn⟩ : ∃ n : ℕ, ENNReal.ofReal t < (n : ENNReal) := by
          by_cases ht : 0 < t
          · obtain ⟨n, hn⟩ := exists_nat_gt t
            refine ⟨n, ?_⟩
            rw [← ENNReal.ofReal_natCast n, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt ht)]
            exact hn
          · refine ⟨1, ?_⟩
            rw [not_lt] at ht
            rw [ENNReal.ofReal_eq_zero.mpr ht]
            simp
        refine ⟨n, ?_⟩
        rw [htop, top_inf_eq]
        exact hn
      · obtain ⟨n, hn⟩ := exists_nat_ge (g x).toReal
        have hle : g x ≤ (n:ENNReal) := by
          have h2 : g x = ENNReal.ofReal (g x).toReal := (ENNReal.ofReal_toReal htop).symm
          rw [h2, ← ENNReal.ofReal_natCast n]
          exact ENNReal.ofReal_le_ofReal hn
        refine ⟨n, ?_⟩
        rw [inf_eq_left.mpr hle]
        exact hx
  calc (⨆ n : ℕ, ν {x : β | ENNReal.ofReal t < g x ⊓ (n:ENNReal)} * a)
      = (⨆ n : ℕ, ν {x : β | ENNReal.ofReal t < g x ⊓ (n:ENNReal)}) * a :=
        (ENNReal.iSup_mul _ a).symm
    _ = ν (⋃ n : ℕ, {x : β | ENNReal.ofReal t < g x ⊓ (n:ENNReal)}) * a := by
        rw [← hmono.measure_iUnion]
    _ = ν {x : β | ENNReal.ofReal t < g x} * a := by rw [hunion]

/-- The layer cake formula for a finite-valued measurable function. -/
private lemma layercake_finite {β : Type*} [MeasurableSpace β]
    {ν : MeasureTheory.Measure β} {p : ℝ} (hp : 0 < p) {g : β → ENNReal} (hg : Measurable g)
    (hfin : ∀ x, g x ≠ ⊤) :
    MeasureTheory.lintegral ν (fun x => ENNReal.rpow (g x) p)
      = ENNReal.ofReal p * MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))
          (fun t => ν {x : β | ENNReal.ofReal t < g x} * ENNReal.ofReal (t ^ (p - 1))) := by
  set f : β → ℝ := fun x => (g x).toReal with hf
  have hfnn : 0 ≤ f := fun x => ENNReal.toReal_nonneg
  have hfmeas : AEMeasurable f ν := hg.aemeasurable.ennreal_toReal
  have hkey := MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul ν (ae_of_all ν hfnn) hfmeas hp
  have hL : MeasureTheory.lintegral ν (fun x => ENNReal.rpow (g x) p)
      = MeasureTheory.lintegral ν (fun x => ENNReal.ofReal (f x ^ p)) := by
    apply MeasureTheory.lintegral_congr
    intro x
    rw [hf]
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le,
      ENNReal.ofReal_toReal (hfin x)]
    rfl
  have hR : MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))
        (fun t => ν {x : β | ENNReal.ofReal t < g x} * ENNReal.ofReal (t ^ (p - 1)))
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))
        (fun t => ν {x : β | t < f x} * ENNReal.ofReal (t ^ (p - 1))) := by
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
    have hs : {x : β | ENNReal.ofReal t < g x} = {x : β | t < f x} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      rw [hf]
      exact ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt ht) (hfin x)
    rw [hs]
  rw [hL, hR, hkey]

/-- The layer cake formula for a measurable `ℝ≥0∞`-valued function, obtained from the
finite-valued case by truncation and monotone convergence. -/
private lemma layercake_measurable {β : Type*} [MeasurableSpace β]
    {ν : MeasureTheory.Measure β} {p : ℝ} (hp : 0 < p) {g : β → ENNReal} (hg : Measurable g) :
    MeasureTheory.lintegral ν (fun x => ENNReal.rpow (g x) p)
      = ENNReal.ofReal p * MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))
          (fun t => ν {x : β | ENNReal.ofReal t < g x} * ENNReal.ofReal (t ^ (p - 1))) := by
  have hfin : ∀ n : ℕ,
      MeasureTheory.lintegral ν (fun x => ENNReal.rpow (g x ⊓ (n:ENNReal)) p)
        = ENNReal.ofReal p * MeasureTheory.lintegral
            (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))
            (fun t => ν {x : β | ENNReal.ofReal t < g x ⊓ (n:ENNReal)}
              * ENNReal.ofReal (t ^ (p - 1))) := by
    intro n
    exact layercake_finite hp (hg.inf measurable_const)
      (fun x => ne_of_lt (lt_of_le_of_lt inf_le_right (ENNReal.natCast_lt_top n)))
  have hLsup : MeasureTheory.lintegral ν (fun x => ENNReal.rpow (g x) p)
      = ⨆ n : ℕ, MeasureTheory.lintegral ν (fun x => ENNReal.rpow (g x ⊓ (n:ENNReal)) p) := by
    have hmct := MeasureTheory.lintegral_iSup' (μ := ν)
      (f := fun n x => ENNReal.rpow (g x ⊓ (n:ENNReal)) p)
      (fun n => ((ENNReal.continuous_rpow_const (y := p)).measurable.comp
        (hg.inf measurable_const)).aemeasurable)
      (by filter_upwards with x i j hij
          exact ENNReal.rpow_le_rpow (inf_le_inf_left (g x) (Nat.cast_le.mpr hij)) hp.le)
    calc MeasureTheory.lintegral ν (fun x => ENNReal.rpow (g x) p)
        = MeasureTheory.lintegral ν
            (fun x => ⨆ n : ℕ, ENNReal.rpow (g x ⊓ (n:ENNReal)) p) := by
          apply MeasureTheory.lintegral_congr; intro x
          exact (trunc_rpow_iSup hp (g x)).symm
      _ = ⨆ n : ℕ, MeasureTheory.lintegral ν
            (fun x => ENNReal.rpow (g x ⊓ (n:ENNReal)) p) := hmct
  have hRsup : MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))
        (fun t => ν {x : β | ENNReal.ofReal t < g x} * ENNReal.ofReal (t ^ (p - 1)))
      = ⨆ n : ℕ, MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))
          (fun t => ν {x : β | ENNReal.ofReal t < g x ⊓ (n:ENNReal)}
            * ENNReal.ofReal (t ^ (p - 1))) := by
    have hmeas : ∀ n : ℕ, AEMeasurable (fun t : ℝ =>
        ν {x : β | ENNReal.ofReal t < g x ⊓ (n:ENNReal)} * ENNReal.ofReal (t ^ (p - 1)))
        (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) := by
      intro n
      have hanti : Antitone (fun t : ℝ =>
          ν {x : β | ENNReal.ofReal t < g x ⊓ (n:ENNReal)}) := by
        intro s t hst
        apply measure_mono
        intro x hx
        exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst) hx
      refine hanti.measurable.aemeasurable.mul ?_
      exact (ContinuousOn.aemeasurable
        (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx)))
        measurableSet_Ioi).ennreal_ofReal
    have hmct := MeasureTheory.lintegral_iSup' (μ := MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))
      (f := fun n t => ν {x : β | ENNReal.ofReal t < g x ⊓ (n:ENNReal)}
            * ENNReal.ofReal (t ^ (p - 1))) hmeas
      (by filter_upwards with t i j hij
          exact mul_le_mul_left (measure_mono
            (fun x hx => lt_of_lt_of_le hx (inf_le_inf_left (g x) (Nat.cast_le.mpr hij)))) _)
    calc MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))
          (fun t => ν {x : β | ENNReal.ofReal t < g x} * ENNReal.ofReal (t ^ (p - 1)))
        = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))
            (fun t => ⨆ n : ℕ, ν {x : β | ENNReal.ofReal t < g x ⊓ (n:ENNReal)}
              * ENNReal.ofReal (t ^ (p - 1))) := by
          apply MeasureTheory.lintegral_congr; intro t
          exact (trunc_meas_iSup t (ENNReal.ofReal (t ^ (p - 1)))).symm
      _ = ⨆ n : ℕ, MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))
          (fun t => ν {x : β | ENNReal.ofReal t < g x ⊓ (n:ENNReal)}
            * ENNReal.ofReal (t ^ (p - 1))) := hmct
  rw [hLsup, hRsup, ENNReal.mul_iSup]
  exact iSup_congr (fun n => hfin n)

theorem lintegral_rpow_enorm_eq_layercake
    {β : Type*} [MeasurableSpace β] {ν : MeasureTheory.Measure β} {p : ℝ} (hp : 0 < p)
    {g : β → ENNReal} (hg : AEMeasurable g ν) :
    MeasureTheory.lintegral ν (fun x => ENNReal.rpow (g x) p)
      = ENNReal.ofReal p * MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))
          (fun t => ν {x : β | ENNReal.ofReal t < g x} * ENNReal.ofReal (t ^ (p - 1))) := by
  have hgm := layercake_measurable (ν := ν) hp hg.measurable_mk
  have hae : g =ᵐ[ν] hg.mk g := hg.ae_eq_mk
  have hL : MeasureTheory.lintegral ν (fun x => ENNReal.rpow (g x) p)
      = MeasureTheory.lintegral ν (fun x => ENNReal.rpow (hg.mk g x) p) := by
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
  have hR : MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))
        (fun t => ν {x : β | ENNReal.ofReal t < g x} * ENNReal.ofReal (t ^ (p - 1)))
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))
        (fun t => ν {x : β | ENNReal.ofReal t < hg.mk g x} * ENNReal.ofReal (t ^ (p - 1))) := by
    apply MeasureTheory.lintegral_congr
    intro t
    have hmeas_eq : ν {x : β | ENNReal.ofReal t < g x}
        = ν {x : β | ENNReal.ofReal t < hg.mk g x} := by
      apply MeasureTheory.measure_congr
      filter_upwards [hae] with x hx
      simp [Set.ofPred, hx]
    rw [hmeas_eq]
  rw [hL, hR]
  exact hgm

end Work.BourgainPlan.Maximal
