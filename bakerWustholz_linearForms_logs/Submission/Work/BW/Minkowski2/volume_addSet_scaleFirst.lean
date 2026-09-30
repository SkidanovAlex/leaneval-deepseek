import Mathlib
import Submission.Work.BW.Minkowski2.defs
import Submission.Work.BW.Minkowski2.slicingDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.Minkowski2

open MeasureTheory

section Aux

/-- Fubini's theorem for a product of two function spaces `ι → ℝ`, `κ → ℝ`: integrating over the
second factor and slicing along the first. -/
theorem volume_eq_lintegral_fst_section {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : Set ((ι → ℝ) × (κ → ℝ))} (hA : MeasurableSet A) :
    MeasureTheory.volume A =
      ∫⁻ v : κ → ℝ, MeasureTheory.volume {a : ι → ℝ | (a, v) ∈ A} := by
  have h := Measure.prod_apply_symm (μ := (MeasureTheory.volume : Measure (ι → ℝ)))
    (ν := (MeasureTheory.volume : Measure (κ → ℝ))) hA
  exact h

/-- A finite Minkowski sum `N + T` is measurable when `T` is measurable. -/
theorem measurableSet_addSet_finset {E : Type*} [AddCommGroup E] [MeasurableSpace E]
    [MeasurableAdd₂ E] (N : Finset E) {T : Set E} (hT : MeasurableSet T) :
    MeasurableSet (Work.BW.addSet (N : Set E) T) := by
  have h : Work.BW.addSet (N : Set E) T = ⋃ p ∈ N, (fun z : E => p + z) '' T := by
    ext z; constructor
    · rintro ⟨p, hp, t, ht, rfl⟩
      exact Set.mem_iUnion₂.mpr ⟨p, hp, Set.mem_image_of_mem _ ht⟩
    · intro hz
      rcases Set.mem_iUnion₂.mp hz with ⟨p, hp, hpt⟩
      rcases hpt with ⟨t, ht, rfl⟩
      exact ⟨p, hp, t, ht, rfl⟩
  rw [h]
  exact Finset.measurableSet_biUnion N fun p _ => by
    rw [Set.image_add_left]
    exact hT.preimage (by fun_prop)

/-- The coordinate splitting `Phi d i` preserves the measure of measurable sets. -/
theorem volume_image_Phi {d i : ℕ} {A : Set (Fin d → ℝ)} (hA : MeasurableSet A) :
    MeasureTheory.volume (Phi d i '' A) = MeasureTheory.volume A := by
  have hmap := (measurePreserving_Phi d i).map_eq
  have hmeas : MeasurableSet (Phi d i '' A) := measurableSet_image_Phi d i hA
  have hpre : (Phi d i) ⁻¹' (Phi d i '' A) = A := by
    ext z; constructor
    · rintro ⟨x, hx, hxz⟩
      rwa [← (Phi d i).injective hxz]
    · intro hz; exact ⟨z, hz, rfl⟩
  conv_lhs => rw [← hmap]
  rw [Measure.map_apply (Phi d i).measurable hmeas, hpre]

/-- Full dilation of a convex set does not decrease the volume of `M + S`. -/
theorem volume_addSet_smul_le {ι : Type*} [Fintype ι] {ρ : ℝ} (hρ : 1 ≤ ρ)
    (M : Finset (ι → ℝ)) (S : Set (ι → ℝ)) (hSconv : Convex ℝ S) :
    MeasureTheory.volume (Work.BW.addSet (M : Set (ι → ℝ)) S) ≤
      MeasureTheory.volume (Work.BW.addSet (M : Set (ι → ℝ)) ((fun x => ρ • x) '' S)) := by
  rcases S.eq_empty_or_nonempty with hSe | ⟨c, hc⟩
  · rw [hSe]; simp [Work.BW.addSet]
  · have hρpos : (0 : ℝ) < ρ := lt_of_lt_of_le zero_lt_one hρ
    have hstep : ∀ s ∈ S, s + (ρ - 1) • c ∈ (fun x => ρ • x) '' S := by
      intro s hs
      refine ⟨(1 / ρ) • s + ((ρ - 1) / ρ) • c,
        hSconv hs hc (div_nonneg zero_le_one hρpos.le)
          (div_nonneg (by linarith) hρpos.le) ?_, ?_⟩
      · rw [← add_div, show 1 + (ρ - 1) = ρ by ring, div_self hρpos.ne']
      · show ρ • ((1 / ρ) • s + ((ρ - 1) / ρ) • c) = s + (ρ - 1) • c
        rw [smul_add, smul_smul, smul_smul]
        have h1 : ρ * (1 / ρ) = 1 := by rw [mul_one_div, div_self hρpos.ne']
        have h2 : ρ * ((ρ - 1) / ρ) = ρ - 1 := by
          rw [← mul_div_assoc, mul_div_cancel_left₀ (ρ - 1) hρpos.ne']
        rw [h1, h2, one_smul]
    have hsub : (fun z : ι → ℝ => z + (ρ - 1) • c) '' (Work.BW.addSet (M : Set (ι → ℝ)) S)
        ⊆ Work.BW.addSet (M : Set (ι → ℝ)) ((fun x => ρ • x) '' S) := by
      rintro z ⟨w, hw, rfl⟩
      rcases hw with ⟨m, hm, s, hs, rfl⟩
      exact ⟨m, hm, s + (ρ - 1) • c, hstep s hs, by abel⟩
    calc MeasureTheory.volume (Work.BW.addSet (M : Set (ι → ℝ)) S)
        = MeasureTheory.volume
            ((fun z : ι → ℝ => z + (ρ - 1) • c) '' (Work.BW.addSet (M : Set (ι → ℝ)) S)) := by
          rw [show (fun z : ι → ℝ => z + (ρ - 1) • c)
                = fun z => ((ρ - 1) • c) + z from funext fun z => add_comm _ _,
            Set.image_add_left, MeasureTheory.measure_preimage_add]
      _ ≤ MeasureTheory.volume (Work.BW.addSet (M : Set (ι → ℝ)) ((fun x => ρ • x) '' S)) :=
          measure_mono hsub

/-- The tautological bound `volume (M + S) ≤ card M * volume S`. -/
theorem volume_addSet_le_card_mul {ι : Type*} [Fintype ι] (M : Finset (ι → ℝ))
    (S : Set (ι → ℝ)) :
    MeasureTheory.volume (Work.BW.addSet (M : Set (ι → ℝ)) S) ≤
      (M.card : ENNReal) * MeasureTheory.volume S := by
  have hsub : Work.BW.addSet (M : Set (ι → ℝ)) S
      ⊆ ⋃ x ∈ M, (fun y : ι → ℝ => x + y) '' S := by
    rintro z ⟨m, hm, s, hs, rfl⟩
    exact Set.mem_iUnion₂.mpr ⟨m, hm, s, hs, rfl⟩
  calc MeasureTheory.volume (Work.BW.addSet (M : Set (ι → ℝ)) S)
      ≤ MeasureTheory.volume (⋃ x ∈ M, (fun y : ι → ℝ => x + y) '' S) := measure_mono hsub
    _ ≤ ∑ x ∈ M, MeasureTheory.volume ((fun y : ι → ℝ => x + y) '' S) :=
        measure_biUnion_finset_le M _
    _ = ∑ _x ∈ M, MeasureTheory.volume S := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Set.image_add_left, MeasureTheory.measure_preimage_add]
    _ = (M.card : ENNReal) * MeasureTheory.volume S := by
        rw [Finset.sum_const, nsmul_eq_mul]

end Aux

/-- **The core measure-theoretic step.** If all points of the finite set `N` have vanishing second
coordinate, then replacing `T` by its partial dilation `scaleX ρ '' T` (which only dilates the
first coordinate) does not decrease the volume of `N + T`. -/
theorem volume_addSet_scaleX_le {ι κ : Type*} [Fintype ι] [Fintype κ] {ρ : ℝ} (hρ : 1 ≤ ρ)
    (N : Finset ((ι → ℝ) × (κ → ℝ))) (hN : ∀ p ∈ N, p.2 = 0)
    (T : Set ((ι → ℝ) × (κ → ℝ))) (hTconv : Convex ℝ T) (hTmeas : MeasurableSet T)
    (hXTmeas : MeasurableSet (scaleX (ι := ι) (κ := κ) ρ '' T)) :
    MeasureTheory.volume (Work.BW.addSet (N : Set _) T) ≤
      MeasureTheory.volume (Work.BW.addSet (N : Set _) (scaleX (ι := ι) (κ := κ) ρ '' T)) := by
  classical
  set N₁ : Finset (ι → ℝ) := N.image Prod.fst with hN₁
  have hTsec : ∀ v : κ → ℝ, Convex ℝ {a : ι → ℝ | (a, v) ∈ T} := by
    intro v x hx y hy θ η hθ hη hθη
    have h := hTconv hx hy hθ hη hθη
    have key : θ • (x, v) + η • (y, v) = (θ • x + η • y, v) := by
      refine Prod.ext ?_ ?_
      · ext k; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      · funext k; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← add_mul, hθη]
    rwa [key] at h
  have hsec₁ : ∀ v : κ → ℝ,
      {a : ι → ℝ | (a, v) ∈ Work.BW.addSet (N : Set _) T}
        = Work.BW.addSet (N₁ : Set (ι → ℝ)) {a : ι → ℝ | (a, v) ∈ T} := by
    intro v
    ext a
    constructor
    · rintro ⟨p, hp, q, hq, hpq⟩
      have hp2 : p.2 = 0 := hN p hp
      have hv : v = q.2 := by simpa [hp2] using congrArg Prod.snd hpq
      have ha : a = p.1 + q.1 := by simpa using congrArg Prod.fst hpq
      refine ⟨p.1, ?_, q.1, ?_, ha⟩
      · rw [hN₁]; exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
      · have hqv : (q.1, v) = q := Prod.ext rfl hv
        show (q.1, v) ∈ T
        rwa [hqv]
    · rintro ⟨m, hm, t, ht, rfl⟩
      rw [hN₁] at hm
      rcases Finset.mem_image.mp hm with ⟨p, hp, rfl⟩
      refine ⟨p, hp, (t, v), ht, ?_⟩
      exact Prod.ext rfl (by simp [hN p hp])
  have hsec₂ : ∀ v : κ → ℝ,
      {a : ι → ℝ | (a, v) ∈ Work.BW.addSet (N : Set _) (scaleX (ι := ι) (κ := κ) ρ '' T)}
        = Work.BW.addSet (N₁ : Set (ι → ℝ))
            ((fun a => ρ • a) '' {a : ι → ℝ | (a, v) ∈ T}) := by
    intro v
    ext a
    constructor
    · rintro ⟨p, hp, q, hq, hpq⟩
      rcases hq with ⟨q₀, hq₀, rfl⟩
      have hp2 : p.2 = 0 := hN p hp
      have hv : v = q₀.2 := by simpa [scaleX, hp2] using congrArg Prod.snd hpq
      have ha : a = p.1 + ρ • q₀.1 := by simpa [scaleX] using congrArg Prod.fst hpq
      refine ⟨p.1, ?_, ρ • q₀.1, ⟨q₀.1, ?_, rfl⟩, ha⟩
      · rw [hN₁]; exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
      · have hqv : (q₀.1, v) = q₀ := Prod.ext rfl hv
        show (q₀.1, v) ∈ T
        rwa [hqv]
    · rintro ⟨m, hm, t, ht, rfl⟩
      rw [hN₁] at hm
      rcases Finset.mem_image.mp hm with ⟨p, hp, rfl⟩
      rcases ht with ⟨t₀, ht₀, rfl⟩
      refine ⟨p, hp, scaleX (ι := ι) (κ := κ) ρ (t₀, v), ⟨(t₀, v), ht₀, rfl⟩, ?_⟩
      exact Prod.ext rfl (by simp [hN p hp])
  have hAmeas : MeasurableSet (Work.BW.addSet (N : Set _) T) :=
    measurableSet_addSet_finset N hTmeas
  have hBmeas : MeasurableSet (Work.BW.addSet (N : Set _) (scaleX (ι := ι) (κ := κ) ρ '' T)) :=
    measurableSet_addSet_finset N hXTmeas
  calc MeasureTheory.volume (Work.BW.addSet (N : Set _) T)
      = ∫⁻ v : κ → ℝ,
          MeasureTheory.volume {a : ι → ℝ | (a, v) ∈ Work.BW.addSet (N : Set _) T} :=
        volume_eq_lintegral_fst_section hAmeas
    _ = ∫⁻ v : κ → ℝ, MeasureTheory.volume
          (Work.BW.addSet (N₁ : Set (ι → ℝ)) {a : ι → ℝ | (a, v) ∈ T}) := by
        refine lintegral_congr fun v => ?_
        rw [hsec₁ v]
    _ ≤ ∫⁻ v : κ → ℝ, MeasureTheory.volume
          (Work.BW.addSet (N₁ : Set (ι → ℝ))
            ((fun a => ρ • a) '' {a : ι → ℝ | (a, v) ∈ T})) :=
        lintegral_mono fun v => volume_addSet_smul_le hρ N₁ _ (hTsec v)
    _ = ∫⁻ v : κ → ℝ, MeasureTheory.volume
          {a : ι → ℝ | (a, v) ∈ Work.BW.addSet (N : Set _) (scaleX (ι := ι) (κ := κ) ρ '' T)} := by
        refine lintegral_congr fun v => ?_
        rw [hsec₂ v]
    _ = MeasureTheory.volume (Work.BW.addSet (N : Set _) (scaleX (ι := ι) (κ := κ) ρ '' T)) :=
        (volume_eq_lintegral_fst_section hBmeas).symm

/-- The measure-theoretic inequality in `ℝ≥0∞` form. -/
theorem volume_addSet_scaleFirst_ennreal {d i : ℕ} {ρ : ℝ} (hρ : 1 ≤ ρ)
    (M : Finset (Fin d → ℝ)) (hM : ∀ x ∈ M, ∀ j : Fin d, i ≤ (j : ℕ) → x j = 0)
    (S : Set (Fin d → ℝ)) (hSconv : Convex ℝ S) (hSmeas : MeasurableSet S) :
    MeasureTheory.volume (Work.BW.addSet (M : Set (Fin d → ℝ)) S) ≤
      MeasureTheory.volume (Work.BW.addSet (M : Set (Fin d → ℝ))
        (Work.BW.scaleFirst i ρ '' S)) := by
  classical
  have hρne : ρ ≠ 0 := by linarith
  have hAmeas : MeasurableSet (Work.BW.addSet (M : Set (Fin d → ℝ)) S) :=
    measurableSet_addSet d M hSmeas
  have hTmeas : MeasurableSet (Work.BW.scaleFirst i ρ '' S) :=
    measurableSet_scaleFirst_image d i hρne hSmeas
  have hBmeas : MeasurableSet (Work.BW.addSet (M : Set (Fin d → ℝ))
      (Work.BW.scaleFirst i ρ '' S)) := measurableSet_addSet d M hTmeas
  have hL : MeasureTheory.volume (Work.BW.addSet (M : Set (Fin d → ℝ)) S)
      = MeasureTheory.volume (Work.BW.addSet (M.image (Phi d i) : Set _) (Phi d i '' S)) := by
    rw [← volume_image_Phi hAmeas, Phi_image_addSet]
  have hR : MeasureTheory.volume (Work.BW.addSet (M : Set (Fin d → ℝ))
        (Work.BW.scaleFirst i ρ '' S))
      = MeasureTheory.volume (Work.BW.addSet (M.image (Phi d i) : Set _)
          (scaleX (ι := Xidx d i) (κ := Yidx d i) ρ '' (Phi d i '' S))) := by
    rw [← volume_image_Phi hBmeas, Phi_image_addSet, Phi_image_scaleFirst]
  have hXTmeas : MeasurableSet
      (scaleX (ι := Xidx d i) (κ := Yidx d i) ρ '' (Phi d i '' S)) := by
    rw [← Phi_image_scaleFirst d i ρ S]
    exact measurableSet_image_Phi d i hTmeas
  rw [hL, hR]
  exact volume_addSet_scaleX_le hρ (M.image (Phi d i)) (Phi_snd_eq_zero d i M hM)
    (Phi d i '' S) (convex_image_Phi d i hSconv) (measurableSet_image_Phi d i hSmeas) hXTmeas

/-- Slicing inequality for Minkowski's proof of his second theorem: dilating the first `i`
coordinates by a factor `ρ ≥ 1` does not decrease the volume of `M + S`, where `M` is a finite set
of points supported in the first `i` coordinates and `S` is convex. -/
theorem volume_addSet_scaleFirst {n i : ℕ} {ρ : ℝ} (hρ : 1 ≤ ρ)
    (M : Finset (Fin n → ℝ)) (hM : ∀ x ∈ M, ∀ j : Fin n, i ≤ (j : ℕ) → x j = 0)
    (S : Set (Fin n → ℝ)) (hSconv : Convex ℝ S) (hSmeas : MeasurableSet S) :
    MeasureTheory.volume.real (Work.BW.addSet (M : Set (Fin n → ℝ)) S) ≤
      MeasureTheory.volume.real (Work.BW.addSet (M : Set (Fin n → ℝ)) (Work.BW.scaleFirst i ρ '' S)) := by
  by_cases hStop : MeasureTheory.volume S = ⊤
  · rw [Measure.real_def]
    have hA0 : (MeasureTheory.volume (Work.BW.addSet (M : Set (Fin n → ℝ)) S)).toReal = 0 := by
      rcases M.eq_empty_or_nonempty with hM0 | ⟨x0, hx0⟩
      · rw [hM0]; simp [Work.BW.addSet]
      · have hsub : (fun s : Fin n → ℝ => x0 + s) '' S
            ⊆ Work.BW.addSet (M : Set (Fin n → ℝ)) S := by
          rintro z ⟨s, hs, rfl⟩
          exact ⟨x0, hx0, s, hs, rfl⟩
        have htop : MeasureTheory.volume (Work.BW.addSet (M : Set (Fin n → ℝ)) S) = ⊤ := by
          refine top_le_iff.mp ?_
          rw [← hStop]
          calc MeasureTheory.volume S
              = MeasureTheory.volume ((fun s : Fin n → ℝ => x0 + s) '' S) := by
                rw [Set.image_add_left]
                simp
            _ ≤ MeasureTheory.volume (Work.BW.addSet (M : Set (Fin n → ℝ)) S) :=
                measure_mono hsub
        rw [htop]; simp
    rw [hA0]
    exact ENNReal.toReal_nonneg
  · have hTS : MeasureTheory.volume (Work.BW.scaleFirst (d := n) i ρ '' S)
        = ENNReal.ofReal |LinearMap.det (Work.BW.scaleFirst (d := n) i ρ)|
            * MeasureTheory.volume S :=
      Measure.addHaar_image_linearMap (MeasureTheory.volume : Measure (Fin n → ℝ))
        (Work.BW.scaleFirst (d := n) i ρ) S
    have hBlt : MeasureTheory.volume (Work.BW.addSet (M : Set (Fin n → ℝ))
        (Work.BW.scaleFirst i ρ '' S)) < ⊤ := by
      refine lt_of_le_of_lt (volume_addSet_le_card_mul M _) ?_
      rw [hTS]
      exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hStop))
    rw [Measure.real_def, Measure.real_def]
    exact ENNReal.toReal_mono hBlt.ne
      (volume_addSet_scaleFirst_ennreal hρ M hM S hSconv hSmeas)

end Work.BW.Minkowski2
