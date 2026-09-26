import Mathlib
import Submission.Work.Drive.Mono.FiberModel.Defs
import Submission.Work.Drive.Mono.FiberModel.height_basic
import Submission.Work.Drive.Mono.FiberModel.planar_basic
import Submission.Work.Drive.Mono.fibreMax_continuous
import Submission.Work.Topology.SphereSlicing.convex_PBox
import Submission.Work.Topology.SphereSlicing.isOpen_PBox

namespace Work.Drive.Mono.FiberModel

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

/-! ## Auxiliary lemmas for `height_facts`

Everything here is a direct consequence of the definitions in `Defs.lean` and the two compactness
facts `height_basic.isCompact_fibre_set`/`fibre_nonempty`, of the convexity of the box
(`SphereSlicing.convex_PBox`), of the attainedness of the two extrema (`height_basic.fMin_mem`,
`height_basic.fMax_mem`) and of the already-proved continuity of the fibre maximum
(`Work.Drive.Mono.fibreMax_continuous`). -/

/-- Membership in the closed-box fibre, in coordinates: a point of the closed box whose image under
`levPair` is `X` lies in the fibre over `X`. -/
theorem mem_fibre_of {v : R3} {ℓ : R3 →L[ℝ] ℝ} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {X : ℝ × ℝ} {y : R3} (hy : y ∈ ClBox s c σ) (hX : levPair v ℓ y = X) :
    y ∈ fibre v ℓ s c σ X := by
  rw [fibre_eq_set]
  refine ⟨hy, ?_, ?_⟩
  · have h := congrArg Prod.fst hX
    simpa [levPair] using h
  · have h := congrArg Prod.snd hX
    simpa [levPair] using h

/-- The image of a point of the fibre under `levPair` is the fibre's label. -/
theorem levPair_eq_of_mem_fibre {v : R3} {ℓ : R3 →L[ℝ] ℝ} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {X : ℝ × ℝ} {y : R3} (hy : y ∈ fibre v ℓ s c σ X) :
    levPair v ℓ y = X := by
  rw [fibre_eq_set] at hy
  rw [levPair]
  exact Prod.ext hy.2.1 hy.2.2

/-- A point of the fibre lies in the closed box. -/
theorem mem_ClBox_of_mem_fibre {v : R3} {ℓ : R3 →L[ℝ] ℝ} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {X : ℝ × ℝ} {y : R3} (hy : y ∈ fibre v ℓ s c σ X) :
    y ∈ ClBox s c σ := by
  rw [fibre_eq_set] at hy
  exact hy.1

/-- Linearity of `levPair` for two-term linear combinations. -/
theorem levPair_smul_add (v : R3) (ℓ : R3 →L[ℝ] ℝ) (a b : ℝ) (y₁ y₂ : R3) :
    levPair v ℓ (a • y₁ + b • y₂) = a • levPair v ℓ y₁ + b • levPair v ℓ y₂ := by
  rw [levPair_eq_levPairCLM]
  rw [map_add, map_smul, map_smul]

/-- Linearity of `ζ` for two-term linear combinations, in coordinates. -/
theorem zeta_smul_add (ζ : R3 →L[ℝ] ℝ) (a b : ℝ) (y₁ y₂ : R3) :
    ζ (a • y₁ + b • y₂) = a * ζ y₁ + b * ζ y₂ := by
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- The minimum over the fibre is a lower bound for the fibre values. -/
theorem fMin_le_of_mem_fibre {ζ : R3 →L[ℝ] ℝ} {v : R3} {ℓ : R3 →L[ℝ] ℝ} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {X : ℝ × ℝ} {z : R3} (hz : z ∈ fibre v ℓ s c σ X) :
    fMin ζ v ℓ s c σ X ≤ ζ z := by
  have hz' : z ∈ {y : R3 | y ∈ ClBox s c σ ∧ inner ℝ v y = X.1 ∧ ℓ y = X.2} := by
    rwa [← fibre_eq_set]
  rw [fMin, Work.Drive.Mono.fibreMin]
  simp only [innerSL_apply_apply]
  exact csInf_le ((isCompact_fibre_set (s := s) (c := c) (σ := σ) (v := v) (ℓ := ℓ) X).image
    ζ.continuous).bddBelow ⟨z, hz', rfl⟩

/-- The maximum over the fibre is an upper bound for the fibre values. -/
theorem le_fMax_of_mem_fibre {ζ : R3 →L[ℝ] ℝ} {v : R3} {ℓ : R3 →L[ℝ] ℝ} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {X : ℝ × ℝ} {z : R3} (hz : z ∈ fibre v ℓ s c σ X) :
    ζ z ≤ fMax ζ v ℓ s c σ X := by
  have hz' : z ∈ {y : R3 | y ∈ ClBox s c σ ∧ inner ℝ v y = X.1 ∧ ℓ y = X.2} := by
    rwa [← fibre_eq_set]
  rw [fMax, Work.Drive.Mono.fibreMax]
  simp only [innerSL_apply_apply]
  exact le_csSup ((isCompact_fibre_set (s := s) (c := c) (σ := σ) (v := v) (ℓ := ℓ) X).image
    ζ.continuous).bddAbove ⟨z, hz', rfl⟩

/-- The fibre of the closed box over a plane point is convex. -/
theorem convex_fibre (v : R3) (ℓ : R3 →L[ℝ] ℝ) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (X : ℝ × ℝ) : Convex ℝ (fibre v ℓ s c σ X) := by
  rw [fibre_eq_set]
  intro y hy y' hy' a b ha hb hab
  refine ⟨(Work.Topology.SphereSlicing.convex_PBox s c σ).closure hy.1 hy'.1 ha hb hab, ?_, ?_⟩
  · rw [inner_add_right, inner_smul_right, inner_smul_right, hy.2.1, hy'.2.1, ← add_mul, hab,
      one_mul]
  · rw [map_add, map_smul, map_smul, hy.2.2, hy'.2.2, smul_eq_mul, smul_eq_mul, ← add_mul, hab,
      one_mul]

/-- **The `ζ`-image of the fibre of the closed box over a point of the shadow is the interval
between the two extreme heights.** -/
theorem fibre_image_Icc {ζ : R3 →L[ℝ] ℝ} {v : R3} {ℓ : R3 →L[ℝ] ℝ} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {X : ℝ × ℝ} (hX : X ∈ boxShadow s c σ v ℓ) :
    ζ '' fibre v ℓ s c σ X = Set.Icc (fMin ζ v ℓ s c σ X) (fMax ζ v ℓ s c σ X) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro t ⟨y, hy, rfl⟩
    exact ⟨fMin_le_of_mem_fibre hy, le_fMax_of_mem_fibre hy⟩
  · intro t ht
    obtain ⟨ymin, hymin, hyminζ⟩ := fMin_mem (ζ := ζ) hX
    obtain ⟨ymax, hymax, hymaxζ⟩ := fMax_mem (ζ := ζ) hX
    have hconv := convex_fibre v ℓ s c σ X
    have hg : Continuous fun u : ℝ => ζ ((1 - u) • ymin + u • ymax) := by fun_prop
    have hsub := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hg.continuousOn
    have h0 : ζ ((1 - (0 : ℝ)) • ymin + (0 : ℝ) • ymax) = fMin ζ v ℓ s c σ X := by
      simpa using hyminζ
    have h1 : ζ ((1 - (1 : ℝ)) • ymin + (1 : ℝ) • ymax) = fMax ζ v ℓ s c σ X := by
      simpa using hymaxζ
    rw [h0, h1] at hsub
    obtain ⟨u, hu, huζ⟩ := hsub ht
    exact ⟨(1 - u) • ymin + u • ymax,
      hconv hymin hymax (by linarith [hu.1, hu.2]) (by linarith [hu.1, hu.2]) (by ring), huζ⟩

/-- **A vector of the kernel of `levPair` on which `ζ` does not vanish**, given `HasTrivKernel`.

`HasTrivKernel v ℓ ζ` makes `(⟪v,·⟫, ℓ, ζ) : ℝ³ → (ℝ × ℝ) × ℝ` injective; the two spaces have the
same dimension `3`, so it is also surjective, and the preimage of `((0,0),1)` is the required
vector. -/
theorem exists_ker_ne {v : R3} {ℓ ζ : R3 →L[ℝ] ℝ} (hker : HasTrivKernel v ℓ ζ) :
    ∃ w : R3, w ≠ 0 ∧ inner ℝ v w = 0 ∧ ℓ w = 0 ∧ ζ w ≠ 0 := by
  have hrank : Module.finrank ℝ R3 = Module.finrank ℝ ((ℝ × ℝ) × ℝ) := by
    rw [finrank_euclideanSpace_fin]
    simp [Module.finrank_prod, Module.finrank_self]
  have hinj : Function.Injective ⇑((levPairCLM v ℓ).prod ζ) := by
    intro a b hab
    have h1 : levPairCLM v ℓ a = levPairCLM v ℓ b := by
      have := congrArg Prod.fst hab
      simpa only [ContinuousLinearMap.prod_apply] using this
    have h2 : ζ a = ζ b := by
      have := congrArg Prod.snd hab
      simpa only [ContinuousLinearMap.prod_apply] using this
    have hp : inner ℝ v a = inner ℝ v b := by
      have := congrArg Prod.fst h1
      rwa [levPairCLM_apply, levPairCLM_apply] at this
    have hq : ℓ a = ℓ b := by
      have := congrArg Prod.snd h1
      rwa [levPairCLM_apply, levPairCLM_apply] at this
    have hzero : a - b = 0 := by
      refine hker (a - b) ?_ ?_ ?_
      · rw [inner_sub_right, hp, sub_self]
      · rw [map_sub, hq, sub_self]
      · rw [map_sub, h2, sub_self]
    exact sub_eq_zero.mp hzero
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj
  obtain ⟨w, hw⟩ := hsurj ((0, 0), 1)
  change (levPairCLM v ℓ w, ζ w) = ((0, 0), 1) at hw
  rw [levPairCLM_apply] at hw
  have hw1 : inner ℝ v w = 0 := by
    have := congrArg (fun p : (ℝ × ℝ) × ℝ => p.1.1) hw
    simpa using this
  have hw2 : ℓ w = 0 := by
    have := congrArg (fun p : (ℝ × ℝ) × ℝ => p.1.2) hw
    simpa using this
  have hw3 : ζ w = 1 := by
    have := congrArg (fun p : (ℝ × ℝ) × ℝ => p.2) hw
    simpa using this
  refine ⟨w, ?_, hw1, hw2, ?_⟩
  · intro hw0
    rw [hw0] at hw3
    norm_num at hw3
  · rw [hw3]
    norm_num

/-- **The open box is the interior of the closed box** (for positive radius). -/
theorem interior_ClBox (s : ℝ) (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    interior (ClBox s c σ) = Submission.PBox s c σ := by
  rw [ClBox,
    (Work.Topology.SphereSlicing.convex_PBox s c σ).interior_closure_eq_interior_of_nonempty_interior
      (by
        rw [(Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq]
        exact PBox_nonempty hs c σ)]
  exact (Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq

/-- **An interior point of the image of a convex set is the image of an interior point.**

For a convex `C` with nonempty interior, a linear `f` and a point `y`, if `f y` is an interior point
of `f '' C` then `f y = f y'` for some `y' ∈ interior C`.  (Concretely: push `f y` a little in the
direction away from `f z`, `z ∈ interior C`, lift the resulting point to `C`, and take the
corresponding convex combination with `z`.) -/
theorem exists_mem_interior_of_mem_interior_image {C : Set R3} {f : R3 →L[ℝ] (ℝ × ℝ)} {y : R3}
    (hC : Convex ℝ C) {z : R3} (hz : z ∈ interior C)
    (hyX : f y ∈ interior (f '' C)) : ∃ y' ∈ interior C, f y' = f y := by
  have hnb : f '' C ∈ nhds (f y) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hyX) interior_subset
  have hcont : Continuous fun t : ℝ => f y + t • (f y - f z) := by fun_prop
  have htend : Filter.Tendsto (fun t : ℝ => f y + t • (f y - f z)) (nhds 0) (nhds (f y)) := by
    have h0 : f y + (0 : ℝ) • (f y - f z) = f y := by simp
    simpa [h0] using (hcont.continuousAt (x := (0 : ℝ))).tendsto
  have hev₁ : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), f y + t • (f y - f z) ∈ f '' C :=
    (htend.mono_left nhdsWithin_le_nhds).eventually hnb
  have hev₂ : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Ioi 0 := self_mem_nhdsWithin
  obtain ⟨τ, hτpos, hτmem⟩ := (hev₂.and hev₁).exists
  obtain ⟨y₀, hy₀C, hy₀eq⟩ := hτmem
  have hτ0 : (0 : ℝ) < τ := hτpos
  have h1ne : (1 : ℝ) + τ ≠ 0 := by linarith
  refine ⟨(1 / (1 + τ)) • y₀ + (τ / (1 + τ)) • z, ?_, ?_⟩
  · refine hC.combo_self_interior_mem_interior hy₀C hz ?_ ?_ ?_
    · exact div_nonneg zero_le_one (by linarith)
    · exact div_pos hτ0 (by linarith)
    · rw [← add_div, div_self h1ne]
  · rw [map_add, map_smul, map_smul, hy₀eq]
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul] <;> field_simp <;> ring

/-- **Over the interior of the shadow, the fibre of the closed box meets the open box.** -/
theorem exists_mem_interior_ClBox_of_mem_interior {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v : R3} {ℓ : R3 →L[ℝ] ℝ} {X : ℝ × ℝ} (hs : 0 < s)
    (hX : X ∈ interior (boxShadow s c σ v ℓ)) :
    ∃ y ∈ interior (ClBox s c σ), levPair v ℓ y = X := by
  have hcenter : c ∈ interior (ClBox s c σ) := by
    rw [interior_ClBox s hs c σ]
    intro i
    rw [sub_self, abs_zero]
    exact mul_pos (Submission.boxSide_pos i) hs
  have hconv : Convex ℝ (ClBox s c σ) := (Work.Topology.SphereSlicing.convex_PBox s c σ).closure
  rw [boxShadow, shadow] at hX
  obtain ⟨y, hy, hyX⟩ := interior_subset hX
  rw [levPair_eq_levPairCLM] at hX hyX
  obtain ⟨y', hy', hy'eq⟩ :=
    exists_mem_interior_of_mem_interior_image (C := ClBox s c σ) (f := levPairCLM v ℓ)
      hconv hcenter (y := y) (by rw [hyX]; exact hX)
  exact ⟨y', hy', by rw [levPair_eq_levPairCLM, hy'eq, hyX]⟩

/-- **On the open box the value of `ζ` is strictly between the two extreme heights of the fibre.**

(Hence in particular `fMin < fMax` over the interior of the shadow: the fibre meets the open box,
and on the open box one can move a little along any non-trivial vector of `ker (⟪v,·⟫, ℓ)`.) -/
theorem zeta_mem_Ioo_of_mem_interior {ζ : R3 →L[ℝ] ℝ} {v : R3} {ℓ : R3 →L[ℝ] ℝ} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} (hker : HasTrivKernel v ℓ ζ) {X : ℝ × ℝ} {y : R3}
    (hy : y ∈ interior (ClBox s c σ)) (hyX : levPair v ℓ y = X) :
    ζ y ∈ Set.Ioo (fMin ζ v ℓ s c σ X) (fMax ζ v ℓ s c σ X) := by
  obtain ⟨w, hwne, hw1, hw2, hwζ⟩ := exists_ker_ne hker
  have hstep : ∀ u : R3, inner ℝ v u = 0 → ℓ u = 0 →
      ∃ t : ℝ, 0 < t ∧ y + t • u ∈ interior (ClBox s c σ) := by
    intro u hu1 hu2
    have hnb : interior (ClBox s c σ) ∈ nhds y := isOpen_interior.mem_nhds hy
    have hcont : Continuous fun t : ℝ => y + t • u := by fun_prop
    have htend : Filter.Tendsto (fun t : ℝ => y + t • u) (nhds 0) (nhds y) := by
      have h0 : y + (0 : ℝ) • u = y := by simp
      simpa [h0] using (hcont.continuousAt (x := (0 : ℝ))).tendsto
    have hev₁ : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), y + t • u ∈ interior (ClBox s c σ) :=
      (htend.mono_left nhdsWithin_le_nhds).eventually hnb
    have hev₂ : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Ioi 0 := self_mem_nhdsWithin
    obtain ⟨t, ht, htmem⟩ := (hev₂.and hev₁).exists
    exact ⟨t, ht, htmem⟩
  have hlev : ∀ u : R3, inner ℝ v u = 0 → ℓ u = 0 → ∀ t : ℝ, levPair v ℓ (y + t • u) = X := by
    intro u hu1 hu2 t
    have h1 : inner ℝ v (y + t • u) = inner ℝ v y := by
      rw [inner_add_right, inner_smul_right, hu1, mul_zero, add_zero]
    have h2 : ℓ (y + t • u) = ℓ y := by
      rw [map_add, map_smul, hu2, smul_zero, add_zero]
    rw [levPair, h1, h2]
    simpa [levPair] using hyX
  obtain ⟨t₁, ht₁, hz₁⟩ := hstep w hw1 hw2
  obtain ⟨t₂, ht₂, hz₂⟩ := hstep (-w) (by simp [hw1]) (by simp [hw2])
  have hf1 : (y + t₁ • w) ∈ fibre v ℓ s c σ X :=
    mem_fibre_of (interior_subset hz₁) (hlev w hw1 hw2 t₁)
  have hf2 : (y + t₂ • (-w)) ∈ fibre v ℓ s c σ X :=
    mem_fibre_of (interior_subset hz₂) (hlev (-w) (by simp [hw1]) (by simp [hw2]) t₂)
  have hb1 : fMin ζ v ℓ s c σ X ≤ ζ (y + t₁ • w) := fMin_le_of_mem_fibre hf1
  have hb2 : ζ (y + t₁ • w) ≤ fMax ζ v ℓ s c σ X := le_fMax_of_mem_fibre hf1
  have hb3 : fMin ζ v ℓ s c σ X ≤ ζ (y + t₂ • (-w)) := fMin_le_of_mem_fibre hf2
  have hb4 : ζ (y + t₂ • (-w)) ≤ fMax ζ v ℓ s c σ X := le_fMax_of_mem_fibre hf2
  have hz1 : ζ (y + t₁ • w) = ζ y + t₁ * ζ w := by
    rw [map_add, map_smul, smul_eq_mul]
  have hz2 : ζ (y + t₂ • (-w)) = ζ y - t₂ * ζ w := by
    rw [map_add, map_smul, map_neg, smul_eq_mul]; ring
  rcases lt_trichotomy (ζ w) 0 with hlt | heq | hgt
  · refine ⟨lt_of_le_of_lt hb1 ?_, lt_of_lt_of_le ?_ hb4⟩
    · rw [hz1]; nlinarith
    · rw [hz2]; nlinarith
  · exact absurd heq hwζ
  · refine ⟨lt_of_le_of_lt hb3 ?_, lt_of_lt_of_le ?_ hb2⟩
    · rw [hz2]; nlinarith
    · rw [hz1]; nlinarith

/-- **Over the interior of the shadow, the `ζ`-image of the fibre of the *open* box is the open
interval between the two extreme heights.** -/
theorem image_PBox_fibre_eq_Ioo {ζ : R3 →L[ℝ] ℝ} {v : R3} {ℓ : R3 →L[ℝ] ℝ} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} (hker : HasTrivKernel v ℓ ζ) (hs : 0 < s) {X : ℝ × ℝ}
    (hX : X ∈ interior (boxShadow s c σ v ℓ)) :
    ζ '' {y ∈ Submission.PBox s c σ | levPair v ℓ y = X} =
      Set.Ioo (fMin ζ v ℓ s c σ X) (fMax ζ v ℓ s c σ X) := by
  rw [← interior_ClBox s hs c σ]
  have hXw : X ∈ boxShadow s c σ v ℓ := interior_subset hX
  have hconv : Convex ℝ (ClBox s c σ) := (Work.Topology.SphereSlicing.convex_PBox s c σ).closure
  refine Set.Subset.antisymm ?_ ?_
  · rintro t ⟨y, hmem, rfl⟩
    exact zeta_mem_Ioo_of_mem_interior hker hmem.1 hmem.2
  · intro t ht
    obtain ⟨ystar, hystar, hystarX⟩ :=
      exists_mem_interior_ClBox_of_mem_interior (v := v) (ℓ := ℓ) hs hX
    obtain ⟨ymin, hymin, hyminζ⟩ := fMin_mem (ζ := ζ) hXw
    obtain ⟨ymax, hymax, hymaxζ⟩ := fMax_mem (ζ := ζ) hXw
    have hminC : ymin ∈ ClBox s c σ := mem_ClBox_of_mem_fibre hymin
    have hminX : levPair v ℓ ymin = X := levPair_eq_of_mem_fibre hymin
    have hmaxC : ymax ∈ ClBox s c σ := mem_ClBox_of_mem_fibre hymax
    have hmaxX : levPair v ℓ ymax = X := levPair_eq_of_mem_fibre hymax
    by_cases hle : t ≤ ζ ystar
    · have hg : Continuous fun u : ℝ => ζ ((1 - u) • ystar + u • ymin) := by fun_prop
      have hg0 : ζ ((1 - (0 : ℝ)) • ystar + (0 : ℝ) • ymin) = ζ ystar := by simp
      have hg1 : ζ ((1 - (1 : ℝ)) • ystar + (1 : ℝ) • ymin) = fMin ζ v ℓ s c σ X := by
        simpa using hyminζ
      have hsub := intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num) hg.continuousOn
      rw [hg0, hg1] at hsub
      obtain ⟨u, hu, huζ⟩ := hsub ⟨ht.1.le, hle⟩
      have hu1 : u < 1 := by
        rcases lt_or_eq_of_le hu.2 with h | h
        · exact h
        · exfalso
          rw [h] at huζ
          simp only [sub_self, zero_smul, zero_add, one_smul] at huζ
          rw [hyminζ] at huζ
          linarith [ht.1, huζ]
      have hcombo : u • ymin + (1 - u) • ystar ∈ interior (ClBox s c σ) :=
        hconv.combo_self_interior_mem_interior hminC hystar (by linarith [hu.1, hu.2])
          (by linarith [hu.1, hu.2]) (by ring)
      have hlev : levPair v ℓ (u • ymin + (1 - u) • ystar) = X := by
        rw [levPair_smul_add, hminX, hystarX, ← add_smul, show u + (1 - u) = 1 by ring, one_smul]
      have hζ : ζ (u • ymin + (1 - u) • ystar) = t := by
        rw [add_comm]
        exact huζ
      exact ⟨u • ymin + (1 - u) • ystar, ⟨hcombo, hlev⟩, hζ⟩
    · have hltc : ζ ystar < t := not_le.mp hle
      have hg : Continuous fun u : ℝ => ζ ((1 - u) • ystar + u • ymax) := by fun_prop
      have hg0 : ζ ((1 - (0 : ℝ)) • ystar + (0 : ℝ) • ymax) = ζ ystar := by simp
      have hg1 : ζ ((1 - (1 : ℝ)) • ystar + (1 : ℝ) • ymax) = fMax ζ v ℓ s c σ X := by
        simpa using hymaxζ
      have hsub := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hg.continuousOn
      rw [hg0, hg1] at hsub
      obtain ⟨u, hu, huζ⟩ := hsub ⟨hltc.le, ht.2.le⟩
      have hu1 : u < 1 := by
        rcases lt_or_eq_of_le hu.2 with h | h
        · exact h
        · exfalso
          rw [h] at huζ
          simp only [sub_self, zero_smul, zero_add, one_smul] at huζ
          rw [hymaxζ] at huζ
          linarith [ht.2, huζ]
      have hcombo : u • ymax + (1 - u) • ystar ∈ interior (ClBox s c σ) :=
        hconv.combo_self_interior_mem_interior hmaxC hystar (by linarith [hu.1, hu.2])
          (by linarith [hu.1, hu.2]) (by ring)
      have hlev : levPair v ℓ (u • ymax + (1 - u) • ystar) = X := by
        rw [levPair_smul_add, hmaxX, hystarX, ← add_smul, show u + (1 - u) = 1 by ring, one_smul]
      have hζ : ζ (u • ymax + (1 - u) • ystar) = t := by
        rw [add_comm]
        exact huζ
      exact ⟨u • ymax + (1 - u) • ystar, ⟨hcombo, hlev⟩, hζ⟩

/-- **The closed box is exactly the solid between the two height functions.** -/
theorem mem_ClBox_iff {ζ : R3 →L[ℝ] ℝ} {v : R3} {ℓ : R3 →L[ℝ] ℝ} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} (hker : HasTrivKernel v ℓ ζ) {y : R3} :
    y ∈ ClBox s c σ ↔ (levPair v ℓ y ∈ boxShadow s c σ v ℓ ∧
      fMin ζ v ℓ s c σ (levPair v ℓ y) ≤ ζ y ∧
      ζ y ≤ fMax ζ v ℓ s c σ (levPair v ℓ y)) := by
  have hcent : Convex ℝ (ClBox s c σ) := (Work.Topology.SphereSlicing.convex_PBox s c σ).closure
  constructor
  · intro hy
    refine ⟨⟨y, hy, rfl⟩, ?_, ?_⟩
    · exact fMin_le_of_mem_fibre (mem_fibre_of hy rfl)
    · exact le_fMax_of_mem_fibre (mem_fibre_of hy rfl)
  · rintro ⟨hX, h1, h2⟩
    obtain ⟨ymin, hymin, hyminζ⟩ := fMin_mem (ζ := ζ) hX
    obtain ⟨ymax, hymax, hymaxζ⟩ := fMax_mem (ζ := ζ) hX
    have hminC : ymin ∈ ClBox s c σ := mem_ClBox_of_mem_fibre hymin
    have hmaxC : ymax ∈ ClBox s c σ := mem_ClBox_of_mem_fibre hymax
    have hminX : levPair v ℓ ymin = levPair v ℓ y := levPair_eq_of_mem_fibre hymin
    have hmaxX : levPair v ℓ ymax = levPair v ℓ y := levPair_eq_of_mem_fibre hymax
    rcases eq_or_lt_of_le h1 with heq | hlt
    · have hy0 : y - ymin = 0 := by
        refine hker (y - ymin) ?_ ?_ ?_
        · have hh : inner ℝ v ymin = inner ℝ v y := by
            have h := congrArg Prod.fst hminX
            simpa [levPair] using h
          rw [inner_sub_right, hh, sub_self]
        · have hh : ℓ ymin = ℓ y := by
            have h := congrArg Prod.snd hminX
            simpa [levPair] using h
          rw [map_sub, hh, sub_self]
        · rw [map_sub, ← heq, hyminζ, sub_self]
      rw [sub_eq_zero] at hy0
      rw [hy0]
      exact hminC
    · have hmaxlt : fMin ζ v ℓ s c σ (levPair v ℓ y) < fMax ζ v ℓ s c σ (levPair v ℓ y) :=
        lt_of_lt_of_le hlt h2
      have hne : fMax ζ v ℓ s c σ (levPair v ℓ y) - fMin ζ v ℓ s c σ (levPair v ℓ y) ≠ 0 := by
        linarith
      set t : ℝ := (ζ y - fMin ζ v ℓ s c σ (levPair v ℓ y)) /
        (fMax ζ v ℓ s c σ (levPair v ℓ y) - fMin ζ v ℓ s c σ (levPair v ℓ y)) with htdef
      have htmul : t * (fMax ζ v ℓ s c σ (levPair v ℓ y) - fMin ζ v ℓ s c σ (levPair v ℓ y))
          = ζ y - fMin ζ v ℓ s c σ (levPair v ℓ y) := by
        rw [htdef, div_mul_cancel₀ _ hne]
      have ht0 : 0 ≤ t := by
        rw [htdef]
        exact div_nonneg (by linarith) (by linarith)
      have ht1 : t ≤ 1 := by
        rw [htdef, div_le_one (by linarith)]
        linarith
      have hz : (1 - t) • ymin + t • ymax ∈ ClBox s c σ :=
        hcent hminC hmaxC (by linarith) (by linarith) (by ring)
      have hzX : levPair v ℓ ((1 - t) • ymin + t • ymax) = levPair v ℓ y := by
        rw [levPair_smul_add, hminX, hmaxX, ← add_smul, show (1 - t) + t = 1 by ring, one_smul]
      have hzζ : ζ ((1 - t) • ymin + t • ymax) = ζ y := by
        rw [zeta_smul_add, hyminζ, hymaxζ]
        linarith [htmul]
      have hy0 : y - ((1 - t) • ymin + t • ymax) = 0 := by
        refine hker (y - ((1 - t) • ymin + t • ymax)) ?_ ?_ ?_
        · have hh : inner ℝ v ((1 - t) • ymin + t • ymax) = inner ℝ v y := by
            have h := congrArg Prod.fst hzX
            simpa [levPair] using h
          rw [inner_sub_right, hh, sub_self]
        · have hh : ℓ ((1 - t) • ymin + t • ymax) = ℓ y := by
            have h := congrArg Prod.snd hzX
            simpa [levPair] using h
          rw [map_sub, hh, sub_self]
        · rw [map_sub, hzζ, sub_self]
      rw [sub_eq_zero] at hy0
      rw [hy0]
      exact hz

/-- `sInf A = - sSup (-A)` for a set bounded above. -/
theorem sInf_eq_neg_sSup {A : Set ℝ} (hne : (-A).Nonempty) (hb : BddAbove (-A)) :
    sInf A = -sSup (-A) := by
  have h := csInf_neg (s := -A) hne hb
  rwa [neg_neg] at h

/-- **The minimal height is the negative of the maximal height of `-ζ`.** -/
theorem fMin_eq_neg_fMax (ζ : R3 →L[ℝ] ℝ) (v : R3) (ℓ : R3 →L[ℝ] ℝ) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (X : ℝ × ℝ) (hX : X ∈ boxShadow s c σ v ℓ) :
    fMin ζ v ℓ s c σ X = -fMax (-ζ) v ℓ s c σ X := by
  rw [fMin, fMax, Work.Drive.Mono.fibreMin, Work.Drive.Mono.fibreMax]
  simp only [innerSL_apply_apply]
  have hne : (ζ '' {y : R3 | y ∈ ClBox s c σ ∧ inner ℝ v y = X.1 ∧ ℓ y = X.2}).Nonempty := by
    obtain ⟨y, hy⟩ := fibre_nonempty (v := v) (ℓ := ℓ) hX
    rw [fibre_eq_set] at hy
    exact ⟨ζ y, y, hy, rfl⟩
  have hbd : BddBelow (ζ '' {y : R3 | y ∈ ClBox s c σ ∧ inner ℝ v y = X.1 ∧ ℓ y = X.2}) :=
    ((isCompact_fibre_set (s := s) (c := c) (σ := σ) (v := v) (ℓ := ℓ) X).image
      ζ.continuous).bddBelow
  have himg : (-ζ) '' {y : R3 | y ∈ ClBox s c σ ∧ inner ℝ v y = X.1 ∧ ℓ y = X.2}
      = -(ζ '' {y : R3 | y ∈ ClBox s c σ ∧ inner ℝ v y = X.1 ∧ ℓ y = X.2}) := by
    ext t
    rw [Set.mem_neg, mem_image, mem_image]
    constructor
    · rintro ⟨y, hy, hyeq⟩
      rw [neg_apply] at hyeq
      exact ⟨y, hy, by linarith⟩
    · rintro ⟨y, hy, hyeq⟩
      exact ⟨y, hy, by rw [neg_apply]; linarith⟩
  rw [himg]
  refine sInf_eq_neg_sSup ?_ ?_
  · obtain ⟨a, ha⟩ := hne
    exact ⟨-a, by rwa [Set.mem_neg, neg_neg]⟩
  · obtain ⟨m, hm⟩ := hbd
    exact ⟨-m, fun a ha => by
      rw [Set.mem_neg] at ha
      simpa using neg_le_neg (hm ha)⟩

/-- **The maximal height over the shadow of the box is continuous** (this is
`Work.Drive.Mono.fibreMax_continuous` in the vocabulary of this file). -/
theorem continuousOn_fMax {ζ : R3 →L[ℝ] ℝ} {v : R3} {ℓ : R3 →L[ℝ] ℝ} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} (hker : HasTrivKernel v ℓ ζ) (hs : 0 < s) :
    ContinuousOn (fMax ζ v ℓ s c σ) (boxShadow s c σ v ℓ) := by
  have hker' : ∀ y : R3, innerSL ℝ v y = 0 → ℓ y = 0 → ζ y = 0 → y = 0 := by
    intro y h1 h2 h3
    exact hker y (by simpa [innerSL_apply_apply] using h1) h2 h3
  have h := Work.Drive.Mono.fibreMax_continuous hs c σ (p := innerSL ℝ v) (q := ℓ) (ζ := ζ) hker'
  have hset : {w : ℝ × ℝ | ∃ y ∈ closure (Submission.PBox s c σ),
        innerSL ℝ v y = w.1 ∧ ℓ y = w.2} = boxShadow s c σ v ℓ := by
    rw [boxShadow, shadow]
    ext w
    constructor
    · rintro ⟨y, hy, h1, h2⟩
      refine ⟨y, hy, ?_⟩
      show ((inner ℝ v y : ℝ), ℓ y) = w
      rw [← innerSL_apply_apply, h1, h2]
    · rintro ⟨y, hy, hyw⟩
      refine ⟨y, hy, ?_, ?_⟩
      · show innerSL ℝ v y = w.1
        rw [innerSL_apply_apply]
        exact congrArg Prod.fst hyw
      · exact congrArg Prod.snd hyw
  rw [hset] at h
  exact h

/-- **The minimal height over the shadow of the box is continuous.** -/
theorem continuousOn_fMin {ζ : R3 →L[ℝ] ℝ} {v : R3} {ℓ : R3 →L[ℝ] ℝ} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} (hker : HasTrivKernel v ℓ ζ) (hs : 0 < s) :
    ContinuousOn (fMin ζ v ℓ s c σ) (boxShadow s c σ v ℓ) := by
  have hker' : HasTrivKernel v ℓ (-ζ) := by
    intro y h1 h2 h3
    exact hker y h1 h2 (by simpa using h3)
  have h : ContinuousOn (fun X => -fMax (-ζ) v ℓ s c σ X) (boxShadow s c σ v ℓ) :=
    (continuousOn_fMax (ζ := -ζ) hker' hs).neg
  refine h.congr ?_
  intro X hX
  exact fMin_eq_neg_fMax ζ v ℓ s c σ X hX

/-- **The maximal height over the shadow of the box is concave.** -/
theorem concaveOn_fMax {ζ : R3 →L[ℝ] ℝ} {v : R3} {ℓ : R3 →L[ℝ] ℝ} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} :
    ConcaveOn ℝ (boxShadow s c σ v ℓ) (fMax ζ v ℓ s c σ) := by
  have hconv : Convex ℝ (ClBox s c σ) := (Work.Topology.SphereSlicing.convex_PBox s c σ).closure
  refine ⟨convex_boxShadow s c σ v ℓ, ?_⟩
  intro x hx y hy a b ha hb hab
  obtain ⟨y₁, hy₁, hy₁ζ⟩ := fMax_mem (ζ := ζ) hx
  obtain ⟨y₂, hy₂, hy₂ζ⟩ := fMax_mem (ζ := ζ) hy
  have hzmem : a • y₁ + b • y₂ ∈ fibre v ℓ s c σ (a • x + b • y) :=
    mem_fibre_of (hconv (mem_ClBox_of_mem_fibre hy₁) (mem_ClBox_of_mem_fibre hy₂) ha hb hab)
      (by rw [levPair_smul_add, levPair_eq_of_mem_fibre hy₁, levPair_eq_of_mem_fibre hy₂])
  calc a • fMax ζ v ℓ s c σ x + b • fMax ζ v ℓ s c σ y
      = ζ (a • y₁ + b • y₂) := by
        rw [← hy₁ζ, ← hy₂ζ, zeta_smul_add]
        simp [smul_eq_mul]
    _ ≤ fMax ζ v ℓ s c σ (a • x + b • y) := le_fMax_of_mem_fibre hzmem

/-- **The minimal height over the shadow of the box is convex.** -/
theorem convexOn_fMin {ζ : R3 →L[ℝ] ℝ} {v : R3} {ℓ : R3 →L[ℝ] ℝ} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} :
    ConvexOn ℝ (boxShadow s c σ v ℓ) (fMin ζ v ℓ s c σ) := by
  have hconv : Convex ℝ (ClBox s c σ) := (Work.Topology.SphereSlicing.convex_PBox s c σ).closure
  refine ⟨convex_boxShadow s c σ v ℓ, ?_⟩
  intro x hx y hy a b ha hb hab
  obtain ⟨y₁, hy₁, hy₁ζ⟩ := fMin_mem (ζ := ζ) hx
  obtain ⟨y₂, hy₂, hy₂ζ⟩ := fMin_mem (ζ := ζ) hy
  have hzmem : a • y₁ + b • y₂ ∈ fibre v ℓ s c σ (a • x + b • y) :=
    mem_fibre_of (hconv (mem_ClBox_of_mem_fibre hy₁) (mem_ClBox_of_mem_fibre hy₂) ha hb hab)
      (by rw [levPair_smul_add, levPair_eq_of_mem_fibre hy₁, levPair_eq_of_mem_fibre hy₂])
  calc fMin ζ v ℓ s c σ (a • x + b • y)
      ≤ ζ (a • y₁ + b • y₂) := fMin_le_of_mem_fibre hzmem
    _ = a • fMin ζ v ℓ s c σ x + b • fMin ζ v ℓ s c σ y := by
        rw [zeta_smul_add, hy₁ζ, hy₂ζ]
        simp [smul_eq_mul]

end

/-- **The fibre facts and the height functions of the fibre model of a level of the tilted sweep.**

Available: `height_basic.fibre_eq_set` (`fibre v ℓ s c σ X = {y | y ∈ ClBox ∧ ⟪v,y⟫ = X.1 ∧ ℓ y =
X.2}`, the bridge to `fibreMax`/`fibreMin`), `height_basic.fibre_nonempty`,
`height_basic.isCompact_fibre_set`, `height_basic.fMax_mem` and `height_basic.fMin_mem` (both extrema
are attained).  The remaining work is the `Icc`/`Ioo` descriptions (`Icc` from attainedness plus
`le_fMax`/`fMin_le`, the `Icc ⊆` direction using that the fibre is a convex set on which `ζ` has
trivial kernel, and `Ioo` from `PBox = interior (ClBox)`), the strict inequality on `interior W`, and
the continuity/concavity of `fMax` and convexity of `fMin`. -/
theorem height_facts {ζ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ}
    {s : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    (hker : Work.Drive.Mono.FiberModel.HasTrivKernel v ℓ ζ) (hs : 0 < s) :
    (∀ X ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ,
        (Work.Drive.Mono.FiberModel.fibre v ℓ s c σ X).Nonempty) ∧
    (∀ X ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ,
        ζ '' Work.Drive.Mono.FiberModel.fibre v ℓ s c σ X =
          Set.Icc (Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ X)
            (Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ X)) ∧
    (∀ X ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ,
        Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ X ≤ Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ X) ∧
    (∀ X ∈ interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ),
        Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ X < Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ X) ∧
    (∀ X ∈ interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ),
        ζ '' {y ∈ Submission.PBox s c σ | Work.Drive.Mono.FiberModel.levPair v ℓ y = X} =
          Set.Ioo (Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ X)
            (Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ X)) ∧
    (∀ y : LeanEval.KnotTheory.PardonDistortion.R3,
        y ∈ Work.Drive.Mono.FiberModel.ClBox s c σ ↔
          (Work.Drive.Mono.FiberModel.levPair v ℓ y ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ ∧
            Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ (Work.Drive.Mono.FiberModel.levPair v ℓ y) ≤ ζ y ∧
            ζ y ≤ Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ (Work.Drive.Mono.FiberModel.levPair v ℓ y))) ∧
    ContinuousOn (Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ)
      (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) ∧
    ContinuousOn (Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ)
      (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) ∧
    ConcaveOn ℝ (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ)
      (Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ) ∧
    ConvexOn ℝ (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ)
      (Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ)
:= by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X hX
    exact fibre_nonempty hX
  · intro X hX
    exact fibre_image_Icc (ζ := ζ) hX
  · intro X hX
    obtain ⟨y, hy, hyζ⟩ := fMin_mem (ζ := ζ) hX
    rw [← hyζ]
    exact le_fMax_of_mem_fibre hy
  · intro X hX
    obtain ⟨y, hy, hyX⟩ := exists_mem_interior_ClBox_of_mem_interior (v := v) (ℓ := ℓ) hs hX
    have h := zeta_mem_Ioo_of_mem_interior hker hy hyX
    exact lt_trans h.1 h.2
  · intro X hX
    exact image_PBox_fibre_eq_Ioo hker hs hX
  · intro y
    exact mem_ClBox_iff hker
  · exact continuousOn_fMax hker hs
  · exact continuousOn_fMin hker hs
  · exact concaveOn_fMax
  · exact convexOn_fMin

end Work.Drive.Mono.FiberModel
