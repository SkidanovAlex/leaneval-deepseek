/-
# `Work.RPB.B1a.isConservativeOn_chainIntegral`

Let `g : ℂ → ℂ → ℂ` be jointly continuous on `U ×ˢ chainTrace L`, and suppose that for every
`ζ ∈ chainTrace L` the partial map `w ↦ g w ζ` is complex differentiable on `U`.  Then
`w ↦ chainIntegral (fun ζ => g w ζ) L` (`= ∫_L g w`) is conservative on `U`.

The proof is the classical Fubini argument: for a rectangle `Rectangle z w ⊆ U` we must show
that the integral over its boundary vanishes.  Exchanging the boundary integral with the chain
integral (a finite sum of segment integrals) reduces this to the fact that each partial map
`η ↦ g η ζ` is holomorphic on `U`, hence conservative.

The exchange of the two integrations is the whole content; it is carried out here directly,
without any differentiation under the integral sign: the boundary integral is written as an
iterated real interval integral, and the chain integral is expanded into its segment integrals,
so that only Fubini (for iterated interval integrals) and additivity of the integral are needed.
-/
import Mathlib
import Submission.Work.RPB.B1a.SegChain

namespace Work.RPB.B1a

open Complex Set MeasureTheory intervalIntegral
open scoped Topology

noncomputable section

/-! ## Integrability of a parametric interval integral

If `F : ℝ → ℝ → ℂ` is continuous on a closed box, then `x ↦ ∫ t in c..d, F x t` is interval
integrable.  This is the only place where a measure-theoretic input is needed; it is deduced from
Fubini's theorem (`Integrable.integral_prod_left`). -/

lemma intervalIntegrable_paramIntegral {F : ℝ → ℝ → ℂ} {a b c d : ℝ}
    (hF : ContinuousOn (Function.uncurry F) (Set.uIcc a b ×ˢ Set.uIcc c d)) :
    IntervalIntegrable (fun x : ℝ => ∫ t in c..d, F x t) volume a b := by
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (uIoc a b)).prod (volume.restrict (uIoc c d))) := by
    have h1 : IntegrableOn (Function.uncurry F) (uIcc a b ×ˢ uIcc c d) volume :=
      ContinuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc) hF
    have h2 : IntegrableOn (Function.uncurry F) (uIoc a b ×ˢ uIoc c d) volume :=
      h1.mono_set (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h2
    exact h2
  rw [intervalIntegrable_iff, IntegrableOn]
  rcases le_total c d with hcd | hcd
  · rw [show (fun x : ℝ => ∫ t in c..d, F x t) =
        fun x => ∫ t, F x t ∂(volume.restrict (uIoc c d)) from ?_]
    · exact hint.integral_prod_left
    · funext x
      rw [intervalIntegral.integral_of_le hcd, uIoc_of_le hcd]
  · rw [show (fun x : ℝ => ∫ t in c..d, F x t) =
        fun x => -(∫ t, F x t ∂(volume.restrict (uIoc c d))) from ?_]
    · exact hint.integral_prod_left.neg
    · funext x
      rw [intervalIntegral.integral_of_ge hcd, uIoc_comm, uIoc_of_le hcd]

/-! ## Fubini for the wedge (rectangle boundary) integral -/

/-- The `Complex.wedgeIntegral` of a parametric integral is the integral of the `wedgeIntegral`s. -/
lemma wedgeIntegral_intervalIntegral_swap {h : ℝ → ℂ → ℂ} {z w : ℂ}
    (hcont : ContinuousOn (fun p : ℝ × ℂ => h p.1 p.2) (Icc 0 1 ×ˢ Rectangle z w)) :
    wedgeIntegral z w (fun η => ∫ t in (0:ℝ)..1, h t η) =
      ∫ t in (0:ℝ)..1, wedgeIntegral z w (fun η => h t η) := by
  have hswap : Continuous fun p : ℝ × ℝ => (p.2, p.1) := by fun_prop
  have hcX : ContinuousOn (fun p : ℝ × ℝ => h p.1 ((p.2 : ℂ) + z.im * I))
      (uIcc 0 1 ×ˢ uIcc z.re w.re) := by
    refine hcont.comp
      (by fun_prop : Continuous fun p : ℝ × ℝ => (p.1, (p.2:ℂ) + z.im*I)).continuousOn ?_
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    rw [uIcc_of_le zero_le_one] at hs
    refine ⟨hs, ?_⟩
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    simp [Complex.add_re, Complex.add_im, hx]
  have hcY : ContinuousOn (fun p : ℝ × ℝ => h p.1 ((w.re : ℂ) + p.2 * I))
      (uIcc 0 1 ×ˢ uIcc z.im w.im) := by
    refine hcont.comp
      (by fun_prop : Continuous fun p : ℝ × ℝ => (p.1, (w.re:ℂ) + p.2*I)).continuousOn ?_
    rintro ⟨s, y⟩ ⟨hs, hy⟩
    rw [uIcc_of_le zero_le_one] at hs
    refine ⟨hs, ?_⟩
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    simp [Complex.add_re, Complex.add_im, hy]
  have hPK : IntervalIntegrable (fun t : ℝ => ∫ x in z.re..w.re, h t (x + z.im * I)) volume 0 1 := by
    refine intervalIntegrable_paramIntegral (F := fun t x => h t (x + z.im * I)) ?_
    change ContinuousOn (fun p : ℝ × ℝ => h p.1 ((p.2 : ℂ) + z.im * I))
      (uIcc 0 1 ×ˢ uIcc z.re w.re)
    exact hcX
  have hQK : IntervalIntegrable (fun t : ℝ => ∫ y in z.im..w.im, h t (w.re + y * I)) volume 0 1 := by
    refine intervalIntegrable_paramIntegral (F := fun t y => h t (w.re + y * I)) ?_
    change ContinuousOn (fun p : ℝ × ℝ => h p.1 ((w.re : ℂ) + p.2 * I))
      (uIcc 0 1 ×ˢ uIcc z.im w.im)
    exact hcY
  have hintX : IntegrableOn (Function.uncurry (fun x t : ℝ => h t ((x:ℂ) + z.im * I)))
      (uIoc z.re w.re ×ˢ uIoc 0 1) volume := by
    apply (ContinuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc) ?_).mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
    change ContinuousOn (fun p : ℝ × ℝ => h p.2 ((p.1 : ℂ) + z.im * I))
      (uIcc z.re w.re ×ˢ uIcc 0 1)
    exact hcX.comp hswap.continuousOn (by rintro ⟨x, t⟩ ⟨hx, ht⟩; exact ⟨ht, hx⟩)
  have hintY : IntegrableOn (Function.uncurry (fun y t : ℝ => h t ((w.re:ℂ) + y * I)))
      (uIoc z.im w.im ×ˢ uIoc 0 1) volume := by
    apply (ContinuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc) ?_).mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
    change ContinuousOn (fun p : ℝ × ℝ => h p.2 ((w.re : ℂ) + p.1 * I))
      (uIcc z.im w.im ×ˢ uIcc 0 1)
    exact hcY.comp hswap.continuousOn (by rintro ⟨y, t⟩ ⟨hy, ht⟩; exact ⟨ht, hy⟩)
  have h1 := intervalIntegral_intervalIntegral_swap (F := fun x t : ℝ => h t (x + z.im * I)) hintX
  have h2 := intervalIntegral_intervalIntegral_swap (F := fun y t : ℝ => h t (w.re + y * I)) hintY
  have key : (∫ t in (0:ℝ)..1, ((∫ x in z.re..w.re, h t (x + z.im*I))
        + I * (∫ y in z.im..w.im, h t (w.re + y*I))))
      = (∫ t in (0:ℝ)..1, ∫ x in z.re..w.re, h t (x + z.im*I))
        + I * (∫ t in (0:ℝ)..1, ∫ y in z.im..w.im, h t (w.re + y*I)) := by
    rw [intervalIntegral.integral_add hPK (hQK.const_mul I), intervalIntegral.integral_const_mul]
  simp only [Complex.wedgeIntegral, smul_eq_mul]
  rw [h1, h2, key]

/-! ## Elementary linearity of the wedge integral -/

lemma wedgeIntegral_add {f g : ℂ → ℂ} {z w : ℂ}
    (hf1 : IntervalIntegrable (fun x : ℝ => f (x + z.im*I)) volume z.re w.re)
    (hf2 : IntervalIntegrable (fun y : ℝ => f (w.re + y*I)) volume z.im w.im)
    (hg1 : IntervalIntegrable (fun x : ℝ => g (x + z.im*I)) volume z.re w.re)
    (hg2 : IntervalIntegrable (fun y : ℝ => g (w.re + y*I)) volume z.im w.im) :
    wedgeIntegral z w (f + g) = wedgeIntegral z w f + wedgeIntegral z w g := by
  simp only [Complex.wedgeIntegral, Pi.add_apply]
  rw [intervalIntegral.integral_add hf1 hg1, intervalIntegral.integral_add hf2 hg2, smul_add]
  ring

lemma wedgeIntegral_mul_const (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    wedgeIntegral z w (fun η => f η * c) = wedgeIntegral z w f * c := by
  simp only [Complex.wedgeIntegral, smul_eq_mul]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
  ring

/-! ## Membership in a rectangle -/

lemma mem_Rectangle_of_horizontalLine (z w : ℂ) {x : ℝ} (hx : x ∈ uIcc z.re w.re) :
    ((x : ℂ) + z.im * I) ∈ Rectangle z w := by
  rw [Complex.Rectangle, Complex.mem_reProdIm]
  simp [Complex.add_re, Complex.add_im, hx]

lemma mem_Rectangle_of_verticalLine (z w : ℂ) {y : ℝ} (hy : y ∈ uIcc z.im w.im) :
    ((w.re : ℂ) + y * I) ∈ Rectangle z w := by
  rw [Complex.Rectangle, Complex.mem_reProdIm]
  simp [Complex.add_re, Complex.add_im, hy]

lemma Rectangle_swap (z w : ℂ) : Rectangle z w = Rectangle w z := by
  rw [Complex.Rectangle, Complex.Rectangle, uIcc_comm z.re w.re, uIcc_comm z.im w.im]

/-! ## Interval integrability of the chain integral along a line -/

/-- Along a continuous parametrized line `γ`, the function
`x ↦ chainIntegral (fun ζ => g (γ x) ζ) L` is interval integrable (when `g` is continuous on the
product of the line with the trace of the chain). -/
lemma intervalIntegrable_chainIntegral_line {g : ℂ → ℂ → ℂ} (L : List (ℂ × ℂ)) {γ : ℝ → ℂ}
    {α β : ℝ}
    (h : ContinuousOn (fun p : ℝ × ℂ => g (γ p.1) p.2) (uIcc α β ×ˢ chainTrace L)) :
    IntervalIntegrable (fun x : ℝ => chainIntegral (fun ζ => g (γ x) ζ) L) volume α β := by
  induction L with
  | nil =>
    have h0 : (fun x : ℝ => chainIntegral (fun ζ => g (γ x) ζ) []) = fun _ => (0:ℂ) := by
      funext x; simp [chainIntegral]
    rw [h0]
    exact intervalIntegrable_const
  | cons s L ih =>
    obtain ⟨a, b⟩ := s
    have htail : ContinuousOn (fun p : ℝ × ℂ => g (γ p.1) p.2) (uIcc α β ×ˢ chainTrace L) :=
      h.mono (Set.prod_mono Subset.rfl (chainTrace_tail_subset_cons (a,b) L))
    have hseg : IntervalIntegrable (fun x : ℝ => segIntegral (fun ζ => g (γ x) ζ) a b)
        volume α β := by
      refine intervalIntegrable_paramIntegral
        (F := fun x t => g (γ x) (a + (t:ℂ)*(b-a)) * (b-a)) ?_
      have hφ : Continuous fun p : ℝ × ℝ => (p.1, a + (p.2:ℂ)*(b-a)) := by fun_prop
      refine (h.comp hφ.continuousOn ?_).mul_const (b - a)
      rintro ⟨x, t⟩ ⟨hx, ht⟩
      refine ⟨hx, ?_⟩
      have ht' : t ∈ Icc (0:ℝ) 1 := by rwa [uIcc_of_le zero_le_one] at ht
      exact mem_chainTrace_param List.mem_cons_self ht'
    rw [show (fun x : ℝ => chainIntegral (fun ζ => g (γ x) ζ) ((a,b) :: L))
        = (fun x : ℝ => segIntegral (fun ζ => g (γ x) ζ) a b)
          + (fun x : ℝ => chainIntegral (fun ζ => g (γ x) ζ) L) from by
      funext x; rw [chainIntegral_cons]; rfl]
    exact hseg.add (ih htail)

/-! ## Swapping the wedge integral with a segment integral -/

/-- The wedge integral commutes with a segment integral (Fubini). -/
lemma wedgeIntegral_segIntegral_swap {g : ℂ → ℂ → ℂ} {a b : ℂ} {z w : ℂ}
    (hcont : ContinuousOn (fun p : ℝ × ℂ => g p.2 (a + (p.1:ℂ)*(b-a)) * (b-a))
      (Icc 0 1 ×ˢ Rectangle z w)) :
    wedgeIntegral z w (fun η => segIntegral (fun ζ => g η ζ) a b)
      = segIntegral (fun ζ => wedgeIntegral z w (fun η => g η ζ)) a b := by
  rw [show (fun η => segIntegral (fun ζ => g η ζ) a b)
      = (fun η => ∫ t in (0:ℝ)..1, g η (a + (t:ℂ)*(b-a)) * (b-a)) from rfl,
    wedgeIntegral_intervalIntegral_swap (h := fun t η => g η (a + (t:ℂ)*(b-a)) * (b-a)) hcont,
    show segIntegral (fun ζ => wedgeIntegral z w (fun η => g η ζ)) a b
      = (∫ t in (0:ℝ)..1, wedgeIntegral z w (fun η => g η (a + (t:ℂ)*(b-a))) * (b-a)) from rfl]
  exact intervalIntegral.integral_congr fun t _ =>
    wedgeIntegral_mul_const (b-a) (fun η => g η (a + (t:ℂ)*(b-a))) z w

/-! ## Swapping the wedge integral with a chain integral -/

/-- The wedge integral commutes with the integral along a polygonal chain. -/
lemma wedgeIntegral_chainIntegral_swap {g : ℂ → ℂ → ℂ} (L : List (ℂ × ℂ)) {z w : ℂ}
    (hcont : ContinuousOn (fun p : ℂ × ℂ => g p.1 p.2) (Rectangle z w ×ˢ chainTrace L)) :
    wedgeIntegral z w (fun η => chainIntegral (fun ζ => g η ζ) L)
      = chainIntegral (fun ζ => wedgeIntegral z w (fun η => g η ζ)) L := by
  induction L with
  | nil => simp [chainIntegral, Complex.wedgeIntegral]
  | cons s L ih =>
    obtain ⟨a, b⟩ := s
    have hlineH : ContinuousOn (fun p : ℝ × ℂ => g ((p.1 : ℂ) + z.im * I) p.2)
        (uIcc z.re w.re ×ˢ chainTrace ((a, b) :: L)) := by
      refine hcont.comp
        (by fun_prop : Continuous fun p : ℝ × ℂ => ((p.1:ℂ) + z.im*I, p.2)).continuousOn ?_
      rintro ⟨x, ζ⟩ ⟨hx, hζ⟩
      exact ⟨mem_Rectangle_of_horizontalLine z w hx, hζ⟩
    have hlineV : ContinuousOn (fun p : ℝ × ℂ => g ((w.re : ℂ) + p.1 * I) p.2)
        (uIcc z.im w.im ×ˢ chainTrace ((a, b) :: L)) := by
      refine hcont.comp
        (by fun_prop : Continuous fun p : ℝ × ℂ => ((w.re:ℂ) + p.1*I, p.2)).continuousOn ?_
      rintro ⟨y, ζ⟩ ⟨hy, hζ⟩
      exact ⟨mem_Rectangle_of_verticalLine z w hy, hζ⟩
    have hseg_sub : chainTrace [(a, b)] ⊆ chainTrace ((a, b) :: L) :=
      chainTrace_mono fun s hs => by rw [List.mem_singleton] at hs; exact hs ▸ List.mem_cons_self
    have htail_sub : chainTrace L ⊆ chainTrace ((a, b) :: L) :=
      chainTrace_tail_subset_cons (a, b) L
    have hsegH : IntervalIntegrable (fun x : ℝ => segIntegral (fun ζ => g ((x:ℂ) + z.im*I) ζ) a b)
        volume z.re w.re := by
      have h' := intervalIntegrable_chainIntegral_line (L := [(a, b)])
        (γ := fun x : ℝ => (x:ℂ) + z.im*I)
        (hlineH.mono (Set.prod_mono Subset.rfl hseg_sub))
      simpa using h'
    have hsegV : IntervalIntegrable (fun y : ℝ => segIntegral (fun ζ => g ((w.re:ℂ) + y*I) ζ) a b)
        volume z.im w.im := by
      have h' := intervalIntegrable_chainIntegral_line (L := [(a, b)])
        (γ := fun y : ℝ => (w.re:ℂ) + y*I)
        (hlineV.mono (Set.prod_mono Subset.rfl hseg_sub))
      simpa using h'
    have htailH : IntervalIntegrable (fun x : ℝ => chainIntegral (fun ζ => g ((x:ℂ) + z.im*I) ζ) L)
        volume z.re w.re :=
      intervalIntegrable_chainIntegral_line (L := L) (γ := fun x : ℝ => (x:ℂ) + z.im*I)
        (hlineH.mono (Set.prod_mono Subset.rfl htail_sub))
    have htailV : IntervalIntegrable (fun y : ℝ => chainIntegral (fun ζ => g ((w.re:ℂ) + y*I) ζ) L)
        volume z.im w.im :=
      intervalIntegrable_chainIntegral_line (L := L) (γ := fun y : ℝ => (w.re:ℂ) + y*I)
        (hlineV.mono (Set.prod_mono Subset.rfl htail_sub))
    have hsegcont : ContinuousOn (fun p : ℝ × ℂ => g p.2 (a + (p.1:ℂ)*(b-a)) * (b-a))
        (Icc 0 1 ×ˢ Rectangle z w) := by
      have hφ : Continuous fun p : ℝ × ℂ => (p.2, a + (p.1:ℂ)*(b-a)) := by fun_prop
      refine (hcont.comp hφ.continuousOn ?_).mul_const (b - a)
      rintro ⟨t, η⟩ ⟨ht, hη⟩
      refine ⟨hη, ?_⟩
      exact mem_chainTrace_param (L := (a, b) :: L) List.mem_cons_self ht
    rw [show (fun η => chainIntegral (fun ζ => g η ζ) ((a,b) :: L))
        = (fun η => segIntegral (fun ζ => g η ζ) a b)
          + (fun η => chainIntegral (fun ζ => g η ζ) L) from by
      funext η; rw [chainIntegral_cons]; rfl]
    rw [wedgeIntegral_add hsegH hsegV htailH htailV,
      wedgeIntegral_segIntegral_swap hsegcont,
      ih (hcont.mono (Set.prod_mono Subset.rfl htail_sub)),
      chainIntegral_cons]

/-! ## The main result -/

theorem isConservativeOn_chainIntegral {U : Set ℂ} (L : List (ℂ × ℂ)) {g : ℂ → ℂ → ℂ}
    (hjoint : ContinuousOn (fun p : ℂ × ℂ => g p.1 p.2) (U ×ˢ chainTrace L))
    (hhol : ∀ ζ ∈ chainTrace L, DifferentiableOn ℂ (fun w => g w ζ) U) :
    Complex.IsConservativeOn (fun w => chainIntegral (fun ζ => g w ζ) L) U := by
  intro z w hzw
  have hzw' : Rectangle w z ⊆ U := by rw [Rectangle_swap]; exact hzw
  have hcont₁ : ContinuousOn (fun p : ℂ × ℂ => g p.1 p.2) (Rectangle z w ×ˢ chainTrace L) :=
    hjoint.mono (Set.prod_mono hzw Subset.rfl)
  have hcont₂ : ContinuousOn (fun p : ℂ × ℂ => g p.1 p.2) (Rectangle w z ×ˢ chainTrace L) :=
    hjoint.mono (Set.prod_mono hzw' Subset.rfl)
  have h1 : wedgeIntegral z w (fun η => chainIntegral (fun ζ => g η ζ) L)
      = chainIntegral (fun ζ => wedgeIntegral z w (fun η => g η ζ)) L :=
    wedgeIntegral_chainIntegral_swap L (z := z) (w := w) hcont₁
  have h2 : wedgeIntegral w z (fun η => chainIntegral (fun ζ => g η ζ) L)
      = chainIntegral (fun ζ => wedgeIntegral w z (fun η => g η ζ)) L :=
    wedgeIntegral_chainIntegral_swap L (z := w) (w := z) hcont₂
  rw [h1, h2]
  have hcongr : chainIntegral (fun ζ => wedgeIntegral w z (fun η => g η ζ)) L
      = chainIntegral (fun ζ => - wedgeIntegral z w (fun η => g η ζ)) L := by
    refine chainIntegral_congr L fun s hs ζ hζ => ?_
    have hζ' : ζ ∈ chainTrace L := segment_subset_chainTrace hs hζ
    have hc := (hhol ζ hζ').isConservativeOn z w hzw
    rw [hc]
    ring
  rw [hcongr, chainIntegral_neg]
  ring

end

end Work.RPB.B1a
