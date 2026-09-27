import Mathlib
import Submission.Work.Drive.N2Lead.pinFlow
import Submission.Work.Drive.N2Lead.landingWide_band
import Submission.Work.Drive.N2Lead.range_eq_connectedComponentIn
import Submission.Work.Drive.N2Lead.exists_continuous_arcLift
import Submission.Work.Drive.N2C.levelCurves_ofComponentCurves
import Submission.Work.Drive.N2.exists_levelComponentCurves

/-!
# The dichotomy of the saddle pin (an independent proof of `saddlePin_oneComp_or`)

`Work.Drive.N2Lead.saddlePin_oneComp_or` says: for every small `η`, at least one of the two collar
levels `f p ∓ 3η/2` of the saddle window carries its *pin* on a single component of the level.
This file proves it (in the `Work.Drive.N2C` namespace) from the bricks on disk:

* the pin classification at the anchor level (`Work.Drive.N2Lead.SaddleChart.pin_eq_arcs`) and its
  **upper-level twin** `pin_eq_arcs_up` (proved here);
* the flow rows at the four arc junctions (`Work.Drive.N2Lead.flow_arcIds`);
* the two-sided wide landing (`Work.Drive.N2Lead.landingWide_band`);
* the continuous lift of an arc to the parameter of a component of the level
  (`Work.Drive.N2Lead.exists_continuous_arcLift`).

The mathematical content is the split/merge dichotomy of Morse theory.
-/

namespace Work.Drive.N2C

set_option maxHeartbeats 1600000

open scoped Manifold ContDiff Topology
open Set Filter

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

section Algebra

/-- The square of the principal square root. -/
lemma sq_of_sqrt_add {a b : ℝ} :
    (Complex.sqrt ((a : ℂ) + (b : ℂ) * Complex.I)) ^ 2 = ((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I :=
  Work.Drive.N2.complex_sqrt_sq _

/-- The square of a scaled square root. -/
lemma scaled_sq {r a b : ℝ} {c : ℂ} (hc : c ^ 2 = (a : ℂ) + (b : ℂ) * Complex.I) :
    ((((r : ℝ)) : ℂ) * c) ^ 2 = ((r ^ 2 * a : ℝ) : ℂ) + ((r ^ 2 * b : ℝ) : ℂ) * Complex.I := by
  rw [mul_pow, hc]
  push_cast
  ring

end Algebra

section Topology

/-- **The topological core of the dichotomy** (increasing lift).  Let `γ` be a continuous
`1`-periodic curve injective modulo `1`, and `α` an arc in its range lifted by a strictly increasing
continuous `τ` whose endpoints span less than one period.  Then the complement of the arc in the
range of `γ` is preconnected: it is the image of the closed interval `[τ u, τ (-u) + 1]`. -/
lemma isPreconnected_sdiff_arc_of_mono_lift {γ : ℝ → M} {α : ℝ → M} {τ : ℝ → ℝ} {u : ℝ}
    (hγc : Continuous γ) (hγper : ∀ x : ℝ, γ (x + 1) = γ x)
    (hγmod : ∀ x y : ℝ, γ x = γ y → ∃ k : ℤ, x = y + k)
    (hγα : ∀ w ∈ Ioo (-u) u, γ (τ w) = α w)
    (hτc : ContinuousOn τ (Icc (-u) u)) (hu : 0 < u)
    (hm : StrictMonoOn τ (Icc (-u) u)) :
    IsPreconnected (Set.range γ \ α '' Ioo (-u) u) := by
  classical
  have hmem1 : (-u : ℝ) ∈ Icc (-u) u := ⟨le_refl _, by linarith⟩
  have hmem2 : (u : ℝ) ∈ Icc (-u) u := ⟨by linarith, le_refl _⟩
  have hub : τ (-u) < τ u := hm hmem1 hmem2 (by linarith)
  have F1 : ∀ w ∈ Ioo (-u) u, τ w ∈ Ioo (τ (-u)) (τ u) := fun w hw =>
    ⟨hm hmem1 ⟨le_of_lt hw.1, le_of_lt hw.2⟩ hw.1, hm ⟨le_of_lt hw.1, le_of_lt hw.2⟩ hmem2 hw.2⟩
  have F2 : ∀ t ∈ Ioo (τ (-u)) (τ u), ∃ w ∈ Ioo (-u) u, τ w = t := by
    intro t ht
    have him := intermediate_value_Icc (show (-u : ℝ) ≤ u by linarith) hτc
      (show t ∈ Icc (τ (-u)) (τ u) from ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
    obtain ⟨w, hw, hwt⟩ := him
    refine ⟨w, ?_, hwt⟩
    rcases lt_or_eq_of_le hw.1 with h | h
    · rcases lt_or_eq_of_le hw.2 with h' | h'
      · exact ⟨h, h'⟩
      · exact absurd (hwt ▸ ht.2) (by rw [h']; exact lt_irrefl _)
    · exact absurd (hwt ▸ ht.1) (by rw [h]; exact lt_irrefl _)
  have hstrip1 : α '' Ioo (-u) u ⊆ γ '' Ioo (τ (-u)) (τ u) := by
    rintro x ⟨w, hw, rfl⟩
    exact ⟨τ w, F1 w hw, hγα w hw⟩
  have hstrip2 : γ '' Ioo (τ (-u)) (τ u) ⊆ α '' Ioo (-u) u := by
    rintro x ⟨t, ht, rfl⟩
    obtain ⟨w, hw, hwt⟩ := F2 t ht
    refine ⟨w, hw, ?_⟩
    rw [← hγα w hw, hwt]
  have hcompl : Set.range γ \ α '' Ioo (-u) u = γ '' Icc (τ u) (τ (-u) + 1) := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨⟨t, rfl⟩, hx⟩
      set t' : ℝ := Int.fract (t - τ u) + τ u with ht'def
      have ht'1 : τ u ≤ t' := by simp [ht'def, Int.fract_nonneg]
      have ht'2 : t' < τ u + 1 := by have := Int.fract_lt_one (t - τ u); rw [ht'def]; linarith
      have hγt' : γ t' = γ t := by
        have hkey : t' = t + -(⌊t - τ u⌋ : ℝ) := by
          rw [ht'def, Int.fract]; push_cast; ring
        rw [hkey]
        simpa using eq_of_add_intCast_of_periodic hγper t (-(⌊t - τ u⌋))
      refine ⟨t', ⟨ht'1, ?_⟩, hγt'⟩
      by_contra hle
      push_neg at hle
      have hmem : t' - 1 ∈ Ioo (τ (-u)) (τ u) := ⟨by linarith, by linarith⟩
      obtain ⟨w, hw, hwt⟩ := F2 (t' - 1) hmem
      refine hx ⟨w, hw, ?_⟩
      have hw1 : α w = γ (t' - 1) := by rw [← hγα w hw, hwt]
      rw [hw1, (hγper (t' - 1)).symm, show t' - 1 + 1 = t' by ring, hγt']
    · rintro x ⟨t, ht, rfl⟩
      refine ⟨⟨t, rfl⟩, fun hmem => ?_⟩
      obtain ⟨t', ht', hγt'⟩ := hstrip1 hmem
      obtain ⟨k, hk⟩ := hγmod t' t hγt'
      have hkt : (k : ℝ) = -(t - t') := by linarith [hk]
      have h1 : (k : ℝ) < 0 := by rw [hkt]; linarith [ht.1, ht'.2]
      have h2 : (-1 : ℝ) < (k : ℝ) := by rw [hkt]; linarith [ht.2, ht'.1]
      have hk0 : k = 0 := by
        have h1' : k < 0 := by exact_mod_cast h1
        have h2' : (-1 : ℤ) < k := by exact_mod_cast h2
        omega
      rw [hk0] at hk
      simp only [Int.cast_zero, add_zero] at hk
      exact absurd (hk ▸ ht'.2) (not_lt.mpr ht.1)
  rw [hcompl]
  exact IsPreconnected.image (isPreconnected_Icc (a := τ u) (b := τ (-u) + 1)) γ hγc.continuousOn

/-- **The topological core of the dichotomy.**  Same as `isPreconnected_sdiff_arc_of_mono_lift`
without the sign restriction on the lift: only the *span* `|τ u - τ (-u)| < 1` is needed. -/
lemma isPreconnected_sdiff_arc_of_lift {γ : ℝ → M} {α : ℝ → M} {τ : ℝ → ℝ} {u : ℝ}
    (hγc : Continuous γ) (hγper : ∀ x : ℝ, γ (x + 1) = γ x)
    (hγmod : ∀ x y : ℝ, γ x = γ y → ∃ k : ℤ, x = y + k)
    (hγα : ∀ w ∈ Ioo (-u) u, γ (τ w) = α w)
    (hτc : ContinuousOn τ (Icc (-u) u)) (hu : 0 < u)
    (hτm : StrictMonoOn τ (Icc (-u) u) ∨ StrictAntiOn τ (Icc (-u) u)) :
    IsPreconnected (Set.range γ \ α '' Ioo (-u) u) := by
  have hmem1 : (-u : ℝ) ∈ Icc (-u) u := ⟨le_refl _, by linarith⟩
  have hmem2 : (u : ℝ) ∈ Icc (-u) u := ⟨by linarith, le_refl _⟩
  rcases hτm with hm | hm
  · exact isPreconnected_sdiff_arc_of_mono_lift hγc hγper hγmod hγα hτc hu hm
  · have hlt : τ u < τ (-u) := hm hmem1 hmem2 (by linarith)
    have hm' : StrictMonoOn (fun w : ℝ => τ (-w)) (Icc (-u) u) := by
      intro x hx y hy hxy
      exact hm ⟨by linarith [hy.2], by linarith [hy.1]⟩
        ⟨by linarith [hx.2], by linarith [hx.1]⟩ (by linarith)
    have hc' : ContinuousOn (fun w : ℝ => τ (-w)) (Icc (-u) u) :=
      hτc.comp continuous_neg.continuousOn (fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩)
    have hkey := isPreconnected_sdiff_arc_of_mono_lift (α := fun w : ℝ => α (-w))
      (τ := fun w : ℝ => τ (-w)) hγc hγper hγmod
        (fun w hw => by rw [hγα (-w) ⟨by linarith [hw.2], by linarith [hw.1]⟩]) hc' hu hm'
    have himg : (fun w : ℝ => α (-w)) '' Ioo (-u) u = α '' Ioo (-u) u := by
      ext x
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨-w, ⟨by linarith [hw.2], by linarith [hw.1]⟩, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨-w, ⟨by linarith [hw.2], by linarith [hw.1]⟩, by simp⟩
    rw [himg] at hkey
    exact hkey

end Topology



section Arcs

variable {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p}

/-- **The anchor-arc parametrisation is injective** (on the interval on which its chart vectors lie
in the chart's target). -/
lemma SaddleChart_arcU_injOn (S : Work.Drive.N2Lead.SaddleChart D) {ηs : ℝ} (hηs : 0 ≤ ηs)
    (hηs1 : ηs ≤ 1) : Set.InjOn (fun w : ℝ => S.arcU ηs w) (Ioo (-2) 2) := by
  intro w hw w' hw' h
  have hw2 : |w| ≤ 2 := le_of_lt (abs_lt.mpr hw)
  have hw2' : |w'| ≤ 2 := le_of_lt (abs_lt.mpr hw')
  have hZ : S.Zc (S.arcU ηs w) = S.Zc (S.arcU ηs w') := congrArg S.Zc h
  rw [S.arcU_Zc hηs hηs1 hw2, S.arcU_Zc hηs hηs1 hw2'] at hZ
  have hlam : (((D.ρ D.j / 8 : ℝ)) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (div_pos (D.hρ D.j) (by norm_num))
  have hsq : ((ηs : ℂ) - (w : ℂ) * Complex.I) = ((ηs : ℂ) - (w' : ℂ) * Complex.I) := by
    have h1 : (Complex.I : ℂ) * Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I)
        = Complex.I * Complex.sqrt ((ηs : ℂ) - (w' : ℂ) * Complex.I) :=
      mul_left_cancel₀ hlam hZ
    have h2 := mul_left_cancel₀ Complex.I_ne_zero h1
    have h3 : (Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I)) ^ 2
        = (Complex.sqrt ((ηs : ℂ) - (w' : ℂ) * Complex.I)) ^ 2 := by rw [h2]
    rwa [Work.Drive.N2.complex_sqrt_sq, Work.Drive.N2.complex_sqrt_sq] at h3
  have him := congrArg Complex.im hsq
  have hw_eq : w = w' := by
    simpa [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im] using him
  exact hw_eq

/-- **The classification of the upper pin**: every point of the pin at the upper level lies on one of
the two arcs `arcR`, `arcL` (the mirror of `Work.Drive.N2Lead.SaddleChart.pin_eq_arcs`). -/
lemma SaddleChart_pin_eq_arcs_up (S : Work.Drive.N2Lead.SaddleChart D) {ηs m : ℝ} (hηs : 0 < ηs)
    (hηs1 : ηs ≤ 1) (hm0 : 0 ≤ m) (hm2 : m ≤ 2)
    {x : M}
    (hx : x ∈ Work.Drive.N2Lead.saddlePin D
      (f p + ((D.ρ D.j / 8 : ℝ)) ^ 2 * ηs) m) :
    ∃ w : ℝ, |w| ≤ m ∧ (x = S.arcR ηs w ∨ x = S.arcL ηs w) := by
  obtain ⟨hxsrc, hxnorm, hxval, hxin⟩ := hx
  have hx' : x ∈ S.φ'.source := by rw [S.source_eq]; exact hxsrc
  have hlam : 0 < (D.ρ D.j / 8 : ℝ) := div_pos (D.hρ D.j) (by norm_num)
  have hlam2 : 0 < ((D.ρ D.j / 8 : ℝ)) ^ 2 := pow_pos hlam 2
  have hre : ((S.Zc x) ^ 2).re = ((D.ρ D.j / 8 : ℝ)) ^ 2 * ηs := by
    have h := S.level_eq x hx'
    rw [hxval] at h
    linarith
  set w : ℝ := ((S.Zc x) ^ 2).im / ((D.ρ D.j / 8 : ℝ)) ^ 2 with hwdef
  have hw_eq : ((D.ρ D.j / 8 : ℝ)) ^ 2 * w = ((S.Zc x) ^ 2).im := by
    rw [hwdef, mul_div_cancel₀ _ (ne_of_gt hlam2)]
  have himabs : |((S.Zc x) ^ 2).im| ≤ m * ((D.ρ D.j / 8 : ℝ)) ^ 2 := by
    rw [S.Zc_sq_im_abs hx']; exact hxin
  have hw : |w| ≤ m := by
    rw [hwdef, abs_div, abs_of_pos hlam2, div_le_iff₀ hlam2]; exact himabs
  have hsq : (S.Zc x) ^ 2 = (S.Zc (S.arcR ηs w)) ^ 2 := by
    have h1 : (S.Zc (S.arcR ηs w)) ^ 2
        = ((((D.ρ D.j / 8 : ℝ)) ^ 2 * ηs : ℝ) : ℂ)
          + ((((D.ρ D.j / 8 : ℝ)) ^ 2 * w : ℝ) : ℂ) * Complex.I := by
      rw [S.arcR_Zc hηs.le hηs1 (le_trans hw hm2)]
      exact scaled_sq (sq_of_sqrt_add (a := ηs) (b := w))
    have h2 : (S.Zc x) ^ 2 = ((((D.ρ D.j / 8 : ℝ)) ^ 2 * ηs : ℝ) : ℂ)
          + ((((D.ρ D.j / 8 : ℝ)) ^ 2 * w : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, hre]
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add, hw_eq]
    rw [h1, h2]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact ⟨w, hw, Or.inl (S.injOn_Zc hx' (S.arcR_source hηs.le hηs1 (le_trans hw hm2)) h)⟩
  · refine ⟨w, hw, Or.inr ?_⟩
    refine S.injOn_Zc hx' (S.arcL_source hηs.le hηs1 (le_trans hw hm2)) ?_
    rw [S.arcL_Zc hηs.le hηs1 (le_trans hw hm2), h, S.arcR_Zc hηs.le hηs1 (le_trans hw hm2)]
    ring

end Arcs


section Main

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M]

open Work.Drive.Morse

/-- **The dichotomy of the saddle pin.** -/
theorem saddlePinDichotomy {f : M → ℝ} (hf : Work.Drive.Morse.IsMorseDistinct f) {p : M}
    (D : Work.Drive.N2.WindowDatum f p) (hsad : D.s₁ D.j ≠ D.s₂ D.j)
    (hmorse : Work.Drive.Morse.MorseLemma2) :
    ∃ η₂ : ℝ, 0 < η₂ ∧ ∀ η : ℝ, 0 < η → η ≤ η₂ →
      Work.Drive.N2Lead.OnOneComponent (f := f) (f p - 3 * η / 2)
          (Work.Drive.N2Lead.saddlePin D (f p - 3 * η / 2) (99 / 50)) ∨
      Work.Drive.N2Lead.OnOneComponent (f := f) (f p + 3 * η / 2)
          (Work.Drive.N2Lead.saddlePin D (f p + 3 * η / 2) (99 / 50)) := by
  classical
  have hsgn : D.s₁ D.j = - D.s₂ D.j := by
    rcases D.hsgn D.j with ⟨h1, h2⟩
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp_all
  obtain ⟨S⟩ := Work.Drive.N2Lead.saddleChart_exists D hsgn
  let lam0 : ℝ := D.ρ D.j / 8
  have hlam0pos : 0 < lam0 := by
    dsimp only [lam0]; exact div_pos (D.hρ D.j) (by norm_num)
  refine ⟨min (D.ηd / 2) (lam0 ^ 2 / 40),
    lt_min (by linarith [D.hηd]) (by nlinarith [hlam0pos]), ?_⟩
  intro η hη hle
  have hηd : η < D.ηd := by
    have h1 : η ≤ D.ηd / 2 := le_trans hle (min_le_left _ _)
    linarith
  have hsmall : η < lam0 ^ 2 / 20 := by
    have h1 : η ≤ lam0 ^ 2 / 40 := le_trans hle (min_le_right _ _)
    linarith [h1, hlam0pos]
  let ηs : ℝ := 3 * η / 2 / lam0 ^ 2
  have hηspos : 0 < ηs := by
    dsimp only [ηs]; positivity
  have hηs1 : ηs ≤ 1 := by
    have h : ηs < 1 / 10 := by
      dsimp only [ηs]
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [hsmall, sq_pos_of_pos hlam0pos]
    linarith
  -- the two levels
  have hlow : f p - lam0 ^ 2 * ηs = f p - 3 * η / 2 := by
    dsimp only [ηs]
    field_simp
  have hhigh : f p + lam0 ^ 2 * ηs = f p + 3 * η / 2 := by
    dsimp only [ηs]
    field_simp
  set a : ℝ := f p - lam0 ^ 2 * ηs with hadef
  set u : ℝ := f p + lam0 ^ 2 * ηs with hudef
  set m : ℝ := 99 / 50 with hmdef
  set c₀ : ℝ := 39 / 20 with hc₀def
  have hm0 : 0 ≤ m := by rw [hmdef]; norm_num
  have hm2 : m ≤ 2 := by rw [hmdef]; norm_num
  have hm2lt : m < 2 := by rw [hmdef]; norm_num
  have hc₀pos : 0 < c₀ := by rw [hc₀def]; norm_num
  have hc₀1 : 1 < c₀ := by rw [hc₀def]; norm_num
  have hc₀2 : c₀ ≤ 2 := by rw [hc₀def]; norm_num
  have hc₀2lt : c₀ < 2 := by rw [hc₀def]; norm_num
  have key : Work.Drive.N2Lead.OnOneComponent (f := f) a (Work.Drive.N2Lead.saddlePin D a m) ∨
      Work.Drive.N2Lead.OnOneComponent (f := f) u (Work.Drive.N2Lead.saddlePin D u m) := by
    by_cases hleft : Work.Drive.N2Lead.OnOneComponent (f := f) a (Work.Drive.N2Lead.saddlePin D a m)
    · exact Or.inl hleft
    · refine Or.inr ?_
      -- the pinned arc of the anchor level
      have harcU0 : S.arcU ηs 0 ∈ Work.Drive.N2Lead.saddlePin D a m := by
        rw [hadef]
        exact S.arcU_mem_pin (ηs := ηs) (m := m) (w := 0) hηspos.le hηs1 hm0 hm2
          (by rw [abs_zero]; exact hm0)
      set K : Set M := connectedComponentIn {z : M | f z = a} (S.arcU ηs 0) with hKdef
      have hKsub : K ⊆ {z : M | f z = a} := connectedComponentIn_subset _ _
      have hKpre : IsPreconnected K := isPreconnected_connectedComponentIn
      -- the two anchor arcs lie in `K`
      have harcU_K : ∀ w ∈ Icc (-2 : ℝ) 2, S.arcU ηs w ∈ K := by
        intro w hw
        have hcont : ContinuousOn (fun u : ℝ => S.arcU ηs u) (Icc (-2) 2) :=
          S.continuousOn_arcU hηspos hηs1
        have hconn : IsPreconnected ((fun u : ℝ => S.arcU ηs u) '' Icc (-2) 2) :=
          IsPreconnected.image isPreconnected_Icc _ hcont
        have hsub : ((fun u : ℝ => S.arcU ηs u) '' Icc (-2) 2) ⊆ {z : M | f z = a} := by
          rintro x ⟨v, hv, rfl⟩
          rw [hadef]
          exact S.arcU_level hηspos.le hηs1
            (le_trans (abs_le.mpr ⟨hv.1, hv.2⟩) (by norm_num))
        have hmems : (fun u : ℝ => S.arcU ηs u) 0
            ∈ ((fun u : ℝ => S.arcU ηs u) '' Icc (-2) 2) :=
          ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩
        exact hconn.subset_connectedComponentIn hmems hsub ⟨w, hw, rfl⟩
      have harcD_K_of : S.arcD ηs 0 ∈ K → ∀ w ∈ Icc (-2 : ℝ) 2, S.arcD ηs w ∈ K := by
        intro hD0 w hw
        have hcont : ContinuousOn (fun u : ℝ => S.arcD ηs u) (Icc (-2) 2) :=
          S.continuousOn_arcD hηspos hηs1
        have hconn : IsPreconnected ((fun u : ℝ => S.arcD ηs u) '' Icc (-2) 2) :=
          IsPreconnected.image isPreconnected_Icc _ hcont
        have hsub : ((fun u : ℝ => S.arcD ηs u) '' Icc (-2) 2) ⊆ {z : M | f z = a} := by
          rintro x ⟨v, hv, rfl⟩
          rw [hadef]
          exact S.arcD_level hηspos.le hηs1
            (le_trans (abs_le.mpr ⟨hv.1, hv.2⟩) (by norm_num))
        have hmems : (fun u : ℝ => S.arcD ηs u) 0
            ∈ ((fun u : ℝ => S.arcD ηs u) '' Icc (-2) 2) :=
          ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩
        have h1 : ((fun u : ℝ => S.arcD ηs u) '' Icc (-2) 2) ⊆
            connectedComponentIn {z : M | f z = a} (S.arcD ηs 0) :=
          hconn.subset_connectedComponentIn hmems hsub
        have h2 : connectedComponentIn {z : M | f z = a} (S.arcD ηs 0) = K :=
          (connectedComponentIn_eq hD0).symm
        exact h2 ▸ h1 ⟨w, hw, rfl⟩
      have hD0out : S.arcD ηs 0 ∉ K := by
        intro hD0
        refine hleft (fun x hx y hy => ?_)
        have hxK : x ∈ K := by
          obtain ⟨w, hw, h | h⟩ := S.pin_eq_arcs hηspos hηs1 hm0 hm2 hx
          · rw [h]; exact harcU_K w (abs_le.mp (le_trans hw hm2))
          · rw [h]; exact harcD_K_of hD0 w (abs_le.mp (le_trans hw hm2))
        have hyK : y ∈ K := by
          obtain ⟨w, hw, h | h⟩ := S.pin_eq_arcs hηspos hηs1 hm0 hm2 hy
          · rw [h]; exact harcU_K w (abs_le.mp (le_trans hw hm2))
          · rw [h]; exact harcD_K_of hD0 w (abs_le.mp (le_trans hw hm2))
        have hKx : connectedComponentIn {z : M | f z = a} x = K :=
          (connectedComponentIn_eq hxK).symm
        rw [hKx]; exact hyK
      -- (A) no point of the lower arc lies in `K`
      have harcD_out : ∀ w ∈ Icc (-2 : ℝ) 2, S.arcD ηs w ∉ K := by
        intro w hw hmem
        have hcont : ContinuousOn (fun u : ℝ => S.arcD ηs u) (Icc (-2) 2) :=
          S.continuousOn_arcD hηspos hηs1
        have hconn : IsPreconnected ((fun u : ℝ => S.arcD ηs u) '' Icc (-2) 2) :=
          IsPreconnected.image isPreconnected_Icc _ hcont
        have hsub : ((fun u : ℝ => S.arcD ηs u) '' Icc (-2) 2) ⊆ {z : M | f z = a} := by
          rintro x ⟨v, hv, rfl⟩
          rw [hadef]
          exact S.arcD_level hηspos.le hηs1
            (le_trans (abs_le.mpr ⟨hv.1, hv.2⟩) (by norm_num))
        have h1 : ((fun u : ℝ => S.arcD ηs u) '' Icc (-2) 2) ⊆
            connectedComponentIn {z : M | f z = a} (S.arcD ηs w) :=
          hconn.subset_connectedComponentIn ⟨w, hw, rfl⟩ hsub
        have h2 : connectedComponentIn {z : M | f z = a} (S.arcD ηs w) = K :=
          (connectedComponentIn_eq hmem).symm
        exact hD0out (h2 ▸ h1 ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩)
      -- (B) the small-invariant points of `K` in the chart are the arc
      have hstrip_id : ∀ x ∈ K, x ∈ S.φ'.source → |((S.Zc x) ^ 2).im| < c₀ * lam0 ^ 2 →
          x ∈ S.arcU ηs '' Ioo (-c₀) c₀ := by
        intro x hxK hxsrc hxin
        set w : ℝ := ((S.Zc x) ^ 2).im / lam0 ^ 2 with hwdef
        have hwlameq : lam0 ^ 2 * w = ((S.Zc x) ^ 2).im := by
          rw [hwdef, mul_div_cancel₀ _ (ne_of_gt (by positivity : (0:ℝ) < lam0 ^ 2))]
        have hwlt : |w| < c₀ := by
          rw [hwdef, abs_div, abs_of_pos (by positivity : (0:ℝ) < lam0 ^ 2),
            div_lt_iff₀ (by positivity)]
          exact hxin
        have hxpin : x ∈ Work.Drive.N2Lead.saddlePin D a c₀ := by
          refine ⟨by rw [← S.source_eq]; exact hxsrc, ?_, hKsub hxK, ?_⟩
          · -- the chart norm is < ρ
            have hre : ((S.Zc x) ^ 2).re = -lam0 ^ 2 * ηs := by
              have h := S.level_eq x hxsrc
              have h2 : f x = f p - lam0 ^ 2 * ηs := hKsub hxK
              linarith [h, h2]
            have hcomplex : (S.Zc x) ^ 2
                = ((lam0 ^ 2 : ℝ) : ℂ) * (((-ηs : ℝ) : ℂ) + ((w : ℝ) : ℂ) * Complex.I) := by
              apply Complex.ext
              · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
                  Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_one, add_zero]
                rw [hre]; ring
              · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero,
                  Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, zero_add]
                rw [hwlameq]; ring
            have hnorm : ‖S.Zc x‖ ^ 2
                = lam0 ^ 2 * ‖((-ηs : ℝ) : ℂ) + ((w : ℝ) : ℂ) * Complex.I‖ := by
              have hnorm_r : ‖(((lam0 ^ 2 : ℝ)) : ℂ)‖ = lam0 ^ 2 := by
                rw [Complex.norm_def, Complex.normSq_ofReal, ← pow_two, Real.sqrt_sq (by positivity)]
              rw [← norm_pow, hcomplex, norm_mul, hnorm_r]
            have harg : ‖((-ηs : ℝ) : ℂ) + ((w : ℝ) : ℂ) * Complex.I‖ ≤ 3 := by
              have h2 : ‖((-ηs : ℝ) : ℂ) + ((w : ℝ) : ℂ) * Complex.I‖ ^ 2 = ηs ^ 2 + w ^ 2 := by
                rw [Complex.sq_norm, Complex.normSq_apply]
                simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
                  Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
                  Complex.add_im, Complex.mul_im, zero_add]
                ring
              have h3 : ηs ^ 2 + w ^ 2 ≤ 9 := by
                have h4 : w ^ 2 < c₀ ^ 2 := by
                  nlinarith [abs_lt.mp hwlt, sq_nonneg w]
                nlinarith [hηs1, hc₀2, h4, sq_nonneg ηs]
              nlinarith [norm_nonneg (((-ηs : ℝ) : ℂ) + ((w : ℝ) : ℂ) * Complex.I), h2, h3]
            have hlt2 : ‖S.Zc x‖ ^ 2 < (8 * lam0) ^ 2 := by
              rw [hnorm]
              nlinarith [harg, hlam0pos]
            have hnorm_lt : ‖S.Zc x‖ < 8 * lam0 := by
              have h := sq_lt_sq.mp hlt2
              rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity : (0:ℝ) ≤ 8 * lam0)]
                at h
              exact h
            have hnorm_eq : ‖D.φ D.j x‖ = ‖S.Zc x‖ := by
              rw [← S.norm_eq hxsrc, ← S.norm_Zc]
            have hρ : D.ρ D.j = 8 * lam0 := by
              rw [show lam0 = D.ρ D.j / 8 from rfl]; ring
            rw [hnorm_eq, hρ]
            exact hnorm_lt
          · rw [← S.Zc_sq_im_abs hxsrc]; exact le_of_lt hxin
        obtain ⟨w', hw', h | h⟩ := S.pin_eq_arcs hηspos hηs1 hc₀pos.le hc₀2 hxpin
        · refine ⟨w', ?_, h.symm⟩
          have hA : ((S.Zc (S.arcU ηs w')) ^ 2).im = lam0 ^ 2 * w' := by
            have h1 := S.arcU_imSq (ηs := ηs) (w := w') hηspos.le hηs1 (le_trans hw' hc₀2)
            simpa only [lam0] using h1
          have hB : ((S.Zc x) ^ 2).im = lam0 ^ 2 * w' := by rw [h]; exact hA
          have hw'eq : w' = ((S.Zc x) ^ 2).im / lam0 ^ 2 := by
            rw [hB]; field_simp
          have h1 : |w'| < c₀ := by
            rw [hw'eq, abs_div, abs_of_pos (by positivity : (0:ℝ) < lam0 ^ 2),
              div_lt_iff₀ (by positivity)]
            exact hxin
          exact ⟨(abs_lt.mp h1).1, (abs_lt.mp h1).2⟩
        · exact absurd (h ▸ hxK) (harcD_out w' (abs_le.mp (le_trans hw' hc₀2)))
      -- (B2) the level curves of the anchor level and the lift of the arc
      have hreg_a : ∀ x : M, f x = a → ¬ IsCritical f x := by
        intro x hx hcrit
        obtain ⟨i, hi⟩ := D.hcover x hcrit
        rw [← hi] at hx
        rcases eq_or_ne i D.j with h | hi'
        · subst h
          rw [D.hxj] at hx
          dsimp only [a] at hx
          nlinarith [hηspos, sq_pos_of_pos hlam0pos]
        · have h2 := D.hsep i D.j hi'
          rw [D.hxj] at h2
          have h4 : lam0 ^ 2 * ηs < 2 * D.ηd := by
            have h5 : lam0 ^ 2 * ηs = 3 * η / 2 := by dsimp only [ηs]; field_simp
            rw [h5]
            linarith [hηd, hη, D.hηd]
          rw [hx] at h2
          rw [show f p - lam0 ^ 2 * ηs - f p = -(lam0 ^ 2 * ηs) by ring, abs_neg,
            abs_of_nonneg (by positivity)] at h2
          linarith [h2, h4]
      have harcU0_level : f (S.arcU ηs 0) = a := by
        dsimp only [a]
        exact S.arcU_level hηspos.le hηs1 (by norm_num)
      obtain ⟨nf, γ, hsm, hper, hinj, hval, hder, hker, hcov, hdisj, hcl, hmod⟩ :=
        Work.Drive.N2.exists_levelComponentCurves f hf.1 a hreg_a ⟨S.arcU ηs 0, harcU0_level⟩
      have hcover' : ∀ x : M, f x = a → ∃ (i : Fin nf) (t : ℝ), x = γ i t := by
        intro x hx
        have hmem : x ∈ ⋃ i, Set.range (γ i) := by rw [hcov]; exact hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
        obtain ⟨t, ht⟩ := hi
        exact ⟨i, t, ht.symm⟩
      obtain ⟨L⟩ := Work.Drive.N2C.levelCurves_ofComponentCurves (f := f) (a := a) hsm hper hinj
        hval hker hcover' hdisj
      obtain ⟨i, t₀, ht₀⟩ := L.cover (S.arcU ηs 0) harcU0_level
      have hK_eq : K = Set.range (L.γ i) := by
        have h := Work.Drive.N2Lead.range_eq_connectedComponentIn L i t₀
        rw [← ht₀] at h
        exact h.symm
      obtain ⟨τ, hτc, hτγ⟩ := Work.Drive.N2Lead.exists_continuous_arcLift L i (J := Ioo (-2) 2)
        isOpen_Ioo (convex_Ioo (-2 : ℝ) 2).isPreconnected
        ((S.continuousOn_arcU hηspos hηs1).mono
          (fun w hw => ⟨le_of_lt hw.1, le_of_lt hw.2⟩))
        (fun w hw => by
          rw [← hK_eq]
          exact harcU_K w (abs_le.mp (le_of_lt (abs_lt.mpr hw))))
      have hτinj : Set.InjOn τ (Ioo (-2) 2) := by
        intro w hw w' hw' h
        have h1 : S.arcU ηs w = S.arcU ηs w' := by rw [← hτγ w hw, ← hτγ w' hw', h]
        exact SaddleChart_arcU_injOn S hηspos.le hηs1 hw hw' h1
      have hτmono : StrictMonoOn τ (Ioo (-2) 2) ∨ StrictAntiOn τ (Ioo (-2) 2) :=
        hτc.strictMonoOn_of_injOn_Ioo (by norm_num) hτinj
      have hτc' : ContinuousOn τ (Icc (-c₀) c₀) :=
        hτc.mono (fun w hw => ⟨by linarith [hw.1, hc₀2lt], by linarith [hw.2, hc₀2lt]⟩)
      have hτmono' : StrictMonoOn τ (Icc (-c₀) c₀) ∨ StrictAntiOn τ (Icc (-c₀) c₀) :=
        hτmono.imp
          (fun h => h.mono (fun w hw => ⟨by linarith [hw.1, hc₀2lt], by linarith [hw.2, hc₀2lt]⟩))
          (fun h => h.mono (fun w hw => ⟨by linarith [hw.1, hc₀2lt], by linarith [hw.2, hc₀2lt]⟩))
      have hτγ' : ∀ w ∈ Ioo (-c₀) c₀, L.γ i (τ w) = S.arcU ηs w :=
        fun w hw => hτγ w ⟨by linarith [hw.1, hc₀2lt], by linarith [hw.2, hc₀2lt]⟩
      -- (C) the box condition
      have hbox : ∀ x : M, x ∈ K → x ∉ S.arcU ηs '' Ioo (-c₀) c₀ →
          (x ∉ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j) ∨
            c₀ * lam0 ^ 2 ≤ |((S.Zc x) ^ 2).im|) := by
        intro x hxK hxC
        rcases em (x ∈ (D.φ D.j).source) with hxsrc | hxsrc
        · right
          by_contra hlt
          have hlt' : |((S.Zc x) ^ 2).im| < c₀ * lam0 ^ 2 := lt_of_not_ge hlt
          have hxsrc' : x ∈ S.φ'.source := by rw [S.source_eq]; exact hxsrc
          have habs : |((S.Zc x) ^ 2).im|
              = |((Work.Drive.N2.chartZ (D.φ D.j) x) ^ 2).im| :=
            (sq_eq_sq_iff_abs_eq_abs _ _).mp (S.im_sq_eq x hxsrc')
          exact hxC (hstrip_id x hxK hxsrc' hlt')
        · left
          intro hmem
          exact hxsrc hmem.1
      -- (D) the flow carries `K` minus the arc onto the upper level
      have hFcont : Continuous fun y : M => D.Φ (u - a, y) :=
        D.hΦsm.continuous.comp (continuous_const.prodMk continuous_id)
      have hFsub : ∀ y ∈ K \ S.arcU ηs '' Ioo (-c₀) c₀, f (D.Φ (u - a, y)) = u := by
        intro y hy
        have hyK := hy.1
        have hyC := hy.2
        have hboxy := hbox y hyK hyC
        have hfy : f y = a := hKsub hyK
        have h1 : lam0 ^ 2 * (2 * η / lam0 ^ 2) = 2 * η := by
          field_simp
        have hbpos : 0 < 2 * η / lam0 ^ 2 := by positivity
        have hb10 : 2 * η / lam0 ^ 2 < 1 / 10 := by
          rw [div_lt_iff₀ (by positivity)]
          nlinarith [hsmall, sq_pos_of_pos hlam0pos]
        have hsep : (D.ρ D.j / 8) ^ 2 * (2 * η / lam0 ^ 2) < 2 * D.ηd := by
          rw [show (D.ρ D.j / 8) = lam0 from rfl, h1]
          linarith
        have hband : f y ∈ Ioo (f p - lam0 ^ 2 * (2 * η / lam0 ^ 2))
            (f p + lam0 ^ 2 * (2 * η / lam0 ^ 2)) := by
          rw [h1, hfy]
          refine ⟨?_, ?_⟩ <;> dsimp only [a] <;> nlinarith [hη, hlam0pos]
        have hb : u ∈ Ioo (f p - lam0 ^ 2 * (2 * η / lam0 ^ 2))
            (f p + lam0 ^ 2 * (2 * η / lam0 ^ 2)) := by
          rw [h1]
          refine ⟨?_, ?_⟩ <;> dsimp only [u] <;> nlinarith [hη, hlam0pos]
        have hland := Work.Drive.N2Lead.landingWide_band D hsgn S.φ' S.Zc lam0 rfl S.source_eq
          S.ball_eq S.Zc_eq (fun y hy => S.level_eq y (by rw [S.source_eq]; exact hy)) S.im_inv
          (η := 2 * η / lam0 ^ 2) hbpos hb10 hc₀1 hsep (y := y) hboxy hband (b := u) hb
        rw [hfy] at hland
        exact hland
      -- the two junction images
      have hηs10 : ηs < 1 / 10 := by
        rw [show ηs = 3 * η / 2 / lam0 ^ 2 from rfl, div_lt_iff₀ (by positivity)]
        nlinarith [hsmall, sq_pos_of_pos hlam0pos]
      have hηb10 : 2 * η / lam0 ^ 2 < 1 / 10 := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [hsmall, sq_pos_of_pos hlam0pos]
      have hjun := Work.Drive.N2Lead.flow_arcIds D hsgn S (η := η) (ηs := ηs) (c₀ := m)
        (δ := 1 / 20) hη rfl (by norm_num) (by norm_num) hηs10 hηb10
        (by rw [hmdef]; norm_num) hm2
      have hua : u - a = 3 * η := by
        have h : lam0 ^ 2 * ηs = 3 * η / 2 := by dsimp only [ηs]; field_simp
        dsimp only [u, a]
        rw [h]; ring
      have hnotC_m : S.arcU ηs m ∉ S.arcU ηs '' Ioo (-c₀) c₀ := by
        rintro ⟨w, hw, hw'⟩
        have h1 : m ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hm0], hm2lt⟩
        have h2 : w ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hw.1, hc₀2lt], by linarith [hw.2, hc₀2lt]⟩
        have h3 : m = w := SaddleChart_arcU_injOn S hηspos.le hηs1 h1 h2 hw'.symm
        have h4 : m < c₀ := by rw [h3]; exact hw.2
        rw [hmdef, hc₀def] at h4
        exact absurd h4 (by norm_num)
      have hnotC_nm : S.arcU ηs (-m) ∉ S.arcU ηs '' Ioo (-c₀) c₀ := by
        rintro ⟨w, hw, hw'⟩
        have h1 : -m ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hm0], by linarith [hm0]⟩
        have h2 : w ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hw.1, hc₀2lt], by linarith [hw.2, hc₀2lt]⟩
        have h3 : -m = w := SaddleChart_arcU_injOn S hηspos.le hηs1 h1 h2 hw'.symm
        have h4 : -c₀ < -m := by rw [h3]; exact hw.1
        rw [hmdef, hc₀def] at h4
        exact absurd h4 (by norm_num)
      -- the component of `arcR m` on the upper level
      set K' : Set M := connectedComponentIn {z : M | f z = u} (S.arcR ηs m) with hK'def
      have hFpre : IsPreconnected ((fun y : M => D.Φ (u - a, y)) ''
          (K \ S.arcU ηs '' Ioo (-c₀) c₀)) := by
        rw [hK_eq]
        exact IsPreconnected.image (isPreconnected_sdiff_arc_of_lift (γ := L.γ i)
          (α := fun w : ℝ => S.arcU ηs w) (τ := τ) (L.sm i).continuous (L.per i) (L.modOne i)
          hτγ' hτc' hc₀pos hτmono') _ hFcont.continuousOn
      have hFpre_sub : ((fun y : M => D.Φ (u - a, y)) ''
          (K \ S.arcU ηs '' Ioo (-c₀) c₀)) ⊆ {z : M | f z = u} := by
        rintro z ⟨y, hy, rfl⟩
        exact hFsub y hy
      have hmemR : S.arcR ηs m ∈ ((fun y : M => D.Φ (u - a, y)) ''
          (K \ S.arcU ηs '' Ioo (-c₀) c₀)) :=
        ⟨S.arcU ηs m, ⟨harcU_K m (show m ∈ Icc (-2 : ℝ) 2 from ⟨by linarith [hm0], hm2⟩),
          hnotC_m⟩, by rw [hua]; exact hjun.1⟩
      have hmemL : S.arcL ηs (-m) ∈ ((fun y : M => D.Φ (u - a, y)) ''
          (K \ S.arcU ηs '' Ioo (-c₀) c₀)) :=
        ⟨S.arcU ηs (-m), ⟨harcU_K (-m)
          (show -m ∈ Icc (-2 : ℝ) 2 from ⟨by linarith [hm2], by linarith [hm0]⟩),
          hnotC_nm⟩, by rw [hua]; exact hjun.2.1⟩
      have hRm : S.arcR ηs m ∈ K' := hFpre.subset_connectedComponentIn hmemR hFpre_sub hmemR
      have hLm : S.arcL ηs (-m) ∈ K' := hFpre.subset_connectedComponentIn hmemR hFpre_sub hmemL
      have hR_K' : ∀ w ∈ Icc (-m) m, S.arcR ηs w ∈ K' := by
        intro w hw
        have hcont : ContinuousOn (fun u : ℝ => S.arcR ηs u) (Icc (-m) m) :=
          (S.continuousOn_arcR hηspos hηs1).mono
            (fun x hx => show x ∈ Icc (-2 : ℝ) 2 from ⟨by linarith [hx.1, hm2], by linarith [hx.2, hm2]⟩)
        have hconn : IsPreconnected ((fun u : ℝ => S.arcR ηs u) '' Icc (-m) m) :=
          IsPreconnected.image isPreconnected_Icc _ hcont
        have hsub : ((fun u : ℝ => S.arcR ηs u) '' Icc (-m) m) ⊆ {z : M | f z = u} := by
          rintro z ⟨v, hv, rfl⟩
          dsimp only [u]
          exact S.arcR_level hηspos.le hηs1 (le_trans (show |v| ≤ m from abs_le.mpr ⟨hv.1, hv.2⟩) hm2)
        exact hconn.subset_connectedComponentIn ⟨m, ⟨by linarith [hm0], le_rfl⟩, rfl⟩ hsub
          ⟨w, hw, rfl⟩
      have hL_K' : ∀ w ∈ Icc (-m) m, S.arcL ηs w ∈ K' := by
        intro w hw
        have hcont : ContinuousOn (fun u : ℝ => S.arcL ηs u) (Icc (-m) m) :=
          (S.continuousOn_arcL hηspos hηs1).mono
            (fun x hx => show x ∈ Icc (-2 : ℝ) 2 from ⟨by linarith [hx.1, hm2], by linarith [hx.2, hm2]⟩)
        have hconn : IsPreconnected ((fun u : ℝ => S.arcL ηs u) '' Icc (-m) m) :=
          IsPreconnected.image isPreconnected_Icc _ hcont
        have hsub : ((fun u : ℝ => S.arcL ηs u) '' Icc (-m) m) ⊆ {z : M | f z = u} := by
          rintro z ⟨v, hv, rfl⟩
          dsimp only [u]
          exact S.arcL_level hηspos.le hηs1 (le_trans (show |v| ≤ m from abs_le.mpr ⟨hv.1, hv.2⟩) hm2)
        have hmems : S.arcL ηs (-m) ∈ ((fun u : ℝ => S.arcL ηs u) '' Icc (-m) m) :=
          ⟨-m, ⟨by linarith [hm0], by linarith [hm0]⟩, rfl⟩
        have h1 := hconn.subset_connectedComponentIn hmems hsub
        have h2 : connectedComponentIn {z : M | f z = u} (S.arcL ηs (-m)) = K' :=
          (connectedComponentIn_eq hLm).symm
        rw [h2] at h1
        exact h1 ⟨w, hw, rfl⟩
      intro x hx y hy
      obtain ⟨wx, hwx, hxR⟩ := SaddleChart_pin_eq_arcs_up S hηspos hηs1 hm0 hm2 hx
      obtain ⟨wy, hwy, hyR⟩ := SaddleChart_pin_eq_arcs_up S hηspos hηs1 hm0 hm2 hy
      have hxK' : x ∈ K' := by
        rcases hxR with h | h
        · rw [h]; exact hR_K' wx (abs_le.mp hwx)
        · rw [h]; exact hL_K' wx (abs_le.mp hwx)
      have hyK' : y ∈ K' := by
        rcases hyR with h | h
        · rw [h]; exact hR_K' wy (abs_le.mp hwy)
        · rw [h]; exact hL_K' wy (abs_le.mp hwy)
      have hcomp : connectedComponentIn {z : M | f z = u} x = K' :=
        (connectedComponentIn_eq hxK').symm
      rw [hcomp]
      exact hyK'
  rw [hlow, hhigh] at key
  exact key


end Main

end Work.Drive.N2C
