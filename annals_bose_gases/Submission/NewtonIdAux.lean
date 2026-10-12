import Mathlib
import ChallengeDeps
import Submission.RadialCutoff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Newtonian identity `∫ (Δφ)(x)/‖x−y‖ dx = −4π·φ(y)` (Layer 3)
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The underlying coordinate space of `ℝ³`. -/
abbrev X3 : Type := Fin 3 → ℝ

/-- Laplacian commutes with translation on the right. -/
lemma laplacian_comp_add_right (φ : ℝ³ → ℝ) (y : ℝ³) :
    (Δ fun u : ℝ³ => φ (u + y)) = fun u => (Δ φ) (u + y) := by
  funext u
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f := fun x : ℝ³ => φ (x + y)) euclBasis3]
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f := φ) euclBasis3]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedFDeriv_comp_add_right]

/-- Integral is invariant under translation (right addition). -/
lemma integral_add_right_eq (F : ℝ³ → ℝ) (y : ℝ³) :
    (∫ x : ℝ³, F (x + y)) = ∫ x : ℝ³, F x := by
  exact MeasureTheory.integral_add_right_eq_self F y

lemma integral_add_left_eq (F : ℝ³ → ℝ) (y : ℝ³) :
    (∫ x : ℝ³, F (y + x)) = ∫ x : ℝ³, F x := by
  exact MeasureTheory.integral_add_left_eq_self F y

/-- A smooth function with compact support stays smooth after translation. -/
lemma contDiff_translate (φ : ℝ³ → ℝ) (hφ : ContDiff ℝ ∞ φ) (y : ℝ³) :
    ContDiff ℝ ∞ (fun u : ℝ³ => φ (u + y)) := by
  exact hφ.comp (contDiff_id.add contDiff_const)

/-- Compact support is preserved by translation. -/
lemma hasCompactSupport_translate (φ : ℝ³ → ℝ) (hφcs : HasCompactSupport φ) (y : ℝ³) :
    HasCompactSupport (fun u : ℝ³ => φ (u + y)) := by
  rcases hφcs.isBounded.subset_closedBall (0 : ℝ³) with ⟨B, hBsub⟩
  let r : ℝ := B + ‖y‖
  refine HasCompactSupport.intro' (ProperSpace.isCompact_closedBall (0 : ℝ³) r) isClosed_closedBall ?_
  intro x hx
  have hnorm : r < ‖x‖ := by
    have hx' : ¬ dist x 0 ≤ r := by simpa using hx
    simpa [r, dist_eq_norm, dist_zero_right] using (not_le.mp hx')
  have harg : B < ‖x + y‖ := by
    have hxlarge : B + ‖y‖ < ‖x‖ := by simpa [r] using hnorm
    have htri : ‖x‖ ≤ ‖x + y‖ + ‖y‖ := by
      simpa using (norm_add_le (x + y) (-y) : ‖(x + y) + (-y)‖ ≤ ‖x + y‖ + ‖(-y : ℝ³)‖)
    linarith
  have hnot : x + y ∉ Metric.closedBall (0 : ℝ³) B := by
    rw [Metric.mem_closedBall]
    exact not_le.mpr (by simpa [dist_eq_norm] using harg)
  by_contra hz
  have hsupp : x + y ∈ Function.support φ := by
    simpa [Function.support] using hz
  exact hnot (hBsub (subset_tsupport φ hsupp))

/-- Translation reduction: `newton_integral_delta_zero` for the translated function implies
`newton_integral_delta` for the original. -/
theorem newton_integral_delta_of_zero {y : ℝ³} (φ : ℝ³ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hφcs : HasCompactSupport φ)
    (hzero : ∀ ψ : ℝ³ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : ℝ³, (Δ ψ) x * (‖x‖ : ℝ)⁻¹) = -4 * π * ψ 0) :
    (∫ x : ℝ³, (Δ φ) x * (‖x - y‖ : ℝ)⁻¹) = -4 * π * φ y := by
  let φy : ℝ³ → ℝ := fun u => φ (u + y)
  have hφy : ContDiff ℝ ∞ φy := by
    dsimp [φy]
    exact contDiff_translate φ hφ y
  have hφycs : HasCompactSupport φy := by
    dsimp [φy]
    exact hasCompactSupport_translate φ hφcs y
  have hmain := hzero φy hφy hφycs
  have hΔ : (fun u : ℝ³ => (Δ φy) u * (‖u‖ : ℝ)⁻¹) =
      fun u : ℝ³ => (Δ φ) (u + y) * (‖u‖ : ℝ)⁻¹ := by
    funext u
    have hc := laplacian_comp_add_right φ y
    have : (Δ φy) u = (Δ φ) (u + y) := by
      have := congrFun hc u
      simpa [φy] using this
    rw [this]
  have hpt : (fun u : ℝ³ => (Δ φ) (y + u) * (‖(y + u) - y‖ : ℝ)⁻¹) =
      (fun u : ℝ³ => (Δ φ) (u + y) * (‖u‖ : ℝ)⁻¹) := by
    funext u
    have hsub : (y + u) - y = u := by abel
    rw [hsub]
    rw [add_comm y u]
  have htr : (∫ x : ℝ³, (Δ φ) x * (‖x - y‖ : ℝ)⁻¹) =
      (∫ u : ℝ³, (Δ φ) (u + y) * (‖u‖ : ℝ)⁻¹) := by
    have h1 := integral_add_left_eq (fun x : ℝ³ => (Δ φ) x * (‖x - y‖ : ℝ)⁻¹) y
    -- h1 : ∫ x, F (y + x) = ∫ x, F x   where F x = (Δ φ) x * ‖x - y‖⁻¹
    calc
      (∫ x : ℝ³, (Δ φ) x * (‖x - y‖ : ℝ)⁻¹) = ∫ x : ℝ³, (Δ φ) (y + x) * (‖(y + x) - y‖ : ℝ)⁻¹ := by
        exact h1.symm
      _ = ∫ u : ℝ³, (Δ φ) (u + y) * (‖u‖ : ℝ)⁻¹ := by
        rw [hpt]
  calc
    (∫ x : ℝ³, (Δ φ) x * (‖x - y‖ : ℝ)⁻¹)
        = ∫ u : ℝ³, (Δ φ) (u + y) * (‖u‖ : ℝ)⁻¹ := htr
    _ = ∫ u : ℝ³, (Δ φy) u * (‖u‖ : ℝ)⁻¹ := by rw [hΔ]
    _ = -4 * π * φ y := by
          have hψ : φy 0 = φ y := by simp [φy]
          simpa [hψ] using hmain

section X3_MeanZero

/-- If `f` is zero on the complement of `s`, then the integral of `f` over the whole space equals
its integral over `s`. -/
lemma integral_eq_integral_on_support {f : X3 → ℝ} {s : Set X3} (hs : MeasurableSet s)
    (h : ∀ x, x ∉ s → f x = 0) : (∫ x : X3, f x) = ∫ x in s, f x := by
  have hpt : f = s.indicator f := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx, h x]
  exact (congrArg (fun g : X3 → ℝ => ∫ x : X3, g x) hpt).trans
    (integral_indicator (s := s) (f := f) (μ := volume) hs)

/-- A smooth compactly supported function on the coordinate space has zero integral of its
partial derivative in any coordinate direction. -/
lemma integral_fderiv_single_eq_zero (U : X3 → ℝ) (hU : ContDiff ℝ ∞ U)
    (hUcs : HasCompactSupport U) (i : Fin 3) :
    (∫ c : X3, fderiv ℝ U c (Pi.single i 1)) = 0 := by
  rcases hUcs.isBounded.subset_closedBall (0 : X3) with ⟨B0, hsub0⟩
  let B : ℝ := max (B0 + 1) 1
  have hB : 0 < B := by
    dsimp [B]
    exact lt_max_of_lt_right (by norm_num)
  have hB0 : B0 < B := by
    dsimp [B]
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hderiv0 : ∀ c : X3, ‖c‖ ≥ B → fderiv ℝ U c = 0 := by
    intro c hc
    have hcnot : c ∉ tsupport U := by
      intro hmem
      have hle0 : ‖c‖ ≤ B0 := by
        have hd : dist c 0 ≤ B0 := Metric.mem_closedBall.mp (hsub0 hmem)
        simpa [dist_eq_norm, dist_zero_right] using hd
      linarith
    exact fderiv_of_notMem_tsupport ℝ hcnot
  have hsup0 : ∀ c : X3, ‖c‖ ≥ B → U c = 0 := by
    intro c hc
    have hcnot : c ∉ Metric.closedBall (0 : X3) B0 := by
      rw [Metric.mem_closedBall]
      have : B0 < ‖c‖ := lt_of_lt_of_le hB0 hc
      exact not_le.mpr (by simpa [dist_eq_norm, dist_zero_right] using this)
    by_contra hz
    exact hcnot (hsub0 (subset_tsupport U (by simpa [Function.support] using hz)))
  let a : X3 := fun _ => -B
  let b : X3 := fun _ => B
  have hle : a ≤ b := by
    intro j
    dsimp [a, b]
    linarith
  let f : X3 → X3 := fun x => fun j => if j = i then U x else 0
  have hfC : ContDiff ℝ ∞ f := by
    change ContDiff ℝ ∞ (fun x : X3 => fun j : Fin 3 => if j = i then U x else 0)
    refine (contDiff_pi (n := ∞)).2 ?_
    intro j
    by_cases hji : j = i
    · have : (fun x : X3 => if j = i then U x else 0) = U := by
        funext x
        simp [hji]
      rw [this]
      exact hU
    · have : (fun x : X3 => if j = i then U x else 0) = fun _ : X3 => 0 := by
        funext x
        simp [hji]
      rw [this]
      exact contDiff_const
  have hcf : ContinuousOn f (Set.Icc a b) := hfC.continuous.continuousOn
  have hdiff : ∀ x : X3, DifferentiableAt ℝ f x :=
    fun x => (hfC.differentiable (by norm_num : (∞ : ℕ∞ω) ≠ 0)) x
  have hHd : ∀ x ∈ (Set.univ.pi fun j => Set.Ioo (a j) (b j)) \ (∅ : Set X3),
      HasFDerivAt f (fderiv ℝ f x) x := by
    intro x hx
    exact (hdiff x).hasFDerivAt
  have hderiv : ∀ x : X3, fderiv ℝ f x = ContinuousLinearMap.pi
      (fun j : Fin 3 => if j = i then fderiv ℝ U x else 0) := by
    intro x
    have hφ' : ∀ j : Fin 3, HasFDerivAt (fun x : X3 => f x j)
        (if j = i then fderiv ℝ U x else 0) x := by
      intro j
      by_cases hji : j = i
      · have hfun : (fun x : X3 => f x j) = U := by
          funext x
          simp [f, hji]
        rw [hfun]
        rw [hji]
        simpa using (hU.differentiable (by norm_num : (∞ : ℕ∞ω) ≠ 0) x).hasFDerivAt
      · have hfun : (fun x : X3 => f x j) = fun _ : X3 => 0 := by
          funext x
          simp [f, hji]
        rw [hfun]
        have : (if j = i then fderiv ℝ U x else 0) = 0 := by simp [hji]
        rw [this]
        exact (hasFDerivAt_const (c := (0 : ℝ)) x)
    have h := (hasFDerivAt_pi (φ := fun j x => f x j)
      (φ' := fun j => if j = i then fderiv ℝ U x else 0) (x := x)).2 hφ'
    have hh : HasFDerivAt f (ContinuousLinearMap.pi
        (fun j : Fin 3 => if j = i then fderiv ℝ U x else 0)) x := by
      simpa using h
    exact hh.fderiv
  have hid : ∀ x : X3, (∑ j : Fin 3, (fderiv ℝ f x) (Pi.single j 1) j) =
      fderiv ℝ U x (Pi.single i 1) := by
    intro x
    have h1 : ∀ j : Fin 3, j ≠ i → (fderiv ℝ f x) (Pi.single j 1) j = 0 := by
      intro j hji
      rw [hderiv x]
      simp [hji]
    calc
      (∑ j : Fin 3, (fderiv ℝ f x) (Pi.single j 1) j)
          = (fderiv ℝ f x) (Pi.single i 1) i := by
            exact Finset.sum_eq_single i (fun j _ hji => h1 j hji) (by intro hi; simp at hi)
      _ = fderiv ℝ U x (Pi.single i 1) := by
            rw [hderiv x]
            simp
  have hcontg : Continuous (fun x : X3 => fderiv ℝ U x (Pi.single i 1)) := by
    have hcont : Continuous (fun x : X3 => (fderiv ℝ U x : X3 →L[ℝ] ℝ)) :=
      ContDiff.continuous_fderiv hU (by norm_num : (∞ : ℕ∞ω) ≠ 0)
    exact hcont.clm_apply (continuous_const : Continuous fun _ : X3 => (Pi.single i (1 : ℝ) : X3))
  have hHi_int : IntegrableOn (fun x : X3 => fderiv ℝ U x (Pi.single i 1)) (Set.Icc a b) := by
    refine ContinuousOn.integrableOn_compact ?_ hcontg.continuousOn
    exact isCompact_Icc
  have hHi : IntegrableOn (fun x : X3 => ∑ j : Fin 3, (fderiv ℝ f x) (Pi.single j 1) j)
      (Set.Icc a b) := by
    refine hHi_int.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (hid x).symm
  have hbox := MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable (n := 2) (E := ℝ)
      a b hle f (fun x => fderiv ℝ f x) (∅ : Set X3) (by simp) hcf hHd hHi
  have hboxzero : (∫ x in Set.Icc a b, fderiv ℝ U x (Pi.single i 1)) = 0 := by
    have hb : (∫ x in Set.Icc a b, ∑ j : Fin 3, (fderiv ℝ f x) (Pi.single j 1) j) = 0 := by
      rw [hbox]
      apply Finset.sum_eq_zero
      intro j hj
      let insj : ℝ → (Fin 2 → ℝ) → X3 :=
        fun t x => Fin.insertNth (α := fun _ : Fin 3 => ℝ) j t x
      have hface : ∀ t : ℝ, |t| = B → ∀ x : Fin 2 → ℝ, f (insj t x) j = 0 := by
        intro t ht x
        simp [f]
        by_cases hji : j = i
        · simp [hji]
          have hz : insj t x j = t := by
            dsimp [insj]
            exact Fin.insertNth_apply_same (α := fun _ : Fin 3 => ℝ) j t x
          have hnorm : B ≤ ‖insj t x‖ := by
            have h1 : |insj t x j| ≤ ‖insj t x‖ := norm_le_pi_norm (insj t x) j
            rw [hz] at h1
            rw [ht] at h1
            exact h1
          exact hsup0 (insj t x) hnorm
        · simp [hji]
      have hb0 : (fun x : Fin 2 → ℝ => f (insj (b j) x) j) = fun _ : Fin 2 → ℝ => 0 := by
        funext x
        exact hface (b j) (by dsimp [b]; rw [abs_of_nonneg (le_of_lt hB)]) x
      have ha0 : (fun x : Fin 2 → ℝ => f (insj (a j) x) j) = fun _ : Fin 2 → ℝ => 0 := by
        funext x
        exact hface (a j) (by dsimp [a]; rw [abs_neg, abs_of_nonneg (le_of_lt hB)]) x
      have hterm : (∫ x : Fin 2 → ℝ in Set.Icc (a ∘ j.succAbove) (b ∘ j.succAbove),
            f (insj (b j) x) j) -
          (∫ x : Fin 2 → ℝ in Set.Icc (a ∘ j.succAbove) (b ∘ j.succAbove),
            f (insj (a j) x) j) = 0 := by
        rw [hb0, ha0]
        simp
      exact hterm
    have hb2 : (∫ x in Set.Icc a b, fderiv ℝ U x (Pi.single i 1)) =
        (∫ x in Set.Icc a b, ∑ j : Fin 3, (fderiv ℝ f x) (Pi.single j 1) j) := by
      exact congrArg (fun h : X3 → ℝ => ∫ x in Set.Icc a b, h x)
        (funext fun x => (hid x).symm)
    rw [hb2, hb]
  have hsupp : ∀ x : X3, x ∉ Set.Icc a b → fderiv ℝ U x (Pi.single i 1) = 0 := by
    intro x hx
    by_cases hbig : B ≤ ‖x‖
    · rw [hderiv0 x hbig]
      simp
    · exfalso
      have hlt : ‖x‖ < B := lt_of_not_ge hbig
      have hmem : x ∈ Set.Icc a b := by
        rw [Set.mem_Icc]
        constructor
        · intro j
          dsimp [a]
          have habs : |x j| ≤ ‖x‖ := norm_le_pi_norm x j
          have hle : |x j| ≤ B := le_trans habs (le_of_lt hlt)
          rcases abs_le.mp hle with ⟨h1, h2⟩
          linarith
        · intro j
          dsimp [b]
          have habs : |x j| ≤ ‖x‖ := norm_le_pi_norm x j
          have hle : |x j| ≤ B := le_trans habs (le_of_lt hlt)
          rcases abs_le.mp hle with ⟨h1, h2⟩
          linarith
      exact hx hmem
  calc
    (∫ c : X3, fderiv ℝ U c (Pi.single i 1))
        = ∫ c in Set.Icc a b, fderiv ℝ U c (Pi.single i 1) :=
          integral_eq_integral_on_support (f := fun c => fderiv ℝ U c (Pi.single i 1))
            (s := Set.Icc a b) measurableSet_Icc hsupp
    _ = 0 := hboxzero

end X3_MeanZero

section Transfer

/-- `WithLp.toLp` restricted to coordinates is a smooth map. -/
lemma contDiff_toLp : ContDiff ℝ ∞ (fun c : X3 => (WithLp.toLp 2 c : ℝ³)) := by
  rw [contDiff_piLp (p := 2) (𝕜 := ℝ) (n := ∞)]
  intro k
  have hfun : (fun c : X3 => (WithLp.toLp 2 c : ℝ³) k) = fun c : X3 => c k := by
    funext c
    simp
  rw [hfun]
  exact contDiff_apply (𝕜 := ℝ) (E := ℝ) (n := ∞) k

/-- The canonical map `X3 → ℝ³` is the continuous linear equivalence `cle`. -/
def cle : X3 ≃L[ℝ] ℝ³ := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm

/-- `cle` and `WithLp.toLp` agree on functions. -/
lemma cle_eq_toLp (c : X3) : cle c = (WithLp.toLp 2 c : ℝ³) := rfl

/-- Preimage under `cle` is image under its inverse. -/
lemma preimage_cle_eq_image (A : Set ℝ³) : cle ⁻¹' A = cle.symm '' A := by
  ext c
  constructor
  · intro hc
    refine ⟨cle c, hc, ?_⟩
    exact (cle.symm_apply_apply c).symm
  · rintro ⟨d, hdA, rfl⟩
    exact (cle.apply_symm_apply d) ▸ hdA

/-- Measure transfer: an integral over `ℝ³` equals the integral over `X3` of the pullback. -/
lemma integral_toLp (g : ℝ³ → ℝ) :
    (∫ u : X3, g (WithLp.toLp 2 u)) = ∫ x : ℝ³, g x := by
  let e : X3 ≃ᵐ ℝ³ := MeasurableEquiv.toLp 2 (Fin 3 → ℝ)
  have h : MeasurePreserving (e : X3 → ℝ³) :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).symm
  change (∫ u : X3, g (e u)) = ∫ x : ℝ³, g x
  exact MeasurePreserving.integral_comp' h g

/-- The chain rule for `u ∘ WithLp.toLp`. -/
lemma fderiv_comp_toLp {u : ℝ³ → ℝ} (hu : ContDiff ℝ ∞ u) (c v : X3) :
    fderiv ℝ (fun c : X3 => u (WithLp.toLp 2 c)) c v =
      fderiv ℝ u (WithLp.toLp 2 c) (WithLp.toLp 2 v) := by
  have hL : HasFDerivAt (fun c : X3 => (WithLp.toLp 2 c : ℝ³)) (cle.toContinuousLinearMap) c := by
    have h := PiLp.hasFDerivAt_toLp (p := 2) (𝕜 := ℝ) (c : X3)
    simpa [cle] using h
  have hg : DifferentiableAt ℝ u (WithLp.toLp 2 c) :=
    (hu.differentiable (by norm_num : (∞ : ℕ∞ω) ≠ 0) (WithLp.toLp 2 c))
  have hc := (hg.hasFDerivAt.comp c hL)
  have hmain := HasFDerivAt.fderiv hc
  change fderiv ℝ (u ∘ (WithLp.toLp 2 : X3 → ℝ³)) c v = fderiv ℝ u (WithLp.toLp 2 c) (WithLp.toLp 2 v)
  rw [hmain]
  simp [cle]

/-- Compact support is preserved by `WithLp.toLp` (a homeomorphism). -/
lemma hasCompactSupport_toLp_comp (u : ℝ³ → ℝ) (hu_cs : HasCompactSupport u) :
    HasCompactSupport (fun c : X3 => u (WithLp.toLp 2 c)) := by
  have hc_eq : (fun c : X3 => u (WithLp.toLp 2 c)) = fun c : X3 => u (cle c) := by
    funext c
    rw [cle_eq_toLp]
  rw [hc_eq]
  refine HasCompactSupport.intro' (K := cle ⁻¹' tsupport u) ?_ ?_ ?_
  · rw [preimage_cle_eq_image]
    exact hu_cs.image (cle.symm.continuous)
  · exact IsClosed.preimage cle.continuous (isClosed_tsupport u)
  · intro c hc
    by_contra hz
    have hmem : cle c ∈ tsupport u := subset_tsupport u (by simpa [Function.support] using hz)
    exact hc hmem

end Transfer
section EMeanZero

/-- The integral over the whole coordinate space of a continuous function with compact support
exists. (wrapper) -/
lemma integrable_pderiv_X3 (U : X3 → ℝ) (hU : ContDiff ℝ ∞ U) (hUcs : HasCompactSupport U)
    (j : Fin 3) : Integrable (fun c : X3 => fderiv ℝ U c (Pi.single j 1)) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · have hcont : Continuous (fun c : X3 => (fderiv ℝ U c : X3 →L[ℝ] ℝ)) :=
      ContDiff.continuous_fderiv hU (by norm_num : (∞ : ℕ∞ω) ≠ 0)
    exact hcont.clm_apply (continuous_const : Continuous fun _ : X3 => (Pi.single j (1 : ℝ) : X3))
  · refine HasCompactSupport.intro' (K := tsupport U) hUcs (isClosed_tsupport U) ?_
    intro c hc
    rw [fderiv_of_notMem_tsupport ℝ hc]
    simp

/-- Every directional derivative of a smooth compactly supported function on `ℝ³` has zero
integral. -/
lemma integral_fderiv_eq_zero {u : ℝ³ → ℝ} (hu : ContDiff ℝ ∞ u) (hu_cs : HasCompactSupport u) :
    ∀ w : ℝ³, (∫ x : ℝ³, fderiv ℝ u x w) = 0 := by
  intro w
  let U : X3 → ℝ := fun c => u (WithLp.toLp 2 c)
  have hUc : ContDiff ℝ ∞ U := by
    dsimp [U]
    exact hu.comp contDiff_toLp
  have hUcs : HasCompactSupport U := by
    dsimp [U]
    exact hasCompactSupport_toLp_comp u hu_cs
  have hzero : ∀ j : Fin 3, (∫ c : X3, fderiv ℝ U c (Pi.single j 1)) = 0 :=
    fun j => integral_fderiv_single_eq_zero (U := U) hUc hUcs j
  have hint : ∀ j : Fin 3, Integrable (fun c : X3 => fderiv ℝ U c (Pi.single j 1)) :=
    integrable_pderiv_X3 U hUc hUcs
  let d : X3 := w.ofLp
  have hd : w = WithLp.toLp 2 d := by
    simp [d]
  have hdecomp : d = ∑ j : Fin 3, (d j) • (Pi.single j (1 : ℝ)) := by
    funext k
    have hk : (∑ j : Fin 3, (d j) • (Pi.single j (1 : ℝ))) k = d k := by
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hjk
        simp [hjk]
      · intro hk0
        simp at hk0
    exact hk.symm
  have hlin : ∀ c : X3, fderiv ℝ U c d =
      ∑ j : Fin 3, (d j) • fderiv ℝ U c (Pi.single j 1) := by
    intro c
    conv_lhs => rw [hdecomp]
    rw [map_sum]
    simp only [map_smul]
  calc
    (∫ x : ℝ³, fderiv ℝ u x w)
        = ∫ x : ℝ³, fderiv ℝ u x (WithLp.toLp 2 d) := by rw [hd]
    _ = ∫ c : X3, fderiv ℝ u (WithLp.toLp 2 c) (WithLp.toLp 2 d) := by
          exact (integral_toLp (g := fun x : ℝ³ => fderiv ℝ u x (WithLp.toLp 2 d))).symm
    _ = ∫ c : X3, fderiv ℝ U c d := by
          exact congrArg (fun h : X3 → ℝ => ∫ c : X3, h c)
            (funext fun c => (fderiv_comp_toLp hu c d).symm)
    _ = ∑ j : Fin 3, (d j) • (∫ c : X3, fderiv ℝ U c (Pi.single j 1)) := by
          calc
            (∫ c : X3, fderiv ℝ U c d)
                = ∫ c : X3, ∑ j : Fin 3, (d j) • fderiv ℝ U c (Pi.single j 1) := by
                  exact congrArg (fun h : X3 → ℝ => ∫ c : X3, h c) (funext fun c => hlin c)
            _ = ∑ j : Fin 3, ∫ c : X3, (d j) • fderiv ℝ U c (Pi.single j 1) := by
                  rw [MeasureTheory.integral_finsetSum (s := Finset.univ)]
                  intro j _
                  exact (hint j).smul (d j)
            _ = ∑ j : Fin 3, (d j) • (∫ c : X3, fderiv ℝ U c (Pi.single j 1)) := by
                  apply Finset.sum_congr rfl
                  intro j _
                  simpa [smul_eq_mul] using (integral_const_mul (d j)
                    (fun c : X3 => fderiv ℝ U c (Pi.single j 1)))
    _ = 0 := by
          simp [hzero]

end EMeanZero

section SmoothRadial

/-- If a smooth profile vanishes near `0`, its composition with the norm is smooth. -/
lemma contDiff_norm_comp_of_zero_near {S : ℝ → ℝ} (hS : ContDiff ℝ ∞ S) {a : ℝ} (ha : 0 < a)
    (hS0 : ∀ t : ℝ, |t| < a → S t = 0) :
    ContDiff ℝ ∞ (fun x : ℝ³ => S ‖x‖) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply ContDiffAt.congr_of_eventuallyEq
    · exact contDiffAt_const (x := (0 : ℝ³)) (c := (0 : ℝ)) (n := ∞)
    · filter_upwards [Metric.ball_mem_nhds 0 ha] with y hy
      have hnorm : ‖y‖ < a := by simpa [Metric.mem_ball, dist_zero_right] using hy
      exact hS0 ‖y‖ (by simpa [abs_of_nonneg (norm_nonneg y)] using hnorm)
  · have hN : ContDiffAt ℝ ∞ (fun y : ℝ³ => ‖y‖) x := contDiffAt_norm ℝ (n := ∞) hx
    exact hS.contDiffAt.comp x hN

/-- `x ↦ fderiv u x e` is continuous for smooth `u`. -/
lemma continuous_fderiv_apply (u : ℝ³ → ℝ) (hu : ContDiff ℝ ∞ u) (e : ℝ³) :
    Continuous (fun x : ℝ³ => fderiv ℝ u x e) := by
  have hcont : Continuous (fun x : ℝ³ => (fderiv ℝ u x : ℝ³ →L[ℝ] ℝ)) :=
    ContDiff.continuous_fderiv hu (by norm_num : (∞ : ℕ∞ω) ≠ 0)
  exact hcont.clm_apply (continuous_const : Continuous fun _ : ℝ³ => e)

/-- `x ↦ fderiv u x e` has compact support for compactly supported smooth `u`. -/
lemma hasCompactSupport_fderiv_apply (u : ℝ³ → ℝ) (hu_cs : HasCompactSupport u) (e : ℝ³) :
    HasCompactSupport (fun x : ℝ³ => fderiv ℝ u x e) := by
  refine HasCompactSupport.intro' (K := tsupport u) hu_cs (isClosed_tsupport u) ?_
  intro x hx
  rw [fderiv_of_notMem_tsupport ℝ hx]
  simp

/-- Products of smooth compactly supported functions are integrable. -/
lemma integrable_smooth_smul (u v : ℝ³ → ℝ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hu_cs : HasCompactSupport u) (hv_cs : HasCompactSupport v) :
    Integrable (fun x : ℝ³ => u x * v x) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact hu.continuous.mul hv.continuous
  · refine HasCompactSupport.intro' (K := tsupport u) hu_cs (isClosed_tsupport u) ?_
    intro x hx
    by_contra hz
    apply hx
    exact subset_tsupport u (by simpa [Function.support] using (mul_ne_zero_iff.mp hz).1)

end SmoothRadial

section Green

/-- Product rule for the directional derivative. -/
lemma fderiv_mul_apply {u v : ℝ³ → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (x : ℝ³) (e : ℝ³) :
    fderiv ℝ (fun y : ℝ³ => u y * v y) x e =
      fderiv ℝ u x e * v x + u x * fderiv ℝ v x e := by
  have hdu : DifferentiableAt ℝ u x :=
    hu.differentiable (by norm_num : (∞ : ℕ∞ω) ≠ 0) x
  have hdv : DifferentiableAt ℝ v x :=
    hv.differentiable (by norm_num : (∞ : ℕ∞ω) ≠ 0) x
  have hmul := fderiv_mul (𝕜 := ℝ) (x := x) (c := u) (d := v) hdu hdv
  calc
    fderiv ℝ (fun y : ℝ³ => u y * v y) x e = (fderiv ℝ (u * v) x) e := by rfl
    _ = (u x • fderiv ℝ v x + v x • fderiv ℝ u x) e := by rw [hmul]
    _ = u x * (fderiv ℝ v x e) + v x * (fderiv ℝ u x e) := by simp
    _ = fderiv ℝ u x e * v x + u x * fderiv ℝ v x e := by ring

/-- Integration by parts: moving the derivative from `u` to `v`. -/
lemma integral_partial_ibp {u v : ℝ³ → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hu_cs : HasCompactSupport u) (hv_cs : HasCompactSupport v) (e : ℝ³) :
    (∫ x : ℝ³, fderiv ℝ u x e * v x) = -∫ x : ℝ³, u x * fderiv ℝ v x e := by
  let A : ℝ³ → ℝ := fun x => fderiv ℝ u x e * v x
  let B : ℝ³ → ℝ := fun x => u x * fderiv ℝ v x e
  have hpr : (fun x : ℝ³ => fderiv ℝ (fun y : ℝ³ => u y * v y) x e) = fun x => A x + B x := by
    funext x
    dsimp [A, B]
    exact fderiv_mul_apply hu hv x e
  have h1 : ContDiff ℝ ∞ (fun x : ℝ³ => u x * v x) := hu.mul hv
  have h1cs : HasCompactSupport (fun x : ℝ³ => u x * v x) := by
    refine HasCompactSupport.intro' (K := tsupport u) hu_cs (isClosed_tsupport u) ?_
    intro x hx
    by_contra hz
    apply hx
    exact subset_tsupport u (by simpa [Function.support] using (mul_ne_zero_iff.mp hz).1)
  have hA_int : Integrable A := by
    dsimp [A]
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (continuous_fderiv_apply u hu e).mul hv.continuous
    · refine HasCompactSupport.intro' (K := tsupport u) hu_cs (isClosed_tsupport u) ?_
      intro x hx
      rw [fderiv_of_notMem_tsupport ℝ hx]
      simp
  have hB_int : Integrable B := by
    dsimp [B]
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hu.continuous.mul (continuous_fderiv_apply v hv e)
    · refine HasCompactSupport.intro' (K := tsupport v) hv_cs (isClosed_tsupport v) ?_
      intro x hx
      rw [fderiv_of_notMem_tsupport ℝ hx]
      simp
  have hz := integral_fderiv_eq_zero (u := fun x : ℝ³ => u x * v x) h1 h1cs e
  have hsum : (∫ x : ℝ³, A x) + (∫ x : ℝ³, B x) = 0 := by
    calc
      (∫ x : ℝ³, A x) + (∫ x : ℝ³, B x)
          = ∫ x : ℝ³, A x + B x := (integral_add hA_int hB_int).symm
      _ = ∫ x : ℝ³, fderiv ℝ (fun y : ℝ³ => u y * v y) x e := by
            rw [hpr]
      _ = 0 := hz
  dsimp [A, B] at hsum
  linarith

/-- The Laplacian is the sum of second directional derivatives in an orthonormal basis. -/
lemma laplacian_basis_sum (g : ℝ³ → ℝ) (hg : ContDiff ℝ ∞ g) (x : ℝ³) :
    (Δ g) x = ∑ i : Fin 3,
      fderiv ℝ (fun z : ℝ³ => fderiv ℝ g z (euclBasis3 i)) x (euclBasis3 i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f := g) euclBasis3]
  apply Finset.sum_congr rfl
  intro i _
  have hg2 : ContDiffAt ℝ 2 g x :=
    hg.contDiffAt.of_le (by decide : (2 : ℕ∞ω) ≤ ∞)
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ g) x :=
    hg2.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    h1.differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  rw [radlap_iteratedFDeriv_two_eq_fderiv_dir (f := g) (x := x) (a := euclBasis3 i) hd]

/-- `x ↦ fderiv u x e` is smooth for smooth `u`. -/
lemma contDiff_fderiv_apply (u : ℝ³ → ℝ) (hu : ContDiff ℝ ∞ u) (e : ℝ³) :
    ContDiff ℝ ∞ (fun x : ℝ³ => fderiv ℝ u x e) := by
  have hfder : ContDiff ℝ ∞ (fun x : ℝ³ => (fderiv ℝ u x : ℝ³ →L[ℝ] ℝ)) := by
    exact hu.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  exact hfder.clm_apply (contDiff_const : ContDiff ℝ ∞ fun _ : ℝ³ => e)

/-- Green's second identity on the whole space for smooth compactly supported functions. -/
lemma integral_laplacian_mul {ψ f : ℝ³ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hf : ContDiff ℝ ∞ f)
    (hψcs : HasCompactSupport ψ) (hfcs : HasCompactSupport f) :
    (∫ x : ℝ³, (Δ ψ) x * f x) = ∫ x : ℝ³, ψ x * (Δ f) x := by
  have hT : ∀ i : Fin 3,
      (∫ x : ℝ³, fderiv ℝ (fun z : ℝ³ => fderiv ℝ ψ z (euclBasis3 i)) x (euclBasis3 i) * f x) =
        ∫ x : ℝ³, fderiv ℝ (fun z : ℝ³ => fderiv ℝ f z (euclBasis3 i)) x (euclBasis3 i) * ψ x := by
    intro i
    let a : ℝ³ → ℝ := fun z => fderiv ℝ ψ z (euclBasis3 i)
    let b : ℝ³ → ℝ := fun z => fderiv ℝ f z (euclBasis3 i)
    have ha : ContDiff ℝ ∞ a := by
      dsimp [a]
      exact contDiff_fderiv_apply ψ hψ (euclBasis3 i)
    have hb : ContDiff ℝ ∞ b := by
      dsimp [b]
      exact contDiff_fderiv_apply f hf (euclBasis3 i)
    have ha_cs : HasCompactSupport a := by
      dsimp [a]
      exact hasCompactSupport_fderiv_apply ψ hψcs (euclBasis3 i)
    have hb_cs : HasCompactSupport b := by
      dsimp [b]
      exact hasCompactSupport_fderiv_apply f hfcs (euclBasis3 i)
    have h1 := integral_partial_ibp (u := a) (v := f) ha hf ha_cs hfcs (euclBasis3 i)
    have h2 := integral_partial_ibp (u := b) (v := ψ) hb hψ hb_cs hψcs (euclBasis3 i)
    calc
      (∫ x : ℝ³, fderiv ℝ (fun z : ℝ³ => fderiv ℝ ψ z (euclBasis3 i)) x (euclBasis3 i) * f x)
          = -∫ x : ℝ³, a x * fderiv ℝ f x (euclBasis3 i) := by
            simpa [a] using h1
      _ = -∫ x : ℝ³, b x * fderiv ℝ ψ x (euclBasis3 i) := by
            apply congrArg Neg.neg
            apply congrArg (fun g : ℝ³ → ℝ => ∫ x : ℝ³, g x)
            funext x
            dsimp [a, b]
            ring
      _ = ∫ x : ℝ³, fderiv ℝ (fun z : ℝ³ => fderiv ℝ f z (euclBasis3 i)) x (euclBasis3 i) * ψ x := by
            simpa [b] using h2.symm
  have hint1 : ∀ i : Fin 3, Integrable (fun x : ℝ³ =>
      fderiv ℝ (fun z : ℝ³ => fderiv ℝ ψ z (euclBasis3 i)) x (euclBasis3 i) * f x) := by
    intro i
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (continuous_fderiv_apply (fun z : ℝ³ => fderiv ℝ ψ z (euclBasis3 i))
        (contDiff_fderiv_apply ψ hψ (euclBasis3 i)) (euclBasis3 i)).mul hf.continuous
    · refine HasCompactSupport.intro' (K := tsupport f) hfcs (isClosed_tsupport f) ?_
      intro x hx
      by_contra hz
      apply hx
      exact subset_tsupport f (by simpa [Function.support] using (mul_ne_zero_iff.mp hz).2)
  have hint2 : ∀ i : Fin 3, Integrable (fun x : ℝ³ =>
      fderiv ℝ (fun z : ℝ³ => fderiv ℝ f z (euclBasis3 i)) x (euclBasis3 i) * ψ x) := by
    intro i
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (continuous_fderiv_apply (fun z : ℝ³ => fderiv ℝ f z (euclBasis3 i))
        (contDiff_fderiv_apply f hf (euclBasis3 i)) (euclBasis3 i)).mul hψ.continuous
    · refine HasCompactSupport.intro' (K := tsupport ψ) hψcs (isClosed_tsupport ψ) ?_
      intro x hx
      by_contra hz
      apply hx
      exact subset_tsupport ψ (by simpa [Function.support] using (mul_ne_zero_iff.mp hz).2)
  have hsum1 : (∫ x : ℝ³, (Δ ψ) x * f x) = ∑ i : Fin 3,
      ∫ x : ℝ³, fderiv ℝ (fun z : ℝ³ => fderiv ℝ ψ z (euclBasis3 i)) x (euclBasis3 i) * f x := by
    calc
      (∫ x : ℝ³, (Δ ψ) x * f x)
          = ∫ x : ℝ³, ∑ i : Fin 3,
              fderiv ℝ (fun z : ℝ³ => fderiv ℝ ψ z (euclBasis3 i)) x (euclBasis3 i) * f x := by
            apply congrArg (fun g : ℝ³ → ℝ => ∫ x : ℝ³, g x)
            funext x
            rw [laplacian_basis_sum ψ hψ x]
            rw [Finset.sum_mul]
      _ = ∑ i : Fin 3, ∫ x : ℝ³,
            fderiv ℝ (fun z : ℝ³ => fderiv ℝ ψ z (euclBasis3 i)) x (euclBasis3 i) * f x := by
            rw [integral_finsetSum (s := Finset.univ)]
            intro i _
            exact hint1 i
  have hsum2 : (∫ x : ℝ³, ψ x * (Δ f) x) = ∑ i : Fin 3,
      ∫ x : ℝ³, fderiv ℝ (fun z : ℝ³ => fderiv ℝ f z (euclBasis3 i)) x (euclBasis3 i) * ψ x := by
    calc
      (∫ x : ℝ³, ψ x * (Δ f) x)
          = ∫ x : ℝ³, (Δ f) x * ψ x := by
            apply congrArg (fun g : ℝ³ → ℝ => ∫ x : ℝ³, g x)
            funext x
            ring
      _ = ∫ x : ℝ³, ∑ i : Fin 3,
              fderiv ℝ (fun z : ℝ³ => fderiv ℝ f z (euclBasis3 i)) x (euclBasis3 i) * ψ x := by
            apply congrArg (fun g : ℝ³ → ℝ => ∫ x : ℝ³, g x)
            funext x
            rw [laplacian_basis_sum f hf x]
            rw [Finset.sum_mul]
      _ = ∑ i : Fin 3, ∫ x : ℝ³,
            fderiv ℝ (fun z : ℝ³ => fderiv ℝ f z (euclBasis3 i)) x (euclBasis3 i) * ψ x := by
            rw [integral_finsetSum (s := Finset.univ)]
            intro i _
            exact hint2 i
  calc
    (∫ x : ℝ³, (Δ ψ) x * f x) = ∑ i : Fin 3,
        ∫ x : ℝ³, fderiv ℝ (fun z : ℝ³ => fderiv ℝ ψ z (euclBasis3 i)) x (euclBasis3 i) * f x := hsum1
    _ = ∑ i : Fin 3, ∫ x : ℝ³,
        fderiv ℝ (fun z : ℝ³ => fderiv ℝ f z (euclBasis3 i)) x (euclBasis3 i) * ψ x := by
          apply Finset.sum_congr rfl
          intro i _
          exact hT i
    _ = ∫ x : ℝ³, ψ x * (Δ f) x := hsum2.symm

end Green

section Kernel

/-- The Newtonian kernel `1/‖x‖` is harmonic away from the origin. -/
lemma laplacian_inv_norm_eq_zero {x : ℝ³} (hx : x ≠ 0) :
    (Δ fun z : ℝ³ => (‖z‖ : ℝ)⁻¹) x = 0 := by
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hf : ContDiffAt ℝ 2 (fun t : ℝ => t⁻¹) ‖x‖ :=
    contDiffAt_inv (𝕜 := ℝ) (n := (2 : ℕ∞ω)) hx0
  have hlap := laplacian_radial_norm (f := fun t : ℝ => t⁻¹) hx hf
  rw [hlap]
  -- derivative computations (as in the module probe)
  have deriv_inv_sq : deriv (fun t : ℝ => (t ^ 2)⁻¹) ‖x‖ = -(2 * ‖x‖) * (‖x‖ ^ 2)⁻¹ ^ 2 := by
    have hfun : (fun t : ℝ => (t ^ 2)⁻¹) = (fun t : ℝ => t⁻¹) ∘ (fun t : ℝ => t ^ 2) := by
      funext t; rfl
    rw [hfun]
    rw [deriv_comp]
    · rw [deriv_inv]
      have hder : deriv (fun t : ℝ => t ^ 2) ‖x‖ = 2 * ‖x‖ := by
        simpa using (hasDerivAt_pow 2 ‖x‖).deriv
      rw [hder]
      ring
    · exact differentiableAt_inv (pow_ne_zero 2 hx0)
    · exact (hasDerivAt_pow 2 ‖x‖).differentiableAt
  have deriv_dd_inv : deriv (deriv fun t : ℝ => t⁻¹) ‖x‖ = 2 * ‖x‖ * (‖x‖ ^ 2)⁻¹ ^ 2 := by
    rw [deriv_inv']
    change deriv (-(fun t : ℝ => (t ^ 2)⁻¹)) ‖x‖ = 2 * ‖x‖ * (‖x‖ ^ 2)⁻¹ ^ 2
    rw [deriv.neg]
    rw [deriv_inv_sq]
    ring
  rw [deriv_dd_inv]
  rw [deriv_inv]
  field_simp [hx0]
  ring

/-- Smooth kernel equal to `1/‖x‖` on the annulus `R1 ≤ ‖x‖ ≤ 2·M1` and vanishing near zero and at
infinity. -/
lemma smooth_kernel (R1 M1 : ℝ) (hR1 : 0 < R1) (hR1M1 : R1 < M1) :
    ∃ f : ℝ³ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (∀ x : ℝ³, R1 ≤ ‖x‖ → ‖x‖ ≤ 2 * M1 → f x = (‖x‖ : ℝ)⁻¹) ∧
      (∀ x : ℝ³, ‖x‖ ≤ R1 / 2 → f x = 0) ∧
      (∀ x : ℝ³, 4 * M1 ≤ ‖x‖ → f x = 0) := by
  -- build the one-dimensional profile
  have hR1h : R1 / 2 < R1 := by linarith
  have hMpos : 0 < M1 := lt_trans hR1 hR1M1
  have hMlo : 2 * M1 < 4 * M1 := by linarith
  rcases one_dim_cutoff hR1h with ⟨g₁, hg₁, _, _, hg₁le, hg₁ge⟩
  rcases one_dim_cutoff hMlo with ⟨g₂, hg₂, _, _, hg₂le, hg₂ge⟩
  let u : ℝ → ℝ := fun t => 1 - g₁ t
  let w : ℝ → ℝ := g₂
  let h : ℝ → ℝ := fun t => u t * w t
  let S : ℝ → ℝ := fun t => h t * t⁻¹
  have hu : ContDiff ℝ ∞ u := by
    dsimp [u]
    exact contDiff_const.sub hg₁
  have hw : ContDiff ℝ ∞ w := by
    dsimp [w]
    exact hg₂
  have hh : ContDiff ℝ ∞ h := hu.mul hw
  have hS : ContDiff ℝ ∞ S := by
    rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : t = 0
    · subst t
      apply ContDiffAt.congr_of_eventuallyEq (n := ∞)
      · exact contDiffAt_const (x := (0 : ℝ)) (c := (0 : ℝ)) (n := ∞)
      · have hhalf : 0 < R1 / 2 := by positivity
        filter_upwards [Metric.ball_mem_nhds 0 hhalf] with y hy
        have hyle : y ≤ R1 / 2 := by
          have : |y| < R1 / 2 := by simpa [Metric.mem_ball, dist_zero_right] using hy
          linarith [abs_le.mp (le_of_lt this)] -- hmm
        dsimp [S, h, u]
        rw [hg₁le y hyle]
        ring
    · have hh_at : ContDiffAt ℝ ∞ h t := hh.contDiffAt
      have hinv : ContDiffAt ℝ ∞ (fun s : ℝ => s⁻¹) t :=
        contDiffAt_inv (𝕜 := ℝ) (n := ∞) ht
      exact (hh_at.mul hinv)
  have hS0 : ∀ t : ℝ, |t| < R1 / 2 → S t = 0 := by
    intro t ht
    have hle : t ≤ R1 / 2 := by linarith [abs_le.mp (le_of_lt ht)]
    dsimp [S, h, u]
    rw [hg₁le t hle]
    ring
  let f : ℝ³ → ℝ := fun x => S ‖x‖
  have hfC : ContDiff ℝ ∞ f := by
    dsimp [f]
    have hhalf : 0 < R1 / 2 := by positivity
    exact contDiff_norm_comp_of_zero_near hS hhalf hS0
  have hfcs : HasCompactSupport f := by
    dsimp [f]
    refine HasCompactSupport.intro' (K := Metric.closedBall (0 : ℝ³) (4 * M1)) ?_ ?_ ?_
    · exact ProperSpace.isCompact_closedBall (0 : ℝ³) (4 * M1)
    · exact isClosed_closedBall
    · intro x hx
      have hnorm : 4 * M1 < ‖x‖ := by
        rw [Metric.mem_closedBall] at hx
        have hx' : ¬ dist x 0 ≤ 4 * M1 := hx
        simpa [dist_eq_norm, dist_zero_right] using (not_le.mp hx')
      have hge : 4 * M1 ≤ ‖x‖ := le_of_lt hnorm
      have hSge : S ‖x‖ = 0 := by
        dsimp [S, h, w]
        rw [hg₂ge ‖x‖ hge]
        ring
      simpa [f] using hSge
  have hfkernel : ∀ x : ℝ³, R1 ≤ ‖x‖ → ‖x‖ ≤ 2 * M1 → f x = (‖x‖ : ℝ)⁻¹ := by
    intro x h1 h2
    dsimp [f, S, h, u, w]
    rw [hg₁ge ‖x‖ h1]  -- u ‖x‖ = 1
    rw [hg₂le ‖x‖ h2]
    ring
  have hfsmall : ∀ x : ℝ³, ‖x‖ ≤ R1 / 2 → f x = 0 := by
    intro x hx
    dsimp [f, S, h, u]
    rw [hg₁le ‖x‖ hx]
    ring
  have hfbig : ∀ x : ℝ³, 4 * M1 ≤ ‖x‖ → f x = 0 := by
    intro x hx
    have hSge : S ‖x‖ = 0 := by
      dsimp [S, h, w]
      rw [hg₂ge ‖x‖ hx]
      ring
    simpa [f] using hSge
  exact ⟨f, hfC, hfcs, hfkernel, hfsmall, hfbig⟩

end Kernel

section Vanishing

/-- The Laplacian vanishes wherever the function is locally zero. -/
lemma laplacian_eq_zero_of_not_mem_tsupport (g : ℝ³ → ℝ) {x : ℝ³} (hx : x ∉ tsupport g) :
    (Δ g) x = 0 := by
  have hloc : g =ᶠ[𝓝 x] (fun _ : ℝ³ => (0 : ℝ)) := (notMem_tsupport_iff_eventuallyEq.mp hx)
  have hc := InnerProductSpace.laplacian_congr_nhds (E := ℝ³) (f₁ := g)
    (f₂ := fun _ : ℝ³ => (0 : ℝ)) hloc
  have h0 : (Δ (fun _ : ℝ³ => (0 : ℝ))) x = 0 := by simp
  simpa [h0] using (Filter.EventuallyEq.eq_of_nhds hc)

/-- If `g` vanishes on a ball around zero, its Laplacian vanishes strictly inside that ball. -/
lemma mv_laplacian_eq_zero_of_norm_lt {g : ℝ³ → ℝ} {R : ℝ} (hg0 : ∀ x : ℝ³, ‖x‖ ≤ R → g x = 0)
    {x : ℝ³} (hx : ‖x‖ < R) : (Δ g) x = 0 := by
  have hnot : x ∉ tsupport g := by
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [Metric.ball_mem_nhds x (sub_pos.mpr hx)] with y hy
    have hylt : ‖y‖ < R := by
      have h1 : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
        simpa using (norm_add_le (y - x) x : ‖(y - x) + x‖ ≤ ‖y - x‖ + ‖x‖)
      have h2 : ‖y - x‖ < R - ‖x‖ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hy
      linarith
    exact hg0 y (le_of_lt hylt)
  exact laplacian_eq_zero_of_not_mem_tsupport g hnot

/-- The vanishing integral: if `ψ` is smooth, compactly supported and vanishes on the closed ball
of radius `R1`, then `∫ (Δψ)/‖·‖ = 0`. -/
lemma integral_delta_laplacian_zero {ψ : ℝ³ → ℝ} {R1 : ℝ} (hR1 : 0 < R1)
    (hψ : ContDiff ℝ ∞ ψ) (hψcs : HasCompactSupport ψ)
    (hψ0 : ∀ x : ℝ³, ‖x‖ ≤ R1 → ψ x = 0) :
    (∫ x : ℝ³, (Δ ψ) x * (‖x‖ : ℝ)⁻¹) = 0 := by
  rcases hψcs.isBounded.subset_closedBall (0 : ℝ³) with ⟨B, hBsub⟩
  let M1 : ℝ := max (B + 1) (R1 + 1)
  have hR1M1 : R1 < M1 := by
    dsimp [M1]
    exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hBM1 : B < M1 := by
    dsimp [M1]
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hM1pos : 0 < M1 := lt_trans hR1 hR1M1
  rcases smooth_kernel R1 M1 hR1 hR1M1 with ⟨f, hfC, hfcs, hfkernel, hfsmall, hfbig⟩
  -- Δψ ≠ 0 forces ‖x‖ ∈ [R1, B]
  have hbounds : ∀ x : ℝ³, (Δ ψ) x ≠ 0 → R1 ≤ ‖x‖ ∧ ‖x‖ ≤ B := by
    intro x hΔ
    constructor
    · by_contra hlt
      have : (Δ ψ) x = 0 := by
        exact mv_laplacian_eq_zero_of_norm_lt (g := ψ) hψ0 (lt_of_not_ge hlt)
      exact hΔ this
    · by_contra hgt
      have hnot : x ∉ tsupport ψ := by
        intro hmem
        have hle : ‖x‖ ≤ B := by
          have hd : dist x 0 ≤ B := Metric.mem_closedBall.mp (hBsub hmem)
          simpa [dist_eq_norm, dist_zero_right] using hd
        linarith
      have : (Δ ψ) x = 0 := laplacian_eq_zero_of_not_mem_tsupport ψ hnot
      exact hΔ this
  -- ψ ≠ 0 forces R1 < ‖x‖ < M1
  have hboundsψ : ∀ x : ℝ³, ψ x ≠ 0 → R1 < ‖x‖ ∧ ‖x‖ < M1 := by
    intro x hx
    constructor
    · by_contra hle
      exact hx (hψ0 x (le_of_not_gt hle))
    · have hmem : x ∈ tsupport ψ := subset_tsupport ψ (by simpa [Function.support] using hx)
      have hd : dist x 0 ≤ B := Metric.mem_closedBall.mp (hBsub hmem)
      have hle : ‖x‖ ≤ B := by simpa [dist_eq_norm, dist_zero_right] using hd
      nlinarith
  -- (a) the integrand with f equals the integrand with ‖·‖⁻¹
  have h1eq : (fun x : ℝ³ => (Δ ψ) x * (‖x‖ : ℝ)⁻¹) = fun x => (Δ ψ) x * f x := by
    funext x
    by_cases hz : (Δ ψ) x = 0
    · simp [hz]
    · rcases hbounds x hz with ⟨hR1le, hBle⟩
      have hle2 : ‖x‖ ≤ 2 * M1 := by nlinarith
      rw [hfkernel x hR1le hle2]
  -- (b) ψ x · (Δf) x = 0 everywhere
  have h2eq : (fun x : ℝ³ => ψ x * (Δ f) x) = fun _ : ℝ³ => 0 := by
    funext x
    by_cases hz : ψ x = 0
    · simp [hz]
    · rcases hboundsψ x hz with ⟨hR1lt, hM1lt⟩
      have hx0 : x ≠ 0 := by
        intro hx0
        rw [hx0] at hR1lt
        simp at hR1lt
        linarith
      have hloc : f =ᶠ[𝓝 x] (fun z : ℝ³ => (‖z‖ : ℝ)⁻¹) := by
        -- on a neighborhood of x within {R1 < ‖·‖ < 2M1}
        have hopen : {y : ℝ³ | R1 < ‖y‖ ∧ ‖y‖ < 2 * M1} ∈ 𝓝 x := by
          have ho1 : {y : ℝ³ | R1 < ‖y‖} ∈ 𝓝 x :=
            (isOpen_Ioi.preimage continuous_norm).mem_nhds hR1lt
          have ho2 : {y : ℝ³ | ‖y‖ < 2 * M1} ∈ 𝓝 x :=
            (isOpen_Iio.preimage continuous_norm).mem_nhds (by
              have : ‖x‖ < 2 * M1 := by nlinarith
              exact this)
          exact Filter.inter_mem ho1 ho2
        filter_upwards [hopen] with y hy
        exact hfkernel y (le_of_lt hy.1) (le_of_lt hy.2)
      have hΔcongr : (Δ f) x = (Δ fun z : ℝ³ => (‖z‖ : ℝ)⁻¹) x := by
        have hc := InnerProductSpace.laplacian_congr_nhds (E := ℝ³) (f₁ := f)
          (f₂ := fun z : ℝ³ => (‖z‖ : ℝ)⁻¹) hloc
        exact Filter.EventuallyEq.eq_of_nhds hc
      have hΔ0 : (Δ fun z : ℝ³ => (‖z‖ : ℝ)⁻¹) x = 0 := laplacian_inv_norm_eq_zero hx0
      rw [hΔcongr, hΔ0]
      ring
  -- assemble
  calc
    (∫ x : ℝ³, (Δ ψ) x * (‖x‖ : ℝ)⁻¹) = ∫ x : ℝ³, (Δ ψ) x * f x := by
          exact congrArg (fun g : ℝ³ → ℝ => ∫ x : ℝ³, g x) h1eq
    _ = ∫ x : ℝ³, ψ x * (Δ f) x := integral_laplacian_mul hψ hfC hψcs hfcs
    _ = 0 := by
          rw [h2eq]
          simp

end Vanishing

section ZeroCase

/-- `x ↦ g x / ‖x‖` is continuous when `g` is smooth and vanishes near `0`. -/
lemma continuous_mul_inv {g : ℝ³ → ℝ} (hg : Continuous g) {ρ : ℝ} (hρ : 0 < ρ)
    (hg0 : ∀ x : ℝ³, ‖x‖ ≤ ρ → g x = 0) : Continuous (fun x : ℝ³ => g x * (‖x‖ : ℝ)⁻¹) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply ContinuousAt.congr_of_eventuallyEq
    · exact (continuousAt_const : ContinuousAt (fun _ : ℝ³ => (0 : ℝ)) (0 : ℝ³))
    · have hhalf : 0 < ρ / 2 := by positivity
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ³) hhalf] with y hy
      have hylt : ‖y‖ < ρ / 2 := by simpa [Metric.mem_ball, dist_zero_right] using hy
      have hle : ‖y‖ ≤ ρ := by linarith
      simp [hg0 y hle]
  · have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hA : ContinuousAt g x := hg.continuousAt
    have hB : ContinuousAt (fun y : ℝ³ => (‖y‖ : ℝ)⁻¹) x := by
      have hinv : ContDiffAt ℝ ∞ (fun t : ℝ => t⁻¹) ‖x‖ :=
        contDiffAt_inv (𝕜 := ℝ) (n := ∞) hx0
      have hN : ContDiffAt ℝ ∞ (fun y : ℝ³ => ‖y‖) x :=
        contDiffAt_norm ℝ (n := ∞) hx
      exact (hinv.comp x hN).continuousAt
    exact hA.mul hB

/-- `x ↦ g x / ‖x‖` is integrable when `g` is smooth, compactly supported and vanishes near `0`. -/
lemma integrable_mul_inv {g : ℝ³ → ℝ} (hg : Continuous g) (hg_cs : HasCompactSupport g)
    {ρ : ℝ} (hρ : 0 < ρ) (hg0 : ∀ x : ℝ³, ‖x‖ ≤ ρ → g x = 0) :
    Integrable (fun x : ℝ³ => g x * (‖x‖ : ℝ)⁻¹) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact continuous_mul_inv hg hρ hg0
  · refine HasCompactSupport.intro' (K := tsupport g) hg_cs (isClosed_tsupport g) ?_
    intro x hx
    by_contra hz
    apply hx
    exact subset_tsupport g (by simpa [Function.support] using (mul_ne_zero_iff.mp hz).1)

/-- The radial profile of a smooth function is smooth: `radialProfile θ` is
`θ` composed with the smooth linear map `r ↦ r • radU0`. -/
lemma radialProfile_contDiff {θ : ℝ³ → ℝ} (hθ : ContDiff ℝ ∞ θ) :
    ContDiff ℝ ∞ (radialProfile θ) := by
  have hsmul : ContDiff ℝ ∞ (fun r : ℝ => r • radU0) := by
    have hf : ContDiff ℝ ∞ (fun r : ℝ => r) := contDiff_id
    have hg : ContDiff ℝ ∞ (fun _ : ℝ => radU0) := contDiff_const
    convert (ContDiff.smul (𝕜 := ℝ) hf hg) using 1
    all_goals (funext r; rfl)
  unfold radialProfile
  exact hθ.comp hsmul

/-- The radial profile of a compactly supported function is compactly supported. -/
lemma radialProfile_hasCompactSupport {θ : ℝ³ → ℝ} (hθcs : HasCompactSupport θ) :
    HasCompactSupport (radialProfile θ) := by
  let K : Set ℝ³ := tsupport θ
  have hKbdd : Bornology.IsBounded K := IsCompact.isBounded hθcs
  obtain ⟨B, hKsub⟩ := Bornology.IsBounded.subset_closedBall hKbdd (0 : ℝ³)
  let B₀ : ℝ := max B 0
  have hB₀ : 0 ≤ B₀ := le_max_right B 0
  have hKsub₀ : K ⊆ Metric.closedBall (0 : ℝ³) B₀ := by
    have hmono : Metric.closedBall (0 : ℝ³) B ⊆ Metric.closedBall (0 : ℝ³) B₀ :=
      Metric.closedBall_subset_closedBall (le_max_left B 0)
    exact hKsub.trans hmono
  refine HasCompactSupport.intro' (ProperSpace.isCompact_closedBall (0 : ℝ) B₀) isClosed_closedBall ?_
  intro r hrK
  by_contra hne
  have hsupp : r • radU0 ∈ Function.support θ := by
    simpa [Function.support, radialProfile] using hne
  have hmemK : r • radU0 ∈ K := subset_tsupport θ hsupp
  have hball : r • radU0 ∈ Metric.closedBall (0 : ℝ³) B₀ := hKsub₀ hmemK
  have hnorm : ‖r • radU0‖ ≤ B₀ := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hball
  have habs : |r| ≤ B₀ := by
    simpa [norm_smul_radU0] using hnorm
  have hrb : r ∈ Metric.closedBall (0 : ℝ) B₀ := by
    simpa [Metric.mem_closedBall, dist_zero_right] using habs
  exact hrK hrb

/-- Newtonian identity for smooth radial cutoffs (radial version). -/
lemma radial_delta_norm_inv {θ : ℝ³ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθcs : HasCompactSupport θ) (hθrad : IsRadial θ) (hθ0 : θ 0 = 1) :
    (∫ x : ℝ³, (‖x‖ : ℝ)⁻¹ * (Δ θ) x) = -4 * π := by
  let σ : ℝ → ℝ := radialProfile θ
  have hσc : ContDiff ℝ ∞ σ := by
    dsimp [σ]
    exact radialProfile_contDiff hθ
  have hσcs : HasCompactSupport σ := by
    dsimp [σ]
    exact radialProfile_hasCompactSupport hθcs
  have hσ0 : σ 0 = 1 := by
    dsimp [σ]
    simp [radialProfile, hθ0]
  have hθeq : θ = (fun y : ℝ³ => σ ‖y‖) := by
    funext y
    simpa [σ] using (radial_eq_profile hθrad y)
  rw [hθeq]
  exact integral_norm_inv_mul_delta_smooth hσc hσcs hσ0

end ZeroCase

end Submission.BoseGases
