import Mathlib
import Submission.Work.Drive.N2Lead.saddleWindow_of_packet_band
import Submission.Work.Drive.N2.saddleScaled
import Submission.Work.Drive.N2.saddleModelPsi
import Submission.Work.Drive.N2.saddlePsi_norm_le
import Submission.Work.Drive.N2Lead.saddlePsiWideCollar

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

/-- The planar inclusion `cE3 : ℂ → ℝ³` is an isometry onto the plane `{z = 0}` (local copy of
`Work.Drive.N2Lead.norm_cE3` of `mobius_park_off.lean`, under a name of its own so that this module
and that one can be imported together). -/
lemma norm_cE3_eq_engine (z : ℂ) : ‖Work.Drive.N2.cE3 z‖ = ‖z‖ := by
  have h2 : ‖Work.Drive.N2.cE3 z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Fin.sum_univ_three, Work.Drive.N2.cE3_apply_zero, Work.Drive.N2.cE3_apply_one,
      Work.Drive.N2.cE3_apply_two, Real.norm_eq_abs]
    rw [Complex.sq_norm, Complex.normSq_apply, sq_abs, sq_abs]
    ring
  nlinarith [norm_nonneg (Work.Drive.N2.cE3 z), norm_nonneg z]

/-- **The model bound of the relaxed off-pin row.**  At a *strip point* of the widened band — that is,
`|Re (z ^ 2)| ≤ ηb` and `|Im (z ^ 2)| ≤ c₀` — the model picture has norm squared at most `ηb + c₀`:

`‖cE3 (Ψ z)‖² = ‖(Ψ z)²‖ = ‖φ (z²)‖ ≤ |σ (Re z², Im z²)| + |Im z²| ≤ ηb + c₀`,

because the level coordinate `σ` is the convex combination of `Re z²` and `-η`, and both lie in
`[-ηb, ηb]` as soon as `η ≤ ηb`.  (The quadratic bound `√(η² + c₀²)` of
`Work.Drive.N2.saddlePsi_norm_le` is *not* what is needed here: the relaxed row compares against the
*linear* threshold `c₀ + 2η`, which lies far below `√(η² + c₀²)` for `c₀` near `2`.) -/
lemma norm_sq_cE3_saddlePsi_of_band {η δ ηb c₀ : ℝ} (hη : 0 < η) (hηb : η ≤ ηb) (hδ : 0 < δ)
    (h2 : 0 ≤ 2 - 4 * δ) {z : ℂ} (hre : |(z ^ 2).re| ≤ ηb) (him : |(z ^ 2).im| ≤ c₀) :
    ‖Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ z)‖ ^ 2 ≤ ηb + c₀ := by
  have hnorm : ‖Work.Drive.N2.saddlePsi η δ z‖ ^ 2
      = ‖Work.Drive.N2.saddlePhi η δ (z ^ 2)‖ := by
    have hsq : Work.Drive.N2.saddlePsi η δ z ^ 2 = Work.Drive.N2.saddlePhi η δ (z ^ 2) :=
      Work.Drive.N2.saddlePsi_sq hδ h2 z
    rw [← hsq, norm_pow]
  rw [norm_cE3_eq_engine, hnorm]
  have h1 : ‖Work.Drive.N2.saddlePhi η δ (z ^ 2)‖
      ≤ |(Work.Drive.N2.saddlePhi η δ (z ^ 2)).re|
        + |(Work.Drive.N2.saddlePhi η δ (z ^ 2)).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  rw [Work.Drive.N2.saddlePhi_re, Work.Drive.N2.saddlePhi_im] at h1
  have hσ : |Work.Drive.N2.saddleSigma η δ ((z ^ 2).re, (z ^ 2).im)| ≤ ηb := by
    rw [Work.Drive.N2.saddleSigma_apply]
    have hM0 : 0 ≤ Work.Drive.N2.saddleM δ ((z ^ 2).im) :=
      Work.Drive.N2.saddleM_nonneg δ _
    have hM1 : Work.Drive.N2.saddleM δ ((z ^ 2).im) ≤ 1 :=
      Work.Drive.N2.saddleM_le_one δ _
    have hs : (z ^ 2).re ≤ ηb := (abs_le.mp hre).2
    have hs' : -ηb ≤ (z ^ 2).re := (abs_le.mp hre).1
    have hle : -η ≤ ηb := by linarith
    have hle' : -ηb ≤ -η := by linarith
    have hconv : (z ^ 2).re + Work.Drive.N2.saddleM δ ((z ^ 2).im) * (-η - (z ^ 2).re)
        = (1 - Work.Drive.N2.saddleM δ ((z ^ 2).im)) * (z ^ 2).re
          + Work.Drive.N2.saddleM δ ((z ^ 2).im) * (-η) := by ring
    rw [hconv, abs_le]
    constructor
    · have hA : (1 - Work.Drive.N2.saddleM δ ((z ^ 2).im)) * (z ^ 2).re
          ≤ (1 - Work.Drive.N2.saddleM δ ((z ^ 2).im)) * ηb :=
        mul_le_mul_of_nonneg_left hs (by linarith)
      have hB : Work.Drive.N2.saddleM δ ((z ^ 2).im) * (-η)
          ≤ Work.Drive.N2.saddleM δ ((z ^ 2).im) * ηb :=
        mul_le_mul_of_nonneg_left hle hM0
      nlinarith [hA, hB, hM1]
    · have hA : (1 - Work.Drive.N2.saddleM δ ((z ^ 2).im)) * (-ηb)
          ≤ (1 - Work.Drive.N2.saddleM δ ((z ^ 2).im)) * (z ^ 2).re :=
        mul_le_mul_of_nonneg_left hs' (by linarith)
      have hB : Work.Drive.N2.saddleM δ ((z ^ 2).im) * (-ηb)
          ≤ Work.Drive.N2.saddleM δ ((z ^ 2).im) * (-η) :=
        mul_le_mul_of_nonneg_left hle' hM0
      nlinarith [hA, hB, hM1]
  linarith [h1, hσ, him]

end Work.Drive.N2Lead

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology in
open Classical in
/-- **The saddle window with the relaxed off-pin row** (Tier `D2d.3`).  This is
`Work.Drive.N2Lead.saddleWindow_of_packet_band` (Tier `D2a`, on disk and proved) with the off-pin row
of the anchor picture `A` relaxed from `hApos : θ x < 1 → 0 < (A x) 2` to the disjunction
`hAoff : θ x < 1 → (A x) 2 ≠ 0 ∨ c₀ + 2 η < ‖A x‖ ^ 2`, which is what the *planar* park `T₁ (C₀)` of a
Möbius saddle satisfies, plus the band bound `ηb ≤ 4 η / 3` that settles the norm alternative through
the model bound `‖cE3 (saddlePsi η δ (Z x))‖ ^ 2 ≤ c₀ + 4 η / 3 < c₀ + 2 η` at a strip point `x` of
the band.  (`hApos` implies `hAoff`, so this strictly generalises the parent apart from `hlam : 0 < lam`,
which every consumer of the saddle window has.) -/
theorem saddleWindow_of_packet_band_off_noTheta {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {c η δ c₀ lam ηb : ℝ}
    (hη : 0 < η) (hη' : η < 1 / 10) (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hlam : 0 < lam)
    (hc₀ : 2 - 2 * δ < c₀) (hc₀' : c₀ < 2) (hηb : η ≤ ηb) (hηb₂ : ηb ≤ 4 * η / 3)
    {U : Set M} (hU : IsOpen U) {Z : M → ℂ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hZsm : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z U)
    (hZinj : Set.InjOn Z U)
    (hZimm : ∀ x ∈ U, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z x))
    (hlev : ∀ x ∈ U, f x = c + lam * ((Z x) ^ 2).re)
    {foot : M → M} (hfoot : ∀ x : M, ContMDiffAt (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) foot x)
    (hfootinj : ∀ x y : M, f x = f y → foot x = foot y → x = y)
    (hfootimm : ∀ x : M, ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 →
      mfderiv (𝓡 2) (𝓡 2) foot x v = 0 → v = 0)
    (hfootval : ∀ y : M, y ∉ Work.Drive.N2.saddleRegion U Z c₀ →
      f y ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) → f (foot y) = c - lam * η)
    (hfrU : ∀ x : M, x ∈ frontier (Work.Drive.N2.saddleRegion U Z c₀) →
      f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) → x ∈ U)
    {θ : M → ℝ}
    (hθ01 : ∀ x : M, 0 ≤ θ x ∧ θ x ≤ 1)
    {A : M → EuclideanSpace ℝ (Fin 3)}
    (hAsm : ∀ x : M, ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A x)
    (hAinj : ∀ x y : M, f x = c - lam * η → f y = c - lam * η → A x = A y → x = y)
    (hAimm : ∀ x : M, f x = c - lam * η → ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 →
      mfderiv (𝓡 2) (𝓡 3) A x v = 0 → v = 0)
    (hApin : ∀ x : M, f x = c - lam * η → θ x = 1 →
      A x = Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ (Z x)))
    (hAoff : ∀ x : M, f x = c - lam * η → θ x < 1 →
      (A x) 2 ≠ 0 ∨ c₀ + 2 * η < ‖A x‖ ^ 2)
    (hseam : ∀ y : M, f y ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) →
      Z y ∈ Work.Drive.N2.saddleCollar ηb δ →
      Z (foot y) = Work.Drive.N2.saddlePsi η δ (Z y))
    (hcolFr : ∀ x : M, x ∈ frontier (Work.Drive.N2.saddleRegion U Z c₀) →
      f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) →
      ∀ᶠ y in 𝓝 x, f y ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) →
        Z y ∈ Work.Drive.N2.saddleCollar ηb δ)
    (hfootFrint : ∀ x : M, x ∈ frontier (Work.Drive.N2.saddleRegion U Z c₀) →
      f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) → foot x ∈ interior (θ ⁻¹' {1}))
    (hlandFr : ∀ x : M, x ∈ frontier (Work.Drive.N2.saddleRegion U Z c₀) →
      f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) → ∀ᶠ y in 𝓝 x, f (foot y) = c - lam * η)
    (hbig : ∀ x : M, x ∉ Work.Drive.N2.saddleRegion U Z c₀ →
      f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) → θ (foot x) = 1 →
      c₀ ≤ |((Z (foot x)) ^ 2).im|) :
    Work.Drive.N2.GoodDrawingOn f (Set.Ioo (c - lam * ηb) (c + lam * ηb))
      (fun x : M => if x ∈ Work.Drive.N2.saddleRegion U Z c₀ then
        Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ (Z x))
      else A (foot x)) := by
  have h2le : (0 : ℝ) ≤ 2 - 4 * δ := by linarith
  -- ## the two anchor rows at the feet
  have hAnch := saddleWindow_anchorRows_of_foot_band (ηb := ηb) (a := c - lam * η)
    (F := {x : M | f x = c - lam * η}) hfootinj hfootval (fun y hyD hyA => hfootval y hyD hyA)
    (fun x hx y hy _ _ h => hAinj x y hx hy h)
    (fun x hx _ v hdf hv => hAimm x hx v hdf hv)
  refine saddleWindow_drawing_lam_band (ηb := ηb) hη hη' hδ hδ' (ne_of_gt hlam) hc₀ hc₀' hU hZsm
    hZinj hZimm hlev hf hAsm hfoot hfootinj hfootimm hAnch.1 hAnch.2 hfrU hfootval ?_ ?_
  · -- ## the front row
    intro x hxfr hxA
    have hfootV : ∀ᶠ y in 𝓝 x, foot y ∈ interior (θ ⁻¹' {1}) :=
      ((hfoot x).continuousAt).preimage_mem_nhds
        (isOpen_interior.mem_nhds (hfootFrint x hxfr hxA))
    have hband : ∀ᶠ y in 𝓝 x, f y ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) :=
      hf.continuous.continuousAt (isOpen_Ioo.mem_nhds hxA)
    filter_upwards [hband, hfootV, hlandFr x hxfr hxA, hcolFr x hxfr hxA] with y hyb hθy hlandy hcol
    have hθy1 : θ (foot y) = 1 := by
      have h1 : foot y ∈ θ ⁻¹' {1} := interior_subset hθy
      simpa using h1
    have hcoly : Z y ∈ Work.Drive.N2.saddleCollar ηb δ := hcol hyb
    have hpt : A (foot y) = Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ (Z (foot y))) :=
      hApin (foot y) hlandy hθy1
    have hseamy : Z (foot y) = Work.Drive.N2.saddlePsi η δ (Z y) := hseam y hyb hcoly
    have hidem : Work.Drive.N2.saddlePsi η δ (Work.Drive.N2.saddlePsi η δ (Z y))
        = Work.Drive.N2.saddlePsi η δ (Z y) :=
      Work.Drive.N2Lead.saddlePsi_idempotent_of_mem_collarWide hη hη' hηb hδ hδ'
        hcoly.1 hcoly.2.1 hcoly.2.2
    show Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ (Z y)) = A (foot y)
    rw [hpt, hseamy, hidem]
  · -- ## the cross row
    intro x hxD hxA y hyD hyA hfxy
    have hfy : f (foot y) = c - lam * η := hfootval y hyD hyA
    by_cases hθy : θ (foot y) = 1
    · -- the pinned foot: the algebra of the squares
      intro hcoll
      have h1 : Work.Drive.N2.saddlePsi η δ (Z x)
          = Work.Drive.N2.saddlePsi η δ (Z (foot y)) := by
        have h := hApin (foot y) hfy hθy
        exact Work.Drive.N2.cE3_injective (hcoll.trans h)
      have hs : (Work.Drive.N2.saddlePsi η δ (Z x)) ^ 2
          = (Work.Drive.N2.saddlePsi η δ (Z (foot y))) ^ 2 := by rw [h1]
      rw [Work.Drive.N2.saddlePsi_sq hδ h2le, Work.Drive.N2.saddlePsi_sq hδ h2le] at hs
      have him : ((Z x) ^ 2).im = ((Z (foot y)) ^ 2).im := by
        have h := congrArg Complex.im hs
        rwa [Work.Drive.N2.saddlePhi_im, Work.Drive.N2.saddlePhi_im] at h
      have hxlt : |((Z x) ^ 2).im| < c₀ := hxD.2
      have hyge : c₀ ≤ |((Z (foot y)) ^ 2).im| := hbig y hyD hyA hθy
      rw [him] at hxlt
      linarith
    · -- the unpinned foot: the two disjuncts of the relaxed off-pin row
      intro hcoll
      have hθlt : θ (foot y) < 1 := lt_of_le_of_ne (hθ01 (foot y)).2 hθy
      rcases hAoff (foot y) hfy hθlt with hne | hfbig
      · -- the third coordinate of the anchor picture does not vanish
        have h2 : (Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ (Z x))) 2 = 0 :=
          Work.Drive.N2.cE3_apply_two _
        rw [hcoll] at h2
        exact hne h2
      · -- the model picture is too short to reach the anchor norm
        have hlt : ‖Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ (Z x))‖ ^ 2 < c₀ + 2 * η := by
          have hb : ‖Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ (Z x))‖ ^ 2 ≤ ηb + c₀ :=
            norm_sq_cE3_saddlePsi_of_band (η := η) (δ := δ) (ηb := ηb) (c₀ := c₀)
              hη hηb hδ h2le ?_ ?_
          · linarith
          · -- the real part of the square lies in the widened band
            have hlevx := hlev x hxD.1
            have h1 := hxA.1
            have h2 := hxA.2
            rw [hlevx] at h1 h2
            exact le_of_lt (abs_lt.mpr ⟨by nlinarith, by nlinarith⟩)
          · -- the imaginary part of the square lies in the strip
            exact le_of_lt hxD.2
        rw [hcoll] at hlt
        linarith


end Work.Drive.N2Lead
