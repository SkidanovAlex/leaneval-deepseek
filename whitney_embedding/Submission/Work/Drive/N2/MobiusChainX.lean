import Mathlib
import Submission.Work.Drive.N2C.mobiusShape
import Submission.Work.Drive.N2Lead.mobiusUpperDefs
import Submission.Work.Drive.N2Lead.mobiusUpperStarRowKit
import Submission.Work.Drive.N2Lead.mobiusGoodDrawing
import Submission.Work.Drive.N2C.wideCollar
import Submission.Work.Drive.N2Lead.mobiusUpperFootKit
import Submission.Work.Drive.N2C.mfrFootPlumbing
import Submission.Work.Drive.N2C.mobiusPacketExists
import Submission.Work.Drive.N2Lead.mobiusUpperCertified
import Submission.Work.Drive.N2Lead.mobiusLowerCertified
import Submission.Work.Drive.N2Lead.mobiusWindowEngine
import Submission.Work.Drive.N2Lead.isCertifiedAt_of_starRegions
import Submission.Work.Drive.N2Lead.isCertifiedAt_of_ambientPath
import Submission.Work.Drive.N2Lead.twistToolkit
import Submission.Work.Drive.N2Lead.twistIsometry
import Submission.Work.Drive.N2C.negTransfer
import Submission.Work.Drive.N2C.saddlePinDichotomy
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2.GoodDrawingFamily
import Submission.Work.Drive.N2Lead.saddlePinDefs
import Submission.Work.Drive.N2Lead.saddleWindowLiftData
import Submission.Work.Drive.N2Lead.saddleWindowCertifiedSplit
import Submission.Work.Drive.N2Lead.exists_junkZeroDatum
import Submission.Work.Drive.N2Lead.exists_reflectedDatum

/-!
# H8's independent chain for the twisted Möbius upper certificate

The compact `n = 2` endgame consumes the upper certificate of the Möbius saddle window through the
chain `mobiusUpperStarRowsOfShape → mobiusUpperCertifiedOfShape → saddleWindowCertifiedMobiusShape
→ saddleCoreOneCompShape → exists_certifiedWindow_saddle_of_core → certifiedWindowSaddle_of_core`.
Every link is a short composition; the *only* mathematical input is the core rows of the twisted
Möbius picture (`Work.Drive.N2C.mfrCoreRows`).  This file reproduces the chain with its own region
data (`xCentres`/`xRegions`/`xRays`, verbatim copies of the lane's `mfr*`) so that the target is
independent of the lane's own files, and parameterises every link by the core rows
(`CoreRowsAll`).  The instantiation of `CoreRowsAll` is a separate, one-line file.

Every link below is proved outright; the chain is complete modulo its explicit `CoreRowsAll`
hypothesis (which `MobiusChainInstantiate.lean` discharges).
-/

open scoped Manifold ContDiff Topology

namespace Work.Drive.N2.MfrX

open Set Filter

noncomputable section

/-! ## 1. The region data (copies of the lane's `mfr*`) -/

/-- The centres of the star regions. -/
def xCentres (n : ℕ) (i : Fin n) (Dp : ℝ) : Fin n → ℂ :=
  fun k => if k = i then 0
    else Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n k) + (Dp : ℂ) * Complex.I

/-- The star regions. -/
def xRegions (n : ℕ) (i : Fin n) (Dp : ℝ) : Fin n → Set ℂ :=
  fun k => if k = i then Metric.ball (0 : ℂ) (Dp + 5) else Metric.ball (xCentres n i Dp k) 2

/-- The rays of the star regions. -/
def xRays (n : ℕ) (i : Fin n) : Fin n → ℂ := fun k => if k = i then 1 else -1

theorem x_isOpen_convex (n : ℕ) (i : Fin n) (Dp : ℝ) (k : Fin n) :
    IsOpen (xRegions n i Dp k) ∧ Convex ℝ (xRegions n i Dp k) := by
  unfold xRegions
  split
  · exact ⟨Metric.isOpen_ball, convex_ball _ _⟩
  · exact ⟨Metric.isOpen_ball, convex_ball _ _⟩

theorem x_closedBall_subset (n : ℕ) (i : Fin n) (Dp : ℝ) (hDp : 0 ≤ Dp) (k : Fin n) :
    Metric.closedBall (xCentres n i Dp k) (1 / 2) ⊆ xRegions n i Dp k := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  by_cases hk : k = i
  · rw [xRegions, if_pos hk, Metric.mem_ball, dist_zero_right]
    rw [xCentres, if_pos hk] at hz
    simp only [sub_zero] at hz
    linarith
  · rw [xRegions, if_neg hk, Metric.mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt hz (by norm_num)

theorem xCentres_im (n : ℕ) (i : Fin n) (Dp : ℝ) {k : Fin n} (hk : k ≠ i) :
    (xCentres n i Dp k).im = 20 + 5 * (k : ℕ) + Dp := by
  simp [xCentres, if_neg hk, Work.Drive.N2Lead.proj2, Work.Drive.N2Lead.farPos,
    Complex.add_im, Complex.mul_im]

theorem xCentres_re (n : ℕ) (i : Fin n) (Dp : ℝ) {k : Fin n} (hk : k ≠ i) :
    (xCentres n i Dp k).re = -20 := by
  simp [xCentres, if_neg hk, Work.Drive.N2Lead.proj2, Work.Drive.N2Lead.farPos,
    Complex.add_re, Complex.mul_re]

theorem x_norm_centres_ge (n : ℕ) (i : Fin n) {Dp : ℝ} (hDp : 0 ≤ Dp) {k : Fin n}
    (hk : k ≠ i) : Dp + 20 ≤ ‖xCentres n i Dp k‖ := by
  have h1 : |(xCentres n i Dp k).im| ≤ ‖xCentres n i Dp k‖ := Complex.abs_im_le_norm _
  rw [xCentres_im n i Dp hk, abs_of_nonneg (by positivity)] at h1
  have : (0 : ℝ) ≤ (k : ℕ) := Nat.cast_nonneg _
  linarith

theorem x_dist_centres_ge (n : ℕ) (i : Fin n) (Dp : ℝ) {k l : Fin n}
    (hk : k ≠ i) (hl : l ≠ i) (hkl : k ≠ l) :
    5 ≤ ‖xCentres n i Dp k - xCentres n i Dp l‖ := by
  have him : (xCentres n i Dp k - xCentres n i Dp l).im
      = 5 * (((k : ℕ) : ℝ) - ((l : ℕ) : ℝ)) := by
    rw [Complex.sub_im, xCentres_im n i Dp hk, xCentres_im n i Dp hl]
    ring
  have h2 := Complex.abs_im_le_norm (xCentres n i Dp k - xCentres n i Dp l)
  rw [him] at h2
  have hne : ((k : ℕ) : ℝ) - ((l : ℕ) : ℝ) ≠ 0 := by
    have h : ((k : ℕ) : ℝ) ≠ ((l : ℕ) : ℝ) := by
      intro hc
      exact hkl (Fin.ext (by exact_mod_cast hc))
    exact sub_ne_zero.mpr h
  have h1 : (1 : ℝ) ≤ |((k : ℕ) : ℝ) - ((l : ℕ) : ℝ)| := by
    obtain ⟨m, hm⟩ : ∃ m : ℤ, ((k : ℕ) : ℝ) - ((l : ℕ) : ℝ) = (m : ℝ) :=
      ⟨((k : ℕ) : ℤ) - ((l : ℕ) : ℤ), by push_cast; ring⟩
    have hm0 : m ≠ 0 := by
      intro h0
      exact hne (by rw [hm, h0]; norm_num)
    have hle := Int.one_le_abs hm0
    rw [hm]
    exact_mod_cast hle
  calc (5 : ℝ) = 5 * 1 := by ring
    _ ≤ 5 * |((k : ℕ) : ℝ) - ((l : ℕ) : ℝ)| := by linarith
    _ = |5 * (((k : ℕ) : ℝ) - ((l : ℕ) : ℝ))| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5)]
    _ ≤ ‖xCentres n i Dp k - xCentres n i Dp l‖ := h2

theorem x_pairwiseDisjoint (n : ℕ) (i : Fin n) {Dp : ℝ} (hDp : 0 ≤ Dp) :
    Pairwise fun k l : Fin n => Disjoint (xRegions n i Dp k) (xRegions n i Dp l) := by
  intro k l hkl
  rw [Set.disjoint_left]
  intro z hzk hzl
  by_cases hk : k = i
  · have hl : l ≠ i := fun h => hkl (hk.trans h.symm)
    rw [xRegions, if_pos hk, Metric.mem_ball, dist_zero_right] at hzk
    rw [xRegions, if_neg hl, Metric.mem_ball, dist_eq_norm] at hzl
    have hge := x_norm_centres_ge n i hDp hl
    have h3 : ‖xCentres n i Dp l‖ ≤ ‖z - xCentres n i Dp l‖ + ‖z‖ := by
      have h := norm_add_le (xCentres n i Dp l - z) z
      rw [sub_add_cancel] at h
      rw [norm_sub_rev] at h
      exact h
    linarith
  · by_cases hl : l = i
    · rw [xRegions, if_neg hk, Metric.mem_ball, dist_eq_norm] at hzk
      rw [xRegions, if_pos hl, Metric.mem_ball, dist_zero_right] at hzl
      have hge := x_norm_centres_ge n i hDp hk
      have h3 : ‖xCentres n i Dp k‖ ≤ ‖z - xCentres n i Dp k‖ + ‖z‖ := by
        have h := norm_add_le (xCentres n i Dp k - z) z
        rw [sub_add_cancel] at h
        rw [norm_sub_rev] at h
        exact h
      linarith
    · rw [xRegions, if_neg hk, Metric.mem_ball, dist_eq_norm] at hzk
      rw [xRegions, if_neg hl, Metric.mem_ball, dist_eq_norm] at hzl
      have h5 := x_dist_centres_ge n i Dp hk hl hkl
      have h4 : ‖xCentres n i Dp k - xCentres n i Dp l‖
          ≤ ‖z - xCentres n i Dp l‖ + ‖z - xCentres n i Dp k‖ := by
        rw [show xCentres n i Dp k - xCentres n i Dp l
            = (z - xCentres n i Dp l) - (z - xCentres n i Dp k) by ring]
        exact norm_sub_le _ _
      linarith
/-! ## 2. The core rows as an explicit hypothesis -/

/-- **The core rows of the twisted Möbius upper picture** for one datum, width and packet: the level
`f p + 3η/2` is covered by the star regions, is non-radial in each of them, and meets each ray at
most once. -/
def CoreRows {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) (η : ℝ)
    (S : Work.Drive.N2Lead.MobiusPacket D η) : Prop :=
  ∃ (ε εp Dp : ℝ), 0 < ε ∧ 0 < εp ∧ 0 ≤ Dp ∧
    (∀ y : M, f y = f p + 3 * η / 2 → ∃ k : Fin S.n,
      Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)
        ∈ xRegions S.n S.i Dp k) ∧
    (∀ (y : M) (k : Fin S.n), f y = f p + 3 * η / 2 →
      Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)
          ∈ xRegions S.n S.i Dp k →
      Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)
          ≠ xCentres S.n S.i Dp k ∧
      ∀ v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) y,
        mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ ℝ) f y v = 0 → v ≠ 0 →
        ¬ (∃ t : ℝ, mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
            (modelWithCornersSelf ℝ ℂ)
            (fun z : M => Work.Drive.N2Lead.proj2
              (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp z)) y v
          = t • (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)
              - xCentres S.n S.i Dp k))) ∧
    (∀ k : Fin S.n, xRays S.n S.i k ≠ 0 ∧ ∀ x y : M, f x = f p + 3 * η / 2 →
      f y = f p + 3 * η / 2 →
      (∃ s : ℝ, 0 < s ∧ Work.Drive.N2Lead.proj2
          (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp x)
        = xCentres S.n S.i Dp k + s • xRays S.n S.i k) →
      (∃ s : ℝ, 0 < s ∧ Work.Drive.N2Lead.proj2
          (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)
        = xCentres S.n S.i Dp k + s • xRays S.n S.i k) → x = y)

/-! ## 3. The star rows of the twisted Möbius picture -/

theorem starRowsX {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (hcore : ∀ {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
      (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
      (hsep : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η < 2 * D.ηd)
      (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
      (S : Work.Drive.N2Lead.MobiusPacket D η) (hshape : Work.Drive.N2C.MobiusShape D η S),
      CoreRows D η S)
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (hsep : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η < 2 * D.ηd)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (S : Work.Drive.N2Lead.MobiusPacket D η) (hshape : Work.Drive.N2C.MobiusShape D η S) :
    ∃ (ε εp Dp : ℝ) (K : ℕ) (Ω : Fin K → Set ℂ) (o : Fin K → ℂ) (ρ : Fin K → ℝ)
      (e : Fin K → ℂ),
      0 < ε ∧ 0 < εp ∧ 0 ≤ Dp ∧ (∀ k, IsOpen (Ω k) ∧ Convex ℝ (Ω k)) ∧ (∀ k, 0 < ρ k) ∧
      (∀ k, Metric.closedBall (o k) (ρ k) ⊆ Ω k) ∧ (Pairwise fun k l => Disjoint (Ω k) (Ω l)) ∧
      (∀ y : M, f y = f p + 3 * η / 2 → ∃ k, Work.Drive.N2Lead.proj2
        (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y) ∈ Ω k) ∧
      (∀ (y : M) (k : Fin K), f y = f p + 3 * η / 2 → Work.Drive.N2Lead.proj2
          (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y) ∈ Ω k →
        Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y) ≠ o k ∧
        ∀ v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) y,
          mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
            (modelWithCornersSelf ℝ ℝ) f y v = 0 → v ≠ 0 →
          ¬ (∃ t : ℝ, mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
              (modelWithCornersSelf ℝ ℂ) (fun z : M => Work.Drive.N2Lead.proj2
                (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp z)) y v
            = t • (Work.Drive.N2Lead.proj2
                (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y) - o k))) ∧
      (∀ k : Fin K, e k ≠ 0 ∧ ∀ x y : M, f x = f p + 3 * η / 2 → f y = f p + 3 * η / 2 →
        (∃ s : ℝ, 0 < s ∧ Work.Drive.N2Lead.proj2
            (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp x) = o k + s • e k) →
        (∃ s : ℝ, 0 < s ∧ Work.Drive.N2Lead.proj2
            (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y) = o k + s • e k) → x = y) := by
  obtain ⟨ε, εp, Dp, hε, hεp, hDp, hcov, hrate, hray⟩ :=
    hcore (p := p) D (η := η) hη hsmall hsep hf S hshape
  refine ⟨ε, εp, Dp, S.n, xRegions S.n S.i Dp, xCentres S.n S.i Dp, fun _ => 1 / 2,
    xRays S.n S.i, hε, hεp, hDp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; exact x_isOpen_convex S.n S.i Dp k
  · intro k; norm_num
  · intro k; exact x_closedBall_subset S.n S.i Dp hDp k
  · exact x_pairwiseDisjoint S.n S.i hDp
  · intro y hy; exact hcov y hy
  · intro y k hy hmem
    exact ⟨(hrate y k hy hmem).1, (hrate y k hy hmem).2⟩
  · intro k
    refine ⟨?_, (hray k).2⟩
    unfold xRays
    by_cases hk : k = S.i <;> simp [hk]

/-! ## 4. The upper certificate of the Möbius window, from the star rows -/

theorem certifiedOfShapeX {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (hcore : ∀ {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
      (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
      (hsep : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η < 2 * D.ηd)
      (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
      (S : Work.Drive.N2Lead.MobiusPacket D η) (hshape : Work.Drive.N2C.MobiusShape D η S),
      CoreRows D η S)
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (hsep : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η < 2 * D.ηd)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (S : Work.Drive.N2Lead.MobiusPacket D η) (hshape : Work.Drive.N2C.MobiusShape D η S) :
    Work.Drive.N2C.IsCertifiedAt f (f p + 3 * η / 2)
      (Work.Drive.N2Lead.mobiusWindowDrawing D η S) := by
  classical
  obtain ⟨ε, εp, Dp, K, Ω, o, ρ, e, hε, hεp, hDp, hΩ, hρ, hball, hdisj, hin, hrate, hhit⟩ :=
    starRowsX hcore (f := f) (p := p) D hη hsmall hsep hf S hshape
  set u : ℝ := f p + 3 * η / 2 with hu
  have hmem : u ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) := by
    rw [hu]; constructor <;> linarith
  have hW := Work.Drive.N2Lead.mobiusGoodDrawing D hη hsmall hf S
  have hiso0 : Work.Drive.N2C.IsLevelIsotopy f u
      (fun _ : ℝ => Work.Drive.N2Lead.mobiusWindowDrawing D η S) := by
    refine ⟨?_, ?_, ?_⟩
    · intro s y hy
      have h1 : ContMDiffAt (𝓡 2) (𝓡 3) Work.Drive.N2Lead.tpTop
          (Work.Drive.N2Lead.mobiusWindowDrawing D η S) y :=
        hW.1 y (by rw [hy, hu]; exact hmem)
      have h2 : ContMDiffAt ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (𝓡 3) Work.Drive.N2Lead.tpTop
          (fun q : ℝ × M => Work.Drive.N2Lead.mobiusWindowDrawing D η S q.2) (s, y) :=
        h1.comp (s, y) contMDiffAt_snd
      simpa only [Function.comp_def] using h2
    · intro s x y hx hy h
      exact hW.2.2 x y (by rw [hx, hu]; exact hmem) (by rw [hy, hu]; exact hmem)
        (by rw [hx, hy]) h
    · intro s y hy v hv h
      exact hW.2.1 y (by rw [hy, hu]; exact hmem) v hv h
  have hisoY : Work.Drive.N2C.IsLevelIsotopy f u
      (fun _ : ℝ => fun y => Work.Drive.N2Lead.twistY S.a' (-1)
        (Work.Drive.N2Lead.mobiusWindowDrawing D η S y)) :=
    Work.Drive.N2Lead.isLevelIsotopy_comp_global hiso0
      (F := Work.Drive.N2Lead.twistY S.a' (-1))
      (Work.Drive.N2Lead.contDiff_twistY_fixed S.a' (-1))
      (Work.Drive.N2Lead.twistY_injective S.a' (-1))
      (fun w => Work.Drive.N2Lead.injective_fderiv_twistY S.a' (-1) w)
  have hisoX : Work.Drive.N2C.IsLevelIsotopy f u
      (fun _ : ℝ => fun y => Work.Drive.N2Lead.twistX ε (-1)
        (Work.Drive.N2Lead.twistY S.a' (-1)
          (Work.Drive.N2Lead.mobiusWindowDrawing D η S y))) :=
    Work.Drive.N2Lead.isLevelIsotopy_comp_global hisoY
      (F := Work.Drive.N2Lead.twistX ε (-1))
      (Work.Drive.N2Lead.contDiff_twistX_fixed ε (-1))
      (Work.Drive.N2Lead.twistX_injective ε (-1))
      (fun w => Work.Drive.N2Lead.injective_fderiv_twistX ε (-1) w)
  have hisoV : Work.Drive.N2C.IsLevelIsotopy f u
      (fun _ : ℝ => Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp) := by
    have h := Work.Drive.N2Lead.isLevelIsotopy_comp_global hisoX
      (F := Work.Drive.N2Lead.pushY Dp εp 1)
      ((Work.Drive.N2Lead.contDiff_pushY Dp εp).comp (contDiff_const.prodMk contDiff_id))
      (Work.Drive.N2Lead.pushY_injective Dp εp 1 hεp hDp)
      (fun w => Work.Drive.N2Lead.injective_fderiv_pushY Dp εp 1 hεp hDp w)
    rwa [show (fun _ : ℝ => fun y => Work.Drive.N2Lead.pushY Dp εp 1
        (Work.Drive.N2Lead.twistX ε (-1)
          (Work.Drive.N2Lead.twistY S.a' (-1)
            (Work.Drive.N2Lead.mobiusWindowDrawing D η S y)))) =
      (fun _ : ℝ => Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp) from by
        funext s y
        simp only [Work.Drive.N2Lead.mobiusTwisted]] at h
  have hreg : ∀ x : M, f x = u → ¬ Work.Drive.Morse.IsCritical f x := by
    intro x hx
    exact Work.Drive.N2Lead.mobiusUpper_not_critical (D := D) hη hsep x
      (by rw [hu] at hx; exact hx)
  have hcertT : Work.Drive.N2C.IsCertifiedAt f u
      (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp) :=
    Work.Drive.N2Lead.isCertifiedAt_of_starRegions hf hreg hisoV Ω o ρ hΩ hρ hball hdisj hin hrate
      (fun k => ⟨e k, (hhit k).1, (hhit k).2⟩)
  have hcert1 : Work.Drive.N2C.IsCertifiedAt f u
      (fun y => Work.Drive.N2Lead.twistX ε (-1) (Work.Drive.N2Lead.twistY S.a' (-1)
        (Work.Drive.N2Lead.mobiusWindowDrawing D η S y))) :=
    Work.Drive.N2Lead.isCertifiedAt_of_ambientPath hf hreg hisoX
      (Work.Drive.N2Lead.ambientPath_pushY Dp εp hεp hDp)
      (by show Work.Drive.N2C.IsCertifiedAt f u (fun y => Work.Drive.N2Lead.pushY Dp εp 1
            (Work.Drive.N2Lead.twistX ε (-1) (Work.Drive.N2Lead.twistY S.a' (-1)
              (Work.Drive.N2Lead.mobiusWindowDrawing D η S y)))); exact hcertT)
  have hcert2 : Work.Drive.N2C.IsCertifiedAt f u
      (fun y => Work.Drive.N2Lead.twistY S.a' (-1)
        (Work.Drive.N2Lead.mobiusWindowDrawing D η S y)) :=
    Work.Drive.N2Lead.isCertifiedAt_of_ambientPath hf hreg hisoY
      (Work.Drive.N2Lead.ambientPath_twistX ε)
      (by show Work.Drive.N2C.IsCertifiedAt f u (fun y => Work.Drive.N2Lead.twistX ε (-1)
            (Work.Drive.N2Lead.twistY S.a' (-1)
              (Work.Drive.N2Lead.mobiusWindowDrawing D η S y))); exact hcert1)
  have hcert3 : Work.Drive.N2C.IsCertifiedAt f u
      (Work.Drive.N2Lead.mobiusWindowDrawing D η S) :=
    Work.Drive.N2Lead.isCertifiedAt_of_ambientPath hf hreg hiso0
      (Work.Drive.N2Lead.ambientPath_twistY S.a')
      (by show Work.Drive.N2C.IsCertifiedAt f u
            (fun y => Work.Drive.N2Lead.twistY S.a' (-1)
              (Work.Drive.N2Lead.mobiusWindowDrawing D η S y)); exact hcert2)
  exact hcert3

/-! ## 5. The certified Möbius saddle window, from the shape producer -/

theorem saddleWindowCertifiedMobiusShapeX {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (hcore : ∀ {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
      (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
      (hsep : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η < 2 * D.ηd)
      (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
      (S : Work.Drive.N2Lead.MobiusPacket D η) (hshape : Work.Drive.N2C.MobiusShape D η S),
      CoreRows D η S)
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hs1 : D.s₁ D.j = 1) (hs2 : D.s₂ D.j = -1)
    (hjunk : ∀ y : M, y ∉ (D.φ D.j).source → D.φ D.j y = 0)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {η : ℝ} (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (hsep : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η < 2 * D.ηd)
    {n : ℕ} {L : Work.Drive.N2C.LevelCurves f (f p - 3 * η / 2) n} {i : Fin n}
    {τU τL : ℝ → ℝ}
    (hτUsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τU (Set.Ioo (-3) 3))
    (hτUd : ∀ w ∈ Set.Ioo (-3) 3, deriv τU w ≠ 0)
    (hτUanti : StrictAntiOn τU (Set.Ioo (-3) 3))
    (hτUval : ∀ w ∈ Set.Ioo (-3) 3,
      L.γ i (τU w) = Work.Drive.N2Lead.arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
    (hτLsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τL (Set.Ioo (-3) 3))
    (hτLd : ∀ w ∈ Set.Ioo (-3) 3, deriv τL w ≠ 0)
    (hτLmono : StrictMonoOn τL (Set.Ioo (-3) 3))
    (hτLval : ∀ w ∈ Set.Ioo (-3) 3,
      L.γ i (τL w) = Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
    (hord : τU (99 / 50) < τU (-(99 / 50)) ∧ τU (-(99 / 50)) < τL (-(99 / 50)) ∧
      τL (-(99 / 50)) < τL (99 / 50) ∧ τL (99 / 50) < τU (99 / 50) + 1) :
    ∃ W : M → EuclideanSpace ℝ (Fin 3),
      Work.Drive.N2.GoodDrawingOn f (Set.Ioo (f p - 2 * η) (f p + 2 * η)) W ∧
      Work.Drive.N2C.IsCertifiedAt f (f p - 3 * η / 2) W ∧
      Work.Drive.N2C.IsCertifiedAt f (f p + 3 * η / 2) W := by
  obtain ⟨S, hshape⟩ := Work.Drive.N2C.mobiusPacketExistsShape (D := D) hs1 hs2 hjunk hf hη hsmall
    hsep hτUsm hτUd hτUanti hτUval hτLsm hτLd hτLmono hτLval hord
  exact ⟨Work.Drive.N2Lead.mobiusWindowDrawing D η S,
    Work.Drive.N2Lead.mobiusGoodDrawing D hη hsmall hf S,
    Work.Drive.N2Lead.mobiusLowerCertified D hη hsmall hf S,
    certifiedOfShapeX hcore (f := f) (p := p) D hη hsmall hsep hf S hshape.some⟩

/-! ## 6. The one-component core, from the certified Möbius window -/

/-- **The normalised datum**: a local copy of the lane's helper (whose module cannot be imported
because it depends on the open star rows). -/
theorem exists_normalizedDatumLocalShapeX {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hsad : D.s₁ D.j ≠ D.s₂ D.j) :
    ∃ D' : Work.Drive.N2.WindowDatum f p,
      D'.s₁ D'.j = 1 ∧ D'.s₂ D'.j = -1 ∧
      (D'.φ D'.j).source = (D.φ D.j).source ∧
      (∀ y : M, y ∉ (D.φ D.j).source → D'.φ D'.j y = 0) ∧
      (∀ (v m : ℝ), Work.Drive.N2Lead.saddlePin D' v m = Work.Drive.N2Lead.saddlePin D v m) ∧
      D'.ρ D'.j = D.ρ D.j ∧ D'.C D'.j = D.C D.j ∧ D'.ηd = D.ηd ∧
      D'.x D'.j = D.x D.j ∧ (∀ y : ℝ × M, D'.Φ y = D.Φ y) := by
  rcases D.hsgn D.j with ⟨h1 | h1, h2 | h2⟩
  · exact absurd (by rw [h1, h2]) hsad
  · obtain ⟨D', hsrc, _ha, hj, hs1, hs2, hρ, hC, hηd, hx, hΦ, hpin⟩ :=
      Work.Drive.N2Lead.exists_junkZeroDatum D
    exact ⟨D', by rw [hs1, h1], by rw [hs2, h2], hsrc, hj, hpin, hρ, hC, hηd, hx, hΦ⟩
  · obtain ⟨D₁, hs1₁, hs2₁, hsrc₁, _hsw, hρ₁, hC₁, hηd₁, hx₁, hΦ₁, hpin₁⟩ :=
      Work.Drive.N2Lead.exists_reflectedDatum D h1 h2
    obtain ⟨D', hsrc', _ha', hj', hs1', hs2', hρ', hC', hηd', hx', hΦ', hpin'⟩ :=
      Work.Drive.N2Lead.exists_junkZeroDatum D₁
    refine ⟨D', by rw [hs1', hs1₁], by rw [hs2', hs2₁], by rw [hsrc', hsrc₁], ?_, ?_,
      by rw [hρ', hρ₁], by rw [hC', hC₁], by rw [hηd', hηd₁], by rw [hx', hx₁],
      fun y => (hΦ' y).trans (hΦ₁ y)⟩
    · intro y hy
      exact hj' y (by simpa [hsrc₁] using hy)
    · intro v m
      exact (hpin' v m).trans (hpin₁ v m)
  · exact absurd (by rw [h1, h2]) hsad

/-- **The one-component core**, from the certified Möbius window. -/
theorem saddleCoreOneCompShapeX {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (hcore : ∀ {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
      (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
      (hsep : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η < 2 * D.ηd)
      (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
      (S : Work.Drive.N2Lead.MobiusPacket D η) (hshape : Work.Drive.N2C.MobiusShape D η S),
      CoreRows D η S)
    {f : M → ℝ} (hf : Work.Drive.Morse.IsMorseDistinct f) {p : M}
    (D : Work.Drive.N2.WindowDatum f p) (hsad : D.s₁ D.j ≠ D.s₂ D.j)
    (hmorse : Work.Drive.Morse.MorseLemma2) :
    ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η : ℝ, 0 < η → η ≤ η₁ →
      Work.Drive.N2Lead.OnOneComponent (f := f) (f p - 3 * η / 2)
          (Work.Drive.N2Lead.saddlePin D (f p - 3 * η / 2) (99 / 50)) →
      ∃ W : M → EuclideanSpace ℝ (Fin 3),
        Work.Drive.N2.GoodDrawingOn f (Set.Ioo (f p - 2 * η) (f p + 2 * η)) W ∧
        Work.Drive.N2C.IsCertifiedAt f (f p - 3 * η / 2) W ∧
        Work.Drive.N2C.IsCertifiedAt f (f p + 3 * η / 2) W := by
  classical
  obtain ⟨D', hs1, hs2, hsrc, hjunk₀, hpin, hρ, _hC, hηd, _hx, _hΦ⟩ :=
    exists_normalizedDatumLocalShapeX D hsad
  have hjunk : ∀ y : M, y ∉ (D'.φ D'.j).source → D'.φ D'.j y = 0 :=
    fun y hy => hjunk₀ y (by simpa [hsrc] using hy)
  obtain ⟨η₁, hη₁, hdata⟩ := Work.Drive.N2Lead.saddleWindowLiftData hf D' hs1 hs2 hjunk hmorse
  refine ⟨min η₁ (min ((D.ρ D.j / 8) ^ 2 / 800) (D.ηd / 2)),
    lt_min hη₁ (lt_min (by have := D.hρ D.j; positivity) (by linarith [D.hηd])), ?_⟩
  intro η hη hle hone
  have hle1 : η ≤ η₁ := le_trans hle (min_le_left _ _)
  have hle2 : η ≤ (D.ρ D.j / 8) ^ 2 / 800 :=
    le_trans hle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hle3 : η ≤ D.ηd / 2 := le_trans hle (le_trans (min_le_right _ _) (min_le_right _ _))
  have hρpos : 0 < (D.ρ D.j / 8) ^ 2 := by
    have := D.hρ D.j; positivity
  have hsmall : Work.Drive.N2.packetEtaB D' η < 1 / 200 := by
    rw [Work.Drive.N2.packetEtaB, hρ, div_lt_iff₀ hρpos]
    nlinarith [hle2]
  have hsep : (D'.ρ D'.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D' η < 2 * D'.ηd := by
    rw [Work.Drive.N2.packetEtaB_law, hηd]
    linarith [hle3, D.hηd]
  have hone' : Work.Drive.N2Lead.OnOneComponent (f := f) (f p - 3 * η / 2)
      (Work.Drive.N2Lead.saddlePin D' (f p - 3 * η / 2) (99 / 50)) := by
    rw [hpin (f p - 3 * η / 2) (99 / 50)]
    exact hone
  obtain ⟨n, L, i, τU, τL, hτUsm, hτUd, hτUanti, hτUval, hτLsm, hτLd, hτLval, hcase⟩ :=
    hdata η hη hle1 hone'
  rcases hcase with ⟨hτLanti, ho1, ho2, ho3, ho4⟩ | ⟨hτLmono, ho1, ho2, ho3, ho4⟩
  · exact Work.Drive.N2Lead.saddleWindowCertifiedSplit D' hs1 hs2 hjunk hf.1 hη hsmall hsep
      hτUsm hτUd hτUanti hτUval hτLsm hτLd hτLanti hτLval ⟨ho1, ho2, ho3, ho4⟩
  · exact saddleWindowCertifiedMobiusShapeX hcore D' hs1 hs2 hjunk hf.1 hη hsmall hsep
      hτUsm hτUd hτUanti hτUval hτLsm hτLd hτLmono hτLval ⟨ho1, ho2, ho3, ho4⟩

/-! ## 7. `D2` from the core and the pin dichotomy -/

/-- The saddle sign row is unchanged by `D ↦ D.neg`. -/
theorem x_neg_saddle_sign {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hsad : D.s₁ D.j ≠ D.s₂ D.j) :
    (Work.Drive.N2C.WindowDatum.neg D).s₁ (Work.Drive.N2C.WindowDatum.neg D).j
      ≠ (Work.Drive.N2C.WindowDatum.neg D).s₂ (Work.Drive.N2C.WindowDatum.neg D).j := by
  have h1 : (Work.Drive.N2C.WindowDatum.neg D).s₁ = fun i => -D.s₁ i := rfl
  have h2 : (Work.Drive.N2C.WindowDatum.neg D).s₂ = fun i => -D.s₂ i := rfl
  have h3 : (Work.Drive.N2C.WindowDatum.neg D).j = D.j := rfl
  rw [h1, h2, h3]
  intro h
  exact hsad (neg_injective h)

/-- `OnOneComponent` is unchanged by passing to `-f`. -/
theorem x_onOneComponent_neg {M : Type*} [TopologicalSpace M]
    {f : M → ℝ} {v : ℝ} {S : Set M} :
    Work.Drive.N2Lead.OnOneComponent (f := fun x : M => -f x) (-v) S ↔
      Work.Drive.N2Lead.OnOneComponent (f := f) v S := by
  have hset : {z : M | (fun x : M => -f x) z = -v} = {z : M | f z = v} := by
    ext z
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  unfold Work.Drive.N2Lead.OnOneComponent
  rw [hset]

/-- A good drawing for `-f` on the band `A` is a good drawing for `f` on the band `-A`. -/
theorem x_goodDrawingOn_of_neg {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {A : Set ℝ} {g : M → EuclideanSpace ℝ (Fin 3)}
    (h : Work.Drive.N2.GoodDrawingOn (fun x : M => -f x) A g) :
    Work.Drive.N2.GoodDrawingOn f {t : ℝ | -t ∈ A} g := by
  have hfun : (fun x : M => -(fun y : M => -f y) x) = f := by
    funext x
    simp
  have h' := (Work.Drive.N2C.goodDrawingOn_neg_iff (f := fun y : M => -f y)).mp h
  rwa [hfun] at h'

/-- A certificate for `-f` at the level `-u` is a certificate for `f` at the level `u`. -/
theorem x_isCertifiedAt_of_neg {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {u : ℝ} {g : M → EuclideanSpace ℝ (Fin 3)}
    (h : Work.Drive.N2C.IsCertifiedAt (fun x : M => -f x) (-u) g) :
    Work.Drive.N2C.IsCertifiedAt f u g := by
  have hfun : (fun x : M => -(fun y : M => -f y) x) = f := by
    funext x
    simp
  have h' := (Work.Drive.N2C.isCertifiedAt_neg_iff (f := fun y : M => -f y) (u := -u)).mp h
  rw [hfun, neg_neg u] at h'
  exact h'

/-- **`D2` from the core and the dichotomy.** -/
theorem exists_certifiedWindow_saddle_of_coreX {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (hcore : ∀ {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
      (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
      (hsep : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η < 2 * D.ηd)
      (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
      (S : Work.Drive.N2Lead.MobiusPacket D η) (hshape : Work.Drive.N2C.MobiusShape D η S),
      CoreRows D η S)
    {f : M → ℝ} (hf : Work.Drive.Morse.IsMorseDistinct f) {p : M}
    (D : Work.Drive.N2.WindowDatum f p) (hsad : D.s₁ D.j ≠ D.s₂ D.j)
    (hmorse : Work.Drive.Morse.MorseLemma2) :
    ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η : ℝ, 0 < η → η ≤ η₁ →
      ∃ W : M → EuclideanSpace ℝ (Fin 3),
        Work.Drive.N2.GoodDrawingOn f (Set.Ioo (f p - 2 * η) (f p + 2 * η)) W ∧
        Work.Drive.N2C.IsCertifiedAt f (f p - 3 * η / 2) W ∧
        Work.Drive.N2C.IsCertifiedAt f (f p + 3 * η / 2) W := by
  obtain ⟨ηc, hηc, hcoreF⟩ :=
    saddleCoreOneCompShapeX hcore hf D hsad hmorse
  obtain ⟨ηc', hηc', hcoreN⟩ :=
    saddleCoreOneCompShapeX hcore (Work.Drive.N2C.IsMorseDistinct.neg hf)
      (Work.Drive.N2C.WindowDatum.neg D) (x_neg_saddle_sign D hsad) hmorse
  obtain ⟨η₂, hη₂, hdich'⟩ := Work.Drive.N2C.saddlePinDichotomy hf D hsad hmorse
  refine ⟨min (min ηc ηc') η₂, lt_min (lt_min hηc hηc') hη₂, fun η hη0 hηle => ?_⟩
  have h1c : η ≤ ηc :=
    le_trans hηle (le_trans (min_le_left (min ηc ηc') η₂) (min_le_left ηc ηc'))
  have h1c' : η ≤ ηc' :=
    le_trans hηle (le_trans (min_le_left (min ηc ηc') η₂) (min_le_right ηc ηc'))
  have h2 : η ≤ η₂ := le_trans hηle (min_le_right (min ηc ηc') η₂)
  rcases hdich' η hη0 h2 with hone | hone'
  · exact hcoreF η hη0 h1c hone
  · have hguard : Work.Drive.N2Lead.OnOneComponent (f := fun x : M => -f x)
        (-(f p) - 3 * η / 2)
        (Work.Drive.N2Lead.saddlePin (Work.Drive.N2C.WindowDatum.neg D)
          (-(f p) - 3 * η / 2) (99 / 50)) := by
      have hv : -(f p) - 3 * η / 2 = -(f p + 3 * η / 2) := by ring
      rw [hv, Work.Drive.N2Lead.saddlePin_neg]
      exact (x_onOneComponent_neg (f := f) (v := f p + 3 * η / 2)).mpr hone'
    obtain ⟨W', hW'⟩ := hcoreN η hη0 h1c' hguard
    refine ⟨W', ?_, ?_, ?_⟩
    · have hband : {t : ℝ | -t ∈ Set.Ioo (-(f p) - 2 * η) (-(f p) + 2 * η)}
          = Set.Ioo (f p - 2 * η) (f p + 2 * η) := by
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_Ioo]
        constructor <;> intro h <;> constructor <;> linarith
      have := x_goodDrawingOn_of_neg (f := f)
        (A := Set.Ioo (-(f p) - 2 * η) (-(f p) + 2 * η)) hW'.1
      rwa [hband] at this
    · have := x_isCertifiedAt_of_neg (f := f) (u := f p - 3 * η / 2) (by
        convert hW'.2.2 using 2 <;> ring)
      exact this
    · have := x_isCertifiedAt_of_neg (f := f) (u := f p + 3 * η / 2) (by
        convert hW'.2.1 using 2 <;> ring)
      exact this

/-- **The certified saddle window from the core.** -/
theorem certifiedWindowSaddle_of_coreX {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (hcore : ∀ {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
      (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
      (hsep : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η < 2 * D.ηd)
      (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
      (S : Work.Drive.N2Lead.MobiusPacket D η) (hshape : Work.Drive.N2C.MobiusShape D η S),
      CoreRows D η S)
    {f : M → ℝ} (hf : Work.Drive.Morse.IsMorseDistinct f) {p : M}
    (D : Work.Drive.N2.WindowDatum f p) (hsad : D.s₁ D.j ≠ D.s₂ D.j)
    (hmorse : Work.Drive.Morse.MorseLemma2) :
    ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η : ℝ, 0 < η → η ≤ η₁ →
      ∃ W : M → EuclideanSpace ℝ (Fin 3),
        Work.Drive.N2.GoodDrawingOn f (Set.Ioo (f p - 2 * η) (f p + 2 * η)) W ∧
        Work.Drive.N2C.IsCertifiedAt f (f p - 3 * η / 2) W ∧
        Work.Drive.N2C.IsCertifiedAt f (f p + 3 * η / 2) W :=
  exists_certifiedWindow_saddle_of_coreX hcore hf D hsad hmorse

end

end Work.Drive.N2.MfrX
