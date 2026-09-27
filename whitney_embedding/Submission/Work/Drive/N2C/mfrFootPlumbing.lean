import Mathlib
import Submission.Work.Drive.N2C.mobiusShape
import Submission.Work.Drive.N2Lead.mobiusUpperDefs
import Submission.Work.Drive.N2Lead.mobiusUpperStarRowKit
import Submission.Work.Drive.N2Lead.mobiusGoodDrawing
import Submission.Work.Drive.N2C.wideCollar
import Submission.Work.Drive.N2Lead.mobiusUpperFootKit
import Submission.Work.Drive.N2Lead.mobiusUpperFarRate

/-!
# Plumbing for the twisted Möbius upper picture

The eventual foot form of the twisted picture (`mobiusTwisted_eventually_foot`): away from the model
region the drawing agrees near a level point with the transported park picture
`pushY Dp εp 1 (twistX ε (-1) (S.C₀ (foot ·)))`.  This is the shared input of the pin/park/far
pieces of the upper certificate of the Möbius saddle window.
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology in
open Set Filter in
/-- **The foot form of the twisted picture, eventually.**  At a point `y` of the level
`f p + 3η/2` which is *outside* the model region, the twisted picture agrees near `y` with the
transported park picture `pushY Dp εp 1 (twistX ε (-1) (S.C₀ (foot ·)))`: on the complement of the
closure of the model region this is `mobiusTwisted_foot`, and on the frontier it is the seam
identity of the saddle engine (`hseam` + `hApin` + the idempotence of `saddlePsi` on the collar). -/
theorem mobiusTwisted_eventually_foot {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (S : Work.Drive.N2Lead.MobiusPacket D η) {ε εp Dp : ℝ} {y : M}
    (hy : f y = f p + 3 * η / 2)
    (hyD : y ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j))
      S.Z (39 / 20)) :
    (fun z : M => Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp z)
      =ᶠ[𝓝 y] (fun z : M => Work.Drive.N2Lead.pushY Dp εp 1
        (Work.Drive.N2Lead.twistX ε (-1)
          (S.C₀ (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) z)))) := by
  set Dreg : Set M := Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j))
    S.Z (39 / 20) with hDdef
  have hηs : 0 < Work.Drive.N2.packetEta D η := Work.Drive.N2.packetEta_pos D hη
  have hηs_lt10 : Work.Drive.N2.packetEta D η < 1 / 10 := by
    have h := Work.Drive.N2.packetEtaB_eq D η
    linarith
  have hηs_le_ηb : Work.Drive.N2.packetEta D η ≤ Work.Drive.N2.packetEtaB D η := by
    have h := Work.Drive.N2.packetEtaB_eq D η
    linarith
  have hηb_lt10 : Work.Drive.N2.packetEtaB D η < 1 / 10 := by linarith
  have hyb : f y ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) := by
    rw [hy]; constructor <;> linarith
  have hDopen : IsOpen Dreg := by
    rw [hDdef]
    exact Work.Drive.N2.isOpen_saddleRegion
      (Work.Drive.N2Lead.isOpen_modelBall_mobius _ _) S.hZsm
  obtain ⟨hfootsm, -, -⟩ :=
    Work.Drive.N2.footMap_rows_noLaw (f := f) (Φ := D.Φ) (hf := hf) (hΦsm := D.hΦsm)
      (hΦ0 := D.hΦ0) (hΦcomp := D.hΦcomp) (a := f p - 3 * η / 2)
  rcases (em (y ∈ frontier Dreg)) with hyfr | hyfr
  · -- the frontier case: the seam identity
    have hfootV : ∀ᶠ z in 𝓝 y, Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) z
        ∈ interior ((Work.Drive.N2Lead.pinTheta D S.Z (99 / 50)) ⁻¹' {1}) :=
      ((hfootsm y).continuousAt).preimage_mem_nhds
        (isOpen_interior.mem_nhds (S.hfootFrint y hyfr hyb))
    have hband' : ∀ᶠ z in 𝓝 y, f z ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) :=
      hf.continuous.continuousAt (isOpen_Ioo.mem_nhds hyb)
    filter_upwards [hband', hfootV, S.hlandFr y hyfr hyb, S.hcolFr y hyfr hyb]
      with z hzb hθz hlandz hcolz
    have hθz1 : Work.Drive.N2Lead.pinTheta D S.Z (99 / 50)
        (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) z) = 1 := by
      have h1 : Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) z
          ∈ (Work.Drive.N2Lead.pinTheta D S.Z (99 / 50)) ⁻¹' {1} := interior_subset hθz
      simpa using h1
    have hpt : S.A (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) z)
        = Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi (Work.Drive.N2.packetEta D η) (1 / 20)
            (S.Z (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) z))) :=
      S.hApin _ hlandz hθz1
    have hseamz : S.Z (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) z)
        = Work.Drive.N2.saddlePsi (Work.Drive.N2.packetEta D η) (1 / 20) (S.Z z) :=
      S.hseam z hzb (hcolz hzb)
    have hidem : Work.Drive.N2.saddlePsi (Work.Drive.N2.packetEta D η) (1 / 20)
        (Work.Drive.N2.saddlePsi (Work.Drive.N2.packetEta D η) (1 / 20) (S.Z z))
        = Work.Drive.N2.saddlePsi (Work.Drive.N2.packetEta D η) (1 / 20) (S.Z z) :=
      saddlePsi_idempotent_of_mem_collarWide hηs hηs_lt10 (by norm_num)
        (by norm_num) hηb_lt10 hηs_le_ηb (hcolz hzb)
    have hdraw : Work.Drive.N2Lead.mobiusWindowDrawing D η S z
        = S.A (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) z) := by
      rw [Work.Drive.N2Lead.mobiusWindowDrawing]
      by_cases hz : z ∈ Dreg
      · rw [if_pos hz, hpt, hseamz, hidem]
      · rw [if_neg hz]
    rw [Work.Drive.N2Lead.mobiusTwisted, hdraw, S.hAeq,
      show Work.Drive.N2Lead.twistY S.a' (-1) (Work.Drive.N2Lead.twistY S.a' 1 (S.C₀ _))
        = S.C₀ _ from by rw [Work.Drive.N2Lead.twistY_comp, neg_add_cancel,
          Work.Drive.N2Lead.twistY_zero]]
  · -- outside the closure: the definition already gives the foot form
    have hycl : y ∉ closure Dreg := by
      intro hcl
      exact hyfr ⟨hcl, by rw [hDopen.interior_eq]; exact hyD⟩
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hycl] with z hzcl
    have hzD : z ∉ Dreg := fun hzD => hzcl (subset_closure hzD)
    rw [Work.Drive.N2Lead.mobiusTwisted, Work.Drive.N2Lead.mobiusWindowDrawing,
      if_neg hzD, S.hAeq,
      show Work.Drive.N2Lead.twistY S.a' (-1) (Work.Drive.N2Lead.twistY S.a' 1 (S.C₀ _))
        = S.C₀ _ from by rw [Work.Drive.N2Lead.twistY_comp, neg_add_cancel,
          Work.Drive.N2Lead.twistY_zero]]



open scoped Manifold ContDiff Topology in
open Set Filter in
/-- **The twisted picture is injective on the level**: it is the composition of the good drawing
(`mobiusGoodDrawing`) with the three injective ambient maps `twistY S.a' (-1)`, `twistX ε (-1)` and
`pushY Dp εp 1`. -/
theorem mfr_injOn_level {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (S : Work.Drive.N2Lead.MobiusPacket D η) {ε εp Dp : ℝ} (hεp : 0 < εp) (hDp : 0 ≤ Dp)
    {x y : M} (hx : f x = f p + 3 * η / 2) (hy : f y = f p + 3 * η / 2)
    (h : Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp x
      = Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y) : x = y := by
  have hband : ∀ z : M, f z = f p + 3 * η / 2 →
      f z ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) := by
    intro z hz; rw [hz]; constructor <;> linarith
  have hW := Work.Drive.N2Lead.mobiusGoodDrawing D hη hsmall hf S
  have h1 : Work.Drive.N2Lead.twistX ε (-1) (Work.Drive.N2Lead.twistY S.a' (-1)
        (Work.Drive.N2Lead.mobiusWindowDrawing D η S x))
      = Work.Drive.N2Lead.twistX ε (-1) (Work.Drive.N2Lead.twistY S.a' (-1)
        (Work.Drive.N2Lead.mobiusWindowDrawing D η S y)) :=
    Work.Drive.N2Lead.pushY_injective Dp εp 1 hεp hDp h
  have h2 : Work.Drive.N2Lead.twistY S.a' (-1) (Work.Drive.N2Lead.mobiusWindowDrawing D η S x)
      = Work.Drive.N2Lead.twistY S.a' (-1) (Work.Drive.N2Lead.mobiusWindowDrawing D η S y) :=
    Work.Drive.N2Lead.twistX_injective ε (-1) h1
  have h3 : Work.Drive.N2Lead.mobiusWindowDrawing D η S x
      = Work.Drive.N2Lead.mobiusWindowDrawing D η S y :=
    Work.Drive.N2Lead.twistY_injective S.a' (-1) h2
  exact hW.2.2 x y (hband x hx) (hband y hy) (by rw [hx, hy]) h3

/-- **The twisted polar picture is `2π`-periodic** in its angular parameter. -/
theorem mfr_polarPic_add_two_pi {r : ℝ → ℝ} (hrper : ∀ φ : ℝ, r (φ + 2 * Real.pi) = r φ)
    (ε εp Dp φ : ℝ) :
    Work.Drive.N2Lead.pushY Dp εp 1 (Work.Drive.N2Lead.twistX ε (-1)
        (Work.Drive.N2.cE3 (r (φ + 2 * Real.pi) * Complex.exp (((φ + 2 * Real.pi : ℝ) : ℂ) * Complex.I))))
      = Work.Drive.N2Lead.pushY Dp εp 1 (Work.Drive.N2Lead.twistX ε (-1)
        (Work.Drive.N2.cE3 (r φ * Complex.exp ((φ : ℂ) * Complex.I)))) := by
  have hexp : Complex.exp (((φ + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((φ : ℂ) * Complex.I) := by
    have : (((φ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I
        = (φ : ℂ) * Complex.I + (2 : ℂ) * (Real.pi : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  rw [hrper φ, hexp]


end Work.Drive.N2C
