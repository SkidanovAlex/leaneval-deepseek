import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.packetDefs
import Submission.Work.Drive.N2.saddleScaled
import Submission.Work.Drive.N2.footMapDefs
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2Lead.saddlePinFunction
import Submission.Work.Drive.N2Lead.twistDefs
import Submission.Work.Drive.N2Lead.twistToolkit
import Submission.Work.Drive.N2Lead.saddlePacket
import Submission.Work.Drive.N2Lead.saddleArcs

/-!
# The Möbius packet of the saddle window: data structure and the assembled drawing

This file isolates the *data* of the Möbius (opposite-sign arc lift) saddle window — the scaled Morse
coordinate, the level curves of the anchor level, the radial profile and its angle function, the
*star-shaped* polar picture `C₀` of the anchor level together with the *park* picture `A` obtained
from it by the slab twist `twistY a' 1` (the Möbius move: the twist acts as the half turn
`(x, y, z) ↦ (-x, y, -z)` on the lower slab, which reverses the orientation of the lower arc), and the
seven flow rows — and the drawing `mobiusWindowDrawing` it induces.

The companion files prove (a) that the drawing is a good drawing on the band, (b) that it is certified
at the anchor level and (c) that it is certified at the upper level, which together give
`Work.Drive.N2Lead.saddleWindowCertifiedMobius`.

Everything here is stated in the constants of the core: half height `ηs = packetEta D η`, band half
width `ηb = packetEtaB D η`, model multiplier `lam = (ρ j / 8)²`, collar width `δ = 1/20`, model strip
half width `c₀ = 39/20`, pin width `m = 99/50` and radius bound `R = 3`.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter
open Classical

noncomputable section

/-! ## The twist toolkit lemmas the packet needs -/

/-- The rotations `rot02`, `rot12` and the two slab twists preserve the norm. -/
lemma norm_sq_rot02 (t : ℝ) (v : E3) : ‖rot02 t v‖ ^ 2 = ‖v‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, rot02]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.vecEmpty, Real.norm_eq_abs, sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]

lemma norm_sq_rot12 (t : ℝ) (v : E3) : ‖rot12 t v‖ ^ 2 = ‖v‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, rot12]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.vecEmpty, Real.norm_eq_abs, sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]

lemma norm_sq_twistY (a s : ℝ) (v : E3) : ‖twistY a s v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [twistY_eq, norm_sq_rot02]

lemma norm_sq_twistX (ε s : ℝ) (v : E3) : ‖twistX ε s v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [twistX_eq, norm_sq_rot12]

lemma norm_sq_pushY (D ε s : ℝ) (v : E3) : ‖pushY D ε s v‖ ^ 2
    = (v 0) ^ 2 + (pushProf D ε s (v 1)) ^ 2 + (v 2) ^ 2 := by
  rw [pushY_eq_prof]
  simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.vecEmpty, Real.norm_eq_abs, sq_abs]

lemma norm_twistY (a s : ℝ) (v : E3) : ‖twistY a s v‖ = ‖v‖ := by
  have h := norm_sq_twistY a s v
  have h1 : ‖twistY a s v‖ = Real.sqrt (‖twistY a s v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
  rw [h1, h, Real.sqrt_sq (norm_nonneg _)]

lemma norm_twistX (ε s : ℝ) (v : E3) : ‖twistX ε s v‖ = ‖v‖ := by
  have h := norm_sq_twistX ε s v
  have h1 : ‖twistX ε s v‖ = Real.sqrt (‖twistX ε s v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
  rw [h1, h, Real.sqrt_sq (norm_nonneg _)]

/-- `twistY a s` is a bijection of `ℝ³` (its inverse is `twistY a (-s)`). -/
lemma twistY_injective (a s : ℝ) : Function.Injective (twistY a s) := by
  intro u v huv
  have h := congrArg (twistY a (-s)) huv
  simpa [twistY_comp, twistY_zero] using h

lemma twistX_injective (ε s : ℝ) : Function.Injective (twistX ε s) := by
  intro u v huv
  have h := congrArg (twistX ε (-s)) huv
  simpa [twistX_comp, twistX_zero] using h

lemma contDiff_twistY_fixed (a s : ℝ) : ContDiff ℝ tpTop (twistY a s) :=
  (contDiff_twistY a).comp (contDiff_const.prodMk contDiff_id)

lemma contDiff_twistX_fixed (ε s : ℝ) : ContDiff ℝ tpTop (twistX ε s) :=
  (contDiff_twistX ε).comp (contDiff_const.prodMk contDiff_id)

/-- If `g ∘ f = id` and both are differentiable, then `fderiv f` is injective. -/
lemma injective_fderiv_of_leftInverse {f g : E3 → E3} (h : ∀ v : E3, g (f v) = v)
    (hg : ∀ w, DifferentiableAt ℝ g w) (hf : ∀ w, DifferentiableAt ℝ f w) (w : E3) :
    Function.Injective (fderiv ℝ f w) := by
  have hc : (fderiv ℝ g (f w)).comp (fderiv ℝ f w) = ContinuousLinearMap.id ℝ E3 := by
    have h1 : fderiv ℝ (g ∘ f) w = (fderiv ℝ g (f w)).comp (fderiv ℝ f w) :=
      fderiv_comp w (hg (f w)) (hf w)
    have h2 : fderiv ℝ (g ∘ f) w = ContinuousLinearMap.id ℝ E3 := by
      rw [show (g ∘ f) = id from funext h, fderiv_id]
    rw [← h1, h2]
  have hAB : ∀ z : E3, fderiv ℝ g (f w) (fderiv ℝ f w z) = z := by
    intro z
    have := congrArg (fun L : E3 →L[ℝ] E3 => L z) hc
    simpa using this
  intro x y hxy
  have hx := hAB x
  have hy := hAB y
  rw [hxy] at hx
  rw [hx] at hy
  exact hy

lemma injective_fderiv_twistY (a s : ℝ) (w : E3) : Function.Injective (fderiv ℝ (twistY a s) w) :=
  injective_fderiv_of_leftInverse (f := twistY a s) (g := twistY a (-s))
    (fun v => by simp [twistY_comp, twistY_zero])
    (fun _ => (contDiff_twistY_fixed a (-s)).differentiable (by simp) |>.differentiableAt)
    (fun _ => (contDiff_twistY_fixed a s).differentiable (by simp) |>.differentiableAt) w

lemma injective_fderiv_twistX (ε s : ℝ) (w : E3) : Function.Injective (fderiv ℝ (twistX ε s) w) :=
  injective_fderiv_of_leftInverse (f := twistX ε s) (g := twistX ε (-s))
    (fun v => by simp [twistX_comp, twistX_zero])
    (fun _ => (contDiff_twistX_fixed ε (-s)).differentiable (by simp) |>.differentiableAt)
    (fun _ => (contDiff_twistX_fixed ε s).differentiable (by simp) |>.differentiableAt) w

/-- `mfderiv`-form of the injectivity of the differential of `twistY` (the two `TangentSpace` types
are definitionally the Euclidean spaces involved, so the `fderiv` form is not directly applicable). -/
lemma injective_mfderiv_twistY (a s : ℝ) (y : E3) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 3) (twistY a s) y) := by
  rw [mfderiv_eq_fderiv]
  exact injective_fderiv_twistY a s y

/-- **`twistY` is the identity on the slab `y ≥ a`** (for `a > 0`) — the row that fixes the upper
arc and the parked circles. -/
lemma twistY_eq_self {a s : ℝ} (ha : 0 < a) {v : E3} (hv : a ≤ v 1) : twistY a s v = v :=
  twistY_eq_self_of_le ha hv

/-- **`twistX` is the identity on the slab `x ≤ -ε`** (for `ε > 0`). -/
lemma twistX_eq_self {ε s : ℝ} (hε : 0 < ε) {v : E3} (hv : v 0 ≤ -ε) : twistX ε s v = v :=
  twistX_eq_self_of_le hε hv

/-- The model ball of a chart is open (local copy, so that the packet does not depend on the
flow modules which also state it). -/
theorem isOpen_modelBall_mobius {M : Type*} [TopologicalSpace M]
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (r : ℝ) :
    IsOpen (Work.Drive.N2.modelBall φ r) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hcont : ContinuousAt (fun z : M => φ z) y :=
    φ.continuousOn.continuousAt (φ.open_source.mem_nhds hy.1)
  have h3 : ∀ᶠ z in 𝓝 y, ‖φ z‖ < r := (hcont.norm).eventually_lt_const hy.2
  filter_upwards [φ.open_source.mem_nhds hy.1, h3] with z hz1 hz2 using ⟨hz1, hz2⟩

/-! ## The packet data -/

/-- **The Möbius packet of the saddle window.**  Everything the D2d assembly consumes. -/
structure MobiusPacket {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) (η : ℝ) where
  /-- the scaled Morse coordinate of the datum chart -/
  Z : M → ℂ
  lam0 : ℝ
  hlam0pos : 0 < lam0
  hlam0 : lam0 = D.ρ D.j / 8
  hZsm : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z
    (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j))
  hZinj : Set.InjOn Z (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j))
  hZimm : ∀ x ∈ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j),
    Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z x)
  hlev : ∀ y ∈ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j),
    f y = f p + lam0 ^ 2 * ((Z y) ^ 2).re
  /-- the level curves of the anchor level `f p - 3η/2` -/
  n : ℕ
  L : Work.Drive.N2C.LevelCurves f (f p - 3 * η / 2) n
  /-- the marked component (the one carrying the pin) -/
  i : Fin n
  /-- the radial profile and the angle function of the packet -/
  r : ℝ → ℝ
  Θ : ℝ → ℝ
  hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r
  hrpos : ∀ φ : ℝ, 0 < r φ
  hrper : ∀ φ : ℝ, r (φ + 2 * Real.pi) = r φ
  hrR : ∀ φ : ℝ, r φ ≤ 3
  hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ
  hΘmono : StrictMono Θ
  hΘderiv : ∀ t : ℝ, deriv Θ t ≠ 0
  hΘper : ∀ t : ℝ, Θ (t + 1) = Θ t + 2 * Real.pi
  /-- the twist radius of the Möbius move -/
  a' : ℝ
  ha'pos : 0 < a'
  ha' : a' ≤ 1
  /-- **the star-shaped polar picture of the anchor level** -/
  C₀ : M → EuclideanSpace ℝ (Fin 3)
  hC₀sm : ∀ x : M, ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) C₀ x
  hC₀val : ∀ t : ℝ, C₀ (L.γ i t) =
    Work.Drive.N2.cE3 (r (Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I))
  hC₀far : ∀ (j : Fin n), j ≠ i → ∀ t : ℝ, C₀ (L.γ j t) = farCurve n j t
  hC₀inj : ∀ x y : M, f x = f p - 3 * η / 2 → f y = f p - 3 * η / 2 → C₀ x = C₀ y → x = y
  hC₀imm : ∀ x : M, f x = f p - 3 * η / 2 → ∀ v : TangentSpace (𝓡 2) x,
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) C₀ x v = 0 → v = 0
  /-- **the park picture of the anchor level** (the twist of `C₀`) -/
  A : M → EuclideanSpace ℝ (Fin 3)
  hAeq : ∀ x : M, A x = twistY a' 1 (C₀ x)
  hApin : ∀ x : M, f x = f p - 3 * η / 2 →
    Work.Drive.N2Lead.pinTheta D Z (99 / 50) x = 1 →
    A x = Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi (Work.Drive.N2.packetEta D η) (1 / 20) (Z x))
  hAoff : ∀ x : M, f x = f p - 3 * η / 2 →
    Work.Drive.N2Lead.pinTheta D Z (99 / 50) x < 1 →
    (A x) 2 ≠ 0 ∨ 39 / 20 + 2 * Work.Drive.N2.packetEta D η < ‖A x‖ ^ 2
  /-- **the seven flow rows** (`Work.Drive.N2Lead.saddleFlowRowsWide` at the core constants) -/
  hfootval : ∀ y : M,
    y ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z (39 / 20) →
    f y ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) →
    f (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y) = f p - 3 * η / 2
  hfrU : ∀ x ∈ frontier
      (Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z (39 / 20)),
    f x ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) →
    x ∈ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)
  hseam : ∀ y : M, f y ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) →
    Z y ∈ Work.Drive.N2.saddleCollar (Work.Drive.N2.packetEtaB D η) (1 / 20) →
    Z (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y)
      = Work.Drive.N2.saddlePsi (Work.Drive.N2.packetEta D η) (1 / 20) (Z y)
  hcolFr : ∀ x ∈ frontier
      (Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z (39 / 20)),
    f x ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) →
    ∀ᶠ y in 𝓝 x, f y ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) →
      Z y ∈ Work.Drive.N2.saddleCollar (Work.Drive.N2.packetEtaB D η) (1 / 20)
  hbig : ∀ x : M,
    x ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z (39 / 20) →
    f x ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) →
    Work.Drive.N2Lead.pinTheta D Z (99 / 50) (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) x) = 1 →
    39 / 20 ≤ |((Z (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) x)) ^ 2).im|
  hfootFrint : ∀ x ∈ frontier
      (Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z (39 / 20)),
    f x ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) →
    Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) x ∈
      interior ((Work.Drive.N2Lead.pinTheta D Z (99 / 50)) ⁻¹' {1})
  hlandFr : ∀ x ∈ frontier
      (Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z (39 / 20)),
    f x ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) →
    ∀ᶠ y in 𝓝 x, f (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y) = f p - 3 * η / 2
  /-- the anchor level is regular -/
  hreg : ∀ x : M, f x = f p - 3 * η / 2 → ¬ Work.Drive.Morse.IsCritical f x

/-- **The drawing of the Möbius saddle window**: the model piece `cE3 ∘ Ψ ∘ Z` inside the model
strip `|Im (Z ·)²| < 39/20`, and the transported park picture outside. -/
def mobiusWindowDrawing {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) (η : ℝ)
    (S : MobiusPacket D η) : M → EuclideanSpace ℝ (Fin 3) :=
  fun x => if x ∈ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z
      (39 / 20)
    then Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi (Work.Drive.N2.packetEta D η) (1 / 20) (S.Z x))
    else S.A (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) x)

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-- The norm of the park picture is the norm of the polar picture: `twistY` preserves the norm. -/
lemma MobiusPacket.norm_A_eq {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p} {η : ℝ}
    (S : MobiusPacket D η) (x : M) : ‖S.A x‖ = ‖S.C₀ x‖ := by
  rw [S.hAeq x, norm_twistY]

/-- The park picture is smooth. -/
lemma MobiusPacket.A_sm {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p} {η : ℝ}
    (S : MobiusPacket D η) (x : M) :
    ContMDiffAt (𝓡 2) (𝓡 3) tpTop S.A x := by
  rw [show S.A = fun y => twistY S.a' 1 (S.C₀ y) from funext S.hAeq]
  exact ((contDiff_twistY_fixed S.a' 1).contMDiff.contMDiffAt).comp x (S.hC₀sm x)

/-- The park picture is injective on the anchor level. -/
lemma MobiusPacket.A_inj {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p} {η : ℝ}
    (S : MobiusPacket D η) {x y : M} (hx : f x = f p - 3 * η / 2) (hy : f y = f p - 3 * η / 2)
    (h : S.A x = S.A y) : x = y := by
  rw [S.hAeq x, S.hAeq y] at h
  exact S.hC₀inj x y hx hy (twistY_injective S.a' 1 h)

/-- **Chain rule for a named function which is the composite of `twistY a 1` with a map `c`.**
Stated with the function as a variable so that the codomain of the `mfderiv` is determined without
elaborating a lambda in the `mfderiv` position. -/
lemma chain_rule_twistY {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (a : ℝ) {F c : M → EuclideanSpace ℝ (Fin 3)}
    (hF : F = fun y => twistY a 1 (c y)) (x : M)
    (hc : MDifferentiableAt (𝓡 2) (𝓡 3) c x) :
    mfderiv (𝓡 2) (𝓡 3) F x
      = (mfderiv (𝓡 3) (𝓡 3) (twistY a 1) (c x)).comp (mfderiv (𝓡 2) (𝓡 3) c x) := by
  have hsm : ContDiff ℝ tpTop (twistY a 1) := contDiff_twistY_fixed a 1
  have htw : MDifferentiableAt (𝓡 3) (𝓡 3) (twistY a 1) (c x) :=
    (hsm.contMDiff.contMDiffAt (x := c x)).mdifferentiableAt (by simp)
  rw [hF]
  exact mfderiv_comp x htw hc

/-- The park picture is `ker df`-immersive on the anchor level. -/
lemma MobiusPacket.A_imm {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p} {η : ℝ}
    (S : MobiusPacket D η) {x : M} (hx : f x = f p - 3 * η / 2)
    {v : TangentSpace (𝓡 2) x}
    (hv : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0) (hA : mfderiv (𝓡 2) (𝓡 3) S.A x v = 0) : v = 0 := by
  have hmd0 : MDifferentiableAt (𝓡 2) (𝓡 3) S.C₀ x :=
    (S.hC₀sm x).mdifferentiableAt (by simp)
  have hclm := chain_rule_twistY (M := M) S.a' (F := S.A) (c := S.C₀) (funext S.hAeq) x hmd0
  have hval : mfderiv (𝓡 2) (𝓡 3) S.A x v
      = (mfderiv (𝓡 3) (𝓡 3) (twistY S.a' 1) (S.C₀ x)) (mfderiv (𝓡 2) (𝓡 3) S.C₀ x v) := by
    rw [hclm]
    rfl
  have h0 : (mfderiv (𝓡 3) (𝓡 3) (twistY S.a' 1) (S.C₀ x))
      (mfderiv (𝓡 2) (𝓡 3) S.C₀ x v) = 0 := by
    rw [← hval]; exact hA
  have hz : mfderiv (𝓡 2) (𝓡 3) S.C₀ x v = 0 := by
    apply injective_mfderiv_twistY S.a' 1 (S.C₀ x)
    rw [map_zero]
    exact h0
  exact S.hC₀imm x hx v hv hz

end

end Work.Drive.N2Lead
