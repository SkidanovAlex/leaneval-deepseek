import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.saddleScaled
import Submission.Work.Drive.N2.saddleCollarFoot
import Submission.Work.Drive.N2.windowRows_of_saddleDatum
import Submission.Work.Drive.N2C.saddleCollarRowWide
import Submission.Work.Drive.N2Lead.saddlePinFunction
import Submission.Work.Drive.N2Lead.landingWide_band
import Submission.Work.Drive.N2Lead.footInvariantWide
import Submission.Work.Drive.N2Lead.saddleFlowRowsAux
import Submission.Work.Drive.N2.swlLanding
import Submission.Work.Drive.N2.saddlePsi_helpers
import Submission.Work.Drive.N2.saddleModelPsi
import Submission.Work.Drive.N2.footMapDefs
import Submission.Work.Drive.N2.im_sq_foot_ge_of_mem_C
import Submission.Work.Drive.N2.footInvariant_of_mem_C

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology in
open Set Filter in
/-- The seven flow/pin rows consumed by `Work.Drive.N2Lead.saddleWindow_of_packet_band_off`
(`NOTES_LEAD_saddlePacket.md` §2 R1–R4, plus the two pin-neighbourhood rows), with the corrected
hypothesis `hc₀m : c₀ < 99/50`.  All seven conjuncts are already on disk:

* conjunct 1 (`hfootval`) is `Work.Drive.N2Lead.landingWide_band` (the `hfree` disjunction it wants,
  `y ∉ modelBall ∨ c₀ * lam0² ≤ |(Zs y)²).im|`, follows from `y ∉ saddleRegion _ Z c₀` by the
  relation `(Zs y)² = lam0² (Z y)²`: `Work.Drive.N2.swl_im_sq_eq_div`);
* conjunct 2 (`hfrU`) is exactly `Work.Drive.N2.wrs_frontierRow` at `η := ηb`;
* conjunct 3 (`hseam`) is `Work.Drive.N2C.saddleCollarRowWide`;
* conjunct 4 (`hcolFr`) is `Work.Drive.N2Lead.eventually_collar_of_frontier`;
* conjunct 5 (`hbig`) is `Work.Drive.N2Lead.footInvariantWide`;
* conjunct 6 (`hfootFrint`) is `Work.Drive.N2Lead.footFrint_of_c₀_lt` (this is the row that NEEDS
  `hc₀m`; without it the conjunct is false — `_sfrw/refute.lean.part`);
* conjunct 7 (`hlandFr`) is `Work.Drive.N2Lead.eventually_landing_of_frontier`.

The last three live in `Submission/Work/Drive/N2Lead/saddleFlowRowsAux.lean` (proved, sorry-free),
together with the shared `Work.Drive.N2Lead.frontier_invariant_eq`. -/
theorem saddleFlowRowsWide {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hsgn : D.s₁ D.j = - D.s₂ D.j)
    {Zs Z : M → ℂ} {lam0 ηs ηb δ c₀ : ℝ}
    (hlam0pos : 0 < lam0) (hlam0 : lam0 = D.ρ D.j / 8)
    (hZrel : ∀ y : M, Zs y = (lam0 : ℂ) * Z y)
    (hZs : ∀ y : M, Zs y = (D.φ D.j y 0 : ℂ) + (D.φ D.j y 1 : ℂ) * Complex.I)
    (hZsm : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z (D.φ D.j).source)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + lam0 ^ 2 * ((Z y) ^ 2).re)
    (hlevSs : ∀ y ∈ (D.φ D.j).source, f y = f p + ((Zs y) ^ 2).re)
    (hODE : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      HasDerivAt (fun σ : ℝ => D.φ D.j (D.Φ (σ, y)) 0)
        (Work.Drive.N2.chartMult lam0 (‖D.φ D.j (D.Φ (t, y))‖ ^ 2)
          * ((1 : ℝ) * D.φ D.j (D.Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => D.φ D.j (D.Φ (σ, y)) 1)
        (Work.Drive.N2.chartMult lam0 (‖D.φ D.j (D.Φ (t, y))‖ ^ 2)
          * ((-1 : ℝ) * D.φ D.j (D.Φ (t, y)) 1)) t)
    (him : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      ((Zs (D.Φ (t, y))) ^ 2).im = ((Zs y) ^ 2).im)
    (hη : 0 < ηs) (hη' : ηs < 1 / 10) (hδ : 0 < δ) (hδ' : δ < 1 / 10)
    (hηb : ηs < ηb) (hηb' : ηb < 1 / 10) (hc₀ : 2 - 2 * δ < c₀) (hc₀' : c₀ < 2)
    (hc₀m : c₀ < 99 / 50)
    (hsep : (D.ρ D.j / 8) ^ 2 * ηb < 2 * D.ηd)
    (hcollSrc : ∀ y : M, Z y ∈ Work.Drive.N2.saddleCollar ηb δ → y ∈ (D.φ D.j).source) :
    (∀ y : M, y ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀ →
        f y ∈ Set.Ioo (f p - lam0 ^ 2 * ηb) (f p + lam0 ^ 2 * ηb) →
        f (Work.Drive.N2.footMap D.Φ f (f p - lam0 ^ 2 * ηs) y) = f p - lam0 ^ 2 * ηs) ∧
      (∀ x ∈ frontier
          (Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀),
        f x ∈ Set.Ioo (f p - lam0 ^ 2 * ηb) (f p + lam0 ^ 2 * ηb) →
        x ∈ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) ∧
      (∀ y : M, f y ∈ Set.Ioo (f p - lam0 ^ 2 * ηb) (f p + lam0 ^ 2 * ηb) →
        Z y ∈ Work.Drive.N2.saddleCollar ηb δ →
        Z (Work.Drive.N2.footMap D.Φ f (f p - lam0 ^ 2 * ηs) y)
          = Work.Drive.N2.saddlePsi ηs δ (Z y)) ∧
      (∀ x ∈ frontier
          (Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀),
        f x ∈ Set.Ioo (f p - lam0 ^ 2 * ηb) (f p + lam0 ^ 2 * ηb) →
        ∀ᶠ y in 𝓝 x, f y ∈ Set.Ioo (f p - lam0 ^ 2 * ηb) (f p + lam0 ^ 2 * ηb) →
          Z y ∈ Work.Drive.N2.saddleCollar ηb δ) ∧
      (∀ x : M, x ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀ →
        f x ∈ Set.Ioo (f p - lam0 ^ 2 * ηb) (f p + lam0 ^ 2 * ηb) →
        Work.Drive.N2Lead.pinTheta D Z (99 / 50)
            (Work.Drive.N2.footMap D.Φ f (f p - lam0 ^ 2 * ηs) x) = 1 →
        c₀ ≤ |((Z (Work.Drive.N2.footMap D.Φ f (f p - lam0 ^ 2 * ηs) x)) ^ 2).im|) ∧
      (∀ x ∈ frontier
          (Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀),
        f x ∈ Set.Ioo (f p - lam0 ^ 2 * ηb) (f p + lam0 ^ 2 * ηb) →
        Work.Drive.N2.footMap D.Φ f (f p - lam0 ^ 2 * ηs) x
          ∈ interior ((Work.Drive.N2Lead.pinTheta D Z (99 / 50)) ⁻¹' {1})) ∧
      (∀ x ∈ frontier
          (Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀),
        f x ∈ Set.Ioo (f p - lam0 ^ 2 * ηb) (f p + lam0 ^ 2 * ηb) →
        ∀ᶠ y in 𝓝 x, f (Work.Drive.N2.footMap D.Φ f (f p - lam0 ^ 2 * ηs) y)
          = f p - lam0 ^ 2 * ηs) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- conjunct 1 (R1): the anchor level is reached from every band point off the region
    intro y hyD hyband
    have hlam0sqpos : 0 < lam0 ^ 2 := pow_pos hlam0pos 2
    have hbox : y ∉ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j) ∨
        c₀ * lam0 ^ 2 ≤ |((Zs y) ^ 2).im| := by
      by_cases hmb : y ∈ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)
      · right
        have hge : c₀ ≤ |((Z y) ^ 2).im| := by
          by_contra hcon
          exact hyD ⟨hmb, not_le.mp hcon⟩
        have himrel : |((Zs y) ^ 2).im| = lam0 ^ 2 * |((Z y) ^ 2).im| := by
          have h1 : (Zs y) ^ 2 = ((lam0 ^ 2 : ℝ) : ℂ) * (Z y) ^ 2 := by
            rw [hZrel y, mul_pow, ← Complex.ofReal_pow]
          rw [h1, Complex.mul_im]
          simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
          rw [abs_mul, abs_of_nonneg (sq_nonneg lam0)]
        rw [himrel]
        have := mul_le_mul_of_nonneg_left hge (sq_nonneg (lam0 : ℝ))
        nlinarith [this]
      · exact Or.inl hmb
    exact Work.Drive.N2Lead.landingWide_band D hsgn (D.φ D.j) Zs lam0 hlam0 rfl (fun r => rfl)
      hZs hlevSs him (lt_trans hη hηb) hηb' (by linarith) hsep hbox hyband
      ⟨by linarith [mul_lt_mul_of_pos_left hηb hlam0sqpos],
        by linarith [mul_lt_mul_of_pos_left hηb hlam0sqpos,
          mul_pos hlam0sqpos (show (0:ℝ) < ηs from hη)]⟩
  · -- conjunct 2 (R3): a frontier band point is in the model ball
    intro x hxfr hxband
    exact Work.Drive.N2.wrs_frontierRow (D := D) (φ' := D.φ D.j) (Zs := Zs) (Z := Z)
      hlam0pos hlam0 rfl (fun r => rfl) hZs hZrel hZsm hlev (lt_trans hη hηb) hηb' hc₀' hxfr hxband
  · -- conjunct 3 (R2): the collar row
    intro y hyband hycol
    have hrow := Work.Drive.N2C.saddleCollarRowWide (η := ηs) (δ := δ) (ηb := ηb)
      D hsgn (D.φ D.j) Zs Z lam0 hlam0 rfl (fun r => rfl) hZs hZrel hlevSs hODE him
      hη hη' hδ hδ' hηb' (le_of_lt hηb) (hcollSrc y hycol) hycol
    exact hrow.2.2
  · -- conjunct 4 (hcolFr)
    exact eventually_collar_of_frontier D hlam0pos hlam0 hZrel hZs hZsm hlev
      (lt_trans hη hηb) hηb' hδ hδ' hc₀ hc₀'
  · -- conjunct 5 (R4 / hbig): the foot invariant, from `θ (foot x) = 1`
    intro x hxreg hxband hθ
    have hfootsrc : Work.Drive.N2.footMap D.Φ f (f p - lam0 ^ 2 * ηs) x
        ∈ (D.φ D.j).source := by
      by_contra hcon
      have h0 := pinTheta_apply_of_notMem D (Z := Z) (m := 99 / 50) hcon
      rw [h0] at hθ
      exact absurd hθ (by norm_num)
    have hpin := (pinTheta_eq_one_iff D (Z := Z) (m := 99 / 50) (by norm_num) hfootsrc).mp hθ
    have hfootC : Work.Drive.N2.footMap D.Φ f (f p - lam0 ^ 2 * ηs) x ∈ D.C D.j := by
      refine D.hCop D.j ⟨hfootsrc, ?_⟩
      have hnormZ : ‖Z (Work.Drive.N2.footMap D.Φ f (f p - lam0 ^ 2 * ηs) x)‖ ≤ 2 := by
        nlinarith [hpin.2,
          norm_nonneg (Z (Work.Drive.N2.footMap D.Φ f (f p - lam0 ^ 2 * ηs) x))]
      have h1 : ‖D.φ D.j (Work.Drive.N2.footMap D.Φ f (f p - lam0 ^ 2 * ηs) x)‖
          = ‖Zs (Work.Drive.N2.footMap D.Φ f (f p - lam0 ^ 2 * ηs) x)‖ := by
        rw [hZs (Work.Drive.N2.footMap D.Φ f (f p - lam0 ^ 2 * ηs) x)]
        exact (Work.Drive.N2.norm_complexOf_plane _).symm
      have h2 : ‖Zs (Work.Drive.N2.footMap D.Φ f (f p - lam0 ^ 2 * ηs) x)‖
          = lam0 * ‖Z (Work.Drive.N2.footMap D.Φ f (f p - lam0 ^ 2 * ηs) x)‖ := by
        rw [hZrel, norm_mul]
        congr 1
        simp [abs_of_nonneg hlam0pos.le]
      have h3 : lam0 * 2 = D.ρ D.j / 4 := by rw [hlam0]; ring
      calc ‖D.φ D.j (Work.Drive.N2.footMap D.Φ f (f p - lam0 ^ 2 * ηs) x)‖
          = lam0 * ‖Z (Work.Drive.N2.footMap D.Φ f (f p - lam0 ^ 2 * ηs) x)‖ := by rw [h1, h2]
        _ ≤ lam0 * 2 := by nlinarith [hlam0pos, hnormZ]
        _ = D.ρ D.j / 4 := h3
        _ < D.ρ D.j := by linarith [D.hρ D.j]
    exact Work.Drive.N2Lead.footInvariantWide D hsgn (φ' := D.φ D.j) (Zs := Zs) (Z := Z)
      (lam0 := lam0) hlam0pos hlam0 rfl (fun r => rfl) hZs hZrel hZsm hlev him hη hη'
      (le_of_lt hηb) hηb' hδ hδ' hc₀ hc₀' hsep hxreg hxband hfootC
  · -- conjunct 6 (hfootFrint)
    exact footFrint_of_c₀_lt D hsgn hlam0pos hlam0 hZrel hZs hZsm hlev hlevSs hODE him
      hη hη' hδ hδ' hηb hηb' hc₀ hc₀' hc₀m
  · -- conjunct 7 (hlandFr)
    exact eventually_landing_of_frontier D hsgn hlam0pos hlam0 hZrel hZs hZsm hlev hlevSs
      hODE him hη hη' hδ hδ' hηb hηb' hc₀ hc₀'


end Work.Drive.N2Lead
