import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.saddleScaled
import Submission.Work.Drive.N2.saddleCollarFoot
import Submission.Work.Drive.N2.saddleModelPsi
import Submission.Work.Drive.N2.saddleWindow_legality
import Submission.Work.Drive.N2.saddlePack
import Submission.Work.Drive.N2.saddleCollarRow
import Submission.Work.Drive.N2.saddleJourneyAvoidsBalls
import Submission.Work.Drive.N2.mem_saddleRegionBall_of_frontier

namespace Work.Drive.N2

open scoped Manifold Topology
open Set

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- The frontier row of the saddle window (scaled form). -/
theorem wrs_frontierRow {f : M → ℝ} {p : M} (D : WindowDatum f p)
    {φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))} {Zs Z : M → ℂ} {lam0 : ℝ}
    (hlam0pos : 0 < lam0) (hlam0 : lam0 = D.ρ D.j / 8)
    (hsrc : φ'.source = (D.φ D.j).source)
    (hball : ∀ r : ℝ, modelBall φ' r = modelBall (D.φ D.j) r)
    (hZs : ∀ y : M, Zs y = ((φ' y 0 : ℝ) : ℂ) + ((φ' y 1 : ℝ) : ℂ) * Complex.I)
    (hZrel : ∀ y : M, Zs y = (lam0 : ℂ) * Z y)
    (hZsm : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z (D.φ D.j).source)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + lam0 ^ 2 * ((Z y) ^ 2).re)
    {η c₀ : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hc₀' : c₀ < 2)
    {x : M}
    (hx : x ∈ frontier (saddleRegion (modelBall (D.φ D.j) (D.ρ D.j)) Z c₀))
    (hxval : f x ∈ Set.Ioo (f p - lam0 ^ 2 * η) (f p + lam0 ^ 2 * η)) :
    x ∈ modelBall (D.φ D.j) (D.ρ D.j) := by
  have hρ : 0 < D.ρ D.j := D.hρ D.j
  have hlam0sq : 0 < lam0 ^ 2 := pow_pos hlam0pos 2
  have hxcl : x ∈ closure (saddleRegion (modelBall (D.φ D.j) (D.ρ D.j)) Z c₀) :=
    frontier_subset_closure hx
  have hxclU : x ∈ closure (modelBall (D.φ D.j) (D.ρ D.j)) :=
    closure_mono (fun y hy => hy.1) hxcl
  have hxsrc : x ∈ (D.φ D.j).source :=
    swl_closure_modelBall_subset_source (D := D) (i := D.j) (r := D.ρ D.j) le_rfl hxclU
  have hZc : ContinuousAt Z x :=
    (hZsm.contMDiffAt ((D.φ D.j).open_source.mem_nhds hxsrc)).continuousAt
  have hsqc : ContinuousAt (fun y : M => (Z y) ^ 2) x := hZc.pow 2
  have himc : ContinuousAt (fun y : M => ((Z y) ^ 2).im) x :=
    Complex.continuous_im.continuousAt.comp hsqc
  have hrec : ContinuousAt (fun y : M => ((Z y) ^ 2).re) x :=
    Complex.continuous_re.continuousAt.comp hsqc
  have himle : ((Z x) ^ 2).im ≤ c₀ :=
    le_of_mem_closure_of_continuousAt (s := saddleRegion (modelBall (D.φ D.j) (D.ρ D.j)) Z c₀)
      (u := fun y : M => ((Z y) ^ 2).im) (x := x) (a := c₀) hxcl himc
      (fun y hy => le_of_lt (abs_lt.mp hy.2).2)
  have himge : -c₀ ≤ ((Z x) ^ 2).im := by
    have h := le_of_mem_closure_of_continuousAt
      (s := saddleRegion (modelBall (D.φ D.j) (D.ρ D.j)) Z c₀)
      (u := fun y : M => -((Z y) ^ 2).im) (x := x) (a := c₀) hxcl himc.neg
      (fun y hy => by have h' := (abs_lt.mp hy.2).1; linarith)
    linarith
  have himabs : |((Z x) ^ 2).im| ≤ c₀ := abs_le.mpr ⟨himge, himle⟩
  have hfcont : ContinuousAt f x := swl_continuousAt_of_mem_source (D := D) hxsrc
  have hlaw : ContinuousAt (fun y : M => (f y - f p) - lam0 ^ 2 * ((Z y) ^ 2).re) x :=
    (hfcont.sub continuousAt_const).sub (hrec.const_mul (lam0 ^ 2))
  have hlaw0 : (f x - f p) - lam0 ^ 2 * ((Z x) ^ 2).re ≤ 0 :=
    le_of_mem_closure_of_continuousAt (s := modelBall (D.φ D.j) (D.ρ D.j))
      (u := fun y : M => (f y - f p) - lam0 ^ 2 * ((Z y) ^ 2).re) (x := x) (a := 0) hxclU hlaw
      (fun y hy => by have := hlev y hy.1; linarith)
  have hlaw0' : 0 ≤ (f x - f p) - lam0 ^ 2 * ((Z x) ^ 2).re := by
    have h := le_of_mem_closure_of_continuousAt (s := modelBall (D.φ D.j) (D.ρ D.j))
      (u := fun y : M => -((f y - f p) - lam0 ^ 2 * ((Z y) ^ 2).re)) (x := x) (a := 0) hxclU
      hlaw.neg
      (fun y hy => by have := hlev y hy.1; linarith)
    linarith
  have hfx : f x = f p + lam0 ^ 2 * ((Z x) ^ 2).re := by linarith
  have h3 : |f x - f p| < lam0 ^ 2 * η := by
    rw [abs_lt]
    exact ⟨by linarith [hxval.1], by linarith [hxval.2]⟩
  have h4 : ((Z x) ^ 2).re = (f x - f p) / lam0 ^ 2 := by
    rw [eq_div_iff (ne_of_gt hlam0sq)]
    linarith [hfx]
  have hre_lt : |((Z x) ^ 2).re| < η := by
    rw [h4, abs_div, abs_of_pos hlam0sq, div_lt_iff₀ hlam0sq]
    linarith [h3]
  have hre_sq : (((Z x) ^ 2).re) ^ 2 < η ^ 2 := by
    rw [sq_lt_sq, abs_of_pos hη]
    exact hre_lt
  have hc₀nn : 0 ≤ c₀ := le_trans (abs_nonneg _) himabs
  have him_sq_le : (((Z x) ^ 2).im) ^ 2 ≤ c₀ ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hc₀nn]
    exact himabs
  have hnorm4 : ‖Z x‖ ^ 4 = ((Z x) ^ 2).re ^ 2 + ((Z x) ^ 2).im ^ 2 := norm_four_eq (Z x)
  have hlt4 : ‖Z x‖ ^ 4 < (8 : ℝ) ^ 4 := by
    rw [hnorm4]
    have hbig : η ^ 2 + c₀ ^ 2 < (8 : ℝ) ^ 4 := by nlinarith [hη, hη', hc₀']
    linarith
  have hnorm_lt : ‖Z x‖ < 8 := lt_of_pow_lt_pow_left₀ 4 (by norm_num) hlt4
  have hZs_norm : ‖Zs x‖ = lam0 * ‖Z x‖ := by
    rw [hZrel x, norm_mul, show ‖(((lam0 : ℝ)) : ℂ)‖ = |lam0| from by simp, abs_of_pos hlam0pos]
  have hφnorm : ‖D.φ D.j x‖ = lam0 * ‖Z x‖ := by
    have h1 : ‖Zs x‖ = ‖φ' x‖ := norm_Z_eq_of_hZ φ' Zs hZs x
    have h2 : ‖φ' x‖ = ‖D.φ D.j x‖ :=
      swl_norm_chart_eq (D := D) hsrc hball (by rw [hsrc]; exact hxsrc)
    linarith
  have hφ_lt : ‖D.φ D.j x‖ < D.ρ D.j := by
    rw [hφnorm, hlam0]
    nlinarith [hnorm_lt, hρ]
  exact ⟨hxsrc, hφ_lt⟩

/-- The collar landing lies in the ODE region. -/
theorem wrs_collarC {f : M → ℝ} {p : M} (D : WindowDatum f p)
    {φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))} {Zs Z : M → ℂ} {lam0 : ℝ}
    (hlam0pos : 0 < lam0) (hlam0 : lam0 = D.ρ D.j / 8)
    (hsrc : φ'.source = (D.φ D.j).source)
    (hball : ∀ r : ℝ, modelBall φ' r = modelBall (D.φ D.j) r)
    (hZs : ∀ y : M, Zs y = ((φ' y 0 : ℝ) : ℂ) + ((φ' y 1 : ℝ) : ℂ) * Complex.I)
    (hZrel : ∀ y : M, Zs y = (lam0 : ℂ) * Z y)
    {η δ : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hδ : 0 < δ) (hδ' : δ < 1 / 10)
    {x z : M} (hcol : Z x ∈ saddleCollar η δ) (hzsrc : z ∈ φ'.source)
    (hZz : Z z = saddlePsi η δ (Z x)) :
    z ∈ D.C D.j := by
  have hρ : 0 < D.ρ D.j := D.hρ D.j
  have hsat : |((Z x) ^ 2).re| ≤ η ∧ 2 - 2 * δ ≤ |((Z x) ^ 2).im| ∧ |((Z x) ^ 2).im| ≤ 2 := by
    simpa only [saddleCollar, Set.mem_ofPred_eq] using hcol
  obtain ⟨hcolre, hcolimlo, hcolimhi⟩ := hsat
  have hpsi := (saddlePsi_collar hη hη' hδ hδ' hcolre hcolimlo hcolimhi).1
  have hsq : (Z z) ^ 2 = (-η : ℂ) + (((Z x) ^ 2).im : ℂ) * Complex.I := by
    rw [hZz]; exact hpsi
  have hrez : ((Z z) ^ 2).re = -η := by
    rw [hsq]; simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have himz : ((Z z) ^ 2).im = ((Z x) ^ 2).im := by
    rw [hsq]; simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have him_le : (((Z z) ^ 2).im) ^ 2 ≤ 4 := by
    rw [himz]
    have h := abs_le.mp hcolimhi
    nlinarith [h.1, h.2, sq_abs ((Z x) ^ 2).im]
  have hre_le : (((Z z) ^ 2).re) ^ 2 ≤ η ^ 2 := by
    rw [hrez]; nlinarith
  have hnorm4 : ‖Z z‖ ^ 4 = ((Z z) ^ 2).re ^ 2 + ((Z z) ^ 2).im ^ 2 := norm_four_eq (Z z)
  have hlt4 : ‖Z z‖ ^ 4 < (8 : ℝ) ^ 4 := by
    rw [hnorm4]
    have hbig : η ^ 2 + 4 < (8 : ℝ) ^ 4 := by nlinarith [hη, hη']
    linarith
  have hnorm_lt : ‖Z z‖ < 8 := lt_of_pow_lt_pow_left₀ 4 (by norm_num) hlt4
  have hZs_norm : ‖Zs z‖ = lam0 * ‖Z z‖ := by
    rw [hZrel z, norm_mul, show ‖(((lam0 : ℝ)) : ℂ)‖ = |lam0| from by simp, abs_of_pos hlam0pos]
  have hφnorm : ‖φ' z‖ = lam0 * ‖Z z‖ := by
    rw [← norm_Z_eq_of_hZ φ' Zs hZs z, hZs_norm]
  have hφ_lt : ‖φ' z‖ < D.ρ D.j := by
    rw [hφnorm, hlam0]
    nlinarith [hnorm_lt, hρ]
  have hmem : z ∈ modelBall φ' (D.ρ D.j) := ⟨hzsrc, hφ_lt⟩
  rw [hball (D.ρ D.j)] at hmem
  exact D.hCop D.j hmem

/-- **The three structural rows of the saddle window.**  For a saddle window datum (`s₁ = -s₂`),
with the canonical scaled coordinate `Z`, `lam0 = D.ρ D.j / 8`, anchor level `a = f p - lam0² η`, the
model ball `U := modelBall (D.φ D.j) (D.ρ D.j)` and the model region
`D := saddleRegion U Z c₀ = {y ∈ U | |Im (Z y)²| < c₀}`:

* **frontier row**: a point of the frontier of `D` whose value lies in the window lies in `U`;
* **landing row**: an off-`D` point of the window is transported to the anchor level by `D.Φ`;
* **collar row, with the ODE region**: a point of the chart source whose coordinate lies in the
  collar is transported inside the ODE region `D.C D.j`, lands on the anchor level and its coordinate
  is the model value. -/
theorem windowRows_of_saddleDatum {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hsgn : D.s₁ D.j = - D.s₂ D.j)
    {η δ c₀ : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hδ : 0 < δ) (hδ' : δ < 1 / 10)
    (hc₀ : 2 - 2 * δ < c₀) (hc₀' : c₀ < 2)
    (hsep : (D.ρ D.j / 8) ^ 2 * η < 2 * D.ηd) :
    ∃ (Z : M → ℂ) (lam0 a : ℝ),
      0 < lam0 ∧ lam0 = D.ρ D.j / 8 ∧ a = f p - lam0 ^ 2 * η ∧
      (∀ y ∈ (D.φ D.j).source, f y = f p + lam0 ^ 2 * ((Z y) ^ 2).re) ∧
      (∀ x : M,
        x ∈ frontier (Work.Drive.N2.saddleRegion
            (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀) →
        f x ∈ Set.Ioo a (a + 2 * lam0 ^ 2 * η) →
        x ∈ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) ∧
      (∀ y : M,
        y ∉ Work.Drive.N2.saddleRegion
            (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀ →
        f y ∈ Set.Ioo a (a + 2 * lam0 ^ 2 * η) →
        f (Work.Drive.N2.footMap D.Φ f a y) = a) ∧
      (∀ x : M, x ∈ (D.φ D.j).source → Z x ∈ Work.Drive.N2.saddleCollar η δ →
        f x ∈ Set.Ioo a (a + 2 * lam0 ^ 2 * η) →
        Work.Drive.N2.footMap D.Φ f a x ∈ D.C D.j ∧
        f (Work.Drive.N2.footMap D.Φ f a x) = a ∧
        Z (Work.Drive.N2.footMap D.Φ f a x) = Work.Drive.N2.saddlePsi η δ (Z x)) := by
  obtain ⟨φ', Zs, Z, lam0, hlam0pos, hlam0, hsrc, hball, hZs, hZrel, hZsm, hZinj, hZimm,
    hlevZ, hlevZs, hODE, him⟩ := Work.Drive.N2.saddlePack D hsgn
  refine ⟨Z, lam0, f p - lam0 ^ 2 * η, hlam0pos, hlam0, rfl, hlevZ, ?_, ?_, ?_⟩
  · intro x hx hxval
    refine Work.Drive.N2.wrs_frontierRow (D := D) hlam0pos hlam0 hsrc hball hZs hZrel hZsm hlevZ
      hη hη' (by linarith) hx ?_
    have h : f p - lam0 ^ 2 * η + 2 * lam0 ^ 2 * η = f p + lam0 ^ 2 * η := by ring
    simpa [h] using hxval
  · intro y hyD hyval
    have hbox : y ∉ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j) ∨
        c₀ * lam0 ^ 2 ≤ |((Zs y) ^ 2).im| := by
      by_cases hyU : y ∈ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)
      · refine Or.inr ?_
        have hlt : c₀ ≤ |((Z y) ^ 2).im| := by
          by_contra hcon
          exact hyD ⟨hyU, lt_of_not_ge hcon⟩
        have him' : ((Zs y) ^ 2).im = lam0 ^ 2 * ((Z y) ^ 2).im :=
          Work.Drive.N2.swl_im_sq_eq_div (Zs := Zs) (Z := Z) (lam0 := lam0) (hZrel y)
        rw [him', abs_mul, abs_of_nonneg (sq_nonneg lam0)]
        calc c₀ * lam0 ^ 2 ≤ |((Z y) ^ 2).im| * lam0 ^ 2 :=
              mul_le_mul_of_nonneg_right hlt (sq_nonneg lam0)
          _ = lam0 ^ 2 * |((Z y) ^ 2).im| := by ring
      · exact Or.inl hyU
    have hband : f y ∈ Set.Ioo (f p - lam0 ^ 2 * η) (f p + lam0 ^ 2 * η) := by
      have h : f p - lam0 ^ 2 * η + 2 * lam0 ^ 2 * η = f p + lam0 ^ 2 * η := by ring
      simpa [h] using hyval
    have h := Work.Drive.N2.landingOfBox_self (D := D) hsgn φ' Zs lam0 hlam0 hsrc hball hZs
      hlevZs hODE him hη hη' (by linarith) hsep hbox hband
    simpa [Work.Drive.N2.footMap] using h
  · intro x hxsrc hcol hxval
    have hlev' : ∀ y ∈ φ'.source, f y = f p + ((Zs y) ^ 2).re :=
      fun y hy => hlevZs y (by rw [hsrc] at hy; exact hy)
    have h := Work.Drive.N2.saddleCollarRow (D := D) hsgn φ' Zs Z lam0 hlam0 hsrc hball hZs
      hZrel hlev' hODE him hη hη' hδ hδ' hsep (by rw [hsrc]; exact hxsrc) hcol
    refine ⟨?_, ?_, ?_⟩
    · exact Work.Drive.N2.wrs_collarC (D := D) hlam0pos hlam0 hsrc hball hZs hZrel hη hη' hδ hδ'
        hcol h.1 h.2.2
    · simpa [Work.Drive.N2.footMap] using h.2.1
    · simpa [Work.Drive.N2.footMap] using h.2.2

end Work.Drive.N2
