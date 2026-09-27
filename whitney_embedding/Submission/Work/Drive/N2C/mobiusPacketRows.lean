import Mathlib
import Submission.Work.Drive.N2Lead.mobiusPacketDefs
import Submission.Work.Drive.N2Lead.saddlePacket
import Submission.Work.Drive.N2Lead.saddlePacketRows
import Submission.Work.Drive.N2Lead.saddlePacketRowsOfArcs
import Submission.Work.Drive.N2Lead.saddleMarkedCurve
import Submission.Work.Drive.N2Lead.polarArc_eq_sqrt
import Submission.Work.Drive.N2Lead.mobiusPinTwist

/-!
# The packet rows of the Möbius saddle window (H7 lane)

The Möbius analogue of `Work.Drive.N2Lead.saddlePacketRowsSplit`: the anchor picture `C₀` is the
polar picture `t ↦ cE3 (r (Θ t) * exp (i Θ t))` on the marked component and the parked circles on the
other components, and the *park picture* `A` is its slab twist `twistY a' 1 ∘ C₀` (the Möbius move:
on the lower slab the twist is the half turn `(x, y, z) ↦ (-x, y, -z)`, which turns the conjugate
polar arc into the lower model arc `cE3 (-arcZ ηs w)`).

The two rows of the twist are the point of the construction:

* the **pin row** `pinTheta D Z m x = 1 → A x = cE3 (saddlePsi ηs δ (Z x))`: a pinned point `x` of
  the anchor level has `Z x = ±arcZ ηs w` with `w = Im ((Z x)²)`, so it is one of the two arc points
  `αU w`, `αL w`; on the upper arc `C₀ x = cE3 (arcZ ηs w) = cE3 (Z x)` has `y = Im (arcZ ηs w) ≥ a'`
  (hypothesis `haArc`), so the twist fixes it, while on the lower arc `C₀ x = cE3 (star (arcZ ηs w))`
  has `y = -Im (arcZ ηs w) ≤ -a'`, so the twist is the half turn, which sends it to
  `cE3 (-arcZ ηs w) = cE3 (Z x)`; and `saddlePsi` is the identity on the anchor level.
* the **off-pin row** is *norm based*: the twist preserves the norm, so on the marked component the
  radial-profile row `hoff` (`r (Θ t)² > c₀ + 2ηs` off the pinned arcs) transfers, and on a parked
  circle `‖A x‖ = ‖farCurve n j t‖ ≥ 19`.
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set Filter
open Classical

set_option maxHeartbeats 8000000

noncomputable section

/-- **The Möbius lower-arc value of the polar profile.**  With `θL = 3π/2 + (1/2) arctan (w/ηs)`
(the *Möbius* lower-arc angle of `saddleAngleFunctionMobius`), the polar point of the radial profile
`r = √(ηs / -cos (2φ))` at `θL` is the **conjugate** of the upper arc point `arcZ ηs w`:

`√(ηs / -cos (2 θL)) * exp (i θL) = star (arcZ ηs w)`.

The proof is that of `Work.Drive.N2Lead.polarArc_eq_sqrt` transported to the angle `2π - φU`:
`θL = 2π - φU` and `-cos (2 θL) = -cos (2 φU)`, so the two left-hand sides are conjugate. -/
theorem polarArcMobiusDn {ηs : ℝ} (hηs : 0 < ηs) (w : ℝ) :
    Real.sqrt (ηs / -Real.cos (2 * (3 * Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs))))
        * Complex.exp (((3 * Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs) : ℝ) : ℂ) * Complex.I)
      = star (Work.Drive.N2Lead.arcZ ηs w) := by
  set φU : ℝ := Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs) with hφU
  have hU := (Work.Drive.N2Lead.polarArc_eq_sqrt hηs w).1
  have hU' : Real.sqrt (ηs / -Real.cos (2 * φU)) * Complex.exp ((φU : ℂ) * Complex.I)
      = Work.Drive.N2Lead.arcZ ηs w := by
    rw [hφU]
    change Real.sqrt (ηs / -Real.cos (2 * (Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs))))
        * Complex.exp (((Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs) : ℝ) : ℂ) * Complex.I)
      = Complex.I * ((ηs : ℂ) - (w : ℂ) * Complex.I).sqrt
    exact hU
  have hθ : 3 * Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs) = 2 * Real.pi - φU := by
    rw [hφU]; ring
  have hcos : -Real.cos (2 * (3 * Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs)))
      = -Real.cos (2 * φU) := by
    rw [hθ]
    have h2 : 2 * (2 * Real.pi - φU) = -(2 * φU) + (2 : ℤ) * (2 * Real.pi) := by
      push_cast; ring
    rw [h2, Real.cos_add_int_mul_two_pi, Real.cos_neg]
  have hstar_exp : star (Complex.exp ((φU : ℂ) * Complex.I))
      = Complex.exp (-((φU : ℂ) * Complex.I)) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hexp : Complex.exp (((2 * Real.pi - φU : ℝ) : ℂ) * Complex.I)
      = star (Complex.exp ((φU : ℂ) * Complex.I)) := by
    have h1 : (((2 * Real.pi - φU : ℝ)) : ℂ) * Complex.I
        = (2 * (Real.pi : ℂ) * Complex.I) - (φU : ℂ) * Complex.I := by
      push_cast; ring
    rw [h1, Complex.exp_sub, Complex.exp_two_pi_mul_I, one_div, hstar_exp, ← Complex.exp_neg]
  rw [hcos, hθ, hexp]
  have hfix : star (((Real.sqrt (ηs / -Real.cos (2 * φU))) : ℝ) : ℂ)
      = (((Real.sqrt (ηs / -Real.cos (2 * φU))) : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  have hcombine : star (((Real.sqrt (ηs / -Real.cos (2 * φU))) : ℝ) : ℂ)
        * star (Complex.exp ((φU : ℂ) * Complex.I))
      = star ((((Real.sqrt (ηs / -Real.cos (2 * φU))) : ℝ) : ℂ)
          * Complex.exp ((φU : ℂ) * Complex.I)) := (star_mul' _ _).symm
  rw [← hfix, hcombine, hU']


/-- **The twisted packet rows of the Möbius saddle window.**  The analogue of
`Work.Drive.N2Lead.saddlePacketRowsSplit` in which the park picture is the slab twist
`A = twistY a' 1 ∘ C₀` of the polar picture `C₀`.  The two complex arc rows `hArcU`, `hArcL`
(`C₀ (L.γ i (τU w)) = cE3 (arcZ ηs w) = cE3 (Z (αU w))` and
`C₀ (L.γ i (τL w)) = cE3 (star (arcZ ηs w))`) are the inputs through which the pin row is proved, and
the twist acts on them by `Work.Drive.N2Lead.mobiusPinTwist`. -/
theorem mobiusPacketRowsTwist {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f) {p : M}
    (D : Work.Drive.N2.WindowDatum f p) {Z : M → ℂ}
    {lam0 ηs δ c₀ m R a' : ℝ} {n : ℕ}
    (L : Work.Drive.N2C.LevelCurves f (f p - lam0 ^ 2 * ηs) n) (i : Fin n)
    {r Θ τU τL : ℝ → ℝ} {αU αL : ℝ → M}
    (hreg : ∀ x : M, f x = f p - lam0 ^ 2 * ηs → ¬ Work.Drive.Morse.IsCritical f x)
    (hlam0pos : 0 < lam0)
    (hZsm : ∀ x ∈ (D.φ D.j).source,
      ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z x)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + lam0 ^ 2 * ((Z y) ^ 2).re)
    (hpinZ : ∀ x : M, x ∈ Work.Drive.N2Lead.saddlePin D (f p - lam0 ^ 2 * ηs) m ↔
      x ∈ (D.φ D.j).source ∧ ‖Z x‖ < 8 ∧ f x = f p - lam0 ^ 2 * ηs ∧ |((Z x) ^ 2).im| ≤ m)
    (hZinj : ∀ w ∈ Set.Icc (-m) m, ∀ x ∈ (D.φ D.j).source, Z x = Z (αU w) → x = αU w)
    (hZinjL : ∀ w ∈ Set.Icc (-m) m, ∀ x ∈ (D.φ D.j).source, Z x = Z (αL w) → x = αL w)
    (hαsrcU : ∀ w ∈ Set.Icc (-m) m, αU w ∈ (D.φ D.j).source)
    (hαsrcL : ∀ w ∈ Set.Icc (-m) m, αL w ∈ (D.φ D.j).source)
    (hZU : ∀ w ∈ Set.Icc (-m) m, Z (αU w) = Work.Drive.N2Lead.arcZ ηs w)
    (hZL : ∀ w ∈ Set.Icc (-m) m, Z (αL w) = -Work.Drive.N2Lead.arcZ ηs w)
    (hηs : 0 < ηs) (hηs1 : ηs < 1 / 10) (hδ : 0 < δ) (hδ1 : δ < 1 / 10)
    (hm : 1 < m) (hm2 : m < 2) (hR : 2 ≤ R) (hR19 : R < 19)
    (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r) (hrpos : ∀ φ : ℝ, 0 < r φ)
    (hrper : ∀ φ : ℝ, r (φ + 2 * Real.pi) = r φ) (hrR : ∀ φ : ℝ, r φ ≤ R)
    (hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ) (hΘmono : StrictMono Θ)
    (hΘderiv : ∀ t : ℝ, deriv Θ t ≠ 0) (hΘper : ∀ t : ℝ, Θ (t + 1) = Θ t + 2 * Real.pi)
    (hArcU : ∀ w ∈ Set.Icc (-m) m,
      r (Θ (τU w)) * Complex.exp (((Θ (τU w) : ℝ) : ℂ) * Complex.I)
        = Work.Drive.N2Lead.arcZ ηs w)
    (hArcL : ∀ w ∈ Set.Icc (-m) m,
      r (Θ (τL w)) * Complex.exp (((Θ (τL w) : ℝ) : ℂ) * Complex.I)
        = star (Work.Drive.N2Lead.arcZ ηs w))
    (hτU : ∀ w ∈ Set.Icc (-m) m, L.γ i (τU w) = αU w)
    (hτL : ∀ w ∈ Set.Icc (-m) m, L.γ i (τL w) = αL w)
    (ha'pos : 0 < a') (ha'small : 2 * a' ≤ Real.sqrt ηs)
    (hoff : ∀ t : ℝ, (∀ (w : ℝ) (k : ℤ), w ∈ Set.Icc (-m) m → t ≠ τU w + k) →
      (∀ (w : ℝ) (k : ℤ), w ∈ Set.Icc (-m) m → t ≠ τL w + k) → c₀ + 2 * ηs < r (Θ t) ^ 2)
    (hnum : c₀ + 2 * ηs < 19 ^ 2) :
    ∃ (C₀ A : M → EuclideanSpace ℝ (Fin 3)),
      (∀ x : M, ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) C₀ x) ∧
      (∀ t : ℝ, C₀ (L.γ i t)
        = Work.Drive.N2.cE3 (r (Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I))) ∧
      (∀ (j : Fin n), j ≠ i → ∀ t : ℝ, C₀ (L.γ j t) = Work.Drive.N2Lead.farCurve n j t) ∧
      (∀ x y : M, f x = f p - lam0 ^ 2 * ηs → f y = f p - lam0 ^ 2 * ηs → C₀ x = C₀ y →
        x = y) ∧
      (∀ x : M, f x = f p - lam0 ^ 2 * ηs → ∀ v : TangentSpace (𝓡 2) x,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) C₀ x v = 0 → v = 0) ∧
      (∀ x : M, A x = Work.Drive.N2Lead.twistY a' 1 (C₀ x)) ∧
      (∀ x : M, f x = f p - lam0 ^ 2 * ηs → Work.Drive.N2Lead.pinTheta D Z m x = 1 →
        A x = Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi ηs δ (Z x))) ∧
      (∀ x : M, f x = f p - lam0 ^ 2 * ηs → Work.Drive.N2Lead.pinTheta D Z m x < 1 →
        (A x) 2 ≠ 0 ∨ c₀ + 2 * ηs < ‖A x‖ ^ 2) := by
  classical
  -- ## the marked polar curve and the packet family of curves
  let C : ℝ → EuclideanSpace ℝ (Fin 3) :=
    fun t => Work.Drive.N2.cE3 (r (Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I))
  obtain ⟨hCsm, hCper, hCinj, hCder, hCnorm⟩ :=
    Work.Drive.N2Lead.saddleMarkedCurve (r := r) (Θ := Θ) (R := R) hr hrpos hrper hrR
      hΘ hΘmono hΘderiv hΘper
  let c : Fin n → ℝ → EuclideanSpace ℝ (Fin 3) :=
    fun j => if j = i then C else Work.Drive.N2Lead.farCurve n j
  have hci : c i = C := by
    show (if i = i then C else Work.Drive.N2Lead.farCurve n i) = C
    rw [if_pos rfl]
  have hcj : ∀ j : Fin n, j ≠ i → c j = Work.Drive.N2Lead.farCurve n j := by
    intro j hj
    show (if j = i then C else Work.Drive.N2Lead.farCurve n j) = Work.Drive.N2Lead.farCurve n j
    rw [if_neg hj]
  have hcsm : ∀ j : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (c j) := by
    intro j
    by_cases hj : j = i
    · have hji : c j = C := by
        show (if j = i then C else Work.Drive.N2Lead.farCurve n j) = C
        rw [if_pos hj]
      rw [hji]; exact hCsm
    · rw [hcj j hj]; exact Work.Drive.N2Lead.farCurve_contDiff n j
  have hcper : ∀ (j : Fin n) (t : ℝ), c j (t + 1) = c j t := by
    intro j t
    by_cases hj : j = i
    · have hji : c j = C := by
        show (if j = i then C else Work.Drive.N2Lead.farCurve n j) = C
        rw [if_pos hj]
      rw [hji]; exact congrArg Work.Drive.N2.cE3 (hCper t)
    · rw [hcj j hj]; exact Work.Drive.N2Lead.farCurve_period n j t
  have hcinj : ∀ (j k : Fin n) (s t : ℝ), c j s = c k t → j = k ∧ ∃ m : ℤ, s = t + m := by
    intro j k s t hst
    change (if j = i then C else Work.Drive.N2Lead.farCurve n j) s
      = (if k = i then C else Work.Drive.N2Lead.farCurve n k) t at hst
    by_cases hj : j = i
    · rw [if_pos hj] at hst
      by_cases hk : k = i
      · rw [if_pos hk] at hst
        exact ⟨hj.trans hk.symm, hCinj s t (Work.Drive.N2.cE3_injective hst)⟩
      · rw [if_neg hk] at hst
        exact absurd hst (Work.Drive.N2Lead.marked_far_ne hCnorm hR19 s t)
    · rw [if_neg hj] at hst
      by_cases hk : k = i
      · rw [if_pos hk] at hst
        exact absurd hst.symm (Work.Drive.N2Lead.marked_far_ne hCnorm hR19 t s)
      · rw [if_neg hk] at hst
        exact Work.Drive.N2Lead.farCurve_inj hst
  have hcder : ∀ (j : Fin n) (t : ℝ), deriv (c j) t ≠ 0 := by
    intro j t
    by_cases hj : j = i
    · have hji : c j = C := by
        show (if j = i then C else Work.Drive.N2Lead.farCurve n j) = C
        rw [if_pos hj]
      rw [hji]; exact hCder t
    · rw [hcj j hj]; exact Work.Drive.N2Lead.deriv_farCurve_ne_zero n j t
  -- ## the polar picture of the anchor level
  obtain ⟨C₀, hC₀sm, hC₀curve, hC₀inj, hC₀imm⟩ :=
    Work.Drive.N2Lead.packetPicture (f := f) (a := f p - lam0 ^ 2 * ηs) (n := n) (c := c)
      L hf hreg hcsm hcper hcinj hcder
  let A : M → EuclideanSpace ℝ (Fin 3) := fun x => Work.Drive.N2Lead.twistY a' 1 (C₀ x)
  -- ## the smoothness of the park picture
  have hAsm : ∀ x : M, ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A x := by
    intro x
    rw [show A = fun y => Work.Drive.N2Lead.twistY a' 1 (C₀ y) from rfl]
    exact ((Work.Drive.N2Lead.contDiff_twistY_fixed a' 1).contMDiff.contMDiffAt).comp x
      (hC₀sm x)
  refine ⟨C₀, A, fun x => hC₀sm x, ?_, ?_, hC₀inj, hC₀imm, fun x => rfl, ?_, ?_⟩
  · -- the marked component is drawn by the polar curve
    intro t
    have h := hC₀curve i t
    rw [hci] at h
    exact h
  · -- the other components are drawn by the parked circles
    intro j hj t
    have h := hC₀curve j t
    rw [hcj j hj] at h
    exact h
  · -- ## the pin row
    intro x hxf hθ1
    have hxsrc : x ∈ (D.φ D.j).source := by
      by_contra hx
      rw [Work.Drive.N2Lead.pinTheta_apply_of_notMem D (Z := Z) (m := m) hx] at hθ1
      norm_num at hθ1
    obtain ⟨himle, _hnorm4⟩ := (Work.Drive.N2Lead.pinTheta_eq_one_iff D hm2 hxsrc).mp hθ1
    have hre : ((Z x) ^ 2).re = -ηs := by
      have h := hlev x hxsrc
      rw [hxf] at h
      have h2 : lam0 ^ 2 * ((Z x) ^ 2).re = lam0 ^ 2 * (-ηs) := by linarith
      exact mul_left_cancel₀ (by positivity : (lam0 : ℝ) ^ 2 ≠ 0) h2
    have hPsi : Work.Drive.N2.saddlePsi ηs δ (Z x) = Z x :=
      Work.Drive.N2.saddlePsi_eq_self_of_re_sq_neg_eta hηs hδ (by linarith) hre
    have hwIcc : ((Z x) ^ 2).im ∈ Set.Icc (-m) m := abs_le.mp himle
    have hsq : (Z x) ^ 2 = (Work.Drive.N2Lead.arcZ ηs (((Z x) ^ 2).im)) ^ 2 := by
      refine Complex.ext ?_ ?_
      · rw [hre, Work.Drive.N2Lead.arcZ_sq_re]
      · rw [Work.Drive.N2Lead.arcZ_sq_im]
    rw [hPsi]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with harc | harc
    · -- the upper arc
      have hZx : Z x = Work.Drive.N2Lead.arcZ ηs (((Z x) ^ 2).im) := harc
      have hxy : x = αU (((Z x) ^ 2).im) := by
        refine hZinj _ hwIcc x hxsrc ?_
        rw [hZU _ hwIcc]
        exact hZx
      have hC₀x : C₀ x = Work.Drive.N2.cE3 (Work.Drive.N2Lead.arcZ ηs (((Z x) ^ 2).im)) := by
        calc C₀ x = C₀ (αU (((Z x) ^ 2).im)) := congrArg C₀ hxy
          _ = C₀ (L.γ i (τU (((Z x) ^ 2).im))) := by rw [hτU _ hwIcc]
          _ = c i (τU (((Z x) ^ 2).im)) := hC₀curve i _
          _ = C (τU (((Z x) ^ 2).im)) := by rw [hci]
          _ = Work.Drive.N2.cE3 (r (Θ (τU (((Z x) ^ 2).im)))
                * Complex.exp (((Θ (τU (((Z x) ^ 2).im)) : ℝ) : ℂ) * Complex.I)) := rfl
          _ = Work.Drive.N2.cE3 (Work.Drive.N2Lead.arcZ ηs (((Z x) ^ 2).im)) := by
                rw [hArcU _ hwIcc]
      show A x = Work.Drive.N2.cE3 (Z x)
      rw [show A x = Work.Drive.N2Lead.twistY a' 1 (C₀ x) from rfl, hC₀x]
      exact ((Work.Drive.N2Lead.mobiusPinTwist hηs ha'pos ha'small (((Z x) ^ 2).im)).2).trans
        ((congrArg Work.Drive.N2.cE3 hZx).symm)
    · -- the lower arc
      have hZx : Z x = -Work.Drive.N2Lead.arcZ ηs (((Z x) ^ 2).im) := harc
      have hxy : x = αL (((Z x) ^ 2).im) := by
        refine hZinjL _ hwIcc x hxsrc ?_
        rw [hZL _ hwIcc]
        exact hZx
      have hC₀x : C₀ x
          = Work.Drive.N2.cE3 (star (Work.Drive.N2Lead.arcZ ηs (((Z x) ^ 2).im))) := by
        calc C₀ x = C₀ (αL (((Z x) ^ 2).im)) := congrArg C₀ hxy
          _ = C₀ (L.γ i (τL (((Z x) ^ 2).im))) := by rw [hτL _ hwIcc]
          _ = c i (τL (((Z x) ^ 2).im)) := hC₀curve i _
          _ = C (τL (((Z x) ^ 2).im)) := by rw [hci]
          _ = Work.Drive.N2.cE3 (r (Θ (τL (((Z x) ^ 2).im)))
                * Complex.exp (((Θ (τL (((Z x) ^ 2).im)) : ℝ) : ℂ) * Complex.I)) := rfl
          _ = Work.Drive.N2.cE3 (star (Work.Drive.N2Lead.arcZ ηs (((Z x) ^ 2).im))) := by
                rw [hArcL _ hwIcc]
      show A x = Work.Drive.N2.cE3 (Z x)
      rw [show A x = Work.Drive.N2Lead.twistY a' 1 (C₀ x) from rfl, hC₀x]
      exact ((Work.Drive.N2Lead.mobiusPinTwist hηs ha'pos ha'small (((Z x) ^ 2).im)).1).trans
        ((congrArg Work.Drive.N2.cE3 hZx).symm)
  · -- ## the off-pin row
    intro x hxf hθlt
    obtain ⟨j, t, hxt⟩ := L.cover x hxf
    have hC₀xt : C₀ x = c j t := by
      rw [hxt]
      exact hC₀curve j t
    have hAx : A x = Work.Drive.N2Lead.twistY a' 1 (c j t) := by
      rw [show A x = Work.Drive.N2Lead.twistY a' 1 (C₀ x) from rfl, hC₀xt]
    by_cases hji : j = i
    · -- the marked component: the radial-profile row
      have hCt : c j t = C t := by
        rw [hji]
        exact congrFun hci t
      have hnotU : ∀ (w : ℝ) (k : ℤ), w ∈ Set.Icc (-m) m → t ≠ τU w + k := by
        intro w k hw ht
        have hxarc : x = αU w := by
          rw [hxt, ht, hji, Work.Drive.N2Lead.levelCurves_gamma_add_int L i k (τU w)]
          exact hτU w hw
        have h1 : Work.Drive.N2Lead.pinTheta D Z m x = 1 := by
          rw [hxarc]
          exact Work.Drive.N2Lead.pinTheta_arcU D hηs hηs1 hm hm2 (hαsrcU w hw) (hZU w hw) hw
        exact absurd h1 (ne_of_lt hθlt)
      have hnotL : ∀ (w : ℝ) (k : ℤ), w ∈ Set.Icc (-m) m → t ≠ τL w + k := by
        intro w k hw ht
        have hxarc : x = αL w := by
          rw [hxt, ht, hji, Work.Drive.N2Lead.levelCurves_gamma_add_int L i k (τL w)]
          exact hτL w hw
        have h1 : Work.Drive.N2Lead.pinTheta D Z m x = 1 := by
          rw [hxarc]
          exact Work.Drive.N2Lead.pinTheta_arcD D hηs hηs1 hm hm2 (hαsrcL w hw) (hZL w hw) hw
        exact absurd h1 (ne_of_lt hθlt)
      right
      have hbr := hoff t hnotU hnotL
      have hnorm : ‖A x‖ ^ 2 = r (Θ t) ^ 2 := by
        rw [hAx, hCt]
        show ‖Work.Drive.N2Lead.twistY a' 1 (C t)‖ ^ 2 = r (Θ t) ^ 2
        rw [Work.Drive.N2Lead.norm_twistY]
        have h1 : ‖C t‖ = r (Θ t) := by
          show ‖Work.Drive.N2.cE3 (r (Θ t)
              * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I))‖ = r (Θ t)
          rw [Work.Drive.N2Lead.norm_cE3_marked, norm_mul,
            Complex.norm_exp_ofReal_mul_I, mul_one,
            Complex.norm_of_nonneg (le_of_lt (hrpos (Θ t)))]
        rw [h1]
      rw [hnorm]
      exact hbr
    · -- a parked circle: the norm of the parked circle is large
      right
      have hnorm : ‖A x‖ ^ 2 = ‖Work.Drive.N2Lead.farCurve n j t‖ ^ 2 := by
        rw [hAx, hcj j hji, Work.Drive.N2Lead.norm_twistY]
      rw [hnorm]
      have h19 := Work.Drive.N2Lead.farCurve_norm n j t
      nlinarith [h19, hnum]

end

end Work.Drive.N2C
