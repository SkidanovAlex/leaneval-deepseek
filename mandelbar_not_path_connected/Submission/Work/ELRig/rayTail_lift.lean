/-
# ELRig — the lift of the two ray tails to the repelling coordinate

`Work.ELRig.rayTail_lift` : for a root-parabolic parameter `c`, the flower of the simple parabolic
point `z₁` of `F c = (T_c)^[10]`, and the two landing statements of the root portrait, the *tails*
of the two external rays `R(α₁)`, `R(α₂)` (the ray points of level `t`, for `1 < t < t₀`) are
covered by the inverse repelling coordinate `Ψ` on a left half plane `{Re w < -R}`, and on that
half plane the two deck transformations `w ↦ w + 1`, `w ↦ w̄ + 1/2` of `Ψ` act on the ray points
by
`rayPt α₁ t ↦ rayPt α₁ (t ^ 1024)`   (the degree `1024 = 2¹⁰` of `F c`), resp.
`rayPt α₁ t ↦ rayPt α₂ (t ^ 32)`     (the degree `32 = 2⁵` of `g = (T_c)^[5]`).

This is step 1 and step 2 of **R-a2** ("ray lift and cylinder") of
`NOTES_LEAD_mandelbar_EL_F_contracts.md` §6:

1. *The tail of `R(αᵢ)` (potential `< t₀`) lies in `Ψ(H_R)`: it misses `Pa ⊂ K`, then use `cover`.*
   The flower's `cover` says that every point near `z₁` other than `z₁` itself is either in the
   attracting petal `Pa` or in `Ψ({Re w < -R})`; a ray point of level `> 1` is not in the filled
   Julia set `K c`, while `Pa ⊆ K c`, so it must be in `Ψ(H_R)`.  That the ray points of level
   `t → 1⁺` approach `z₁` is exactly the landing hypothesis `LandsN hN αᵢ z₁`.
2. *Lift it via `(Ψ|H_R)⁻¹` to a curve `γ̃ᵢ` with `γ̃ᵢ(s+1) = γ̃ᵢ(s)+1` (`Ψ_shift` + `Ψ_inj`), and
   `γ̃₂ = ι γ̃₁` where `ι w = w̄ + ½` (`Ψ_anti`, `T⁵ α₁ = α₂`).*  On the ray points this is the
   pair of identities above: `Ψ (w+1) = F (Ψ w)` and `Ψ (w̄ + 1/2) = g (Ψ w)` are the flower's
   defining functional equations, so all that is needed is the action of `F` and `g` on the ray
   points, i.e. the Böttcher functional equation on the circle.  The exponents `1024` and `32`
   are the degrees of `F c` and `g`, and the angle identities `1024 α₁ ≡ α₁ (mod 1)` (indeed
   `1024 α₁ = 371 + α₁`, since `1023 = 2¹⁰ - 1`) and `-32 α₁ ≡ α₂ (mod 1)` (the angle map of the
   antiholomorphic `g` is `θ ↦ -32 θ`) are `.lean`-level arithmetic on `α₁ = 371/1023`,
   `α₂ = 404/1023`.

Note that the conclusion of the two shifted identities does not depend on *which* lift `w` of
`rayPt α₁ t` is used -- this is why the flower's injectivity `Ψ_inj` is not needed here.
-/
import Mathlib
import Submission.Work.ELRig.Inputs
import Submission.Work.ELRig.rayPt_iterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open Classical Filter Set Function
open scoped Topology ComplexConjugate

namespace Work.ELRig

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## Periodic points lie in the filled Julia set -/

/-- **A `T_c`-periodic point lies in the filled Julia set.**  If `(T_c)^[k] z = z` with `k > 0`
then the `T_c`-orbit of `z` is the finite set `z, T_c z, …, (T_c)^[k-1] z`, hence bounded. -/
theorem mem_K_of_iterate_eq_self {c z : ℂ} {k : ℕ} (hk : 0 < k)
    (h : (Tantibar c)^[k] z = z) : z ∈ Work.EL.K c := by
  simp only [Work.EL.K, Work.ParamRays.filledJulia, Work.ParamRays.BoundedOrbit,
    Work.ParamRays.orbit, Set.mem_ofPred_eq]
  refine ⟨Finset.sum (Finset.range k) (fun r => ‖(Tantibar c)^[r] z‖), fun n => ?_⟩
  have hper : ∀ q : ℕ, ((Tantibar c)^[k])^[q] z = z := by
    intro q
    induction q with
    | zero => simp
    | succ q ih => rw [Function.iterate_succ_apply', ih, h]
  have hidx : n = n % k + k * (n / k) := by
    have h := Nat.div_add_mod n k
    omega
  have hsplit : (Tantibar c)^[n] z = (Tantibar c)^[n % k] z := by
    conv_lhs => rw [hidx]
    rw [Function.iterate_add_apply, Function.iterate_mul, hper]
  rw [hsplit]
  exact Finset.single_le_sum (f := fun r => ‖(Tantibar c)^[r] z‖) (fun i _ => norm_nonneg _)
    (Finset.mem_range.mpr (Nat.mod_lt n hk))

/-! ## The action of `T_c` on the circle points `rayPoint` -/

/-- **`star` of a circle point.**  Complex conjugation sends the circle point of angle `θ` to the
circle point of angle `-θ`: in the Böttcher coordinate the dynamics of the antiholomorphic
`T_c` is `w ↦ w̄²`, so conjugation is the reflection `θ ↦ -θ` of the external angles. -/
theorem star_rayPoint (θ t : ℝ) :
    star (Work.Top.NakaneData.rayPoint θ t) = Work.Top.NakaneData.rayPoint (-θ) t := by
  rw [Work.Top.NakaneData.rayPoint, Work.Top.NakaneData.rayPoint, Complex.ofReal_neg]
  rw [← starRingEnd_apply, map_mul, ← Complex.exp_conj, Complex.conj_ofReal]
  have h1 : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I)
      = -(2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I) := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_ofNat]
    ring
  rw [h1]
  ring

/-- **The Böttcher equation on the circle, in the form used for one step.**  The square of the
conjugate of the circle point of angle `θ` and level `t` is the circle point of angle `T θ`
and level `t²`: `T_c` acts on the exterior of the unit disc by `w ↦ w̄²`. -/
theorem star_rayPoint_sq (θ t : ℝ) :
    star (Work.Top.NakaneData.rayPoint θ t) ^ 2
      = Work.Top.NakaneData.rayPoint (Work.EL.T θ) (t ^ 2) := by
  rw [star_rayPoint θ t, Work.ELRig.rayPoint_pow]
  have hk : ((2 : ℕ) : ℝ) * (-θ) = Work.EL.T θ + (⌊-2 * θ⌋ : ℤ) := by
    rw [show Work.EL.T θ = Int.fract (-2 * θ) from rfl]
    have h := Int.fract_add_floor (-2 * θ)
    push_cast
    linarith
  rw [hk, Work.ELRig.rayPoint_add_int]

/-- The ray point depends on the angle only modulo `1` (both points are the preimages under the
Böttcher coordinate of the same circle point). -/
theorem rayPt_eq_of_rayPoint {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {θ θ' t : ℝ}
    (ht : 1 < t) (ht' : 1 < t)
    (h : Work.Top.NakaneData.rayPoint θ t = Work.Top.NakaneData.rayPoint θ' t) :
    Work.EL.rayPt hN θ t = Work.EL.rayPt hN θ' t := by
  refine hN.injOn_Phi (hN.rayPt_notMem ht) (hN.rayPt_notMem ht') ?_
  rw [hN.Phi_rayPt ht, hN.Phi_rayPt ht', h]

/-- **The ray point is invariant under a shift of the angle by an integer**, the rays being
`1`-periodic in the angle. -/
theorem rayPt_add_int {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (a : ℝ) (k : ℤ)
    {t : ℝ} (ht : 1 < t) :
    Work.EL.rayPt hN (a + k) t = Work.EL.rayPt hN a t :=
  rayPt_eq_of_rayPoint hN ht ht (Work.ELRig.rayPoint_add_int a t k)

/-! ## The dynamics of `T_c` and of its iterates on the ray points -/

/-- **One step of the dynamics.**  `T_c` sends the ray point of angle `θ` and level `t` to the
ray point of angle `T θ` and level `t²`, by the Böttcher functional equation
`φ (T_c z) = (φ z)⁻²` (as a map of the exterior of the unit disc: `w ↦ w̄²`). -/
theorem rayPt_antibar {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hB : Work.ParamRays.IsDynBottcher c φ) {θ t : ℝ} (ht : 1 < t) :
    Tantibar c (Work.EL.rayPt hN θ t) = Work.EL.rayPt hN (Work.EL.T θ) (t ^ 2) := by
  have hzK : Work.EL.rayPt hN θ t ∉ Work.EL.K c := hN.rayPt_notMem ht
  have hzesc : Work.ParamRays.Escaping c (Work.EL.rayPt hN θ t) :=
    (Work.ParamRays.escaping_iff_not_bounded c _).mpr hzK
  have hwesc : Work.ParamRays.Escaping c (Tantibar c (Work.EL.rayPt hN θ t)) := by
    simpa only [Work.ParamRays.orbit, Function.iterate_one] using hzesc.iterate 1
  have hwK : Tantibar c (Work.EL.rayPt hN θ t) ∉ Work.EL.K c :=
    (Work.ParamRays.escaping_iff_not_bounded c _).mp hwesc
  have ht2 : (1 : ℝ) < t ^ 2 := one_lt_pow₀ ht (by norm_num)
  refine hN.injOn_Phi hwK (hN.rayPt_notMem ht2) ?_
  rw [Work.EL.dynPhi_of_notMem (c := c) (φ := φ) hwK, hB.2.1 _ hzesc,
    ← Work.EL.dynPhi_of_notMem (c := c) (φ := φ) hzK, hN.Phi_rayPt ht, hN.Phi_rayPt ht2]
  exact star_rayPoint_sq θ t

/-- **The `n`-fold iterate of the dynamics.**  `(T_c)^[n]` sends the ray point of angle `θ` and
level `t` to the ray point of angle `T^[n] θ` and level `t ^ 2^n`. -/
theorem rayPt_iterate_antibar {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hB : Work.ParamRays.IsDynBottcher c φ) {θ t : ℝ} (ht : 1 < t) (n : ℕ) :
    (Tantibar c)^[n] (Work.EL.rayPt hN θ t)
      = Work.EL.rayPt hN (Work.EL.T^[n] θ) (t ^ (2 ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih,
      rayPt_antibar hN hB (θ := Work.EL.T^[n] θ) (t := t ^ (2 ^ n))
        (one_lt_pow₀ ht (pow_ne_zero n (by norm_num))),
      (Function.iterate_succ_apply' Work.EL.T n θ).symm, ← pow_mul, ← pow_succ]

/-! ## The two specializations used by R-a2 -/

/-- **The degree-`1024` map `F c` on the `α₁`-ray.**  `F c = (T_c)^[10]` sends the ray point of
angle `α₁` and level `t` to the ray point of the *same* angle `α₁` and level `t ^ 1024`: the
angle map of `F c` is multiplication by `1024 = 2¹⁰`, and `1024 α₁ = 371 + α₁`, because
`α₁ = 371/1023` and `1023 = 2¹⁰ - 1`. -/
theorem rayPt_F_alpha1 {c : ℂ} (d : Work.EL.RootParabolic c) {t : ℝ} (ht : 1 < t) :
    Work.EL.F c (Work.EL.rayPt d.hN Work.EL.alpha1 t)
      = Work.EL.rayPt d.hN Work.EL.alpha1 (t ^ (1024 : ℕ)) := by
  rw [Work.ELRig.rayPt_iterate d.hN d.bottcher ht]
  obtain ⟨m, hm⟩ := T_iterate_eq_add_int Work.EL.alpha1 10
  have hnum : ((-2 : ℝ) ^ 10) * (371 / 1023) = 371 / 1023 + 371 := by norm_num
  have hkey : Work.EL.T^[10] Work.EL.alpha1 = Work.EL.alpha1 + ((m + 371 : ℤ) : ℝ) := by
    rw [hm]
    simp only [Work.EL.alpha1]
    push_cast
    linarith [hnum]
  rw [hkey]
  exact rayPt_add_int (t := t ^ (1024 : ℕ)) d.hN Work.EL.alpha1 (m + 371)
    (one_lt_pow₀ ht (by norm_num))

/-- **The antiholomorphic degree-`32` map `g = (T_c)^[5]` on the `α₁`-ray.**  `g` sends the ray
point of angle `α₁` and level `t` to the ray point of angle `α₂` and level `t ^ 32`: the angle
map of `g` is `θ ↦ -32 θ`, and `-32 α₁ = -12 + α₂`. -/
theorem rayPt_g_alpha1 {c : ℂ} (d : Work.EL.RootParabolic c) {t : ℝ} (ht : 1 < t) :
    (Tantibar c)^[5] (Work.EL.rayPt d.hN Work.EL.alpha1 t)
      = Work.EL.rayPt d.hN Work.EL.alpha2 (t ^ (32 : ℕ)) := by
  rw [Work.ELRig.rayPt_iterate_antibar d.hN d.bottcher ht 5]
  have h2 : (2 : ℕ) ^ 5 = 32 := by norm_num
  rw [h2]
  obtain ⟨m, hm⟩ := T_iterate_eq_add_int Work.EL.alpha1 5
  have hnum : ((-2 : ℝ) ^ 5) * (371 / 1023) = 404 / 1023 + (-12) := by norm_num
  have hkey : Work.EL.T^[5] Work.EL.alpha1 = Work.EL.alpha2 + ((m - 12 : ℤ) : ℝ) := by
    rw [hm]
    simp only [Work.EL.alpha1, Work.EL.alpha2]
    push_cast
    linarith [hnum]
  rw [hkey]
  exact rayPt_add_int (t := t ^ (32 : ℕ)) d.hN Work.EL.alpha2 (m - 12)
    (one_lt_pow₀ ht (by norm_num))

/-! ## The lift of the ray tails -/

theorem rayTail_lift {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (hPaK : fl.Pa ⊆ Work.EL.K c)
    (h₁ : Work.EL.LandsN d.hN Work.EL.alpha1 d.z₁)
    (h₂ : Work.EL.LandsN d.hN Work.EL.alpha2 d.z₁) :
    ∃ R t₀ : ℝ, 0 < R ∧ 1 < t₀ ∧
      (∀ θ : ℝ, (θ = Work.EL.alpha1 ∨ θ = Work.EL.alpha2) → ∀ t : ℝ, 1 < t → t < t₀ →
        ∃ w : ℂ, w.re < -R ∧ fl.Ψ w = Work.EL.rayPt d.hN θ t) ∧
      (∀ t : ℝ, 1 < t → t < t₀ → ∀ w : ℂ, w.re < -R → fl.Ψ w = Work.EL.rayPt d.hN Work.EL.alpha1 t →
        fl.Ψ (w + 1) = Work.EL.rayPt d.hN Work.EL.alpha1 (t ^ (1024 : ℕ))) ∧
      (∀ t : ℝ, 1 < t → t < t₀ → ∀ w : ℂ, w.re < -R → fl.Ψ w = Work.EL.rayPt d.hN Work.EL.alpha1 t →
        fl.Ψ (star w + 1 / 2) = Work.EL.rayPt d.hN Work.EL.alpha2 (t ^ (32 : ℕ))) := by
  obtain ⟨r, hr, hcov⟩ := fl.cover 1
  have hz1K : d.z₁ ∈ Work.EL.K c :=
    mem_K_of_iterate_eq_self (k := 5) (by norm_num) d.per_half
  -- a ray point of level `t → 1⁺` is at distance `< r` from `z₁`
  have h1B : ∀ᶠ t in nhdsWithin (1 : ℝ) (Set.Ioi 1),
      Work.EL.rayPt d.hN Work.EL.alpha1 t ∈ Metric.ball d.z₁ r :=
    h₁ (Metric.ball_mem_nhds d.z₁ hr)
  have h2B : ∀ᶠ t in nhdsWithin (1 : ℝ) (Set.Ioi 1),
      Work.EL.rayPt d.hN Work.EL.alpha2 t ∈ Metric.ball d.z₁ r :=
    h₂ (Metric.ball_mem_nhds d.z₁ hr)
  obtain ⟨t₁, ht₁, h1'⟩ := (nhdsGT_basis (1 : ℝ)).eventually_iff.mp h1B
  obtain ⟨t₂, ht₂, h2'⟩ := (nhdsGT_basis (1 : ℝ)).eventually_iff.mp h2B
  refine ⟨1, min t₁ t₂, one_pos, lt_min ht₁ ht₂, ?_, ?_, ?_⟩
  · -- the lift of the two ray tails: `cover` on the half plane `Re < -1`
    intro θ hθ t ht htlt
    have hb1 : Work.EL.rayPt d.hN Work.EL.alpha1 t ∈ Metric.ball d.z₁ r :=
      h1' ⟨ht, lt_of_lt_of_le htlt (min_le_left t₁ t₂)⟩
    have hb2 : Work.EL.rayPt d.hN Work.EL.alpha2 t ∈ Metric.ball d.z₁ r :=
      h2' ⟨ht, lt_of_lt_of_le htlt (min_le_right t₁ t₂)⟩
    have hzK : Work.EL.rayPt d.hN θ t ∉ Work.EL.K c := d.hN.rayPt_notMem ht
    have hne : Work.EL.rayPt d.hN θ t ≠ d.z₁ := by
      intro he
      exact hzK (by rw [he]; exact hz1K)
    have hpos : 0 < ‖Work.EL.rayPt d.hN θ t - d.z₁‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hlt : ‖Work.EL.rayPt d.hN θ t - d.z₁‖ < r := by
      rcases hθ with hh | hh
      · rw [hh]; simpa [Metric.mem_ball, dist_eq_norm] using hb1
      · rw [hh]; simpa [Metric.mem_ball, dist_eq_norm] using hb2
    -- the ray point is not in the attracting petal, hence in `Ψ ({Re w < -1})`
    rcases hcov (Work.EL.rayPt d.hN θ t) hpos hlt with hmem | ⟨w, hw, hΨ⟩
    · exact absurd (hPaK hmem) hzK
    · exact ⟨w, hw, hΨ⟩
  · -- the deck transformation `w ↦ w + 1` realizes `F c` on the `α₁`-ray
    intro t ht htlt w hw hΨ
    rw [fl.Ψ_shift w, hΨ, rayPt_F_alpha1 d ht]
  · -- the deck transformation `w ↦ w̄ + 1/2` realizes `g` on the `α₁`-ray
    intro t ht htlt w hw hΨ
    rw [fl.Ψ_anti w, hΨ, rayPt_g_alpha1 d ht]

end Work.ELRig
