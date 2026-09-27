import Mathlib
import Submission.Work.Drive.PushDisc.lensRegularDefs
import Submission.Work.Drive.PushDisc.alexanderFamily

/-!
# The regular disc `Δ₀` of `L0`

This file defines the explicit base map `Δ₀` of the lead's `L0` (`exists_regularDisc`,
`Drive/PushDisc/NOTES_LEAD_L0.md`): for the two edge functions

    arcA x = f (γ₁ (sigR x)),   arcB x = f (γ₂ (sigR x))

(the two arcs of the bigon, reparametrised by `[-1,1] ∋ x ↦ (x+1)/2`), the Hadamard quotient
`archQuot` with `arch x * archQuot x = arcB x - arcA x`, and a smooth Whitney disc `D` on the
square, the map is

    regularDiscZero D arcA arcB g δ x y
      = arcA x + y • g x
        + lensTheta δ x • (lensLambda (y/arch x) • (D (x, y/arch x)
            - (1 - y/arch x) • arcA x - (y/arch x) • arcB x))

The two cutoffs `lensTheta δ` (supported where `1 - x^2 ≥ δ/2`) and `lensLambda` (supported where
`|y/arch x| ≤ 4`) make the formula smooth *everywhere*: on `{1 - x^2 > δ/2}` the argument `y/arch x`
is smooth, and on `{1 - x^2 < δ}` the whole correction vanishes identically.

Its defining rows are
* `regularDiscZero_bot` : `Δ₀ (x,0) = arcA x`;
* `regularDiscZero_top` : `Δ₀ (x, arch x) = arcB x`;
* `regularDiscZero_sub_disc` : on the lens, `Δ₀ (x,y) - D (x, y/arch x)
  = (1 - lensTheta δ x * lensLambda (y/arch x)) • (arcA x + y • g x - D (x, y/arch x))`,
  which is the closeness estimate `R7`.
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff ENNReal
open Set Metric MeasureTheory Topology Filter
open Work.Drive.Whitney (sigR)

noncomputable section

variable {n : ℕ}

/-- The two edge functions of the bigon, in the lens coordinate `x ∈ [-1,1]`. -/
def arcA {M : Type*} (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ : ℝ → M) (x : ℝ) :
    EuclideanSpace ℝ (Fin (2 * n)) := f (γ₁ (sigR x))

def arcB {M : Type*} (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₂ : ℝ → M) (x : ℝ) :
    EuclideanSpace ℝ (Fin (2 * n)) := f (γ₂ (sigR x))

/-- The transition function used to glue the two Hadamard quotients: `1` for `x ≤ -1/2`,
`0` for `x ≥ 1/2`. -/
def gluePsi (x : ℝ) : ℝ := 1 - Real.smoothTransition (x + 1 / 2)

theorem contDiff_gluePsi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) gluePsi := by
  unfold gluePsi; fun_prop

theorem gluePsi_eq_one {x : ℝ} (hx : x ≤ -(1 / 2)) : gluePsi x = 1 := by
  have h : Real.smoothTransition (x + 1 / 2) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  rw [gluePsi, h]; ring

theorem gluePsi_eq_zero {x : ℝ} (hx : 1 / 2 ≤ x) : gluePsi x = 0 := by
  have h : Real.smoothTransition (x + 1 / 2) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  rw [gluePsi, h]; ring

/-- **The Hadamard quotient by the arch.**  For a smooth `F` with `F 1 = 0 = F (-1)` there is a
smooth `g` with `arch x • g x = F x` for every `x`. -/
theorem exists_archQuot {F : ℝ → EuclideanSpace ℝ (Fin (2 * n))}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (h1 : F 1 = 0) (hm1 : F (-1) = 0) :
    ∃ g : ℝ → EuclideanSpace ℝ (Fin (2 * n)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ ∀ x : ℝ, arch x • g x = F x := by
  -- the two Hadamard quotients, at `-1` and at `1`
  obtain ⟨Gm, hGm, hGmv, -⟩ := hadamard (E := ℝ) (F := EuclideanSpace ℝ (Fin (2 * n)))
    (fun t : ℝ => F (t + (-1))) (hF.comp (contDiff_id.add contDiff_const)) (by simpa using hm1)
  obtain ⟨Gp, hGp, hGpv, -⟩ := hadamard (E := ℝ) (F := EuclideanSpace ℝ (Fin (2 * n)))
    (fun t : ℝ => F (t + 1)) (hF.comp (contDiff_id.add contDiff_const)) (by simpa using h1)
  have hg₁sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => (Gm (x + 1)) 1) :=
    (hGm.clm_apply contDiff_const).comp (contDiff_id.add contDiff_const)
  have hg₂sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => (Gp (x - 1)) 1) :=
    (hGp.clm_apply contDiff_const).comp (contDiff_id.sub contDiff_const)
  have hg₁val : ∀ x : ℝ, F x = (x + 1) • ((Gm (x + 1)) 1) := by
    intro x
    have h := hGmv (x + 1)
    rw [show x + 1 + (-1) = x from by ring] at h
    rw [h]
    simpa using (Gm (x + 1)).map_smul (x + 1) (1 : ℝ)
  have hg₂val : ∀ x : ℝ, F x = (x - 1) • ((Gp (x - 1)) 1) := by
    intro x
    have h := hGpv (x - 1)
    rw [show x - 1 + 1 = x from by ring] at h
    rw [h]
    simpa using (Gp (x - 1)).map_smul (x - 1) (1 : ℝ)
  refine ⟨fun x => gluePsi x • ((1 - x)⁻¹ • ((Gm (x + 1)) 1))
      + (1 - gluePsi x) • ((-(1 + x)⁻¹) • ((Gp (x - 1)) 1)), ?_, ?_⟩
  · -- smoothness
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx1 : x = 1
    · subst hx1
      have hev : (fun y : ℝ => gluePsi y • ((1 - y)⁻¹ • ((Gm (y + 1)) 1))
            + (1 - gluePsi y) • ((-(1 + y)⁻¹) • ((Gp (y - 1)) 1)))
          =ᶠ[𝓝 (1:ℝ)] (fun y : ℝ => (-(1 + y)⁻¹) • ((Gp (y - 1)) 1)) := by
        filter_upwards [isOpen_Ioi.mem_nhds (show (1/2 : ℝ) < 1 by norm_num)] with y hy
        rw [gluePsi_eq_zero (le_of_lt hy), zero_smul, sub_zero, one_smul, zero_add]
      refine ContDiffAt.congr_of_eventuallyEq ?_ hev
      exact ((((contDiff_const.add contDiff_id).contDiffAt.inv (by norm_num)).neg).smul
        hg₂sm.contDiffAt)
    · by_cases hxm : x = -1
      · subst hxm
        have hev : (fun y : ℝ => gluePsi y • ((1 - y)⁻¹ • ((Gm (y + 1)) 1))
              + (1 - gluePsi y) • ((-(1 + y)⁻¹) • ((Gp (y - 1)) 1)))
            =ᶠ[𝓝 (-1:ℝ)] (fun y : ℝ => gluePsi y • ((1 - y)⁻¹ • ((Gm (y + 1)) 1))) := by
          filter_upwards [isOpen_Iio.mem_nhds (show (-1:ℝ) < -(1/2) by norm_num)] with y hy
          rw [gluePsi_eq_one (le_of_lt hy), one_smul, sub_self, zero_smul, add_zero]
        refine ContDiffAt.congr_of_eventuallyEq ?_ hev
        exact (contDiff_gluePsi.contDiffAt.smul
          (((contDiff_const.sub contDiff_id).contDiffAt.inv (by norm_num)).smul hg₁sm.contDiffAt))
      · have h1x : (1 : ℝ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
        have h2x : (1 : ℝ) + x ≠ 0 := by intro h; exact hxm (by linarith)
        exact (contDiff_gluePsi.contDiffAt.smul
            (((contDiff_const.sub contDiff_id).contDiffAt.inv h1x).smul hg₁sm.contDiffAt)).add
          (((contDiffAt_const.sub contDiff_gluePsi.contDiffAt).smul
            ((((contDiff_const.add contDiff_id).contDiffAt.inv h2x)).neg.smul hg₂sm.contDiffAt)))
  · -- the defining identity
    intro x
    rcases eq_or_ne x 1 with rfl | hx1
    · rw [show arch (1:ℝ) = 0 by simp [arch], zero_smul, h1]
    rcases eq_or_ne x (-1) with rfl | hxm1
    · rw [show arch (-1:ℝ) = 0 by simp [arch], zero_smul, hm1]
    have h1x : (1 : ℝ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
    have h2x : (1 : ℝ) + x ≠ 0 := by intro h; exact hxm1 (by linarith)
    have e1 : arch x • ((1 - x)⁻¹ • ((Gm (x + 1)) 1)) = F x := by
      rw [smul_smul, show arch x * (1 - x)⁻¹ = 1 + x from by
        rw [arch]; field_simp; ring]
      simpa [add_comm] using (hg₁val x).symm
    have e2 : arch x • ((-(1 + x)⁻¹) • ((Gp (x - 1)) 1)) = F x := by
      rw [smul_smul, show arch x * (-(1 + x)⁻¹) = x - 1 from by
        rw [arch]; field_simp; ring]
      exact (hg₂val x).symm
    calc arch x • (gluePsi x • ((1 - x)⁻¹ • ((Gm (x + 1)) 1))
          + (1 - gluePsi x) • ((-(1 + x)⁻¹) • ((Gp (x - 1)) 1)))
        = gluePsi x • (arch x • ((1 - x)⁻¹ • ((Gm (x + 1)) 1)))
          + (1 - gluePsi x) • (arch x • ((-(1 + x)⁻¹) • ((Gp (x - 1)) 1))) := by
          rw [smul_add]
          congr 1
          · rw [smul_comm]
          · rw [smul_comm]
      _ = gluePsi x • F x + (1 - gluePsi x) • F x := by rw [e1, e2]
      _ = F x := by rw [← add_smul]; norm_num


/-! ## The two cutoffs and the base map `Δ₀` -/

/-- The cutoff that kills the correction near the cusps: `lensTheta δ x = 0` for `1 - x^2 ≤ δ`
and `= 1` for `1 - x^2 ≥ 3 δ / 2`. -/
def lensTheta (δ x : ℝ) : ℝ := Real.smoothTransition ((1 - x ^ 2 - δ) / (δ / 2))

theorem contDiff_lensTheta (δ : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lensTheta δ) := by
  unfold lensTheta; fun_prop

theorem lensTheta_eq_zero {δ x : ℝ} (hδ : 0 < δ) (h : 1 - x ^ 2 ≤ δ) : lensTheta δ x = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

theorem lensTheta_eq_one {δ x : ℝ} (hδ : 0 < δ) (h : 3 * δ / 2 ≤ 1 - x ^ 2) :
    lensTheta δ x = 1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (by linarith)).mpr (by linarith))

/-- The cutoff in the variable `y / arch x`: `1` for `|v| ≤ √3`, `0` for `|v| ≥ 2`. -/
def lensLambda (v : ℝ) : ℝ := Real.smoothTransition (4 - v ^ 2)

theorem contDiff_lensLambda : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) lensLambda := by
  unfold lensLambda; fun_prop

theorem lensLambda_eq_one {v : ℝ} (h : v ^ 2 ≤ 3) : lensLambda v = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- The correction that replaces the chord `A + y • g` by the disc's parametrisation on the bulk
of the lens. -/
def discCorr (D : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))) (A B g : ℝ → EuclideanSpace ℝ (Fin (2 * n)))
    (δ : ℝ) (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin (2 * n)) :=
  lensTheta δ p.1 • (lensLambda (p.2 / arch p.1) • (D (p.1, p.2 / arch p.1)
    - (1 - p.2 / arch p.1) • A p.1 - (p.2 / arch p.1) • B p.1))

/-- **The base map `Δ₀` of `L0`.** -/
def regularDiscZero (D : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n)))
    (A B g : ℝ → EuclideanSpace ℝ (Fin (2 * n))) (δ : ℝ) :
    ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n)) :=
  fun p => A p.1 + p.2 • g p.1 + discCorr D A B g δ p

theorem contDiff_discCorr {D : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))}
    {A B g : ℝ → EuclideanSpace ℝ (Fin (2 * n))} {δ : ℝ}
    (hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) D) (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B) (hδ : 0 < δ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (discCorr (n := n) D A B g δ) := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨x, y⟩
  by_cases hx : 1 - x ^ 2 ≤ δ / 2
  · -- `lensTheta` vanishes on a neighbourhood
    have hmem : {z : ℝ | 1 - z ^ 2 < δ} ∈ 𝓝 x := by
      have : IsOpen {z : ℝ | 1 - z ^ 2 < δ} := isOpen_lt (by fun_prop) continuous_const
      exact this.mem_nhds (show 1 - x ^ 2 < δ by linarith)
    have hzero : ∀ᶠ q : ℝ × ℝ in 𝓝 (x, y), lensTheta δ q.1 = 0 := by
      filter_upwards [(continuous_fst.tendsto (x, y)).eventually hmem] with q hq
      exact lensTheta_eq_zero hδ (le_of_lt hq)
    have hev : (discCorr (n := n) D A B g δ) =ᶠ[𝓝 (x, y)] (fun _ => (0 : EuclideanSpace ℝ (Fin (2 * n)))) := by
      filter_upwards [hzero] with q hq
      simp [discCorr, hq]
    exact (contDiffAt_const (c := (0 : EuclideanSpace ℝ (Fin (2 * n))))).congr_of_eventuallyEq hev
  · -- `arch x > δ / 2 > 0`, so the formula is smooth
    have harch : δ / 2 < arch x := by
      simp only [not_le] at hx; simpa [arch] using hx
    have hpos : 0 < arch x := by linarith
    have hθ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => lensTheta δ q.1) (x, y) :=
      (contDiff_lensTheta δ).contDiffAt.comp (x, y) contDiffAt_fst
    have harchsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => arch q.1) := by
      rw [show (fun q : ℝ × ℝ => arch q.1) = fun q : ℝ × ℝ => 1 - q.1 ^ 2 from rfl]
      fun_prop
    have hdiv : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × ℝ => q.2 / arch q.1) (x, y) :=
      contDiffAt_snd.div harchsm.contDiffAt (ne_of_gt hpos)
    have hD' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × ℝ => D (q.1, q.2 / arch q.1)) (x, y) :=
      hD.contDiffAt.comp (x, y) (contDiffAt_fst.prodMk hdiv)
    have hA' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => A q.1) (x, y) :=
      hA.contDiffAt.comp (x, y) contDiffAt_fst
    have hB' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => B q.1) (x, y) :=
      hB.contDiffAt.comp (x, y) contDiffAt_fst
    have hlam : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × ℝ => lensLambda (q.2 / arch q.1)) (x, y) :=
      contDiff_lensLambda.contDiffAt.comp (x, y) hdiv
    have hinner : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × ℝ => D (q.1, q.2 / arch q.1)
          - (1 - q.2 / arch q.1) • A q.1 - (q.2 / arch q.1) • B q.1) (x, y) :=
      (hD'.sub (((contDiffAt_const.sub hdiv).smul hA'))).sub (hdiv.smul hB')
    exact hθ.smul (hlam.smul hinner)

theorem contDiff_regularDiscZero {D : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))}
    {A B g : ℝ → EuclideanSpace ℝ (Fin (2 * n))} {δ : ℝ}
    (hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) D) (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hδ : 0 < δ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (regularDiscZero (n := n) D A B g δ) := by
  refine (hA.comp contDiff_fst).add ?_ |>.add (contDiff_discCorr (n := n) hD hA hB hδ)
  exact (contDiff_snd.smul (hg.comp contDiff_fst))


/-! ## The rows of `Δ₀` -/

theorem regularDiscZero_bot {A B g : ℝ → EuclideanSpace ℝ (Fin (2 * n))}
    {D : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))} {δ : ℝ} (hD : ∀ x, D (x, 0) = A x) (x : ℝ) :
    regularDiscZero D A B g δ (x, 0) = A x := by
  simp only [regularDiscZero, discCorr]
  rw [zero_div, hD]
  simp

theorem regularDiscZero_top {A B g : ℝ → EuclideanSpace ℝ (Fin (2 * n))}
    {D : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))} {δ : ℝ} (hδ : 0 < δ)
    (hgval : ∀ x, arch x • g x = B x - A x) (hD : ∀ x, D (x, 1) = B x) (x : ℝ) :
    regularDiscZero D A B g δ (x, arch x) = B x := by
  have hBA : arch x • g x = B x - A x := hgval x
  simp only [regularDiscZero, discCorr]
  rcases eq_or_ne (arch x) 0 with h | h
  · have hle : 1 - x ^ 2 ≤ δ := by
      have hx2 : x ^ 2 = 1 := by
        have hh := h; simp only [arch] at hh; linarith
      rw [hx2]; linarith
    have hθ : lensTheta δ x = 0 := lensTheta_eq_zero hδ hle
    have hab : A x = B x := by
      have hh := hgval x
      rw [h] at hh
      simp only [zero_smul] at hh
      exact (sub_eq_zero.mp hh.symm).symm
    rw [hθ, h, hab]
    simp
  · rw [div_self h, hD]
    have hcorr : lensTheta δ x • (lensLambda 1 • (B x - ((1 : ℝ) - 1) • A x - (1 : ℝ) • B x)) = 0 := by
      rw [show lensLambda 1 = 1 from by
            rw [lensLambda, show (4 : ℝ) - 1 ^ 2 = 3 by norm_num,
              Real.smoothTransition.one_of_one_le (by norm_num)]]
      simp
    rw [hcorr, add_zero, hBA]
    abel

/-- **The closeness identity.**  On the lens, `Δ₀` differs from the disc parametrisation
`D (x, y/arch x)` by the factor `1 - lensTheta δ x * lensLambda (y/arch x)`. -/
theorem regularDiscZero_sub_disc {A B g : ℝ → EuclideanSpace ℝ (Fin (2 * n))}
    {D : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))} {δ : ℝ}
    (hgval : ∀ x, arch x • g x = B x - A x) {x y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ arch x) :
    regularDiscZero D A B g δ (x, y) - D (x, y / arch x)
      = (1 - lensTheta δ x * lensLambda (y / arch x)) • (A x + y • g x - D (x, y / arch x)) := by
  have hkey : (y / arch x) * arch x = y := by
    rcases eq_or_ne (arch x) 0 with h | h
    · rw [h, div_zero, zero_mul]
      exact le_antisymm hy0 (by rw [h] at hy1; exact hy1)
    · rw [div_mul_cancel₀ _ h]
  have hBA : arch x • g x = B x - A x := hgval x
  have hsub : D (x, y / arch x) - (1 - y / arch x) • A x - (y / arch x) • B x
      = D (x, y / arch x) - A x - y • g x := by
    have ht : (y / arch x) • (arch x • g x) = y • g x := by
      rw [smul_smul, hkey]
    rw [show D (x, y / arch x) - (1 - y / arch x) • A x - (y / arch x) • B x
        = D (x, y / arch x) - A x - (y / arch x) • (B x - A x) by
      rw [smul_sub]; module]
    rw [← hBA, ht]
  simp only [regularDiscZero, discCorr]
  rw [hsub]
  module

end

end Work.Drive.PushDisc
