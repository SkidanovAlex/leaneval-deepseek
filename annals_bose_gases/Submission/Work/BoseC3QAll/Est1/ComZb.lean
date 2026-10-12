import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseC3QAll.Est1.ComZ
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Est1.ComZ` — the analysis of the `χ̂²` half

This module proves the inequalities of the `χ̂²` half `Est1.estT2sum_comZ`
(FS `eq:EstimT2comm`): the split of `T2ComF` (`Est1.t2com_split`) is bounded by
the `Ã`-form `FA` (`Est1.FA`) plus the two errors (`wc`-deviation and the
`χ̂(s-k)χ̂(s'-k)` term), and `FA` is compared with `⟨G Φ⟩` and the two moments
`⟨n₊⟩`, `‖Φ‖²`.

## Contents

* `two_abs_bp_le` — AM–GM for the Fock form.
* `sum_excited_neg` — the reindexing `s ↦ -s` on the excited modes.
* `sum_fL_le_NPL` — `Σ_{s}f_L(s) ≤ NPL`.
* `TA_le_N` — `TA ≤ ⟨n₊⟩`.
* `TB_le` — `TB ≤ TA + NPL·‖Φ‖²`.
* `AbsA0_le` — `Σ f_Lf_L'|⟨Ã_s,Ã_{s'}⟩| ≤ NPL·Σ f_L‖Ã_s‖²`.
* `sum_hatChiSq_shift` — `Σ_{s'}|χ̂²(s'-s)| ≤ K₀+1`.
* `sum_Atil_sq_le` — `Σ f_L‖Ã_{s,k}Φ‖² ≤ 2TA + 2β²TB`.
* `FA_PSD`, `FA_le_Q` — positivity of `FA` and the comparison with `⟨G Φ⟩`.
* `rawY_bound` — the `χ̂(s-k)χ̂(s'-k)` error.
-/

noncomputable section
open scoped BigOperators
namespace Work.BoseC3QAll
namespace Est1
open Work.BoseB7
variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
/-- The scalar deviation: for `|x|,|u|,|v| ≤ X ≤ 2/3`,
`|(1-uv)/((1-x²)²(1-u²)(1-v²)) - 1| ≤ 2²⁰X²`. -/
theorem wc_arith {x u v X : ℝ} (hx : |x| ≤ X) (hu : |u| ≤ X) (hv : |v| ≤ X)
    (hX0 : 0 ≤ X) (hX : X ≤ 2 / 3) :
    |(1 - u * v) / ((1 - x ^ 2) ^ 2 * (1 - u ^ 2) * (1 - v ^ 2)) - 1| ≤ 2 ^ 8 * X ^ 2 := by
  have hx2 : x ^ 2 ≤ X ^ 2 := sq_le_sq.mpr (by rwa [← abs_of_nonneg hX0] at hx)
  have hu2 : u ^ 2 ≤ X ^ 2 := sq_le_sq.mpr (by rwa [← abs_of_nonneg hX0] at hu)
  have hv2 : v ^ 2 ≤ X ^ 2 := sq_le_sq.mpr (by rwa [← abs_of_nonneg hX0] at hv)
  have hX21 : X ^ 2 ≤ 1 := by nlinarith
  have hna : 0 ≤ 1 - X ^ 2 := by linarith
  have hnu : 0 ≤ 1 - u ^ 2 := by linarith
  have hnv : 0 ≤ 1 - v ^ 2 := by linarith
  have hnx2 : 0 ≤ (1 - x ^ 2) ^ 2 := by positivity
  have hnuv : 0 ≤ (1 - u ^ 2) * (1 - v ^ 2) := mul_nonneg hnu hnv
  set D : ℝ := (1 - x ^ 2) ^ 2 * (1 - u ^ 2) * (1 - v ^ 2) with hD
  have hDlo : (1 - X ^ 2) ^ 4 ≤ D := by
    have h1 : (1 - X ^ 2) ^ 2 ≤ (1 - x ^ 2) ^ 2 := by nlinarith
    have h2 : (1 - X ^ 2) * (1 - X ^ 2) ≤ (1 - u ^ 2) * (1 - v ^ 2) :=
      mul_le_mul (by linarith) (by linarith) hna hnu
    rw [hD]
    calc (1 - X ^ 2) ^ 4 = (1 - X ^ 2) ^ 2 * ((1 - X ^ 2) * (1 - X ^ 2)) := by ring
      _ ≤ (1 - x ^ 2) ^ 2 * ((1 - u ^ 2) * (1 - v ^ 2)) :=
          mul_le_mul h1 h2 (mul_nonneg hna hna) hnx2
      _ = (1 - x ^ 2) ^ 2 * (1 - u ^ 2) * (1 - v ^ 2) := by ring
  have hDle : D ≤ 1 := by
    rw [hD, show (1 - x ^ 2) ^ 2 * (1 - u ^ 2) * (1 - v ^ 2)
        = (1 - x ^ 2) ^ 2 * ((1 - u ^ 2) * (1 - v ^ 2)) by ring]
    have h1 : (1 - x ^ 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg x, hx2, hX21]
    have h2 : (1 - u ^ 2) * (1 - v ^ 2) ≤ 1 := by
      nlinarith [sq_nonneg u, sq_nonneg v, hu2, hv2, hX21, sq_nonneg (u * v)]
    calc (1 - x ^ 2) ^ 2 * ((1 - u ^ 2) * (1 - v ^ 2)) ≤ 1 * 1 :=
          mul_le_mul h1 h2 hnuv (by norm_num)
      _ = 1 := by norm_num
  have hDge : (1 : ℝ) / 11 ≤ D := by
    have h81 : ((5 : ℝ) / 9) ^ 4 ≤ (1 - X ^ 2) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) (by nlinarith) 4
    have h54 : ((5 : ℝ) / 9) ^ 4 = 625 / 6561 := by norm_num
    linarith
  have hDpos : 0 < D := by linarith
  have hDinv : 1 / D ≤ 11 := by
    rw [div_le_iff₀ hDpos]
    linarith [hDge]
  have huv : |u * v| ≤ X ^ 2 := by
    rw [abs_mul]
    nlinarith [abs_le.mp hu, abs_le.mp hv, abs_nonneg u, abs_nonneg v, hX0]
  have huva : -(X ^ 2) ≤ u * v := (abs_le.mp huv).1
  have huvb : u * v ≤ X ^ 2 := (abs_le.mp huv).2
  have h1D : 1 - D ≤ 4 * X ^ 2 := by
    have hb : 1 - 4 * X ^ 2 ≤ (1 - X ^ 2) ^ 4 := by
      have h2 : (0 : ℝ) ≤ 6 - 4 * X ^ 2 + (X ^ 2) ^ 2 := by nlinarith [sq_nonneg (X ^ 2 - 2)]
      have h4 : 0 ≤ (X ^ 2) ^ 2 := by positivity
      have hexp : (1 - X ^ 2) ^ 4 - (1 - 4 * X ^ 2)
          = (X ^ 2) ^ 2 * (6 - 4 * X ^ 2 + (X ^ 2) ^ 2) := by ring
      linarith [mul_nonneg h4 h2]
    linarith
  have h1D0 : 0 ≤ 1 - D := by linarith
  have hnum : |1 - u * v - D| ≤ 5 * X ^ 2 := by
    rw [abs_le]
    constructor <;> linarith [huvb, huva, h1D, h1D0]
  have hkey : (1 - u * v) / D - 1 = (1 - u * v - D) / D := by
    field_simp
  rw [show (1 - u * v) / ((1 - x ^ 2) ^ 2 * (1 - u ^ 2) * (1 - v ^ 2))
      = (1 - u * v) / D from by rw [hD]]
  rw [hkey, abs_div, abs_of_pos hDpos]
  calc |1 - u * v - D| / D ≤ 5 * X ^ 2 / D :=
        div_le_div_of_nonneg_right hnum hDpos.le
    _ = 5 * X ^ 2 * (1 / D) := by ring
    _ ≤ 5 * X ^ 2 * 11 := mul_le_mul_of_nonneg_left hDinv (by positivity)
    _ ≤ 2 ^ 8 * X ^ 2 := by nlinarith [sq_nonneg X]

/-- `η > 0` at the parameter point. -/
theorem eta_pos {E : Q3Env Mode} (h : FSParamsView E) : 0 < eta E := by
  rw [Work.BoseC3QAll.eta_eq E h]
  exact Work.BoseBox.fsXp_pos h.t_pos

/-- **The `wc`-deviation**: `|wc - 1| ≤ C_dev` on the relevant modes. -/
theorem wc_dev (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F)
        (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Work.BoseC3QAll.Q3KernelFSAll K₀ F T E →
        ∀ k s s' : Mode, k ∈ F.PHset E → E.fL s ≠ 0 → E.fL s' ≠ 0 → E.W1 k ≠ 0 →
          |wc E k s s' - 1| ≤ devc K₀ E := by
  obtain ⟨t₁, ht₁, h₁⟩ := PH_subset_PHq_sub K₀ b₀ hb₀
  obtain ⟨t₂, ht₂, h₂⟩ := kernel_basic K₀ b₀ hb₀
  obtain ⟨t₃, ht₃, h₃⟩ := lille_threshold K₀
  refine ⟨min (min t₁ t₂) t₃, lt_min (lt_min ht₁ ht₂) ht₃, ?_⟩
  intro Mode _ _ _ F T E hv hle hb hK k s s' hk hfl hfl' hW
  have hle₁ : hv.t ≤ t₁ := le_trans hle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hle₂ : hv.t ≤ t₂ := le_trans hle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hle₃ : hv.t ≤ t₃ := le_trans hle (min_le_right _ _)
  obtain ⟨hPHq, hsubq, -⟩ := h₁ F T E hv hle₁ hb hK
  obtain ⟨-, -, -, hαle, -⟩ := h₂ F T E hv hle₂ hb hK
  have hK0 : 0 ≤ K₀ := K₀_nonneg_of_kernel K₀ F T E hv hK
  have hlil : 0 ≤ E.lille := le_of_lt (lille_pos E hv)
  have h96 : 96 * max K₀ 0 * E.lille ≤ 1 := h₃ E hv hle₃
  have hX64 : 64 * K₀ * E.lille ≤ 2 / 3 := by
    have hmax : K₀ ≤ max K₀ 0 := le_max_left _ _
    have h1 : K₀ * E.lille ≤ max K₀ 0 * E.lille := mul_le_mul_of_nonneg_right hmax hlil
    nlinarith
  have hX0 : 0 ≤ 64 * K₀ * E.lille := by positivity
  have hkPH : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
  have hqk : F.PHq E.KH E.aScat k := hPHq k hkPH
  have hqsk : F.PHq E.KH E.aScat (s - k) := hsubq s k hfl hk hW
  have hqs'k : F.PHq E.KH E.aScat (s' - k) := hsubq s' k hfl' hk hW
  have hxk : |E.alpha k| ≤ 64 * K₀ * E.lille := hαle k hqk
  have hxu : |E.alpha (s - k)| ≤ 64 * K₀ * E.lille := hαle (s - k) hqsk
  have hxv : |E.alpha (s' - k)| ≤ 64 * K₀ * E.lille := hαle (s' - k) hqs'k
  rw [wc_form]
  have harith := wc_arith hxk hxu hxv hX0 hX64
  rw [devc]
  calc |(1 - E.alpha (s - k) * E.alpha (s' - k)) /
        ((1 - E.alpha k ^ 2) ^ 2 * (1 - E.alpha (s - k) ^ 2)
          * (1 - E.alpha (s' - k) ^ 2)) - 1|
      ≤ 2 ^ 8 * (64 * K₀ * E.lille) ^ 2 := harith
    _ = 2 ^ 20 * K₀ ^ 2 * E.lille ^ 2 := by ring

/-- `Λ ≤ 2ρ_z(Ŵ₁ω(0) + K₀aK_H⁻¹)(1+2𝓁²)`, from `wsum_eq` and `Xi_bound`. -/
theorem wsum_le {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hv : FSParamsView E)
    (hK : Q3KernelFSAll K₀ F T E) (hℓ : 0 < E.ell) (hlil : E.lille ^ 2 ≤ 1 / 2)
    (hDne : ∀ k ∈ F.PHset E, E.D k ≠ 0) :
    wsum F E ≤ 2 * E.rho * (E.W1omega0 + K₀ * E.aScat * E.KH⁻¹) * (1 + 2 * E.lille ^ 2) := by
  have hden : 1 - E.lille ^ 2 ≠ 0 := by
    intro h; linarith [hlil]
  rw [wsum_eq hℓ hden hDne]
  have hΞ : Xi F E ≤ E.W1omega0 + K₀ * E.aScat * E.KH⁻¹ := by
    have := (abs_le.mp (Xi_bound hv hK)).1
    linarith
  have hρ : 0 < E.rho := Work.BoseB7.rho_pos E hv
  have hdenpos : (0 : ℝ) < 1 - E.lille ^ 2 := by linarith
  have hK0 : 0 ≤ K₀ := K₀_nonneg_of_kernel K₀ F T E hv hK
  have hKH : 0 < E.KH := lt_of_lt_of_le zero_lt_one hv.one_le_KH
  have hA : 0 ≤ E.W1omega0 + K₀ * E.aScat * E.KH⁻¹ := by
    have h1 : 0 ≤ K₀ * E.aScat * E.KH⁻¹ :=
      mul_nonneg (mul_nonneg hK0 (le_of_lt hv.a_pos)) (inv_nonneg.mpr hKH.le)
    linarith [hK.W1omega0_nonneg]
  have hinv : 1 / (1 - E.lille ^ 2) ≤ 1 + 2 * E.lille ^ 2 := by
    rw [div_le_iff₀ hdenpos]
    nlinarith [sq_nonneg E.lille, hlil]
  rw [show 2 * E.rho * Xi F E / (1 - E.lille ^ 2)
      = 2 * E.rho * Xi F E * (1 / (1 - E.lille ^ 2)) by ring]
  calc 2 * E.rho * Xi F E * (1 / (1 - E.lille ^ 2))
      ≤ 2 * E.rho * (E.W1omega0 + K₀ * E.aScat * E.KH⁻¹) * (1 / (1 - E.lille ^ 2)) := by
        have h1 : 0 ≤ 2 * E.rho := by linarith
        have h2 : Xi F E * (1 / (1 - E.lille ^ 2))
            ≤ (E.W1omega0 + K₀ * E.aScat * E.KH⁻¹) * (1 / (1 - E.lille ^ 2)) :=
          mul_le_mul_of_nonneg_right hΞ (by positivity)
        nlinarith [h1, h2]
    _ ≤ 2 * E.rho * (E.W1omega0 + K₀ * E.aScat * E.KH⁻¹) * (1 + 2 * E.lille ^ 2) := by
        have h1 : 0 ≤ 2 * E.rho * (E.W1omega0 + K₀ * E.aScat * E.KH⁻¹) :=
          mul_nonneg (by linarith) hA
        exact mul_le_mul_of_nonneg_left hinv h1


/-! ## 10. The `Ã`-vs-`ã` comparison -/

/-- `Σ_{s'∈excited}|χ̂²(s'-s)| ≤ K₀+1`: the shifted kernel is summable because the
shift `s' ↦ s'-s` injects the excited modes into the lattice and `Σ|χ̂²| ≤ K₀+1`
(the value at `0` is the only mode lost). -/
theorem sum_hatChiSq_shift {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3KernelFSAll K₀ F T E) (s : Mode) :
    (∑ s' ∈ excited Mode, |E.hatChiSq (s' - s)|) ≤ K₀ + 1 := by
  have hinj : ∀ a ∈ excited Mode, ∀ b ∈ excited Mode, a - s = b - s → a = b := by
    intro a _ b _ h
    have h2 : a - s + s = b - s + s := by rw [h]
    rwa [sub_add_cancel, sub_add_cancel] at h2
  calc (∑ s' ∈ excited Mode, |E.hatChiSq (s' - s)|)
      = ∑ q ∈ (excited Mode).image (fun s' => s' - s), |E.hatChiSq q| :=
        (Finset.sum_image (f := fun q => |E.hatChiSq q|)
          (g := fun s' => s' - s) hinj).symm
    _ ≤ ∑ q ∈ (Finset.univ : Finset Mode), |E.hatChiSq q| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun q _ _ => abs_nonneg _)
    _ = ∑ q ∈ excited Mode, |E.hatChiSq q| + |E.hatChiSq 0| := by
        rw [show (Finset.univ : Finset Mode) = insert 0 (excited Mode) by
          ext q; simp [excited]]
        rw [Finset.sum_insert (by simp [excited])]
        ring
    _ ≤ K₀ + 1 := by
        have h1 := hK.sum_hatChiSq
        have h2 := hK.hatChiSq_le 0
        linarith

/-- `Σ_{s,s'}f_L(s)f_L(s')|χ̂²(s'-s)|X_s ≤ (K₀+1)Σ_sf_L(s)X_s` for `X ≥ 0`. -/
theorem sum_chi2_le {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3KernelFSAll K₀ F T E) (X : Mode → ℝ) (hX : ∀ s ∈ excited Mode, 0 ≤ X s) :
    (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * X s)
      ≤ (K₀ + 1) * ∑ s ∈ excited Mode, E.fL s * X s := by
  have hw : ∀ s ∈ excited Mode,
      (∑ s' ∈ excited Mode, E.fL s' * |E.hatChiSq (s' - s)|) ≤ K₀ + 1 := by
    intro s _
    calc (∑ s' ∈ excited Mode, E.fL s' * |E.hatChiSq (s' - s)|)
        ≤ ∑ s' ∈ excited Mode, |E.hatChiSq (s' - s)| :=
          Finset.sum_le_sum fun s' _ =>
            mul_le_of_le_one_left (abs_nonneg _) (hK.fL_le_one s')
      _ ≤ K₀ + 1 := sum_hatChiSq_shift hK s
  calc (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * X s)
      = ∑ s ∈ excited Mode, (E.fL s * X s)
          * (∑ s' ∈ excited Mode, E.fL s' * |E.hatChiSq (s' - s)|) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s' _ => ?_
        ring
    _ ≤ ∑ s ∈ excited Mode, (E.fL s * X s) * (K₀ + 1) :=
        Finset.sum_le_sum fun s hs =>
          mul_le_mul_of_nonneg_left (hw s hs) (mul_nonneg (hK.fL_nonneg s) (hX s hs))
    _ = (K₀ + 1) * ∑ s ∈ excited Mode, E.fL s * X s := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        ring

/-- The transposed form: the weight may sit on the second index. -/
theorem sum_chi2_le' {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3KernelFSAll K₀ F T E) (X : Mode → ℝ) (hX : ∀ s ∈ excited Mode, 0 ≤ X s) :
    (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * X s')
      ≤ (K₀ + 1) * ∑ s ∈ excited Mode, E.fL s * X s := by
  rw [Finset.sum_comm]
  have h := sum_chi2_le (K₀ := K₀) hK X hX
  refine le_trans ?_ h
  refine Finset.sum_le_sum fun s' _ => Finset.sum_le_sum fun s _ => ?_
  rw [hatChiSq_swap hK s' s]
  exact le_of_eq (by ring)

/-- The weighted first-index sum, scaled by `c ≥ 0`. -/
theorem sum_chi2_cX {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3KernelFSAll K₀ F T E) (c : ℝ) (hc : 0 ≤ c) (X : Mode → ℝ)
    (hX : ∀ s ∈ excited Mode, 0 ≤ X s) :
    (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * (c * X s))
      ≤ c * ((K₀ + 1) * (∑ s ∈ excited Mode, E.fL s * X s)) := by
  have h := sum_chi2_le (K₀ := K₀) hK X hX
  rw [show (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * (c * X s))
      = c * (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * X s) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    ring]
  exact mul_le_mul_of_nonneg_left h hc

/-- The weighted second-index sum, scaled by `c ≥ 0`. -/
theorem sum_chi2_cY {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3KernelFSAll K₀ F T E) (c : ℝ) (hc : 0 ≤ c) (Y : Mode → ℝ)
    (hY : ∀ s ∈ excited Mode, 0 ≤ Y s) :
    (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * (c * Y s'))
      ≤ c * ((K₀ + 1) * (∑ s ∈ excited Mode, E.fL s * Y s)) := by
  have h := sum_chi2_le' (K₀ := K₀) hK Y hY
  rw [show (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * (c * Y s'))
      = c * (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * Y s') from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    ring]
  exact mul_le_mul_of_nonneg_left h hc

/-- The combined form: `Σ_{s,s'}Wt·(c·(X_s+Y_{s'})) ≤ c((K₀+1)Σf_LX + (K₀+1)Σf_LY)`. -/
theorem sum_chi2_pair {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3KernelFSAll K₀ F T E) (c : ℝ) (hc : 0 ≤ c) (X Y : Mode → ℝ)
    (hX : ∀ s ∈ excited Mode, 0 ≤ X s) (hY : ∀ s ∈ excited Mode, 0 ≤ Y s) :
    (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * (c * (X s + Y s')))
      ≤ c * ((K₀ + 1) * (∑ s ∈ excited Mode, E.fL s * X s)
        + (K₀ + 1) * (∑ s ∈ excited Mode, E.fL s * Y s)) := by
  have hA := sum_chi2_cX (K₀ := K₀) hK c hc X hX
  have hB := sum_chi2_cY (K₀ := K₀) hK c hc Y hY
  have hsplit : (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * (c * (X s + Y s')))
      = (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
          E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * (c * X s))
        + (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
          E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * (c * Y s')) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s' _ => ?_
    ring
  rw [hsplit]
  linarith

/-- **`FA - ⟨G Φ⟩`**: the `Ã`-vs-`ã` comparison, with the `O(β_m)` correction. -/
theorem FA_sub_Q_le {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3KernelFSAll K₀ F T E) (k : Mode) (Φ : F.H) (hK0 : 0 ≤ K₀)
    (hbm : ∀ s, E.fL s ≠ 0 → |bA E s k| ≤ bm K₀ E) :
    FA F T E k Φ - F.qw Φ (T.Gop E)
      ≤ 2 * (K₀ + 1) * (bm K₀ E + bm K₀ E ^ 2) * (TA F T E Φ + TB F T E Φ) := by
  have hbm0 : 0 ≤ bm K₀ E := bm_nonneg hK0
  have hQ : F.qw Φ (T.Gop E)
      = ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
          E.fL s * E.fL s' * E.hatChiSq (s' - s) * F.bp (T.ta s Φ) (T.ta s' Φ) := by
    simp only [FockData.qw, Work.BoseB7A.TildeData.Gop, map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply, bp_taDag_left]
  have hexp : ∀ s s', F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ)
        - F.bp (T.ta s Φ) (T.ta s' Φ)
      = bA E s' k * F.bp (T.ta s Φ) (T.taDag (-s') Φ)
        + bA E s k * F.bp (T.taDag (-s) Φ) (T.ta s' Φ)
        + bA E s k * bA E s' k * F.bp (T.taDag (-s) Φ) (T.taDag (-s') Φ) := by
    intro s s'
    have h1 : Atil F T E s k Φ = T.ta s Φ + (bA E s k) • T.taDag (-s) Φ := rfl
    have h2 : Atil F T E s' k Φ = T.ta s' Φ + (bA E s' k) • T.taDag (-s') Φ := rfl
    rw [h1, h2]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hsumU : (∑ s ∈ excited Mode, E.fL s * (F.bp (T.ta s Φ) (T.ta s Φ)
      + F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ))) = TA F T E Φ + TB F T E Φ := by
    rw [TA, TB, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hpair := sum_chi2_pair (K₀ := K₀) hK (bm K₀ E + bm K₀ E ^ 2)
    (by nlinarith [hbm0, sq_nonneg (bm K₀ E)]) (fun s => F.bp (T.ta s Φ) (T.ta s Φ) + F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ))
    (fun s => F.bp (T.ta s Φ) (T.ta s Φ) + F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ))
    (fun s _ => add_nonneg (F.bp_nonneg _) (F.bp_nonneg _))
    (fun s _ => add_nonneg (F.bp_nonneg _) (F.bp_nonneg _))
  rw [hQ]
  have hdiff : FA F T E k Φ
        - (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
            E.fL s * E.fL s' * E.hatChiSq (s' - s) * F.bp (T.ta s Φ) (T.ta s' Φ))
      = ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
          E.fL s * E.fL s' * E.hatChiSq (s' - s)
            * (F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ) - F.bp (T.ta s Φ) (T.ta s' Φ)) := by
    rw [FA, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s' _ => by ring
  rw [hdiff]
  calc ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * E.hatChiSq (s' - s)
          * (F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ) - F.bp (T.ta s Φ) (T.ta s' Φ))
      ≤ ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
          E.fL s * E.fL s' * |E.hatChiSq (s' - s)|
            * ((bm K₀ E + bm K₀ E ^ 2)
              * ((F.bp (T.ta s Φ) (T.ta s Φ) + F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ))
                + (F.bp (T.ta s' Φ) (T.ta s' Φ) + F.bp (T.taDag (-s') Φ) (T.taDag (-s') Φ)))) := by
        refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun s' _ => ?_
        rw [hexp s s']
        by_cases h0 : E.fL s = 0
        · rw [h0]; simp
        · by_cases h0' : E.fL s' = 0
          · rw [h0']; simp
          · have hfs : 0 ≤ E.fL s := hK.fL_nonneg s
            have hfs' : 0 ≤ E.fL s' := hK.fL_nonneg s'
            have hβs : |bA E s k| ≤ bm K₀ E := hbm s h0
            have hβs' : |bA E s' k| ≤ bm K₀ E := hbm s' h0'
            have hβs2 : (bA E s k) ^ 2 ≤ (bm K₀ E) ^ 2 := by
              nlinarith [abs_nonneg (bA E s k), sq_abs (bA E s k), hβs, hbm0]
            have hβs'2 : (bA E s' k) ^ 2 ≤ (bm K₀ E) ^ 2 := by
              nlinarith [abs_nonneg (bA E s' k), sq_abs (bA E s' k), hβs', hbm0]
            have h1 := two_abs_bp_le F (T.ta s Φ) (T.taDag (-s') Φ)
            have h2 := two_abs_bp_le F (T.taDag (-s) Φ) (T.ta s' Φ)
            have h3 := two_abs_bp_le F (T.taDag (-s) Φ) (T.taDag (-s') Φ)
            have e1 : |bA E s' k * F.bp (T.ta s Φ) (T.taDag (-s') Φ)|
                ≤ bm K₀ E * ((F.bp (T.ta s Φ) (T.ta s Φ)
                  + F.bp (T.taDag (-s') Φ) (T.taDag (-s') Φ)) / 2) := by
              rw [abs_mul]
              exact mul_le_mul hβs' (by linarith [h1]) (abs_nonneg _) hbm0
            have e2 : |bA E s k * F.bp (T.taDag (-s) Φ) (T.ta s' Φ)|
                ≤ bm K₀ E * ((F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ)
                  + F.bp (T.ta s' Φ) (T.ta s' Φ)) / 2) := by
              rw [abs_mul]
              exact mul_le_mul hβs (by linarith [h2]) (abs_nonneg _) hbm0
            have e3 : |bA E s k * bA E s' k * F.bp (T.taDag (-s) Φ) (T.taDag (-s') Φ)|
                ≤ bm K₀ E ^ 2 * ((F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ)
                  + F.bp (T.taDag (-s') Φ) (T.taDag (-s') Φ)) / 2) := by
              rw [abs_mul, abs_mul]
              have hβm : |bA E s k| * |bA E s' k| ≤ bm K₀ E ^ 2 := by
                calc |bA E s k| * |bA E s' k| ≤ bm K₀ E * bm K₀ E :=
                      mul_le_mul hβs hβs' (abs_nonneg _) hbm0
                  _ = bm K₀ E ^ 2 := by ring
              exact mul_le_mul hβm (by linarith [h3]) (abs_nonneg _) (by positivity)
            have habs1 := abs_add_le (bA E s' k * F.bp (T.ta s Φ) (T.taDag (-s') Φ))
              (bA E s k * F.bp (T.taDag (-s) Φ) (T.ta s' Φ))
            have habs2 := abs_add_le (bA E s' k * F.bp (T.ta s Φ) (T.taDag (-s') Φ)
                + bA E s k * F.bp (T.taDag (-s) Φ) (T.ta s' Φ))
              (bA E s k * bA E s' k * F.bp (T.taDag (-s) Φ) (T.taDag (-s') Φ))
            have hmono : |bA E s' k * F.bp (T.ta s Φ) (T.taDag (-s') Φ)
                  + bA E s k * F.bp (T.taDag (-s) Φ) (T.ta s' Φ)
                  + bA E s k * bA E s' k * F.bp (T.taDag (-s) Φ) (T.taDag (-s') Φ)|
                ≤ |bA E s' k * F.bp (T.ta s Φ) (T.taDag (-s') Φ)|
                  + |bA E s k * F.bp (T.taDag (-s) Φ) (T.ta s' Φ)|
                  + |bA E s k * bA E s' k * F.bp (T.taDag (-s) Φ) (T.taDag (-s') Φ)| := by
              linarith [habs1, habs2]
            have hkey : |bA E s' k * F.bp (T.ta s Φ) (T.taDag (-s') Φ)
                  + bA E s k * F.bp (T.taDag (-s) Φ) (T.ta s' Φ)
                  + bA E s k * bA E s' k * F.bp (T.taDag (-s) Φ) (T.taDag (-s') Φ)|
                ≤ (bm K₀ E + bm K₀ E ^ 2)
                  * ((F.bp (T.ta s Φ) (T.ta s Φ) + F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ))
                    + (F.bp (T.ta s' Φ) (T.ta s' Φ) + F.bp (T.taDag (-s') Φ) (T.taDag (-s') Φ))) := by
              nlinarith [hmono, e1, e2, e3, hbm0,
                F.bp_nonneg (T.ta s Φ), F.bp_nonneg (T.ta s' Φ),
                F.bp_nonneg (T.taDag (-s) Φ), F.bp_nonneg (T.taDag (-s') Φ)]
            calc E.fL s * E.fL s' * E.hatChiSq (s' - s)
                  * (bA E s' k * F.bp (T.ta s Φ) (T.taDag (-s') Φ)
                    + bA E s k * F.bp (T.taDag (-s) Φ) (T.ta s' Φ)
                    + bA E s k * bA E s' k * F.bp (T.taDag (-s) Φ) (T.taDag (-s') Φ))
                ≤ |E.fL s * E.fL s' * E.hatChiSq (s' - s)
                    * (bA E s' k * F.bp (T.ta s Φ) (T.taDag (-s') Φ)
                      + bA E s k * F.bp (T.taDag (-s) Φ) (T.ta s' Φ)
                      + bA E s k * bA E s' k * F.bp (T.taDag (-s) Φ) (T.taDag (-s') Φ))| :=
                  le_abs_self _
              _ = |E.fL s * E.fL s' * E.hatChiSq (s' - s)|
                    * |bA E s' k * F.bp (T.ta s Φ) (T.taDag (-s') Φ)
                      + bA E s k * F.bp (T.taDag (-s) Φ) (T.ta s' Φ)
                      + bA E s k * bA E s' k * F.bp (T.taDag (-s) Φ) (T.taDag (-s') Φ)| := by
                  rw [abs_mul]
              _ = E.fL s * E.fL s' * |E.hatChiSq (s' - s)|
                    * |bA E s' k * F.bp (T.ta s Φ) (T.taDag (-s') Φ)
                      + bA E s k * F.bp (T.taDag (-s) Φ) (T.ta s' Φ)
                      + bA E s k * bA E s' k * F.bp (T.taDag (-s) Φ) (T.taDag (-s') Φ)| := by
                  rw [abs_mul, abs_mul, abs_of_nonneg hfs, abs_of_nonneg hfs']
              _ ≤ E.fL s * E.fL s' * |E.hatChiSq (s' - s)|
                    * ((bm K₀ E + bm K₀ E ^ 2)
                      * ((F.bp (T.ta s Φ) (T.ta s Φ) + F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ))
                        + (F.bp (T.ta s' Φ) (T.ta s' Φ) + F.bp (T.taDag (-s') Φ) (T.taDag (-s') Φ)))) :=
                  mul_le_mul_of_nonneg_left hkey
                    (mul_nonneg (mul_nonneg hfs hfs') (abs_nonneg _))
    _ ≤ (bm K₀ E + bm K₀ E ^ 2) * ((K₀ + 1) * (TA F T E Φ + TB F T E Φ)
          + (K₀ + 1) * (TA F T E Φ + TB F T E Φ)) := by
        have := hpair
        rw [hsumU] at this
        exact this
    _ = 2 * (K₀ + 1) * (bm K₀ E + bm K₀ E ^ 2) * (TA F T E Φ + TB F T E Φ) := by ring


end Est1

end Work.BoseC3QAll
