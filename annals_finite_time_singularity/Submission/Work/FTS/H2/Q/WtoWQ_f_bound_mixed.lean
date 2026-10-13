import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.DthIter_mul_smoothQuad
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.Elliptic.WtoW_f_bound
import Submission.Work.Elliptic.WtoW_pzIter_sum_theta
import Submission.Work.Spaces.WlInf_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Q

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.Spaces

/-! ## The Leibniz expansion of `D_θ^{b+1} f` on the open quadrant

`D_θ f = sin(2θ)·∂_θ f`, so the `b`-th iterate of `D_θ` on this product expands by the
binomial convolution of `D_θ`, and `D_θ^i (sin 2·) = sin(2θ)·γ_i(θ)` with `γ_i = sigCoeff i`.
This is the `SmoothQuad` counterpart of `Work.Elliptic.WtoW_f_expand` (which needs the
analyticity hypothesis `SmoothNbhd`, unavailable for the cut-off data of the route). -/

/-- **Leibniz expansion of `D_θ^{b+1} f`**, in the genuine `C^∞` class on the open quadrant:
for `SmoothQuad f` and `b ≤ 3`, at every interior angle,

`D_θ^{b+1} f z θ = Σ_{i ≤ b} C(b,i)·(sin(2θ)·γ_i(θ))·D_θ^{b-i}(∂_θ f) z θ`. -/
theorem DthIter_succ_expand_quad {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    (b : ℕ) (hb : b ≤ 3) :
    ∀ z ∈ Set.Ioi (-1), ∀ θ ∈ Set.Ioo 0 (π / 2),
      DthIter (b + 1) f z θ
        = ∑ i ∈ Finset.range (b + 1),
            ((b.choose i : ℝ) * (Real.sin (2 * θ) * Work.Elliptic.sigCoeff i θ))
              * DthIter (b - i) (pth f) z θ := by
  intro z hz θ hθ
  have hDth1 : DthIter 1 f = Dth f := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, DthIter_succ, DthIter_zero]
  have hstep1 : DthIter (b + 1) f = DthIter b (Dth f) := by
    rw [← hDth1]; exact (DthIter_add_right b 1 f).symm
  rw [hstep1]
  have hpth : Work.FTS.LocData.SmoothQuad (pth f) :=
    Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU hsm
  have hg : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' : ℝ => Real.sin (2 * θ'))
      (Set.Ioo 0 (π / 2)) :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffOn
  have hf : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' : ℝ => pth f z θ')
      (Set.Ioo 0 (π / 2)) := hpth.curry_θ hz
  have hlei := Work.FTS.LocData.DthIter_mul_smoothQuad b (fun z θ => Real.sin (2 * θ)) (pth f)
    hθ hg hf
  rw [show Dth f = fun z θ => Real.sin (2 * θ) * pth f z θ from rfl]
  rw [hlei]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi3 : i ≤ 3 := by have := Finset.mem_range.mp hi; omega
  rw [Work.Elliptic.WtoW_f_DthIter_sin_two_eq i hi3 z θ]
  ring

/-- **`∂_z^c` pushed through the Leibniz expansion.**  The angular coefficients
`C(b,i)·sin(2θ)·γ_i(θ)` do not depend on `z`, and the `z`-slices of `D_θ^{b-i}(∂_θ f)` are
`C^∞` on `Ioi (-1)` (for interior `θ`), so `pzIter c` may be pushed inside the finite sum. -/
theorem pzIter_DthIter_expand_quad {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f)
    (b c : ℕ) (hb : b ≤ 3) :
    ∀ z ∈ Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      pzIter c (DthIter (b + 1) f) z θ
        = ∑ i ∈ Finset.range (b + 1),
            ((b.choose i : ℝ) * (Real.sin (2 * θ) * Work.Elliptic.sigCoeff i θ))
              * pzIter c (DthIter (b - i) (pth f)) z θ := by
  intro z hz θ hθ
  have hz1 : (-1 : ℝ) < z := by have h0 : (0 : ℝ) ≤ z := hz; linarith
  have hpth : Work.FTS.LocData.SmoothQuad (pth f) :=
    Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU hsm
  have hloc : (fun z' => DthIter (b + 1) f z' θ)
      =ᶠ[𝓝 z] (fun z' => ∑ i ∈ Finset.range (b + 1),
            ((b.choose i : ℝ) * (Real.sin (2 * θ) * Work.Elliptic.sigCoeff i θ))
              * DthIter (b - i) (pth f) z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz1] with z' hz'
    exact DthIter_succ_expand_quad hsm b hb z' hz' θ hθ
  have hpz : pzIter c (DthIter (b + 1) f) z θ
      = pzIter c (fun z θ => ∑ i ∈ Finset.range (b + 1),
            ((b.choose i : ℝ) * (Real.sin (2 * θ) * Work.Elliptic.sigCoeff i θ))
              * DthIter (b - i) (pth f) z θ) z θ := by
    rw [pzIter_eq_iteratedDeriv, pzIter_eq_iteratedDeriv]
    exact hloc.iteratedDeriv_eq c
  rw [hpz]
  exact Work.Elliptic.WtoW_pzIter_sum_theta (Finset.range (b + 1))
    (fun i θ' => (b.choose i : ℝ) * (Real.sin (2 * θ') * Work.Elliptic.sigCoeff i θ'))
    (fun i => DthIter (b - i) (pth f)) c (fun i _ =>
      (((hpth.DthIter (b - i)).curry_z hθ).contDiffAt (isOpen_Ioi.mem_nhds hz1)).of_le
        (by simp [Work.Stability.smoothOrder]))

/-- **The `f`-side bound of `WtoWQ` for the angular slots (`a ≥ 1`).**  For `f` smooth on
the open quadrant (`SmoothQuad`), vanishing on the two angular boundary lines and with
`∂_θ f ∈ 𝒲^{4,∞}`, every mixed derivative with at least one `θ`-derivative,
`(z+1)^c ∂_z^c D_θ^a f` (`a ≥ 1`, `c + a ≤ 4`), is bounded by
`K |∂_θ f|_{𝒲^{4,∞}} sin(2θ)` on `[0,∞) × [0,π/2]`, with universal `K`.

The pointwise identity behind it is the Leibniz expansion
`D_θ^{a} f = D_θ^{a-1}(sin(2θ) · ∂_θ f) = Σ_{i ≤ a-1} C(a-1,i) · (sin(2θ)·γ_i(θ)) · D_θ^{a-1-i}(∂_θ f)`
where `γ_i = sigCoeff i` is the bounded angular coefficient with
`D_θ^i (sin 2·) = sin(2θ)·γ_i` (`Work.Elliptic.WtoW_f_DthIter_sin_two_eq`,
`Work.Elliptic.WtoW_f_sigCoeff_bound`); this holds at every interior angle from the Leibniz
rule for `D_θ` in the genuine `C^∞` order (`Work.Spaces.DthIter_mul` /
`Submission.Work.FTS.LocData.DthIter_mul_smoothQuad` / `Work.FTS.H2.HQ.mixed_mul_eq_quad`)
applied to `sin(2θ)` and `∂_θ f` (both `SmoothQuad` there).  Each summand is pushed through
`∂_z^c` by `Work.Elliptic.WtoW_pzIter_sum_theta` (coefficients do not depend on `z`; the
`z`-slices of `D_θ^{a-1-i}(∂_θ f)` are smooth on `Ioi (-1)` for interior `θ`, from
`SmoothQuad.curry_z`), and bounded by `Work.Elliptic.WtoW_f_term`,
`|(z+1)^c ∂_z^c D_θ^j (∂_θ f)| ≤ 2 |∂_θ f|_𝒲`, which uses only `WlInfMem`.  The sum over
`i ≤ a-1 ≤ 3` of `C(a-1,i)·48·sin(2θ)·2|∂_θ f|_𝒲` is `≤ 16·48·2·|∂_θ f|_𝒲·sin(2θ)`.
At `θ = 0, π/2` both sides vanish identically (`D_θ^a` carries a factor `sin(2θ)` for
`a ≥ 1`, `Work.Spaces.pzIter_DthIter_eq_zero_of_sin_eq_zero`), and the `z = 0` case
follows by continuity in `z` (`(0,θ)` is interior for `θ ∈ (0,π/2)`). -/
theorem WtoWQ_f_bound_mixed : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.LocData.SmoothQuad f → Work.Spaces.VanishTheta f →
    Work.Spaces.WlInfMem α 4 (Work.Spaces.pth f) →
    ∀ (c a : ℕ), 1 ≤ a → c + a ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ c * Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ|
        ≤ K * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) * Real.sin (2 * θ) := by
  refine ⟨1000, by norm_num, ?_⟩
  intro α f hα hα1 hsm hv hmem c a ha hca z hz θ hθ
  have hWnn : 0 ≤ Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 (Work.Spaces.pth f) hmem)
      (Work.Spaces.wlThSum_nonneg α 4 (Work.Spaces.pth f) hmem)
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hb3 : b ≤ 3 := by omega
  rcases eq_or_lt_of_le hθ.1 with hθzero | hθpos
  · -- `θ = 0`: both sides vanish
    have hsin0 : Real.sin (2 * θ) = 0 := by rw [← hθzero]; simp
    have hzero := Work.Spaces.pzIter_DthIter_eq_zero_of_sin_eq_zero f b hsin0 c z
    rw [hzero, mul_zero, abs_zero, hsin0, mul_zero]
  · rcases eq_or_lt_of_le hθ.2 with hθpi | hθlt
    · -- `θ = π/2`: both sides vanish
      have hsinpi : Real.sin (2 * θ) = 0 := by
        rw [hθpi, show 2 * (π / 2) = π by ring, Real.sin_pi]
      have hzero := Work.Spaces.pzIter_DthIter_eq_zero_of_sin_eq_zero f b hsinpi c z
      rw [hzero, mul_zero, abs_zero, hsinpi, mul_zero]
    · -- interior angle: the Leibniz expansion and the termwise bound
      have hθQ : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθpos, hθlt⟩
      have hsnn : 0 ≤ Real.sin (2 * θ) := Work.Elliptic.WtoW_sin2_nonneg hθ
      rw [pzIter_DthIter_expand_quad hsm b c hb3 z hz θ hθQ]
      have hfac : (z + 1) ^ c * (∑ i ∈ Finset.range (b + 1),
            ((b.choose i : ℝ) * (Real.sin (2 * θ) * Work.Elliptic.sigCoeff i θ))
              * pzIter c (DthIter (b - i) (pth f)) z θ)
          = ∑ i ∈ Finset.range (b + 1),
              ((b.choose i : ℝ) * (Real.sin (2 * θ) * Work.Elliptic.sigCoeff i θ))
                * ((z + 1) ^ c * pzIter c (DthIter (b - i) (pth f)) z θ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hfac]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hsum2 : (∑ i ∈ Finset.range (b + 1),
            |((b.choose i : ℝ) * (Real.sin (2 * θ) * Work.Elliptic.sigCoeff i θ))
                * ((z + 1) ^ c * pzIter c (DthIter (b - i) (pth f)) z θ)|)
          ≤ ∑ i ∈ Finset.range (b + 1),
              ((b.choose i : ℝ) * 48 * Real.sin (2 * θ))
                * (2 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi3 : i ≤ 3 := by have := Finset.mem_range.mp hi; omega
        have h1 : |((b.choose i : ℝ) * (Real.sin (2 * θ) * Work.Elliptic.sigCoeff i θ))|
            ≤ (b.choose i : ℝ) * 48 * Real.sin (2 * θ) := by
          have hbs : |Work.Elliptic.sigCoeff i θ| ≤ 48 :=
            Work.Elliptic.WtoW_f_sigCoeff_bound i hi3 θ
          have hbc : |((b.choose i : ℝ))| = (b.choose i : ℝ) :=
            abs_of_nonneg (by positivity)
          have hs2 : |Real.sin (2 * θ) * Work.Elliptic.sigCoeff i θ|
              ≤ Real.sin (2 * θ) * 48 := by
            rw [abs_mul, abs_of_nonneg hsnn]
            exact mul_le_mul_of_nonneg_left hbs hsnn
          rw [abs_mul, hbc]
          calc (b.choose i : ℝ) * |Real.sin (2 * θ) * Work.Elliptic.sigCoeff i θ|
              ≤ (b.choose i : ℝ) * (Real.sin (2 * θ) * 48) :=
                mul_le_mul_of_nonneg_left hs2 (by positivity)
            _ = (b.choose i : ℝ) * 48 * Real.sin (2 * θ) := by ring
        have h2 : |(z + 1) ^ c * pzIter c (DthIter (b - i) (pth f)) z θ|
            ≤ 2 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) :=
          Work.Elliptic.WtoW_f_term α f hα hα1 hmem (b - i) c (by omega) (by omega) z hz θ hθ
        have hCi : (0 : ℝ) ≤ (b.choose i : ℝ) * 48 * Real.sin (2 * θ) :=
          mul_nonneg (mul_nonneg (by positivity) (by norm_num)) hsnn
        rw [abs_mul]
        exact mul_le_mul h1 h2 (abs_nonneg _) hCi
      refine le_trans hsum2 ?_
      have hsum3 : (∑ i ∈ Finset.range (b + 1),
            ((b.choose i : ℝ) * 48 * Real.sin (2 * θ))
              * (2 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)))
          ≤ 768 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) * Real.sin (2 * θ) := by
        have h1 : (∑ i ∈ Finset.range (b + 1),
              ((b.choose i : ℝ) * 48 * Real.sin (2 * θ))
                * (2 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)))
            = (∑ i ∈ Finset.range (b + 1), (b.choose i : ℝ))
                * (96 * Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [h1]
        have hcast : (∑ i ∈ Finset.range (b + 1), (b.choose i : ℝ)) = (2 : ℝ) ^ b := by
          rw [← Nat.cast_sum, Nat.sum_range_choose]
          push_cast
          ring
        rw [hcast]
        have hb2 : (2 : ℝ) ^ b ≤ 8 := by
          calc (2 : ℝ) ^ b ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hb3
            _ = 8 := by norm_num
        have hXnn : 0 ≤ 96 * Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) :=
          mul_nonneg (mul_nonneg (by norm_num) hsnn) hWnn
        calc (2 : ℝ) ^ b * (96 * Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f))
            ≤ 8 * (96 * Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) :=
              mul_le_mul_of_nonneg_right hb2 hXnn
          _ = 768 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) * Real.sin (2 * θ) := by ring
      refine le_trans hsum3 ?_
      have hsM : 0 ≤ Work.Spaces.WlInf α 4 (Work.Spaces.pth f) * Real.sin (2 * θ) :=
        mul_nonneg hWnn hsnn
      nlinarith [hsM]

end Work.FTS.H2.Q
