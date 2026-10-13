/-
# `Work.FTS.LocData.Main` — the localised datum, and its smallness in `𝓗⁴`

This is the main module of the localised-data chapter (node **N9** of `FTS_AUDIT_LEAD.md` §4):
the profile `F_*` of the self-similar ansatz is replaced by the localised datum

  `locData α L β hLoc = F_*·χ(·/L) + β·hLoc`,   `hLoc α z θ = φ(z)·Γ(θ)`,  `φ = χ(4· - 5)`,

where `χ` is the explicit cut-off of `Work.Stability.Cutoff`.  The point of the node is that
localisation changes **only the initial data**:

* `locData` vanishes for `z ≥ 2L`, so the *physical* vorticity `x ↦ F(ρ(x)^p,θ(x))·e_θ(x)` is
  compactly supported (`locData_compactSupport`) and every far-field clause of the challenge
  becomes trivial;
* the perturbation `g = locData - F_* = -zfar L F_* + β·hLoc` of the modulation is *small* in the
  weighted norm `HkNorm α 4` and can be made `L₁₂`-orthogonal at `z = 0` by the single scalar
  `β = L₁₂(zfar L F_*)(0) / L₁₂(hLoc)(0)`;
* `g` is an admissible datum in the sense of `DataAdm` (`dataAdm_locG`).

## The chain of estimates

| quantity | bound | module |
|---|---|---|
| `HkIntegrand α 4 F_*` | `≤ 10⁴ α² angMaj/(z²)` | `HkIntegrand_Fstar_le` |
| `HkIntegrand α 4 (zfar L F_*)` | `≤ 10⁵ α² angMaj/(1+z)²` | `HkIntegrand_zfar_Fstar_le` |
| `HkSq α 4 (zfar L F_*)` | `≤ C·α/L` | `HkSq_zfar_Fstar_le` |
| `HkIntegrand α 4 (hLoc α)` | `≤ K² angMaj/(1+z)²` | `HkIntegrand_hLoc_le` |
| `HkSq α 4 (hLoc α)` | `≤ C` | `HkMem_hLoc_direct` |
| `|L₁₂(zfar L F_*)(0)|` | `≤ 4α/L` | `L12_zfar_Fstar_abs_le` |
| `L₁₂(hLoc α)(0)` | `> 0` | `L12_hLoc` |

The two square roots combine as `√(a+b) ≤ √a + √b`, and the `L^{-1/2}`-decay of the tail together
with `β = O(1/L)` makes *both* the `𝓗⁴`-distance from `F_*` and `|β|` smaller than any prescribed
`ε > 0` once `L` is large.  Nothing in the chapter assumes regularity at or past a blow-up time:
`locData` is a datum, not a solution.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.HkIntegrand_neg
import Submission.Work.FTS.LocData.HkIntegrand_const_mul
import Submission.Work.FTS.LocData.HkIntegrand_add_le
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.LocData.HkSq_const_mul
import Submission.Work.FTS.LocData.HkSq_add_le
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.LocData.angMaj_mem
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.HkIntegrand_hLoc_le
import Submission.Work.Stability.HkSqZfar
import Submission.Work.FTS.LocData.L12_hLoc
import Submission.Work.FTS.LocData.L12_zfar_Fstar_abs_le
import Submission.Work.FTS.LocData.L12_locG
import Submission.Work.FTS.LocData.SmoothQuad_locG
import Submission.Work.FTS.LocData.SmoothQuad_hLoc
import Submission.Work.FTS.LocData.hLoc_vanishing
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocData.vanishTheta_locG
import Submission.Work.FTS.LocData.profileZeroFar_locData
import Submission.Work.FTS.LocData.omegaProfile_compact
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## `ℋ^k`-bookkeeping -/

/-- Negation preserves `ℋ^k`-membership. -/
theorem HkMem_neg (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (fun z θ => -f z θ) := by
  constructor
  · intro z hz
    refine IntegrableOn.congr_fun (hf.1 z hz) (fun θ _ => ?_) measurableSet_Icc
    exact (HkIntegrand_neg α k f z θ).symm
  · have h : (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => -f z θ) z θ)
        = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
      funext z
      rw [funext (fun θ => HkIntegrand_neg α k f z θ)]
    rw [h]
    exact hf.2

/-- The `ℋ^k`-functional is invariant under negation. -/
theorem HkSq_neg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k (fun z θ => -f z θ) = Work.Spaces.HkSq α k f := by
  simp only [Work.Spaces.HkSq]
  exact setIntegral_congr_fun measurableSet_Ici
    (fun z _ => setIntegral_congr_fun measurableSet_Icc
      (fun θ _ => HkIntegrand_neg α k f z θ))

/-- **`HkSq` is subadditive** for `ℋ^k`-functions: `|a+b|² ≤ 2|a|² + 2|b|²`. -/
theorem HkSq_sub_le (α : ℝ) (k : ℕ) {a b : ℝ → ℝ → ℝ} (hsa : SmoothQuad a)
    (hsb : SmoothQuad b) (ha : Work.Spaces.HkMem α k a) (hb : Work.Spaces.HkMem α k b) :
    Work.Spaces.HkSq α k (fun z θ => a z θ - b z θ)
      ≤ 2 * Work.Spaces.HkSq α k a + 2 * Work.Spaces.HkSq α k b := by
  have h := HkSq_add_le α k hsa (smoothQuad_neg hsb) ha (HkMem_neg α k hb)
  have heq : (fun z θ => a z θ + -b z θ) = (fun z θ => a z θ - b z θ) := by
    funext z θ; ring
  rw [heq] at h
  rwa [HkSq_neg] at h

/-! ## The localised perturbation of the profile -/

/-- The far part `zfar L F_*` of the reference profile is `C^∞` on the quadrant (product of the
cut-off factor `1 - χ(·/L)` with `F_*`). -/
theorem SmoothQuad_zfar_Fstar (α L : ℝ) :
    SmoothQuad (Work.Stability.zfar L (Work.Construction.Fstar α)) := by
  have hone : SmoothQuad (fun _ _ : ℝ => (1 : ℝ)) :=
    smoothQuad_of_contDiffOn_uncurry contDiffOn_const
  have hchi : SmoothQuad (fun z θ => (1 : ℝ) - Work.Stability.chi (z / L)) :=
    smoothQuad_sub hone (SmoothQuad_chi_div L)
  have hmain : (fun z θ => (1 - Work.Stability.chi (z / L)) * Work.Construction.Fstar α z θ)
      = Work.Stability.zfar L (Work.Construction.Fstar α) := by
    funext z θ
    rw [Work.Stability.zfar_apply]
  rw [← hmain]
  exact smoothQuad_mul hchi (Fstar_smoothQuad α)

/-- `locG` as a sum: `locG α L β h = -zfar L F_* + β·h`. -/
theorem locG_as_sum (α L β : ℝ) (h : ℝ → ℝ → ℝ) :
    locG α L β h
      = fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α)) z θ + β * h z θ := by
  funext z θ
  exact locG_eq_zfar α L β h z θ

/-- **The pointwise majorant of the `ℋ⁴`-integrand of `locG`.**  If `K² angMaj/(1+z)²` dominates
the `ℋ⁴`-integrand of the bump `hLoc α`, then `(2·10⁵ α² + 2β²K²)·angMaj/(1+z)²` dominates the
`ℋ⁴`-integrand of `locG α L β (hLoc α)`. -/
theorem HkIntegrand_locG_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {L β K Cz : ℝ} (hL : 1 ≤ L)
    (hCz : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
        ≤ Cz * α ^ 2 * angMaj α θ / (1 + z) ^ 2)
    (hK : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (hLoc α) z θ ≤ K ^ 2 * angMaj α θ / (1 + z) ^ 2)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 4 (locG α L β (hLoc α)) z θ
      ≤ (2 * Cz * α ^ 2 + 2 * β ^ 2 * K ^ 2) * angMaj α θ / (1 + z) ^ 2 := by
  rw [locG_as_sum]
  have hsq : SmoothQuad (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α)) z θ) :=
    smoothQuad_neg (SmoothQuad_zfar_Fstar α L)
  have hsq2 : SmoothQuad (fun z θ => β * hLoc α z θ) := smoothQuad_const_mul β (SmoothQuad_hLoc α)
  have hstep := HkIntegrand_add_le α 4 hsq hsq2 hz hθ
  have hneg : Work.Spaces.HkIntegrand α 4
      (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α)) z θ) z θ
      = Work.Spaces.HkIntegrand α 4
          (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ :=
    HkIntegrand_neg α 4 (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
  have hcm : Work.Spaces.HkIntegrand α 4 (fun z θ => β * hLoc α z θ) z θ
      = β ^ 2 * Work.Spaces.HkIntegrand α 4 (hLoc α) z θ :=
    HkIntegrand_const_mul α 4 β (hLoc α) z θ
  have hzfar := hCz z hz θ hθ
  have hbump := hK z hz θ hθ
  have hang : 0 ≤ angMaj α θ := angMaj_nonneg hθ
  have hden : 0 < (1 + z) ^ 2 := pow_pos (by linarith [show (0:ℝ) ≤ z from hz]) 2
  rw [hneg, hcm] at hstep
  refine le_trans hstep ?_
  have h1 : 2 * Work.Spaces.HkIntegrand α 4
        (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
      ≤ 2 * (Cz * α ^ 2 * angMaj α θ / (1 + z) ^ 2) := by linarith
  have h2 : 2 * (β ^ 2 * Work.Spaces.HkIntegrand α 4 (hLoc α) z θ)
      ≤ 2 * (β ^ 2 * (K ^ 2 * angMaj α θ / (1 + z) ^ 2)) := by
    have hβ2 : 0 ≤ β ^ 2 := sq_nonneg β
    nlinarith [hbump, hβ2, hang, hden]
  have h3 : 2 * (Cz * α ^ 2 * angMaj α θ / (1 + z) ^ 2)
      + 2 * (β ^ 2 * (K ^ 2 * angMaj α θ / (1 + z) ^ 2))
      = (2 * Cz * α ^ 2 + 2 * β ^ 2 * K ^ 2) * angMaj α θ / (1 + z) ^ 2 := by
    ring
  linarith [h1, h2, h3]

/-- The majorant `c·angMaj α θ/(1+z)²` is integrable in `θ` for every `z ∈ Iz`, and its
`z`-integral is integrable on `Iz`. -/
theorem integrableOn_angMaj_majorant (α c : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (∀ z ∈ Work.Spaces.Iz,
        IntegrableOn (fun θ => c * angMaj α θ / (1 + z) ^ 2) Work.Spaces.Iθ) ∧
      IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, c * angMaj α θ / (1 + z) ^ 2)
        Work.Spaces.Iz := by
  obtain ⟨hint, hbound⟩ := angMaj_mem α hα hα1
  have hbound' : ∫ θ in Work.Spaces.Iθ, angMaj α θ ≤ 1000 / (3 * α) + 10001 := hbound
  constructor
  · intro z hz
    have h3 : IntegrableOn (fun θ => (c / (1 + z) ^ 2) * angMaj α θ) Work.Spaces.Iθ :=
      hint.const_mul (c / (1 + z) ^ 2)
    refine h3.congr_fun (fun θ _ => ?_) measurableSet_Icc
    ring
  · have hbase : IntegrableOn (fun x : ℝ => (x + 1) ^ (-2 : ℝ)) (Set.Ioi (0 : ℝ)) :=
      integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (by norm_num) (by norm_num)
    have hconst : IntegrableOn (fun x : ℝ => (∫ θ in Work.Spaces.Iθ, c * angMaj α θ)
        * (x + 1) ^ (-2 : ℝ)) (Set.Ioi (0 : ℝ)) :=
      hbase.const_mul _
    have hval : ∫ θ in Work.Spaces.Iθ, c * angMaj α θ
        = c * ∫ θ in Work.Spaces.Iθ, angMaj α θ := integral_const_mul c _
    have heq : ∀ z ∈ Set.Ioi (0 : ℝ),
        (∫ θ in Work.Spaces.Iθ, c * angMaj α θ / (1 + z) ^ 2)
          = (∫ θ in Work.Spaces.Iθ, c * angMaj α θ) * (z + 1) ^ (-2 : ℝ) := by
      intro z hz
      have hzpos : (0 : ℝ) < z + 1 := by linarith [Set.mem_Ioi.mp hz]
      rw [show (fun θ => c * angMaj α θ / (1 + z) ^ 2)
          = fun θ => (c * angMaj α θ) * (z + 1) ^ (-2 : ℝ) from by
        funext θ
        rw [show ((z + 1) ^ (-2 : ℝ)) = ((z + 1) ^ 2)⁻¹ by
          rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg (le_of_lt hzpos),
            Real.rpow_two]]
        ring]
      rw [integral_mul_const]
    have hfin : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, c * angMaj α θ / (1 + z) ^ 2)
        (Set.Ioi (0 : ℝ)) :=
      hconst.congr_fun (fun z hz => (heq z hz).symm) measurableSet_Ioi
    rw [Work.Spaces.Iz]
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr hfin

/-- **`locG α L β (hLoc α)` lies in `ℋ⁴`** (with `L ≥ 1`): the localised perturbation is
dominated by the integrable majorant `(2·10⁵ α² + 2β²K²)·angMaj α θ/(1+z)²`. -/
theorem HkMem_locG (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {L β K Cz : ℝ} (hL : 1 ≤ L)
    (hCz : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
        ≤ Cz * α ^ 2 * angMaj α θ / (1 + z) ^ 2)
    (hK : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (hLoc α) z θ ≤ K ^ 2 * angMaj α θ / (1 + z) ^ 2) :
    Work.Spaces.HkMem α 4 (locG α L β (hLoc α)) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 4 (locG α L β (hLoc α)) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_HkIntegrand_smoothQuad α 4 _ (SmoothQuad_locG α L β hα hα1 (SmoothQuad_hLoc α))
  refine HkMem_of_majorant (f := locG α L β (hLoc α))
    (M := fun z θ => (2 * Cz * α ^ 2 + 2 * β ^ 2 * K ^ 2) * angMaj α θ / (1 + z) ^ 2)
    α 4 hcont ?_ ?_ ?_
  · exact (integrableOn_angMaj_majorant α (2 * Cz * α ^ 2 + 2 * β ^ 2 * K ^ 2) hα hα1).1
  · exact (integrableOn_angMaj_majorant α (2 * Cz * α ^ 2 + 2 * β ^ 2 * K ^ 2) hα hα1).2
  · intro z hz θ hθ
    exact HkIntegrand_locG_le α hα hα1 hL hCz hK hz hθ

/-- **`zfar L F_* ∈ ℋ⁴`.**  The far part of the reference profile is dominated pointwise by the
integrable majorant `10⁵α²·angMaj α θ/(1+z)²` (`HkIntegrand_zfar_Fstar_le`); this is the `ℋ⁴`
membership of the localised tail.  (The sibling module `HkMem_zfar_Fstar` states the same fact.) -/
theorem HkMem_zfar_Fstar_direct (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {L : ℝ} (hL : 1 ≤ L) :
    Work.Spaces.HkMem α 4 (Work.Stability.zfar L (Work.Construction.Fstar α)) := by
  obtain ⟨Cz, -, hCz⟩ := HkIntegrand_zfar_Fstar_le
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4
      (Work.Stability.zfar L (Work.Construction.Fstar α)) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_HkIntegrand_smoothQuad α 4 _ (SmoothQuad_zfar_Fstar α L)
  refine HkMem_of_majorant
    (f := Work.Stability.zfar L (Work.Construction.Fstar α))
    (M := fun z θ => (Cz * α ^ 2) * angMaj α θ / (1 + z) ^ 2)
    α 4 hcont ?_ ?_ ?_
  · exact (integrableOn_angMaj_majorant α (Cz * α ^ 2) hα hα1).1
  · exact (integrableOn_angMaj_majorant α (Cz * α ^ 2) hα hα1).2
  · intro z hz θ hθ
    have h := hCz α hα hα1 L hL z hz θ hθ
    calc Work.Spaces.HkIntegrand α 4
          (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
        ≤ Cz * α ^ 2 * angMaj α θ / (1 + z) ^ 2 := h
      _ = (Cz * α ^ 2) * angMaj α θ / (1 + z) ^ 2 := by ring

/-- **`hLoc α ∈ ℋ⁴`**: domination of the `ℋ⁴`-integrand of the bump by the integrable majorant
`K²·angMaj α θ/(1+z)²` (`HkIntegrand_hLoc_le`). -/
theorem HkMem_hLoc_direct (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {K : ℝ}
    (hK : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (hLoc α) z θ ≤ K ^ 2 * angMaj α θ / (1 + z) ^ 2) :
    Work.Spaces.HkMem α 4 (hLoc α) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 (hLoc α) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_HkIntegrand_smoothQuad α 4 _ (SmoothQuad_hLoc α)
  refine HkMem_of_majorant (f := hLoc α) (M := fun z θ => K ^ 2 * angMaj α θ / (1 + z) ^ 2)
    α 4 hcont ?_ ?_ ?_
  · exact (integrableOn_angMaj_majorant α (K ^ 2) hα hα1).1
  · exact (integrableOn_angMaj_majorant α (K ^ 2) hα hα1).2
  · intro z hz θ hθ
    exact hK z hz θ hθ

/-- **The `L^{-1}`-decay of the far part in `ℋ⁴`**: there is `C` with
`HkSq α 4 (zfar L F_*) ≤ C·α/L` for `L ≥ 1`.  This is the pointwise majorant
`HkIntegrand_zfar_Fstar_le` fed into the far-tail bound `Work.Stability.HkSqZfar`. -/
theorem HkSq_zfar_Fstar_le_direct (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, ∀ L : ℝ, 1 ≤ L →
      Work.Spaces.HkSq α 4 (Work.Stability.zfar L (Work.Construction.Fstar α)) ≤ C * α / L := by
  obtain ⟨Cz, hCznn, hCz⟩ := HkIntegrand_zfar_Fstar_le
  have hslice := (integrableOn_angMaj_majorant α (Cz * α ^ 2) hα hα1).1
  have hCang : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, angMaj α θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => angMaj_nonneg hθ)
  refine ⟨Cz * (∫ θ in Work.Spaces.Iθ, angMaj α θ), fun L hL => ?_⟩
  have hLpos : 0 < L := by linarith
  have hMnn : (0 : ℝ) ≤ Cz * α ^ 2 * (∫ θ in Work.Spaces.Iθ, angMaj α θ) :=
    mul_nonneg (mul_nonneg hCznn (sq_nonneg α)) hCang
  have hmajint : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
        (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ)
        ≤ (Cz * α ^ 2 * (∫ θ in Work.Spaces.Iθ, angMaj α θ)) / z ^ 2 := by
    intro z hz
    by_cases hzL : z < L
    · have hzero : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
          (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ) = 0 :=
        Work.Stability.integral_HkIntegrand_zfar_eq_zero (α := α) (k := 4) (Z := L) hLpos
          ⟨hz, hzL⟩
      rw [hzero]
      positivity
    · push_neg at hzL
      have hle : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
            (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ)
          ≤ ∫ θ in Work.Spaces.Iθ, Cz * α ^ 2 * angMaj α θ / (1 + z) ^ 2 := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ))
          (hslice z hz) ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact hCz α hα hα1 L hL z hz θ hθ
      have hval : (∫ θ in Work.Spaces.Iθ, Cz * α ^ 2 * angMaj α θ / (1 + z) ^ 2)
          = (Cz * α ^ 2 / (1 + z) ^ 2) * (∫ θ in Work.Spaces.Iθ, angMaj α θ) := by
        rw [show (fun θ => Cz * α ^ 2 * angMaj α θ / (1 + z) ^ 2)
            = fun θ => (Cz * α ^ 2 / (1 + z) ^ 2) * angMaj α θ from by funext θ; ring]
        rw [integral_const_mul]
      have hden : z ^ 2 ≤ (1 + z) ^ 2 := by nlinarith [hz]
      have hstep : (Cz * α ^ 2 / (1 + z) ^ 2) * (∫ θ in Work.Spaces.Iθ, angMaj α θ)
          ≤ (Cz * α ^ 2 * (∫ θ in Work.Spaces.Iθ, angMaj α θ)) / z ^ 2 := by
        have hA : (0 : ℝ) ≤ Cz * α ^ 2 * (∫ θ in Work.Spaces.Iθ, angMaj α θ) := hMnn
        have hz2 : (0 : ℝ) < z ^ 2 := by nlinarith [hzL]
        have hB : ((1 + z) ^ 2)⁻¹ ≤ (z ^ 2)⁻¹ := by
          have h := one_div_le_one_div_of_le hz2 hden
          simpa [one_div] using h
        calc (Cz * α ^ 2 / (1 + z) ^ 2) * (∫ θ in Work.Spaces.Iθ, angMaj α θ)
            = (Cz * α ^ 2 * (∫ θ in Work.Spaces.Iθ, angMaj α θ)) * ((1 + z) ^ 2)⁻¹ := by
              ring
          _ ≤ (Cz * α ^ 2 * (∫ θ in Work.Spaces.Iθ, angMaj α θ)) * (z ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_left hB hA
          _ = (Cz * α ^ 2 * (∫ θ in Work.Spaces.Iθ, angMaj α θ)) / z ^ 2 := by ring
      linarith [hle, hval.le, hval.ge, hstep]
  have hdom : Work.Stability.FarTailDom α 4
      (Real.sqrt (Cz * α ^ 2 * (∫ θ in Work.Spaces.Iθ, angMaj α θ))) L
      (Work.Construction.Fstar α) := by
    intro z hz hzL
    rw [Real.sq_sqrt hMnn]
    exact hmajint z hz
  have hkey := Work.Stability.HkSqZfar (α := α) (k := 4)
    (M := Real.sqrt (Cz * α ^ 2 * (∫ θ in Work.Spaces.Iθ, angMaj α θ))) (Z := L)
    (f := Work.Construction.Fstar α) hLpos (Real.sqrt_nonneg _) hdom
  rw [Real.sq_sqrt hMnn] at hkey
  refine le_trans hkey ?_
  have hα2 : α ^ 2 ≤ α := by nlinarith [hα, hα1]
  have hCL : (0 : ℝ) ≤ Cz * (∫ θ in Work.Spaces.Iθ, angMaj α θ) := mul_nonneg hCznn hCang
  have h1 : Cz * α ^ 2 * (∫ θ in Work.Spaces.Iθ, angMaj α θ)
      ≤ (Cz * (∫ θ in Work.Spaces.Iθ, angMaj α θ)) * α := by nlinarith [hα2, hCL, hα.le]
  have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt (inv_pos.mpr hLpos))
  simpa [div_eq_mul_inv] using h2

/-! ## The datum `g = locG` is admissible -/

/-- The bump `hLoc α = φ·Γ` vanishes for `z ≤ 3/4` (its radial factor is `χ(4· - 5)`). -/
theorem bumpZ_eq_zero_of_le {z : ℝ} (hz : z ≤ 3 / 4) : bumpZ z = 0 := by
  rw [bumpZ_apply, Work.Stability.chi_eq_zero]
  have h1 : 4 * z - 5 ≤ -2 := by linarith
  have h2 : |4 * z - 5| = -(4 * z - 5) := abs_of_nonpos (by linarith)
  rw [h2]; linarith

/-- The bump `hLoc α = φ·Γ` vanishes for `z ≥ 7/4`. -/
theorem bumpZ_eq_zero_of_ge {z : ℝ} (hz : 7 / 4 ≤ z) : bumpZ z = 0 := by
  rw [bumpZ_apply, Work.Stability.chi_eq_zero]
  have h1 : 4 * z - 5 ≥ 2 := by linarith
  have h2 : |4 * z - 5| = 4 * z - 5 := abs_of_nonneg (by linarith)
  rw [h2]; linarith

theorem hLoc_eq_zero_of_le (α : ℝ) {z : ℝ} (hz : z ≤ 3 / 4) (θ : ℝ) : hLoc α z θ = 0 := by
  rw [hLoc_apply, bumpZ_eq_zero_of_le hz, zero_mul]

theorem hLoc_eq_zero_of_ge (α : ℝ) {z : ℝ} (hz : 7 / 4 ≤ z) (θ : ℝ) : hLoc α z θ = 0 := by
  rw [hLoc_apply, bumpZ_eq_zero_of_ge hz, zero_mul]

/-- **`locG α L β (hLoc α)` is an admissible datum**: `C^∞` on the quadrant, vanishing on the
angular boundary and to second order at the axis `z = 0`, and honestly in `ℋ⁴`. -/
theorem dataAdm_locG (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {L β K Cz : ℝ} (hL : 1 ≤ L)
    (hCz : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
        ≤ Cz * α ^ 2 * angMaj α θ / (1 + z) ^ 2)
    (hK : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (hLoc α) z θ ≤ K ^ 2 * angMaj α θ / (1 + z) ^ 2) :
    DataAdm α (locG α L β (hLoc α)) := by
  refine ⟨SmoothQuad_locG α L β hα hα1 (SmoothQuad_hLoc α), ?_, ?_,
    HkMem_locG α hα hα1 hL hCz hK⟩
  · have hv := (hLoc_vanishing α hα).1
    exact vanishTheta_locG α L β hα hα1 (fun z => ⟨hv.1 z, hv.2 z⟩)
  · exact zero_slice_locG α L β hα hα1 (fun z θ hz => hLoc_eq_zero_of_le α hz θ) hL

/-- **The `ℋ⁴`-bound on the localised perturbation of the datum**: for `β = N/D`,
`HkNorm α 4 (locG α L β (hLoc α)) ≤ √(2C₀α/L) + √2·|β|·√C₁`, where `C₀` bounds
`L·HkSq α 4 (zfar L F_*)` and `C₁` bounds `HkSq α 4 (hLoc α)`. -/
theorem HkNorm_locG_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {L β C₀ C₁ : ℝ} (hL : 1 ≤ L)
    (hC₀nn : 0 ≤ C₀) (hC₁nn : 0 ≤ C₁)
    (hmemH : Work.Spaces.HkMem α 4 (hLoc α))
    (hC₀ : Work.Spaces.HkSq α 4 (Work.Stability.zfar L (Work.Construction.Fstar α))
      ≤ C₀ * α / L)
    (hC₁ : Work.Spaces.HkSq α 4 (hLoc α) ≤ C₁) :
    Work.Spaces.HkNorm α 4 (locG α L β (hLoc α))
      ≤ Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt 2 * |β| * Real.sqrt C₁ := by
  have hmemT : Work.Spaces.HkMem α 4 (Work.Stability.zfar L (Work.Construction.Fstar α)) :=
    HkMem_zfar_Fstar_direct α hα hα1 hL
  have hmeqb : Work.Spaces.HkMem α 4 (fun z θ => β * hLoc α z θ) :=
    HkMem_const_mul α 4 β hmemH
  -- the sum bound
  have hsum := HkSq_add_le α 4 (smoothQuad_neg (SmoothQuad_zfar_Fstar α L))
    (smoothQuad_const_mul β (SmoothQuad_hLoc α)) (HkMem_neg α 4 hmemT) hmeqb
  have heq : (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
      + β * hLoc α z θ) = locG α L β (hLoc α) := by
    funext z θ
    exact (locG_eq_zfar α L β (hLoc α) z θ).symm
  rw [heq] at hsum
  have hsq : Work.Spaces.HkSq α 4 (locG α L β (hLoc α))
      ≤ 2 * (C₀ * α / L) + 2 * β ^ 2 * C₁ := by
    have hneg : Work.Spaces.HkSq α 4
        (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α)) z θ)
        = Work.Spaces.HkSq α 4 (Work.Stability.zfar L (Work.Construction.Fstar α)) :=
      HkSq_neg α 4 _
    have hcm : Work.Spaces.HkSq α 4 (fun z θ => β * hLoc α z θ)
        = β ^ 2 * Work.Spaces.HkSq α 4 (hLoc α) := HkSq_const_mul α 4 β hmemH
    rw [hneg, hcm] at hsum
    have h1 : 2 * Work.Spaces.HkSq α 4 (Work.Stability.zfar L (Work.Construction.Fstar α))
        ≤ 2 * (C₀ * α / L) := by linarith
    have h2 : 2 * (β ^ 2 * Work.Spaces.HkSq α 4 (hLoc α)) ≤ 2 * (β ^ 2 * C₁) := by
      nlinarith [sq_nonneg β]
    linarith
  -- the square roots
  have hsq0 : 0 ≤ Work.Spaces.HkSq α 4 (locG α L β (hLoc α)) :=
    Work.Spaces.HkSq_nonneg α 4 _
  have hmono : Real.sqrt (Work.Spaces.HkSq α 4 (locG α L β (hLoc α)))
      ≤ Real.sqrt (2 * (C₀ * α / L) + 2 * β ^ 2 * C₁) := Real.sqrt_le_sqrt hsq
  have hLpos : 0 < L := by linarith
  have h2C₀ : (0 : ℝ) ≤ 2 * (C₀ * α / L) := by
    have : 0 ≤ C₀ * α / L := div_nonneg (mul_nonneg hC₀nn hα.le) hLpos.le
    linarith
  have h2C₁ : (0 : ℝ) ≤ 2 * β ^ 2 * C₁ := by
    have : 0 ≤ β ^ 2 * C₁ := mul_nonneg (sq_nonneg β) hC₁nn
    linarith
  have hsplit : Real.sqrt (2 * (C₀ * α / L) + 2 * β ^ 2 * C₁)
      ≤ Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt (2 * β ^ 2 * C₁) := by
    have h1 : 2 * (C₀ * α / L) + 2 * β ^ 2 * C₁
        ≤ (Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt (2 * β ^ 2 * C₁)) ^ 2 := by
      have ha := Real.sq_sqrt h2C₀
      have hb := Real.sq_sqrt h2C₁
      have ha' := Real.sqrt_nonneg (2 * (C₀ * α / L))
      have hb' := Real.sqrt_nonneg (2 * β ^ 2 * C₁)
      nlinarith [ha, hb, ha', hb']
    calc Real.sqrt (2 * (C₀ * α / L) + 2 * β ^ 2 * C₁)
        ≤ Real.sqrt ((Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt (2 * β ^ 2 * C₁)) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt (2 * β ^ 2 * C₁) :=
          Real.sqrt_sq (by positivity)
  have hscal : Real.sqrt (2 * β ^ 2 * C₁) = Real.sqrt 2 * |β| * Real.sqrt C₁ := by
    rw [show (2 : ℝ) * β ^ 2 * C₁ = 2 * β ^ 2 * C₁ by ring,
      Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * β ^ 2) C₁,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) (β ^ 2), Real.sqrt_sq_eq_abs]
  calc Work.Spaces.HkNorm α 4 (locG α L β (hLoc α))
      = Real.sqrt (Work.Spaces.HkSq α 4 (locG α L β (hLoc α))) := rfl
    _ ≤ Real.sqrt (2 * (C₀ * α / L) + 2 * β ^ 2 * C₁) := hmono
    _ ≤ Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt (2 * β ^ 2 * C₁) := hsplit
    _ = Real.sqrt (2 * (C₀ * α / L)) + Real.sqrt 2 * |β| * Real.sqrt C₁ := by rw [hscal]

/-! ## The main theorem -/

/-- **THE LOCALISED DATUM IS SMALL** (node N9 of the route).  For every `ε > 0` there is `L₀`
such that for every `L ≥ L₀` there is a scalar `β` with `|β| ≤ ε`, the perturbation
`g = locData α L β (hLoc α) - F_*` `L₁₂`-orthogonal at `z = 0` (`L₁₂(g)(0) = 0`), of
`𝓗⁴`-distance `HkNorm α 4 g ≤ ε` from the reference profile `F_*`, and *admissible* in the
datum class `DataAdm α` of the existence theorem (N6). -/
theorem locData_small (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ ε > 0, ∃ L₀ : ℝ, ∀ L ≥ L₀, ∃ β : ℝ,
      |β| ≤ ε ∧
        Work.Construction.L12 (locG α L β (hLoc α)) 0 = 0 ∧
        Work.Spaces.HkNorm α 4 (locG α L β (hLoc α)) ≤ ε ∧
        DataAdm α (locG α L β (hLoc α)) := by
  intro ε hε
  obtain ⟨C₀, hC₀⟩ := HkSq_zfar_Fstar_le_direct α hα hα1
  obtain ⟨Cz, hCznn, hCz⟩ := HkIntegrand_zfar_Fstar_le
  obtain ⟨K, hKnn, hKmaj⟩ := HkIntegrand_hLoc_le α hα hα1
  have hmemH : Work.Spaces.HkMem α 4 (hLoc α) := HkMem_hLoc_direct α hα hα1 hKmaj
  set C₁ : ℝ := Work.Spaces.HkSq α 4 (hLoc α) with hC₁def
  have hC₁ : Work.Spaces.HkSq α 4 (hLoc α) ≤ C₁ := le_of_eq hC₁def.symm
  have hC₁nn : (0 : ℝ) ≤ C₁ := by rw [hC₁def]; exact Work.Spaces.HkSq_nonneg α 4 _
  have hDpos : 0 < Work.Construction.L12 (hLoc α) 0 := (L12_hLoc α hα hα1).2
  set D : ℝ := Work.Construction.L12 (hLoc α) 0 with hDdef
  have hDpos' : 0 < D := hDpos
  have hC₀nn : 0 ≤ C₀ := by
    have h : 0 ≤ C₀ * α / 1 :=
      le_trans (Work.Spaces.HkSq_nonneg α 4 _)
        (by simpa using hC₀ 1 le_rfl)
    nlinarith [hα]
  have hC₁nn' : 0 ≤ C₁ := hC₁nn
  set L₀ : ℝ := max 1 (max (8 * C₀ * α / ε ^ 2)
    (max (4 * α / (ε * D)) (8 * Real.sqrt 2 * Real.sqrt C₁ * α / (ε * D)))) with hL₀
  refine ⟨L₀, fun L hL => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hL2 : 8 * C₀ * α / ε ^ 2 ≤ L := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
    exact this
  have hL3 : 4 * α / (ε * D) ≤ L := by
    have h1 : max (4 * α / (ε * D)) (8 * Real.sqrt 2 * Real.sqrt C₁ * α / (ε * D)) ≤ L :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
    exact le_trans (le_max_left _ _) h1
  have hL4 : 8 * Real.sqrt 2 * Real.sqrt C₁ * α / (ε * D) ≤ L := by
    have h1 : max (4 * α / (ε * D)) (8 * Real.sqrt 2 * Real.sqrt C₁ * α / (ε * D)) ≤ L :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
    exact le_trans (le_max_right _ _) h1
  have hεpos : 0 < ε := hε
  -- the normalising scalar
  refine ⟨Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0 / D, ?_, ?_, ?_, ?_⟩
  · -- `|β| ≤ ε`
    have hN : |Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0|
        ≤ 4 * α / L := L12_zfar_Fstar_abs_le α hα hα1 hL1
    have hLpos : 0 < L := by linarith
    have hden : 0 < ε * D := mul_pos hεpos hDpos'
    have h3 : 4 * α / L ≤ ε * D := by
      rw [div_le_iff₀ hLpos]
      have h3' : 4 * α ≤ ε * D * L := by
        rw [div_le_iff₀ hden] at hL3
        linarith [hL3]
      linarith [h3']
    rw [abs_div, abs_of_pos hDpos', div_le_iff₀ hDpos']
    linarith [hN, h3]
  · -- the `L₁₂`-orthogonality
    rw [L12_locG α L _ hα hα1 hL1]
    have hDne : D ≠ 0 := ne_of_gt hDpos'
    field_simp
    ring
  · -- the `𝓗⁴`-bound
    refine le_trans (HkNorm_locG_le α hα hα1 hL1 hC₀nn hC₁nn hmemH (hC₀ L hL1) hC₁) ?_
    have hN : |Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0|
        ≤ 4 * α / L := L12_zfar_Fstar_abs_le α hα hα1 hL1
    have hLpos : 0 < L := by linarith
    have hβb : |Work.Construction.L12 (Work.Stability.zfar L
        (Work.Construction.Fstar α)) 0 / D| ≤ 4 * α / (L * D) := by
      rw [abs_div, abs_of_pos hDpos']
      rw [show 4 * α / (L * D) = (4 * α / L) / D by field_simp]
      rw [div_le_iff₀ hDpos', div_mul_cancel₀ _ (ne_of_gt hDpos')]
      exact hN
    have harg1 : 2 * (C₀ * α / L) ≤ (ε / 2) ^ 2 := by
      have h2 : 8 * C₀ * α ≤ ε ^ 2 * L := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < ε ^ 2)] at hL2
        linarith [hL2]
      rw [show (2 : ℝ) * (C₀ * α / L) = 2 * C₀ * α / L by ring]
      rw [div_le_iff₀ hLpos]
      nlinarith [h2]
    have hsqrt1 : Real.sqrt (2 * (C₀ * α / L)) ≤ ε / 2 := by
      calc Real.sqrt (2 * (C₀ * α / L)) ≤ Real.sqrt ((ε / 2) ^ 2) := Real.sqrt_le_sqrt harg1
        _ = ε / 2 := Real.sqrt_sq (by linarith)
    have hβterm : Real.sqrt 2 * |Work.Construction.L12 (Work.Stability.zfar L
        (Work.Construction.Fstar α)) 0 / D| * Real.sqrt C₁ ≤ ε / 2 := by
      have h2 : 0 ≤ Real.sqrt 2 * Real.sqrt C₁ :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      calc Real.sqrt 2 * |Work.Construction.L12 (Work.Stability.zfar L
            (Work.Construction.Fstar α)) 0 / D| * Real.sqrt C₁
          = (Real.sqrt 2 * Real.sqrt C₁) * |Work.Construction.L12 (Work.Stability.zfar L
              (Work.Construction.Fstar α)) 0 / D| := by ring
        _ ≤ (Real.sqrt 2 * Real.sqrt C₁) * (4 * α / (L * D)) :=
            mul_le_mul_of_nonneg_left hβb h2
        _ = (8 * Real.sqrt 2 * Real.sqrt C₁ * α / (ε * D)) * (ε / (2 * L)) := by
            field_simp
            ring
        _ ≤ L * (ε / (2 * L)) := mul_le_mul_of_nonneg_right hL4 (by positivity)
        _ = ε / 2 := by field_simp
    linarith [hsqrt1, hβterm]
  · -- admissibility
    exact dataAdm_locG α hα hα1 hL1
      (fun z hz θ hθ => hCz α hα hα1 L hL1 z hz θ hθ) hKmaj

/-! ## Compactly supported vorticity in physical variables -/

/-- The localised profile vanishes beyond the self-similar scale `2L`. -/
theorem profileZeroFar_locData_hLoc (α L β : ℝ) (hL : 1 ≤ L) :
    ProfileZeroFar (2 * L) (locData α L β (hLoc α)) := by
  have hmax : max (2 * L) (7 / 4) = 2 * L := by
    rw [max_eq_left]; linarith
  rw [← hmax]
  exact profileZeroFar_locData α L β hL (fun z θ hz => hLoc_eq_zero_of_ge α hz θ)

/-- **The localised datum has compactly supported vorticity in physical variables.**  The
physical vorticity of the profile `F = locData α L β (hLoc α)` is the `e_θ`-field
`x ↦ F(ρ(x)^p, θ(x))·e_θ(x)`; it vanishes identically off the ball of radius `(2L)^{1/p}`,
because `F` vanishes beyond the self-similar scale `2L`.  (The profile exponent of the
construction is `p = 3α`, so that the angular factor is `Γ(θ) = (sinθcos²θ)^α` and the vorticity
is `α`-Hölder.) -/
theorem locData_compactSupport (p α L β : ℝ) (hp : 0 < p) (hL : 1 ≤ L) :
    (∀ x : R3, (2 * L) ≤ Work.Cyl.rho x ^ p →
        omegaProfile p (locData α L β (hLoc α)) x = 0) ∧
      HasCompactSupport (omegaProfile p (locData α L β (hLoc α))) :=
  omegaProfile_compact hp (by linarith) (profileZeroFar_locData_hLoc α L β hL)

/-- The version at the profile exponent `p = 3α` of the construction. -/
theorem locData_compactSupport_three (α L β : ℝ) (hα : 0 < α) (hL : 1 ≤ L) :
    (∀ x : R3, (2 * L) ≤ Work.Cyl.rho x ^ (3 * α) →
        omegaProfile (3 * α) (locData α L β (hLoc α)) x = 0) ∧
      HasCompactSupport (omegaProfile (3 * α) (locData α L β (hLoc α))) :=
  locData_compactSupport (3 * α) α L β (by linarith) hL

end Work.FTS.LocData
