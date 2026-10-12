import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotCubicResiduals
import Submission.Work.BoseBoxFock.latSampling_uvSmear
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.W1_latticeSum_eq` — the Poisson sampling of `W₁` on the box lattice,
## with the zero mode removed

The lattice sum of the UV-truncated weight `W₁ = W1fun v h ℓ` over the box lattice
`Lab N = (ZMod (2N+1))³` (the cube `[-(2π/ℓ)N/2, (2π/ℓ)N/2]³` of momenta, cut off by
`uvCut fu (uvRad ℓ N)`) equals `ℓ³` times the Poisson periodisation of the *smoothed* weight
`uvSmear fu Λ W₁`, minus the zero mode.

## Proof

`latSampling_uvSmear` is the (decay-based) Poisson sampling identity of the lattice
`(2π/ℓ)ℤ³` at the smoothed weight, with `chat (uvSmear fu Λ f) = uvCut fu Λ · chat f`
(`chat_uvSmear`):

    `∑'_m ζ_Λ(k_m)·Ŵ₁(k_m)·e^{i⟪k_m,z⟫} = ℓ³ ∑'_d (ψ_Λ ⋆ W₁)(z + ℓ·latVec d)` ,  `k_m = (2π/ℓ)·latVec m`.

The left series is *supported on the cube* `|m|_∞ ≤ N`: `uvCut fu Λ k = 0` whenever
`2Λ ≤ ‖k‖`, and for `2Λ = (2π/ℓ)N/2` this means `‖m‖ ≥ N/2`, which forces every coordinate of
`m` into `[-N, N]`.  Conversely every integer vector of the cube is `labVec N k` for a unique
label `k : Lab N` (`valMinAbs : ZMod (2N+1) → [-N,N]`), so the lattice series is the `Lab N`-sum.
Finally the zero mode (`k = 0`, `kmomLab ℓ N 0 = 0`, phase `1`) is cancelled on both sides.

Nothing here involves the state, the box or the Hamiltonian: it is a purely analytic identity
between a finite lattice sum and a periodised convolution, and it holds with only
`W₁ ∈ L¹`, `W₁` compactly supported and even.
-/

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The label cube `Lab N ↔ [-N,N]³` -/

/-- The least-absolute representative of an integer `j` with `|j| ≤ N` in `ZMod (2N+1)` is `j`
itself: `valMinAbs` is a bijection `ZMod (2N+1) → [-N,N]`. -/
private lemma intCast_valMinAbs_of_abs_le (N : ℕ) {j : ℤ} (hj : |j| ≤ (N : ℤ)) :
    ((j : ZMod (2 * N + 1))).valMinAbs = j := by
  haveI : NeZero (2 * N + 1) := ⟨by omega⟩
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  obtain ⟨h1, h2⟩ := abs_le.mp hj
  constructor <;> push_cast <;> omega

/-- Every integer vector of the cube `[-N,N]³` is `labVec N` of a label: `labVec N` is surjective
onto the cube. -/
private lemma labVec_surjOn_cube (N : ℕ) {m : Fin 3 → ℤ} (hm : ∀ i, |m i| ≤ (N : ℤ)) :
    ∃ k : Lab N, labVec N k = m := by
  refine ⟨fun i => ((m i : ℤ) : ZMod (2 * N + 1)), funext fun i => ?_⟩
  exact intCast_valMinAbs_of_abs_le N (hm i)

/-- `labVec N` is injective (the centred representative is unique). -/
private lemma labVec_injective (N : ℕ) : Function.Injective (labVec N) := by
  intro a b h
  funext i
  exact ZMod.valMinAbs_inj.mp (congrFun h i)

private lemma labVec_zero (N : ℕ) : labVec N 0 = 0 := by
  funext i
  simp [labVec]

private lemma latVec_zero : latVec (0 : Fin 3 → ℤ) = (0 : E3) := by
  ext i
  simp [latVec_apply]

/-! ## 2. Elementary facts about the cut-off and the momentum label -/

/-- The UV cut-off vanishes beyond `2Λ`: `uvCut fu Λ k = 0` for `2Λ ≤ ‖k‖` (a `LowCut` is `0`
on `[2,∞)`). -/
private lemma uvCut_eq_zero_of_two_mul_le {fu : Work.BoseBoxFix.LowCut} {Λ : ℝ} (hΛ : 0 < Λ)
    {k : E3} (hk : 2 * Λ ≤ ‖k‖) : uvCut fu Λ k = 0 := by
  rw [uvCut, fu.zero _ ?_]
  rw [le_div_iff₀ hΛ]
  linarith

/-- `Work.BoseB4.vec m = 2π • latVec m`: the unit-cube dual lattice momentum is `2π` times the
integer lattice vector. -/
private lemma vec_eq_two_pi_smul_latVec (m : Fin 3 → ℤ) :
    Work.BoseB4.vec m = (2 * Real.pi) • latVec m := by
  refine PiLp.ext fun i => ?_
  simp only [Work.BoseB4.vec, latVec, WithLp.ofLp_smul, WithLp.ofLp_toLp, Pi.smul_apply,
    smul_eq_mul]

/-- `kmomLab ℓ N k = (2π/ℓ) • latVec (labVec N k)`: the momentum of a box label is the sampling
lattice point of its centred integer vector. -/
private lemma kmomLab_eq_smul (ℓ : ℝ) (N : ℕ) (k : Lab N) :
    kmomLab ℓ N k = (2 * Real.pi / ℓ) • latVec (labVec N k) := by
  rw [kmomLab, vec_eq_two_pi_smul_latVec, smul_smul]
  congr 1
  ring

/-! ## 3. The theorem -/

theorem W1_latticeSum_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {fu : Work.BoseBoxFix.LowCut} (N : ℕ) (hN : 1 ≤ N) (z : EuclideanSpace ℝ (Fin 3))
    (hI : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ))
    (hcs : HasCompactSupport (Work.BoseFixR.W1fun v h ℓ))
    (hev : ∀ x, Work.BoseFixR.W1fun v h ℓ (-x) = Work.BoseFixR.W1fun v h ℓ x) :
    (∑ k : Work.BoseBoxFock.Lab N, if k = 0 then 0 else
        ((Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N) (Work.BoseBoxFock.kmomLab ℓ N k) *
          Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (Work.BoseBoxFock.kmomLab ℓ N k) : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) z : ℂ)))
      = (ℓ : ℂ) ^ 3 * (∑' d : Fin 3 → ℤ,
          ((Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad ℓ N) (Work.BoseFixR.W1fun v h ℓ)
            (z + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
        - ((Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N) 0 *
            Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) 0 : ℝ) : ℂ) := by
  classical
  -- abbreviations: the cut-off radius `Λ = uvRad ℓ N`, the weight `W = W₁`, the summands `T`
  -- (over the box labels) and `G` (over the full lattice `ℤ³`)
  set Λ : ℝ := uvRad ℓ N with hΛdef
  set W : E3 → ℝ := Work.BoseFixR.W1fun v h ℓ with hWdef
  set T : Lab N → ℂ := fun k => ((uvCut fu Λ (kmomLab ℓ N k) *
      Work.BoseFixR.chat W (kmomLab ℓ N k) : ℝ) : ℂ)
      * Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) z : ℂ)) with hT
  set G : (Fin 3 → ℤ) → ℂ := fun m => ((uvCut fu Λ ((2 * Real.pi / ℓ) • latVec m) *
      Work.BoseFixR.chat W ((2 * Real.pi / ℓ) • latVec m) : ℝ) : ℂ)
      * Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec m) z : ℂ)) with hG
  change (∑ k : Lab N, if k = 0 then 0 else T k)
      = (ℓ : ℂ) ^ 3 * (∑' d : Fin 3 → ℤ, ((uvSmear fu Λ W (z + ℓ • latVec d) : ℝ) : ℂ))
        - ((uvCut fu Λ 0 * Work.BoseFixR.chat W 0 : ℝ) : ℂ)
  have hΛpos : 0 < Λ := by
    rw [hΛdef, uvRad]
    have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hπ : (0 : ℝ) < 2 * Real.pi / ℓ := by positivity
    nlinarith
  -- * the lattice series is supported on the label cube `[-N,N]³`, hence equals the `Lab N`-sum
  have hcube : (∑' m : Fin 3 → ℤ, G m) = ∑ k : Lab N, G (labVec N k) := by
    have hzero : ∀ m ∉ (Finset.univ.image (labVec N) : Finset (Fin 3 → ℤ)), G m = 0 := by
      intro m hm
      have hncube : ¬ ∀ i, |m i| ≤ (N : ℤ) := by
        intro hall
        obtain ⟨k, hk⟩ := labVec_surjOn_cube N hall
        exact hm (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩)
      push Not at hncube
      obtain ⟨i, hi⟩ := hncube
      have hcut : uvCut fu Λ ((2 * Real.pi / ℓ) • latVec m) = 0 := by
        refine uvCut_eq_zero_of_two_mul_le hΛpos ?_
        have h2L : 2 * Λ = (2 * Real.pi / ℓ) * ((N : ℝ) / 2) := by rw [hΛdef, uvRad]; ring
        have hnorm : ‖(2 * Real.pi / ℓ) • latVec m‖ = (2 * Real.pi / ℓ) * ‖latVec m‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        rw [h2L, hnorm]
        have hNlt : (N : ℝ) < ‖latVec m‖ := by
          have h1 : |((m i : ℤ) : ℝ)| ≤ ‖latVec m‖ := by
            have h2 := PiLp.norm_apply_le (latVec m) i
            rwa [latVec_apply] at h2
          have h3' : ((N : ℤ) : ℝ) < |((m i : ℤ) : ℝ)| := by exact_mod_cast hi
          have h3 : (N : ℝ) < |((m i : ℤ) : ℝ)| := by simpa using h3'
          linarith
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      rw [hG]
      simp only [hcut, Complex.ofReal_zero, zero_mul]
    have hinj : Set.InjOn (labVec N) (↑(Finset.univ : Finset (Lab N)) : Set (Lab N)) :=
      fun a _ b _ hab => labVec_injective N hab
    rw [tsum_eq_sum (s := (Finset.univ.image (labVec N) : Finset (Fin 3 → ℤ))) hzero,
      Finset.sum_image hinj]
  -- * splitting off the zero mode `k = 0`
  have hsplit : (∑ k : Lab N, (if k = 0 then (0 : ℂ) else T k))
      = (∑ k : Lab N, T k) - T 0 := by
    have hpt : ∀ k : Lab N, (if k = 0 then (0:ℂ) else T k) = T k - (if k = 0 then T k else 0) := by
      intro k
      by_cases hk : k = 0 <;> simp [hk]
    calc (∑ k : Lab N, (if k = 0 then (0:ℂ) else T k))
        = ∑ k : Lab N, (T k - (if k = 0 then T k else 0)) :=
          Finset.sum_congr rfl fun k _ => hpt k
      _ = (∑ k : Lab N, T k) - ∑ k : Lab N, (if k = 0 then T k else 0) :=
          Finset.sum_sub_distrib _ _
      _ = (∑ k : Lab N, T k) - T 0 := by
          rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ 0)]
  -- * the `Lab N`-sum is the lattice series, reindexed by `labVec N`
  have hsum_eq : (∑ k : Lab N, T k) = ∑' m : Fin 3 → ℤ, G m := by
    rw [hcube]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hT, hG, kmomLab_eq_smul]
  -- * the zero mode
  have hT0 : T 0 = ((uvCut fu Λ 0 * Work.BoseFixR.chat W 0 : ℝ) : ℂ) := by
    have h0 : kmomLab ℓ N 0 = (0 : E3) := by
      rw [kmomLab_eq_smul, labVec_zero, latVec_zero, smul_zero]
    simp [hT, h0]
  -- * Poisson sampling of the smoothed weight (`chat (uvSmear fu Λ W) = uvCut fu Λ · chat W`)
  have hpoisson : (∑' m : Fin 3 → ℤ, G m)
      = (ℓ : ℂ) ^ 3 * ∑' d : Fin 3 → ℤ, ((uvSmear fu Λ W (z + ℓ • latVec d) : ℝ) : ℂ) := by
    rw [← latSampling_uvSmear fu hΛpos hI hcs hev hℓ z]
    refine tsum_congr fun m => ?_
    simp only [hG, Work.BoseBoxFock.chat_uvSmear fu hΛpos hI]
  rw [hsplit, hsum_eq, hT0, hpoisson]

end Work.BoseBoxFock
