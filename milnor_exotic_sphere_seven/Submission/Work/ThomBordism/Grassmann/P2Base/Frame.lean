import Mathlib
import Submission.Work.ThomBordism.Grassmann.CP4Probe.Map
import Submission.Work.ThomBordism.Grassmann.CP4Probe.Compat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-!
# The rank-`4` plane over `ℂP⁴` in `ℝ¹²`, and its Stiefel frame

For `z ∈ ℂ⁵` put `Λ(z) = (z₀,…,z₄,0) ∈ ℂ⁶` and `Λ'(z) = (0,z₀,…,z₄) ∈ ℂ⁶`.  The complex span
`N_{[z]} = ℂ-span{Λ(z),Λ'(z)} ⊂ ℂ⁶` is a well defined *complex* rank-`2` subbundle of the trivial
rank-`6` complex bundle over `ℂP⁴` (both generators scale by `λ` under `z ↦ λ z`, so the span is
invariant), and its underlying real bundle `V = realif N ⊂ ℝ¹²` is a rank-`4` oriented subbundle of
`ℝ¹²` — i.e. a point of `G̃r₄(ℝ¹²) = OG 4 8` with `V ≅ realif(O(-1)²)`.

This module constructs the **Stiefel frame** of that plane, i.e. the map `p2Map : C(ℂP⁴, OG 4 8)`:
`Λ` and `Λ'` are not orthogonal, so the frame is obtained by orthonormalising the pair explicitly,

* `u = Λ/‖Λ‖`, and
* `w = (Λ' - ⟪u,Λ'⟫ u)/‖Λ' - ⟪u,Λ'⟫ u‖` — the normalisation of the component of `Λ'` orthogonal
  to `ℂΛ`,

and the frame is `(u, iu, w, iw)` realified to `ℝ¹²`.  The key point is that `w` scales by the
*same* phase as `u` under `z ↦ λ z`, so that the frame changes by the block-diagonal rotation
`diag(rot(λ/|λ|), rot(λ/|λ|)) ∈ SO(4)`, which makes the map descend to `ℂP⁴`.
-/

namespace Work.ThomBordism.Grassmann.P2Base

open Work.TangentClasses Work.Projective

noncomputable section

/-! ## The ambient space `ℂ⁶ ≅ ℝ¹²` -/

/-- `ℂ⁶`, the ambient complex space of the construction. -/
abbrev E6 : Type := EuclideanSpace ℂ (Fin 6)

/-- **The coordinate identification `ℂ⁶ ≅ ℝ¹²`** (a real linear isometry, chosen abstractly through
orthonormal bases; the construction does not depend on which realification is used). -/
noncomputable def cE6 : E6 ≃ₗᵢ[ℝ] Amb 12 :=
  (stdOrthonormalBasis ℝ E6).equiv (stdOrthonormalBasis ℝ (Amb 12))
    (finCongr (by
      rw [← Module.finrank_mul_finrank ℝ ℂ E6, finrank_euclideanSpace_fin,
        Complex.finrank_real_complex, finrank_euclideanSpace_fin]))

/-! ## The inner product of standard basis vectors of `ℂⁿ` -/

theorem inner_single_single_C {n : ℕ} (i j : Fin n) (a b : ℂ) :
    inner ℂ (EuclideanSpace.single (𝕜 := ℂ) i a : EuclideanSpace ℂ (Fin n))
      (EuclideanSpace.single (𝕜 := ℂ) j b) = if i = j then b * (starRingEnd ℂ) a else 0 := by
  rw [PiLp.inner_apply, Finset.sum_eq_single i]
  · rw [PiLp.single_apply, PiLp.single_apply, if_pos rfl]
    by_cases h : i = j
    · subst h; rw [if_pos rfl, RCLike.inner_apply, if_pos rfl]
    · rw [if_neg h, inner_zero_right, if_neg h]
  · intro j' _ hj'
    rw [PiLp.single_apply, if_neg hj']
    simp
  · intro h; exact absurd (Finset.mem_univ i) h

/-! ## The two generators `Λ`, `Λ'` -/

/-- The `j`-th coordinate of `Λ(z)` inside `Fin 6`. -/
def lamIdx (j : Fin 5) : Fin 6 := ⟨j.val, by omega⟩

/-- The `j`-th coordinate of `Λ'(z)` inside `Fin 6`. -/
def lamIdxS (j : Fin 5) : Fin 6 := ⟨j.val + 1, by omega⟩

theorem lamIdx_injective : Function.Injective lamIdx := by
  intro a b h
  have h' := congrArg Fin.val h
  simp only [lamIdx] at h'
  exact Fin.ext h'

theorem lamIdxS_injective : Function.Injective lamIdxS := by
  intro a b h
  have h' := congrArg Fin.val h
  simp only [lamIdxS] at h'
  omega

/-- `Λ(z) = (z₀,…,z₄,0) ∈ ℂ⁶`, as a `ℂ`-linear map. -/
noncomputable def lamL : E5 →L[ℂ] E6 :=
  ∑ j : Fin 5, (EuclideanSpace.proj (𝕜 := ℂ) j).smulRight
    (EuclideanSpace.single (𝕜 := ℂ) (lamIdx j) (1 : ℂ))

/-- `Λ'(z) = (0,z₀,…,z₄) ∈ ℂ⁶`, as a `ℂ`-linear map. -/
noncomputable def lamR : E5 →L[ℂ] E6 :=
  ∑ j : Fin 5, (EuclideanSpace.proj (𝕜 := ℂ) j).smulRight
    (EuclideanSpace.single (𝕜 := ℂ) (lamIdxS j) (1 : ℂ))

theorem lamL_apply (z : E5) :
    lamL z = ∑ j : Fin 5, z.ofLp j • (EuclideanSpace.single (𝕜 := ℂ) (lamIdx j) (1 : ℂ) : E6) := by
  rw [lamL]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show (EuclideanSpace.proj (𝕜 := ℂ) j) z = z.ofLp j from rfl, smul_single_eq]

theorem lamR_apply (z : E5) :
    lamR z = ∑ j : Fin 5, z.ofLp j • (EuclideanSpace.single (𝕜 := ℂ) (lamIdxS j) (1 : ℂ) : E6) := by
  rw [lamR]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show (EuclideanSpace.proj (𝕜 := ℂ) j) z = z.ofLp j from rfl, smul_single_eq]

/-! ## Coordinates -/

theorem lamL_coord_self (z : E5) (j : Fin 5) : (lamL z).ofLp (lamIdx j) = z.ofLp j := by
  rw [lamL_apply, WithLp.ofLp_sum, Finset.sum_apply]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · rw [PiLp.single_apply, if_pos rfl, mul_one]
  · intro j' _ hj'
    rw [PiLp.single_apply, if_neg (fun h => hj' (lamIdx_injective h).symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem lamR_coord_self (z : E5) (j : Fin 5) : (lamR z).ofLp (lamIdxS j) = z.ofLp j := by
  rw [lamR_apply, WithLp.ofLp_sum, Finset.sum_apply]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · rw [PiLp.single_apply, if_pos rfl, mul_one]
  · intro j' _ hj'
    rw [PiLp.single_apply, if_neg (fun h => hj' (lamIdxS_injective h).symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem lamL_coord_zero_of_notMem (z : E5) {k : Fin 6} (hk : ∀ j : Fin 5, lamIdx j ≠ k) :
    (lamL z).ofLp k = 0 := by
  rw [lamL_apply, WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  rw [PiLp.single_apply, if_neg (fun h => hk j h.symm), mul_zero]

theorem lamL_coord_five (z : E5) : (lamL z).ofLp (5 : Fin 6) = 0 :=
  lamL_coord_zero_of_notMem z (fun j => by
    intro h; have := congrArg Fin.val h; simp only [lamIdx] at this; omega)


theorem lamR_coord_zero_of_notMem (z : E5) {k : Fin 6} (hk : ∀ j : Fin 5, lamIdxS j ≠ k) :
    (lamR z).ofLp k = 0 := by
  rw [lamR_apply, WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  rw [PiLp.single_apply, if_neg (fun h => hk j h.symm), mul_zero]

theorem lamR_coord_five (z : E5) : (lamR z).ofLp (5 : Fin 6) = z.ofLp (4 : Fin 5) := by
  have h : lamIdxS (4 : Fin 5) = (5 : Fin 6) := rfl
  rw [← h]
  exact lamR_coord_self z 4

theorem lamR_coord_zero (z : E5) : (lamR z).ofLp (0 : Fin 6) = 0 :=
  lamR_coord_zero_of_notMem z (fun j => by
    intro h; have := congrArg Fin.val h; simp only [lamIdxS] at this; omega)

/-! ## Inner products of the generators -/

theorem inner_lamL_lamL (z y : E5) : inner ℂ (lamL z) (lamL y) = inner ℂ z y := by
  rw [lamL_apply, lamL_apply, inner_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [sum_inner]
  simp only [inner_smul_left, inner_smul_right, inner_single_single_C, map_one, mul_one]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, mul_one, RCLike.inner_apply]
  · intro x _ hx
    rw [if_neg (fun h => hx (lamIdx_injective h)), mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem inner_lamR_lamR (z y : E5) : inner ℂ (lamR z) (lamR y) = inner ℂ z y := by
  rw [lamR_apply, lamR_apply, inner_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [sum_inner]
  simp only [inner_smul_left, inner_smul_right, inner_single_single_C, map_one, mul_one]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, mul_one, RCLike.inner_apply]
  · intro x _ hx
    rw [if_neg (fun h => hx (lamIdxS_injective h)), mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem norm_lamL (z : E5) : ‖lamL z‖ = ‖z‖ := by
  have h := inner_lamL_lamL z z
  have h1 : ‖lamL z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ) (lamL z), h, norm_sq_eq_re_inner (𝕜 := ℂ) z]
  nlinarith [norm_nonneg (lamL z), norm_nonneg z]

theorem norm_lamR (z : E5) : ‖lamR z‖ = ‖z‖ := by
  have h := inner_lamR_lamR z z
  have h1 : ‖lamR z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ) (lamR z), h, norm_sq_eq_re_inner (𝕜 := ℂ) z]
  nlinarith [norm_nonneg (lamR z), norm_nonneg z]

theorem lamL_ne_zero {z : E5} (hz : z ≠ 0) : lamL z ≠ 0 := by
  intro h
  refine hz ?_
  have : ‖z‖ = 0 := by rw [← norm_lamL z, h, norm_zero]
  exact norm_eq_zero.mp this

theorem lamR_ne_zero {z : E5} (hz : z ≠ 0) : lamR z ≠ 0 := by
  intro h
  refine hz ?_
  have : ‖z‖ = 0 := by rw [← norm_lamR z, h, norm_zero]
  exact norm_eq_zero.mp this

/-! ## The normalised generator `u = Λ/‖Λ‖` -/

/-- The normalised `Λ`.  (The scalar is the complex number `(‖Λ‖)⁻¹`; this keeps the scalar
identities of the frames elementary.) -/
noncomputable def lamUnit (z : E5) : E6 := ((‖lamL z‖ : ℂ))⁻¹ • lamL z

theorem lamUnit_norm (z : E5) (hz : z ≠ 0) : ‖lamUnit z‖ = 1 := by
  have hne : ‖lamL z‖ ≠ 0 := norm_ne_zero_iff.mpr (lamL_ne_zero hz)
  rw [lamUnit, norm_smul]
  have h2 : ‖((‖lamL z‖ : ℝ) : ℂ)⁻¹‖ = (‖lamL z‖)⁻¹ := by
    rw [norm_inv]
    congr 1
    simp
  rw [h2, inv_mul_cancel₀ hne]

theorem lamUnit_ne_zero (z : E5) (hz : z ≠ 0) : lamUnit z ≠ 0 := by
  intro h
  have := lamUnit_norm z hz
  rw [h, norm_zero] at this
  exact one_ne_zero this.symm

theorem inner_lamUnit_lamUnit (z : E5) (hz : z ≠ 0) : inner ℂ (lamUnit z) (lamUnit z) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, lamUnit_norm z hz]
  norm_num

theorem lamUnit_smul_unit (z : E5) {μ : ℂ} (hμ : ‖μ‖ = 1) :
    lamUnit (μ • z) = μ • lamUnit z := by
  have hL : lamL (μ • z) = μ • lamL z := map_smul lamL μ z
  have hnorm : ‖lamL (μ • z)‖ = ‖lamL z‖ := by rw [hL, norm_smul, hμ, one_mul]
  have hcoe : ((‖lamL (μ • z)‖ : ℝ) : ℂ) = ((‖lamL z‖ : ℝ) : ℂ) := by rw [hnorm]
  rw [lamUnit, lamUnit, hcoe, hL, smul_comm]

/-- Changing the scalar by a positive real does not change `u`. -/
theorem lamUnit_smul_ofReal (z : E5) {a : ℝ} (ha : 0 < a) :
    lamUnit ((a : ℂ) • z) = lamUnit z := by
  have hL : lamL ((a : ℂ) • z) = (a : ℂ) • lamL z := map_smul lamL (a : ℂ) z
  have h2 : ‖((a : ℝ) : ℂ)‖ = a := by
    rw [show ‖((a : ℝ) : ℂ)‖ = |a| from by simp, abs_of_pos ha]
  have hnorm : ‖lamL ((a : ℂ) • z)‖ = a * ‖lamL z‖ := by rw [hL, norm_smul, h2]
  have hcoe : ((‖lamL ((a : ℂ) • z)‖ : ℝ) : ℂ)
      = ((a : ℝ) : ℂ) * ((‖lamL z‖ : ℝ) : ℂ) := by rw [hnorm, Complex.ofReal_mul]
  have hane : ((a : ℝ) : ℂ) ≠ 0 := by simpa using (ne_of_gt ha : (a : ℝ) ≠ 0)
  rw [lamUnit, lamUnit, hcoe, hL, mul_inv, smul_smul]
  congr 1
  have hcomm : (↑a : ℂ)⁻¹ * (↑‖lamL z‖ : ℂ)⁻¹ * ↑a = (↑a : ℂ)⁻¹ * ↑a * (↑‖lamL z‖ : ℂ)⁻¹ := by
    ring
  rw [hcomm, inv_mul_cancel₀ hane, one_mul]

/-! ## A chain lemma for `Fin (n+1)` -/

/-- If `f k = β f (k+1)` for all `k < n`, `β ≠ 0` and `f n = 0`, then `f = 0`. -/
theorem fin_chain_zero {n : ℕ} (f : Fin (n + 1) → ℂ) (β : ℂ) (hβ : β ≠ 0)
    (h : ∀ k : Fin n, f (Fin.castSucc k) = β * f (Fin.succ k)) (hn : f (Fin.last n) = 0) :
    f = 0 := by
  have key : ∀ m : ℕ, m ≤ n → f ⟨n - m, by omega⟩ = 0 := by
    intro m hm
    induction m with
    | zero =>
        have : (⟨n - 0, by omega⟩ : Fin (n + 1)) = Fin.last n := by
          ext; simp [Fin.last]
        rw [this, hn]
    | succ m ih =>
        have hm' : m ≤ n := by omega
        have hstep := h ⟨n - (m + 1), by omega⟩
        have h1 : (Fin.castSucc (⟨n - (m + 1), by omega⟩ : Fin n))
            = (⟨n - (m + 1), by omega⟩ : Fin (n + 1)) := rfl
        have h2 : (Fin.succ (⟨n - (m + 1), by omega⟩ : Fin n))
            = (⟨n - m, by omega⟩ : Fin (n + 1)) := by
          ext; simp [Fin.succ]; omega
        rw [h1, h2, ih hm', mul_zero] at hstep
        exact hstep
  funext k
  have hk : (⟨n - (n - k.val), by omega⟩ : Fin (n + 1)) = k := by
    ext; simp; omega
  rw [← hk]
  exact key (n - k.val) (by omega)

/-! ## The orthogonal complement of `ℂΛ` -/

/-- The component of `Λ'` orthogonal to `ℂΛ`, normalised. -/
noncomputable def wVec (z : E5) : E6 := lamR z - (inner ℂ (lamUnit z) (lamR z)) • lamUnit z

theorem inner_lamUnit_wVec (z : E5) (hz : z ≠ 0) : inner ℂ (lamUnit z) (wVec z) = 0 := by
  rw [wVec, inner_sub_right, inner_smul_right, inner_lamUnit_lamUnit z hz, mul_one, sub_self]

theorem inner_wVec_lamUnit (z : E5) (hz : z ≠ 0) : inner ℂ (wVec z) (lamUnit z) = 0 := by
  rw [← inner_conj_symm, inner_lamUnit_wVec z hz, map_zero]

theorem wVec_smul_unit (z : E5) {μ : ℂ} (hμ : ‖μ‖ = 1) :
    wVec (μ • z) = μ • wVec z := by
  have hL : lamR (μ • z) = μ • lamR z := map_smul lamR μ z
  have hu : lamUnit (μ • z) = μ • lamUnit z := lamUnit_smul_unit z hμ
  have hμ1 : (starRingEnd ℂ) μ * μ = 1 := by rw [RCLike.conj_mul, hμ]; norm_num
  have hinner : inner ℂ (lamUnit (μ • z)) (lamR (μ • z)) = inner ℂ (lamUnit z) (lamR z) := by
    rw [hu, hL, inner_smul_left, inner_smul_right, ← mul_assoc, hμ1, one_mul]
  rw [wVec, wVec, hinner, hL, hu, smul_sub]
  congr 1
  rw [smul_smul, smul_smul, mul_comm]

theorem wVec_ne_zero (z : E5) (hz : z ≠ 0) : wVec z ≠ 0 := by
  intro h
  set c : ℂ := inner ℂ (lamUnit z) (lamR z) with hc
  have hR : lamR z = c • lamUnit z := by
    have h1 := sub_eq_zero.mp h
    simpa only [hc] using h1
  set β : ℂ := c * ((‖lamL z‖ : ℂ))⁻¹ with hβ
  have hRL : lamR z = β • lamL z := by
    rw [hβ, hR, lamUnit, smul_smul]
  have hβne : β ≠ 0 := by
    intro hb
    refine lamR_ne_zero hz ?_
    rw [hRL, hb, zero_smul]
  have hcoord : ∀ k : Fin 6, (lamR z).ofLp k = β * (lamL z).ofLp k := by
    intro k
    have h1 := congrArg (fun w : E6 => w.ofLp k) hRL
    rwa [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] at h1
  have hstep : ∀ k : Fin 4, z.ofLp (Fin.castSucc k) = β * z.ofLp (Fin.succ k) := by
    intro k
    have hh := hcoord (lamIdxS (Fin.castSucc k))
    have hkey : (lamL z).ofLp (lamIdxS (Fin.castSucc k)) = z.ofLp (Fin.succ k) := by
      show (lamL z).ofLp (lamIdx (Fin.succ k)) = z.ofLp (Fin.succ k)
      exact lamL_coord_self z (Fin.succ k)
    rw [lamR_coord_self z (Fin.castSucc k), hkey] at hh
    exact hh
  have hlast : z.ofLp (4 : Fin 5) = 0 := by
    have hh := hcoord (5 : Fin 6)
    rw [lamR_coord_five, lamL_coord_five, mul_zero] at hh
    exact hh
  have hz0 : (fun k : Fin 5 => z.ofLp k) = 0 :=
    fin_chain_zero (fun k : Fin 5 => z.ofLp k) β hβne hstep hlast
  refine hz ?_
  rw [WithLp.ext_iff]
  simpa using hz0

/-! ## The normalised orthogonal component `w` -/

/-- The normalised `w`. -/
noncomputable def wUnit (z : E5) : E6 := ((‖wVec z‖ : ℂ))⁻¹ • wVec z

theorem wUnit_norm (z : E5) (hz : z ≠ 0) : ‖wUnit z‖ = 1 := by
  have hne : ‖wVec z‖ ≠ 0 := norm_ne_zero_iff.mpr (wVec_ne_zero z hz)
  rw [wUnit, norm_smul]
  have h2 : ‖((‖wVec z‖ : ℝ) : ℂ)⁻¹‖ = (‖wVec z‖)⁻¹ := by
    rw [norm_inv]
    congr 1
    simp
  rw [h2, inv_mul_cancel₀ hne]

theorem wUnit_ne_zero (z : E5) (hz : z ≠ 0) : wUnit z ≠ 0 := by
  intro h
  have := wUnit_norm z hz
  rw [h, norm_zero] at this
  exact one_ne_zero this.symm

theorem inner_wUnit_wUnit (z : E5) (hz : z ≠ 0) : inner ℂ (wUnit z) (wUnit z) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, wUnit_norm z hz]
  norm_num

theorem inner_lamUnit_wUnit (z : E5) (hz : z ≠ 0) : inner ℂ (lamUnit z) (wUnit z) = 0 := by
  rw [wUnit, inner_smul_right, inner_lamUnit_wVec z hz, mul_zero]

theorem inner_wUnit_lamUnit (z : E5) (hz : z ≠ 0) : inner ℂ (wUnit z) (lamUnit z) = 0 := by
  rw [← inner_conj_symm, inner_lamUnit_wUnit z hz, map_zero]

theorem wVec_smul_ofReal (z : E5) {a : ℝ} (ha : 0 < a) :
    wVec ((a : ℂ) • z) = (a : ℂ) • wVec z := by
  have hL : lamR ((a : ℂ) • z) = (a : ℂ) • lamR z := map_smul lamR (a : ℂ) z
  have hu : lamUnit ((a : ℂ) • z) = lamUnit z := lamUnit_smul_ofReal z ha
  have hinner : inner ℂ (lamUnit ((a : ℂ) • z)) (lamR ((a : ℂ) • z))
      = (a : ℂ) * inner ℂ (lamUnit z) (lamR z) := by
    rw [hu, hL, inner_smul_right]
  rw [wVec, wVec, hinner, hL, hu, smul_sub, smul_smul]

theorem wUnit_smul_unit (z : E5) {μ : ℂ} (hμ : ‖μ‖ = 1) :
    wUnit (μ • z) = μ • wUnit z := by
  have hw : wVec (μ • z) = μ • wVec z := wVec_smul_unit z hμ
  have hnorm : ‖wVec (μ • z)‖ = ‖wVec z‖ := by rw [hw, norm_smul, hμ, one_mul]
  have hcoe : ((‖wVec (μ • z)‖ : ℝ) : ℂ) = ((‖wVec z‖ : ℝ) : ℂ) := by rw [hnorm]
  rw [wUnit, wUnit, hcoe, hw, smul_comm]

theorem wUnit_smul_ofReal (z : E5) {a : ℝ} (ha : 0 < a) :
    wUnit ((a : ℂ) • z) = wUnit z := by
  have hw : wVec ((a : ℂ) • z) = (a : ℂ) • wVec z := wVec_smul_ofReal z ha
  have h2 : ‖((a : ℝ) : ℂ)‖ = a := by
    rw [show ‖((a : ℝ) : ℂ)‖ = |a| from by simp, abs_of_pos ha]
  have hnorm : ‖wVec ((a : ℂ) • z)‖ = a * ‖wVec z‖ := by rw [hw, norm_smul, h2]
  have hcoe : ((‖wVec ((a : ℂ) • z)‖ : ℝ) : ℂ)
      = ((a : ℝ) : ℂ) * ((‖wVec z‖ : ℝ) : ℂ) := by rw [hnorm, Complex.ofReal_mul]
  have hane : ((a : ℝ) : ℂ) ≠ 0 := by simpa using (ne_of_gt ha : (a : ℝ) ≠ 0)
  rw [wUnit, wUnit, hcoe, hw, mul_inv, smul_smul]
  congr 1
  have hcomm : (↑a : ℂ)⁻¹ * (↑‖wVec z‖ : ℂ)⁻¹ * ↑a
      = (↑a : ℂ)⁻¹ * ↑a * (↑‖wVec z‖ : ℂ)⁻¹ := by ring
  rw [hcomm, inv_mul_cancel₀ hane, one_mul]

/-! ## The frame of the plane -/

/-- The pair `(x, i x)`. -/
def twoE (x : E6) : Fin 2 → E6 := ![x, Complex.I • x]

@[simp] theorem twoE_zero (x : E6) : twoE x 0 = x := rfl

@[simp] theorem twoE_one (x : E6) : twoE x 1 = Complex.I • x := rfl

/-- The complex frame vectors of the plane `ℂ-span{Λ,Λ'}`, indexed by the two blocks
`(Λ, iΛ)` and `(w, iw)`. -/
def p2VecB (z : E5) : Fin 2 ⊕ Fin 2 → E6 :=
  Sum.elim (twoE (lamUnit z)) (twoE (wUnit z))

/-- The frame vectors of the plane, indexed by `Fin 4`. -/
def p2VecC (z : E5) : Fin 4 → E6 := fun a => p2VecB z (finSumFinEquiv.symm a)

/-- **The frame of the plane in `ℝ¹²`.** -/
def p2Frame (z : E5) : Fin 4 → Amb 12 := fun a => cE6 (p2VecC z a)

/-- The index equivalence `Fin 2 ⊕ Fin 2 ≃ Fin 4` used for the two blocks. -/
abbrev p2Idx : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv

theorem p2VecB_inl (z : E5) (a : Fin 2) : p2VecB z (Sum.inl a) = twoE (lamUnit z) a := rfl

theorem p2VecB_inr (z : E5) (a : Fin 2) : p2VecB z (Sum.inr a) = twoE (wUnit z) a := rfl

theorem p2VecC_inl (z : E5) (a : Fin 2) :
    p2VecC z (p2Idx (Sum.inl a)) = twoE (lamUnit z) a := by
  rw [p2VecC, Equiv.symm_apply_apply, p2VecB_inl]

theorem p2VecC_inr (z : E5) (a : Fin 2) :
    p2VecC z (p2Idx (Sum.inr a)) = twoE (wUnit z) a := by
  rw [p2VecC, Equiv.symm_apply_apply, p2VecB_inr]

/-! ## Orthonormality -/

theorem I_smul_I_smul (x : E6) : Complex.I • (Complex.I • x) = -x := by
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]

/-- The pair `(x, i x)` is orthonormal for a unit vector `x`. -/
theorem twoE_orthonormal {x : E6} (hx : ‖x‖ = 1) : Orthonormal ℝ (twoE x) := by
  rw [orthonormal_iff_ite]
  intro a a'
  have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  have hb : a' = 0 ∨ a' = 1 := by fin_cases a' <;> simp
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rw [twoE_zero, if_pos rfl, real_inner_self_eq_norm_sq, hx]
    norm_num
  · rw [twoE_zero, twoE_one, if_neg (by decide)]
    exact real_inner_I_smul_self ℂ x
  · rw [twoE_zero, twoE_one, if_neg (by decide), real_inner_comm]
    exact real_inner_I_smul_self ℂ x
  · rw [twoE_one, if_pos rfl, real_inner_self_eq_norm_sq, norm_smul, Complex.norm_I, one_mul, hx]
    norm_num

/-- Two blocks whose complex inner product vanishes are mutually orthogonal. -/
theorem twoE_inner_zero {x y : E6} (h : inner ℂ x y = 0) (a a' : Fin 2) :
    inner ℝ (twoE x a) (twoE y a') = 0 := by
  have h1 : inner ℂ x (Complex.I • y) = 0 := by rw [inner_smul_right, h, mul_zero]
  have h2 : inner ℂ (Complex.I • x) y = 0 := by rw [inner_smul_left, h, mul_zero]
  have h3 : inner ℂ (Complex.I • x) (Complex.I • y) = 0 := by
    rw [inner_smul_left, inner_smul_right, h, mul_zero, mul_zero]
  have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  have hb : a' = 0 ∨ a' = 1 := by fin_cases a' <;> simp
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp only [twoE_zero, twoE_one, ClosedSubmodule.inner_real_eq_re_inner, h, h1, h2, h3,
      map_zero, Complex.zero_re]

theorem p2VecB_orthonormal (z : E5) (hz : z ≠ 0) : Orthonormal ℝ (p2VecB z) := by
  rw [orthonormal_iff_ite]
  rintro (a | a) (b | b)
  · rw [p2VecB_inl, p2VecB_inl]
    refine (orthonormal_iff_ite.mp (twoE_orthonormal (lamUnit_norm z hz)) a b).trans ?_
    simp only [Sum.inl.injEq]
  · rw [p2VecB_inl, p2VecB_inr, twoE_inner_zero (inner_lamUnit_wUnit z hz) a b]
    rw [if_neg (fun hh => Sum.inl_ne_inr hh)]
  · rw [p2VecB_inl, p2VecB_inr, real_inner_comm,
      twoE_inner_zero (inner_lamUnit_wUnit z hz) b a,
      if_neg (fun hh => Sum.inr_ne_inl hh)]
  · rw [p2VecB_inr, p2VecB_inr]
    refine (orthonormal_iff_ite.mp (twoE_orthonormal (wUnit_norm z hz)) a b).trans ?_
    simp only [Sum.inr.injEq]

theorem p2VecC_orthonormal (z : E5) (hz : z ≠ 0) : Orthonormal ℝ (p2VecC z) := by
  rw [orthonormal_iff_ite]
  intro a a'
  have h := orthonormal_iff_ite.mp (p2VecB_orthonormal z hz) (p2Idx.symm a) (p2Idx.symm a')
  have hiff : (p2Idx.symm a = p2Idx.symm a') ↔ (a = a') := by
    constructor
    · intro hh
      have h1 : a = p2Idx (p2Idx.symm a) := (Equiv.apply_symm_apply p2Idx a).symm
      have h2 : a' = p2Idx (p2Idx.symm a') := (Equiv.apply_symm_apply p2Idx a').symm
      rw [h1, h2, hh]
    · intro hh; rw [hh]
  have h' : inner ℝ (p2VecB z (p2Idx.symm a)) (p2VecB z (p2Idx.symm a'))
      = if a = a' then 1 else 0 := by
    simpa only [hiff] using h
  simpa only [p2VecC] using h'

theorem p2Frame_orthonormal (z : E5) (hz : z ≠ 0) : Orthonormal ℝ (p2Frame z) := by
  rw [orthonormal_iff_ite]
  intro a a'
  have h := orthonormal_iff_ite.mp (p2VecC_orthonormal z hz) a a'
  rw [show inner ℝ (p2Frame z a) (p2Frame z a') = inner ℝ (p2VecC z a) (p2VecC z a') from
    cE6.inner_map_map (p2VecC z a) (p2VecC z a')]
  exact h

/-! ## Continuity -/

theorem continuous_lamUnit_subtype :
    Continuous fun z : {z : E5 // z ≠ 0} => lamUnit z.1 := by
  have hL : Continuous fun z : {z : E5 // z ≠ 0} => lamL z.1 :=
    lamL.continuous.comp continuous_subtype_val
  have hnorm : Continuous fun z : {z : E5 // z ≠ 0} => (((‖lamL z.1‖ : ℝ) : ℂ))⁻¹ := by
    refine Continuous.inv₀ (Complex.continuous_ofReal.comp (continuous_norm.comp hL)) ?_
    intro z
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact norm_ne_zero_iff.mpr (lamL_ne_zero z.2)
  exact hnorm.smul hL

theorem continuous_wVec_subtype :
    Continuous fun z : {z : E5 // z ≠ 0} => wVec z.1 := by
  have hL : Continuous fun z : {z : E5 // z ≠ 0} => lamR z.1 :=
    lamR.continuous.comp continuous_subtype_val
  have hscalar : Continuous fun z : {z : E5 // z ≠ 0} => inner ℂ (lamUnit z.1) (lamR z.1) :=
    continuous_inner.comp (continuous_lamUnit_subtype.prodMk hL)
  exact hL.sub (hscalar.smul continuous_lamUnit_subtype)

theorem continuous_wUnit_subtype :
    Continuous fun z : {z : E5 // z ≠ 0} => wUnit z.1 := by
  have hnorm : Continuous fun z : {z : E5 // z ≠ 0} => (((‖wVec z.1‖ : ℝ) : ℂ))⁻¹ := by
    refine Continuous.inv₀ (Complex.continuous_ofReal.comp (continuous_norm.comp continuous_wVec_subtype)) ?_
    intro z
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact norm_ne_zero_iff.mpr (wVec_ne_zero z.1 z.2)
  exact hnorm.smul continuous_wVec_subtype

theorem continuous_p2VecB_subtype (p : Fin 2 ⊕ Fin 2) :
    Continuous fun z : {z : E5 // z ≠ 0} => p2VecB z.1 p := by
  rcases p with b | b <;> fin_cases b <;>
    simp only [p2VecB, Sum.elim_inl, Sum.elim_inr, twoE_zero, twoE_one] <;>
    first
      | exact continuous_lamUnit_subtype
      | exact continuous_wUnit_subtype
      | exact continuous_lamUnit_subtype.const_smul Complex.I
      | exact continuous_wUnit_subtype.const_smul Complex.I

theorem continuous_p2Frame_subtype :
    Continuous fun z : {z : E5 // z ≠ 0} => p2Frame z.1 := by
  refine continuous_pi (fun a => ?_)
  obtain ⟨p, rfl⟩ := p2Idx.surjective a
  refine cE6.continuous.comp ?_
  simpa only [p2Frame, p2VecC, Equiv.symm_apply_apply] using continuous_p2VecB_subtype p

/-! ## The Stiefel point and the map `ℂP⁴ → G̃r₄(ℝ¹²)` -/

/-- The Stiefel point of the plane of a nonzero representative. -/
noncomputable def p2Stiefel (z : {z : E5 // z ≠ 0}) : Stiefel 4 8 :=
  ⟨p2Frame z.1, p2Frame_orthonormal z.1 z.2⟩

theorem p2Stiefel_val (z : {z : E5 // z ≠ 0}) : (p2Stiefel z).1 = p2Frame z.1 := rfl

theorem continuous_p2Stiefel : Continuous p2Stiefel :=
  Continuous.subtype_mk continuous_p2Frame_subtype (fun z => p2Frame_orthonormal z.1 z.2)

/-! ## The rotation matrices -/

/-- The `2 × 2` rotation matrix of a complex number, in the convention compatible with the frame
`(x, i x)`: `A_{0,0} = A_{1,1} = Re μ`, `A_{1,0} = -A_{0,1} = Im μ`. -/
def p2RotMat (μ : ℂ) : Matrix (Fin 2) (Fin 2) ℝ := (probeRotMat μ).transpose

@[simp] theorem p2RotMat_zero_zero (μ : ℂ) : p2RotMat μ 0 0 = μ.re := rfl
@[simp] theorem p2RotMat_zero_one (μ : ℂ) : p2RotMat μ 0 1 = -μ.im := rfl
@[simp] theorem p2RotMat_one_zero (μ : ℂ) : p2RotMat μ 1 0 = μ.im := rfl
@[simp] theorem p2RotMat_one_one (μ : ℂ) : p2RotMat μ 1 1 = μ.re := rfl

theorem isSO_p2RotMat {μ : ℂ} (hμ : ‖μ‖ = 1) : IsSO (p2RotMat μ) :=
  (isSO_probeRotMat hμ).transpose

/-- The block-diagonal rotation `diag(rot μ, rot μ)`. -/
def p2RotB (μ : ℂ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks (p2RotMat μ) 0 0 (p2RotMat μ)

theorem p2RotB_transpose_mul {μ : ℂ} (hμ : ‖μ‖ = 1) :
    (p2RotB μ).transpose * p2RotB μ = 1 := by
  rw [p2RotB, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, (isSO_p2RotMat hμ).1,
    Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  simpa using (Matrix.fromBlocks_one (l := Fin 2) (m := Fin 2) (α := ℝ))

theorem p2RotB_det {μ : ℂ} (hμ : ‖μ‖ = 1) : (p2RotB μ).det = 1 := by
  rw [p2RotB, Matrix.det_fromBlocks_zero₁₂, (isSO_p2RotMat hμ).2, mul_one]

/-- The rotation of `ℝ¹² = (ℝ² ⊕ ℝ²) ⊕ ℝ⁴` obtained by reindexing `p2RotB`. -/
def p2Rot (μ : ℂ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.reindex p2Idx p2Idx (p2RotB μ)

theorem isSO_p2Rot {μ : ℂ} (hμ : ‖μ‖ = 1) : IsSO (p2Rot μ) := by
  constructor
  · rw [p2Rot, Matrix.reindex_apply, Matrix.transpose_submatrix,
      Matrix.submatrix_mul_equiv (p2RotB μ).transpose (p2RotB μ) p2Idx.symm
        p2Idx.symm p2Idx.symm, p2RotB_transpose_mul hμ,
      Matrix.submatrix_one_equiv p2Idx.symm]
  · rw [p2Rot, Matrix.reindex_apply,
      Matrix.det_submatrix_equiv_self p2Idx.symm (p2RotB μ), p2RotB_det hμ]

/-- The rotation of a unit complex number, as an element of `SO(4)`. -/
noncomputable def p2SO (μ : ℂ) (hμ : ‖μ‖ = 1) : SOk 4 := ⟨p2Rot μ, isSO_p2Rot hμ⟩

@[simp] theorem p2SO_val (μ : ℂ) (hμ : ‖μ‖ = 1) : (p2SO μ hμ).1 = p2Rot μ := rfl

/-! ## Equivariance of the frame -/

theorem cE6_complex_smul (μ : ℂ) (x : E6) :
    cE6 (μ • x) = μ.re • cE6 x + μ.im • cE6 (Complex.I • x) := by
  have h : μ • x = μ.re • x + μ.im • (Complex.I • x) := by
    conv_lhs => rw [← Complex.re_add_im μ]
    rw [add_smul, mul_smul]
    rfl
  rw [h, map_add, map_smul, map_smul]

theorem twoE_zero_smul (x : E6) (μ : ℂ) :
    cE6 (twoE (μ • x) 0) = μ.re • cE6 (twoE x 0) + μ.im • cE6 (twoE x 1) := by
  rw [twoE_zero, twoE_zero, twoE_one, cE6_complex_smul]

theorem twoE_one_smul (x : E6) (μ : ℂ) :
    cE6 (twoE (μ • x) 1) = μ.re • cE6 (twoE x 1) - μ.im • cE6 (twoE x 0) := by
  have hsm : Complex.I • (μ • x) = μ • (Complex.I • x) := smul_comm Complex.I μ x
  rw [twoE_one, twoE_one, twoE_zero, hsm, cE6_complex_smul, I_smul_I_smul, map_neg]
  simp only [smul_neg]
  abel

theorem twoE_smul_apply (x : E6) (μ : ℂ) (b : Fin 2) :
    cE6 (twoE (μ • x) b)
      = p2RotMat μ 0 b • cE6 (twoE x 0) + p2RotMat μ 1 b • cE6 (twoE x 1) := by
  fin_cases b
  · simp only [Fin.zero_eta, twoE_zero, twoE_one, p2RotMat_zero_zero, p2RotMat_one_zero]
    rw [cE6_complex_smul]
  · have hsm : Complex.I • (μ • x) = μ • (Complex.I • x) := smul_comm Complex.I μ x
    simp only [Fin.mk_one, twoE_zero, twoE_one, p2RotMat_zero_one, p2RotMat_one_one]
    rw [hsm, cE6_complex_smul, I_smul_I_smul, map_neg]
    simp only [smul_neg, neg_smul]
    abel

theorem p2Frame_smul_unit (z : E5) {μ : ℂ} (hμ : ‖μ‖ = 1) :
    p2Frame (μ • z) = soActFun (k := 4) (m := 8) (p2Rot μ) (p2Frame z) := by
  have hL : lamUnit (μ • z) = μ • lamUnit z := lamUnit_smul_unit z hμ
  have hW : wUnit (μ • z) = μ • wUnit z := wUnit_smul_unit z hμ
  funext a
  obtain ⟨p, rfl⟩ := p2Idx.surjective a
  have hstep : soActFun (k := 4) (m := 8) (p2Rot μ) (p2Frame z) (p2Idx p)
      = ∑ p' : Fin 2 ⊕ Fin 2, p2RotB μ p' p • p2Frame z (p2Idx p') := by
    rw [soActFun, ← Equiv.sum_comp p2Idx
      (fun j => p2Rot μ j (p2Idx p) • p2Frame z j)]
    refine Finset.sum_congr rfl (fun p' _ => ?_)
    rw [p2Rot, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply]
  rw [hstep, Fintype.sum_sum_type]
  rcases p with b | b
  · have hcross : (∑ b' : Fin 2, p2RotB μ (Sum.inr b') (Sum.inl b)
        • p2Frame z (p2Idx (Sum.inr b'))) = 0 := by
      refine Finset.sum_eq_zero (fun b' _ => ?_)
      rw [p2RotB, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, zero_smul]
    have hblock : (∑ b' : Fin 2, p2RotB μ (Sum.inl b') (Sum.inl b)
        • p2Frame z (p2Idx (Sum.inl b')))
        = ∑ b' : Fin 2, p2RotMat μ b' b • cE6 (twoE (lamUnit z) b') := by
      refine Finset.sum_congr rfl (fun b' _ => ?_)
      rw [p2RotB, Matrix.fromBlocks_apply₁₁, p2Frame, p2VecC_inl]
    rw [hcross, add_zero, hblock]
    have hleft : p2Frame (μ • z) (p2Idx (Sum.inl b))
        = cE6 (twoE (μ • lamUnit z) b) := by
      simp only [p2Frame, p2VecC, p2VecB, Sum.elim_inl, Equiv.symm_apply_apply, hL]
    rw [hleft, Fin.sum_univ_two]
    exact twoE_smul_apply (lamUnit z) μ b
  · have hcross : (∑ b' : Fin 2, p2RotB μ (Sum.inl b') (Sum.inr b)
        • p2Frame z (p2Idx (Sum.inl b'))) = 0 := by
      refine Finset.sum_eq_zero (fun b' _ => ?_)
      rw [p2RotB, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_smul]
    have hblock : (∑ b' : Fin 2, p2RotB μ (Sum.inr b') (Sum.inr b)
        • p2Frame z (p2Idx (Sum.inr b')))
        = ∑ b' : Fin 2, p2RotMat μ b' b • cE6 (twoE (wUnit z) b') := by
      refine Finset.sum_congr rfl (fun b' _ => ?_)
      rw [p2RotB, Matrix.fromBlocks_apply₂₂, p2Frame, p2VecC_inr]
    rw [hcross, zero_add, hblock]
    have hleft : p2Frame (μ • z) (p2Idx (Sum.inr b))
        = cE6 (twoE (μ • wUnit z) b) := by
      simp only [p2Frame, p2VecC, p2VecB, Sum.elim_inr, Equiv.symm_apply_apply, hW]
    rw [hleft, Fin.sum_univ_two]
    exact twoE_smul_apply (wUnit z) μ b

theorem p2Frame_ofReal_smul (z : E5) {a : ℝ} (ha : 0 < a) :
    p2Frame ((a : ℂ) • z) = p2Frame z := by
  have h1 : lamUnit ((a : ℂ) • z) = lamUnit z := lamUnit_smul_ofReal z ha
  have h2 : wUnit ((a : ℂ) • z) = wUnit z := wUnit_smul_ofReal z ha
  funext i
  obtain ⟨p, rfl⟩ := p2Idx.surjective i
  rcases p with b | b <;>
    simp only [p2Frame, p2VecC, p2VecB, Sum.elim_inl, Sum.elim_inr,
      Equiv.symm_apply_apply, h1, h2]

/-! ## The map on `ℂP⁴` -/

/-- The Stiefel point of the plane of a nonzero representative `v : Fin 5 → ℂ`. -/
noncomputable def p2StiefelF (v : {v : Fin 5 → ℂ // v ≠ 0}) : Stiefel 4 8 :=
  ⟨p2Frame (cfOf v.1), p2Frame_orthonormal (cfOf v.1) (cfOf_ne_zero v.2)⟩

theorem p2StiefelF_val (v : {v : Fin 5 → ℂ // v ≠ 0}) :
    (p2StiefelF v).1 = p2Frame (cfOf v.1) := rfl

theorem continuous_p2FrameF :
    Continuous fun v : {v : Fin 5 → ℂ // v ≠ 0} => p2Frame (cfOf v.1) := by
  have hcf : Continuous fun v : {v : Fin 5 → ℂ // v ≠ 0} => cfOf v.1 :=
    continuous_cfOf.comp continuous_subtype_val
  have hsub : Continuous fun v : {v : Fin 5 → ℂ // v ≠ 0} =>
      (⟨cfOf v.1, cfOf_ne_zero v.2⟩ : {z : E5 // z ≠ 0}) :=
    Continuous.subtype_mk hcf (fun v => cfOf_ne_zero v.2)
  have hcomp : (fun v : {v : Fin 5 → ℂ // v ≠ 0} => p2Frame (cfOf v.1))
      = (fun z : {z : E5 // z ≠ 0} => p2Frame z.1) ∘
        (fun v : {v : Fin 5 → ℂ // v ≠ 0} => (⟨cfOf v.1, cfOf_ne_zero v.2⟩ : {z : E5 // z ≠ 0})) := rfl
  rw [hcomp]
  exact continuous_p2Frame_subtype.comp hsub

theorem continuous_p2StiefelF : Continuous p2StiefelF :=
  Continuous.subtype_mk continuous_p2FrameF
    (fun v => p2Frame_orthonormal (cfOf v.1) (cfOf_ne_zero v.2))

theorem p2Stiefel_smul_condition :
    ∀ (a b : {z : E5 // z ≠ 0}) (t : ℂ), (a : E5) = t • (b : E5) →
      ogMk 4 8 (p2Stiefel a) = ogMk 4 8 (p2Stiefel b) := by
  intro a b t h
  by_cases ht : t = 0
  · rw [ht, zero_smul] at h
    exact absurd h a.2
  · have htn : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
    set μ : ℂ := t / ((‖t‖ : ℝ) : ℂ) with hμdef
    have hcn : (((‖t‖ : ℝ)) : ℂ) ≠ 0 := by
      simpa using htn
    have hμ : ‖μ‖ = 1 := by
      have h1 : ‖(((‖t‖ : ℝ)) : ℂ)‖ = ‖t‖ := by simp
      rw [hμdef, norm_div, h1, div_self htn]
    have htq : ((‖t‖ : ℝ) : ℂ) * μ = t := by
      rw [hμdef, mul_comm, div_mul_cancel₀ t hcn]
    have hsplit : (a : E5) = ((‖t‖ : ℝ) : ℂ) • (μ • (b : E5)) := by
      rw [smul_smul, htq, h]
    have hpos : 0 < ‖t‖ := norm_pos_iff.mpr ht
    set A : SOk 4 := ⟨p2Rot μ, isSO_p2Rot hμ⟩ with hA
    have heq : p2Stiefel a = A.act (p2Stiefel b) := by
      apply Subtype.ext
      show p2Frame (a : E5) = soActFun (k := 4) (m := 8) (p2Rot μ) (p2Frame (b : E5))
      rw [hsplit, p2Frame_ofReal_smul _ hpos, p2Frame_smul_unit _ hμ]
    rw [heq]
    exact Quotient.sound ⟨A.transpose, (SOk.act_transpose_act A (p2Stiefel b)).symm⟩

theorem p2StiefelF_smul_condition :
    ∀ (a b : {v : Fin 5 → ℂ // v ≠ 0}) (t : ℂ), (a : Fin 5 → ℂ) = t • (b : Fin 5 → ℂ) →
      ogMk 4 8 (p2StiefelF a) = ogMk 4 8 (p2StiefelF b) := by
  intro a b t h
  refine p2Stiefel_smul_condition ⟨cfOf a.1, cfOf_ne_zero a.2⟩
    ⟨cfOf b.1, cfOf_ne_zero b.2⟩ t ?_
  rw [← cfOf_smul]
  exact congrArg cfOf h

/-- The underlying function of the `p₂`-probe. -/
noncomputable def p2MapFun (x : CP 4) : OG 4 8 :=
  Projectivization.lift (fun v : {v : Fin 5 → ℂ // v ≠ 0} => ogMk 4 8 (p2StiefelF v))
    p2StiefelF_smul_condition x

theorem p2MapFun_apply (v : {v : Fin 5 → ℂ // v ≠ 0}) :
    p2MapFun (Projectivization.mk' ℂ v) = ogMk 4 8 (p2StiefelF v) :=
  Projectivization.lift_mk _ _ v.1 v.2

theorem continuous_p2MapFun : Continuous p2MapFun := by
  have hq : Topology.IsQuotientMap (Projectivization.mk' ℂ :
      {v : Fin 5 → ℂ // v ≠ 0} → CP 4) := isQuotientMap_quotient_mk'
  have hφ : Continuous (fun v : {v : Fin 5 → ℂ // v ≠ 0} => ogMk 4 8 (p2StiefelF v)) :=
    (ogMk 4 8).continuous.comp continuous_p2StiefelF
  have hcomp : p2MapFun ∘ (Projectivization.mk' ℂ :
        {v : Fin 5 → ℂ // v ≠ 0} → CP 4)
      = fun v => ogMk 4 8 (p2StiefelF v) :=
    funext (fun v => p2MapFun_apply v)
  rw [hq.continuous_iff, hcomp]
  exact hφ

/-- **The `p₂`-probe for `(k, m) = (4, 8)`**: the map sending a complex line of `ℂ⁵` to the
oriented real `4`-plane `ℝ-span{Λ(z), iΛ(z), Λ'(z), iΛ'(z)} ⊂ ℂ⁶ = ℝ¹²`. -/
noncomputable def p2Map : C(CP 4, OG 4 8) := ⟨p2MapFun, continuous_p2MapFun⟩

theorem p2Map_apply (v : {v : Fin 5 → ℂ // v ≠ 0}) :
    p2Map (Projectivization.mk' ℂ v) = ogMk 4 8 (p2StiefelF v) := p2MapFun_apply v

end

end Work.ThomBordism.Grassmann.P2Base
