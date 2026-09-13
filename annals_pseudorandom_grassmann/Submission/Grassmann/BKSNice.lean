import Submission.Grassmann.BKSHom
import Submission.Grassmann.Duality
open Finset BigOperators Matrix
open Classical
open PseudorandomGrassmann
open Module
set_option autoImplicit false
set_option maxHeartbeats 1000000
local notation "𝔽₂" => ZMod 2
namespace Submission.Grassmann
noncomputable section
variable {k ℓ : ℕ}

def projFirstFin (h : ℓ ≤ k) : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin ℓ → 𝔽₂) :=
  LinearMap.pi fun i : Fin ℓ => LinearMap.proj ((subLtEquiv h).symm i).1

@[simp] lemma projFirstFin_apply (h : ℓ ≤ k) (v : Fin k → 𝔽₂) (i : Fin ℓ) :
    projFirstFin h v i = v ((subLtEquiv h).symm i).1 := rfl

def projLastFin (h : ℓ ≤ k) : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin (k - ℓ) → 𝔽₂) :=
  LinearMap.pi fun j : Fin (k - ℓ) => LinearMap.proj ((subGeEquiv h).symm j).1

@[simp] lemma projLastFin_apply (h : ℓ ≤ k) (v : Fin k → 𝔽₂) (j : Fin (k - ℓ)) :
    projLastFin h v j = v ((subGeEquiv h).symm j).1 := rfl

def pairVecFin (h : ℓ ≤ k) (y : Fin ℓ → 𝔽₂) (u : Fin (k - ℓ) → 𝔽₂) : Fin k → 𝔽₂ :=
  fun i => if hi : (i : ℕ) < ℓ then y (subLtEquiv h ⟨i, hi⟩)
    else u (subGeEquiv h ⟨i, le_of_not_gt hi⟩)

lemma projFirstFin_pairVecFin (h : ℓ ≤ k) (y : Fin ℓ → 𝔽₂) (u : Fin (k - ℓ) → 𝔽₂) :
    projFirstFin h (pairVecFin h y u) = y := by
  funext i
  rw [projFirstFin_apply, pairVecFin, dif_pos ((subLtEquiv h).symm i).2]
  exact congrArg y ((subLtEquiv h).apply_symm_apply i)

lemma projLastFin_pairVecFin (h : ℓ ≤ k) (y : Fin ℓ → 𝔽₂) (u : Fin (k - ℓ) → 𝔽₂) :
    projLastFin h (pairVecFin h y u) = u := by
  funext j
  rw [projLastFin_apply, pairVecFin, dif_neg (by have := ((subGeEquiv h).symm j).2; omega)]
  exact congrArg u ((subGeEquiv h).apply_symm_apply j)

lemma eq_of_projFin_eq (h : ℓ ≤ k) {v w : Fin k → 𝔽₂}
    (h1 : projFirstFin h v = projFirstFin h w) (h2 : projLastFin h v = projLastFin h w) : v = w := by
  funext i
  by_cases hi : (i : ℕ) < ℓ
  · have := congrFun h1 (subLtEquiv h ⟨i, hi⟩)
    simpa [projFirstFin_apply] using this
  · have hge : ℓ ≤ (i : ℕ) := le_of_not_gt hi
    have := congrFun h2 (subGeEquiv h ⟨i, hge⟩)
    simpa [projLastFin_apply] using this

def canonVecFin (h : ℓ ≤ k) (L : VGood k ℓ) (i : Fin ℓ) : Fin k → 𝔽₂ :=
  canonVec L ((subLtEquiv h).symm i)

lemma projFirstFin_canonVecFin (h : ℓ ≤ k) (L : VGood k ℓ) (i : Fin ℓ) :
    projFirstFin h (canonVecFin h L i) = Pi.single i 1 := by
  have h1 : projFirst ℓ k (canonVecFin h L i) = Pi.single ((subLtEquiv h).symm i) 1 :=
    projFirst_canonVec L ((subLtEquiv h).symm i)
  funext i'
  have h2 : (projFirst ℓ k (canonVecFin h L i)) ((subLtEquiv h).symm i') =
      ((if i' = i then (1:𝔽₂) else 0) : 𝔽₂) := by
    rw [h1, Pi.single_apply]
    by_cases hb : i' = i
    · rw [if_pos (by rw [hb]), if_pos hb]
    · rw [if_neg (fun hc => hb ((subLtEquiv h).symm.injective hc)), if_neg hb]
  simpa [projFirstFin_apply, projFirst_apply, Pi.single_apply] using h2

lemma projLastFin_canonVecFin (h : ℓ ≤ k) (L : VGood k ℓ) (i : Fin ℓ) :
    projLastFin h (canonVecFin h L i) = phiFin h L i := by
  funext j
  rw [projLastFin_apply, phiFin_apply]
  rfl

lemma mem_span_canonVecFin (h : ℓ ≤ k) (L : VGood k ℓ) {x : Fin k → 𝔽₂}
    (hx : x ∈ L.carrier) : x ∈ Submodule.span 𝔽₂ (Set.range (canonVecFin h L)) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun 𝔽₂).mp (mem_span_canonVec h L hx)
  rw [Submodule.mem_span_range_iff_exists_fun 𝔽₂]
  refine ⟨fun i : Fin ℓ => c ((subLtEquiv h).symm i), ?_⟩
  rw [← hc]
  exact Fintype.sum_bijective ((subLtEquiv h).symm : Fin ℓ → {i : Fin k // (i : ℕ) < ℓ})
    ((subLtEquiv h).symm.bijective)
    (fun i : Fin ℓ => c ((subLtEquiv h).symm i) • canonVecFin h L i)
    (fun x : {i : Fin k // (i : ℕ) < ℓ} => c x • canonVec L x) (fun i => rfl)

lemma projFirstFin_injOn (h : ℓ ≤ k) (L : VGood k ℓ) {v w : Fin k → 𝔽₂}
    (hv : v ∈ L.carrier) (hw : w ∈ L.carrier) (hh : projFirstFin h v = projFirstFin h w) : v = w := by
  apply projFirst_injOn h L v w hv hw
  funext i
  have := congrFun hh (subLtEquiv h i)
  simpa [projFirstFin_apply] using this

/-- The dot product as a linear map into the dual. -/
noncomputable def dotLinLin (n : ℕ) :
    (Fin n → 𝔽₂) →ₗ[𝔽₂] Module.Dual 𝔽₂ (Fin n → 𝔽₂) :=
  ∑ j : Fin n, (LinearMap.smulRight (LinearMap.proj j) (LinearMap.proj j) :
    (Fin n → 𝔽₂) →ₗ[𝔽₂] Module.Dual 𝔽₂ (Fin n → 𝔽₂))

lemma dotLinLin_apply (n : ℕ) (w q : Fin n → 𝔽₂) :
    dotLinLin n w q = ∑ j, w j * q j := by
  simp only [dotLinLin, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]

variable {n' m' : ℕ}

noncomputable def Omega (h : ℓ ≤ k) (T₀ : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂) :
    (Fin k → 𝔽₂) →ₗ[𝔽₂] Module.Dual 𝔽₂ (Fin (k - ℓ) → 𝔽₂) :=
  (dotLinLin (k - ℓ)).comp (projLastFin h) -
    (dotLinLin (k - ℓ)).comp ((T₀.transpose).mulVecLin.comp (projFirstFin h))

lemma pair_swap (T₀ : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂) (q : Fin (k - ℓ) → 𝔽₂)
    (w : Fin ℓ → 𝔽₂) :
    (∑ j, ((T₀.transpose).mulVec w) j * q j) = ∑ j, (T₀.mulVec q) j * w j := by
  show ((T₀.transpose).mulVec w) ⬝ᵥ q = (T₀.mulVec q) ⬝ᵥ w
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

lemma Omega_apply (h : ℓ ≤ k) (T₀ : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂) (v : Fin k → 𝔽₂)
    (q : Fin (k - ℓ) → 𝔽₂) :
    Omega h T₀ v q = (∑ j, projLastFin h v j * q j) - ∑ j, (T₀.mulVec q) j * projFirstFin h v j := by
  rw [Omega, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.sub_apply, LinearMap.comp_apply, Matrix.mulVecLin_apply,
    dotLinLin_apply, dotLinLin_apply, pair_swap]

noncomputable def Bsub (h : ℓ ≤ k) (Q : Matrix (Fin n') (Fin (k - ℓ)) 𝔽₂)
    (T₀ : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂) : Submodule 𝔽₂ (Fin k → 𝔽₂) :=
  LinearMap.ker ((LinearMap.dualMap (LinearMap.ker Q.mulVecLin).subtype).comp (Omega h T₀))

lemma mem_Bsub_iff (h : ℓ ≤ k) (Q : Matrix (Fin n') (Fin (k - ℓ)) 𝔽₂)
    (T₀ : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂) (v : Fin k → 𝔽₂) :
    v ∈ Bsub h Q T₀ ↔ ∀ q ∈ LinearMap.ker Q.mulVecLin, Omega h T₀ v q = 0 := by
  rw [Bsub, LinearMap.mem_ker]
  constructor
  · intro hv q hq
    have := DFunLike.congr_fun hv ⟨q, hq⟩
    simpa [LinearMap.dualMap_apply] using this
  · intro hv
    refine LinearMap.ext fun q => ?_
    simpa [LinearMap.dualMap_apply] using hv q.1 q.2

lemma omega_canonVecFin (h : ℓ ≤ k) (T₀ : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂)
    (L : VGood k ℓ) (q : Fin (k - ℓ) → 𝔽₂) (i : Fin ℓ) :
    Omega h T₀ (canonVecFin h L i) q = ((phiFin h L - T₀).mulVec q) i := by
  rw [Omega_apply, projLastFin_canonVecFin, projFirstFin_canonVecFin]
  rw [show (∑ j, phiFin h L i j * q j) = (phiFin h L *ᵥ q) i from rfl]
  rw [show (∑ j, (T₀.mulVec q) j * (Pi.single i (1:𝔽₂) : Fin ℓ → 𝔽₂) j) = (T₀ *ᵥ q) i from by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Pi.single_apply, hj]
    · intro hh; exact absurd (Finset.mem_univ i) hh]
  rw [Matrix.sub_mulVec, Pi.sub_apply]

lemma omega_add (h : ℓ ≤ k) (T₀ : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂)
    (q q' : Fin (k - ℓ) → 𝔽₂) (v : Fin k → 𝔽₂) :
    Omega h T₀ v (q + q') = Omega h T₀ v q + Omega h T₀ v q' := by
  rw [Omega_apply, Omega_apply, Omega_apply]
  have h1 : ∀ j, projLastFin h v j * (q + q') j
      = projLastFin h v j * q j + projLastFin h v j * q' j := fun j => by
    rw [Pi.add_apply, mul_add]
  have h2 : ∀ j, (T₀.mulVec (q + q')) j * projFirstFin h v j
      = (T₀.mulVec q) j * projFirstFin h v j + (T₀.mulVec q') j * projFirstFin h v j := by
    intro j
    rw [Matrix.mulVec_add, Pi.add_apply, add_mul]
  simp only [h1, h2, Finset.sum_add_distrib]
  ring

lemma omega_smul (h : ℓ ≤ k) (T₀ : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂) (c : 𝔽₂)
    (q : Fin (k - ℓ) → 𝔽₂) (v : Fin k → 𝔽₂) :
    Omega h T₀ v (c • q) = c * Omega h T₀ v q := by
  rw [Omega_apply, Omega_apply]
  have h1 : ∀ j, projLastFin h v j * (c • q) j = c * (projLastFin h v j * q j) := fun j => by
    rw [Pi.smul_apply, smul_eq_mul]; ring
  have h2 : ∀ j, (T₀.mulVec (c • q)) j * projFirstFin h v j
      = c * ((T₀.mulVec q) j * projFirstFin h v j) := by
    intro j
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]; ring
  simp only [h1, h2]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]

/-- The linear map `y ↦ (y, T₀ᵀ y)`. -/
noncomputable def AΦ (h : ℓ ≤ k) (T₀ : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂) :
    (Fin ℓ → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂) :=
  LinearMap.pi fun i : Fin k =>
    if hi : (i : ℕ) < ℓ then LinearMap.proj (subLtEquiv h ⟨i, hi⟩)
    else (LinearMap.proj (subGeEquiv h ⟨i, le_of_not_gt hi⟩)).comp T₀.transpose.mulVecLin

lemma AΦ_apply (h : ℓ ≤ k) (T₀ : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂) (y : Fin ℓ → 𝔽₂) :
    AΦ h T₀ y = pairVecFin h y (T₀.transpose.mulVec y) := by
  funext i
  rw [AΦ, LinearMap.pi_apply]
  by_cases hi : (i : ℕ) < ℓ
  · rw [dif_pos hi, pairVecFin, dif_pos hi]
    rfl
  · rw [dif_neg hi, pairVecFin, dif_neg hi]
    rfl

noncomputable def Asub (h : ℓ ≤ k) (ι : Matrix (Fin ℓ) (Fin m') 𝔽₂)
    (T₀ : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂) : Submodule 𝔽₂ (Fin k → 𝔽₂) :=
  LinearMap.range ((AΦ h T₀).comp (F2.ortho (LinearMap.range ι.mulVecLin)).subtype)

lemma finrank_Asub_le (h : ℓ ≤ k) (ι : Matrix (Fin ℓ) (Fin m') 𝔽₂)
    (T₀ : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂) :
    Module.finrank 𝔽₂ (Asub h ι T₀) ≤ ℓ - Module.finrank 𝔽₂ (LinearMap.range ι.mulVecLin) := by
  have h1 : Module.finrank 𝔽₂ (Asub h ι T₀) ≤
      Module.finrank 𝔽₂ ↥(F2.ortho (LinearMap.range ι.mulVecLin)) := by
    rw [Asub]
    have hrn := LinearMap.finrank_range_add_finrank_ker
      ((AΦ h T₀).comp (F2.ortho (LinearMap.range ι.mulVecLin)).subtype)
    omega
  rwa [F2.finrank_ortho] at h1

lemma finrank_Bsub (h : ℓ ≤ k) (Q : Matrix (Fin n') (Fin (k - ℓ)) 𝔽₂)
    (T₀ : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂) :
    k - Module.finrank 𝔽₂ (Bsub h Q T₀) ≤ Module.finrank 𝔽₂ ↥(LinearMap.ker Q.mulVecLin) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker
    ((LinearMap.dualMap (LinearMap.ker Q.mulVecLin).subtype).comp (Omega h T₀))
  have hE : Module.finrank 𝔽₂ (Fin k → 𝔽₂) = k := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hle : Module.finrank 𝔽₂ (LinearMap.range ((LinearMap.dualMap
        (LinearMap.ker Q.mulVecLin).subtype).comp (Omega h T₀)))
      ≤ Module.finrank 𝔽₂ ↥(LinearMap.ker Q.mulVecLin) := by
    refine le_trans (Submodule.finrank_mono le_top) ?_
    rw [finrank_top, Subspace.dual_finrank_eq]
  have hB : Module.finrank 𝔽₂ (Bsub h Q T₀) = Module.finrank 𝔽₂
      ↥(LinearMap.ker ((LinearMap.dualMap (LinearMap.ker Q.mulVecLin).subtype).comp (Omega h T₀))) :=
    rfl
  rw [hE] at hrn
  omega

/-! ## The pullback: nice matrix sets and `SubGr` -/

lemma projFirstFin_sum_canonVec (h : ℓ ≤ k) (L : VGood k ℓ) (y : Fin ℓ → 𝔽₂) :
    projFirstFin h (∑ i : Fin ℓ, y i • canonVecFin h L i) = y := by
  rw [map_sum]
  funext i
  simp only [Finset.sum_apply, map_smul, projFirstFin_canonVecFin, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, mul_one]
  · intro j _ hj
    rw [Pi.single_eq_of_ne (Ne.symm hj), mul_zero]
  · intro hh; exact absurd (Finset.mem_univ i) hh

lemma projLastFin_sum_canonVec (h : ℓ ≤ k) (L : VGood k ℓ) (y : Fin ℓ → 𝔽₂) :
    projLastFin h (∑ i : Fin ℓ, y i • canonVecFin h L i) = (phiFin h L).transpose.mulVec y := by
  rw [map_sum]
  funext j
  simp only [Finset.sum_apply, map_smul, projLastFin_canonVecFin, Pi.smul_apply, smul_eq_mul]
  rw [Matrix.mulVec_transpose]
  rfl

lemma sum_canonVec_mem (h : ℓ ≤ k) (L : VGood k ℓ) (y : Fin ℓ → 𝔽₂) :
    (∑ i : Fin ℓ, y i • canonVecFin h L i) ∈ L.carrier :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (canonVec_mem L ((subLtEquiv h).symm i))

lemma sum_canonVec_eq_pairVec (h : ℓ ≤ k) (L : VGood k ℓ) (y : Fin ℓ → 𝔽₂) :
    (∑ i : Fin ℓ, y i • canonVecFin h L i)
      = pairVecFin h y ((phiFin h L).transpose.mulVec y) := by
  refine eq_of_projFin_eq h ?_ ?_
  · rw [projFirstFin_sum_canonVec, projFirstFin_pairVecFin]
  · rw [projLastFin_sum_canonVec, projLastFin_pairVecFin]

lemma vecMul_transpose_of_range_le {N : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂}
    {ι : Matrix (Fin ℓ) (Fin m') 𝔽₂} (hr : LinearMap.range N.mulVecLin ≤ LinearMap.range ι.mulVecLin)
    {y : Fin ℓ → 𝔽₂} (hy : y ∈ F2.ortho (LinearMap.range ι.mulVecLin)) : y ᵥ* N = 0 := by
  funext j
  have h1 : N.mulVec (Pi.single j (1:𝔽₂)) ∈ LinearMap.range ι.mulVecLin := hr ⟨_, rfl⟩
  have h2 := (F2.mem_ortho.mp hy) _ h1
  rw [Matrix.vecMul, dotProduct]
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h2

/-- **The pullback of a nice set of matrices**: the matrices `phiFin h L` with
`ker Q ≤ ker (phiFin h L - T₀)` and `range (phiFin h L - T₀) ≤ range ι` are exactly those
`L` with `Asub h ι T₀ ≤ L ≤ Bsub h Q T₀`. -/
theorem pullback (h : ℓ ≤ k) (Q : Matrix (Fin n') (Fin (k - ℓ)) 𝔽₂)
    (ι : Matrix (Fin ℓ) (Fin m') 𝔽₂) (T₀ : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂) (L : VGood k ℓ) :
    (LinearMap.ker Q.mulVecLin ≤ LinearMap.ker ((phiFin h L - T₀).mulVecLin) ∧
      LinearMap.range ((phiFin h L - T₀).mulVecLin) ≤ LinearMap.range ι.mulVecLin) ↔
    (Asub h ι T₀ ≤ L.carrier ∧ L.carrier ≤ Bsub h Q T₀) := by
  have hAsub : ∀ y : Fin ℓ → 𝔽₂, y ∈ F2.ortho (LinearMap.range ι.mulVecLin) →
      AΦ h T₀ y ∈ Asub h ι T₀ := by
    intro y hy
    rw [Asub]
    exact ⟨⟨y, hy⟩, rfl⟩
  constructor
  · intro ⟨hk, hr⟩
    have key : ∀ y ∈ F2.ortho (LinearMap.range ι.mulVecLin),
        (phiFin h L).transpose.mulVec y = T₀.transpose.mulVec y := by
      intro y hy
      have h0 : y ᵥ* (phiFin h L - T₀) = 0 :=
        vecMul_transpose_of_range_le (N := phiFin h L - T₀) hr hy
      have h1 : (phiFin h L - T₀).transpose.mulVec y = 0 := by
        rw [Matrix.mulVec_transpose]; exact h0
      rw [Matrix.transpose_sub, Matrix.sub_mulVec] at h1
      exact sub_eq_zero.mp h1
    constructor
    · rintro v hv
      rw [Asub] at hv
      obtain ⟨y, rfl⟩ := hv
      show AΦ h T₀ y.1 ∈ L.carrier
      rw [AΦ_apply, ← key y.1 y.2, ← sum_canonVec_eq_pairVec h L y.1]
      exact sum_canonVec_mem h L y.1
    · intro v hv
      rw [mem_Bsub_iff]
      intro q hq
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun 𝔽₂).mp
        (mem_span_canonVecFin h L hv)
      rw [← hc, map_sum]
      conv_lhs => rw [LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      have h2 : Omega h T₀ (canonVecFin h L i) q = 0 := by
        rw [omega_canonVecFin, Matrix.sub_mulVec, Pi.sub_apply]
        have h3 := congrFun ((LinearMap.mem_ker).mp (hk hq)) i
        rw [Matrix.mulVecLin_apply, Pi.zero_apply, Matrix.sub_mulVec, Pi.sub_apply] at h3
        exact h3
      rw [h2, mul_zero]
  · intro ⟨hA, hB⟩
    have key : ∀ y ∈ F2.ortho (LinearMap.range ι.mulVecLin),
        (phiFin h L).transpose.mulVec y = T₀.transpose.mulVec y := by
      intro y hy
      have hmem : pairVecFin h y (T₀.transpose.mulVec y) ∈ L.carrier := by
        rw [← AΦ_apply]
        exact hA (hAsub y hy)
      have h1 : (∑ i : Fin ℓ, y i • canonVecFin h L i)
          = pairVecFin h y (T₀.transpose.mulVec y) :=
        projFirstFin_injOn h L (sum_canonVec_mem h L y) hmem
          (by rw [projFirstFin_sum_canonVec, projFirstFin_pairVecFin])
      have h2 := congrArg (projLastFin h) h1
      rw [projLastFin_sum_canonVec, projLastFin_pairVecFin] at h2
      exact h2
    constructor
    · intro q hq
      rw [LinearMap.mem_ker]
      funext i
      rw [Matrix.mulVecLin_apply, Pi.zero_apply, ← omega_canonVecFin h T₀ L q i]
      exact (mem_Bsub_iff h Q T₀ (canonVecFin h L i)).mp
        (hB (canonVec_mem L ((subLtEquiv h).symm i))) q hq
    · intro x
      rintro ⟨z, rfl⟩
      rw [← F2.ortho_ortho (LinearMap.range ι.mulVecLin)]
      rw [F2.mem_ortho]
      intro y hy
      have h0 : (phiFin h L - T₀).transpose.mulVec y = 0 := by
        rw [Matrix.transpose_sub, Matrix.sub_mulVec, key y hy, sub_self]
      have h5 : y ⬝ᵥ ((phiFin h L - T₀).mulVec z) = 0 := by
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h0]
        simp [dotProduct]
      simp only [dotProduct, Matrix.mulVecLin_apply] at h5
      simp only [Matrix.mulVecLin_apply]
      rw [Finset.sum_congr rfl (fun i _ => mul_comm _ _), h5]

/-- **The pullback, in the form used by the assembly.** -/
theorem exists_subGr_of_nice (h : ℓ ≤ k) (Q : Matrix (Fin n') (Fin (k - ℓ)) 𝔽₂)
    (ι : Matrix (Fin ℓ) (Fin m') 𝔽₂) (T₀ : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂) :
    ∃ A B : Submodule 𝔽₂ (Fin k → 𝔽₂),
      Module.finrank 𝔽₂ A + (k - Module.finrank 𝔽₂ B) ≤
        Module.finrank 𝔽₂ ↥(LinearMap.ker Q.mulVecLin) +
          (ℓ - Module.finrank 𝔽₂ ↥(LinearMap.range ι.mulVecLin)) ∧
      ∀ L : VGood k ℓ,
        (LinearMap.ker Q.mulVecLin ≤ LinearMap.ker ((phiFin h L - T₀).mulVecLin) ∧
          LinearMap.range ((phiFin h L - T₀).mulVecLin) ≤ LinearMap.range ι.mulVecLin) ↔
        (A ≤ L.carrier ∧ L.carrier ≤ B) := by
  refine ⟨Asub h ι T₀, Bsub h Q T₀, ?_, fun L => pullback h Q ι T₀ L⟩
  linarith [finrank_Asub_le h ι T₀, finrank_Bsub h Q T₀]

end
end Submission.Grassmann
