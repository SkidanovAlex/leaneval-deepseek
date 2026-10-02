import Mathlib
import Submission.Work.ThomBordism.Grassmann.FibreBaseDefs
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.Grassmann.PlaneEval
import Submission.Work.ThomBordism.Grassmann.GrassmannianTopology
import Submission.Work.ThomBordism.Grassmann.SphereCover
import Submission.Work.ThomBordism.Grassmann.Frame
import Submission.Work.ThomBordism.Grassmann.blockMat_isSO
import Submission.Work.ThomBordism.Grassmann.submatrix_ct_isSO
import Submission.Work.ThomBordism.Grassmann.fibreBaseAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-!
# The fibre of the tautological bundle at the base vector

The set of oriented `k`-planes in `ℝ^{k+m}` containing the fixed line `baseVec k m` is in canonical
bijection with the oriented `(k-1)`-planes in `baseVec k m ^⊥ ≅ ℝ^{(k-1)+m}`.  This module exhibits
the bijection as the continuous map `Ω : G̃r_{k-1}(ℝ^{(k-1)+m}) → {P | baseVec ∈ P}` which appends
the vector `baseVec` to a `(k-1)`-frame; it is a continuous bijection from a compact space to a
Hausdorff space, hence a homeomorphism (`fibreBaseHomeomorph`).
-/

namespace Work.ThomBordism.Grassmann

open scoped Topology

noncomputable section

variable {k m : ℕ}

/-! ## Extracting coefficients of a combination of an orthonormal frame -/

/-- **The coefficient of an orthonormal frame**: for an orthonormal family `F`, the `(i,j)` entry of
a matrix `A` is the inner product of `F i` with the `j`-th vector of `A · F`. -/
theorem soAct_entry {n M : ℕ} {F : Fin n → Amb (n + M)} (hF : Orthonormal ℝ F)
    (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    A i j = inner ℝ (F i) (soActFun A F j) := by
  have h := orthonormal_iff_ite.mp hF
  rw [soActFun, inner_sum, Finset.sum_eq_single i]
  · rw [inner_smul_right, h i i, if_pos rfl, mul_one]
  · intro b _ hb
    rw [inner_smul_right, h i b, if_neg (Ne.symm hb), mul_zero]
  · intro hmem; exact absurd (Finset.mem_univ i) hmem

/-! ## The frame obtained by appending `baseVec` -/

/-- **The `k`-frame `(snocE h_0, …, snocE h_{k-2}, baseVec k m)`** attached to a `(k-1)`-frame
`h`: the frame of the oriented `k`-plane spanned by the image of `h` together with `baseVec k m`. -/
def frameUb (k m : ℕ) (hk : 2 ≤ k) (h : Stiefel (k-1) m) : Fin k → Amb (k+m) :=
  fun i => if hi : i.val < k-1 then snocE k m (by omega) (h.1 ⟨i.val, hi⟩) else baseVec k m

theorem frameUb_ct (hk : 2 ≤ k) (h : Stiefel (k-1) m) (j : Fin (k-1)) :
    frameUb k m hk h (ct k (by omega) j) = snocE k m (by omega) (h.1 j) := by
  rw [frameUb, dif_pos (by rw [ct_val]; exact j.isLt)]
  exact congrArg (fun a => snocE k m (by omega) (h.1 a)) (Fin.ext rfl)

theorem frameUb_last (hk : 2 ≤ k) (h : Stiefel (k-1) m) :
    frameUb k m hk h (lastk k (by omega)) = baseVec k m := by
  rw [frameUb, dif_neg (by rw [lastk_val]; omega)]

theorem orthonormal_frameUb (hk : 2 ≤ k) (h : Stiefel (k-1) m) :
    Orthonormal ℝ (frameUb k m hk h) := by
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hi : i.val < k-1
  · by_cases hj : j.val < k-1
    · rw [frameUb, dif_pos hi, frameUb, dif_pos hj, LinearIsometry.inner_map_map,
        (orthonormal_iff_ite.mp h.2) ⟨i.val, hi⟩ ⟨j.val, hj⟩]
      by_cases hij : i = j
      · subst hij; rw [if_pos rfl, if_pos rfl]
      · rw [if_neg hij,
          if_neg (fun hh => hij (Fin.ext (by simpa using congrArg Fin.val hh)))]
    · have hj' : j.val = k-1 := by have := j.isLt; omega
      rw [frameUb, dif_pos hi, frameUb, dif_neg hj, inner_snocE_baseVec k m (by omega),
        if_neg (fun hij => by have := congrArg Fin.val hij; simp [hj'] at this; omega)]
  · have hi' : i.val = k-1 := by have := i.isLt; omega
    by_cases hj : j.val < k-1
    · rw [frameUb, dif_neg hi, frameUb, dif_pos hj, inner_baseVec_snocE k m (by omega),
        if_neg (fun hij => by have := congrArg Fin.val hij; simp [hi'] at this; omega)]
    · have hij : i = j := Fin.ext (by omega)
      rw [frameUb, dif_neg hi, frameUb, dif_neg hj, inner_baseVec_self k m (by omega), if_pos hij]

/-- **The `(k-1)`-frame upgrade**: the orthonormal `k`-frame `frameUb` as a point of the Stiefel
manifold. -/
def frameStiefel (hk : 2 ≤ k) (h : Stiefel (k-1) m) : Stiefel k m :=
  ⟨frameUb k m hk h, orthonormal_frameUb hk h⟩

theorem continuous_frameUb (hk : 2 ≤ k) : Continuous (frameUb k m hk) := by
  refine continuous_pi fun i => ?_
  by_cases hi : i.val < k-1
  · have h1 : (fun h : Stiefel (k-1) m => frameUb k m hk h i)
        = fun h => snocE k m (by omega) (h.1 ⟨i.val, hi⟩) := by
      funext h; rw [frameUb, dif_pos hi]
    rw [h1]
    exact (snocE k m (by omega)).continuous.comp
      ((continuous_apply (⟨i.val, hi⟩ : Fin (k-1))).comp continuous_subtype_val)
  · have h1 : (fun h : Stiefel (k-1) m => frameUb k m hk h i) = fun _ => baseVec k m := by
      funext h; rw [frameUb, dif_neg hi]
    rw [h1]; exact continuous_const

@[simp] theorem frameStiefel_val (hk : 2 ≤ k) (h : Stiefel (k-1) m) :
    (frameStiefel hk h).1 = frameUb k m hk h := by rw [frameStiefel]

@[simp] theorem soAct_act_val (A : SOk k) (h : Stiefel k m) :
    (SOk.act A h).1 = soActFun A.1 h.1 := by rw [SOk.act]

theorem continuous_frameStiefel (hk : 2 ≤ k) :
    Continuous (frameStiefel (k := k) (m := m) hk) :=
  Continuous.subtype_mk (continuous_frameUb (k := k) (m := m) hk)
    (fun h => orthonormal_frameUb hk h)

/-! ## Linearity of `snocE` over finite sums -/

theorem snocE_sum_smul_fibreBase (hk : 1 ≤ k) (c : Fin (k-1) → ℝ) (v : Fin (k-1) → Amb ((k-1)+m)) :
    (∑ j, c j • snocE k m hk (v j)) = snocE k m hk (∑ j, c j • v j) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul]

/-! ## The map on frames, and its compatibility with the group actions -/

/-- The action of the block matrix `diag(B,1)` on the frame `frameUb h`, in the last coordinate. -/
theorem soAct_blockMat_last (hk : 2 ≤ k) (B : Matrix (Fin (k-1)) (Fin (k-1)) ℝ)
    (h : Stiefel (k-1) m) :
    soActFun (blockMat k B) (frameUb k m hk h) (lastk k (by omega)) = baseVec k m := by
  rw [soActFun, sum_fin_eq k (by omega)
    (fun j => blockMat k B j (lastk k (by omega)) • frameUb k m hk h j)]
  rw [Finset.sum_eq_zero (fun j _ => by rw [blockMat_ct_last k (by omega) B j, zero_smul]),
    blockMat_last_last k (by omega) B, one_smul, frameUb_last, zero_add]

/-- The action of the block matrix `diag(B,1)` on the frame `frameUb h`, in the `i`-th of the first
`k-1` coordinates. -/
theorem soAct_blockMat_ct (hk : 2 ≤ k) (B : Matrix (Fin (k-1)) (Fin (k-1)) ℝ)
    (h : Stiefel (k-1) m) (i : Fin (k-1)) :
    soActFun (blockMat k B) (frameUb k m hk h) (ct k (by omega) i)
      = snocE k m (by omega) (soActFun B h.1 i) := by
  rw [soActFun, sum_fin_eq k (by omega)
    (fun j => blockMat k B j (ct k (by omega) i) • frameUb k m hk h j)]
  rw [Finset.sum_congr rfl (fun j _ => by rw [blockMat_ct_ct k (by omega) B j i, frameUb_ct]),
    blockMat_last_ct k (by omega) B i, zero_smul, add_zero, snocE_sum_smul_fibreBase, soActFun]

/-- **The frame inclusion is `SO(k-1)`-equivariant** (with the block matrix `diag(A,1)`). -/
theorem frameUb_act (hk : 2 ≤ k) (A : SOk (k-1)) (h : Stiefel (k-1) m) :
    frameUb k m hk (A.act h) = soActFun (blockMat k A.1) (frameUb k m hk h) := by
  funext i
  rcases eq_lastk_or_eq_ct k (by omega) i with hi | ⟨i', hi⟩
  · subst hi; rw [frameUb_last, soAct_blockMat_last]
  · subst hi; rw [frameUb_ct, soAct_blockMat_ct]; rfl

/-- The map on frames `h ↦ [frameUb h]` as a map into the Grassmannian. -/
def omegaMk (k m : ℕ) (hk : 2 ≤ k) (h : Stiefel (k-1) m) : OG k m :=
  Quotient.mk'' (frameStiefel hk h)

theorem omegaMk_act (hk : 2 ≤ k) (A : SOk (k-1)) (h : Stiefel (k-1) m) :
    omegaMk k m hk (A.act h) = omegaMk k m hk h := by
  have hC : IsSO (blockMat k A.1) := blockMat_isSO k (by omega) A.1 A.2
  have hsub : frameStiefel hk (A.act h)
      = SOk.act (⟨blockMat k A.1, hC⟩ : SOk k) (frameStiefel hk h) :=
    Subtype.ext (frameUb_act hk A h)
  exact (Quotient.sound (show (grassmannSetoid k m).r (frameStiefel hk h)
    (frameStiefel hk (A.act h)) from ⟨⟨blockMat k A.1, hC⟩, hsub⟩)).symm

/-- **The map `Ω : G̃r_{k-1}(ℝ^{(k-1)+m}) → G̃r_k(ℝ^{k+m})`** which appends the vector
`baseVec k m` to an oriented `(k-1)`-plane. -/
def omegaFun (k m : ℕ) (hk : 2 ≤ k) : OG (k-1) m → OG k m :=
  Quotient.lift (fun h => omegaMk k m hk h) fun h h' hh => by
    obtain ⟨A, rfl⟩ := hh
    exact (omegaMk_act hk A h).symm

@[simp] theorem omegaFun_mk (hk : 2 ≤ k) (h : Stiefel (k-1) m) :
    omegaFun k m hk (Quotient.mk'' h) = omegaMk k m hk h := rfl

theorem continuous_omegaMk (hk : 2 ≤ k) : Continuous (omegaMk (k := k) (m := m) hk) :=
  continuous_quotient_mk'.comp (continuous_frameStiefel hk)

theorem continuous_omegaFun (hk : 2 ≤ k) : Continuous (omegaFun (k := k) (m := m) hk) := by
  refine (isQuotientMap_quotient_mk' (X := Stiefel (k-1) m)
    (s := grassmannSetoid (k-1) m)).continuous_iff.mpr ?_
  exact (continuous_omegaMk (k := k) (m := m) hk).congr (fun x => (omegaFun_mk hk x).symm)

/-- `Ω` lands in the set of planes containing `baseVec k m`. -/
theorem memPlane_omegaFun (hk : 2 ≤ k) (x : OG (k-1) m) :
    memPlane (omegaFun k m hk x) (baseVec k m) := by
  induction x using Quotient.inductionOn with
  | h h =>
    refine ⟨frameStiefel hk h, rfl, ?_⟩
    exact Submodule.subset_span ⟨lastk k (by omega), frameUb_last hk h⟩

/-- **`Ω` as a map into the fibre of the base vector.** -/
def omega (k m : ℕ) (hk : 2 ≤ k) : OG (k-1) m → Subtype (fun P : OG k m =>
    memPlane P (baseVec k m)) :=
  fun x => ⟨omegaFun k m hk x, memPlane_omegaFun hk x⟩

@[simp] theorem omega_apply_val (hk : 2 ≤ k) (x : OG (k-1) m) :
    (omega k m hk x : OG k m) = omegaFun k m hk x := rfl

theorem continuous_omega (hk : 2 ≤ k) : Continuous (omega (k := k) (m := m) hk) :=
  Continuous.subtype_mk (continuous_omegaFun hk) _

/-! ## Injectivity of `Ω` -/

/-- The action of a matrix on the frame `frameUb h`, in the `i`-th of the first `k-1` coordinates,
as an explicit sum. -/
theorem soAct_frameUb_ct (hk : 2 ≤ k) (A : Matrix (Fin k) (Fin k) ℝ) (h : Stiefel (k-1) m)
    (i : Fin (k-1)) :
    soActFun A (frameUb k m hk h) (ct k (by omega) i)
      = snocE k m (by omega)
            (∑ j : Fin (k-1), A (ct k (by omega) j) (ct k (by omega) i) • h.1 j)
        + A (lastk k (by omega)) (ct k (by omega) i) • baseVec k m := by
  rw [soActFun, sum_fin_eq k (by omega)
    (fun j => A j (ct k (by omega) i) • frameUb k m hk h j)]
  rw [Finset.sum_congr rfl (fun j _ => by rw [frameUb_ct]), frameUb_last, snocE_sum_smul_fibreBase]

theorem omegaFun_injective (hk : 2 ≤ k) : Function.Injective (omegaFun (k := k) (m := m) hk) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
      simp only [omegaFun_mk, omegaMk] at hxy
      obtain ⟨A, hA⟩ := Quotient.exact hxy
      have hF : frameUb k m hk b = soActFun A.1 (frameUb k m hk a) := congrArg Subtype.val hA
      have hFa : Orthonormal ℝ (frameUb k m hk a) := orthonormal_frameUb hk a
      have hcol : ∀ i : Fin k, i ≠ lastk k (by omega) → A.1 (lastk k (by omega)) i = 0 := by
        intro i hi
        have h1 : A.1 (lastk k (by omega)) i
            = inner ℝ (frameUb k m hk a (lastk k (by omega))) (frameUb k m hk b i) := by
          rw [soAct_entry hFa A.1 (lastk k (by omega)) i, ← hF]
        rw [h1]
        rcases eq_lastk_or_eq_ct k (by omega) i with hi' | ⟨i', hi'⟩
        · exact absurd hi' hi
        · subst hi'
          rw [frameUb_last, frameUb_ct, inner_baseVec_snocE k m (by omega)]
      have hrow : ∀ j : Fin k, j ≠ lastk k (by omega) → A.1 j (lastk k (by omega)) = 0 := by
        intro j hj
        have h1 : A.1 j (lastk k (by omega))
            = inner ℝ (frameUb k m hk a j) (frameUb k m hk b (lastk k (by omega))) := by
          rw [soAct_entry hFa A.1 j (lastk k (by omega)), ← hF]
        rw [h1, frameUb_last]
        rcases eq_lastk_or_eq_ct k (by omega) j with hj' | ⟨j', hj'⟩
        · exact absurd hj' hj
        · subst hj'
          rw [frameUb_ct, inner_snocE_baseVec k m (by omega)]
      have hd : A.1 (lastk k (by omega)) (lastk k (by omega)) = 1 := by
        have h1 : A.1 (lastk k (by omega)) (lastk k (by omega))
            = inner ℝ (frameUb k m hk a (lastk k (by omega)))
                (frameUb k m hk b (lastk k (by omega))) := by
          rw [soAct_entry hFa A.1 (lastk k (by omega)) (lastk k (by omega)), ← hF]
        rw [h1, frameUb_last, frameUb_last, inner_baseVec_self k m (by omega)]
      have hB : IsSO (A.1.submatrix (ct k (by omega)) (ct k (by omega))) :=
        submatrix_ct_isSO k (by omega) A.1 A.2 hcol hrow hd
      refine Quotient.sound ⟨⟨A.1.submatrix (ct k (by omega)) (ct k (by omega)), hB⟩, ?_⟩
      apply Subtype.ext
      funext i
      have h2 : frameUb k m hk b (ct k (by omega) i)
          = snocE k m (by omega) (soActFun (A.1.submatrix (ct k (by omega)) (ct k (by omega))) a.1 i) := by
        rw [hF, soAct_frameUb_ct hk A.1 a i, hcol (ct k (by omega) i) (ct_ne_lastk k (by omega) i),
          zero_smul, add_zero]
        rfl
      rw [frameUb_ct] at h2
      exact snocE_injective k m (by omega) h2


/-! ## Surjectivity of `Ω` -/

theorem omega_surjective (hk : 2 ≤ k) : Function.Surjective (omega (k := k) (m := m) hk) := by
  rintro ⟨P, hP⟩
  obtain ⟨f, hf, hv⟩ := hP
  let L : Amb k →ₗᵢ[ℝ] Amb (k+m) := frameComb k m f
  have hLrange : L.range = Submodule.span ℝ (Set.range f.1) := by
    apply le_antisymm
    · rintro y ⟨v, rfl⟩
      rw [show L.toLinearMap v = ∑ i : Fin k, v.ofLp i • f.1 i from rfl]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro y ⟨i, rfl⟩
      refine ⟨EuclideanSpace.single i 1, ?_⟩
      rw [show L.toLinearMap (EuclideanSpace.single i (1 : ℝ)) = ∑ j : Fin k,
        (EuclideanSpace.single i (1 : ℝ)).ofLp j • f.1 j from rfl, Finset.sum_eq_single i]
      · rw [PiLp.single_apply, if_pos rfl, one_smul]
      · intro b _ hb
        rw [PiLp.single_apply, if_neg hb, zero_smul]
      · intro hmem; exact absurd (Finset.mem_univ i) hmem
  have hW : baseVec k m ∈ L.range := by rw [hLrange]; exact hv
  let c : Amb k := (L.equivRange).symm ⟨baseVec k m, hW⟩
  have hLc : L c = baseVec k m := by
    have h := (L.equivRange).apply_symm_apply ⟨baseVec k m, hW⟩
    exact congrArg Subtype.val h
  have hcnorm : ‖c‖ = 1 := by
    have h := (L.equivRange).norm_map c
    rw [← h]
    rw [show (L.equivRange) c = ⟨baseVec k m, hW⟩ from
      (L.equivRange).apply_symm_apply ⟨baseVec k m, hW⟩]
    rw [Submodule.coe_norm, norm_baseVec (by omega : k + m ≠ 0)]
  obtain ⟨M, hM, hMcol⟩ := exists_SO_lastColumn k hk c hcnorm
  have hMe : soActFun M f.1 (lastk k (by omega)) = baseVec k m := by
    rw [soActFun]
    rw [show (∑ i : Fin k, M i (lastk k (by omega)) • f.1 i)
        = ∑ i : Fin k, c.ofLp i • f.1 i from
      Finset.sum_congr rfl fun i _ => by rw [hMcol i]]
    rw [← frameComb_apply]
    exact hLc
  have hMorth : Orthonormal ℝ (soActFun M f.1) := orthonormal_soActFun hM.1 f.2
  have hge : ∀ i : Fin (k-1),
      inner ℝ (soActFun M f.1 (ct k (by omega) i)) (baseVec k m) = 0 := by
    intro i
    rw [← hMe, (orthonormal_iff_ite.mp hMorth) (ct k (by omega) i) (lastk k (by omega)),
      if_neg (ct_ne_lastk k (by omega) i)]
  have hhorth : Orthonormal ℝ
      (fun i : Fin (k-1) => truncE k m (by omega) (soActFun M f.1 (ct k (by omega) i))) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [show inner ℝ (truncE k m (by omega) (soActFun M f.1 (ct k (by omega) i)))
          (truncE k m (by omega) (soActFun M f.1 (ct k (by omega) j)))
        = inner ℝ (soActFun M f.1 (ct k (by omega) i))
            (soActFun M f.1 (ct k (by omega) j)) from by
      rw [← LinearIsometry.inner_map_map (snocE k m (by omega))
          (truncE k m (by omega) (soActFun M f.1 (ct k (by omega) i)))
          (truncE k m (by omega) (soActFun M f.1 (ct k (by omega) j))),
        snocE_truncE k m (by omega) _ (hge i), snocE_truncE k m (by omega) _ (hge j)]]
    rw [(orthonormal_iff_ite.mp hMorth) (ct k (by omega) i) (ct k (by omega) j)]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos (by rw [hij])]
    · rw [if_neg hij, if_neg (fun hh => hij (ct_injective k (by omega) hh))]
  let hfr : Stiefel (k-1) m := ⟨fun i : Fin (k-1) =>
      truncE k m (by omega) (soActFun M f.1 (ct k (by omega) i)), hhorth⟩
  let A' : SOk k := ⟨M, hM⟩
  have A'val : A'.1 = M := rfl
  have hfr_val : ∀ i : Fin (k-1),
      hfr.1 i = truncE k m (by omega) (soActFun M f.1 (ct k (by omega) i)) := fun i => rfl
  have hA' : frameStiefel hk hfr = A'.act f := by
    apply Subtype.ext
    funext i
    rw [frameStiefel_val, soAct_act_val, A'val]
    rcases eq_lastk_or_eq_ct k (by omega) i with hi | ⟨i', hi⟩
    · subst hi
      rw [frameUb_last]
      exact hMe.symm
    · subst hi
      rw [frameUb_ct, hfr_val i']
      exact snocE_truncE k m (by omega) _ (hge i')
  refine ⟨Quotient.mk'' hfr, ?_⟩
  apply Subtype.ext
  simp only [omega_apply_val, omegaFun_mk, omegaMk]
  rw [← hf]
  exact (Quotient.sound (show (grassmannSetoid k m).r f (frameStiefel hk hfr) from
    ⟨A', hA'⟩)).symm

theorem omega_injective (hk : 2 ≤ k) : Function.Injective (omega (k := k) (m := m) hk) :=
  fun x y hxy => omegaFun_injective (k := k) (m := m) hk (congrArg Subtype.val hxy)

theorem omega_bijective (hk : 2 ≤ k) : Function.Bijective (omega (k := k) (m := m) hk) :=
  ⟨omega_injective hk, omega_surjective hk⟩


theorem fibreBaseHomeomorph (k m : ℕ) (hk : 2 ≤ k) :
    Nonempty (Subtype (fun P : Work.ThomBordism.Grassmann.OG k m =>
        Work.ThomBordism.Grassmann.memPlane P (Work.ThomBordism.Grassmann.baseVec k m))
      ≃ₜ Work.ThomBordism.Grassmann.OG (k - 1) m) :=
  ⟨(Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective (omega (k := k) (m := m) hk)
    (omega_bijective hk)) (continuous_omega hk)).symm⟩

end

end Work.ThomBordism.Grassmann
