import Submission.Grassmann.Prop56

/-!
# Transposition of functions on `L(V,W)` (the "WLOG `dim V₁ ≥ 1`" duality)

arXiv:2209.04243 uses the duality `f ↦ f*` (`f*(A) = f(Aᵀ)`) to reduce an order-one derivative
in the `codim W₁ = 1` direction to the (already handled) `dim V₁ = 1` direction.  Under
transposition the pair `(V₁, W₁) = (ker Q, range ι)` becomes `(ker ιᵀ, range Qᵀ)`, so
`dim V₁` and `codim W₁` are exchanged.

This file collects the interaction of `transposeFun` with the analytic objects of the
bilinear-scheme Fourier calculus: `restr`, `shift`, `lapMulN`, `nprojPure`, `hybridPred`,
`hybridOrder`, `l2sq`, `GlobalBS` and `inflBS2`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-! ## Elementary algebra -/

lemma transposeFun_transposeFun {m n : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    transposeFun (transposeFun f) = f := by
  funext A; simp [transposeFun]

lemma transposeFun_add {m n : ℕ} (f g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    transposeFun (f + g) = transposeFun f + transposeFun g := by
  funext A; rfl

lemma transposeFun_sub {m n : ℕ} (f g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    transposeFun (f - g) = transposeFun f - transposeFun g := by
  funext A; rfl

lemma transposeFun_smul {m n : ℕ} (c : ℂ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    transposeFun (c • f) = c • transposeFun f := by
  funext A; rfl

lemma transposeFun_neg {m n : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    transposeFun (-f) = -transposeFun f := by
  funext A; rfl

/-! ## Interaction with the analytic objects -/

/-- Transposition commutes with restrictions, swapping the quotient and inclusion matrices. -/
lemma transposeFun_restr {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    transposeFun (restr Q ι f) = restr ιᵀ Qᵀ (transposeFun f) := by
  funext C
  simp only [transposeFun, restr]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_transpose, Matrix.mul_assoc]

/-- Transposition commutes with shifts. -/
lemma transposeFun_shift {m n : ℕ} (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    transposeFun (shift T f) = shift Tᵀ (transposeFun f) := by
  funext C
  simp only [transposeFun, shift, Matrix.transpose_add, Matrix.transpose_transpose]

/-- Transposition commutes with normalised Fourier multipliers, transposing the predicate. -/
lemma transposeFun_lapMulN {m n : ℕ} (P : Matrix (Fin n) (Fin m) 𝔽₂ → Prop)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    transposeFun (lapMulN P f) = lapMulN (fun Y : Matrix (Fin m) (Fin n) 𝔽₂ => P Yᵀ)
      (transposeFun f) := by
  refine eq_of_fhat_eq fun Y => ?_
  rw [fhat_transposeFun, fhat_lapMulN, fhat_lapMulN, fhat_transposeFun]

/-- Transposition preserves the normalised `L²` norm. -/
lemma l2sq_transposeFun {m n : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l2sq (transposeFun f) = l2sq f := by
  have hsum : (∑ A : Matrix (Fin n) (Fin m) 𝔽₂, ‖transposeFun f A‖ ^ 2) =
      ∑ B : Matrix (Fin m) (Fin n) 𝔽₂, ‖f B‖ ^ 2 :=
    Fintype.sum_equiv (Matrix.transposeAddEquiv (Fin n) (Fin m) 𝔽₂).toEquiv
      (fun A : Matrix (Fin n) (Fin m) 𝔽₂ => ‖transposeFun f A‖ ^ 2)
      (fun B : Matrix (Fin m) (Fin n) 𝔽₂ => ‖f B‖ ^ 2)
      (fun A => by simp [transposeFun])
  simp only [l2sq]
  rw [hsum, Nat.mul_comm m n]

/-- The normalised Fourier coefficients of the normalised pure-level projection. -/
lemma fhat_nprojPure {m n : ℕ} (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    fhat (nprojPure d f) X = (if X.rank = d then 1 else 0) * fhat f X := by
  rw [nprojPure, fhat_smul, fhat_projPure]
  by_cases hX : X.rank = d
  · rw [if_pos hX, if_pos hX]
    field_simp
  · rw [if_neg hX, if_neg hX]; ring

/-- Transposition commutes with the normalised pure-level projection. -/
lemma transposeFun_nprojPure {m n d : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    transposeFun (nprojPure d f) = nprojPure d (transposeFun f) := by
  refine eq_of_fhat_eq fun Y => ?_
  simp only [fhat_transposeFun, fhat_nprojPure, Matrix.rank_transpose]

/-! ## The orthocomplement dictionary -/

/-- The range of a linear map is the orthocomplement of the kernel of its transpose. -/
lemma range_mulVecLin_eq_ortho_ker_transpose {m n : ℕ} (Y : Matrix (Fin m) (Fin n) 𝔽₂) :
    LinearMap.range (Matrix.mulVecLin Y) = F2.ortho (LinearMap.ker (Matrix.mulVecLin Yᵀ)) := by
  rw [← range_mulVecLin_transpose_eq_ortho_ker (Yᵀ), Matrix.transpose_transpose]

/-- The kernel of the transpose is the orthocomplement of the range. -/
lemma ker_mulVecLin_transpose_eq_ortho_range {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    LinearMap.ker (Matrix.mulVecLin Xᵀ) = F2.ortho (LinearMap.range X.mulVecLin) := by
  ext v
  rw [LinearMap.mem_ker, F2.mem_ortho]
  constructor
  · intro h w hw
    obtain ⟨u, rfl⟩ := hw
    rw [Matrix.mulVecLin_apply, ← dotProduct_mulVec_transpose]
    have h2 : Xᵀ *ᵥ v = 0 := by
      have hh := h
      rwa [Matrix.mulVecLin_apply] at hh
    rw [h2]; simp
  · intro h
    rw [Matrix.mulVecLin_apply]
    funext i
    let e : Fin m → 𝔽₂ := Pi.single i (1 : 𝔽₂)
    have he : e i = 1 := Pi.single_eq_same i 1
    have he' : ∀ j, j ≠ i → e j = 0 := fun j hj => Pi.single_eq_of_ne hj 1
    have hz : (Xᵀ *ᵥ v) i = ∑ j, (Xᵀ *ᵥ v) j * e j := by
      rw [Finset.sum_eq_single i]
      · rw [he, mul_one]
      · intro j _ hj; rw [he' j hj, mul_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [hz, dotProduct_mulVec_transpose]
    exact h (X *ᵥ e) ⟨e, Matrix.mulVecLin_apply X e⟩

/-- The preimage of an orthocomplement is the orthocomplement of the image of the adjoint. -/
lemma comap_mulVecLin_ortho {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (S : Submodule 𝔽₂ (Fin n → 𝔽₂)) :
    Submodule.comap X.mulVecLin (F2.ortho S) =
      F2.ortho (Submodule.map (Matrix.mulVecLin Xᵀ) S) := by
  ext u
  rw [Submodule.mem_comap, F2.mem_ortho, F2.mem_ortho]
  constructor
  · intro h w hw
    obtain ⟨s, hs, rfl⟩ := hw
    simp only [Matrix.mulVecLin_apply]
    have key : (∑ i, u i * (Xᵀ *ᵥ s) i) = ∑ j, X.mulVecLin u j * s j := by
      rw [show (∑ i, u i * (Xᵀ *ᵥ s) i) = ∑ i, (Xᵀ *ᵥ s) i * u i from
        Finset.sum_congr rfl (fun i _ => mul_comm _ _)]
      rw [dotProduct_mulVec_transpose, Matrix.mulVecLin_apply]
      exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    rw [key]
    exact h s hs
  · intro h s hs
    have key : (∑ j, X.mulVecLin u j * s j) = ∑ i, u i * (Xᵀ *ᵥ s) i := by
      rw [Matrix.mulVecLin_apply,
        show (∑ j, (X *ᵥ u) j * s j) = ∑ j, s j * (X *ᵥ u) j from
          Finset.sum_congr rfl (fun j _ => mul_comm _ _),
        ← dotProduct_mulVec_transpose]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [key]
    exact h (Xᵀ *ᵥ s) ⟨s, hs, Matrix.mulVecLin_apply Xᵀ s⟩

/-- The "four-arrow" lemma relating `range`, `ker`, `map` and `comap`. -/
lemma le_range_and_comap_iff' {U V : Type*} [AddCommGroup U] [Module 𝔽₂ U]
    [AddCommGroup V] [Module 𝔽₂ V] (f : U →ₗ[𝔽₂] V) (S : Submodule 𝔽₂ V)
    (R : Submodule 𝔽₂ U) :
    (S ≤ LinearMap.range f ∧ Submodule.comap f S ≤ R) ↔
      (LinearMap.ker f ≤ R ∧ S ≤ Submodule.map f R) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, fun q hq => ?_⟩
    · exact h2 (by rw [Submodule.mem_comap, hx]; exact S.zero_mem)
    · obtain ⟨u, rfl⟩ := h1 hq
      exact ⟨u, h2 (by rw [Submodule.mem_comap]; exact hq), rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun q hq => ?_, fun u hu => ?_⟩
    · obtain ⟨r, _, hr⟩ := h2 hq
      exact ⟨r, hr⟩
    · rw [Submodule.mem_comap] at hu
      obtain ⟨r, hrR, hr⟩ := h2 hu
      have hker : u - r ∈ R := h1 (by rw [LinearMap.mem_ker, map_sub, hr, sub_self])
      have hsum : u = r + (u - r) := by abel
      rw [hsum]
      exact R.add_mem hrR hker

/-! ## The hybrid predicate is transpose-invariant -/

/-- **Transposing exchanges `dim V₁` and `codim W₁`.**  The hybrid Fourier multiplier of the
transposed pair `(ιᵀ, Qᵀ)` at the transposed character `Y` is the multiplier of `(Q, ι)` at
`Yᵀ`. -/
lemma hybridPred_transpose {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (Y : Matrix (Fin m) (Fin n) 𝔽₂) :
    hybridPred ιᵀ Qᵀ Y ↔ hybridPred Q ι Yᵀ := by
  have hc1 : (∀ w : Fin n → 𝔽₂, Y.mulVec w ∈ LinearMap.ker (Matrix.mulVecLin ιᵀ) →
      w ∈ LinearMap.range (Matrix.mulVecLin Qᵀ)) ↔
      Submodule.comap (Matrix.mulVecLin Y) (LinearMap.ker (Matrix.mulVecLin ιᵀ)) ≤
        LinearMap.range (Matrix.mulVecLin Qᵀ) := by
    constructor
    · intro hh w hw
      rw [Submodule.mem_comap] at hw
      exact hh w (by rwa [Matrix.mulVecLin_apply] at hw)
    · intro hh w hw
      exact hh (by rw [Submodule.mem_comap, Matrix.mulVecLin_apply]; exact hw)
  have hc2 : (∀ w : Fin m → 𝔽₂, Yᵀ.mulVec w ∈ LinearMap.ker Q.mulVecLin →
      w ∈ LinearMap.range ι.mulVecLin) ↔
      Submodule.comap (Matrix.mulVecLin Yᵀ) (LinearMap.ker Q.mulVecLin) ≤
        LinearMap.range ι.mulVecLin := by
    constructor
    · intro hh w hw
      rw [Submodule.mem_comap] at hw
      exact hh w (by rwa [Matrix.mulVecLin_apply] at hw)
    · intro hh w hw
      exact hh (by rw [Submodule.mem_comap, Matrix.mulVecLin_apply]; exact hw)
  have hL : hybridPred ιᵀ Qᵀ Y ↔
      (LinearMap.ker (Matrix.mulVecLin Yᵀ) ≤ LinearMap.range ι.mulVecLin) ∧
        (LinearMap.ker Q.mulVecLin ≤
          Submodule.map (Matrix.mulVecLin Yᵀ) (LinearMap.range ι.mulVecLin)) := by
    rw [hybridPred, hc1, ker_mulVecLin_transpose_eq_ortho_range ι,
      range_mulVecLin_eq_ortho_ker_transpose Y,
      comap_mulVecLin_ortho (X := Y) (S := LinearMap.range ι.mulVecLin),
      range_mulVecLin_transpose_eq_ortho_ker Q]
    exact ⟨fun h => ⟨(F2.le_ortho_iff (L := LinearMap.ker (Matrix.mulVecLin Yᵀ))
          (L' := LinearMap.range ι.mulVecLin)).mp h.1,
        (F2.le_ortho_iff (L := LinearMap.ker Q.mulVecLin)
          (L' := Submodule.map (Matrix.mulVecLin Yᵀ) (LinearMap.range ι.mulVecLin))).mp h.2⟩,
      fun h => ⟨(F2.le_ortho_iff (L := LinearMap.ker (Matrix.mulVecLin Yᵀ))
          (L' := LinearMap.range ι.mulVecLin)).mpr h.1,
        (F2.le_ortho_iff (L := LinearMap.ker Q.mulVecLin)
          (L' := Submodule.map (Matrix.mulVecLin Yᵀ) (LinearMap.range ι.mulVecLin))).mpr h.2⟩⟩
  have hR : hybridPred Q ι Yᵀ ↔
      (LinearMap.ker (Matrix.mulVecLin Yᵀ) ≤ LinearMap.range ι.mulVecLin) ∧
        (LinearMap.ker Q.mulVecLin ≤
          Submodule.map (Matrix.mulVecLin Yᵀ) (LinearMap.range ι.mulVecLin)) := by
    rw [hybridPred, hc2, le_range_and_comap_iff' (Matrix.mulVecLin Yᵀ)
      (LinearMap.ker Q.mulVecLin) (LinearMap.range ι.mulVecLin)]
  rw [hL, hR]

/-! ## The order is transpose-invariant -/

lemma hybridOrder_transpose {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) :
    hybridOrder ιᵀ Qᵀ = hybridOrder Q ι := by
  have hι : Module.finrank 𝔽₂ ↥(LinearMap.ker (Matrix.mulVecLin ιᵀ)) =
      m - Module.finrank 𝔽₂ ↥(LinearMap.range ι.mulVecLin) := by
    have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin ιᵀ)
    rw [show Module.finrank 𝔽₂ (Fin m → 𝔽₂) = m from Module.finrank_fin_fun (ZMod 2)] at h
    have h2 : Module.finrank 𝔽₂ ↥(LinearMap.range (Matrix.mulVecLin ιᵀ)) =
        Module.finrank 𝔽₂ ↥(LinearMap.range ι.mulVecLin) := Matrix.rank_transpose ι
    omega
  have hQ : Module.finrank 𝔽₂ ↥(LinearMap.ker Q.mulVecLin) =
      n - Module.finrank 𝔽₂ ↥(LinearMap.range (Matrix.mulVecLin Qᵀ)) := by
    have h := LinearMap.finrank_range_add_finrank_ker Q.mulVecLin
    rw [show Module.finrank 𝔽₂ (Fin n → 𝔽₂) = n from Module.finrank_fin_fun (ZMod 2)] at h
    have h2 : Module.finrank 𝔽₂ ↥(LinearMap.range (Matrix.mulVecLin Qᵀ)) =
        Module.finrank 𝔽₂ ↥(LinearMap.range Q.mulVecLin) := Matrix.rank_transpose Q
    omega
  have e1 : hybridOrder ιᵀ Qᵀ =
      Module.finrank 𝔽₂ ↥(LinearMap.ker (Matrix.mulVecLin ιᵀ)) +
        (n - Module.finrank 𝔽₂ ↥(LinearMap.range (Matrix.mulVecLin Qᵀ))) := rfl
  have e2 : hybridOrder Q ι =
      Module.finrank 𝔽₂ ↥(LinearMap.ker Q.mulVecLin) +
        (m - Module.finrank 𝔽₂ ↥(LinearMap.range ι.mulVecLin)) := rfl
  rw [e1, e2, hι, hQ]
  omega

/-! ## Globalness and influences are transpose-invariant -/

lemma GlobalBS_transpose {m n d : ℕ} {ε : ℝ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    GlobalBS d ε f ↔ GlobalBS d ε (transposeFun f) := by
  constructor
  · intro h m' n' Q ι hord T
    have h1 : transposeFun (restr ιᵀ Qᵀ (shift Tᵀ f)) =
        restr Q ι (shift T (transposeFun f)) := by
      rw [transposeFun_restr, transposeFun_shift, Matrix.transpose_transpose,
        Matrix.transpose_transpose, Matrix.transpose_transpose]
    rw [← h1, l2sq_transposeFun]
    exact h (Q := ιᵀ) (ι := Qᵀ) (by rw [hybridOrder_transpose]; exact hord) Tᵀ
  · intro h m' n' Q ι hord T
    have h1 : transposeFun (restr Q ι (shift T f)) =
        restr ιᵀ Qᵀ (shift Tᵀ (transposeFun f)) := by
      rw [transposeFun_restr, transposeFun_shift]
    rw [← l2sq_transposeFun (f := restr Q ι (shift T f)), h1]
    exact h (Q := ιᵀ) (ι := Qᵀ) (by rw [hybridOrder_transpose]; exact hord) Tᵀ

/-- Transposition commutes with the derivative of an order-one influence. -/
theorem inflBS2_transpose {m n m' n' d : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    inflBS2 Q ι T (nprojPure d f) =
      inflBS2 ιᵀ Qᵀ Tᵀ (nprojPure d (transposeFun f)) := by
  have hpred : (fun Y : Matrix (Fin m) (Fin n) 𝔽₂ => hybridPred Q ι Yᵀ) =
      hybridPred ιᵀ Qᵀ := by
    funext Y
    exact propext (hybridPred_transpose Q ι Y).symm
  have h1 : transposeFun (restr Q ι (shift T (lapMulN (hybridPred Q ι) (nprojPure d f)))) =
      restr ιᵀ Qᵀ (shift Tᵀ (lapMulN (fun Y : Matrix (Fin m) (Fin n) 𝔽₂ =>
        hybridPred Q ι Yᵀ) (nprojPure d (transposeFun f)))) := by
    rw [transposeFun_restr, transposeFun_shift, transposeFun_lapMulN, transposeFun_nprojPure]
  rw [inflBS2, inflBS2, ← hpred, ← h1, l2sq_transposeFun]

end

end Submission.Grassmann