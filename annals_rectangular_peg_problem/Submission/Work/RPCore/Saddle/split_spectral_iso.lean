import Mathlib
import Submission.Work.RPCore.Defs
import Submission.Work.RPCore.Saddle.SplitSpectralDiag
import Submission.Work.RPCore.Saddle.diag_inner_le
import Submission.Work.RPCore.Saddle.diag_le_inner
import Submission.Work.RPCore.Saddle.diag_norm_bound
import Submission.Work.RPCore.Saddle.sign_split

namespace Work.RPCore.Saddle

open scoped RealInnerProductSpace

noncomputable section

/-- For an orthonormal basis `B` and a function `c` with `A (B i) = c i • B i`, the coordinates of
`A v` in the basis `B` are `c i` times the coordinates of `v`. -/
private theorem repr_apply_eq_smul {M : ℕ} {A : EuclideanSpace ℝ (Fin M) →L[ℝ] EuclideanSpace ℝ (Fin M)}
    (hA : ∀ v w, inner ℝ (A v) w = inner ℝ v (A w)) {ι : Type*} [Fintype ι]
    (B : OrthonormalBasis ι ℝ (EuclideanSpace ℝ (Fin M))) (c : ι → ℝ)
    (hB : ∀ i, A (B i) = c i • B i) (v : EuclideanSpace ℝ (Fin M)) (i : ι) :
    (B.repr (A v)) i = c i * (B.repr v) i := by
  show (B.repr (A v)).ofLp i = c i * (B.repr v).ofLp i
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
  rw [← hA (B i) v, hB i, real_inner_smul_left]

theorem split_spectral_iso {M : ℕ} (A : EuclideanSpace ℝ (Fin M) →L[ℝ] EuclideanSpace ℝ (Fin M))
    (hA : ∀ v w, inner ℝ (A v) w = inner ℝ v (A w)) (hinj : Function.Injective A) :
    ∃ (k l : ℕ) (hk : k + l = M)
      (e : EuclideanSpace ℝ (Fin M) ≃ₗᵢ[ℝ]
        WithLp 2 (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)))
      (A₁ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
      (A₂ : EuclideanSpace ℝ (Fin l) →L[ℝ] EuclideanSpace ℝ (Fin l)) (lam K : ℝ),
      0 < lam ∧ lam ≤ K ∧
      (∀ x, inner ℝ (A₁ x) x ≤ -lam * ‖x‖ ^ 2) ∧ (∀ x, ‖A₁ x‖ ≤ K * ‖x‖) ∧
      (∀ y, lam * ‖y‖ ^ 2 ≤ inner ℝ (A₂ y) y) ∧ (∀ y, ‖A₂ y‖ ≤ K * ‖y‖) ∧
      (∀ v, e (A v) = WithLp.toLp 2 (A₁ ((e v).fst), A₂ ((e v).snd))) ∧
      (∀ v, inner ℝ (A v) v
        = inner ℝ (A₁ ((e v).fst)) ((e v).fst) + inner ℝ (A₂ ((e v).snd)) ((e v).snd)) := by
  classical
  -- Self-adjointness of `A` as a `LinearMap`.
  have hsym : (A : EuclideanSpace ℝ (Fin M) →ₗ[ℝ] EuclideanSpace ℝ (Fin M)).IsSymmetric := hA
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin M)) = M := by simp
  -- Spectral data: an orthonormal eigenbasis `b` with eigenvalues `c`.
  let b : OrthonormalBasis (Fin M) ℝ (EuclideanSpace ℝ (Fin M)) := hsym.eigenvectorBasis hn
  let c : Fin M → ℝ := hsym.eigenvalues hn
  have hbA : ∀ i, A (b i) = c i • b i := fun i => by
    rw [show A (b i)
        = (A : EuclideanSpace ℝ (Fin M) →ₗ[ℝ] EuclideanSpace ℝ (Fin M)) (b i) from rfl]
    exact hsym.apply_eigenvectorBasis hn i
  -- Injectivity forces every eigenvalue to be nonzero.
  have hne : ∀ i, c i ≠ 0 := by
    intro i hi
    have h1 : A (b i) = 0 := by rw [hbA i, hi, zero_smul]
    have h2 : b i = 0 := hinj (by rw [h1, map_zero])
    have h3 : ‖b i‖ = 1 := b.orthonormal.1 i
    rw [h2, norm_zero] at h3
    exact one_ne_zero h3.symm
  -- Split the index set by the sign of the eigenvalue.
  obtain ⟨k, l, hk, φ, hφneg, hφpos⟩ := sign_split c hne
  -- Reindex the eigenbasis so that negative eigenvalues come first.
  let B : OrthonormalBasis (Fin k ⊕ Fin l) ℝ (EuclideanSpace ℝ (Fin M)) := b.reindex φ.symm
  have hB : ∀ i, B i = b (φ i) := by
    intro i
    simp only [B, OrthonormalBasis.reindex_apply]
    rfl
  have hBA : ∀ i, A (B i) = c (φ i) • B i := by
    intro i; rw [hB i]; exact hbA (φ i)
  -- The `L²`-decomposition isometry.
  let e : EuclideanSpace ℝ (Fin M) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) :=
    B.repr.trans (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 (fun _ : Fin k ⊕ Fin l => ℝ))
  -- Diagonal blocks.
  let dn : Fin k → ℝ := fun j => c (φ (Sum.inl j))
  let dp : Fin l → ℝ := fun j => c (φ (Sum.inr j))
  let A₁ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) := diagCLM dn
  let A₂ : EuclideanSpace ℝ (Fin l) →L[ℝ] EuclideanSpace ℝ (Fin l) := diagCLM dp
  -- Bounds `lam ≤ |c i| ≤ K`.
  let vals : Finset ℝ := insert 1 (Finset.univ.image (fun i : Fin M => |c i|))
  have hvals : vals.Nonempty := Finset.insert_nonempty 1 _
  set lam : ℝ := vals.inf' hvals id with hlamdef
  set K : ℝ := vals.sup' hvals id with hKdef
  have hlam_pos : 0 < lam := by
    rw [hlamdef, Finset.lt_inf'_iff]
    intro y hy
    rcases Finset.mem_insert.mp hy with h | h
    · rw [h]; norm_num
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
      rw [← hi]
      exact abs_pos.mpr (hne i)
  have hlam_le : ∀ i, lam ≤ |c i| := by
    intro i
    have hmi : |c i| ∈ vals :=
      Finset.mem_insert_of_mem (b := 1) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    rw [hlamdef]
    exact Finset.inf'_le id hmi
  have hK_ge : ∀ i, |c i| ≤ K := by
    intro i
    have hmi : |c i| ∈ vals :=
      Finset.mem_insert_of_mem (b := 1) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    rw [hKdef]
    exact Finset.le_sup' id hmi
  have h1K : (1 : ℝ) ≤ K := by
    rw [hKdef]; exact Finset.le_sup' id (Finset.mem_insert_self 1 _)
  have hlam1 : lam ≤ 1 := by
    rw [hlamdef]; exact Finset.inf'_le id (Finset.mem_insert_self 1 _)
  have hlamK : lam ≤ K := le_trans hlam1 h1K
  have hKnn : 0 ≤ K := le_trans zero_le_one h1K
  -- Sign consequences for the two blocks.
  have hneg : ∀ j, dn j ≤ -lam := by
    intro j
    have h1 : lam ≤ |c (φ (Sum.inl j))| := hlam_le _
    have h2 : c (φ (Sum.inl j)) < 0 := hφneg j
    rw [abs_of_neg h2] at h1
    have : dn j = c (φ (Sum.inl j)) := rfl
    linarith
  have hpos : ∀ j, lam ≤ dp j := by
    intro j
    have h1 : lam ≤ |c (φ (Sum.inr j))| := hlam_le _
    have h2 : 0 < c (φ (Sum.inr j)) := hφpos j
    rw [abs_of_pos h2] at h1
    exact h1
  have hnegK : ∀ j, |dn j| ≤ K := fun j => hK_ge _
  have hposK : ∀ j, |dp j| ≤ K := fun j => hK_ge _
  -- The four quantitative bounds.
  have hA₁_neg : ∀ x, inner ℝ (A₁ x) x ≤ -lam * ‖x‖ ^ 2 :=
    fun x => diag_inner_le dn hneg x
  have hA₁_norm : ∀ x, ‖A₁ x‖ ≤ K * ‖x‖ :=
    fun x => diag_norm_bound dn hKnn hnegK x
  have hA₂_pos : ∀ y, lam * ‖y‖ ^ 2 ≤ inner ℝ (A₂ y) y :=
    fun y => diag_le_inner dp hpos y
  have hA₂_norm : ∀ y, ‖A₂ y‖ ≤ K * ‖y‖ :=
    fun y => diag_norm_bound dp hKnn hposK y
  -- Coordinates of `e v`.
  have he_ofLp : ∀ v, (e v).ofLp =
      (WithLp.toLp 2 (fun j : Fin k => (B.repr v) (Sum.inl j)),
       WithLp.toLp 2 (fun j : Fin l => (B.repr v) (Sum.inr j))) := by
    intro v
    have h : e v = WithLp.toLp 2
        (WithLp.toLp 2 (fun j : Fin k => (B.repr v) (Sum.inl j)),
         WithLp.toLp 2 (fun j : Fin l => (B.repr v) (Sum.inr j))) := by
      rw [show e v = (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2
          (fun _ : Fin k ⊕ Fin l => ℝ)) (B.repr v) from rfl]
      simp [PiLp.sumPiLpEquivProdLpPiLp]
    rw [h, WithLp.ofLp_toLp]
  have hfst : ∀ v, (e v).fst = WithLp.toLp 2 (fun j : Fin k => (B.repr v) (Sum.inl j)) := by
    intro v
    show (WithLp.ofLp (e v)).1 = _
    rw [he_ofLp v]
  have hsnd : ∀ v, (e v).snd = WithLp.toLp 2 (fun j : Fin l => (B.repr v) (Sum.inr j)) := by
    intro v
    show (WithLp.ofLp (e v)).2 = _
    rw [he_ofLp v]
  -- Diagonal operators on `toLp`-coordinates.
  have hdiag_toLp : ∀ (n : ℕ) (d g : Fin n → ℝ),
      diagCLM d (WithLp.toLp 2 g) = WithLp.toLp 2 (fun i => d i * g i) := by
    intro n d g
    apply_fun WithLp.ofLp using WithLp.ofLp_injective 2
    funext i
    simp [diagCLM_apply]
  have hinner_diag : ∀ (n : ℕ) (d g : Fin n → ℝ),
      inner ℝ (diagCLM d (WithLp.toLp 2 g)) (WithLp.toLp 2 g)
        = ∑ i, d i * (g i) ^ 2 := by
    intro n d g
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Real.inner_apply, diagCLM_apply]
    ring
  -- The eigenvalue relation in the reindexed basis.
  have hkey : ∀ v (i : Fin k ⊕ Fin l),
      (B.repr (A v)) i = c (φ i) * (B.repr v) i :=
    fun v i => repr_apply_eq_smul hA B (fun i => c (φ i)) hBA v i
  -- The intertwining identity.
  have he : ∀ v, e (A v) = WithLp.toLp 2 (A₁ ((e v).fst), A₂ ((e v).snd)) := by
    intro v
    apply_fun WithLp.ofLp using WithLp.ofLp_injective 2
    rw [he_ofLp (A v), WithLp.ofLp_toLp]
    refine Prod.ext ?_ ?_
    · rw [hfst v]
      show WithLp.toLp 2 (fun j : Fin k => (B.repr (A v)) (Sum.inl j))
        = diagCLM dn (WithLp.toLp 2 (fun j : Fin k => (B.repr v) (Sum.inl j)))
      rw [hdiag_toLp]
      apply_fun WithLp.ofLp using WithLp.ofLp_injective 2
      funext j
      rw [WithLp.ofLp_toLp, WithLp.ofLp_toLp]
      exact hkey v (Sum.inl j)
    · rw [hsnd v]
      show WithLp.toLp 2 (fun j : Fin l => (B.repr (A v)) (Sum.inr j))
        = diagCLM dp (WithLp.toLp 2 (fun j : Fin l => (B.repr v) (Sum.inr j)))
      rw [hdiag_toLp]
      apply_fun WithLp.ofLp using WithLp.ofLp_injective 2
      funext j
      rw [WithLp.ofLp_toLp, WithLp.ofLp_toLp]
      exact hkey v (Sum.inr j)
  -- The inner-product decomposition.
  have hin2 : ∀ v, inner ℝ (A v) v
      = inner ℝ (A₁ ((e v).fst)) ((e v).fst) + inner ℝ (A₂ ((e v).snd)) ((e v).snd) := by
    intro v
    rw [← LinearIsometryEquiv.inner_map_map B.repr (A v) v]
    rw [PiLp.inner_apply, Fintype.sum_sum_type]
    rw [hfst v, hsnd v]
    rw [show A₁ = diagCLM dn from rfl, show A₂ = diagCLM dp from rfl]
    rw [hinner_diag k dn (fun j => (B.repr v) (Sum.inl j)),
        hinner_diag l dp (fun j => (B.repr v) (Sum.inr j))]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Real.inner_apply, hkey v (Sum.inl j)]; ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Real.inner_apply, hkey v (Sum.inr j)]; ring
  exact ⟨k, l, hk, e, A₁, A₂, lam, K,
    hlam_pos, hlamK, hA₁_neg, hA₁_norm, hA₂_pos, hA₂_norm, he, hin2⟩

end

end Work.RPCore.Saddle
