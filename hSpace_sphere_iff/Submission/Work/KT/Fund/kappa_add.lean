import Mathlib
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.kappa_add_defs
import Submission.Work.KT.Fund.kappa_indep
import Submission.Work.KT.Fund.recipProj_block
import Submission.Work.KT.Fund.graphB_recipB_conjTranspose_mul_self
import Submission.Work.KT.Fund.isUnit_one_add_conjTranspose_mul

namespace Work.KT.Fund

open Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- Entrywise application of a function commutes with reindexing. -/
lemma reindex_map' {m n : Type} {α β : Type} (e : m ≃ n) (M : Matrix m m α)
    (f : α → β) :
    (Matrix.reindex e e M).map f = Matrix.reindex e e (M.map f) := by
  funext i j
  rfl

/-- Reindexing twice is reindexing along the composite. -/
lemma reindex_reindex' {a b c : Type} {R : Type} (e : a ≃ b) (f : b ≃ c) (M : Matrix a a R) :
    Matrix.reindex f f (Matrix.reindex e e M) = Matrix.reindex (e.trans f) (e.trans f) M := by
  funext i j
  rfl

/-- Entrywise application of a ring homomorphism commutes with `fromBlocks`. -/
lemma map_fromBlocks_ringHom {m n : Type} {α β : Type} [Semiring α] [Semiring β]
    (φ : α →+* β) (A : Matrix m m α) (B : Matrix n n α) :
    (Matrix.fromBlocks A 0 0 B).map φ = Matrix.fromBlocks (A.map φ) 0 0 (B.map φ) := by
  funext i j
  rcases i with a | a <;> rcases j with b | b <;>
    simp [Matrix.map_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

/-- The block diagonal of two matrices reindexes along `Equiv.sumCongr`. -/
lemma fromBlocks_reindex_sumCongr {m n m' n' : Type} {R : Type} [Zero R]
    (e : m ≃ m') (f : n ≃ n') (A : Matrix m m R) (B : Matrix n n R) :
    Matrix.reindex (Equiv.sumCongr e f) (Equiv.sumCongr e f) (Matrix.fromBlocks A 0 0 B)
      = Matrix.fromBlocks (Matrix.reindex e e A) 0 0 (Matrix.reindex f f B) := by
  funext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

/-- Product of two `pairMat`s. -/
lemma pairMat_mul {ι : Type} [Fintype ι] (A B A' B' : Matrix ι ι C(X × Ball ℂ, ℂ))
    (h : A.map (fun f => bdryRestrict X f) = B.map (fun f => bdryRestrict X f))
    (h' : A'.map (fun f => bdryRestrict X f) = B'.map (fun f => bdryRestrict X f))
    (H : (A * A').map (fun f => bdryRestrict X f) = (B * B').map (fun f => bdryRestrict X f)) :
    pairMat X A B h * pairMat X A' B' h' = pairMat X (A * A') (B * B') H := by
  apply mat_ext X
  · rw [← Work.KT.Matrix.map_mul' (prF X) (pairMat X A B h) (pairMat X A' B' h'),
      pairMat_map_prF, pairMat_map_prF, pairMat_map_prF]
  · rw [← Work.KT.Matrix.map_mul' (prS X) (pairMat X A B h) (pairMat X A' B' h'),
      pairMat_map_prS, pairMat_map_prS, pairMat_map_prS]

/-- A `pairMat` of idempotents is idempotent. -/
lemma pairMat_idem {ι : Type} [Fintype ι] (A B : Matrix ι ι C(X × Ball ℂ, ℂ))
    (hA : A * A = A) (hB : B * B = B)
    (h : A.map (fun f => bdryRestrict X f) = B.map (fun f => bdryRestrict X f)) :
    (pairMat X A B h) * (pairMat X A B h) = pairMat X A B h := by
  have H : (A * A).map (fun f => bdryRestrict X f) = (B * B).map (fun f => bdryRestrict X f) := by
    rw [hA, hB]; exact h
  rw [pairMat_mul X A B A B h h H]
  apply mat_ext X
  · rw [pairMat_map_prF, pairMat_map_prF, hA]
  · rw [pairMat_map_prS, pairMat_map_prS, hB]

/-- `pairMat` of two block-diagonal matrices is the block diagonal of the `pairMat`s. -/
lemma pairMat_fromBlocks_kappa_add {m n : Type}
    (A₁ B₁ : Matrix m m C(X × Ball ℂ, ℂ)) (A₂ B₂ : Matrix n n C(X × Ball ℂ, ℂ))
    (h : (Matrix.fromBlocks A₁ 0 0 A₂).map (fun f => bdryRestrict X f)
      = (Matrix.fromBlocks B₁ 0 0 B₂).map (fun f => bdryRestrict X f))
    (h₁ : A₁.map (fun f => bdryRestrict X f) = B₁.map (fun f => bdryRestrict X f))
    (h₂ : A₂.map (fun f => bdryRestrict X f) = B₂.map (fun f => bdryRestrict X f)) :
    pairMat X (Matrix.fromBlocks A₁ 0 0 A₂) (Matrix.fromBlocks B₁ 0 0 B₂) h
      = Matrix.fromBlocks (pairMat X A₁ B₁ h₁) 0 0 (pairMat X A₂ B₂ h₂) := by
  apply mat_ext X
  · rw [pairMat_map_prF, map_fromBlocks_ringHom, pairMat_map_prF, pairMat_map_prF]
  · rw [pairMat_map_prS, map_fromBlocks_ringHom, pairMat_map_prS, pairMat_map_prS]
theorem graphB_block' {R : Type} [Ring R] {n k : ℕ}
    (F₁ : Matrix (Fin n) (Fin n) R) (F₂ : Matrix (Fin k) (Fin k) R) :
    graphB R (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks F₁ 0 0 F₂))
      = Matrix.reindex (blkEquiv n k) finSumFinEquiv
          (Matrix.fromBlocks (graphB R F₁) 0 0 (graphB R F₂)) := by
  apply (Matrix.reindex (blkEquiv n k) finSumFinEquiv).symm.injective
  rw [Equiv.symm_apply_apply, Matrix.reindex_symm]
  ext i j
  have hcast : ∀ (b : Fin n) (j : Fin k), ¬ (Fin.castAdd k b = Fin.natAdd n j) := by
    intro b j h
    have h1 : (Fin.castAdd k b).val = (Fin.natAdd n j).val := by rw [h]
    have h2 : (Fin.castAdd k b).val < n := Fin.castAdd_lt k b
    have h3 : n ≤ (Fin.natAdd n j).val := by simp [Fin.natAdd]
    omega
  have hnat : ∀ (j : Fin n) (d : Fin k), ¬ (Fin.natAdd n d = Fin.castAdd k j) := by
    intro j d h
    have h1 : (Fin.natAdd n d).val = (Fin.castAdd k j).val := by rw [h]
    have h2 : (Fin.castAdd k j).val < n := Fin.castAdd_lt k j
    have h3 : n ≤ (Fin.natAdd n d).val := by simp [Fin.natAdd]
    omega
  rcases i with ((a | b) | (c | d)) <;> rcases j with (j' | j'') <;>
    simp [Matrix.reindex_apply, graphB, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, hcast, hnat]

theorem graphProj_block' {Y : Type} [TopologicalSpace Y] (n k : ℕ)
    (F₁ : Matrix (Fin n) (Fin n) C(Y, ℂ))
    (F₂ : Matrix (Fin k) (Fin k) C(Y, ℂ)) :
    Work.KT.Fund.graphProj C(Y, ℂ)
        (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks F₁ 0 0 F₂))
      = Matrix.reindex (Work.KT.Fund.blkEquiv n k) (Work.KT.Fund.blkEquiv n k)
          (Matrix.fromBlocks (Work.KT.Fund.graphProj C(Y, ℂ) F₁) 0 0
            (Work.KT.Fund.graphProj C(Y, ℂ) F₂)) := by
  have h₁ : IsUnit ((graphB C(Y, ℂ) F₁).conjTranspose * graphB C(Y, ℂ) F₁) := by
    rw [(graphB_recipB_conjTranspose_mul_self C(Y, ℂ) F₁ F₁).1]
    exact isUnit_one_add_conjTranspose_mul F₁
  have h₂ : IsUnit ((graphB C(Y, ℂ) F₂).conjTranspose * graphB C(Y, ℂ) F₂) := by
    rw [(graphB_recipB_conjTranspose_mul_self C(Y, ℂ) F₂ F₂).1]
    exact isUnit_one_add_conjTranspose_mul F₂
  unfold graphProj
  rw [graphB_block']
  exact orthProj_reindex_blk (graphB C(Y, ℂ) F₁) (graphB C(Y, ℂ) F₂) h₁ h₂

/-- The block-split of the clutched idempotent, up to Murray--von Neumann equivalence.  The two
`Mat`s are written out with their entries, so that no `Sigma.fst`/`Mat.sum` reduction is needed. -/
lemma clutchIdem_add_mvn (n k : ℕ)
    (u : (Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))ˣ)
    (u₁ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (u₂ : (Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))ˣ)
    (F G : Matrix (Fin (n + k)) (Fin (n + k)) C(X × Ball ℂ, ℂ))
    (F₁ G₁ : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (F₂ G₂ : Matrix (Fin k) (Fin k) C(X × Ball ℂ, ℂ))
    (hF : F.map (fun f => bdryRestrict X f)
      = (u : Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ)))
    (hG : G.map (fun f => bdryRestrict X f)
      = ((u⁻¹ : (Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))ˣ) :
          Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ)))
    (hF₁ : F₁.map (fun f => bdryRestrict X f)
      = (u₁ : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (hG₁ : G₁.map (fun f => bdryRestrict X f)
      = ((u₁⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
          Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (hF₂ : F₂.map (fun f => bdryRestrict X f)
      = (u₂ : Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ)))
    (hG₂ : G₂.map (fun f => bdryRestrict X f)
      = ((u₂⁻¹ : (Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))ˣ) :
          Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ)))
    (hFblk : F = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks F₁ 0 0 F₂))
    (hGblk : G = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks G₁ 0 0 G₂)) :
    Mat.MvN
      ⟨(n + k) + (n + k),
        Matrix.reindex (finSumFinEquiv : Fin (n + k) ⊕ Fin (n + k) ≃ Fin ((n + k) + (n + k)))
          finSumFinEquiv
          (pairMat X (graphProj C(X × Ball ℂ, ℂ) F) (recipProj C(X × Ball ℂ, ℂ) G)
            (clutch_agree X (n + k) u F G hF hG))⟩
      ⟨(n + n) + (k + k),
        Matrix.reindex (finSumFinEquiv : Fin (n + n) ⊕ Fin (k + k) ≃ Fin ((n + n) + (k + k)))
          finSumFinEquiv
          (Matrix.fromBlocks
            (Matrix.reindex (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)) finSumFinEquiv
              (pairMat X (graphProj C(X × Ball ℂ, ℂ) F₁) (recipProj C(X × Ball ℂ, ℂ) G₁)
                (clutch_agree X n u₁ F₁ G₁ hF₁ hG₁))) 0 0
            (Matrix.reindex (finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k + k)) finSumFinEquiv
              (pairMat X (graphProj C(X × Ball ℂ, ℂ) F₂) (recipProj C(X × Ball ℂ, ℂ) G₂)
                (clutch_agree X k u₂ F₂ G₂ hF₂ hG₂))))⟩ := by
  have hA : graphProj C(X × Ball ℂ, ℂ) F
      = Matrix.reindex (blkEquiv n k) (blkEquiv n k)
          (Matrix.fromBlocks (graphProj C(X × Ball ℂ, ℂ) F₁) 0 0
            (graphProj C(X × Ball ℂ, ℂ) F₂)) := by
    rw [hFblk]; exact graphProj_block' (Y := X × Ball ℂ) n k F₁ F₂
  have hB : recipProj C(X × Ball ℂ, ℂ) G
      = Matrix.reindex (blkEquiv n k) (blkEquiv n k)
          (Matrix.fromBlocks (recipProj C(X × Ball ℂ, ℂ) G₁) 0 0
            (recipProj C(X × Ball ℂ, ℂ) G₂)) := by
    rw [hGblk]; exact recipProj_block (Y := X × Ball ℂ) n k G₁ G₂
  have hcl := clutch_agree X (n + k) u F G hF hG
  have hcl₁ := clutch_agree X n u₁ F₁ G₁ hF₁ hG₁
  have hcl₂ := clutch_agree X k u₂ F₂ G₂ hF₂ hG₂
  set M₁ := pairMat X (graphProj C(X × Ball ℂ, ℂ) F₁) (recipProj C(X × Ball ℂ, ℂ) G₁) hcl₁
    with hM₁
  set M₂ := pairMat X (graphProj C(X × Ball ℂ, ℂ) F₂) (recipProj C(X × Ball ℂ, ℂ) G₂) hcl₂
    with hM₂
  have hMidem : M₁ * M₁ = M₁ := by
    rw [hM₁]
    exact pairMat_idem X _ _ (graphProj_isIdem X F₁) (recipProj_isIdem X G₁) hcl₁
  have hMidem₂ : M₂ * M₂ = M₂ := by
    rw [hM₂]
    exact pairMat_idem X _ _ (graphProj_isIdem X F₂) (recipProj_isIdem X G₂) hcl₂
  have hWW : (Matrix.fromBlocks M₁ 0 0 M₂) * (Matrix.fromBlocks M₁ 0 0 M₂)
      = Matrix.fromBlocks M₁ 0 0 M₂ := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hMidem, hMidem₂]
  have hN : pairMat X (graphProj C(X × Ball ℂ, ℂ) F) (recipProj C(X × Ball ℂ, ℂ) G) hcl
      = Matrix.reindex (blkEquiv n k) (blkEquiv n k) (Matrix.fromBlocks M₁ 0 0 M₂) := by
    apply mat_ext X
    · rw [pairMat_map_prF,
        reindex_map' (blkEquiv n k) (Matrix.fromBlocks M₁ 0 0 M₂) (prF X),
        map_fromBlocks_ringHom, hM₁, hM₂, pairMat_map_prF, pairMat_map_prF]
      exact hA
    · rw [pairMat_map_prS,
        reindex_map' (blkEquiv n k) (Matrix.fromBlocks M₁ 0 0 M₂) (prS X),
        map_fromBlocks_ringHom, hM₁, hM₂, pairMat_map_prS, pairMat_map_prS]
      exact hB
  have hp2 : Matrix.reindex (finSumFinEquiv : Fin (n + k) ⊕ Fin (n + k) ≃ Fin ((n + k) + (n + k)))
        finSumFinEquiv
        (pairMat X (graphProj C(X × Ball ℂ, ℂ) F) (recipProj C(X × Ball ℂ, ℂ) G) hcl)
      = Matrix.reindex ((blkEquiv n k).trans
            (finSumFinEquiv : Fin (n + k) ⊕ Fin (n + k) ≃ Fin ((n + k) + (n + k))))
          ((blkEquiv n k).trans
            (finSumFinEquiv : Fin (n + k) ⊕ Fin (n + k) ≃ Fin ((n + k) + (n + k))))
          (Matrix.fromBlocks M₁ 0 0 M₂) := by
    rw [hN, reindex_reindex' (blkEquiv n k)
      (finSumFinEquiv : Fin (n + k) ⊕ Fin (n + k) ≃ Fin ((n + k) + (n + k)))
      (Matrix.fromBlocks M₁ 0 0 M₂)]
  have hq2 : Matrix.reindex (finSumFinEquiv : Fin (n + n) ⊕ Fin (k + k) ≃ Fin ((n + n) + (k + k)))
        finSumFinEquiv
        (Matrix.fromBlocks
          (Matrix.reindex (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)) finSumFinEquiv M₁) 0 0
          (Matrix.reindex (finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k + k)) finSumFinEquiv M₂))
      = Matrix.reindex (((Equiv.sumCongr (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n))
              (finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k + k))).trans
            (finSumFinEquiv : Fin (n + n) ⊕ Fin (k + k) ≃ Fin ((n + n) + (k + k)))))
          (((Equiv.sumCongr (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n))
              (finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k + k))).trans
            (finSumFinEquiv : Fin (n + n) ⊕ Fin (k + k) ≃ Fin ((n + n) + (k + k)))))
          (Matrix.fromBlocks M₁ 0 0 M₂) := by
    rw [← fromBlocks_reindex_sumCongr (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n))
        (finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k + k)) M₁ M₂,
      reindex_reindex' (Equiv.sumCongr (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n))
          (finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k + k)))
        (finSumFinEquiv : Fin (n + n) ⊕ Fin (k + k) ≃ Fin ((n + n) + (k + k)))
        (Matrix.fromBlocks M₁ 0 0 M₂)]
  let ψ : (Fin n ⊕ Fin n) ⊕ (Fin k ⊕ Fin k) ≃ Fin ((n + n) + (k + k)) :=
    (Equiv.sumCongr (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n))
      (finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k + k))).trans
      (finSumFinEquiv : Fin (n + n) ⊕ Fin (k + k) ≃ Fin ((n + n) + (k + k)))
  let φ : (Fin n ⊕ Fin n) ⊕ (Fin k ⊕ Fin k) ≃ Fin ((n + k) + (n + k)) :=
    (blkEquiv n k).trans
      (finSumFinEquiv : Fin (n + k) ⊕ Fin (n + k) ≃ Fin ((n + k) + (n + k)))
  refine ⟨Matrix.reindex ψ φ (Matrix.fromBlocks M₁ 0 0 M₂),
    Matrix.reindex φ ψ (Matrix.fromBlocks M₁ 0 0 M₂), ?_, ?_⟩
  · rw [Work.KT.reindexMul, hWW]
    exact hp2.symm
  · rw [Work.KT.reindexMul, hWW]
    exact hq2.symm

/-- Additivity of the clutched class of a block-diagonal unit. -/
lemma clutchIdem_block_cls (n k : ℕ)
    (u : (Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))ˣ)
    (u₁ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (u₂ : (Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))ˣ)
    (F G : Matrix (Fin (n + k)) (Fin (n + k)) C(X × Ball ℂ, ℂ))
    (F₁ G₁ : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (F₂ G₂ : Matrix (Fin k) (Fin k) C(X × Ball ℂ, ℂ))
    (hF : F.map (fun f => bdryRestrict X f)
      = (u : Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ)))
    (hG : G.map (fun f => bdryRestrict X f)
      = ((u⁻¹ : (Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))ˣ) :
          Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ)))
    (hF₁ : F₁.map (fun f => bdryRestrict X f)
      = (u₁ : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (hG₁ : G₁.map (fun f => bdryRestrict X f)
      = ((u₁⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
          Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (hF₂ : F₂.map (fun f => bdryRestrict X f)
      = (u₂ : Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ)))
    (hG₂ : G₂.map (fun f => bdryRestrict X f)
      = ((u₂⁻¹ : (Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))ˣ) :
          Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ)))
    (hFblk : F = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks F₁ 0 0 F₂))
    (hGblk : G = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks G₁ 0 0 G₂)) :
    cls (clutchIdem X (n + k) u F G hF hG)
      = cls (clutchIdem X n u₁ F₁ G₁ hF₁ hG₁)
        + cls (clutchIdem X k u₂ F₂ G₂ hF₂ hG₂) := by
  have hmvn := clutchIdem_add_mvn X n k u u₁ u₂ F G F₁ G₁ F₂ G₂
    hF hG hF₁ hG₁ hF₂ hG₂ hFblk hGblk
  have hPidem : Mat.IsIdem (⟨(n + k) + (n + k),
        Matrix.reindex (finSumFinEquiv : Fin (n + k) ⊕ Fin (n + k) ≃ Fin ((n + k) + (n + k)))
          finSumFinEquiv
          (pairMat X (graphProj C(X × Ball ℂ, ℂ) F) (recipProj C(X × Ball ℂ, ℂ) G)
            (clutch_agree X (n + k) u F G hF hG))⟩ : Mat ↥(pullAlg2 X)) :=
    clutchIdem_isIdem X (n + k) u F G hF hG
  have hQidem : Mat.IsIdem (⟨(n + n) + (k + k),
        Matrix.reindex (finSumFinEquiv : Fin (n + n) ⊕ Fin (k + k) ≃ Fin ((n + n) + (k + k)))
          finSumFinEquiv
          (Matrix.fromBlocks
            (Matrix.reindex (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)) finSumFinEquiv
              (pairMat X (graphProj C(X × Ball ℂ, ℂ) F₁) (recipProj C(X × Ball ℂ, ℂ) G₁)
                (clutch_agree X n u₁ F₁ G₁ hF₁ hG₁))) 0 0
            (Matrix.reindex (finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k + k)) finSumFinEquiv
              (pairMat X (graphProj C(X × Ball ℂ, ℂ) F₂) (recipProj C(X × Ball ℂ, ℂ) G₂)
                (clutch_agree X k u₂ F₂ G₂ hF₂ hG₂))))⟩ : Mat ↥(pullAlg2 X)) :=
    Mat.sum_isIdem (clutchIdem_isIdem X n u₁ F₁ G₁ hF₁ hG₁)
      (clutchIdem_isIdem X k u₂ F₂ G₂ hF₂ hG₂)
  have h1 : cls (⟨(n + k) + (n + k),
        Matrix.reindex (finSumFinEquiv : Fin (n + k) ⊕ Fin (n + k) ≃ Fin ((n + k) + (n + k)))
          finSumFinEquiv
          (pairMat X (graphProj C(X × Ball ℂ, ℂ) F) (recipProj C(X × Ball ℂ, ℂ) G)
            (clutch_agree X (n + k) u F G hF hG))⟩ : Mat ↥(pullAlg2 X))
      = cls (⟨(n + n) + (k + k),
        Matrix.reindex (finSumFinEquiv : Fin (n + n) ⊕ Fin (k + k) ≃ Fin ((n + n) + (k + k)))
          finSumFinEquiv
          (Matrix.fromBlocks
            (Matrix.reindex (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)) finSumFinEquiv
              (pairMat X (graphProj C(X × Ball ℂ, ℂ) F₁) (recipProj C(X × Ball ℂ, ℂ) G₁)
                (clutch_agree X n u₁ F₁ G₁ hF₁ hG₁))) 0 0
            (Matrix.reindex (finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k + k)) finSumFinEquiv
              (pairMat X (graphProj C(X × Ball ℂ, ℂ) F₂) (recipProj C(X × Ball ℂ, ℂ) G₂)
                (clutch_agree X k u₂ F₂ G₂ hF₂ hG₂))))⟩ : Mat ↥(pullAlg2 X)) :=
    cls_eq_of_mvn hPidem hQidem hmvn
  calc cls (clutchIdem X (n + k) u F G hF hG)
      = cls (⟨(n + k) + (n + k),
          Matrix.reindex (finSumFinEquiv : Fin (n + k) ⊕ Fin (n + k) ≃ Fin ((n + k) + (n + k)))
            finSumFinEquiv
            (pairMat X (graphProj C(X × Ball ℂ, ℂ) F) (recipProj C(X × Ball ℂ, ℂ) G)
              (clutch_agree X (n + k) u F G hF hG))⟩ : Mat ↥(pullAlg2 X)) := rfl
    _ = cls (⟨(n + n) + (k + k),
          Matrix.reindex (finSumFinEquiv : Fin (n + n) ⊕ Fin (k + k) ≃ Fin ((n + n) + (k + k)))
            finSumFinEquiv
            (Matrix.fromBlocks
              (Matrix.reindex (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)) finSumFinEquiv
                (pairMat X (graphProj C(X × Ball ℂ, ℂ) F₁) (recipProj C(X × Ball ℂ, ℂ) G₁)
                  (clutch_agree X n u₁ F₁ G₁ hF₁ hG₁))) 0 0
              (Matrix.reindex (finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k + k)) finSumFinEquiv
                (pairMat X (graphProj C(X × Ball ℂ, ℂ) F₂) (recipProj C(X × Ball ℂ, ℂ) G₂)
                  (clutch_agree X k u₂ F₂ G₂ hF₂ hG₂))))⟩ : Mat ↥(pullAlg2 X)) := h1
    _ = cls ((clutchIdem X n u₁ F₁ G₁ hF₁ hG₁).sum
          (clutchIdem X k u₂ F₂ G₂ hF₂ hG₂)) := rfl
    _ = cls (clutchIdem X n u₁ F₁ G₁ hF₁ hG₁)
        + cls (clutchIdem X k u₂ F₂ G₂ hF₂ hG₂) :=
        cls_sum (clutchIdem_isIdem X n u₁ F₁ G₁ hF₁ hG₁)
          (clutchIdem_isIdem X k u₂ F₂ G₂ hF₂ hG₂)

/-- Reindexing the identity matrix. -/
lemma reindex_one' {m n : Type} [DecidableEq m] [DecidableEq n] {R : Type} [Zero R] [One R]
    (e : m ≃ n) : Matrix.reindex e e (1 : Matrix m m R) = 1 := by
  funext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : e.symm i ≠ e.symm j := fun hh => h (e.symm.injective hh)
    simp [h, h']

/-- `liftOf` of the forward clutching function `u : (Matrix (Fin n) (Fin n) C(X × S¹, ℂ))ˣ`. -/
def liftOfU {n : ℕ} (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
  liftOf X (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))

/-- `liftOf` of the inverse clutching function `u⁻¹`. -/
def liftOfUinv {n : ℕ} (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
  liftOf X ((u⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))

lemma liftOfU_spec {n : ℕ} (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    (liftOfU X u).map (fun f => bdryRestrict X f) =
      (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) :=
  liftOf_spec X (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))

lemma liftOfUinv_spec {n : ℕ} (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    (liftOfUinv X u).map (fun f => bdryRestrict X f) =
      ((u⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
        Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) :=
  liftOf_spec X ((u⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))

theorem kappa_add (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n k : ℕ) (u : (Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))ˣ)
    (u₁ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (u₂ : (Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))ˣ)
    (h : (u : Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (u₁ : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) 0 0
            (u₂ : Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ)))) :
    Work.KT.Fund.kappa X (n + k) u
      = Work.KT.Fund.kappa X n u₁ + Work.KT.Fund.kappa X k u₂ := by
  rw [kappa_val X (n + k) u, kappa_val X n u₁, kappa_val X k u₂, ← map_add]
  refine congrArg (k0Glue X).symm ?_
  have hF : (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (liftOfU X u₁) 0 0 (liftOfU X u₂))).map
        (fun f => bdryRestrict X f)
      = (u : Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ)) := by
    rw [reindex_map' finSumFinEquiv (Matrix.fromBlocks (liftOfU X u₁) 0 0 (liftOfU X u₂))
        (fun f => bdryRestrict X f),
      map_fromBlocks_ringHom (bdryRestrict X), liftOfU_spec X u₁, liftOfU_spec X u₂, ← h]
  have hG : (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (liftOfUinv X u₁) 0 0 (liftOfUinv X u₂))).map
        (fun f => bdryRestrict X f)
      = ((u⁻¹ : (Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))ˣ) :
          Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ)) := by
    rw [reindex_map' finSumFinEquiv (Matrix.fromBlocks (liftOfUinv X u₁) 0 0 (liftOfUinv X u₂))
        (fun f => bdryRestrict X f),
      map_fromBlocks_ringHom (bdryRestrict X), liftOfUinv_spec X u₁, liftOfUinv_spec X u₂]
    have hZ : (u : Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))
        * Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks
            ((u₁⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
              Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) 0 0
            ((u₂⁻¹ : (Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))ˣ) :
              Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))) = 1 := by
      rw [h, Work.KT.reindexMul, Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Units.mul_inv]
      rw [Matrix.fromBlocks_one, reindex_one' finSumFinEquiv]
    symm
    calc ((u⁻¹ : (Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))ˣ) :
            Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))
        = ((u⁻¹ : (Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))ˣ) :
            Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ)) * 1 := (mul_one _).symm
      _ = ((u⁻¹ : (Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))ˣ) :
            Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ)) * ((u : Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))
            * Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks
                ((u₁⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
                  Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) 0 0
                ((u₂⁻¹ : (Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))ˣ) :
                  Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ)))) := by rw [hZ]
      _ = (((u⁻¹ : (Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))ˣ) :
              Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ)) * (u : Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ)))
          * Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks
              ((u₁⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
                Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) 0 0
              ((u₂⁻¹ : (Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))ˣ) :
                Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))) := by rw [mul_assoc]
      _ = 1 * Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks
              ((u₁⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
                Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) 0 0
              ((u₂⁻¹ : (Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))ˣ) :
                Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))) := by rw [Units.inv_mul]
      _ = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks
              ((u₁⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
                Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) 0 0
              ((u₂⁻¹ : (Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))ˣ) :
                Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))) := one_mul _
  exact (kappa_indep X (n + k) u (liftOfU X u)
      (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (liftOfU X u₁) 0 0 (liftOfU X u₂)))
      (liftOfUinv X u)
      (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (liftOfUinv X u₁) 0 0 (liftOfUinv X u₂)))
      (liftOfU_spec X u) hF (liftOfUinv_spec X u) hG).trans
    (clutchIdem_block_cls X n k u u₁ u₂
      (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (liftOfU X u₁) 0 0 (liftOfU X u₂)))
      (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (liftOfUinv X u₁) 0 0 (liftOfUinv X u₂)))
      (liftOfU X u₁) (liftOfUinv X u₁) (liftOfU X u₂) (liftOfUinv X u₂)
      hF hG (liftOfU_spec X u₁) (liftOfUinv_spec X u₁) (liftOfU_spec X u₂) (liftOfUinv_spec X u₂)
      rfl rfl)
end

end Work.KT.Fund
