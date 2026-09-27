import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.k0_rep
import Submission.Work.KT.Fund.AssemblyDefs
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.kappa_add
import Submission.Work.KT.Fund.kappa_one
import Submission.Work.KT.Fund.Geom
import Submission.Work.KT.Fund.Laurent
import Submission.Work.KT.Fund.Disc
import Submission.Work.KT.hk_k0_eq_diff
import Submission.Work.KT.EG.kappaRedDefs
import Submission.Work.KT.FP.FpDefs
import Submission.Work.KT.FP.kappa_eq_disc
import Submission.Work.KT.FP.bott_index
import Submission.Work.KT.Fund.kappa_bott

/-! Guidance from the project lead (the requester):

ROUTE: Submission/Work/KT/FP_README.md and DESIGN.md 'Addendum: fund_product split' (the lead's split of fund_product). CONVENTION: [Ring A] + explicit commutativity. Siblings run in parallel; fund_product = EG.fund_product_of_bott ... (fp_retract X).1 hrmul (fp_retract X).2 (fp_surj ...) (fp_inj ...).

| 5 | `fp_inj` | 0.5–1k | low | 3, 4, `Fund.kappa_bott` (in flight) | now; closes when 3, 4 and `kappa_bott` land |

The assembly (`fund_product_assembled`) is **proved** from 1, 2 and 5, using `EG.fund_product_of_bott`
(proved) and `k0_basic` (proved).

---

## 1 `fp_retract`
* **`r ∘ s = id`.** `(Fund.bp X) ≫ fst = id` as continuous maps, so
  `pullAlg fst ≫ pullAlg bp = pullAlg id`. Then use `k0_basic` conjuncts 3 and 4 (`K0.map` of a
  composite and of `id`).
* **`r γ = 1`.** `bp ≫ snd` is the constant map at `pt`, so `pullAlg (const pt)` factors as
  `(Algebra.ofId ℂ C(X,ℂ)).comp (evalC pt)`. Apply `K0.map_comp`, then `EG.hopf_eval_one pt`
  (`= cls (Mat.one ℂ 1)`). Finally, `K0.map` of `algebraMap` sends `Mat.one ℂ 1` to
  `Mat.one C(X,ℂ) 1` (`mapCls` + `Matrix.map_one`).

## 2 `fp_surj`
1. **`r y = 0 ⇒ pullUp y = 0`.** Use `Fund.Disc`: `pullUp y = sD (ev0 (pullUp y))`, and
   `ev0 ∘ pullUp = r` (both restrict to `X × {up 0} = X × {pt}`).
2. **`pullDn y = 0`.**
   * Write `pullDn y = sD a'`.
   * The square commutes, so `ρ (pullDn y) = ρ (pullUp y) = 0`, with `ρ` the boundary restriction.
   * `ρ ∘ sD` is the pull-back along `X × S¹ → X`, which has a left inverse (evaluate at `1 ∈ S¹`).
     Hence `a' = 0`.
3. **Conclude.** `kappa_span` gives `y = Σ cᵢ (κ uᵢ − κ 1)`. Then `κ 1 = cls 1` (`Fund.kappa_one`),
   and `EG.kappa_reduce` gives each `κ uᵢ − cls 1 = μ (s bᵢ) β`. Sum by additivity of `μ` and `s`:
   `b = Σ cᵢ bᵢ`.

## 3 `kappa_eq_disc` (the converse of `kappa_span`'s `clutchIdem_mvN`)
1. **Stable MvN.** `κ u = κ v` gives `cls (clutchIdem u) = cls (clutchIdem v)` over `pullAlg2 X`
   (`k0Glue` is an isomorphism). Apply `cls_eq_stable_mvN`, then add the complement to make the
   stabiliser trivial: `clutchIdem u ⊕ 1_k ~ clutchIdem v ⊕ 1_k`.
2. **Pass to `u ⊕ 1`.** The `clutchIdem_add_mvn` / `clutchIdem_one` pattern (as in `Fund.kappa_add`)
   gives `clutchIdem (u⊕1) ~ clutchIdem (v⊕1)`.
3. **Disc units.** Project the MvN witnesses `(a, b)` by `prF`/`prS`. Sandwich them with the
   trivialisations to get units over `C(X × Ball ℂ)`:
   * upper disc: `α₀ := graphLinv (F_v) · a₀ · graphB (F_u)`;
   * lower disc: `α₁ := recipLinv · a₁ · recipB`, with inverses built the same way from `b`.
   * The lemmas are all in `kappa_span.lean`: `graphLinv_mul`, `graphB_mul_graphLinv`,
     `recipB_inv_mul_graphB`, `rgraphLinv_map`.
   * First replace `a` by `Q a P` (possible since `ba = P`, `ab = Q`).
4. **Compatibility on the circle.** `α₁| · (u⊕1) = (v⊕1) · α₀|`, from `clutch_agree` and
   `recipB_inv_mul_graphB`. So `u⊕1 = g₀| (v⊕1) g₁|` with `g₀ = α₁⁻¹` and `g₁ = α₀`.
* Reuse `Bott.mvN_glue`, `Bott.k0_mv_inj`/`stable_free` and `Bott.isUnit_mulMap_prod`.

## 4 `bott_index` (Hatcher VBKT Thm 2.2, the injectivity half, pp. 45–47)
-/

namespace Work.KT.FP

open Matrix

noncomputable section

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

section Helpers

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The complementary idempotent `1 - P` of an idempotent `P`. -/
lemma isIdem_one_sub {n : ℕ} (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P) :
    Mat.IsIdem (⟨n, 1 - P⟩ : Mat C(X, ℂ)) :=
  base_idem' X P hP

/-! ## Reindexing of the ring operations -/

lemma reindex_add'' {R : Type} [Add R] {m n : Type} (e : m ≃ n) (A B : Matrix m m R) :
    Matrix.reindex e e (A + B) = Matrix.reindex e e A + Matrix.reindex e e B := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply]

lemma reindex_sub'' {R : Type} [Sub R] {m n : Type} (e : m ≃ n) (A B : Matrix m m R) :
    Matrix.reindex e e (A - B) = Matrix.reindex e e A - Matrix.reindex e e B := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply]

lemma reindex_smul'' {R : Type} [Monoid R] {m n : Type} (e : m ≃ n) (c : R)
    (A : Matrix m m R) :
    Matrix.reindex e e (c • A) = c • Matrix.reindex e e A := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply]

lemma map_one_fp {m : ℕ} :
    (1 : Matrix (Fin m) (Fin m) C(X, ℂ)).map (⇑(pMRH X)) = 1 :=
  Matrix.map_one _ (map_zero (pMRH X)) (map_one (pMRH X))

lemma map_zero_fp {m : ℕ} :
    (0 : Matrix (Fin m) (Fin m) C(X, ℂ)).map (⇑(pMRH X)) = 0 :=
  Matrix.map_zero _ (map_zero (pMRH X))

/-! ## The padded projection -/

/-- The padded projection `diag(P, 0_k)`, on the index set `Fin (n + k)`. -/
def padProj {n : ℕ} (k : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin (n + k)) (Fin (n + k)) C(X, ℂ) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks P 0 0 (0 : Matrix (Fin k) (Fin k) C(X, ℂ)))

/-- The padded projection is idempotent. -/
lemma padProj_isIdem {n k : ℕ} (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P) :
    padProj X k P * padProj X k P = padProj X k P := by
  rw [padProj, Work.KT.reindexMul, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, hP]

/-- `[diag(P, 0_k)] = [P]`. -/
lemma cls_padProj {n k : ℕ} (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P) :
    cls (⟨n + k, padProj X k P⟩ : Mat C(X, ℂ)) = cls (⟨n, P⟩ : Mat C(X, ℂ)) := by
  have hzero : Mat.IsIdem (⟨k, (0 : Matrix (Fin k) (Fin k) C(X, ℂ))⟩ : Mat C(X, ℂ)) := by
    show (0 : Matrix (Fin k) (Fin k) C(X, ℂ)) * 0 = 0
    simp
  have h : (⟨n + k, padProj X k P⟩ : Mat C(X, ℂ))
      = Mat.sum (⟨n, P⟩ : Mat C(X, ℂ)) ⟨k, (0 : Matrix (Fin k) (Fin k) C(X, ℂ))⟩ := rfl
  rw [h, cls_sum (p := (⟨n, P⟩ : Mat C(X, ℂ)))
      (q := ⟨k, (0 : Matrix (Fin k) (Fin k) C(X, ℂ))⟩) hP hzero,
    cls_zero_mat k, add_zero]

/-- The complement of the padded projection: `1 - diag(P,0) = diag(1-P, 1)`. -/
lemma one_sub_padProj {n k : ℕ} (P : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    (1 : Matrix (Fin (n + k)) (Fin (n + k)) C(X, ℂ)) - padProj X k P
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (1 - P) 0 0 (1 : Matrix (Fin k) (Fin k) C(X, ℂ))) := by
  have hb : (1 : Matrix (Fin n ⊕ Fin k) (Fin n ⊕ Fin k) C(X, ℂ))
      - Matrix.fromBlocks P 0 0 (0 : Matrix (Fin k) (Fin k) C(X, ℂ))
      = Matrix.fromBlocks (1 - P) 0 0 (1 : Matrix (Fin k) (Fin k) C(X, ℂ)) := by
    ext i j
    rcases i with a | a <;> rcases j with b | b <;>
      simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
        reduceCtorEq, if_true, if_false, sub_zero, zero_sub]
  rw [padProj, ← Work.KT.Fund.reindex_one' (R := C(X, ℂ)) finSumFinEquiv,
    ← reindex_sub'', hb]

/-- The complementary idempotents `1 - P`, `P` add up to `[1_n]`. -/
lemma fstStar_compl (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P) :
    Work.KT.EG.fstStar X (cls (⟨n, 1 - P⟩ : Mat C(X, ℂ)))
      + Work.KT.EG.fstStar X (cls (⟨n, P⟩ : Mat C(X, ℂ)))
      = cls (Mat.one C(X × S2, ℂ) n) := by
  rw [← map_add]
  have h1P : Mat.IsIdem (⟨n, 1 - P⟩ : Mat C(X, ℂ)) := base_idem' X P hP
  have hsum : cls (⟨n, 1 - P⟩ : Mat C(X, ℂ)) + cls (⟨n, P⟩ : Mat C(X, ℂ))
      = cls (Mat.one C(X, ℂ) n) := by
    rw [add_comm, ← cls_sum (p := (⟨n, P⟩ : Mat C(X, ℂ)))
      (q := (⟨n, 1 - P⟩ : Mat C(X, ℂ))) hP h1P]
    exact cls_eq_of_mvN (Mat.sum_idem hP h1P) (Mat.one_idem (C(X, ℂ)) n)
      (Work.KT.mvN_sum_compl (C(X, ℂ)) (⟨n, P⟩ : Mat C(X, ℂ)) hP)
  rw [hsum, Work.KT.EG.fstStar_cls_one]

/-- The padded Bott unit is the Bott matrix of the padded idempotent `diag(P, 0)`. -/
lemma padUnit_bottUnit {n k : ℕ} (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P) :
    ((padUnit X k (bottUnit X n P hP) :
        (Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))ˣ) :
        Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))
      = Fund.pullMat X (1 - padProj X k P)
        + (zUnit X : C(X × Sph ℂ, ℂ)) • Fund.pullMat X (padProj X k P) := by
  have h1 : pM X (1 - padProj X k P)
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (pM X (1 - P)) 0 0
            (1 : Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))) := by
    rw [one_sub_padProj, pM, Work.KT.Fund.reindex_map',
      Work.KT.Fund.map_fromBlocks_ringHom, map_one_fp]
    rfl
  have h2 : pM X (padProj X k P)
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (pM X P) 0 0
            (0 : Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))) := by
    rw [padProj, pM, Work.KT.Fund.reindex_map',
      Work.KT.Fund.map_fromBlocks_ringHom, map_zero_fp]
    rfl
  have hb : Matrix.fromBlocks
        (pM X (1 - P) + (zUnit X : C(X × Sph ℂ, ℂ)) • pM X P) 0 0
        (1 : Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))
      = Matrix.fromBlocks (pM X (1 - P)) 0 0
          (1 : Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))
        + (zUnit X : C(X × Sph ℂ, ℂ)) •
          Matrix.fromBlocks (pM X P) 0 0
            (0 : Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ)) := by
    rw [Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
    simp
  rw [padUnit_val, bottUnit_val, bottMat]
  show Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (pM X (1 - P) + (zUnit X : C(X × Sph ℂ, ℂ)) • pM X P) 0 0
          (1 : Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ)))
      = pM X (1 - padProj X k P)
        + (zUnit X : C(X × Sph ℂ, ℂ)) • pM X (padProj X k P)
  rw [h1, h2, hb, reindex_add'', reindex_smul'']

/-- **The reduced clutched class of the Bott unit** (`Fund.kappa_bott`). -/
lemma redK_bottUnit (μ : K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ))
    (hμ : IsK0Mul μ) (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P) :
    Work.KT.EG.redK X n (bottUnit X n P hP)
      = μ (Work.KT.EG.fstStar X (cls (⟨n, P⟩ : Mat C(X, ℂ)))) (Work.KT.EG.betaHopf X) := by
  have hu : ((bottUnit X n P hP : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
        Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = Fund.pullMat X (1 - P)
        + (zUnit X : C(X × Sph ℂ, ℂ)) • Fund.pullMat X P := by
    rw [bottUnit_val, pullMat_eq_pM]
    rfl
  have hb := Fund.kappa_bott X n P hP (bottUnit X n P hP) hu μ hμ
  have hAF : Work.KT.EG.fstStar X (cls (⟨n, 1 - P⟩ : Mat C(X, ℂ)))
      = cls (Mat.one C(X × S2, ℂ) n)
        - Work.KT.EG.fstStar X (cls (⟨n, P⟩ : Mat C(X, ℂ))) := by
    have h := fstStar_compl X n P hP
    rw [← h]; abel
  simp only [Work.KT.EG.fstStar, Work.KT.EG.gammaHopf] at hb hAF ⊢
  rw [Work.KT.EG.redK, hb, hAF, Work.KT.EG.mu_betaHopf (X := X) hμ]
  abel

end Helpers

/-- Injectivity half of Bott periodicity: `b ↦ s(b)·(γ − 1)` is injective. -/
theorem fp_inj (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (μ : K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ)) (hμ : IsK0Mul μ) :
    ∀ b : K0 C(X, ℂ),
      μ (K0.mapA (A := C(X, ℂ)) (B := C(X × S2, ℂ))
          (pullAlg (ContinuousMap.fst : C(X × S2, X))) b)
        (K0.mapA (A := C(S2, ℂ)) (B := C(X × S2, ℂ))
          (pullAlg (ContinuousMap.snd : C(X × S2, S2))) (cls hopfIdem) -
          cls (Mat.one C(X × S2, ℂ) 1)) = 0 → b = 0 := by
  intro b hb
  -- decompose `b` as a difference of classes of idempotents of equal size
  obtain ⟨n, P, Q, hP, hQ, hb'⟩ := hk_k0_eq_diff (C(X, ℂ)) b
  -- the reduced clutched classes of the two Bott units
  have hredP := redK_bottUnit X μ hμ n P hP
  have hredQ := redK_bottUnit X μ hμ n Q hQ
  -- the hypothesis says `bottMap b = 0`
  have hbott : Fund.bottMap X μ b = 0 := hb
  have hs : Fund.s X b = Work.KT.EG.fstStar X (cls (⟨n, P⟩ : Mat C(X, ℂ)))
      - Work.KT.EG.fstStar X (cls (⟨n, Q⟩ : Mat C(X, ℂ))) := by
    rw [hb', map_sub]
    rfl
  have h0 : μ (Fund.s X b) (Fund.beta X) = 0 := hbott
  have h1 : μ (Work.KT.EG.fstStar X (cls (⟨n, P⟩ : Mat C(X, ℂ)))
        - Work.KT.EG.fstStar X (cls (⟨n, Q⟩ : Mat C(X, ℂ))))
      (Work.KT.EG.betaHopf X) = 0 := by
    rw [← hs]
    exact h0
  have hdiff : μ (Work.KT.EG.fstStar X (cls (⟨n, P⟩ : Mat C(X, ℂ))))
        (Work.KT.EG.betaHopf X)
      = μ (Work.KT.EG.fstStar X (cls (⟨n, Q⟩ : Mat C(X, ℂ))))
        (Work.KT.EG.betaHopf X) := by
    have h := h1
    rw [show μ (Work.KT.EG.fstStar X (cls (⟨n, P⟩ : Mat C(X, ℂ)))
            - Work.KT.EG.fstStar X (cls (⟨n, Q⟩ : Mat C(X, ℂ))))
          = μ (Work.KT.EG.fstStar X (cls (⟨n, P⟩ : Mat C(X, ℂ))))
            - μ (Work.KT.EG.fstStar X (cls (⟨n, Q⟩ : Mat C(X, ℂ)))) from map_sub μ _ _] at h
    rw [AddMonoidHom.sub_apply, sub_eq_zero] at h
    exact h
  -- hence the two clutched classes agree
  have hk : Fund.kappa X n (bottUnit X n P hP) = Fund.kappa X n (bottUnit X n Q hQ) := by
    have hred : Work.KT.EG.redK X n (bottUnit X n P hP)
        = Work.KT.EG.redK X n (bottUnit X n Q hQ) := by
      rw [hredP, hredQ, hdiff]
    rw [Work.KT.EG.redK, Work.KT.EG.redK] at hred
    have h2 := congrArg (· + cls (Mat.one C(X × S2, ℂ) n)) hred
    simpa using h2
  -- Milnor's patching converse
  obtain ⟨k, g₀, g₁, hrel⟩ :=
    kappa_eq_disc X n (bottUnit X n P hP) (bottUnit X n Q hQ) hk
  -- the Bott index
  obtain ⟨N, hinv, hnorm⟩ := bott_index X
  have hN : N (n + k) (padUnit X k (bottUnit X n P hP))
      = N (n + k) (padUnit X k (bottUnit X n Q hQ)) :=
    hinv (n + k) (padUnit X k (bottUnit X n Q hQ)) (padUnit X k (bottUnit X n P hP)) g₀ g₁ hrel
  -- its normalisation on the padded Bott units
  have hnormP : N (n + k) (padUnit X k (bottUnit X n P hP))
      = cls (⟨n, P⟩ : Mat C(X, ℂ)) := by
    have hR : padProj X k P * padProj X k P = padProj X k P := padProj_isIdem X P hP
    have hu : ((padUnit X k (bottUnit X n P hP) :
        (Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))ˣ) :
        Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))
        = Fund.pullMat X (1 - padProj X k P)
          + (zUnit X : C(X × Sph ℂ, ℂ)) • Fund.pullMat X (padProj X k P) :=
      padUnit_bottUnit X (k := k) P hP
    rw [hnorm (n + k) (padProj X k P) hR (padUnit X k (bottUnit X n P hP)) hu,
      cls_padProj X P hP]
  have hnormQ : N (n + k) (padUnit X k (bottUnit X n Q hQ))
      = cls (⟨n, Q⟩ : Mat C(X, ℂ)) := by
    have hR : padProj X k Q * padProj X k Q = padProj X k Q := padProj_isIdem X Q hQ
    have hu : ((padUnit X k (bottUnit X n Q hQ) :
        (Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))ˣ) :
        Matrix (Fin (n + k)) (Fin (n + k)) C(X × Sph ℂ, ℂ))
        = Fund.pullMat X (1 - padProj X k Q)
          + (zUnit X : C(X × Sph ℂ, ℂ)) • Fund.pullMat X (padProj X k Q) :=
      padUnit_bottUnit X (k := k) Q hQ
    rw [hnorm (n + k) (padProj X k Q) hR (padUnit X k (bottUnit X n Q hQ)) hu,
      cls_padProj X Q hQ]
  rw [hb', ← hnormP, ← hnormQ, hN, sub_self]

end

end Work.KT.FP
