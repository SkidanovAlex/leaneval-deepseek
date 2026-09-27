import Mathlib
import Submission.Work.KT.HopfK.Basic
import Submission.Work.KT.HopfK.Cone
import Submission.Work.KT.hk_k0_eq_diff
import Submission.Work.KT.hk_idem_C
import Submission.Work.KT.hk_radial_collar
import Submission.Work.KT.hk_cap_triv
import Submission.Work.KT.rel_cancel
import Submission.Work.KT.k0_basic
import Submission.Work.KT.hk_k0cls
import Submission.Work.KT.homInv_cls_eq_of_conj

namespace Work.KT.HopfK

open Matrix

set_option maxHeartbeats 4000000

noncomputable section

/-! ## Elementary lemmas -/

/-- Entrywise image of the identity matrix. -/
private lemma Mat.map_one' {R S : Type} [Ring R] [Ring S] (φ : R →+* S) (n : ℕ) :
    Mat.map φ (Mat.one R n) = Mat.one S n := by
  change (⟨n, (1 : Matrix (Fin n) (Fin n) R).map (⇑φ)⟩ : Mat S) =
    (⟨n, (1 : Matrix (Fin n) (Fin n) S)⟩ : Mat S)
  rw [Matrix.map_one (⇑φ) (map_zero φ) (map_one φ)]

/-- The class of the diagonal idempotent `diag(1_r,0)` of size `n ≥ r` is the class of `1_r`. -/
private lemma cls_diagMat (R : Type) [Ring R] (r n : ℕ) (h : r ≤ n) :
    cls (diagMat R r n) = cls (Mat.one R r) :=
  cls_eq_of_mvN (diagMat_isIdem R r n) (Mat.one_idem R r) (hk_diagMat_mvN_one R r n h)

/-- The class of the diagonal idempotent `diag(1_r,0)` of size `n ≥ r` over `ℂ`. -/
private lemma cls_diagIdemMat (r n : ℕ) (h : r ≤ n) :
    cls (⟨n, diagIdemMat r n⟩ : Mat ℂ) = cls (Mat.one ℂ r) :=
  cls_diagMat ℂ r n h

/-- The diagonal idempotents of size `n` determined by `r` and by `m` agree as soon as
`min r n = m`. -/
private lemma diagIdemMat_eq_of_min {r n m : ℕ} (h : min r n = m) :
    diagIdemMat r n = diagIdemMat m n := by
  rcases le_or_gt r n with hr | hr
  · have hrm : r = m := by rw [← h, min_eq_left hr]
    rw [hrm]
  · have hnm : n = m := by rw [← h, min_eq_right hr.le]
    subst hnm
    change Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then (1 : ℂ) else 0) =
      Matrix.diagonal (fun i : Fin n => if (i : ℕ) < n then (1 : ℂ) else 0)
    rw [Matrix.diagonal_eq_diagonal_iff]
    intro i
    rw [if_pos (lt_trans i.isLt hr), if_pos i.isLt]

/-- A constant matrix over a `ℂ`-algebra is unchanged by an evaluation `A →ₐ[ℂ] ℂ`. -/
private lemma matConst_map_alg {A : Type} [Semiring A] [Algebra ℂ A] {n : ℕ}
    (ψ : A →ₐ[ℂ] ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    (matConst A M).map (⇑ψ) = M := by
  ext i j
  simp only [matConst, Matrix.map_apply]
  rw [ψ.commutes]
  simp

/-! ## The main lemma -/

theorem hk_collared (m : ℕ) (hm : 1 ≤ m) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (t0 : Tgt m) (ht0p : t0 ∈ capTplus m) (ht0m : t0 ∈ capTminus m)
    (a : K0 (coneAlg (hopfKMap m μ)))
    (ha : K0.mapA (augCone (hopfKMap m μ) t0) a = 0) :
    ∃ (n r : ℕ) (p q : Matrix (Fin n) (Fin n) (coneAlg (hopfKMap m μ))),
      Mat.IsIdem (⟨n, p⟩ : Mat (coneAlg (hopfKMap m μ))) ∧
      Mat.IsIdem (⟨n, q⟩ : Mat (coneAlg (hopfKMap m μ))) ∧
      cls (⟨n, p⟩ : Mat (coneAlg (hopfKMap m μ))) - cls (coneDiag m (hopfKMap m μ) r n) = a ∧
      cls (⟨n, q⟩ : Mat (coneAlg (hopfKMap m μ))) - cls (coneDiag m (hopfKMap m μ) r n) = a ∧
      (∀ t : Tgt m, t ∈ capTplus m → p.map (evalT m (hopfKMap m μ) t) = diagIdemMat r n) ∧
      (∀ t : Tgt m, t ∈ capTminus m → q.map (evalT m (hopfKMap m μ) t) = diagIdemMat r n) ∧
      (∀ z : Ball (Eu m × Eu m), 1 / 2 ≤ ‖(z : Eu m × Eu m)‖ →
        p.map (evalD m (hopfKMap m μ) z) = p.map (evalD m (hopfKMap m μ) (normPtBall z))) ∧
      (∀ z : Ball (Eu m × Eu m), 1 / 2 ≤ ‖(z : Eu m × Eu m)‖ →
        q.map (evalD m (hopfKMap m μ) z) = q.map (evalD m (hopfKMap m μ) (normPtBall z))) := by
  -- `a = cls P - cls Q`
  have haT : K0.mapA (evalT m (hopfKMap m μ) t0) a = 0 := ha
  obtain ⟨m₀, P, Q, hP, hQ, ha_eq⟩ := hk_k0_eq_diff (coneAlg (hopfKMap m μ)) a
  have hP' : Mat.IsIdem (⟨m₀, P⟩ : Mat (coneAlg (hopfKMap m μ))) := hP
  have hQ' : Mat.IsIdem (⟨m₀, Q⟩ : Mat (coneAlg (hopfKMap m μ))) := hQ
  let Qc : Matrix (Fin m₀) (Fin m₀) (coneAlg (hopfKMap m μ)) := 1 - Q
  have hQc : Mat.IsIdem (⟨m₀, Qc⟩ : Mat (coneAlg (hopfKMap m μ))) := Mat.isIdem_one_sub hQ'
  -- the complementary idempotent class
  have hcompl : cls (⟨m₀, Qc⟩ : Mat (coneAlg (hopfKMap m μ))) =
      cls (Mat.one (coneAlg (hopfKMap m μ)) m₀) - cls (⟨m₀, Q⟩ : Mat (coneAlg (hopfKMap m μ))) := by
    have hmvn := mvN_sum_compl (coneAlg (hopfKMap m μ))
      (⟨m₀, Q⟩ : Mat (coneAlg (hopfKMap m μ))) hQ'
    have hsum := cls_eq_of_mvN (Mat.sum_idem hQ' hQc)
      (Mat.one_idem (coneAlg (hopfKMap m μ)) m₀) hmvn
    rw [cls_sum hQ' hQc] at hsum
    exact eq_sub_iff_add_eq.mpr
      ((add_comm (cls (⟨m₀, Qc⟩ : Mat (coneAlg (hopfKMap m μ))))
        (cls (⟨m₀, Q⟩ : Mat (coneAlg (hopfKMap m μ))))).trans hsum)
  -- the block matrix `F = P ⊕ (1 - Q)` of size `N = 2 m₀`
  let N : ℕ := m₀ + m₀
  let Fm : Matrix (Fin N) (Fin N) (coneAlg (hopfKMap m μ)) :=
    (Mat.sum (⟨m₀, P⟩ : Mat (coneAlg (hopfKMap m μ))) ⟨m₀, Qc⟩).2
  have hFm : Fm * Fm = Fm := Mat.sum_idem hP' hQc
  have hFcls : cls (⟨N, Fm⟩ : Mat (coneAlg (hopfKMap m μ))) =
      cls (⟨m₀, P⟩ : Mat (coneAlg (hopfKMap m μ))) +
        cls (⟨m₀, Qc⟩ : Mat (coneAlg (hopfKMap m μ))) := cls_sum hP' hQc
  have hcone_cls : cls (coneDiag m (hopfKMap m μ) m₀ N) =
      cls (Mat.one (coneAlg (hopfKMap m μ)) m₀) :=
    cls_diagMat (coneAlg (hopfKMap m μ)) m₀ N (Nat.le_add_right m₀ m₀)
  have haF : a = cls (⟨N, Fm⟩ : Mat (coneAlg (hopfKMap m μ))) -
      cls (coneDiag m (hopfKMap m μ) m₀ N) := by
    rw [ha_eq, hFcls, hcompl, hcone_cls]
    abel
  -- radial collaring of `F`
  obtain ⟨R, hR, hRcls, hRcollar⟩ := hk_radial_collar m μ (hopfKMap m μ) N Fm hFm
  have hR' : Mat.IsIdem (⟨N, R⟩ : Mat (coneAlg (hopfKMap m μ))) := hR
  have hRcls' : cls (⟨N, R⟩ : Mat (coneAlg (hopfKMap m μ))) = cls (⟨N, Fm⟩ : Mat (coneAlg (hopfKMap m μ))) := hRcls
  -- the evaluation at `t0`
  let φT : coneAlg (hopfKMap m μ) →+* ℂ := (evalT m (hopfKMap m μ) t0).toRingHom
  let X : Matrix (Fin N) (Fin N) ℂ := R.map (⇑φT)
  have hX : X * X = X := by
    change (R.map (⇑φT)) * (R.map (⇑φT)) = R.map (⇑φT)
    rw [← Matrix.map_mul, hR]
  have hmapR : K0.mapA (evalT m (hopfKMap m μ) t0) (cls (⟨N, R⟩ : Mat (coneAlg (hopfKMap m μ))))
      = cls (⟨N, X⟩ : Mat ℂ) := by
    show K0.map (evalT m (hopfKMap m μ) t0).toRingHom (cls (⟨N, R⟩ : Mat (coneAlg (hopfKMap m μ))))
      = cls (⟨N, X⟩ : Mat ℂ)
    rw [K0.map_cls _ hR']
    rfl
  have hmapF : K0.mapA (evalT m (hopfKMap m μ) t0) (cls (⟨N, R⟩ : Mat (coneAlg (hopfKMap m μ))))
      = K0.mapA (evalT m (hopfKMap m μ) t0) (a + cls (coneDiag m (hopfKMap m μ) m₀ N)) := by
    congr 1
    rw [hRcls']
    rw [haF]
    abel
  have hCd : Mat.map (evalT m (hopfKMap m μ) t0).toRingHom (coneDiag m (hopfKMap m μ) m₀ N)
      = (⟨N, diagIdemMat m₀ N⟩ : Mat ℂ) := by
    have hmat : (coneDiag m (hopfKMap m μ) m₀ N).2.map (⇑(evalT m (hopfKMap m μ) t0).toRingHom)
        = diagIdemMat m₀ N := by
      ext i j
      simp only [coneDiag, Matrix.map_apply, Matrix.diagonal_apply, diagIdemMat]
      by_cases hij : i = j
      · subst hij
        by_cases hi : (i : ℕ) < m₀ <;> simp [hi]
      · simp [hij]
    rw [show Mat.map (evalT m (hopfKMap m μ) t0).toRingHom (coneDiag m (hopfKMap m μ) m₀ N)
        = (⟨N, (coneDiag m (hopfKMap m μ) m₀ N).2.map
            (⇑(evalT m (hopfKMap m μ) t0).toRingHom)⟩ : Mat ℂ) from rfl, hmat]
  have hmapD : K0.mapA (evalT m (hopfKMap m μ) t0) (a + cls (coneDiag m (hopfKMap m μ) m₀ N))
      = cls (⟨N, diagIdemMat m₀ N⟩ : Mat ℂ) := by
    show K0.map (evalT m (hopfKMap m μ) t0).toRingHom
      (a + cls (coneDiag m (hopfKMap m μ) m₀ N)) = cls (⟨N, diagIdemMat m₀ N⟩ : Mat ℂ)
    rw [map_add, haT, zero_add,
      K0.map_cls _ (coneDiag_isIdem m (hopfKMap m μ) m₀ N), hCd]
  have hclsX : cls (⟨N, X⟩ : Mat ℂ) = cls (⟨N, diagIdemMat m₀ N⟩ : Mat ℂ) := by
    rw [← hmapR, hmapF, hmapD]
  -- conjugating `X` to the diagonal idempotent
  obtain ⟨r', g, ginv, hgg', hhh', hconj'⟩ := hk_idem_C N X hX
  have hpdiag : (diagIdemMat r' N) * (diagIdemMat r' N) = diagIdemMat r' N :=
    diagMat_isIdem ℂ r' N
  have hclsdiag : cls (⟨N, diagIdemMat r' N⟩ : Mat ℂ) = cls (⟨N, diagIdemMat m₀ N⟩ : Mat ℂ) := by
    have hu : g * X = diagIdemMat r' N * g := by
      calc g * X = g * X * (ginv * g) := by rw [hhh', mul_one]
        _ = (g * X * ginv) * g := by noncomm_ring
        _ = diagIdemMat r' N * g := by rw [hconj']
    have h := homInv_cls_eq_of_conj (p := diagIdemMat r' N) (q := X) hpdiag hX
      ⟨g, ginv, hgg', hhh'⟩ hu
    rw [h, hclsX]
  have hmin : min r' N = m₀ := by
    have hd : diagIdemMat r' N = diagIdemMat (min r' N) N :=
      diagIdemMat_eq_of_min (r := r') (n := N) (m := min r' N) rfl
    have hEq : cls (⟨N, diagIdemMat (min r' N) N⟩ : Mat ℂ) = cls (⟨N, diagIdemMat m₀ N⟩ : Mat ℂ) := by
      rw [← hd]; exact hclsdiag
    have hr : k0Rank (cls (⟨N, diagIdemMat (min r' N) N⟩ : Mat ℂ)) = ((min r' N : ℕ) : ℤ) := by
      rw [cls_diagIdemMat (min r' N) N (min_le_right _ _), k0Rank_one]
    have hm : k0Rank (cls (⟨N, diagIdemMat m₀ N⟩ : Mat ℂ)) = ((m₀ : ℕ) : ℤ) := by
      rw [cls_diagIdemMat m₀ N (Nat.le_add_right m₀ m₀), k0Rank_one]
    have hh := congrArg k0Rank hEq
    rw [hr, hm] at hh
    exact_mod_cast hh
  have hdiag : diagIdemMat r' N = diagIdemMat m₀ N := diagIdemMat_eq_of_min hmin
  have hconj'' : g * X * ginv = diagIdemMat r' N := hconj'
  have hconj : g * X * ginv = diagIdemMat m₀ N := by rw [hconj'', hdiag]
  -- conjugation by the constant matrices `g`, `ginv`
  let ggA : Matrix (Fin N) (Fin N) (coneAlg (hopfKMap m μ)) := matConst (coneAlg (hopfKMap m μ)) g
  let hhA : Matrix (Fin N) (Fin N) (coneAlg (hopfKMap m μ)) := matConst (coneAlg (hopfKMap m μ)) ginv
  have hggA : ggA * hhA = 1 := by
    change matConst (coneAlg (hopfKMap m μ)) g * matConst (coneAlg (hopfKMap m μ)) ginv = 1
    rw [← matConst_mul, hgg', matConst_one]
  have hhhA : hhA * ggA = 1 := by
    change matConst (coneAlg (hopfKMap m μ)) ginv * matConst (coneAlg (hopfKMap m μ)) g = 1
    rw [← matConst_mul, hhh', matConst_one]
  let Pc : Matrix (Fin N) (Fin N) (coneAlg (hopfKMap m μ)) := ggA * R * hhA
  have hPc : Pc * Pc = Pc := by
    change (ggA * R * hhA) * (ggA * R * hhA) = ggA * R * hhA
    calc (ggA * R * hhA) * (ggA * R * hhA) = ggA * (R * (hhA * ggA) * R) * hhA := by noncomm_ring
      _ = ggA * (R * 1 * R) * hhA := by rw [hhhA]
      _ = ggA * (R * R) * hhA := by rw [mul_one]
      _ = ggA * R * hhA := by rw [hR]
  have hclsPc : cls (⟨N, Pc⟩ : Mat (coneAlg (hopfKMap m μ))) = cls (⟨N, R⟩ : Mat (coneAlg (hopfKMap m μ))) := by
    have hu : ggA * R = Pc * ggA := by
      change ggA * R = (ggA * R * hhA) * ggA
      rw [Matrix.mul_assoc (ggA * R) hhA ggA, hhhA, mul_one]
    exact homInv_cls_eq_of_conj Pc R hPc hR' ⟨ggA, hhA, hggA, hhhA⟩ hu
  have hPct0 : Pc.map (evalT m (hopfKMap m μ) t0) = diagIdemMat m₀ N := by
    have h1 : Pc.map (evalT m (hopfKMap m μ) t0) =
        ggA.map (evalT m (hopfKMap m μ) t0) * (R.map (evalT m (hopfKMap m μ) t0))
          * hhA.map (evalT m (hopfKMap m μ) t0) := by
      change ((ggA * R * hhA).map (evalT m (hopfKMap m μ) t0)) = _
      rw [Matrix.map_mul, Matrix.map_mul]
    rw [h1, matConst_map_alg (A := coneAlg (hopfKMap m μ)) (ψ := evalT m (hopfKMap m μ) t0) g,
      matConst_map_alg (A := coneAlg (hopfKMap m μ)) (ψ := evalT m (hopfKMap m μ) t0) ginv]
    show g * X * ginv = diagIdemMat m₀ N
    rw [hconj]
  have hPccollar : ∀ z : Ball (Eu m × Eu m), 1 / 2 ≤ ‖(z : Eu m × Eu m)‖ →
      Pc.map (evalD m (hopfKMap m μ) z) = Pc.map (evalD m (hopfKMap m μ) (normPtBall z)) := by
    intro z hz
    have h1 : ∀ w : Ball (Eu m × Eu m),
        Pc.map (evalD m (hopfKMap m μ) w) =
          g * R.map (evalD m (hopfKMap m μ) w) * ginv := by
      intro w
      change ((ggA * R * hhA).map (evalD m (hopfKMap m μ) w)) = _
      rw [Matrix.map_mul, Matrix.map_mul,
        matConst_map_alg (A := coneAlg (hopfKMap m μ)) (ψ := evalD m (hopfKMap m μ) w) g,
        matConst_map_alg (A := coneAlg (hopfKMap m μ)) (ψ := evalD m (hopfKMap m μ) w) ginv]
    rw [h1 z, h1 (normPtBall z), hRcollar z hz]
  -- collared representatives on the two caps
  obtain ⟨hcap1, hcap2⟩ :=
    hk_cap_triv m μ (hopfKMap m μ) t0 ht0p ht0m N m₀ Pc hPc hPct0 hPccollar
  obtain ⟨g₁, G₁, hg1, hG1, hcapP, hradP, _⟩ := hcap1
  obtain ⟨g₂, G₂, hg2, hG2, hcapM, hradM, _⟩ := hcap2
  refine ⟨N, m₀, g₁ * Pc * G₁, g₂ * Pc * G₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `p` is idempotent
    show (g₁ * Pc * G₁) * (g₁ * Pc * G₁) = g₁ * Pc * G₁
    calc (g₁ * Pc * G₁) * (g₁ * Pc * G₁) = g₁ * (Pc * (G₁ * g₁) * Pc) * G₁ := by noncomm_ring
      _ = g₁ * (Pc * 1 * Pc) * G₁ := by rw [hG1]
      _ = g₁ * (Pc * Pc) * G₁ := by rw [mul_one]
      _ = g₁ * Pc * G₁ := by rw [hPc]
  · show (g₂ * Pc * G₂) * (g₂ * Pc * G₂) = g₂ * Pc * G₂
    calc (g₂ * Pc * G₂) * (g₂ * Pc * G₂) = g₂ * (Pc * (G₂ * g₂) * Pc) * G₂ := by noncomm_ring
      _ = g₂ * (Pc * 1 * Pc) * G₂ := by rw [hG2]
      _ = g₂ * (Pc * Pc) * G₂ := by rw [mul_one]
      _ = g₂ * Pc * G₂ := by rw [hPc]
  · -- the class of `p`
    have hpcls : cls (⟨N, g₁ * Pc * G₁⟩ : Mat (coneAlg (hopfKMap m μ))) =
        cls (⟨N, Pc⟩ : Mat (coneAlg (hopfKMap m μ))) := by
      have hu : g₁ * Pc = (g₁ * Pc * G₁) * g₁ := by
        rw [Matrix.mul_assoc (g₁ * Pc) G₁ g₁, hG1, mul_one]
      exact homInv_cls_eq_of_conj (g₁ * Pc * G₁) Pc
        (by
          show (g₁ * Pc * G₁) * (g₁ * Pc * G₁) = g₁ * Pc * G₁
          calc (g₁ * Pc * G₁) * (g₁ * Pc * G₁) = g₁ * (Pc * (G₁ * g₁) * Pc) * G₁ := by noncomm_ring
            _ = g₁ * (Pc * 1 * Pc) * G₁ := by rw [hG1]
            _ = g₁ * (Pc * Pc) * G₁ := by rw [mul_one]
            _ = g₁ * Pc * G₁ := by rw [hPc])
        hPc ⟨g₁, G₁, hg1, hG1⟩ hu
    rw [hpcls, hclsPc, hRcls']
    exact haF.symm
  · have hqcls : cls (⟨N, g₂ * Pc * G₂⟩ : Mat (coneAlg (hopfKMap m μ))) =
        cls (⟨N, Pc⟩ : Mat (coneAlg (hopfKMap m μ))) := by
      have hu : g₂ * Pc = (g₂ * Pc * G₂) * g₂ := by
        rw [Matrix.mul_assoc (g₂ * Pc) G₂ g₂, hG2, mul_one]
      exact homInv_cls_eq_of_conj (g₂ * Pc * G₂) Pc
        (by
          show (g₂ * Pc * G₂) * (g₂ * Pc * G₂) = g₂ * Pc * G₂
          calc (g₂ * Pc * G₂) * (g₂ * Pc * G₂) = g₂ * (Pc * (G₂ * g₂) * Pc) * G₂ := by noncomm_ring
            _ = g₂ * (Pc * 1 * Pc) * G₂ := by rw [hG2]
            _ = g₂ * (Pc * Pc) * G₂ := by rw [mul_one]
            _ = g₂ * Pc * G₂ := by rw [hPc])
        hPc ⟨g₂, G₂, hg2, hG2⟩ hu
    rw [hqcls, hclsPc, hRcls']
    exact haF.symm
  · exact hcapP
  · exact hcapM
  · exact hradP
  · exact hradM

end

end Work.KT.HopfK
