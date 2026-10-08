import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Props.CFP.eigen_pair_commute
import Submission.Work.L2F.Props.CFP.sub_sq_zero_commute
import Submission.Work.L2F.Props.CFP.factor_eq_zero
import Submission.Work.L2F.Props.CFP.pow_two_mul_orderOf_eigenvalue
import Submission.Work.L2F.Props.CFP.eigenvector_of_conj_inverse

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props

theorem range_pair_vec {F : Type*} (v u : Fin 2 → F) :
    Set.range ![v, u] = ({v, u} : Set (Fin 2 → F)) := by
  ext w
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

variable {F : Type*} [Field F]

theorem span_pair_eq_top_of_not_mem (v u : Fin 2 → F) (hv : v ≠ 0)
    (hu : u ∉ Submodule.span F ({v} : Set (Fin 2 → F))) :
    Submodule.span F ({v, u} : Set (Fin 2 → F)) = ⊤ := by
  have hu0 : u ≠ 0 := fun h0 => hu (h0 ▸ Submodule.zero_mem _)
  have hli : LinearIndependent F ![v, u] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    by_cases hb : b = 0
    · subst hb
      simp only [zero_smul, add_zero] at hab
      exact ⟨(smul_eq_zero.mp hab).resolve_right hv, rfl⟩
    · exfalso
      have hb' : b • u = -(a • v) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hab
      apply hu
      rw [Submodule.mem_span_singleton]
      refine ⟨-(b⁻¹ * a), ?_⟩
      calc (-(b⁻¹ * a)) • v = -((b⁻¹ * a) • v) := by rw [neg_smul]
        _ = -(b⁻¹ • (a • v)) := by rw [smul_smul]
        _ = b⁻¹ • (b • u) := by rw [← smul_neg, ← hb']
        _ = (b⁻¹ * b) • u := by rw [smul_smul]
        _ = u := by rw [inv_mul_cancel₀ hb, one_smul]
  have hsp := hli.span_eq_top_of_card_eq_finrank (by simp)
  rwa [range_pair_vec v u] at hsp

theorem scalar_eq_smul_one (c : F) :
    Matrix.scalar (Fin 2) c = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

/-- The eigenvalue of an element of `SL(2,F)` on a nonzero eigenvector is nonzero (the matrix is
invertible). -/
theorem eigenvector_eigenvalue_ne_zero (X : Matrix.SpecialLinearGroup (Fin 2) F)
    (v : Fin 2 → F) (hv : v ≠ 0) (c : F)
    (hXv : Matrix.mulVec (X : Matrix (Fin 2) (Fin 2) F) v = c • v) : c ≠ 0 := by
  intro h0
  have hzero : Matrix.mulVec (X : Matrix (Fin 2) (Fin 2) F) v = 0 := by
    rw [hXv, h0, zero_smul]
  have h1 : Matrix.mulVec
      (((X⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
      (Matrix.mulVec (X : Matrix (Fin 2) (Fin 2) F) v) = v := by
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  rw [hzero, Matrix.mulVec_zero] at h1
  exact hv h1.symm

theorem exists_scalar_of_conj_eq_inv (X : Matrix.SpecialLinearGroup (Fin 2) F)
    (T : GL (Fin 2) F)
    (h : Matrix.SpecialLinearGroup.toPGL X * Matrix.ProjGenLinGroup.mk T
      = Matrix.ProjGenLinGroup.mk T * (Matrix.SpecialLinearGroup.toPGL X)⁻¹) :
    ∃ eps : F, eps * eps = 1 ∧
      (X : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F)
        = eps • ((T : Matrix (Fin 2) (Fin 2) F) *
            ((X⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := by
  set Xm : Matrix (Fin 2) (Fin 2) F := (X : Matrix (Fin 2) (Fin 2) F) with hXm
  set Tm : Matrix (Fin 2) (Fin 2) F := (T : Matrix (Fin 2) (Fin 2) F) with hTm
  set Xim : Matrix (Fin 2) (Fin 2) F :=
    ((X⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hXim
  have h1 : Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL X * T)
      = Matrix.ProjGenLinGroup.mk (T * (Matrix.SpecialLinearGroup.toGL X)⁻¹) := by
    have h2 : Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL X)
        * Matrix.ProjGenLinGroup.mk T
        = Matrix.ProjGenLinGroup.mk T
          * Matrix.ProjGenLinGroup.mk ((Matrix.SpecialLinearGroup.toGL X)⁻¹) := by
      simpa using h
    rwa [← map_mul, ← map_mul] at h2
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h1
  rw [← map_inv (Matrix.SpecialLinearGroup.toGL) X] at hu
  have hmat : Xm * Tm * ((u : F) • 1) = Tm * Xim := by
    have h' := congrArg (fun z : GL (Fin 2) F => (z : Matrix (Fin 2) (Fin 2) F)) hu
    simp only [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_scalar,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, scalar_eq_smul_one] at h'
    simpa only [hXm, hTm, hXim] using h'
  have h3 : (u : F) • (Xm * Tm) = Tm * Xim := by
    rw [← hmat, Matrix.mul_smul, Matrix.mul_one]
  have h4 : Xm * Tm = ((u : F))⁻¹ • (Tm * Xim) := by
    have hune : (u : F) ≠ 0 := Units.ne_zero u
    have h5 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => ((u : F))⁻¹ • M) h3
    rwa [smul_smul, inv_mul_cancel₀ hune, one_smul] at h5
  have hTmT : (((T⁻¹ : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) * Tm = 1 := by
    rw [hTm, ← GeneralLinearGroup.coe_mul, inv_mul_cancel, GeneralLinearGroup.coe_one]
  have hconj : (((T⁻¹ : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) * Xm * Tm
      = ((u : F))⁻¹ • Xim := by
    calc (((T⁻¹ : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) * Xm * Tm
        = (((T⁻¹ : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) * (Xm * Tm) := by
          rw [mul_assoc]
      _ = (((T⁻¹ : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) * (((u : F))⁻¹ • (Tm * Xim)) := by
          rw [h4]
      _ = ((u : F))⁻¹ • ((((T⁻¹ : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) * (Tm * Xim)) := by
          rw [Matrix.mul_smul]
      _ = ((u : F))⁻¹ • ((((T⁻¹ : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) * Tm * Xim) := by
          rw [mul_assoc]
      _ = ((u : F))⁻¹ • (1 * Xim) := by rw [hTmT]
      _ = ((u : F))⁻¹ • Xim := by rw [one_mul]
  refine ⟨((u : F))⁻¹, ?_, ?_⟩
  · have hdet := congrArg Matrix.det hconj
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, Fintype.card_fin] at hdet
    have hdetX : Xm.det = 1 := by rw [hXm, Matrix.SpecialLinearGroup.det_coe]
    have hdetXi : Xim.det = 1 := by rw [hXim, Matrix.SpecialLinearGroup.det_coe]
    have hdetT : ((((T⁻¹ : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)).det * Tm.det = 1 := by
      rw [← Matrix.det_mul, hTmT, Matrix.det_one]
    rw [hdetX, hdetXi, mul_one, mul_one, hdetT] at hdet
    rw [pow_two] at hdet
    exact hdet.symm
  · simpa only [hXm, hTm, hXim] using h4

end Work.L2F.Props

namespace Work.L2F.Props

open Work.L2F.Props.CFP

theorem inverted_commute_of_common_fixed_point (F : Type*) [Field F]
    (t x y : Matrix.ProjGenLinGroup (Fin 2) F) (ht : orderOf t = 2)
    (hx : t * x * t⁻¹ = x⁻¹) (hy : t * y * t⁻¹ = y⁻¹)
    (hxodd : Odd (orderOf x)) (hyodd : Odd (orderOf y))
    (v : Fin 2 → F) (hv : v ≠ 0)
    (hxfix : ∃ X : Matrix.SpecialLinearGroup (Fin 2) F,
        Matrix.SpecialLinearGroup.toPGL X = x ∧
          ∃ c : F, Matrix.mulVec (X : Matrix (Fin 2) (Fin 2) F) v = c • v)
    (hyfix : ∃ Y : Matrix.SpecialLinearGroup (Fin 2) F,
        Matrix.SpecialLinearGroup.toPGL Y = y ∧
          ∃ c : F, Matrix.mulVec (Y : Matrix (Fin 2) (Fin 2) F) v = c • v) :
    x * y = y * x := by
  obtain ⟨X, hXx, c, hXv⟩ := hxfix
  obtain ⟨Y, hYy, d, hYv⟩ := hyfix
  obtain ⟨T, hT⟩ : ∃ T : GL (Fin 2) F, Matrix.ProjGenLinGroup.mk T = t :=
    Matrix.ProjGenLinGroup.mk_surjective t
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht, pow_two] at h
  have htt : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hxt : x * t = t * x⁻¹ := by
    have h := congrArg (fun z => t * z) hx
    rw [htt] at h
    have h2 : t * (t * x * t) = x * t := by
      rw [show t * (t * x * t) = (t * t) * (x * t) by group, ht2, one_mul]
    rwa [h2] at h
  have hyt : y * t = t * y⁻¹ := by
    have h := congrArg (fun z => t * z) hy
    rw [htt] at h
    have h2 : t * (t * y * t) = y * t := by
      rw [show t * (t * y * t) = (t * t) * (y * t) by group, ht2, one_mul]
    rwa [h2] at h
  have hrelX : Matrix.SpecialLinearGroup.toPGL X * Matrix.ProjGenLinGroup.mk T
      = Matrix.ProjGenLinGroup.mk T * (Matrix.SpecialLinearGroup.toPGL X)⁻¹ := by
    have h := hxt
    rw [← hXx, ← hT] at h
    exact h
  have hrelY : Matrix.SpecialLinearGroup.toPGL Y * Matrix.ProjGenLinGroup.mk T
      = Matrix.ProjGenLinGroup.mk T * (Matrix.SpecialLinearGroup.toPGL Y)⁻¹ := by
    have h := hyt
    rw [← hYy, ← hT] at h
    exact h
  obtain ⟨eps, heps2, hXrel⟩ := exists_scalar_of_conj_eq_inv (F := F) X T hrelX
  obtain ⟨del, hdel2, hYrel⟩ := exists_scalar_of_conj_eq_inv (F := F) Y T hrelY
  set u : Fin 2 → F := Matrix.mulVec (T : Matrix (Fin 2) (Fin 2) F) v with hu_def
  have hu_ne : u ≠ 0 := by
    intro h0
    have h1 : Matrix.mulVec (((T⁻¹ : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) u = v := by
      rw [hu_def, Matrix.mulVec_mulVec, ← GeneralLinearGroup.coe_mul, inv_mul_cancel,
        GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    rw [h0] at h1
    simp only [Matrix.mulVec_zero] at h1
    exact hv h1.symm
  have hXu : Matrix.mulVec (X : Matrix (Fin 2) (Fin 2) F) u = (eps * c⁻¹) • u := by
    rw [hu_def]
    exact eigenvector_of_conj_inverse F T X v c eps hXv hXrel
  have hYu : Matrix.mulVec (Y : Matrix (Fin 2) (Fin 2) F) u = (del * d⁻¹) • u := by
    rw [hu_def]
    exact eigenvector_of_conj_inverse F T Y v d del hYv hYrel
  have hcne : c ≠ 0 := eigenvector_eigenvalue_ne_zero X v hv c hXv
  have hdne : d ≠ 0 := eigenvector_eigenvalue_ne_zero Y v hv d hYv
  have hcomm : (X : Matrix (Fin 2) (Fin 2) F) * (Y : Matrix (Fin 2) (Fin 2) F)
      = (Y : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F) := by
    by_cases hin : u ∈ Submodule.span F ({v} : Set (Fin 2 → F))
    · obtain ⟨gam, hgam⟩ : ∃ gam : F, gam • v = u := Submodule.mem_span_singleton.mp hin
      have hgamne : gam ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at hgam
        exact hu_ne hgam.symm
      have hc2eps : c ^ 2 = eps := by
        have e1 : Matrix.mulVec (X : Matrix (Fin 2) (Fin 2) F) u = (gam * c) • v := by
          rw [← hgam, Matrix.mulVec_smul, hXv, smul_smul]
        have e2 : Matrix.mulVec (X : Matrix (Fin 2) (Fin 2) F) u = ((eps * c⁻¹) * gam) • v := by
          rw [hXu, ← hgam, smul_smul]
        have hsub : ((gam * c) - (eps * c⁻¹) * gam) • v = 0 := by
          rw [sub_smul, ← e1, ← e2, sub_self]
        have hgc : gam * c = (eps * c⁻¹) * gam := by
          rcases smul_eq_zero.mp hsub with h | h
          · exact sub_eq_zero.mp h
          · exact absurd h hv
        have hl : gam⁻¹ * (gam * c) = c := by rw [← mul_assoc, inv_mul_cancel₀ hgamne, one_mul]
        have hr : gam⁻¹ * ((eps * c⁻¹) * gam) = eps * c⁻¹ := by
          rw [← mul_assoc, mul_comm (gam⁻¹) (eps * c⁻¹), mul_assoc, inv_mul_cancel₀ hgamne,
            mul_one]
        have hceq : c = eps * c⁻¹ := by
          have := congrArg (fun z => gam⁻¹ * z) hgc
          rwa [hl, hr] at this
        have k1 : c * c = (eps * c⁻¹) * c := congrArg (fun z => z * c) hceq
        have k2 : (eps * c⁻¹) * c = eps := by
          rw [mul_assoc, inv_mul_cancel₀ hcne, mul_one]
        rw [pow_two]
        exact k1.trans k2
      have hd2del : d ^ 2 = del := by
        have e1 : Matrix.mulVec (Y : Matrix (Fin 2) (Fin 2) F) u = (gam * d) • v := by
          rw [← hgam, Matrix.mulVec_smul, hYv, smul_smul]
        have e2 : Matrix.mulVec (Y : Matrix (Fin 2) (Fin 2) F) u = ((del * d⁻¹) * gam) • v := by
          rw [hYu, ← hgam, smul_smul]
        have hsub : ((gam * d) - (del * d⁻¹) * gam) • v = 0 := by
          rw [sub_smul, ← e1, ← e2, sub_self]
        have hgd : gam * d = (del * d⁻¹) * gam := by
          rcases smul_eq_zero.mp hsub with h | h
          · exact sub_eq_zero.mp h
          · exact absurd h hv
        have hl : gam⁻¹ * (gam * d) = d := by rw [← mul_assoc, inv_mul_cancel₀ hgamne, one_mul]
        have hr : gam⁻¹ * ((del * d⁻¹) * gam) = del * d⁻¹ := by
          rw [← mul_assoc, mul_comm (gam⁻¹) (del * d⁻¹), mul_assoc, inv_mul_cancel₀ hgamne,
            mul_one]
        have hdeq : d = del * d⁻¹ := by
          have := congrArg (fun z => gam⁻¹ * z) hgd
          rwa [hl, hr] at this
        have k1 : d * d = (del * d⁻¹) * d := congrArg (fun z => z * d) hdeq
        have k2 : (del * d⁻¹) * d = del := by
          rw [mul_assoc, inv_mul_cancel₀ hdne, mul_one]
        rw [pow_two]
        exact k1.trans k2
      have hc2 : c ^ 2 = 1 := by
        have heps1 : eps = 1 ∨ eps = -1 := mul_self_eq_one_iff.mp heps2
        have hpow : (c ^ 2) ^ (orderOf x) = 1 := by
          have h := pow_two_mul_orderOf_eigenvalue F X v hv c hXv (orderOf x)
            (by rw [hXx, pow_orderOf_eq_one])
          rwa [pow_mul] at h
        rcases heps1 with h1 | h1
        · rw [hc2eps, h1]
        · have hneg : (-1 : F) ^ (orderOf x) = 1 := by
            rw [← h1, ← hc2eps]
            exact hpow
          have hneg' : (-1 : F) ^ (orderOf x) = -1 := hxodd.neg_one_pow
          have h2 : (2 : F) = 0 := by
            have h4 : (1 : F) = -1 := hneg.symm.trans hneg'
            have h5 : (1 : F) + 1 = (0 : F) := by
              have h6 : (1 : F) + 1 = (-1 : F) + 1 := congrArg (fun z => z + 1) h4
              rw [neg_add_cancel] at h6
              exact h6
            rw [show (2 : F) = 1 + 1 by norm_num]
            exact h5
          have hone : (-1 : F) = 1 := by
            have h3 : (-1 : F) + (2 : F) = 1 := by
              have htwo : (2 : F) = 1 + 1 := by norm_num
              rw [htwo, ← add_assoc, neg_add_cancel, zero_add]
            rw [h2, add_zero] at h3
            exact h3
          rw [hc2eps, h1, hone]
      have hd2 : d ^ 2 = 1 := by
        have hdel1 : del = 1 ∨ del = -1 := mul_self_eq_one_iff.mp hdel2
        have hpow : (d ^ 2) ^ (orderOf y) = 1 := by
          have h := pow_two_mul_orderOf_eigenvalue F Y v hv d hYv (orderOf y)
            (by rw [hYy, pow_orderOf_eq_one])
          rwa [pow_mul] at h
        rcases hdel1 with h1 | h1
        · rw [hd2del, h1]
        · have hneg : (-1 : F) ^ (orderOf y) = 1 := by
            rw [← h1, ← hd2del]
            exact hpow
          have hneg' : (-1 : F) ^ (orderOf y) = -1 := hyodd.neg_one_pow
          have h2 : (2 : F) = 0 := by
            have h4 : (1 : F) = -1 := hneg.symm.trans hneg'
            have h5 : (1 : F) + 1 = (0 : F) := by
              have h6 : (1 : F) + 1 = (-1 : F) + 1 := congrArg (fun z => z + 1) h4
              rw [neg_add_cancel] at h6
              exact h6
            rw [show (2 : F) = 1 + 1 by norm_num]
            exact h5
          have hone : (-1 : F) = 1 := by
            have h3 : (-1 : F) + (2 : F) = 1 := by
              have htwo : (2 : F) = 1 + 1 := by norm_num
              rw [htwo, ← add_assoc, neg_add_cancel, zero_add]
            rw [h2, add_zero] at h3
            exact h3
          rw [hd2del, h1, hone]
      have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hc2)
      have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hd2)
      have hM2 : ((X : Matrix (Fin 2) (Fin 2) F) - c • 1)
          * ((X : Matrix (Fin 2) (Fin 2) F) - c • 1) = 0 := by
        have h := factor_eq_zero F X v hv c hXv
        rwa [hcinv] at h
      have hMv : Matrix.mulVec ((X : Matrix (Fin 2) (Fin 2) F) - c • 1) v = 0 := by
        rw [Matrix.sub_mulVec, hXv, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
      have hN2 : ((Y : Matrix (Fin 2) (Fin 2) F) - d • 1)
          * ((Y : Matrix (Fin 2) (Fin 2) F) - d • 1) = 0 := by
        have h := factor_eq_zero F Y v hv d hYv
        rwa [hdinv] at h
      have hNv : Matrix.mulVec ((Y : Matrix (Fin 2) (Fin 2) F) - d • 1) v = 0 := by
        rw [Matrix.sub_mulVec, hYv, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
      exact sub_sq_zero_commute F (X : Matrix (Fin 2) (Fin 2) F) (Y : Matrix (Fin 2) (Fin 2) F)
        v hv c d hM2 hN2 hMv hNv
    · have hspan : Submodule.span F ({v, u} : Set (Fin 2 → F)) = ⊤ :=
        span_pair_eq_top_of_not_mem v u hv hin
      exact eigen_pair_commute F (X : Matrix (Fin 2) (Fin 2) F) (Y : Matrix (Fin 2) (Fin 2) F)
        v u c (eps * c⁻¹) d (del * d⁻¹) hspan hXv hXu hYv hYu
  have hSL : X * Y = Y * X := by
    apply Subtype.ext
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using hcomm
  calc x * y = Matrix.SpecialLinearGroup.toPGL X * Matrix.SpecialLinearGroup.toPGL Y := by
        rw [hXx, hYy]
    _ = Matrix.SpecialLinearGroup.toPGL (X * Y) := (map_mul _ X Y).symm
    _ = Matrix.SpecialLinearGroup.toPGL (Y * X) := by rw [hSL]
    _ = Matrix.SpecialLinearGroup.toPGL Y * Matrix.SpecialLinearGroup.toPGL X := map_mul _ Y X
    _ = y * x := by rw [hYy, hXx]

end Work.L2F.Props
