import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

set_option linter.style.haveILetI false

open Polynomial Module

namespace Commons.Algebra.Polynomial

noncomputable section

variable {F : Type*} [Field F]

-- ============ Part 1: linearity of divByMonic ============

section Linearity

variable {R : Type*} [CommRing R]

lemma divByMonic_add {q : R[X]} (hq : q.Monic) (p₁ p₂ : R[X]) :
    (p₁ + p₂) /ₘ q = p₁ /ₘ q + p₂ /ₘ q := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI := hR
    exact Subsingleton.elim _ _
  · refine (div_modByMonic_unique (p₁ /ₘ q + p₂ /ₘ q) (p₁ %ₘ q + p₂ %ₘ q) hq
        ⟨?_, (degree_add_le _ _).trans_lt
          (max_lt (degree_modByMonic_lt _ hq) (degree_modByMonic_lt _ hq))⟩).1
    linear_combination (modByMonic_add_div p₁ q) + (modByMonic_add_div p₂ q)

lemma divByMonic_smul {q : R[X]} (hq : q.Monic) (c : R) (p : R[X]) :
    (c • p) /ₘ q = c • (p /ₘ q) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI := hR
    exact Subsingleton.elim _ _
  · rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul]
    refine (div_modByMonic_unique (C c * (p /ₘ q)) (C c * (p %ₘ q)) hq ⟨?_, ?_⟩).1
    · linear_combination (C c) * (modByMonic_add_div p q)
    · calc (C c * (p %ₘ q)).degree
          ≤ (C c).degree + (p %ₘ q).degree := degree_mul_le _ _
        _ ≤ 0 + (p %ₘ q).degree := by gcongr; exact degree_C_le
        _ = (p %ₘ q).degree := zero_add _
        _ < q.degree := degree_modByMonic_lt p hq

end Linearity

-- degree helper
lemma degree_divByMonic_lt_of_degree_lt {R : Type*} [Field R] {p q : R[X]} (hq : q.Monic) {n : ℕ}
    (hp : p.degree < (q.natDegree + n : ℕ)) : (p /ₘ q).degree < (n : WithBot ℕ) := by
  by_cases h0 : p /ₘ q = 0
  · rw [h0]; exact bot_lt_iff_ne_bot.mpr (by simp)
  · have hp0 : p ≠ 0 := by rintro rfl; simp at h0
    have hpq : q.natDegree ≤ p.natDegree := by
      by_contra h
      rw [not_le] at h
      exact h0 (divByMonic_eq_zero_iff hq |>.mpr (by
        rw [degree_eq_natDegree hp0, degree_eq_natDegree hq.ne_zero]
        exact_mod_cast h))
    have hpnd : p.natDegree < q.natDegree + n := by
      rw [degree_eq_natDegree hp0] at hp
      exact_mod_cast hp
    have : (p /ₘ q).natDegree = p.natDegree - q.natDegree := natDegree_divByMonic p hq
    rw [degree_eq_natDegree h0, this]
    exact_mod_cast (by omega : p.natDegree - q.natDegree < n)

-- ============ Part 2: divByMonic as a linear map ============

/-- `p ↦ p /ₘ h` as an `F`-linear map. -/
def divByMonicLinearMap (h : F[X]) (hh : h.Monic) : F[X] →ₗ[F] F[X] where
  toFun p := p /ₘ h
  map_add' := divByMonic_add hh
  map_smul' := divByMonic_smul hh

@[simp] lemma divByMonicLinearMap_apply (h : F[X]) (hh : h.Monic) (p : F[X]) :
    divByMonicLinearMap h hh p = p /ₘ h := rfl

/-- The map `a ↦ (f * (a %ₘ h)) /ₘ h` on `AdjoinRoot h`, landing in `F[X]`. -/
def Qraw (h f : F[X]) (hh : h.Monic) : AdjoinRoot h →ₗ[F] F[X] :=
  (divByMonicLinearMap h hh).comp ((Algebra.lmul F F[X] f).comp (AdjoinRoot.modByMonicHom hh))

lemma Qraw_apply (h f : F[X]) (hh : h.Monic) (a : AdjoinRoot h) :
    Qraw h f hh a = (f * (AdjoinRoot.modByMonicHom hh a)) /ₘ h := rfl

lemma Qraw_mem (h f : F[X]) (hh : h.Monic) (a : AdjoinRoot h) :
    Qraw h f hh a ∈ Polynomial.degreeLT F f.natDegree := by
  refine AdjoinRoot.induction_on (f := h) a (fun g => ?_)
  rw [Polynomial.mem_degreeLT, Qraw_apply, AdjoinRoot.modByMonicHom_mk]
  have hpdeg : (g %ₘ h).degree < (h.natDegree : WithBot ℕ) := by
    rw [← degree_eq_natDegree hh.ne_zero]; exact degree_modByMonic_lt g hh
  have hfp : (f * (g %ₘ h)).degree < (h.natDegree + f.natDegree : ℕ) := by
    rcases eq_or_ne (g %ₘ h) 0 with hgp | hgp
    · rw [hgp, mul_zero]; exact bot_lt_iff_ne_bot.mpr (by simp)
    rcases eq_or_ne f 0 with hf0 | hf0
    · rw [hf0, zero_mul]; exact bot_lt_iff_ne_bot.mpr (by simp)
    have hnd : (g %ₘ h).natDegree < h.natDegree := by
      rw [degree_eq_natDegree hgp] at hpdeg; exact_mod_cast hpdeg
    have : (f * (g %ₘ h)).degree = ((f.natDegree + (g %ₘ h).natDegree : ℕ) : WithBot ℕ) := by
      rw [degree_eq_natDegree (mul_ne_zero hf0 hgp), natDegree_mul hf0 hgp, Nat.cast_add]
    rw [this]
    exact_mod_cast (by omega : f.natDegree + (g %ₘ h).natDegree < h.natDegree + f.natDegree)
  exact degree_divByMonic_lt_of_degree_lt hh hfp

/-- The map `a ↦ (f * (a %ₘ h)) /ₘ h`, as a linear map into `F[X]_{natDegree f}`. -/
def Qmap (h f : F[X]) (hh : h.Monic) : AdjoinRoot h →ₗ[F] Polynomial.degreeLT F f.natDegree :=
  (Qraw h f hh).codRestrict _ (Qraw_mem h f hh)

@[simp] lemma Qmap_coe (h f : F[X]) (hh : h.Monic) (a : AdjoinRoot h) :
    ((Qmap h f hh a : Polynomial.degreeLT F f.natDegree) : F[X]) = Qraw h f hh a := rfl

section Main

/-- The map `(a, q) ↦ (mk h f * a, q + Q a)` on `AdjoinRoot h × F[X]_{deg f}`. -/
def PhiMap (h f : F[X]) (hh : h.Monic) :
    AdjoinRoot h × Polynomial.degreeLT F f.natDegree →ₗ[F]
      AdjoinRoot h × Polynomial.degreeLT F f.natDegree :=
  LinearMap.prod
    ((LinearMap.mulLeft F (AdjoinRoot.mk h f)).comp
      (LinearMap.fst F (AdjoinRoot h) (Polynomial.degreeLT F f.natDegree)))
    (LinearMap.coprod (Qmap h f hh)
      (LinearMap.id : Polynomial.degreeLT F f.natDegree →ₗ[F] Polynomial.degreeLT F f.natDegree))

lemma PhiMap_apply (h f : F[X]) (hh : h.Monic)
    (x : AdjoinRoot h × Polynomial.degreeLT F f.natDegree) :
    PhiMap h f hh x = (AdjoinRoot.mk h f * x.1, Qmap h f hh x.1 + x.2) := by
  rfl

/-- The map `(p, q) ↦ (mk h p, q)`. -/
def SigmaMap (h f : F[X]) (hh : h.Monic) :
    Polynomial.degreeLT F h.natDegree × Polynomial.degreeLT F f.natDegree →ₗ[F]
      AdjoinRoot h × Polynomial.degreeLT F f.natDegree :=
  LinearMap.prod
    (((AdjoinRoot.mkₐ h).toLinearMap).comp
      ((Polynomial.degreeLT F h.natDegree).subtype.comp
        (LinearMap.fst F (Polynomial.degreeLT F h.natDegree) (Polynomial.degreeLT F f.natDegree))))
    (LinearMap.snd F (Polynomial.degreeLT F h.natDegree) (Polynomial.degreeLT F f.natDegree))

lemma SigmaMap_apply (h f : F[X]) (_hh : h.Monic)
    (x : Polynomial.degreeLT F h.natDegree × Polynomial.degreeLT F f.natDegree) :
    SigmaMap h f _hh x = (AdjoinRoot.mk h x.1, x.2) := by
  rfl

/-- The map `(a, q) ↦ a %ₘ h + q * h`, into `F[X]_{deg h + deg f}`. -/
def Kraw (h f : F[X]) (hh : h.Monic) :
    AdjoinRoot h × Polynomial.degreeLT F f.natDegree →ₗ[F] F[X] :=
  (AdjoinRoot.modByMonicHom hh).comp
      (LinearMap.fst F (AdjoinRoot h) (Polynomial.degreeLT F f.natDegree)) +
    (LinearMap.mulLeft F h).comp
      ((Polynomial.degreeLT F f.natDegree).subtype.comp
        (LinearMap.snd F (AdjoinRoot h) (Polynomial.degreeLT F f.natDegree)))

lemma Kraw_apply (h f : F[X]) (hh : h.Monic)
    (x : AdjoinRoot h × Polynomial.degreeLT F f.natDegree) :
    Kraw h f hh x = AdjoinRoot.modByMonicHom hh x.1 + h * (x.2 : F[X]) := by
  rfl

lemma Kmem (h f : F[X]) (hh : h.Monic) (x : AdjoinRoot h × Polynomial.degreeLT F f.natDegree) :
    Kraw h f hh x ∈ Polynomial.degreeLT F (h.natDegree + f.natDegree) := by
  rw [Polynomial.mem_degreeLT, Kraw_apply]
  have hp : (AdjoinRoot.modByMonicHom hh x.1).degree < (h.natDegree : WithBot ℕ) := by
    refine AdjoinRoot.induction_on (f := h) x.1 (fun g => ?_)
    rw [AdjoinRoot.modByMonicHom_mk, ← degree_eq_natDegree hh.ne_zero]
    exact degree_modByMonic_lt g hh
  have hq : (x.2 : F[X]).degree < (f.natDegree : WithBot ℕ) := Polynomial.mem_degreeLT.mp x.2.2
  have hhq : (h * (x.2 : F[X])).degree < ((h.natDegree + f.natDegree : ℕ) : WithBot ℕ) := by
    rcases eq_or_ne (x.2 : F[X]) 0 with hq0 | hq0
    · rw [hq0, mul_zero]; exact bot_lt_iff_ne_bot.mpr (by simp)
    have hqnd : (x.2 : F[X]).natDegree < f.natDegree := by
      rw [degree_eq_natDegree hq0] at hq; exact_mod_cast hq
    have : (h * (x.2 : F[X])).degree = ((h.natDegree + (x.2 : F[X]).natDegree : ℕ) : WithBot ℕ) := by
      rw [degree_eq_natDegree (mul_ne_zero hh.ne_zero hq0), natDegree_mul hh.ne_zero hq0,
        Nat.cast_add]
    rw [this]
    exact_mod_cast (by omega : h.natDegree + (x.2 : F[X]).natDegree < h.natDegree + f.natDegree)
  refine (degree_add_le _ _).trans_lt (max_lt ?_ hhq)
  exact hp.trans_le (by exact_mod_cast Nat.le_add_right _ _)

/-- The map `(a, q) ↦ a %ₘ h + q * h`, as a linear map into `F[X]_{deg h + deg f}`. -/
def Kmap (h f : F[X]) (hh : h.Monic) :
    AdjoinRoot h × Polynomial.degreeLT F f.natDegree →ₗ[F]
      Polynomial.degreeLT F (h.natDegree + f.natDegree) :=
  (Kraw h f hh).codRestrict _ (Kmem h f hh)

@[simp] lemma Kmap_coe (h f : F[X]) (hh : h.Monic)
    (x : AdjoinRoot h × Polynomial.degreeLT F f.natDegree) :
    ((Kmap h f hh x : Polynomial.degreeLT F (h.natDegree + f.natDegree)) : F[X]) =
      Kraw h f hh x := rfl

end Main

section Compose

lemma sylvesterMap_eq_comp (h f : F[X]) (hh : h.Monic) :
    (Polynomial.sylvesterMap h f le_rfl le_rfl :
        Polynomial.degreeLT F h.natDegree × Polynomial.degreeLT F f.natDegree →ₗ[F]
          Polynomial.degreeLT F (h.natDegree + f.natDegree))
      = (Kmap h f hh).comp ((PhiMap h f hh).comp (SigmaMap h f hh)) := by
  apply LinearMap.ext
  intro x
  obtain ⟨p, q⟩ := x
  apply Subtype.ext
  simp only [LinearMap.comp_apply]
  rw [PhiMap_apply, SigmaMap_apply, Kmap_coe, Kraw_apply]
  rw [← map_mul]
  rw [AdjoinRoot.modByMonicHom_mk]
  have hp : (p : F[X]) %ₘ h = p := by
    rw [modByMonic_eq_self_iff hh, degree_eq_natDegree hh.ne_zero]
    exact Polynomial.mem_degreeLT.mp p.2
  have hQ : ((Qmap h f hh ((AdjoinRoot.mk h) p) : Polynomial.degreeLT F f.natDegree) : F[X])
      = (f * (p : F[X])) /ₘ h := by
    rw [Qmap_coe, Qraw_apply, AdjoinRoot.modByMonicHom_mk, hp]
  rw [show (Qmap h f hh ((AdjoinRoot.mk h) p) + q : Polynomial.degreeLT F f.natDegree)
        = (Qmap h f hh ((AdjoinRoot.mk h) p)) + q from rfl]
  rw [Submodule.coe_add, hQ]
  simp only [Polynomial.sylvesterMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [mul_add, ← add_assoc, modByMonic_add_div (f * (p : F[X])) h]
  ring

end Compose

section Det

/-- The power basis `1, root h, ..., root h^{d-1}` of `AdjoinRoot h`. -/
def baseA (h : F[X]) (hh : h.Monic) : Basis (Fin h.natDegree) F (AdjoinRoot h) :=
  AdjoinRoot.powerBasisAux' hh

/-- The basis `((1,0),...,(root^{d-1},0),(0,1),...,(0,X^{e-1}))` of `AdjoinRoot h × F[X]_e`. -/
def baseT (h f : F[X]) (hh : h.Monic) :
    Basis (Fin (h.natDegree + f.natDegree)) F
      (AdjoinRoot h × Polynomial.degreeLT F f.natDegree) :=
  ((AdjoinRoot.powerBasisAux' hh).prod (Polynomial.degreeLT.basis F f.natDegree)).reindex
    finSumFinEquiv

/-- The basis `((1,0),...,(X^{d-1},0),(0,1),...,(0,X^{e-1}))` of `F[X]_d × F[X]_e`. -/
def baseS (h f : F[X]) :
    Basis (Fin (h.natDegree + f.natDegree)) F
      (Polynomial.degreeLT F h.natDegree × Polynomial.degreeLT F f.natDegree) :=
  Polynomial.degreeLT.basisProd F h.natDegree f.natDegree

/-- The monomial basis of `F[X]_{d+e}`. -/
def baseU (h f : F[X]) :
    Basis (Fin (h.natDegree + f.natDegree)) F
      (Polynomial.degreeLT F (h.natDegree + f.natDegree)) :=
  Polynomial.degreeLT.basis F (h.natDegree + f.natDegree)

lemma baseA_apply (h : F[X]) (hh : h.Monic) (i : Fin h.natDegree) :
    baseA h hh i = (AdjoinRoot.root h) ^ (i : ℕ) := by
  have h1 : baseA h hh i = (AdjoinRoot.powerBasis' hh).basis i := rfl
  rw [h1]
  have := PowerBasis.basis_eq_pow (AdjoinRoot.powerBasis' hh) i
  rw [AdjoinRoot.powerBasis'_gen] at this
  exact this

lemma baseT_castAdd (h f : F[X]) (hh : h.Monic) (i : Fin h.natDegree) :
    baseT h f hh (Fin.castAdd f.natDegree i) = (baseA h hh i, 0) := by
  rw [baseT, Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd, baseA]
  exact Prod.ext (Basis.prod_apply_inl_fst (AdjoinRoot.powerBasisAux' hh)
    (Polynomial.degreeLT.basis F f.natDegree) i)
    (Basis.prod_apply_inl_snd (AdjoinRoot.powerBasisAux' hh)
    (Polynomial.degreeLT.basis F f.natDegree) i)

lemma baseT_natAdd (h f : F[X]) (hh : h.Monic) (i : Fin f.natDegree) :
    baseT h f hh (Fin.natAdd h.natDegree i) = (0, Polynomial.degreeLT.basis F f.natDegree i) := by
  rw [baseT, Basis.reindex_apply, finSumFinEquiv_symm_apply_natAdd]
  exact Prod.ext (Basis.prod_apply_inr_fst (AdjoinRoot.powerBasisAux' hh)
    (Polynomial.degreeLT.basis F f.natDegree) i)
    (Basis.prod_apply_inr_snd (AdjoinRoot.powerBasisAux' hh)
    (Polynomial.degreeLT.basis F f.natDegree) i)

lemma baseS_castAdd (h f : F[X]) (i : Fin h.natDegree) :
    baseS h f (Fin.castAdd f.natDegree i) = (Polynomial.degreeLT.basis F h.natDegree i, 0) := by
  rw [baseS, Polynomial.degreeLT.basisProd, Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd]
  exact Prod.ext (Basis.prod_apply_inl_fst (Polynomial.degreeLT.basis F h.natDegree)
    (Polynomial.degreeLT.basis F f.natDegree) i)
    (Basis.prod_apply_inl_snd (Polynomial.degreeLT.basis F h.natDegree)
    (Polynomial.degreeLT.basis F f.natDegree) i)

lemma baseS_natAdd (h f : F[X]) (i : Fin f.natDegree) :
    baseS h f (Fin.natAdd h.natDegree i) = (0, Polynomial.degreeLT.basis F f.natDegree i) := by
  rw [baseS, Polynomial.degreeLT.basisProd, Basis.reindex_apply, finSumFinEquiv_symm_apply_natAdd]
  exact Prod.ext (Basis.prod_apply_inr_fst (Polynomial.degreeLT.basis F h.natDegree)
    (Polynomial.degreeLT.basis F f.natDegree) i)
    (Basis.prod_apply_inr_snd (Polynomial.degreeLT.basis F h.natDegree)
    (Polynomial.degreeLT.basis F f.natDegree) i)

lemma SigmaMap_baseS (h f : F[X]) (hh : h.Monic) (j : Fin (h.natDegree + f.natDegree)) :
    SigmaMap h f hh (baseS h f j) = baseT h f hh j := by
  revert j
  refine Fin.addCases ?_ ?_
  · intro j₁
    rw [baseS_castAdd, SigmaMap_apply, baseT_castAdd, baseA_apply,
      Polynomial.degreeLT.basis_val, map_pow, AdjoinRoot.mk_X]
  · intro j₂
    rw [baseS_natAdd, SigmaMap_apply, baseT_natAdd]
    simp

lemma toMatrix_SigmaMap (h f : F[X]) (hh : h.Monic) :
    LinearMap.toMatrix (baseS h f) (baseT h f hh) (SigmaMap h f hh) = 1 := by
  ext i j
  rw [LinearMap.toMatrix_apply, SigmaMap_baseS]
  simp only [Matrix.one_apply, Basis.repr_self, Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

lemma baseT_reindex (h f : F[X]) (hh : h.Monic) :
    baseT h f hh = ((AdjoinRoot.powerBasisAux' hh).prod
      (Polynomial.degreeLT.basis F f.natDegree)).reindex finSumFinEquiv := rfl

lemma Kmap_baseT_castAdd (h f : F[X]) (hh : h.Monic) (j : Fin h.natDegree) :
    ((Kmap h f hh (baseT h f hh (Fin.castAdd f.natDegree j)) :
        Polynomial.degreeLT F (h.natDegree + f.natDegree)) : F[X])
      = (X : F[X]) ^ (j : ℕ) := by
  rw [Kmap_coe, Kraw_apply, baseT_castAdd]
  have hroot : (AdjoinRoot.root h) ^ (j : ℕ) = AdjoinRoot.mk h ((X : F[X]) ^ (j : ℕ)) := by
    rw [map_pow, AdjoinRoot.mk_X]
  rw [baseA_apply, hroot, AdjoinRoot.modByMonicHom_mk]
  have hmod : (X : F[X]) ^ (j : ℕ) %ₘ h = (X : F[X]) ^ (j : ℕ) := by
    rw [modByMonic_eq_self_iff hh, degree_X_pow, degree_eq_natDegree hh.ne_zero]
    exact_mod_cast j.2
  rw [hmod]
  simp

lemma Kmap_baseT_natAdd (h f : F[X]) (hh : h.Monic) (j : Fin f.natDegree) :
    ((Kmap h f hh (baseT h f hh (Fin.natAdd h.natDegree j)) :
        Polynomial.degreeLT F (h.natDegree + f.natDegree)) : F[X])
      = (X : F[X]) ^ (j : ℕ) * h := by
  rw [Kmap_coe, Kraw_apply, baseT_natAdd]
  simp [mul_comm]

end Det

section Det2

lemma toMatrix_reindex_reindex {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    {M : Type*} [AddCommGroup M] [Module F M] (b b' : Basis ι F M) (e : ι ≃ ι') (T : M →ₗ[F] M) :
    LinearMap.toMatrix (b.reindex e) (b'.reindex e) T = (LinearMap.toMatrix b b' T).reindex e e := by
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    LinearMap.toMatrix_apply, Basis.repr_reindex, Basis.reindex_apply,
    Finsupp.equivMapDomain_apply]

lemma toMatrix_PhiMap_prod (h f : F[X]) (hh : h.Monic) :
    LinearMap.toMatrix ((AdjoinRoot.powerBasisAux' hh).prod (Polynomial.degreeLT.basis F f.natDegree))
      ((AdjoinRoot.powerBasisAux' hh).prod (Polynomial.degreeLT.basis F f.natDegree)) (PhiMap h f hh)
      = Matrix.fromBlocks
          (LinearMap.toMatrix (baseA h hh) (baseA h hh) (LinearMap.mulLeft F (AdjoinRoot.mk h f)))
          0
          (Matrix.of fun i j => (Polynomial.degreeLT.basis F f.natDegree).repr
            (Qmap h f hh (baseA h hh j)) i)
          1 := by
  ext (i | i) (j | j) <;>
    simp only [LinearMap.toMatrix_apply, PhiMap_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, Matrix.one_apply, Matrix.of_apply, Basis.prod_repr_inl, Basis.prod_repr_inr,
      Basis.prod_apply_inl_fst, Basis.prod_apply_inl_snd, Basis.prod_apply_inr_fst,
      Basis.prod_apply_inr_snd, baseA, map_zero, zero_add, add_zero, mul_zero,
      LinearMap.mulLeft_apply, Pi.zero_apply]
  all_goals (first | rfl | (rw [Basis.repr_self, Finsupp.single_apply]; exact if_congr eq_comm rfl rfl))

lemma det_toMatrix_PhiMap (h f : F[X]) (hh : h.Monic) :
    (LinearMap.toMatrix (baseT h f hh) (baseT h f hh) (PhiMap h f hh)).det
      = (LinearMap.toMatrix (baseA h hh) (baseA h hh)
          (LinearMap.mulLeft F (AdjoinRoot.mk h f))).det := by
  have h1 : LinearMap.toMatrix (baseT h f hh) (baseT h f hh) (PhiMap h f hh)
      = (LinearMap.toMatrix ((AdjoinRoot.powerBasisAux' hh).prod
            (Polynomial.degreeLT.basis F f.natDegree))
          ((AdjoinRoot.powerBasisAux' hh).prod
            (Polynomial.degreeLT.basis F f.natDegree)) (PhiMap h f hh)).reindex
          finSumFinEquiv finSumFinEquiv := by
    rw [baseT, toMatrix_reindex_reindex]
  rw [h1, Matrix.det_reindex_self, toMatrix_PhiMap_prod, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_one, mul_one]

lemma det_toMatrix_mulLeft (h f : F[X]) (hh : h.Monic) :
    (LinearMap.toMatrix (baseA h hh) (baseA h hh) (LinearMap.mulLeft F (AdjoinRoot.mk h f))).det
      = Algebra.norm F (AdjoinRoot.mk h f) := by
  rw [LinearMap.det_toMatrix, Algebra.norm_apply]
  rfl

end Det2

section Det3

lemma coeff_X_pow_apply (n m : ℕ) : ((X : F[X]) ^ n).coeff m = if m = n then 1 else 0 := by
  rw [coeff_X_pow]

lemma toMatrix_Kmap_upper (h f : F[X]) (hh : h.Monic) :
    (LinearMap.toMatrix (baseT h f hh) (baseU h f) (Kmap h f hh)).IsUpperTriangular := by
  intro i j hij
  revert i
  refine Fin.addCases ?_ ?_ j
  · intro j₁ i hij
    rw [LinearMap.toMatrix_apply, baseU, Polynomial.degreeLT.basis_repr, Kmap_baseT_castAdd,
      coeff_X_pow_apply]
    rw [if_neg]
    have : (j₁ : ℕ) < (i : ℕ) := hij
    exact ne_of_gt this
  · intro j₂ i hij
    rw [LinearMap.toMatrix_apply, baseU, Polynomial.degreeLT.basis_repr, Kmap_baseT_natAdd]
    have hdeg : (X ^ (j₂ : ℕ) * h).natDegree = (j₂ : ℕ) + h.natDegree := by
      rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hh.ne_zero, natDegree_X_pow]
    apply coeff_eq_zero_of_natDegree_lt
    have h2 : h.natDegree + (j₂ : ℕ) < (i : ℕ) := hij
    rw [hdeg]
    omega

lemma toMatrix_Kmap_diag (h f : F[X]) (hh : h.Monic) (j : Fin (h.natDegree + f.natDegree)) :
    LinearMap.toMatrix (baseT h f hh) (baseU h f) (Kmap h f hh) j j = 1 := by
  revert j
  refine Fin.addCases ?_ ?_
  · intro j₁
    rw [LinearMap.toMatrix_apply, baseU, Polynomial.degreeLT.basis_repr, Kmap_baseT_castAdd,
      coeff_X_pow_apply]
    rw [if_pos]
    rfl
  · intro j₂
    rw [LinearMap.toMatrix_apply, baseU, Polynomial.degreeLT.basis_repr, Kmap_baseT_natAdd]
    have hdeg : (X ^ (j₂ : ℕ) * h).natDegree = (j₂ : ℕ) + h.natDegree := by
      rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hh.ne_zero, natDegree_X_pow]
    rw [show ((Fin.natAdd h.natDegree j₂ : Fin (h.natDegree + f.natDegree)) : ℕ)
        = (X ^ (j₂ : ℕ) * h).natDegree from by rw [hdeg, Fin.val_natAdd]; omega]
    rw [coeff_natDegree, leadingCoeff_mul, leadingCoeff_X_pow, hh.leadingCoeff, one_mul]

lemma det_toMatrix_Kmap (h f : F[X]) (hh : h.Monic) :
    (LinearMap.toMatrix (baseT h f hh) (baseU h f) (Kmap h f hh)).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (toMatrix_Kmap_upper h f hh)]
  rw [Finset.prod_eq_one]
  intro j _
  exact toMatrix_Kmap_diag h f hh j

end Det3

section Final

/-- The resultant of a monic polynomial `h` with `f` equals the norm of the class of `f` in
`F[X]/(h) ≅ AdjoinRoot h`.  Indeed both are `∏_{h(α) = 0} f(α)`. -/
theorem resultant_eq_norm_adjoinRoot {F : Type*} [Field F] (h : Polynomial F) (hh : h.Monic)
    (f : Polynomial F) :
    Polynomial.resultant h f = Algebra.norm F (AdjoinRoot.mk h f) := by
  have hS : Polynomial.resultant h f
      = (LinearMap.toMatrix (baseS h f) (baseU h f)
          (Polynomial.sylvesterMap h f le_rfl le_rfl)).det := by
    rw [show Polynomial.resultant h f
        = (Polynomial.sylvester h f h.natDegree f.natDegree).det from rfl]
    congr 1
    exact (Polynomial.toMatrix_sylvesterMap' h f le_rfl le_rfl).symm
  rw [hS, sylvesterMap_eq_comp h f hh]
  rw [LinearMap.toMatrix_comp (baseS h f) (baseT h f hh) (baseU h f) (Kmap h f hh)
        ((PhiMap h f hh).comp (SigmaMap h f hh)),
      LinearMap.toMatrix_comp (baseS h f) (baseT h f hh) (baseT h f hh) (PhiMap h f hh)
        (SigmaMap h f hh)]
  rw [Matrix.det_mul, Matrix.det_mul, det_toMatrix_Kmap, toMatrix_SigmaMap, Matrix.det_one,
    det_toMatrix_PhiMap, det_toMatrix_mulLeft]
  ring

end Final


end

end Commons.Algebra.Polynomial