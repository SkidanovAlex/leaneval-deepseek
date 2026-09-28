import Mathlib
import Submission.Work.Cohomology.CapProduct
import Submission.Work.Cohomology.cupLeibniz

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section
variable {R : Type} [CommRing R] {X : SSet}

/-- The linear map underlying the cast of chains along an equality of degrees. -/
def castChainLM {a b : ℕ} (h : a = b) :
    (↑((X.chainComplex (ModuleCat.of R R)).X a)) →ₗ[R]
      (↑((X.chainComplex (ModuleCat.of R R)).X b)) :=
  (LinearEquiv.cast (M := fun k => ↑((X.chainComplex (ModuleCat.of R R)).X k)) h).toLinearMap

lemma castChainLM_apply {a b : ℕ} (h : a = b)
    (x : ↑((X.chainComplex (ModuleCat.of R R)).X a)) :
    castChainLM (X := X) h x = h ▸ x := by
  cases h
  simp [castChainLM]

/-- Linear maps on chains which agree on all generators are equal. -/
lemma chainLinear_ext {N m : ℕ}
    {f g : (↑((X.chainComplex (ModuleCat.of R R)).X N)) →ₗ[R]
      (↑((X.chainComplex (ModuleCat.of R R)).X m))}
    (h : ∀ σ : X _⦋N⦌, f ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)
      = g ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)) : f = g := by
  have key : (ModuleCat.ofHom f : (X.chainComplex (ModuleCat.of R R)).X N
        ⟶ (X.chainComplex (ModuleCat.of R R)).X m)
      = (ModuleCat.ofHom g : (X.chainComplex (ModuleCat.of R R)).X N
        ⟶ (X.chainComplex (ModuleCat.of R R)).X m) := by
    apply SSet.chainComplex_hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    have hc : (X.ιChainComplex (R := ModuleCat.of R R) σ).hom r
        = r • (X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1 := by
      simpa using LinearMap.map_smul (X.ιChainComplex (R := ModuleCat.of R R) σ).hom r (1:R)
    have h' : f ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)
        = g ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1) := h σ
    calc f ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom r)
        = f (r • (X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1) := by rw [hc]
      _ = r • f ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1) := by rw [map_smul]
      _ = r • g ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1) := by rw [h']
      _ = g (r • (X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1) := by rw [map_smul]
      _ = g ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom r) := by rw [hc]
  simpa only [ModuleCat.hom_ofHom] using congrArg ModuleCat.Hom.hom key

/-- The differential of the chain complex, on a generator. -/
lemma capd_d_gen (n' : ℕ) (σ : X _⦋n'+1⦌) :
    ((X.chainComplex (ModuleCat.of R R)).d (n'+1) n').hom
      ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)
    = ∑ k : Fin (n'+2), ((-1:R)^(k:ℕ)) •
        ((X.ιChainComplex (R := ModuleCat.of R R) (X.δ k σ)).hom 1) := by
  have h := congrArg (fun (g : ModuleCat.of R R ⟶ (X.chainComplex (ModuleCat.of R R)).X n') => g.hom 1)
      (SSet.ιChainComplex_d (X := X) (R := ModuleCat.of R R) σ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h]
  rw [ModuleCat.hom_sum]
  simp only [LinearMap.sum_apply, ModuleCat.hom_smul, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Int.cast_smul_eq_zsmul R, Int.cast_pow, Int.cast_neg, Int.cast_one]

lemma capd_neg_one_pow_mul_pow_add (n k : ℕ) : ((-1:R)^n) * ((-1:R)^(n+k)) = (-1:R)^k := by
  rw [← pow_add, show n + (n + k) = n + n + k by ring, pow_add, pow_add,
    neg_one_pow_mul_self, one_mul]

lemma capd_neg_one_pow_succ (n : ℕ) : (-1:R)^(n+1) = -((-1:R)^n) := by
  rw [pow_succ]; ring

lemma cap_d_gen (R : Type) [CommRing R] (X : SSet) {n m : ℕ} (α : Cochain R X n)
    (σ : X _⦋n + (m + 1)⦌) :
    ((X.chainComplex (ModuleCat.of R R)).d (m + 1) m).hom
        (cap R X α (m + 1) ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1))
      = (-1 : R) ^ n • (cap R X α m
            (((X.chainComplex (ModuleCat.of R R)).d (n + (m + 1)) (n + m)).hom
              ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1))
          - cap R X (cochainDiff R X α) m
            ((capIdx n m) ▸ ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1))) := by
  let Fr : X _⦋n⦌ := frontFace X n (n + (m + 1)) (by omega) σ
  let τ : X _⦋m + 1⦌ := backFace X n (m + 1) σ
  let F' : X _⦋n + 1⦌ := frontFace X (n + 1) (n + m + 1) (by omega) σ
  let Φ : ⦋(n + 1) + m⦌ ⟶ ⦋n + (m + 1)⦌ := eqToHom (congrArg SimplexCategory.mk (capIdx n m)).symm
  let σ' : X _⦋(n + 1) + m⦌ := X.map Φ.op σ
  let B' : X _⦋m⦌ := backFace X (n + 1) m (X.map (shiftHom n m).op σ)
  let G : R := genEval R X α Fr
  let U : ↑((X.chainComplex (ModuleCat.of R R)).X m) :=
    (X.ιChainComplex (R := ModuleCat.of R R) (X.δ (0 : Fin (m + 2)) τ)).hom 1
  let dface : ℕ → X _⦋n + m⦌ := fun k => if h : k < n + m + 2 then X.δ ⟨k, h⟩ σ else X.δ 0 σ
  let dtau : ℕ → X _⦋m⦌ := fun i => if h : i < m + 2 then X.δ ⟨i, h⟩ τ else X.δ 0 τ
  let dF : ℕ → X _⦋n⦌ := fun i => if h : i < n + 2 then X.δ ⟨i, h⟩ F' else X.δ 0 F'
  let Gs : ℕ → ↑((X.chainComplex (ModuleCat.of R R)).X m) :=
    fun k => (-1 : R) ^ k • (cap R X α m ((X.ιChainComplex (R := ModuleCat.of R R) (dface k)).hom 1))
  let Ps : R := ∑ k ∈ Finset.range (n + 1), (-1 : R) ^ k * genEval R X α (dF k)
  let E0 : R := ∑ i ∈ Finset.range (n + 2), (-1 : R) ^ i * genEval R X α (dF i)
  let W : ↑((X.chainComplex (ModuleCat.of R R)).X m) :=
    ∑ k' ∈ Finset.range (m + 1), (-1 : R) ^ (n + 1 + k') •
      (X.ιChainComplex (R := ModuleCat.of R R) (dtau (k' + 1))).hom 1
  let Sτ : ↑((X.chainComplex (ModuleCat.of R R)).X m) :=
    ∑ i ∈ Finset.range (m + 2), (-1 : R) ^ i •
      (X.ιChainComplex (R := ModuleCat.of R R) (dtau i)).hom 1
  have hΦ : Φ = shiftHom n m := by
    refine ConcreteCategory.hom_ext Φ (shiftHom n m) (fun i => ?_)
    apply Fin.ext
    show ((ConcreteCategory.hom Φ) i).val = ((ConcreteCategory.hom (shiftHom n m)) i).val
    simp only [Φ]
    rw [coe_eqToHom_mk_symm (capIdx n m), shiftHom_val]
  have hσ' : σ' = X.map (shiftHom n m).op σ := by
    show X.map Φ.op σ = X.map (shiftHom n m).op σ
    exact congrArg (fun ψ => X.map ψ.op σ) hΦ
  have hfront' : frontFace X (n + 1) ((n + 1) + m) (by omega) σ' = F' := by
    rw [hσ', E7 n m (shiftHom n m) (shiftHom_val n m) σ]
  have hback' : backFace X (n + 1) m σ' = B' := by
    rw [hσ']
  have hBU : (X.ιChainComplex (R := ModuleCat.of R R) B').hom 1 = U := by
    simp only [U, B']
    rw [← E6 n m (0 : Fin (m + 2)) rfl (shiftHom n m) (shiftHom_val n m) σ]
  have hdσ : (((X.chainComplex (ModuleCat.of R R)).d (n + (m + 1)) (n + m)).hom
      ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1))
      = ∑ k : Fin (n + m + 2), (-1 : R) ^ (k : ℕ) •
          (X.ιChainComplex (R := ModuleCat.of R R) (X.δ k σ)).hom 1 :=
    capd_d_gen (n + m) σ
  have hAs : cap R X α m (((X.chainComplex (ModuleCat.of R R)).d (n + (m + 1)) (n + m)).hom
      ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1))
      = ∑ k ∈ Finset.range (n + m + 2), Gs k := by
    rw [hdσ, map_sum]
    simp only [map_smul]
    refine (Finset.sum_congr rfl ?_).trans (Fin.sum_univ_eq_sum_range Gs (n + m + 2))
    intro k _
    simp only [Gs, dface, dif_pos (by omega : (k:ℕ) < n + m + 2)]
  have hSτ : ((X.chainComplex (ModuleCat.of R R)).d (m + 1) m).hom
      ((X.ιChainComplex (R := ModuleCat.of R R) τ).hom 1) = Sτ := by
    rw [capd_d_gen m τ]
    simp only [Sτ]
    refine (Finset.sum_congr rfl ?_).trans (Fin.sum_univ_eq_sum_range
      (fun i => (-1:R)^i • (X.ιChainComplex (R := ModuleCat.of R R) (dtau i)).hom 1) (m + 2))
    intro i _
    simp only [dtau, dif_pos (by omega : (i:ℕ) < m + 2)]
  have hterm1 : ∀ k ∈ Finset.range (n + 1), Gs k = ((-1 : R) ^ k * genEval R X α (dF k)) • U := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hk2 : k < n + m + 2 := by omega
    have hkn : k ≤ n := by omega
    have hk3 : k < n + 2 := by omega
    simp only [Gs, dface, dif_pos hk2]
    rw [cap_apply]
    rw [E1 n m ⟨k, hk2⟩ hkn σ]
    rw [E2 n m ⟨k, hk2⟩ hkn (shiftHom n m) (shiftHom_val n m) σ]
    rw [hBU, ← smul_smul]
    simp only [dF, F', dif_pos hk3]
  have hterm2 : ∀ k' ∈ Finset.range (m + 1),
      Gs (n + 1 + k') = G • ((-1 : R) ^ (n + 1 + k') •
        (X.ιChainComplex (R := ModuleCat.of R R) (dtau (k' + 1))).hom 1) := by
    intro k' hk'
    rw [Finset.mem_range] at hk'
    have hk2 : n + 1 + k' < n + m + 2 := by omega
    have hge : n + 1 ≤ n + 1 + k' := by omega
    have hk3 : k' + 1 < m + 2 := by omega
    have hj : (k' + 1 : ℕ) = (n + 1 + k') - n := by omega
    simp only [Gs, dface, dif_pos hk2]
    rw [cap_apply]
    rw [E3 n m ⟨n + 1 + k', hk2⟩ hge σ]
    rw [E4 n m ⟨n + 1 + k', hk2⟩ hge ⟨k' + 1, hk3⟩ hj σ]
    rw [smul_comm]
    simp only [G, Fr, τ, dtau, dif_pos hk3]
  have hsum1 : (∑ k ∈ Finset.range (n + 1), Gs k) = Ps • U := by
    refine (Finset.sum_congr rfl hterm1).trans ?_
    simp only [Ps]
    rw [← Finset.sum_smul]
  have hsum2 : (∑ k' ∈ Finset.range (m + 1), Gs (n + 1 + k')) = G • W := by
    refine (Finset.sum_congr rfl hterm2).trans ?_
    simp only [W]
    rw [Finset.smul_sum]
  have hAs' : cap R X α m (((X.chainComplex (ModuleCat.of R R)).d (n + (m + 1)) (n + m)).hom
      ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)) = Ps • U + G • W := by
    rw [hAs]
    rw [show n + m + 2 = (n + 1) + (m + 1) by omega, Finset.sum_range_add]
    rw [hsum1, hsum2]
  have hgen : (capIdx n m) ▸ ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)
      = (X.ιChainComplex (R := ModuleCat.of R R) σ').hom 1 := by
    rw [generator_transport]
  have hBs' : cap R X (cochainDiff R X α) m ((capIdx n m) ▸
        ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)) = E0 • U := by
    rw [hgen, cap_apply]
    rw [hfront', genEval_cochainDiff, hback', hBU]
    simp only [E0]
    congr 1
    refine (Finset.sum_congr rfl ?_).trans (Fin.sum_univ_eq_sum_range
      (fun i => (-1:R)^i * genEval R X α (dF i)) (n + 2))
    intro i _
    simp only [dF, F', dif_pos (by omega : (i:ℕ) < n + 2)]
  have hgn : genEval R X α (dF (n + 1)) = G := by
    simp only [dF, dif_pos (by omega : n + 1 < n + 2), F']
    rw [E5 n m ⟨n + 1, by omega⟩ rfl σ]
  have hPE : Ps - E0 = (-1 : R) ^ n * G := by
    simp only [E0, Ps]
    rw [Finset.sum_range_succ (fun i => (-1 : R) ^ i * genEval R X α (dF i)) (n + 1)]
    rw [hgn, capd_neg_one_pow_succ]
    ring
  have hSW' : U + (-1 : R) ^ n • W = Sτ := by
    have hWn : (-1 : R) ^ n • W = ∑ k' ∈ Finset.range (m + 1),
        (-1 : R) ^ (k' + 1) • (X.ιChainComplex (R := ModuleCat.of R R) (dtau (k' + 1))).hom 1 := by
      simp only [W]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun k' _ => ?_)
      rw [smul_smul]
      rw [show (-1 : R) ^ n * (-1 : R) ^ (n + 1 + k') = (-1 : R) ^ (k' + 1) by
        rw [show n + 1 + k' = n + (1 + k') by omega, capd_neg_one_pow_mul_pow_add n (1 + k'),
          show 1 + k' = k' + 1 by omega]]
    rw [hWn]
    simp only [Sτ, U]
    rw [Finset.sum_range_succ' (fun i => (-1 : R) ^ i •
      (X.ιChainComplex (R := ModuleCat.of R R) (dtau i)).hom 1) (m + 1)]
    simp only [dtau, dif_pos (by omega : (0:ℕ) < m + 2), pow_zero, one_smul]
    rw [add_comm]
    rfl
  have hcap1 : cap R X α (m + 1) ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)
      = G • (X.ιChainComplex (R := ModuleCat.of R R) τ).hom 1 := by
    rw [cap_apply]
  have hL : ((X.chainComplex (ModuleCat.of R R)).d (m + 1) m).hom
      (cap R X α (m + 1) ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)) = G • Sτ := by
    rw [hcap1, map_smul, hSτ]
  have hR : (-1 : R) ^ n • (cap R X α m
          (((X.chainComplex (ModuleCat.of R R)).d (n + (m + 1)) (n + m)).hom
            ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1))
        - cap R X (cochainDiff R X α) m
          ((capIdx n m) ▸ ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1))) = G • Sτ := by
    rw [hAs', hBs']
    have hX : Ps • U + G • W - E0 • U = (Ps - E0) • U + G • W := by rw [sub_smul]; abel
    rw [hX, hPE, smul_add]
    have h1 : (-1 : R) ^ n • (((-1 : R) ^ n * G) • U) = G • U := by
      rw [smul_smul, ← mul_assoc, neg_one_pow_mul_self, one_mul]
    have h2 : (-1 : R) ^ n • (G • W) = G • ((-1 : R) ^ n • W) := by rw [smul_comm]
    rw [h1, h2, ← smul_add, ← hSW']
  rw [hL, hR]

theorem cap_d (R : Type) [CommRing R] (X : SSet) {n m : ℕ} (α : Work.Cohomology.Cochain R X n)
    (c : (X.chainComplex (ModuleCat.of R R)).X (n + (m + 1))) :
    ((X.chainComplex (ModuleCat.of R R)).d (m + 1) m).hom (Work.Cohomology.cap R X α (m + 1) c) =
      (-1 : R) ^ n • (Work.Cohomology.cap R X α m
          (((X.chainComplex (ModuleCat.of R R)).d (n + (m + 1)) (n + m)).hom c) -
        Work.Cohomology.cap R X (Work.Cohomology.cochainDiff R X α) m ((Work.Cohomology.capIdx n m) ▸ c)) := by
  let L : (↑((X.chainComplex (ModuleCat.of R R)).X (n + (m + 1)))) →ₗ[R]
      (↑((X.chainComplex (ModuleCat.of R R)).X m)) :=
    ((X.chainComplex (ModuleCat.of R R)).d (m + 1) m).hom.comp (cap R X α (m + 1))
  let Q : (↑((X.chainComplex (ModuleCat.of R R)).X (n + (m + 1)))) →ₗ[R]
      (↑((X.chainComplex (ModuleCat.of R R)).X m)) :=
    (-1 : R) ^ n • (((cap R X α m).comp
        (((X.chainComplex (ModuleCat.of R R)).d (n + (m + 1)) (n + m)).hom))
      - ((cap R X (cochainDiff R X α) m).comp (castChainLM (X := X) (capIdx n m))))
  have hLQ : L = Q := by
    apply chainLinear_ext
    intro σ
    show L ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)
      = Q ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)
    simp only [L, Q, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply]
    rw [castChainLM_apply]
    exact cap_d_gen R X α σ
  have h := congrArg (fun f => f c) hLQ
  simp only [L, Q, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply] at h
  rw [castChainLM_apply] at h
  exact h

end
end Work.Cohomology
