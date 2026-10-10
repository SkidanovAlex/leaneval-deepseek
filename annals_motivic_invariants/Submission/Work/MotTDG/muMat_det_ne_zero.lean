import Mathlib
import Submission.Work.MotTDG.Defs
import Submission.Work.MotTDG.Ring
import Submission.Work.MotTDG.tenMon_linearIndependent
import Submission.Work.MotTDG.rhoVW_eq_zero

set_option linter.unusedVariables false -- v435-speed

namespace Work.MotTDG

open WeierstrassCurve WeierstrassCurve.Affine

/-!
**TDG-e**: the multiplier matrix `μ` of the Veronese--Weierstrass reduction is invertible.

For a Klein datum `D` with `ab ≠ 0`, whose Klein coordinates satisfy the five Pfaffian equations
(`hkl`) and whose Klein matrix is invertible with witness `e` (`hsp`, the `spans` condition), the
matrix `Work.MotTDG.muMat D L` — the matrix of coefficients with which the five
Veronese--Weierstrass quadrics `vwQuad` enter the identity `p_k (C v) = ∑_j μ_{k j} vwQuad_j (v)`
(node TDG-c plus TDG-d) — has nonzero determinant over every extension field `L ⊇ 𝕜`.

PROOF ROUTE.  Write `E = D.E.baseChange L`, `κ i = Work.MotV.kleinCoord D L i`, `bas = basE E`,
`c = cL D L`, `a = algebraMap 𝕜 L D.a`, `b = algebraMap 𝕜 L D.b`, `a₁ … a₆ = E.a₁ … E.a₆`, and
`μ = muMat D L`.  Let `e : Fin 5 → Fin 5 → 𝕜` be a witness of `hsp` and `eL = eL D L e`.

* Step 1.  `bas` is linearly independent over `L`: `basE E = tenMon E ∘ Fin.castLE (by norm_num)`,
  so this is `Work.MotTDG.tenMon_linearIndependent` (node **TDG-a**, import it) restricted along
  the injective map `Fin.castLE (by norm_num : 5 ≤ 10)` (use `Fintype.linearIndependent_iff` and
  the `@[simp]` results `basE_zero … basE_four`, `tenMon_zero … tenMon_four`).
* Step 2.  `eL * cL D L = 1`: expand `basE E m = ∑ i, algebraMap L _ (eL m i) * κ i`
  (`Work.MotTDG.basE_eq_eL_kleinCoord`) by `Work.MotTDG.kleinCoord_eq_cL`, collect the coefficient
  of `basE E l`, and use Step 1 to conclude `∑ i, eL m i * cL i l = δ_{ml}`.
* Step 3.  Hence `cL D L * eL = 1` as well (`Matrix.mul_eq_one_comm`, or `Matrix.det_ne_zero` plus
  `Matrix.inv`), so `κ` is linearly independent too and each `κ i ≠ 0`.
* Step 4.  Suppose `(muMat D L).det = 0`.  Then the rows of `μ` are linearly dependent over `L`:
  there is `λ : Fin 5 → L` with `λ ≠ 0` and `∑ k, λ k * μ k j = 0` for every `j`
  (`Matrix.exists_vecMul_eq_zero_iff` applied to the transpose, or `Matrix.det_eq_zero_iff`).
* Step 5.  Deduce `∑ k, λ k * Work.MotK.kleinP a b (fun i => ∑ m, c i m * v m) k = 0` for *every*
  `v : Fin 5 → L`, by expanding with `Work.MotTDG.kleinP_mulVec_expand` (node **TDG-b**) and
  reducing with `Work.MotTDG.quad_reduce` (node **TDG-c**): the `vwQuad` coefficients are
  `∑ k, λ k * μ k j = 0` by Step 4 and the `goodMon` coefficients are
  `∑ k, λ k * rhoVW … (colP …) (colB …) t = 0` because every summand vanishes by
  `Work.MotTDG.rhoVW_eq_zero` (**TDG-d**, import it).
* Step 6.  For each `m : Fin 5` take the test vector `v := fun p => eL p (2 * m)`.  By Step 3
  (`cL * eL = 1`) one gets `(fun i => ∑ p, c i p * v p) = Pi.single (2 * m) 1`, i.e. the vector
  `e_{2m}`, and `Work.MotK.kleinP a b (Pi.single i 1) k = -(a * b)` when `i = 2 * k` and `0`
  otherwise (read off the five components `kleinP0 … kleinP4` of `Work.MotK.kleinP`; here
  `i ↦ 2 * i` is injective on `Fin 5`, so `2 * m = 2 * k ↔ m = k`).
* Step 7.  Step 5 at this `v` gives `λ m * (-(a * b)) = 0`, hence `λ m = 0` for every `m` by
  `hab`, contradicting `λ ≠ 0`.

The result is `Work.MotTDG.muMat_det_ne_zero`; node TDG-M consumes it.
-/

/-- The Klein basis `1, x, y, x², xy` is `L`-linearly independent: it is the restriction of the
ten monomials of node TDG-a (`Work.MotTDG.tenMon_linearIndependent`) along the injective map
`Fin.castLE (by norm_num : 5 ≤ 10)`. -/
theorem muBasE_linearIndependent {L : Type} [Field L] (E : WeierstrassCurve L) :
    LinearIndependent L (basE E) := by
  have h : (fun m : Fin 5 => tenMon E (Fin.castLE (by norm_num : 5 ≤ 10) m)) = basE E := by
    funext m
    fin_cases m <;> simp [tenMon, goodMon, basE]
  rw [← h]
  exact (tenMon_linearIndependent E).comp _
    (Fin.castLE_injective (by norm_num : 5 ≤ 10))

/-- **The `spans` witness matrix is a left inverse of the Klein matrix** (over `L`).  Writing
`κ = cL ·ᵥ bas` (`Work.MotTDG.kleinCoord_eq_cL`) and `bas = eL ·ᵥ κ`
(`Work.MotTDG.basE_eq_eL_kleinCoord`), the composite `eL * cL` acts on the `L`-independent family
`basE` as the identity, hence is the identity. -/
theorem mu_eL_mul_cL {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜)
    (L : Type) [Field L] [Algebra 𝕜 L] (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L (FunctionField (D.E.baseChange L)) (algebraMap 𝕜 L (e m i))
        * Work.MotV.kleinCoord D L i) :
    eL D L e * cL D L = 1 := by
  have hbas : LinearIndependent L (basE (D.E.baseChange L)) :=
    muBasE_linearIndependent (D.E.baseChange L)
  have hklein : ∀ i, Work.MotV.kleinCoord D L i
      = ∑ l, (cL D L i l) • basE (D.E.baseChange L) l := by
    intro i
    rw [kleinCoord_eq_cL]
    exact Finset.sum_congr rfl fun l _ => (Algebra.smul_def _ _).symm
  have hbasE : ∀ m, basE (D.E.baseChange L) m
      = ∑ i, (eL D L e m i) • Work.MotV.kleinCoord D L i := by
    intro m
    rw [basE_eq_eL_kleinCoord D L e he m]
    exact Finset.sum_congr rfl fun i _ => (Algebra.smul_def _ _).symm
  have hsum : ∀ m, (∑ l, (∑ i, eL D L e m i * cL D L i l) • basE (D.E.baseChange L) l)
      = basE (D.E.baseChange L) m := by
    intro m
    rw [hbasE m]
    symm
    calc ∑ i, (eL D L e m i) • Work.MotV.kleinCoord D L i
        = ∑ i, (eL D L e m i) • (∑ l, (cL D L i l) • basE (D.E.baseChange L) l) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hklein i]
      _ = ∑ i, ∑ l, (eL D L e m i * cL D L i l) • basE (D.E.baseChange L) l := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
      _ = ∑ l, (∑ i, eL D L e m i * cL D L i l) • basE (D.E.baseChange L) l := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun l _ => (Finset.sum_smul).symm
  ext m l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hsingle : (∑ l', (if l' = m then (1 : L) else 0) • basE (D.E.baseChange L) l')
      = basE (D.E.baseChange L) m := by
    rw [Finset.sum_eq_single m]
    · simp
    · intro l' _ hl'; simp [hl']
    · intro hm; exact absurd (Finset.mem_univ m) hm
  have hzero : (∑ l', ((∑ i, eL D L e m i * cL D L i l') - (if l' = m then (1 : L) else 0))
      • basE (D.E.baseChange L) l') = 0 := by
    simp only [sub_smul]
    rw [Finset.sum_sub_distrib, hsum m, hsingle, sub_self]
  have h0 := (Fintype.linearIndependent_iff.mp hbas)
    (fun l' => (∑ i, eL D L e m i * cL D L i l') - (if l' = m then (1 : L) else 0)) hzero l
  rw [sub_eq_zero] at h0
  rw [h0]
  by_cases hlm : l = m
  · simp [hlm]
  · simp [hlm, Ne.symm hlm]

/-- **The elementary computation of Step 6/7 of node TDG-e.**  For the standard basis vector
`e_{2m} = Pi.single (2 * m) 1` of `R^5` (the doubling `m ↦ 2m` being a bijection of `Fin 5`) the
Pfaffian `p_k` takes the value `-(a b)` exactly at `k = m` and vanishes otherwise, so
`∑_k λ_k p_k (e_{2m}) = -(a b) λ_m`. -/
theorem sum_kleinP_single {R : Type*} [CommRing R] (a b : R) (lam : Fin 5 → R) (m : Fin 5) :
    ∑ k, lam k * Work.MotK.kleinP a b (Pi.single ((2 : Fin 5) * m) 1) k = -(a * b) * lam m := by
  fin_cases m <;>
    simp [Work.MotK.kleinP, Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2,
      Work.MotK.kleinP3, Work.MotK.kleinP4, Fin.sum_univ_succ] <;> ring

theorem muMat_det_ne_zero {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜)
    (hab : D.a * D.b ≠ 0)
    (hkl : ∀ (L : Type) [Field L] [Algebra 𝕜 L] (k : Fin 5),
      Work.MotK.kleinP (algebraMap 𝕜 _ D.a) (algebraMap 𝕜 _ D.b) (Work.MotV.kleinCoord D L) k = 0)
    (hsp : ∃ e : Fin 5 → Fin 5 → 𝕜, ∀ (L : Type) [Field L] [Algebra 𝕜 L] (m : Fin 5),
      Work.MotV.kleinBas D L m =
        ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i)
    (L : Type) [Field L] [Algebra 𝕜 L] : (muMat D L).det ≠ 0 := by
  classical
  obtain ⟨e, he⟩ := hsp
  -- Step 2/3: the `spans` witness matrix is the two-sided inverse of the Klein matrix over `L`.
  have hce : cL D L * eL D L e = 1 :=
    mul_eq_one_comm.mp (mu_eL_mul_cL D L e (fun m => he L m))
  -- `a b ≠ 0` after base change.
  have habL : algebraMap 𝕜 L D.a * algebraMap 𝕜 L D.b ≠ 0 := by
    intro h
    refine hab ((algebraMap 𝕜 L).injective ?_)
    rw [map_mul, h, map_zero]
  -- Step 4: a nontrivial linear dependence among the rows of `μ`.
  intro hdet
  rw [← Matrix.exists_vecMul_eq_zero_iff] at hdet
  obtain ⟨lam, hlam_ne, hlam⟩ := hdet
  have hlam_j : ∀ j : Fin 5, ∑ k, lam k * muMat D L k j = 0 := by
    intro j
    have := congrFun hlam j
    simpa [Matrix.vecMul, Matrix.vecMul_apply, Matrix.col, dotProduct] using this
  -- Step 5: the reduced identity `p_k (C v) = ∑_j μ_{k j} vwQuad_j (v)` and its `λ`-combination.
  have key : ∀ (v : Fin 5 → L),
      ∑ k, lam k * Work.MotK.kleinP (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b)
        (fun i => ∑ m, cL D L i m * v m) k = 0 := by
    intro v
    have hp : ∀ k : Fin 5,
        Work.MotK.kleinP (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b)
          (fun i => ∑ m, cL D L i m * v m) k
        = ∑ j, muMat D L k j * vwQuad (D.E.baseChange L).a₁ (D.E.baseChange L).a₂
            (D.E.baseChange L).a₃ (D.E.baseChange L).a₄ (D.E.baseChange L).a₆ v j := by
      intro k
      have h1 : Work.MotK.kleinP (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b)
            (fun i => ∑ m, cL D L i m * v m) k
          = quadForm (colP (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) (cL D L) k)
              (colB (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) (cL D L) k) v :=
        kleinP_mulVec_expand _ _ _ _ _
      have h2 := quad_reduce (D.E.baseChange L).a₁ (D.E.baseChange L).a₂ (D.E.baseChange L).a₃
        (D.E.baseChange L).a₄ (D.E.baseChange L).a₆
        (colP (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) (cL D L) k)
        (colB (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) (cL D L) k) v
      rw [h1, h2]
      have hz : (∑ t, rhoVW (D.E.baseChange L).a₁ (D.E.baseChange L).a₂ (D.E.baseChange L).a₃
          (D.E.baseChange L).a₄ (D.E.baseChange L).a₆
          (colP (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) (cL D L) k)
          (colB (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) (cL D L) k) t * goodMon v t) = 0 :=
        Finset.sum_eq_zero fun t _ => by rw [rhoVW_eq_zero D hkl L k t, zero_mul]
      rw [hz, add_zero]
      rfl
    calc ∑ k, lam k * Work.MotK.kleinP (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b)
            (fun i => ∑ m, cL D L i m * v m) k
        = ∑ k, lam k * (∑ j, muMat D L k j *
            vwQuad (D.E.baseChange L).a₁ (D.E.baseChange L).a₂ (D.E.baseChange L).a₃
              (D.E.baseChange L).a₄ (D.E.baseChange L).a₆ v j) :=
          Finset.sum_congr rfl fun k _ => by rw [hp k]
      _ = ∑ j, (∑ k, lam k * muMat D L k j) *
            vwQuad (D.E.baseChange L).a₁ (D.E.baseChange L).a₂ (D.E.baseChange L).a₃
              (D.E.baseChange L).a₄ (D.E.baseChange L).a₆ v j := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          have hcast : (∑ k, lam k * (muMat D L k j *
              vwQuad (D.E.baseChange L).a₁ (D.E.baseChange L).a₂ (D.E.baseChange L).a₃
                (D.E.baseChange L).a₄ (D.E.baseChange L).a₆ v j))
              = (∑ k, lam k * muMat D L k j) *
                vwQuad (D.E.baseChange L).a₁ (D.E.baseChange L).a₂ (D.E.baseChange L).a₃
                  (D.E.baseChange L).a₄ (D.E.baseChange L).a₆ v j := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun k _ => by ring
          rw [hcast]
      _ = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          rw [hlam_j j, zero_mul]
  -- Steps 6/7: evaluate at `v = eL · e_{2m}`, where `C v = e_{2m}`.
  have hzero_all : ∀ m : Fin 5, lam m = 0 := by
    intro m
    have hv := key (fun p => eL D L e p ((2 : Fin 5) * m))
    have hCv : (fun i => ∑ p, cL D L i p * eL D L e p ((2 : Fin 5) * m))
        = Pi.single ((2 : Fin 5) * m) 1 := by
      funext i
      rw [← Matrix.mul_apply, hce, Matrix.one_apply, Pi.single_apply]
    rw [hCv, sum_kleinP_single] at hv
    rcases mul_eq_zero.mp hv with h | h
    · exact absurd h (neg_ne_zero.mpr habL)
    · exact h
  exact hlam_ne (funext hzero_all)

end Work.MotTDG
