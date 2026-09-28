import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Sig2.gam_rank_det
import Submission.Work.HP.Sig2.nu_indep
import Submission.Work.HP.Sig2.VeroMon
import Submission.Work.HP.MDBasic.mem_Gam_iff
import Submission.Work.HP.lam_basic
import Submission.Work.HP.Vero.span_realify_latOrth_inf
import Submission.Work.HP.Vero.MulDefs
import Submission.Work.HP.Vero.MulAux
import Submission.Work.HP.Vero.MulMono
import Submission.Work.HP.Vero.intCastPi_mulVec
import Submission.Work.HP.Vero.eNorm_mulVec_unitMon
import Submission.Work.HP.Vero.lam_le_of_span
import Submission.Work.HP.Vero.LiftDefs
import Submission.Work.HP.Vero.LamGen
import Submission.Work.HP.Vero.mulVec_assoc
import Submission.Work.HP.Vero.mulVec_symm
import Submission.Work.HP.Sig2.lift_two_vectors

namespace Work.HP.Vero

open Work.HP.Vero.Aux

open Finset

/-! ## Auxiliary lemmas for the assembly -/

/-- `A ↦ mulVec a b d A B` is linear in its second argument. -/
def mulVecRgen' {n : ℕ} (a b d : ℕ) (A : Mon a n → ℝ) : (Mon b n → ℝ) →ₗ[ℝ] (Mon d n → ℝ) where
  toFun B := mulVec a b d A B
  map_add' B B' := mulVec_add_right A B B'
  map_smul' c B := mulVec_smul_right c A B

@[simp] lemma mulVecRgen'_apply {n : ℕ} (a b d : ℕ) (A : Mon a n → ℝ) (B : Mon b n → ℝ) :
    mulVecRgen' a b d A B = mulVec a b d A B := rfl

/-- `ℤ`-linear independence of integer vectors implies `ℝ`-linear independence of their images. -/
lemma linInd_toR {ι : Type*} [Fintype ι] {κ : Type*} {v : κ → (ι → ℤ)}
    (h : LinearIndependent ℤ v) : LinearIndependent ℝ (fun i => toR (v i)) := by
  have h' := (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ) (v := v)).mpr h
  have hfun : (fun i => toR (v i)) = (fun i => algebraMap ℤ ℝ ∘ v i) := by
    funext i j; rfl
  rwa [hfun]

/-- The unit monomials span everything. -/
lemma span_unitMon_eq_top (d n : ℕ) :
    Submodule.span ℝ (Set.range (fun P : Mon d n => unitMon (R := ℝ) P)) = ⊤ := by
  rw [eq_top_iff]
  intro F _
  rw [← sum_smul_unitMon (R := ℝ) F]
  exact Submodule.sum_mem _ (fun P _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨P, rfl⟩))

lemma intCastPi_unitMon {d n : ℕ} (P : Mon d n) :
    intCastPi (unitMon (R := ℤ) P) = unitMon (R := ℝ) P := by
  funext m
  by_cases h : m = P
  · subst h; simp [unitMon]
  · simp [unitMon, h]

lemma fun_unitMon_cast {d n : ℕ} (P : Mon d n) :
    (fun m => ((unitMon (R := ℤ) P m : ℤ) : ℝ)) = unitMon (R := ℝ) P := by
  funext m
  by_cases h : m = P
  · subst h; simp [unitMon]
  · simp [unitMon, h]

lemma veronese_toR (d n : ℕ) (x : Fin (n + 1) → ℤ) (m : Mon d n) :
    veronese d n (toR x) m = ((veronese d n x m : ℤ) : ℝ) := by
  simp only [veronese, toR]
  push_cast
  rfl

lemma formEvalR_intCastToR (d n : ℕ) (A : Mon d n → ℤ) (x : Fin (n + 1) → ℤ) :
    formEvalR d n (intCastPi A) (toR x) = ((formEval d n A x : ℤ) : ℝ) := by
  rw [formEvalR, formEval]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [veronese_toR]
  rfl

lemma evalinR_eq_linComb (d n : ℕ) (z : Fin (n + 1) → ℤ) :
    evalLinR d n (toR z)
      = Fintype.linearCombination ℝ (fun i => ((veronese d n z i : ℤ) : ℝ)) := by
  apply LinearMap.ext
  intro A
  rw [evalLinR_apply, formEvalR, Fintype.linearCombination_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [smul_eq_mul, veronese_toR]

/-- The two-vector Veronese space is the real span of the realified lattice `Γ₂`. -/
lemma span_Gam_eq_Lam (d n : ℕ) (x y : Fin (n + 1) → ℤ) :
    Submodule.span ℝ ((Gam d n x y).map intCastPi : Set (Mon d n → ℝ))
      = Lam d n (toR x) (toR y) := by
  unfold Gam
  rw [span_realify_latOrth_inf, ← evalinR_eq_linComb, ← evalinR_eq_linComb]
  rfl

/-- **The `Ψ`-lift (two vectors).**  If `Γ₂ = Gam 2 n x y = Λ_{ν₂(x)} ∩ Λ_{ν₂(y)}` contains
`NN 2 n - 2` `ℤ`-independent vectors `a j` of norm at most `B`, then
`Gam d n x y = Λ_{ν_d(x)} ∩ Λ_{ν_d(y)}` contains `NN d n - 2` `ℤ`-independent vectors of norm at
most `B` (the paper's reduction of "Key result two vectors" from `d = 2` to all `d`). -/
theorem lam_Gam_veronese_le (d n : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ n) (x y : Fin (n + 1) → ℤ)
    (hx : IsPrim x) (hy : IsPrim y) (hxy : LinearIndependent ℤ ![x, y])
    (B : ℝ) (hB : 0 ≤ B) (a : Fin (NN 2 n - 2) → (Mon 2 n → ℤ))
    (ha : ∀ j, a j ∈ Gam 2 n x y) (hai : LinearIndependent ℤ a)
    (han : ∀ j, eNorm (a j) ≤ B) :
    lam (Gam d n x y) (NN d n - 2) ≤ B := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, (Nat.sub_add_cancel hd).symm⟩
  have hxyne : x ≠ y := by
    intro h
    have hrel : (1 : ℤ) • x + (-1) • y = 0 := by rw [h]; simp
    exact one_ne_zero ((LinearIndependent.pair_iff.mp hxy) 1 (-1) hrel).1
  have hxyne' : x ≠ -y := by
    intro h
    have hrel : (1 : ℤ) • x + (1 : ℤ) • y = 0 := by rw [h]; simp
    exact one_ne_zero ((LinearIndependent.pair_iff.mp hxy) 1 1 hrel).1
  have hν : LinearIndependent ℤ ![veronese (k + 2) n x, veronese (k + 2) n y] :=
    Work.HP.Sig2.nu_indep (k + 2) n (by omega) x y hx hy hxyne hxyne'
  have hν2 : LinearIndependent ℤ ![veronese 2 n x, veronese 2 n y] :=
    Work.HP.Sig2.nu_indep 2 n (by norm_num) x y hx hy hxyne hxyne'
  have hxyR : LinearIndependent ℝ ![toR x, toR y] := by
    have h := linInd_toR hxy
    convert h using 1
    funext i; fin_cases i <;> rfl
  have hLam2 : Lam 2 n (toR x) (toR y)
      = Submodule.span ℝ (Set.range (fun j : Fin (NN 2 n - 2) => intCastPi (a j))) := by
    have hli : LinearIndependent ℝ (fun j : Fin (NN 2 n - 2) => intCastPi (a j)) := by
      have h := linInd_toR (v := a) hai
      convert h using 1
      funext j i
      rfl
    have hdim_span : Module.finrank ℝ
        (Submodule.span ℝ (Set.range (fun j : Fin (NN 2 n - 2) => intCastPi (a j))))
        = NN 2 n - 2 := by
      rw [finrank_span_eq_card hli, Fintype.card_fin]
    have hdim_Lam : Module.finrank ℝ (Lam 2 n (toR x) (toR y)) = NN 2 n - 2 := by
      rw [← span_Gam_eq_Lam 2 n x y, Submodule.map_coe, finrank_span_image_intCastPi]
      exact (Work.HP.Sig2.gam_rank_det 2 n x y hν2).1
    refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [← span_Gam_eq_Lam 2 n x y]
      exact Submodule.subset_span ⟨a j, ha j, rfl⟩
    · rw [hdim_span, hdim_Lam]
  have hLam2V : Lam2V k (k + 2) n (toR x) (toR y)
      = Submodule.span ℝ (Set.range (fun p : Mon k n × Fin (NN 2 n - 2) =>
          mulVec k 2 (k + 2) (unitMon (R := ℝ) p.1) (intCastPi (a p.2)))) := by
    refine le_antisymm ?_ ?_
    · rw [Lam2V, Submodule.span_le]
      rintro B ⟨G, Q, hQ, rfl⟩
      rw [hLam2] at hQ
      have hA : mulVec k 2 (k + 2) G Q ∈
          Submodule.span ℝ (Set.range (fun j => mulVec k 2 (k + 2) G (intCastPi (a j)))) := by
        have hle : Submodule.span ℝ (Set.range (fun j : Fin (NN 2 n - 2) => intCastPi (a j)))
            ≤ Submodule.comap (mulVecRgen' k 2 (k + 2) G)
                (Submodule.span ℝ (Set.range
                  (fun j => mulVec k 2 (k + 2) G (intCastPi (a j))))) := by
          rw [Submodule.span_le]
          rintro _ ⟨j, rfl⟩
          exact Submodule.mem_comap.mpr (Submodule.subset_span ⟨j, rfl⟩)
        exact Submodule.mem_comap.mp (hle hQ)
      refine Submodule.span_le.mpr ?_ hA
      rintro _ ⟨j, rfl⟩
      dsimp only
      rw [← sum_smul_unitMon (R := ℝ) G,
        show mulVec k 2 (k + 2) (∑ P : Mon k n, G P • unitMon (R := ℝ) P) (intCastPi (a j))
          = mulVecRgen k 2 (k + 2) (intCastPi (a j))
              (∑ P : Mon k n, G P • unitMon (R := ℝ) P) from rfl,
        map_sum]
      refine Submodule.sum_mem _ fun P _ => ?_
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(P, j), rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      refine Submodule.subset_span ⟨unitMon (R := ℝ) p.1, intCastPi (a p.2), ?_, rfl⟩
      rw [hLam2]
      exact Submodule.subset_span ⟨p.2, rfl⟩
  have hv_mem : ∀ p : Mon k n × Fin (NN 2 n - 2),
      mulVec k 2 (k + 2) (unitMon (R := ℤ) p.1) (a p.2) ∈ Gam (k + 2) n x y := by
    rintro ⟨P, j⟩
    rw [MDBasic.mem_Gam_iff]
    constructor
    · have h2 : formEvalR (k + 2) n
          (mulVec k 2 (k + 2) (unitMon (R := ℝ) P) (intCastPi (a j))) (toR x) = 0 := by
        have haj := (MDBasic.mem_Gam_iff 2 n x y (a j)).mp (ha j)
        rw [Work.HP.Sig2.LiftTwo.mulVec_formEvalR', formEvalR_intCastToR, haj.1,
          Int.cast_zero, mul_zero]
      have h3 : formEvalR (k + 2) n
          (intCastPi (mulVec k 2 (k + 2) (unitMon (R := ℤ) P) (a j))) (toR x) = 0 := by
        rw [intCastPi_mulVec, fun_unitMon_cast]; exact h2
      have h4 := formEvalR_intCastToR (k + 2) n
        (mulVec k 2 (k + 2) (unitMon (R := ℤ) P) (a j)) x
      rw [h4] at h3
      exact_mod_cast h3
    · have h2 : formEvalR (k + 2) n
          (mulVec k 2 (k + 2) (unitMon (R := ℝ) P) (intCastPi (a j))) (toR y) = 0 := by
        have haj := (MDBasic.mem_Gam_iff 2 n x y (a j)).mp (ha j)
        rw [Work.HP.Sig2.LiftTwo.mulVec_formEvalR', formEvalR_intCastToR, haj.2,
          Int.cast_zero, mul_zero]
      have h3 : formEvalR (k + 2) n
          (intCastPi (mulVec k 2 (k + 2) (unitMon (R := ℤ) P) (a j))) (toR y) = 0 := by
        rw [intCastPi_mulVec, fun_unitMon_cast]; exact h2
      have h4 := formEvalR_intCastToR (k + 2) n
        (mulVec k 2 (k + 2) (unitMon (R := ℤ) P) (a j)) y
      rw [h4] at h3
      exact_mod_cast h3
  have hv_norm : ∀ p : Mon k n × Fin (NN 2 n - 2),
      eNorm (mulVec k 2 (k + 2) (unitMon (R := ℤ) p.1) (a p.2)) ≤ B := by
    rintro ⟨P, j⟩
    rw [eNorm_mulVec_unitMon P (a j)]
    exact han j
  have hv_span : Submodule.span ℝ (Set.range (fun p : Mon k n × Fin (NN 2 n - 2) =>
        intCastPi (mulVec k 2 (k + 2) (unitMon (R := ℤ) p.1) (a p.2))))
      = Submodule.span ℝ ((Gam (k + 2) n x y).map intCastPi : Set (Mon (k + 2) n → ℝ)) := by
    have hrw : (fun p : Mon k n × Fin (NN 2 n - 2) =>
        intCastPi (mulVec k 2 (k + 2) (unitMon (R := ℤ) p.1) (a p.2)))
        = (fun p => mulVec k 2 (k + 2) (unitMon (R := ℝ) p.1) (intCastPi (a p.2))) := by
      funext p
      rw [intCastPi_mulVec, fun_unitMon_cast]
      rfl
    rw [hrw, span_Gam_eq_Lam (k + 2) n x y,
      Lam_gen_a k n (toR x) (toR y) hxyR, hLam2V]
  have hrank : rk (Gam (k + 2) n x y) = NN (k + 2) n - 2 :=
    (Work.HP.Sig2.gam_rank_det (k + 2) n x y hν).1
  have hmain := lam_le_of_span (Gam (k + 2) n x y)
    (fun p : Mon k n × Fin (NN 2 n - 2) =>
      mulVec k 2 (k + 2) (unitMon (R := ℤ) p.1) (a p.2)) hv_mem hv_span hB hv_norm
  rwa [hrank] at hmain

end Work.HP.Vero
