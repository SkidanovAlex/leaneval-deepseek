import Mathlib
import Submission.Work.HP.Sig2.GamTwoDefs
import Submission.Work.HP.Sig2.GramOfPosDef
import Submission.Work.HP.Sig2.PerpCompLemmas
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.Vero.span_realify_latOrth_inf

set_option autoImplicit false
noncomputable section

open Matrix

namespace Work.HP.Sig2

open Work.HP Work.HP.Transf

/-! ## Elementary calculus of `dotR` -/

/-- `dotR` against a finite sum of scaled vectors. -/
private lemma dotR_sum_smul_right {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] (w : ι → ℝ)
    (a : κ → ℝ) (z : κ → ι → ℝ) : dotR w (∑ j, a j • z j) = ∑ j, a j * dotR w (z j) := by
  rw [dotR_comm]
  rw [dotR_sum_left Finset.univ (fun j => a j • z j) w]
  exact Finset.sum_congr rfl fun j _ => by rw [dotR_smul_left, dotR_comm]

/-- The two orders of the factors inside a sum: `∑ x, a x * b x = ∑ x, b x * a x`. -/
private lemma sum_mul_comm' {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (∑ x, a x * b x) = ∑ x, b x * a x :=
  Finset.sum_congr rfl fun x _ => mul_comm _ _

/-! ## The Schur-complement determinant of a block matrix with a `1 × 1` trailing block -/

/-- Determinant of the block matrix `[[G, w],[wᵀ, s]]` (with `Fin 1`-indexed trailing blocks)
expanded along the leading block `G`, which is invertible by hypothesis. -/
private lemma det_fromBlocks_finone {m : Type} [Fintype m] [DecidableEq m] (G : Matrix m m ℝ)
    (w : m → ℝ) (s : ℝ) (hG : IsUnit G.det) (hsymm : ∀ i j, G⁻¹ i j = G⁻¹ j i) :
    (Matrix.fromBlocks G (fun i (_ : Fin 1) => w i) (fun (_ : Fin 1) j => w j)
        (fun (_ _ : Fin 1) => s)).det = G.det * (s - ∑ i, ∑ j, w i * G⁻¹ i j * w j) := by
  letI : Invertible G := Matrix.invertibleOfIsUnitDet G hG
  let B : Matrix m (Fin 1) ℝ := fun i _ => w i
  let C : Matrix (Fin 1) m ℝ := fun _ j => w j
  let D : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => s
  have hFB : Matrix.fromBlocks G B C D
      = Matrix.fromBlocks G (fun i (_ : Fin 1) => w i) (fun (_ : Fin 1) j => w j)
          (fun (_ _ : Fin 1) => s) := rfl
  rw [← hFB, Matrix.det_fromBlocks₁₁ G B C D]
  have hCB : (C * ⅟G * B) 0 0 = ∑ i, (∑ j, w j * G⁻¹ j i) * w i := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_apply,
      show (∑ j, C 0 j * ⅟G j i) = ∑ j, w j * G⁻¹ j i from by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show C 0 j = w j from rfl, Matrix.invOf_eq_nonsing_inv],
      show B i 0 = w i from rfl]
  have hsum : (∑ i, (∑ j, w j * G⁻¹ j i) * w i)
      = ∑ i, ∑ j, w i * G⁻¹ i j * w j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsymm j i]
    ring
  rw [Matrix.det_fin_one,
    show (D - C * ⅟G * B) 0 0 = D 0 0 - (C * ⅟G * B) 0 0 from by rw [Matrix.sub_apply],
    show D 0 0 = s from rfl, hCB, hsum]

/-! ## The rank of `A ⊔ ℝw` for `w ∉ A` -/

/-- Adjoining a vector outside a real subspace raises the dimension by one. -/
private lemma finrank_sup_span_singleton {ι : Type*} [Fintype ι] {A : Submodule ℝ (ι → ℝ)}
    {w : ι → ℝ} (hw : w ∉ A) :
    Module.finrank ℝ ↥(A ⊔ Submodule.span ℝ ({w} : Set (ι → ℝ))) = Module.finrank ℝ A + 1 := by
  have hw0 : w ≠ 0 := fun h => hw (h ▸ A.zero_mem)
  have hinf : A ⊓ Submodule.span ℝ ({w} : Set (ι → ℝ)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    rw [Submodule.mem_inf] at hz
    obtain ⟨hzA, hzS⟩ := hz
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hzS
    by_cases hc0 : c = 0
    · rw [hc0, zero_smul] at hc
      exact hc.symm
    · exfalso
      have hzA' : c • w ∈ A := by rwa [← hc] at hzA
      have hmem : c⁻¹ • (c • w) ∈ A := A.smul_mem c⁻¹ hzA'
      rw [smul_smul, inv_mul_cancel₀ hc0, one_smul] at hmem
      exact hw hmem
  have h2 : Module.finrank ℝ ↥(A ⊓ Submodule.span ℝ ({w} : Set (ι → ℝ))) = 0 := by
    rw [hinf]
    exact finrank_bot ℝ (ι → ℝ)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq A (Submodule.span ℝ ({w} : Set (ι → ℝ)))
  rw [h2, finrank_span_singleton hw0] at h1
  omega

/-! ## The main theorem -/

/-- For an integral lattice `Λ ⊆ ℤ^ι` and `v ∈ ℤ^ι` whose perpendicular component with respect to
`span_ℝ(Λ)` is nonzero, the lattice `Λ ⊔ ℤv` has rank one more than `Λ` and covolume
`detL Λ * ‖v_⊥‖`.

IMPORTANT: this file must remain importable together with `Submission.Work.HP.Vero`; do not import
`numaux.Defs`, `DetLOrth`, `det_gam`, `det_gam_gen`, `EElow`, `MDEstimates` (name clash on
`Work.HP.orthLat`).
-/
theorem CovolumeSingle {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Submodule ℤ (ι → ℤ))
    (v : ι → ℤ) (hv : perpComp Λ (toR v) ≠ 0) :
    rk (Λ ⊔ Submodule.span ℤ ({v} : Set (ι → ℤ))) = rk Λ + 1 ∧
      detL (Λ ⊔ Submodule.span ℤ ({v} : Set (ι → ℤ)))
        = detL Λ * rNorm (perpComp Λ (toR v)) := by
  classical
  let M : Submodule ℤ (ι → ℤ) := Λ ⊔ Submodule.span ℤ ({v} : Set (ι → ℤ))
  change rk M = rk Λ + 1 ∧ detL M = detL Λ * rNorm (perpComp Λ (toR v))
  let bb := Submodule.basisOfPid (Pi.basisFun ℤ ι) Λ
  let b : Module.Basis (Fin bb.1) ℤ Λ := bb.2
  have hpe : perpComp Λ (toR v) = perpCompB b (toR v) := rfl
  have hGinv : gramOf b * (gramOf b)⁻¹ = 1 := (gramOf_isUnit_inv b).2.2
  have hGunit : IsUnit (gramOf b).det :=
    (Matrix.isUnit_iff_isUnit_det (gramOf b)).mp (gramOf_isUnit_inv b).1
  have hGpos : 0 ≤ (gramOf b).det := (GramOfPosDef b).det_pos.le
  have hsymmInv : ∀ i j : Fin bb.1, (gramOf b)⁻¹ i j = (gramOf b)⁻¹ j i := by
    intro i j
    have hsymm : (gramOf b)ᵀ = gramOf b := by
      ext k l
      rw [Matrix.transpose_apply]
      exact gramOf_comm b l k
    have h1 : (gramOf b)ᵀ⁻¹ = (gramOf b)⁻¹ := by rw [hsymm]
    have h2 : (gramOf b)⁻¹ᵀ = (gramOf b)ᵀ⁻¹ := Matrix.transpose_nonsing_inv (gramOf b)
    have h3 : (gramOf b)⁻¹ᵀ = (gramOf b)⁻¹ := by rw [h2, h1]
    have h4 := congrFun (congrFun h3 j) i
    simpa [Matrix.transpose_apply] using h4
  -- `toR v` is not in the real span of `Λ`
  have hnotmem : toR v ∉ PerpCompAux.spanR Λ := by
    intro hmem
    exact hv (PerpCompAux.perpComp_eq_zero_of_mem Λ hmem)
  -- the extended family of integer vectors, and the corresponding family in `M`
  let F : Fin bb.1 ⊕ Fin 1 → ι → ℤ := fun x => match x with
    | Sum.inl i => ((b i : Λ) : ι → ℤ)
    | Sum.inr _ => v
  let g : Fin bb.1 ⊕ Fin 1 → M := fun x =>
    ⟨F x, match x with
      | Sum.inl i => Submodule.mem_sup_left (b i).2
      | Sum.inr _ => Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton v))⟩
  have hg_inl : ∀ i : Fin bb.1, ((g (Sum.inl i) : M) : ι → ℤ) = ((b i : Λ) : ι → ℤ) :=
    fun i => rfl
  have hg_inr : ∀ u : Fin 1, ((g (Sum.inr u) : M) : ι → ℤ) = v := fun u => rfl
  have hlin : LinearIndependent ℤ F := by
    rw [Fintype.linearIndependent_iff]
    intro e he
    have he1 : (∑ i : Fin bb.1, e (Sum.inl i) • intCastPi ((b i : Λ) : ι → ℤ))
        + e (Sum.inr 0) • intCastPi v = 0 := by
      have h := congrArg (fun z : ι → ℤ => (intCastPi z : ι → ℝ)) he
      simp only [map_sum, map_smul, map_zero] at h
      rw [Fintype.sum_sum_type] at h
      rw [Fin.sum_univ_one (fun u : Fin 1 => e (Sum.inr u) • intCastPi (F (Sum.inr u)))] at h
      simp only [F] at h
      exact h
    by_cases he0 : e (Sum.inr 0) = 0
    · have hsum : (∑ i : Fin bb.1, e (Sum.inl i) • intCastPi ((b i : Λ) : ι → ℤ)) = 0 := by
        rw [he0, zero_smul, add_zero] at he1
        exact he1
      have hcoefs : ∀ i : Fin bb.1, e (Sum.inl i) = 0 := by
        have hliR := linearIndependent_intCastPi_basis b
        have hkey : (∑ i : Fin bb.1,
            (((e (Sum.inl i) : ℤ) : ℝ)) • intCastPi (((b i : Λ) : ι → ℤ))) = 0 := by
          rw [← hsum]
          exact Finset.sum_congr rfl fun i _ => by rw [Int.cast_smul_eq_zsmul]
        have h := (Fintype.linearIndependent_iff.mp hliR)
          (fun i : Fin bb.1 => ((e (Sum.inl i) : ℤ) : ℝ)) hkey
        intro i
        exact_mod_cast h i
      intro x
      rcases x with i | u
      · exact hcoefs i
      · rw [Subsingleton.elim u 0]
        exact he0
    · exfalso
      have hneg : e (Sum.inr 0) • intCastPi v
          = -(∑ i : Fin bb.1, e (Sum.inl i) • intCastPi ((b i : Λ) : ι → ℤ)) :=
        eq_neg_of_add_eq_zero_right he1
      have hmem : e (Sum.inr 0) • intCastPi v ∈ PerpCompAux.spanR Λ := by
        rw [hneg]
        refine Submodule.neg_mem _ ?_
        rw [show (∑ i : Fin bb.1, e (Sum.inl i) • intCastPi ((b i : Λ) : ι → ℤ))
            = ∑ i : Fin bb.1, ((e (Sum.inl i) : ℤ) : ℝ) • intCastPi ((b i : Λ) : ι → ℤ) from
          Finset.sum_congr rfl fun i _ => by rw [Int.cast_smul_eq_zsmul]]
        exact Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, (b i).2, rfl⟩)
      have hcoef : ((e (Sum.inr 0) : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr he0
      have hmemv : intCastPi v ∈ PerpCompAux.spanR Λ := by
        have h2 : intCastPi v
            = (((e (Sum.inr 0) : ℤ) : ℝ))⁻¹ • (e (Sum.inr 0) • intCastPi v) := by
          rw [← Int.cast_smul_eq_zsmul ℝ (e (Sum.inr 0)) (intCastPi v)]
          exact (inv_smul_smul₀ hcoef (intCastPi v)).symm
        rw [h2]
        exact Submodule.smul_mem _ _ hmem
      exact hnotmem hmemv
  have hlinG : LinearIndependent ℤ g := by
    refine (LinearIndependent.of_comp (R := ℤ) (Submodule.subtype M)) ?_
    have hcomp : ((Submodule.subtype M : M →ₗ[ℤ] (ι → ℤ)) ∘ g) = F := by
      funext x
      rfl
    rw [hcomp]
    exact hlin
  have hspanG : ⊤ ≤ Submodule.span ℤ (Set.range g) := by
    intro x _
    obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp x.2
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hc
    have haexp : (∑ i : Fin bb.1, (b.repr ⟨a, ha⟩) i • ((b i : Λ) : ι → ℤ)) = a := by
      have h := congrArg (Submodule.subtype Λ) (Module.Basis.sum_repr b ⟨a, ha⟩)
      rw [map_sum] at h
      simp only [map_smul] at h
      exact h
    have hx : (∑ i : Fin bb.1, (b.repr ⟨a, ha⟩) i • g (Sum.inl i)) + k • g (Sum.inr 0) = x := by
      apply Subtype.ext
      rw [Submodule.coe_add]
      have h1 : ((∑ i : Fin bb.1, (b.repr ⟨a, ha⟩) i • g (Sum.inl i) : M) : ι → ℤ)
          = ∑ i : Fin bb.1, (b.repr ⟨a, ha⟩) i • ((b i : Λ) : ι → ℤ) := by
        rw [Submodule.coe_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [Submodule.coe_smul, hg_inl i]
      have h2 : ((k • g (Sum.inr 0) : M) : ι → ℤ) = k • v := by
        rw [show ((k • g (Sum.inr 0) : M) : ι → ℤ)
            = k • ((g (Sum.inr 0) : M) : ι → ℤ) from
          map_smul (Submodule.subtype M) k (g (Sum.inr 0)), hg_inr 0]
      rw [h1, h2, haexp, hk]
      exact hac
    rw [← hx]
    refine Submodule.add_mem _ ?_ ?_
    · refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      exact Submodule.subset_span (Set.mem_range_self (Sum.inl i))
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self (Sum.inr 0)))
  let β : Module.Basis (Fin bb.1 ⊕ Fin 1) ℤ M := Module.Basis.mk hlinG hspanG
  have hβ : ∀ x, β x = g x := fun x => Module.Basis.mk_apply hlinG hspanG x
  -- the Gram matrix of `β` is the block matrix `[[G, w], [wᵀ, ‖v‖²]]`
  have hgram : gramOf β = Matrix.fromBlocks (gramOf b)
      (fun i (_ : Fin 1) => dotR (toR v) (toR ((b i : Λ) : ι → ℤ)))
      (fun (_ : Fin 1) j => dotR (toR v) (toR ((b j : Λ) : ι → ℤ)))
      (fun (_ _ : Fin 1) => dotR (toR v) (toR v)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · show (∑ x, (((β (Sum.inl i) : M) : ι → ℤ) x : ℝ)
          * (((β (Sum.inl j) : M) : ι → ℤ) x : ℝ))
        = (∑ x, (((b i : Λ) : ι → ℤ) x : ℝ) * (((b j : Λ) : ι → ℤ) x : ℝ))
      simp only [hβ, hg_inl]
    · show (∑ x, (((β (Sum.inl i) : M) : ι → ℤ) x : ℝ)
          * (((β (Sum.inr j) : M) : ι → ℤ) x : ℝ))
        = dotR (toR v) (toR ((b i : Λ) : ι → ℤ))
      rw [dotR_comm]
      simp only [hβ, hg_inl, hg_inr, dotR, toR]
    · show (∑ x, (((β (Sum.inr i) : M) : ι → ℤ) x : ℝ)
          * (((β (Sum.inl j) : M) : ι → ℤ) x : ℝ))
        = dotR (toR v) (toR ((b j : Λ) : ι → ℤ))
      simp only [hβ, hg_inr, hg_inl, dotR, toR]
    · show (∑ x, (((β (Sum.inr i) : M) : ι → ℤ) x : ℝ)
          * (((β (Sum.inr j) : M) : ι → ℤ) x : ℝ))
        = dotR (toR v) (toR v)
      simp only [hβ, hg_inr, dotR, toR]
  have hdetM : detL M = Real.sqrt (Matrix.det (gramOf β)) :=
    Work.HP.Lat.detL_basis_gram M β
  have hdetΛ : detL Λ = Real.sqrt ((gramOf b).det) :=
    Work.HP.Lat.detL_basis_gram Λ b
  -- the algebraic identity identifying the Schur complement with `‖v_⊥‖²`
  have hproj : dotR (toR v) (PerpCompAux.projB b (toR v))
      = ∑ i : Fin bb.1, ∑ j : Fin bb.1,
          dotR (toR v) (toR ((b i : Λ) : ι → ℤ)) * (gramOf b)⁻¹ i j
            * dotR (toR v) (toR ((b j : Λ) : ι → ℤ)) := by
    rw [PerpCompAux.projB, dotR_sum_smul_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    simp only [toR_eq_intCastPi]
    exact Finset.sum_congr rfl fun j _ => by ring
  have horth : dotR (perpComp Λ (toR v)) (PerpCompAux.projB b (toR v)) = 0 := by
    have h := (perpCompB_mem_orth b hGinv).2 (toR v) (PerpCompAux.projB b (toR v))
      (PerpCompAux.projB_mem b (toR v))
    rw [hpe]
    exact h
  have hkey : dotR (toR v) (toR v) - ∑ i : Fin bb.1, ∑ j : Fin bb.1,
        dotR (toR v) (toR ((b i : Λ) : ι → ℤ)) * (gramOf b)⁻¹ i j
          * dotR (toR v) (toR ((b j : Λ) : ι → ℤ))
      = dotR (perpComp Λ (toR v)) (perpComp Λ (toR v)) := by
    rw [← hproj]
    have hpcc : dotR (PerpCompAux.projB b (toR v)) (perpComp Λ (toR v)) = 0 := by
      rw [dotR_comm]
      exact horth
    have hvdecomp : toR v = perpComp Λ (toR v) + PerpCompAux.projB b (toR v) := by
      rw [hpe, PerpCompAux.perpCompB_eq]
      abel
    have hA : dotR (toR v) (toR v)
        = dotR (perpComp Λ (toR v)) (perpComp Λ (toR v))
          + dotR (PerpCompAux.projB b (toR v)) (PerpCompAux.projB b (toR v)) := by
      conv_lhs => rw [hvdecomp]
      rw [dotR_add_left, dotR_add_right, dotR_add_right, horth, hpcc]
      ring
    have hB : dotR (toR v) (PerpCompAux.projB b (toR v))
        = dotR (PerpCompAux.projB b (toR v)) (PerpCompAux.projB b (toR v)) := by
      nth_rewrite 1 [hvdecomp]
      rw [dotR_add_left, horth, zero_add]
    rw [hA, hB]
    ring
  have hdetβ : Matrix.det (gramOf β)
      = (gramOf b).det * dotR (perpComp Λ (toR v)) (perpComp Λ (toR v)) := by
    rw [hgram, det_fromBlocks_finone (gramOf b)
      (fun i => dotR (toR v) (toR ((b i : Λ) : ι → ℤ))) (dotR (toR v) (toR v)) hGunit hsymmInv,
      hkey]
  have hsqrt : Real.sqrt (dotR (perpComp Λ (toR v)) (perpComp Λ (toR v)))
      = rNorm (perpComp Λ (toR v)) := by
    rw [← Transf.rNorm_sq (perpComp Λ (toR v)), Real.sqrt_sq (Transf.rNorm_nonneg _)]
  -- rank
  have hspanM : Submodule.span ℝ (intCastPi '' (M : Set (ι → ℤ)))
      = PerpCompAux.spanR Λ ⊔ Submodule.span ℝ ({toR v} : Set (ι → ℝ)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro z ⟨m, hm, rfl⟩
      obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp hm
      obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hc
      have h1 : intCastPi a ∈ PerpCompAux.spanR Λ := Submodule.subset_span ⟨a, ha, rfl⟩
      have h2 : intCastPi m = intCastPi a + k • toR v := by
        rw [← hac, ← hk, map_add, map_smul]
        rfl
      rw [h2]
      refine Submodule.add_mem_sup h1 ?_
      rw [show k • toR v = ((k : ℤ) : ℝ) • toR v from
        (Int.cast_smul_eq_zsmul ℝ k (toR v)).symm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton (toR v)))
    · rw [sup_le_iff]
      refine ⟨?_, ?_⟩
      · exact Submodule.span_mono (Set.image_mono (fun a ha => Submodule.mem_sup_left ha))
      · rw [Submodule.span_le]
        rintro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact Submodule.subset_span
          ⟨v, Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton v)), rfl⟩
  have hfin : Module.finrank ℝ (Submodule.span ℝ (intCastPi '' (M : Set (ι → ℤ))))
      = Module.finrank ℝ (PerpCompAux.spanR Λ) + 1 := by
    rw [hspanM, finrank_sup_span_singleton hnotmem]
  have hrk : rk M = rk Λ + 1 := by
    change Module.finrank ℤ M = Module.finrank ℤ Λ + 1
    rw [← Vero.finrank_span_image_intCastPi M, ← Vero.finrank_span_image_intCastPi Λ]
    exact hfin
  refine ⟨hrk, ?_⟩
  calc detL M = Real.sqrt (Matrix.det (gramOf β)) := hdetM
    _ = Real.sqrt ((gramOf b).det
          * dotR (perpComp Λ (toR v)) (perpComp Λ (toR v))) := by rw [hdetβ]
    _ = Real.sqrt ((gramOf b).det)
          * Real.sqrt (dotR (perpComp Λ (toR v)) (perpComp Λ (toR v))) := Real.sqrt_mul hGpos _
    _ = detL Λ * rNorm (perpComp Λ (toR v)) := by rw [← hdetΛ, hsqrt]

end Work.HP.Sig2
