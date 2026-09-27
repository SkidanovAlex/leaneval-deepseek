import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLContract.Diag
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLContract.Lemmas.SL3Topology
import Submission.Work.EKLContract.Lemmas.V_open_one
import Submission.Work.EKLContract.Lemmas.mkX_mul
import Submission.Work.EKLContract.Lemmas.isClosed_Thick
import Submission.Work.EKLComp.EucDefs
import Submission.Work.EKLComp.enorm3_basic_bounds
import Submission.Work.EKLComp.core_assembly
import Submission.Work.EKLComp.exists_euclidean_shortest_lattice_vector
import Submission.Work.EKLComp.exists_unimodular_first_column
import Submission.Work.EKLComp.exists_orthonormal_frame
import Submission.Work.EKLComp.thick_inj_given_short
import Submission.Work.EKLComp.polishSpace_X3
import Submission.Work.EKLComp.uniform_inj_of_isCompact
import Submission.Work.EKLProd.sl3EntryBox_compact

/-!
# Component C2 of the frozen EKL contract: the space of lattices

This module proves `Work.EKLComp.prove_X3 : Work.EKLContract.P_X3`, the five conjuncts of the
frozen contract C2 (`Submission/Work/EKLContract/Defs.lean`):

1. `T2Space X₃`,
2. `PolishSpace X₃`,
3. Mahler compactness: `IsCompact (Thick ρ)` for `ρ > 0`,
4. uniform injectivity of the orbit maps on compacta,
5. openness of the orbit maps `g ↦ g • x`.

The mathematical content is Mahler compactness (3).  The engine is the quantitative Mahler
criterion `thick_basis_bound_self`: a `ρ`-thick unimodular lattice has a ℤ-basis, all of whose
vectors have sup-norm `≤ px3C ρ`, i.e. bounded by a constant depending only on `ρ`.
-/

open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

namespace Work.EKLComp

open Work.EKLContract

noncomputable section

/-! ## Conjunct 1: `X₃` is Hausdorff -/

/-- **Conjunct 1.** `X₃ = SL₃(ℝ)/SL₃(ℤ)` is a Hausdorff space: `Γ₃` is discrete (hence closed)
in the T₂ group `SL₃(ℝ)`, and the quotient of a topological group by a closed subgroup is
Hausdorff. -/
instance t2Space_X3 : T2Space X3 := inferInstance

/-- The projection `mkX : SL₃(ℝ) → X₃` is an open quotient map (quotient by a subgroup). -/
theorem isOpenQuotientMap_mkX : IsOpenQuotientMap (mkX : SL3 → X3) :=
  QuotientGroup.isOpenQuotientMap_mk (N := Γ3)

/-! ## Conjunct 5: openness of the orbit maps -/

/-- **Conjunct 5.** The orbit map `g ↦ g • x` carries `V δ` onto a neighbourhood of `x`. -/
theorem orbit_image_V_mem_nhds (x : X3) (δ : ℝ) (hδ : 0 < δ) :
    (fun g : SL3 => g • x) '' V δ ∈ 𝓝 x := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  have hcomp : (fun g : SL3 => g • (k : X3)) = mkX ∘ (fun g : SL3 => g * k) := by
    funext g; exact (Lemmas.mkX_mul g k).symm
  rw [hcomp, Set.image_comp]
  have hV : V δ ∈ 𝓝 (1 : SL3) := (Lemmas.V_open_one δ hδ).1.mem_nhds (Lemmas.V_open_one δ hδ).2
  have h1 : (fun g : SL3 => g * k) '' V δ ∈ 𝓝 k := by
    have hcoe : (fun g : SL3 => g * k) = ⇑(Homeomorph.mulRight k) := rfl
    rw [hcoe]
    simpa using (Homeomorph.mulRight k).isOpenMap.image_mem_nhds hV
  have h3 : mkX '' ((fun g : SL3 => g * k) '' V δ) ∈ 𝓝 (mkX k) := by
    have hm : 𝓝 (mkX k) = Filter.map mkX (𝓝 k) := (isOpenQuotientMap_mkX.map_nhds_eq k).symm
    rw [hm]
    exact Filter.mem_map.mpr (Filter.mem_of_superset h1 (fun y hy => ⟨y, hy, rfl⟩))
  simpa [mkX] using h3

/-! ## Conjunct 3: Mahler compactness -/

/-- Homogeneity of the hand-rolled Euclidean norm `enorm3`. -/
lemma px3enorm3_smul (c : ℝ) (v : Fin 3 → ℝ) : enorm3 (c • v) = |c| * enorm3 v := by
  have h : dot3 (c • v) (c • v) = c ^ 2 * dot3 v v := by
    rw [dot3, dot3, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  have h1 : enorm3 (c • v) = Real.sqrt (c ^ 2 * dot3 v v) := by rw [enorm3, h]
  have h2 : enorm3 v = Real.sqrt (dot3 v v) := rfl
  rw [h1, h2, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- An integral `3 × 3` matrix with non-zero determinant has trivial kernel. -/
lemma px3_mulVec_eq_zero {A : Matrix (Fin 3) (Fin 3) ℤ} (hA : A.det ≠ 0) {m : Fin 3 → ℤ}
    (h : Matrix.mulVec A m = 0) : m = 0 := by
  have h1 : Matrix.mulVec (A.adjugate * A) m = 0 := by
    rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
  funext i
  have h2 : A.det * m i = 0 := by
    have := congr_fun h1 i
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
  exact (mul_eq_zero.mp h2).resolve_left hA

/-- A Euclidean-shortest vector of a `ρ`-thick unimodular lattice has a **primitive** coordinate
vector: were `m = k • m'` with `|k| ≥ 2` integral and `m' ≠ 0`, then `m'` would be a strictly
shorter non-zero lattice vector. -/
lemma px3_shortest_primitive (g : Matrix (Fin 3) (Fin 3) ℝ) (hg : g.det = 1) (ρ : ℝ)
    (hρ : 0 < ρ)
    (hmin : ∀ m : Fin 3 → ℤ, m ≠ 0 → ρ ≤ ‖Matrix.mulVec g (fun i => (m i : ℝ))‖) :
    ∃ m : Fin 3 → ℤ, m ≠ 0 ∧ (∀ k : ℤ, (∀ i, k ∣ m i) → k = 1 ∨ k = -1) ∧
      (∀ m' : Fin 3 → ℤ, m' ≠ 0 →
        enorm3 (Matrix.mulVec g (fun i => (m i : ℝ))) ≤
          enorm3 (Matrix.mulVec g (fun i => (m' i : ℝ)))) ∧
      enorm3 (Matrix.mulVec g (fun i => (m i : ℝ))) ≤ 2 * Real.sqrt 3 ∧
      ρ ≤ enorm3 (Matrix.mulVec g (fun i => (m i : ℝ))) := by
  obtain ⟨m, hmne, hmin', ha2, hρa⟩ := exists_euclidean_shortest_lattice_vector g hg ρ hρ hmin
  refine ⟨m, hmne, ?_, hmin', ha2, hρa⟩
  intro k hk
  by_contra hcon
  push_neg at hcon
  obtain ⟨hk1, hmk1⟩ := hcon
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hmne (funext fun i => by simpa using (hk i))
  set m' : Fin 3 → ℤ := fun i => m i / k with hm'def
  have hm'mul : ∀ i, m i = k * m' i := by
    intro i
    rw [hm'def, mul_comm]
    exact (Int.ediv_mul_cancel (hk i)).symm
  have hm'ne : m' ≠ 0 := by
    intro h0
    exact hmne (funext fun i => by rw [hm'mul i, h0]; simp)
  have hcast : (fun i => (m i : ℝ)) = (k : ℝ) • (fun i => (m' i : ℝ)) := by
    funext i; rw [hm'mul i]; simp [Pi.smul_apply, smul_eq_mul]
  have hmv : Matrix.mulVec g (fun i => (m i : ℝ)) =
      (k : ℝ) • Matrix.mulVec g (fun i => (m' i : ℝ)) := by
    rw [hcast, Matrix.mulVec_smul]
  have hEnorm : enorm3 (Matrix.mulVec g (fun i => (m i : ℝ))) =
      |(k : ℝ)| * enorm3 (Matrix.mulVec g (fun i => (m' i : ℝ))) := by
    rw [hmv, px3enorm3_smul]
  have hpos : 0 < enorm3 (Matrix.mulVec g (fun i => (m' i : ℝ))) := by
    have h1 : ρ ≤ ‖Matrix.mulVec g (fun i => (m' i : ℝ))‖ := hmin m' hm'ne
    have h2 : ‖Matrix.mulVec g (fun i => (m' i : ℝ))‖ ≤
        enorm3 (Matrix.mulVec g (fun i => (m' i : ℝ))) := (enorm3_basic_bounds _).2.2.1
    linarith
  have h3 : enorm3 (Matrix.mulVec g (fun i => (m i : ℝ))) ≤
      enorm3 (Matrix.mulVec g (fun i => (m' i : ℝ))) := hmin' m' hm'ne
  have hkabs : (2 : ℤ) ≤ |k| := by
    rcases lt_trichotomy k 0 with h | h | h
    · rw [abs_of_neg h]; omega
    · exact absurd h hk0
    · rw [abs_of_pos h]; omega
  have hk2 : (2 : ℝ) ≤ |(k : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast hkabs
  nlinarith [hEnorm, h3, hk2, hpos]

/-- **Quantitative Mahler criterion.**  Every `ρ`-thick unimodular lattice has a ℤ-basis whose
vectors all have sup-norm at most `px3C ρ`: there is a unimodular integral `A` with the entries of
`g A` bounded by the constant `px3C ρ` depending only on `ρ`. -/
theorem thick_basis_bound_self (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Matrix (Fin 3) (Fin 3) ℝ, g.det = 1 →
      (∀ m : Fin 3 → ℤ, m ≠ 0 → ρ ≤ ‖Matrix.mulVec g (fun j => (m j : ℝ))‖) →
      ∃ A : Matrix (Fin 3) (Fin 3) ℤ, A.det = 1 ∧
        ∀ i j, |(g * (A.map (Int.castRingHom ℝ))) i j| ≤ C := by
  refine ⟨px3C ρ, px3C_pos ρ hρ, ?_⟩
  intro g hg hmin
  obtain ⟨m, hmne, hmprim, hmin', ha2, hρa⟩ := px3_shortest_primitive g hg ρ hρ hmin
  obtain ⟨A0, hA0det, hA0col⟩ := exists_unimodular_first_column m hmne hmprim
  -- view `A₀` as an element of `SL₃(ℝ)` and put the shortest vector in the first column
  set A0sl : Matrix.SpecialLinearGroup (Fin 3) ℤ := (⟨A0, hA0det⟩ : Matrix.SpecialLinearGroup (Fin 3) ℤ)
    with hA0sl
  set B0 : SL3 := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A0sl with hB0
  have hA0slval : (A0sl : Matrix (Fin 3) (Fin 3) ℤ) = A0 := by
    rw [hA0sl, Matrix.SpecialLinearGroup.coe_mk]
  have hB0mat : (B0 : Matrix (Fin 3) (Fin 3) ℝ) = A0.map (Int.castRingHom ℝ) := by
    rw [hB0, Matrix.SpecialLinearGroup.coe_matrix_coe, hA0slval]
  set M : Matrix (Fin 3) (Fin 3) ℝ := g * (B0 : Matrix (Fin 3) (Fin 3) ℝ) with hMdef
  have hMdet : M.det = 1 := by
    rw [hMdef, Matrix.det_mul, hg, Matrix.SpecialLinearGroup.det_coe, one_mul]
  set v : Fin 3 → ℝ := Matrix.mulVec g (fun i => (m i : ℝ)) with hvdef
  have hvcol : ∀ i, M i 0 = v i := by
    have hcol : ∀ k : Fin 3, (B0 : Matrix (Fin 3) (Fin 3) ℝ) k 0 = (m k : ℝ) := by
      intro k
      rw [hB0mat, Matrix.map_apply, hA0col k]
      simp
    intro i
    rw [hMdef, hvdef, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun k _ => by rw [hcol k]
  have hMmin : ∀ m' : Fin 3 → ℤ, m' ≠ 0 →
      enorm3 v ≤ enorm3 (Matrix.mulVec M (fun i => (m' i : ℝ))) := by
    intro m' hm'
    have hne : Matrix.mulVec A0 m' ≠ 0 := fun h0 =>
      hm' (px3_mulVec_eq_zero (by rw [hA0det]; norm_num) h0)
    have hveq : Matrix.mulVec M (fun i => (m' i : ℝ)) =
        Matrix.mulVec g (fun i => ((Matrix.mulVec A0 m') i : ℝ)) := by
      rw [hMdef, ← Matrix.mulVec_mulVec, hB0mat, map_mulVec_int]
    rw [hveq, hvdef]
    exact hmin' (Matrix.mulVec A0 m') hne
  have hvne : v ≠ 0 := by
    rw [hvdef]
    intro h0
    have h1 : ρ ≤ ‖Matrix.mulVec g (fun i => (m i : ℝ))‖ := hmin m hmne
    rw [h0, norm_zero] at h1
    linarith
  obtain ⟨T, hTv, hTnorm, _hTdot, hTdet, _hTent, hTbound⟩ := exists_orthonormal_frame v hvne
  obtain ⟨A, hAdet, hAbound⟩ :=
    core_assembly_uniform M hMdet v hvcol (enorm3 v) rfl (lt_of_lt_of_le hρ hρa) ρ hρ hρa ha2
      hMmin T hTv hTnorm hTdet hTbound
  refine ⟨A0 * A, ?_, ?_⟩
  · rw [Matrix.det_mul, hA0det, hAdet, mul_one]
  · intro i j
    have hrew : (g * ((A0 * A).map (Int.castRingHom ℝ))) i j =
        (M * (A.map (Int.castRingHom ℝ))) i j := by
      rw [hMdef, hB0mat, Matrix.map_mul, Matrix.mul_assoc]
    rw [hrew]
    exact hAbound i j

/-- **Conjunct 3 (Mahler compactness).**  `Thick ρ = {λ₁ ≥ ρ}` is compact for `ρ > 0`. -/
theorem thick_isCompact (ρ : ℝ) (hρ : 0 < ρ) : IsCompact (Thick ρ) := by
  obtain ⟨C, hC, hb⟩ := thick_basis_bound_self ρ hρ
  -- the entry box of radius `C` in `SL₃(ℝ)` is compact
  have hKcpt : IsCompact {g : SL3 | ∀ i j, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C} := by
    have h := Work.EKLProd.sl3EntryBox_compact (fun (_ : Fin 3) (_ : Fin 3) => -C)
      (fun (_ : Fin 3) (_ : Fin 3) => C)
    have hset : {g : SL3 | ∀ i j, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C}
        = {g : SL3 | ∀ i j, (fun (_ : Fin 3) (_ : Fin 3) => -C) i j ≤
            (g : Matrix (Fin 3) (Fin 3) ℝ) i j ∧
            (g : Matrix (Fin 3) (Fin 3) ℝ) i j ≤ (fun (_ : Fin 3) (_ : Fin 3) => C) i j} := by
      ext g; simp only [Set.mem_setOf_eq, abs_le]
    rw [hset]; exact h
  -- `Thick ρ` lies in the image of the box
  have hsub : Thick ρ ⊆ mkX '' {g : SL3 | ∀ i j, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C} := by
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hthick : ∀ m : Fin 3 → ℤ, m ≠ 0 →
        ρ ≤ ‖Matrix.mulVec (toMat g) (fun j => (m j : ℝ))‖ := by
      intro m hm
      by_contra hlt
      have hlt' : ‖Matrix.mulVec (g : Matrix (Fin 3) (Fin 3) ℝ) (fun j => (m j : ℝ))‖ < ρ :=
        lt_of_not_ge hlt
      refine hx ⟨g, rfl, m, hm, fun i => lt_of_le_of_lt ?_ hlt'⟩
      simpa [Real.norm_eq_abs] using
        norm_le_pi_norm (Matrix.mulVec (g : Matrix (Fin 3) (Fin 3) ℝ) (fun j => (m j : ℝ))) i
    obtain ⟨A, hAdet, hAbound⟩ :=
      hb (g : Matrix (Fin 3) (Fin 3) ℝ) (Matrix.SpecialLinearGroup.det_coe g) hthick
    set Asl : Matrix.SpecialLinearGroup (Fin 3) ℤ := (⟨A, hAdet⟩ : Matrix.SpecialLinearGroup (Fin 3) ℤ)
      with hAsl
    set Bsl : SL3 := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) Asl with hBsl
    have hAslval : (Asl : Matrix (Fin 3) (Fin 3) ℤ) = A := by
      rw [hAsl, Matrix.SpecialLinearGroup.coe_mk]
    have hBmat : (Bsl : Matrix (Fin 3) (Fin 3) ℝ) = A.map (Int.castRingHom ℝ) := by
      rw [hBsl, Matrix.SpecialLinearGroup.coe_matrix_coe, hAslval]
    have hBΓ : Bsl ∈ Γ3 := MonoidHom.mem_range.mpr ⟨Asl, rfl⟩
    have hBmk : mkX Bsl = mkX 1 :=
      QuotientGroup.eq.mpr (by simpa using Γ3.inv_mem hBΓ)
    refine ⟨g * Bsl, ?_, ?_⟩
    · show ∀ i j, |((g * Bsl : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C
      intro i j
      have hcoe : ((g * Bsl : SL3) : Matrix (Fin 3) (Fin 3) ℝ) =
          (g : Matrix (Fin 3) (Fin 3) ℝ) * (A.map (Int.castRingHom ℝ)) := by
        rw [Matrix.SpecialLinearGroup.coe_mul, hBmat]
      rw [hcoe]
      exact hAbound i j
    · calc mkX (g * Bsl) = g • mkX Bsl := Lemmas.mkX_mul g Bsl
        _ = g • mkX 1 := by rw [hBmk]
        _ = mkX (g * 1) := (Lemmas.mkX_mul g 1).symm
        _ = mkX g := by rw [mul_one]
  exact IsCompact.of_isClosed_subset (hKcpt.image QuotientGroup.continuous_mk)
    (Lemmas.isClosed_Thick ρ) hsub

/-- **Component C2 of the frozen EKL contract.** -/
theorem prove_X3 : Work.EKLContract.P_X3 := by
  refine ⟨t2Space_X3, polishSpace_X3, fun ρ hρ => thick_isCompact ρ hρ, ?_, ?_⟩
  · -- uniform injectivity of the orbit maps on compacta
    intro K hK
    obtain ⟨δ, hδ, huniq⟩ := uniform_inj_of_isCompact K hK
    exact ⟨δ, hδ, fun x hx g hg h hh heq => huniq x hx g h hg hh heq⟩
  · -- openness of the orbit maps
    intro x δ hδ
    exact orbit_image_V_mem_nhds x δ hδ

end

end Work.EKLComp
