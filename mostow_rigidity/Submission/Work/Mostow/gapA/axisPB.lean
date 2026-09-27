import Mathlib
import Submission.Work.Mostow.gapA.axisNormDefs
import Submission.Work.Mostow.gapA.ogAux
import Submission.Work.Mostow.perpNullUnit

/-!
# The orthonormal basis of the normal plane, and the rotation determinant

For two distinct boundary points `a b ∈ Sph 3` (the endpoints of the geodesic `geodSet a b`):

* `exists_PB` produces the positive definite orthonormal basis `PB a b` of the normal plane
  `NormP a b = {⟨·,θ_a⟩ = ⟨·,θ_b⟩ = 0}` together with the spanning statements;
* `rotMat_det` proves that the `2 × 2` matrix of the action of `g ∈ AxisSub hA a b` on the normal
  plane has determinant `1`, i.e. the normal action is a *rotation*: the determinant identity
  `p s - r q = 1` is obtained from the identity `A_σ * C = C * D` of `4 × 4` matrices, where
  `C` is the coordinate matrix of the basis `(θ_a, θ_b, e1, e2)` and `D = fromBlocks 1 0 0 M`.
-/

open _root_.Matrix

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open _root_.Matrix

noncomputable section

variable {a b : E 3}

lemma NormSub_eq_NormP : NormSub a b = NormP a b := by
  ext Z
  rw [mem_NormSub, mem_NormP]

lemma mem_ker_perpMap_iff (Z : Fin 3 ⊕ Fin 1 → ℝ) :
    Z ∈ LinearMap.ker (perpMap a b) ↔ Z ∈ NormSub a b := by
  rw [mem_NormSub]
  constructor
  · intro h
    have h' : (perpMap a b) Z = 0 := (LinearMap.mem_ker).mp h
    refine ⟨?_, ?_⟩
    · rw [mink_eq_mform]
      exact (congrArg Prod.fst h').trans (by simp)
    · rw [mink_eq_mform]
      exact (congrArg Prod.snd h').trans (by simp)
  · rintro ⟨h1, h2⟩
    refine (LinearMap.mem_ker).mpr ?_
    have h1' : mform Z (theta a) = 0 := by rw [← mink_eq_mform]; exact h1
    have h2' : mform Z (theta b) = 0 := by rw [← mink_eq_mform]; exact h2
    change (mform Z (theta a), mform Z (theta b)) = 0
    rw [h1', h2']
    rfl

lemma finrank_NormSub (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) :
    Module.finrank ℝ (NormSub a b) = 2 := by
  have htpart0 : tpart (0 : E 3) = 1 := by
    show Real.sqrt (1 + ‖(0 : E 3)‖ ^ 2) = 1
    rw [norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), add_zero, Real.sqrt_one]
  have htparta : tpart a = Real.sqrt 2 := by
    show Real.sqrt (1 + ‖a‖ ^ 2) = Real.sqrt 2
    rw [(mem_Sph_iff a).mp ha]
    norm_num
  have hr1 : (perpMap a b) (hlift (0 : E 3)) = (-1, -1) := by
    change (mform (hlift (0 : E 3)) (theta a), mform (hlift (0 : E 3)) (theta b)) = (-1, -1)
    rw [mform_hlift_theta', mform_hlift_theta', htpart0]
    simp
  have hr2 : (perpMap a b) (hlift a) = (1 - Real.sqrt 2, inner ℝ a b - Real.sqrt 2) := by
    change (mform (hlift a) (theta a), mform (hlift a) (theta b))
      = (1 - Real.sqrt 2, inner ℝ a b - Real.sqrt 2)
    rw [mform_hlift_theta', mform_hlift_theta', real_inner_self_eq_norm_sq, (mem_Sph_iff a).mp ha,
      htparta]
    norm_num
  have hli : LinearIndependent ℝ
      ![(perpMap a b) (hlift (0 : E 3)), (perpMap a b) (hlift a)] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hsum : g 0 • (perpMap a b) (hlift (0 : E 3)) + g 1 • (perpMap a b) (hlift a) = 0 := by
      have h := hg
      rwa [Fin.sum_univ_two] at h
    rw [hr1, hr2] at hsum
    have h1 : g 0 * (-1) + g 1 * (1 - Real.sqrt 2) = 0 := by
      have h := congrArg Prod.fst hsum
      simpa [Prod.smul_fst, Prod.fst_add, smul_eq_mul] using h
    have h2 : g 0 * (-1) + g 1 * (inner ℝ a b - Real.sqrt 2) = 0 := by
      have h := congrArg Prod.snd hsum
      simpa [Prod.smul_snd, Prod.snd_add, smul_eq_mul] using h
    have hc : (1 : ℝ) - inner ℝ a b ≠ 0 := by
      intro hh
      have h4 : inner ℝ a b < 1 :=
        inner_lt_one_of_ne_unit ((mem_Sph_iff a).mp ha) ((mem_Sph_iff b).mp hb) hab
      linarith
    have hg1 : g 1 = 0 := by
      have hdiff : (1 - inner ℝ a b) * g 1 = 0 := by linarith only [h1, h2]
      exact (mul_eq_zero.mp hdiff).resolve_left hc
    have hg0 : g 0 = 0 := by
      rw [hg1, zero_mul, add_zero] at h1
      linarith
    fin_cases i
    · exact hg0
    · exact hg1
  have hcard : Module.finrank ℝ
      (Submodule.span ℝ (Set.range ![(perpMap a b) (hlift (0 : E 3)),
        (perpMap a b) (hlift a)])) = 2 := by
    rw [finrank_span_eq_card hli]
    simp
  have hrange_le : Submodule.span ℝ (Set.range ![(perpMap a b) (hlift (0 : E 3)),
      (perpMap a b) (hlift a)]) ≤ (perpMap a b).range := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact ⟨hlift (0 : E 3), rfl⟩
    · exact ⟨hlift a, rfl⟩
  have hge : 2 ≤ Module.finrank ℝ (perpMap a b).range := by
    rw [← hcard]
    exact Submodule.finrank_mono hrange_le
  have hle : Module.finrank ℝ (perpMap a b).range ≤ 2 := by
    have h := Submodule.finrank_le ((perpMap a b).range)
    have h2 : Module.finrank ℝ (ℝ × ℝ) = 2 := by
      rw [Module.finrank_prod, Module.finrank_self]
    rw [h2] at h
    exact h
  have hrange : Module.finrank ℝ (perpMap a b).range = 2 := le_antisymm hle hge
  have hrk := LinearMap.finrank_range_add_finrank_ker (perpMap a b)
  rw [hrange] at hrk
  have hV : Module.finrank ℝ (Fin 3 ⊕ Fin 1 → ℝ) = 4 := by simp
  rw [hV] at hrk
  have hker : NormSub a b = LinearMap.ker (perpMap a b) := by
    ext Z; rw [mem_ker_perpMap_iff]
  rw [hker]
  omega

/-! ## Existence of the orthonormal basis -/

theorem existsAxisBasis (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) :
    Nonempty (AxisBasis a b) := by
  obtain ⟨W, hWa, hWb, hWW⟩ := perpNullUnit (n := 3) (by norm_num) ha hb hab
  have hWmem : W ∈ NormSub a b := by
    refine ⟨?_, ?_⟩
    · rw [mink_eq_mform]; exact hWa
    · rw [mink_eq_mform]; exact hWb
  have hWnorm : mink W W = 1 := by rw [mink_eq_mform]; exact hWW
  let f : NormSub a b →ₗ[ℝ] ℝ :=
    { toFun := fun Z => mink (Z : Fin 3 ⊕ Fin 1 → ℝ) W
      map_add' := fun x y => by simp [minkSeg_add_left]
      map_smul' := fun c x => by simp [mink_smul_left''] }
  have hfker : LinearMap.ker f ≠ ⊥ := by
    refine LinearMap.ker_ne_bot_of_finrank_lt ?_
    rw [finrank_NormSub ha hb hab]
    simp
  obtain ⟨Z₀, hZ₀mem, hZ₀ne⟩ := (Submodule.ne_bot_iff (LinearMap.ker f)).mp hfker
  have hZ₀vec : (Z₀ : Fin 3 ⊕ Fin 1 → ℝ) ≠ 0 := fun h => hZ₀ne (Subtype.ext h)
  have hZ₀orth : mink (Z₀ : Fin 3 ⊕ Fin 1 → ℝ) W = 0 := (LinearMap.mem_ker).mp hZ₀mem
  have hZ₀pos : 0 < mink (Z₀ : Fin 3 ⊕ Fin 1 → ℝ) Z₀ := by
    rcases lt_or_eq_of_le (mink_nonneg_of_mem_NormSub ha Z₀.2) with h | h
    · exact h
    · exact absurd (eq_zero_of_mem_NormSub_of_mink_self_eq_zero ha hb hab Z₀.2 h.symm) hZ₀vec
  set c : ℝ := (Real.sqrt (mink (Z₀ : Fin 3 ⊕ Fin 1 → ℝ) Z₀))⁻¹ with hcdef
  set E2 : Fin 3 ⊕ Fin 1 → ℝ := c • (Z₀ : Fin 3 ⊕ Fin 1 → ℝ) with hE2def
  have hE2mem : E2 ∈ NormSub a b := (NormSub a b).smul_mem c Z₀.2
  have hc2 : c * c = (mink (Z₀ : Fin 3 ⊕ Fin 1 → ℝ) Z₀)⁻¹ := by
    rw [hcdef, ← mul_inv, ← sq, Real.sq_sqrt (le_of_lt hZ₀pos)]
  have hE2norm : mink E2 E2 = 1 := by
    rw [hE2def, mink_smul_left'', mink_smul_right'', ← mul_assoc, hc2,
      inv_mul_cancel₀ (ne_of_gt hZ₀pos)]
  have hE2orth : mink E2 W = 0 := by
    rw [hE2def, mink_smul_left'', hZ₀orth, mul_zero]
  have hWE2 : mink W E2 = 0 := by rw [minkSeg_comm]; exact hE2orth
  have hspan : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Z ∈ NormSub a b →
      ∃ α β : ℝ, Z = α • W + β • E2 := by
    intro Z hZ
    have hli : LinearIndependent ℝ
        ![(⟨W, hWmem⟩ : NormSub a b), (⟨E2, hE2mem⟩ : NormSub a b)] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have hsum : g 0 • (⟨W, hWmem⟩ : NormSub a b) + g 1 • (⟨E2, hE2mem⟩ : NormSub a b) = 0 := by
        have h := hg
        rwa [Fin.sum_univ_two] at h
      have h1 : g 0 = 0 := by
        have hpair : mink (g 0 • W + g 1 • E2) W = 0 := by
          have h := congrArg (fun x : NormSub a b => (x : Fin 3 ⊕ Fin 1 → ℝ)) hsum
          have hW : g 0 • W + g 1 • E2 = 0 := by simpa using h
          rw [hW]; simp [mink]
        simp only [minkSeg_add_left, mink_smul_left'', hWnorm, hE2orth, mul_one, mul_zero,
          zero_add, add_zero] at hpair
        exact hpair
      have h2 : g 1 = 0 := by
        have hpair : mink (g 0 • W + g 1 • E2) E2 = 0 := by
          have h := congrArg (fun x : NormSub a b => (x : Fin 3 ⊕ Fin 1 → ℝ)) hsum
          have hW : g 0 • W + g 1 • E2 = 0 := by simpa using h
          rw [hW]; simp [mink]
        simp only [minkSeg_add_left, mink_smul_left'', hWE2, hE2norm, mul_one, mul_zero,
          zero_add, add_zero] at hpair
        exact hpair
      fin_cases i
      · exact h1
      · exact h2
    have htop : Submodule.span ℝ (Set.range ![(⟨W, hWmem⟩ : NormSub a b),
        (⟨E2, hE2mem⟩ : NormSub a b)]) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_eq_card hli, finrank_NormSub ha hb hab]
      simp
    have hmem : (⟨Z, hZ⟩ : NormSub a b) ∈
        Submodule.span ℝ (Set.range ![(⟨W, hWmem⟩ : NormSub a b),
          (⟨E2, hE2mem⟩ : NormSub a b)]) := by
      rw [htop]; trivial
    have hrange : Set.range ![(⟨W, hWmem⟩ : NormSub a b), (⟨E2, hE2mem⟩ : NormSub a b)]
        = ({(⟨W, hWmem⟩ : NormSub a b), (⟨E2, hE2mem⟩ : NormSub a b)} : Set (NormSub a b)) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ rfl
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    rw [hrange, Submodule.mem_span_pair] at hmem
    obtain ⟨α, β, hαβ⟩ := hmem
    refine ⟨α, β, ?_⟩
    have h := congrArg (fun x : NormSub a b => (x : Fin 3 ⊕ Fin 1 → ℝ)) hαβ
    simpa using h.symm
  have hspanV : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, ∃ α β γ δ : ℝ,
      Z = α • nvec a + β • nvec b + γ • W + δ • E2 := by
    intro Z
    set D : ℝ := mink (nvec a) (nvec b) with hDdef
    have hDne : D ≠ 0 := by rw [hDdef]; exact mink_nvec_pair_ne_zero ha hb hab
    have hNmem : Z - (mink Z (nvec b) / D) • nvec a - (mink Z (nvec a) / D) • nvec b
        ∈ NormSub a b := by
      refine ⟨?_, ?_⟩
      · have hb_a : mink (nvec b) (nvec a) = D := by rw [minkSeg_comm, hDdef]
        simp only [mink_sub_left', mink_smul_left'', mink_nvec_self' ha, hb_a, mul_zero,
          sub_zero, div_mul_cancel₀ (mink Z (nvec a)) hDne, sub_self]
      · have hab_b : mink (nvec a) (nvec b) = D := hDdef.symm
        simp only [mink_sub_left', mink_smul_left'', mink_nvec_self' hb, hab_b, mul_zero,
          sub_zero, div_mul_cancel₀ (mink Z (nvec b)) hDne, sub_self]
    obtain ⟨γ, δ, hγδ⟩ := hspan _ hNmem
    refine ⟨mink Z (nvec b) / D, mink Z (nvec a) / D, γ, δ, ?_⟩
    calc Z = (Z - (mink Z (nvec b) / D) • nvec a - (mink Z (nvec a) / D) • nvec b)
            + (mink Z (nvec b) / D) • nvec a + (mink Z (nvec a) / D) • nvec b := by abel
      _ = (γ • W + δ • E2) + (mink Z (nvec b) / D) • nvec a
            + (mink Z (nvec a) / D) • nvec b := by rw [hγδ]
      _ = (mink Z (nvec b) / D) • nvec a + (mink Z (nvec a) / D) • nvec b + γ • W
            + δ • E2 := by abel

  exact ⟨{ E1 := W, E2 := E2, mem1 := hWmem, mem2 := hE2mem, n11 := hWnorm, n22 := hE2norm,
           n12 := hWE2, span := hspan, spanV := hspanV }⟩

theorem exists_PB (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) : Nonempty (PB a b) := by
  obtain ⟨B⟩ := existsAxisBasis (a := a) (b := b) ha hb hab
  refine ⟨⟨B.E1, B.E2, ?_, ?_, B.n11, B.n22, B.n12, ?_, ?_⟩⟩
  · rw [← NormSub_eq_NormP]; exact B.mem1
  · rw [← NormSub_eq_NormP]; exact B.mem2
  · intro Z hZ; exact B.span Z (by rw [← NormSub_eq_NormP] at hZ; exact hZ)
  · intro Z; exact B.spanV Z

theorem rotMat_det (hA : POActionProp 3) (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b)
    (B : PB a b) (g : PO 3 1) (hg : g ∈ AxisSub hA a b) : (rotMat B g).det = 1 := by
  obtain ⟨hg1, hg2, hgd⟩ := mem_AxisSub_iff.mp hg
  obtain ⟨p, q, hpq⟩ := B.span (emat g *ᵥ B.e1) (emat_mem_NormP_of_mem hA B hg B.mem1)
  obtain ⟨r, s, hrs⟩ := B.span (emat g *ᵥ B.e2) (emat_mem_NormP_of_mem hA B hg B.mem2)
  have hp : p = rot00 B g := by
    rw [rot00, hpq]
    simp only [minkSeg_add_left, mink_smul_left'', B.n11, minkSeg_comm B.e2 B.e1, B.n12,
      mul_one, mul_zero, add_zero, zero_add]
  have hq : q = rot10 B g := by
    rw [rot10, hpq]
    simp only [minkSeg_add_left, mink_smul_left'', B.n12, B.n22, mul_one, mul_zero, add_zero, zero_add]
  have hr : r = rot01 B g := by
    rw [rot01, hrs]
    simp only [minkSeg_add_left, mink_smul_left'', B.n11, minkSeg_comm B.e2 B.e1, B.n12,
      mul_one, mul_zero, add_zero, zero_add]
  have hs : s = rot11 B g := by
    rw [rot11, hrs]
    simp only [minkSeg_add_left, mink_smul_left'', B.n12, B.n22, mul_one, mul_zero, add_zero, zero_add]
  have hdet : p * s - r * q = 1 := by
    set bv : Fin 2 ⊕ Fin 2 → (Fin 3 ⊕ Fin 1 → ℝ) :=
      Sum.elim ![(nvec a), (nvec b)] ![(B.e1), (B.e2)] with hbv
    set D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
      Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0
        (!![p, r; q, s] : Matrix (Fin 2) (Fin 2) ℝ) with hD
    set σ : Fin 3 ⊕ Fin 1 ≃ Fin 2 ⊕ Fin 2 :=
      (finSumFinEquiv (m := 3) (n := 1)).trans (finSumFinEquiv (m := 2) (n := 2)).symm with hσ
    set Aσ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
      fun i j => (emat g) (σ.symm i) (σ.symm j) with hAσ
    set C : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ := fun i j => bv j (σ.symm i) with hC
    have hAσ_apply : ∀ a b : Fin 2 ⊕ Fin 2, Aσ a b = (emat g) (σ.symm a) (σ.symm b) :=
      fun a b => by rw [hAσ]
    have hC_apply : ∀ a b : Fin 2 ⊕ Fin 2, C a b = bv b (σ.symm a) := fun a b => by rw [hC]
    have hcol : ∀ j : Fin 2 ⊕ Fin 2, Matrix.mulVec (emat g) (bv j) = ∑ l, D l j • bv l := by
      rintro (i | i) <;> fin_cases i <;>
        simp only [hbv, hD, Fintype.sum_sum_type, Fin.sum_univ_two, Sum.elim_inl, Sum.elim_inr,
          cons_val_zero, cons_val_one, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁,
          Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply] <;>
        simp [hg1, hg2, hpq, hrs]
    have hCD : Aσ * C = C * D := by
      ext i j
      have h1 : (Aσ * C) i j = (Matrix.mulVec (emat g) (bv j)) (σ.symm i) := by
        rw [Matrix.mul_apply]
        simp only [hAσ_apply, hC_apply]
        rw [Equiv.sum_comp σ.symm (fun k => (emat g) (σ.symm i) k * (bv j) k)]
        rfl
      have h2 : (C * D) i j = (∑ l, D l j • bv l) (σ.symm i) := by
        rw [Matrix.mul_apply, Finset.sum_apply]
        refine Finset.sum_congr rfl ?_
        intro l _
        rw [hC_apply]
        simp only [Pi.smul_apply]
        ring
      rw [h1, h2, hcol j]
    have hCdet : C.det ≠ 0 := by
      intro h0
      obtain ⟨v, hvne, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
      have hsum : (∑ j, v j • bv j) = 0 := by
        ext k
        obtain ⟨i, rfl⟩ := σ.symm.surjective k
        have h : (C *ᵥ v) i = 0 := by
          have := congrFun hv0 i
          simpa using this
        have h2 : (C *ᵥ v) i = (∑ j, v j • bv j) (σ.symm i) := by
          rw [show (C *ᵥ v) i = ∑ j, C i j * v j from rfl, Finset.sum_apply]
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [hC_apply]
          simp only [Pi.smul_apply]
          ring
        rw [← h2]
        exact h
      have hind : v (Sum.inl 0) • nvec a + v (Sum.inl 1) • nvec b + v (Sum.inr 0) • B.e1
          + v (Sum.inr 1) • B.e2 = 0 := by
        rw [← hsum, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_two]
        simp only [hbv, Sum.elim_inl, Sum.elim_inr, cons_val_zero, cons_val_one]
        abel
      obtain ⟨h1, h2, h3, h4⟩ := indepV B ha hb hab hind
      refine hvne (funext fun j => ?_)
      rcases j with j | j <;> fin_cases j
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    have hDdet : D.det = 1 := by
      have h := congrArg Matrix.det hCD
      simp only [Matrix.det_mul] at h
      have hA : Aσ.det = 1 := by
        have hsub : Aσ = (emat g).submatrix σ.symm σ.symm := by
          ext a b
          rw [hAσ_apply]
          rfl
        rw [hsub, Matrix.det_submatrix_equiv_self σ.symm (emat g), hgd]
      rw [hA, one_mul] at h
      have h2 : C.det * D.det = C.det * 1 := by rw [mul_one]; exact h.symm
      exact mul_left_cancel₀ hCdet h2
    have hMD : (!![p, r; q, s] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
      have hD' : D.det = (1 : Matrix (Fin 2) (Fin 2) ℝ).det
          * (!![p, r; q, s] : Matrix (Fin 2) (Fin 2) ℝ).det := by
        rw [hD]
        exact Matrix.det_fromBlocks_zero₁₂ _ _ _
      rw [hD', Matrix.det_one, one_mul] at hDdet
      exact hDdet
    simpa [Matrix.det_fin_two] using hMD
  have hrot : rotMat B g = !![p, r; q, s] := by
    rw [rotMat, ← hp, ← hq, ← hr, ← hs]
  rw [hrot, Matrix.det_fin_two]
  exact hdet

end
end Work.Mostow.gapA
