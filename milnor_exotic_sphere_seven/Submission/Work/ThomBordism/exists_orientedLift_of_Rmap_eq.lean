import Mathlib
import Submission.Work.ThomBordism.exists_orientedLift_of_close

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Topology Matrix
open Classical

namespace Work.ThomBordism

open Work.PTGeometric
open Work.ThomBordism.Grassmann hiding Amb

/-! ## Linear algebra of the straight-line homotopy on the agreement set

The auxiliary statement here is the one extra piece of mathematics that the variant
`exists_orientedLift_of_Rmap_eq` needs on top of `exists_orientedLift_of_close`: on the set `S`
where the *Riesz projection* of the perturbation agrees with `P` (and not the perturbation
itself), the straight-line homotopy `t ↦ Rmap (P x + t • (symm (Pm x) - P x))` is nevertheless
constant.  This follows from the spectral description of `Phi`: if `Phi A = P` for a self-adjoint
`A`, then `A` preserves the splitting `range P ⊕ ker P`, hence so does `(1-t)•P + t•A`, whose
top spectral cluster is `range P` for every `t ∈ [0,1]`. -/

/-- `symm` is additive. -/
lemma ol_symm_add {n : ℕ} (A B : EndOp n) : symm (A + B) = symm A + symm B := by
  show (2 : ℝ)⁻¹ • (A + B + ContinuousLinearMap.adjoint (A + B))
    = (2 : ℝ)⁻¹ • (A + ContinuousLinearMap.adjoint A)
      + (2 : ℝ)⁻¹ • (B + ContinuousLinearMap.adjoint B)
  rw [map_add]
  module

/-- `symm` is homogeneous. -/
lemma ol_symm_smul {n : ℕ} (c : ℝ) (A : EndOp n) : symm (c • A) = c • symm A := by
  show (2 : ℝ)⁻¹ • (c • A + ContinuousLinearMap.adjoint (c • A))
    = c • ((2 : ℝ)⁻¹ • (A + ContinuousLinearMap.adjoint A))
  rw [map_smul]
  module

/-- `symm` fixes the self-adjoint operators. -/
lemma ol_symm_eq_self_of_adjoint {n : ℕ} {A : EndOp n}
    (h : ContinuousLinearMap.adjoint A = A) : symm A = A := by
  show (2 : ℝ)⁻¹ • (A + ContinuousLinearMap.adjoint A) = A
  rw [h]
  module

private lemma ol_one_sub_abs_le {x : ℝ} : 1 - |x| ≤ |x - 1| := by
  have h5 : (1 : ℝ) - |x| ≤ |1 - x| := by simpa using abs_sub_abs_le_abs_sub (1 : ℝ) x
  rwa [abs_sub_comm (1 : ℝ) x] at h5

/-- The top-cluster indicator `chi` is unchanged when the eigenvalue is moved along the segment
from `chi lam` to `lam`, for a cluster eigenvalue. -/
lemma ol_chi_affine {lam t : ℝ} (hcl : min |lam| |lam - 1| < 1 / 4)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    chi ((1 - t) * chi lam + t * lam) = chi lam := by
  have ht1 : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hbot : |lam| < 1 / 4 ∨ |lam - 1| < 1 / 4 := by
    rcases le_total |lam| |lam - 1| with h3 | h3
    · left; rwa [min_eq_left h3] at hcl
    · right; rwa [min_eq_right h3] at hcl
  have hgeom : ∀ x : ℝ, 1 - |x| ≤ |x - 1| := fun x => ol_one_sub_abs_le
  by_cases h : |lam - 1| < 1 / 2
  · have hchi : chi lam = 1 := by rw [chi, if_pos h]
    have hmem : |lam - 1| < 1 / 4 := by
      rcases hbot with h' | h'
      · have h4 := hgeom lam
        linarith
      · exact h'
    rw [hchi, mul_one]
    rw [chi, if_pos]
    have hid : 1 - t + t * lam - 1 = t * (lam - 1) := by ring
    rw [hid, abs_mul]
    calc |t| * |lam - 1| ≤ 1 * |lam - 1| := mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
      _ = |lam - 1| := one_mul _
      _ < 1 / 2 := h
  · have hchi : chi lam = 0 := by rw [chi, if_neg h]
    rw [hchi, mul_zero, zero_add]
    rw [chi, if_neg]
    have hmem : |lam| < 1 / 4 := by
      rcases hbot with h' | h'
      · exact h'
      · exact absurd h' (by linarith)
    have hone : |t * lam| ≤ |lam| := by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) ht1
    intro hc
    have h4 := hgeom (t * lam)
    linarith

/-- **The Riesz projection is constant along the segment from a projection to a self-adjoint
operator whose top cluster is that projection.**  If `P` is a rank-`k` orthogonal projection, `A`
is self-adjoint with `Phi A = P` (and `‖A - P‖ < 1/4`, which is automatic from the cluster
condition), then `Phi` of every point of the segment `t ↦ (1-t)•P + t•A` (`t ∈ [0,1]`) is `P`
again. -/
theorem ol_Phi_smul_line {n k : ℕ} {P A : EndOp n} (hP : P ∈ Gr n k) (hAdist : ‖A - P‖ < 1 / 4)
    (hAsym : (A : Amb n →ₗ[ℝ] Amb n).IsSymmetric) (hPA : Phi A = P)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Phi (symm (P + t • (A - P))) = P := by
  have hn : Module.finrank ℝ (Amb n) = n := finrank_amb n
  have hAc : Cluster A := Cluster.of_dist hP hAdist
  set B : EndOp n := symm (P + t • (A - P)) with hBdef
  have hB_eq : B = (1 - t) • P + t • A := by
    rw [hBdef]
    have h1 : P + t • (A - P) = (1 - t) • P + t • A := by module
    rw [h1, ol_symm_add, ol_symm_smul, ol_symm_smul, symm_eq_self_of_mem_Gr hP,
      ol_symm_eq_self_of_adjoint (LinearMap.IsSymmetric.clm_adjoint_eq hAsym)]
  have hBsym : (B : Amb n →ₗ[ℝ] Amb n).IsSymmetric := by
    rw [hBdef]; exact symm_isSymmetric _
  have hBc : Cluster B := by
    refine Cluster.of_dist hP ?_
    have h : B - P = t • (A - P) := by rw [hB_eq]; module
    rw [h]
    rw [norm_smul, Real.norm_eq_abs]
    calc |t| * ‖A - P‖ ≤ 1 * ‖A - P‖ :=
          mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩) (norm_nonneg _)
      _ = ‖A - P‖ := one_mul _
      _ < 1 / 4 := hAdist
  have hBvp : ∀ i : Fin n, Phi B (hAsym.eigenvectorBasis hn i)
      = chi (hAsym.eigenvalues hn i) • hAsym.eigenvectorBasis hn i := by
    intro i
    have hvne : hAsym.eigenvectorBasis hn i ≠ 0 :=
      (hAsym.eigenvectorBasis hn).orthonormal.ne_zero i
    have hPv : P (hAsym.eigenvectorBasis hn i)
        = chi (hAsym.eigenvalues hn i) • hAsym.eigenvectorBasis hn i := by
      have h := Phi_apply_eigenbasis hAsym hAc hn i
      rwa [hPA] at h
    have hAv : A (hAsym.eigenvectorBasis hn i)
        = hAsym.eigenvalues hn i • hAsym.eigenvectorBasis hn i :=
      hAsym.apply_eigenvectorBasis hn i
    have hBv : B (hAsym.eigenvectorBasis hn i)
        = ((1 - t) * chi (hAsym.eigenvalues hn i) + t * hAsym.eigenvalues hn i)
            • hAsym.eigenvectorBasis hn i := by
      rw [hB_eq]
      rw [add_apply, smul_apply, smul_apply, hPv, hAv, smul_smul, smul_smul, ← add_smul]
    have hchi : chi ((1 - t) * chi (hAsym.eigenvalues hn i) + t * hAsym.eigenvalues hn i)
        = chi (hAsym.eigenvalues hn i) :=
      ol_chi_affine (hAc _ (hAsym.hasEigenvalue_eigenvalues hn i)) ht
    have hlam : Module.End.HasEigenvalue (B : Amb n →ₗ[ℝ] Amb n)
        ((1 - t) * chi (hAsym.eigenvalues hn i) + t * hAsym.eigenvalues hn i) :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hBv, hvne⟩
    have h2 : Phi B (hAsym.eigenvectorBasis hn i)
        = chi ((1 - t) * chi (hAsym.eigenvalues hn i) + t * hAsym.eigenvalues hn i)
            • hAsym.eigenvectorBasis hn i :=
      Phi_apply_eigen B hBsym hBc hvne _ hlam hBv
    rwa [hchi] at h2
  refine ContinuousLinearMap.ext fun x => ?_
  have h1 : Phi B x
      = ∑ i, (chi (hAsym.eigenvalues hn i) * inner ℝ (hAsym.eigenvectorBasis hn i) x)
          • hAsym.eigenvectorBasis hn i := by
    conv_lhs => rw [← sum_repr_inner hAsym hn x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, hBvp i, smul_smul, mul_comm]
  have h2 : P x = ∑ i, (chi (hAsym.eigenvalues hn i)
        * inner ℝ (hAsym.eigenvectorBasis hn i) x) • hAsym.eigenvectorBasis hn i := by
    rw [← hPA]
    exact Phi_apply_eq hAsym hAc hn x
  rw [h1, h2]

/-- **The straight-line homotopy of `Rmap (Pm ·)` is constant where the Riesz projection of the
perturbation already agrees with `P`.** -/
theorem olQ_eq_of_Rmap_eq {k m : ℕ} {M : Type} {P Pm : M → EndOp (k + m)}
    (hProj : ∀ x, P x ∈ Gr (k + m) k) (hPm : ∀ x, ‖Pm x - P x‖ < 1 / 8)
    {x : M} (hx : Rmap (Pm x) = P x) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    olQ k m P Pm x t = P x := by
  have hAdist : ‖symm (Pm x) - P x‖ < 1 / 4 := by
    have h1 : symm (Pm x) - P x = symm (Pm x) - symm (P x) := by
      rw [symm_eq_self_of_mem_Gr (hProj x)]
    rw [h1]
    linarith [norm_symm_sub_le (Pm x) (P x), hPm x]
  show Phi (symm (P x + t • (symm (Pm x) - P x))) = P x
  exact ol_Phi_smul_line (hP := hProj x) hAdist (symm_isSymmetric (Pm x)) hx ht

theorem exists_orientedLift_of_Rmap_eq (k m : ℕ) {M : Type} [TopologicalSpace M]
    (P : M → Work.PTGeometric.Amb (k + m) →L[ℝ] Work.PTGeometric.Amb (k + m))
    (hPc : Continuous P) (hProj : ∀ x, P x ∈ Work.PTGeometric.Gr (k + m) k)
    (G : M → Work.ThomBordism.Grassmann.OG k m) (hGc : Continuous G)
    (hG : ∀ x, Work.PTGeometric.projOfPlane k m (G x) = P x)
    (Pm : M → Work.PTGeometric.Amb (k + m) →L[ℝ] Work.PTGeometric.Amb (k + m))
    (hPmc : Continuous Pm) (hPm : ∀ x, ‖Pm x - P x‖ < 1 / 8)
    (S : Set M) (hSP : ∀ x ∈ S, Work.PTGeometric.Rmap (Pm x) = P x) :
    ∃ G' : M → Work.ThomBordism.Grassmann.OG k m, Continuous G' ∧
      (∀ x, Work.PTGeometric.projOfPlane k m (G' x) = Work.PTGeometric.Rmap (Pm x)) ∧
      (∀ x ∈ S, G' x = G x) := by
  classical
  by_cases hk : k = 0
  · subst hk
    refine ⟨G, hGc, ?_, fun x _ => rfl⟩
    intro x
    have hg : Rmap (Pm x) ∈ Gr (0 + m) 0 := by
      rw [← olQ_one 0 m P Pm x]
      exact olQ_mem 0 m hProj hPm x (by norm_num)
    rw [hG x, ol_eq_zero_of_mem_Gr_zero (hProj x), ol_eq_zero_of_mem_Gr_zero hg]
  by_cases hm : m = 0
  · subst hm
    refine ⟨G, hGc, ?_, fun x _ => rfl⟩
    intro x
    have hg : Rmap (Pm x) ∈ Gr (k + 0) (k + 0) := by
      rw [← olQ_one k 0 P Pm x]
      exact olQ_mem k 0 hProj hPm x (by norm_num)
    rw [hG x, ol_eq_one_of_mem_Gr_self (hProj x), ol_eq_one_of_mem_Gr_self hg]
  -- main case
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  set US : ChartIdx k m → Set M := fun A => {x | G x ∈ baseSet A} with hUS
  have hUSopen : ∀ A, IsOpen (US A) := fun A => (isOpen_baseSet A).preimage hGc
  set Qh : M × ↥(Set.Icc (0 : ℝ) 1) → EndOp (k + m) :=
    fun p => olQ k m P Pm p.1 (p.2 : ℝ) with hQh
  have hQhc : Continuous Qh := olQ_continuous k m hPc hPmc hProj hPm
  have hQhmem : ∀ p, Qh p ∈ Gr (k + m) k := fun p =>
    olQ_mem k m hProj hPm p.1 (abs_le_one_of_mem_Icc p.2.2)
  -- the local data on each chart
  have hloc : ∀ A : ChartIdx k m, ∃ F : ↥(US A) × ↥(Set.Icc (0 : ℝ) 1) → OG k m,
      Continuous F ∧ (∀ p, projOfPlane k m (F p) = Qh (p.1.1, p.2)) ∧
      (∀ x hx, F (⟨x, hx⟩, ⟨0, by norm_num⟩) = G x) := by
    intro A
    have hGp : Continuous fun p : ↥(US A) × ↥(Set.Icc (0 : ℝ) 1) => G p.1.1 :=
      hGc.comp (continuous_subtype_val.comp continuous_fst)
    have hγfun : Continuous fun p : ↥(US A) × ↥(Set.Icc (0 : ℝ) 1) =>
        (⟨G p.1.1, p.1.2⟩ : ↥(baseSet A)) :=
      Continuous.subtype_mk (f := fun p : ↥(US A) × ↥(Set.Icc (0 : ℝ) 1) => G p.1.1) hGp
        (fun p => p.1.2)
    let γ : ↥(US A) × ↥(Set.Icc (0 : ℝ) 1) → ↥(baseSet A) := fun p => ⟨G p.1.1, p.1.2⟩
    have hγ : Continuous γ := hγfun
    let Q' : ↥(US A) × ↥(Set.Icc (0 : ℝ) 1) → EndOp (k + m) := fun p => Qh (p.1.1, p.2)
    have hQ'c : Continuous Q' :=
      hQhc.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    have hinj : ∀ p, ∀ v ∈ Submodule.span ℝ (Set.range ((olCFS k m A (γ p)).1)),
        Q' p v = 0 → v = 0 := by
      intro p v hv hQv
      have hspan : Submodule.span ℝ (Set.range ((olCFS k m A (γ p)).1))
          = LinearMap.range (P p.1.1 : Amb (k + m) →ₗ[ℝ] Amb (k + m)) := by
        have h1 : frameProj (olCF k m A (γ p)) = P p.1.1 := by
          have h2 : frameProj (olCF k m A (γ p))
              = projOfPlane k m (ogMk k m (olCFS k m A (γ p))) :=
            (projOfPlane_mk k m (olCFS k m A (γ p))).symm
          rw [h2, olCFS_proj k m A (γ p)]
          exact hG p.1.1
        have hfr : Submodule.span ℝ (Set.range ((olCFS k m A (γ p)).1))
            = LinearMap.range (frameProj (olCF k m A (γ p)) :
                Amb (k + m) →ₗ[ℝ] Amb (k + m)) :=
          (frameProj_range (olCF_orthonormal k m A (γ p))).symm
        rw [hfr, h1]
      have hv' : P p.1.1 v = v := by
        have hv2 : v ∈ LinearMap.range (P p.1.1 : Amb (k + m) →ₗ[ℝ] Amb (k + m)) := by
          rw [← hspan]; exact hv
        obtain ⟨u, hu⟩ := hv2
        rw [← hu]
        exact mem_Gr_apply_apply (hProj p.1.1) u
      exact ol_inj_of_homotopy k m hProj hPm p.1.1 (abs_le_one_of_mem_Icc p.2.2) hv' hQv
    refine ⟨olLocCand k m A γ Q' hinj, ?_, ?_, ?_⟩
    · exact olLocCand_continuous k m hkpos A γ hγ hQ'c hinj
    · intro p
      exact olLocCand_proj k m A γ (fun p => hQhmem (p.1.1, p.2)) hinj p
    · intro x hx
      refine olLocCand_start k m A γ hinj ?_
      show Q' (⟨x, hx⟩, ⟨0, by norm_num⟩) = projOfPlane k m (↑(γ (⟨x, hx⟩, ⟨0, by norm_num⟩)))
      rw [show Q' (⟨x, hx⟩, ⟨0, by norm_num⟩) = P x from olQ_zero k m hProj x]
      exact (hG x).symm
  choose F hFc hFproj hF0 using hloc
  -- the local maps agree on the overlaps
  have hagree : ∀ (A B : ChartIdx k m) (x : M) (hxA : x ∈ US A) (hxB : x ∈ US B),
      F A (⟨x, hxA⟩, ⟨1, by norm_num⟩) = F B (⟨x, hxB⟩, ⟨1, by norm_num⟩) := by
    intro A B x hxA hxB
    have ha : Continuous fun t : ↥(Set.Icc (0 : ℝ) 1) => F A (⟨x, hxA⟩, t) :=
      (hFc A).comp (continuous_const.prodMk continuous_id)
    have hb : Continuous fun t : ↥(Set.Icc (0 : ℝ) 1) => F B (⟨x, hxB⟩, t) :=
      (hFc B).comp (continuous_const.prodMk continuous_id)
    have hab : ∀ t : ↥(Set.Icc (0 : ℝ) 1),
        projOfPlane k m (F A (⟨x, hxA⟩, t)) = projOfPlane k m (F B (⟨x, hxB⟩, t)) := by
      intro t
      rw [hFproj A (⟨x, hxA⟩, t), hFproj B (⟨x, hxB⟩, t)]
    have h0 : F A (⟨x, hxA⟩, ⟨0, by norm_num⟩) = F B (⟨x, hxB⟩, ⟨0, by norm_num⟩) := by
      rw [hF0 A x hxA, hF0 B x hxB]
    exact congrFun (ol_path_lift_unique hkpos ha hb hab h0) ⟨1, by norm_num⟩
  -- glue
  obtain ⟨G', hG'c, hG'val⟩ := ol_exists_glue US hUSopen
    (fun x => ⟨chartCover (G x), mem_baseSet_chartCover (G x)⟩)
    (fun A p => F A (p, ⟨1, by norm_num⟩))
    (fun A => (hFc A).comp (continuous_id.prodMk continuous_const))
    (fun A B x hxA hxB => hagree A B x hxA hxB)
  refine ⟨G', hG'c, ?_, ?_⟩
  · intro x
    have hx : x ∈ US (chartCover (G x)) := mem_baseSet_chartCover (G x)
    rw [hG'val (chartCover (G x)) x hx]
    show projOfPlane k m (F (chartCover (G x)) (⟨x, hx⟩, ⟨1, by norm_num⟩)) = Rmap (Pm x)
    rw [hFproj (chartCover (G x)) (⟨x, hx⟩, ⟨1, by norm_num⟩)]
    exact olQ_one k m P Pm x
  · intro x hxS
    have hx : x ∈ US (chartCover (G x)) := mem_baseSet_chartCover (G x)
    rw [hG'val (chartCover (G x)) x hx]
    have hconst : ∀ t : ↥(Set.Icc (0 : ℝ) 1), Qh (x, t) = projOfPlane k m (G x) := by
      intro t
      show olQ k m P Pm x (t : ℝ) = projOfPlane k m (G x)
      rw [olQ_eq_of_Rmap_eq hProj hPm (hSP x hxS) t.2, hG x]
    have ha : Continuous fun t : ↥(Set.Icc (0 : ℝ) 1) =>
        F (chartCover (G x)) (⟨x, hx⟩, t) :=
      (hFc (chartCover (G x))).comp (continuous_const.prodMk continuous_id)
    have hab : ∀ t : ↥(Set.Icc (0 : ℝ) 1),
        projOfPlane k m (F (chartCover (G x)) (⟨x, hx⟩, t)) = projOfPlane k m (G x) := by
      intro t
      rw [hFproj (chartCover (G x)) (⟨x, hx⟩, t), hconst t]
    have h0 : F (chartCover (G x)) (⟨x, hx⟩, ⟨0, by norm_num⟩) = G x :=
      hF0 (chartCover (G x)) x hx
    exact congrFun (ol_path_lift_unique hkpos ha continuous_const hab h0) ⟨1, by norm_num⟩

end Work.ThomBordism
