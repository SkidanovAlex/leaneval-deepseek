import Mathlib
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.continuous_graphProj_recipProj
import Submission.Work.KT.homotopy_inv

namespace Work.KT.Fund

noncomputable section

open _root_.Matrix

/-- The boundary restriction `C(X × D, ℂ) → C(X × S¹, ℂ)` is `ℝ`-linear. -/
lemma bdryRestrict_smul_real (X : Type) [TopologicalSpace X] (r : ℝ)
    (f : C(X × Ball ℂ, ℂ)) : bdryRestrict X (r • f) = r • bdryRestrict X f := by
  ext p; simp [bdryRestrict_apply, Algebra.smul_def]

/-- `pairMat` does not depend on the proof of boundary agreement (a proposition). -/
lemma pairMat_congr (X : Type) [TopologicalSpace X] {ι : Type}
    (M₀ M₁ : Matrix ι ι C(X × Ball ℂ, ℂ))
    (h h' : M₀.map (fun f => bdryRestrict X f) = M₁.map (fun f => bdryRestrict X f)) :
    pairMat X M₀ M₁ h = pairMat X M₀ M₁ h' := by
  apply Matrix.ext
  intro i j
  rfl

/-- `clutchIdem` is independent of the two boundary-agreement proofs (propositions). -/
lemma clutchIdem_proof_irrel (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    {F G : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)}
    (hF hF' : F.map (fun f => bdryRestrict X f)
      = (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (hG hG' : G.map (fun f => bdryRestrict X f)
      = ((u⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
          Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))) :
    clutchIdem X n u F G hF hG = clutchIdem X n u F G hF' hG' := by
  unfold clutchIdem
  congr 1

/-- `clutchIdem` only depends on the lifts `F`, `G` themselves, up to the equality of lifts. -/
lemma clutchIdem_congr_args (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    {F₁ F₂ G₁ G₂ : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)}
    (hF₁ : F₁.map (fun f => bdryRestrict X f)
      = (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (hF₂ : F₂.map (fun f => bdryRestrict X f)
      = (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (hG₁ : G₁.map (fun f => bdryRestrict X f)
      = ((u⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
          Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (hG₂ : G₂.map (fun f => bdryRestrict X f)
      = ((u⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
          Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (eF : F₁ = F₂) (eG : G₁ = G₂) :
    clutchIdem X n u F₁ G₁ hF₁ hG₁ = clutchIdem X n u F₂ G₂ hF₂ hG₂ := by
  subst eF
  subst eG
  exact clutchIdem_proof_irrel X n u hF₁ hF₂ hG₁ hG₂

theorem kappa_indep (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (F F' G G' : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (hF : F.map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (hF' : F'.map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (hG : G.map (fun f => Work.KT.Fund.bdryRestrict X f)
      = ((u⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
          Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (hG' : G'.map (fun f => Work.KT.Fund.bdryRestrict X f)
      = ((u⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
          Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))) :
    Work.KT.cls (Work.KT.Fund.clutchIdem X n u F G hF hG)
      = Work.KT.cls (Work.KT.Fund.clutchIdem X n u F' G' hF' hG') := by
  -- Straight-line interpolation between the two chosen lifts.
  let Fp : unitInterval → Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
    fun t => F + (t : ℝ) • (F' - F)
  let Gp : unitInterval → Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
    fun t => G + (t : ℝ) • (G' - G)
  -- The interpolated matrices are lifts of `u` and `u⁻¹` for every `t`.
  have hFp : ∀ t : unitInterval, (Fp t).map (fun f => bdryRestrict X f)
      = (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
    intro t
    show (F + (t : ℝ) • (F' - F)).map (fun f => bdryRestrict X f) = _
    rw [Matrix.map_add (⇑(bdryRestrict X)) (fun a b => map_add (bdryRestrict X) a b),
        Matrix.map_smul (⇑(bdryRestrict X)) (t : ℝ)
          (fun a => bdryRestrict_smul_real X (t : ℝ) a),
        Matrix.map_sub (⇑(bdryRestrict X)) (fun a b => map_sub (bdryRestrict X) a b),
        hF, hF']
    simp
  have hGp : ∀ t : unitInterval, (Gp t).map (fun f => bdryRestrict X f)
      = ((u⁻¹ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
          Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
    intro t
    show (G + (t : ℝ) • (G' - G)).map (fun f => bdryRestrict X f) = _
    rw [Matrix.map_add (⇑(bdryRestrict X)) (fun a b => map_add (bdryRestrict X) a b),
        Matrix.map_smul (⇑(bdryRestrict X)) (t : ℝ)
          (fun a => bdryRestrict_smul_real X (t : ℝ) a),
        Matrix.map_sub (⇑(bdryRestrict X)) (fun a b => map_sub (bdryRestrict X) a b),
        hG, hG']
    simp
  have hFp_zero : Fp 0 = F := by simp [Fp]
  have hFp_one : Fp 1 = F' := by simp [Fp]
  have hGp_zero : Gp 0 = G := by simp [Gp]
  have hGp_one : Gp 1 = G' := by simp [Gp]
  -- Continuity of the interpolated lifts.
  have hFp_cont : Continuous Fp := by
    show Continuous (fun t : unitInterval => F + (t : ℝ) • (F' - F))
    apply Continuous.add continuous_const
    exact continuous_subtype_val.smul continuous_const
  have hGp_cont : Continuous Gp := by
    show Continuous (fun t : unitInterval => G + (t : ℝ) • (G' - G))
    apply Continuous.add continuous_const
    exact continuous_subtype_val.smul continuous_const
  -- Continuity of the two projection families.
  have hgp : Continuous
      (fun t : unitInterval => graphProj C(X × Ball ℂ, ℂ) (Fp t)) :=
    (continuous_graphProj_recipProj (X × Ball ℂ) n).1.comp hFp_cont
  have hrp : Continuous
      (fun t : unitInterval => recipProj C(X × Ball ℂ, ℂ) (Gp t)) :=
    (continuous_graphProj_recipProj (X × Ball ℂ) n).2.comp hGp_cont
  -- The path of clutched idempotents.
  let γ : unitInterval → Matrix (Fin (n + n)) (Fin (n + n)) ↥(pullAlg2 X) :=
    fun t => Matrix.reindex finSumFinEquiv finSumFinEquiv
      (pairMat X (graphProj C(X × Ball ℂ, ℂ) (Fp t))
        (recipProj C(X × Ball ℂ, ℂ) (Gp t))
        (clutch_agree X n u (Fp t) (Gp t) (hFp t) (hGp t)))
  have hγ_cont : Continuous γ := by
    apply Continuous.matrix_reindex
    apply continuous_matrix
    intro i j
    simp only [pairMat, mkPair]
    refine Continuous.subtype_mk ?_ _
    exact (hgp.matrix_elem i j).prodMk (hrp.matrix_elem i j)
  have hγ_idem : ∀ t : unitInterval, γ t * γ t = γ t := fun t =>
    clutchIdem_isIdem X n u (Fp t) (Gp t) (hFp t) (hGp t)
  -- Homotopy invariance of the `K₀`-class.
  have key := homotopy_inv (C(X × Ball ℂ, ℂ) × C(X × Ball ℂ, ℂ)) (pullAlg2 X)
    (isClosed_pullAlg2 X) (n + n) γ hγ_cont hγ_idem
  -- Rewrite the two endpoints, using that `clutchIdem` only depends on the lifts.
  have e0 := clutchIdem_congr_args X n u (hFp 0) hF (hGp 0) hG hFp_zero hGp_zero
  have e1 := clutchIdem_congr_args X n u (hFp 1) hF' (hGp 1) hG' hFp_one hGp_one
  have h0 : (⟨n + n, γ 0⟩ : Mat ↥(pullAlg2 X)) = clutchIdem X n u F G hF hG := by
    rw [show (⟨n + n, γ 0⟩ : Mat ↥(pullAlg2 X))
        = clutchIdem X n u (Fp 0) (Gp 0) (hFp 0) (hGp 0) from rfl, e0]
  have h1 : (⟨n + n, γ 1⟩ : Mat ↥(pullAlg2 X)) = clutchIdem X n u F' G' hF' hG' := by
    rw [show (⟨n + n, γ 1⟩ : Mat ↥(pullAlg2 X))
        = clutchIdem X n u (Fp 1) (Gp 1) (hFp 1) (hGp 1) from rfl, e1]
  rw [← h0, ← h1]
  exact key

end

end Work.KT.Fund
