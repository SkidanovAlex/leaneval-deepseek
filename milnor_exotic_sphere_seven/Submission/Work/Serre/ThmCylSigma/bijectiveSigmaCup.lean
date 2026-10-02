import Mathlib
import Submission.Work.Serre.ThmCylSigma.Main
import Submission.Work.Serre.ThmCylSigma.Assembly

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre.ThmCylSigma

theorem bijectiveSigmaCup {ι : Type} {B Y : ι → Type} [∀ i, TopologicalSpace (B i)]
    [∀ i, TopologicalSpace (Y i)]
    (A : ∀ i, Set (Y i)) (π : ∀ i, C(Y i, B i)) (n N : ℕ) (hn : 0 < n)
    (Uσ : Work.Thom.RelCoh ℚ n (Σ i, Y i) (Work.Serre.Sigma.sigmaSet A))
    (U : ∀ i, Work.Thom.RelCoh ℚ n (Y i) (A i))
    (hrestr : ∀ i, (Work.Thom.relCohMap (Work.Serre.Sigma.pieceIncl (Y := Y) i).hom (A i)
        (Work.Serre.Sigma.sigmaSet A)
        (fun x hx => Work.Serre.Sigma.pieceIncl_mem_sigmaSet A i x hx) ℚ n).hom Uσ = U i)
    (hU : ∀ i k, k + n ≤ N → Function.Bijective (fun x : Work.Thom.Coh ℚ k (B i) =>
      (Work.Thom.mixedCupC ℚ (A i) k n) ((Work.Thom.CohMap (π i) ℚ k).hom x) (U i))) :
    ∀ k, k + n ≤ N → Function.Bijective (fun x : Work.Thom.Coh ℚ k (Σ i, B i) =>
      (Work.Thom.mixedCupC ℚ (Work.Serre.Sigma.sigmaSet A) k n)
        ((Work.Thom.CohMap (Work.Serre.Sigma.sigmaMap π) ℚ k).hom x) Uσ) := by
  classical
  -- the degree `n` is positive, so it is a successor
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  intro k hk
  -- the piecewise cup maps are bijective
  have hΦi : ∀ i, Function.Bijective (fun x : Work.Thom.Coh ℚ k (B i) =>
      (Work.Thom.mixedCupC ℚ (A i) k (r + 1))
        ((Work.Thom.CohMap (π i) ℚ k).hom x) (U i)) := fun i => hU i k hk
  -- the cup map of the `σ`-type
  set Φσ : Work.Thom.Coh ℚ k (Σ i, B i) →ₗ[ℚ]
      Work.Thom.RelCoh ℚ (k + (r + 1)) (Σ i, Y i) (Work.Serre.Sigma.sigmaSet A) :=
    ((Work.Thom.mixedCupC ℚ (Work.Serre.Sigma.sigmaSet A) k (r + 1)).flip Uσ) ∘ₗ
      (Work.Thom.CohMap (Work.Serre.Sigma.sigmaMap π) ℚ k).hom with hΦσdef
  have hΦσ_apply : ∀ x : Work.Thom.Coh ℚ k (Σ i, B i), Φσ x =
      (Work.Thom.mixedCupC ℚ (Work.Serre.Sigma.sigmaSet A) k (r + 1))
        ((Work.Thom.CohMap (Work.Serre.Sigma.sigmaMap π) ℚ k).hom x) Uσ := fun x => by
    simp only [hΦσdef, LinearMap.comp_apply, LinearMap.flip_apply]
  -- the restriction of the `σ`-type cup map
  have hkey : ∀ (i : ι) (x : Work.Thom.Coh ℚ k (Σ i, B i)),
      (Work.Thom.relCohMap (Work.Serre.Sigma.pieceIncl (Y := Y) i).hom (A i)
        (Work.Serre.Sigma.sigmaSet A)
        (fun x hx => Work.Serre.Sigma.pieceIncl_mem_sigmaSet A i x hx) ℚ ((k + r) + 1)).hom
          (Φσ x) =
      (Work.Thom.mixedCupC ℚ (A i) k (r + 1))
        ((Work.Thom.CohMap (π i) ℚ k).hom
          ((Work.Thom.CohMap (Work.Serre.Sigma.pieceIncl (Y := B) i).hom ℚ k).hom x)) (U i) := by
    intro i x
    have h := Work.Serre.Sigma.relCohMap_mixedCup_sigmaMap (A := A) (π := π) (n := r + 1)
      (k := k) Uσ x i
    rw [hrestr i] at h
    rw [hΦσ_apply x]
    exact h
  have hbij : Function.Bijective Φσ := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have hzero : Φσ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      have hx0 : ∀ i,
          (Work.Thom.CohMap (Work.Serre.Sigma.pieceIncl (Y := B) i).hom ℚ k).hom (x - y) = 0 := by
        intro i
        have h1 := hkey i (x - y)
        rw [hzero, map_zero] at h1
        have hf0 : (Work.Thom.mixedCupC ℚ (A i) k (r + 1))
            ((Work.Thom.CohMap (π i) ℚ k).hom (0 : Work.Thom.Coh ℚ k (B i))) (U i) = 0 := by
          simp only [map_zero, LinearMap.zero_apply]
        exact (hΦi i).1 (h1.symm.trans hf0.symm)
      exact sub_eq_zero.mp (Work.Serre.Sigma.Coh_sigma_eq_zero_of_restr_eq_zero k (x - y) hx0)
    · intro y
      have hex : ∀ i, ∃ z : Work.Thom.Coh ℚ k (B i),
          (Work.Thom.mixedCupC ℚ (A i) k (r + 1)) ((Work.Thom.CohMap (π i) ℚ k).hom z) (U i) =
            (Work.Thom.relCohMap (Work.Serre.Sigma.pieceIncl (Y := Y) i).hom (A i)
              (Work.Serre.Sigma.sigmaSet A)
              (fun x hx => Work.Serre.Sigma.pieceIncl_mem_sigmaSet A i x hx) ℚ
                (k + r + 1)).hom y :=
        fun i => (hΦi i).2 _
      choose z hz using hex
      obtain ⟨x, hx⟩ := Work.Serre.Sigma.exists_Coh_sigma_of_restr (Y := B) (k := k) z
      refine ⟨x, ?_⟩
      have hzero : Φσ x - y = 0 := by
        apply Work.Serre.Sigma.relZero_of_restr_zero (A := A) (m := k + r)
        intro i
        rw [map_sub, hkey i x, hx i, hz i, sub_self]
      exact sub_eq_zero.mp hzero
  have hfun : (fun x : Work.Thom.Coh ℚ k (Σ i, B i) =>
      (Work.Thom.mixedCupC ℚ (Work.Serre.Sigma.sigmaSet A) k (r + 1))
        ((Work.Thom.CohMap (Work.Serre.Sigma.sigmaMap π) ℚ k).hom x) Uσ) = Φσ :=
    funext (fun x => (hΦσ_apply x).symm)
  rw [hfun]
  exact hbij

end Work.Serre.ThmCylSigma
