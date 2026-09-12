import Mathlib.Analysis.InnerProductSpace.ExteriorPower
import Submission.Commons.LinearAlgebra.Matrix.det_ne_zero_card_eq_of_support

namespace Commons.Analysis.InnerProductSpace

open Module exteriorPower

theorem inner_exteriorPower_basis_iMulti_eq_zero_of_support {d j : ℕ} (ℓ : ℕ)
    (a : Fin j → EuclideanSpace ℝ (Fin d)) (Q : Finset (Fin j))
    (I : Set.powersetCard (Fin d) j)
    (hlow : ∀ s ∈ Q, ∀ i : Fin d, ℓ ≤ i.val → inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i) (a s) = 0)
    (hhigh : ∀ s ∉ Q, ∀ i : Fin d, i.val < ℓ → inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i) (a s) = 0)
    (hcard : ((I : Set (Fin d)) ∩ {i : Fin d | ℓ ≤ i.val}).ncard ≠ j - Q.card) :
    inner ℝ (((EuclideanSpace.basisFun (Fin d) ℝ).exteriorPower j) I)
        (exteriorPower.ιMulti ℝ j a) = 0 := by
  classical
  set b := EuclideanSpace.basisFun (Fin d) ℝ with hb
  set f : Fin j ↪o Fin d := Set.powersetCard.ofFinEmbEquiv.symm I with hf
  set H : Finset (Fin j) := Finset.univ.filter (fun t => ℓ ≤ (f t).val) with hH
  set M : Matrix (Fin j) (Fin j) ℝ :=
    Matrix.of (fun i j' => inner ℝ (b (f j')) (a i)) with hM
  -- The basis vector of `⋀^j ℝᵈ` indexed by `I` is the wedge of the `b (f t)`.
  have hwedge : (b.exteriorPower j) I = exteriorPower.ιMulti ℝ j (fun t => b (f t)) := by
    have h1 : (b.exteriorPower j) I = (b.toBasis.exteriorPower j) I := by
      rw [← OrthonormalBasis.toBasis_exteriorPower b j]
      exact (congrFun (OrthonormalBasis.coe_toBasis (b.exteriorPower j)) I).symm
    rw [h1, exteriorPower.basis_apply]
    simp only [exteriorPower.ιMulti_family, hf, OrthonormalBasis.coe_toBasis]
    rfl
  have hinner : inner ℝ ((b.exteriorPower j) I) (exteriorPower.ιMulti ℝ j a) = M.det := by
    rw [hwedge, exteriorPower.inner_ιMulti_ιMulti]
  have hHcard : H.card = ((I : Set (Fin d)) ∩ {i : Fin d | ℓ ≤ i.val}).ncard := by
    have hrange : Set.range (f : Fin j → Fin d) = (I : Set (Fin d)) := by
      ext i
      rw [hf]
      exact Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem I i
    have hSetEq : (f '' (↑H : Set (Fin j))) = (I : Set (Fin d)) ∩ {i : Fin d | ℓ ≤ i.val} := by
      ext i
      simp only [Set.mem_image, Finset.mem_coe, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨t, ht, rfl⟩
        refine ⟨?_, ?_⟩
        · rw [← hrange]; exact Set.mem_range_self t
        · simpa [H] using ht
      · rintro ⟨hiI, hiℓ⟩
        have hi : i ∈ Set.range (f : Fin j → Fin d) := by rw [hrange]; exact hiI
        obtain ⟨t, rfl⟩ := hi
        exact ⟨t, by simpa [H] using hiℓ, rfl⟩
    rw [← hSetEq, Set.ncard_image_of_injective (↑H : Set (Fin j)) f.injective,
      Set.ncard_coe_finset]
  have hdet : M.det = 0 := by
    by_contra hne
    have h1 : ∀ s ∈ Q, ∀ i ∈ H, M s i = 0 := by
      intro s hs i hi
      have hi' : ℓ ≤ (f i).val := by simpa [H] using hi
      show inner ℝ (b (f i)) (a s) = 0
      exact hlow s hs (f i) hi'
    have h2 : ∀ s ∉ Q, ∀ i ∉ H, M s i = 0 := by
      intro s hs i hi
      have hi' : (f i).val < ℓ := by
        have : ¬ (ℓ ≤ (f i).val) := by simpa [H] using hi
        exact not_le.mp this
      show inner ℝ (b (f i)) (a s) = 0
      exact hhigh s hs (f i) hi'
    have hh := Commons.LinearAlgebra.Matrix.det_ne_zero_card_eq_of_support M Q H h1 h2 hne
    simp only [Fintype.card_fin] at hh
    exact hcard (hHcard.symm.trans hh)
  rw [hinner, hdet]

end Commons.Analysis.InnerProductSpace