import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.sampling_sq_sum_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.Rb5Lin

theorem honest_sum_le_full_lattice {W : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ : ℝ} {N : ℕ}
    (hsum : Summable (fun k : {k : Fin 3 → ℤ // k ≠ 0} =>
      (Work.BoseFixR.chat W (ℓ⁻¹ • Work.BoseB4.vec k.1)) ^ 2
        / (2 * ‖ℓ⁻¹ • Work.BoseB4.vec k.1‖ ^ 2))) :
    (∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
        (Work.BoseFixR.chat W (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
          / (2 * ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2))
      ≤ ∑' k : {k : Fin 3 → ℤ // k ≠ 0},
          (Work.BoseFixR.chat W (ℓ⁻¹ • Work.BoseB4.vec k.1)) ^ 2
            / (2 * ‖ℓ⁻¹ • Work.BoseB4.vec k.1‖ ^ 2) := by
  classical
  -- The summand, as a function of the integer lattice label `m`.
  set φ : (Fin 3 → ℤ) → ℝ := fun m =>
    (Work.BoseFixR.chat W (ℓ⁻¹ • Work.BoseB4.vec m)) ^ 2
      / (2 * ‖ℓ⁻¹ • Work.BoseB4.vec m‖ ^ 2) with hφ
  -- The image of the box labels `k ≠ 0` inside `ℤ³` under `labVec N`.
  set T : Finset (Fin 3 → ℤ) :=
    ((Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0).image
      (Work.BoseBoxFock.labVec N) with hT
  have hφnn : ∀ m : Fin 3 → ℤ, 0 ≤ φ m := by
    intro m
    rw [hφ]
    exact div_nonneg (sq_nonneg _) (by positivity)
  have hlabVec_zero : Work.BoseBoxFock.labVec N (0 : Work.BoseBoxFock.Lab N) = 0 := by
    funext i
    simp [Work.BoseBoxFock.labVec]
  -- `0` is not in the image: it is the image of `labVec N 0`, and `labVec N` is injective.
  have hT0 : (0 : Fin 3 → ℤ) ∉ T := by
    rw [hT, Finset.mem_image]
    rintro ⟨k, hk, hk0⟩
    rw [Finset.mem_erase] at hk
    exact hk.1 (Work.BoseFixR.labVec_injective N (by rw [hk0, hlabVec_zero]))
  -- The image set, viewed as a finite subset of the nonzero integer vectors.
  let emb : {m : Fin 3 → ℤ // m ∈ T} → {m : Fin 3 → ℤ // m ≠ 0} :=
    fun m => ⟨m.1, fun h => hT0 (h ▸ m.2)⟩
  have hsumm : Summable (fun k : {k : Fin 3 → ℤ // k ≠ 0} => φ k.1) := by
    simpa only [hφ] using hsum
  have hbess := Summable.sum_le_tsum (T.attach.image emb) (fun y _ => hφnn y.1) hsumm
  -- Step 1: the honest box momenta are the lattice momenta of `labVec N`.
  have h1 : (∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
        (Work.BoseFixR.chat W (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
          / (2 * ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2))
      = ∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
          φ (Work.BoseBoxFock.labVec N k) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hφ, Work.BoseBoxFock.kmomLab]
  -- Step 2: reindex the box sum by the (injective) labelling map.
  have h2 : (∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
          φ (Work.BoseBoxFock.labVec N k)) = ∑ m ∈ T, φ m := by
    rw [hT]
    exact (Finset.sum_image (f := φ) (g := Work.BoseBoxFock.labVec N)
      (fun x _ y _ h => Work.BoseFixR.labVec_injective N h)).symm
  -- Step 3: the same finite set, as a subset of the subtype of nonzero vectors.
  have hinj : Set.InjOn emb (↑T.attach : Set {m : Fin 3 → ℤ // m ∈ T}) := by
    intro x _ y _ h
    have h' : (emb x).1 = (emb y).1 := congrArg Subtype.val h
    exact Subtype.ext h'
  have h3 : (∑ m ∈ T, φ m) = ∑ y ∈ T.attach.image emb, φ y.1 := by
    rw [Finset.sum_image (f := fun y : {m : Fin 3 → ℤ // m ≠ 0} => φ y.1) hinj]
    exact (Finset.sum_attach T φ).symm
  calc (∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
        (Work.BoseFixR.chat W (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
          / (2 * ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2))
      = ∑ y ∈ T.attach.image emb, φ y.1 := by rw [h1, h2, h3]
    _ ≤ ∑' k : {k : Fin 3 → ℤ // k ≠ 0}, φ k.1 := hbess

end Work.BoseFixR.Rb5Lin
