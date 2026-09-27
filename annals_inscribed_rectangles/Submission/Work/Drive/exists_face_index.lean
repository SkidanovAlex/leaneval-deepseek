import Mathlib
import Submission.Work.Drive.BoxParityDefs

/-!
# Existence of a face on which the derivative stays surjective

`Amb m = ℝ^{m+1}` and `Tgt m = ℝ^m`.  If `T = fderiv ℝ F p : ℝ^{m+1} →L[ℝ] ℝ^m` is surjective then
its kernel is a line, and some coordinate functional is nonzero on that line; for the corresponding
coordinate `i` the hyperplane `{v | v i = 0}` meets `ker T` only in `0`, so the restriction of `T`
to that coordinate hyperplane is still surjective.  This is the "the zero on the boundary of the box
lies on a face cut out transversally" input used in `Submission.Drive.ParityProp`.
-/

namespace Work.Drive

theorem exists_face_index {m : ℕ} {F : Work.Drive.Amb m → Work.Drive.Tgt m} {p : Work.Drive.Amb m}
    (hreg : Function.Surjective (fderiv ℝ F p)) :
    ∃ i : Fin (m + 1), Function.Surjective (fun v : {v : Work.Drive.Amb m // v i = 0} =>
      fderiv ℝ F p v.1) := by
  set T := fderiv ℝ F p with hT
  -- `T` is surjective, so its range is everything, hence its kernel is one-dimensional.
  have hrange : T.range = ⊤ := LinearMap.range_eq_top.mpr hreg
  have hkerdim : Module.finrank ℝ T.ker = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker (T : Amb m →ₗ[ℝ] Tgt m)
    rw [hrange, finrank_top] at h
    have hA : Module.finrank ℝ (Amb m) = m + 1 := by simp [Amb]
    have hB : Module.finrank ℝ (Tgt m) = m := by simp [Tgt]
    omega
  have hker_ne : T.ker ≠ ⊥ := by
    intro h
    have : Module.finrank ℝ T.ker = 0 := by rw [h]; exact finrank_bot ℝ (Amb m)
    omega
  -- Pick a nonzero vector `u` spanning the kernel.
  obtain ⟨u, hu_mem, hu_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  have hu : T u = 0 := LinearMap.mem_ker.mp hu_mem
  -- It has a nonzero coordinate `i`.
  have hcoord : ∃ i : Fin (m + 1), u i ≠ 0 := by
    have hne : u.ofLp ≠ 0 := by
      intro h
      apply hu_ne
      apply WithLp.ofLp_injective
      simpa using h
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    exact ⟨i, by simpa using hi⟩
  obtain ⟨i, hi⟩ := hcoord
  refine ⟨i, ?_⟩
  -- On the hyperplane `{v i = 0}`, `T` is still surjective: shift any preimage by a multiple of `u`
  -- to force its `i`-th coordinate to vanish.
  intro y
  obtain ⟨v, hv⟩ := hreg y
  refine ⟨⟨v - (v i / u i) • u, ?_⟩, ?_⟩
  · simp [hi]
  · change T (v - (v i / u i) • u) = y
    rw [map_sub, map_smul, hv, hu, smul_zero, sub_zero]

end Work.Drive
