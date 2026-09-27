import Mathlib
import Submission.Work.PL.Subdiv.Embed

namespace Work.PL.Subdiv.DomDim

open Set

/-- An injective affine map sends a set of dimension `≤ d` to a set of dimension `≤ d`:
the image of the simplex spanned by `s` is the simplex spanned by the (finite) image
of `s`, and taking an image can only lower the number of vertices. -/
theorem domDim_affine_image {m m' : ℕ} (A : PL.E m →ᵃ[ℝ] PL.E m') (hA : Function.Injective A)
    {X : Set (PL.E m)} {d : ℤ} (h : PL.DomDim X d) : PL.DomDim (A '' X) d := by
  obtain ⟨S, hS, hsub⟩ := h
  refine ⟨S.image (fun s => s.image A), ?_, ?_⟩
  · intro s' hs'
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hs'
    have h1 : (s.image A).card ≤ s.card := Finset.card_image_le
    have h2 : ((s.image A).card : ℤ) ≤ (s.card : ℤ) := by exact_mod_cast h1
    have h3 := hS s hs
    omega
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp (hsub hx)
    refine Set.mem_iUnion₂.mpr ⟨s.image A, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
    have hmem : A x ∈ A '' convexHull ℝ (s : Set (PL.E m)) := ⟨x, hxs, rfl⟩
    rw [AffineMap.image_convexHull] at hmem
    simpa only [PL.simp, Finset.coe_image] using hmem

end Work.PL.Subdiv.DomDim
