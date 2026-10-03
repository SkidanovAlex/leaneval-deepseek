import Mathlib
import Submission.Work.KMTContract.Defs

namespace Work.KMTContract

/-- The convolution `n ↦ ∑'_j κ j * g (n - j)` of an arbitrary kernel `κ` with a finitely
supported function `g` is summable: the summand vanishes off the finite set of `j` with `n - j` in
the (finite) support of `g`. -/
private theorem summable_conv (κ : ℤ → ℂ) {g : ℤ → ℂ}
    (hg : Work.Analysis.InverseTheory.FinSupp g) (n : ℤ) :
    Summable fun j : ℤ => κ j * g (n - j) := by
  obtain ⟨s, hs⟩ := hg
  refine summable_of_ne_finset_zero (s := s.image (fun x => n - x)) fun j hj => ?_
  have : n - j ∉ s := fun hns => hj (Finset.mem_image.mpr ⟨n - j, hns, by ring⟩)
  rw [hs (n - j) this, mul_zero]

/-- Linearity of a convolution with a fixed kernel on finitely supported inputs. -/
private theorem conv_add_smul (κ : ℤ → ℂ) {f f' : ℤ → ℂ} (c : ℂ)
    (hf : Work.Analysis.InverseTheory.FinSupp f)
    (hf' : Work.Analysis.InverseTheory.FinSupp f') (n : ℤ) :
    (∑' j : ℤ, κ j * (f (n - j) + c * f' (n - j)))
      = (∑' j : ℤ, κ j * f (n - j)) + c * (∑' j : ℤ, κ j * f' (n - j)) := by
  have h1 : Summable fun j : ℤ => κ j * f (n - j) := summable_conv κ hf n
  have h2 : Summable fun j : ℤ => κ j * f' (n - j) := summable_conv κ hf' n
  rw [show (∑' j : ℤ, κ j * (f (n - j) + c * f' (n - j)))
        = ∑' j : ℤ, (κ j * f (n - j) + c * (κ j * f' (n - j))) from
      tsum_congr fun j => by ring]
  rw [h1.tsum_add (h2.mul_left c), tsum_mul_left]

/-- **Linearity of the Ionescu--Wainger projection on finitely supported functions.**
`kmtProj ρ l k f = ∑'_j (iwKernel … j) * f (n - j)` is a convolution with a fixed kernel, so it is
linear; on *finitely supported* inputs (which is the only case the contract needs, for the
bilinearity hypothesis of the interpolation lemma `VarBilinInterp`) all the series involved are
finite and the proof is just `tsum_add`/`tsum_const_smul` plus the finite support. -/
theorem kmtProj_finsupp_linear (ρ : ℝ) (l : ℕ) (k : ℤ) (f f' : ℤ → ℂ) (c : ℂ)
    (hf : Work.Analysis.InverseTheory.FinSupp f)
    (hf' : Work.Analysis.InverseTheory.FinSupp f') :
    Work.KMTContract.kmtProj ρ l k (fun x => f x + c * f' x)
      = fun x => Work.KMTContract.kmtProj ρ l k f x + c * Work.KMTContract.kmtProj ρ l k f' x := by
  funext n
  simp only [kmtProj_apply]
  exact conv_add_smul _ c hf hf' n

end Work.KMTContract
