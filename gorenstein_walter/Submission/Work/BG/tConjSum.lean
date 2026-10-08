import Mathlib
import Submission.Work.BG.T32Aux
import Submission.OddOrder.GroupTheory.TISubsetCounting

/-!
# Area BG: the conjugacy-sum over the TI-set `T = H₀ ∖ U` (BG 1981, Theorem 3.2, p. 208)

`T = H₀ ∖ U` (Bender–Glauberman, Hypothesis 1.2) is a TI-subset of `G` whose normalizer is
`H` (`Work.BG.Hyp12.TI`, `Work.BG.Hyp12.normalizer_T`).  Consequently the conjugacy
saturation `T^G = 𝒞_G(T)` is the *disjoint* union of the `[G : H]` conjugates `gTg⁻¹`
(`gH ∈ G/H`), and since a class function `θ` is constant on conjugacy classes each of those
conjugates contributes the same sum `∑_{x ∈ T} θ x`:

  `∑_{x ∈ T^G} θ x = [G : H] · ∑_{x ∈ T} θ x`.

This is the counting step of the proof of Theorem 3.2 (the `H`-index form: it is `H`, not `H₀`,
because `N_G(T) = H`), and it is the `Work.BG` specialization of the shared lemma
`OddOrder.GroupTheory.IsTISubset.sum_conjClassSet`: the `H`-stability of `T` required there is
exactly the normalizer clause `N_G(T) = H` of Hypothesis 1.2.
-/

namespace Work.BG

-- The pointwise `SMul (MulAut G) (Set G)` instance (`Set.smulSet`) is scoped under
-- `Pointwise`; the TI-counting lemma `IsTISubset.sum_conjClassSet` is stated with it.
open scoped Pointwise

open OddOrder.RepresentationTheory Work.GW2 Work.BG in
theorem tConjSum {G : Type} [Group G] [Finite G] [Fintype G] (C : Work.BG.Sec2Ctx G)
    (θ : ClassFunction G ℂ) :
    (∑ x ∈ Work.BG.TconjFin C, θ x) =
      (C.P.H.index : ℂ) * (∑ x ∈ Work.BG.Tfin C, θ x) := by
  -- `T = H₀ ∖ U` is `H`-stable: `H` is its normalizer (Hypothesis 1.2).
  have hstab : ∀ l ∈ C.P.H, MulAut.conj l • Tset C.P.H0 C.P.U = Tset C.P.H0 C.P.U := by
    intro l hl
    have hl' : l ∈ Subgroup.normalizer (Tset C.P.H0 C.P.U) := by
      rw [C.P.normalizer_T]; exact hl
    rw [Subgroup.mem_normalizer_iff_conj_image_eq] at hl'
    rw [← Set.image_smul]
    simpa only [MulAut.smul_def] using hl'
  -- The weighted TI-counting lemma `∑_{x ∈ A^G} f x = [G : L] • ∑_{a ∈ A} f a`.
  have h := OddOrder.GroupTheory.IsTISubset.sum_conjClassSet (G := G)
      (A := Tset C.P.H0 C.P.U) (L := C.P.H) (M := ℂ) (f := fun x => θ x)
      C.P.TI hstab (fun g x => θ.conj_eq x g)
  simpa [TconjFin, Tfin, nsmul_eq_mul] using h

end Work.BG
