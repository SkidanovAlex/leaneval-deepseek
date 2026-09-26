import Mathlib
import Submission.Work.PTCert.Interfaces
import Submission.Work.RouteB.EdgeLap
import Submission.Work.PTCert.sigmaGroupFacts

/-!
# Conjugation by a signed permutation preserves the Nielsen generating set

`sigAut p s = signAut s * permAut p` is the signed permutation `a_k ↦ a_{p k}^{±1}`
of `F_r`.  This file proves `Work.PTCert.sigAutConj_mem_SAutGen`: conjugating any
element of the Nielsen transvection generating set `SAutGen r` (the paper's
`{ρᵢⱼ^{±1}, λᵢⱼ^{±1}}`) by a signed permutation again lands in `SAutGen r`.

The two ingredients already available in `Submission/Commons/GroupTheory/FreeGroup`
are `sigma_conj_mem_SAutGen` (conjugation by a single-generator inversion `σᵢ` is a
transvection-to-transvection map, an involution) and `permAut_conj_mem_SAutGen`
(conjugation by a basis permutation permutes the transvections).  Since
`signAut s` is a product of `σᵢ`'s, a short induction on the list of inverted
generators upgrades the single-`σᵢ` statement to arbitrary sign flips, and then
`sigAut p s = signAut s * permAut p` combines the two.
-/

namespace Work.PTCert

open Submission.PTCert

/-- Conjugation by a single generator inversion `σᵢ` preserves `SAutGen r`
(restatement, for the `Submission`-namespace definitions, of the commons lemma
`Commons.GroupTheory.FreeGroup.sigma_conj_mem_SAutGen`). -/
lemma sigma_conj_mem_SAutGen (r : ℕ) (i : Fin r) {y : MulAut (FreeGroup (Fin r))}
    (hy : y ∈ Submission.FreeGroupAut.SAutGen r) :
    Submission.FreeGroupAut.sigma i * y * (Submission.FreeGroupAut.sigma i)⁻¹
      ∈ Submission.FreeGroupAut.SAutGen r := by
  rw [Submission.FreeGroupAut.sigma_inv]
  exact Commons.GroupTheory.FreeGroup.sigma_conj_mem_SAutGen r i hy

/-- Conjugation by a product of generator inversions `∏_{i ∈ L} σᵢ` preserves
`SAutGen r`.  This is the induction on `L` that upgrades the single-`σᵢ`
statement to an arbitrary sign flip. -/
lemma list_sigma_conj_mem_SAutGen (r : ℕ) (L : List (Fin r))
    {y : MulAut (FreeGroup (Fin r))} (hy : y ∈ Submission.FreeGroupAut.SAutGen r) :
    (L.map Submission.FreeGroupAut.sigma).prod * y
        * ((L.map Submission.FreeGroupAut.sigma).prod)⁻¹
      ∈ Submission.FreeGroupAut.SAutGen r := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.prod_nil, one_mul, inv_one, mul_one]
    exact hy
  | cons b L ih =>
    rw [List.map_cons, List.prod_cons]
    have hz := sigma_conj_mem_SAutGen r b ih
    convert hz using 1
    group

/-- **Conjugation by a sign flip preserves `SAutGen r`.** -/
lemma signAut_conj_mem_SAutGen (r : ℕ) (s : Fin r → Bool)
    {y : MulAut (FreeGroup (Fin r))} (hy : y ∈ Submission.FreeGroupAut.SAutGen r) :
    Submission.PTCert.signAut s * y * (Submission.PTCert.signAut s)⁻¹
      ∈ Submission.FreeGroupAut.SAutGen r := by
  unfold Submission.PTCert.signAut
  exact list_sigma_conj_mem_SAutGen r _ hy

theorem sigAutConj_mem_SAutGen (r : ℕ) (p : Equiv.Perm (Fin r)) (s : Fin r → Bool)
    {x : MulAut (FreeGroup (Fin r))} (hx : x ∈ Submission.FreeGroupAut.SAutGen r) :
    Submission.PTCert.sigAut p s * x * (Submission.PTCert.sigAut p s)⁻¹
      ∈ Submission.FreeGroupAut.SAutGen r := by
  -- conjugation by the basis permutation `p` still lies in `SAutGen r`…
  have h1 : Submission.RouteB.permAut p * x * (Submission.RouteB.permAut p)⁻¹
      ∈ Submission.FreeGroupAut.SAutGen r :=
    Commons.GroupTheory.FreeGroup.permAut_conj_mem_SAutGen r p hx
  -- …and so does conjugating that by the sign flip.
  have h2 := signAut_conj_mem_SAutGen r s h1
  convert h2 using 1
  rw [Submission.PTCert.sigAut]
  group

end Work.PTCert
