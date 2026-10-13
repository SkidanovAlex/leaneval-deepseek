import Mathlib
import Submission.Work.WilLibTS.TS.PolynomialSignSetFinite2

namespace Work.WilLibTS.TS.PolynomialSignSet

theorem prod {X Y ι κ : Type*} {c : X → ι → ℝ} {d : Y → κ → ℝ} {S : Set X} {T : Set Y}
    (hS : Work.WilLibTS.TS.PolynomialSignSet c S)
    (hT : Work.WilLibTS.TS.PolynomialSignSet d T) :
    Work.WilLibTS.TS.PolynomialSignSet (fun z : X × Y => Sum.elim (c z.1) (d z.2))
      {z : X × Y | z.1 ∈ S ∧ z.2 ∈ T} := by
  -- Lift the sign set `S` in the coordinates `c` to `X × Y` in the coordinates
  -- `Sum.elim (c z.1) (d z.2)`, using only the `Sum.inl` coordinates.
  have hS' : Work.WilLibTS.TS.PolynomialSignSet (fun z : X × Y => Sum.elim (c z.1) (d z.2))
      (Prod.fst ⁻¹' S) :=
    hS.polynomial_preimage Prod.fst (fun i => MvPolynomial.X (Sum.inl i))
      (by intro z i; simp)
  -- Same for `T`, using the `Sum.inr` coordinates.
  have hT' : Work.WilLibTS.TS.PolynomialSignSet (fun z : X × Y => Sum.elim (c z.1) (d z.2))
      (Prod.snd ⁻¹' T) :=
    hT.polynomial_preimage Prod.snd (fun k => MvPolynomial.X (Sum.inr k))
      (by intro z k; simp)
  have h := hS'.inter hT'
  convert h using 1
  ext z
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]

end Work.WilLibTS.TS.PolynomialSignSet
