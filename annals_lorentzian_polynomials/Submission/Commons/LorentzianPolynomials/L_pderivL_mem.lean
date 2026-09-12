import Mathlib
import Submission.Commons.LorentzianPolynomials.partials_mem_L

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set

set_option autoImplicit false

namespace Commons.LorentzianPolynomials

/-- Iterated partial derivatives of an element of `L n d` along a list of at most `d - 2`
indices stay in `L`: there exists an element `g` of `L n (d - l.length)` whose underlying
polynomial is `l.foldl (fun q i => MvPolynomial.pderiv i q) f.1`. -/
theorem L_pderivL_mem {n d : ℕ} (l : List (Fin n)) (f : H n d) (hf : f ∈ L n d)
    (hl : l.length ≤ d - 2) :
    ∃ g : H n (d - l.length),
      g.1 = l.foldl (fun q i => MvPolynomial.pderiv i q) f.1 ∧ g ∈ L n (d - l.length) := by
  classical
  cases l with
  | nil =>
      -- no derivatives to take: `f` itself is the witness
      have hdeg : d - ([] : List (Fin n)).length = d := by simp
      rw [hdeg]
      refine ⟨f, ?_, hf⟩
      rfl
  | cons i l' =>
      -- a nonempty list of at most `d - 2` derivatives forces the degree to be at least `2`,
      -- so the already-proven `partials_mem_L` applies
      have hd2 : 2 ≤ d := by
        have h₂ : l'.length + 1 ≤ d - 2 := by simpa using hl
        omega
      rcases partials_mem_L (n := n) (d := d) hd2 (i :: l') hl f hf with ⟨u, huL, hu_eq⟩
      refine ⟨u, ?_, huL⟩
      simpa [Commons.Combinatorics.MvPolynomial.pderivL] using hu_eq

end Commons.LorentzianPolynomials
