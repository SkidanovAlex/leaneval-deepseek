import Mathlib
import Submission.Work.Hering.AppVIII.Defs
import Submission.Work.Hering.AppVIII.FrobField

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The group `C(n,ε)` of Higman's table (`n = 2s+1`) and the maps induced on `C/Z` and `Z`

This file only contains definitions, shared by the proofs of Appendix VIII, Proposition 4.

* `KC s = GF(2^(2s+1))`;
* `thetaC s = (frobeniusEquiv (KC s) 2)^s : x ↦ x^(2^s)`;
* `CTypeC s ε = C(n,ε)`, the Suzuki 2-group of type `C` in the two-step model
  `(x,y,z)*(x',y',z') = (x+x', y+y', z+z'+ x·θx' + ε·√x·θ(y'²) + y·y')`;
* `quadC s ε (x,y) = x·θx + ε·√x·θ(y²) + y²`, the squaring map on `V = C/Z(C) ≅ K × K`;
* `fstFun α`, `sndFun α`: the additive isomorphisms of `V` and `Z` induced by
  `α ∈ Aut C(n,ε)` (via the representatives `⟨u,0⟩` and `⟨0,z⟩`).
-/

set_option autoImplicit false

noncomputable section

namespace Work.Hering.AppVIII

open Work.Higman

/-- `K = GF(2^(2s+1))`, the field of definition of `C(n,ε)` of Higman's table. -/
abbrev KC (s : ℕ) : Type := GaloisField 2 (2 * s + 1)

/-- `θ : x ↦ x ^ (2^s)`, the `s`-th power of the Frobenius of `GF(2^(2s+1))`. -/
def thetaC (s : ℕ) : KC s ≃+* KC s := (frobeniusEquiv (KC s) 2) ^ s

/-- The Suzuki 2-group `C(n,ε)` (`n = 2s+1`) of type `C`, in the two-step model. -/
abbrev CTypeC (s : ℕ) (ε : KC s) : Type := CType (KC s) (thetaC s) ε

/-- The diagonal of the cocycle of `C(n,ε)`: `q(x,y) = x·θx + ε·√x·θ(y²) + y²`.  This is the
squaring map `V → Z` of the two-step group: `⟨u,0⟩² = ⟨0, q u⟩`. -/
def quadC (s : ℕ) (ε : KC s) (p : KC s × KC s) : KC s := cCocycle (KC s) (thetaC s) ε p p

/-- The cocycle `b` of `C(n,ε)`, as a function of two `A`-coordinates. -/
def cocC (s : ℕ) (ε : KC s) (p q : KC s × KC s) : KC s := cCocycle (KC s) (thetaC s) ε p q

/-- The map induced by `α ∈ Aut C(n,ε)` on `V = C/Z(C) ≅ K × K`: `u ↦ (α ⟨u,0⟩).fst`. -/
def fstFun {s : ℕ} {ε : KC s} (α : MulAut (CTypeC s ε)) (u : KC s × KC s) : KC s × KC s :=
  (α ⟨u, 0⟩).fst

/-- The map induced by `α ∈ Aut C(n,ε)` on `Z(C) ≅ K`: `z ↦ (α ⟨0,z⟩).snd`. -/
def sndFun {s : ℕ} {ε : KC s} (α : MulAut (CTypeC s ε)) (z : KC s) : KC s := (α ⟨0, z⟩).snd

/-- `P₁ = π^{-1}(0 × K) ≤ C(n,ε)`: the stabiliser of this subgroup is the object of
Appendix VIII, Proposition 4. -/
abbrev P1C (s : ℕ) (ε : KC s) : Subgroup (CTypeC s ε) := CTypeP1 (thetaC s) ε

end Work.Hering.AppVIII
