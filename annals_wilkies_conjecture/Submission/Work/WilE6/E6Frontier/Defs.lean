/-
  WilE6, frontier half of `E6_fiber_closure`: vocabulary for the assembly
  `E6_fiber_closure_proved_of_complement`.

  The frontier `fiberClosure X.set \ X.set` is the intersection of the (already
  produced) fibrewise closure with the complement of `X`, and both come with their
  own chains.  The operation that puts them over a common chain is
  `Work.WilE7.EAChain.cat`; `interCat` below is the conjunction of two `SemiPf`-sets
  over the concatenated chain, with the product DNF.
-/
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.Defs
import Submission.Work.WilE5.Basic

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE6
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- The conjunction of two basic conditions over the concatenated chain: a basic set for
the chain `cat X.c Y.c`. -/
def conjCat {k : ℕ} {r₁ r₂ : ℕ} (B : Basic k r₁) (C : Basic k r₂) : Basic k (r₁ + r₂) :=
  Work.WilE5.conj (Work.WilE7.Basic.inl (r₂ := r₂) B) (Work.WilE7.Basic.inr (r₁ := r₁) C)

/-- The intersection of two semi-Pfaffian sets in the same ambient space, presented over the
concatenated chain: the product DNF of the two lists of basic conditions. -/
def interCat {k : ℕ} (X Y : SemiPf k) : SemiPf k :=
  ⟨X.r + Y.r, Work.WilE7.EAChain.cat X.c Y.c,
   X.basics.flatMap (fun B => Y.basics.map (fun C => conjCat B C))⟩

end Work.WilE6
