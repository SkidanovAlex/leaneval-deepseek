import Mathlib
import Submission.Work.ORLyndon.Fox
import Submission.Work.ORLyndon.FoxComp

namespace Work.ORLyndon

theorem foxD_map_of_injective {X Y : Type*} [DecidableEq X] [DecidableEq Y] {K : Type*} [Field K]
    (ι : X → Y) (hι : Function.Injective ι) (q : X) (w : FreeGroup X) :
    Work.ORLyndon.foxD (K := K) (ι q) (FreeGroup.map ι w) =
      MonoidAlgebra.mapDomainRingHom K (FreeGroup.map ι) (Work.ORLyndon.foxD (K := K) q w) := by
  -- Chain rule (already available in the chapter) reduces to a sum over the generators of `X`
  -- against the Fox derivatives of the images `ι x` of the generators.
  rw [foxD_comp (K := K) (FreeGroup.map ι) (ι q) w]
  -- An image generator `ι x` has nonzero `∂/∂(ι q)` exactly when `x = q` (injectivity of `ι`).
  have h : ∀ x, Work.ORLyndon.foxD (K := K) (ι q) (FreeGroup.map ι (FreeGroup.of x))
      = if x = q then 1 else 0 := by
    intro x
    rw [FreeGroup.map.of, foxD_of]
    by_cases hx : x = q
    · subst hx; simp
    · have : ι x ≠ ι q := fun hh => hx (hι hh)
      simp [hx, this]
  simp only [h]
  -- Hence only the `q`-term of the (finitely supported) sum survives.
  rw [Finsupp.sum, Finset.sum_eq_single q]
  · simp only [if_true, mul_one, foxFD_apply]
  · intro b _ hb
    simp [hb]
  · intro hq
    have hq' : foxFD (K := K) w q = 0 := by
      simpa only [Finsupp.mem_support_iff, not_not] using hq
    rw [hq']
    simp

end Work.ORLyndon
