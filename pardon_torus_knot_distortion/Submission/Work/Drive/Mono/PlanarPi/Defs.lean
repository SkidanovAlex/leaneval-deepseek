import Mathlib
import Submission.Work.CoreTopology.Disk

/-!
# The planar `Π`-region: the three convex pieces

Fix a closed set `B` (in practice `B = closure Q` for an open convex bounded `Q ⊆ ℝ²`), two
functionals `p`, `q` on the ambient space and three reals `a`, `h`, `lam` with `0 < h`.

* `piCapP B p c = B ∩ {c ≤ p}` — the `+`-cap: the part of `B` beyond the `+`-face of the strip
  `|p - a| ≤ h` (used with `c = a + h`);
* `piCapM B p c = B ∩ {p ≤ c}` — the `-`-cap (used with `c = a - h`);
* `piWall B p q a h lam = B ∩ {|p - a| ≤ h} ∩ {lam ≤ q}` — the part of `B` above the wall `q = lam`
  and inside the strip;
* `piRegion B p q a h lam = B ∩ ({a + h ≤ p} ∪ {p ≤ a - h} ∪ {lam ≤ q})` — the whole `Π`-shaped
  region: the two caps together with everything above the wall.
-/

namespace Work.Drive.Mono.PlanarPi

open Set

variable {X : Type*}

/-- The `+`-cap of `B`: the points of `B` with `c ≤ p x`. -/
def piCapP (B : Set X) (p : X → ℝ) (c : ℝ) : Set X := B ∩ {x | c ≤ p x}

/-- The `-`-cap of `B`: the points of `B` with `p x ≤ c`. -/
def piCapM (B : Set X) (p : X → ℝ) (c : ℝ) : Set X := B ∩ {x | p x ≤ c}

/-- The part of `B` inside the strip `|p - a| ≤ h` and above the wall `q = lam`. -/
def piWall (B : Set X) (p q : X → ℝ) (a h lam : ℝ) : Set X :=
  B ∩ {x | |p x - a| ≤ h} ∩ {x | lam ≤ q x}

/-- The planar `Π`-region: the part of `B` beyond the strip or above the wall. -/
def piRegion (B : Set X) (p q : X → ℝ) (a h lam : ℝ) : Set X :=
  B ∩ ({x | a + h ≤ p x} ∪ {x | p x ≤ a - h} ∪ {x | lam ≤ q x})

end Work.Drive.Mono.PlanarPi
