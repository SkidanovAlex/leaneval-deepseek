import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.CharCore.Basic
import Submission.Work.Induction.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Vocabulary for Glauberman's proof of the `Q₈` case of Brauer–Suzuki

This file fixes the notation of Glauberman, *On groups with a quaternion Sylow 2-subgroup*,
Illinois J. Math. **18** (1974) 60–65 (see `REFS/brauer_suzuki.md` §3 and the transcription
`REFS/vision/glauberman1974/`), so that the individual steps (1)–(11) of the proof can be
stated and delegated separately.

Fix a finite group `G` and an element `x` of order `4` (in the application, `x` lies in a Sylow
`2`-subgroup `S ≅ Q₈` of `G`).  Then

* `X x = ⟨x⟩`, `T x = ⟨x²⟩` (the centre of `Q₈`);
* `Cstar x = C_G (X x)`, `Nstar x = N_G (X x)`, `Hstar x = O_{2'}(C*) ≤ G`;
* `Astar x = C* \ (T · H*)` (Glauberman's `A*`), `Bset x` = the set of `G`-conjugates of the
  elements of `A*` (Glauberman's `B`).

Characters:

* `lamFun x` is the unique linear character of `C*` with kernel `T · H*` (the map
  `C* → C*/(T·H*) ≅ C₂ → {±1}`), written as a function `↥C* → ℂ`;
* `zetaFun x` is the class function on `N*` with `ζ (y) = 2 (1 - λ (y))` for `y ∈ C*` and
  `ζ (y) = 0` for `y ∈ N* \ C*`; it is the `1̃_{C*} - λ̃` of Glauberman (1974);
* `etaFun x = Ind_{N*}^{G} ζ` is Glauberman's generalized character `η`.
-/

set_option autoImplicit false

open Classical
open scoped Pointwise

namespace Work.BrauerSuzuki.Q8

variable {G : Type*} [Group G]

/-! ## The subgroups attached to an element `x` -/

/-- `X = ⟨x⟩`. -/
def X (x : G) : Subgroup G := Subgroup.zpowers x

/-- `T = ⟨x ^ 2⟩`. -/
def T (x : G) : Subgroup G := Subgroup.zpowers (x ^ 2)

/-- `C* = C_G(X)`, the centralizer of `⟨x⟩`. -/
def Cstar (x : G) : Subgroup G := Subgroup.centralizer (X x : Set G)

/-- `N* = N_G(X)`, the normalizer of `⟨x⟩`. -/
def Nstar (x : G) : Subgroup G := Subgroup.normalizer (X x : Set G)

/-- `H* = O_{2'}(C*)`, viewed as a subgroup of `G` through `C* ≤ G`. -/
def Hstar (x : G) : Subgroup G :=
  (Submission.Blueprint.oddCore ↥(Cstar x)).map (Cstar x).subtype

/-- `A* = C* \ (T · H*)`: the elements of `C*` whose `2`-part generates `X`. -/
def Astar (x : G) : Set G := (Cstar x : Set G) \ ((T x : Set G) * (Hstar x : Set G))

/-- `B` = the set of `G`-conjugates of the elements of `A*`. -/
def Bset (x : G) : Set G := {y : G | ∃ a ∈ Astar x, IsConj y a}

/-! ## The characters `λ`, `ζ`, `η` -/

/-- The unique linear character `λ` of `C*` with kernel `T · H*`: it is `1` on `T · H*` and
`-1` off it (the quotient `C*/(T · H*)` has order `2`). -/
noncomputable def lamFun (x : G) (y : ↥(Cstar x)) : ℂ :=
  if (y : G) ∈ (T x : Set G) * (Hstar x : Set G) then 1 else -1

/-- `ζ` on `N*`: `2 (1 - λ (y))` for `y ∈ C*`, and `0` for `y ∈ N* \ C*`. -/
noncomputable def zetaFun (x : G) (y : ↥(Nstar x)) : ℂ :=
  if hy : (y : G) ∈ Cstar x then 2 * (1 - lamFun x ⟨(y : G), hy⟩) else 0

/-- `η = Ind_{N*}^{G} ζ`, the generalized character of `G` of Glauberman (1974). -/
noncomputable def etaFun (x : G) [Fintype G] : G → ℂ :=
  Work.Induction.indFun (Nstar x) (zetaFun x)

end Work.BrauerSuzuki.Q8
