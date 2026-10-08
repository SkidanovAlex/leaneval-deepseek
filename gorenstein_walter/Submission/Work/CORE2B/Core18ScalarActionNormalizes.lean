import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.C18ScalarActionNormalizes_proved

/-!
# GW design pass 18, item A, leaf A1: scalar action normalizes every subgroup of `F(U)`

If `s` acts on every `O_p(U)` either trivially or by inversion, then `s` normalizes every
subgroup `X ≤ F(U)`.

Sketch (0.15–0.3k lines).  Let `x ∈ X`.  Write `x = ∏_p x_p` with `x_p` the `p`-part of `x`
(a power of `x`, so `x_p ∈ X`; obtain it by induction on `(orderOf x).primeFactors` with
Bezout: for `orderOf x = a * b`, `Nat.Coprime a b`, `x = (x ^ a) ^ u * (x ^ b) ^ v` in `zpow`).
Each `x_p` is a `p`-element of `F(U)`, hence lies in `O_p(U)`
(`Work.CORE3.pCoreIn_of_pow_eq_one_of_mem_fittingIn` handles exponent `p`; for exponent `p^k`
use `IsPGroup` of `zpowers x_p` + "a normal nilpotent subgroup's `p`-elements lie in its unique
Sylow `p`" — or the BMAX lemma `fittingPiIn_le_iSup_pCoreIn`).  By `hact`, `s x_p s⁻¹ ∈ {x_p, x_p⁻¹} ⊆ X`;
conjugation is multiplicative, so `s x s⁻¹ = ∏ s x_p s⁻¹ ∈ X`.  Finally `s X s⁻¹ ≤ X` and
finiteness give `s ∈ N_G(X)` (`Subgroup.mem_normalizer_iff_of_le`-style, or
`mem_normalizer_iff` directly since the map is injective on a finite set).

GAP sanity check: `_design_gw/gw18_A.g` (A1).
-/


namespace Work.GW18

open Subgroup

theorem Core18ScalarActionNormalizes {G : Type} [Group G] [Finite G] (U : Subgroup G) (s : G)
    (hact : ∀ p : ℕ, p.Prime →
      (∀ z ∈ Work.GW2.pCoreIn p U, s * z * s⁻¹ = z) ∨
        (∀ z ∈ Work.GW2.pCoreIn p U, s * z * s⁻¹ = z⁻¹))
    (X : Subgroup G) (hX : X ≤ Work.GW2.fittingIn U) :
    s ∈ Subgroup.normalizer (X : Set G) := Work.CORE2B.C18ScalarActionNormalizes_proved U s hact X hX

end Work.GW18
