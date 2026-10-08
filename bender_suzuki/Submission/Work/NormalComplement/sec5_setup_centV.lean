import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- **Peterfalvi I Ch. III §5 Prop. 2 (a), the key structural fact** (p.184):
with `C = C_G(A)`, `F₀ = O^{2'}(C)` (seen in `G`), every element of `F₀` lying in
`V = centD H t = C_D(t)` is **central** in `F₀`.  Equivalently `F₀ ⊓ V ≤ Z(F₀)`; the source writes
it `F₀ ∩ V = F₀ ∩ A ⊆ Z(F₀)` and uses it to see that the pointwise stabiliser of three points of
`Ω_A` is trivial in `F₀/Z(F₀)`, i.e. that `Y = F₀/Z(F₀)` is a Zassenhaus group.

Route (corrected after review — the naive "inner automorphism" step needs `p ∤ |A|`):
* `h.E'V : Ecomm H t W ⊓ centD H t = ⁅A, P⁆` and `h.d2` (`IsD2`, third conjunct
  `⁅W ⊓ D, W ⊓ D⁆ ⊓ centD H t ≠ ⊥`) give `⁅A, P⁆ ≠ ⊥`, so **`P` does not centralise `A`**, i.e.
  `C_P(A) = 1` (any `1 ≠ p₀ ∈ C_P(A)` generates `P` as `|P| = p` is prime).
* `V = A ⋊ P`: `h.A_sup`, `h.A_inf`, `h.A_normal : V ≤ N_G(A)`.
* **`p ∤ |A|`**: `h.P_syl : IsSylowIn p P D` with `D = twoPoint H t` and `A ≤ V ≤ D`; a Sylow
  `p`-subgroup of `V` has order `|V|_p = p · |A|_p` and is a `p`-subgroup of `D`, so it divides
  `|D|_p = p`, whence `|A|_p = 1`.
* **`C_V(A) = A`**: let `v = a·p ∈ V` (`a ∈ A`, `p ∈ P`) centralise `A`.  Then conjugation by `v`
  is trivial on `A`, so `c_p|_A = c_{a⁻¹}|_A`, i.e. the automorphism of the `p'`-group `A` induced
  by `p` is **inner**.  Its order divides `p`, while the inner automorphism group of `A` has order
  dividing `|A|`, hence is prime to `p`; so `c_p|_A = id`, i.e. `p ∈ C_P(A) = 1`, and `v = a ∈ A`.
* Finally every `x ∈ F₀ ⊓ V` centralises `A` (all of `F₀ = O^{2'}(C_G(A))` does), so `x ∈ A`, and
  every element of `A` commutes with every element of `F₀` (as `F₀ ≤ C_G(A)`), i.e. `x ∈ Z(F₀)`.
The statement is elementwise to avoid subgroup coercions. -/
theorem sec5_setup_centV (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    let C : Subgroup G := Subgroup.centralizer (A : Set G)
    let F₀ : Subgroup G := (Submission.Blueprint.oddResidual ↥C).map C.subtype
    ∀ x : ↥F₀, (x : G) ∈ Submission.Blueprint.centD H t → x ∈ Subgroup.center ↥F₀ := by
  sorry

end Work.NormalComplement
