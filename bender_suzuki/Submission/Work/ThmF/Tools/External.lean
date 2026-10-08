import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# External inputs of Chapter V (not yet discharged)

Peterfalvi's Chapter V §3 proof quotes three results from the literature that are **not** part of
the Bender–Suzuki argument proper (they are classical theorems of finite group theory).  Following
the project lead's instruction (2026-10-02) they are recorded here as *named inputs*, stated as
`Prop`s, so that §3 can be built on them and they can be discharged later from the sources:

* `HallWielandtProp` — **M. Hall**, *The Theory of Groups*, §14.4, p. 212 (Hall–Wielandt):
  a Sylow `p`-subgroup `S`, a weakly closed abelian subgroup `A ≤ S`, then
  `G/O^p(G) ≅ N_G(A)/O^p(N_G(A))` (stated here in the equivalent form that the two groups have no
  quotient of order `p` at the same time).  Used in steps (9), (12), (17).
  NB: the delivered `Work.Grun.hall_14_4_1` is P. Hall's *14.4.1*, a different statement.
* `WielandtFixedPoint` — **Huppert–Blackburn**, XI (12-4) (Wielandt's fixed-point formula), in the
  form in which Peterfalvi II Ch. V §3 step (4) applies it to the Frobenius group `KP` acting on
  `Q`: `|Q| = |C_Q(P)|^{|P|}`.
* `ArithmeticNineTwoSeven` — **Huppert–Blackburn**, IX (2-7), used in steps (6) and (8):
  if `f^a = 2^b + 1` with `f` odd, then `a = 1` or `f^a = 9`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThmF

open Classical

open Submission.Blueprint

/-- **M. Hall §14.4 (Hall–Wielandt), external input.**

Let `S` be a Sylow `p`-subgroup of a finite group `G` and `A ≤ S` a subgroup that is weakly
closed in `S` with respect to `G` (`A^g ≤ S ⟹ A^g = A`).  If `A` is abelian, then
`G/O^p(G) ≅ N_G(A)/O^p(N_G(A))`; equivalently (since a finite group has no quotient of order `p`
iff `O^p` is the whole group) `G` has a normal subgroup of index `p` if and only if `N_G(A)`
does. -/
def HallWielandtProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime →
    ∀ (S : Sylow p G) (A : Subgroup G), A ≤ (S : Subgroup G) →
      (∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) →
        A.map (MulAut.conj g).toMonoidHom = A) →
      (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      (HasNormalIndexP p G ↔ HasNormalIndexP p ↥(Subgroup.normalizer (A : Set G)))

/-- The corollary form of Hall–Wielandt used in Ch. V §3, from the external input
`HallWielandtProp`. -/
theorem hallWielandt_of_external (h : HallWielandtProp) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) (A : Subgroup G) (hA : A ≤ (S : Subgroup G))
    (hwc : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) →
      A.map (MulAut.conj g).toMonoidHom = A)
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    HasNormalIndexP p G ↔ HasNormalIndexP p ↥(Subgroup.normalizer (A : Set G)) :=
  h G p Fact.out S A hA hwc hab

/-- **Huppert–Blackburn XI Theorem 12.4 (Wielandt's order formula), external input.**

`𝔊` is a group of operators on the finite group `𝔖` with `(|𝔊|, |𝔖|) = 1`.  If the sums of the
elements of the subgroups `𝔊₁, …, 𝔊ₘ` satisfy a relation `Σ nᵢ 𝔊ᵢ = 0` in the integral group ring
`MonoidAlgebra ℤ 𝔊`, then `Π |C_𝔖(𝔊ᵢ)|^{nᵢ |𝔊ᵢ|} = 1`; equivalently `Σ nᵢ |𝔊ᵢ| log |C_𝔖(𝔊ᵢ)| = 0`
(stated below in the multiplicative form of rational numbers).

HB XI 12.4 is the ingredient of Peterfalvi II Ch. V §3 step (4): the group ring identity
`Σ_{x∈K} P^x + K = KP + |K|·1` of a Frobenius group `KP` with kernel `K` is a relation between the
subgroups `P^x` (`x ∈ K`), `K`, `KP` and `{1}` with coefficients `1, …, 1, 1, -1, -|K|`, and the
formula gives `|C_Q(P)|^{|K|p} = |Q|^{|K|}`, i.e. `|Q| = |C_Q(P)|^p`, for `C_Q(K) = 1`.

(NB: the OCR of the source's exponent reads `n_i g_i`; the correct exponent is `n_i |𝔊_i|`, which
is the only reading consistent with the worked instances — e.g. `𝔊 = C₂×C₂` acting on `C₃` via
`[A] + [B] + [C] = [𝔊] + 2[{1}]` for the three subgroups of order 2, where `n_i |𝔊_i|` gives
`1·1·3 = 1·3²/3²`, while `n_i` alone fails.  This should be re-checked against the vision
transcription when available.) -/
def WielandtOrderFormula : Prop :=
  ∀ (𝔊 : Type) [Group 𝔊] [Fintype 𝔊] (𝔖 : Type) [Group 𝔖] [Fintype 𝔖]
    (ρ : 𝔊 →* MulAut 𝔖),
    Nat.Coprime (Nat.card 𝔊) (Nat.card 𝔖) →
    ∀ (m : ℕ) (n : Fin m → ℤ) (Gi : Fin m → Subgroup 𝔊),
      (∑ i, n i • ∑ g : 𝔊, if g ∈ Gi i then (MonoidAlgebra.single g (1 : ℤ) : MonoidAlgebra ℤ 𝔊) else 0) = 0 →
      (∏ i ∈ Finset.univ.filter (fun i => 0 < n i),
          (Nat.card {a : 𝔖 // ∀ g ∈ Gi i, ρ g a = a}) ^ ((n i).toNat * Nat.card (Gi i))) =
        (∏ i ∈ Finset.univ.filter (fun i => n i < 0),
          (Nat.card {a : 𝔖 // ∀ g ∈ Gi i, ρ g a = a}) ^ ((-n i).toNat * Nat.card (Gi i)))

/-- **Wielandt's fixed-point formula in the form used in Peterfalvi II Ch. V §3 step (4).**

`K` acts fixed-point-freely on the finite group `Q` (`C_Q(k) = 1` for `k ∈ K#`), `P` has prime
order `p`, and `KP` is a Frobenius group with kernel `K` and complement `P`: `K` is normalised by
`P` (`K ⊴ KP`, `P ⊓ K = 1`) and the conjugates of `P` under `K` meet `P` trivially
(`P ⊓ P^k = 1` for `k ∈ K#`) — equivalently `P` is a Frobenius complement.  Then
`|Q| = |C_Q(P)|^p`.  This is the specialisation of `WielandtOrderFormula` (HB XI 12.4) to the
relation `Σ_{x∈K} P^x + K = KP + |K|·1`.

**Corrected 2026-10-05.**  The Frobenius clause was previously transcribed as
`K ⊓ conj g⁻¹ K = ⊥ for g ∈ P#` (conjugating the *kernel*); that clause is satisfied by two
distinct Sylow `7`-subgroups `K, P` of `GL(3,2)`, for which the conclusion reads `8 = |C_Q(P)|^7`
— false.  The clause must be (a) `K ⊴ KP`, i.e. `P` normalises `K`, and (b) `P ⊓ P^k = ⊥` for
`k ∈ K#`, which together express that `P` is a Frobenius complement with kernel `K`.  See
`Work.ThmF.ChV3.step5`'s history. -/
def WielandtFixedPoint : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (p : ℕ), p.Prime →
    ∀ (K P : Subgroup (MulAut Q)),
      Nat.Coprime (Nat.card K * Nat.card P) (Nat.card Q) →
      (∀ k ∈ K, k ≠ 1 → ∀ q : Q, k q = q → q = 1) →
      (∀ q : Q, (∀ k ∈ K, k q = q) → q = 1) →
      Nat.card P = p →
      (∀ g ∈ P, ∀ k ∈ K, g * k * g⁻¹ ∈ K) →
      (∀ k ∈ K, k ≠ 1 → P ⊓ conj k⁻¹ P = ⊥) →
      Nat.card Q = (Set.ncard {q : Q | ∀ g ∈ P, g q = q}) ^ p

/-- **Huppert–Blackburn IX (2-7), external input**: if `f^a = 2^b + 1` with `f` odd, then
`a = 1` or `f^a = 9`. -/
def ArithmeticNineTwoSeven : Prop :=
  ∀ (f a b : ℕ), Odd f → 2 ≤ f → 0 < a → f ^ a = 2 ^ b + 1 → a = 1 ∨ f ^ a = 9

end Work.ThmF
