import Submission.Work.ZassenhausSuzuki.Recognition

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ZassenhausSuzuki`: the two halves of the Suzuki core

`SuzukiCoreProp` (see `Recognition.lean`) is the family-specific input of the Suzuki case.  It
factors into two independent inputs, matching the two halves of Suzuki's proof:

* `SuzukiDataProp` — the **structure of `Q`**: `Q` carries a coordinatisation
  `e : Q ≃* A(K,θ)` by Higman's group (`K = GF(2^m)`, `m` odd, `θ` a Tits endomorphism)
  such that the two-point stabiliser `D = H ∩ H^t` acts through the standard torus `Λ`
  (`h_λ`).  Proof ingredients: Feit 1960 / HB III XI §6 (`Q` is a 2-group — a hypothesis
  here), Baumeister–Grüninger 4.6, 5.6, 5.9 (`Q` is a Suzuki 2-group of order `q²`,
  `q = |Z(Q)|`, and the Hua group is cyclic of order `q-1`), Higman 1963 through
  `HigmanProp` (`szA_of_isSuzukiTwoGroup`), and Suzuki 1962, *Lemma 6* (the cyclic group of
  order `q-1` acting fixed-point-freely on the involutions is conjugate to `Λ`, see
  `SuzukiLemma6Prop`).
* `SuzukiFProp` — the **computation of `f`**: in those coordinates the book's map `f`,
  characterised by `t x t = g(x)h(x) t f(x)` (`FRel H t x y`), is the Suzuki map `τ`
  (`SzA.sigma`).  Proof ingredients: Suzuki 1962, §4–5 (equivalently HB III XI §11, or
  Baumeister–Grüninger §5.16–5.21); this is also where the *Tits* property of `θ` is
  obtained (BG 5.21), which is why `SuzukiDataProp` mentions it as a hypothesis of the
  parametrisation.

`SuzukiLemma6Prop` is the transcription of Suzuki's Lemma 6 into the vocabulary of this area
(REFS/vision/suzuki1962/p0010.md):

> **Lemma 6.** *Let `Z'` be a cyclic group of automorphisms of `S(q;x)`.  Suppose that the
> order of `Z'` is `q - 1` and no element `≠ 1` leaves an involution of `S(q;x)` invariant.
> Then there is an automorphism `θ` of `S(q;x)` such that `Z' = θ⁻¹ Z θ`.*

Here `S(q;x) = A(GF(2^m), θ)` with `q = 2^m` and `Z = Λ = ` the image of `h_λ` (the standard
cyclic group of order `q-1` acting on the centre by multiplication).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness

namespace Work.ZassenhausSuzuki

/-- **Suzuki 1962, Lemma 6.**  Let `A(GF(2^m), θ)` be a Suzuki 2-group (`θ ≠ 1` of odd order,
`q = 2^m`).  A cyclic subgroup `Z'` of its automorphism group of order `q - 1` acting without
non-trivial fixed points on the involutions is conjugate under `Aut A` to the standard torus
`Λ = {h_λ}`.  (Cf. `REFS/vision/suzuki1962/p0010.md`.) -/
def SuzukiLemma6Prop : Prop :=
  ∀ (m : ℕ) (θ : GaloisField 2 m ≃+* GaloisField 2 m), θ ≠ 1 → Odd (orderOf θ) →
    ∀ Z' : Subgroup (MulAut (SzA (GaloisField 2 m) θ)),
      IsCyclic Z' → Nat.card Z' = 2 ^ m - 1 →
      (∀ z ∈ Z', z ≠ 1 → ∀ x : SzA (GaloisField 2 m) θ, x * x = 1 → z x = x → x = 1) →
      ∃ ψ : MulAut (SzA (GaloisField 2 m) θ),
        Z' = ((SzA.hLamHom θ).range).map (MulAut.conj ψ).toMonoidHom

/-- **The structure half of the Suzuki core.**  A simple split rank-one Zassenhaus
configuration with non-abelian 2-group `Q` admits a Tits parametrisation `(m, θ)` of `Q` by
Higman's group `A(GF(2^m), θ)` under which the two-point stabiliser acts through the standard
torus `Λ`. -/
def SuzukiDataProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    ∀ (H Q : Subgroup G) (t : G), IsSplitRankOne H Q t → IsZassenhaus H →
      IsPGroup 2 Q → ¬ IsAbelianSubgroup Q →
      ∃ (m : ℕ) (_ : Odd m) (_ : 3 ≤ m) (θ : GaloisField 2 m ≃+* GaloisField 2 m),
        IsTitsTheta θ ∧ ∃ e : Q ≃* SzA (GaloisField 2 m) θ,
          ∀ d : G, d ∈ twoPoint H t → ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
            ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
              e y = SzA.hLam θ (lam : GaloisField 2 m) (e x)

/-- **The `f`-computation half of the Suzuki core.**  In the coordinates of `SuzukiDataProp`,
the book's map `f` (`FRel H t x y`) is the Suzuki map `τ`. -/
def SuzukiFProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    ∀ (H Q : Subgroup G) (t : G), IsSplitRankOne H Q t → IsZassenhaus H →
      ∀ (m : ℕ) (θ : GaloisField 2 m ≃+* GaloisField 2 m), IsTitsTheta θ →
        ∀ e : Q ≃* SzA (GaloisField 2 m) θ,
          (∀ d : G, d ∈ twoPoint H t → ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
            ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
              e y = SzA.hLam θ (lam : GaloisField 2 m) (e x)) →
          ∀ x : Q, x ≠ 1 → FRel H t (x : G) (((e.symm (SzA.sigma θ (e x)) : Q) : G))

/-- `SuzukiCoreProp` follows from the two halves `SuzukiDataProp` + `SuzukiFProp`. -/
theorem suzukiCoreProp_of (hData : SuzukiDataProp) (hF : SuzukiFProp) : SuzukiCoreProp := by
  intro G hGrp hFin hsimple H Q t hsplit hzass h2grp hnab
  letI := hGrp
  letI := hFin
  obtain ⟨m, hm, hm3, θ, hθ, e, htorus⟩ := hData G hsimple H Q t hsplit hzass h2grp hnab
  exact ⟨m, hm, hm3, θ, hθ,
    ⟨{ split := hsplit, zassenhaus := hzass, nonabelian := hnab, e := e,
       frel := hF G hsimple H Q t hsplit hzass m θ hθ e htorus }⟩⟩

end Work.ZassenhausSuzuki
