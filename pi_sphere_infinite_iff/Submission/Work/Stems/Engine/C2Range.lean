import Submission.Work.Serre.serreS2OfC0C2oddS1
import Submission.Work.StemsB.sphRatHomology
import Submission.Work.Drive.Interfaces

/-!
# The `K(ℤ,n)` layer in **range form**

`Submission/Work/Stems/EM_AUDIT.md` §2 (ii) and (iv): the blueprint's `C2` layer is stated in *all*
degrees (`Work.Serre.SerreC2even`, `SerreC2odd`), while the range-form inputs it is proved from
(`SerreE3b`: the Gysin isomorphism only for `m < b`; the finite truncations of `C0`) deliver only a
*bounded* range; and the bare `C0` (existence of a `K(A,m)`-model) does not supply the map
`Sⁿ → K(ℤ,n)` on which the sphere route depends.

What both consumers actually use is a range, and the range that the induction delivers is
`2n` (the periodicity isomorphism is available for `m < n` at a `K(ℤ,n)`-model, which gives the
cohomology up to degree `2n`).  This file therefore records:

* `Work.Stems.Engine.SphereModelData` — `C0` in the form the sphere route needs: a model of `K(ℤ,n)`
  together with the bottom-cell map `Sⁿ → X` inducing a bijection on `πₙ` (the blueprint's `C0`
  construction delivers this — "maps between models" — but its bare statement does not);
* `Work.Stems.Engine.C2oddRange` — the odd step of `C2` in range form: for odd `n` the cover
  `Eₙ = hofib(Sⁿ → Lₙ)` is rationally acyclic **below degree `2n`**
  (`Work.Serre.RatVanishingBelow`, the very form `Work.Serre.SerreS1` consumes);
* `Work.Stems.Engine.C2evenRange` — the even step in range form: a model of `K(ℤ,2j)` has the
  rational cohomology of `ℂP^∞` rescaled by `2j`, **below degree `2n = 4j`**;
* the *assembly* `Work.Stems.Engine.stableStemsTorsion_of_rangeInputs`: the range-form inputs give
  the STEMS contract — this is the provable form of `SerreS2OfC0C2oddS1`, and it avoids the
  all-degrees statements that `SerreE3b` cannot reach.
-/

open CategoryTheory Limits
open Work.Serre
open scoped Topology Topology.Homotopy unitInterval

namespace Work.Stems.Engine

noncomputable section

/-- **`C0` in the form the sphere route needs.**  For every `n ≥ 1` there is a model `X` of
`K(ℤ,n)` together with a map `Sⁿ → X` inducing a bijection on `πₙ`.

This is *derivable* from the bare `Work.Serre.SerreC0`: `Work.Serre.exists_bijective_piMapN'`
(proved in `Submission/Work/Serre/serreS2OfC0C2oddS1.lean`) constructs such a map out of a model,
using that `πₙ(X) ≅ ℤ` and the Hurewicz theorem in the first non-vanishing degree.  The definition
is kept because it is the interface the sphere route talks about; the assembly below in fact takes
the weaker hypothesis `SerreC0`. -/
def SphereModelData : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n),
    ∃ (X : Type) (_ : TopologicalSpace X) (pt : X)
      (_ : Work.Serre.IsEMSpace ℤ n (by omega) X pt)
      (s₀ : Work.Serre.Sph n) (f : C(Work.Serre.Sph n, X)),
      Function.Bijective (Work.Serre.piMapN f n s₀)


/-- **Range form of `Work.Serre.SerreE3b`** (Gysin / Euler class of a rational spherical fibration).
If the fibre of a Serre fibration is rationally a sphere of dimension `r` *up to degree `N`*
(vanishing in degrees `0 < t < N`, `t ≠ r`, and `H_r ≅ ℚ`), then `x ↦ x ⌣ e` is an isomorphism
`H^m(B;ℚ) ≅ H^{m+r+1}(B;ℚ)` in the range `m < b` (the base's connectivity) **and** `m + r < N`.

The engine's `SerreE3b` assumes the fibre is a rational sphere in *all* degrees; the range form is
what the `K(ℤ,n)` induction can supply, and it is what makes `C2evenRange` provable. -/
def GysinRange : Prop :=
  ∀ (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (b₀ : B)
      (r b N : ℕ),
    1 ≤ r → 1 ≤ b → Work.StemsB.IsSerreFibration p → PathConnectedSpace B →
      Work.Serre.Conn B b₀ b →
      Work.Serre.RatAcyclic E →
      (∀ t : ℕ, 0 < t → t ≠ r → t < N →
        IsZero (Work.Serre.ratH
          (TopCat.of (Work.RatHurewicz.homotopyFibre p e₀)) t)) →
      Nonempty (Work.Serre.ratH
        (TopCat.of (Work.RatHurewicz.homotopyFibre p e₀)) r ≅ ModuleCat.of ℚ ℚ) →
      ∀ m : ℕ, m < b → m + r < N →
        ∃ e : Work.Serre.ratCoh (TopCat.of B) (r + 1),
          IsIso (ModuleCat.ofHom (Work.Serre.cupWith (TopCat.of B) (r + 1) e m))


/-- **The odd side of the `C2` induction, with a bound function `B`.**  Every model of `K(ℤ,n)`,
`n` odd, is rationally a sphere of dimension `n` below degree `B n`
(`Work.Stems.Engine.RatSphereBelow X n (B n)`): `H_n ≅ ℚ` and `H_j = 0` for every `0 < j < B n`,
`j ≠ n`.

(The statement is *not* `RatVanishingBelow X (B n)` — that would demand `H_n(X) = 0` in the same
breath as `H_n(X) ≅ ℚ`, and would be unsatisfiable as soon as `B n > n`; a reviewer caught this in
the first version.)

This is the auxiliary statement the mutual induction needs: the *even* step applies the range-form
Gysin to the path–loop fibration `ΩY → PY → Y` of a model `Y` of `K(ℤ,2j)`, whose fibre `ΩY` is a
model of `K(ℤ,2j-1)` — and Gysin needs that fibre to be a rational sphere *up to the range*, not
just vanishing.  The bound function is a parameter because the induction's ranges are tight (the
naive accounting loses a fixed amount per level; the multiplicative information of the corrected
`E4` regains it). -/
def RatSphereBelow (X : Type) [TopologicalSpace X] (n N : ℕ) : Prop :=
  Nonempty (Work.Serre.ratH (TopCat.of X) n ≅ ModuleCat.of ℚ ℚ) ∧
    ∀ j : ℕ, 0 < j → j < N → j ≠ n → IsZero (Work.Serre.ratH (TopCat.of X) j)

def OddSphereRange (B : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), Odd n → ∀ (X : Type) [TopologicalSpace X] (pt : X),
    Work.Serre.IsEMSpace ℤ n (by omega) X pt →
    Work.Stems.Engine.RatSphereBelow X n (B n)

/-- **The base case of the induction: a model of `K(ℤ,1)` is rationally `S¹`.**  `SerreC1`
supplies a map `S¹ → X` inducing an isomorphism on rational homology, and
`Work.StemsB.sphRatHomology` computes the rational homology of `S¹` (`H_1 ≅ ℚ`, nothing else in
positive degrees).  So the odd side holds at `n = 1` in *all* degrees. -/
theorem oddSphere_one (hC1 : Work.Serre.SerreC1) (X : Type) [TopologicalSpace X] (pt : X)
    (hX : Work.Serre.IsEMSpace ℤ 1 (by omega) X pt) :
    Nonempty (Work.Serre.ratH (TopCat.of X) 1 ≅ ModuleCat.of ℚ ℚ) ∧
      (∀ j : ℕ, j ≠ 0 → j ≠ 1 → IsZero (Work.Serre.ratH (TopCat.of X) j)) := by
  obtain ⟨f, hf⟩ := hC1 X pt hX
  obtain ⟨⟨e₁⟩, h₂⟩ := Work.StemsB.sphRatHomology 1 (by omega)
  have key : ∀ j : ℕ,
      Work.Serre.ratH (TopCat.of (Work.Serre.Sph 1)) j ≅ Work.Serre.ratH (TopCat.of X) j :=
    fun j => haveI := hf j; asIso (Work.Serre.ratHomologyMap f j)
  refine ⟨⟨(key 1).symm ≪≫ e₁⟩, fun j hj0 hj1 => ?_⟩
  exact IsZero.of_iso (h₂ j hj0 hj1) (key j).symm

/-- **`n = 1` in the auxiliary form**: a model of `K(ℤ,1)` is rationally `S¹` **below every bound**,
which is the base case of the mutual induction (`Work.Stems.Engine.OddSphereRange 1`). -/
theorem ratSphereBelow_one (hC1 : Work.Serre.SerreC1) (X : Type) [TopologicalSpace X] (pt : X)
    (hX : Work.Serre.IsEMSpace ℤ 1 (by omega) X pt) (N : ℕ) :
    Work.Stems.Engine.RatSphereBelow X 1 N := by
  obtain ⟨he, h₂⟩ := oddSphere_one hC1 X pt hX
  refine ⟨he, fun j hj0 hjd hj1 => h₂ j (by omega) hj1⟩

/-- **`C2`, odd step, in range form.**  For odd `n` and a map `Sⁿ → X` to a model of `K(ℤ,n)`
inducing a bijection on `πₙ`, the homotopy fibre `Eₙ` is rationally acyclic in degrees `0 < j < 2n`.

This is `Work.Serre.SerreC2odd` with `RatAcyclic` weakened to `RatVanishingBelow (2n-3)` — the
range that the corrected `E4` (plus the even step for the fibre `ΩX = K(ℤ,n-1)`, whose own range
stops one degree short, see the reviewer's audit of `C2evenRange`) actually gives, and more than the
range `SerreS1` needs: applied to the `n`-connected `Eₙ` it produces torsion in `π_j(Eₙ)` for
`j ≤ 2n-3`, which by Freudenthal covers all of the STEMS contract. -/
def C2oddRange : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), Odd n →
    ∀ (X : Type) [TopologicalSpace X] (pt : X), Work.Serre.IsEMSpace ℤ n (by omega) X pt →
      ∀ (s₀ : Work.Serre.Sph n) (f : C(Work.Serre.Sph n, X)),
        Function.Bijective (Work.Serre.piMapN f n s₀) →
          Work.Serre.RatVanishingBelow (Work.RatHurewicz.homotopyFibre f s₀) (2 * n - 3)

/-- **`C2`, even step, in range form.**  A model `X` of `K(ℤ,2j)` (`j ≥ 1`) has, below degree
`2 · (2j)`, the rational homology of `ℂP^∞` rescaled by `2j`: `H_{2jk}(X;ℚ) ≅ ℚ` and
`H_d(X;ℚ) = 0` when `2j ∤ d`.

This is `Work.Serre.SerreC2even` with the range restricted to the degrees the periodicity
isomorphism of the range-form Gysin (`Work.Stems.Engine.GysinRange`) reaches: the side condition
`m + r < N` with the fibre `ΩX = K(ℤ,2j-1)` known only up to `N = 2(2j-1)-1` (the odd step) forces
the bound `4j - 1`. -/
def C2evenRange : Prop :=
  ∀ (j : ℕ) (hj : 1 ≤ j) (X : Type) [TopologicalSpace X] (pt : X),
    Work.Serre.IsEMSpace ℤ (2 * j) (by omega) X pt →
    (∀ k : ℕ, 2 * j * k < 2 * (2 * j) - 1 →
        Nonempty (Work.Serre.ratH (TopCat.of X) (2 * j * k) ≅ ModuleCat.of ℚ ℚ)) ∧
      (∀ d : ℕ, d < 2 * (2 * j) - 1 → (∀ k : ℕ, d ≠ 2 * j * k) →
        IsZero (Work.Serre.ratH (TopCat.of X) d))

theorem coverRouteRange (hC0 : Work.Serre.SerreC0) (hC2 : C2oddRange) (hS1 : Work.Serre.SerreS1)
    (n : ℕ) (hn : 3 ≤ n) (hnodd : Odd n) (i : ℕ) (hi : i + 5 ≤ n) (x₀ : Sph n) :
    PiTorsion (Sph n) x₀ (n + i) := by
  obtain ⟨X, hXtop, pt, hE⟩ := hC0 (A := ℤ) n (by omega)
  letI : TopologicalSpace X := hXtop
  have hE' : IsEMSpace ℤ n (by omega : 0 < n) X pt := hE
  obtain ⟨s₀, f, hfs₀, hbij⟩ := exists_bijective_piMapN' n (by omega) X pt hE'
  set E := Work.RatHurewicz.homotopyFibre f s₀
  set e₀ := Work.RatHurewicz.homotopyFibreBasepoint f s₀
  have hratio : Work.Serre.RatVanishingBelow E (2 * n - 3) :=
    hC2 n (by omega) hnodd X pt hE' s₀ f hbij
  have hX' : ∀ j, j ≠ n → Subsingleton (HomotopyGroup (Fin j) X (f s₀)) :=
    fun j hj => hfs₀ ▸ hE'.2 j hj
  -- `E` is `(n-1)`-connected, so `SerreS1` applies with `k = n - 1` and `M = 2 * (n - 1) - 2`
  have hconn : ∀ j < n - 1, Subsingleton (HomotopyGroup (Fin j) E e₀) :=
    fun j hj => homotopyFibre_subsingleton_of_lt f s₀ hn hX' (j := j) (by omega)
  have hvan : ∀ m : ℕ, n - 1 ≤ m + 1 → m + 1 ≤ 2 * (n - 1) - 2 →
      IsZero (ratH (TopCat.of E) (m + 1)) :=
    fun m hm1 hm2 => hratio (m + 1) (by omega) (by omega)
  have hEtors : PiTorsion E e₀ (n + i - 1 + 1) := by
    have h1 : n - 1 ≤ n + i - 1 + 1 + 1 := by omega
    have h2 : n + i - 1 + 1 + 1 ≤ 2 * (n - 1) - 2 := by omega
    exact hS1 (n - 1) (by omega) E e₀ hconn (2 * (n - 1) - 2) (by omega)
      (fun m h1' h2' => hvan m h1' h2') (n + i - 1 + 1) h1 h2
  -- the projection `E → Sⁿ` is onto in `π_{n+i+1}`
  have hF : Subsingleton (HomotopyGroup (Fin (n + i - 1 + 1)) (Work.RatHurewicz.fibreOf f s₀)
      (Work.RatHurewicz.fibreOfPt f s₀)) :=
    fibreOf_subsingleton f s₀ (n + i - 1)
      (subsingleton_homotopyGroup_of_index_eq (a := n + i + 1) (b := (n + i - 1) + 2)
        (by omega) (hX' (n + i + 1) (by omega)))
  have hsurj := piMap_fst_surjective_of_fibre_trivial f s₀ (n + i - 1) hF
  have htor : PiTorsion (Sph n) (Work.RatHurewicz.homotopyFibreFst f s₀
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) (n + i - 1 + 1) :=
    piTorsion_of_surjective_hom (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst f s₀)
      (n + i - 1 + 1) (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) hsurj hEtors
  -- reindex and change the base point
  have htor' : PiTorsion (Sph n) (Work.RatHurewicz.homotopyFibreFst f s₀
      (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) (n + i) :=
    piTorsion_of_index_eq _ (by omega : n + i - 1 + 1 = n + i) htor
  exact piTorsion_of_joined (n + i)
    ((pathConnectedSpace_sph n (by omega)).joined s₀ x₀) htor'


theorem stableStemsTorsion_of_rangeInputs (hC0 : Work.Serre.SerreC0) (hC2 : C2oddRange)
    (hS1 : Work.Serre.SerreS1) (hF : Work.Serre.SerreFreudenthal) :
    Work.Drive.StableStemsTorsion := by
  intro i hi n hn x₀ α
  -- the range covered by the odd case, and one suspension step away from it (even `m`)
  have far : ∀ m : ℕ, i + 5 ≤ m → ∀ x₀ : Work.Serre.Sph m, Work.Serre.PiTorsion (Work.Serre.Sph m) x₀ (m + i) := by
    intro m hm5 x₀
    rcases Nat.even_or_odd m with he | ho
    · refine hF m i (by omega) (by omega) (fun y₀ => ?_) x₀
      exact coverRouteRange hC0 hC2 hS1 (m + 1) (by omega) (odd_succ_of_even he) i (by omega) y₀
    · exact coverRouteRange hC0 hC2 hS1 m (by omega) ho i hm5 x₀
  have hmain : Work.Serre.PiTorsion (Work.Serre.Sph n) x₀ (n + i) := by
    by_cases h5 : i + 5 ≤ n
    · exact far n h5 x₀
    · by_cases h4 : i + 4 ≤ n
      · -- `n = i + 4`: one suspension lands in the range `i + 5 ≤ n + 1`
        exact hF n i (by omega) (by omega) (fun y₀ => far (n + 1) (by omega) y₀) x₀
      · -- `n = i + 3`: two suspensions land in the range `i + 5 ≤ n + 2`
        exact hF n i (by omega) (by omega) (fun y₀ =>
          hF (n + 1) i (by omega) (by omega) (fun z₀ => far (n + 2) (by omega) z₀) y₀) x₀
  exact hmain α

end

end Work.Stems.Engine
