import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Serre.Engine
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.cylRelPi
import Submission.Work.Serre.RangeOne.rangeWhitehead
import Submission.Work.Serre.rwMapTop
import Submission.Work.Serre.rwPiBijectiveOfRelPiVanishing
import Submission.Work.RatHurewicz.compression_of_relPiVanishing
import Submission.Work.Cohomology.good_empty
import Submission.Work.Cohomology.isZero_dualComplex_empty
import Submission.Work.RatHurewicz.Excision
import Submission.Work.RatHurewicz.LESConsequences

namespace Work.Serre

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology unitInterval Simplicial

/-- **The singular homology of an empty space vanishes** (rational coefficients). -/
theorem isZero_ratH_of_isEmpty (X : Type) [TopologicalSpace X] [IsEmpty X] (m : ℕ) :
    IsZero (ratH (TopCat.of X) m) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  refine ShortComplex.exact_of_isZero_X₂ _ ?_
  have h : IsEmpty ((TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op ⦋m⦌)) := by
    refine ⟨fun x => ?_⟩
    have hx := (TopCat.toSSetObjEquivT (TopCat.of X) (Opposite.op ⦋m⦌)) x
    haveI : Nonempty (↑(stdSimplex ℝ (Fin ((Opposite.unop (Opposite.op ⦋m⦌)).len + 1)))) :=
      inferInstance
    exact isEmptyElim (hx (Classical.arbitrary _))
  haveI := h
  exact Work.Cohomology.isZero_coproduct_of_isEmpty
    (fun _ : ((TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op ⦋m⦌)) => ModuleCat.of ℚ ℚ)

/-- **Range form of the relative Hurewicz result (the extra degree of the range-Whitehead claim).**

Let `i : C(A, W)`, `F_a = homotopyFibre i a` and `Rel a k = RelHomotopyGroup i a k = π_k(F_a)` (so
`Rel a k` is the classical `π_{k+1}(W, A, a)`).  Assume
* `hconn0` : every point of `W` is joined by a path to a point of `i(A)` (i.e. `i` is surjective on
  `π₀`; equivalently the pair `(W, A)` is `0`-connected),
* `hconn` : at every base point `a : A`, `Rel a k` is trivial for `k ≤ n` (the map is
  `(n+1)`-connected), and
* `htop` : at every `a : A`, the projection `homotopyFibreFst i a : F_a → A` induces the zero map
  `Rel a (n+1) → π_{n+1}(A, a)`.
Then `H_j(i; ℚ)` is an isomorphism for `1 ≤ j ≤ n + 1`.

Both extra hypotheses are necessary.  Without `hconn0`, `A = S¹ ↪ W = S¹ ⊔ S¹` (first summand, any
`n`) has all fibres contractible — so `hconn`/`htop` hold at every base point — yet `H₁(i;ℚ)` misses
the second summand.  Without the pointwise form of `hconn`/`htop`, `A = W = PUnit ⊕ S¹` with `i` the
identity on the first summand and the constant map on the second, based at the first summand, has
`homotopyFibre i a₀` a point, yet `H₁(i;ℚ) = 0 : ℚ → ℚ`.

The proof factors through the mapping cylinder of `i`: the hypothesis gives the bijectivity of `i` on
`π_q` for `q ≤ n + 1`, `Work.Serre.rwPiBijectiveOfRelPiVanishing`; the range-Whitehead theorem
`Work.Serre.RangeOne.rangeWhitehead` then gives the isomorphism in degrees `≤ n`, and the extra top
degree `j = n + 1` is `Work.Serre.rwMapTop`. -/
theorem rangeWhiteheadPair (n : ℕ) {A W : Type} [TopologicalSpace A] [TopologicalSpace W]
    (i : C(A, W))
    (hconn0 : ∀ w : W, ∃ a : A, Nonempty (Path w (i a)))
    (hconn : ∀ (a : A) (k : ℕ), k + 1 ≤ n + 1 → Subsingleton
      (Work.RatHurewicz.RelHomotopyGroup i a k))
    (htop : ∀ (a : A) (x : Work.RatHurewicz.RelHomotopyGroup i a (n+1)),
      Work.Serre.piMapN (Work.RatHurewicz.homotopyFibreFst i a) (n+1)
        (Work.RatHurewicz.homotopyFibreBasepoint i a) x = 1) :
    ∀ j : ℕ, 1 ≤ j → j ≤ n + 1 → _root_.CategoryTheory.IsIso (Work.Serre.ratHomologyMap i j) := by
  intro j hj1 hj2
  have hpi : ∀ (q : ℕ), q ≤ n + 1 → ∀ a : A,
      Function.Bijective (Work.Serre.piMapN i q a) :=
    Work.Serre.rwPiBijectiveOfRelPiVanishing n i hconn0 hconn htop
  by_cases hA : Nonempty A
  · haveI : Nonempty A := hA
    rcases lt_or_ge j (n + 1) with hlt | hge
    · exact RangeOne.rangeWhitehead A W (Classical.arbitrary A) i (n + 1)
        (fun q hq x => hpi q hq x) j hlt
    · have hj : j = n + 1 := by omega
      subst hj
      exact Work.Serre.rwMapTop n i hconn0 hpi
  · haveI : IsEmpty A := not_nonempty_iff.mp hA
    haveI : IsEmpty W := ⟨fun w => by obtain ⟨a, -⟩ := hconn0 w; exact hA ⟨a⟩⟩
    exact IsZero.isIso (isZero_ratH_of_isEmpty A j) (isZero_ratH_of_isEmpty W j) _

end

end Work.Serre
