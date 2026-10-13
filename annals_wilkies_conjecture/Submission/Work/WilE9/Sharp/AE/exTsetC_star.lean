import Mathlib
import Submission.Work.WilE9.Sharp.AE.Basic
import Submission.Work.WilE9.Sharp.exSemiPf_bounds
import Submission.Work.WilE9.Sharp.exSemiPf_deg_bound
import Submission.Work.WilE9.Sharp.exTset_star
import Submission.Work.WilE8.StarOfSemipfLe.star_of_semipf_le
import Submission.Work.WilE9.Sharp.AE.union_components_star

/-!
  WilE9 / Sharp / AE — `exTsetC` is a `Star`-set.

  `exTsetC n m E q L` is the projection to the first `n + 1` coordinates of `exComp n m E q L`,
  the union of the connected components of the extended set `(exSemiPf n m E L).set` through the
  points whose stratum coordinates lie in the component `connectedComponentIn E.X.set q`
  (`AE/Basic.lean`).

  The two structural facts used below are that this union is *saturated* (`exComp_subset_set`,
  `exComp_componentIn_subset`): `exComp` is a union of connected components of the extended set.
  The component bound `hE2` then yields a finite hitting set of the components, and restricting it
  to the components contained in `exComp` presents `exComp` by finitely many pieces — this is
  `Work.WilE9.Sharp.AE.union_components_star`, the component-restricted form of
  `Work.WilE8.StarOfSemipfLe.star_of_semipf_le`.

  The degree bookkeeping is that of `Sharp/exTset_star.lean`: the extended system has format the
  constant `Next n a₀ + a₀` (uniform in `m ≤ a₀` and `E.X.fmt ≤ a₀`), and its degree is bounded by
  `b₀` evaluated at `(E.deg, |L|, a₀)` for a fixed `b₀` (`Sharp/exSemiPf_deg_bound`, which takes the
  external budget `D = E.deg` and the hypothesis `E.X.basics.length ≤ E.deg + 1`).  Substituting
  the component-bound monomial `q.eval d · d` into `b₀` gives the single polynomial `b`.
-/

namespace Work.WilE9.Sharp.AE

open Classical WilkiesDesign WilkiesDesign.E

/-- `exComp n m E q L` is contained in the extended set `(exSemiPf n m E L).set`, of which it is
a union of connected components. -/
theorem exComp_subset_set {n m : ℕ} (E : Work.WilE9.Sharp.EffStratum n m)
    (q : Fin (n + (1 + m)) → ℝ) (L : List (Fin n)) :
    Work.WilE9.Sharp.exComp n m E q L ⊆ (Work.WilE9.Sharp.exSemiPf n m E L).set := by
  intro z hz
  simp only [Work.WilE9.Sharp.exComp, Set.mem_iUnion, exists_prop] at hz
  obtain ⟨z', -, hzmem⟩ := hz
  exact connectedComponentIn_subset _ _ hzmem

/-- `exComp n m E q L` is a *union* of connected components of `(exSemiPf n m E L).set`: the
component of any of its points is contained in it. -/
theorem exComp_componentIn_subset {n m : ℕ} (E : Work.WilE9.Sharp.EffStratum n m)
    (q : Fin (n + (1 + m)) → ℝ) (L : List (Fin n)) :
    ∀ z ∈ Work.WilE9.Sharp.exComp n m E q L,
      connectedComponentIn (Work.WilE9.Sharp.exSemiPf n m E L).set z ⊆
        Work.WilE9.Sharp.exComp n m E q L := by
  intro z hz
  simp only [Work.WilE9.Sharp.exComp, Set.mem_iUnion, exists_prop] at hz
  obtain ⟨z', hz', hzmem⟩ := hz
  rw [← connectedComponentIn_eq hzmem]
  intro w hw
  exact Set.mem_iUnion.mpr ⟨z', Set.mem_iUnion.mpr ⟨hz', hw⟩⟩

theorem exTsetC_star
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (n a₀ : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 3) ℕ),
      ∀ (m : ℕ) (E : Work.WilE9.Sharp.EffStratum n m) (q : Fin (n + (1 + m)) → ℝ)
        (L : List (Fin n)),
        m ≤ a₀ → E.X.fmt ≤ a₀ → E.X.basics.length ≤ E.deg + 1 →
        WilkiesDesign.E.Star a (MvPolynomial.eval ![E.deg, L.length, a₀] b) (n + 1)
          (Work.WilE9.Sharp.exTsetC n m E q L) := by
  classical
  -- the degree bound for the extended system, at the external budget `D = E.deg`
  obtain ⟨b₀, hb₀⟩ := Work.WilE9.Sharp.exSemiPf_deg_bound n a₀
  -- the format is the constant `Next n a₀ + a₀`; the monomial `q.eval d · d` is substituted into `b₀`
  refine ⟨Work.WilE9.Sharp.Next n a₀ + a₀,
    Polynomial.eval₂ MvPolynomial.C b₀
      ((hE2 (Work.WilE9.Sharp.Next n a₀ + a₀)).choose * Polynomial.X), ?_⟩
  intro m E q L hm hfmt hlen
  -- the format of the extended system, uniformly in `m ≤ a₀` and `E.X.fmt ≤ a₀`
  have hfmt' : (Work.WilE9.Sharp.exSemiPf n m E L).fmt ≤ Work.WilE9.Sharp.Next n a₀ + a₀ := by
    have h1 : Work.WilE9.Sharp.Next n m ≤ Work.WilE9.Sharp.Next n a₀ := by
      simp only [Work.WilE9.Sharp.Next]; omega
    have h2 : E.X.r ≤ a₀ := by
      have h := hfmt
      simp only [SemiPf.fmt] at h
      omega
    show Work.WilE9.Sharp.Next n m + E.X.r ≤ Work.WilE9.Sharp.Next n a₀ + a₀
    omega
  have hdeg_b := hb₀ m E L E.deg hm hfmt le_rfl hlen
  -- the component bound for the component-restricted extended set
  have hstar := union_components_star hE2 (n + 1) (n + m + 3)
    (Work.WilE9.Sharp.Next n a₀ + a₀) (Work.WilE9.Sharp.exSemiPf n m E L) hfmt'
    (Work.WilE9.Sharp.exComp n m E q L) (exComp_subset_set E q L)
    (exComp_componentIn_subset E q L)
  -- and its degree, substituted into the monomial `q.eval d · d`
  have hmul : (hE2 (Work.WilE9.Sharp.Next n a₀ + a₀)).choose.eval
        (Work.WilE9.Sharp.exSemiPf n m E L).deg * (Work.WilE9.Sharp.exSemiPf n m E L).deg ≤
      MvPolynomial.eval ![E.deg, L.length, a₀]
        (Polynomial.eval₂ MvPolynomial.C b₀
          ((hE2 (Work.WilE9.Sharp.Next n a₀ + a₀)).choose * Polynomial.X)) := by
    rw [Work.WilE9.Sharp.mvpoly_eval_eval₂_C, Polynomial.eval_mul, Polynomial.eval_X]
    exact Nat.mul_le_mul (Work.WilE9.Ift.OneShot.poly_eval_le hdeg_b) hdeg_b
  exact Work.WilE8.Star.mono hstar le_rfl hmul

end Work.WilE9.Sharp.AE
