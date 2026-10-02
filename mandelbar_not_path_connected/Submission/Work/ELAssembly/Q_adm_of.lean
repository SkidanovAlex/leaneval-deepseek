import Mathlib
import Submission.Work.ELAssembly.Defs
import Submission.Work.ELNest.bAng_range

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

open Work.EL

/-! ## Admissibility of a two-pair polygon

The list `[P, Q]` of two co-landing pairs is an admissible ray polygon
(`Work.EL.PolyAdmissible`, `Submission/Work/ELTop/Defs.lean:229`) exactly when the four angles
are strictly cyclically ordered as `P.a < P.b < Q.a < Q.b < P.a + 1` and the two landing points
differ.  The two lemmas below unpack that definition once and for all. -/

/-- The four-element list `[a, b, c, d]` is cyclically strictly ordered
(`Work.EL.CyclicStrict`) as soon as `a < b < c < d < a + 1`. -/
theorem cyclicStrict_four {a b c d : ℝ} (h1 : a < b) (h2 : b < c) (h3 : c < d)
    (h4 : d < a + 1) : Work.EL.CyclicStrict [a, b, c, d] := by
  have hpw : List.Pairwise (· < ·) [a, b, c, d] := by
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ ?_))
    · intro y hy
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with h | h | h <;> linarith
    · intro y hy
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with h | h <;> linarith
    · intro y hy
      simp only [List.mem_singleton] at hy
      linarith
    · exact List.pairwise_singleton _ _
  refine ⟨by simp, hpw, ?_⟩
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  have hhead : ([a, b, c, d] : List ℝ).headD 0 = a := rfl
  rw [hhead]
  rcases hx with h | h | h | h <;> linarith

/-- **Admissibility of a two-pair ray polygon.**  If `P.a < P.b < Q.a < Q.b < P.a + 1` and the
two landing points differ, then `[P, Q]` is an admissible ray polygon. -/
theorem polyAdmissible_pair {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (P Q : Work.EL.CoPair hN) (h1 : P.a < P.b) (h2 : P.b < Q.a) (h3 : Q.a < Q.b)
    (h4 : Q.b < P.a + 1) (hyne : P.y ≠ Q.y) : Work.EL.PolyAdmissible [P, Q] := by
  have hcyc : Work.EL.CyclicStrict [P.a, P.b, Q.a, Q.b] :=
    cyclicStrict_four h1 h2 h3 h4
  refine ⟨by simp, ?_, ?_⟩
  · have hflat : ([P, Q].flatMap fun R => [R.a, R.b]) = [P.a, P.b, Q.a, Q.b] := by simp
    rw [hflat]
    exact hcyc
  · refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
    intro y hy
    simp only [List.mem_singleton] at hy
    subst hy
    exact hyne

/-! ## The admissibility of the `(α-pair, level-n pair)` polygons of the `z₁`-nest

The angles of the `α`-pair are `α₁ = 371/1023 < α₂ = 404/1023`, and the level-`n` pair of the
nest at `z₁` has angles `βₙ' = α₂ + (β₀' − α₂)/1024ⁿ` and `βₙ + 1 = α₁ − (α₁ − β₀)/1024ⁿ + 1`,
which by `Work.ELNest.bAng_range` lie in `(α₂, 1)` and `(1, α₁ + 1)` respectively.  Hence the
four angles are strictly cyclically ordered; the only remaining requirement is that the level-`n`
pair does not land at `z₁`, which is the hypothesis `hne`. -/

/-- **`Q_adm` of `Work.ELAssembly.CertGeometry`**: the polygon bounded by the `α`-pair and the
level-`n` pair of the nest at `z₁` is admissible, provided the level-`n` pair does not land at
`z₁`. -/
theorem Q_adm_of {c : ℂ} (d : Work.EL.RootParabolic c) (N : Work.ELAssembly.NestPairs d)
    (hne : ∀ n : ℕ, (N.Qp n).y ≠ d.z₁) (n : ℕ) :
    Work.EL.PolyAdmissible [Work.ELAssembly.alphaPairOf d, N.Qp n] := by
  obtain ⟨⟨hb0, hb1⟩, hb2, hb3⟩ := Work.ELNest.bAng_range n
  have hα12 : Work.EL.alpha1 < Work.EL.alpha2 := by
    norm_num [Work.EL.alpha1, Work.EL.alpha2]
  have h1 : (Work.ELAssembly.alphaPairOf d).a < (Work.ELAssembly.alphaPairOf d).b := by
    rw [Work.ELAssembly.alphaPairOf_a, Work.ELAssembly.alphaPairOf_b]
    exact hα12
  have h2 : (Work.ELAssembly.alphaPairOf d).b < (N.Qp n).a := by
    rw [Work.ELAssembly.alphaPairOf_b, N.Qpa n]
    rw [show Work.EL.alpha2 = Work.ELNest.alpha2 from rfl]
    exact hb2
  have h3 : (N.Qp n).a < (N.Qp n).b := by
    rw [N.Qpa n, N.Qpb n]
    have hb1'' : Work.ELNest.alpha1 < 1 := by norm_num [Work.ELNest.alpha1]
    have hβ0' : Work.ELNest.beta0' < 1 := by norm_num [Work.ELNest.beta0']
    linarith
  have h4 : (N.Qp n).b < (Work.ELAssembly.alphaPairOf d).a + 1 := by
    rw [N.Qpb n, Work.ELAssembly.alphaPairOf_a]
    rw [show Work.EL.alpha1 = Work.ELNest.alpha1 from rfl]
    linarith
  refine polyAdmissible_pair _ _ h1 h2 h3 h4 ?_
  intro h
  exact hne n h.symm

end Work.ELAssembly
