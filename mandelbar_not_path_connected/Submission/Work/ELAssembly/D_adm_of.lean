/-
# Admissibility of the three-pair polygons of the `b₂`-nest (`D_adm_of`)

`Work.ELAssembly.CertGeometry.D_adm` (the field `D_adm` of the certificate geometry) requires
the three pairs of the level-`n` `b₂`-nest to bound an admissible ray polygon,
`Work.EL.PolyAdmissible [N.Za n, N.Zb n, N.Zc n]`.

That is a purely combinatorial statement about the six angles

```
(armA1 n, armA2 n, armB1 n, armB2 n, armC1 n, armC2 n + 1)
```

of the arms of the two nests: they must be strictly cyclically ordered, and the three landing
points pairwise distinct.  The landing-point part is the hypothesis `hAB`/`hBC`/`hCA`; the angle
part is proved here from the closed forms of the six arm angles (`armChain_nest`), which are
affine in `y = 64⁻ⁿ ∈ (0, 1]`, and the elementary real estimates those satisfy.

* `cyclicStrict_six` — a six-element strictly increasing list is `CyclicStrict` once its last
  entry is below `head + 1`.
* `polyAdmissible_three` — three co-landing pairs with strictly cyclic angles and pairwise
  distinct landing points bound an admissible ray polygon.
* `arm_angles_lt` — the six arm angles are strictly increasing, and the last is below the first
  plus one.
-/
import Mathlib
import Submission.Work.ELAssembly.Chains
import Submission.Work.ELNest.armChain_nest

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

open Work.EL

/-! ## Cyclic strict ordering of six angles -/

/-- The six-element list `[a, b, c, d, e, f]` is cyclically strictly ordered
(`Work.EL.CyclicStrict`) as soon as `a < b < c < d < e < f < a + 1`. -/
theorem cyclicStrict_six {a b c d e f : ℝ} (h1 : a < b) (h2 : b < c) (h3 : c < d)
    (h4 : d < e) (h5 : e < f) (h6 : f < a + 1) : Work.EL.CyclicStrict [a, b, c, d, e, f] := by
  refine ⟨by simp, ?_, ?_⟩
  · refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_
      (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.pairwise_singleton _ _)))))
    · intro y hy
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with h | h | h | h | h <;> linarith
    · intro y hy
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with h | h | h | h <;> linarith
    · intro y hy
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with h | h | h <;> linarith
    · intro y hy
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with h | h <;> linarith
    · intro y hy
      simp only [List.mem_singleton] at hy
      linarith
  · intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    have hhead : ([a, b, c, d, e, f] : List ℝ).headD 0 = a := rfl
    rw [hhead]
    rcases hx with h | h | h | h | h | h <;> linarith

/-! ## Admissibility of a three-pair ray polygon -/

/-- **Admissibility of a three-pair ray polygon.**  If the six angles are strictly cyclically
ordered as `P.a < P.b < Q.a < Q.b < R.a < R.b < P.a + 1` and the three landing points are
pairwise distinct, then `[P, Q, R]` is an admissible ray polygon. -/
theorem polyAdmissible_three {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (P Q R : Work.EL.CoPair hN) (h1 : P.a < P.b) (h2 : P.b < Q.a) (h3 : Q.a < Q.b)
    (h4 : Q.b < R.a) (h5 : R.a < R.b) (h6 : R.b < P.a + 1)
    (hyPQ : P.y ≠ Q.y) (hyPR : P.y ≠ R.y) (hyQR : Q.y ≠ R.y) :
    Work.EL.PolyAdmissible [P, Q, R] := by
  refine ⟨by simp, ?_, ?_⟩
  · have hflat : ([P, Q, R].flatMap fun S => [S.a, S.b]) = [P.a, P.b, Q.a, Q.b, R.a, R.b] := by
      simp
    rw [hflat]
    exact cyclicStrict_six h1 h2 h3 h4 h5 h6
  · refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.pairwise_singleton _ _))
    · intro y hy
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with h | h
      · rw [h]; exact hyPQ
      · rw [h]; exact hyPR
    · intro y hy
      simp only [List.mem_singleton] at hy
      rw [hy]; exact hyQR

/-! ## The six arm angles are strictly cyclically ordered -/

/-- **The six arm angles at level `n` are strictly increasing, and the last is below the first
plus one.**  The closed forms (`armChain_nest`) are affine in `y = 64⁻ⁿ ∈ (0, 1]`:

```
armA1 = 22/63 + (289/21483) y     armA2 = 25/63 - (41/21483) y
armB1 = 25/63 + (1156/21483) y    armB2 = 37/63 - (164/21483) y
armC1 = 37/63 + (4624/21483) y    armC2 = 22/63 - (656/21483) y
```

and the six claims are the resulting rational linear estimates. -/
theorem arm_angles_lt (n : ℕ) :
    Work.ELNest.armA1 n < Work.ELNest.armA2 n ∧
    Work.ELNest.armA2 n < Work.ELNest.armB1 n ∧
    Work.ELNest.armB1 n < Work.ELNest.armB2 n ∧
    Work.ELNest.armB2 n < Work.ELNest.armC1 n ∧
    Work.ELNest.armC1 n < Work.ELNest.armC2 n + 1 ∧
    Work.ELNest.armC2 n + 1 < Work.ELNest.armA1 n + 1 := by
  have hy : (0 : ℝ) < ((64 : ℝ) ^ n)⁻¹ := by positivity
  have hy1 : ((64 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [Work.ELNest.armA1_closed n, Work.ELNest.armA2_closed n, Work.ELNest.armB1_closed n,
      Work.ELNest.armB2_closed n, Work.ELNest.armC1_closed n, Work.ELNest.armC2_closed n]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith [hy, hy1]

/-! ## The statement -/

/-- **`D_adm` of `Work.ELAssembly.CertGeometry`**: the polygon bounded by the three level-`n`
arm pairs of the `b₂`-nest is admissible.  The angle ordering is `arm_angles_lt`; the pairwise
distinctness of the three landing points is the hypothesis. -/
theorem D_adm_of {c : ℂ} (d : Work.EL.RootParabolic c) (N : Work.ELAssembly.NestPairs d)
    (hAB : ∀ n : ℕ, (N.Za n).y ≠ (N.Zb n).y) (hBC : ∀ n : ℕ, (N.Zb n).y ≠ (N.Zc n).y)
    (hCA : ∀ n : ℕ, (N.Zc n).y ≠ (N.Za n).y) (n : ℕ) :
    Work.EL.PolyAdmissible [N.Za n, N.Zb n, N.Zc n] := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := arm_angles_lt n
  have g1 : (N.Za n).a < (N.Za n).b := by rw [N.Zaa n, N.Zab n]; exact h1
  have g2 : (N.Za n).b < (N.Zb n).a := by rw [N.Zab n, N.Zba n]; exact h2
  have g3 : (N.Zb n).a < (N.Zb n).b := by rw [N.Zba n, N.Zbb n]; exact h3
  have g4 : (N.Zb n).b < (N.Zc n).a := by rw [N.Zbb n, N.Zca n]; exact h4
  have g5 : (N.Zc n).a < (N.Zc n).b := by rw [N.Zca n, N.Zcb n]; exact h5
  have g6 : (N.Zc n).b < (N.Za n).a + 1 := by rw [N.Zcb n, N.Zaa n]; exact h6
  exact polyAdmissible_three _ _ _ g1 g2 g3 g4 g5 g6 (hAB n) (hCA n).symm (hBC n)

end Work.ELAssembly
