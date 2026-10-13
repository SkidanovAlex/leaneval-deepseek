import Mathlib
import Submission.Work.WilG4c.SliceC1Shape
import Submission.Work.WilG4c.SliceC1_mem_m

set_option autoImplicit false

namespace Work.WilG4c

/-- The shape `c1P` realises `{z | C1Exp P M G z}` for an *arbitrary* set `G` that is a member
of `S.Ω F0 D (P + M + 1)` (not only for a graph `famGraph f` of a family, as in
`SliceC1_mem_m`).

The point is that the format and atom count of `c1P S F D G hG` depend only on `S` and on the
index parameters `P`, `M`, not on `D`, `G` or the proof `hG`: the shape's underlying `TSh` term
uses `G` only through `PKS.mem` atoms, whose shape component `TSh.mem n m ι` forgets the set
and its proof.  Hence the `Ω`-bound for the fibre `C¹`-locus is uniform in the input data.

The format parameter has to be raised, because `Set.univ ∈ S.Ω F 4 n` needs `F ≥ n + 4`: this
is why the dummy instantiation is taken at `F0 + ((P + M + 1) + 4)` and why `G`'s membership
is moved up to that format before `c1P` is applied to it.  The degree stays `D`, and the
declared degree `D + 2` of the `mem` atoms is absorbed by the quadratic bound
`b.eval D = c1.Atoms * (D + 2 + 8)`. -/
theorem C1Exp_mem_Omega (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (F0 P M : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (G : Set (Fin (P + M + 1) → ℝ)),
      G ∈ S.Ω F0 D (P + M + 1) →
      {z : Fin (P + M) → ℝ | Work.WilG4c.C1Exp P M G z} ∈ S.Ω a (b.eval D) (P + M) := by
  have hu : (Set.univ : Set (Fin (P + M + 1) → ℝ)) ∈
      S.Ω (F0 + ((P + M + 1) + 4)) 4 (P + M + 1) := by
    have h := Work.WilG5.univ_mem (S := S) (n := P + M + 1)
    exact Work.WilG5.mem_mono h _ _ (by omega) (by omega)
  let c1 : PKS S (F0 + ((P + M + 1) + 4)) 4 (P + M) :=
    c1P (S := S) (F := F0 + ((P + M + 1) + 4)) (D := 4) (P := P) (M := M)
      (G := Set.univ) hu
  refine ⟨c1.Fmt, Polynomial.C c1.Atoms * (Polynomial.X + Polynomial.C 2) +
    Polynomial.C (c1.Atoms * 8), ?_⟩
  intro D G hG
  have hG' : G ∈ S.Ω (F0 + ((P + M + 1) + 4)) D (P + M + 1) :=
    Work.WilG5.mem_mono hG _ _ (by omega) (le_refl D)
  have hmem := PKS.Real_mem_Omega
    (c1P (S := S) (F := F0 + ((P + M + 1) + 4)) (D := D) (P := P) (M := M)
      (G := G) hG')
  rw [c1P_Real (hG := hG')] at hmem
  have hb : (Polynomial.C c1.Atoms * (Polynomial.X + Polynomial.C 2) +
      Polynomial.C (c1.Atoms * 8)).eval D = c1.Atoms * (D + 2 + 8) := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  rw [hb]
  refine Work.WilG5.mem_mono hmem c1.Fmt (c1.Atoms * (D + 2 + 8)) ?_ ?_
  · exact le_of_eq rfl
  · have h := PKS.Deg_le
      (c1P (S := S) (F := F0 + ((P + M + 1) + 4)) (D := D) (P := P) (M := M)
        (G := G) hG')
    rwa [show (c1P (S := S) (F := F0 + ((P + M + 1) + 4)) (D := D) (P := P)
        (M := M) (G := G) hG').Atoms = c1.Atoms from rfl] at h

end Work.WilG4c
