import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.exists_modByMonic_aeval_natDegree_lt
import Submission.Work.MotV5.taylor_one_eq_self_natDegree_eq_zero
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Elements of `K⟮asRoot g⟯` fixed by the Artin–Schreier shift are rational

Let `K = 𝕜(t)`, `Kb = AlgebraicClosure K`, `α = asRoot g` a root of `X⁵ - X - g` in `Kb`, and let
`σ : Kb ≃ₐ[K] Kb` be a `K`-automorphism with `σ α = α + 1` (the Artin–Schreier generator; its
existence is the content of `MotV5/asAut_Kb.lean`).  The theorem below proves that an element
`c ∈ K⟮α⟯` fixed by `σ` is already in `K`:

`∃ d : K, algebraMap K Kb d = c`.

The proof is elementary and avoids Galois theory.  Write `d := (minpoly K α).natDegree` and pick,
for `c ∈ K⟮α⟯ = K[α]`, the *reduced* representative `r ∈ K[X]` with `aeval α r = c` and
`r.natDegree < d` (division by the monic `minpoly K α`); this is
`Work.MotV5.exists_modByMonic_aeval_natDegree_lt`.  Since `σ` fixes `K` and sends `α` to `α + 1`,
fixedness of `c` reads

`aeval (α+1) r = aeval α (taylor 1 r)`  and hence  `aeval α (taylor 1 r - r) = 0`,

where `taylor 1 r = r(X + 1)`.  As `(taylor 1 r - r).natDegree ≤ r.natDegree < d`, uniqueness of
the reduced representative (a nonzero polynomial of degree `< d` cannot vanish at `α`) forces
`r(X + 1) = r`.  Finally `r.natDegree < d ≤ 5` (because `minpoly K α ∣ X⁵ - X - g`), so
`r.natDegree ≤ 4`, and by `Work.MotV5.taylor_one_eq_self_natDegree_eq_zero` a polynomial of degree
`≤ 4` over a field of characteristic `5` invariant under `X ↦ X + 1` is constant.  Hence `r` is a
constant and `c` is the image of that constant.
-/

namespace Work.MotV5

theorem exists_algebraMap_of_mem_adjoin_asRoot_of_sigma_fixed (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (g : RatFunc 𝕜) (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (hσ : σ (Work.MotV5.asRoot g) = Work.MotV5.asRoot g + 1)
    (c : Work.MotV.Kb 𝕜)
    (hc : c ∈ IntermediateField.adjoin (RatFunc 𝕜) {Work.MotV5.asRoot g}) (hfix : σ c = c) :
    ∃ d : RatFunc 𝕜, algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) d = c := by
  classical
  -- `α := asRoot g` is a root of the monic polynomial `X⁵ - X - g`, hence integral, and
  -- `deg (minpoly ℚ(t) α) ≤ 5`.
  have hp_deg : (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g :
      Polynomial (RatFunc 𝕜)).natDegree = 5 := by
    compute_degree!
  have hp_ne : (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g :
      Polynomial (RatFunc 𝕜)) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hp_deg
    exact absurd hp_deg (by norm_num)
  have hp_root : Polynomial.aeval (Work.MotV5.asRoot g)
      (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g : Polynomial (RatFunc 𝕜)) = 0 := by
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [Work.MotV5.asRoot_spec]
    first | refl_ring1 | ring
  have hp_monic : (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g :
      Polynomial (RatFunc 𝕜)).Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hp_deg]
    simp [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  have hInt : IsIntegral (RatFunc 𝕜) (Work.MotV5.asRoot g) :=
    ⟨_, hp_monic, hp_root⟩
  have hm : (minpoly (RatFunc 𝕜) (Work.MotV5.asRoot g)).natDegree ≤ 5 := by
    have hdvd : minpoly (RatFunc 𝕜) (Work.MotV5.asRoot g) ∣
        (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g : Polynomial (RatFunc 𝕜)) :=
      minpoly.dvd _ _ hp_root
    calc (minpoly (RatFunc 𝕜) (Work.MotV5.asRoot g)).natDegree
        ≤ (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g :
            Polynomial (RatFunc 𝕜)).natDegree := Polynomial.natDegree_le_of_dvd hdvd hp_ne
      _ = 5 := hp_deg
  -- take the reduced representative of `c`: `c = aeval α r` with `r.natDegree < deg (minpoly)`.
  obtain ⟨r, hr, hrlt⟩ :=
    exists_modByMonic_aeval_natDegree_lt (K := RatFunc 𝕜) (L := Work.MotV.Kb 𝕜)
      (Work.MotV5.asRoot g) c hInt hc
  -- fixedness of `c` transfers to `taylor 1 r - r`.
  have hsh : Polynomial.aeval (Work.MotV5.asRoot g) (Polynomial.taylor 1 r) = c := by
    have h1 : Polynomial.aeval (Work.MotV5.asRoot g) (Polynomial.taylor 1 r) =
        Polynomial.aeval (Work.MotV5.asRoot g + 1) r := by
      rw [Polynomial.taylor_apply, Polynomial.aeval_comp]
      congr 1
      simp
    rw [h1, ← hσ, Polynomial.aeval_algHom_apply σ (Work.MotV5.asRoot g) r, hr, hfix]
  have hdiff : Polynomial.aeval (Work.MotV5.asRoot g) (Polynomial.taylor 1 r - r) = 0 := by
    rw [map_sub, hsh, hr, sub_self]
  -- uniqueness of the reduced representative forces `taylor 1 r = r`.
  have htaylor : Polynomial.taylor 1 r = r := by
    have hzero : Polynomial.taylor 1 r - r = 0 := by
      by_contra hne
      have hdvd : minpoly (RatFunc 𝕜) (Work.MotV5.asRoot g) ∣ (Polynomial.taylor 1 r - r) :=
        minpoly.dvd _ _ hdiff
      have h1 : (minpoly (RatFunc 𝕜) (Work.MotV5.asRoot g)).natDegree ≤
          (Polynomial.taylor 1 r - r).natDegree := Polynomial.natDegree_le_of_dvd hdvd hne
      have h2 : (Polynomial.taylor 1 r - r).natDegree ≤ r.natDegree := by
        calc (Polynomial.taylor 1 r - r).natDegree
            ≤ max (Polynomial.taylor 1 r).natDegree r.natDegree := Polynomial.natDegree_sub_le _ _
          _ = r.natDegree := by rw [Polynomial.natDegree_taylor, max_self]
      omega
    exact sub_eq_zero.mp hzero
  -- hence `r` has degree `≤ 4` and, by the characteristic `5` rigidity, is constant.
  have hr0 : r.natDegree = 0 :=
    taylor_one_eq_self_natDegree_eq_zero r (by omega) htaylor
  set a := r.coeff 0 with ha
  have hrC : r = Polynomial.C a := by
    rw [ha]
    exact Polynomial.eq_C_of_natDegree_le_zero (p := r) (by omega)
  refine ⟨a, ?_⟩
  rw [← hr, hrC, Polynomial.aeval_C]

end Work.MotV5
