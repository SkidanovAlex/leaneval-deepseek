import Mathlib
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_FarRepel_zetaDiffExplicit
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_FarRepel_lDiffExplicit
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_FarRepel_dhBasic

namespace Work.LinnikAreas.FarRepel

/-- (in namespace `Work.LinnikAreas.FarRepel`; module `Submission.Work.LinnikAreas.FarRepel.multZ_explicit`)

**Differentiated explicit formula for `ζ_K = ζ · L(·,χ)`, tsum form.**  Let `χ` be a non-principal
primitive character mod `q`, let `j ≥ 1` and `1 < Re s`, and let `a ∈ {0,1}` be the parity shift of
`χ` (`a = 0` if `χ` is even, `a = 1` if odd, i.e. the trivial zeros of `L(·,χ)` are `-a, -a-2, …`).
Write `multZ χ u = analyticOrderNatAt completedRiemannZeta u + Work.LinnikContract.zeroMult χ u`
for the multiplicity of `u` as a non-trivial zero of `ζ_K`, and put `k := 2j-1` (odd, `k+1 = 2j`).
Then the zero family is summable and

`(∑' u, (multZ χ u : ℂ)·(1/(s-u))^{2j}) + (∑' n, (1/(s+2n+2))^{2j}) + (∑' n, (1/(s+a+2n))^{2j})
   = 1/(s-1)^{2j} - (1/k!)·( ((logDeriv ζ)^{(k)})(s) + ((logDeriv L(·,χ))^{(k)})(s) )`.

This is the *sum* of the two already-proved halves of the Lagarias–Montgomery–Odlyzko identity
(p. 289; Kadiri–Ng–Wong arXiv:1902.08640 (2.5)): the `ζ`-half `zetaDiffExplicit` (`k` odd, exponent
`k+1 = 2j`) and the `L`-half `lDiffExplicit`, glued with `Summable.add`, `Summable.tsum_add` and
`Nat.cast_add` for `multZ`.  It is exactly the input the Deuring–Heilbronn assembly consumes: taking
real parts of the two evaluation points via `re_tsum_multZ` / `re_tsum_triv` and discarding the
trivial zeros via `trivSeries_nonneg` (all in `dhBasic`) produces the two-point bound `hkey` required
by `Work.LinnikAreas.FarRepel.final_step`. -/
theorem multZ_explicit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) (j : ℕ) (hj : 1 ≤ j)
    (a : ℕ) (ha0 : χ.Even → a = 0) (ha1 : χ.Odd → a = 1)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun u : ℂ => (multZ χ u : ℂ) * (1 / (s - u)) ^ (2 * j)) ∧
    (∑' u : ℂ, (multZ χ u : ℂ) * (1 / (s - u)) ^ (2 * j))
      + ((∑' n : ℕ, (1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ (2 * j))
          + (∑' n : ℕ, (1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ (2 * j)))
      = 1 / (s - 1) ^ (2 * j)
        - (1 / ((2 * j - 1).factorial : ℂ)) *
            (iteratedDeriv (2 * j - 1) (logDeriv riemannZeta) s
              + iteratedDeriv (2 * j - 1) (logDeriv (DirichletCharacter.LFunction χ)) s) := by
  classical
  have hk : 1 ≤ 2 * j - 1 := by omega
  have hodd : (2 * j - 1) % 2 = 1 := by
    have h : 2 * j - 1 = 2 * (j - 1) + 1 := by omega
    rw [h]; omega
  have hsucc : 2 * j - 1 + 1 = 2 * j := by omega
  obtain ⟨hsumZ, hZ⟩ := zetaDiffExplicit (2 * j - 1) hk hodd hs
  obtain ⟨hsumL, hL⟩ := lDiffExplicit χ hχ hprim (2 * j - 1) hk hodd a ha0 ha1 hs
  rw [hsucc] at hsumZ hZ hsumL hL
  -- termwise splitting of `multZ` into its two zero families
  have hpt : ∀ u : ℂ, (multZ χ u : ℂ) * (1 / (s - u)) ^ (2 * j)
      = (analyticOrderNatAt completedRiemannZeta u : ℂ) * (1 / (s - u)) ^ (2 * j)
        + (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ (2 * j) := fun u => by
    simp only [multZ, Nat.cast_add, add_mul]
  have hsum : Summable (fun u : ℂ => (multZ χ u : ℂ) * (1 / (s - u)) ^ (2 * j)) :=
    (hsumZ.add hsumL).congr (fun u => (hpt u).symm)
  refine ⟨hsum, ?_⟩
  have hsplit : (∑' u : ℂ, (multZ χ u : ℂ) * (1 / (s - u)) ^ (2 * j))
      = (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℂ) * (1 / (s - u)) ^ (2 * j))
        + (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ (2 * j)) := by
    rw [tsum_congr hpt, Summable.tsum_add hsumZ hsumL]
  rw [hsplit,
    show (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℂ) * (1 / (s - u)) ^ (2 * j))
        + (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ (2 * j))
        + ((∑' n : ℕ, (1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ (2 * j))
            + (∑' n : ℕ, (1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ (2 * j)))
      = ((∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℂ) * (1 / (s - u)) ^ (2 * j))
          + (∑' n : ℕ, (1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ (2 * j)))
        + ((∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ (2 * j))
          + (∑' n : ℕ, (1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ (2 * j))) by ring,
    hZ, hL]
  ring


end Work.LinnikAreas.FarRepel
